//===--- SemaReflect.cpp - Semantic Analysis for Reflection ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file implements semantic analysis for reflection.
//
//===----------------------------------------------------------------------===//

#include "TreeTransform.h"
#include "clang/Sema/SemaDiagnostic.h"
#include "clang/Sema/Sema.h"
#include "clang/Sema/Ownership.h"
#include "clang/Sema/Template.h"
#include "clang/AST/CanonicalType.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Type.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/Sema/Lookup.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Sema/Overload.h"
#include "clang/Sema/Initialization.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/Sema/Template.h"
#include "clang/Sema/TemplateDeduction.h"

#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

#include <array>
#include <string>

using namespace clang;
using namespace sema;

static ClassTemplateDecl*
LookupStdReflectionDecl(Sema &S, StringRef ReflectionSupportClassName, SourceLocation Loc) {
    NamespaceDecl *StdReflection = S.lookupStdReflectionNamespace();
    if (!StdReflection) {
        S.Diag(Loc, diag::err_implied_std_reflection_decl_not_found);
        return nullptr;
    }
    LookupResult Result(S, &S.PP.getIdentifierTable().get(ReflectionSupportClassName), Loc, Sema::LookupOrdinaryName);
    if (!S.LookupQualifiedName(Result, StdReflection)) {
        S.Diag(Loc, diag::err_implied_std_reflection_decl_not_found);
        return nullptr;
    }
    ClassTemplateDecl *DeclTemplate = Result.getAsSingle<ClassTemplateDecl>();
    if (!DeclTemplate) {
        Result.suppressDiagnostics();
        NamedDecl *FoundDecl = *Result.begin();
        S.Diag(FoundDecl->getLocation(), diag::err_malformed_std_reflection_decl);
        return nullptr;
    }
    TemplateParameterList *Params = DeclTemplate->getTemplateParameters();
    if (Params->getMinRequiredArguments() != 1 || !llvm::isa<NonTypeTemplateParmDecl>(Params->getParam(0))) {
        S.Diag(DeclTemplate->getLocation(), diag::err_malformed_std_reflection_decl);
        return nullptr;
    }
    return DeclTemplate;
}

static FunctionDecl*
InstantiateFunctionTemplateDecl(Sema &SemaRef, FunctionTemplateDecl *FTD, DeclContext *Context,
                                llvm::ArrayRef<TemplateArgument> Arguments) {
    void *InsertPos = nullptr;
    if (FunctionDecl *FDecl =  FTD->findSpecialization(Arguments, InsertPos))
        return FDecl;
    TemplateArgumentList ArgList(TemplateArgumentList::OnStack, Arguments);
    MultiLevelTemplateArgumentList MultiArgList(ArgList);
    TemplateDeductionInfo TempDeducInfo((SourceLocation()));
    Sema::InstantiatingTemplate InstTemp(SemaRef, SourceLocation(), FTD,  Arguments,
                                         Sema::CodeSynthesisContext::ExplicitTemplateArgumentSubstitution,
                                         TempDeducInfo);
    TemplateDeclInstantiator Instantiator(SemaRef, Context, MultiArgList);
    auto Instantiated = Instantiator.Visit(FTD);
    if (Instantiated) {
        if (FunctionTemplateDecl* InstantiatedDecl = llvm::dyn_cast<FunctionTemplateDecl>(Instantiated)) {
             FunctionDecl *X = InstantiatedDecl->getTemplatedDecl();
             return X;
        }
    }
    return nullptr;
}

static StringLiteral*
CreateStringLiteral(Sema &S, StringRef NewStringLiteral, SourceLocation Loc) {
    QualType StrTy = S.Context.getConstantArrayType(S.Context.CharTy, llvm::APInt(32, NewStringLiteral.size() + 1),
                                                    ArrayType::Normal, 0);
    return StringLiteral::Create(S.Context, NewStringLiteral.data(), StringLiteral::Ascii, false, StrTy, Loc);
}

static IntegerLiteral*
CreateIntegerLiteral(Sema &S, int64_t Integer, SourceLocation Loc) {
    return IntegerLiteral::Create(S.Context, llvm::APInt(64, Integer, /*IsSigned=*/ false), S.Context.UnsignedLongTy, Loc);
}

static ClassTemplateDecl*
LookupStdTupleTemplate(Sema &S, SourceLocation Loc) {
    NamespaceDecl *StdNamespaceDecl = S.getStdNamespace();
    if (!StdNamespaceDecl) {
        S.Diag(Loc, diag::err_implied_std_tuple_not_found);
        return nullptr;
    }
    LookupResult StdTupleResult(S, &S.PP.getIdentifierTable().get("tuple"), Loc,
                                Sema::LookupNameKind::LookupTagName);
    if (!S.LookupQualifiedName(StdTupleResult, StdNamespaceDecl)) {
        S.Diag(Loc, diag::err_implied_std_tuple_not_found);
        return nullptr;
    }
    ClassTemplateDecl *StdTupleTemplate = StdTupleResult.getAsSingle<ClassTemplateDecl>();
    if (!StdTupleTemplate) {
        StdTupleResult.suppressDiagnostics();;
        NamedDecl *Found = *StdTupleResult.begin();
        S.Diag(Found->getLocation(), diag::err_malformed_std_tuple);
        return nullptr;
    }
    TemplateParameterList *Parameters = StdTupleTemplate->getTemplateParameters();
    if (Parameters->size() != 1 || !isa<TemplateTypeParmDecl>(Parameters->getParam(0)) ||
            !(llvm::dyn_cast<TemplateTypeParmDecl>(Parameters->getParam(0)))->isParameterPack()) {
        S.Diag(StdTupleTemplate->getLocation(), diag::err_malformed_std_tuple);
        return nullptr;
    }
    return StdTupleTemplate;
}

static QualType
SpecializeClassTemplate(Sema &S, ClassTemplateDecl *TemplateDecl, TemplateArgumentListInfo *TemplateArgs, SourceLocation Loc) {
    if (!TemplateDecl) {
        return QualType();
    }
    SmallVector<TemplateArgument, 4> Converted;
    void *InsertPos = nullptr;
    S.CheckTemplateArgumentList(TemplateDecl, TemplateDecl->getLocStart(), *TemplateArgs, false, Converted, true);
    ClassTemplateSpecializationDecl* TemplateSpecializationDecl
             = TemplateDecl->findSpecialization(Converted, InsertPos);
    if (!TemplateSpecializationDecl) {
        TemplateSpecializationDecl = ClassTemplateSpecializationDecl::Create(S.Context,
                                                  TemplateDecl->getTemplatedDecl()->getTagKind(),
                                                  TemplateDecl->getDeclContext(),
                                                  TemplateDecl->getTemplatedDecl()->getLocStart(),
                                                  TemplateDecl->getLocation(), TemplateDecl,
                                                  Converted, nullptr);
        TemplateDecl->AddSpecialization(TemplateSpecializationDecl, nullptr);
        if (TemplateDecl->isOutOfLine())
            TemplateSpecializationDecl->setLexicalDeclContext(TemplateDecl->getLexicalDeclContext());
        if (TemplateSpecializationDecl->getSpecializationKind() == TemplateSpecializationKind::TSK_Undeclared) {
            TemplateArgumentList ArgList(TemplateArgumentList::OnStack, Converted);
            MultiLevelTemplateArgumentList TemplateArgList;
            TemplateArgList.addOuterTemplateArguments(&ArgList);
            S.InstantiateAttrsForDecl(TemplateArgList, TemplateDecl->getTemplatedDecl(), TemplateSpecializationDecl);
        }
    }
    S.RequireCompleteType(TemplateDecl->getLocation(), S.Context.getTypeDeclType(TemplateSpecializationDecl),
                          diag::err_incomplete_type);
    return S.Context.getTemplateSpecializationType(TemplateName(TemplateDecl), *TemplateArgs,
                                                 S.Context.getTypeDeclType(TemplateSpecializationDecl));
}

static CXXRecordDecl*
LookupStdStringView(Sema &S, SourceLocation Loc) {
    NamespaceDecl *StdNamespaceDecl = S.getStdNamespace();
    if (!StdNamespaceDecl) {
        S.Diag(Loc, diag::err_implied_std_string_view_not_found);
        return nullptr;
    }
    LookupResult StdStringViewResult(S, &S.PP.getIdentifierTable().get("string"), Loc,
                                Sema::LookupNameKind::LookupTagName);
    if (!S.LookupQualifiedName(StdStringViewResult, StdNamespaceDecl)) {
        S.Diag(Loc, diag::err_implied_std_string_view_not_found);
        return nullptr;
    }
    TypedefDecl *StdStringViewTypedefDecl = StdStringViewResult.getAsSingle<TypedefDecl>();
    QualType StdStringViewType = StdStringViewTypedefDecl->getUnderlyingType();
    return (StdStringViewType.getTypePtr())->getAsCXXRecordDecl();
}

CXXRecordDecl*
Sema::getStdStringView(SourceLocation Loc) {
    if (!StdStringViewCache) {
        StdStringViewCache = LookupStdStringView(*this, Loc);
    }
    return StdStringViewCache;
}

static CXXRecordDecl*
LookupMetaEnumConstant(Sema &S, SourceLocation Loc) {
    NamespaceDecl *ReflectionNamespaceDecl = S.lookupStdReflectionNamespace();
    if (!ReflectionNamespaceDecl) {
        S.Diag(Loc, diag::err_implied_std_string_view_not_found); // change the error message
        return nullptr;
    }
    LookupResult MetaEnumConstantResult(S, &S.PP.getIdentifierTable().get("meta_enum_constant"), Loc,
                                Sema::LookupNameKind::LookupTagName);
    if (!S.LookupQualifiedName(MetaEnumConstantResult, ReflectionNamespaceDecl)) {
        S.Diag(Loc, diag::err_implied_std_string_view_not_found); // change the error message
        return nullptr;
    }
    return MetaEnumConstantResult.getAsSingle<CXXRecordDecl>();
}

CXXRecordDecl*
Sema::getMetaEnumConstantDecl(SourceLocation Loc) {
    if (!MetaEnumConstantDecl) {
        MetaEnumConstantDecl = LookupMetaEnumConstant(*this, Loc);
    }
    return MetaEnumConstantDecl;
}

static ClassTemplateDecl*
getReflectionEnumDecl(Sema &S, SourceLocation Loc) {
    if (!S.ReflectionEnumDecl) {
        S.ReflectionEnumDecl = LookupStdReflectionDecl(S, "meta_enum", Loc);
    }
    return S.ReflectionEnumDecl;
}

QualType
Sema::BuildStdTuple(TemplateArgumentListInfo *TemplateArgs, SourceLocation Loc) {
    if (!StdTupleTemplate) {
        StdTupleTemplate = LookupStdTupleTemplate(*this, Loc);
        if (!StdTupleTemplate)
            return QualType();
    }
    return SpecializeClassTemplate(*this, StdTupleTemplate, TemplateArgs, Loc);
}

ExprResult
Sema::CreateStringViewObject(Sema &S, StringRef String, SourceLocation Loc) {
    CXXRecordDecl *StdStringViewDecl = S.getStdStringView(Loc);
    if (!StdStringViewDecl)
        return ExprError();
    StringLiteral *NewStringLiteral = CreateStringLiteral(S, String, Loc);
    IntegerLiteral *NewIntegerLiteral = CreateIntegerLiteral(S, String.size() + 1, Loc);
    OverloadCandidateSet CtorCandidateSet(Loc, OverloadCandidateSet::CandidateSetKind::CSK_Normal);
    for (auto Ctor : S.LookupConstructors(StdStringViewDecl)) {
        if (auto FuncDecl = llvm::dyn_cast<FunctionDecl>(Ctor)) {
           S.AddOverloadCandidate(FuncDecl, DeclAccessPair::make(FuncDecl, Ctor->getAccess()),
                                 {NewStringLiteral, NewIntegerLiteral}, CtorCandidateSet,
                                 /*SuppressUserConversions=*/ false,
                                 /*PartialOverloading=*/ true);
        }
    }
    OverloadCandidateSet::iterator BestResultPtr;
    OverloadingResult OResult = CtorCandidateSet.BestViableFunction(S, Loc, BestResultPtr, true);
    assert(OResult == OverloadingResult::OR_Success && "No viable string_view ctor candidates found");
    CXXConstructorDecl *StdStringViewCtorDecl = llvm::dyn_cast<CXXConstructorDecl>(BestResultPtr->Function);
    ParmVarDecl *FirstParm = StdStringViewCtorDecl->getParamDecl(0);
    ParmVarDecl *SecondParm = StdStringViewCtorDecl->getParamDecl(1);
    ParmVarDecl *ThirdParm = StdStringViewCtorDecl->getParamDecl(2);
    ImplicitCastExpr *FirstArgExpr = ImplicitCastExpr::Create(S.Context, FirstParm->getType(), CastKind::CK_ArrayToPointerDecay,
                             NewStringLiteral, nullptr, ExprValueKind::VK_RValue);
    ImplicitCastExpr *SecondArgExpr = ImplicitCastExpr::Create(S.Context, SecondParm->getType(), CastKind::CK_IntegralCast,
                             NewIntegerLiteral, nullptr, ExprValueKind::VK_RValue);
    CXXDefaultArgExpr *ThirdArgExpr = CXXDefaultArgExpr::Create(S.Context, Loc, ThirdParm);
    llvm::ArrayRef<Expr*> Args({ FirstArgExpr, SecondArgExpr, ThirdArgExpr });
    TypeSourceInfo *TInfo = S.Context.CreateTypeSourceInfo(QualType(StdStringViewDecl->getTypeForDecl(), 0));
    CXXTemporaryObjectExpr *TempObjExpr = new (S.Context) CXXTemporaryObjectExpr(
       S.Context, StdStringViewCtorDecl, TInfo->getType(),
       TInfo, Args, Loc,
       /*HadMultipleCandidates=*/ false,
       /*isListInitialization= */ false,
       /*isStdInitListInitialization=*/ false,
       /*RequiresZeroInit=     */ false);
    return TempObjExpr;
}

ExprResult
Sema::CreateTupleObject(Sema &S, MultiExprArg Args, SourceLocation Loc) {
    TemplateArgumentListInfo TemplateArgs(Loc, Loc);
    SmallVector<Expr*, 8> Arguments;
    for (Expr *E : Args) {
        TemplateArgs.addArgument(TemplateArgumentLoc(TemplateArgument(E->getType()), S.Context.CreateTypeSourceInfo(E->getType())));
        Expr *AddedExpr = E;
        E->getType().dump();
        llvm::outs() << "\n";
        if (!llvm::isa<MaterializeTemporaryExpr>(E)) {
            if (!E->isGLValue())
                AddedExpr = S.CreateMaterializeTemporaryExpr(E->getType(), E, !(E->isRValue() || E->isXValue()));
        }
        Arguments.push_back(AddedExpr);
    }
    QualType StdTupleTy = S.BuildStdTuple(&TemplateArgs, Loc);
    CXXRecordDecl *StdTupleSpecDecl = StdTupleTy.getTypePtr()->getAsCXXRecordDecl();
    OverloadCandidateSet CtorCandidateSet(SourceLocation(), OverloadCandidateSet::CandidateSetKind::CSK_Normal);
    for (NamedDecl *D : S.LookupConstructors(StdTupleSpecDecl)) {
        if (FunctionDecl *FDecl = llvm::dyn_cast<FunctionDecl>(D)) {
            S.AddOverloadCandidate(FDecl, DeclAccessPair::make(FDecl, FDecl->getAccess()), Args, CtorCandidateSet);
        }
        else if (FunctionTemplateDecl *FTDecl = llvm::dyn_cast<FunctionTemplateDecl>(D)) {
            S.AddTemplateOverloadCandidate(FTDecl, DeclAccessPair::make(FTDecl, FTDecl->getAccess()),
                                           &TemplateArgs, Args, CtorCandidateSet);
        }
    }
    OverloadCandidateSet::iterator BestResultPtr;
    OverloadingResult OResult = CtorCandidateSet.BestViableFunction(S, SourceLocation(), BestResultPtr, true);
    assert((OResult == OverloadingResult::OR_Success) && "No viable std::tuple ctor candidates found");
    CXXConstructorDecl *CtorDecl = nullptr;
    if (BestResultPtr->Function)
        CtorDecl = llvm::dyn_cast<CXXConstructorDecl>(BestResultPtr->Function);
    TypeSourceInfo* TInfo = S.Context.CreateTypeSourceInfo(StdTupleTy);
    llvm::SmallVector<Expr*, 8> FinalConverted;
    S.CompleteConstructorCall(CtorDecl, Args, Loc, FinalConverted, true);
    S.MarkFunctionReferenced(CtorDecl->getLocation(), CtorDecl);
    CXXTemporaryObjectExpr *TempObjExpr = new (S.Context) CXXTemporaryObjectExpr(
         S.Context, CtorDecl, StdTupleTy,
         TInfo, FinalConverted, SourceRange(Loc),
         /*HadMultipleCandidates=*/ false,
         /*isListInitialization= */ true,
         /*isStdInitListInitialization=*/ false,
         /*RequiresZeroInit=     */ false);
    return TempObjExpr;
}

static TemplateArgument
CreateIntegralTemplateArgument(ASTContext &Context, uint64_t integer) {
    llvm::APInt Int(64, integer, false);
    return TemplateArgument(Context, llvm::APSInt(Int), Context.LongTy);
}

ExprResult
Sema::ActOnCXXReflectExprExpression(Declarator &D, Scope *S,
                                    SourceLocation KWLocation,
                                    SourceLocation LParenLoc,
                                    SourceLocation RParenLoc) {
    TypeSourceInfo *TInfo = GetTypeForDeclarator(D, S);
    QualType Ty = TInfo->getType();
    TagDecl* TyPtr = Ty.getTypePtr()->getAsTagDecl();
    if (!TyPtr->isEnum())
        return ExprError();
    ClassTemplateDecl *MetaEnumDecl = LookupStdReflectionDecl(*this, "meta_enum", KWLocation);
    TemplateArgument Arg = CreateIntegralTemplateArgument(Context, reinterpret_cast<uint64_t>(TyPtr));
    TemplateArgumentListInfo TALInfo(LParenLoc, RParenLoc);
    TALInfo.addArgument(TemplateArgumentLoc(Arg, Context.CreateTypeSourceInfo(Arg.getIntegralType())));
    QualType TargetType = SpecializeClassTemplate(*this, MetaEnumDecl, &TALInfo, KWLocation);
    return BuildCXXReflectExprExpression(TyPtr, TargetType, KWLocation, LParenLoc, RParenLoc);
}

ExprResult
Sema::ActOnCXXEnumReflectQueryExpr(Scope *S, unsigned QueryNumber, SourceLocation KWLocation, SourceLocation RParenLoc) {
    Scope *TempScope = S;
    while (!TempScope->isClassScope())
        TempScope = TempScope->getParent();
    DeclContext *Context = TempScope->getEntity();
    EnumDecl *EDecl = nullptr; // fix this !!!!
    return BuildCXXEnumReflectQueryExpr(EDecl, QueryNumber, KWLocation, RParenLoc);
}

ExprResult
Sema::BuildCXXReflectExprExpression(TagDecl *TyPtr, QualType T, SourceLocation KWLocation,
                                    SourceLocation LParenLoc, SourceLocation RParenLoc) {
    assert(llvm::isa<EnumDecl>(TyPtr) && "TyPtr is not an EnumDecl");
    return new (Context) CXXReflectExpr(KWLocation, LParenLoc, RParenLoc, llvm::dyn_cast<EnumDecl>(TyPtr), T,
                                        CXXConstructExpr::CK_Complete, ExprValueKind::VK_LValue,
                                        ExprObjectKind::OK_Ordinary, /*TypeDependent=*/ false, /*ValueDependent=*/ false,
                                        /*InstantiationDependent=*/ false, /*UnexpandedParamPacks=*/ false);
}

ExprResult
Sema::BuildCXXEnumReflectQueryExpr(TagDecl *TyPtr, unsigned QueryNumber, SourceLocation KWLocation, SourceLocation RParenLoc) {
    assert(llvm::isa<EnumDecl>(TyPtr) && "TyPtr is not an EnumDecl");
    return new (Context) CXXEnumReflectionQueryExpr(KWLocation, RParenLoc, llvm::dyn_cast<EnumDecl>(TyPtr), QueryNumber, CXXConstructExpr::CK_Complete,
                                                    QualType(), ExprValueKind::VK_LValue, ExprObjectKind::OK_Ordinary, /*TypeDependent=*/ false, /*ValueDependent=*/ false,
                                                    /*InstantiationDependent=*/ false, /*UnexpandedParamPacks=*/ false);
}

ExprResult
Sema::ActOnCXXEnumNameExpression(Declarator &D, Scope *S,
                                 SourceLocation KWLocation,
                                 SourceLocation LParenLoc,
                                 SourceLocation RParenLoc) {
    TypeSourceInfo *TInfo = GetTypeForDeclarator(D, S);
    QualType Ty = TInfo->getType();
    TagDecl *TagPtr = Ty.getTypePtr()->getAsTagDecl();
    return CreateStringViewObject(*this, TagPtr->getName(), KWLocation);
}

ExprResult
Sema::ActOnCXXEnumNumValExpression(Declarator &D, Scope *S,
                                   SourceLocation KWLocation,
                                   SourceLocation LParenLoc,
                                   SourceLocation RParenLoc){
    TypeSourceInfo *TInfo = GetTypeForDeclarator(D, S);
    QualType Ty = TInfo->getType();
    TagDecl *TagPtr = Ty.getTypePtr()->getAsTagDecl();
    EnumDecl *EDecl = llvm::dyn_cast<EnumDecl>(TagPtr);
    return CreateIntegerLiteral
            (*this, std::distance(EDecl->enumerator_begin(), EDecl->enumerator_end()), KWLocation);
}

ExprResult
Sema::ActOnCXXEnumValuesExpression(Declarator &D, Scope *S,
                                   SourceLocation KWLocation,
                                   SourceLocation LParenLoc,
                                   SourceLocation RParenLoc){
    TypeSourceInfo *TInfo = GetTypeForDeclarator(D, S);
    QualType Ty = TInfo->getType();
    TagDecl *TagPtr = Ty.getTypePtr()->getAsTagDecl();
    EnumDecl *EDecl = llvm::dyn_cast<EnumDecl>(TagPtr);
    llvm::SmallVector<Expr*, 4> TupleArgs;
    CXXRecordDecl *ECDecl =  getMetaEnumConstantDecl( KWLocation);
    DeclContextLookupResult Res =  LookupConstructors(ECDecl);
    CXXConstructorDecl *CtorDecl = llvm::dyn_cast<CXXConstructorDecl>(Res.front());
    QualType TargetType(ECDecl->getTypeForDecl(), 0);
    for (EnumDecl::enumerator_iterator first = EDecl->enumerator_begin(), last = EDecl->enumerator_end();
         first != last; ++ first) {
        EnumConstantDecl *EnumConstant = *first;
        Expr *FirstArg =
                Sema::CreateStringViewObject(*this, EnumConstant->getName(),  KWLocation).get();
        Expr *SecondArg = IntegerLiteral::Create( Context, llvm::APInt(32, EnumConstant->getInitVal().getLimitedValue(),
                                                            /*IsSigned=*/ false),  Context.IntTy,  KWLocation);
        llvm::SmallVector<Expr*, 2> Args({FirstArg, SecondArg});
        llvm::SmallVector<Expr*, 2> FinalConverted;
        CompleteConstructorCall(CtorDecl, Args, KWLocation, FinalConverted, true);
        CXXTemporaryObjectExpr *TempObjExpr = new (Context) CXXTemporaryObjectExpr(
             Context, CtorDecl, TargetType,
             Context.getTrivialTypeSourceInfo(TargetType), FinalConverted, SourceRange(KWLocation),
             /*HadMultipleCandidates=*/ false,
             /*isListInitialization= */ false,
             /*isStdInitListInitialization=*/ false,
             /*RequiresZeroInit=     */ false);
        Expr * E = CreateMaterializeTemporaryExpr(TempObjExpr->getType(), TempObjExpr, !(TempObjExpr->isRValue() || TempObjExpr->isXValue()));
#if 0
        CXXConstructExpr *Construction =
                 BuildCXXConstructExpr( KWLocation, TargetType, CtorDecl, true, Args,
                                                /*HasMultipleCandidates=*/  false,
                                                /*ListInitialization=*/     false,
                                                /*StdListInitialization=*/  false,
                                                /*ZeroInitialization=*/     true,
                                                CXXConstructExpr::CK_Complete,
                                                SourceRange( KWLocation, KWLocation)).getAs<CXXConstructExpr>();
#endif
        TupleArgs.push_back(E);
    }
    return CreateTupleObject(*this, TupleArgs,  KWLocation);
    return ExprError();
}

