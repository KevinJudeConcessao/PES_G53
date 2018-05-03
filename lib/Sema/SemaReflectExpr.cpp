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
    LookupResult Result(S, &S.PP.getIdentifierTable().get(ReflectionSupportClassName), Loc, Sema::LookupTagName);
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

#if 0

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
#endif

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

QualType
Sema::SpecializeClassTemplate(ClassTemplateDecl *TemplateDecl, TemplateArgumentListInfo *TemplateArgs, SourceLocation Loc) {
    if (!TemplateDecl) {
        return QualType();
    }
    SmallVector<TemplateArgument, 4> Converted;
    void *InsertPos = nullptr;
    CheckTemplateArgumentList(TemplateDecl, TemplateDecl->getLocStart(), *TemplateArgs, false, Converted, true);
    ClassTemplateSpecializationDecl* TemplateSpecializationDecl
            = TemplateDecl->findSpecialization(Converted, InsertPos);
    if (!TemplateSpecializationDecl) {
        TemplateSpecializationDecl = ClassTemplateSpecializationDecl::Create(Context,
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
            InstantiateAttrsForDecl(TemplateArgList, TemplateDecl->getTemplatedDecl(), TemplateSpecializationDecl);
        }
    }
    RequireCompleteType(TemplateDecl->getLocation(), Context.getTypeDeclType(TemplateSpecializationDecl),
                          diag::err_incomplete_type);
    return Context.getTemplateSpecializationType(TemplateName(TemplateDecl), *TemplateArgs,
                                                   Context.getTypeDeclType(TemplateSpecializationDecl));
}

static CXXRecordDecl*
LookupStdStringView(Sema &S, SourceLocation Loc) {
    NamespaceDecl *StdNamespaceDecl = S.getStdNamespace();
    if (!StdNamespaceDecl) {
        S.Diag(Loc, diag::err_implied_std_string_view_not_found);
        return nullptr;
    }
    LookupResult StdStringViewResult(S, &S.PP.getIdentifierTable().get("string_view"), Loc,
                                     Sema::LookupNameKind::LookupTagName);
    if (!S.LookupQualifiedName(StdStringViewResult, StdNamespaceDecl)) {
        S.Diag(Loc, diag::err_implied_std_string_view_not_found);
        return nullptr;
    }
    TypedefNameDecl *StdStringViewTypedefDecl = StdStringViewResult.getAsSingle<TypedefNameDecl>();
    QualType StdStringViewType = StdStringViewTypedefDecl->getUnderlyingType();
    return (StdStringViewType.getTypePtr())->getAsCXXRecordDecl();
}

static ClassTemplateDecl*
LookupStdStringLiteral(Sema &S, SourceLocation Loc) {
    NamespaceDecl *StdNamespaceDecl = S.getStdNamespace();
    if (!StdNamespaceDecl) {
        S.Diag(Loc, diag::err_implied_std_string_view_not_found);
        return nullptr;
    }
    LookupResult StdStringLiteralResult(S, &S.PP.getIdentifierTable().get("string_literal"), Loc,
                                     Sema::LookupNameKind::LookupTagName);
    if (!S.LookupQualifiedName(StdStringLiteralResult, StdNamespaceDecl)) {
        S.Diag(Loc, diag::err_implied_std_string_view_not_found);
        return nullptr;
    }
    ClassTemplateDecl *StdStringLiteralTemplate = StdStringLiteralResult.getAsSingle<ClassTemplateDecl>();
    if (!StdStringLiteralTemplate) {
        StdStringLiteralResult.suppressDiagnostics();;
        NamedDecl *Found = *StdStringLiteralResult.begin();
        S.Diag(Found->getLocation(), diag::err_malformed_std_tuple);
        return nullptr;
    }
#if 0
    TemplateParameterList *Parameters = StdStringLiteralTemplate->getTemplateParameters();
    if (Parameters->size() != 1 || !isa<TemplateTypeParmDecl>(Parameters->getParam(0)) ||
            !(llvm::dyn_cast<TemplateTypeParmDecl>(Parameters->getParam(0)))->isParameterPack()) {
        S.Diag(StdStringLiteralTemplate->getLocation(), diag::err_malformed_std_tuple);
        return nullptr;
    }
#endif
    return StdStringLiteralTemplate;
}

CXXRecordDecl *Sema::getStdStringView(SourceLocation Loc) {
    if (!StdStringViewCache) {
        StdStringViewCache = LookupStdStringView(*this, Loc);
    }
    return StdStringViewCache;
}

QualType
Sema::BuildReflectionObjectType(const StringRef &TargetMeta, TemplateArgument IntTemplateArg, SourceLocation Loc) {
    assert(IntTemplateArg.getKind() == TemplateArgument::Integral && "template argument not of integral type !!");
    ClassTemplateDecl *TargetTemplateDecl = LookupStdReflectionDecl(*this, TargetMeta, Loc);
    TemplateArgumentListInfo ArgInfo(Loc, Loc);
    ArgInfo.addArgument(TemplateArgumentLoc(IntTemplateArg, TemplateArgumentLocInfo()));
    return SpecializeClassTemplate(TargetTemplateDecl, &ArgInfo, Loc);
}

QualType
Sema::BuildStdTuple(TemplateArgumentListInfo *TemplateArgs, SourceLocation Loc) {
    if (!StdTupleTemplate) {
        StdTupleTemplate = LookupStdTupleTemplate(*this, Loc);
        if (!StdTupleTemplate)
            return QualType();
    }
    return SpecializeClassTemplate(StdTupleTemplate, TemplateArgs, Loc);
}

QualType
Sema::BuildStdStringLiteral(const llvm::StringRef &String, SourceLocation Loc) {
    if (!StdStringLiteralCache) {
        StdStringLiteralCache = LookupStdStringLiteral(*this, Loc);
        if (!StdStringLiteralCache)
            return QualType();
    }
    TemplateArgumentListInfo TemplateArgs(Loc, Loc);
    for(llvm::StringRef::iterator first = String.begin(), last = String.end(); first != last; ++first) {
        TemplateArgs.addArgument(TemplateArgumentLoc(TemplateArgument(Context, llvm::APSInt(llvm::APInt(sizeof(char) * 8, *first), false), Context.CharTy),
                                                     TemplateArgumentLocInfo()));
    }
    return SpecializeClassTemplate(StdStringLiteralCache, &TemplateArgs, Loc);
}

ExprResult
Sema::CreateStringLiteralObject(QualType Ty, SourceLocation Loc) {
    CXXRecordDecl *StdStringViewSpecDecl = Ty.getTypePtr()->getAsCXXRecordDecl();
    CXXConstructorDecl *CtorDecl = LookupDefaultConstructor(StdStringViewSpecDecl);
    TypeSourceInfo* TInfo = Context.CreateTypeSourceInfo(Ty);
    MarkFunctionReferenced(CtorDecl->getLocation(), CtorDecl);
    CXXConstructExpr *CtorExpr = CXXConstructExpr::Create(Context, Ty, Loc, CtorDecl,
                                                          /*Elidable=*/ false, {},
                                                          /*HadMultipleCandidates=*/ false,
                                                          /*isListInitialization= */ false,
                                                          /*isStdInitListInitialization=*/ false,
                                                          /*RequiresZeroInit=     */ false,
                                                          CXXConstructExpr::CK_Complete, SourceRange(Loc));
    return MaybeBindToTemporary(CtorExpr);
}

ExprResult
Sema::CreateStringViewObject(StringRef String, SourceLocation Loc) {
    CXXRecordDecl *StdStringViewDecl = getStdStringView(Loc);
    if (!StdStringViewDecl)
        return ExprError();
    StringLiteral *NewStringLiteral = CreateStringLiteral(*this, String, Loc);
    IntegerLiteral *NewIntegerLiteral = CreateIntegerLiteral(*this, String.size() + 1, Loc);
    OverloadCandidateSet CtorCandidateSet(Loc, OverloadCandidateSet::CandidateSetKind::CSK_Normal);
    for (auto Ctor : LookupConstructors(StdStringViewDecl)) {
        if (auto FuncDecl = llvm::dyn_cast<FunctionDecl>(Ctor)) {
            AddOverloadCandidate(FuncDecl, DeclAccessPair::make(FuncDecl, Ctor->getAccess()),
            {NewStringLiteral, NewIntegerLiteral}, CtorCandidateSet,
                                   /*SuppressUserConversions=*/ false,
                                   /*PartialOverloading=*/ false);
        }
    }
    OverloadCandidateSet::iterator BestResultPtr;
    OverloadingResult OResult = CtorCandidateSet.BestViableFunction(*this, Loc, BestResultPtr, true);
    assert(OResult == OverloadingResult::OR_Success && "No viable string_view ctor candidates found");
    CXXConstructorDecl *StdStringViewCtorDecl = llvm::dyn_cast<CXXConstructorDecl>(BestResultPtr->Function);
    ParmVarDecl *FirstParm = StdStringViewCtorDecl->getParamDecl(0);
    ParmVarDecl *SecondParm = StdStringViewCtorDecl->getParamDecl(1);
    /*ParmVarDecl *ThirdParm = StdStringViewCtorDecl->getParamDecl(2);*/
    ImplicitCastExpr *FirstArgExpr = ImplicitCastExpr::Create(Context, FirstParm->getType(), CastKind::CK_ArrayToPointerDecay,
                                                              NewStringLiteral, nullptr, ExprValueKind::VK_RValue);
    ImplicitCastExpr *SecondArgExpr = ImplicitCastExpr::Create(Context, SecondParm->getType(), CastKind::CK_IntegralCast,
                                                               NewIntegerLiteral, nullptr, ExprValueKind::VK_RValue);
    /*CXXDefaultArgExpr *ThirdArgExpr = CXXDefaultArgExpr::Create(Context, Loc, ThirdParm);*/
    llvm::ArrayRef<Expr*> Args({ FirstArgExpr, SecondArgExpr, /*ThirdArgExpr*/ });
    QualType Ty = Context.getTypeDeclType(StdStringViewDecl);
    CXXConstructExpr *E = CXXConstructExpr::Create(Context, Ty, Loc, StdStringViewCtorDecl,
                                     /*Elidable=*/ false, Args,
                                     /*HadMultipleCandidates=*/ false,
                                     /*isListInitialization= */ false,
                                     /*isStdInitListInitialization=*/ false,
                                     /*RequiresZeroInit=     */ false,
                                     CXXConstructExpr::CK_Complete, SourceRange(Loc));
    return MaybeBindToTemporary(E);
}

ExprResult
Sema::CreateTupleObject(QualType Ty, llvm::MutableArrayRef<Expr *> Args, SourceLocation Loc) {
    TemplateArgumentListInfo TemplateArgs(Loc, Loc);
    SmallVector<Expr*, 8> Arguments;
    for (Expr *E : Args) {
        TemplateArgs.addArgument(TemplateArgumentLoc(TemplateArgument(E->getType()), Context.CreateTypeSourceInfo(E->getType())));
        Expr *AddedExpr = E;
        if (!llvm::isa<MaterializeTemporaryExpr>(E)) {
            if (!E->isGLValue())
                AddedExpr = CreateMaterializeTemporaryExpr(E->getType(), E, !(E->isRValue() || E->isXValue()));
        }
        Arguments.push_back(AddedExpr);
    }
    QualType StdTupleTy = Ty;
    CXXRecordDecl *StdTupleSpecDecl = StdTupleTy.getTypePtr()->getAsCXXRecordDecl();
    OverloadCandidateSet CtorCandidateSet(SourceLocation(), OverloadCandidateSet::CandidateSetKind::CSK_Normal);
    for (NamedDecl *D : LookupConstructors(StdTupleSpecDecl)) {
        if (FunctionDecl *FDecl = llvm::dyn_cast<FunctionDecl>(D)) {
            AddOverloadCandidate(FDecl, DeclAccessPair::make(FDecl, FDecl->getAccess()), Args, CtorCandidateSet);
        }
        else if (FunctionTemplateDecl *FTDecl = llvm::dyn_cast<FunctionTemplateDecl>(D)) {
            AddTemplateOverloadCandidate(FTDecl, DeclAccessPair::make(FTDecl, FTDecl->getAccess()),
                                           &TemplateArgs, Args, CtorCandidateSet);
        }
    }
    OverloadCandidateSet::iterator BestResultPtr;
    OverloadingResult OResult = CtorCandidateSet.BestViableFunction(*this, SourceLocation(), BestResultPtr, true);
    assert((OResult == OverloadingResult::OR_Success) && "No viable std::tuple ctor candidates found");
    CXXConstructorDecl *CtorDecl = nullptr;
    if (BestResultPtr->Function)
        CtorDecl = llvm::dyn_cast<CXXConstructorDecl>(BestResultPtr->Function);
    TypeSourceInfo* TInfo = Context.CreateTypeSourceInfo(StdTupleTy);
    llvm::SmallVector<Expr*, 8> FinalConverted;
    CompleteConstructorCall(CtorDecl, Args, Loc, FinalConverted, true);
    MarkFunctionReferenced(CtorDecl->getLocation(), CtorDecl);
    CXXTemporaryObjectExpr *TempObjExpr = new (Context) CXXTemporaryObjectExpr(
                Context, CtorDecl, StdTupleTy,
                TInfo, FinalConverted, SourceRange(Loc),
                /*HadMultipleCandidates=*/ false,
                /*isListInitialization= */ false,
                /*isStdInitListInitialization=*/ false,
                /*RequiresZeroInit=     */ false);
    return TempObjExpr;
}

ExprResult
Sema::CreateMetaDeclObject(QualType MetaDeclObjectType, SourceLocation Loc) {
    CXXConstructorDecl *CtorDecl = LookupDefaultConstructor(MetaDeclObjectType->getAsCXXRecordDecl());
    MarkFunctionReferenced(Loc, CtorDecl);
    CXXConstructExpr *E = CXXConstructExpr::Create(Context, MetaDeclObjectType, Loc, CtorDecl,
                                     /*Elidable=*/ false, {},
                                     /*HadMultipleCandidates=*/ false,
                                     /*isListInitialization= */ false,
                                     /*isStdInitListInitialization=*/ false,
                                     /*RequiresZeroInit=     */ false,
                                     CXXConstructExpr::CK_Complete, SourceRange(Loc));
    return MaybeBindToTemporary(E);
}

static TemplateArgument
CreateIntegralTemplateArgument(ASTContext &Context, uint64_t integer) {
    llvm::APInt Int(64, integer, false);
    return TemplateArgument(Context, llvm::APSInt(Int), Context.LongTy);
}

bool
Sema::ActOnReflectionScopedIdentifier(CXXScopeSpec &ScopeSpec, IdentifierInfo *II,
                                      SourceLocation IDLocation, Reflection &Ref) {
    LookupResult Res(*this, DeclarationNameInfo(DeclarationName(II), IDLocation), Sema::LookupAnyName);
    LookupParsedName(Res, getCurScope(), &ScopeSpec);
    if (!Res.isSingleResult()) {
        unsigned DiagID;
        switch (Res.getResultKind()) {
        default:
            llvm_unreachable("Unfounded Lookup for ID in reflect_expr !!");
        case LookupResult::Ambiguous:
            DiagID = diag::err_reflect_expr_id_found_ambiguous;
            break;
        case LookupResult::FoundOverloaded:
        case LookupResult::FoundUnresolvedValue:
            DiagID = diag::err_reflect_expr_id_found_overloaded;
            break;
        case LookupResult::NotFound:
            DiagID = diag::err_reflect_expr_type_id_not_found;
            break;
        }
        Diag(IDLocation, DiagID) << II;
        return false;
    }
    Ref = Reflection(Res.getFoundDecl());
    return true;
}

bool
Sema::ActOnReflectionTypeIdentifier(Declarator &D, Reflection &Ref) {
    TypeSourceInfo *TInfo = GetTypeForDeclarator(D, getCurScope());
    const Type *TyPtr = (TInfo->getType()).getTypePtr();
    Decl *DeclPtr = nullptr;
    /* For our demonstration, we choose decls such as classes, enums, structs, and namespaces
     * getAsTagDecl() will fail if TyPtr refers to functions, arrays, pointers, built-in types, etc */
    Ref = ((DeclPtr = TyPtr->getAsTagDecl()) ? Reflection(DeclPtr) : Reflection(QualType(TyPtr, 0)));
    return true;
}

QualType
Sema::getReflectExprTypeforDecl(const Decl *DeclPtr, SourceLocation Loc) {
    StringRef TargetClassType = "meta_decl";
    if (isa<EnumDecl>(DeclPtr))
        TargetClassType = "meta_enum";
    else if (isa<EnumConstantDecl>(DeclPtr))
        TargetClassType = "meta_enum_constant";
    else if (isa<CXXRecordDecl>(DeclPtr))
        TargetClassType = "meta_record";
    else if (isa<NamespaceDecl>(DeclPtr))
        TargetClassType = "meta_namespace";
    else if (isa<FieldDecl>(DeclPtr))
        TargetClassType = "meta_field";
    else if (isa<CXXMethodDecl>(DeclPtr) && !llvm::dyn_cast<CXXMethodDecl>(DeclPtr)->isStatic())
        TargetClassType = "meta_method";
    else if (isa<FunctionDecl>(DeclPtr))
        TargetClassType = "meta_function";
    else if (isa<ValueDecl>(DeclPtr))
        TargetClassType = "meta_variable";
    TemplateArgument PtrArg = CreateIntegralTemplateArgument(getASTContext(),
                                                                 reinterpret_cast<uint64_t>(DeclPtr));
    return BuildReflectionObjectType(TargetClassType, PtrArg, Loc);
}

QualType
Sema::getInvalidReflectExprTypeForDecl(SourceLocation Loc) {
    StringRef TargetClassType = "meta_decl";
    TemplateArgument PtrArg = CreateIntegralTemplateArgument(getASTContext(), 0);
    return BuildReflectionObjectType(TargetClassType, PtrArg, Loc);
}

namespace {
class TransformReflection : public TreeTransform<TransformReflection> {
   public:
    TransformReflection(Sema &SemaRef) : TreeTransform<TransformReflection>(SemaRef) {}
    bool AlwaysRebuild() { return true; }
    ExprResult TransformReflectionExpr(ReflectionExpr *E) {
        return TreeTransform<TransformReflection>::TransformReflectionExpr(E);
    }
    ExprResult TransformReflectionIntrinsicExpr(ReflectionIntrinsicExpr *E) {
        return TreeTransform<TransformReflection>::TransformReflectionIntrinsicExpr(E);
    }
};
}

ExprResult
Sema::ActOnReflectExprExpression(SourceLocation KWLocation, SourceLocation LParenLocation,
                                 Reflection Ref, SourceLocation RParenLocation) {
    bool IsTypeDependent = false, IsValueDependent = false;
    bool IsInstantiationDependent = false, ContainsUnexpandedParameterPack = false;
    Decl *DeclPtr = nullptr;
    QualType ResultType;
    if (const Type *TyPtr = Ref.getAsType()) {
        /* written for the sake of completeness */
        IsTypeDependent = TyPtr->isDependentType();
        IsValueDependent = TyPtr->isDependentType();
        IsInstantiationDependent = TyPtr->isInstantiationDependentType();
        ContainsUnexpandedParameterPack = TyPtr->containsUnexpandedParameterPack();
        ResultType = Context.DependentTy;
    } else if (const Decl *D = Ref.getAsDecl()) {
        /* Handle items such as fields, enum constants, and methods/constructors/destructors */
        if (const ValueDecl *VDecl = llvm::dyn_cast<ValueDecl>(D)) {
            DeclRefExpr *DRExpr = new (Context) DeclRefExpr(const_cast<ValueDecl*>(VDecl), /*RefersToEnclosingVariableOrCapture=*/ false,
                                                            VDecl->getType(), ExprValueKind::VK_RValue, KWLocation);
            IsTypeDependent = DRExpr->isValueDependent();
            IsValueDependent = DRExpr->isValueDependent();
            IsInstantiationDependent = DRExpr->isInstantiationDependent();
            ContainsUnexpandedParameterPack = DRExpr->containsUnexpandedParameterPack();
        }
        else if (const TypeDecl *TDecl = llvm::dyn_cast<TypeDecl>(D)) {
            const Type *TyPtr = TDecl->getTypeForDecl();
            IsTypeDependent = TyPtr->isDependentType();
            IsValueDependent = TyPtr->isDependentType();
            IsInstantiationDependent = TyPtr->isInstantiationDependentType();
            ContainsUnexpandedParameterPack = TyPtr->containsUnexpandedParameterPack();
        }
        else if (const NamedDecl *NDecl = llvm::dyn_cast<NamedDecl>(D)) {
            /* This is required to handle other named-decls like namespaces
             * Expression dependencies are rightfully false at this point.
             * DO NOTHING !!! */
        }
        DeclPtr = const_cast<Decl*>(D);
        ResultType = getReflectExprTypeforDecl(DeclPtr, KWLocation);
    }
    return new (Context) ReflectionExpr(KWLocation, LParenLocation, RParenLocation, Ref, ResultType,
                                        IsTypeDependent, IsValueDependent, IsInstantiationDependent,
                                        ContainsUnexpandedParameterPack);
}

ExprResult
Sema::ActOnReflectionIntrinsicExpression(SourceLocation KWLoc, SourceLocation LParenLoc,
                                        llvm::SmallVector<Expr*, 2> IntrinsicArgs, SourceLocation RParenLoc) {
    QualType ResultTy;
    llvm::APSInt IntrinsicID;
    SmallVector<Expr*, 2> TransformedArgs;
    for (Expr* Arg: IntrinsicArgs) {
        Expr *TransformedArg = Arg;
        if (TransformedArg->isGLValue()) {
            TransformedArg = ImplicitCastExpr::Create(Context, TransformedArg->getType(), CastKind::CK_LValueToRValue,
                                                      TransformedArg, nullptr, VK_RValue);
        }
        TransformedArgs.push_back(TransformedArg);
    }
    TransformedArgs[0]->EvaluateAsInt(IntrinsicID, Context);
    switch (static_cast<ReflectionIntrinsicsID>(IntrinsicID.getExtValue())) {
        default:
            llvm_unreachable("Unknown reflection intrinsic ID");
        break;
        /* name properties */
        case RI_Name:
            ResultTy = Context.DependentTy;
            break;
        case RI_IsNamed:
            ResultTy = Context.BoolTy;
            break;
         /* type support */
        case RI_TypeName:
            ResultTy = Context.DependentTy;
            break;
        /* context traversal */
        case RI_ParentDecl:
        case RI_ParentLexicalDecl:
        case RI_PreviousDecl:
        case RI_NextDecl:
            ResultTy = Context.DependentTy;
            break;
        /* access specifiers */
        case RI_AccessSpecifier:
            ResultTy = Context.IntTy;
            break;
        /* source file information */
        case RI_SourceFile:
            ResultTy = Context.getTagDeclType(getStdStringView(KWLoc));
            break;
        case RI_SourceFileStart:
        case RI_SourceFileEnd: {
                TemplateArgumentListInfo ArgInfo;
                ArgInfo.addArgument(TemplateArgumentLoc(TemplateArgument(Context.IntTy),
                                                        Context.getTrivialTypeSourceInfo(Context.IntTy)));
                ArgInfo.addArgument(TemplateArgumentLoc(TemplateArgument(Context.IntTy),
                                                        Context.getTrivialTypeSourceInfo(Context.IntTy)));
                ResultTy = BuildStdTuple(&ArgInfo, KWLoc);
            }
            break;
        /* children sequencing support */
        case RI_Begin:
        case RI_End:
        case RI_SubSequence:
            ResultTy = Context.DependentTy;
            break;
        /* value support */
        case RI_Value:
            ResultTy = Context.DependentTy;
            break;
        /* specifiers */
        case RI_Specifier:
            ResultTy = Context.IntTy;
            break;
    }
    return new (Context) ReflectionIntrinsicExpr(Context, KWLoc, LParenLoc, RParenLoc, TransformedArgs, ResultTy);
}

ExprResult
Sema::ActOnStrLitExpression(const llvm::StringRef& String, SourceLocation Loc) {
    QualType Ty = BuildStdStringLiteral(String, Loc);
    return CreateStringLiteralObject(Ty, Loc);
}

bool
Sema::isStdStringLiteral(QualType Ty, SourceLocation Loc) {
   assert(getLangOpts().CPlusPlus && "Looking for std::string_literal<char...> outside of C++.");
   if (!StdNamespace)
       return false;
   ClassTemplateDecl *Template = nullptr;
   if (const RecordType *RTy = Ty->getAs<RecordType>()) {
       ClassTemplateSpecializationDecl *Spec = llvm::dyn_cast<ClassTemplateSpecializationDecl>(RTy->getDecl());
       if (!Spec)
         return false;
       Template = Spec->getSpecializedTemplate();
   }
   else if (const TemplateSpecializationType *TSTy = Ty->getAs<TemplateSpecializationType>())
       Template = llvm::dyn_cast_or_null<ClassTemplateDecl>(TSTy->getTemplateName().getAsTemplateDecl());
   if (!Template)
       return false;
   if (!StdStringLiteralCache)
       StdStringLiteralCache = LookupStdStringLiteral(*this, Loc);
   if (Template->getCanonicalDecl() != StdStringLiteralCache->getCanonicalDecl())
       return false;
   return true;
}

ExprResult
Sema::ActOnIdExprExpression(llvm::ArrayRef<Expr*> IdExprParts, SourceLocation Loc) {
    bool TypeDependent = false;
    bool InstantiationDependent = false;
    bool ValueDependent = false;
    bool UnexpandedPack = false;
    for (Expr * IdExprPart : IdExprParts) {
        if (IdExprPart->isTypeDependent())
            TypeDependent = true;
        if (IdExprPart->isInstantiationDependent())
            InstantiationDependent = true;
        if (IdExprPart->isValueDependent())
            ValueDependent = true;
        if (IdExprPart->containsUnexpandedParameterPack())
            UnexpandedPack = true;
    }

    if (TypeDependent || InstantiationDependent || ValueDependent || UnexpandedPack){
            llvm ::outs() << "Inside idexpr";
            return new (Context) IdExprExpr(IdExprParts, Loc, Context.DependentTy, TypeDependent, ValueDependent, InstantiationDependent, UnexpandedPack);
    }    
    return BuildIdExprExpression(IdExprParts, Loc);
}

ExprResult
Sema::BuildIdExprExpression(llvm::ArrayRef<Expr*> IdExprParts, SourceLocation Loc) {
    llvm::SmallVector<char, 16> IdNameCharacters;
    for (Expr *E: IdExprParts) {
        E->dump();
        if (StringLiteral *S = llvm::dyn_cast<StringLiteral>(E)) {
            StringRef String = S->getString();
            for (char c: String) {
                if(c == 0)
                    llvm::outs() << "NULL";
                else llvm::outs() << c;
            }
            std::transform(String.begin(), String.end(), std::back_inserter(IdNameCharacters),
                           [](char Character) -> char { return Character; });
        }
        else if (E->isIntegerConstantExpr(Context)) {
            llvm::APSInt Integer = llvm::APSInt::get(0);
            E->EvaluateAsInt(Integer, Context);
            std::string StringRep = Integer.toString(10);;
            std::transform(StringRep.begin(), StringRep.end(), std::back_inserter(IdNameCharacters),
                  [](char Character) -> char { return Character; });
        }
        else if (isStdStringLiteral(E->getType(), Loc)) {
            llvm::ArrayRef<TemplateArgument> TemplateArgs;
            QualType Ty = E->getType();
            if (const TemplateSpecializationType *TSTy = Ty->getAs<TemplateSpecializationType>())
                TemplateArgs = TSTy->template_arguments();
            else if (const RecordType *Rty = Ty->getAs<RecordType>()) {
                ClassTemplateSpecializationDecl *Spec = llvm::dyn_cast<ClassTemplateSpecializationDecl>(Rty->getDecl());
                TemplateArgs = Spec->getTemplateArgs().get(0).getPackAsArray();
            }
            std::transform(TemplateArgs.begin(), TemplateArgs.end(), std::back_inserter(IdNameCharacters),
                           [](TemplateArgument Argument) -> char { return static_cast<char>(Argument.getAsIntegral().getExtValue()); });
        }
        else if (DeclRefExpr *D = llvm::dyn_cast<DeclRefExpr>(E)) {
            StringRef String = D->getDecl()->getName();
            std::transform(String.begin(), String.end(), std::back_inserter(IdNameCharacters),
                           [](char Character) { return Character; });
        } else {
            return ExprError();
        }
    }
    llvm::StringRef Id(std::string(IdNameCharacters.begin(), IdNameCharacters.end()));
    LookupResult IdResult(*this, &PP.getIdentifierTable().get(Id), Loc,
                                Sema::LookupNameKind::LookupOrdinaryName);
    LookupName(IdResult, getCurScope());
    if (!IdResult.isSingleResult())
        return ExprError(Diag(Loc, diag::err_undeclared_var_use) << Id);
    ValueDecl *VD = IdResult.getAsSingle<ValueDecl>();
    DeclRefExpr *E = new (Context) DeclRefExpr(VD, false, VD->getType(), ExprValueKind::VK_LValue, Loc);
    MarkDeclRefReferenced(E);
    return E;
}
