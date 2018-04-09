#ifndef LLVM_CLANG_AST_REFLECTION_H
#define LLVM_CLANG_AST_REFLECTION_H

#include "clang/AST/Expr.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Type.h"
#include "llvm/ADT/DenseMap.h"

namespace clang {
enum ReflectionKind {
    RK_Empty,
    RK_Decl,
    RK_Type,
    RK_Expression
};

class Reflection {
private:
    ReflectionKind RKind;
    const void *Ptr;
    static Reflection CreateReflection(ReflectionKind RK, const void *Ptr) {
        Reflection NewReflection;
        NewReflection.RKind = RK;
        NewReflection.Ptr   = Ptr;
        return NewReflection;
    }
public:
    Reflection()
        : RKind(RK_Empty), Ptr(nullptr) {}
    Reflection(Decl *D)
        : RKind(RK_Decl), Ptr(D) {}
    Reflection(QualType Ty)
        : RKind(RK_Type), Ptr(Ty.getTypePtr()) {}
    Reflection(Expr *E)
        : RKind(RK_Expression), Ptr(E) {}
    bool IsEmpty() const {
        return RKind == RK_Empty && Ptr == nullptr;
    }
    bool IsDecl() const {
        return RKind == RK_Decl;
    }
    bool IsType() const {
        return RKind == RK_Type;
    }
    bool IsExpression() const {
        return RKind == RK_Expression;
    }
    explicit operator bool() const {
        return IsEmpty();
    }
    ReflectionKind GetKind() const {
        return RKind;
    }
    const void * getOpaquePtr() const {
        return Ptr;
    }
    template<typename T>
    const T* getAs() const {
        return reinterpret_cast<const T*>(Ptr);
    }
    const Decl* getDecl() const {
        assert(IsDecl() && "Not a function/class/struct/enum/"
                           "enum constant Decl");
        return static_cast<const Decl*>(Ptr);
    }
    const Decl* getAsDecl() const {
        return IsDecl() ? getAs<const Decl>() : nullptr;
    }
    const Type* getType() const {
        assert(IsType() && "Not a type");
        return static_cast<const Type*>(Ptr);
    }
    QualType getQualType() const {
        return QualType(getType(), 0);
    }
    const Type* getAsType() const {
        return IsType() ? getAs<const Type>() : nullptr;
    }
    const Expr* getExpr() const {
        assert(IsExpression() && "Not an Expr");
        return static_cast<const Expr*>(Ptr);
    }
    const Expr* getAsExpr() const {
        return IsExpression() ? getAs<Expr>() : nullptr;
    }
};
} // end namespace clang

#endif // LLVM_CLANG_AST_REFLECTION_H
