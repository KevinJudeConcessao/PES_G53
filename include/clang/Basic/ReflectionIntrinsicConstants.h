#ifndef LLVM_CLANG_BASIC_REFLECTIONINTRINSICCONSTANTS_H
#define LLVM_CLANG_BASIC_REFLECTIONINTRINSICCONSTANTS_H
enum ReflectionIntrinsicsID {
    RI_Invalid,

    // name properties
    RI_Name,
    RI_IsNamed,

    // type support
    RI_TypeName,

    // context traversal
    RI_ParentDecl,
    RI_ParentLexicalDecl,
    RI_PreviousDecl,
    RI_NextDecl,

    // access specifiers
    RI_AccessSpecifier,

    // source file information
    RI_SourceFile,
    RI_SourceFileStart,
    RI_SourceFileEnd,

    // constants for child decl sequencing support
    RI_Begin,
    RI_End,
    RI_SubSequence,

    // value support
    RI_Value,

    // specifiers
    RI_Specifier
};

enum Specifier {
    RI_IsExtern,
    RI_IsStatic,
    RI_IsMutable,
    RI_IsVirtual,
    RI_IsPureVirtual,
    RI_IsConstExpr
};

enum ClassAccessSpecifier {
    RI_NoAccess,
    RI_Private,
    RI_Public,
    RI_Protected
};

#endif // LLVM_CLANG_BASIC_REFLECTIONINTRINSICCONSTANTS_H
