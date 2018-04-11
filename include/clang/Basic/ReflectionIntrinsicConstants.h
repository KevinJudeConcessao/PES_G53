#ifndef LLVM_CLANG_BASIC_REFLECTIONINTRINSICCONSTANTS_H
#define LLVM_CLANG_BASIC_REFLECTIONINTRINSICCONSTANTS_H

enum ReflectionIntrinsicsID {
    RI_Invalid,
    // constants for all decls
    RI_Name,
    RI_ParentDecl,
    RI_LexicalParentDecl,
    RI_PreviousDecl,
    RI_NextDecl,
    RI_IsComplete,
    RI_SourceFileName,
    RI_SourceFileStart,
    RI_SourceFileEnd,

    // constants for child decl sequencing support
    RI_Begin,
    RI_End,

    // constants for enum support
    RI_Enumerators,
    RI_EnumSize,

    // constants for enum constant support
    RI_EnumConstantValue,
    RI_NumID
};

#endif // LLVM_CLANG_BASIC_REFLECTIONINTRINSICCONSTANTS_H
