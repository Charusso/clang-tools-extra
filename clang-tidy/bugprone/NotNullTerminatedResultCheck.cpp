//===--- NotNullTerminatedResultCheck.cpp - clang-tidy ----------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "NotNullTerminatedResultCheck.h"
#include "clang/AST/ASTContext.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Lex/Lexer.h"
#include "clang/Lex/PPCallbacks.h"

using namespace clang::ast_matchers;

namespace clang {
namespace tidy {
namespace bugprone {

static const char *const FuncExprName = "entire-called-function-expr";
static const char *const CastExprName = "cast-expr";
static const char *const UnknownDestName = "destination-length-is-unknown";
static const char *const NotJustCharTyName = "unsigned-or-signed-char";
static const char *const DestArrayTyName = "destination-is-array-type";
static const char *const DestVarDeclName = "destination-variable-declaration";
static const char *const SrcVarDeclName = "source-variable-declaration";
static const char *const UnknownLengthName = "given-length-is-unknown";
static const char *const BinOpName = "has-binary-operator";
static const char *const WrongLengthExprName = "strlen-or-size";
static const char *const DestMallocExprName = "destination-malloc-expr";
static const char *const DestExprName = "destination-decl-ref-expr";
static const char *const SrcExprName = "source-expression-or-string-literal";
static const char *const LengthExprName = "given-length-expression";

enum class LengthHandleKind { LH_Increase, LH_Decrease };

namespace {
static bool IsInjectUL = false;
static std::map<StringRef, int> MacroDefinedMap;

class SimpleMacroPPCallbacks : public PPCallbacks {
public:
  void MacroDefined(const Token &MacroNameTok,
                    const MacroDirective *MD) override;
};
} // namespace

void SimpleMacroPPCallbacks::MacroDefined(const Token &MacroNameTok,
                                          const MacroDirective *MD) {
  const MacroInfo *MI = MD->getMacroInfo();
  if (MI->isBuiltinMacro())
    return;

  if (!MI->tokens().size())
    return;

  const auto &T = MI->tokens().back();
  if (T.isLiteral()) {
    StringRef ValueStr = StringRef(T.getLiteralData(), T.getLength());
    llvm::APInt IntValue;
    ValueStr.getAsInteger(10, IntValue);

    StringRef MacroName = MacroNameTok.getIdentifierInfo()->getName();
    MacroDefinedMap[MacroName] = IntValue.getZExtValue();
  }
}

static SourceLocation exprLocEnd(const Expr *E,
                                 const MatchFinder::MatchResult &Result) {
  return Lexer::getLocForEndOfToken(E->getLocEnd(), 0, *Result.SourceManager,
                                    Result.Context->getLangOpts());
}

static StringRef exprToStr(const Expr *E,
                           const MatchFinder::MatchResult &Result) {
  if (!E)
    return "";

  return Lexer::getSourceText(
      CharSourceRange::getTokenRange(E->getSourceRange()),
      *Result.SourceManager, Result.Context->getLangOpts(), 0);
}

static bool isKnownDest(const MatchFinder::MatchResult &Result) {
  return !Result.Nodes.getNodeAs<Expr>(UnknownDestName);
}

static bool isDestAndSrcEquals(const MatchFinder::MatchResult &Result) {
  if (const auto DestVD = Result.Nodes.getNodeAs<Decl>(DestVarDeclName))
    if (const auto *SrcVD = Result.Nodes.getNodeAs<Decl>(SrcVarDeclName))
      return DestVD->getCanonicalDecl() == SrcVD->getCanonicalDecl();

  return false;
}

static const Expr *getDestExpr(const MatchFinder::MatchResult &Result) {
  return Result.Nodes.getNodeAs<Expr>(DestExprName);
}

static const Expr *getSrcExpr(const MatchFinder::MatchResult &Result) {
  return Result.Nodes.getNodeAs<Expr>(SrcExprName);
}

static const Expr *getLengthExpr(const MatchFinder::MatchResult &Result) {
  return Result.Nodes.getNodeAs<Expr>(LengthExprName);
}

static bool isGivenLengthEQToSrcLength(const MatchFinder::MatchResult &Result);
static bool isNoWrongLength(const MatchFinder::MatchResult &Result) {
  if (Result.Nodes.getNodeAs<IntegerLiteral>(WrongLengthExprName))
    return !isGivenLengthEQToSrcLength(Result);
 
  return !Result.Nodes.getNodeAs<Expr>(WrongLengthExprName);
}

static const Expr *getDestCapacityExpr(const MatchFinder::MatchResult &Result) {
  if (const auto *DestMalloc = Result.Nodes.getNodeAs<Expr>(DestMallocExprName))
    return DestMalloc;

  if (const auto DestTy = Result.Nodes.getNodeAs<ArrayType>(DestArrayTyName))
    if (const auto *DestVAT = dyn_cast_or_null<VariableArrayType>(DestTy))
      return DestVAT->getSizeExpr();

  if (const auto *DestVD = Result.Nodes.getNodeAs<VarDecl>(DestVarDeclName))
    if (const auto DestTL = DestVD->getTypeSourceInfo()->getTypeLoc())
      if (const auto DestCTL = DestTL.getAs<ConstantArrayTypeLoc>())
        return DestCTL.getSizeExpr();

  return nullptr;
}

static int getLength(const Expr *E, const MatchFinder::MatchResult &Result) {
  llvm::APSInt Length;

  if (const auto *LengthDRE = dyn_cast_or_null<DeclRefExpr>(E))
    if (const auto *LengthVD = dyn_cast_or_null<VarDecl>(LengthDRE->getDecl()))
      if (!isa<ParmVarDecl>(LengthVD))
        if (const auto *LengthInit = LengthVD->getInit())
          if (LengthInit->EvaluateAsInt(Length, *Result.Context))
            return Length.getZExtValue();

  if (const auto *LengthIL = dyn_cast_or_null<IntegerLiteral>(E))
    return LengthIL->getValue().getZExtValue();

  if (const auto *StrDRE = dyn_cast_or_null<DeclRefExpr>(E))
    if (const auto *StrVD = dyn_cast_or_null<VarDecl>(StrDRE->getDecl()))
      if (const auto *StrInit = StrVD->getInit())
        if (const auto *StrSL =
                dyn_cast_or_null<StringLiteral>(StrInit->IgnoreImpCasts()))
          return StrSL->getLength();

  if (const auto *SrcSL = dyn_cast_or_null<StringLiteral>(E))
    return SrcSL->getLength();

  return 0;
}

static int getDestCapacity(const MatchFinder::MatchResult &Result) {
  if (const auto *DestCapacityExpr = getDestCapacityExpr(Result))
    return getLength(DestCapacityExpr, Result);

  return 0;
}

static int getGivenLength(const MatchFinder::MatchResult &Result) {
  const auto *LengthExpr = Result.Nodes.getNodeAs<Expr>(LengthExprName);
  if (const int Length = getLength(LengthExpr, Result))
    return Length;

  if (const auto *Strlen = dyn_cast_or_null<CallExpr>(LengthExpr))
    if (Strlen->getNumArgs() > 0)
      if (const auto *StrlenArg = Strlen->getArg(0)->IgnoreImpCasts())
        if (const int StrlenArgLength = getLength(StrlenArg, Result))
          return StrlenArgLength;

  return 0;
}

//===---------------------------------------------------------------------===//
//                      Rewrite decision helper functions
//===---------------------------------------------------------------------===//

static bool isStringDataAndLength(const MatchFinder::MatchResult &Result) {
  StringRef DestStr = exprToStr(getDestExpr(Result), Result);
  StringRef SrcStr = exprToStr(getSrcExpr(Result), Result);
  StringRef GivenLengthStr = exprToStr(getLengthExpr(Result), Result);

  const bool ProblematicLength =
      GivenLengthStr.contains(".size") || GivenLengthStr.contains(".length");

  return ProblematicLength &&
         (SrcStr.contains(".data") || DestStr.contains(".data"));
}

static bool isGivenLengthEQToSrcLength(const MatchFinder::MatchResult &Result) {
  if (isStringDataAndLength(Result))
    return true;

  const int GivenLength = getGivenLength(Result);

  // It is the length without the null terminator.
  const int SrcLength = getLength(getSrcExpr(Result), Result);

  if (GivenLength != 0 && GivenLength == SrcLength)
    return true;

  // If 'strlen()' check if the VarDecl of the argument is equal to SrcVarDecl.
  if (const auto *StrlenExpr = Result.Nodes.getNodeAs<CallExpr>(LengthExprName))
    if (StrlenExpr->getNumArgs() > 0)
      if (const auto *StrlenDRE = dyn_cast_or_null<DeclRefExpr>(
              StrlenExpr->getArg(0)->IgnoreImpCasts()))
        return dyn_cast_or_null<VarDecl>(StrlenDRE->getDecl()) ==
               Result.Nodes.getNodeAs<VarDecl>(SrcVarDeclName);

  return false;
}

static bool isDestCapacityOverflows(const MatchFinder::MatchResult &Result) {
  if (!isKnownDest(Result))
    return true;

  // Assume that it cannot overflow if the destination length contains '+ 1'.
  if (Result.Nodes.getNodeAs<BinaryOperator>(BinOpName))
    return false;

  const auto *DestCapacityExpr = getDestCapacityExpr(Result);
  const auto *LengthExpr = getLengthExpr(Result);
  const int DestCapacity = getLength(DestCapacityExpr, Result);
  const int GivenLength = getGivenLength(Result);

  if (GivenLength != 0 && DestCapacity != 0)
    return isGivenLengthEQToSrcLength(Result) && DestCapacity == GivenLength;

  StringRef DestCapacityExprStr = exprToStr(DestCapacityExpr, Result);
  StringRef LengthExprStr = exprToStr(LengthExpr, Result);
  if (DestCapacityExprStr != "" && DestCapacityExprStr == LengthExprStr)
    return true;

  if (const auto DestTy = Result.Nodes.getNodeAs<ArrayType>(DestArrayTyName))
    if (const auto *DestVAT = dyn_cast_or_null<VariableArrayType>(DestTy)) {
      StringRef SizeExprStr = exprToStr(DestVAT->getSizeExpr(), Result);
      if (SizeExprStr.contains("+1") || SizeExprStr.contains("+ 1"))
        return false;
    }

  return true;
}

// True if the capacity of the destination array is based on the given length,
// therefore it looks like it cannot overflow.
static bool isProperDestCapacity(const MatchFinder::MatchResult &Result) {
  StringRef DestCapacityExprStr =
      exprToStr(getDestCapacityExpr(Result), Result).trim(' ');
  StringRef LengthExprStr = exprToStr(getLengthExpr(Result), Result).trim(' ');

  return DestCapacityExprStr != "" && LengthExprStr != "" &&
         DestCapacityExprStr.contains(LengthExprStr);
}

//===---------------------------------------------------------------------===//
//                        Code injection functions
//===---------------------------------------------------------------------===//

static void lengthDecrease(const Expr *LengthExpr,
                           const MatchFinder::MatchResult &Result,
                           DiagnosticBuilder &Diag) {
  // This is the following structure: ((strlen(src) * 2) + 1)
  //                     InnerOpExpr:   ~~~~~~~~~~~~^~~
  //                     OuterOpExpr:  ~~~~~~~~~~~~~~~~~~^~~
  if (const auto *OuterOpExpr =
          dyn_cast_or_null<BinaryOperator>(LengthExpr->IgnoreParenCasts())) {
    const auto *LHSExpr = OuterOpExpr->getLHS();
    const auto *RHSExpr = OuterOpExpr->getRHS();
    const auto *InnerOpExpr =
        isa<IntegerLiteral>(RHSExpr->IgnoreCasts()) ? LHSExpr : RHSExpr;

    // This is the following structure: ((strlen(src) * 2) + 1)
    //                  LHSRemoveRange: ~~
    //                  RHSRemoveRange:                  ~~~~~~
    const auto LHSRemoveRange =
        SourceRange(LengthExpr->getLocStart(),
                    InnerOpExpr->getLocStart().getLocWithOffset(-1));
    const auto RHSRemoveRange =
        SourceRange(exprLocEnd(InnerOpExpr, Result), LengthExpr->getLocEnd());
    const auto LHSRemoveFix = FixItHint::CreateRemoval(LHSRemoveRange);
    const auto RHSRemoveFix = FixItHint::CreateRemoval(RHSRemoveRange);

    if (LengthExpr->getLocStart() == InnerOpExpr->getLocStart())
      Diag << RHSRemoveFix;
    else if (LengthExpr->getLocEnd() == InnerOpExpr->getLocEnd())
      Diag << LHSRemoveFix;
    else
      Diag << LHSRemoveFix << RHSRemoveFix;
  } else {
    const auto InsertDecreaseFix =
        FixItHint::CreateInsertion(exprLocEnd(LengthExpr, Result), " - 1");
    Diag << InsertDecreaseFix;
  }
}

static void lengthIncrease(const Expr *LengthExpr,
                           const MatchFinder::MatchResult &Result,
                           DiagnosticBuilder &Diag) {
  const bool NeedInnerParen =
      dyn_cast_or_null<BinaryOperator>(LengthExpr) &&
      cast<BinaryOperator>(LengthExpr)->getOpcode() != BO_Add;

  if (NeedInnerParen) {
    const auto InsertFirstParenFix =
        FixItHint::CreateInsertion(LengthExpr->getLocStart(), "(");
    const auto InsertPlusOneAndSecondParenFix = FixItHint::CreateInsertion(
        exprLocEnd(LengthExpr, Result), !IsInjectUL ? ") + 1" : ") + 1UL");
    Diag << InsertFirstParenFix << InsertPlusOneAndSecondParenFix;
  } else {
    const auto InsertPlusOne = FixItHint::CreateInsertion(
        exprLocEnd(LengthExpr, Result), !IsInjectUL ? " + 1" : " + 1UL");
    Diag << InsertPlusOne;
  }
}

static void lengthExprHandle(LengthHandleKind LengthHandle,
                             const Expr *LengthExpr,
                             const MatchFinder::MatchResult &Result,
                             DiagnosticBuilder &Diag) {
  if (!LengthExpr)
    return;

  const auto It = MacroDefinedMap.find(exprToStr(LengthExpr, Result));
  if (It == MacroDefinedMap.end()) {
    if (const auto *LengthIL = dyn_cast_or_null<IntegerLiteral>(LengthExpr)) {
      const size_t NewLength = LengthIL->getValue().getZExtValue() +
                               (LengthHandle == LengthHandleKind::LH_Increase
                                    ? (IsInjectUL ? 1UL : 1)
                                    : -1);
      const auto NewLengthFix = FixItHint::CreateReplacement(
          LengthIL->getSourceRange(),
          (Twine(NewLength) + (IsInjectUL ? "UL" : "")).str());
      Diag << NewLengthFix;
      return;
    }

    if (LengthHandle == LengthHandleKind::LH_Increase)
      lengthIncrease(LengthExpr, Result, Diag);
    else
      lengthDecrease(LengthExpr, Result, Diag);
  } else {
    if (LengthHandle == LengthHandleKind::LH_Increase) {
      const auto InsertPlusOne = FixItHint::CreateInsertion(
          exprLocEnd(LengthExpr, Result), !IsInjectUL ? " + 1" : " + 1UL");
      Diag << InsertPlusOne;
    } else {
      const auto InsertMinusOne =
          FixItHint::CreateInsertion(exprLocEnd(LengthExpr, Result), " - 1");
      Diag << InsertMinusOne;
    }
  }
}

static void lengthArgHandle(LengthHandleKind LengthHandle, int ArgPos,
                            const MatchFinder::MatchResult &Result,
                            DiagnosticBuilder &Diag) {
  const auto *FuncExpr = Result.Nodes.getNodeAs<CallExpr>(FuncExprName);
  const auto *LengthExpr = FuncExpr->getArg(ArgPos)->IgnoreImpCasts();
  lengthExprHandle(LengthHandle, LengthExpr, Result, Diag);
}

static bool destCapacityFix(const MatchFinder::MatchResult &Result,
                            DiagnosticBuilder &Diag) {
  const bool IsOverflows = isDestCapacityOverflows(Result);
  if (IsOverflows)
    lengthExprHandle(LengthHandleKind::LH_Increase, getDestCapacityExpr(Result),
                     Result, Diag);

  return IsOverflows;
}

static void removeArg(int ArgPos, const MatchFinder::MatchResult &Result,
                      DiagnosticBuilder &Diag) {
  // This is the following structure: (src, '\0', strlen(src))
  //                     ArgToRemove:             ~~~~~~~~~~~
  //                          LHSArg:       ~~~~
  //                    RemoveArgFix:           ~~~~~~~~~~~~~
  const auto *FuncExpr = Result.Nodes.getNodeAs<CallExpr>(FuncExprName);
  const auto ArgToRemove = FuncExpr->getArg(ArgPos);
  const auto LHSArg = FuncExpr->getArg(ArgPos - 1);
  const auto RemoveArgFix = FixItHint::CreateRemoval(
      SourceRange(exprLocEnd(LHSArg, Result),
                  exprLocEnd(ArgToRemove, Result).getLocWithOffset(-1)));
  Diag << RemoveArgFix;
}

static void renameFunc(StringRef NewFuncName,
                       const MatchFinder::MatchResult &Result,
                       DiagnosticBuilder &Diag) {
  const auto *FuncExpr = Result.Nodes.getNodeAs<CallExpr>(FuncExprName);
  const int FuncNameLength =
      FuncExpr->getDirectCallee()->getIdentifier()->getLength();
  const auto FuncNameRange =
      SourceRange(FuncExpr->getLocStart(),
                  FuncExpr->getLocStart().getLocWithOffset(FuncNameLength - 1));

  const auto FuncNameFix =
      FixItHint::CreateReplacement(FuncNameRange, NewFuncName);
  Diag << FuncNameFix;
}

static void insertDestCapacityArg(bool IsOverflows, StringRef Name,
                                  const MatchFinder::MatchResult &Result,
                                  DiagnosticBuilder &Diag) {
  const auto *FuncExpr = Result.Nodes.getNodeAs<CallExpr>(FuncExprName);
  SmallString<64> NewSecondArg;

  if (const int DestLength = getDestCapacity(Result)) {
    NewSecondArg = Twine(IsOverflows ? DestLength + 1 : DestLength).str();
  } else {
    NewSecondArg = exprToStr(getDestCapacityExpr(Result), Result);
    NewSecondArg += IsOverflows ? (!IsInjectUL ? " + 1" : " + 1UL") : "";
  }

  NewSecondArg += ", ";
  const auto InsertNewArgFix = FixItHint::CreateInsertion(
      FuncExpr->getArg(1)->getLocStart(), NewSecondArg);
  Diag << InsertNewArgFix;
}

static void insertNullTerminatorExpr(StringRef Name,
                                     const MatchFinder::MatchResult &Result,
                                     DiagnosticBuilder &Diag) {
  const auto *FuncExpr = Result.Nodes.getNodeAs<CallExpr>(FuncExprName);
  const int FuncLocStartColumn =
      Result.SourceManager->getPresumedColumnNumber(FuncExpr->getLocStart());
  const auto SpaceRange = SourceRange(
      FuncExpr->getLocStart().getLocWithOffset(-FuncLocStartColumn + 1),
      FuncExpr->getLocStart());
  StringRef SpaceBeforeStmtStr = Lexer::getSourceText(
      CharSourceRange::getCharRange(SpaceRange), *Result.SourceManager,
      Result.Context->getLangOpts(), 0);

  SmallString<128> NewAddNullTermExprStr;
  NewAddNullTermExprStr = "\n";
  NewAddNullTermExprStr += SpaceBeforeStmtStr;
  NewAddNullTermExprStr += exprToStr(getDestExpr(Result), Result);
  NewAddNullTermExprStr += "[";
  NewAddNullTermExprStr += exprToStr(getLengthExpr(Result), Result);
  NewAddNullTermExprStr += "] = ";
  NewAddNullTermExprStr += (Name[0] != 'w') ? "\'\\0\';" : "L\'\\0\';";

  const auto AddNullTerminatorExprFix = FixItHint::CreateInsertion(
      exprLocEnd(FuncExpr, Result).getLocWithOffset(1), NewAddNullTermExprStr);
  Diag << AddNullTerminatorExprFix;
}

NotNullTerminatedResultCheck::NotNullTerminatedResultCheck(
    StringRef Name, ClangTidyContext *Context)
    : ClangTidyCheck(Name, Context),
      AreSafeFunctionsAvailable(Options.get("AreSafeFunctionsAvailable", "")) {
  if (AreSafeFunctionsAvailable == "" || AreSafeFunctionsAvailable[0] == 'd' ||
      AreSafeFunctionsAvailable[0] == 'D')
    SafeFunctionsAvailable = SafeFunctionsAvailableKind::Default;
  else if (AreSafeFunctionsAvailable[0] == 'y' ||
           AreSafeFunctionsAvailable[0] == 'Y')
    SafeFunctionsAvailable = SafeFunctionsAvailableKind::Yes;
  else if (AreSafeFunctionsAvailable[0] == 'n' ||
           AreSafeFunctionsAvailable[0] == 'N')
    SafeFunctionsAvailable = SafeFunctionsAvailableKind::No;
  else
    SafeFunctionsAvailable = atoi(AreSafeFunctionsAvailable.c_str())
                                 ? SafeFunctionsAvailableKind::Yes
                                 : SafeFunctionsAvailableKind::No;
}

void NotNullTerminatedResultCheck::storeOptions(
    ClangTidyOptions::OptionMap &Opts) {
  Options.store(Opts, "AreSafeFunctionsAvailable", AreSafeFunctionsAvailable);
}

void NotNullTerminatedResultCheck::registerPPCallbacks(
    CompilerInstance &Compiler) {
  Compiler.getPreprocessor().addPPCallbacks(
      llvm::make_unique<SimpleMacroPPCallbacks>());
}

namespace {
AST_MATCHER_P(Expr, hasDefinition, ast_matchers::internal::Matcher<Expr>,
              InnerMatcher) {
  const Expr *SimpleNode = &Node;
  SimpleNode = SimpleNode->IgnoreParenCasts()->IgnoreImpCasts();

  if (InnerMatcher.matches(*SimpleNode, Finder, Builder))
    return true;

  const auto DREHasInit = ignoringImpCasts(
      declRefExpr(to(varDecl(hasInitializer(ignoringImpCasts(InnerMatcher))))));

  if (DREHasInit.matches(*SimpleNode, Finder, Builder))
    return true;

  // - Example:  int getLength(const char *str) { return strlen(str); }
  const auto CallExprReturnInit = ignoringImpCasts(
      callExpr(callee(functionDecl(hasBody(has(returnStmt(hasReturnValue(
          ignoringImpCasts(anyOf(DREHasInit, InnerMatcher))))))))));

  if (CallExprReturnInit.matches(*SimpleNode, Finder, Builder))
    return true;

  // - Example:  int length = getLength(src);
  const auto DREHasReturnInit = ignoringImpCasts(
      declRefExpr(to(varDecl(hasInitializer(CallExprReturnInit)))));

  if (DREHasReturnInit.matches(*SimpleNode, Finder, Builder))
    return true;
  
  const char *const VarDeclName = "variable-declaration";
  const auto DREHasDefinition = ignoringImpCasts(declRefExpr(
      allOf(to(varDecl().bind(VarDeclName)),
            hasAncestor(compoundStmt(hasDescendant(binaryOperator(
                hasLHS(declRefExpr(to(varDecl(equalsBoundNode(VarDeclName))))),
                hasRHS(ignoringImpCasts(InnerMatcher)))))))));

  if (DREHasDefinition.matches(*SimpleNode, Finder, Builder))
    return true;

  return false;
}
} // namespace

void NotNullTerminatedResultCheck::registerMatchers(MatchFinder *Finder) {
  const auto IncOp =
      binaryOperator(hasOperatorName("+"),
                     hasEitherOperand(ignoringParenImpCasts(integerLiteral())))
          .bind(BinOpName);

  const auto DecOp =
      binaryOperator(hasOperatorName("-"),
                     hasEitherOperand(ignoringParenImpCasts(integerLiteral())));

  const auto HasIncOp = anyOf(ignoringImpCasts(IncOp), hasDescendant(IncOp));
  const auto HasDecOp = anyOf(ignoringImpCasts(DecOp), hasDescendant(DecOp));

  const auto StringTy = type(hasUnqualifiedDesugaredType(recordType(
      hasDeclaration(cxxRecordDecl(hasName("::std::basic_string"))))));

  const auto AnyOfStringTy =
      anyOf(hasType(StringTy), hasType(qualType(pointsTo(StringTy))));

  const auto CharTy =
      anyOf(asString("char"), asString("wchar_t"),
            allOf(anyOf(asString("unsigned char"), asString("signed char")),
                  type().bind(NotJustCharTyName)));

  const auto CharTyArray = hasType(qualType(hasCanonicalType(
      arrayType(hasElementType(CharTy)).bind(DestArrayTyName))));

  const auto CharTyPointer =
      hasType(qualType(hasCanonicalType(pointerType(pointee(CharTy)))));

  const auto AnyOfCharTy = anyOf(CharTyArray, CharTyPointer);

  //===--------------------------------------------------------------------===//
  // The following six case match problematic length expressions
  //===--------------------------------------------------------------------===//

  // - Example:  char src[] = "foo";       strlen(src);
  const auto Strlen =
      callExpr(callee(functionDecl(hasAnyName("::strlen", "::wcslen"))))
          .bind(WrongLengthExprName);

  // - Example:  std::string str = "foo";  str.size();
  const auto SizeOrLength =
      cxxMemberCallExpr(
          allOf(on(expr(AnyOfStringTy)),
                has(memberExpr(member(hasAnyName("size", "length"))))))
          .bind(WrongLengthExprName);

  // - Example:  char src[] = "foo";       sizeof(src);
  const auto SizeOfCharExpr =
      unaryExprOrTypeTraitExpr(has(expr(hasType(qualType(
          hasCanonicalType(anyOf(arrayType(hasElementType(isAnyCharacter())),
                                 pointerType(pointee(isAnyCharacter())))))))));

  const auto WrongLength =
      anyOf(ignoringImpCasts(Strlen), ignoringImpCasts(SizeOrLength),
            hasDescendant(Strlen), hasDescendant(SizeOrLength));
  
  // - Example:  length = strlen(src);
  const auto DREWithoutInc =
      ignoringImpCasts(declRefExpr(to(varDecl(hasInitializer(WrongLength)))));

  const auto AnyOfCallOrDREWithoutInc = anyOf(DREWithoutInc, WrongLength);

  // - Example:  int getLength(const char *str) { return strlen(str); }
  const auto CallExprReturnWithoutInc =
      ignoringImpCasts(callExpr(callee(functionDecl(hasBody(
          has(returnStmt(hasReturnValue(AnyOfCallOrDREWithoutInc))))))));

  // - Example:  int length = getLength(src);
  const auto DREHasReturnWithoutInc = ignoringImpCasts(
      declRefExpr(to(varDecl(hasInitializer(CallExprReturnWithoutInc)))));

  const auto AnyOfWrongLengthInit =
      anyOf(AnyOfCallOrDREWithoutInc, CallExprReturnWithoutInc,
            DREHasReturnWithoutInc);

  enum class StrlenKind { WithInc, WithoutInc };

  const auto AnyOfLengthExpr = [=](StrlenKind LengthKind) {
    return ignoringImpCasts(allOf(
        unless(hasDefinition(SizeOfCharExpr)),
        anyOf(allOf((LengthKind == StrlenKind::WithoutInc)
                        ? ignoringImpCasts(unless(hasDefinition(HasIncOp)))
                        : ignoringImpCasts(
                              allOf(hasDefinition(HasIncOp),
                                    unless(hasDefinition(HasDecOp)))),
                    AnyOfWrongLengthInit),
              ignoringImpCasts(integerLiteral().bind(WrongLengthExprName))),
        expr().bind(LengthExprName)));
  };

  const auto LengthWithoutInc = AnyOfLengthExpr(StrlenKind::WithoutInc);
  const auto LengthWithInc = AnyOfLengthExpr(StrlenKind::WithInc);

  //===--------------------------------------------------------------------===//
  // The following five case match the 'destination' array length's
  // expression which is used in memcpy() and memmove() matchers.
  //===--------------------------------------------------------------------===//

  const auto SizeExpr = anyOf(SizeOfCharExpr, integerLiteral(equals(1)));

  const auto MallocLengthExpr = allOf(
      anyOf(argumentCountIs(1), argumentCountIs(2)),
      hasAnyArgument(allOf(unless(SizeExpr),
                           expr(ignoringImpCasts(anyOf(HasIncOp, anything())))
                               .bind(DestMallocExprName))));

  // - Example:  (char *)malloc(length);
  const auto DestMalloc = anyOf(castExpr(has(callExpr(MallocLengthExpr))),
                                callExpr(MallocLengthExpr));

  // - Example:  new char[length];
  const auto DestCXXNewExpr = ignoringImpCasts(
      cxxNewExpr(hasArraySize(expr().bind(DestMallocExprName))));

  const auto AnyOfDestInit = anyOf(DestMalloc, DestCXXNewExpr);

  // - Example:  char dest[13];  or  char dest[length];
  const auto DestArrayTyDecl = declRefExpr(
      to(anyOf(varDecl(CharTyArray).bind(DestVarDeclName),
               varDecl(hasInitializer(AnyOfDestInit)).bind(DestVarDeclName))));

  // - Example:  foo[bar[baz]].qux; (or just ParmVarDecl)
  const auto DestUnknownDecl =
      declRefExpr(allOf(to(varDecl(AnyOfCharTy).bind(DestVarDeclName)),
                        expr().bind(UnknownDestName)));

  const auto AnyOfDestDecl =
      allOf(anyOf(hasDefinition(anyOf(AnyOfDestInit, DestArrayTyDecl)),
                  DestUnknownDecl, anything()),
            expr().bind(DestExprName));

  const auto SrcDecl = declRefExpr(
      allOf(to(decl().bind(SrcVarDeclName)),
            anyOf(hasAncestor(cxxMemberCallExpr().bind(SrcExprName)),
                  expr().bind(SrcExprName))));

  const auto SrcDeclMayInBinOp =
      anyOf(ignoringImpCasts(SrcDecl), hasDescendant(SrcDecl));

  const auto AnyOfSrcDecl = anyOf(
      ignoringImpCasts(stringLiteral().bind(SrcExprName)), SrcDeclMayInBinOp);

  const auto NullTerminatorExpr = binaryOperator(
      hasLHS(hasDescendant(
          declRefExpr(to(varDecl(equalsBoundNode(DestVarDeclName)))))),
      hasRHS(ignoringImpCasts(
          anyOf(characterLiteral(equals(static_cast<unsigned>(0))),
                integerLiteral(equals(0))))));

  //===--------------------------------------------------------------------===//
  // The following nineteen case match problematic function calls.
  //===--------------------------------------------------------------------===//

  const auto WithoutSrc = [=](StringRef Name, int LengthPos,
                              StrlenKind LengthKind) {
    return allOf(
        callee(functionDecl(hasName(Name))),
        hasArgument(
            0, allOf(AnyOfDestDecl, unless(hasAncestor(compoundStmt(
                                        hasDescendant(NullTerminatorExpr)))))),
        hasArgument(LengthPos, (LengthKind == StrlenKind::WithoutInc)
                                   ? LengthWithoutInc
                                   : LengthWithInc));
  };

  const auto WithSrc = [=](StringRef Name, int SourcePos, int LengthPos,
                           StrlenKind LengthKind) {
    return allOf(callee(functionDecl(hasName(Name))),
                 hasArgument(SourcePos ? 0 : 1,
                             allOf(AnyOfDestDecl,
                                   unless(hasAncestor(compoundStmt(
                                       hasDescendant(NullTerminatorExpr)))))),
                 hasArgument(SourcePos, AnyOfSrcDecl),
                 hasArgument(LengthPos, (LengthKind == StrlenKind::WithoutInc)
                                            ? LengthWithoutInc
                                            : LengthWithInc));
  };

  const auto Memcpy = WithSrc("::memcpy", 1, 2, StrlenKind::WithoutInc);
  const auto Wmemcpy = WithSrc("::wmemcpy", 1, 2, StrlenKind::WithoutInc);
  const auto Memcpy_s = WithSrc("::memcpy_s", 2, 3, StrlenKind::WithoutInc);
  const auto Wmemcpy_s = WithSrc("::wmemcpy_s", 2, 3, StrlenKind::WithoutInc);
  const auto Memchr = WithSrc("::memchr", 0, 2, StrlenKind::WithoutInc);
  const auto Wmemchr = WithSrc("::wmemchr", 0, 2, StrlenKind::WithoutInc);
  const auto Memmove = WithSrc("::memmove", 1, 2, StrlenKind::WithoutInc);
  const auto Wmemmove = WithSrc("::wmemmove", 1, 2, StrlenKind::WithoutInc);
  const auto Memmove_s = WithSrc("::memmove_s", 2, 3, StrlenKind::WithoutInc);
  const auto Wmemmove_s = WithSrc("::wmemmove_s", 2, 3, StrlenKind::WithoutInc);
  const auto Memset = WithoutSrc("::memset", 2, StrlenKind::WithInc);
  const auto Wmemset = WithoutSrc("::wmemset", 2, StrlenKind::WithInc);
  const auto Strerror_s = WithoutSrc("::strerror_s", 1, StrlenKind::WithoutInc);
  const auto StrncmpLHS = WithSrc("::strncmp", 1, 2, StrlenKind::WithInc);
  const auto WcsncmpLHS = WithSrc("::wcsncmp", 1, 2, StrlenKind::WithInc);
  const auto StrncmpRHS = WithSrc("::strncmp", 0, 2, StrlenKind::WithInc);
  const auto WcsncmpRHS = WithSrc("::wcsncmp", 0, 2, StrlenKind::WithInc);
  const auto Strxfrm = WithSrc("::strxfrm", 1, 2, StrlenKind::WithoutInc);
  const auto Wcsxfrm = WithSrc("::wcsxfrm", 1, 2, StrlenKind::WithoutInc);

  const auto AnyOfMatchers =
      anyOf(Memcpy, Wmemcpy, Memcpy_s, Wmemcpy_s, Memchr, Wmemchr, Memmove,
            Wmemmove, Memmove_s, Wmemmove_s, Memset, Wmemset, Strerror_s,
            StrncmpLHS, WcsncmpLHS, StrncmpRHS, WcsncmpRHS, Strxfrm, Wcsxfrm);

  Finder->addMatcher(callExpr(AnyOfMatchers).bind(FuncExprName), this);

  Finder->addMatcher(
      castExpr(has(callExpr(anyOf(Memchr, Wmemchr)).bind(FuncExprName)))
          .bind(CastExprName),
      this);
}

void NotNullTerminatedResultCheck::check(
    const MatchFinder::MatchResult &Result) {
  const auto *FuncExpr = Result.Nodes.getNodeAs<CallExpr>(FuncExprName);
  if (FuncExpr->getLocStart().isMacroID())
    return;

  // Increment by integer '1' can result in overflow if it is the maximal value.
  // After that it will be extended to 'size_t' and its value will be wrong,
  // therefore we have to inject '+ 1UL' instead.
  IsInjectUL = getGivenLength(Result) == std::numeric_limits<int>::max();

  if (SafeFunctionsAvailable == SafeFunctionsAvailableKind::Default) {
    const auto It = MacroDefinedMap.find("__STDC_WANT_LIB_EXT1__");
    if (It != MacroDefinedMap.end())
      SafeFunctionsAvailable = It->second ? SafeFunctionsAvailableKind::Yes
                                          : SafeFunctionsAvailableKind::No;
    else
      SafeFunctionsAvailable = SafeFunctionsAvailableKind::No;
  }

  StringRef Name = FuncExpr->getDirectCallee()->getName();
  if (Name.startswith("mem") || Name.startswith("wmem"))
    memoryHandlerFunctionFix(Name, Result);
  else if (Name == "strerror_s")
    strerror_sFix(Result);
  else if (Name.endswith("ncmp"))
    ncmpFix(Name, Result);
  else if (Name.endswith("xfrm"))
    xfrmFix(Name, Result);
}

void NotNullTerminatedResultCheck::memoryHandlerFunctionFix(
    StringRef Name, const MatchFinder::MatchResult &Result) {
  if (isNoWrongLength(Result))
    return;

  if (Name.endswith("chr")) {
    memchrFix(Name, Result);
    return;
  }

  if ((Name.contains("cpy") || Name.contains("move")) &&
      isDestAndSrcEquals(Result))
    return;

  auto Diag =
      diag(Result.Nodes.getNodeAs<CallExpr>(FuncExprName)->getLocStart(),
           "the result from calling '%0' is not null-terminated")
      << Name;

  if (Name.endswith("cpy"))
    memcpyFix(Name, Result, Diag);
  else if (Name.endswith("cpy_s"))
    memcpy_sFix(Name, Result, Diag);
  else if (Name.endswith("move"))
    memmoveFix(Name, Result, Diag);
  else if (Name.endswith("move_s")) {
    destCapacityFix(Result, Diag);
    lengthArgHandle(LengthHandleKind::LH_Increase, 3, Result, Diag);
  } else if (Name.endswith("set")) {
    lengthArgHandle(LengthHandleKind::LH_Decrease, 2, Result, Diag);
  }
}

void NotNullTerminatedResultCheck::memcpyFix(
    StringRef Name, const MatchFinder::MatchResult &Result,
    DiagnosticBuilder &Diag) {
  const bool IsOverflows = destCapacityFix(Result, Diag);

  // If it is cannot be rewritten to string handler function
  if (Result.Nodes.getNodeAs<Type>(NotJustCharTyName)) {
    if (SafeFunctionsAvailable == SafeFunctionsAvailableKind::Yes &&
        isKnownDest(Result)) {
      renameFunc((Name[0] != 'w') ? "memcpy_s" : "wmemcpy_s", Result, Diag);
      insertDestCapacityArg(IsOverflows, Name, Result, Diag);
    }

    lengthArgHandle(LengthHandleKind::LH_Increase, 2, Result, Diag);
    return;
  }

  const bool IsCpy =
      isGivenLengthEQToSrcLength(Result) || isProperDestCapacity(Result);
  const bool IsSafe =
      SafeFunctionsAvailable == SafeFunctionsAvailableKind::Yes &&
      IsOverflows && isKnownDest(Result) && !isProperDestCapacity(Result);
  const bool IsDestLengthNotRequired =
      IsSafe && getLangOpts().CPlusPlus &&
      Result.Nodes.getNodeAs<ArrayType>(DestArrayTyName);

  SmallString<10> NewFuncName;
  NewFuncName = (Name[0] != 'w') ? "str" : "wcs";
  NewFuncName += IsCpy ? "cpy" : "ncpy";
  NewFuncName += IsSafe ? "_s" : "";
  renameFunc(NewFuncName, Result, Diag);

  if (IsSafe && !IsDestLengthNotRequired)
    insertDestCapacityArg(IsOverflows, Name, Result, Diag);

  if (IsCpy)
    removeArg(2, Result, Diag);

  if (!IsCpy && !IsSafe)
    insertNullTerminatorExpr(Name, Result, Diag);
}

void NotNullTerminatedResultCheck::memcpy_sFix(
    StringRef Name, const MatchFinder::MatchResult &Result,
    DiagnosticBuilder &Diag) {
  const bool IsOverflows = destCapacityFix(Result, Diag);

  if (Result.Nodes.getNodeAs<Type>(NotJustCharTyName)) {
    lengthArgHandle(LengthHandleKind::LH_Increase, 3, Result, Diag);
    return;
  }

  const bool RemoveDestLength =
      getLangOpts().CPlusPlus &&
      Result.Nodes.getNodeAs<ArrayType>(DestArrayTyName);
  const bool IsCpy = isGivenLengthEQToSrcLength(Result);
  const bool IsSafe = IsOverflows;

  SmallString<10> NewFuncName;
  NewFuncName = (Name[0] != 'w') ? "str" : "wcs";
  NewFuncName += IsCpy ? "cpy" : "ncpy";
  NewFuncName += IsSafe ? "_s" : "";
  renameFunc(NewFuncName, Result, Diag);

  if (!IsSafe || (IsSafe && RemoveDestLength))
    removeArg(1, Result, Diag);
  else if (IsOverflows && isKnownDest(Result))
    lengthArgHandle(LengthHandleKind::LH_Increase, 1, Result, Diag);

  if (IsCpy)
    removeArg(3, Result, Diag);

  if (!IsCpy && !IsSafe)
    insertNullTerminatorExpr(Name, Result, Diag);
}

void NotNullTerminatedResultCheck::memchrFix(
    StringRef Name, const MatchFinder::MatchResult &Result) {
  const auto *FuncExpr = Result.Nodes.getNodeAs<CallExpr>(FuncExprName);
  if (const auto GivenCL =
          dyn_cast_or_null<CharacterLiteral>(FuncExpr->getArg(1)))
    if (GivenCL->getValue() != 0)
      return;

  auto Diag = diag(FuncExpr->getArg(2)->IgnoreParenCasts()->getLocStart(),
                   "the length is too short for the last %0")
              << ((Name[0] != 'w') ? "\'\\0\'" : "L\'\\0\'");

  if (const auto *CastExpr = Result.Nodes.getNodeAs<Expr>(CastExprName)) {
    const auto CastRemoveFix = FixItHint::CreateRemoval(SourceRange(
        CastExpr->getLocStart(), FuncExpr->getLocStart().getLocWithOffset(-1)));
    Diag << CastRemoveFix;
  }
  StringRef NewFuncName = (Name[0] != 'w') ? "strchr" : "wcschr";
  renameFunc(NewFuncName, Result, Diag);
  removeArg(2, Result, Diag);
}

void NotNullTerminatedResultCheck::memmoveFix(
    StringRef Name, const MatchFinder::MatchResult &Result,
    DiagnosticBuilder &Diag) {
  const bool IsOverflows = destCapacityFix(Result, Diag);

  if (SafeFunctionsAvailable == SafeFunctionsAvailableKind::Yes &&
      isKnownDest(Result)) {
    renameFunc((Name[0] != 'w') ? "memmove_s" : "wmemmove_s", Result, Diag);
    insertDestCapacityArg(IsOverflows, Name, Result, Diag);
  }

  lengthArgHandle(LengthHandleKind::LH_Increase, 2, Result, Diag);
}

void NotNullTerminatedResultCheck::strerror_sFix(
    const MatchFinder::MatchResult &Result) {
  StringRef Name = "strerror_s";
  auto Diag =
      diag(Result.Nodes.getNodeAs<CallExpr>(FuncExprName)->getLocStart(),
           "the result from calling '%0' is not null-terminated and "
           "missing the last character of the error message")
      << Name;

  destCapacityFix(Result, Diag);
  lengthArgHandle(LengthHandleKind::LH_Increase, 1, Result, Diag);
}

void NotNullTerminatedResultCheck::ncmpFix(
    StringRef Name, const MatchFinder::MatchResult &Result) {
  const auto *FuncExpr = Result.Nodes.getNodeAs<CallExpr>(FuncExprName);
  const auto *FirstArgExpr = FuncExpr->getArg(0)->IgnoreImpCasts();
  const auto *SecondArgExpr = FuncExpr->getArg(1)->IgnoreImpCasts();
  bool IsLengthTooLong = false;

  if (const auto *LengthExpr =
          Result.Nodes.getNodeAs<CallExpr>(WrongLengthExprName)) {
    const auto *LengthExprArg = LengthExpr->getArg(0);
    StringRef FirstExprStr = exprToStr(FirstArgExpr, Result).trim(' ');
    StringRef SecondExprStr = exprToStr(SecondArgExpr, Result).trim(' ');
    StringRef LengthArgStr = exprToStr(LengthExprArg, Result).trim(' ');
    IsLengthTooLong =
        LengthArgStr == FirstExprStr || LengthArgStr == SecondExprStr;
  } else {
    const int SrcLength = getLength(getSrcExpr(Result), Result);
    const int GivenLength = getGivenLength(Result);
    IsLengthTooLong = GivenLength - 1 == SrcLength;
  }

  if (!IsLengthTooLong && !isStringDataAndLength(Result))
    return;

  auto Diag = diag(FuncExpr->getArg(2)->IgnoreParenCasts()->getLocStart(),
                   "comparison length is too long and might lead to a "
                   "buffer overflow");

  lengthArgHandle(LengthHandleKind::LH_Decrease, 2, Result, Diag);
}

void NotNullTerminatedResultCheck::xfrmFix(
    StringRef Name, const MatchFinder::MatchResult &Result) {
  if (!isDestCapacityOverflows(Result))
    return;

  auto Diag =
      diag(Result.Nodes.getNodeAs<CallExpr>(FuncExprName)->getLocStart(),
           "the result from calling '%0' is not null-terminated")
      << Name;

  destCapacityFix(Result, Diag);
  lengthArgHandle(LengthHandleKind::LH_Increase, 2, Result, Diag);
}

} // namespace bugprone
} // namespace tidy
} // namespace clang
