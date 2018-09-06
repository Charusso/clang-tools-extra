//===--- NotNullTerminatedResultCheck.h - clang-tidy ------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_BUGPRONE_NOT_NULL_TERMINATED_RESULT_H
#define LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_BUGPRONE_NOT_NULL_TERMINATED_RESULT_H

#include "../ClangTidy.h"

namespace clang {
namespace tidy {
namespace bugprone {

/// Finds function calls where it is possible to cause a not null-terminated
/// result. Usually the proper length of a string is ``strlen(src) + 1`` or
/// equal length of this expression, because the null terminator needs an extra
/// space. Without the null terminator it can result in an undefined behaviour
/// when the string is read.
///
/// For the user-facing documentation see:
/// http://clang.llvm.org/extra/clang-tidy/checks/bugprone-not-null-terminated-result.html
class NotNullTerminatedResultCheck : public ClangTidyCheck {
public:
  NotNullTerminatedResultCheck(StringRef Name, ClangTidyContext *Context);
  void storeOptions(ClangTidyOptions::OptionMap &Opts) override;
  void registerMatchers(ast_matchers::MatchFinder *Finder) override;
  void check(const ast_matchers::MatchFinder::MatchResult &Result) override;
  void registerPPCallbacks(CompilerInstance &Compiler) override;

private:
  enum class SafeFunctionsAvailableKind { Default, No, Yes };
  SafeFunctionsAvailableKind SafeFunctionsAvailable;

  // It is specifying if the target environment is considered to implement
  // '_s' suffixed memory and string handler functions which are safer than
  // older version (e.g. 'memcpy_s()'):
  // - If "Default", "d", or "" (empty string) the checker relies on the
  //   '__STDC_WANT_LIB_EXT1__' macro being defined.
  // - If "Yes", "y", or non-zero the '_s' suffixed functions are available.
  // - If "No", "n", or 0 (zero) the '_s' suffixed functions are not available.
  // - The default value is ``""`` (empty string).
  const std::string AreSafeFunctionsAvailable;

  void memoryHandlerFunctionFix(
      StringRef Name, const ast_matchers::MatchFinder::MatchResult &Result);
  void memcpyFix(StringRef Name,
                 const ast_matchers::MatchFinder::MatchResult &Result,
                 DiagnosticBuilder &Diag);
  void memcpy_sFix(StringRef Name,
                   const ast_matchers::MatchFinder::MatchResult &Result,
                   DiagnosticBuilder &Diag);
  void memchrFix(StringRef Name,
                 const ast_matchers::MatchFinder::MatchResult &Result);
  void memmoveFix(StringRef Name,
                  const ast_matchers::MatchFinder::MatchResult &Result,
                  DiagnosticBuilder &Diag);
  void strerror_sFix(const ast_matchers::MatchFinder::MatchResult &Result);
  void ncmpFix(StringRef Name,
               const ast_matchers::MatchFinder::MatchResult &Result);
  void xfrmFix(StringRef Name,
               const ast_matchers::MatchFinder::MatchResult &Result);
};

} // namespace bugprone
} // namespace tidy
} // namespace clang

#endif // LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_BUGPRONE_NOT_NULL_TERMINATED_RESULT_H
