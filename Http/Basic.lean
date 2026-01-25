module

public import Std.Internal.Parsec
public import Uri.Parser
meta import Lean

open Std.Internal.Parsec Std.Internal.Parsec.String in
@[always_inline]
public def Http.instParser : Uri.Parser.MonadParser Parser where
  satisfy := satisfy
  pchar := pchar
  pstring := pstring
  skipChar := skipChar
  skipString := skipString
  attempt := attempt
  optional := optional
  many := many
  many1 := many1
  manyChars := manyChars
  many1Chars := many1Chars
  fail := fail
  notFollowedBy := notFollowedBy
  peek? := peek?

/- this snippet hide the definition `instParser` since we don't want it to be used by downstream users -/
run_meta do
  Lean.MonadEnv.modifyEnv (fun env => Lean.Meta.addToCompletionBlackList env ``Http.instParser)
