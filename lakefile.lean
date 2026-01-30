import Lake
open Lake DSL

package "http" where
  version := v!"0.1.0"

@[default_target]
lean_lib «Http» where

require binary from git "https://github.com/Lean-zh/binary.git" @"main"
require uri from git "https://github.com/Qiu233/uri"
