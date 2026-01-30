import Lake
open Lake DSL

package "http" where
  version := v!"0.1.0"

@[default_target]
lean_lib «Http» where

require uri from git "https://github.com/Qiu233/uri"
