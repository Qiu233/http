import Lake
open Lake DSL

package "http" where
  version := v!"0.1.0"
  leanOptions := #[⟨`experimental.module, true⟩]

lean_lib «Http» where

require binary from git "https://github.com/Lean-zh/binary.git"
require uri from git "https://github.com/Qiu233/uri"
