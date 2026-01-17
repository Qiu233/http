import Lake
open Lake DSL

package "http" where
  version := v!"0.1.0"
  leanOptions := #[⟨`experimental.module, true⟩]

lean_lib «Http» where

require binary from git "https://github.com/Lean-zh/binary.git" @ "2fb5c4b9b3d53bcd09461ef0f69ea455b3144b12"
require uri from git "https://github.com/Qiu233/uri" @ "0cc931ef8729538e2ad8801f5a6660448bff51a4"
