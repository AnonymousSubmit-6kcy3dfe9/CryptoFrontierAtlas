import Lake

open Lake DSL

package «CryptoFrontierAtlasLean» where
  version := v!"0.1.0"
  moreLeanArgs := #["-DwarningAsError=true"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

lean_lib CryptoFrontierAtlas where
  srcDir := "."

lean_lib LeanCipher where
  srcDir := "."
