import Lake
open Lake DSL

package «certifyingDatalog» where
  -- add any package configuration options here


lean_lib «CertifyingDatalog» {
  -- add library configuration options here
}
require std from git "https://github.com/leanprover/std4" @ "main"


require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe «certifyingDatalog» where
  root:= `Main
