import Lake
open Lake DSL

package «certifyingDatalog» where
  -- add any package configuration options here


lean_lib «CertifyingDatalog» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"nightly-testing-2025-02-24"

@[default_target]
lean_exe «certifyingDatalog» where
  root:= `Main
