import Lake
open Lake DSL

require UnicodeBasic from git "https://github.com/fgdorais/lean4-unicode-basic.git"
   @  "8603bb1d0d5edae780e3a85a0398fd83dbbb80a3"

require std from git "https://github.com/leanprover/std4"
   @  "v4.5.0-rc1"

require mathlib from git "https://github.com/leanprover-community/mathlib4"
   @ "v4.5.0-rc1"

meta if get_config? env = some "dev" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4"
   @ "94e10377bef4e64820ffd7dcab6affef3304af62"

package «Regex» {
}

lean_lib «Regex» {
  roots := #[`Regex]
  buildType := .debug
}

@[default_target]
lean_exe inspect {
  root := `Main
  buildType := .debug
}

@[default_target]
lean_exe benchmark {
  root := `Benchmark
  buildType := .debug
}

lean_exe test {
  root := `Test
}
