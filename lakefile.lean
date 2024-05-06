import Lake
open Lake DSL

meta if get_config? env = some "dev" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4"
    @ "a34d3c1f7b72654c08abe5741d94794db40dbb2e"

require UnicodeBasic from git "https://github.com/fgdorais/lean4-unicode-basic.git"
    @ "02b5c10791d189630fde0428ce930ec0974f0a9f"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.7.0"

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
