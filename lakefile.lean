import Lake
open Lake DSL

meta if get_config? env = some "dev" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4"
    @ "c7f4ac84b973b6efd8f24ba2b006cad1b32c9c53"

require UnicodeBasic from git "https://github.com/fgdorais/lean4-unicode-basic.git"
    @ "main"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.8.0"

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

lean_lib Test where
  srcDir := "test"
  roots := #[`Test, `RegexTest, `TomlLoader, `PcreLoader]

@[test_runner]
lean_exe test where
  srcDir := "test"
  root := `Test
