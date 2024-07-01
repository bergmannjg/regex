import Lake
open Lake DSL

meta if get_config? env = some "dev" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4"
    @ "1f51169609a3a7c448558c3d3eb353fb355c7025"

require UnicodeBasic from git "https://github.com/fgdorais/lean4-unicode-basic.git"
    @ "main"

require mathlib from git "https://github.com/leanprover-community/mathlib4"
    @ "ab0de47a15970636867ab3bea74476a1264ffbb2"

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

@[test_driver]
lean_exe test where
  srcDir := "test"
  root := `Test
