import Lake
open Lake DSL

meta if get_config? env = some "dev" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4"
    @ "v4.12.0"

require UnicodeBasic from git "https://github.com/fgdorais/lean4-unicode-basic.git"  @ "v1.0.2"

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.12.0"

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
