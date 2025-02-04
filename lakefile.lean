import Lake
open Lake DSL

meta if get_config? env = some "dev" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4"
    @ "v4.16.0"

require UnicodeBasic from git "https://github.com/fgdorais/lean4-unicode-basic.git"  @ "v1.1.3"

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.16.0"

require tryAtEachStep from git "https://github.com/dwrensha/tryAtEachStep" @ "lean-v4.16.0"

package «Regex» {
  lintDriver := "batteries/runLinter"
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
