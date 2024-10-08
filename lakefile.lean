import Lake
open Lake DSL

meta if get_config? env = some "dev" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4"
    @ "v4.11.0-rc1"

require UnicodeBasic from git "https://github.com/fgdorais/lean4-unicode-basic.git"
    @ "6c260d58b9c9fe49f1312a6ecc0437de84e2fb8d"

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.11.0-rc1"

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
