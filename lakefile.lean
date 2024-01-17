import Lake
open Lake DSL

require UnicodeBasic from git "https://github.com/fgdorais/lean4-unicode-basic.git"
   @  "main"

require std from git "https://github.com/leanprover/std4"
   @  "main"

meta if get_config? env = some "dev" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

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