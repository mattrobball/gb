import Lake
open Lake DSL

package «gb» {
  -- add package configuration options here
}

lean_lib «GB» {
  -- add library configuration options here
}

@[default_target]
lean_exe «gb» {
  root := `Main
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"
