import Lake
open Lake DSL

package «study» {
  -- add package configuration options here
}

lean_lib «Study» {
  -- add library configuration options here
}

@[default_target]
lean_exe «study» {
  root := `Main
}
