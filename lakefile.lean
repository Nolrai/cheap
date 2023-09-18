import Lake
open Lake DSL

package cheap {
  -- add package configuration options here
}

@[default_target]
lean_lib CHEAP {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"3045aef4ffb0fd709de915066088b9bb54ba54a6"
