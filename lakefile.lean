import Lake
open Lake DSL

package «IIT» where

lean_lib «IIT» where

@[default_target]
lean_exe «iit» where
  root := `Main

require std from git "https://github.com/leanprover/std4" @ "v4.8.0-rc1"
