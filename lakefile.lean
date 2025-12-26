import Lake
open Lake DSL

package VerifiedAgora {
-- add any package configuration options here
}



require SafeVerify from git
"https://github.com/riyazahuja/SafeVerify.git" @ "main"

@[default_target]
lean_lib VerifiedAgora where

@[default_target]
lean_exe get_targets where
  root := `VerifiedAgora.getTargets
  supportInterpreter := true

@[default_target]
lean_exe get_all_targets where
  root := `VerifiedAgora.allTargets
  supportInterpreter := true
