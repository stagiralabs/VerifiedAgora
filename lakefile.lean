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
  root := `VerifiedAgora.get_targets
  supportInterpreter := true
