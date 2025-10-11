import Lake
open Lake DSL

package VerifiedAgora {
-- add any package configuration options here
}



require SafeVerify from git
"https://github.com/GasStationManager/SafeVerify.git" @ "main"

@[default_target]
lean_lib VerifiedAgora where

-- @[default_target]
-- lean_lib TrainingData where

-- require lean4checker from git
--   "https://github.com/leanprover/lean4checker.git" @ "v4.20.1"
