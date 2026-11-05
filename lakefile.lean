import Lake
open Lake DSL

package verifiable_ai_assurance_core where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"

-- The workflow retrieves and verifies these already-public source files.
lean_lib ResponsibilityOS
lean_lib adic_cyber_assurance_gateway

@[default_target]
lean_lib VerifiableAIAssurance
