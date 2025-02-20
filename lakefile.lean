import Lake
open Lake DSL

package «lean4-example» {
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]
}

@[default_target]
lean_lib «NeutronRISCVAdd» {
}
lean_lib «NeutronRISCVBitDecomposition» {
}
lean_lib «Lean4Example» {
}

require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v4.16.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.16.0"

require aesop from git "https://github.com/leanprover-community/aesop" @ "v4.16.0"

require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"
