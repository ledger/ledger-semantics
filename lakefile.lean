import Lake
open Lake DSL

package ledger where
  -- `sorry` warnings are errors: an unproved theorem fails the build.
  moreLeanArgs := #["-DwarningAsError=true"]
  -- No auto-bound implicits: in a specification kernel, a typo must be
  -- an error, not a silently universally-quantified variable.
  leanOptions := #[⟨`autoImplicit, false⟩]

-- Mathlib pinned to the toolchain version in `lean-toolchain`. The Nix
-- dev shell provides the same Lean (see flake.nix); keep all three in sync.
require "leanprover-community" / "mathlib" @ git "v4.30.0"

@[default_target]
lean_lib Ledger where
  -- Build the module index and every module under Ledger/.
  globs := #[.andSubmodules `Ledger]
