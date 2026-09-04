import Lake
open Lake DSL

package «nash_equilibrium» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0"

lean_lib NashEquilibrium where
  roots := #[
    `NashEquilibrium.Basic,
    `NashEquilibrium.Mixed,
    `NashEquilibrium.Examples]

@[default_target]
lean_lib Challenge where
  roots := #[`Challenge]

@[default_target]
lean_lib Solution where
  roots := #[`Solution]
