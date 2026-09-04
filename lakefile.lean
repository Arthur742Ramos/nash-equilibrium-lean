import Lake
open Lake DSL

package «nash_equilibrium» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0"

@[default_target]
lean_lib NashEquilibrium where
  roots := #[
    `NashEquilibrium.Basic,
    `NashEquilibrium.Mixed,
    `NashEquilibrium.MixedTopology,
    `NashEquilibrium.MixedBrouwer,
    `NashEquilibrium.Examples]

lean_lib Gametheory where
  roots := #[
    `Gametheory.Scarf,
    `Gametheory.ScarfPath,
    `Gametheory.Brouwer,
    `Gametheory.Brouwer_product]

@[default_target]
lean_lib Challenge where
  roots := #[`Challenge]

@[default_target]
lean_lib Solution where
  roots := #[`Solution]
