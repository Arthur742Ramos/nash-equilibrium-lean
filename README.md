# Nash Equilibria (Lean)

This repository is a Lean-native formalization of finite strategic-form games.
It defines finite player-specific strategy sets, pure profiles, unilateral
deviations, best responses, dominant strategies, and ordinal-potential games.
Its main result proves that every finite ordinal-potential game has a pure Nash
equilibrium by maximizing the potential over the finite set of legal profiles.

The library also contains a finite mixed-strategy layer and checked examples:
Prisoner's Dilemma has a dominant defection profile, matching pennies has no
pure equilibrium, and its uniform profile is a mixed equilibrium under the
finite expected-payoff definitions.

## Build

The project pins Lean 4.33.0 and Mathlib v4.33.0. From the repository root:

    lake build
    bash scripts/verify-palomar.sh

The package audit compiles the complete library, compiles the standalone
Challenge and Solution surfaces, checks the Challenge import closure, audits
the selected theorem's axioms, and validates the metadata and Comparator
configuration. The pinned Comparator replay is available separately through
scripts/verify-comparator.sh.

## Palomar surface

Challenge.lean is intentionally small and standalone. It contains the
mathematical statement with one proof hole and imports only
Mathlib.Data.Finset.Max. Solution.lean imports the native implementation and
provides the checked proof under the matching namespace
NashEquilibrium.Palomar.

The selected result is
NashEquilibrium.Palomar.exists_nash_of_ordinal_potential.
The Comparator definition targets make the Game, profile, deviation, Nash,
and ordinal-potential interfaces explicit.

## Relationship to the Isabelle/AFP entry

The mathematical scope is informed by the published AFP entry
[Nash Equilibria for Finite Games in Isabelle/HOL](https://isa-afp.org/entries/Nash_Equilibrium.html).
This repository is a separate Lean-native companion: it does not claim to be
a file-level translation, and its mixed-strategy layer does not currently
reproduce the Isabelle Brouwer-based general mixed-Nash existence theorem.

## Status

The artifact is prepared for local Palomar checks. Local compilation is not a
claim of hosted Comparator verification, editorial review, or registration.
Those states require a public pinned commit and the corresponding Palomar
workflow.
