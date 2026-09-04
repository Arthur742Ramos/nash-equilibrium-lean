# Nash Equilibria (Lean)

This repository is a Lean-native formalization of finite strategic-form games.
It defines finite player-specific strategy sets, pure profiles, unilateral
deviations, best responses, dominant strategies, and two carefully separated
potential notions. `IsGeneralizedOrdinalPotential` is the one-way condition
that every strict payoff improvement raises the potential. `IsOrdinalPotential`
is reserved for the standard bidirectional strict-sign equivalence.

The selected theorem surface is a finite improvement-system certificate:

- a standard ordinal potential has a pure Nash profile that globally maximizes
  the potential;
- under the standard condition, pure Nash profiles are exactly potential local
  maxima; and
- under the generalized condition, every nonempty better-response path strictly
  ascends the potential, so directed better-response cycles are impossible;
- in fact, every legal starting profile reaches a pure Nash equilibrium by a
  finite better-response path (weak acyclicity).

This is a formalization contribution about semantic precision and a reusable
finite-dynamics interface, not a claim of a new economic theorem. A checked
constant-payoff example demonstrates the terminology boundary: the generalized
condition permits a strict potential rise on a payoff-neutral deviation, while
the standard condition rejects it.

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
the selected declarations' axioms, and validates the metadata and Comparator
configuration. The pinned Comparator replay is available separately through
scripts/verify-comparator.sh.

## Palomar surface

Challenge.lean is intentionally small and standalone. It contains the
mathematical statement with one proof hole and imports only the finite maximum
and finite-function modules from Mathlib. Solution.lean imports the native implementation and
provides the checked proofs under the matching namespace
NashEquilibrium.Palomar.

The selected declarations are:

    NashEquilibrium.Palomar.exists_nash_maximizing_ordinal_potential
    NashEquilibrium.Palomar.isNash_iff_potential_local_maximum
    NashEquilibrium.Palomar.no_betterResponse_cycle_of_generalized_ordinal_potential
    NashEquilibrium.Palomar.weaklyAcyclic_of_generalized_ordinal_potential

The Comparator definition targets make the Game, profile, deviation, Nash,
standard/generalized potential, maximizer, local-maximum, and better-response
interfaces explicit. The main Challenge theorem returns a reusable certificate
containing both equilibrium stability and global potential maximality; it is
stronger than a bare existential conclusion.

## Literature and positioning

The terminology follows [Monderer and Shapley, *Potential Games*](https://doi.org/10.1006/game.1996.0044):
the standard ordinal notion matches strict payoff and potential comparisons in
both directions. The weaker one-way condition is tracked separately as a
generalized ordinal potential. [Rosenthal's congestion-game paper](https://doi.org/10.1007/BF01737559)
is the foundational precursor for potential-based pure-equilibrium existence.
For later structural context, see [Candogan, Menache, Ozdaglar, and Parrilo](https://doi.org/10.1287/moor.1110.0500).

The closest directly comparable formalization literature located is
[Bagnall, Merten, and Stewart's Ssreflect/Coq library](https://jfr.unibo.it/article/view/7235),
which covers potential games and best-response dynamics. The companion
[Isabelle/AFP entry](https://isa-afp.org/entries/Nash_Equilibrium.html) covers
finite pure and mixed Nash equilibria, including a Brouwer-based general mixed
existence theorem. This Lean repository is an independent, narrower companion:
it does not claim a file-level translation or reproduce that mixed theorem, and
it makes the potential terminology and improvement-path certificate explicit.

## Relationship to the Isabelle/AFP entry

The mathematical scope is informed by the published AFP entry
[Nash Equilibria for Finite Games in Isabelle/HOL](https://isa-afp.org/entries/Nash_Equilibrium.html).
The Lean development changes the definitions and proof architecture. In
particular, it does not silently call the one-way improvement implication
"ordinal"; it names that class generalized and reserves the standard name for
the bidirectional condition. The Isabelle Brouwer-based general mixed-Nash
existence theorem is outside this repository's claim.

## Status

The artifact is prepared for local Palomar checks. Local compilation is not a
claim of hosted Comparator verification, editorial review, or registration.
Those states require a public pinned commit and the corresponding Palomar
workflow.
