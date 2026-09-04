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

The library also contains a finite mixed-strategy layer and checked examples.
It proves support equalization, zero probability for strictly suboptimal
moves, Dirac transport from pure Nash profiles, the normalized excess-map
construction, and the fixed-point-to-mixed-Nash reduction.  A companion
topology module proves that the mixed-profile set is closed, compact, convex,
and nonempty and that the payoff/excess/map operations are continuous.  The
repository now also proves the full finite mixed-Nash existence theorem: a
kernel-checked Scarf/Brouwer product-of-simplices development is connected to
the native `MixedGame` representation by `NashEquilibrium.MixedBrouwer`.
Prisoner's Dilemma has a dominant defection profile, matching pennies has no
pure equilibrium and a uniform mixed equilibrium, coordination has two pure
equilibria, and rock-paper-scissors has a uniform mixed equilibrium.

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
mathematical statement with one proof hole and imports only Mathlib. Solution.lean
imports the native implementation and provides the checked proofs under the matching namespace
NashEquilibrium.Palomar.

The selected declarations are:

    NashEquilibrium.Palomar.exists_nash_maximizing_ordinal_potential
    NashEquilibrium.Palomar.isNash_iff_potential_local_maximum
    NashEquilibrium.Palomar.no_betterResponse_cycle_of_generalized_ordinal_potential
    NashEquilibrium.Palomar.weaklyAcyclic_of_generalized_ordinal_potential
    NashEquilibrium.Palomar.mixedNash_support_payoff_eq

The Comparator definition targets make the Game, profile, deviation, Nash,
standard/generalized potential, maximizer, local-maximum, and better-response
interfaces explicit, and also checks the mixed-profile, finite payoff, and
support-payoff interfaces. The main Challenge theorem returns a reusable
certificate containing both equilibrium stability and global potential
maximality; it is stronger than a bare existential conclusion.

## Literature and positioning

The equilibrium concept and its mixed-strategy existence theorem originate in
[Nash's 1950 PNAS paper](https://doi.org/10.1073/pnas.36.1.48) and the expanded
[1951 treatment](https://doi.org/10.2307/1969529). The terminology follows
[Monderer and Shapley, *Potential Games*](https://doi.org/10.1006/game.1996.0044):
the standard ordinal notion matches strict payoff and potential comparisons in
both directions. The weaker one-way condition is tracked separately as a
generalized ordinal potential. [Rosenthal's congestion-game paper](https://doi.org/10.1007/BF01737559)
is the foundational precursor for potential-based pure-equilibrium existence.
For later structural context, see [Candogan, Menache, Ozdaglar, and Parrilo](https://doi.org/10.1287/moor.1110.0500).

Relevant formalization literature includes [Le Roux, Martin-Dorel, and Smaus,
*An Existence Theorem of Nash Equilibrium in Coq and Isabelle*](https://doi.org/10.4204/EPTCS.256.4),
which formally studies a Nash-existence theorem in both Coq and Isabelle. The
closest directly comparable formalization literature for potential games is
[Bagnall, Merten, and Stewart's Ssreflect/Coq library](https://jfr.unibo.it/article/view/7235),
which covers potential games and best-response dynamics. The companion
[Isabelle/AFP entry](https://isa-afp.org/entries/Nash_Equilibrium.html) covers
finite pure and mixed Nash equilibria, including a Brouwer-based general mixed
existence theorem. The fixed-point layer used here is the independently
published Lean development [*Formalizing Scarf, Brouwer, and Nash in
Lean*](https://arxiv.org/abs/2607.05987), whose source is preserved with
attribution in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md). This repository
adds the native bridge to its own mixed-game definitions; it does not claim
priority for the Scarf/Brouwer proof or a file-level translation of the AFP
entry.

## Relationship to the Isabelle/AFP entry

The mathematical scope is informed by the published AFP entry
[Nash Equilibria for Finite Games in Isabelle/HOL](https://isa-afp.org/entries/Nash_Equilibrium.html).
The Lean development changes the definitions and proof architecture. It now
matches the AFP entry's finite mixed-strategy existence result at the theorem
level through support/Dirac lemmas, the normalized excess map, and a
kernel-checked product-simplex Brouwer theorem, while retaining a different
native profile representation. In particular, it does not silently call the one-way improvement implication
"ordinal"; it names that class generalized and reserves the standard name for
the bidirectional condition. The Scarf/Brouwer core is included as an
attributed third-party dependency, and `NashEquilibrium.MixedBrouwer` supplies
the Lean-native reindexing and payoff-map bridge. The empty-player edge case is
handled directly, so the exported theorem covers every finite game with a
nonempty move type.

## Status

The mixed-Nash existence layer builds successfully under the pinned Lean and
Mathlib versions and has an explicit third-party license/attribution record.
Palomar Comparator verification, editorial review, and registration remain
separate states and are not inferred from local compilation.
