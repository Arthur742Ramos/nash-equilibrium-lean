# Scoped Isabelle and Lean comparison

Checked against the published [pure theory](https://isa-afp.org/browser_info/current/AFP/Nash_Equilibrium/Nash_Equilibrium.html)
and [mixed theory](https://isa-afp.org/browser_info/current/AFP/Nash_Equilibrium/Mixed_Nash_Equilibrium.html).
This is an informal correspondence, not a machine-checked translation.

| Result or boundary | Isabelle/AFP | This Lean library |
| --- | --- | --- |
| Pure potential existence | `finite_potential_game.exists_Nash_equilibrium`, with a one-way improvement assumption | `exists_nash_of_generalized_ordinal_potential`; the selected standard-potential theorem additionally returns global maximality |
| Potential semantics | `potential_increases` is an implication | Separate `IsGeneralizedOrdinalPotential` and bidirectional `IsOrdinalPotential`; checked neutral-deviation counterexample |
| Pure representation | Active player set and player-specific strategy sets | All members of `Player` are active; player-specific legal `Finset`s |
| Dynamics interface | The cited pure existence argument maximizes potential | Explicit better-response paths, no-cycle theorem, and weak-acyclicity certificate; no claim that these classical consequences are new |
| Mixed existence | Brouwer applied to the normalized payoff-excess map | `exists_mixedNash`, via native topology and a bridge to the attributed product-simplex theorem |
| Mixed representation | Real finite-coordinate profiles, common finite strategy type | `Player → Move → ℝ`, common finite nonempty `Move`; empty `Player` also allowed |

The [entry abstract](https://isa-afp.org/entries/Nash_Equilibrium.html) advertises
support and Dirac results. This table does not assert declaration-level parity
for those results; they are not mapped individually here. Lean provides `mixedNash_support_payoff_eq`,
`mixedNash_zero_probability_if_less`, and `diracMixedNash_of_pure_deviations`.

The pure legal-move restrictions are not automatically transported to mixed
games. No dependent per-player move-type existence theorem, equilibrium
computation algorithm, complexity bound, or certified cross-prover equivalence
is claimed.

## Contribution and reuse

The [Lyu–Li development](https://arxiv.org/abs/2607.05987) already proves Scarf,
Brouwer, and Nash in Lean. Four upstream files are reused, not rederived here;
their exact revision and MIT terms are in THIRD_PARTY_NOTICES.md. This project's
work is the native game API, potential semantics, finite-dynamics interface,
mixed-game adapter, examples, and selected statement/solution verification.
This comparison documents scope and engineering choices, not mathematical
priority or evidence of a research-level extension.
