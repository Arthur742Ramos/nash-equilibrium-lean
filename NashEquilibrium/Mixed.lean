import NashEquilibrium.Basic

/-!
# Finite mixed strategies

This module records the finite mixed-strategy layer natively in Lean.  A
mixed profile assigns a nonnegative real weight to every player/move pair,
with weights summing to one for each player.  The expected payoff of a pure
deviation is defined by finite enumeration of the opponents' pure profiles.
The concrete matching-pennies and rock-paper-scissors equilibria are proved
in `NashEquilibrium.Examples`.
-/

namespace NashEquilibrium

universe u v

open scoped BigOperators

abbrev MixedProfile (Player : Type u) (Move : Type v) := Player → Move → ℝ

structure MixedGame (Player : Type u) (Move : Type v)
    [Fintype Player] [Fintype Move] [DecidableEq Player] [DecidableEq Move] where
  /-- The real-valued payoff at a pure profile. -/
  payoff : Player → Profile Player Move → ℝ

variable {Player : Type u} {Move : Type v}
variable [Fintype Player] [Fintype Move] [DecidableEq Player] [DecidableEq Move]

/-- A mixed profile is a probability distribution over moves for every player. -/
def IsMixedProfile (m : MixedProfile Player Move) : Prop :=
  (∀ p a, 0 ≤ m p a) ∧ ∀ p, ∑ a : Move, m p a = 1

/-- The product of the opponents' probabilities at a pure profile. -/
def opponentWeight (m : MixedProfile Player Move) (p : Player)
    (s : Profile Player Move) : ℝ :=
  ∏ q ∈ Finset.univ.erase p, m q (s q)

/-- Expected payoff from fixing player `p` to move `a` and mixing opponents. -/
def pureDeviationPayoff (G : MixedGame Player Move) (m : MixedProfile Player Move)
    (p : Player) (a : Move) : ℝ :=
  ∑ s : Profile Player Move,
    if s p = a then opponentWeight m p s * G.payoff p s else 0

/-- Expected payoff of a mixed strategy against the opponents' profile. -/
def mixedPayoff (G : MixedGame Player Move) (m : MixedProfile Player Move)
    (p : Player) : ℝ :=
  ∑ a : Move, m p a * pureDeviationPayoff G m p a

/-- The finite mixed Nash condition. -/
def IsMixedNash (G : MixedGame Player Move) (m : MixedProfile Player Move) : Prop :=
  IsMixedProfile m ∧ ∀ p a, pureDeviationPayoff G m p a ≤ mixedPayoff G m p

/-- The uniform mixed profile on a nonempty finite move type. -/
noncomputable def uniformMixedProfile [Nonempty Move] : MixedProfile Player Move :=
  fun _ _ => (Fintype.card Move : ℝ)⁻¹

theorem uniformMixedProfile_isMixedProfile [Nonempty Move] :
    IsMixedProfile (uniformMixedProfile (Player := Player) (Move := Move)) := by
  classical
  have hcard : (0 : ℝ) < Fintype.card Move := by
    exact_mod_cast Fintype.card_pos
  constructor
  · intro p a
    exact inv_nonneg.mpr (le_of_lt hcard)
  · intro p
    simp [uniformMixedProfile, hcard.ne']

end NashEquilibrium
