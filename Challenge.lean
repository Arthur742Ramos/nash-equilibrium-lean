import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace NashEquilibrium

universe u v w z

/-!
# Palomar statement surface

This is the small, standalone statement that a mathematical reader audits.
The implementation and proof live in the native `NashEquilibrium` library and
are deliberately not imported here.
-/

/-- A pure strategy profile assigns one move to every player. -/
abbrev Profile (Player : Type u) (Move : Type v) := Player → Move

/-- A finite strategic-form game with player-specific legal move sets. -/
structure Game (Player : Type u) (Move : Type v) (Utility : Type w)
    [Fintype Player] [Fintype Move] [DecidableEq Player] [DecidableEq Move] where
  /-- The finite set of legal moves available to each player. -/
  strategies : Player → Finset Move
  /-- The payoff received by a player at a pure profile. -/
  payoff : Player → Profile Player Move → Utility
  /-- Every player has at least one legal move. -/
  nonempty_strategies : ∀ p, (strategies p).Nonempty

variable {Player : Type u} {Move : Type v} {Utility : Type w}
variable {PotentialValue : Type z}
variable [Fintype Player] [Fintype Move] [DecidableEq Player] [DecidableEq Move]

/-- A profile is legal when every player chooses a legal move. -/
def IsProfile (G : Game Player Move Utility) (s : Profile Player Move) : Prop :=
  ∀ p, s p ∈ G.strategies p

/-- Change only player `p`'s move in a profile. -/
def deviation (s : Profile Player Move) (p : Player) (a : Move) :
    Profile Player Move :=
  Function.update s p a

/-- A profile is a pure Nash equilibrium when no legal deviation improves payoffs. -/
def IsNash [Preorder Utility] (G : Game Player Move Utility)
    (s : Profile Player Move) : Prop :=
  IsProfile G s ∧
    ∀ p a, a ∈ G.strategies p → G.payoff p (deviation s p a) ≤ G.payoff p s

/-- The generalized ordinal-potential condition, with a one-way implication. -/
def IsGeneralizedOrdinalPotential [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue) : Prop :=
  ∀ {s p a}, IsProfile G s → a ∈ G.strategies p →
    G.payoff p s < G.payoff p (deviation s p a) →
      potential s < potential (deviation s p a)

/-- The standard ordinal-potential condition, requiring strict-sign equivalence. -/
def IsOrdinalPotential [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue) : Prop :=
  ∀ {s p a}, IsProfile G s → a ∈ G.strategies p →
    (G.payoff p s < G.payoff p (deviation s p a) ↔
      potential s < potential (deviation s p a))

/-- A legal profile that globally maximizes the potential over legal profiles. -/
def IsPotentialMaximizer [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (s : Profile Player Move) : Prop :=
  IsProfile G s ∧ ∀ t, IsProfile G t → potential t ≤ potential s

/-- A legal unilateral payoff improvement as a directed profile edge. -/
def IsBetterResponseStep [LinearOrder Utility]
    (G : Game Player Move Utility)
    (s t : Profile Player Move) : Prop :=
  IsProfile G s ∧ IsProfile G t ∧
    ∃ p a, a ∈ G.strategies p ∧ t = deviation s p a ∧
      G.payoff p s < G.payoff p t

/-- A nonempty finite path of legal better-response steps. -/
inductive BetterResponsePath [LinearOrder Utility]
    (G : Game Player Move Utility) :
    Profile Player Move → Profile Player Move → Prop where
  | single {s t} : IsBetterResponseStep G s t → BetterResponsePath G s t
  | tail {s t u} : IsBetterResponseStep G s t →
      BetterResponsePath G t u → BetterResponsePath G s u

/-- A profile is a potential local maximum when no legal deviation raises it. -/
def IsPotentialLocalMaximum [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (s : Profile Player Move) : Prop :=
  IsProfile G s ∧
    ∀ p a, a ∈ G.strategies p →
      potential (deviation s p a) ≤ potential s

/-- Every legal starting profile can reach a Nash profile by better responses. -/
def IsWeaklyAcyclic [LinearOrder Utility]
    (G : Game Player Move Utility) : Prop :=
  ∀ s, IsProfile G s →
    ∃ t, IsNash G t ∧ (t = s ∨ BetterResponsePath G s t)

/-- A legal unilateral deviation from a legal profile is again legal. -/
theorem deviation_isProfile
    (G : Game Player Move Utility)
    {s : Profile Player Move} {p : Player} {a : Move}
    (hs : IsProfile G s) (ha : a ∈ G.strategies p) :
    IsProfile G (deviation s p a) := by
  intro q
  by_cases hqp : q = p
  · subst q
    simpa [deviation] using ha
  · simpa [deviation, hqp] using hs q

/-! A compact mixed-strategy statement surface.  These definitions mirror the
native mixed layer, while the selected theorem below is proved directly from
finite sums and the probability constraints. -/

abbrev MixedProfile (Player : Type u) (Move : Type v) := Player → Move → ℝ

structure MixedGame (Player : Type u) (Move : Type v)
    [Fintype Player] [Fintype Move] [DecidableEq Player] [DecidableEq Move] where
  payoff : Player → Profile Player Move → ℝ

def IsMixedProfile (m : MixedProfile Player Move) : Prop :=
  (∀ p a, 0 ≤ m p a) ∧ ∀ p, ∑ a : Move, m p a = 1

def opponentWeight (m : MixedProfile Player Move) (p : Player)
    (s : Profile Player Move) : ℝ :=
  ∏ q ∈ Finset.univ.erase p, m q (s q)

def pureDeviationPayoff (G : MixedGame Player Move) (m : MixedProfile Player Move)
    (p : Player) (a : Move) : ℝ :=
  ∑ s : Profile Player Move,
    if s p = a then opponentWeight m p s * G.payoff p s else 0

def mixedPayoff (G : MixedGame Player Move) (m : MixedProfile Player Move)
    (p : Player) : ℝ :=
  ∑ a : Move, m p a * pureDeviationPayoff G m p a

def IsMixedNash (G : MixedGame Player Move) (m : MixedProfile Player Move) : Prop :=
  IsMixedProfile m ∧ ∀ p a, pureDeviationPayoff G m p a ≤ mixedPayoff G m p

namespace Palomar

/--
A standard ordinal-potential game has a Nash profile that globally maximizes
the potential.
-/
theorem exists_nash_maximizing_ordinal_potential
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsOrdinalPotential G potential) :
    ∃ s, IsNash G s ∧ IsPotentialMaximizer G potential s := by
  classical
  let legal : Finset (Profile Player Move) :=
    Finset.univ.filter (fun s => IsProfile G s)
  have hlegal : legal.Nonempty := by
    let s : Profile Player Move := fun p => Classical.choose (G.nonempty_strategies p)
    have hs : IsProfile G s := by
      intro p
      exact Classical.choose_spec (G.nonempty_strategies p)
    exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image legal potential hlegal
  have hs_profile : IsProfile G s := (Finset.mem_filter.mp hs).2
  have hmax_profile : ∀ t, IsProfile G t → potential t ≤ potential s := by
    intro t ht
    exact hmax t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)
  have hs_nash : IsNash G s := by
    refine ⟨hs_profile, ?_⟩
    intro p a ha
    by_contra hnot
    have himprove : G.payoff p s < G.payoff p (deviation s p a) :=
      lt_of_not_ge hnot
    have hdeviation_profile : IsProfile G (deviation s p a) :=
      deviation_isProfile G hs_profile ha
    have hdeviation_mem : deviation s p a ∈ legal :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdeviation_profile⟩
    have hpotential_rises :
        potential s < potential (deviation s p a) :=
      (hpotential hs_profile ha).mp himprove
    exact (not_lt_of_ge (hmax _ hdeviation_mem)) hpotential_rises
  exact ⟨s, hs_nash, ⟨hs_profile, hmax_profile⟩⟩

/-- Standard ordinal potentials identify pure Nash equilibria with local maxima. -/
theorem isNash_iff_potential_local_maximum
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsOrdinalPotential G potential)
    {s : Profile Player Move} :
    IsNash G s ↔ IsPotentialLocalMaximum G potential s := by
  constructor
  · intro hs
    rcases hs with ⟨hs_profile, hs_nash⟩
    refine ⟨hs_profile, ?_⟩
    intro p a ha
    by_contra hnot
    have hpotential_rises :
        potential s < potential (deviation s p a) := lt_of_not_ge hnot
    have himprove :
        G.payoff p s < G.payoff p (deviation s p a) :=
      (hpotential hs_profile ha).mpr hpotential_rises
    exact (not_lt_of_ge (hs_nash p a ha)) himprove
  · intro hs
    rcases hs with ⟨hs_profile, hs_local⟩
    refine ⟨hs_profile, ?_⟩
    intro p a ha
    by_contra hnot
    have himprove :
        G.payoff p s < G.payoff p (deviation s p a) := lt_of_not_ge hnot
    have hpotential_rises :
        potential s < potential (deviation s p a) :=
      (hpotential hs_profile ha).mp himprove
    exact (not_lt_of_ge (hs_local p a ha)) hpotential_rises

/-- Better-response edges strictly ascend every generalized ordinal potential. -/
theorem betterResponseStep_potential_increases
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsGeneralizedOrdinalPotential G potential)
    {s t : Profile Player Move}
    (hstep : IsBetterResponseStep G s t) :
    potential s < potential t := by
  rcases hstep with ⟨hs, _, ⟨p, a, ha, ht, himprove⟩⟩
  subst t
  exact hpotential hs ha himprove

/-- Every nonempty better-response path strictly ascends the potential. -/
theorem betterResponsePath_potential_strict
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsGeneralizedOrdinalPotential G potential)
    {s t : Profile Player Move}
    (hpath : BetterResponsePath G s t) :
    potential s < potential t := by
  induction hpath with
  | single hstep =>
      exact betterResponseStep_potential_increases G potential hpotential hstep
  | tail hstep hrest ih =>
      exact (betterResponseStep_potential_increases G potential hpotential hstep).trans ih

/-- A generalized ordinal potential makes the better-response relation acyclic. -/
theorem no_betterResponse_cycle_of_generalized_ordinal_potential
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsGeneralizedOrdinalPotential G potential)
    {s : Profile Player Move} :
    ¬ BetterResponsePath G s s := by
  intro hcycle
  exact (lt_irrefl (potential s))
    (betterResponsePath_potential_strict G potential hpotential hcycle)

/-- Finite generalized ordinal-potential games are weakly acyclic. -/
theorem weaklyAcyclic_of_generalized_ordinal_potential
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsGeneralizedOrdinalPotential G potential) :
    IsWeaklyAcyclic G := by
  sorry

/-- A mixed Nash equilibrium equalizes every pure move in its support. -/
theorem mixedNash_support_payoff_eq
    {G : MixedGame Player Move} {m : MixedProfile Player Move}
    (h : IsMixedNash G m) {p : Player} {a : Move} (ha : 0 < m p a) :
    pureDeviationPayoff G m p a = mixedPayoff G m p := by
  have hm : IsMixedProfile m := h.1
  have hgap_nonneg (b : Move) :
      0 ≤ m p b * (mixedPayoff G m p - pureDeviationPayoff G m p b) := by
    exact mul_nonneg (hm.1 p b) (sub_nonneg.mpr (h.2 p b))
  have hsum :
      (∑ b : Move, m p b * (mixedPayoff G m p - pureDeviationPayoff G m p b)) = 0 := by
    calc
      (∑ b : Move, m p b * (mixedPayoff G m p - pureDeviationPayoff G m p b)) =
          (∑ b : Move, m p b * mixedPayoff G m p) -
            (∑ b : Move, m p b * pureDeviationPayoff G m p b) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ = (∑ b : Move, m p b) * mixedPayoff G m p - mixedPayoff G m p := by
        simp [mixedPayoff, Finset.sum_mul]
      _ = 0 := by
        rw [hm.2 p]
        ring
  have hterm :
      m p a * (mixedPayoff G m p - pureDeviationPayoff G m p a) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hgap_nonneg b)).mp hsum
      a (Finset.mem_univ a)
  have hdiff : mixedPayoff G m p - pureDeviationPayoff G m p a = 0 := by
    exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt ha)
  linarith

/-- Every finite real-payoff game on a common nonempty move type has a mixed equilibrium. -/
theorem exists_mixedNash [Nonempty Move] (G : MixedGame Player Move) :
    ∃ m : MixedProfile Player Move, IsMixedNash G m := by
  sorry

end Palomar

end NashEquilibrium
