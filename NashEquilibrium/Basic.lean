import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi

/-!
# Finite strategic-form games

This module gives a native Lean presentation of finite strategic-form games.
Players and moves are finite types, while each player may have a finite
player-specific set of legal moves.  The potential layer distinguishes the
standard ordinal sign-equivalence from the weaker generalized implication.
Finite maxima yield a Nash certificate, while better-response paths expose the
corresponding finite dynamics.
-/

namespace NashEquilibrium

universe u v w z

abbrev Profile (Player : Type u) (Move : Type v) := Player → Move

structure Game (Player : Type u) (Move : Type v) (Utility : Type w)
    [Fintype Player] [Fintype Move] [DecidableEq Player] [DecidableEq Move] where
  /-- The finite set of legal moves available to each player. -/
  strategies : Player → Finset Move
  /-- The payoff received by a player at a pure strategy profile. -/
  payoff : Player → Profile Player Move → Utility
  /-- Every player has at least one legal move. -/
  nonempty_strategies : ∀ p, (strategies p).Nonempty

variable {Player : Type u} {Move : Type v} {Utility : Type w}
variable {PotentialValue : Type z}
variable [Fintype Player] [Fintype Move] [DecidableEq Player] [DecidableEq Move]

/-- A profile is legal when every player chooses one of their moves. -/
def IsProfile (G : Game Player Move Utility) (s : Profile Player Move) : Prop :=
  ∀ p, s p ∈ G.strategies p

/-- Change only player `p`'s move in a profile. -/
def deviation (s : Profile Player Move) (p : Player) (a : Move) :
    Profile Player Move :=
  Function.update s p a

omit [Fintype Player] [Fintype Move] [DecidableEq Move] in
@[simp]
theorem deviation_same (s : Profile Player Move) (p : Player) (a : Move) :
    deviation s p a p = a := by
  simp [deviation]

omit [Fintype Player] [Fintype Move] [DecidableEq Move] in
theorem deviation_other {s : Profile Player Move} {p q : Player} {a : Move}
    (h : q ≠ p) : deviation s p a q = s q := by
  simp [deviation, h]

/-- A profile is a pure Nash equilibrium when no legal unilateral deviation
improves its deviating player's payoff. -/
def IsNash [Preorder Utility] (G : Game Player Move Utility)
    (s : Profile Player Move) : Prop :=
  IsProfile G s ∧
    ∀ p a, a ∈ G.strategies p → G.payoff p (deviation s p a) ≤ G.payoff p s

/-- `a` is a best response to the opponents' choices in `s`. -/
def IsBestResponse [Preorder Utility] (G : Game Player Move Utility)
    (s : Profile Player Move) (p : Player) (a : Move) : Prop :=
  a ∈ G.strategies p ∧
    ∀ b, b ∈ G.strategies p →
      G.payoff p (deviation s p b) ≤ G.payoff p (deviation s p a)

/-- A move is dominant if it is at least as good as every legal move at every
legal profile. -/
def IsDominant [Preorder Utility] (G : Game Player Move Utility)
    (p : Player) (a : Move) : Prop :=
  a ∈ G.strategies p ∧
    ∀ s, IsProfile G s → ∀ b, b ∈ G.strategies p →
      G.payoff p (deviation s p b) ≤ G.payoff p (deviation s p a)

theorem isNash_iff_bestResponse [Preorder Utility]
    {G : Game Player Move Utility} {s : Profile Player Move}
    (hs : IsProfile G s) :
    IsNash G s ↔ ∀ p, IsBestResponse G s p (s p) := by
  constructor
  · intro h
    rcases h with ⟨_, hNash⟩
    intro p
    refine ⟨hs p, ?_⟩
    intro a ha
    simpa [deviation] using hNash p a ha
  · intro h
    refine ⟨hs, ?_⟩
    intro p a ha
    have hp := h p
    exact (hp.2 a ha).trans_eq (by simp [deviation])

theorem dominant_profile_isNash [Preorder Utility]
    (G : Game Player Move Utility) (dominant : Player → Move)
    (hdom : ∀ p, IsDominant G p (dominant p)) :
    IsNash G (fun p => dominant p) := by
  have hprofile : IsProfile G (fun p => dominant p) := by
    intro p
    exact (hdom p).1
  refine ⟨hprofile, ?_⟩
  intro p a ha
  have h := (hdom p).2 (fun q => dominant q) hprofile a ha
  simpa [deviation] using h

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

/--
The generalized ordinal-potential condition: every strict unilateral payoff
improvement strictly increases the potential.

This is the one-way condition used for finite-improvement arguments.  It is
strictly weaker than the standard ordinal-potential equivalence: a generalized
potential is allowed to increase on a payoff-neutral deviation.
-/
def IsGeneralizedOrdinalPotential [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue) : Prop :=
  ∀ {s p a}, IsProfile G s → a ∈ G.strategies p →
    G.payoff p s < G.payoff p (deviation s p a) →
      potential s < potential (deviation s p a)

/--
The standard ordinal-potential condition: the strict payoff and potential
comparisons agree in both directions for every legal unilateral deviation.

Unlike `IsGeneralizedOrdinalPotential`, this bidirectional condition rules out
strict potential ascent on payoff-neutral deviations (apply it to the reverse
deviation as well).
-/
def IsOrdinalPotential [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue) : Prop :=
  ∀ {s p a}, IsProfile G s → a ∈ G.strategies p →
    (G.payoff p s < G.payoff p (deviation s p a) ↔
      potential s < potential (deviation s p a))

/-- Every standard ordinal potential is also a generalized ordinal potential. -/
theorem ordinalPotential_isGeneralized
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsOrdinalPotential G potential) :
    IsGeneralizedOrdinalPotential G potential := by
  intro s p a hs ha himprove
  exact (hpotential hs ha).mp himprove

/-- A legal profile whose potential dominates every other legal profile. -/
def IsPotentialMaximizer [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (s : Profile Player Move) : Prop :=
  IsProfile G s ∧ ∀ t, IsProfile G t → potential t ≤ potential s

/-- A legal unilateral payoff improvement viewed as a directed profile edge. -/
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

/-- Concatenate two nonempty better-response paths. -/
theorem betterResponsePath_trans
    [LinearOrder Utility]
    (G : Game Player Move Utility)
    {s t u : Profile Player Move}
    (h₁ : BetterResponsePath G s t)
    (h₂ : BetterResponsePath G t u) :
    BetterResponsePath G s u := by
  induction h₁ with
  | single hstep =>
      exact BetterResponsePath.tail hstep h₂
  | tail hstep hrest ih =>
      exact BetterResponsePath.tail hstep (ih h₂)

/-- A generalized ordinal potential rules out directed better-response cycles. -/
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

/--
Every legal starting profile can reach a pure Nash equilibrium by a finite
sequence of better responses.  This is the weak-acyclicity consequence of a
finite generalized ordinal potential.
-/
def IsWeaklyAcyclic [LinearOrder Utility]
    (G : Game Player Move Utility) : Prop :=
  ∀ s, IsProfile G s →
    ∃ t, IsNash G t ∧ (t = s ∨ BetterResponsePath G s t)

/-- Finite generalized ordinal-potential games are weakly acyclic. -/
theorem weaklyAcyclic_of_generalized_ordinal_potential
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsGeneralizedOrdinalPotential G potential) :
    IsWeaklyAcyclic G := by
  classical
  have htrans : IsTrans (Profile Player Move) (Function.swap (BetterResponsePath G)) :=
    ⟨fun _ _ _ h₁ h₂ => betterResponsePath_trans G h₂ h₁⟩
  have hirrefl : Std.Irrefl (Function.swap (BetterResponsePath G)) :=
    ⟨fun _ h => no_betterResponse_cycle_of_generalized_ordinal_potential
      G potential hpotential h⟩
  have hwellFounded : WellFounded (Function.swap (BetterResponsePath G)) :=
    @Finite.wellFounded_of_trans_of_irrefl
      (Profile Player Move) inferInstance (Function.swap (BetterResponsePath G)) htrans hirrefl
  let C : Profile Player Move → Prop := fun s =>
    IsProfile G s → ∃ t, IsNash G t ∧ (t = s ∨ BetterResponsePath G s t)
  have hC : ∀ s, C s := by
    intro s
    refine hwellFounded.induction s ?_
    intro s ih hs
    by_cases hs_nash : IsNash G s
    · exact ⟨s, hs_nash, Or.inl rfl⟩
    · have himprove_exists :
          ∃ p a, a ∈ G.strategies p ∧
            G.payoff p s < G.payoff p (deviation s p a) := by
        by_contra hnone
        apply hs_nash
        refine ⟨hs, ?_⟩
        intro p a ha
        by_contra hnot
        apply hnone
        exact ⟨p, a, ha, lt_of_not_ge hnot⟩
      rcases himprove_exists with ⟨p, a, ha, himprove⟩
      have hdeviation_profile : IsProfile G (deviation s p a) :=
        deviation_isProfile G hs ha
      have hstep : BetterResponsePath G s (deviation s p a) :=
        BetterResponsePath.single
          ⟨hs, hdeviation_profile, ⟨p, a, ha, rfl, himprove⟩⟩
      obtain ⟨t, ht_nash, ht_path⟩ :=
        ih (deviation s p a) hstep hdeviation_profile
      refine ⟨t, ht_nash, ?_⟩
      rcases ht_path with rfl | ht_path
      · exact Or.inr hstep
      · exact Or.inr (betterResponsePath_trans G hstep ht_path)
  exact hC

/-- A standard ordinal potential identifies Nash equilibria with local maxima. -/
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

/--
A finite generalized ordinal-potential game has a Nash equilibrium that is a
global potential maximizer.

The returned maximizer is a reusable certificate: it proves both equilibrium
stability and domination of the potential over every legal profile.
-/
theorem exists_nash_maximizing_generalized_ordinal_potential
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsGeneralizedOrdinalPotential G potential) :
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
      hpotential hs_profile ha himprove
    exact (not_lt_of_ge (hmax _ hdeviation_mem)) hpotential_rises
  exact ⟨s, hs_nash, ⟨hs_profile, hmax_profile⟩⟩

/-- A standard ordinal potential has a global maximizer that is Nash. -/
theorem exists_nash_maximizing_ordinal_potential
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsOrdinalPotential G potential) :
    ∃ s, IsNash G s ∧ IsPotentialMaximizer G potential s := by
  exact exists_nash_maximizing_generalized_ordinal_potential G potential
    (ordinalPotential_isGeneralized G potential hpotential)

/-- Existence of a pure Nash equilibrium for a generalized ordinal potential. -/
theorem exists_nash_of_generalized_ordinal_potential
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsGeneralizedOrdinalPotential G potential) :
    ∃ s, IsNash G s := by
  rcases exists_nash_maximizing_generalized_ordinal_potential
      G potential hpotential with ⟨s, hs, _⟩
  exact ⟨s, hs⟩

/-- Existence of a pure Nash equilibrium for the standard ordinal potential. -/
theorem exists_nash_of_ordinal_potential
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsOrdinalPotential G potential) :
    ∃ s, IsNash G s := by
  exact exists_nash_of_generalized_ordinal_potential G potential
    (ordinalPotential_isGeneralized G potential hpotential)

end NashEquilibrium
