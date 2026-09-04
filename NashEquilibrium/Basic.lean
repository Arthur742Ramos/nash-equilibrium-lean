import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi

/-!
# Finite strategic-form games

This module gives a native Lean presentation of finite strategic-form games.
Players and moves are finite types, while each player may have a finite
player-specific set of legal moves.  The central existence theorem uses the
finite maximum principle: a finite ordinal-potential game has a pure Nash
equilibrium.
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

/-- Every strict unilateral improvement strictly increases `potential`. -/
def IsOrdinalPotential [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue) : Prop :=
  ∀ {s p a}, IsProfile G s → a ∈ G.strategies p →
    G.payoff p s < G.payoff p (deviation s p a) →
      potential s < potential (deviation s p a)

/-- A finite ordinal-potential game has a pure Nash equilibrium.

The proof is constructive up to the finite maximum theorem: choose a legal
profile maximizing the potential.  A profitable deviation would be legal and
would have strictly larger potential, contradicting maximality. -/
theorem exists_nash_of_ordinal_potential
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsOrdinalPotential G potential) :
    ∃ s, IsNash G s := by
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
  refine ⟨s, hs_profile, ?_⟩
  intro p a ha
  by_contra hnot
  have himprove : G.payoff p s < G.payoff p (deviation s p a) :=
    lt_of_not_ge hnot
  have hdeviation_profile : IsProfile G (deviation s p a) := by
    intro q
    by_cases hqp : q = p
    · subst q
      simpa [deviation] using ha
    · simpa [deviation, hqp] using hs_profile q
  have hdeviation_mem : deviation s p a ∈ legal :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdeviation_profile⟩
  have hpotential : potential s < potential (deviation s p a) :=
    hpotential hs_profile ha himprove
  exact (not_lt_of_ge (hmax _ hdeviation_mem)) hpotential

end NashEquilibrium
