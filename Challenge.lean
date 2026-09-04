import Mathlib.Data.Finset.Max

namespace NashEquilibrium

universe u v w z

/-!
# Palomar statement surface

This is the small, standalone statement that a mathematical reader audits.
The implementation and proof live in the native `NashEquilibrium` library and
are deliberately not imported here.
-/

abbrev Profile (Player : Type u) (Move : Type v) := Player → Move

structure Game (Player : Type u) (Move : Type v) (Utility : Type w)
    [Fintype Player] [Fintype Move] [DecidableEq Player] [DecidableEq Move] where
  strategies : Player → Finset Move
  payoff : Player → Profile Player Move → Utility
  nonempty_strategies : ∀ p, (strategies p).Nonempty

variable {Player : Type u} {Move : Type v} {Utility : Type w}
variable {PotentialValue : Type z}
variable [Fintype Player] [Fintype Move] [DecidableEq Player] [DecidableEq Move]

def IsProfile (G : Game Player Move Utility) (s : Profile Player Move) : Prop :=
  ∀ p, s p ∈ G.strategies p

def deviation (s : Profile Player Move) (p : Player) (a : Move) :
    Profile Player Move :=
  Function.update s p a

def IsNash [Preorder Utility] (G : Game Player Move Utility)
    (s : Profile Player Move) : Prop :=
  IsProfile G s ∧
    ∀ p a, a ∈ G.strategies p → G.payoff p (deviation s p a) ≤ G.payoff p s

def IsOrdinalPotential [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue) : Prop :=
  ∀ {s p a}, IsProfile G s → a ∈ G.strategies p →
    G.payoff p s < G.payoff p (deviation s p a) →
      potential s < potential (deviation s p a)

namespace Palomar

theorem exists_nash_of_ordinal_potential
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsOrdinalPotential G potential) :
    ∃ s, IsNash G s := by
  sorry

end Palomar

end NashEquilibrium
