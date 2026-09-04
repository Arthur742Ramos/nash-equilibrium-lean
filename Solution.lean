import NashEquilibrium.Basic

namespace NashEquilibrium.Palomar

universe u v w z

variable {Player : Type u} {Move : Type v} {Utility : Type w}
variable {PotentialValue : Type z}
variable [Fintype Player] [Fintype Move] [DecidableEq Player] [DecidableEq Move]

/-! The checked proof corresponding to the Palomar statement surface. -/

theorem exists_nash_of_ordinal_potential
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsOrdinalPotential G potential) :
    ∃ s, IsNash G s := by
  exact NashEquilibrium.exists_nash_of_ordinal_potential G potential hpotential

end NashEquilibrium.Palomar
