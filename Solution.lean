import NashEquilibrium.Basic

namespace NashEquilibrium.Palomar

universe u v w z

variable {Player : Type u} {Move : Type v} {Utility : Type w}
variable {PotentialValue : Type z}
variable [Fintype Player] [Fintype Move] [DecidableEq Player] [DecidableEq Move]

/-! The checked proofs corresponding to the Palomar statement surface. -/

theorem exists_nash_maximizing_ordinal_potential
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsOrdinalPotential G potential) :
    ∃ s, IsNash G s ∧ IsPotentialMaximizer G potential s := by
  exact NashEquilibrium.exists_nash_maximizing_ordinal_potential
    G potential hpotential

theorem isNash_iff_potential_local_maximum
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsOrdinalPotential G potential)
    {s : Profile Player Move} :
    IsNash G s ↔ IsPotentialLocalMaximum G potential s := by
  exact NashEquilibrium.isNash_iff_potential_local_maximum
    G potential hpotential

theorem no_betterResponse_cycle_of_generalized_ordinal_potential
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsGeneralizedOrdinalPotential G potential)
    {s : Profile Player Move} :
    ¬ BetterResponsePath G s s := by
  exact NashEquilibrium.no_betterResponse_cycle_of_generalized_ordinal_potential
    G potential hpotential

theorem weaklyAcyclic_of_generalized_ordinal_potential
    [LinearOrder Utility] [LinearOrder PotentialValue]
    (G : Game Player Move Utility)
    (potential : Profile Player Move → PotentialValue)
    (hpotential : IsGeneralizedOrdinalPotential G potential) :
    IsWeaklyAcyclic G := by
  exact NashEquilibrium.weaklyAcyclic_of_generalized_ordinal_potential
    G potential hpotential

end NashEquilibrium.Palomar
