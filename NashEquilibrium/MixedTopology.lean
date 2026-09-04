import NashEquilibrium.Mixed
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Separation.Hausdorff

/-!
# Finite-dimensional mixed-profile geometry

This module supplies the topological facts surrounding the normalized excess
map.  The mixed-profile set is closed, compact, convex, and nonempty, and the
payoff/excess/map operations are continuous.  Together with a separately
provided Brouwer theorem these are the analytic ingredients of the usual
general mixed-Nash existence proof.
-/

namespace NashEquilibrium

universe u v

open scoped BigOperators

variable {Player : Type u} {Move : Type v}
variable [Fintype Player] [Fintype Move] [DecidableEq Player] [DecidableEq Move]

/-- The set of finite mixed profiles. -/
def mixedProfiles : Set (MixedProfile Player Move) :=
  {m | IsMixedProfile m}

@[simp] theorem mem_mixedProfiles_iff (m : MixedProfile Player Move) :
    m ∈ mixedProfiles (Player := Player) (Move := Move) ↔ IsMixedProfile m :=
  Iff.rfl

theorem mixedProfiles_prob_nonneg
    {m : MixedProfile Player Move}
    (hm : m ∈ mixedProfiles (Player := Player) (Move := Move))
    (p : Player) (a : Move) :
    0 ≤ m p a := by
  exact hm.1 p a

theorem mixedProfiles_sum_prob
    {m : MixedProfile Player Move}
    (hm : m ∈ mixedProfiles (Player := Player) (Move := Move))
    (p : Player) :
    ∑ a : Move, m p a = 1 := by
  exact hm.2 p

theorem mixedProfiles_prob_le_one
    {m : MixedProfile Player Move}
    (hm : m ∈ mixedProfiles (Player := Player) (Move := Move))
    (p : Player) (a : Move) :
    m p a ≤ 1 := by
  calc
    m p a ≤ ∑ b : Move, m p b := by
      exact Finset.single_le_sum
        (fun b _ => mixedProfiles_prob_nonneg hm p b) (Finset.mem_univ a)
    _ = 1 := mixedProfiles_sum_prob hm p

theorem continuous_opponentWeight (p : Player) (s : Profile Player Move) :
    Continuous (fun m : MixedProfile Player Move => opponentWeight m p s) := by
  unfold opponentWeight
  apply continuous_finsetProd
  intro q hq
  exact (continuous_apply (s q)).comp (continuous_apply q)

theorem continuous_pureDeviationPayoff
    (G : MixedGame Player Move) (p : Player) (a : Move) :
    Continuous (fun m : MixedProfile Player Move => pureDeviationPayoff G m p a) := by
  unfold pureDeviationPayoff
  apply continuous_finsetSum
  intro s hs
  by_cases h : s p = a
  · simp only [if_pos h]
    exact (continuous_opponentWeight p s).mul continuous_const
  · simp only [if_neg h]
    exact continuous_const

theorem continuous_mixedPayoff
    (G : MixedGame Player Move) (p : Player) :
    Continuous (fun m : MixedProfile Player Move => mixedPayoff G m p) := by
  unfold mixedPayoff
  apply continuous_finsetSum
  intro a ha
  have hcoord : Continuous (fun m : MixedProfile Player Move => m p a) := by
    exact (continuous_apply a).comp (continuous_apply p)
  exact hcoord.mul (continuous_pureDeviationPayoff G p a)

theorem continuous_excess
    (G : MixedGame Player Move) (p : Player) (a : Move) :
    Continuous (fun m : MixedProfile Player Move => excess G m p a) := by
  unfold excess
  exact continuous_const.max
    ((continuous_pureDeviationPayoff G p a).sub (continuous_mixedPayoff G p))

theorem continuous_excessSum
    (G : MixedGame Player Move) (p : Player) :
    Continuous (fun m : MixedProfile Player Move => excessSum G m p) := by
  unfold excessSum
  apply continuous_finsetSum
  intro a ha
  exact continuous_excess G p a

theorem continuous_nashMap (G : MixedGame Player Move) :
    Continuous (nashMap G) := by
  apply continuous_pi
  intro p
  apply continuous_pi
  intro a
  rw [show (fun m : MixedProfile Player Move => nashMap G m p a) =
      (fun m => (m p a + excess G m p a) / (1 + excessSum G m p)) by
        funext m; rfl]
  have hnum : Continuous (fun m : MixedProfile Player Move =>
      m p a + excess G m p a) :=
    (by
      have hcoord : Continuous (fun m : MixedProfile Player Move => m p a) := by
        exact (continuous_apply a).comp (continuous_apply p)
      exact hcoord.add (continuous_excess G p a))
  have hden : Continuous (fun m : MixedProfile Player Move =>
      1 + excessSum G m p) :=
    continuous_const.add (continuous_excessSum G p)
  exact hnum.div hden (fun m => ne_of_gt (excessSum_denom_pos G m p))

theorem mixedProfiles_closed :
    IsClosed (mixedProfiles (Player := Player) (Move := Move)) := by
  have hnonneg : IsClosed {m : MixedProfile Player Move | ∀ p a, 0 ≤ m p a} := by
    have heq :
        {m : MixedProfile Player Move | ∀ p a, 0 ≤ m p a} =
          ⋂ p : Player, ⋂ a : Move, {m : MixedProfile Player Move | 0 ≤ m p a} := by
      ext m
      simp
    rw [heq]
    exact isClosed_iInter fun p => isClosed_iInter fun a => by
      have hcoord : Continuous (fun m : MixedProfile Player Move => m p a) := by
        exact (continuous_apply a).comp (continuous_apply p)
      have hpre : IsClosed
          ((fun m : MixedProfile Player Move => m p a) ⁻¹' Set.Ici (0 : ℝ)) :=
        isClosed_Ici.preimage hcoord
      simpa [Set.preimage] using hpre
  have hsum_cont (p : Player) :
      Continuous (fun m : MixedProfile Player Move => ∑ a : Move, m p a) := by
    apply continuous_finsetSum
    intro a ha
    exact (continuous_apply a).comp (continuous_apply p)
  have hsum : IsClosed {m : MixedProfile Player Move |
      ∀ p, ∑ a : Move, m p a = 1} := by
    have heq :
        {m : MixedProfile Player Move | ∀ p, ∑ a : Move, m p a = 1} =
          ⋂ p : Player, {m : MixedProfile Player Move | ∑ a : Move, m p a = 1} := by
      ext m
      simp
    rw [heq]
    exact isClosed_iInter fun p => isClosed_eq (hsum_cont p) continuous_const
  change IsClosed {m : MixedProfile Player Move |
    (∀ p a, 0 ≤ m p a) ∧ ∀ p, ∑ a : Move, m p a = 1}
  exact hnonneg.inter hsum

theorem mixedProfiles_subset_box :
    mixedProfiles (Player := Player) (Move := Move) ⊆
      Set.pi Set.univ (fun _ : Player =>
        Set.pi Set.univ (fun _ : Move => Set.Icc (0 : ℝ) 1)) := by
  intro m hm p hp
  have hmp : IsMixedProfile m := hm
  intro a ha
  exact ⟨hmp.1 p a, mixedProfiles_prob_le_one hm p a⟩

theorem mixedProfiles_compact :
    IsCompact (mixedProfiles (Player := Player) (Move := Move)) := by
  let box : Set (MixedProfile Player Move) :=
    Set.pi Set.univ (fun _ : Player =>
      Set.pi Set.univ (fun _ : Move => Set.Icc (0 : ℝ) 1))
  have hbox : IsCompact box := by
    apply isCompact_univ_pi
    intro p
    apply isCompact_univ_pi
    intro a
    exact isCompact_Icc
  apply IsCompact.of_isClosed_subset hbox mixedProfiles_closed
  exact mixedProfiles_subset_box

theorem mixedProfiles_convex :
    Convex ℝ (mixedProfiles (Player := Player) (Move := Move)) := by
  rw [convex_iff_add_mem]
  intro m hm n hn u v hu hv huv
  change IsMixedProfile (u • m + v • n)
  change IsMixedProfile m at hm
  change IsMixedProfile n at hn
  constructor
  · intro p a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hu (hm.1 p a)) (mul_nonneg hv (hn.1 p a))
  · intro p
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      (∑ a : Move, (u * m p a + v * n p a)) =
          u * (∑ a : Move, m p a) + v * (∑ a : Move, n p a) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ = 1 := by rw [hm.2 p, hn.2 p]; linarith

theorem mixedProfiles_nonempty [Nonempty Move] :
    (mixedProfiles (Player := Player) (Move := Move)).Nonempty := by
  exact ⟨uniformMixedProfile, uniformMixedProfile_isMixedProfile⟩

theorem nashMap_mem_mixedProfiles (G : MixedGame Player Move)
    {m : MixedProfile Player Move}
    (hm : m ∈ mixedProfiles (Player := Player) (Move := Move)) :
    nashMap G m ∈ mixedProfiles (Player := Player) (Move := Move) := by
  exact nashMap_isMixedProfile G hm

theorem exists_mixedNash_of_nashMap_fixedPoint (G : MixedGame Player Move)
    (hfixed : ∃ m, m ∈ mixedProfiles (Player := Player) (Move := Move) ∧
      nashMap G m = m) :
    ∃ m, m ∈ mixedProfiles (Player := Player) (Move := Move) ∧ IsMixedNash G m := by
  obtain ⟨m, hm, hfp⟩ := hfixed
  exact ⟨m, hm, mixedNash_of_nashMap_fixedPoint G hm hfp⟩

end NashEquilibrium
