import NashEquilibrium.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Finite mixed strategies

This module records the finite mixed-strategy layer natively in Lean.  A
mixed profile assigns a nonnegative real weight to every player/move pair,
with weights summing to one for each player.  The expected payoff of a pure
deviation is defined by finite enumeration of the opponents' pure profiles.
The module also proves the support-payoff lemma and connects pure profiles to
mixed profiles through Dirac embeddings.  General fixed-point infrastructure
is kept separate from the elementary finite definitions below.
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

/-! The excess map is the finite-dimensional fixed-point construction used in
the standard proof of mixed Nash existence.  The preservation theorem below is
elementary; a separate foundational fixed-point theorem is intentionally not
assumed by this library. -/

/-- The positive payoff gap of a pure deviation. -/
def excess (G : MixedGame Player Move) (m : MixedProfile Player Move)
    (p : Player) (a : Move) : ℝ :=
  max 0 (pureDeviationPayoff G m p a - mixedPayoff G m p)

/-- The total excess of one player's pure deviations. -/
def excessSum (G : MixedGame Player Move) (m : MixedProfile Player Move)
    (p : Player) : ℝ :=
  ∑ a : Move, excess G m p a

/-- The normalized excess map on mixed profiles. -/
noncomputable def nashMap (G : MixedGame Player Move) (m : MixedProfile Player Move) :
    MixedProfile Player Move :=
  fun p a =>
    (m p a + excess G m p a) / (1 + excessSum G m p)

@[simp] theorem excess_nonneg (G : MixedGame Player Move)
    (m : MixedProfile Player Move) (p : Player) (a : Move) :
    0 ≤ excess G m p a := by
  simp [excess]

@[simp] theorem excessSum_nonneg (G : MixedGame Player Move)
    (m : MixedProfile Player Move) (p : Player) :
    0 ≤ excessSum G m p := by
  exact Finset.sum_nonneg fun a _ => excess_nonneg G m p a

theorem excessSum_denom_pos (G : MixedGame Player Move)
    (m : MixedProfile Player Move) (p : Player) :
    0 < 1 + excessSum G m p := by
  linarith [excessSum_nonneg G m p]

@[simp] theorem nashMap_apply (G : MixedGame Player Move)
    (m : MixedProfile Player Move) (p : Player) (a : Move) :
    nashMap G m p a =
      (m p a + excess G m p a) / (1 + excessSum G m p) :=
  rfl

theorem nashMap_isMixedProfile (G : MixedGame Player Move)
    {m : MixedProfile Player Move} (hm : IsMixedProfile m) :
    IsMixedProfile (nashMap G m) := by
  have hprob_le_one (p : Player) (a : Move) : m p a ≤ 1 := by
    calc
      m p a ≤ ∑ b : Move, m p b := by
        exact Finset.single_le_sum (fun b _ => hm.1 p b) (Finset.mem_univ a)
      _ = 1 := hm.2 p
  have hnonneg (p : Player) (a : Move) : 0 ≤ nashMap G m p a := by
    rw [nashMap_apply]
    exact div_nonneg (add_nonneg (hm.1 p a) (excess_nonneg G m p a))
      (le_of_lt (excessSum_denom_pos G m p))
  have hle_one (p : Player) (a : Move) : nashMap G m p a ≤ 1 := by
    rw [nashMap_apply]
    have hex_le : excess G m p a ≤ excessSum G m p := by
      exact Finset.single_le_sum (fun b _ => excess_nonneg G m p b) (Finset.mem_univ a)
    apply (div_le_iff₀ (excessSum_denom_pos G m p)).2
    linarith [hprob_le_one p a]
  constructor
  · exact hnonneg
  · intro p
    simp_rw [nashMap_apply]
    calc
      (∑ a : Move, (m p a + excess G m p a) / (1 + excessSum G m p)) =
          (∑ a : Move, (m p a + excess G m p a)) /
            (1 + excessSum G m p) := by
              rw [Finset.sum_div]
      _ = (∑ a : Move, m p a + ∑ a : Move, excess G m p a) /
            (1 + excessSum G m p) := by rw [Finset.sum_add_distrib]
      _ = 1 := by
        rw [hm.2 p]
        have hden : 1 + excessSum G m p ≠ 0 :=
          ne_of_gt (excessSum_denom_pos G m p)
        rw [show (∑ a : Move, excess G m p a) = excessSum G m p by rfl]
        exact div_self hden

/-- A fixed point of the normalized excess map has no positive excess. -/
theorem fixedPoint_excess_zero (G : MixedGame Player Move)
    {m : MixedProfile Player Move} (hm : IsMixedProfile m)
    (hfp : nashMap G m = m) (p : Player) (a : Move) :
    excess G m p a = 0 := by
  let total : ℝ := excessSum G m p
  have total_nonneg : 0 ≤ total := by
    exact excessSum_nonneg G m p
  have denom_pos : 0 < 1 + total := by
    exact excessSum_denom_pos G m p
  have denom_ne : 1 + total ≠ 0 := ne_of_gt denom_pos
  have excess_eq (b : Move) :
      excess G m p b = m p b * total := by
    have hcoord := congrFun (congrFun hfp p) b
    have heq : m p b =
        (m p b + excess G m p b) / (1 + excessSum G m p) := by
      simpa [nashMap_apply] using hcoord.symm
    have hmult : m p b * (1 + total) = m p b + excess G m p b := by
      apply (eq_div_iff denom_ne).mp
      simpa [total] using heq
    linarith
  by_cases htotal : total = 0
  · rw [excess_eq, htotal]
    simp
  · have total_pos : 0 < total := lt_of_le_of_ne total_nonneg (Ne.symm htotal)
    have positive_move_payoff {b : Move} (hb : 0 < m p b) :
        pureDeviationPayoff G m p b =
          mixedPayoff G m p + m p b * total := by
      have hex_pos : 0 < excess G m p b := by
        rw [excess_eq]
        exact mul_pos hb total_pos
      have hdiff_pos :
          0 < pureDeviationPayoff G m p b - mixedPayoff G m p := by
        by_contra hnot
        have hdiff_nonpos :
            pureDeviationPayoff G m p b - mixedPayoff G m p ≤ 0 := le_of_not_gt hnot
        have hex_zero : excess G m p b = 0 := by
          simp [excess, max_eq_left hdiff_nonpos]
        linarith
      have hdiff_eq :
          pureDeviationPayoff G m p b - mixedPayoff G m p = excess G m p b := by
        simp [excess, max_eq_right (le_of_lt hdiff_pos)]
      linarith [hdiff_eq, excess_eq b]
    have weighted_payoff_eq (b : Move) :
        m p b * pureDeviationPayoff G m p b =
          m p b * mixedPayoff G m p + total * (m p b) ^ 2 := by
      by_cases hbzero : m p b = 0
      · simp [hbzero]
      · have hbpos : 0 < m p b :=
          lt_of_le_of_ne (hm.1 p b) (Ne.symm hbzero)
        rw [positive_move_payoff hbpos]
        ring
    have weighted_average_eq :
        mixedPayoff G m p =
          mixedPayoff G m p * (∑ b : Move, m p b) +
            total * (∑ b : Move, (m p b) ^ 2) := by
      calc
        mixedPayoff G m p =
            ∑ b : Move, m p b * pureDeviationPayoff G m p b := by
              rfl
        _ = ∑ b : Move,
            (m p b * mixedPayoff G m p + total * (m p b) ^ 2) := by
              apply Finset.sum_congr rfl
              intro b hb
              exact weighted_payoff_eq b
        _ = (∑ b : Move, m p b * mixedPayoff G m p) +
              (∑ b : Move, total * (m p b) ^ 2) := by
              rw [Finset.sum_add_distrib]
        _ = mixedPayoff G m p * (∑ b : Move, m p b) +
              total * (∑ b : Move, (m p b) ^ 2) := by
              simp [Finset.sum_mul, Finset.mul_sum, mul_comm]
    have total_squares_zero :
        total * (∑ b : Move, (m p b) ^ 2) = 0 := by
      have haverage := weighted_average_eq
      rw [hm.2 p] at haverage
      linarith
    have squares_zero : (∑ b : Move, (m p b) ^ 2) = 0 := by
      exact (mul_eq_zero.mp total_squares_zero).resolve_left (ne_of_gt total_pos)
    have positive_probability_exists : ∃ b : Move, 0 < m p b := by
      by_contra hnone
      have hzero (b : Move) : m p b = 0 := by
        apply le_antisymm
        · exact le_of_not_gt (fun hb => hnone ⟨b, hb⟩)
        · exact hm.1 p b
      have hsum_zero : (∑ b : Move, m p b) = 0 := by
        simp [hzero]
      linarith [hm.2 p]
    obtain ⟨b, hb⟩ := positive_probability_exists
    have hsq_pos : 0 < (m p b) ^ 2 := by positivity
    have hsq_le : (m p b) ^ 2 ≤ ∑ c : Move, (m p c) ^ 2 := by
      exact Finset.single_le_sum (fun c _ => sq_nonneg (m p c)) (Finset.mem_univ b)
    have hsum_sq_pos : 0 < ∑ c : Move, (m p c) ^ 2 :=
      lt_of_lt_of_le hsq_pos hsq_le
    have : False := by
      have hprod_pos : 0 < total * (∑ c : Move, (m p c) ^ 2) :=
        mul_pos total_pos hsum_sq_pos
      linarith [total_squares_zero, hprod_pos]
    exact False.elim this

/-- A fixed point of the excess map is a mixed Nash equilibrium. -/
theorem mixedNash_of_nashMap_fixedPoint (G : MixedGame Player Move)
    {m : MixedProfile Player Move} (hm : IsMixedProfile m)
    (hfp : nashMap G m = m) :
    IsMixedNash G m := by
  refine ⟨hm, ?_⟩
  intro p a
  have hex : excess G m p a = 0 := fixedPoint_excess_zero G hm hfp p a
  have hdiff :
      pureDeviationPayoff G m p a - mixedPayoff G m p ≤ 0 := by
    have hle := le_max_right (0 : ℝ)
      (pureDeviationPayoff G m p a - mixedPayoff G m p)
    rw [← excess] at hle
    rw [hex] at hle
    exact hle
  linarith


/-- The probability constraints carried by a mixed Nash equilibrium. -/
theorem mixedNash_profile {G : MixedGame Player Move} {m : MixedProfile Player Move}
    (h : IsMixedNash G m) : IsMixedProfile m :=
  h.1

/-- Every pure deviation is no better than the mixed payoff at equilibrium. -/
theorem mixedNash_deviation_le {G : MixedGame Player Move} {m : MixedProfile Player Move}
    (h : IsMixedNash G m) (p : Player) (a : Move) :
    pureDeviationPayoff G m p a ≤ mixedPayoff G m p :=
  h.2 p a

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

/-- A move in the support of an equilibrium receives the equilibrium payoff. -/
theorem mixedNash_support_payoff_eq
    {G : MixedGame Player Move} {m : MixedProfile Player Move}
    (h : IsMixedNash G m) {p : Player} {a : Move} (ha : 0 < m p a) :
    pureDeviationPayoff G m p a = mixedPayoff G m p := by
  have hm : IsMixedProfile m := mixedNash_profile h
  have hgap_nonneg (b : Move) :
      0 ≤ m p b * (mixedPayoff G m p - pureDeviationPayoff G m p b) := by
    exact mul_nonneg (hm.1 p b) (sub_nonneg.mpr (mixedNash_deviation_le h p b))
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

/-- A strictly suboptimal pure move has zero probability at equilibrium. -/
theorem mixedNash_zero_probability_if_less
    {G : MixedGame Player Move} {m : MixedProfile Player Move}
    (h : IsMixedNash G m)
    {p : Player} {a : Move}
    (hless : pureDeviationPayoff G m p a < mixedPayoff G m p) :
    m p a = 0 := by
  by_contra hzero
  have hnonneg : 0 ≤ m p a := (mixedNash_profile h).1 p a
  have hpos : 0 < m p a := lt_of_le_of_ne hnonneg (Ne.symm hzero)
  have heq := mixedNash_support_payoff_eq h hpos
  linarith

/-- The Dirac mixed profile concentrated at a pure profile. -/
def diracMixedProfile (s : Profile Player Move) : MixedProfile Player Move :=
  fun p a => if a = s p then 1 else 0

@[simp] theorem diracMixedProfile_apply (s : Profile Player Move) (p : Player) (a : Move) :
    diracMixedProfile s p a = (if a = s p then 1 else 0) :=
  rfl

@[simp] theorem diracMixedProfile_isMixedProfile (s : Profile Player Move) :
    IsMixedProfile (diracMixedProfile s) := by
  classical
  constructor
  · intro p a
    by_cases h : a = s p <;> simp [diracMixedProfile, h]
  · intro p
    simp [diracMixedProfile]

theorem opponentWeight_diracMixedProfile
    (s t : Profile Player Move) (p : Player) :
    opponentWeight (diracMixedProfile s) p t =
      if ∀ q, q ≠ p → t q = s q then 1 else 0 := by
  classical
  by_cases h : ∀ q, q ≠ p → t q = s q
  · simp only [opponentWeight, diracMixedProfile, if_pos h]
    apply Finset.prod_eq_one
    intro q hq
    have hqp : q ≠ p := by
      simpa using (Finset.mem_erase.mp hq).1
    simp [h q hqp]
  · have hex : ∃ q, q ≠ p ∧ t q ≠ s q := by
      by_contra hno
      apply h
      intro q hqp
      by_contra hneq
      apply hno
      exact ⟨q, hqp, hneq⟩
    rcases hex with ⟨q, hqp, hneq⟩
    have hqmem : q ∈ Finset.univ.erase p := by simp [hqp]
    simp only [opponentWeight, diracMixedProfile, if_neg h]
    apply Finset.prod_eq_zero hqmem
    simp [hneq]

/-- At a Dirac profile, a pure deviation has its pointwise pure payoff. -/
theorem pureDeviationPayoff_diracMixedProfile
    (G : MixedGame Player Move) (s : Profile Player Move) (p : Player) (a : Move) :
    pureDeviationPayoff G (diracMixedProfile s) p a =
      G.payoff p (deviation s p a) := by
  classical
  unfold pureDeviationPayoff
  rw [Fintype.sum_eq_single (deviation s p a)]
  · have hdevp : deviation s p a p = a := by
      simp [deviation]
    have hdevopp : ∀ q, q ≠ p → deviation s p a q = s q := by
      intro q hqp
      simp [deviation, hqp]
    rw [if_pos hdevp]
    rw [opponentWeight_diracMixedProfile, if_pos hdevopp]
    simp
  · intro t hne
    by_cases hpa : t p = a
    · have hnotall : ¬ ∀ q, q ≠ p → t q = s q := by
        intro hall
        apply hne
        funext q
        by_cases hqp : q = p
        · subst q
          simp [deviation, hpa]
        · simp [deviation, hqp, hall q hqp]
      simp [hpa, opponentWeight_diracMixedProfile, hnotall]
    · simp [hpa]

/-- A Dirac profile has the corresponding pure payoff as its mixed payoff. -/
theorem mixedPayoff_diracMixedProfile
    (G : MixedGame Player Move) (s : Profile Player Move) (p : Player) :
    mixedPayoff G (diracMixedProfile s) p = G.payoff p s := by
  classical
  unfold mixedPayoff
  rw [Fintype.sum_eq_single (s p)]
  · simp [pureDeviationPayoff_diracMixedProfile, deviation]
  · intro a hne
    simp [diracMixedProfile, hne]

/-- A pure Nash profile embeds as a mixed Nash profile. -/
theorem diracMixedNash_of_pure_deviations
    (G : MixedGame Player Move) (s : Profile Player Move)
    (h : ∀ p a, G.payoff p (deviation s p a) ≤ G.payoff p s) :
    IsMixedNash G (diracMixedProfile s) := by
  refine ⟨diracMixedProfile_isMixedProfile s, ?_⟩
  intro p a
  rw [pureDeviationPayoff_diracMixedProfile, mixedPayoff_diracMixedProfile]
  exact h p a

end NashEquilibrium
