import Gametheory.Brouwer_product
import NashEquilibrium.MixedTopology

/-!
# Mixed Nash existence

This module supplies the fixed-point step for the finite mixed-game layer.
The foundational fixed-point theorem is the simplex-product Brouwer theorem
from `Gametheory.Brouwer_product`; the bridge below reindexes arbitrary
finite player and move types to finite ordinals and applies the normalized
excess map from `NashEquilibrium.Mixed`.
-/

namespace NashEquilibrium

universe u v

open scoped BigOperators

variable {Player : Type u} {Move : Type v}
variable [Fintype Player] [Fintype Move] [DecidableEq Player] [DecidableEq Move]

theorem exists_nashMap_fixedPoint [Nonempty Move] (G : MixedGame Player Move) :
    ∃ m, m ∈ mixedProfiles (Player := Player) (Move := Move) ∧ nashMap G m = m := by
  classical
  cases isEmpty_or_nonempty Player with
  | inl h_empty =>
      let m : MixedProfile Player Move :=
        fun p => @isEmptyElim Player h_empty (fun _ => Move → ℝ) p
      refine ⟨m, ?_⟩
      refine ⟨?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro p
          exact @isEmptyElim Player h_empty (fun p => ∀ a, 0 ≤ m p a) p
        · intro p
          exact @isEmptyElim Player h_empty (fun p => ∑ a, m p a = 1) p
      · funext p
        exact @isEmptyElim Player h_empty
          (fun p => nashMap G m p = m p) p
  | inr h_nonempty =>
      let n : ℕ := Fintype.card Player
      have hn : 0 < n := Fintype.card_pos_iff.mpr h_nonempty
      letI : Inhabited (Fin n) := ⟨⟨0, hn⟩⟩
      let eP : Player ≃ Fin n := Fintype.equivFin Player
      let mcard : ℕ+ :=
        ⟨Fintype.card Move, Fintype.card_pos_iff.mpr inferInstance⟩
      let eM : Move ≃ Fin (Fintype.card Move) := Fintype.equivFin Move
      let card : Fin n → ℕ+ := fun _ => mcard
      let Product := Fin n → stdSimplex ℝ (Fin (Fintype.card Move))

      let fromProduct : Product → MixedProfile Player Move :=
        fun x p a => (x (eP p)).1 (eM a)

      have fromProduct_isMixedProfile (x : Product) :
          IsMixedProfile (fromProduct x) := by
        constructor
        · intro p a
          exact (x (eP p)).2.1 (eM a)
        · intro p
          change ∑ a : Move, (x (eP p)).1 (eM a) = 1
          calc
            ∑ a : Move, (x (eP p)).1 (eM a) =
                ∑ j : Fin (Fintype.card Move), (x (eP p)).1 j := by
                  simpa [eM] using
                    (Equiv.sum_comp (Fintype.equivFin Move)
                      (fun j : Fin (Fintype.card Move) => (x (eP p)).1 j))
            _ = 1 := by
              exact (x (eP p)).2.2

      let toProduct :
          ∀ (m : MixedProfile Player Move), IsMixedProfile m → Product :=
        fun m hm i =>
          ⟨fun j => m (eP.symm i) (eM.symm j), by
            constructor
            · intro j
              exact hm.1 (eP.symm i) (eM.symm j)
            · have hsum :
                  (∑ j : Fin (Fintype.card Move),
                    m (eP.symm i) (eM.symm j)) =
                    ∑ a : Move, m (eP.symm i) a := by
                exact Equiv.sum_comp eM.symm
                  (fun a : Move => m (eP.symm i) a)
              change (∑ j : Fin (Fintype.card Move),
                m (eP.symm i) (eM.symm j)) = 1
              rw [hsum, hm.2]⟩

      have toProduct_fromProduct (x : Product) :
          toProduct (fromProduct x) (fromProduct_isMixedProfile x) = x := by
        funext i
        ext j
        simp [toProduct, fromProduct, eM]

      have hfrom_cont : Continuous fromProduct := by
        apply continuous_pi
        intro p
        apply continuous_pi
        intro a
        change Continuous (fun x : Product => (x (eP p)).1 (eM a))
        exact (continuous_apply (eM a)).comp
          (continuous_subtype_val.comp (continuous_apply (eP p)))

      let F : Product → Product := fun x =>
        toProduct (nashMap G (fromProduct x))
          (nashMap_isMixedProfile G (fromProduct_isMixedProfile x))

      have hF_cont : Continuous F := by
        apply continuous_pi
        intro i
        apply Continuous.subtype_mk
        · apply continuous_pi
          intro j
          have hnm : Continuous (nashMap G ∘ fromProduct) :=
            (continuous_nashMap G).comp hfrom_cont
          change Continuous (fun x : Product =>
            nashMap G (fromProduct x) (eP.symm i) (eM.symm j))
          exact (continuous_apply (eM.symm j)).comp
            ((continuous_apply (eP.symm i)).comp hnm)

      obtain ⟨x, hx⟩ := Brouwer_Product card F hF_cont
      let m : MixedProfile Player Move := fromProduct x
      have hm : IsMixedProfile m := fromProduct_isMixedProfile x
      have hfp : nashMap G m = m := by
        funext p a
        have hcoord :=
          congrArg (fun z : stdSimplex ℝ (Fin (mcard : ℕ)) => z.1 (eM a))
            (congrFun hx (eP p))
        simpa [F, m, toProduct, fromProduct, card, mcard, eP, eM] using hcoord
      exact ⟨m, hm, hfp⟩

theorem exists_mixedNash [Nonempty Move] (G : MixedGame Player Move) :
    ∃ m : MixedProfile Player Move, IsMixedNash G m := by
  obtain ⟨m, hm, hfp⟩ := exists_nashMap_fixedPoint G
  exact ⟨m, mixedNash_of_nashMap_fixedPoint G hm hfp⟩

end NashEquilibrium
