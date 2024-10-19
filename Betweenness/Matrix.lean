import Betweenness.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

-- TODO: this should work in any suitably nice ring, for any suitably nice matrices
-- Generalize this appropriately!
instance {n m : ℕ} : Between (Matrix (Fin n) (Fin m) ℝ) where
  between a x b := ∃t ∈ Set.Icc (α := ℝ) 0 1, x = (1 - t) • a + t • b
  refl {a b} := ⟨1, by simp, by simp⟩
  symm  {a b c} | ⟨t, ht, habc⟩ => ⟨1 - t, by simp [ht.1, ht.2],
    by simp only [habc, sub_sub_cancel]; rw [add_comm]⟩
  extend {a b x y z}
  | ⟨tx, htx, haxb⟩, ⟨ty, hty, hayb⟩, ⟨tz, htz, hxzy⟩ => ⟨
      (1 - tz) * tx + tz * ty,
      by
        generalize hw : (1 - tz) * tx + tz * ty = w
        have wnn : 0 ≤ w :=
          hw ▸ add_nonneg (mul_nonneg (sub_nonneg_of_le htz.2) htx.1) (mul_nonneg htz.1 hty.1)
        have hw' : w = tx + tz * (ty - tx) := by
          rw [<-hw, sub_mul, one_mul, mul_sub, sub_eq_add_neg, sub_eq_neg_add, add_assoc]
        have wle : w ≤ 1 := calc
          w = _ := hw'
          _ ≤ tx + 1 * (1 - tx) := add_le_add (le_refl _)
            (mul_le_mul_of_nonneg htz.2
              (sub_le_sub hty.2 (le_refl _)) htz.1 (sub_nonneg_of_le htx.2))
          _ = 1 := by simp
          ;
        constructor
        · exact ⟨wnn, wle⟩
        · calc
          _ = ((1 - tz) * (1 - tx) + tz * (1 - ty)) • a + ((1 - tz) * tx + tz * ty) • b := by
            rw [
              add_smul, add_smul, add_comm (a := _ • b), add_assoc, add_comm, <-add_assoc,
              <-smul_smul, <-smul_smul, <-smul_add, <-hayb, <-smul_smul, <-smul_smul,
              add_assoc, <-smul_add, add_comm (a := _ • b), <-haxb, add_comm, hxzy
            ]
          _ = _ := by congr 2; calc
          (1 - tz) * (1 - tx) + tz * (1 - ty) = 1 - (tx - tz * tx + tz * ty) := by rw [
              mul_sub, sub_mul, one_mul, mul_one, sub_mul, one_mul, sub_sub, add_comm (a := tz),
              sub_add, mul_sub, mul_one, sub_eq_add_neg (a := tz), add_comm (a := tz),
              add_sub_add_right_eq_sub, sub_neg_eq_add
            ]
          _ = _ := by rw [
            hw', mul_sub, add_sub, sub_eq_neg_add (b := tz * tx), sub_eq_neg_add (b := tz * tx),
            add_assoc
          ]
    ⟩
  antisymm {a b c}
  | ⟨t, ht, h⟩, ⟨t', ht', h'⟩ => by
    if h0 : t = 0 then
      cases h0
      simp only [sub_zero, one_smul, zero_smul, add_zero] at h
      cases h; cases h'
      simp [<-add_smul]
    else
    have hc : c = (1 - t⁻¹) • a + t⁻¹ • b := by
      rw [
        congrArg (t⁻¹ • ·) h, smul_add, smul_smul, smul_smul, <-add_assoc, <-add_smul,
        mul_sub, mul_one, inv_mul_cancel₀ h0, one_smul, add_sub, sub_add_cancel, sub_self,
        zero_smul, zero_add
      ]
    have hab := hc.symm.trans h'
    if htt : t' = t⁻¹ then
      cases htt
      cases inv_le_one_iff₀.mp ht'.2 with
      | inl h0' => exact (h0 (le_antisymm h0' ht.1)).elim
      | inr h1 => cases (le_antisymm h1 ht.2); simp [hc]
    else
    have ha : (t' - t⁻¹) • a = (t' - t⁻¹) • b := by
      convert congrArg ((t' - 1) • a + · - t⁻¹ • b) hab using 1
      · rw [
          <-add_assoc, <-add_smul, add_sub, sub_add_cancel, <-add_sub, <-sub_smul, sub_self,
          zero_smul, add_zero
        ]
      · rw [
          <-add_assoc, <-add_smul, add_sub, sub_add_cancel, sub_self, zero_smul, zero_add,
          <-sub_smul
        ]
    have hb : a = b := by convert congrArg ((t' - t⁻¹)⁻¹ • ·) ha <;> simp [sub_ne_zero_of_ne htt]
    cases hb
    rw [h', <-add_smul, sub_add_cancel, one_smul]

-- TODO: show that a linear transformation is a betweenness homomorphism

-- TODO: show that an invertible linear transformation is a betweenness isomorphism

-- TODO: show that matrix multiplication "for the appropriate rank" is a "betweenness injection"
