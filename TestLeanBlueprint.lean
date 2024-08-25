-- This module serves as the root of the `TestLeanMatlib` library.
-- Import modules here that should be built as part of the library.
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

axiom f : ℚ → ℚ
axiom f_property : ∀ x y : ℚ, f (f x + y) = f y + x ∨ f (f y + x) = f x + y

def fixed (x : ℚ) : Prop := f x = x

theorem x_fx_fixed (x : ℚ): fixed (f x + x) := by
  have h := f_property x x
  simp at h
  exact h

theorem plus_fixed (x y : ℚ): fixed x ∧ fixed y → fixed (x + y) := by
  unfold fixed
  intro h1
  cases h1 with
  | intro hx hy =>
    have h2 := f_property x y
    rw[hx, hy, add_comm y x] at h2
    simp at h2
    exact h2

theorem zero_fixed : fixed 0 := by
  have h := f_property 0 (- f 0)
  rw[add_neg_cancel (f 0), add_zero] at h
  cases h with
  | inl h1 =>
    have h11 := x_fx_fixed (-f 0)
    rw [← h1, add_neg_cancel (f 0)] at h11
    exact h11
  | inr h2 =>
    have h12 := x_fx_fixed (f (-f 0))
    unfold fixed at h12
    rw[h2, zero_add, h2] at h12
    rw[← h12] at h2
    exact h2

theorem f_eq_zero (x : ℚ) : f x = 0 → x = 0 := by
  intro h
  have h2 := x_fx_fixed x
  rw[h] at h2
  simp at h2
  rw[h2] at h
  exact h

theorem f_neg_fx (x : ℚ) : f (-f x) = -x := by
  have h := f_property (-f x) x
  cases h with
  | inl h1 =>
    simp at h1
    apply f_eq_zero at h1
    linarith
  | inr h2 =>
    simp at h2
    rw[zero_fixed] at h2
    linarith

theorem f_only (x : ℚ) : ∃! y : ℚ, f y = x := by
  use -f (-x)
  constructor
  case h.left =>
    have h1 := f_neg_fx (-x)
    simp at h1
    exact h1
  case h.right =>
    intro y1 h2
    contrapose! h2
    by_contra h3
    have h4 := f_neg_fx y1
    rw[h3] at h4
    rw[h4] at h2
    simp at h2

theorem f_eq (x y : ℚ) : f x = f y → x = y := by
  intro h
  contrapose! h
  by_contra feq
  have fyeq : f y = f y := rfl
  have h1 := f_only (f y)
  rcases h1 with ⟨z, hz, uniq_z⟩
  have hx: x = z := uniq_z x feq
  have hy: y = z := uniq_z y fyeq
  rw [hx, hy] at h
  tauto

-- hint by https://www.zhihu.com/question/661946849/answer/3569022065
theorem plus_fpos_fneg_fixed (x : ℚ) : fixed (f x + f (-x)) := by
  have h1 := x_fx_fixed x
  have h2 := x_fx_fixed (-x)
  have h3 : fixed ((f x + x) + (f (-x) + -x)) := by
    apply plus_fixed (f x + x) (f (-x) + -x)
    exact ⟨h1, h2⟩
  have simplification : (f x + x) + (f (-x) + -x) = f x + f (-x) := by
    linarith
  rw[simplification] at h3
  exact h3

theorem plus_fpos_fneg_eq_ffx_x (x : ℚ) : f x + f (-x) = f (f x) - x := by
  have h1 := f_property (f x) (-x)
  have h2 := plus_fpos_fneg_fixed (-x)
  unfold fixed at h2
  simp at h2
  cases h1 with
  | inl h1l =>
    rw[← h2] at h1l
    apply f_eq at h1l
    linarith
  | inr h1r =>
    rw [h2] at h1r
    linarith

-- hint by https://www.zhihu.com/question/661946849/answer/3581319017
lemma uneq_plus_fpos_fneg_lemma (x y : ℚ): f x + f (-x) ≠ 0 ∧ f y + f (-y) ≠ 0 ∧ f (f x + y) = f y + x→ f x + f (-x) = f y + f (-y) := by
  intro h
  cases h with
  | intro hx hy_xy =>
    cases hy_xy with
    | intro hy hxy =>
      have h1 := f_property (-x) (f x + y)
      cases h1 with
      | inl h1l =>
        rw[hxy] at h1l
        simp at h1l
        apply f_eq at h1l
        have h1l_simp : f x + f (-x) = 0 := by linarith
        tauto
      | inr h2l =>
        rw [hxy] at h2l
        simp at h2l
        have h2l1 : f (f y) - y = f x + f (-x) := by linarith
        rw[← plus_fpos_fneg_eq_ffx_x y] at h2l1
        linarith
theorem uneq_plus_fpos_fneg (x y : ℚ) : f x + f (-x) ≠ 0 ∧ f y + f (-y) ≠ 0 → f x + f (-x) = f y + f (-y) := by
  intro h
  cases h with
  | intro hx hy =>
    have h1 := f_property x y
    cases h1 with
    | inl h1l =>
      have h1l1 := uneq_plus_fpos_fneg_lemma x y
      tauto
    | inr h1r =>
      have h1r1 := uneq_plus_fpos_fneg_lemma y x
      tauto

#check uneq_plus_fpos_fneg
#print axioms uneq_plus_fpos_fneg
