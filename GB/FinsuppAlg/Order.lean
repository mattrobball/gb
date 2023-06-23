/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/

import GB.FinsuppAlg.Basic
import Init.Data.Format.Basic

variable {k : Type} {M : Type}
variable [DecidableEq k] [CommRing k] [LinearOrderedAddCommMonoid M]

open Finsupp Finset FinsuppAlg

namespace FinsuppAlg

theorem apply_ne_zero_of_apply_sum_ne_zero {f g : alg k M} (h : (f + g) m ≠ 0) :
    (f m ≠ 0) ∨ (g m ≠ 0) := by
  by_contra h'
  push_neg at h'
  simp only [zero_add, FinsuppAlg.add_apply, ne_eq, h'.1, h'.2] at h

/-- The leading monomial of `f` normalized to `lm 0 = ⊥`. -/
def lm (f : alg k M) : WithBot M := f.support.max

/-- The leading monomial of `f ≠ 0` as a term of `M` -/
def lm' (f : alg k M) (h : f ≠ 0) : M := f.support.max' <| support_nonempty_iff.mpr h

theorem lm'_eq_support_max (f : alg k M) (h : f ≠ 0)
    (h' : Finset.Nonempty f.support := support_nonempty_iff.mpr h) : lm' f h = f.support.max' h' := rfl

@[simp]
theorem lm_zero_eq_bot : lm (0 : M →₀ k) = ⊥ := rfl

theorem lm_single' {m : M} {a : k} : lm (single' m a) = if a = 0 then (⊥ : WithBot _) else m := by
  dsimp [lm,single']
  by_cases a = 0
  · simp only [if_pos h]; rfl
  · simp only [if_neg h, max_singleton]

theorem ne_zero_of_lm_ne_top {f : alg k M} (h : lm f ≠ ⊥) : f ≠ 0 := fun h' => by simp [h'] at h

theorem lm_eq_top_iff_zero {f : alg k M} : lm f = ⊥ ↔ f = 0 := by
  refine ⟨ fun h => by_contra fun h' => ?_, fun h => lm_zero_eq_bot (k := k) (M := M) ▸ congrArg _ h ⟩
  exact h' <| support_eq_empty.mp <| Finset.max_eq_bot.mp h

theorem lm_eq_some_lm'_of_ne_zero {f : alg k M} (h : f ≠ 0) : lm f = lm' f h := by
  dsimp [lm,lm']
  simp [coe_max']

theorem le_lm_of_apply_ne_zero {f : alg k M} {m : M} (h : f m ≠ 0) : m ≤ lm f :=
  le_max <| mem_support_toFun _ _|>.mpr h

theorem ne_lm_of_apply_eq_zero {f : alg k M} {m : M} (h : f m = 0) : ↑m ≠ lm f := fun h' =>
  mem_support_toFun _ _|>.mp (mem_of_max h'.symm) h

theorem apply_eq_zero_of_gt_lm {f : alg k M} {m : M} (h : lm f < m) : f m = 0 := by
  by_contra h'
  have : m ≤ lm f := le_max <| mem_support_toFun _ _|>.mpr h'
  exact not_le_of_gt h this

theorem _root_.WithBot.some_of_gt {α : Type _} [LinearOrder α] {x y : WithBot α} (h : x < y) :
    ∃ (a : α), a = y := WithBot.ne_bot_iff_exists.mp fun h' => WithBot.not_lt_none _ <| h' ▸ h

theorem lm_sum_le_lm_max (f g : alg k M) : lm (f + g) ≤ max (lm f) (lm g) :=
  le_or_gt _ _|>.elim id fun h => by
    have ⟨m, hm⟩ := WithBot.some_of_gt h
    rw [←hm] at h
    have left : f m = 0 := apply_eq_zero_of_gt_lm <| lt_of_le_of_lt (le_max_left _ _) h
    have right : g m = 0 := apply_eq_zero_of_gt_lm <| lt_of_le_of_lt (le_max_right _ _) h
    have : (f + g) m = 0 := by simp [left,right]
    exact ne_lm_of_apply_eq_zero this hm|>.elim

theorem lm_sum_of_le_lm {f g : alg k M} (h : lm f < lm g) : lm (f + g) = lm g := le_antisymm
  (max_eq_right (le_of_lt h) ▸ lm_sum_le_lm_max _ _) (by
    have ⟨m, hm⟩ := WithBot.some_of_gt h
    have : f m = 0 := apply_eq_zero_of_gt_lm <| hm ▸ h
    have : (f + g) m ≠ 0 := by
      simp only [FinsuppAlg.add_apply, this, zero_add, ne_eq]
      intro h
      exact ne_lm_of_apply_eq_zero h hm
    rw [← hm]
    apply le_max <| mem_support_toFun _ _|>.mpr this)

theorem lm_sum_of_le_lm' {f g : alg k M} (h : lm g < lm f) : lm (f + g) = lm f :=
  add_comm f g ▸ lm_sum_of_le_lm h

/-- The coefficient of the leading monomial. -/
def lc (f : alg k M) : k := lm f|>.recBotCoe 0 f

@[simp]
theorem lc_zero : lc (0 : alg k M) = 0 := rfl

theorem lc_eq_support_max_of_ne_zero {f : alg k M} (h' : f ≠ 0) : lc f = f (lm' f h') := by
  by_cases lm f = ⊥
  · apply (h' <| lm_eq_top_iff_zero.mp h).elim
  · dsimp [lc]
    rw [lm_eq_some_lm'_of_ne_zero h', WithBot.recBotCoe_coe]

theorem eq_zero_of_lc_zero {f : alg k M} (h : lc f = 0) : f = 0 := by
  by_contra h'
  rw [lc_eq_support_max_of_ne_zero h'] at h
  have : lm' f h' ∉ f.support := by simp [h]
  apply this <| max'_mem f.support _

theorem lc_eq_zero (f : alg k M) : lc f = 0 ↔ f = 0 :=
  ⟨eq_zero_of_lc_zero, fun h => lc_zero (k := k) (M := M) ▸ congrArg lc h⟩

/-- The leading term of `f` -/
def lt (f : alg k M) : alg k M := lm f|>.recBotCoe 0 (fun m => single' m <| lc f)

@[simp]
theorem lt_zero : lt (0 : alg k M) = 0 := rfl

theorem lt_eq_single'_of_ne_zero {f : alg k M} (h' : f ≠ 0) : lt f = (single' (lm' f h') <| lc f) := by
  by_cases lm f = ⊥
  · apply (h' <| lm_eq_top_iff_zero.mp h).elim
  · dsimp [lt]
    rw [lm_eq_some_lm'_of_ne_zero h', WithBot.recBotCoe_coe]

theorem lt_eq_zero_iff_lc_eq_zero (f : alg k M) : lt f = 0 ↔ lc f = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [lc_eq_zero _|>.mp h]⟩
  · by_cases h' : f = 0
    · apply lc_eq_zero _|>.mpr h'
    · dsimp [lt] at h
      rw [lm_eq_some_lm'_of_ne_zero h', WithBot.recBotCoe_coe] at h
      rw [← single'_apply (lm' f h') (lc f)]
      simp [h]

theorem lt_eq_zero_iff (f : alg k M) : lt f = 0 ↔ f = 0 :=
  lt_eq_zero_iff_lc_eq_zero _|>.trans <| lc_eq_zero _

/-- The tail of `f` is `f` with its leading term subtracted off -/
abbrev tail (f : alg k M) : alg k M := f - lt f

theorem self_eq_lt_add_tail (f : alg k M) : f = lt f + tail f := by
  ext; simp

theorem self_eq_tail_add_lt (f : alg k M) : f = tail f + lt f := by
  ext; simp

@[simp]
theorem tail_zero : tail (0 : alg k M) = 0 := by
  ext; simp

theorem tail_eq_self_iff (f : alg k M) : tail f = f ↔ f = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ tail_zero⟩
  nth_rw 2 [self_eq_tail_add_lt f] at h
  rw [← lc_eq_zero, ← lt_eq_zero_iff_lc_eq_zero]
  ext m
  have h' : (tail f) m = (tail f + lt f) m := by congr
  simpa using h'

theorem tail_apply_lm_eq_zero {f : alg k M} (h : f ≠ 0) : (tail f) (lm' f h) = 0 := by
  dsimp [tail]
  rw [FinsuppAlg.sub_coe_apply, ← lc_eq_support_max_of_ne_zero,
    lt_eq_single'_of_ne_zero, single'_apply, sub_self]

theorem tail_apply_eq {f : alg k M} (m : M) (h : f ≠ 0) (h' : m ≠ lm' f h) : f m = (tail f) m := by
  have : (lt f) m = 0 := by
    rw [lt_eq_single'_of_ne_zero h, single'_apply_neq]
    exact h'
  simp [this]

theorem tail_support_subset {f : alg k M} (hf : f ≠ 0) : (tail f).support < f.support := by
  refine ⟨fun m h' => ?_, fun h' => ?_⟩
  · rw [mem_support_toFun] at *
    change f m ≠ 0; change (tail f) m ≠ 0 at h'
    by_cases m ≠ lm' f hf
    · rwa [tail_apply_eq _ hf h]
    · push_neg at h; rw [h] at h'
      exact (h' <| tail_apply_lm_eq_zero hf).elim
  · have : ∀ m, f m ≠ 0 → (tail f) m ≠ 0 := fun m h =>
      (mem_support_toFun (tail f) m).mp <| h' <| (mem_support_toFun f m).mpr h
    have that : f (lm' f hf) ≠ 0 := by
      rw [← lc_eq_support_max_of_ne_zero]
      intro h
      exact hf <| (lc_eq_zero f).mp h
    obtain h'' := this (lm' f hf) that
    exact h'' <| tail_apply_lm_eq_zero hf

theorem eq_zero_of_tail_supp_eq_supp {f : alg k M} (h : (tail f).support = f.support) : f = 0 := by
  by_contra h'
  exact tail_support_subset h'|>.2 (h.symm ▸ Finset.Subset.refl _)

@[default_instance]
instance : SizeOf (alg k M) where
  sizeOf := fun f => f.support.card

theorem single'_mul_apply {f : alg k M} {m m' : M} {a : k} : (single' m a * f) m' = a * f (m + m') := sorry

theorem mul_single'_apply {f : alg k M} {m m' : M} {a : k} : (f * single' m a) m' = a * f (m + m') := sorry

-- theorem single'_mul_support_eq_card_of_ne_zero {f : alg k M} {m : M} {a : k} :g

theorem lm_eq_lm_lt {f : alg k M} : lm f = lm (lt f) := sorry

theorem lm_single'_mul_single'_eq_ite (m m' : M) (a a' : k) :
    lm (single' m a * single' m' a') = if a*a' = 0 then (⊥ : WithBot M) else m + m' := by
  rw [single'_mul_single', lm_single']; rfl

theorem lm_single'_mul_single'_eq_sum_lm_of_mul_ne_zero_aux {m m' : M} {a a' : k}
    (h : a ≠ 0 → a' ≠ 0 → a*a' ≠ 0) :
    lm (single' m a * single' m' a') = lm (single' m a) + lm (single' m' a') := by
  simp only [lm_single'_mul_single'_eq_ite, lm_single']
  by_cases ha : a = 0
  · simp [ha]
  · by_cases ha' : a' = 0
    · simp [ha']
    · simp [h ha ha', ha, ha']

variable [NoZeroDivisors k]

theorem lm_single'_mul_single'_eq_sum_lm_of_mul_ne_zero {m m' : M} {a a' : k} :
    lm (single' m a * single' m' a') = lm (single' m a) + lm (single' m' a') :=
  lm_single'_mul_single'_eq_sum_lm_of_mul_ne_zero_aux
    (fun h h' h'' => NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h''|>.elim h h')

theorem foo {f g : alg k M} {m : M} {a : k} (h : lm f < lm g) (h' : a ≠ 0) :
    lm (f * single' m a) < lm (g * single' m a) := sorry

theorem sum_lm_mul_single' {f : alg k M} {m : M} {a : k} :
    lm (f * single' m a) = lm f + (m : WithBot M) := by
  sorry

theorem sum_lm_mul [NoZeroDivisors k] (f g : alg k M) : lm (f * g) = lm f + lm g := sorry


instance lmLT : LT (alg k M) where
  lt f g := lm f < lm g

theorem tail_lt_self_of_ne_zero {f : alg k M} (h : f ≠ 0) : tail f < f := by
  change lm (tail f) < lm f
  rw [lm_eq_some_lm'_of_ne_zero h]
  apply (Classical.em (tail f = 0)).elim
  · intro h'
    rw [h',lm_zero_eq_bot]
    apply WithBot.none_lt_some
  · intro h'
    rw [lm_eq_some_lm'_of_ne_zero h']
    apply WithBot.some_lt_some.mpr
    rw [lm'_eq_support_max _ h', Finset.max'_lt_iff]
    intro m h''
    have h''' : m ≤ lm' f h := le_max' _ _ <| tail_support_subset h|>.1 h''
    apply Ne.lt_of_le ?_ h'''
    intro h''''
    rw [h''''] at h''
    exact (mem_support_toFun _ _).mp h'' (tail_apply_lm_eq_zero _)

variable (k M)

theorem wf_lm [I : IsWellOrder M (·<·)] : WellFounded (@LT.lt (alg k M) _) :=
  InvImage.wf (r := fun m m' : WithBot M => m < m') (fun (f : alg k M) => lm f)
    <| WithBot.wellFounded_lt I.wf

variable {k M}

variable [IsWellOrder M (· < ·)]

def toOrdList (f : alg k M) : List <| k × M :=
  have : IsWellOrder M (· < ·) := inferInstance
  if h : f = 0 then [] else
    have : tail f < f := tail_lt_self_of_ne_zero h
    ⟨lc f, lm' f h⟩ :: toOrdList (tail f)
termination_by' ⟨_, wf_lm k M⟩

namespace FinsuppAlg.Repr

open Std Format

instance (priority := 1000) [ToFormat k] [ToFormat M] : ToFormat <| k × M where
  format := fun p => (format p.1) ++ "u^" ++ (format p.2)

instance repr [ToFormat k] [ToFormat M] : Repr (alg k M) where
  reprPrec := fun f _ =>
    match toOrdList f with
    | [] => ""
    | as => Format.joinSep as (" + ")

def foo : alg ℤ ℕ := mk [⟨1,0⟩,⟨2,1⟩,⟨3,2⟩]

#eval foo

end FinsuppAlg.Repr

