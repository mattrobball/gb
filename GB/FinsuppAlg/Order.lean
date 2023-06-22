/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/

import GB.FinsuppAlg.Basic

variable {k : Type} {M : Type}
variable [DecidableEq k] [CommRing k] [LinearOrderedAddCommMonoid M]

open Finsupp Finset FinsuppAlg

namespace FinsuppAlg

-- scoped instance : Monad <| WithBot := inferInstanceAs <| Monad <| Option

/-- The leading monomial of `f` normalized to `lm 0 = ⊥`. -/
def lm (f : alg k M) : WithBot M := f.support.max

/-- The leading monomial of `f ≠ 0` as a term of `M` -/
def lm' (f : alg k M) (h : f ≠ 0) : M := f.support.max' <| support_nonempty_iff.mpr h

theorem lm'_eq_support_max (f : alg k M) (h : f ≠ 0) (h' : Finset.Nonempty f.support) :
    lm' f h = f.support.max' h' := rfl

@[simp]
theorem lm_zero_eq_bot : lm (0 : M →₀ k) = ⊥ := rfl

theorem lm_single {m : M} {a : k} (h : a ≠ 0) : lm (single' m a) = m := by
  dsimp [lm,single']
  simp only [if_neg h, max_singleton]

theorem ne_zero_of_lm_ne_top {f : alg k M} (h : lm f ≠ ⊥) : f ≠ 0 := fun h' => by simp [h'] at h

theorem lm_eq_top_iff_zero {f : alg k M} : lm f = ⊥ ↔ f = 0 := by
  refine ⟨ fun h => by_contra fun h' => ?_, fun h => lm_zero_eq_bot (k := k) (M := M) ▸ congrArg _ h ⟩
  exact h' <| support_eq_empty.mp <| Finset.max_eq_bot.mp h

theorem lm_eq_some_lm'_of_ne_zero {f : alg k M} (h : f ≠ 0) : lm f = lm' f h := by
  dsimp [lm,lm']
  simp [coe_max']

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
    rw [lm'_eq_support_max _ h' <| support_nonempty_iff.mpr h', Finset.max'_lt_iff]
    intro m h''
    have h''' : m ≤ lm' f h := le_max' _ _ <| tail_support_subset h|>.1 h''
    apply Ne.lt_of_le ?_ h'''
    intro h''''
    rw [h''''] at h''
    exact (mem_support_toFun _ _).mp h'' (tail_apply_lm_eq_zero _)

instance wflmLT {wf : WellFounded <| fun m m' : M => m < m'} : WellFoundedLT (alg k M) where
  wf := InvImage.wf (r := fun m m' : WithBot M => m < m') (fun (f : alg k M) => lm f)
    <| WithBot.wellFounded_lt wf

