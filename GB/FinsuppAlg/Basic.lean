/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/

import Mathlib.Data.Finsupp.Defs
import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Algebra.Algebra.Basic

open Finsupp Finset

variable (k : Type) (M : Type)
variable [DecidableEq k] [DecidableEq M]
variable [AddMonoid M] [CommRing k]

namespace FinsuppAlg

abbrev alg := M →₀ k

variable {k M}

def single' (a : M) (b : k) : M →₀ k where
  support :=
    if b = 0 then ∅ else {a}
  toFun :=
    Pi.single a b
  mem_support_toFun a' := by
      obtain rfl | hb := eq_or_ne b 0
      · simp [Pi.single, update]
      rw [if_neg hb, mem_singleton]
      obtain rfl | ha := eq_or_ne a' a
      · simp [hb, Pi.single, update]
      simp [Pi.single_eq_of_ne' ha.symm, ha]

@[simp]
theorem single'_coe (m : M) (a : k) : (single' m a : M → k) = Pi.single m a := rfl

@[simp]
theorem single'_apply (m : M) (a : k) : (single' m a) m = a := by simp

@[simp]
theorem single'_apply_neq (m m' : M) (a : k) (h : m' ≠ m) : (single' m a) m' = 0 := by
  dsimp [single']
  rw [Pi.single_apply, if_neg h]

theorem single'_support (m : M) (a : k) : (single' m a).support = if a = 0 then ∅ else {m} := rfl

instance : Add (alg k M) where
  add v w :=
    { support := (v.support ∪ w.support).filter (fun a => v a + w a ≠ 0)
      toFun := fun a => v a + w a
      mem_support_toFun := fun a => by
        simp only [mem_filter,mem_union,mem_support_iff, and_iff_right_iff_imp]
        rw [←not_and_or]
        intro h hneg
        rw [hneg.1,hneg.2,zero_add] at h
        simp at h }

def mk (l : List <| M × k) : alg k M := l.map (fun p => single' p.1 p.2)|>.foldl (· + ·) 0

protected theorem coe_add (f g : alg k M) : ⇑(f + g) = f + g := rfl

instance : SMul ℕ (alg k M) where
  smul n v :=
    { support := v.support.filter (fun a => n • v a ≠ 0)
      toFun := fun a => n • v a
      mem_support_toFun := fun a => by aesop }
        -- simp only [mem_filter,mem_support_iff,and_iff_right_iff_imp]
        -- intro h hneg
        -- rw [hneg] at h
        -- simp at h }

instance (priority := 1000) : Neg (alg k M) where
  neg v :=
    { support := v.support
      toFun := fun a => - v a
      mem_support_toFun := fun a => by simp }

@[simp]
protected theorem neg_coe_apply (f : alg k M) (m : M) : (- f : alg k M) m = - f m := rfl

instance (priority := 1000) : Sub (alg k M) where
  sub v w := v + (- w)

@[simp]
protected theorem sub_coe_apply (f g : alg k M) (m : M) : (f - g : alg k M) m = f m - g m := by
  change f m + (- g m) = f m - g m
  rw [sub_eq_add_neg]

instance : AddCommMonoid (alg k M) :=
  FunLike.coe_injective.addCommMonoid _ coe_zero FinsuppAlg.coe_add fun _ _ => rfl

instance : Mul (alg k M) :=
  ⟨fun f g => f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single' (a₁ + a₂) (b₁ * b₂)⟩

instance : SMul k (alg k M) where
  smul a v :=
    { support := v.support.filter (fun m => a • v m ≠ 0)
      toFun := fun m  => a • v m
      mem_support_toFun := fun m => by aesop }
        -- simp only [smul_eq_mul, ne_eq, mem_support_iff, mem_filter, and_iff_right_iff_imp]
        -- intro h h'
        -- simp [h'] at h}

end FinsuppAlg

-- instance : Semiring (alg k M) := sorry
--
-- instance : Algebra k (alg k M) :=
--   { smul := sorry
--     smul_def' := sorry
--     commutes' := sorry }
