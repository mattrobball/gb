/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/

import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Group.Pi
import Mathlib.Data.Nat.Basic

universe u

class LinearOrderedAddSubtrCommMonoid (M : Type u) extends LinearOrderedAddCommMonoid M, Sub M where
  lcs : M → M → M
  lcs_left : ∀ {m₁ m₂ : M}, ∃ m', lcs m₁ m₂ = m' + m₁
  lcs_right : ∀ {m₁ m₂ : M}, ∃ m', lcs m₁ m₂ = m' + m₂
  lcs_least : ∀ {m₁ m₂ m : M}, (∃ m₁', m = m₁' + m₁) → (∃ m₂', m = m₂' + m₂) → ∃ m', m = m' + lcs m₁ m₂
  sub_of_add : ∀ {m₁ m₂ m₃ : M}, m₁ = m₂ + m₃ → m₁ - m₂ = m₃

namespace LinearOrderedAddSubtrCommMonoid

instance nat : LinearOrderedAddSubtrCommMonoid ℕ :=
  { add_le_add_left := fun a b h c => Nat.add_le_add_left h c
    lcs := max
    lcs_left := fun {a b} => ⟨max a b - a, Nat.sub_add_cancel (Nat.le_max_left a b)|>.symm⟩
    lcs_right := fun {a b} => ⟨max a b - b,  Nat.sub_add_cancel (Nat.le_max_right a b)|>.symm⟩
    lcs_least := fun {a b c} ⟨d,hd⟩ ⟨e,he⟩ => ⟨c - max a b, by
      refine Nat.sub_add_cancel (max_le ?_ ?_)|>.symm
      · simp only [hd, Nat.le_add_left]
      · simp only [he, Nat.le_add_left] ⟩
    sub_of_add := fun h => by
      rw [h, Nat.add_comm, Nat.add_sub_cancel]}

-- def piFin (n : ℕ) : LinearOrderedAddSubtrCommMonoid (Fin n → ℕ) :=
--   { le_total := sorry
--     decidableLE := sorry
--     add_le_add_left := sorry
--     lcs := fun f g i => max (f i) (g i)
--     lcs_left := fun {f g} => ⟨fun i => max (f i) (g i) - f i,
--       funext fun i => Nat.sub_add_cancel (Nat.le_max_left _ _)|>.symm⟩
--     lcs_right := fun {f g} => ⟨fun i => max (f i) (g i) - g i,
--       funext fun i => Nat.sub_add_cancel (Nat.le_max_right _ _)|>.symm⟩
--     lcs_least := fun {f g h} ⟨u,hu⟩ ⟨v,hv⟩ => ⟨fun i => h i - max (f i) (g i), funext fun i => by
--       refine Nat.sub_add_cancel (max_le ?_ ?_)|>.symm
--       · simp [hu, Nat.le_add_left]
--       · simp [hv, Nat.le_add_left] ⟩
--     sub_of_add := fun h => funext <| fun _ => by
--       rw [h, Pi.sub_apply, Pi.add_apply, Nat.add_comm, Nat.add_sub_cancel]}

end LinearOrderedAddSubtrCommMonoid

