/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Pi
import Mathlib.Data.Fintype.Pi

/-- Notation typeclass `━?` (typed `\--_?`) which represents subtractability -/
class Sbt (α : Type _) where
  sbt : α → α → Prop

infix:50 " ━? " => Sbt.sbt

instance (M : Type u) [AddCommSemigroup M] : Sbt M where
  sbt m₁ m₂ := ∃ m₃, m₂ + m₃ = m₁

namespace Nat

instance decSbt (n m : ℕ) : Decidable <| n ━? m := decidable_of_iff (m ≤ n)
  ⟨fun h => ⟨n-m, by nth_rw 2 [← Nat.sub_add_cancel h]; ac_rfl⟩,
    fun h => h.elim fun a h => by simp only [le_add_right,←h] ⟩

end Nat

namespace Pi

variable {α : Type _} [Fintype α]

theorem forall_le_iff_pi_sbt {f g : α → ℕ} : (∀ i, g i ≤ f i) ↔ f ━? g :=
  ⟨fun h => ⟨fun i => f i - g i, funext fun i => by rw [← Nat.sub_add_cancel <| h i]; ac_rfl⟩ ,
    fun h' i => h'.elim fun h h'' => by
      rw [← congrFun h'' i, add_apply]; apply Nat.le_add_right (g i) (h i)⟩

instance fintypeDecSbt (f g : α → ℕ) : Decidable <| f ━? g :=
  decidable_of_iff (∀ i, g i ≤ f i) forall_le_iff_pi_sbt

/-- This maybe faster ...? -/
def finDecSbt {n : ℕ} (f g : Fin n → ℕ) : Decidable <| f ━? g :=
  @decidable_of_iff _ (∀ i, g i ≤ f i) forall_le_iff_pi_sbt <| Nat.decidableForallFin _

end Pi
