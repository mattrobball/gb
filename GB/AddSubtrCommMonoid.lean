import Mathlib.Algebra.Group.Pi
import Mathlib.Data.Nat.Basic

universe u

class AddSubtrCommMonoid (M : Type u) extends AddCommMonoid M, Sub M where
  sub_of_add : ∀ {m₁ m₂ m₃ : M}, m₁ = m₂ + m₃ →  m₁ - m₂ = m₃

namespace AddSubtrCommMonoid

instance nat : AddSubtrCommMonoid ℕ :=
  { sub_of_add := fun h => by
      rw [h, Nat.add_comm, Nat.add_sub_cancel]}

instance piFin (n : ℕ) : AddSubtrCommMonoid (Fin n → ℕ) :=
  { sub_of_add := fun h => funext <| fun _ => by
      rw [h, Pi.sub_apply, Pi.add_apply, Nat.add_comm, Nat.add_sub_cancel]}

end AddSubtrCommMonoid

