import  .Sup_fin data.finsupp order.lattice data.nat.cast .euclidean_domain unique_factorization_domain
import .to_finsupp poly .to_multiset poly_over_integral_domain
--import data.multiset
universes u v w

local notation a`~ᵤ`b := associated a b

noncomputable theory

open classical set function finsupp lattice
local attribute [instance] prop_decidable
local attribute [instance] finsupp.to_comm_semiring
local attribute [instance] finsupp.to_semiring
local infix ^ := monoid.pow

namespace polynomial

open associated
variables {α : Type u} {a a' a₁ a₂ : α} --{n m : ℕ} --do we want n and m?

instance {α : Type u} [unique_factorization_domain α]: unique_factorization_domain (polynomial α) :=
{ fac := sorry,
  unique := sorry,
  .. polynomial.integral_domain}

lemma degree_gcd_le_left [unique_factorization_domain α] {a b : polynomial α} (h : a ≠ 0): degree (gcd a b) ≤ degree a :=
begin
  have  h1 : gcd a b ∣ a,
  from gcd_left,
  apply nat.le_trans (degree_dvd h1 h),
  exact nat.le_refl _,
end

lemma associated_neg [unique_factorization_domain α] (a : polynomial α) : (a ~ᵤ (-a)) :=
begin
  have h_u: is_unit (-1 : polynomial α),
  {
    have : ((-1 : polynomial α) * -1 = 1),
    {
      simp,
    },
    exact is_unit_of_mul_eq_one_left this,
  },
  rcases h_u with ⟨u, hu⟩,
  exact ⟨u, by {rw ←hu, simp}⟩,
end

end polynomial
