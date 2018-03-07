import  .Sup_fin data.finsupp order.lattice data.nat.cast .euclidean_domain unique_factorization_domain
import .to_finsupp poly .to_multiset poly_over_UFD
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
variables {α : Type u} 

section field

variable [field α]

lemma is_unit_C_of_ne_zero {c : α} (h : c ≠ 0) : is_unit (C c) :=
begin
  have : (C c) * (C c⁻¹) = 1,
  {
    rw ←C_mul_C,
    have : c *c⁻¹ = 1,
      from mul_inv_cancel h,
    simp *,
  },
  exact is_unit_of_mul_eq_one_left this,
end

lemma is_constant_iff_eq_zero_or_is_unit (a : polynomial α) : is_constant a ↔ a = 0 ∨ is_unit a :=
begin
  split,
  {
    intro h,
    by_cases h1 : a = 0,
    {
      simp *,
    },
    {
      rcases h with ⟨c, hc⟩,
      subst hc,
      rw C_eq_zero_iff_eq_zero at h1,
      have : is_unit (C c),
        from is_unit_C_of_ne_zero h1,
      simp *,
    }
  },
  {
    intro h,
    cases h,
    {
      subst h,
      simp,
    },
    {
      exact is_constant_of_is_unit h,      
    }
  }
end

lemma degree_ne_zero_of_irreducible (a : polynomial α) (h : irreducible a) : (degree a) ≠ 0:=
begin
  rw [ne.def, ←is_constant_iff_degree_eq_zero, is_constant_iff_eq_zero_or_is_unit, not_or_distrib],
  exact ⟨h.1, h.2.1⟩,
end

end field

end polynomial 