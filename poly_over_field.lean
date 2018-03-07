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

open associated

lemma setoid_r_eq_associated {α : Type*} [unique_factorization_domain α] (p q : α) :
  @setoid.r α (associated.setoid α) p q = associated p q :=
rfl

lemma make_monic_associated [field α] (a : polynomial α) : (make_monic a) ~ᵤ (a) :=
begin
  simp [make_monic],
  by_cases h1 : a = 0,
  {
    simp * at *,
  },
  {
    simp [if_neg, *],
    have : is_unit (C (leading_coeff a)),
    {
      have : is_constant (C (leading_coeff a)),
        from ⟨_, rfl⟩,
      rw is_constant_iff_eq_zero_or_is_unit at this,
      cases this with h,
      {
        rw [C_eq_zero_iff_eq_zero, leading_coef_eq_zero_iff_eq_zero] at h,
        contradiction,
      },
      {
        simp *,
      }
    },
    rw mul_comm,
    apply associated_of_mul_is_unit this,
    rw ←leading_coef_eq_zero_iff_eq_zero at h1,
    rw [mul_assoc, ←C_mul_C, inv_mul_cancel h1],
    simp,
  }

end

lemma monic_out_eq [field α] (q : associated.quot (polynomial α)): associated.mk (monic_out q) = q :=
begin
  apply quot.induction_on q,
  intro a,
  apply quot.sound,
  dsimp [setoid_r_eq_associated, monic_out],
  change (make_monic a ~ᵤ a),
  exact make_monic_associated _,  
end

lemma monic_out_mk_associated [field α] (p : polynomial α): (monic_out (associated.mk p) ~ᵤ p) :=
associated.complete (monic_out_eq (associated.mk p))

lemma monic_out_mk_eq [field α] (p : polynomial α) (h : monic p) : (monic_out (associated.mk p) = p) :=
begin
  have : (monic_out (associated.mk p) ~ᵤ p),
    from monic_out_mk_associated p,
  rwa [associated_iff_eq_of_monic_of_monic _ h] at this,
  apply monic_monic_out_of_ne_zero,
  rw [ne.def, associated.mk_eq_zero_iff_eq_zero],
  by_contradiction hp,
  subst hp,
  simp [not_monic_zero, *] at *,
end


lemma monic_out_one : monic_out (1 : quot (polynomial α)) = 1 :=
begin
  have : mk 1 = (1 : quot (polynomial α)),
  {
    rw mk_eq_one_iff_is_unit,
    simp,
  },
  rw ←this,
  rw monic_out_mk_eq,
  simp,

end

open multiset
lemma prod_map_monic_out_commute (s : multiset (quot (polynomial α))) : (map monic_out (s)).prod = monic_out s.prod :=
begin
  apply multiset.induction_on s,
  {
    simp [monic_out_one],
  },
  {
    intros a s h,
    simp * at *, --need monic_out_mul
  }


end


end field

end polynomial 