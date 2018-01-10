import  .Sup_fin data.finsupp order.lattice data.nat.cast .euclidean_domain unique_factorization_domain
import .to_finsupp poly
universes u v w

noncomputable theory

open classical set function finsupp lattice
local attribute [instance] prop_decidable
local attribute [instance] finsupp.to_comm_semiring
local attribute [instance] finsupp.to_semiring
local infix ^ := monoid.pow

namespace polynomial
variables {α : Type u} {a a' a₁ a₂ : α} --{n m : ℕ} --do we want n and m?



instance {α : Type u} [unique_factorization_domain α]: unique_factorization_domain (polynomial α) :=
{ fac := sorry,
  unique := sorry,
  .. polynomial.integral_domain}

set_option trace.check true

lemma degree_eq_zero_of_is_unit [integral_domain α]{p : polynomial α}(h : is_unit p) : degree p = 0 :=
begin
  have h1 : ∃(r : polynomial α), p * r = 1,
  {
    fapply exists.intro,
    exact (to_unit h).inv,
    have h2 : (to_unit h).val*(to_unit h).inv = 1,
    from (to_unit h).val_inv,
    rw [to_unit_is_unit_val_eq] at h2,
    assumption
  },
  let r := some h1,
  have h2 : p * r = 1,
  from some_spec h1,
  have h3 : p * r ≠ 0,
  {
    calc p * r = 1 : h2
    ... ≠ 0 : by simp
  },
  have h4 : degree (p*r) = degree p + degree r,
  simp [degree_mul_integral_domain h3],
  rw h2 at h4,
  simp at h4,
  exact nat.eq_zero_of_add_eq_zero_right (eq.symm h4),
end

lemma eq_constant_of_is_unit [integral_domain α]{p : polynomial α}(h : is_unit p) : ∃c : α, p =  C c :=
begin
  have h1 : degree p = 0,
  from degree_eq_zero_of_is_unit h,
  simp only [eq_const_of_degree_eq_zero, *]
end

lemma leading_coeff_inv_mul_monic_of_ne_zero [field α ] {x : polynomial α} (h : x ≠ 0) : monic ((C (leading_coeff x)⁻¹) * x) :=
begin
  unfold monic,
  rw [leading_coeff_mul_eq_mul_leading_coef],
  simp,
  simp at h,
  rw [←leading_coef_eq_zero_iff_eq_zero] at h,
  exact inv_mul_cancel h
end

lemma leading_coeff_dvd [field α ] {x : polynomial α} : (C (leading_coeff x)) ∣ x := 
begin 
  by_cases h1 : (x = 0),
  {
    simp *
  },
  {
    simp [has_dvd.dvd],
    fapply exists.intro,
    exact (C (leading_coeff x)⁻¹)*x,
    rw [←leading_coef_eq_zero_iff_eq_zero, ←ne.def] at h1,
    rw [←mul_assoc, ←C_mul_C, mul_inv_cancel h1],
    simp
  }



end

lemma polynomial_fac [field α] {x : polynomial α} : ∃ c :  α, ∃ p : multiset (polynomial α), x = C c * p.prod ∧ (∀x∈p, irreducible x ∧ monic x)  :=
begin
  by_cases h1 : (x = 0),
  {
    fapply exists.intro,
    exact 0,
    fapply exists.intro,
    exact 0,
    simp [*]
  },
  {
    by_cases h2 : (is_unit x),
    {
      have h3: ∃c : α, x =  C c,
      from eq_constant_of_is_unit h2,
      let c := some h3,
      fapply exists.intro,
      exact c,
      fapply exists.intro,
      exact 0,
      simp,
      exact some_spec h3
    },
    {
      let f := some (unique_factorization_domain.fac h1 h2),
      have h3 : x = f.prod ∧ (∀x∈f, irreducible x),
      from some_spec (unique_factorization_domain.fac h1 h2),
      fapply exists.intro,
      exact (f.map leading_coeff).prod,
      fapply exists.intro,
      exact (f.map (λ y, (C (leading_coeff y)⁻¹ )*y) ),
      --Need lemma prod_mul_prod
    }

    



    /-
    let u := some (factorization h1),
    have h2 : ∃(g : multiset (polynomial α)), x = ↑u * multiset.prod g ∧ ∀ (y : polynomial α), y ∈ g → irreducible y,
    from some_spec (factorization h1),
    let g := some h2,
    have h3 : x = ↑u * multiset.prod g ∧ ∀ (y : polynomial α), y ∈ g → irreducible y,
    from some_spec h2,
    fapply exists.intro,
    exact u *((g.map leading_coeff).prod)-/

  }
end

 end polynomial
