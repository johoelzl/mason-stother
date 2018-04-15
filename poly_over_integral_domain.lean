import  .Sup_fin data.finsupp order.lattice data.nat.cast .euclidean_domain unique_factorization_domain
import .to_finsupp .to_finset poly
universes u v w

noncomputable theory

open classical set function finsupp lattice

local attribute [instance] finsupp.to_comm_semiring
local attribute [instance] finsupp.to_semiring
local infix ^ := monoid.pow
local notation a `~ᵤ` b : 50 := associated a b --also present in UFD
namespace polynomial
local attribute [instance] prop_decidable
variables {α : Type u} {a a' a₁ a₂ : α} --{n m : ℕ} --do we want n and m?

section integral_domain
variable [integral_domain α]

lemma X_pow_ne_zero {n : ℕ}: (X ^ n : polynomial α) ≠ 0 :=
begin
  intro h2,
  have h3: (single n 1 : polynomial α ) n = 1,
  {
    simp,
  },
  rw X_pow_eq_single at h2,   
  rw h2 at h3,
  simp * at *,
end

lemma zero_ne_one : (0:polynomial α) ≠ 1:=
begin
  intro h,
  have : (0 : polynomial α) 0 = (1 : polynomial α) 0, 
  { rw [h]},
  simp * at *
end

instance {α : Type u} [integral_domain α] : zero_ne_one_class (polynomial α):=
{ zero_ne_one := zero_ne_one, .. polynomial.comm_ring }

/- Can we use this to reduce the lemma below?
lemma leading_coeff_mul_leading_coeff_eq_zero_of_mul_eq_zero (f g : polynomial α) (h : f * g = 0) : (leading_coeff f) * (leading_coeff g) = 0 :=
begin
  have h1 : leading_coeff f = 0 ∨  leading_coeff g = 0,
  {
    by_contradiction h2,
    rw [not_or_distrib, leading_coef_eq_zero_iff_eq_zero, leading_coef_eq_zero_iff_eq_zero] at h2,
  }
end
-/

lemma eq_zero_or_eq_zero_of_mul_eq_zero : ∀ f g : polynomial α, f * g = 0 → f = 0 ∨ g = 0 :=
begin
  intros f g h1,
  by_contradiction h2,
  rw [not_or_distrib, ←leading_coef_eq_zero_iff_eq_zero, ←leading_coef_eq_zero_iff_eq_zero] at h2,
  have h7 : (leading_coeff f) * (leading_coeff g) ≠ 0,
  {
    intro h8,
    have h9 : leading_coeff f = 0 ∨  leading_coeff g = 0,
      from eq_zero_or_eq_zero_of_mul_eq_zero h8,
    cases h9 ; simp * at *,
  },
  have h8 : (f * g) (degree f + degree g) ≠ 0,
  {
    simpa [mul_degree_add_degree_eq_leading_coeff_mul_leading_coeff],   
  },
  rw [h1, zero_apply] at h8,
  contradiction
end

instance {α : Type u} [integral_domain α] : no_zero_divisors (polynomial α):=
{eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero
.. polynomial.comm_ring}

instance {α : Type u} [integral_domain α]: integral_domain (polynomial α) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero,
  .. polynomial.comm_ring, .. polynomial.zero_ne_one_class }

--naming?
lemma mul_eq_zero_iff_mul_leading_coef_eq_zero {f g : polynomial α} : f * g = 0 ↔ (leading_coeff f) * (leading_coeff g) = 0 :=
begin
  constructor,
  { 
    intro h1,
    rw [←mul_degree_add_degree_eq_leading_coeff_mul_leading_coeff, h1],
    simp,
  },
  {
    intro h1,
    have h2 : leading_coeff f = 0 ∨ leading_coeff g = 0,
      from _root_.eq_zero_or_eq_zero_of_mul_eq_zero  h1,
    cases h2 ; {simp [leading_coef_eq_zero_iff_eq_zero, * ] at *}
  }
end

--naming?
lemma degree_mul_eq_add_of_mul_ne_zero {f g : polynomial α} : f * g ≠ 0 → degree (f * g) = degree f + degree g :=
begin
  intro h1, 
  have h2 : f ≠ 0,
    from ne_zero_of_mul_ne_zero_right h1,
  have h3 : g ≠ 0,
    from ne_zero_of_mul_ne_zero_left h1,
  have h4 : (f * g) (degree f + degree g) ≠ 0,
  {
    calc (f * g) (degree f + degree g) = (leading_coeff f) * (leading_coeff g) : mul_degree_add_degree_eq_leading_coeff_mul_leading_coeff
      ... ≠ 0 : by {simp,rw [←not_iff_not_of_iff mul_eq_zero_iff_mul_leading_coef_eq_zero], exact h1},
  },
  have h5 : (degree f + degree g) ≤ degree (f * g),
    from le_degree h4,
  have h6 : degree (f * g) ≤ (degree f + degree g),
    from degree_mul,
  apply le_antisymm; simp * at *
end

--naming?
lemma degree_dvd {f g : polynomial α} (h1 : f ∣ g)(h4 : g ≠ 0) : degree f ≤ degree g :=
begin
  rcases h1 with ⟨c, h2⟩,
  subst h2,
  by_cases h : (f = 0),
  {
    simp [h, nat.zero_le],
  },
  {
    have h3 : degree (f * c) = degree f + degree c,
      from degree_mul_eq_add_of_mul_ne_zero h4,
    exact (nat.le.intro h3.symm),
  }
end

lemma prod_ne_zero_of_forall_mem_ne_zero {f : finset (polynomial α)} : (∀ x ∈ f, x ≠ (0 : polynomial α)) → f.prod id ≠ 0 :=
begin
  apply finset.induction_on f,
  {
    simp *,
  },
  {
    intros a s h1 h2 h3,
    have h4 : (∀ (x : polynomial α), x ∈ s → x ≠ 0),
    {
      intros x h4,
      simp * at *,
    },
    have h5 : finset.prod s id ≠ 0,
      from h2 h4,
    have h6 : a ≠ 0,
    {
      simp * at *,
    },
    simp [finset.prod_insert h1],
    exact mul_ne_zero h6 h5,
  }
end

--naming?
lemma degree_prod {β : Type u} {s : finset β} {f : β → polynomial α} : finset.prod s f ≠ 0 → degree (s.prod f) = s.sum (degree ∘ f) :=
begin
  fapply finset.induction_on s,
  {
    simp *,
  },
  {
    intros a s h1 h2 h3,
    have h4 : finset.prod s f ≠ 0,
    {
      rw [finset.prod_insert h1] at h3,
      exact ne_zero_of_mul_ne_zero_left h3,      
    },
    have h5 : degree (finset.prod s f) = finset.sum s (degree ∘ f),
      from h2 h4,
    simp *,
    rw [degree_mul_eq_add_of_mul_ne_zero, h5],
    rw [finset.prod_insert h1] at h3,
    exact h3,
  },
end

-- naming? incliude id?
lemma degree_prod_eq_sum_degree_of_prod_ne_zero {f : finset (polynomial α)} : (f.prod id ≠ 0) → degree (f.prod id) = f.sum (degree) :=
begin
  fapply finset.induction_on f,
  {
    simp *
  },
  {
    intros a s h1 h2 h3,
    simp [finset.prod_insert h1, finset.sum_insert h1],
    have h4: finset.prod (s) id ≠ 0,
    {
      rw finset.prod_insert at h3,
      exact ne_zero_of_mul_ne_zero_left h3,
      exact h1,
    },
    have h5: degree (finset.prod s id) = finset.sum s degree,
      from h2 h4,
    have h6 : a * finset.prod s (λ (x : polynomial α), x) ≠ 0,
    {
      simp [finset.prod_insert h1, *] at *,
    },
    simp [degree_mul_eq_add_of_mul_ne_zero h6, *] at *,
  }
end

--naming
lemma degree_pow {x : polynomial α}{n : ℕ} : degree (x ^ n) = n * degree x :=
begin
  induction n with n h1,
  {
    simp *,
  },
  {
    by_cases h : (x = 0),
    {
      simp [pow_succ, *] at *,
    },
    {
      rw [pow_succ, degree_mul_eq_add_of_mul_ne_zero, h1],
      exact calc degree x + n * degree x = 1 * degree x + n * degree x : by simp
          ... = n * degree x + 1 * degree x : by rw add_comm (1 * degree x) (n * degree x)
          ... = (n + 1) * degree x : by rw [add_mul]
          ... = nat.succ n * degree x : rfl,
      have : (x ^ n ≠ 0),
        from pow_ne_zero _ h,
      exact mul_ne_zero h this,
    },   
  }
end

--naming?
lemma degree_finsupp_prod {f : polynomial α →₀ ℕ} (h1 : finsupp.prod f (λ x n, x^n) ≠ 0): degree (finsupp.prod f (λ x n, x^n)) = finsupp.sum f (λ x n, n*(degree x)):=
begin
  rw [finsupp.prod, degree_prod h1, finsupp.sum],
  simp [(∘), * , degree_pow],
end

--naming?
lemma leading_coeff_mul_eq_mul_leading_coef {f g : polynomial α} : leading_coeff (f * g) = leading_coeff f * leading_coeff g :=
begin
  by_cases h1 : (f * g = 0),
  {
    simp * at *,
    cases eq_zero_or_eq_zero_of_mul_eq_zero _ _ h1 with h2 ; {simp *},
  },
  {
    have : degree (f * g) = degree f + degree g,
      from degree_mul_eq_add_of_mul_ne_zero h1,
    simp [leading_coeff, this, mul_degree_add_degree_eq_leading_coeff_mul_leading_coeff]
  }    
end

lemma monic_mul_of_monic_of_monic {a b : polynomial α} (ha : monic a) (hb : monic b) : monic (a * b) :=
begin
  simp [monic, leading_coeff_mul_eq_mul_leading_coef, *] at *,
end

lemma monic_prod_of_forall_mem_monic [comm_semiring α] {s : multiset (polynomial α)} (hs: ∀x ∈ s, monic x) : monic s.prod :=
begin
  revert hs,
  apply multiset.induction_on s,
  {
    simp * at *,
  },
  {
    intros a s h1 h2,
    simp * at *,
    have ha : monic a,
    {
      simp * at *,
    },
    have hs : monic (multiset.prod s),
    {
      apply h1,
      intros x s,
      simp * at *,
    },
    exact monic_mul_of_monic_of_monic ha hs,
  }
end

lemma not_is_constant_mul_of_not_is_constant_of_ne_zero (p q : polynomial α) 
(h1 : ¬ is_constant p)(h2 : q ≠ 0) : ¬ is_constant (p * q) :=
begin
  intro h,
  by_cases hc : p * q = 0,
  {
    have h6 : p = 0 ∨ q = 0,
      from eq_zero_or_eq_zero_of_mul_eq_zero _ _ hc,
    cases h6 ; simp * at *, 
  },
  {
    have : degree (p*q) = degree p + degree q,
      from degree_mul_eq_add_of_mul_ne_zero hc,
    have h3 : degree (p*q) = 0,
    { rwa [←is_constant_iff_degree_eq_zero]},
    have h4 : degree p > 0,
    { rwa [nat.pos_iff_ne_zero, ne.def, ←is_constant_iff_degree_eq_zero]},
    have h6 : degree p + degree q > 0,
      from nat.add_pos_left h4 _,
    simp [*] at *,
    exact nat.not_lt_zero _ h6,
  },
end

--Should be in lib, used it on two spots already.
lemma one_le_of_ne_zero {n : ℕ} : n ≠ 0 → 1 ≤ n := --is also used in MS, hence can't make private.
begin
  intro h1,
  induction n,
  {
    contradiction,
  },
  {
    simp [nat.succ_le_succ, nat.zero_le],
  }
end

--naming?
lemma is_constant_add {a b c : polynomial α} (h1 : is_constant a) (h2 : is_constant b) (h_add : a + b = c): is_constant c :=
begin
  have h3 : degree (a + b) ≤ max (degree a) (degree b),
    from degree_add,
  rw is_constant_iff_degree_eq_zero at *,    
  simp * at *,
  exact nat.eq_zero_of_le_zero h3,
end



lemma degree_eq_zero_of_is_unit [integral_domain α]{p : polynomial α}(h : is_unit p) : degree p = 0 :=
begin
  have h1 : ∃(r : polynomial α), p * r = 1,
  {
    rcases h with ⟨u, hu⟩,
    fapply exists.intro u.inv,
    subst hu,
    rw [←units.inv_coe, units.mul_inv],
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
  simp [degree_mul_eq_add_of_mul_ne_zero h3],
  rw h2 at h4,
  simp at h4,
  exact nat.eq_zero_of_add_eq_zero_right (eq.symm h4),
end

lemma is_constant_of_is_unit [integral_domain α]{p : polynomial α}(h : is_unit p) : is_constant p :=
begin
  have h1 : degree p = 0,
  from degree_eq_zero_of_is_unit h,
  rw is_constant,
  exact is_constant_of_degree_eq_zero h1,
end


--Naming is incorrect, need C in the name here
lemma is_unit_of_is_unit [integral_domain α] {a : α}(h1 : is_unit a) : is_unit (C a) :=
begin
  simp [is_unit] at *,
  rcases h1 with ⟨u, hu⟩,
  let Cu : units (polynomial α):=
  {
    val := C u.val,
    inv := C u.inv,
    val_inv := by rw [←C_mul_C, u.val_inv, C_1],
    inv_val := by rw [←C_mul_C, u.inv_val, C_1]
  },
  exact ⟨Cu, by simp [hu, units.val_coe]⟩,
end

lemma eq_one_of_monic_unit [integral_domain α] {f : polynomial α}(h1 : monic f) (h2 : is_unit f) : f = 1 :=
begin
  rw monic at *,
  have h3 : ∃c : α, f =  C c,
  from is_constant_of_is_unit h2,
  let c := some h3,
  have h4 : f = C c,
  from some_spec h3,
  rw [h4, leading_coeff_C] at h1,
  rw h1 at h4,
  simp at h4,
  assumption
end

--lemma monic polynomials are associated iff they are equal.
lemma associated_iff_eq_of_monic_of_monic [integral_domain α] {x y : polynomial α}(h1 : monic x)(h2 : monic y) : (x ~ᵤ y) ↔ x = y :=
begin
  constructor,
  {
     intro h3,
     rw associated at h3,
     let u:= some h3,
     have h4 : x = ↑u * y,
     from some_spec h3,
     rw monic at *,
     have h5 : leading_coeff (↑u * y) = (leading_coeff ↑u) * (leading_coeff y),
     from leading_coeff_mul_eq_mul_leading_coef,
     rw [←h4, h1, h2] at h5,
     have h6 : leading_coeff (↑u : polynomial α) = 1,
     {simp at h5, exact eq.symm h5},
     have h7 : is_unit (↑u : polynomial α ),
     {
       constructor,
       swap,
       exact u,
       exact rfl
     },
     have h8 : monic (↑u : polynomial α ),
     from h6,
     have h9 : (↑u : polynomial α ) = 1,
     from eq_one_of_monic_unit h8 h7,
     rw h9 at h4,
     simp [h4]

  },
  {
    intro h3,
    simp [h3]
  }
end


lemma eq_C_leading_coeff_of_is_unit [integral_domain α] {a : polynomial α} (h : is_unit a) : a = C (leading_coeff a) :=
begin
  have : ∃c : α, a =  C c,
    from is_constant_of_is_unit h,
  rcases this with ⟨c, hc⟩,
  subst hc,
  simp [leading_coeff_C],
end



end integral_domain
end polynomial