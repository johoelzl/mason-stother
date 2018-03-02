import  .Sup_fin data.finsupp order.lattice data.nat.cast .euclidean_domain unique_factorization_domain
import .to_finsupp poly .to_multiset
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
variables {α : Type u} {a a' a₁ a₂ : α} --{n m : ℕ} --do we want n and m?

instance {α : Type u} [unique_factorization_domain α]: unique_factorization_domain (polynomial α) :=
{ fac := sorry,
  unique := sorry,
  .. polynomial.integral_domain}

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
  simp [degree_mul_eq_add_of_mul_ne_zero h3],
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

--Naming is incorrect, need C in the name here
lemma is_unit_of_is_unit [integral_domain α] {a : α}(h1 : is_unit a) : is_unit (C a) :=
begin
  simp [is_unit] at *,
  let u := to_unit h1,
  fapply exists.intro,
  {
    constructor,
    tactic.rotate_right 2,
    exact C a,
    exact C (↑u⁻¹),
    {
      rw [←C_mul_C,←@to_unit_is_unit_val_eq _ _ a _, ←units.val_coe, units.mul_inv],
      simp
    },
    {
      rw [←C_mul_C,←@to_unit_is_unit_val_eq _ _ a _, ←units.val_coe, units.inv_mul],
      simp
    }
  },
  exact rfl,
end

lemma eq_one_of_monic_unit [integral_domain α] {f : polynomial α}(h1 : monic f) (h2 : is_unit f) : f = 1 :=
begin
  rw monic at *,
  have h3 : ∃c : α, f =  C c,
  from eq_constant_of_is_unit h2,
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
open associated

def make_monic [field α] (f : polynomial α) := if (f = 0) then 0 else (C (f.leading_coeff)⁻¹ * f)

#check make_monic



lemma monic_make_monic_of_ne_zero [field α] (f : polynomial α) (h : f ≠ 0) : monic f.make_monic :=
begin
  simp [make_monic, if_neg, *],
  exact leading_coeff_inv_mul_monic_of_ne_zero h,
end

lemma eq_C_leading_coeff_of_is_unit [integral_domain α] {a : polynomial α} (h : is_unit a) : a = C (leading_coeff a) :=
begin
  have : ∃c : α, a =  C c,
    from eq_constant_of_is_unit h,
  rcases this with ⟨c, hc⟩,
  subst hc,
  simp [leading_coeff_C],
end

--set_option pp.all true

#check eq.rec

--We can always choose a monic representant
def monic_out [field α] (a : quot (polynomial α)) : polynomial α := 
begin
  fapply quot.rec_on a,
  exact make_monic,
  {
    intros f p h,
    have : make_monic f = make_monic p,
    {


      have h1: associated f p,
        from h,
      rcases h1 with ⟨u, hu⟩,
      have hu2: is_unit ↑u,
        from is_unit_unit u,
      by_cases hf : f = 0,
      {
        subst hf,
        have hu3 := hu.symm,
        rw mul_eq_zero_iff_eq_zero_or_eq_zero at hu3,
        cases hu3,
        {
          simp [hu3] at *,
          contradiction,
        },
        {
          subst hu3,
        }
      },
      {
        by_cases hp : p = 0,
        {
          subst hp,
          simp * at *,
        },
        {
          have hp2 : ↑u * p ≠  0,
          {
            rw [ne.def, mul_eq_zero_iff_eq_zero_or_eq_zero],
            rw not_or_distrib,
            exact ⟨ne_zero_of_is_unit zero_ne_one hu2, hp⟩,
          },
          simp [make_monic, if_neg, *],
          rw [leading_coeff_mul_eq_mul_leading_coef, mul_inv_eq, C_mul_C, mul_assoc],
          rw [eq_C_leading_coeff_of_is_unit hu2] {occs := occurrences.pos [2]},
          rw [←mul_assoc (C (leading_coeff ↑u)⁻¹), ←C_mul_C, inv_mul_cancel],
          simp,
          admit,
          admit,
          admit,
          
        }
      }


    },
    

  },

end



lemma polynomial_fac [field α] (x : polynomial α) : ∃ c :  α, ∃ p : multiset (polynomial α), x = C c * p.prod ∧ (∀x∈p, irreducible x ∧ monic x)  :=
begin
  by_cases h1 : (x = 0),
  {
    fapply exists.intro,
    exact 0,
    fapply exists.intro,
    exact 0,
    simp [C_0, h1],
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
      have h3a : x = multiset.prod f,
      from and.elim_left h3,
      have h3b : ∀ (x : polynomial α), x ∈ f → irreducible x,
      from and.elim_right h3,
      fapply exists.intro,
      exact (f.map leading_coeff).prod,
      fapply exists.intro,
      exact (f.map (λ y, (C (leading_coeff y)⁻¹ )*y) ),
      constructor,
      {
        rw h3a,
        rw [C_prod_eq_prod_C, multiset.map_map],--, ←multiset.prod_add

        have h4 : ∀ g : multiset (polynomial α), (∀ (y : polynomial α), y ∈ g → irreducible y) → multiset.prod g =
    C (multiset.prod (multiset.map leading_coeff g)) *
      multiset.prod (multiset.map (λ (y : polynomial α), C (leading_coeff y)⁻¹ * y) g),
      {
        apply @multiset.induction _ (λ (g : multiset (polynomial α)),
    (∀ (y : polynomial α), y ∈ g → irreducible y) →
    multiset.prod g =
      C (multiset.prod (multiset.map leading_coeff g)) *
        multiset.prod (multiset.map (λ (y : polynomial α), C (leading_coeff y)⁻¹ * y) g)),
        {
          simp [multiset.map_zero, multiset.map_zero, multiset.zero_add (0 : multiset (polynomial α))]
        },
        {
          intros a s h4 h5,
          have h5a : ∀ (y : polynomial α), y ∈ s → irreducible y,
          {
            intros y h6,
            have : y ∈ a::s,
            {simp *},
            exact h5 y this,
          },
          have h4a : multiset.prod s =
    C (multiset.prod (multiset.map leading_coeff s)) *
      multiset.prod (multiset.map (λ (y : polynomial α), C (leading_coeff y)⁻¹ * y) s),
          from h4 h5a,
          have h6 : irreducible a,
          {
            apply h5 a,
            simp,
          },
          have h7 : leading_coeff a ≠ 0,
          {
            have : a ≠ 0,
            from and.elim_left h6,
            rw [ne.def, leading_coef_eq_zero_iff_eq_zero],
            assumption
          },
          clear h4, 
          simp only [multiset.map_cons, multiset.prod_cons, C_prod_eq_prod_C],
          apply eq.symm,
          calc C (leading_coeff a * multiset.prod (multiset.map leading_coeff s)) *
      (C (leading_coeff a)⁻¹ * a *
         multiset.prod (multiset.map (λ (y : polynomial α), C (leading_coeff y)⁻¹ * y) s)) =
         (C (leading_coeff a) * C (multiset.prod (multiset.map leading_coeff s)) ) *
      (C (leading_coeff a)⁻¹) * a *
         multiset.prod (multiset.map (λ (y : polynomial α), C (leading_coeff y)⁻¹ * y) s) : by simp [C_mul_C, mul_assoc]
         ... = (C (leading_coeff a) * (C (multiset.prod (multiset.map leading_coeff s))  *
      (C (leading_coeff a)⁻¹))) * a *
         multiset.prod (multiset.map (λ (y : polynomial α), C (leading_coeff y)⁻¹ * y) s) : by simp [mul_assoc]
          ... = (C (leading_coeff a) * ( (C (leading_coeff a)⁻¹) *
      C (multiset.prod (multiset.map leading_coeff s)) )) * a *
         multiset.prod (multiset.map (λ (y : polynomial α), C (leading_coeff y)⁻¹ * y) s) : by rw [mul_comm (C (leading_coeff a)⁻¹) _]
        ... = C (leading_coeff a) *  (C (leading_coeff a)⁻¹) *
              (C (multiset.prod (multiset.map leading_coeff s))  * a) *
                multiset.prod (multiset.map (λ (y : polynomial α), C (leading_coeff y)⁻¹ * y) s) : by simp only [mul_assoc]        
        ... = C (leading_coeff a) *  (C (leading_coeff a)⁻¹) *
              (a  * C (multiset.prod (multiset.map leading_coeff s))) *
                multiset.prod (multiset.map (λ (y : polynomial α), C (leading_coeff y)⁻¹ * y) s) : by rw [mul_comm _ a]          
         ... = C (leading_coeff a) *  (C (leading_coeff a)⁻¹) *
              a  * (C (multiset.prod (multiset.map leading_coeff s)) *
                multiset.prod (multiset.map (λ (y : polynomial α), C (leading_coeff y)⁻¹ * y) s)) : by simp only [mul_assoc]         
          ... = C (leading_coeff a) *  (C (leading_coeff a)⁻¹) *
              a  * (multiset.prod s) : by rw ←h4a         
          ... = C ((leading_coeff a) * ((leading_coeff a)⁻¹)) *
              a  * (multiset.prod s) : by simp [C_mul_C, mul_assoc]
          ... = C 1 * a * (multiset.prod s) : by rw [mul_inv_cancel h7]       
         ... = _ : by simp,
        }
      },
      have : multiset.prod f =
      C (multiset.prod (multiset.map leading_coeff f)) *
        multiset.prod (multiset.map (λ (y : polynomial α), C (leading_coeff y)⁻¹ * y) f),
      from h4 f h3b,
      rw [C_prod_eq_prod_C, multiset.map_map] at this,
      exact this,
      },
      intros y h1,
      constructor,
      {
         --Must make lemmas for irreducible
         rw multiset.mem_map at h1,
         let a := some h1,
         have h4 : a ∈ f ∧ C (leading_coeff a)⁻¹ * a = y,
         from some_spec h1,
         have h4a : a ∈ f,
         from and.elim_left h4,
         have h5 : irreducible a,
         from h3b a h4a,
         have h4b : C (leading_coeff a)⁻¹ * a = y,
         from and.elim_right h4,
         have h6 : is_unit (C (leading_coeff a)⁻¹),
         {
           constructor,
           swap,
           have h6: is_unit ((leading_coeff a)⁻¹),
           {
             apply for_all_is_unit_of_not_zero,
             have : a ≠ 0,
             from and.elim_left h5,
             rw [ne.def, ←leading_coef_eq_zero_iff_eq_zero] at this,
             exact inv_ne_zero this,
           },
           have h7: is_unit (C (leading_coeff a)⁻¹),
           from is_unit_of_is_unit h6,
           exact to_unit h7,
           simp,
         },
         have h7 : (y ~ᵤ a),
         {
           rw [←@to_unit_is_unit_val_eq _ _ (C (leading_coeff a)⁻¹) _] at h4b,
           exact ⟨to_unit h6,eq.symm h4b⟩
         },
         have h8 : (a ~ᵤ y),
         from associated.symm h7,
         exact irreducible_of_associated h5 h8        
      },
      {
        rw multiset.mem_map at h1,
        let a := some h1,
        have h4 : a ∈ f ∧ C (leading_coeff a)⁻¹ * a = y,
        from some_spec h1,
        have h4a : C (leading_coeff a)⁻¹ * a = y,
        from and.elim_right h4,
        rw ←h4a,
        apply leading_coeff_inv_mul_monic_of_ne_zero,
        have h4b : a ∈ f,
        from and.elim_left h4,
        exact and.elim_left (h3b a h4b)
      }
    }

  }
end



/-
--The more general setting, avoids problem with the roots of the zero polynomial
axiom monic_irr (p : polynomial β) : polynomial β →₀ ℕ
axiom irr_poly_irreducible (p : polynomial β) : ∀x ∈ (monic_irr p).support, irreducible x
axiom irr_poly_monic (p : polynomial β) : ∀x ∈ (monic_irr p).support, monic x
axiom unique_factorization (p : polynomial β) : ∃ c : β , p = C c * ((finsupp.prod (monic_irr p) (λ k n, k ^n) ) )
def c_fac (p : polynomial β) : β := some ( unique_factorization p)
axiom c_fac_unit (p : polynomial β) :  is_unit (c_fac p)
-/

lemma polynomial_fac_finsupp [field α] (x : polynomial α) : ∃ c :  α, ∃ p :(polynomial α) →₀ ℕ, x = C c * ((finsupp.prod (p) (λ k n, k ^n) ) ) ∧ (∀x∈p.support, irreducible x ∧ monic x)  :=
begin
  have h1 : ∃ c :  α, ∃ p : multiset (polynomial α), x = C c * p.prod ∧ (∀x∈p, irreducible x ∧ monic x),
  from polynomial_fac _,
  rcases h1 with ⟨c, p, h2⟩,
  exact ⟨c, p.to_finsupp, 
    begin
      rw ←multiset.to_finsupp_prod,
      constructor,
      exact h2.1,
      intros y h3,
      rw multiset.to_finsupp_support at h3,
      let h4 := h2.2,
      rw multiset.mem_to_finset at h3,
      exact h4 _ h3,
      end
  ⟩
end

lemma degree_gcd_le_left [unique_factorization_domain α] {a b : polynomial α} (h : a ≠ 0): degree (gcd a b) ≤ degree a :=
begin
  have  h1 : gcd a b ∣ a,
  from gcd_left,
  apply nat.le_trans (degree_dvd h1 h),
  exact nat.le_refl _,
end

end polynomial
