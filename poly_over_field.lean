import  .Sup_fin data.finsupp order.lattice data.nat.cast .euclidean_domain unique_factorization_domain
import .to_finsupp poly .to_multiset poly_over_UFD to_field
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
variables {α : Type u} 

section field


--Naming is incorrect --Belongs in poly over field
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

open associated




def make_monic [field α] (f : polynomial α) := if (f = 0) then 0 else (C (f.leading_coeff)⁻¹ * f)



lemma monic_make_monic_of_ne_zero [field α] (f : polynomial α) (h : f ≠ 0) : monic f.make_monic :=
begin
  simp [make_monic, if_neg, *],
  exact leading_coeff_inv_mul_monic_of_ne_zero h,
end

def monic_out [field α] (a : quot (polynomial α)) : polynomial α :=
quot.lift_on a make_monic (assume f p h,
  begin
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
        rw [ne.def, leading_coef_eq_zero_iff_eq_zero],
        rw [ne.def, mul_eq_zero_iff_eq_zero_or_eq_zero, not_or_distrib] at hp2,
        exact hp2.1,
        rw [ne.def, leading_coef_eq_zero_iff_eq_zero],
        exact hp,
        rw [ne.def, leading_coef_eq_zero_iff_eq_zero],
        rw [ne.def, mul_eq_zero_iff_eq_zero_or_eq_zero, not_or_distrib] at hp2, --Duplication
        simp *,
      }
    }
  end)

lemma monic_monic_out_of_ne_zero [field α] (f : quot (polynomial α)) (h : f ≠ 0) : monic (monic_out f) :=
begin
  revert h,
  apply quot.induction_on f,
  intros a h,
  apply monic_make_monic_of_ne_zero,
  rw [ne.def, ←mk_eq_zero_iff_eq_zero],
  exact h,
end

/-@[simp] theorem quot.out_eq {r : α → α → Prop} (q : quot r) : quot.mk r q.out = q :=
classical.some_spec (quot.exists_rep q)-/


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
      from is_constant_of_is_unit h2,
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
        rw [C_prod_eq_map_C_prod, multiset.map_map],--, ←multiset.prod_add

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
          simp only [multiset.map_cons, multiset.prod_cons, C_prod_eq_map_C_prod],
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
      rw [C_prod_eq_map_C_prod, multiset.map_map] at this,
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
           apply is_unit_of_is_unit,
           apply for_all_is_unit_of_not_zero,
           apply inv_ne_zero,
           rw [ne.def, leading_coef_eq_zero_iff_eq_zero],
           exact h5.1,
         },
         have h7 : (y ~ᵤ a),
         {
           rcases h6 with ⟨u, hu⟩,
           exact ⟨u, by simp * at *⟩,

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


@[simp] lemma monic_out_one : monic_out (1 : quot (polynomial α)) = 1 :=
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

@[simp] lemma monic_out_zero : monic_out (0 : quot (polynomial α)) = 0 :=
begin
  rw [zero_def, ←mk_def, ←associated_zero_iff_eq_zero],
  apply monic_out_mk_associated,
end

open multiset

#check monic_out_mk_associated

lemma monic_out_mul_eq_monic_out_mul_monic_out (a b : quot (polynomial α)): monic_out (a * b) = monic_out a * monic_out b :=
begin
  apply quot.induction_on a,
  apply quot.induction_on b,
  intros a b,
  rw [←mk_def', ←mk_def'] at *,
  rw [←mul_mk],
  by_cases ha : a = 0,
  {
    simp * at *,
  },
  {
    by_cases hb : b = 0,
    {
      simp * at *,
    },
    {
      have hab : a * b ≠ 0,
        from mul_ne_zero ha hb,
      rw ←associated_iff_eq_of_monic_of_monic,
      have h1 : ((b * a) ~ᵤ (monic_out (mk (b * a)))),
        from (monic_out_mk_associated (b * a)).symm,
      have h2 : ((b * a) ~ᵤ (monic_out (mk b) * monic_out (mk a))),
      {
        apply mul_associated_mul_of_associated_of_associated,
        exact (monic_out_mk_associated b).symm,
        exact (monic_out_mk_associated a).symm,
      },
      exact associated.trans h1.symm h2,
      {
        rw mul_comm at hab,
        apply monic_monic_out_of_ne_zero,
        simp [mk_eq_zero_iff_eq_zero, *],
      },
      rw ←mk_eq_zero_iff_eq_zero at *,
      apply monic_mul_of_monic_of_monic,
      exact monic_monic_out_of_ne_zero _ hb,
      exact monic_monic_out_of_ne_zero _ ha,
    }
  }
end


lemma prod_map_monic_out_eq_monic_out_prod (s : multiset (quot (polynomial α))) : (map monic_out s).prod = monic_out s.prod :=
begin
  apply multiset.induction_on s,
  {
    simp [monic_out_one],
  },
  {
    intros a s h,
    simp * at *,
    simp only [monic_out_mul_eq_monic_out_mul_monic_out],
  }
end

lemma irreducible_monic_out_of_irred {a : quot (polynomial α)} (h : irred a) : irreducible (monic_out a) :=
begin
  revert h,
  apply quot.induction_on a,
  intros a h,
  have h1 : (monic_out (mk a) ~ᵤ a),
    from monic_out_mk_associated _,
  have h2 : irreducible a,
    from h,
  exact irreducible_of_associated h2 h1.symm,
end


lemma eq_of_rel_multiset_associated_of_forall_mem_monic_of_forall_mem_monic 
  (s t : multiset (polynomial α)) (h : rel_multiset associated s t) 
  (hs : ∀ x ∈ s, monic x) (ht : ∀ x ∈ t, monic x) : s = t :=
begin
  induction h,
  case rel_multiset.nil { refl },
  case rel_multiset.cons : a b xs ys hr hst ih h2 h3 {
    have h1 : a = b,
    {
      rw ←associated_iff_eq_of_monic_of_monic,
      exact hr,
      {
        apply h2,
        rw mem_cons,
        simp *,
      },
      {
        apply h3,
        rw mem_cons,
        simp *,
      }
    },
    subst h1,
    have h2 : xs = ys,
    {
      apply ih,
      {
        intros x h,
        apply h2,
        rw mem_cons,
        simp *,
      },
      {
        intros y h,
        apply h3,
        rw mem_cons,
        simp *,
      }
    },
    subst h2,
  }
end

--the normal form of a polynomial f = u p_1 p_2 ... p_n, with u a unit, and p_i monic and irreducible

def c_fac (p : polynomial α) : α := 
if (p = 0) then 0 else some (polynomial_fac p)

def factors (p : polynomial α) : multiset (polynomial α) :=
if (p = 0) then 0 else classical.some (some_spec $ polynomial_fac p)

lemma factors_irred (p : polynomial α) : ∀x ∈ (p.factors), irreducible x := --The x argument should be implicit
begin
  intros x h,
  rw [polynomial.factors] at h,
  by_cases h1: p = 0,
  {
    simp * at *,
  },
  {
    simp * at *,
    exact ((some_spec $ some_spec $ polynomial_fac p).2 x h).1,
  }
end

lemma factors_monic (p : polynomial α) : ∀x ∈ (p.factors), monic x :=
begin
  intros x h,
  rw [polynomial.factors] at h,
  by_cases h1: p = 0,
  {
    simp * at *,
  },
  {
    simp * at *,
    exact ((some_spec $ some_spec $ polynomial_fac p).2 x h).2,
  }
end

lemma factors_eq (p : polynomial α) : p = C (p.c_fac) * p.factors.prod :=
begin
  by_cases h1: p = 0,
  {
    simp [polynomial.c_fac,*] at *,
  },
  {
    simp [polynomial.c_fac, polynomial.factors, *] at *,
    exact (some_spec (some_spec ( polynomial_fac p))).1,
  }
end

@[simp] lemma c_fac_zero : (0 : polynomial α).c_fac = 0 :=
begin
  simp [polynomial.c_fac],
end

@[simp] lemma factors_zero : (0 : polynomial α).factors = 0 :=
begin
  simp [polynomial.factors],
end


lemma c_fac_ne_zero_of_ne_zero (f : polynomial α) (h : f ≠ 0) : f.c_fac ≠ 0 :=
begin
  by_contradiction h1,
  simp at h1,
  rw f.factors_eq at h,
  simp * at *,
end

 
end field

end polynomial



