#exit -- currently not used

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


section field
variable [field α]

--should be only local?
--local attribute [instance, priority 1100] field.to_integral_domain --correct?
--@[priority 1100] instance : integral_domain (α) := field.to_integral_domain --should have lowest priority,
--because we only want to use this for the lemmma mul_ne_of_ne

--set_option pp.implicit true
set_option pp.numerals false
--set_option trace.class_instances true

attribute [priority 2000] field.zero_ne_one

--Some parts use that field is a division ring, and some parts use that it it an integral domain.
--This causes a diamond problem, 
lemma division_with_remainder_polynomials {f g : polynomial α} : g ≠ 0 → (∃ q r : polynomial α,( (f = q * g + r) ∧ ((r = 0)  ∨  ( (degree r ) < (degree g)) )  ) ) :=
begin
  intro h1,
  apply induction_on_degree f,
  
  intro qq,
  apply nat.strong_induction_on qq,
  intros n ih h h3,
  let m : ℕ := degree g,
  by_cases h4 : (h = 0),
  {
    rw h4,
    fapply exists.intro,
    apply (0 : polynomial α),
    fapply exists.intro,
    apply (0 : polynomial α),
    simp
  },
  {
    by_cases h5 : (n < m),
      {
        fapply exists.intro,
        apply (0: polynomial α),
        fapply exists.intro,
        apply (h),
        simp *,
      },
      {
        -------
         let a' := h - (C ((leading_coeff h) * (leading_coeff g)⁻¹)) * X ^ (n - m) * g, -- here we need that α is a division ring
         let a'' := (C ((leading_coeff h) * (leading_coeff g)⁻¹)) * (X : polynomial α) ^ (n - m) * g,
         have h3a : h * g ≠ 0,
         rw ←ne.def at h4,
         exact @mul_ne_zero (polynomial α) _ _ _ h4 h1, --can it find the right mul_ne_zero??

         have h3b : (X ^ (n - m) : polynomial α) ≠ 0,
         from X_pow_ne_zero,


         have h3c : C ((leading_coeff h) * (leading_coeff g)⁻¹) ≠ 0,
           have h3a2: (leading_coeff h) ≠ 0,
           simp [h4, leading_coef_eq_zero_iff_eq_zero],
           have h3a3: (leading_coeff g) ≠ 0,
           simp [h1, leading_coef_eq_zero_iff_eq_zero],             
           have h3a4: (leading_coeff g)⁻¹ ≠ 0,
           simp [h3a3, inv_ne_zero],
           simp,
           rw [←embedding, ←not_iff_not_of_iff eq_zero_iff_embed_eq_zero],
           exact mul_ne_zero h3a2 h3a4,

         have h3d : (C ((leading_coeff h) * (leading_coeff g)⁻¹)) * (X ^ (n - m) : polynomial α) ≠ 0,
         exact mul_ne_zero h3c h3b, -- here we need α is an integral domain
         have h3e : (C ((leading_coeff h) * (leading_coeff g)⁻¹)) * (X ^ (n - m) : polynomial α) * g ≠ 0,
         exact mul_ne_zero h3d h1,
         have h3f : degree ((C ((leading_coeff h) * (leading_coeff g)⁻¹)) * X ^ (n - m)) =
                degree  (C ((leading_coeff h) * (leading_coeff g)⁻¹)) + degree ( X ^ (n - m) ),    
         from  degree_mul_integral_domain h3d,
         have h6 : degree a'' = n,
         calc degree a'' = degree ( (C ((leading_coeff h) * (leading_coeff g)⁻¹)) * (X : polynomial α) ^ (n - m) * g ): rfl
            ... = degree ((C ((leading_coeff h) * (leading_coeff g)⁻¹)) * X ^ (n - m)) + degree g : degree_mul_integral_domain h3e
            ... = ( degree (C ((leading_coeff h) * (leading_coeff g)⁻¹)) + degree ( X ^ (n - m) )) + degree g 
            : by rw (degree_mul_integral_domain h3d)
            --... = (n - m) + m : by simp *
            --... = 0 + degree ( X ^ (n - m) ) + degree g : by rw [degree_C] --degree X_pow goes wrong
           -- ... = degree ( X ^ (n - m) ) + degree g  : by simp only [zero_add]
            --... = degree ( X ^ (n - m) ) + m : by simp only [m]
           -- ... = (n - m) + m : by simp only [degree_X_pow (field.zero_ne_one α)] --Couldn't find the right zero_ne_one
            ... = (n - m) + m : by simp only [degree_C, zero_add, m, degree_X_pow (field.zero_ne_one α)]
            --... = (n - m) + m : by simp only [degree_X_pow _]
            
            --... = 0 + @degree ( X ^ (n - m) ) + degree g : by simp * --itthinksthese m's are different? Is it becuase the namespace is cluthered?
            --seems to problem with type classes: one uses integral_to_domain, and the other division ring to domain.
            --problem: field can be reduced to division ring and integraldomain,and they can be moved down to,
            --domain, but it doesn't see that these are the same. Diamond problem? 
            --... = ( degree (C ((leading_coeff h) * (leading_coeff g)⁻¹)) + (n - m)) + degree g
            --: by rw @degree_X_pow α _ (_root_.zero_ne_one : (0 : α) ≠ 1)
            --... = degree (C ((leading_coeff h) * (leading_coeff g)⁻¹)) + (n - m) + m : by rw [(rfl : m = degree g)]
            --... = 0 + (n - m) + m : by rw [degree_C]
            --... = (n - m) + m : by rw [@zero_add α _]
            ... = m + (n - m) : @add_comm ℕ _ _ _
            ... = n : nat.add_sub_of_le (le_of_not_gt h5),
         have h7 : leading_coeff a'' = leading_coeff h,
           {
             calc leading_coeff a'' = a'' (degree a'') : rfl
             ... = a'' n : by rw h6
             ... = ( C (leading_coeff h * (leading_coeff g)⁻¹) * (X ^ (n - m) * g)) n : by rw mul_assoc
             ... =  (leading_coeff h * (leading_coeff g)⁻¹) * ( (X ^ (n - m) * g) n) : finsupp.smul_apply --should be a polynomial lemma

             /-
             unfold leading_coeff,
             rw h6,
             rw [(rfl : a'' = C (leading_coeff h * (leading_coeff g)⁻¹) * X ^ (n - m) * g)],
             rw mul_assoc, --? what did it simplify?-/
             
           },
         
         have h8 : degree a' < n,
           have h8 : a' n = 0,
             rw [sub_apply],

             --simp *, --should simplify?
       /-  by_contradiction h8, --not needed
           have h9 : degree a' ≤ n,
           calc degree a' ≤ max (degree h) (degree a'') : degree_sub
           ... = n : by simp [h3, h6],
           --... = n : by simp,
           have h10 : n ≤ degree a',
           from le_of_not_lt h8,
           have h11 : degree a' = n,
           exact le_antisymm h9 h10,
           have h12 : leading_coeff a' = 0,
             dunfold leading_coeff,
             rw h11,            
             rw [(rfl : a' = h - C (leading_coeff h * (leading_coeff g)⁻¹) * X ^ (n - m) * g)],
             rw sub_apply, --Why didn't simp work?
             rw ←h3
    -/


         
        -------
      }
  }
  
end

--We will start with an induction on the degree of f next time!
--They have to do a bit of a hasle to first handle the case of f = 0, because for that they did not define the degree.
lemma division_with_remainder_polynomials {f g : polynomial α} : g ≠ 0 → (∃ q r : polynomial α,( (f = q * g + r) ∧ ((r = 0)  ∨  ( (degree r ) < (degree g)) )  ) ) :=
begin
  by_cases h1 : (f = 0),
  {
    intro h2,
    rw h1,
    fapply exists.intro,
    apply (0 : polynomial α),
    fapply exists.intro,
    apply (0 : polynomial α),
    simp
  },
  {
    intro h2,
    apply induction_on_degree f,
    intro qq, -- needed for the richt format of strong_induction_on
    apply nat.strong_induction_on qq,
    intros k ih,
    intros h h_deg,
    let m : ℕ := degree g,
    let n : ℕ := degree f,
    by_cases h3 : (n < m),
      {
        fapply exists.intro,
        apply (0: polynomial α),
        fapply exists.intro,
        apply (h),
        simp *,
      },
      {                
      --have defined the embedding of R in R[x]? --Did all below had to be h?
      --But if all is h, than I can't prove that h*g ≠ 0?
      --But if I don't use h, than what is the point of h?
      --I did remove it in induction_on_degree_2,
      --but there it seemed that I could never apply the inductive hypotheses?
      -- I thing h is a dummy polynomial which is only needed to get the degree from?
      -- And it seems that h is used in the base case
        let a' := f - (C ((leading_coeff f) * (leading_coeff g)⁻¹)) * X ^ (n - m) * g,
        let a'' := (C ((leading_coeff f) * (leading_coeff g)⁻¹)) * (X : polynomial α) ^ (n - m) * g,
        have h3a : f * g ≠ 0, 
        from mul_ne_zero h1 h2,

        have h3b : (X ^ (n - m) : polynomial α) ≠ 0,
          rw X_pow_eq_single,
          by_contradiction h3b2,
          rw not_not at h3b2,
          have : n - m = n - m,
          trivial,
          have h3b3: (single (n - m) 1 : polynomial α) (n - m) = 1,
          calc (single (n - m) 1 : polynomial α) (n - m) = if ((n - m) = (n - m)) then 1 else 0 : single_apply
            ... = 1 : by rw [if_pos this],
          have h3b4: (single (n - m) 1 : polynomial α) (n - m) = 0,
          rw h3b2,
          exact @zero_apply _ _ (n - m),
          rw h3b4 at h3b3,
          have : (0 : α) ≠ 1,
          exact _root_.zero_ne_one,
          exact this h3b3,

        have h3c : C ((leading_coeff f) * (leading_coeff g)⁻¹) ≠ 0,
          have h3a2: (leading_coeff f) ≠ 0,
          simp [h1, leading_coef_eq_zero_iff_eq_zero],
          have h3a3: (leading_coeff g) ≠ 0,
            simp [h1, leading_coef_eq_zero_iff_eq_zero],
            assumption,
          have h3a4: (leading_coeff g)⁻¹ ≠ 0,
          simp [h3a3, inv_ne_zero],
          simp,
          rw [←embedding, ←not_iff_not_of_iff eq_zero_iff_embed_eq_zero],
          exact mul_ne_zero h3a2 h3a4,

        have h3d : (C ((leading_coeff f) * (leading_coeff g)⁻¹)) * (X ^ (n - m) : polynomial α) ≠ 0,
        exact mul_ne_zero h3c h3b,
        have h3e : (C ((leading_coeff f) * (leading_coeff g)⁻¹)) * (X ^ (n - m) : polynomial α) * g ≠ 0,
        exact mul_ne_zero h3d h2,
        have h3f : degree ((C ((leading_coeff f) * (leading_coeff g)⁻¹)) * X ^ (n - m)) =
              degree  (C ((leading_coeff f) * (leading_coeff g)⁻¹)) + degree ( X ^ (n - m) ),    
        from  degree_mul_integral_domain h3d,
        have h4 : degree a'' = n,
        calc degree a'' = degree ( (C ((leading_coeff f) * (leading_coeff g)⁻¹)) * (X : polynomial α) ^ (n - m) * g ): rfl
          ... = degree ((C ((leading_coeff f) * (leading_coeff g)⁻¹)) * X ^ (n - m)) + degree g : degree_mul_integral_domain h3e
          ... = ( degree (C ((leading_coeff f) * (leading_coeff g)⁻¹)) + degree ( X ^ (n - m) )) + degree g 
          : by rw (degree_mul_integral_domain h3d)
          ... = (0 : ℕ) + degree ( X ^ (n - m) ) + degree g : by rw [degree_C]
          ... = 0 + degree ( (X : polynomial α) ^ (n - m) ) + m : by rw (rfl : degree g = m)     
          ... = 0 + (n - m) + m : by rw [degree_X_pow (zero_ne_one_class.zero_ne_one α)]
          ... = (n - m) + m : nat.zero_add ((n - m) + m)
          ... = m + (n - m) : add_comm _ _
          ... = n : nat.add_sub_of_le (le_of_not_gt h3),
        have h4 : degree a' < n,
        ---calc degree a' ≤ max f ((((leading_coeff f) * (leading_coeff g)⁻¹) :  α) * X ^ (n - m) * g)
        
      }
    

  }

end







--naming!?
lemma division_with_remainder_polynomials {f g : polynomial α} : g ≠ 0 → (∃ q r : polynomial α,( (f = q * g + r) ∧ ((r = 0)  ∨  ( (degree r ) < (degree g)) )  ) ) :=
begin
  by_cases h1 : (f = 0),
  {
    intro h2,
    rw h1,
    fapply exists.intro,
    apply (0 : polynomial α),
    fapply exists.intro,
    apply (0 : polynomial α),
    simp
  },
  {
    intro h2,
    let n := degree f,
    apply induction_on_degree_2 f,
    intro k,
    apply nat.strong_induction_on k, -- doesn't work, we need strong induction.
    {
      
      let m := degree g,
      by_cases h3 : (n < m),
      {
        fapply exists.intro,
        apply (0: polynomial α),
        fapply exists.intro,
        apply (f),
        simp *
      },
      { 
         
        --have defined the embedding of R in R[x]?
         let a' := f - (C ((leading_coeff f) * (leading_coeff g)⁻¹)) * X ^ (n - m) * g,
         let a'' := (C ((leading_coeff f) * (leading_coeff g)⁻¹)) * (X : polynomial α) ^ (n - m) * g,
         have h3a : f * g ≠ 0, 
         from mul_ne_zero h1 h2,

         have h3b : (X ^ (n - m) : polynomial α) ≠ 0,
           rw X_pow_eq_single,
           by_contradiction h3b2,
           rw not_not at h3b2,
           have : n - m = n - m,
           trivial,
           have h3b3: (single (n - m) 1 : polynomial α) (n - m) = 1,
           calc (single (n - m) 1 : polynomial α) (n - m) = if ((n - m) = (n - m)) then 1 else 0 : single_apply
              ... = 1 : by rw [if_pos this],
           have h3b4: (single (n - m) 1 : polynomial α) (n - m) = 0,
           rw h3b2,
           exact @zero_apply _ _ (n - m),
           rw h3b4 at h3b3,
           have : (0 : α) ≠ 1,
           exact _root_.zero_ne_one,
           exact this h3b3,

         have h3c : C ((leading_coeff f) * (leading_coeff g)⁻¹) ≠ 0,
           have h3a2: (leading_coeff f) ≠ 0,
           simp [h1, leading_coef_eq_zero_iff_eq_zero],
           have h3a3: (leading_coeff g) ≠ 0,
             simp [h1, leading_coef_eq_zero_iff_eq_zero],
             assumption,
           have h3a4: (leading_coeff g)⁻¹ ≠ 0,
           simp [h3a3, inv_ne_zero],
           simp,
           rw [←embedding, ←not_iff_not_of_iff eq_zero_iff_embed_eq_zero],
           exact mul_ne_zero h3a2 h3a4,

         have h3d : (C ((leading_coeff f) * (leading_coeff g)⁻¹)) * (X ^ (n - m) : polynomial α) ≠ 0,
         exact mul_ne_zero h3c h3b,
         have h3e : (C ((leading_coeff f) * (leading_coeff g)⁻¹)) * (X ^ (n - m) : polynomial α) * g ≠ 0,
         exact mul_ne_zero h3d h2,
         have h3f : degree ((C ((leading_coeff f) * (leading_coeff g)⁻¹)) * X ^ (n - m)) =
                degree  (C ((leading_coeff f) * (leading_coeff g)⁻¹)) + degree ( X ^ (n - m) ),    
         from  degree_mul_integral_domain h3d,
         have h4 : degree a'' = n,
         calc degree a'' = degree ( (C ((leading_coeff f) * (leading_coeff g)⁻¹)) * (X : polynomial α) ^ (n - m) * g ): rfl
            ... = degree ((C ((leading_coeff f) * (leading_coeff g)⁻¹)) * X ^ (n - m)) + degree g : degree_mul_integral_domain h3e
            ... = ( degree (C ((leading_coeff f) * (leading_coeff g)⁻¹)) + degree ( X ^ (n - m) )) + degree g 
            : by rw (degree_mul_integral_domain h3d)
            
            ... = (n - m) + m : by simp *
            ... = m + (n - m) : add_comm _ _
            ... = n : nat.add_sub_of_le (le_of_not_gt h3),
         have h4 : degree a' < n,
         ---calc degree a' ≤ max f ((((leading_coeff f) * (leading_coeff g)⁻¹) :  α) * X ^ (n - m) * g)
         
      }
    }
  }
end

--Still need to obtain an integral domain from field α 
instance {α : Type u} [field α] : euclidean_domain (polynomial α) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero,
  zero_ne_one := zero_ne_one, --correct?
  norm := degree,
  h1 := degree_zero,
  h_norm := sorry,
  .. polynomial.comm_ring }


end field


end polynomial