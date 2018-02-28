-- the to be Mason-Stother formalization
-- Authors Johannes & Jens

--Defining the gcd
import poly
--import euclidean_domain
import unique_factorization_domain
import data.finsupp
import algebraically_closed_field
import poly_over_UFD


noncomputable theory
local infix ^ := monoid.pow
local notation `d[`a`]` := polynomial.derivative a
local notation Σ := finset.sume
local notation Π := finset.prod
local notation `Π₀` := finsupp.prod
local notation `~`a:=polynomial a

open polynomial
open classical
local attribute [instance] prop_decidable


-- TODO: there is some problem with the module instances for module.to_add_comm_group ...
-- force ring.to_add_comm_group to be stronger
attribute [instance] ring.to_add_comm_group

universe u

attribute [instance] field.to_unique_factorization_domain --correct?


variable {β : Type u}
variables [field β]


def polynomial.c_fac (p : polynomial β) : β := some (polynomial_fac p)

def polynomial.factors (p : polynomial β) : multiset (~β) :=
classical.some (some_spec $ polynomial_fac p)

lemma polynomial.factors_irred (p : polynomial β) : ∀x ∈ (p.factors), irreducible x :=
assume x h, ((some_spec $ some_spec $ polynomial_fac p).2 x h).1

lemma polynomial.factors_monic (p : polynomial β) : ∀x ∈ (p.factors), monic x :=
λx h, ((some_spec $ some_spec $ polynomial_fac p).2 x h).2

lemma polynomial.factors_eq (p : polynomial β) : p = C (p.c_fac) * p.factors.prod :=
(some_spec (some_spec ( polynomial_fac p))).1


open classical multiset
section mason_stothers

--It might be good to remove the attribute to domain of integral domain?
def rad (p : polynomial β) : polynomial β :=
p.factors.erase_dup.prod

lemma c_fac_ne_zero_of_ne_zero (f : polynomial β) (h : f ≠ 0) : f.c_fac ≠ 0 :=
begin
  by_contradiction h1,
  simp at h1,
  rw f.factors_eq at h,
  simp * at *,
end

lemma rad_ne_zero {p : polynomial β} : rad p ≠ 0 :=
begin
  rw [rad],
  apply multiset.prod_ne_zero_of_forall_mem_ne_zero,
  intros x h1,
  have h2 : irreducible x,
  {
    rw mem_erase_dup at h1,
    exact p.factors_irred x h1,
  },
  exact h2.1,
end

--naming --Where do we use this?
lemma degree_rad_eq_sum_support_degree {f : polynomial β} :
  degree (rad f) = sum (map degree f.factors.erase_dup) :=
begin 
  rw rad,
  have h1 : finset.prod (to_finset (polynomial.factors f)) id ≠ 0,
    {
      apply polynomial.prod_ne_zero_of_forall_mem_ne_zero,
      intros x h1,
      have : irreducible x,
        {
          rw mem_to_finset at h1,
          exact f.factors_irred x h1,
        },
      exact and.elim_left this,
    },
  rw ←to_finset_val f.factors,
  exact calc degree (prod ((to_finset (polynomial.factors f)).val)) = 
    degree (prod (map id (to_finset (polynomial.factors f)).val)) : by rw map_id_eq
    ... = sum (map degree ((to_finset (polynomial.factors f)).val)) : degree_prod_eq_sum_degree_of_prod_ne_zero h1,
end

private lemma mem_factors_of_mem_factors_sub_factors_erase_dup (f : polynomial β) (x : polynomial β) (h : x ∈ (f.factors)-(f.factors.erase_dup)) :   x ∈ f.factors :=
begin
  have : ((f.factors)-(f.factors.erase_dup)) ≤ f.factors,
    from multiset.sub_le_self _ _,
  exact mem_of_le this h,
end

--naming
lemma prod_pow_min_on_ne_zero {f : polynomial β} :
  ((f.factors)-(f.factors.erase_dup)).prod ≠ 0 :=
begin
  apply multiset.prod_ne_zero_of_forall_mem_ne_zero,
  intros x h,
  have h1 : x ∈ f.factors,
    from mem_factors_of_mem_factors_sub_factors_erase_dup f x h,
  have : irreducible x,
    from f.factors_irred x h1,
  exact this.1,
end


lemma degree_factors_prod_eq_degree_factors_sub_erase_dup_add_degree_rad {f : polynomial β} : 
  degree (f.factors.prod) = degree ((f.factors)-(f.factors.erase_dup)).prod + degree (rad f) :=
begin
  rw [← sub_erase_dup_add_erase_dup_eq f.factors] {occs := occurrences.pos [1]},
  rw [←prod_mul_prod_eq_add_prod],
  apply degree_mul_eq_add_of_mul_ne_zero,
  exact mul_ne_zero prod_pow_min_on_ne_zero rad_ne_zero,
end

open polynomial

private lemma Mason_Stothers_lemma_aux_1 (f : polynomial β): 
  ∀x ∈ f.factors, x^(count x f.factors - 1) ∣ d[f.factors.prod] :=
begin
  rw [derivative_prod_multiset],
  intros x h,
  apply multiset.dvd_sum,
  intros y hy,
  rw multiset.mem_map at hy,
  rcases hy with ⟨z, hz⟩,
  have : y = d[z] * prod (erase (factors f) z),
    from hz.2.symm,
  subst this,
  apply dvd_mul_of_dvd_right,
  rcases (exists_cons_of_mem hz.1) with ⟨t, ht⟩,
  rw ht,
  by_cases h1 : x = z,
  {
    subst h1,
    simp,
    apply forall_pow_count_dvd_prod,
  },
  {
    simp [count_cons_of_ne h1],
    refine dvd_trans _ (forall_pow_count_dvd_prod t x),
    apply pow_count_sub_one_dvd_pow_count,
  },
end

private lemma count_factors_sub_one (f x : polynomial β) :  (count x f.factors - 1) = count x (factors f - erase_dup (factors f))  :=
begin
  rw count_sub,
  by_cases h1 : x ∈ f.factors,
  {
    have : count x (erase_dup (factors f)) = 1,
    {
      have h2: 0 < count x (erase_dup (factors f)),
      {
        rw [count_pos, mem_erase_dup],
        exact h1
      },
      have h3: count x (erase_dup (factors f)) ≤ 1,
      {
        have : nodup (erase_dup (factors f)),
          from nodup_erase_dup _,
        rw nodup_iff_count_le_one at this,
        exact this x,
      },
      have : 1 ≤ count x (erase_dup (factors f)),
        from h2,
      exact nat.le_antisymm h3 this,
    },
    rw this,
  },
  {
    rw ←count_eq_zero at h1,
    simp *,
  }
end

private lemma Mason_Stothers_lemma_aux_2 (f : polynomial β) (h_dvd : ∀x ∈ f.factors, x^(count x f.factors - 1) ∣ gcd f d[f]): 
  (f.factors - f.factors.erase_dup).prod ∣ gcd f d[f] :=
begin
  apply facs_to_pow_prod_dvd_multiset,
  intros x h,
  have h1 : x ∈ f.factors,
    from mem_factors_of_mem_factors_sub_factors_erase_dup f x h,  
  split,
  {
    exact f.factors_irred x h1,
  },
  split,
  {
    rw ←count_factors_sub_one,
    exact h_dvd x h1,
  },
  {
    intros y hy h2,
    have : y ∈ f.factors,
      from mem_factors_of_mem_factors_sub_factors_erase_dup f y hy,
    have h3: monic x,
      from f.factors_monic x h1,
    have h4: monic y,
      from f.factors_monic y this,   
    rw associated_iff_eq h3 h4, --naming not correct
    exact h2,
  }
end

private lemma degree_factors_prod (f : polynomial β) (h : f ≠ 0): degree (f.factors.prod) = degree f :=
begin
  rw [f.factors_eq] {occs := occurrences.pos [2]},
  rw [degree_mul_eq_add_of_mul_ne_zero, degree_C],
  simp,
  rw ←f.factors_eq,
  exact h,
end


lemma Mason_Stothers_lemma (f : polynomial β) :
  degree f ≤ degree (gcd f (derivative f )) + degree (rad f) := --I made degree radical from this one
begin
  by_cases hf : (f = 0),
  {
    simp [hf, nat.zero_le],
  },
  {
    have h_dvd_der : ∀x ∈ f.factors, x^(count x f.factors - 1) ∣ d[f],
    {
      rw [f.factors_eq] {occs := occurrences.pos [3]},
      rw [derivative_C_mul],
      intros x h,
      apply dvd_mul_of_dvd_right,
      exact Mason_Stothers_lemma_aux_1 f x h,
    },
    have h_dvd_f : ∀x ∈ f.factors, x^(count x f.factors - 1) ∣ f,
    {
      rw [f.factors_eq] {occs := occurrences.pos [3]},
      intros x hx, --We have intros x hx a lot here, duplicate?
      apply dvd_mul_of_dvd_right,
      refine dvd_trans _ (forall_pow_count_dvd_prod _ x), --Duplicate 2 lines with Mason_Stothers_lemma_aux_1
      apply pow_count_sub_one_dvd_pow_count,
    },
    have h_dvd_gcd_f_der : ∀x ∈ f.factors, x^(count x f.factors - 1) ∣ gcd f d[f],
    {
      intros x hx,
      exact gcd_min (h_dvd_f x hx) (h_dvd_der x hx),
    },
    have h_prod_dvd_gcd_f_der : (f.factors - f.factors.erase_dup).prod ∣ gcd f d[f],
      from Mason_Stothers_lemma_aux_2 _ h_dvd_gcd_f_der,
    have h_gcd : gcd f d[f] ≠ 0,
    {
      rw [ne.def, gcd_eq_zero_iff_eq_zero_and_eq_zero],
      simp [hf]
    },
    have h1 : degree ((f.factors - f.factors.erase_dup).prod) ≤ degree (gcd f d[f]),
      from degree_dvd h_prod_dvd_gcd_f_der h_gcd,
    have h2 : degree f = degree ((f.factors)-(f.factors.erase_dup)).prod + degree (rad f),
    {
      rw ←degree_factors_prod,
      exact degree_factors_prod_eq_degree_factors_sub_erase_dup_add_degree_rad,
      exact hf,
    },
    rw h2,
    apply add_le_add_right,
    exact h1,
  }  
end

/-

lemma Mason_Stothers_lemma (f : polynomial β) :
  degree f ≤ degree (gcd f (derivative f )) + degree (rad f) := --I made degree radical from this one
begin
  by_cases hf : (f = 0),
  {
    rw [hf],
    simp,
    exact nat.zero_le _,
  },
  have h_tmp : ((finsupp.prod (factors f) (λ k n, k ^n) ) ) = (factors f).support.prod (λa, (λ k n, k ^n) a ((factors f) a)),
  simp [finsupp.prod],
  have h_der : derivative ((factors f).support.prod (λa, (λ k n, k ^n) a ((factors f) a))) 
  = (factors f).support.sum (λb, derivative ((λa, (λ k n, k ^n) a ((factors f) a)) b) * (finset.erase (factors f).support b).prod (λa, (λ k n, k ^n) a ((factors f) a))),
  simp [derivative_prod],

  have h_der2 : ∀x ∈ (support (factors f)), (x^((factors f) x -1))∣(derivative ((factors f).support.prod (λa, (λ k n, k ^n) a ((factors f) a))) ),--
  {   
    intros, 
    rw h_der,
    refine dvd_sum _,
    intros y hy,
    by_cases (x = y),
    {
      have : x ^ ((factors f) x - 1) ∣
    d[(λ (a : ~β), (λ (k : ~β) (n : ℕ), k ^ n) a ((factors f) a)) y],
      rw derivative_pow,
      have : (factors f) y ≠  0,
      simp [iff.elim_left (mem_support_iff _) hy],
      simp only [if_neg this],
      refine dvd.intro (↑((factors f) y) * d[y]) _,
      rw [h],
      exact calc
      y ^ ((factors f) y - 1) * (↑((factors f) y) * d[y]) =
      y ^ ((factors f) y - 1) * ↑((factors f) y) * d[y] : by rw mul_assoc
      ... = ↑((factors f) y) * y ^ ((factors f) y - 1) * d[y] : by rw [(mul_comm (y ^ ((factors f) y - 1)) ( ↑((factors f) y)))],
      exact dvd_mul_of_dvd_left this _
    },
    {
      have : x ^ ((factors f) x - 1) ∣ (finset.prod (finset.erase (support (factors f)) y) (λ (a : ~β), a ^ (factors f) a)),
      have : x ∈ (finset.erase (support (factors f)) y),
      exact finset.mem_erase_of_ne_of_mem h H,
      apply dvd_prod_of_dvd_mem,
      exact this,
      exact dvd_pow_sub_one_pow,
      refine dvd_mul_of_dvd_right this _
    }
  },

  have h_fac : f = C (c_fac f) * ((finsupp.prod (factors f) (λ k n, k ^n) ) ), 
    from (h_factors f).1,
  have h_dvd_der : ∀x ∈ (support (factors f)), (x^((factors f) x -1))∣ (derivative f),
  {
    intros y hy,
    rw (congr_arg derivative h_fac),
    rw h_tmp,
    rw derivative_C_mul,
    apply dvd_mul_of_dvd_right (h_der2 y hy)
  },
  have h_dvd_f : ∀x ∈ (support (factors f)), (x^((factors f) x -1))∣ f,
  {
    intros y hy,
    conv in (f) {rw h_fac}, --Nice using the conv could be very handy.
    rw h_tmp,
    refine dvd_mul_of_dvd_right _ (C (c_fac f)),
    apply dvd_prod_of_dvd_mem,
    apply hy,
    apply dvd_pow_sub_one_pow
  },
  have h_dvd_gcd_f_der : ∀x ∈ (support (factors f)), (x^((factors f) x -1))∣ (gcd f (derivative f)),
  {
    intros y hy,
    apply gcd_min,
    apply h_dvd_f y,
    apply hy,
    apply h_dvd_der y,
    apply hy
  }, --For the next lemma some notions of UFD need to be made.
  have h_prod_dvd_gcd_f_der :(to_finsupp_pow_min_one (factors f)).prod (λ x y, x ^ y) ∣ gcd f d[f],
  {  
    apply facs_to_pow_prod_dvd,
    rw [to_finsupp_pow_min_one],
    dunfold to_finsupp_pow_min_one._proof_1,
    intros x h1,
    have h2 : x ∈ support (factors f),
    {
      have :(support (map_range (λ (n : ℕ), n - has_one.one ℕ) _ (factors f))) ⊆ ( support (factors f)),
      from support_pow_min_one_subset_support,
      exact finset.mem_of_subset this h1
    },
    have h3 : irreducible x,
    from factors_irred f x h2,
    have h4 : x ^ ((map_range (λ (n : ℕ), n - has_one.one ℕ) _ (factors f)) x) ∣ gcd f d[f],
    {
        rw map_range_apply,
        exact h_dvd_gcd_f_der x h2
    },
    have h5 : ∀ (y : ~β),
        y ∈ support (map_range (λ (n : ℕ), n - has_one.one ℕ) _ (factors f)) → x ≠ y → ¬associated x y,
        {
          intros y h5,
          have h6 : y ∈ support (factors f),
          {--duplicate code here
            have :(support (map_range (λ (n : ℕ), n - has_one.one ℕ) _ (factors f))) ⊆ ( support (factors f)),
            from support_pow_min_one_subset_support,
            exact finset.mem_of_subset this h5
          },
          have h7 : monic x,
          from  factors_monic f x h2,
          have h8 : monic y,
          from factors_monic f y h6,
          intro h9,
          rw associated_iff_eq h7 h8,
          exact h9,
        },
        exact ⟨h3 ,h4 ,h5 ⟩,
  },
  {
    have h_gcd : gcd f d[f] ≠ 0,
    {
      rw [ne.def, gcd_eq_zero_iff_eq_zero_and_eq_zero],
      simp [hf]
    },
    have h1 : degree (finsupp.prod (to_finsupp_pow_min_one (factors f)) (λ (x : ~β) (y : ℕ), x ^ y)) ≤ degree (gcd f d[f]),
    from degree_dvd h_prod_dvd_gcd_f_der h_gcd,
    have h2 : degree f = degree (finsupp.prod (to_finsupp_pow_min_one (factors f)) (λ (x : ~β) (y : ℕ), x ^ y)) + (degree (rad f)),
    {
      have h2: (C (c_fac f) * finsupp.prod (factors f) (λ (k : ~β) (n : ℕ), k ^ n) ≠ 0),
      {
        rw [←h_fac],
        exact hf
      },
      conv 
      {
        to_lhs,
        rw [h_fac, degree_mul_eq_add_of_mul_ne_zero h2],
        simp,
        rw [degree_eq_add_degree_rad_degree_pow_min_one],
      }
    },
    rw h2,
    apply add_le_add_right,
    exact h1 
  },
end

-/





end mason_stothers