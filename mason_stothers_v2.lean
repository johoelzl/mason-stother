-- the to be Mason-Stother formalization
-- Authors Johannes & Jens

--Defining the gcd
import poly
--import euclidean_domain 
--Need to fix an admit in UFD, for the ...multiset lemma
import unique_factorization_domain
import data.finsupp
import algebraically_closed_field
import poly_over_UFD
import poly_over_field
import poly_derivative


noncomputable theory
local infix ^ := monoid.pow
local notation `d[`a`]` := polynomial.derivative a
local notation Σ := finset.sume
local notation Π := finset.prod
local notation `Π₀` := finsupp.prod
local notation `~`a:=polynomial a
local notation a `~ᵤ` b : 50 := associated a b

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


open classical multiset
section mason_stothers

--It might be good to remove the attribute to domain of integral domain?
def rad (p : polynomial β) : polynomial β :=
p.factors.erase_dup.prod


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

lemma ne_zero_of_dvd_ne_zero {γ : Type u}{a b : γ} [comm_semiring γ] (h1 : a ∣ b) (h2 : b ≠ 0) : a ≠ 0 :=
begin
  simp only [has_dvd.dvd] at h1,
  let c := some h1,
  have h3: b = a * c,
  from some_spec h1,
  by_contradiction h4,
  rw not_not at h4,
  rw h4 at h3,
  simp at h3,
  contradiction
end


open polynomial --Why here?

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
    rw associated_iff_eq_of_monic_of_monic h3 h4,
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

--make private?
lemma Mason_Stothers_lemma (f : polynomial β) :
  degree f ≤ degree (gcd f (derivative f )) + degree (rad f) := --I made degree radical from this one
begin
  by_cases hf : (f = 0),
  { simp [hf, nat.zero_le]},
  {
    have h_dvd_der : ∀x ∈ f.factors, x^(count x f.factors - 1) ∣ d[f],
    {
      rw [f.factors_eq] {occs := occurrences.pos [3]},
      rw [derivative_C_mul],
      intros x h,
      exact dvd_mul_of_dvd_right (Mason_Stothers_lemma_aux_1 f x h) _,
    },
    have h_dvd_f : ∀x ∈ f.factors, x^(count x f.factors - 1) ∣ f,
    {
      rw [f.factors_eq] {occs := occurrences.pos [3]},
      intros x hx, --We have intros x hx a lot here, duplicate?
      apply dvd_mul_of_dvd_right,
      exact dvd_trans (pow_count_sub_one_dvd_pow_count _ _) (forall_pow_count_dvd_prod _ x), --Duplicate 2 lines with Mason_Stothers_lemma_aux_1
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


lemma Mason_Stothers_lemma'
(f : polynomial β) : degree f - degree (gcd f (derivative f )) ≤  degree (rad f) := 
begin
  have h1 : degree f - degree (gcd f (derivative f )) ≤ degree (gcd f (derivative f )) + degree (rad f) - degree (gcd f (derivative f )),
  {
    apply nat.sub_le_sub_right,
    apply Mason_Stothers_lemma,
  },
  have h2 : degree (gcd f d[f]) + degree (rad f) - degree (gcd f d[f]) =  degree (rad f),
  {
    rw [add_comm _ (degree (rad f)), nat.add_sub_assoc, nat.sub_self, nat.add_zero],
    exact nat.le_refl _,
  },
  rw h2 at h1,
  exact h1,
end

lemma eq_zero_of_le_pred {n : ℕ} (h : n ≤ nat.pred n) : n = 0 :=
begin
  cases n,
    simp,
    simp at h,
    have h1 : nat.succ n = n,
    from le_antisymm h (nat.le_succ n),
    have h2 : nat.succ n ≠ n,
    from nat.succ_ne_self n,
    contradiction,
end

lemma derivative_eq_zero_of_dvd_derivative_self {a : polynomial β} (h : a ∣ d[a]) : d[a] = 0 :=
begin
  by_contradiction hc,
  have h1 : degree d[a] ≤ degree a - 1,
  from degree_derivative_le,
  have h2 : degree a ≤ degree d[a],
  from degree_dvd h hc,
  have h3 : degree a = 0,
  {
    have h3 : degree a ≤ degree a - 1,
    from le_trans h2 h1,
    exact eq_zero_of_le_pred h3,
  },
  rw ←is_constant_iff_degree_eq_zero at h3,
  have h5 : d[a] = 0,
  from derivative_eq_zero_of_is_constant h3,
  contradiction,
end

--In MS detailed I call this zero wronskian
lemma derivative_eq_zero_and_derivative_eq_zero_of_coprime_of_wron_eq_zero
{a b : polynomial β} 
(h1 : coprime a b)
(h2 : d[a] * b - a * d[b] = 0)
: d[a] = 0 ∧  d[b] = 0 := 
begin
  have h3 : d[a] * b = a * d[b],
  {
    exact calc d[a] * b = d[a] * b + (-a * d[b] + a * d[b]) : by simp
    ... = d[a] * b - (a * d[b]) + a * d[b] : by simp [add_assoc]
    ... = 0 + a * d[b] : by rw [h2]
    ... = _ : by simp
  },
  have h4 : a ∣ d[a] * b,
  from dvd.intro _ h3.symm,
  rw mul_comm at h4,
  have h5 : a ∣ d[a],
  exact dvd_of_dvd_mul_of_coprime h4 h1,
  have h6 : d[a] = 0,
  from derivative_eq_zero_of_dvd_derivative_self h5,

  --duplication
  rw mul_comm at h3,
  have h7 : b ∣ a * d[b],
  from dvd.intro _ h3,
  have h8 : b ∣ d[b],
  exact dvd_of_dvd_mul_of_coprime h7 (h1.symm),
  have h9 : d[b] = 0,
  from derivative_eq_zero_of_dvd_derivative_self h8,
  exact ⟨h6, h9⟩,
end

--Lemma coprime_gcd in MS_detailed
lemma coprime_gcd_derivative_gcd_derivative_of_coprime {a b : polynomial β} (h : coprime a b) (c d : polynomial β) : coprime (gcd a c) (gcd b d) :=
begin
  rw coprime,
  by_contradiction h1,
  let e := (gcd (gcd a c) (gcd b d)),
  have ha : e ∣ a,
  {
    have h2a: e ∣ (gcd a c),
      from gcd_left,
    have h2b : (gcd a c) ∣ a,
      from gcd_left,
    exact dvd_trans h2a h2b,
  },
  have hb : e ∣ b,
  {
    have h2a: e ∣ (gcd b d),
      from gcd_right,
    have h2b : (gcd b d) ∣ b,
      from gcd_left,
    exact dvd_trans h2a h2b,
  },
  have he: e ∣ (gcd a b),
    from gcd_min ha hb,
  have h2 : ¬is_unit (gcd a b),
    from not_is_unit_of_not_is_unit_dvd h1 he,
  rw coprime at h,
  exact h2 h,
end

lemma degree_gcd_derivative_le_degree {a : polynomial β}: degree (gcd a d[a]) ≤ degree a :=
begin
  by_cases h : (a = 0),
  {
    simp * at *,
  },
  {
    apply degree_gcd_le_left,
    exact h,
  }
end

lemma degree_gcd_derivative_lt_degree_of_degree_ne_zero {a : polynomial β} (h : degree a ≠ 0) (h_char : characteristic_zero β) : degree (gcd a d[a]) < degree a :=
begin
  have h1 : degree (gcd a d[a]) ≤ degree d[a],
  {
    apply degree_dvd,
    apply gcd_right,
    rw [ne.def, derivative_eq_zero_iff_is_constant, is_constant_iff_degree_eq_zero],
    exact h,
    exact h_char,
  },
  have h2 : ∃ n, degree a = nat.succ n,
  from nat.exists_eq_succ_of_ne_zero h,
  let n := some h2,
  have h3 : degree a = nat.succ n,
  from some_spec h2,
  exact calc degree (gcd a d[a]) ≤ degree d[a] : h1
  ... ≤ degree a - 1 : degree_derivative_le
  ... ≤ nat.succ n - 1 : by rw h3
  ... = n : rfl
  ... < nat.succ n : nat.lt_succ_self _
  ... = degree a : eq.symm h3,

end

open associated

lemma not_zero_mem_factors {a : polynomial β} : (0 : polynomial β) ∉ a.factors :=
begin
  by_contradiction h1,
  have : irreducible (0 : polynomial β),
    from a.factors_irred 0 h1,
  have : ¬ irreducible (0 : polynomial β),
  {  simp},
  contradiction,
end

lemma c_fac_eq_zero_iff_eq_zero {a : polynomial β} : a.c_fac = 0 ↔ a = 0 :=
begin
  split,
  {
    intro h,
    rw a.factors_eq,
    simp *,
  },
  {
    intro h,
    rw [a.factors_eq, mul_eq_zero_iff_eq_zero_or_eq_zero] at h,
    cases h,
    {
      rw C_eq_zero_iff_eq_zero at h,
      exact h,
    },
    {
      rw prod_eq_zero_iff_zero_mem' at h,
      have : (0 : polynomial β) ∉ a.factors,
        from not_zero_mem_factors,
      contradiction,
    }
  }
end

--Not used
private lemma mk_C_c_fac_eq_one_of_ne_zero {a : polynomial β} (h : a ≠ 0) : mk (C a.c_fac) = 1 :=
begin
  rw [ne.def, ←c_fac_eq_zero_iff_eq_zero] at h,
  have h1 : is_unit a.c_fac,
    from for_all_is_unit_of_not_zero h,
  have h2 : is_unit (C a.c_fac),
    from is_unit_of_is_unit h1,
  rw mk_eq_one_iff_is_unit,
  exact h2,
end

--a and b can be implicit
lemma factors_inter_factors_eq_zero_of_coprime (a b : polynomial β) (h : coprime a b) : a.factors ∩ b.factors = 0 :=
begin
  by_cases ha: a = 0,
  {
    subst ha,
    simp,
  },
  {
    by_cases hb: b = 0,
    {
      subst hb,
      simp,
    },
    { --I already have a similar lemma for coprime
      rw [coprime_iff_mk_inf_mk_eq_one, a.factors_eq, b.factors_eq, mul_mk, mul_mk] at h, --we go to the quotient structure with respect to units.
      rw inf_mul_eq_one_iff_inf_eq_one_and_inf_eq_one at h, --We probably can do without going to the quotient, because we have the lemmas for coprime
      let h1 := h.2,    
      rw mul_inf_eq_one_iff_inf_eq_one_and_inf_eq_one at h1,
      let h2 := h1.2,
      rw [mk_def, mk_def, ←prod_mk, ←prod_mk] at h2,
      rw prod_inf_prod_eq_one_iff_forall_forall_inf_eq_one at h2,

      rw [inter_eq_zero_iff_disjoint, disjoint_iff_ne],
      {
        intros x hx y hy,
        have h3 : mk x ⊓ mk y = 1,
        {
          apply h2,
          {
            rw mem_map,
            exact ⟨x, hx, rfl⟩,
          },
          {
            rw mem_map,
            exact ⟨y, hy, rfl⟩,            
          },
        },
        rw [←coprime_iff_mk_inf_mk_eq_one, coprime_iff_not_associated_of_irreducible_of_irreducible] at h3,
        rw [associated_iff_eq_of_monic_of_monic] at h3,
        exact h3,
        exact a.factors_monic x hx,
        exact b.factors_monic y hy,
        exact a.factors_irred x hx,
        exact b.factors_irred y hy,
      }
    }
  }
end

open associated

private lemma monic_prod_factors (a : polynomial β) : monic a.factors.prod :=
  monic_prod_of_forall_mem_monic a.factors_monic


lemma c_fac_eq_leading_coeff (a : polynomial β) : a.c_fac = leading_coeff a :=
begin
  by_cases ha : a = 0,
  {
    simp * at *,
  },
  {
    have h1 : a = (C a.c_fac) * a.factors.prod,
      from a.factors_eq,
    rw [h1] {occs := occurrences.pos[2]},
    rw leading_coeff_mul_eq_mul_leading_coef,
    let h3 := monic_prod_factors a,
      rw monic at h3,
    simp [h3],
  }
end

private lemma C_inv_c_fac_mul_eq_prod_factors {a : polynomial β} (ha : a ≠ 0): (C a.c_fac⁻¹) * a = a.factors.prod :=
begin
  have h1 : a = (C a.c_fac) * a.factors.prod,
    from a.factors_eq,    
  rw [ne.def, ←c_fac_eq_zero_iff_eq_zero] at ha,
  exact calc (C a.c_fac⁻¹) * a = (C a.c_fac⁻¹) * (C (c_fac a) * prod (factors a)) : by rw [←h1]
      ... = _ : by rw [←mul_assoc, ←C_mul_C, inv_mul_cancel ha, C_1, one_mul], 
end

lemma factors_eq_map_monic_out_to_multiset_mk (a : polynomial β) : a.factors = map monic_out (associated.to_multiset (associated.mk a)) :=
begin
  by_cases ha : a = 0,
  {
    simp * at *,
  },
  {
    have h1 : a = C (a.c_fac) * a.factors.prod,
      from a.factors_eq,
    have h2 : C (a.c_fac⁻¹) * a = a.factors.prod,
      from C_inv_c_fac_mul_eq_prod_factors ha,
    have h3: a.factors.prod = (map monic_out (to_multiset (mk a))).prod,
    {
      rw prod_map_monic_out_eq_monic_out_prod,
      rw ←h2,
      rw ←associated_iff_eq_of_monic_of_monic,
      rw to_multiset_prod_eq,
      have h4 : (a ~ᵤ (monic_out (mk a))),
        from (monic_out_mk_associated _).symm,
      have h5 : (C (c_fac a)⁻¹ * a ~ᵤ a),
      {
        have h5a : (c_fac a)⁻¹ ≠ 0,
        {
          rw ←c_fac_eq_zero_iff_eq_zero at ha,
          apply inv_ne_zero,
          exact ha,
        },
        have h5b : (C (c_fac a)⁻¹) ≠ 0, --Is this used?
        {
          rw [ne.def, C_eq_zero_iff_eq_zero],
          exact h5a,
        },
        have h5c: is_unit (C (c_fac a)⁻¹),
          from is_unit_C_of_ne_zero h5a,
        rcases h5c with ⟨u, hu⟩,
        exact ⟨u, by simp *⟩,
      },
      exact associated.trans h5 h4,
      rwa [ne.def, mk_eq_zero_iff_eq_zero],
      {
        rw c_fac_eq_leading_coeff,
        exact leading_coeff_inv_mul_monic_of_ne_zero ha,          
      },
      {
        apply monic_monic_out_of_ne_zero,
        rw [to_multiset_prod_eq],--Wrong naminG!!
        rw ←mk_eq_zero_iff_eq_zero at ha, --Duplicate
        exact ha,
        rw ←mk_eq_zero_iff_eq_zero at ha,         
        exact ha,
      }
    },
    have h4a: ∀ (x : ~β), x ∈ map monic_out (to_multiset (mk a)) → irreducible x,
    {
      intros x h,
      rw mem_map at h,
      rcases h with ⟨y, hy⟩,
      rw hy.2.symm,
      apply irreducible_monic_out_of_irred,
      apply to_multiset_irred _ y hy.1,
    },
    have h4 : rel_multiset associated a.factors (map monic_out (to_multiset (mk a))),
      from unique_factorization_domain.unique a.factors_irred h4a h3,
    apply eq_of_rel_multiset_associated_of_forall_mem_monic_of_forall_mem_monic,
    exact h4,
    exact a.factors_monic,
    {
      intros x h,
      rw mem_map at h,
      rcases h with ⟨y, hy⟩,
      rw hy.2.symm,
      apply monic_monic_out_of_ne_zero,
      {
        have : irred y,
          from to_multiset_irred _ y hy.1,
        exact ne_zero_of_irred this,
      }
    }
  }
end

--aux
--I already have to_multiset_mul, how can I reuse that here?? How to make the connection between monic and associated??
lemma factors_mul_eq_factors_add_factors {a b : polynomial β} (ha : a ≠ 0) (hb : b ≠ 0) : factors (a * b) = a.factors + b.factors :=
begin
  rw [factors_eq_map_monic_out_to_multiset_mk, factors_eq_map_monic_out_to_multiset_mk, factors_eq_map_monic_out_to_multiset_mk],
  rw [mul_mk, to_multiset_mul],
  simp,
  simp [mk_eq_zero_iff_eq_zero, *],
  simp [mk_eq_zero_iff_eq_zero, *],
end

@[simp] lemma rad_zero : rad (0 : polynomial β ) = 1 :=
begin
  simp [rad],
end

lemma rad_mul_eq_rad_mul_rad_of_coprime {a b : polynomial β} (ha : a ≠ 0) (hb : b ≠ 0) (h : coprime a b) : rad (a * b) = (rad a) * (rad b) :=
begin
  simp only [rad],
  rw prod_mul_prod_eq_add_prod,
  apply congr_arg,
  
  rw factors_mul_eq_factors_add_factors ha hb, --Might be good to go to nodup
  rw multiset.ext,
  intros x,
  by_cases h1 : x ∈ (a.factors + b.factors),
  {
    have h2 : count x (erase_dup (factors a + factors b)) = 1,
    {
      apply count_eq_one_of_mem,
      exact nodup_erase_dup _,
      rwa mem_erase_dup,
    },
    rw mem_add at h1,
    have h3 : x ∈ a.factors ∩ b.factors ↔ x ∈ a.factors ∧ x ∈ b.factors,
      from mem_inter,
    have h4: a.factors ∩ b.factors = 0,
      from factors_inter_factors_eq_zero_of_coprime _ _ h,
    cases h1,
    {
      have : x ∉ b.factors,
      {
          simp * at *,
      },
      rw ←mem_erase_dup at h1,
      have h1a : count x (erase_dup (factors a)) = 1,
        from count_eq_one_of_mem (nodup_erase_dup _) h1,
      rw ←mem_erase_dup at this,
      have h1b : count x (erase_dup (factors b)) = 0,
      {
        rwa count_eq_zero,
      },
      rw count_add,
      simp * at *,
    },
    { --Strong duplication
      have : x ∉ a.factors,
      {
          simp * at *,
      },
      rw ←mem_erase_dup at h1,
      have h1a : count x (erase_dup (factors b)) = 1,
        from count_eq_one_of_mem (nodup_erase_dup _) h1,
      rw ←mem_erase_dup at this,
      have h1b : count x (erase_dup (factors a)) = 0,
      {
        rwa count_eq_zero,
      },
      rw count_add,
      simp * at *,      
    }
  },
  {
    have h2 : count x (erase_dup (factors a + factors b)) = 0,
    {
      rwa [count_eq_zero, mem_erase_dup],
    },
    rw [mem_add, not_or_distrib] at h1,
    have h3 : count x (erase_dup (factors a)) = 0,
    {
      rw [count_eq_zero, mem_erase_dup],
      exact h1.1,  
    },
    have h4 : count x (erase_dup (factors b)) = 0,
    {
      rw [count_eq_zero, mem_erase_dup],
      exact h1.2,        
    },
    simp * at *,
  },
end



--We will need extra conditions here
--We only need this one
lemma degree_rad_add {a b: polynomial β} (ha : a ≠ 0) (hb : b ≠ 0) (hab : coprime a b): degree (rad a) + degree (rad b) ≤ degree (rad (a * b)) :=
begin
  rw rad_mul_eq_rad_mul_rad_of_coprime ha hb hab,
  rw degree_mul_eq_add_of_mul_ne_zero,
  apply _root_.mul_ne_zero,
  {
    apply multiset.prod_ne_zero_of_forall_mem_ne_zero,
    intros x h,
    rw mem_erase_dup at h,
    exact (a.factors_irred _ h).1 --Anoying setup for factors_irred
  },
  {
    apply multiset.prod_ne_zero_of_forall_mem_ne_zero,
    intros x h,
    rw mem_erase_dup at h,
    exact (b.factors_irred _ h).1 --Anoying setup for factors_irred    
  },
end

private lemma h_rad_add {a b c: polynomial β} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : coprime a b) (h_coprime_bc : coprime b c)
  (h_coprime_ca : coprime c a)
:  degree(rad(a))+degree(rad(b))+degree(rad(c)) ≤ degree(rad(a*b*c)) :=
begin
  have habc : coprime (a*b) c,
    {
      have h1: ((gcd (a * b) c) ~ᵤ (gcd b c)),
        from gcd_mul_cancel h_coprime_ca.symm,
      exact is_unit_of_associated h_coprime_bc h1.symm,
    },
  have h1 : a * b ≠ 0,
    from mul_ne_zero ha hb,
  have h3 : degree (rad a) + degree (rad b) ≤ degree (rad (a * b)),
    from degree_rad_add ha hb hab,
  exact calc degree(rad(a))+degree(rad(b))+degree(rad(c)) ≤ degree (rad (a * b)) + degree (rad c) : add_le_add_right h3 _
  ... ≤ _ : degree_rad_add h1 hc habc
end


lemma gt_zero_of_ne_zero {n : ℕ} (h : n ≠ 0) : n > 0 :=
begin
  have h1 : ∃ m : ℕ, n = nat.succ m,
  from nat.exists_eq_succ_of_ne_zero h,
  let m := some h1,
  have h2 : n = nat.succ m,
  from some_spec h1,
  rw h2,
  exact nat.zero_lt_succ _,
end

lemma MS_aux_1a {c : polynomial β} (h3 : ¬degree c = 0)(h_char : characteristic_zero β) : 1 ≤ (degree c - degree (gcd c d[c])) :=
begin
  have h4 : degree c - degree (gcd c d[c]) > 0,
  {
    rw [nat.pos_iff_ne_zero, ne.def, nat.sub_eq_zero_iff_le],
    simp,
    exact degree_gcd_derivative_lt_degree_of_degree_ne_zero h3 h_char,
  },
  exact h4,

end

--should be in poly
lemma MS_aux_1b {a b c : polynomial β} (h_char : characteristic_zero β) (h_add : a + b = c)
  (h_constant : ¬(is_constant a ∧ is_constant b ∧ is_constant c)) (h1 : is_constant b)
(h2 : ¬is_constant a) : ¬ is_constant c :=
begin
  rw [is_constant_iff_degree_eq_zero] at *,
  have h3 : c (degree a) ≠ 0,
  {
    rw ← h_add,
    simp,
    have h3 : b (degree a) = 0,
    {
      apply eq_zero_of_gt_degree,
      rw h1,
      exact gt_zero_of_ne_zero h2,
    },
    rw h3,
    simp,
    have h4 : leading_coeff a = 0 ↔ a = 0,
    from leading_coef_eq_zero_iff_eq_zero,
    rw leading_coeff at h4,
    rw h4,
    by_contradiction h5,
    rw h5 at h2,
    simp at h2,
    exact h2,
  },
  have h4 : degree a ≤ degree c,
  from le_degree h3,
  by_contradiction h5,
  rw h5 at h4,
  have : degree a = 0,
  from nat.eq_zero_of_le_zero h4,
  contradiction,     
end

lemma MS_aux_1 {a b c : polynomial β} (h_char : characteristic_zero β) (h_add : a + b = c)
  (h_constant : ¬(is_constant a ∧ is_constant b ∧ is_constant c)) :
  1 ≤ degree b - degree (gcd b d[b]) + (degree c - degree (gcd c d[c])) :=
begin
  by_cases h1 : (is_constant b),
  {
    by_cases h2 : (is_constant a),
    {
      have h3 : is_constant c,
      from is_constant_add h2 h1 h_add,
      simp * at *,
    },
    {
      have h3 : ¬ is_constant c,
      {
        exact MS_aux_1b h_char h_add h_constant h1 h2,
      },
      rw [is_constant_iff_degree_eq_zero] at h3,
      have h4 : 1 ≤ (degree c - degree (gcd c d[c])),
      from MS_aux_1a h3 h_char,
      apply nat.le_trans h4,
      simp,
      exact nat.zero_le _,
    }
  },
  {
    rw [is_constant_iff_degree_eq_zero] at h1,
    have h2 : 1 ≤ degree b - degree (gcd b d[b]),
    from MS_aux_1a h1 h_char,
    apply nat.le_trans h2,
    simp,
    exact nat.zero_le _,
  }

end


---Very likely that the lemmas on rad are overcomplicated, they should use erase_dup_more



lemma dvd_of_mem_factors (f : polynomial β) (x : polynomial β) (h : x ∈ f.factors) : x ∣ f :=
begin
  rw f.factors_eq,
  have : x ∣ f.factors.prod,
    from dvd_prod_of_mem f.factors h,
  exact dvd_mul_of_dvd_right this _,
end


lemma not_is_unit_prod_factors_of_factors_ne_zero (a : polynomial β) (h : a.factors ≠ 0) : ¬ is_unit (a.factors.prod) :=
begin
  exact not_is_unit_prod_of_ne_zero_of_forall_mem_irreducible h a.factors_irred,
end


@[simp] lemma factors_C (c : β) : (C c).factors = 0 :=
begin
  by_cases h1 : C c = 0,
  {
    simp *,
  },
  {
    by_contradiction h2,
    rcases (exists_mem_of_ne_zero h2) with ⟨x, hx⟩,
    have h2 : x ∣ C c, --The part below could be a separate lemma
    {
      exact dvd_of_mem_factors (C c) x hx,   
    },
    have h3: irreducible x,
      from (C c).factors_irred x hx,
    have h4: ¬is_unit x,
      from not_is_unit_of_irreducible h3,
    have h5: ¬is_unit (C c),
      from not_is_unit_of_not_is_unit_dvd h4 h2,
    have h6 : is_constant (C c),
      {simp},
    rw is_constant_iff_eq_zero_or_is_unit at h6,
    simp * at *, 
  }
end

lemma is_constant_iff_factors_eq_zero (a : polynomial β) : is_constant a ↔ a.factors = 0 :=
begin
  split,
  {
    intro h,
    rcases h with ⟨c, hc⟩,
    subst hc,
    simp,
  },
  {
    intro h,
    rw a.factors_eq,
    simp * at *,
  }
end

--lemma factors_eq_zero_iff_rad_eq_zero (a : polynomial β)



lemma rad_dvd_prod_factors (a : polynomial β) : (rad a) ∣ a.factors.prod :=
begin
  rw rad,
  apply prod_dvd_prod_of_le,
  exact erase_dup_le _,
end 

lemma rad_dvd (a : polynomial β) : (rad a) ∣ a :=
begin
  rw [a.factors_eq] {occs := occurrences.pos [2]},
  apply dvd_mul_of_dvd_right,
  exact rad_dvd_prod_factors _,  
end

lemma degree_rad_le (a : polynomial β) : degree (rad a) ≤ degree a :=
begin
  by_cases h1 : a = 0,
  {
    subst h1,
    simp,
  },
  {
    apply degree_dvd,
    exact rad_dvd _,
    exact h1,
  }
end



lemma is_unit_rad_iff_factors_eq_zero (a : polynomial β) : is_unit (rad a) ↔ a.factors = 0 :=
begin
  split,
  {
    intro h,
    rw ←erase_dup_eq_zero_iff_eq_zero,
    by_contradiction h1,
    have : ¬is_unit (rad a),
      {
        apply not_is_unit_prod_of_ne_zero_of_forall_mem_irreducible h1,
        intros x h,
        rw mem_erase_dup at h,
        exact a.factors_irred x h,
      },
    simp * at *,
  },
  {
    intro h,
    rw ←erase_dup_eq_zero_iff_eq_zero at h,
    rw rad,
    simp *,
  }
end

lemma degree_rad_eq_zero_iff_is_constant (a : polynomial β) : degree (rad a) = 0 ↔ is_constant a :=
begin
  split,
  {
    intro h,
    rw is_constant_iff_factors_eq_zero,
    rw [←is_constant_iff_degree_eq_zero, is_constant_iff_eq_zero_or_is_unit] at h,
    cases h,
    {
      have : rad a ≠ 0,
        from rad_ne_zero,
      contradiction,
    },
    {
      rw ←is_unit_rad_iff_factors_eq_zero,
      exact h,
    },
  },
  {
    intro h,
    rw is_constant_iff_factors_eq_zero at h,
    apply degree_eq_zero_of_is_unit,
    rw is_unit_rad_iff_factors_eq_zero,
    exact h,
  }
end

--Strong duplication with MS_aux_1
lemma MS_aux_2 {a b c : polynomial β} (h_char : characteristic_zero β) (h_add : a + b = c)
  (h_constant : ¬(is_constant a ∧ is_constant b ∧ is_constant c)) :
   1 ≤ degree (rad a) + (degree c - degree (gcd c d[c])) :=
begin
  by_cases h1 : is_constant b,
  {
    by_cases h2 : is_constant a,
    {
      have h3 : is_constant c,
      from is_constant_add h2 h1 h_add,
      simp * at *,
    },
    {
      have h3 : ¬ is_constant c,
      {
        rw [is_constant_iff_degree_eq_zero] at *,
        have h3 : c (degree a) ≠ 0,
        {
          rw ← h_add,
          simp,
          have h3 : b (degree a) = 0,
          {
            apply eq_zero_of_gt_degree,
            rw h1,
            exact gt_zero_of_ne_zero h2,
          },
          rw h3,
          simp,
          have h4 : leading_coeff a = 0 ↔ a = 0,
          from leading_coef_eq_zero_iff_eq_zero,
          rw leading_coeff at h4,
          rw h4,
          by_contradiction h5,
          rw h5 at h2,
          simp at h2,
          exact h2,
        },
        have h4 : degree a ≤ degree c,
        from le_degree h3,
        by_contradiction h5,
        rw h5 at h4,
        have : degree a = 0,
        from nat.eq_zero_of_le_zero h4,
        contradiction,
      }, 
      rw [is_constant_iff_degree_eq_zero] at h3,
      have h4 : 1 ≤ (degree c - degree (gcd c d[c])),
      from MS_aux_1a h3 h_char,
      apply nat.le_trans h4,
      simp,
      exact nat.zero_le _,   
    }
  },
  {
    by_cases h2 : (is_constant a),
    {
      rw add_comm at h_add,
      have h_constant' : ¬(is_constant b ∧ is_constant a ∧ is_constant c),
      {simp [*, and_comm]},
      have h3 : ¬is_constant c,
      from MS_aux_1b h_char h_add h_constant' h2 h1,
      rw [is_constant_iff_degree_eq_zero] at h3,
      have h4 : 1 ≤ (degree c - degree (gcd c d[c])),
      from MS_aux_1a h3 h_char,
      apply nat.le_trans h4,
      simp,
      exact nat.zero_le _,   
    },
    {
      have : degree a ≠ 0,
      {
        rw [ne.def, ←is_constant_iff_degree_eq_zero],
        exact h2,
      },
      rw [ne.def, ←is_constant_iff_degree_eq_zero, ←degree_rad_eq_zero_iff_is_constant] at this,
      have h3: 1 ≤ degree (rad a),
      {
        rcases (nat.exists_eq_succ_of_ne_zero this) with ⟨n, hn⟩,
        simp * at *,
        rw nat.succ_le_succ_iff,
        exact nat.zero_le _,
      },
      apply nat.le_trans h3,
      exact nat.le_add_right _ _,
    }
  }
end

private lemma rw_aux_1a [field β] 
  (a b c : polynomial β)
  (h_add : a + b = c)
  (h_constant : ¬(is_constant a ∧ is_constant b ∧ is_constant c)) :
  degree a ≠ 0 ∨ degree b ≠ 0 :=
begin
  rw [not_and_distrib, not_and_distrib] at h_constant,
  cases h_constant,
  {
    rw is_constant_iff_degree_eq_zero at h_constant,
    simp *,
  },
  {
    cases h_constant,
    {
      rw is_constant_iff_degree_eq_zero at h_constant,
      simp *,      
    },
    {
      rw is_constant_iff_degree_eq_zero at h_constant,
      have : degree (a + b) ≤ max (degree a) (degree b),
        from degree_add,
      simp * at *,
      rw le_max_iff at this,
      rcases (nat.exists_eq_succ_of_ne_zero h_constant) with ⟨n, hn⟩,
      simp * at *,
      cases this with h,
      {
        have : ¬degree a = 0,
        {
          by_contradiction h1,
          simp * at *,
          exact nat.not_succ_le_zero _ h,
        },
        simp *,
      },
      {
        have : ¬degree b = 0,
        {
          by_contradiction h1,
          simp * at *,
          exact nat.not_succ_le_zero _ this,
        },
        simp *,        
      }
    }
  }
end

private lemma rw_aux_1b [field β] 
  (a b c : polynomial β)
  (h_add : a + b = c)
  (h_constant : ¬(is_constant a ∧ is_constant b ∧ is_constant c)) :
  1 ≤ degree a + degree b :=
begin
  have : degree a ≠ 0 ∨ degree b ≠ 0,
    from rw_aux_1a a b c h_add h_constant,
  cases this with h h ;
  {
    rcases (nat.exists_eq_succ_of_ne_zero h) with ⟨n, hn⟩,
    simp * at *,
    have : 1 ≤ nat.succ n,
    {
      rw nat.succ_le_succ_iff,
      exact nat.zero_le _,
    },
    apply nat.le_trans this,
    apply nat.le_add_right,
  },
end

--h_deg_c_le_1
lemma rw_aux_1 [field β]
  --(h_char : characteristic_zero β)
  (a b c : polynomial β)
  --(h_coprime_ab : coprime a b)
  --(h_coprime_bc : coprime b c)
  --(h_coprime_ca : coprime c a)
  (h_add : a + b = c)
  (h_constant : ¬(is_constant a ∧ is_constant b ∧ is_constant c)) 
  (h_deg_add_le : degree (gcd a d[a]) + degree (gcd b d[b]) + degree (gcd c d[c]) ≤ degree a + degree b - 1) :
  degree c ≤
    (degree a - degree (gcd a d[a])) +
    (degree b - degree (gcd b d[b])) +
    (degree c - degree (gcd c d[c])) - 1 :=
have 1 ≤ degree a + degree b, from rw_aux_1b a b c h_add h_constant,
have h : ∀p:polynomial β, degree (gcd p d[p]) ≤ degree p, from (λ p, @degree_gcd_derivative_le_degree _ _ p),
have (degree (gcd a d[a]) : ℤ) + (degree (gcd b d[b]) : ℤ) + (degree (gcd c d[c]) : ℤ) ≤
    (degree a : ℤ) + (degree b : ℤ) - 1,
  by rwa [← int.coe_nat_add, ← int.coe_nat_add, ← int.coe_nat_add, ← int.coe_nat_one,
    ← int.coe_nat_sub this, int.coe_nat_le],
have (degree c : ℤ) ≤
    ((degree a : ℤ) - (degree (gcd a d[a]) : ℤ)) +
    ((degree b : ℤ) - (degree (gcd b d[b]) : ℤ)) +
    ((degree c : ℤ) - (degree (gcd c d[c]) : ℤ)) - 1,
  from calc (degree c : ℤ) ≤
    ((degree c : ℤ) + ((degree a : ℤ) + (degree b : ℤ) - 1)) -
      ((degree (gcd a d[a]) : ℤ) + (degree (gcd b d[b]) : ℤ) + (degree (gcd c d[c]) : ℤ)) : 
      le_sub_iff_add_le.mpr $ add_le_add_left this _
    ... = _ : by simp,
have 1 + (degree c : ℤ) ≤
    ((degree a : ℤ) - (degree (gcd a d[a]) : ℤ)) +
    ((degree b : ℤ) - (degree (gcd b d[b]) : ℤ)) +
    ((degree c : ℤ) - (degree (gcd c d[c]) : ℤ)),
  from add_le_of_le_sub_left this,
nat.le_sub_left_of_add_le $
  by rwa [← int.coe_nat_sub (h _), ← int.coe_nat_sub (h _), ← int.coe_nat_sub (h _),
      ← int.coe_nat_add, ← int.coe_nat_add, ← int.coe_nat_one, ← int.coe_nat_add, int.coe_nat_le] at this

/-
lemma Mason_Stothers_lemma
(f : polynomial β) : degree f ≤ degree (gcd f (derivative f )) + degree (rad f) -/
/-
lemma Mason_Stothers_lemma'
(f : polynomial β) : degree f - degree (gcd f (derivative f )) ≤  degree (rad f) := 
 -/
 /-
--We will need extra conditions here
lemma degree_rad_add {a b c : polynomial β}: degree (rad a) + degree (rad b) + degree (rad c) ≤ degree (rad (a * b * c)) :=
begin
  admit,
end-/

lemma nat.add_mono{a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d :=
begin
  exact calc a + c ≤ a + d : nat.add_le_add_left hcd _
  ... ≤ b + d : nat.add_le_add_right hab _
end


--h_le_rad
lemma rw_aux_2 [field β] --We want to use the Mason Stothers lemmas here
  {a b c : polynomial β}
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0)
  (h_coprime_ab : coprime a b)
  (h_coprime_bc : coprime b c)
  (h_coprime_ca : coprime c a)
   : degree a - degree (gcd a d[a]) + (degree b - degree (gcd b d[b])) + (degree c - degree (gcd c d[c])) - 1 ≤
  degree (rad (a * b * c)) - 1:=
begin
  apply nat.sub_le_sub_right,
  have h_rad:  degree(rad(a))+degree(rad(b))+degree(rad(c)) ≤ degree(rad(a*b*c)),
    from h_rad_add ha hb hc h_coprime_ab h_coprime_bc h_coprime_ca,
  refine nat.le_trans _ h_rad,
  apply nat.add_mono _ (Mason_Stothers_lemma' c),
  apply nat.add_mono (Mason_Stothers_lemma' a) (Mason_Stothers_lemma' b), 
end

private lemma h_dvd_wron_a 
(a b c : polynomial β): gcd a d[a] ∣ d[a] * b - a * d[b] :=
 begin
  have h1 : gcd a d[a] ∣ d[a] * b,
  {
    apply dvd_trans gcd_right,
    apply dvd_mul_of_dvd_left,
    simp
  },
  have h2 : gcd a d[a] ∣ a * d[b],
  {
    apply dvd_trans gcd_left,
    apply dvd_mul_of_dvd_left,
    simp
  },
  exact dvd_sub h1 h2,
end

private lemma h_dvd_wron_b 
(a b c : polynomial β): gcd b d[b] ∣ d[a] * b - a * d[b] :=
begin
  have h1 : gcd b d[b] ∣ d[a] * b,
  {
    apply dvd_trans gcd_left,
    apply dvd_mul_of_dvd_right,
    simp
  },
  have h2 : gcd b d[b] ∣ a * d[b],
  {
    apply dvd_trans gcd_right,
    apply dvd_mul_of_dvd_right,
    simp
  },
  exact dvd_sub h1 h2,
end
  
private lemma h_dvd_wron_c 
(a b c : polynomial β)
(h_wron : d[a] * b - a * d[b] = d[a] * c - a * d[c])
: gcd c d[c] ∣ d[a] * b - a * d[b] :=
begin
  rw h_wron,
  have h1 : gcd c d[c] ∣ a * d[c],
  {
    apply dvd_trans gcd_right,
    apply dvd_mul_of_dvd_right,
    simp
  },
  have h2 : gcd c d[c] ∣ d[a] * c,
  {
    apply dvd_trans gcd_left,
    apply dvd_mul_of_dvd_right,
    simp
  },
  exact dvd_sub h2 h1,
end




private lemma one_le_of_ne_zero {n : ℕ } (h : n ≠ 0) : 1 ≤ n := 
begin
  let m := some (nat.exists_eq_succ_of_ne_zero h),
  have h1 : n = nat.succ m,
  from some_spec (nat.exists_eq_succ_of_ne_zero h), 
  rw [h1, nat.succ_le_succ_iff],
  exact nat.zero_le _,
end

--Todo can we remove the a = 0, b = 0 cases?
lemma degree_wron_le {a b : polynomial β} : degree (d[a] * b - a * d[b]) ≤ degree a + degree b - 1 :=
begin
  by_cases h1 : (a = 0),
  {
    simp *,
    exact nat.zero_le _,
  },
  {
    by_cases h2 : (degree a = 0),
    {

      by_cases h3 : (b = 0),
      {
        rw h3,
        simp,
        exact nat.zero_le _,
      },
      {
        simp [*],
        by_cases h4 : (degree b = 0),
        {
          simp *,
          rw [←is_constant_iff_degree_eq_zero] at *,
          have h5 : derivative a = 0,
          from derivative_eq_zero_of_is_constant h2,
          have h6 : derivative b = 0,
          from derivative_eq_zero_of_is_constant h4,
          simp *,          
        },
        {
          have h2a : degree a = 0,
          from h2,
          rw [←is_constant_iff_degree_eq_zero] at h2,
          have h5 : derivative a = 0,
          from derivative_eq_zero_of_is_constant h2,
          simp *,
          by_cases h6 : (derivative b = 0),
          {
            simp *,
            exact nat.zero_le _,
          },
          {
            --rw [degree_neg],
            apply nat.le_trans degree_mul,
            simp *,
            exact degree_derivative_le,
          }
        },

      }
    },
    {
      by_cases h3 : (b = 0),
      {
        simp *,
        exact nat.zero_le _,
      },
      {
        by_cases h4 : (degree b = 0),
        {
          simp *,
          rw [←is_constant_iff_degree_eq_zero] at h4,
          have h5 : derivative b = 0,
          from derivative_eq_zero_of_is_constant h4,
          simp *,
          apply nat.le_trans degree_mul,
          rw [is_constant_iff_degree_eq_zero] at h4,
          simp *,
          exact degree_derivative_le,
        },
        {
          apply nat.le_trans degree_sub,
          have h5 : degree (d[a] * b) ≤ degree a + degree b - 1,
          {
            apply nat.le_trans degree_mul,
            rw [add_comm _ (degree b), add_comm _ (degree b), nat.add_sub_assoc],
            apply add_le_add_left,
            exact degree_derivative_le,
            exact polynomial.one_le_of_ne_zero h2, --Can I remove this from polynomial??
          },
          have h6 : (degree (a * d[b])) ≤ degree a + degree b - 1,
          {
            apply nat.le_trans degree_mul,
            rw [nat.add_sub_assoc],
            apply add_le_add_left,
            exact degree_derivative_le,
            exact polynomial.one_le_of_ne_zero h4,        
          },
          exact max_le h5 h6,
        }
      }
    }
  }
end

lemma degree_wron_le2 {a b : polynomial β} : degree (d[a] * b - a * d[b]) ≤ degree a + degree b - 1 :=
begin
  by_cases h2 : (degree a = 0),
  {
    simp [is_constant_iff_degree_eq_zero, derivative_eq_zero_of_is_constant, *] at *,
    by_cases h6 : (derivative b = 0),
    { simp [nat.zero_le, *]},
    {
      apply nat.le_trans degree_mul,
      simp [degree_derivative_le, *],
    } 
  },
  {
    by_cases h4 : (degree b = 0), --This case distinction shouldnn't be needed
    {
      simp [is_constant_iff_degree_eq_zero, derivative_eq_zero_of_is_constant, *] at *,
      apply nat.le_trans degree_mul,
      simp [degree_derivative_le, *],
    },
    {
      apply nat.le_trans degree_sub,
      have h5 : degree (d[a] * b) ≤ degree a + degree b - 1,
      {
        apply nat.le_trans degree_mul,
        rw [add_comm _ (degree b), add_comm _ (degree b), nat.add_sub_assoc (polynomial.one_le_of_ne_zero h2)],
        apply add_le_add_left degree_derivative_le,
      },
      have h6 : (degree (a * d[b])) ≤ degree a + degree b - 1,
      {
        apply nat.le_trans degree_mul,
        rw [nat.add_sub_assoc (polynomial.one_le_of_ne_zero h4)],
        apply add_le_add_left degree_derivative_le,  
      },
      exact max_le h5 h6,
    }     
  }
end


private lemma h_wron_ne_zero 
  (a b c : polynomial β)   
  (h_coprime_ab : coprime a b)
  (h_coprime_ca : coprime c a)
  (h_der_not_all_zero : ¬(d[a] = 0 ∧ d[b] = 0 ∧ d[c] = 0))
  (h_wron : d[a] * b - a * d[b] = d[a] * c - a * d[c]): 
  d[a] * b - a * d[b] ≠ 0 :=
begin
  by_contradiction h1,
  rw not_not at h1,
  have h_a_b : d[a] = 0 ∧ d[b] = 0,
  from derivative_eq_zero_and_derivative_eq_zero_of_coprime_of_wron_eq_zero h_coprime_ab h1,
  have h2 : d[a] * c - a * d[c] = 0,
  {rw [←h_wron, h1]},
  have h_a_c : d[a] = 0 ∧ d[c] = 0,
  from derivative_eq_zero_and_derivative_eq_zero_of_coprime_of_wron_eq_zero (h_coprime_ca.symm) h2,
  have h3 : (d[a] = 0 ∧ d[b] = 0 ∧ d[c] = 0),
  exact ⟨and.elim_left h_a_b, and.elim_right h_a_b, and.elim_right h_a_c⟩,
  contradiction    
end

private lemma h_deg_add 
  (a b c : polynomial β)
  (h_wron_ne_zero : d[a] * b - a * d[b] ≠ 0)
  (h_gcds_dvd : (gcd a d[a]) * (gcd b d[b]) * (gcd c d[c]) ∣ d[a] * b - a * d[b]):
  degree (gcd a d[a] * gcd b d[b] * gcd c d[c]) = degree (gcd a d[a]) + degree (gcd b d[b]) + degree (gcd c d[c]) :=
begin
  have h1 : gcd a d[a] * gcd b d[b] * gcd c d[c] ≠ 0,
    from ne_zero_of_dvd_ne_zero h_gcds_dvd h_wron_ne_zero,
  have h2 : degree (gcd a d[a] * gcd b d[b] * gcd c d[c]) = degree (gcd a d[a] * gcd b d[b]) + degree (gcd c d[c]),
    from degree_mul_eq_add_of_mul_ne_zero h1,
  have h3 : gcd a d[a] * gcd b d[b] ≠ 0,
    from ne_zero_of_mul_ne_zero_right h1,
  have h4 : degree (gcd a d[a] * gcd b d[b]) = degree (gcd a d[a]) + degree (gcd b d[b]),
    from degree_mul_eq_add_of_mul_ne_zero h3,
  rw [h2, h4],
end

private lemma h_wron 
(a b c : polynomial β)
(h_add : a + b = c)
(h_der : d[a] + d[b] = d[c])
: d[a] * b - a * d[b] = d[a] * c - a * d[c] :=
begin
  have h1 : d[a] * a + d[a] * b = d[a] * c,
    exact calc d[a] * a + d[a] * b = d[a] * (a + b) : by rw [mul_add]
    ... = _ : by rw h_add,
  have h2 : a * d[a] + a * d[b] = a * d[c],
    exact calc a * d[a] + a * d[b] = a * (d[a] + d[b]) : by rw [mul_add]
    ... = _ : by rw h_der,
  have h3 : d[a] * b - a * d[b] = d[a] * c - a * d[c],
    exact calc d[a] * b - a * d[b] = d[a] * b + (d[a] * a - d[a] * a) - a * d[b] : by simp
    ... = d[a] * b + d[a] * a - d[a] * a - a * d[b] : by simp
    ... = d[a] * c - (d[a] * a +  a * d[b]) : by simp [h1]
    ... = d[a] * c - (a * d[a] +  a * d[b]) : by rw [mul_comm _ a]
    ... = _ : by rw h2,
  exact h3
end


private lemma h_gcds_dvd 
(a b c : polynomial β)
(h_coprime_ab : coprime a b)
(h_coprime_bc : coprime b c)
(h_coprime_ca : coprime c a)
(h_dvd_wron_a : gcd a d[a] ∣ d[a] * b - a * d[b])
(h_dvd_wron_b : gcd b d[b] ∣ d[a] * b - a * d[b])
(h_dvd_wron_c : gcd c d[c] ∣ d[a] * b - a * d[b]):
  (gcd a d[a]) * (gcd b d[b]) * (gcd c d[c]) ∣ d[a] * b - a * d[b] :=
begin 
  apply mul_dvd_of_dvd_of_dvd_of_coprime,
  apply coprime_mul_of_coprime_of_coprime_of_coprime,
  exact coprime_gcd_derivative_gcd_derivative_of_coprime (h_coprime_ca.symm) _ _,
  exact coprime_gcd_derivative_gcd_derivative_of_coprime h_coprime_bc _ _,
  apply mul_dvd_of_dvd_of_dvd_of_coprime,
  exact coprime_gcd_derivative_gcd_derivative_of_coprime h_coprime_ab _ _,
  exact h_dvd_wron_a,
  exact h_dvd_wron_b,
  exact h_dvd_wron_c
end

private lemma degree_rad_pos  
(a b c : polynomial β)
(ha : a ≠ 0)
(hb : b ≠ 0)
(hc : c ≠ 0)
(h_constant : ¬(is_constant a ∧ is_constant b ∧ is_constant c)) :
degree (rad (a*b*c)) > 0 :=
begin
  apply gt_zero_of_ne_zero,
  rw [ne.def, degree_rad_eq_zero_iff_is_constant],
  simp only [not_and_distrib] at *,
  have : a * b ≠ 0,
    from mul_ne_zero ha hb,
  cases h_constant,
  { simp [not_is_constant_mul_of_not_is_constant_of_ne_zero, *]},
  cases h_constant,
  { simp [mul_comm a, not_is_constant_mul_of_not_is_constant_of_ne_zero, *]},
  { simp [mul_comm _ c, not_is_constant_mul_of_not_is_constant_of_ne_zero, *]}
end


theorem Mason_Stothers_special [field β]
  (h_char : characteristic_zero β)
  (a b c : polynomial β)
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0)
  (h_coprime_ab : coprime a b)
  (h_coprime_bc : coprime b c)
  (h_coprime_ca : coprime c a)
  (h_add : a + b = c)
  (h_constant : ¬(is_constant a ∧ is_constant b ∧ is_constant c)) :
  degree c < degree ( rad (a*b*c)) :=

begin
  have h_der_not_all_zero : ¬(d[a] = 0 ∧ d[b] = 0 ∧ d[c] = 0),
  {
    rw [derivative_eq_zero_iff_is_constant h_char, derivative_eq_zero_iff_is_constant h_char, derivative_eq_zero_iff_is_constant h_char],
    exact h_constant,
  },
  have h_der : d[a] + d[b] = d[c],
  {
    rw [←h_add, derivative_add],
  },
  have h_wron : d[a] * b - a * d[b] = d[a] * c - a * d[c],
    from  h_wron a b c h_add h_der,
  have h_dvd_wron_a : gcd a d[a] ∣ d[a] * b - a * d[b],
    from h_dvd_wron_a a b c,
  have h_dvd_wron_b : gcd b d[b] ∣ d[a] * b - a * d[b],
    from h_dvd_wron_b a b c,   
  have h_dvd_wron_c : gcd c d[c] ∣ d[a] * b - a * d[b],
    from h_dvd_wron_c a b c h_wron,
  have h_gcds_dvd : (gcd a d[a]) * (gcd b d[b]) * (gcd c d[c]) ∣ d[a] * b - a * d[b],
    from h_gcds_dvd a b c h_coprime_ab h_coprime_bc h_coprime_ca h_dvd_wron_a h_dvd_wron_b h_dvd_wron_c,
  have h_wron_ne_zero : d[a] * b - a * d[b] ≠ 0,
    from h_wron_ne_zero a b c h_coprime_ab h_coprime_ca h_der_not_all_zero h_wron,
  have h_deg_add : degree (gcd a d[a] * gcd b d[b] * gcd c d[c]) = degree (gcd a d[a]) + degree (gcd b d[b]) + degree (gcd c d[c]),
    from h_deg_add a b c h_wron_ne_zero h_gcds_dvd,
  have h_deg_add_le : degree (gcd a d[a]) + degree (gcd b d[b]) + degree (gcd c d[c]) ≤ degree a + degree b - 1,
  {
    rw [←h_deg_add],
    have h1 : degree (gcd a d[a] * gcd b d[b] * gcd c d[c]) ≤ degree (d[a] * b - a * d[b]),
      from degree_dvd h_gcds_dvd h_wron_ne_zero,
    exact nat.le_trans h1 (degree_wron_le),
  },
  have h_deg_c_le_1 : degree c ≤ (degree a - degree (gcd a d[a])) + (degree b - degree (gcd b d[b])) + (degree c - degree (gcd c d[c])) - 1,
    from rw_aux_1 a b c h_add h_constant h_deg_add_le,
  have h_le_rad : degree a - degree (gcd a d[a]) + (degree b - degree (gcd b d[b])) + (degree c - degree (gcd c d[c])) - 1 ≤
  degree (rad (a * b * c)) - 1,
    from rw_aux_2 ha hb hc h_coprime_ab h_coprime_bc h_coprime_ca,
  have h_ms : degree c ≤ degree ( rad (a*b*c)) - 1,
    from nat.le_trans h_deg_c_le_1 h_le_rad,
  have h_eq : degree ( rad (a*b*c)) - 1 + 1 = degree ( rad (a*b*c)),
  {
    have h_pos : degree ( rad (a*b*c)) > 0,
      from degree_rad_pos a b c ha hb hc h_constant,
    apply nat.succ_pred_eq_of_pos h_pos,
  },
  exact show degree c < degree ( rad (a*b*c)), from calc degree c + 1 ≤ degree ( rad (a*b*c) ) - 1 + 1 : by simp [h_ms]
    ... = degree ( rad (a*b*c)) : h_eq
end

--place in to_multiset
private lemma cons_ne_zero {γ : Type u}(a : γ)(s : multiset γ): a :: s ≠ 0 :=
begin
  intro h,
  have : a ∈ a :: s,
  {
    simp,
  },
  simp * at *,
end 

--place in to_multiset
--private?
private lemma map_eq_zero_iff_eq_zero {γ ζ : Type u} (s : multiset γ)(f: γ → ζ): map f s = 0 ↔ s = 0 :=
begin
  apply multiset.induction_on s,
  {
    simp * at *,
  },
  {
    intros a s h,
    split,
    {
      intro h1,
      simp * at *,
      have h2 : false,
        from cons_ne_zero _ _ h1,
      contradiction,
    },
    {
      intro h1,
      simp * at *,  
    },
  }
end

--structure?
lemma factors_eq_factors_of_associated {a b : polynomial β} (h : (a ~ᵤ b)): a.factors = b.factors :=
begin
  rw [factors_eq_map_monic_out_to_multiset_mk, factors_eq_map_monic_out_to_multiset_mk],
  rw [associated_iff_mk_eq_mk] at *,
  simp * at *,
end

@[simp] lemma rad_neg_eq_rad [field β] (p : polynomial β) : rad (-p) = rad p :=
begin
  have hp : (p ~ᵤ (-p)),
    from associated_neg _,
  have h1 : p.factors = (-p).factors,
    from factors_eq_factors_of_associated hp,
  rw [rad, rad, h1],
end

@[simp] lemma coprime_neg_iff_coprime_left {a b : polynomial β} : coprime (-a) b ↔ coprime a b :=
begin
  split,
  {
    intro h,
    apply coprime_of_coprime_of_associated_left h (associated_neg _),
  },
  {
    intro h,
    apply coprime_of_coprime_of_associated_left h (associated_neg _).symm,
  }
end

@[simp] lemma coprime_neg_iff_coprime_right {a b : polynomial β} : coprime a (-b) ↔ coprime a b :=
begin
  split,
  {
    intro h,
    apply coprime_of_coprime_of_associated_right h (associated_neg _),
  },
  {
    intro h,
    apply coprime_of_coprime_of_associated_right h (associated_neg _).symm,
  }
end

private lemma neg_eq_zero_iff_eq_zero {a : polynomial β} : -a = 0 ↔ a = 0 :=
begin
  split,
  {
    intro h,
    exact calc a = -(-a) : by simp
      ... = - (0) : by rw h
      ... = _ : by simp
  },
  {
    intro h,
    simp *,
  }
end

private lemma neg_ne_zero_iff_ne_zero {a : polynomial β} : -a ≠ 0 ↔ a ≠ 0 :=
  not_iff_not_of_iff neg_eq_zero_iff_eq_zero
  
local attribute [simp] is_constant_neg_iff_is_constant

theorem Mason_Stothers_case_c [field β]
  (h_char : characteristic_zero β)
  (a b c : polynomial β)
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0)
  (h_coprime_ab : coprime a b)
  (h_coprime_bc : coprime b c)
  (h_coprime_ca : coprime c a)
  (h_add : a + b + c = 0)
  (h_constant : ¬(is_constant a ∧ is_constant b ∧ is_constant c)): --You can do this one by cc? simpa [and.comm, and.left_comm, and.assoc] using h_constant
  degree c < degree ( rad (a*b*c)) :=
  begin
    have h_c : degree (-c) < degree ( rad (a*b*(-c))),
    {
      have h_add : a + b = - c,
      {
        exact calc a + b = a + b + (c - c) : by simp 
          ... = a + b + c - c : by simp
          ... = 0 - c : by rw [h_add]
          ... = _ : by simp,
      },
      rw ←(is_constant_neg_iff_is_constant c) at h_constant, --The argument should not have been implicit
      apply Mason_Stothers_special h_char _ _ _ ha hb _ h_coprime_ab _ _ h_add h_constant,--We need relPrime.symm in general 
      {
        simp [neg_ne_zero_iff_ne_zero, *],
      },
      have : coprime b (-c),--Rather as rw, rather as simp rule, coprime a -c = coprime a c
        from coprime_neg_iff_coprime_right.2 h_coprime_bc,
      exact this,
      have : coprime (-c) a,
        from coprime_neg_iff_coprime_left.2 h_coprime_ca,
      exact this,
    },
    have h_neg_abc: a * b * -c = - (a * b * c),
    {
      simp,
    },
    rw [degree_neg, h_neg_abc, rad_neg_eq_rad] at h_c,
    exact h_c,
  end


theorem Mason_Stothers_case_a [field β]
  (h_char : characteristic_zero β)
  (a b c : polynomial β)
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0)
  (h_coprime_ab : coprime a b)
  (h_coprime_bc : coprime b c)
  (h_coprime_ca : coprime c a)
  (h_add : a + b + c = 0)
  (h_constant : ¬(is_constant a ∧ is_constant b ∧ is_constant c)):
  degree a < degree ( rad (a*b*c)) :=
  begin
    have h_a : degree (-a) < degree ( rad (b*c*(-a))),
    {
      have h_add_1 : b + c + a = 0,
      {
        simpa [add_comm, add_assoc] using h_add,
      },
      have h_add_2 : b + c = - a,
      {
        exact calc b + c = b + c + (a - a) : by simp 
          ... = b + c + a - a : by simp
          ... = 0 - a : by rw [h_add_1]
          ... = _ : by simp,
      },
      have h_constant_2 : ¬(is_constant b ∧ is_constant c ∧ is_constant (-a)),
      {
        simpa [(is_constant_neg_iff_is_constant a), and_comm, and_assoc] using h_constant,
        intros h1 h2,
        simp *,
      },
      apply Mason_Stothers_special h_char b c (-a) hb hc (neg_ne_zero_iff_ne_zero.2 ha) h_coprime_bc _ _ h_add_2 h_constant_2,
      {
        simp *,
      },
      {
        simp *,
      },
    },
    have h_neg_abc: b * c * -a = - (a * b * c),
    {
      simp,
      exact calc b * c * a = b * (a * c) : by rw [mul_assoc, mul_comm c a]
        ... = _ : by rw [←mul_assoc, mul_comm b a],      
    },
    rw [degree_neg, h_neg_abc, rad_neg_eq_rad] at h_a,
    exact h_a,
  end

theorem Mason_Stothers_case_b [field β]
  (h_char : characteristic_zero β)
  (a b c : polynomial β)
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0)
  (h_coprime_ab : coprime a b)
  (h_coprime_bc : coprime b c)
  (h_coprime_ca : coprime c a)
  (h_add : a + b + c = 0)
  (h_constant : ¬(is_constant a ∧ is_constant b ∧ is_constant c)):
  degree b < degree ( rad (a*b*c)) :=
  begin
    have h_b : degree (-b) < degree ( rad (a*c*(-b))),
    {
      have h_add_1 : a + c + b = 0,
      {
        simpa [add_comm, add_assoc] using h_add,
      },
      have h_add_2 : a + c = - b,
      {
        exact calc a + c = a + c + (b - b) : by simp 
          ... = a + c + b - b : by simp
          ... = 0 - b : by rw [h_add_1]
          ... = _ : by simp,
      },
      have h_constant_2 : ¬(is_constant a ∧ is_constant c ∧ is_constant (-b)),
      {
        simpa [(is_constant_neg_iff_is_constant b), and_comm, and_assoc] using h_constant,
      },
      apply Mason_Stothers_special h_char a c (-b) ha hc (neg_ne_zero_iff_ne_zero.2 hb) h_coprime_ca.symm _ _ h_add_2 h_constant_2,
      {
        simp [h_coprime_bc.symm, *],
      },
      {
        simp [h_coprime_ab.symm, *],
      }
    },    
    have h_neg_abc: a * c * -b = - (a * b * c),
    {
      simp,
      exact calc a * c * b = a * (b * c) : by rw [mul_assoc, mul_comm c b]
        ... = _ : by rw [←mul_assoc],      
    },
    rw [degree_neg, h_neg_abc, rad_neg_eq_rad] at h_b,
    exact h_b,
  end

theorem Mason_Stothers [field β]
  (h_char : characteristic_zero β)
  (a b c : polynomial β)
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0)
  (h_coprime_ab : coprime a b)
  (h_coprime_bc : coprime b c)
  (h_coprime_ca : coprime c a)
  (h_add : a + b + c = 0)
  (h_constant : ¬(is_constant a ∧ is_constant b ∧ is_constant c)):
  max (degree a) (max (degree b) (degree c)) < degree ( rad (a*b*c)) :=
begin
  have h_a: degree a < degree ( rad (a*b*c)), 
    from Mason_Stothers_case_a h_char a b c ha hb hc h_coprime_ab h_coprime_bc h_coprime_ca h_add h_constant,
  have h_b: degree b < degree ( rad (a*b*c)),
    from Mason_Stothers_case_b h_char a b c ha hb hc h_coprime_ab h_coprime_bc h_coprime_ca h_add h_constant,
  have h_c: degree c < degree ( rad (a*b*c)),
    from Mason_Stothers_case_c h_char a b c ha hb hc h_coprime_ab h_coprime_bc h_coprime_ca h_add h_constant,
  apply max_lt h_a,
  apply max_lt h_b h_c,
end

end mason_stothers