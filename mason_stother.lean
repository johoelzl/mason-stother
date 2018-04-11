
#exit

-- the to be Mason-Stother formalization
-- Authors Johannes & Jens

--Defining the gcd
import poly
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
--variables  [algebraically_closed_field β] -- Should be an instance of algebraically closed.
open finsupp

def c_fac (p : polynomial β) : β := some ( polynomial_fac_finsupp p)

--Looks ugly still
def factors (p : polynomial β) : polynomial β →₀ ℕ :=
classical.some (some_spec $ polynomial_fac_finsupp p)

lemma factors_irred (p : polynomial β) : ∀x ∈ (factors p).support, irreducible x :=
assume x h, ((some_spec $ some_spec $ polynomial_fac_finsupp p).2 x h).1

--(some_spec $ some_spec $ polynomial_fac_finsupp p).2
def factors_monic (p : polynomial β) : ∀x ∈ (factors p).support, monic x :=
λx h, ((some_spec $ some_spec $ polynomial_fac_finsupp p).2 x h).2

lemma h_factors (p : polynomial β) :  p = C (c_fac p) * ((finsupp.prod (factors p) (λ k n, k ^n) ) ) ∧ (∀x∈(factors p).support, irreducible x ∧ monic x)   :=
some_spec (some_spec ( polynomial_fac_finsupp p))

def facs_to_pow_min_one (p : polynomial β →₀ ℕ ) : finset (polynomial β):= p.support.image (λ a, a^(p a - 1))

open classical
section algebraically_closed

--It might be good to remove the attribute to domain of integral domain?
def rad (p : polynomial β) : polynomial β :=
finset.prod (finsupp.support (factors p)) id --The radiacal

lemma rad_ne_zero {p : polynomial β} : rad p ≠ 0 :=
begin
  rw [rad],
  apply prod_ne_zero_of_forall_mem_ne_zero,
  intros x h1,
  have h2 : irreducible x,
  {apply factors_irred p, exact h1},
  exact and.elim_left h2,
end



lemma degree_rad_eq_sum_support_degree {f : polynomial β} :
  degree (rad f) = (finset.sum (finsupp.support (factors f)) degree ) :=
begin
  rw rad,
  have h1 : finset.prod (support (factors f)) id ≠ 0,
  {
    apply prod_ne_zero_of_forall_mem_ne_zero,
    intros x h1,
    have : irreducible x,
    from factors_irred f x h1,
    exact and.elim_left this,
  },
  rw degree_prod_eq_sum_degree_of_prod_ne_zero h1
end

lemma prod_pow_min_on_ne_zero {f : polynomial β} :
  finsupp.prod (to_finsupp_pow_min_one (factors f)) (λ (x : ~β) (y : ℕ), x ^ y) ≠ 0 :=
begin
  rw [finsupp.prod],
  refine prod_ne_zero_of_forall_mem_ne_zero' _ _ _ _,
  {
    intros x h2,
    exact pow_ne_zero _ h2,
  },
  exact _root_.zero_ne_one,
  {
    intros x h2,
    have h3: x ∈ support (factors f),
    from finset.mem_of_subset support_pow_min_one_subset_support h2,
    have h4 : irreducible x,
    from factors_irred f x h3,
    exact and.elim_left h4
  }
end

lemma degree_eq_add_degree_rad_degree_pow_min_one {f : polynomial β} :
  degree (finsupp.prod (factors f) (λ x n, x^n)) =
    degree (finsupp.prod (to_finsupp_pow_min_one (factors f)) (λ (x : ~β) (y : ℕ), x ^ y)) +
    degree (rad f) :=
begin
--!!!!! we need to add 'in' when using conv.
  have h1 : (support (to_finsupp_pow_min_one (factors f))) ⊆ support (factors f),
  {
    from support_pow_min_one_subset_support,
  },
  have h2 : (support (to_finsupp_pow_min_one (factors f))) ∪ (support (factors f) \ (support (to_finsupp_pow_min_one (factors f)))) = support (factors f),
  from finset.union_sdiff_of_subset h1,
  have h3 : ∀x, x ∈ support (factors f) \ support (to_finsupp_pow_min_one (factors f)) ↔ (factors f) x = 1,
  from  mem_sdiff_support_support_pow_min_one_iff_eq_one,
  have h4 : finset.prod (support (to_finsupp_pow_min_one (factors f)))(λ (x : ~β), x ^ (to_finsupp_pow_min_one (factors f)) x * x) =
         finset.prod (support (to_finsupp_pow_min_one (factors f)))
         (λ (x : ~β), x ^ (factors f) x),
  {
    apply finset.prod_congr,
    exact rfl,
    intros x h4,
    rw [mul_comm _ x, ←pow_succ, to_finsupp_pow_min_one, finsupp.map_range_apply],
    have h5 : (factors f) x ≠ 0,
    {
      have h5 : x ∈ support (factors f),
      from finset.mem_of_subset h1 h4,
      rw [finsupp.mem_support_iff] at h5,
      exact h5,
    },
    have h6 : (factors f) x ≥ 1,
    {
      have h6 : 0 < (factors f) x,
      from nat.pos_of_ne_zero h5,
      have h7 : nat.succ 0 ≤ (factors f) x,
      from nat.succ_le_of_lt h6,
      exact h7
    },
    rw [nat.sub_add_cancel h6],
  },
  have h5 :  finset.prod (support (factors f) \ support (to_finsupp_pow_min_one (factors f))) (λ (x : ~β), x) = finset.prod (support (factors f) \ support (to_finsupp_pow_min_one (factors f))) (λ (x : ~β), x ^ (factors f) x) ,
  {
    apply finset.prod_congr,
    exact rfl,
    intro x,
    rw h3 x,
    intro h5,
    rw h5,
    simp only [pow_one x],
  },
  have h6 : Π₀ (to_finsupp_pow_min_one (factors f)) (λ (x : ~β) (y : ℕ), x ^ y) * rad f ≠ 0,
  {
    apply mul_ne_zero,
    exact prod_pow_min_on_ne_zero,
    exact rad_ne_zero
  },
  have h7 : support (to_finsupp_pow_min_one (factors f)) ∩
    (support (factors f) \ support (to_finsupp_pow_min_one (factors f))) = ∅,
  {simp},

  conv
  {
    to_rhs,
    rw [←degree_mul_eq_add_of_mul_ne_zero h6, rad, finsupp.prod, ←h2, finset.prod_union h7, ←mul_assoc, ←finset.prod_mul_distrib],
    simp,
    rw [h4, h5, ←finset.prod_union h7, finset.union_comm _ _, finset.sdiff_union_of_subset h1, ←finsupp.prod],
  }
end


--More general, where does it belong?
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


lemma one_le_of_ne_zero {n : ℕ } (h : n ≠ 0) : 1 ≤ n :=
begin
  let m := some (nat.exists_eq_succ_of_ne_zero h),
  have h1 : n = nat.succ m,
  from some_spec (nat.exists_eq_succ_of_ne_zero h),
  rw [h1, nat.succ_le_succ_iff], --simp * failes here
  exact nat.zero_le _,

end




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
            rw [degree_neg],
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
            exact _root_.one_le_of_ne_zero h2,
          },
          have h6 : (degree (a * d[b])) ≤ degree a + degree b - 1,
          {
            apply nat.le_trans degree_mul,
            rw [nat.add_sub_assoc],
            apply add_le_add_left,
            exact degree_derivative_le,
            exact _root_.one_le_of_ne_zero h4,
          },
          exact max_le h5 h6,
        }
      }
    }
  }
end



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
      have h2: (C (c_fac f) * finsupp.prod (factors f) (λ (k : ~β) (n : ℕ), k ^ n) ≠ 0), --Had a lemma for this?
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

--We don't use factors below this point.

--needs cleaning

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
  exact dvd_of_dvd_mul_of_coprime h7 (coprime_comm h1),
  have h9 : d[b] = 0,
  from derivative_eq_zero_of_dvd_derivative_self h8,
  exact ⟨h6, h9⟩,
end

lemma coprime_gcd_derivative_gcd_derivative_of_coprime {a b : polynomial β} (h : coprime a b) : coprime (gcd a d[a]) (gcd b d[b]) :=
sorry

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

--We will need extra conditions here
lemma degree_rad_add {a b c : polynomial β}: degree (rad a) + degree (rad b) + degree (rad c) ≤ degree (rad (a * b * c)) :=
begin
  admit,
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
      admit --admit here

    }
  }
end

--h_deg_c_le_1
lemma rw_aux_1 [field β]
  (h_char : characteristic_zero β)
  (a b c : polynomial β)
  (h_coprime_ab : coprime a b)
  (h_coprime_bc : coprime b c)
  (h_coprime_ca : coprime c a)
  (h_add : a + b = c)
  (h_constant : ¬(is_constant a ∧ is_constant b ∧ is_constant c))
  (h_deg_add_le : degree (gcd a d[a]) + degree (gcd b d[b]) + degree (gcd c d[c]) ≤ degree a + degree b - 1) :
  degree c ≤
    (degree a - degree (gcd a d[a])) +
    (degree b - degree (gcd b d[b])) +
    (degree c - degree (gcd c d[c])) - 1 :=
have 1 ≤ degree a + degree b, from sorry,
have h : ∀p:polynomial β, degree (gcd p d[p]) ≤ degree p, from sorry,
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
  (h_char : characteristic_zero β)
  (a b c : polynomial β)
  (h_coprime_ab : coprime a b)
  (h_coprime_bc : coprime b c)
  (h_coprime_ca : coprime c a)
  (h_add : a + b = c)
  (h_constant : ¬(is_constant a ∧ is_constant b ∧ is_constant c))
  (h_rad: rad(a)*rad(b)*rad(c)= rad(a*b*c))
   : degree a - degree (gcd a d[a]) + (degree b - degree (gcd b d[b])) + (degree c - degree (gcd c d[c])) - 1 ≤
  degree (rad (a * b * c)) - 1:=
begin
  apply nat.sub_le_sub_right,
  have h_rad:  degree(rad(a))+degree(rad(b))+degree(rad(c)) ≤ degree(rad(a*b*c)),
    from sorry,
  refine nat.le_trans _ h_rad,
  apply nat.add_mono _ (Mason_Stothers_lemma' c),
  apply nat.add_mono (Mason_Stothers_lemma' a) (Mason_Stothers_lemma' b),
end



theorem Mason_Stothers [field β]
  (h_char : characteristic_zero β)
  (a b c : polynomial β)
  (h_coprime_ab : coprime a b)
  (h_coprime_bc : coprime b c)
  (h_coprime_ca : coprime c a)
  (h_add : a + b = c)
  (h_constant : ¬(is_constant a ∧ is_constant b ∧ is_constant c)) :
  degree c ≤ degree ( rad (a*b*c)) - 1 :=

begin
  have h_der_not_all_zero : ¬(d[a] = 0 ∧ d[b] = 0 ∧ d[c] = 0),
  {
    rw [derivative_eq_zero_iff_is_constant, derivative_eq_zero_iff_is_constant, derivative_eq_zero_iff_is_constant],
    exact h_constant,
    exact h_char, -- Should be written down shorter
    exact h_char,
    exact h_char,
  },
  have h_der : d[a] + d[b] = d[c],
  {
    rw [←h_add, derivative_add],
  },
  have h_wron : d[a] * b - a * d[b] = d[a] * c - a * d[c],
  {
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
  },
  have h_dvd_wron_a : gcd a d[a] ∣ d[a] * b - a * d[b],
  {
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
  },
  have h_dvd_wron_b : gcd b d[b] ∣ d[a] * b - a * d[b],
  {
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
  },

  have h_dvd_wron_c : gcd c d[c] ∣ d[a] * b - a * d[b],
  {
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
  },
  have h_gcds_dvd : (gcd a d[a]) * (gcd b d[b]) * (gcd c d[c]) ∣ d[a] * b - a * d[b],
  {
    apply mul_dvd_of_dvd_of_dvd_of_coprime,
    apply coprime_mul_of_coprime_of_coprime_of_coprime,
    exact coprime_gcd_derivative_gcd_derivative_of_coprime (coprime_comm h_coprime_ca),
    exact coprime_gcd_derivative_gcd_derivative_of_coprime h_coprime_bc,
    exact coprime_gcd_derivative_gcd_derivative_of_coprime h_coprime_ca,
    apply mul_dvd_of_dvd_of_dvd_of_coprime,
    exact coprime_gcd_derivative_gcd_derivative_of_coprime h_coprime_ab,
    exact h_dvd_wron_a,
    exact h_dvd_wron_b,
    exact h_dvd_wron_c
  },
  have h_wron_ne_zero : d[a] * b - a * d[b] ≠ 0,
  {
    by_contradiction h1,
    rw not_not at h1,
    have h_a_b : d[a] = 0 ∧ d[b] = 0,
    from derivative_eq_zero_and_derivative_eq_zero_of_coprime_of_wron_eq_zero h_coprime_ab h1,
    have h2 : d[a] * c - a * d[c] = 0,
    {rw [←h_wron, h1]},
    have h_a_c : d[a] = 0 ∧ d[c] = 0,
    from derivative_eq_zero_and_derivative_eq_zero_of_coprime_of_wron_eq_zero (coprime_comm h_coprime_ca) h2,
    have h3 : (d[a] = 0 ∧ d[b] = 0 ∧ d[c] = 0),
    exact ⟨and.elim_left h_a_b, and.elim_right h_a_b, and.elim_right h_a_c⟩,
    contradiction
  },
  have h_deg_add : degree (gcd a d[a] * gcd b d[b] * gcd c d[c]) = degree (gcd a d[a]) + degree (gcd b d[b]) + degree (gcd c d[c]),
  {
    have h1 : gcd a d[a] * gcd b d[b] * gcd c d[c] ≠ 0,
    from ne_zero_of_dvd_ne_zero h_gcds_dvd h_wron_ne_zero,
    have h2 : degree (gcd a d[a] * gcd b d[b] * gcd c d[c]) = degree (gcd a d[a] * gcd b d[b]) + degree (gcd c d[c]),
    from degree_mul_eq_add_of_mul_ne_zero h1,
    have h3 : gcd a d[a] * gcd b d[b] ≠ 0,
    from ne_zero_of_mul_ne_zero_right h1,
    have h4 : degree (gcd a d[a] * gcd b d[b]) = degree (gcd a d[a]) + degree (gcd b d[b]),
    from degree_mul_eq_add_of_mul_ne_zero h3,
    rw [h2, h4]
  },
  have h_deg_add_le : degree (gcd a d[a]) + degree (gcd b d[b]) + degree (gcd c d[c]) ≤ degree a + degree b - 1,
  {
    rw [←h_deg_add],
    have h1 : degree (gcd a d[a] * gcd b d[b] * gcd c d[c]) ≤ degree (d[a] * b - a * d[b]),
    from degree_dvd h_gcds_dvd h_wron_ne_zero,
    exact nat.le_trans h1 (degree_wron_le),
  },--needs cleaning
  have h_deg_c_le_1 : degree c ≤ (degree a - degree (gcd a d[a])) + (degree b - degree (gcd b d[b])) + (degree c - degree (gcd c d[c])) - 1,
  {
    have h1 : degree c + (degree (gcd a d[a]) + degree (gcd b d[b]) + degree (gcd c d[c])) ≤ degree c + (degree a + degree b - 1),
    from nat.add_le_add_left h_deg_add_le _,
    have h2 : degree c + (degree (gcd a d[a]) + degree (gcd b d[b]) + degree (gcd c d[c])) - (degree (gcd a d[a]) + degree (gcd b d[b]) + degree (gcd c d[c]))
    ≤ degree c + (degree a + degree b - 1) - (degree (gcd a d[a]) + degree (gcd b d[b]) + degree (gcd c d[c])),
    from nat.sub_le_sub_right h1 _,
    have h3 : degree c + (degree (gcd a d[a]) + degree (gcd b d[b]) + degree (gcd c d[c])) - (degree (gcd a d[a]) + degree (gcd b d[b]) + degree (gcd c d[c])) = degree c,
    {--twice h3?

      have h3 : degree c + (degree (gcd a d[a]) + degree (gcd b d[b]) + degree (gcd c d[c])) =
      degree c + (degree (gcd c d[c])) + (degree (gcd b d[b]) + degree (gcd a d[a]) ),
      {
        simp [add_assoc, add_comm],
      },
      rw [h3],
      --rw [add_comm (degree (gcd b d[b])) (degree (gcd c d[c]))],
      --rw [←add_assoc, add_comm (degree (gcd a d[a])) _],
      rw [←nat.sub_sub, ←nat.sub_sub], --should use tactic comb here
      have h4 : degree c + degree (gcd c d[c]) + (degree (gcd b d[b]) + degree (gcd a d[a])) =
      degree c + degree (gcd c d[c]) + degree (gcd b d[b]) + degree (gcd a d[a]),
      {
        simp [add_comm],
      },
      rw h4,
      rw [nat.add_sub_assoc, nat.sub_self _, nat.add_zero ], --tactic comb
      rw [nat.add_sub_assoc, nat.sub_self _, nat.add_zero],
      rw [nat.add_sub_assoc, nat.sub_self _, nat.add_zero],
      exact nat.le_refl _,
      exact nat.le_refl _,
      exact nat.le_refl _,
    },
    rw h3 at h2,
    have h4 : degree c + (degree a + degree b - 1) - (degree (gcd a d[a]) + degree (gcd b d[b]) + degree (gcd c d[c]))
    = degree a - degree (gcd a d[a]) + (degree b - degree (gcd b d[b])) + (degree c - degree (gcd c d[c])) - 1,
    {
      have h4 : degree c + (degree a + degree b - 1) = degree c + degree b + degree a - 1,
      {
       rw [add_comm (degree a) _, ← nat.add_sub_assoc, add_assoc],
       apply _root_.one_le_of_ne_zero,
       have h4 : degree b + degree a ≠ 0, --cleaning
       {
         rw [is_constant_iff_degree_eq_zero, is_constant_iff_degree_eq_zero, is_constant_iff_degree_eq_zero] at h_constant,
         rw [not_and_distrib, not_and_distrib] at h_constant,
         cases h_constant,
         {
           by_contradiction h4,
           simp at h4,
           rw [add_eq_zero_iff_eq_zero_of_nonneg] at h4,
           exact h_constant (and.elim_left h4),
           exact nat.zero_le _,
           exact nat.zero_le _,
         },
         {
           cases h_constant,
           {
            by_contradiction h4,
            simp at h4,
            rw [add_eq_zero_iff_eq_zero_of_nonneg] at h4,
            exact h_constant (and.elim_right h4),
            exact nat.zero_le _,
            exact nat.zero_le _,
           },
           {
             by_contradiction h4,
             simp at h4,
             have h5 : degree c ≤ max (degree a) (degree b),
             {
               rw ←h_add,
               exact degree_add,
             },
             rw [add_eq_zero_iff_eq_zero_of_nonneg] at h4,
             rw [and.elim_left h4, and.elim_right h4] at h5,
             simp at h5,
             have h6 : degree c = 0,
             from nat.eq_zero_of_le_zero h5,
             contradiction,
             exact nat.zero_le _,
             exact nat.zero_le _,
           }
         }
       },
       exact h4,
      },
      rw [h4, nat.sub_sub _ 1 _, add_comm 1 _, ←nat.sub_sub _ _ 1],
      rw [←nat.sub_sub, ←nat.sub_sub],
      rw [nat.add_sub_assoc],
      rw [add_assoc, add_comm (degree b) _, ← add_assoc, add_comm (degree c) _, nat.add_sub_assoc],
      rw [add_assoc, add_comm (degree c) _, ←add_assoc, nat.add_sub_assoc],
      exact degree_gcd_derivative_le_degree,
      exact degree_gcd_derivative_le_degree,
      exact degree_gcd_derivative_le_degree,

    },
    rw h4 at h2,
    exact h2,
  },
  have h_le_rad : degree a - degree (gcd a d[a]) + (degree b - degree (gcd b d[b])) + (degree c - degree (gcd c d[c])) - 1 ≤
  degree (rad (a * b * c)) - 1,
  {
    have h1 : degree a - degree (gcd a d[a]) + (degree b - degree (gcd b d[b])) + (degree c - degree (gcd c d[c])) - 1 ≤
    degree (rad a ) + (degree b - degree (gcd b d[b])) + (degree c - degree (gcd c d[c])) - 1,
    {
      have h1a : degree a - degree (gcd a d[a]) + (degree b - degree (gcd b d[b])) + (degree c - degree (gcd c d[c])) - 1 =
      degree a - degree (gcd a d[a]) + ((degree b - degree (gcd b d[b])) + (degree c - degree (gcd c d[c])) - 1),
      {
        rw [add_assoc, nat.add_sub_assoc],
        exact MS_aux_1 h_char h_add h_constant,
      },
      have h1b : degree (rad a) + (degree b - degree (gcd b d[b])) + (degree c - degree (gcd c d[c])) - 1 =
      degree (rad a) + ((degree b - degree (gcd b d[b])) + (degree c - degree (gcd c d[c])) - 1),
      {
        rw [add_assoc, nat.add_sub_assoc],
        exact MS_aux_1 h_char h_add h_constant,
      },
      rw [h1a, h1b],
      apply @nat.add_le_add_right (degree a - degree (gcd a d[a])) (degree (rad a)),
      exact Mason_Stothers_lemma' _,
    },
    apply nat.le_trans h1,
    rw add_comm (degree (rad a)) _,
    have h2 : degree b - degree (gcd b d[b]) + degree (rad a) + (degree c - degree (gcd c d[c])) - 1 ≤
    degree (rad b) + degree (rad a) + (degree c - degree (gcd c d[c])) - 1,
    {
      have h2a : degree b - degree (gcd b d[b]) + degree (rad a) + (degree c - degree (gcd c d[c])) - 1 = degree b - degree (gcd b d[b]) + (degree (rad a) + (degree c - degree (gcd c d[c])) - 1),
      {
        rw [add_assoc, nat.add_sub_assoc],
        exact MS_aux_2 h_char h_add h_constant,
      },
      have h2b : degree (rad b) + degree (rad a) + (degree c - degree (gcd c d[c])) - 1 =
      degree (rad b) + (degree (rad a) + (degree c - degree (gcd c d[c])) - 1),
      {
        rw [add_assoc, nat.add_sub_assoc],
        exact MS_aux_2 h_char h_add h_constant,
      },
      rw [h2a, h2b],
      apply nat.add_le_add_right,
      exact Mason_Stothers_lemma' _,
    },
    apply nat.le_trans h2,
    rw [add_assoc, add_comm (degree (rad a)) _, ← add_assoc, add_comm (degree (rad b)) _],
    have h3 : degree c - degree (gcd c d[c]) + degree (rad b) + degree (rad a) - 1 ≤
    degree (rad c) + degree (rad b) + degree (rad a) - 1,
    {
      have h3a : degree c - degree (gcd c d[c]) + degree (rad b) + degree (rad a) - 1 = degree c - degree (gcd c d[c]) + (degree (rad b) + degree (rad a) - 1),
      {
        rw [add_assoc, nat.add_sub_assoc],
        admit, -- admit here
      },
      have h3b : degree (rad c) + degree (rad b) + degree (rad a) - 1  =
      degree (rad c) + (degree (rad b) + degree (rad a) - 1),
      {
        rw [add_assoc, nat.add_sub_assoc],
        admit, -- admit here
      },
      rw [h3a, h3b],
      apply nat.add_le_add_right,
      exact Mason_Stothers_lemma' _,
    },
    apply nat.le_trans h3,
    rw [add_comm (degree (rad c)) _, add_assoc, add_comm (degree (rad c)) _, ← add_assoc, add_comm (degree (rad b)) _],
    apply nat.sub_le_sub_right,
    exact degree_rad_add,
  },
  exact nat.le_trans h_deg_c_le_1 h_le_rad,
end

end algebraically_closed
