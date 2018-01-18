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


variable {α : Type u}

attribute [instance] field.to_unique_factorization_domain --correct?


variables [comm_semiring α]



-- so every polynomial has a GCD? Shouldn't there be some restriction on α
--axiom gcd_ax : ∀ a b : polynomial α,( ∃( d : polynomial α ), (is_gcd a b d))


--@[instance] constant polynomial.has_gcd : has_gcd (polynomial α)

--def monic (p : polynomial α) : Prop := leading_coeff p = 1
--Assume has_gcd on polynomials
 --∈ set.range (units.val : _ → polynomial α)


--We need to define the radical and the number of distinct roots of a polynomial
--First define roots


structure roots_of (a : polynomial α):= --Can this be made as a set directly?
(val : α)(h1 : root_of a val)

def roots_of_as_set (a : polynomial α) := set_of (root_of a)
--Can we proof this set is finite?

--Can I define the radical?

--Proof linear factor iff root, makes use of the division algorithm. Hence that polynomials are a euclidian ring.

section field

variable β : Type u

variable [field β] --Again an anoying diamond porblem with field to UFD







open finsupp

def lin_fac {β : Type u} [field β] (q : β) : polynomial β := X - C q

lemma deg_ln_fac {q : β} : degree (X + (- C q)) = 1 :=
have one_le_deg : 1 ≤ degree (X + (- C q)), from
    have h1: ((X : polynomial β) + (- C q)) 1 = (1:β),  -- Type annotation is needed here, otherwise + will fail.
    begin
      show (X : polynomial β) 1 + - (C q : polynomial β) 1 = (1:β),
      rw [X, single_eq_same, C, single_eq_of_ne]; simp
    end,
    have ((X : polynomial β) + (- C q)) 1 ≠ 0, from calc
        ((X : polynomial β) + (- C q)) 1 = 1 : h1
        ... ≠ 0 : one_ne_zero,
    le_degree this,
have ((0 : β ) ≠ (1 : β)), from zero_ne_one,
have h_deg_X : degree X = 1, from  degree_X this,
have degree (C q) = 0, from degree_C,
have h_deg_neg_C :degree (- C q) = 0, by rw [degree_neg, this],
have ha: degree (X + (- C q)) ≤ 1, from
  calc
    degree (X + (- C q)) ≤ max (degree (X)) (degree (- C q)) : degree_add
    ... ≤ max 1 0 : by rw [h_deg_X, h_deg_neg_C ]
    ... = 1 : max_eq_left zero_le_one,
have 1 ≤ degree (X + (- C q)), from (one_le_deg),
show degree (X + (- C q)) = 1, from le_antisymm ha this


open euclidean_domain

lemma degree_ne_zero_ne_zero2 {f : polynomial β } : degree f ≠ 0 → f ≠ 0 :=--I want to apply normal by_cpntradiction here, but I don't know how to apply that, due to ambiguous overload.
begin intro, apply (@classical.by_contradiction (f ≠ 0) _), intro,
have h3: (f = 0), from iff.elim_left (@not_not _ (classical.prop_decidable _)) a_1,
have h4: degree f = 0, calc degree f = degree 0 : by rw [h3] ... = 0 : degree_zero,
apply a h4
 end

--Why is there no instance for has subtract?
lemma root_iff_lin_fac : ∀p : polynomial β, ∀k:β, (root_of p k) ↔ (X - C k ∣ p) :=
begin intros, apply iff.intro,
{intro, --apply (exists.elim a), intros,
  -- have h1 : 1 ≠ 0, from dec_trivial,
  have h2 :  degree (X + (- (C k ))) ≠ 0,
  from calc degree (X + (- (C k))) = 1 : @deg_ln_fac _ _ k
  ... ≠ 0 : one_ne_zero,
  have h3 : (X + (- (C k))) ≠ 0, from degree_ne_zero_ne_zero h2,--Mogelijk gaat deze fout omdat het lemma niet was gedefinieerd voor een integral domain.
  --Lemma is gedefinieerd voor semiring, maar mogelijk is het niet zo dat de integral domain kan worden omgezet in een semiring?
  -- Ik zie dat er wel een instance is met naar comm_semi_ring vanaf comm_ring. En een comm_semiring is een ring.
  have h4 : (∃ q : polynomial β, ∃ r : polynomial β ,( (p = q *  (X + (- (C k))) + r) ∧ ((r = 0)  ∨  ( (norm r ) < (norm (X + (- (C k))))) )  ) ),
  apply @h_norm (polynomial β) _ p (X + (- (C k))) (degree_ne_zero_ne_zero2 β  h2) , --dom.h p (X + (- (C α))) h3
  --Er gaat gebeurt iets geks met de type universes, want degree h2, zit in type universe max 1 (u+1), en de andere zir in (u+1).
  --Of mogelijk heeft het te maken met field, integral_domain enzovoort. Maar snapt ie zelf dan niet dat max 1 (1+u) = 1 + u?
  --Mogelijk gaat het fout door het gebruik van de classical axioms, en dat je dat dan overal moet doen?? Zie maar degree_ne_zero2
admit
} , {admit} end


lemma finite_roots {a : polynomial β} : set.finite (roots_of_as_set a):= sorry --How do we do an induction on the degree?

end field

variable {β : Type u}
variables [field β]
--variables  [algebraically_closed_field β] -- Should be an instance of algebraically closed.
open finsupp



--axiom roots (p : polynomial β) : β →₀ ℕ Problem, because the 0 polynomial can have infinite roots.
--axiom eq_prod_lin_fac_roots (p : polynomial β) : ∃ c : β , p = C c * (finsupp.prod (roots p) (λ k n, ( (X - C k ) ^n) )  )

--The more general setting, avoids problem with the roots of the zero polynomial
axiom monic_irr (p : polynomial β) : polynomial β →₀ ℕ
axiom irr_poly_irreducible (p : polynomial β) : ∀x ∈ (monic_irr p).support, irreducible x
axiom irr_poly_monic (p : polynomial β) : ∀x ∈ (monic_irr p).support, monic x
axiom unique_factorization (p : polynomial β) : ∃ c : β , p = C c * ((finsupp.prod (monic_irr p) (λ k n, k ^n) ) )
def c_fac (p : polynomial β) : β := some ( unique_factorization p)
axiom c_fac_unit (p : polynomial β) :  is_unit (c_fac p)

--def facs_to_pow (p : polynomial β →₀ ℕ ) : finset (polynomial β):= p.support.image (λ a, a^(p a))
--def to_finsupp_pow_min_one (p : polynomial β →₀ ℕ) : polynomial β →₀ ℕ := map_range  (λ n, n - 1) (by {simp}) p
def facs_to_pow_min_one (p : polynomial β →₀ ℕ ) : finset (polynomial β):= p.support.image (λ a, a^(p a - 1))
/-
lemma pows (p : polynomial β →₀ ℕ ) : finsupp.prod p (λ k n, k^n) = finset.prod (facs_to_pow p) id
:=
begin
  simp [facs_to_pow, finsupp.prod],
  refine ( eq.symm (finset.prod_image _)),
  {
    intros,
    by_contradiction,
    
  }

end

lemma factorization_eq {f : polynomial β →₀ ℕ }: finsupp.prod f (λ k n, k ^n) = finset.prod (f.support.image (λ a, a^(f a))) id
:=
begin
simp [finsupp.prod]
end
-/
open classical
section algebraically_closed
--set_option pp.numerals false

--It might be good to remove the attribute to domain of integral domain?

def rad (p : polynomial β) : polynomial β := finset.prod (finsupp.support (monic_irr p)) id --The radiacal

lemma rad_ne_zero {p : polynomial β} : rad p ≠ 0 :=
begin
  rw [rad],
  apply prod_ne_zero_of_forall_mem_ne_zero,
  intros x h1,
  have h2 : irreducible x,
  {apply irr_poly_irreducible p, exact h1},
  exact and.elim_left h2,
end

lemma degree_rad_eq_sum_support_degree {f : polynomial β} : degree (rad f) = (finset.sum (finsupp.support (monic_irr f)) degree ) :=
begin 
  rw rad,
  have h1 : finset.prod (support (monic_irr f)) id ≠ 0,
  {
    apply prod_ne_zero_of_forall_mem_ne_zero,
    intros x h1,
    have : irreducible x,
    from irr_poly_irreducible f x h1,
    exact and.elim_left this,
  },
  rw degree_prod_eq_sum_degree_of_prod_ne_zero h1
end


lemma prod_pow_min_on_ne_zero [unique_factorization_domain β]{f : polynomial β}: finsupp.prod (to_finsupp_pow_min_one (monic_irr f)) (λ (x : ~β) (y : ℕ), x ^ y) ≠ 0 :=
begin
  rw [finsupp.prod],
  apply prod_ne_zero_of_forall_mem_ne_zero',
  {
    intros x h2,
    exact pow_ne_zero _ h2,
  },
  exact _root_.zero_ne_one,
  {
    intros x h2,
    have h3: x ∈ support (monic_irr f),
    from finset.mem_of_subset support_pow_min_one_subset_support h2,
    have h4 : irreducible x,
    from irr_poly_irreducible f x h3,
    exact and.elim_left h4
  }
end

--Made a general instance fot this in poly
--lemma degree_monic_irr_eq {f : polynomial β} : degree (finsupp.prod (monic_irr f) (λ x n, x^n)) = finsupp.sum (monic_irr f) (λ x n, n*(degree x))

--lemma degree_monic_monic_irr_pow_min_one {f : polynomial β} : degree ()

lemma degree_eq_add_degree_rad_degree_pow_min_one {f : polynomial β} : degree (finsupp.prod (monic_irr f) (λ x n, x^n)) = degree (finsupp.prod (to_finsupp_pow_min_one (monic_irr f)) (λ (x : ~β) (y : ℕ), x ^ y)) + (degree (rad f)) :=
begin
--!!!!! we need to add 'in' when using conv.
  have h1 : (support (to_finsupp_pow_min_one (monic_irr f))) ⊆ support (monic_irr f),
  {
    from support_pow_min_one_subset_support,
  },
  have h2 : (support (to_finsupp_pow_min_one (monic_irr f))) ∪ (support (monic_irr f) \ (support (to_finsupp_pow_min_one (monic_irr f)))) = support (monic_irr f),
  from finset.union_sdiff_of_subset h1,
  have h3 : ∀x, x ∈ support (monic_irr f) \ support (to_finsupp_pow_min_one (monic_irr f)) ↔ (monic_irr f) x = 1,
  from  mem_sdiff_support_support_pow_min_one_iff_eq_one, 
  have h4 : finset.prod (support (to_finsupp_pow_min_one (monic_irr f)))(λ (x : ~β), x ^ (to_finsupp_pow_min_one (monic_irr f)) x * x) =
         finset.prod (support (to_finsupp_pow_min_one (monic_irr f)))
         (λ (x : ~β), x ^ (monic_irr f) x),
  {
    apply finset.prod_congr,
    exact rfl,
    intros x h4,
    rw [mul_comm _ x, ←pow_succ, to_finsupp_pow_min_one, finsupp.map_range_apply],
    have h5 : (monic_irr f) x ≠ 0,
    {
      have h5 : x ∈ support (monic_irr f),
      from finset.mem_of_subset h1 h4,
      rw [finsupp.mem_support_iff] at h5,
      exact h5,
    },
    have h6 : (monic_irr f) x ≥ 1,
    {
      have h6 : 0 < (monic_irr f) x,
      from nat.pos_of_ne_zero h5,
      have h7 : nat.succ 0 ≤ (monic_irr f) x,
      from nat.succ_le_of_lt h6,
      exact h7
    },
    rw [nat.sub_add_cancel h6],
  },
  have h5 :  finset.prod (support (monic_irr f) \ support (to_finsupp_pow_min_one (monic_irr f))) (λ (x : ~β), x) = finset.prod (support (monic_irr f) \ support (to_finsupp_pow_min_one (monic_irr f))) (λ (x : ~β), x ^ (monic_irr f) x) ,
  {
    apply finset.prod_congr,
    exact rfl,
    intro x,
    rw h3 x,
    intro h5,
    rw h5,
    simp only [pow_one x],  
  },
  have h6 : Π₀ (to_finsupp_pow_min_one (monic_irr f)) (λ (x : ~β) (y : ℕ), x ^ y) * rad f ≠ 0,
  {
    apply mul_ne_zero,
    exact prod_pow_min_on_ne_zero,
    exact rad_ne_zero
  },
  have h7 : support (to_finsupp_pow_min_one (monic_irr f)) ∩
    (support (monic_irr f) \ support (to_finsupp_pow_min_one (monic_irr f))) = ∅,
  {simp},

  conv 
  {
    to_rhs,
    rw [←degree_mul_eq_add_of_mul_ne_zero h6, rad, finsupp.prod, ←h2, finset.prod_union h7, ←mul_assoc, ←finset.prod_mul_distrib],
    simp,
    rw [h4, h5, ←finset.prod_union h7, finset.union_comm _ _, finset.sdiff_union_of_subset h1, ←finsupp.prod],
  }
end

/-
lemma degree_eq_add_degree_rad_degree_pow_min_one {f : polynomial β} : degree (finsupp.prod (monic_irr f) (λ x n, x^n)) = degree (finsupp.prod (to_finsupp_pow_min_one (monic_irr f)) (λ (x : ~β) (y : ℕ), x ^ y)) + (degree (rad f)) :=
begin
  rw [degree_finsupp_prod, degree_finsupp_prod, degree_rad_eq_sum_support_degree, finsupp.sum, finsupp.sum, to_finsupp_pow_min_one],
  have  h1 : (support (map_range (λ (n : ℕ), n - 1) to_finsupp_pow_min_one._proof_1 (monic_irr f))) ⊆ support (monic_irr f),
  from support_pow_min_one_subset_support,
  have h2 : (support (map_range (λ (n : ℕ), n - 1) to_finsupp_pow_min_one._proof_1 (monic_irr f))) ∪ ((support (monic_irr f)) \ (support (map_range (λ (n : ℕ), n - 1) to_finsupp_pow_min_one._proof_1 (monic_irr f))))  = (support (monic_irr f)),
  from finset.union_sdiff_of_subset h1,
  rw [←finset.sum_add_distrib],
end-/
 
--def n₀ (p : polynomial β) : ℕ  := (roots p).support.card --The number of distinct roots
--set_option pp.notation false
--set_option pp.implicit false
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

----set_option trace.simplify true
set_option trace.simplify true
--set_option debugger true
--set_option trace.simp_lemmas.invalid true
-- set_option trace.simplify.rewrite_failure true
set_option pp.implicit false
--important solve simp problem here
--Here a problem with simp, it immideately* failes
lemma degree_wron_le {a b : polynomial β} : degree (d[a] * b - a * d[b]) ≤ degree a + degree b - 1 :=
begin
  by_cases h1 : (a = 0),
  {
    simp,
    rw [h1, degree_zero, derivative_zero,zero_mul,sub_eq_add_neg, zero_add,zero_mul,degree_neg],
    rw [degree_zero],
    exact nat.zero_le _,
  },
  {
    by_cases h2 : (degree a = 0),
    {

      by_cases h3 : (b = 0),
      {
        rw h3,
        simp, --insight ? set_option trace.simp_lemmas.invalid true
        --rw [h3, mul_zero, degree_zero,sub_eq_add_neg, zero_add, derivative_zero,add_zero, mul_zero, degree_neg, degree_zero],
       -- exact nat.zero_le (degree a - 1)--simp should find degree_zero here
      },
    }
  }
end

lemma Mason_Stothers_lemma
(f : polynomial β) : degree f ≤ degree (gcd f (derivative f )) + degree (rad f) := --I made degree radical from this one
begin
  by_cases hf : (f = 0),
  {
    rw [hf],
    simp,
    exact nat.zero_le _,
  },
  --have h_fac : ∃ c : β , f = C c * (finsupp.prod (roots f) (λ k n, ( (X - C k ) ^n) )  ), from eq_prod_lin_fac_roots f,
  have h_tmp : ((finsupp.prod (monic_irr f) (λ k n, k ^n) ) ) = (monic_irr f).support.prod (λa, (λ k n, k ^n) a ((monic_irr f) a)),
  simp [finsupp.prod],
  have h_der : derivative ((monic_irr f).support.prod (λa, (λ k n, k ^n) a ((monic_irr f) a))) 
  = (monic_irr f).support.sum (λb, derivative ((λa, (λ k n, k ^n) a ((monic_irr f) a)) b) * (finset.erase (monic_irr f).support b).prod (λa, (λ k n, k ^n) a ((monic_irr f) a))),
  simp [derivative_prod],

  have h_der2 : ∀x ∈ (support (monic_irr f)), (x^((monic_irr f) x -1))∣(derivative ((monic_irr f).support.prod (λa, (λ k n, k ^n) a ((monic_irr f) a))) ),--
  {   
    intros, 
    rw h_der,
    refine dvd_sum _,
    intros y hy,
    by_cases (x = y),
    {
      have : x ^ ((monic_irr f) x - 1) ∣
    d[(λ (a : ~β), (λ (k : ~β) (n : ℕ), k ^ n) a ((monic_irr f) a)) y],
      rw derivative_pow,
      have : (monic_irr f) y ≠  0,
      simp [iff.elim_left (mem_support_iff _) hy],
      simp only [if_neg this],
      refine dvd.intro (↑((monic_irr f) y) * d[y]) _,
      rw [h],
      exact calc
      y ^ ((monic_irr f) y - 1) * (↑((monic_irr f) y) * d[y]) =
      y ^ ((monic_irr f) y - 1) * ↑((monic_irr f) y) * d[y] : by rw mul_assoc
      ... = ↑((monic_irr f) y) * y ^ ((monic_irr f) y - 1) * d[y] : by rw [(mul_comm (y ^ ((monic_irr f) y - 1)) ( ↑((monic_irr f) y)))],
      exact dvd_mul_of_dvd_left this _
    },
    {
      have : x ^ ((monic_irr f) x - 1) ∣ (finset.prod (finset.erase (support (monic_irr f)) y) (λ (a : ~β), a ^ (monic_irr f) a)),
      have : x ∈ (finset.erase (support (monic_irr f)) y),
      exact finset.mem_erase_of_ne_of_mem h H,
      apply dvd_prod_of_dvd_mem,
      exact this,
      exact dvd_pow_sub_one_pow,
      refine dvd_mul_of_dvd_right this _
    }
  },

  have h_fac : f = C (c_fac f) * ((finsupp.prod (monic_irr f) (λ k n, k ^n) ) ), from some_spec ( unique_factorization f),
  have h_dvd_der : ∀x ∈ (support (monic_irr f)), (x^((monic_irr f) x -1))∣ (derivative f),
  {
    intros y hy,
    rw (congr_arg derivative h_fac),
    rw h_tmp,
    rw derivative_C_mul,
    apply dvd_mul_of_dvd_right (h_der2 y hy)
  },
  have h_dvd_f : ∀x ∈ (support (monic_irr f)), (x^((monic_irr f) x -1))∣ f,
  {
    intros y hy,
    conv in (f) {rw h_fac}, --Nice using the conv could be very handy.
    rw h_tmp,
    refine dvd_mul_of_dvd_right _ (C (c_fac f)),
    apply dvd_prod_of_dvd_mem,
    apply hy,
    apply dvd_pow_sub_one_pow
  },
  have h_dvd_gcd_f_der : ∀x ∈ (support (monic_irr f)), (x^((monic_irr f) x -1))∣ (gcd f (derivative f)),
  {
    intros y hy,
    apply gcd_min,
    apply h_dvd_f y,
    apply hy,
    apply h_dvd_der y,
    apply hy
  }, --For the next lemma some notions of UFD need to be made.
  have h_prod_dvd_gcd_f_der :(to_finsupp_pow_min_one (monic_irr f)).prod (λ x y, x ^ y) ∣ gcd f d[f],
  {  
    apply facs_to_pow_prod_dvd,
    rw [to_finsupp_pow_min_one],
    dunfold to_finsupp_pow_min_one._proof_1,
    intros x h1,
    have h2 : x ∈ support (monic_irr f),
    {
      have :(support (map_range (λ (n : ℕ), n - has_one.one ℕ) _ (monic_irr f))) ⊆ ( support (monic_irr f)),
      from support_pow_min_one_subset_support,
      exact finset.mem_of_subset this h1
    },
    have h3 : irreducible x,
    from irr_poly_irreducible f x h2,
    have h4 : x ^ ((map_range (λ (n : ℕ), n - has_one.one ℕ) _ (monic_irr f)) x) ∣ gcd f d[f],
    {
        rw map_range_apply,
        exact h_dvd_gcd_f_der x h2
    },
    have h5 : ∀ (y : ~β),
        y ∈ support (map_range (λ (n : ℕ), n - has_one.one ℕ) _ (monic_irr f)) → x ≠ y → ¬associated x y,
        {
          intros y h5,
          have h6 : y ∈ support (monic_irr f),
          {--duplicate code here
            have :(support (map_range (λ (n : ℕ), n - has_one.one ℕ) _ (monic_irr f))) ⊆ ( support (monic_irr f)),
            from support_pow_min_one_subset_support,
            exact finset.mem_of_subset this h5
          },
          have h7 : monic x,
          from  irr_poly_monic f x h2,
          have h8 : monic y,
          from irr_poly_monic f y h6,
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
    have h1 : degree (finsupp.prod (to_finsupp_pow_min_one (monic_irr f)) (λ (x : ~β) (y : ℕ), x ^ y)) ≤ degree (gcd f d[f]),
    from degree_dvd h_prod_dvd_gcd_f_der h_gcd,
    have h2 : degree f = degree (finsupp.prod (to_finsupp_pow_min_one (monic_irr f)) (λ (x : ~β) (y : ℕ), x ^ y)) + (degree (rad f)),
    {
      have h2: (C (c_fac f) * finsupp.prod (monic_irr f) (λ (k : ~β) (n : ℕ), k ^ n) ≠ 0),
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

lemma derivative_eq_zero_and_derivative_eq_zero_of_rel_prime_of_wron_eq_zero
{a b : polynomial β} 
(h1 : rel_prime a b)
(h2 : d[a] * b - a * d[b] = 0)
: d[a] = 0 ∧  d[b] = 0 := sorry

lemma rel_prime_gcd_derivative_gcd_derivative_of_rel_prime {a b : polynomial β} (h : rel_prime a b) : rel_prime (gcd a d[a]) (gcd b d[b]) :=
sorry

theorem Mason_Stothers [field β]
  (h_char : characteristic_zero β)
  (a b c : polynomial β)
  (h_rel_prime_ab : rel_prime a b)
  (h_rel_prime_bc : rel_prime b c)
  (h_rel_prime_ca : rel_prime c a)
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
    apply mul_dvd_of_dvd_of_dvd_of_rel_prime,
    apply rel_prime_mul_of_rel_prime_of_rel_prime_of_rel_prime,
    exact rel_prime_gcd_derivative_gcd_derivative_of_rel_prime h_rel_prime_ab,
    exact rel_prime_gcd_derivative_gcd_derivative_of_rel_prime h_rel_prime_bc,
    exact rel_prime_gcd_derivative_gcd_derivative_of_rel_prime h_rel_prime_ca,
    apply mul_dvd_of_dvd_of_dvd_of_rel_prime,
    exact rel_prime_gcd_derivative_gcd_derivative_of_rel_prime h_rel_prime_ab,
    exact h_dvd_wron_a,
    exact h_dvd_wron_b,
    exact h_dvd_wron_c
  },
  have h_wron_ne_zero : d[a] * b - a * d[b] ≠ 0,
  {
    by_contradiction h1,
    rw not_not at h1,
    have h_a_b : d[a] = 0 ∧ d[b] = 0,
    from derivative_eq_zero_and_derivative_eq_zero_of_rel_prime_of_wron_eq_zero h_rel_prime_ab h1,
    have h2 : d[a] * c - a * d[c] = 0,
    {rw [←h_wron, h1]},
    have h_a_c : d[a] = 0 ∧ d[c] = 0,
    from derivative_eq_zero_and_derivative_eq_zero_of_rel_prime_of_wron_eq_zero (rel_prime_comm h_rel_prime_ca) h2,
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



end







end algebraically_closed

