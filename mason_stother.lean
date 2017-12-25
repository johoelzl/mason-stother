-- the to be Mason-Stother formalization
-- Authors Johannes & Jens

--Defining the gcd
import poly
import euclidean_domain
import data.finsupp
import algebraically_closed_field
noncomputable theory
local infix ^ := monoid.pow
local notation `d[`a`]` := polynomial.derivative a
local notation Σ := finset.sum
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
variables [comm_semiring α]



def is_gcd (a b d : polynomial α) :=  d∣a ∧  d∣b ∧  (∀x, x∣a →  x∣b → x∣d)

-- so every polynomial has a GCD? Shouldn't there be some restriction on α
axiom gcd_ax : ∀ a b : polynomial α,( ∃( d : polynomial α ), (is_gcd a b d))

class has_gcd (α : Type u) [comm_semiring α] :=
(gcd : α → α → α) (gcd_right : ∀ a b, ( (gcd a b) ∣ b )) (gcd_left : ∀ a b, (gcd a b) ∣ a) (gcd_min : ∀ a b g, g∣a → g∣b → g∣ (gcd a b))

def gcd [comm_semiring α] [has_gcd α] : α → α → α := has_gcd.gcd
def gcd_min [comm_semiring α] [h : has_gcd α]  := h.gcd_min --Correct???


@[instance] constant polynomial.has_gcd : has_gcd (polynomial α)
--Convert units to a set
def is_unit {t : Type u}[has_mul t] [has_one t](a : t) : Prop := ∃b, a * b = 1 ∧ b * a = 1


def monic (p : polynomial α) : Prop := leading_coeff p = 1
--Assume has_gcd on polynomials
def rel_prime (a b : polynomial α) := is_unit (gcd a b) --∈ set.range (units.val : _ → polynomial α)


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
variable [field β]

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
have h_deg_neg_C :degree (- C q) = 0, by rw [(eq.symm degree_neg), this],
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
variables  [algebraically_closed_field β] -- Should be an instance of algebraically closed.
open finsupp
def irreducible (p : polynomial β): Prop := p ≠ 0 ∧ ¬ is_unit p ∧ ∀d, d∣p → is_unit d



--axiom roots (p : polynomial β) : β →₀ ℕ Problem, because the 0 polynomial can have infinite roots.
--axiom eq_prod_lin_fac_roots (p : polynomial β) : ∃ c : β , p = C c * (finsupp.prod (roots p) (λ k n, ( (X - C k ) ^n) )  )

--The more general setting, avoids problem with the roots of the zero polynomial
axiom monic_irr (p : polynomial β) : polynomial β →₀ ℕ
axiom irr_poly_irreducible (p : polynomial β) : ∀x ∈ (monic_irr p).support, irreducible x
axiom irr_poly_monic (p : polynomial β) : ∀x ∈ (monic_irr p).support, monic x
axiom unique_factorization (p : polynomial β) : ∃ c : β , p = C c * ((finsupp.prod (monic_irr p) (λ k n, k ^n) ) )
def c_fac (p : polynomial β) : β := some ( unique_factorization p)
axiom c_fac_unit (p : polynomial β) :  @is_unit β _ _ (c_fac p)

def facs_to_pow (p : polynomial β →₀ ℕ ) : finset (polynomial β):= p.support.image (λ a, a^(p a))
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



def rad (p : polynomial β) : polynomial β := finset.prod (finsupp.support (monic_irr p)) id --The radiacal
--def n₀ (p : polynomial β) : ℕ  := (roots p).support.card --The number of distinct roots
--set_option pp.notation false
--set_option pp.implicit false
lemma Mason_Stothers_lemma
(f : polynomial β) : f ≠ 0 →  degree f ≤ degree (gcd f (derivative f )) + degree (rad f) := --I made degree radical from this one
begin
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
  }
  
  --have h_f' : derivative f = C (c_fac f) *


--derivative (s.prod p) = s.sum (λb, derivative (p b) * (erase s b).prod p) 

--((finsupp.prod (monic_irr f) (λ k n, k ^n) ) ) = 
--finset.prod (support f) (λ (a : polynomial β), a ^ ⇑f a) =
--derivative (s.prod f) = s.sum (λb, derivative (f b) * (erase s b).prod f) 
-- (monic_irr f).support.prod (λa, (λ k n, k ^n) a ((monic_irr f) a))
end


theorem Mason_Stothers
  (a b c : polynomial β)
  (h_rel_prime_ab : rel_prime a b)
  (h_rel_prime_bc : rel_prime b c)
  (h_rel_prime_ca : rel_prime c a)
  (h1 : a + b = c)
  (h2 : ¬ (derivative a = 0 ∧ derivative b = 0 ∧ derivative c = 0)) :
  degree c ≤ degree ( rad (a*b*c)) - 1 :=
sorry






end algebraically_closed

