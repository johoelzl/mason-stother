-- the to be Mason-Stother formalization
-- Authors Johannes & Jens

--Defining the gcd
import poly
import euclidean_domain
import data.finsupp
noncomputable theory



universe u


variable {α : Type u}
variables [comm_semiring α]

namespace polynomial


def is_gcd (a b d : polynomial α) :=  d∣a ∧  d∣b ∧  (∀x, x∣a →  x∣b → x∣d)

axiom gcd_ax : ∀ a b : polynomial α,( ∃( d : polynomial α ), (is_gcd a b d))

class has_gcd (α : Type u) [comm_semiring α] :=
(gcd : α → α → α) (gcd_right : ∀ a b, ( (gcd a b) ∣ b )) (gcd_left : ∀ a b, (gcd a b) ∣ a) (gcd_min : ∀ a b g, g∣a → g∣b → g∣ (gcd a b))

def gcd [comm_semiring α] [has_gcd α] : α → α → α := has_gcd.gcd

@[instance] constant polynomial.has_gcd : has_gcd (polynomial α) 
--Convert units to a set
--Assume has_gcd on polynomials
def rel_prime (a b : polynomial α) := (gcd a b) ∈ set.range (units.val : _ → polynomial α) 

--We need to define the radical and the number of distinct roots of a polynomial
--First define roots

def root_of (a : polynomial α) (b : α) := polynomial.eval a b = 0


structure roots_of (a : polynomial α):= --Can this be made as a set directly?
(val : α)(h1 : root_of a val)

def roots_of_as_set (a : polynomial α) := set_of (root_of a)
--Can we proof this set is finite? 

--Can I define the radical?

--Proof linear factor iff root, makes use of the division algorithm. Hence that polynomials are a euclidian ring.

end polynomial



section field

variable β : Type u
variable [field β]
open polynomial
open finsupp

def lin_fac {β : Type u} [field β ] (q : β) : polynomial β := (X + (- C q))

lemma deg_ln_fac {q : β} : degree (X + (- C q)) = 1 :=
have one_le_deg : 1 ≤ degree (X + (- C q)), from
    have h1: ((X : polynomial β) + (- C q)) 1 = (1:β),  -- Type annotation is needed here, otherwise + will fail.
    begin 
        simp [add_apply, neg_apply_poly], 
        simp [coe_fn, has_coe_to_fun.coe], 
        simp [X, C, single, single_apply, if_pos, if_neg]
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
    ... ≤ 1 : dec_trivial,
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
lemma root_iff_lin_fac : ∀ p : polynomial β, ∀ k: β,  ( root_of p k) ↔ ((X + (- (C k)))  ∣p) :=
begin intros, apply iff.intro, 
{intro, --apply (exists.elim a), intros, 
  -- have h1 : 1 ≠ 0, from dec_trivial,
  have h2 :  degree (X + (- (C k ))) ≠ 0,
  from calc degree (X + (- (C k))) = 1 : @deg_ln_fac _ _ k
  ... ≠ 0 : dec_trivial,
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
variables [field β] -- Should be an instance of algebraically closed.
axiom roots (p : polynomial β) : (polynomial β) →₀ ℕ  
axiom eq_prod_lin_fac_roots (p : polynomial β)

section algebraically_closed






end algebraically_closed

