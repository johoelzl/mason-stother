-- the to be Mason-Stother formalization
-- Authors Johannes & Jens

--Defining the gcd
import poly
import euclidean_domain
import finsupp
noncomputable theory

#check classical.prop_decidable
universe u
variable {α : Type u}
variables [comm_semiring α] --(a b c : α)

--example (a b d : α  ) (h1: (d∣a)) (h2:d∣b):= nat.zero

namespace gcd1

structure gcd (a b : α) :  Type u :=
(d : α) (h1: d∣a) (h2 : d∣b) (h3 : ∀x, x∣a →  x∣b → x∣d)


def test : gcd polynomial.X (@polynomial.X α  _) := begin fapply (gcd.mk polynomial.X (dvd_refl _) (dvd_refl _) ), {intro, simp} end




instance gcd_to_polynomial (a b : polynomial α): has_coe (gcd a b) (polynomial α) := 
⟨gcd.d⟩ 

-- ↑ is arrow up
--#check ((↑test) + (0:polynomial α))




end gcd1
/- Different definiton of gcd -/

namespace gcd2

def is_gcd (a b d : polynomial α) :=  d∣a ∧  d∣b ∧  (∀x, x∣a →  x∣b → x∣d)


constant ax1 : ∀ a b : polynomial α,( ∃( d : polynomial α ), (is_gcd a b d))

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


variable β : Type u
variable [field β]
-- variable [euclidian_domain (polynomial β)]
--@[instance] constant axPolyInteg : integral_domain (polynomial β)
open polynomial
open finsupp

def lin_fac {β : Type u} [field β ] (q : β) : polynomial β := (X + (- C q))

/-
set_option pp.all  false


lemma test : ite (1 = 1) (1: β) 0  = 1:= rfl
example (q : β ): ite (0 = 1) q (0: β ) = 0:= rfl

#print decidable.no_confusion
lemma decidable_ext :∀ a b : Prop, a = b →   decidable a = decidable b 
   | x y (eq.refl _) := ⟨_⟩ 
lemma decidable_ext2 {p : Prop}: ∀ a b : decidable p, a = b 
| (is_true a)  (is_true b)  := rfl
| (is_true a)  (is_false b)  := by contradiction
| (is_false a)  (is_true b)  := by contradiction
| (is_false a)  (is_false b)  := rfl

#check classical.prop_decidable (1=1)
#check nat.decidable_eq 1 1
lemma l11 : classical.prop_decidable (1=1) = nat.decidable_eq 1 1 := decidable_ext2 (classical.prop_decidable (1=1)) (nat.decidable_eq 1 1)
lemma l01 : classical.prop_decidable (0=1) = nat.decidable_eq 0 1 := decidable_ext2 (classical.prop_decidable (0=1)) (nat.decidable_eq 0 1)
-/

--assume q : β,
--have help : ite ((1:ℕ )= 1) (1: β)  0 = 1 := rfl,
/-
lemma deg_ln_fac_help {q : β} : 1 ≤ degree (X + (- C q)) :=
have h1: ((X : polynomial β) + (- C q)) 1 = (1:β),  -- Type annotation is needed here, otherwise + will fail.
begin simp [add_apply, neg_apply_poly], 
  simp [coe_fn, has_coe_to_fun.coe], 
  simp [X, C, single, single_apply],
  have h2 :  ite ((1:ℕ) = 1) (1:β) (0:β)  = (1:β), from rfl,
  have h3: ite (0 = 1) q (0: β ) = 0, from  rfl,
  exact calc 
    @ite (1 = 1) (classical.prop_decidable (1=1)) _ 1 0 + -(@ite (0 = 1) (classical.prop_decidable (0=1)) _ q 0)  
     = @ite (1 = 1) (nat.decidable_eq 1 1) _ 1 0 + -(@ite (0 = 1) (classical.prop_decidable (0=1)) _ q 0): by simp
    ... =   @ite (1 = 1) (nat.decidable_eq 1 1) _ 1 0 + -(@ite (0 = 1) (nat.decidable_eq 0 1) _ q 0): by simp
    ... = 1 + 0 : by simp
    ... = 1 : by simp
  end,
have ((X : polynomial β) + (- C q)) 1 ≠ 0, from calc
    ((X : polynomial β) + (- C q)) 1 = 1 : h1
    ... ≠ 0 : one_ne_zero,
le_degree this
-/
lemma deg_ln_fac {q : β} : degree (X + (- C q)) = 1 :=
have one_le_deg : 1 ≤ degree (X + (- C q)), from
    have h1: ((X : polynomial β) + (- C q)) 1 = (1:β),  -- Type annotation is needed here, otherwise + will fail.
    begin simp [add_apply, neg_apply_poly], 
    simp [coe_fn, has_coe_to_fun.coe], 
    simp [X, C, single, single_apply],
    have h2 :  ite ((1:ℕ) = 1) (1:β) (0:β)  = (1:β), from rfl,
    have h3: ite (0 = 1) q (0: β ) = 0, from  rfl,
    exact calc 
        @ite (1 = 1) (classical.prop_decidable (1=1)) _ 1 0 + -(@ite (0 = 1) (classical.prop_decidable (0=1)) _ q 0)  
        = @ite (1 = 1) (nat.decidable_eq 1 1) _ 1 0 + -(@ite (0 = 1) (classical.prop_decidable (0=1)) _ q 0): by simp
        ... =   @ite (1 = 1) (nat.decidable_eq 1 1) _ 1 0 + -(@ite (0 = 1) (nat.decidable_eq 0 1) _ q 0): by simp
        ... = 1 + 0 : by simp
        ... = 1 : by simp
    end,
    have ((X : polynomial β) + (- C q)) 1 ≠ 0, from calc
        ((X : polynomial β) + (- C q)) 1 = 1 : h1
        ... ≠ 0 : one_ne_zero,
    le_degree this, 
have (0 ≠ (1 : β)), from zero_ne_one,
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

--set_option pp.all true
--set_option pp.implicit false


open euclidean_domain
#print euclidean_domain.h_norm



lemma degree_ne_zero_ne_zero2 {f : polynomial β } : degree f ≠ 0 → f ≠ 0 :=--I want to apply normal by_cpntradiction here, but I don't know how to apply that, due to ambiguous overload.
begin intro, apply (@classical.by_contradiction (f ≠ 0) _), intro,
have h3: (f = 0), from iff.elim_left (@not_not _ (classical.prop_decidable _)) a_1,
have h4: degree f = 0, calc degree f = degree 0 : by rw [h3] ... = 0 : degree_zero,
apply a h4
 end
#check degree_ne_zero_ne_zero
#check  degree_ne_zero_ne_zero2
set_option pp.all false
set_option pp.implicit false

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
} , {admit} end


lemma finite_roots {a : polynomial β} : set.finite (roots_of_as_set a):= --How do we do an induction on the degree?


end gcd2