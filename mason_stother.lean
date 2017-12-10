-- the to be Mason-Stother formalization
-- Authors Johannes & Jens

--Defining the gcd
import poly
import euclidian_domain
noncomputable theory


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

def roots_of2 (a : polynomial α) := set_of (root_of a)
--Can we proof this set is finite? 

--Can I define the radical?

--Proof linear factor iff root, makes use of the division algorithm. Hence that polynomials are a euclidian ring.


variable β : Type u
variable [field β]
constant axPolyEuclid : euclidian_domain (polynomial β)
open polynomial
#print finsupp.add_comm_group
instance : has_neg (polynomial β ) := _ -- How to get the has_neg?
set_option pp.coercions  true
#print prefix polynomial
#check (↑X : ℕ  -> β)
#check   ((coe  X) : ℕ  -> β )
def lin_fac {β : Type u} [field β ] (q : β) : polynomial β := (X + (- C q))


lemma deg_ln_fac : ∀ a : β, degree (X + (- C a)) = 1 :=
assume q : β,
--have  ((coe (@X β _))) : ℕ -> β  )1 = 1 , from begin end,
have (X : ℕ →₀ β) (1 : ℕ) = (1 : β), begin simp [X, finsupp.single]  end,
_



--Why is there no instance for has subtract?
lemma root_iff_lin_fac : ∀ p : polynomial β, (∃ α : β, root_of p α) ↔ (∃f : polynomial β, polynomial.degree f = 1 ∧  f∣p) :=
begin intros, apply iff.intro, 
{intro, apply (exists.elim a), intros, 
 exact have (X + (- (C a_1))) ≠ 0, begin end,

} , {admit} end


end gcd2