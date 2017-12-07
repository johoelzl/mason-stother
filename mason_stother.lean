-- the to be Mason-Stother formalization
-- Authors Johannes & Jens

--Defining the gcd
import poly
noncomputable theory


universe u
variable {α : Type u}
variables [comm_semiring α] --(a b c : α)

--example (a b d : α  ) (h1: (d∣a)) (h2:d∣b):= nat.zero

namespace gcd1

structure gcd (a b : α):  Type u :=
(d : α) (h1: d∣a) (h2 : d∣b) (h3 : ∀x, x∣a →  x∣b → x∣d)

#check gcd.rec_on 
#print gcd
def test : gcd polynomial.X (@polynomial.X α  _) := begin fapply (gcd.mk polynomial.X (dvd_refl _) (dvd_refl _) ), {intro, simp} end




instance gcd_to_polynomial (a b : polynomial α): has_coe (gcd a b) (polynomial α) := 
⟨gcd.d⟩ 

-- ↑ is arrow up
#check ((↑test) + (0:polynomial α))




end gcd1
/- Different definiton of gcd -/

namespace gcd2

def is_gcd (a b d : polynomial α) :=  d∣a ∧  d∣b ∧  (∀x, x∣a →  x∣b → x∣d)


constant ax1 : ∀ a b : polynomial α,( ∃( d : polynomial α ), (is_gcd a b d))

class gcd (α : Type u) [comm_semiring α] :=
(gcd : α → α → α) (gcd_right : ∀ a b, ( (gcd a b) ∣ b )) (gcd_left : ∀ a b, (gcd a b) ∣ a) (gcd_min : ∀ a b g, g∣a → g∣b → g∣ (gcd a b))

--Convert units to a set
--Assume has_gcd on polynomials


end gcd2