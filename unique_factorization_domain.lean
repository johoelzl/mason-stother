import mason_stother 
import algebra.ring

local infix ^ := monoid.pow

noncomputable theory

open classical

universe u
variable {α : Type u}

def pow_prod [comm_monoid α](p : α →₀ ℕ ) : α := p.prod (λ a n, a^n)
--We need a coercion from α →₀ ℕ to list. De support is een finset, does that have a coercion to list?
--The value of a finset is a multiset, and the multiset is a quotient with regards to permutations of lists.
--def unique_factorization {α : Type u} {x : α} 

--If we obtain a list from the multisets, than there exists a function which permutes and multiplies with a constant.
--We could even make a quotient for lists with regards to this function! Would that be handy?

--With quotient.out a representative can be obtained.
--Now a coercion to multiset.
--Append is associative but not commutative? --Problem
def to_list (x : α →₀ ℕ) : list α := list.foldl (λ y z,  append y (list.repeat z (x z))) list.nil  (quotient.out x.support.val) --Or I make a list directly by folding with repeat append and empty list?

--Now the relation: permutation + mul by unit.
/-
inductive perm : list α → list α → Prop
| nil   : perm [] []
| skip  : Π (x : α) {l₁ l₂ : list α}, perm l₁ l₂ → perm (x::l₁) (x::l₂)
| swap  : Π (x y : α) (l : list α), perm (y::x::l) (x::y::l)
| trans : Π {l₁ l₂ l₃ : list α}, perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃
-/

--Unit mul
/-
inductive associated_list : list α → list α → Prop
| nil : associated_list [] []
| mk  :  
-/

@[reducible] def associated [integral_domain α] (x y : α) : Prop:=
∃u : units α, x = u * y

local notation a`~ᵤ`b := associated a b

lemma is_unit_one [integral_domain α] : is_unit (1 : α ) := --existential in is unit is anoying.
⟨1, rfl⟩ 

@[refl] protected lemma associated.refl [integral_domain α] : ∀ (x : α), x ~ᵤ x :=
assume x, ⟨ 1, (by simp) ⟩ 

set_option trace.check true

@[symm] protected lemma associated.symm [integral_domain α] {x y : α} (p : x ~ᵤ y) : y ~ᵤ x :=
begin 
  fapply exists.intro,
  exact units.inv' (some p ),
  have h1 : x = ↑(some p) * y, from some_spec p,
  have h1a : (↑(units.inv' (some p))) * (↑(some p)) = (1 : α),
    exact units.inv_mul (some p),
  have h2 : (↑(units.inv' (some p))) * x = y, 
  exact calc
  (↑(units.inv' (some p))) * x = (↑(units.inv' (some p))) * (↑(some p) * y) : by rw ←h1
  ... = (↑(units.inv' (some p))) * (↑(some p)) * y : by rw mul_assoc
  ... = 1*y : by rw h1a
  ... = y : by simp,
  simp [mul_comm, h2]
end 



@[symm] protected lemma associated.trans [integral_domain α] {x y z: α} (h1 : x ~ᵤ y)(h2 : y ~ᵤ z): x ~ᵤ z :=
begin 
  fapply exists.intro,
  exact (some h1) * (some h2),
  have h1a: x = ↑(some h1) * y, from some_spec h1,
  have h2a: y = ↑(some h2) * z, from some_spec h2,
  have h3 : x = ↑(some h1) * (↑(some h2) * z), 
  from calc x = ↑(some h1) * y : h1a
  ... = ↑(some h1) * (↑(some h2) * z) : by rw ←h2a,
  have h4 : ↑(some h1) * (↑(some h2) * z) = (↑(some h1) * ↑(some h2)) * z, simp [mul_assoc],
  exact calc  x = ↑(some h1) * (↑(some h2) * z) : h3
  ... = (↑(some h1) * ↑(some h2)) * z : h4
  ... = ↑(some h1 * some h2) * z : by simp [units.mul_coe]
end 

lemma associated.eqv (α : Type) [integral_domain α]: equivalence (@associated α _) :=
mk_equivalence (@associated α _) (@associated.refl α _) (@associated.symm α _) (@associated.trans α _)


def associated_list [integral_domain α]: list α → list α → Prop
| [] [] := true
| [] (h::t) := false
| (h::t) [] := false
| (h₁::t₁) (h₂::t₂) := associated h₁ h₂ 


class unique_factorization_domain (α : Type u) extends integral_domain α :=
(fac : ∀{x : α}, x ≠ 0 →  ∃ p : α →₀ ℕ, x = pow_prod p)
(unique : ∀{x : α}, ∀{f g : α →₀ ℕ }, x = pow_prod f → x = pow_prod g → ∃ (l : list α) (q : list.perm (to_list g) l), associated_list (to_list f) l)

--To prove, that a field is an instance of an unique_fac_dom

/-
first to prove that a field is an intergral domain:
instance discrete_field.to_integral_domain [s : discrete_field α] : integral_domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := discrete_field.eq_zero_or_eq_zero_of_mul_eq_zero,
  ..s }
-/

--Practice
instance field.to_integral_domain [s : field α] : integral_domain α :=
{
    eq_zero_or_eq_zero_of_mul_eq_zero := @eq_zero_or_eq_zero_of_mul_eq_zero _ _,
    ..s
}

instance field.to_unique_factorization_domain [s : field α] : unique_factorization_domain α :=
{ 
    eq_zero_or_eq_zero_of_mul_eq_zero := @eq_zero_or_eq_zero_of_mul_eq_zero _ _, --Problem, will it now use the same as integral domain or again diamond problem?
    fac := _,
    unique := _,
    ..s
}