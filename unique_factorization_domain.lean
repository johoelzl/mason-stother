import mason_stother

local infix ^ := monoid.pow

noncomputable theory

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
def to_list {x : α →₀ ℕ} : list α := list.foldl (λ y z,  append y (list.repeat z (x z))) list.nil  (quotient.out x.support.val) --Or I make a list directly by folding with repeat append and empty list?

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

def associated [integral_domain α] (x y : α) : Prop:=
∃u, is_unit u ∧ x = u * y

local notation a`~ᵤ`b := associated a b

example [integral_domain α] : is_unit_2 (1 : α ) := --existential in is unit is anoying.
⟨1, rfl⟩ 
@[refl] protected lemma associated.refl [integral_domain α] : ∀ (x : α), x ~ᵤ x :=
assume x, ⟨ 1, (by simp)⟩ 

def associated_list [has_mul α] [has_one α]: list α → list α → Prop
| [] [] := true
| [] (h::t) := false
| (h::t) [] := false
| (h₁::t₁) (h₂::t₂) := ∃x, is_unit x ∧ h₁ = h₂ * x

@[refl] protected theorem perm.refl : ∀ (l : list α), l ~ l
| []      := perm.nil
| (x::xs) := skip x (perm.refl xs)

--The factorization could be factorizen as a subtype. Can subtypes be dependent?
class unique_factorization_domain (α : Type u) extends integral_domain α :=
(fac : ∀{x : α}, x ≠ 0 →  ∃ p : α →₀ ℕ, x = pow_prod p)
(unique : ∀{x : α}, ∀{f g : α →₀ ℕ }, x = pow_prod f → x = pow_prod g → )
