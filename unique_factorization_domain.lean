import data.finsupp
import algebra.ring
import .to_finset

local infix ^ := monoid.pow

noncomputable theory

open classical
local attribute [instance] prop_decidable

universe u
variable {α : Type u}

--If I do this I can't reuse the lemmas for units.
def is_unit_2 {t : Type u}[has_mul t] [has_one t](a : t) : Prop := ∃b, a * b = 1 ∧ b * a = 1
--If I do this I can't reuse the lemmas for units.


def is_unit {t : Type u}[semiring t] (a : t) : Prop := ∃b : units t, a = b

def to_unit {t : Type u}[semiring t] {x : t} (h : is_unit x) : units t :=
some h

def irreducible {γ : Type u}[comm_semiring γ](p : γ): Prop := p ≠ 0 ∧ ¬ is_unit p ∧ ∀d, d∣p → is_unit d

--correct simp?
@[simp] lemma  to_unit_is_unit_eq {t : Type u}[semiring t] {x : t} {h : is_unit x} : ↑(@to_unit t _ x h) = x :=
eq.symm (some_spec h)

@[simp] lemma  to_unit_is_unit_val_eq {t : Type u}[semiring t] {x : t} {h : is_unit x} : (@to_unit t _ x h).val = x :=
eq.symm (some_spec h)

--Can't we make units a typeclass? 



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



lemma is_unit_one [semiring α] : is_unit (1 : α ) := --existential in is unit is anoying.
⟨1, rfl⟩ 

lemma not_is_unit_zero [semiring α] (h : (0 : α) ≠ 1) : ¬ is_unit (0 : α) := --Do we need semiring?
begin
  by_contradiction h1,
  let u := to_unit h1,
  have h2: u.val*u.inv = 1,
  from u.val_inv,
  have h3: u.val*u.inv = (0 : α),
  {
    have : ↑u = (0 : α),
    simp [u, h1],
    --rw [to_unit_is_unit_eq (0 : α)],
    have : u.val = (0 : α),
    exact this,
    simp [this],
  },
  rw h2 at h3,
  exact h (eq.symm h3)
end

@[refl] protected lemma associated.refl [integral_domain α] : ∀ (x : α), x ~ᵤ x :=
assume x, ⟨ 1, (by simp) ⟩ 

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


inductive rel_multiset {α β : Type u} (r : α → β → Prop) : multiset α → multiset β → Prop
| nil : rel_multiset {} {}
| cons : ∀a b xs ys, r a b → rel_multiset xs ys → rel_multiset (a::xs) (b::ys)

class unique_factorization_domain (α : Type u) extends integral_domain α :=
(fac : ∀{x : α}, x ≠ 0 → ¬ is_unit x → ∃ p : multiset α, x = p.prod ∧ (∀x∈p, irreducible x))
(unique : ∀{f g : multiset α}, (∀x∈f, irreducible x) → (∀x∈g, irreducible x) → f.prod = g.prod → rel_multiset associated f g)

--To prove, that a field is an instance of an unique_fac_dom

/-
first to prove that a field is an intergral domain:
instance discrete_field.to_integral_domain [s : discrete_field α] : integral_domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := discrete_field.eq_zero_or_eq_zero_of_mul_eq_zero,
  ..s }
-/

--Priority lowered (doesn't help),aim was to prevent diamond problem, div_ring to domain and integral_dom to domain
instance field.to_integral_domain [s : field α] : integral_domain α := 
{
    eq_zero_or_eq_zero_of_mul_eq_zero := @eq_zero_or_eq_zero_of_mul_eq_zero _ _, --How does it get the no_zero_divisors? -- division ring -> domain
    ..s
}


--is there a conversion from a division ring to a group over the multiplication? 

lemma for_all_is_unit_of_not_zero [field α] : ∀{x : α}, x ≠ 0 → is_unit x :=
begin
  assume x h1,
  rw [is_unit],
  fapply exists.intro,
  {
    exact ⟨x, x⁻¹, mul_inv_cancel h1, inv_mul_cancel h1⟩
  },
  {
    refl
  }
end

lemma for_all_not_irreducible [field α] : ∀{x : α}, ¬irreducible x :=
begin
  {
    simp [irreducible],
    intros x h1 h2,
    have : is_unit x,
    from for_all_is_unit_of_not_zero h1,
    contradiction
  }
end

lemma eq_empty_of_forall_irreducible_of_mem [field α] {g : multiset α}: (∀ (x : α), x ∈ g → irreducible x) → g = ∅ :=
begin
  intro h1,
  by_cases h2 : (g = ∅),
  exact h2,
  { 
       let x := some (multiset.exists_mem_of_ne_zero h2),
       have h3 : x ∈ g,
       from some_spec (multiset.exists_mem_of_ne_zero h2),
       have h4 : irreducible x,
       from h1 x h3,
       have : ¬ irreducible x,
       from for_all_not_irreducible,
       contradiction
  }
end

instance field.to_unique_factorization_domain [s : field α] : unique_factorization_domain α :=
{ 
    eq_zero_or_eq_zero_of_mul_eq_zero := @eq_zero_or_eq_zero_of_mul_eq_zero _ _, --Problem, will it now use the same as integral domain or again diamond problem?
    fac := 
    begin
      assume x h1 h2,
      have : is_unit x,
      from for_all_is_unit_of_not_zero h1,
      contradiction
    end,
    unique := 
    begin
      intros f g h1 h2 h3,
      have hf : f = ∅,
      from eq_empty_of_forall_irreducible_of_mem h1,
      have hg : g = ∅,
      from eq_empty_of_forall_irreducible_of_mem h2,
      rw [hf, hg],
      simp [rel_multiset.nil]    
    end,
    ..s
}

--gcds
class has_gcd (α : Type u) [comm_semiring α] :=
(gcd : α → α → α) (gcd_right : ∀ a b, ( (gcd a b) ∣ b )) (gcd_left : ∀ a b, (gcd a b) ∣ a) (gcd_min : ∀ a b g, g∣a → g∣b → g∣ (gcd a b))

def gcd [comm_semiring α] [has_gcd α] : α → α → α := has_gcd.gcd
def gcd_min [comm_semiring α] [h : has_gcd α]  := h.gcd_min --Correct???

def is_gcd [has_dvd α] (a b d :α) :=  d∣a ∧  d∣b ∧  (∀x, x∣a →  x∣b → x∣d)

instance unique_factorization_domain.has_gcd [unique_factorization_domain α] : has_gcd α :=
{
  gcd := --Can this be done neather, with a match expression? Do I have unesisary cases?
  begin
    intros f g,
    by_cases h1 : (f = 0), --!!! Wrong didn't take associates of irreducible elements into account.
    { --Intersection can be taken after quotient over associates
      exact g
    },
    {
      by_cases h2 : (g = 0),
      {
        exact f
      },
      {
        by_cases h3 : (is_unit f),
        {
          exact f
        },
        {
          by_cases h4 : (is_unit g),
          {
            exact g,
          },
          {
            let fac_f := some (unique_factorization_domain.fac h1 h3),
            let fac_g := some (unique_factorization_domain.fac h2 h4),
            exact (fac_f ∩ fac_g).prod
          }
        }
      }
    }
  end,
  gcd_right := sorry,
  gcd_left := sorry,
  gcd_min := sorry
}

#check @to_unit

--Lemma that every element not zero can be represented as a product of a unit with prod primes.
lemma factorization [unique_factorization_domain α]: ∀{x : α}, x ≠ 0 → ∃ u : units α, ∃ p : multiset α, x = u*p.prod ∧ (∀x∈p, irreducible x) :=
begin
  intros x h1,
  by_cases h2 : (is_unit x),
  {
    fapply exists.intro,
    exact to_unit h2,
    fapply exists.intro,
    exact 0,
    simp
  },
  { 
    let f := some (unique_factorization_domain.fac h1 h2),
    fapply exists.intro,
    exact to_unit is_unit_one,
    fapply exists.intro,
    exact f,
    simp,
    exact some_spec (unique_factorization_domain.fac h1 h2)
  }
  
end