import data.finsupp
import algebra.ring
import .to_finset

noncomputable theory

local infix ^ := monoid.pow

open classical
local attribute [instance] prop_decidable

universe u
variable {α : Type u}

--Would it have been smart to define units as a type that lives in Prop??
--Or would this have been pointless because a Prop cannot contain data? It could have been made with exisential quatifier, but than we are in the same situation that we are in now.

def is_unit {t : Type u}[semiring t] (a : t) : Prop := ∃b : units t, a = b

def to_unit {t : Type u}[semiring t] {x : t} (h : is_unit x) : units t :=
some h

--correct simp?
@[simp] lemma  to_unit_is_unit_eq {t : Type u}[semiring t] {x : t} {h : is_unit x} : ↑(@to_unit t _ x h) = x :=
eq.symm (some_spec h)

@[simp] lemma  to_unit_is_unit_val_eq {t : Type u}[semiring t] {x : t} {h : is_unit x} : (@to_unit t _ x h).val = x :=
eq.symm (some_spec h)

def associated [integral_domain α] (x y : α) : Prop:=
∃u : units α, x = u * y

local notation a`~ᵤ`b := associated a b

--Correct???? Should be unit or associate.
def irreducible [integral_domain α] (p : α) : Prop :=
p ≠ 0 ∧ ¬ is_unit p ∧ ∀d, d∣p → (is_unit d ∨ (d ~ᵤ p))

def irreducible' [integral_domain α] (p : α) : Prop :=
p ≠ 0 ∧ ¬ is_unit p ∧ ∀ a b : α, p = a * b → (is_unit a ∨ is_unit b)

lemma irreducible_iff_irreducible' [integral_domain α] {p : α} : irreducible p ↔ irreducible' p :=
begin
  apply iff.intro,
  {
    intro h1,
    have h2 : (p ≠ 0),
    from and.elim_left h1,
    have h3 : (¬ is_unit p),
    from and.elim_left (and.elim_right h1),
    have h4 : ∀d, d∣p → (is_unit d ∨ (d ~ᵤ p)),
    from and.elim_right (and.elim_right h1),
    constructor,
    exact h2,
    constructor,
    exact h3,
    intros a b h5,
    have h6 : a∣p,
    {simp *},
    have h7 : (is_unit a ∨ (a ~ᵤ p)),
    from h4 a h6,
    cases h7,
    {
      simp *
    },
    {
      rw associated at h7,
      let u := some h7,
      have h8 : a = ↑u * p,
      from some_spec h7,
      rw h8 at h5,
      rw [mul_comm _ p, mul_assoc] at h5,
      have h9 : p * 1 = p * (↑u * b),
      {
        rw [←h5],
        simp
      },
      have h10 : 1 = (↑u * b),
      from eq_of_mul_eq_mul_left h2 h9,
      have h11 : is_unit b,
      {
        constructor,
        swap,
        exact u⁻¹ * 1,
        simp [h10],
        have : ↑u⁻¹ * 1 = ↑u⁻¹ * (↑u * b),
        {simp [h10]},
        rw [←mul_assoc, units.inv_mul] at this,
        simp at this,
        exact eq.symm this
      },
      simp [h11]
    }
  },
  {
    intro h1,
    have h2 : (p ≠ 0),
    from and.elim_left h1,
    have h3 : (¬ is_unit p),
    from and.elim_left (and.elim_right h1),
    have h4 : ∀ a b : α, p = a * b → (is_unit a ∨ is_unit b),
    from and.elim_right (and.elim_right h1), 
    constructor,
    exact h2,
    constructor,
    exact h3,
    intros a h5, 
    simp only [has_dvd.dvd] at h5,
    let b := some h5,
    have h6 : p = a * b,
    from some_spec h5,
    have h7 : is_unit a ∨ is_unit b,
    from h4 _ _ h6,
    cases h7,
    {
      simp [h7]
    },
    {
      have h8 : (a ~ᵤ p),
      {
        simp only [associated],
        let bᵤ := to_unit h7,
        fapply exists.intro,
        exact bᵤ⁻¹,
        rw [mul_comm _ _] at h6,
        rw [h6, ←mul_assoc, ←@to_unit_is_unit_val_eq _ _ b _, ←units.val_coe],
        rw [units.inv_mul],
        simp
      },
      simp [h8]
    }
  }
end

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

lemma ne_zero_of_is_unit [semiring α] {a : α} (h : (0 : α) ≠ 1) : is_unit a → a ≠ 0 :=
begin
  intro h1,
  by_contradiction h2,
  simp at h2,
  rw h2 at h1,
  have : ¬ is_unit (0 : α),
  from not_is_unit_zero h,
  contradiction
end

lemma is_unit_unit_mul_unit {a b : α} [semiring α] (h1 : is_unit a) (h2 : is_unit b) : is_unit (a * b) :=
begin
  let aᵤ := to_unit h1,
  let bᵤ := to_unit h2,
  simp only [is_unit],
  fapply exists.intro,
  exact (aᵤ*bᵤ),
  simp
end

lemma not_unit_of_irreducible {a : α}[integral_domain α](h : irreducible a) : ¬ (is_unit a) :=
begin
  exact and.elim_left (and.elim_right h)
end

lemma dvd_irreducible_of_dvd_mul_unit_irreducible {a b c: α}[integral_domain α](h2 : is_unit b)(h3 : irreducible c)(h4 : a ∣ (b * c)) : a ∣ c :=
begin
  simp [has_dvd.dvd] at h4,
  let bᵤ := to_unit h2,
  let d := some h4,
  have h5 : b * c = a * d,
  from some_spec h4,
  simp [has_dvd.dvd],
  fapply exists.intro,
  exact d*bᵤ.inv,
  {
    --rw ←@to_unit_is_unit_val_eq _ _ b h2 at h5,
    calc c = 1 * c : by simp
    ... = (↑bᵤ⁻¹* ↑bᵤ) * c : by rw [←units.inv_mul _]
    ... = ↑bᵤ⁻¹ * (↑bᵤ * c) : by simp [mul_assoc]
    ... = ↑bᵤ⁻¹ * (b * c): by rw [to_unit_is_unit_eq]
    ... = ↑bᵤ⁻¹ * (a * d): by rw h5
    ... = bᵤ.inv * (a * d): by rw [units.inv_coe]
    ... = (a * d) * bᵤ.inv : by simp [mul_assoc, mul_comm]
    ... = a * (d * bᵤ.inv) : by simp [mul_assoc]
  }
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


--Why protected??
@[trans] protected lemma associated.trans [integral_domain α] {x y z: α} (h1 : x ~ᵤ y)(h2 : y ~ᵤ z): x ~ᵤ z :=
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

lemma associated.eqv [integral_domain α] : equivalence (@associated α _) :=
mk_equivalence (@associated α _) (@associated.refl α _) (@associated.symm α _) (@associated.trans α _)


--Problem with 'a' in the namespace
lemma irreducible_of_associated {γ : Type u}[integral_domain γ]{p b : γ}(h1 : irreducible p)(h2 : p ~ᵤ b) : irreducible b :=
begin
  --rw [associated] at h2,
  let u:= some h2,
  have h3 : p = ↑u * b,
  from some_spec h2,

  have h4 : (p ≠ 0),
  from and.elim_left h1,
  have h5 : (¬ is_unit p),
  from and.elim_left (and.elim_right h1),
  have h6 : (∀c, (c∣p → (is_unit c ∨ (c ~ᵤ p)))),
  from and.elim_right (and.elim_right h1),

  have h7 : (b ≠ 0),
  {
    by_contradiction h5,
    simp at h5,
    have : p = 0,
    {simp [h5, h3]},
    contradiction,
  },
  have h8 : (¬ is_unit b),
  {
    by_contradiction,
    have : is_unit ↑u,
    {
      constructor,
      swap,
      exact u,
      simp
    },
    have h9 : is_unit (↑u * b),
    from is_unit_unit_mul_unit this a,
    rw ←h3 at h9,
    contradiction,
  },
  have h9 : (∀c, (c∣b → (is_unit c ∨ (c ~ᵤ b)))),
  {
    intros c h9,
    by_cases h10 : is_unit c,
    {
      simp [h10],
    },
    {
      simp [has_dvd.dvd] at h9,
      let d := some h9,
      have h11 : b = c * d,
      from some_spec h9,
      have h12 :↑(u⁻¹) * p = b,
      {
        rw [h3, ←mul_assoc, units.inv_mul],
        simp
      },
      rw ←h12 at h11,
      have h13 : p = ↑u * (c * d),
      {
        rw [←h11, ←mul_assoc, units.mul_inv],
        simp
      },
      have h14 : c ∣ p,
      {
        rw [←mul_assoc, mul_comm _ c, mul_assoc] at h13,
        simp [h13],
      },
      have h15 : (c~ᵤ p),
      {
        have h16: is_unit c ∨ (c~ᵤ p),
        from h6 c h14,
        cases h16,
        {contradiction},
        {
          assumption,
        }
        
      },
      have h16 : (c~ᵤ b),
      {exact h15.trans h2},
      simp [h16],
    }
  },
  exact ⟨h7,h8,h9⟩, 
end

lemma unit_mul_irreducible_is_irreducible'  {γ : Type u}[integral_domain γ]{a b : γ}(h1 : is_unit a)(h2 : irreducible b) : irreducible (a * b) :=
begin
  let aᵤ := to_unit h1,
  have h3 : (b ~ᵤ (a*b)),
  {
    constructor,
    swap,
    exact aᵤ⁻¹,
    rw [←mul_assoc, ←@to_unit_is_unit_val_eq _ _ a _, ←units.val_coe, units.inv_mul],
    simp
  },
  exact irreducible_of_associated h2 h3
end

lemma zero_associated_zero  {γ : Type u}[integral_domain γ] : (0 : γ) ~ᵤ 0 :=
begin
  simp [associated],
  fapply exists.intro,
  exact 1,
  exact true.intro
end

lemma associated_of_mul_eq_one {γ : Type u}[integral_domain γ]{a b : γ}(h1 : a * b = 1) : a ~ᵤ b :=
begin
  have h2 : b * a = 1,
  {
    rw mul_comm a b at h1,
    exact h1
  },
  have h3 : a * a * (b * b) = 1,
  {
    rw [←mul_assoc, @mul_assoc _ _ a a _, h1], 
    simp [h1]
  },
  have h4 : b * b * (a * a) = 1,
  {
    rw [mul_comm _ _] at h3,
    exact h3
  },
  rw associated,
  fapply exists.intro,
  {
    exact units.mk (a * a) (b * b) h3 h4,
  },
  {
    rw [units.val_coe],
    simp [mul_assoc, h1]
  }
end

def unit_of_mul_eq_one {γ : Type u}[integral_domain γ]{a b : γ} (h1 : a * b = 1) : units γ :=
units.mk a b h1 (by {rw mul_comm _ _ at h1, exact h1})

lemma associated_of_dvd_dvd {γ : Type u} [integral_domain γ] {a b : γ}
  (h1 : a ∣ b) (h2 : b ∣ a) : a ~ᵤ b :=
begin
  simp only [has_dvd.dvd] at *,
  let c := some h2,
  have h3 : a = b * c,
  from some_spec h2,
  let d := some h1,
  have h4 : b = a * d,
  from some_spec h1,

  by_cases h6 : (a = 0),
  {
    have h7 : (b = 0),
    {
      rw h6 at h4,
      simp at h4,
      exact h4,
    },
    rw [h6, h7]
  },
  {
    have h3b : a = a * (d * c),
    {
      rw [h4, mul_assoc] at h3,
      exact h3,
    },
    
    have h5 : a * 1 = a * (d * c),
    {simp, exact h3b}, 
    have h7 : 1 = (d * c),
    from eq_of_mul_eq_mul_left h6 h5,
    rw associated,
    rw mul_comm _ _ at h7,
    fapply exists.intro,
    exact unit_of_mul_eq_one (eq.symm h7),
    rw [unit_of_mul_eq_one, units.val_coe],
    simp,
    rw h3,
    exact mul_comm _ _,
  }
end

lemma associated_zero_iff_eq_zero {α : Type u} {a : α} [integral_domain α] : (a ~ᵤ (0 : α)) ↔ a = 0 :=
begin
  constructor,
  {
    intro h1,
    rw [associated] at h1,
    let u := some h1,
    have h2: a = u * 0,
    from some_spec h1,
    simp [h2],
  },
  {
    intro h1,
    rw h1
  }
end

inductive rel_multiset {α β : Type u} (r : α → β → Prop) : multiset α → multiset β → Prop
| nil : rel_multiset {} {}
| cons : ∀a b xs ys, r a b → rel_multiset xs ys → rel_multiset (a::xs) (b::ys)
--Can we do an induction on rel_multiset?


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

def facs_to_pow  [monoid α] (p : α →₀ ℕ ) : finset α:= p.support.image (λ a, a^(p a))

--correct?
lemma facs_to_pow_prod_dvd [integral_domain α] {f : α →₀ ℕ} {z : α}(h1 : (∀ x ∈ (finsupp.support f), irreducible x ∧ (x^(f x))∣z ∧ (∀y ∈ finsupp.support f,x ≠ y →  ¬ (x ~ᵤ y)) )) : f.prod (λ x y, x^y) ∣ z:=
sorry

--gcds
class has_gcd (α : Type u) [comm_semiring α] :=
(gcd : α → α → α) (gcd_right : ∀ a b, ( (gcd a b) ∣ b )) (gcd_left : ∀ a b, (gcd a b) ∣ a) (gcd_min : ∀ a b g, g∣a → g∣b → g∣ (gcd a b))

def gcd [comm_semiring α] [has_gcd α] : α → α → α := has_gcd.gcd
def gcd_min [comm_semiring α] [h : has_gcd α]  := h.gcd_min --Correct???
def gcd_left [comm_semiring α] [h : has_gcd α] {a b : α }  := has_gcd.gcd_left a b --use {a b : α}?
def gcd_right [comm_semiring α] [h : has_gcd α] {a b : α } := has_gcd.gcd_right a b
def is_gcd [has_dvd α] (a b d :α) :=  d∣a ∧  d∣b ∧  (∀x, x∣a →  x∣b → x∣d)

lemma gcd_zero_zero_eq_zero {α : Type u} [comm_semiring α][has_gcd α] : gcd (0 : α) 0 = 0 :=
begin
  by_contradiction,
  have h1 : (0 : α)∣0,
  {simp},
  have h2 : 0 ∣ (gcd (0 : α) 0),
  from gcd_min _ _ _ h1 h1,
  have : (gcd (0 : α) 0) = 0,
  from eq_zero_of_zero_dvd h2,
  contradiction
end

lemma gcd_zero_associated_left {α : Type u} [integral_domain α][has_gcd α] {f : α} : (gcd f (0 : α)) ~ᵤ f :=
begin
  apply associated_of_dvd_dvd,
  exact gcd_left,
  apply gcd_min,
  simp,
  simp
end

lemma gcd_zero_associated_right {α : Type u} [integral_domain α][has_gcd α] {f : α} : (gcd (0 : α) f) ~ᵤ f :=
begin
  apply associated_of_dvd_dvd,
  exact gcd_right,
  apply gcd_min,
  simp,
  simp
end

lemma gcd_eq_zero_iff_eq_zero_and_eq_zero {α : Type u} [integral_domain α][has_gcd α] {f g : α}  : gcd f g = 0 ↔ f = 0 ∧ g = 0:=
begin
  constructor,
  {
     intro h1,
     by_contradiction h2,
     have h3 : ¬(g = 0 ∧ f = 0),
     {
       rw and.comm at h2,
       exact h2
     },
     simp at *,
     by_cases h4 : (f = 0),
     { 
       have h5 : g ≠ 0,
       from h2 h4,
       rw h4 at h1,
       have h6 : ((gcd 0 g) ~ᵤ g),
       from gcd_zero_associated_right,
       rw [h1] at h6,
       have h7 : (g ~ᵤ 0),
       from associated.symm h6,
       rw [associated_zero_iff_eq_zero] at h7,
       contradiction,
     },
     {
       apply h4,
       apply eq_zero_of_zero_dvd,
       rw ← h1,
       exact gcd_left,
     }

  },
  {
    intro h1,
    have h2 : f = 0,
    from and.elim_left h1,
    have h3 : g = 0,
    from and.elim_right h1,
    rw [h2, h3],
    exact gcd_zero_zero_eq_zero
  }
end

namespace associated

variables (α) [unique_factorization_domain α]

def setoid : setoid α :=
{ r := associated, iseqv := associated.eqv }
local attribute [instance] setoid

def quot : Type u := quotient (associated.setoid α)

variables {α}

@[reducible] def mk (a : α) : quot α := ⟦ a ⟧

instance : has_zero (quot α) := ⟨⟦ 0 ⟧⟩
instance : has_one (quot α) := ⟨⟦ 1 ⟧⟩
instance : has_mul (quot α) :=
⟨λa' b', quotient.lift_on₂ a' b' (λa b, ⟦ a * b ⟧) $
  assume a₁ a₂ b₁ b₂ ⟨c₁, h₁⟩ ⟨c₂, h₂⟩, quotient.sound $
  ⟨c₁ * c₂, by simp [h₁, h₂, mul_assoc, mul_comm, mul_left_comm]⟩⟩

instance : comm_monoid (quot α) :=
{ one       := 1,
  mul       := (*),
  mul_one   := assume a', quotient.induction_on a' $
    assume a, show ⟦a * 1⟧ = ⟦ a ⟧, by simp,
  one_mul   := assume a', quotient.induction_on a' $
    assume a, show ⟦1 * a⟧ = ⟦ a ⟧, by simp,
  mul_assoc := assume a' b' c', quotient.induction_on₃ a' b' c' $
    assume a b c, show ⟦a * b * c⟧ = ⟦a * (b * c)⟧, by rw [mul_assoc],
  mul_comm  := assume a' b', quotient.induction_on₂ a' b' $
    assume a b, show ⟦a * b⟧ = ⟦b * a⟧, by rw [mul_comm] }

instance : partial_order (quot α) :=
{ le := λa b, ∃c, a * c = b,
  le_refl := assume a, ⟨1, by simp⟩,
  le_trans := assume a b c ⟨f₁, h₁⟩ ⟨f₂, h₂⟩,
    ⟨f₁ * f₂, h₂ ▸ h₁ ▸ (mul_assoc _ _ _).symm⟩,
  le_antisymm := assume a' b',
    quotient.induction_on₂ a' b' $ assume a b ⟨f₁', h₁⟩ ⟨f₂', h₂⟩,
    (quotient.induction_on₂ f₁' f₂' $ assume f₁ f₂ h₁ h₂,
      let ⟨c₁, h₁⟩ := quotient.exact h₁.symm, ⟨c₂, h₂⟩ := quotient.exact h₂.symm in
      quotient.sound $ associated_of_dvd_dvd
        (h₁.symm ▸ dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
        (h₂.symm ▸ dvd_mul_of_dvd_right (dvd_mul_right _ _) _)) h₁ h₂ }

def irred (a : quot α) : Prop :=
quotient.lift_on a irreducible $
assume a b h, propext $ iff.intro
  (assume h', irreducible_of_associated h' h)
  (assume h', irreducible_of_associated h' h.symm)

lemma prod_mk {p : multiset α} : (p.map mk).prod = ⟦ p.prod ⟧ :=
multiset.induction_on p (by simp; refl) $
  assume a s ih, by simp [ih]; refl

--#print prefix rel_multiset
--set_option trace.simplify.rewrite true
--set_option trace.class_instances true
#print prefix multiset
#print prefix rel_multiset
#print prefix unique_factorization_domain
--#check multiset.no_confusion
#print prefix quot

--set_option pp.notation false

--lemma 

#check quot.exact

--naming?
lemma complete {a b : α} : mk a = mk b → (a ~ᵤ b) :=
begin
 intro h1,
 simp * at *,
 exact h1,
end

lemma forall_associated_of_map_eq_map : ∀(p q : multiset α),
  p.map mk = q.map mk → rel_multiset associated p q :=
begin
assume p,
  apply multiset.induction_on p,
  {
    intro q,
    simp * at *,
    by_cases h1 : (q = 0),
    {
      simp * at *,
      exact rel_multiset.nil _, 
    },
    {
      intro h2,
      have h3 : ∃ a, a ∈ q,
      from multiset.exists_mem_of_ne_zero h1,
      let a := some h3,
      have h4 : a ∈ q,
      from some_spec h3,
      have h5 : mk a ∈ (multiset.map mk q),
      from multiset.mem_map_of_mem mk h4,
      rw ← h2 at h5,
      by_contradiction h6,
      exact multiset.not_mem_zero _ h5,
    }

  },
  intros a p h1 q h3,
  simp * at *,
  have h4 : mk a ∈ multiset.map mk q,
  {
    rw ← h3,
    simp,
  },
  have h5 : ∃ t', multiset.map mk q = mk a :: t',
  from multiset.exists_cons_of_mem h4,
  let t' := some h5,
  have h6 : multiset.map mk q = mk a :: t',
  from some_spec h5,
  have h7 : ∃ b : α, b ∈ q ∧ mk b = mk a,
  {
    rw multiset.mem_map at h4,
    exact h4,
  },
  let b := some h7,
  have h8 : b ∈ q ∧ mk b = mk a,
  from some_spec h7,
  have h9 : ∃ t, q = b :: t,
  from multiset.exists_cons_of_mem (and.elim_left h8),
  let t := some h9,
  have h10 : q = b :: t,
  from some_spec h9,
  rw h10,
  have h11 : mk a = mk b,
  exact eq.symm (and.elim_right h8),
  apply rel_multiset.cons,
  {
    rw mk at h11,
    rw mk at h11,
    exact complete h11,
  },
  {
    apply h1 _,
    rw h10 at h3,
    simp at h3,
    rw [h11, multiset.cons_inj_right] at h3,
    exact h3,
  }

end

lemma multiset_eq (p q : multiset α) :
  rel_multiset associated p q ↔ p.map mk = q.map mk :=
begin
  constructor,
  {
    intro h1,
    induction h1 with a b h1 h2 h3 h4 h5,
    {
      exact rfl,
    },
    {
      simp [h5],
      exact h3
    },
  },
  {
    exact forall_associated_of_map_eq_map _ _
  },
end


lemma representation (a' : quot α) : a' ≠ 0 →
  ∃p : multiset (quot α), (∀a∈p, irred a) ∧ a' = p.prod :=
quotient.induction_on a' $ assume a, sorry -- TODO: jens

example (p : multiset (quot α)) : ∃q:multiset α, p = q.map mk :=
multiset.induction_on p ⟨0, rfl⟩ $
  assume a', quotient.induction_on a' $ assume a p ⟨q, hq⟩,
  ⟨a :: q, by simp [hq]⟩

lemma uniqueness (p q : multiset (quot α))
  (hp : ∀a∈p, irred a) (hq : ∀a∈q, irred a)
  (h : p.prod = q.prod) : p = q :=
sorry -- TODO: jens

def to_multiset (a : quot α) : multiset (quot α) :=
if h : a = 0 then 0 else classical.some (representation a h)

lemma to_multiset_prod_eq (a : quot α) (h : a ≠ 0) :
  (to_multiset a).prod = a :=
_

lemma prod_le_prod_of_subset {p q : multiset (quot α)} (h : p ⊆ q) : p.prod ≤ q.prod :=
_

lemma prod_le_prod_iff_subset {p q : multiset (quot α)}
  (hp : ∀a∈p, irred a) (hq : ∀a∈q, irred a) :
  p.prod ≤ q.prod ↔ p ⊆ q :=
_


instance : lattice.semilattice_inf (quot α) :=
{ inf := λa b, (to_multiset a ∩ to_multiset b).prod,
  inf_le_left := assume a b, _,
  inf_le_right := _,
  le_inf := _,
  .. associated.partial_order
}

/-
lemma exists_gcd (a b : quot α) (ha : a ≠ 0) (hb : b ≠ 0) : 
  ∃c, c ≤ a ∧ c ≤ b ∧ (∀d, d ≤ a → d ≤ b → d ≤ c) :=
_
-/

end associated





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


def rel_prime {γ : Type u} [unique_factorization_domain γ] (a b : γ) := is_unit (gcd a b)

lemma  rel_prime_mul_of_rel_prime_of_rel_prime_of_rel_prime {α : Type u}{a b c: α} [unique_factorization_domain α] (h1 : rel_prime a b)(h2 : rel_prime b c)(h3 : rel_prime c a) : rel_prime (a*b) c :=
sorry
lemma mul_dvd_of_dvd_of_dvd_of_rel_prime {α : Type u}{a b c: α} [unique_factorization_domain α] (h1 : rel_prime a b)(h2 : a ∣ c)(h3 : b ∣ c) : (a * b) ∣ c:=
sorry

lemma rel_prime_comm {γ : Type u} [unique_factorization_domain γ] {a b : γ} : rel_prime a b → rel_prime b a :=
sorry

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