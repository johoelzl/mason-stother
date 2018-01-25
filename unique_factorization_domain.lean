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

lemma mul_inv'' {t : Type u}[semiring t] {x : t} (h : is_unit x) :  x * (to_unit h).inv = 1 :=
begin
  exact calc x * (to_unit h).inv = (to_unit h).val * (to_unit h).inv : by simp
  ... = 1 : (to_unit h).val_inv
end

lemma inv_mul'' {t : Type u}[semiring t] {x : t} (h : is_unit x) :  (to_unit h).inv * x = 1 :=
begin
  exact calc (to_unit h).inv * x = (to_unit h).inv * (to_unit h).val : by simp
  ... = 1 : (to_unit h).inv_val
end

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

lemma unit_associated_one [integral_domain α] {u : units α}: (u : α) ~ᵤ 1 :=
⟨u, by simp⟩

lemma is_unit_left_iff_exists_mul_eq_one [comm_semiring α] {a: α} : (is_unit a) ↔ ∃ b, a * b = 1 :=
begin
  constructor,
  {
    intro h1,
    fapply exists.intro,
    exact ((to_unit h1) : units α).inv,
    {
      simp [mul_inv'' h1],
    }
  },
  {
    intro h1,
    let b := some h1,
    have h2 : a * b = 1,
    from some_spec h1,
    rw is_unit,
    have h3 :b * a = 1,
    { rw [mul_comm a b]at h2, exact h2},
    fapply exists.intro,
    {
      exact ⟨a, b, h2, h3⟩
    },
    exact rfl
  }
end

lemma is_unit_right_iff_exists_mul_eq_one [comm_semiring α] {b: α} : (is_unit b) ↔ ∃ a, a * b = 1 :=
begin
  have h1 : (is_unit b) ↔ ∃ a, b * a = 1,
  from @is_unit_left_iff_exists_mul_eq_one _ _ b,
  constructor,
  {
    intro h2,
    rw h1 at h2,
    let a := some h2,
    have h3 : b * a = 1,
    from some_spec h2,
    rw mul_comm b a at h3,
    exact ⟨a, h3⟩
  },
  {
    intro h2,
    rw h1,
    let a := some h2,
    have h3 : a * b = 1,
    from some_spec h2,
    rw mul_comm a b at h3,
    exact ⟨a, h3⟩,
  }
end


lemma is_unit_of_associated {γ : Type u}[integral_domain γ]{p b : γ}(h1 : is_unit p)(h2 : p ~ᵤ b) : is_unit b :=
begin
  rw associated at h2,
  rw is_unit_left_iff_exists_mul_eq_one at h1,
  let u := some h2,
  have h3 : p = ↑u * b,
  from some_spec h2,
  let q := some h1,
  have h4 : p * q = 1,
  from some_spec h1,
  have h5 : (q * ↑u) * b = 1,
  {
    exact calc (q * ↑u) * b = q * (↑u * b) : by simp only [mul_assoc]
    ... = q * p : by rw h3
    ... = p * q : by simp [mul_comm]
    ... = _ : h4,
  },
  rw is_unit_right_iff_exists_mul_eq_one,
  exact ⟨(q * ↑u), h5⟩
end

lemma asssociated_one_iff_is_unit [integral_domain α] {a : α} : (a ~ᵤ 1) ↔ is_unit a :=
begin
  constructor,
  {
    intro h1,
    rw associated at h1,
    let u := some h1,
    have h2: a = ↑u * 1,
    from some_spec h1,
    have h3 : ↑(u⁻¹) * a = 1,
    {
      exact calc ↑u⁻¹ * a = ↑u⁻¹ * (↑u * 1) : by rw h2
      ... = (↑u⁻¹ * ↑u) * 1 : by simp [mul_assoc]
      ... = 1 : by simp [units.inv_mul]
    },

    rw is_unit_right_iff_exists_mul_eq_one,
    exact ⟨↑u⁻¹, h3⟩,
  },
  {
    intro h1,
    have h2 : ↑(to_unit h1) = a,
    {simp},
    rw ←h2,
    exact unit_associated_one
    
  }
end

--naming
lemma prod_not_is_unit_eq_one_iff_eq_zero [integral_domain α] {p : multiset α}: (∀ a, a ∈ p → (¬ (is_unit a))) → (p.prod = 1 ↔ p = 0) :=
begin

  by_cases h1 : (p = 0),
  {
    simp [h1]
  },
  {
    have h2 : ∃a , a ∈ p,
    from multiset.exists_mem_of_ne_zero h1,
    let h := some h2,
    have h3 : h ∈ p,
    from some_spec h2,
    have h4 : ∃ t, p = h :: t,
    from multiset.exists_cons_of_mem h3,
    let t := some h4,
    have h5 : p = h :: t,
    from some_spec h4,
    intro h6,
    constructor,
    {
      intro h7,
      rw h5 at h7,
      simp at h7,
      rw mul_comm h _ at h7,
      have h8 : is_unit h,
      {
        rw is_unit_right_iff_exists_mul_eq_one,
        exact ⟨multiset.prod t, h7⟩,
      },
      have h9 : h ∈ p,
      {rw h5, simp},
      have : ¬is_unit h,
      from h6 h h9,
      contradiction,
    },
    {
      intro h7,
      simp *,
    }
  }
end

--Should also make a right.
lemma is_unit_left_of_is_unit_mul [comm_semiring α] {a b : α} : is_unit (a * b) → is_unit a :=
begin
  intro h1,
  let u := to_unit h1,
  have h2 : a * (b* (↑u⁻¹ : α) ) = 1,
  {
    exact calc a * (b* (↑u⁻¹ : α) ) = (a * b) * (↑u⁻¹ : α) : by rw ← mul_assoc
    ... = u.val * (↑u⁻¹ : α) : by rw ← @to_unit_is_unit_val_eq _ _ (a * b) _
    ... = u.val * u.inv : by rw units.inv_coe
    ... = 1 : u.val_inv,
  },
  rw @is_unit_left_iff_exists_mul_eq_one _ _ a,
  exact ⟨(b * ↑u⁻¹), h2 ⟩,
end

inductive rel_multiset {α β : Type u} (r : α → β → Prop) : multiset α → multiset β → Prop
| nil : rel_multiset {} {}
| cons : ∀a b xs ys, r a b → rel_multiset xs ys → rel_multiset (a::xs) (b::ys)
--Can we do an induction on rel_multiset?


class unique_factorization_domain (α : Type u) extends integral_domain α :=
(fac : ∀{x : α}, x ≠ 0 → ¬ is_unit x → ∃ p : multiset α, x = p.prod ∧ (∀x∈p, irreducible x))
(unique : ∀{f g : multiset α}, (∀x∈f, irreducible x) → (∀x∈g, irreducible x) → f.prod = g.prod → rel_multiset associated f g)



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

lemma mk_def {a : α} : mk a = ⟦a⟧ := rfl

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


--Can we say something aboutthe addition?, can we lift addition?

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

@[simp] lemma mk_zero_eq_zero : mk (0 : α) = 0 := rfl

def irred (a : quot α) : Prop :=
quotient.lift_on a irreducible $
assume a b h, propext $ iff.intro
  (assume h', irreducible_of_associated h' h)
  (assume h', irreducible_of_associated h' h.symm)

def is_unit_quot (a : quot α) : Prop :=
quotient.lift_on a is_unit $
assume a b h, propext $ iff.intro
begin
  intro h1,
  apply is_unit_of_associated h1,
  exact h
end
begin
  intro h1,
  have h2 : b ≈ a,
  {cc},
  apply is_unit_of_associated h1,
  exact h2
end

#check irred._proof_1
--We don't need this one I think.
lemma irreducible_iff_mk_irred {a : α} : irreducible a ↔ irred (mk a) :=
begin
  --rw propext,
  constructor,
  {
    
    intro h1,
    exact h1, --Importatnt to understand this
  },
  {
    intro h1,
    exact h1, --Why does it work the other wat?
  }
end


lemma prod_mk {p : multiset α} : (p.map mk).prod = ⟦ p.prod ⟧ :=
multiset.induction_on p (by simp; refl) $
  assume a s ih, by simp [ih]; refl

lemma mul_mk {a b : α} : mk (a * b) = mk a * mk b :=
rfl

lemma zero_def : (0 : quot α) = ⟦ 0 ⟧ :=
rfl

lemma one_def : (1 : quot α) = ⟦ 1 ⟧ :=
rfl

lemma mul_zero {a : quot α} : a * 0 = 0 :=
begin
  let a' := quot.out a,
  have h1 : mk a' = a,
  from quot.out_eq _,
  rw [←h1, zero_def, ← mul_mk],
  simp,
  exact rfl,
end

lemma zero_mul {a : quot α} : 0 * a = 0 :=
begin
  let a' := quot.out a,
  have h1 : mk a' = a,
  from quot.out_eq _,
  rw [←h1, zero_def, ← mul_mk],
  simp,
  exact rfl,
end

--naming?
lemma complete {a b : α} : mk a = mk b → (a ~ᵤ b) :=
begin
 intro h1,
 simp * at *,
 exact h1,
end

lemma mk_eq_mk_iff_associated {a b : α} : mk a = mk b ↔ (a ~ᵤ b) :=
⟨ complete, quot.sound ⟩ 

lemma mk_eq_zero_iff_eq_zero {a : α} : mk a = 0 ↔ a = 0 :=
begin
  constructor,
  {
    intro h1,
    have h2 : (a ~ᵤ 0),
    from complete h1,
    rw associated_zero_iff_eq_zero at h2,
    exact h2,   
  },
  {
     intro h1,
     rw h1,
     simp,
  }
end

lemma ne_one_of_irred {a : quot α} : irred a → a ≠ 1 :=
begin
  apply quotient.induction_on a,
  intro a,
  intro h1,
  have h2 : irreducible a,
  from h1,
  rw ne.def,
  rw [associated.has_one],
  rw mk_eq_mk_iff_associated,
  by_contradiction h3,
  have h4 : ¬ (is_unit a),
  from and.elim_left ( and.elim_right h2),
  rw asssociated_one_iff_is_unit at h3,
  contradiction,
end
/-
lemma irred_iff_ne_zero {a : quot α} : irred a ↔ a ≠ 0 :=
begin
  constructor,
  {
    apply quotient.induction_on a,
    intro a,
    intro h1,
    rw [ne.def, ← mk_def, mk_eq_zero_iff_eq_zero],
    have h2 : irreducible a,
    from h1,
    exact and.elim_left h1,       
  },

end-/

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

#check factorization

--correct simp?
@[simp] lemma mk_unit_eq_one {u : units α} : mk (u : α) = 1 := 
begin
  apply quot.sound,
  exact unit_associated_one
end
#check mk_eq_zero_iff_eq_zero

lemma mk_eq_one_iff_is_unit {a : α} : mk a = 1 ↔ is_unit a :=
begin
  constructor,
  {
    intro h1,
    have h2 : is_unit_quot (mk a),
    {
      rw h1,
      exact is_unit_one
    },
    {
      exact h2,
    }
  },
  {
    intro h1,
    rw ←@to_unit_is_unit_eq _ _ a _,
    exact mk_unit_eq_one,
    exact h1,
  }
end

lemma representation (a' : quot α) : a' ≠ 0 →
  ∃p : multiset (quot α), (∀a∈p, irred a) ∧ a' = p.prod :=
quotient.induction_on a' $ assume a, 
begin
  intro h1,
  have h2 : a ≠ 0,
  { rw [ne.def],rw [ ← mk_eq_zero_iff_eq_zero], exact h1},
  have h3 : ∃ u : units α, ∃ p : multiset α, a = u*p.prod ∧ (∀x∈p, irreducible x),
  from factorization h2,
  let u := some h3,
  have h4: ∃ p : multiset α, a = u*p.prod ∧ (∀x∈p, irreducible x),
  from some_spec h3,
  let p := some h4,
  have h5: a = u*p.prod ∧ (∀x∈p, irreducible x),
  from some_spec h4,
  have h5a : a = ↑u * multiset.prod p,
  from and.elim_left h5,
  have h5b : ∀ (x : α), x ∈ p → irreducible x,
  from and.elim_right h5,
  fapply exists.intro,
  {
    exact multiset.map mk p,
  },
  {
    constructor,
    {
      intros b' h6,
      rw multiset.mem_map at h6,
      let b := some h6,
      have h7 : b ∈ p ∧ mk b = b',
      from some_spec h6,
      have h8 : irreducible b,
      from h5b _ (and.elim_left h7),
      rw ←(and.elim_right h7),
      exact h8
    },
    {
      rw h5a,
      rw [←mk, mul_mk],
      simp,
      rw prod_mk  
    }
  }
end

lemma exists_eq_map_mk (p : multiset (quot α)) : ∃q:multiset α, p = q.map mk :=
multiset.induction_on p ⟨0, rfl⟩ $ 
  assume a', quotient.induction_on a' $ assume a p ⟨q, hq⟩,
  ⟨a :: q, by simp [hq]⟩

--Doens't this hold already for not is_unit? admit done, do we need this one.
 lemma prod_not_is_unit_quot_eq_one_iff_eq_zero {p : multiset (quot α)}: (∀ (a : quot α), a ∈ p → (¬ is_unit_quot a)) → (p.prod = 1 ↔ p = 0) :=
 begin
  intro h1a,
  constructor,
  {
    intro h2a,
    by_contradiction h1,
    have h2 : ∃a , a ∈ p,
    from multiset.exists_mem_of_ne_zero h1,
    let h := some h2,
    have h3 : h ∈ p,
    from some_spec h2,
    have h4 : ∃ t, p = h :: t,
    from multiset.exists_cons_of_mem h3,
    let t := some h4,
    have h5 : p = h :: t,
    from some_spec h4,
    rw h5 at h2a,
    simp at h2a,
    have h6 : ¬is_unit_quot h,
    from h1a h h3,
    let h' := quot.out h,
    have h7 : mk h' = h,
    from quot.out_eq h,
    have h8 : ∃t':multiset α, t = t'.map mk,
    from exists_eq_map_mk _,
    let t' := some h8,
    have h9 : t = t'.map mk,
    from some_spec h8,
    rw [h9, prod_mk, ←h7, ←mul_mk] at h2a,
    have h10 : ((h' * (multiset.prod t')) ~ᵤ (1 : α)),
    from complete h2a,
    rw asssociated_one_iff_is_unit at h10,
    --have h11: is_unit_quot (mk (h' * multiset.prod t')),
    --from h10,
    have h12 : is_unit h',
    from is_unit_left_of_is_unit_mul h10,
    have h13 : is_unit_quot (mk h'),
    from h12,
    rw h7 at h13,
    contradiction,
  },
  {
    intro h1,
    simp *,
  }
 end

lemma prod_irred_quot_eq_one_iff_eq_zero {p : multiset (quot α)}: (∀ (a : quot α), a ∈ p → (irred a)) → (p.prod = 1 ↔ p = 0) :=
begin
  intro h1,
  have h2 : ∀ (a : quot α), a ∈ p → (¬  is_unit_quot a),
  {
    intros b h2,
    have h3 : irred b,
    from h1 b h2,
    let b' := quot.out b,
    have h4  : mk b' = b,
    from quot.out_eq _,
    rw ← h4 at h3,
    have h5 : irreducible b',
    from h3,
    have h6 : ¬ is_unit b',
    from and.elim_left (and.elim_right h5),
    rw ← h4,
    exact h6,
  },
  apply prod_not_is_unit_quot_eq_one_iff_eq_zero,
  exact h2,
end


--#check --(has_mul α).mul

lemma uniqueness (p q : multiset (quot α))
  (hp : ∀a∈p, irred a) (hq : ∀a∈q, irred a)
  (h : p.prod = q.prod) : p = q :=
begin
  by_cases h1a : (p = 0),
  {
    rw h1a at h,
    simp at h,
    have h2 : multiset.prod q = 1,
    from eq.symm h,
    rw prod_irred_quot_eq_one_iff_eq_zero hq at h2,
    simp *,
  },
  {
    by_cases h1b : (q = 0),
    {
      rw h1b at h,
      simp at h,
      rw prod_irred_quot_eq_one_iff_eq_zero hp at h,
      simp *,
    },
    {
      have h1 : ∃p':multiset α, p = p'.map mk,
      from exists_eq_map_mk p,
      have h2 : ∃q':multiset α, q = q'.map mk,
      from exists_eq_map_mk q, 
      let p' := some h1,
      have h3 : p = p'.map mk,
      from some_spec h1,
      let q' := some h2,
      have h4 : q = q'.map mk,
      from some_spec h2,
      have h5 : p' ≠ 0,
      {
        by_contradiction h6,
        simp at h6,
        rw h6 at h3,
        simp at h3,
        contradiction,
      },
      have h6 : q' ≠ 0,
      {
        by_contradiction h6,
        simp at h6,
        rw h6 at h4,
        simp at h4,
        contradiction,
      },

      --attempt
       rw [h3, h4, prod_mk, prod_mk] at h,
       have h7 : (multiset.prod p' ~ᵤ multiset.prod q'),
       from complete h,
       rw associated at h7,
       let u := some h7,
       have h8 : multiset.prod p' = ↑u * multiset.prod q',
       from some_spec h7,
       have h9 : ∃ h, h ∈ q',
       from multiset.exists_mem_of_ne_zero h6,
       let h := some h9,
       have h10 : h ∈ q',
       from some_spec h9,
       have h11 : ∃ t, q' = h :: t,
       from multiset.exists_cons_of_mem h10,
       let t := some h11,
       have h12 : q' = h :: t,
       from some_spec h11,
       rw h12 at h8,
       simp at h8,
       rw ←mul_assoc at h8,
       let h' := ↑u * h,
       have h13 : ∀ (a : α), a ∈ p' → irreducible a,
       {
         intros a h1,
         have h13 : mk a ∈ p,
         {
           rw h3,
           exact multiset.mem_map_of_mem mk h1,
         },
         exact hp _ h13,
       },
      have h14 : ∀ (a : α), a ∈ q' → irreducible a,
       {
         intros a h1,
         have h14 : mk a ∈ q,
         {
           rw h4,
           exact multiset.mem_map_of_mem mk h1,
         },
         exact hq _ h14,
       },
       have h15 : multiset.prod p' = multiset.prod (h'::t),
       {simp [h8],},
       have h16 : ∀ (a : α), a ∈ (h' :: t) → irreducible a,
       {
         intros a h1,
         rw multiset.mem_cons at h1,
         cases h1 with ha ha,
         rw ha,
         apply unit_mul_irreducible_is_irreducible',
         rw is_unit,
         exact ⟨u, rfl⟩,
         exact h14 _ h10,
         have h16 : a ∈ h :: t,
         {simp [ha], },
         rw ← h12 at h16,
         exact h14 _ h16,
       },
       have h17 : rel_multiset associated p' (h' :: t),
       from unique_factorization_domain.unique h13 h16 h15,
       rw multiset_eq at h17,
       have h18 : multiset.map mk (h' :: t) = multiset.map mk q',
       {
         have h18 : mk h' = mk h,
         {
           rw mul_mk,
           simp,
         },
         rw h12,
         simp,
         exact complete h18,
       },
       rw [←h17, ← h3, ← h4] at h18,
       exact h18,
    }
  }
end

def to_multiset (a : quot α) : multiset (quot α) :=
if h : a = 0 then 0 else classical.some (representation a h)

lemma to_multiset_prod_eq (a : quot α) (h : a ≠ 0) :
  (to_multiset a).prod = a :=
begin
  
  rw to_multiset,
  --rw ne.def at h,
  simp * at *,
  have h1 : a = multiset.prod (some _),
  from and.elim_right (some_spec (representation a h)),
  exact eq.symm h1,
end

--Think it should be le not subset
--lemma prod_le_prod_of_subset {p q : multiset (quot α)} (h : p ⊆ q) : p.prod ≤ q.prod :=
lemma prod_le_prod_of_le {p q : multiset (quot α)} (h : p ≤ q) : p.prod ≤ q.prod :=
begin
  have h1 : p + (q - p) = q,
  from multiset.add_sub_of_le h,
  rw ← h1,
  simp,
  fapply exists.intro,
  exact multiset.prod (q - p),
  exact rfl,
end

lemma zero_ne_one : (0 : quot α) ≠ 1 :=
begin
  by_contradiction h1,
  simp [not_not] at *,
  have h2 : ((0 : α) ~ᵤ (1 : α)),
  {
    rw [zero_def, one_def] at h1,
    exact complete h1,
  },
  have h3 : ((1 : α) ~ᵤ (0 : α)),
  from associated.symm h2,
  rw associated_zero_iff_eq_zero at h3,
  have h4 : (0 : α) ≠ 1,
  from zero_ne_one,
  have h5 : (0 : α) = 1,
  from eq.symm h3,
  contradiction,
end 

lemma prod_le_prod_iff_subset {p q : multiset (quot α)}
  (hp : ∀a∈p, irred a) (hq : ∀a∈q, irred a) :
  p.prod ≤ q.prod ↔ p ≤ q :=
begin
  constructor,
  {
    intro h1,
    simp only [has_le.le, preorder.le, partial_order.le] at h1,
    let c := some h1,
    have h2 :  multiset.prod p * c = multiset.prod q,
    from some_spec h1,
    by_cases h3 : (c = 0),
    {
      rw h3 at h2,
      simp [mul_zero] at h2,
      by_cases h4  : (q = 0),
      {
        rw h4 at h2,
        simp at h2,
        by_contradiction h5,
        exact zero_ne_one h2,
      },
      {
        have h5 : ∃ h, h ∈ q,
        from multiset.exists_mem_of_ne_zero h4,
        let h := some h5,
        have h6 :  h ∈ q,
        from some_spec h5,
        have h7 : ∃ t, q = h :: t,
        from multiset.exists_cons_of_mem h6,
        let t := some h7,
        have h8 : q = h :: t,
        from some_spec h7,
        admit,
      }
    },
    {
      have h4 : ∃p : multiset (quot α), (∀a∈p, irred a) ∧ c = p.prod,
      from representation _ h3,
      let c' := some h4,
      have h5 : (∀a∈c', irred a) ∧ c = c'.prod,
      from some_spec h4,
      have h5b : c = c'.prod,
      from and.elim_right h5,
      rw h5b at h2,
      rw ←multiset.prod_add at h2,
      have h6 : ∀ (a : quot α), a ∈ (p + c') → irred a,
      {
        simp,
        intros a h6,
        cases h6,
        exact hp a h6,
        exact (and.elim_left h5) a h6,
      },
      have h7 : p + c' = q,
      from uniqueness _ _ h6 hq h2,
      rw ← h7,
      exact multiset.le_add_right _ _,
    }

  },
  {
    exact prod_le_prod_of_le,
  }
end


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
