import data.finsupp
import algebra.ring
import .to_finset
import .to_multiset

noncomputable theory

local infix ^ := monoid.pow

open classical
local attribute [instance] prop_decidable

universe u
variable {α : Type u}

--Would it have been smart to define units as a type that lives in Prop??
--Or would this have been pointless because a Prop cannot contain data? It could have been made with exisential quatifier, but than we are in the same situation that we are in now.

def is_unit {t : Type u}[semiring t] (a : t) : Prop := ∃b : units t, a = b

/-
We might want to define composite numbers:
With a possible defintion: a product of at least two irred elem.
-/

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

local notation a `~ᵤ` b : 50 := associated a b


def prime {t : Type u}[integral_domain t] (p : t) : Prop := 
p ≠ 0 ∧ ¬ is_unit p ∧ ∀ a b, p ∣ (a * b) → (p ∣ a ∨ p ∣ b)


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

--correct simp?
@[simp] lemma is_unit_one [semiring α] : is_unit (1 : α ) := --existential in is unit is anoying.
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


lemma is_unit_mul_of_is_unit_of_is_unit {a b : α} [semiring α] (h1 : is_unit a) (h2 : is_unit b) : is_unit (a * b) :=
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
    from is_unit_mul_of_is_unit_of_is_unit this a,
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

--How is this usefull?
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

lemma dvd_dvd_of_associated {γ : Type u} [integral_domain γ] {a b : γ}
   : (a ~ᵤ b) → ( a ∣ b) ∧ ( b ∣ a):=
begin
  intro h1,
  rw associated at h1,
  let u := some h1,
  have h2 : a = ↑u * b,
  from some_spec h1,
  have h3 : ↑u * b = a,
  from eq.symm h2,
  constructor,
  {
    have h3 : u.inv * a = b,
    {
      exact calc u.inv * a = u.inv * (↑u * b) : by rw h2
      ... = (u.inv * u.val) * b : by simp [units.val_coe, mul_assoc]
      ... = b : by simp [u.inv_val]
    },
    exact dvd.intro_left _ h3,
  },
  {
    exact dvd.intro_left _ h3,
  }
end

lemma dvd_dvd_iff_associated {γ : Type u} [integral_domain γ] {a b : γ}
   : (a ~ᵤ b) ↔ ( a ∣ b) ∧ ( b ∣ a):=
⟨dvd_dvd_of_associated, 
begin
  intro h1,
  have h1a : a ∣ b,
  from and.elim_left h1,
  have h1b : b ∣ a,
  from and.elim_right h1,
  exact associated_of_dvd_dvd h1a h1b,

end⟩ 



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

lemma is_unit_right_of_is_unit_mul [comm_semiring α] {a b : α} : is_unit (a * b) → is_unit b :=
begin
  rw mul_comm a b,
  exact is_unit_left_of_is_unit_mul,
end

lemma is_unit_of_mul_eq_one_left [comm_semiring α] {a b : α} (h : a * b = 1): is_unit a :=
begin
  rw is_unit_left_iff_exists_mul_eq_one,
  exact ⟨b , h⟩
end

lemma is_unit_of_mul_eq_one_right [comm_semiring α] {a b : α} (h : a * b = 1): is_unit b :=
begin
  rw is_unit_right_iff_exists_mul_eq_one,
  exact ⟨a , h⟩
end



lemma irreducible_of_prime {α : Type u}[integral_domain α] {p : α} (h1 : prime p) : irreducible p :=
begin
  rw prime at h1,
  --rw irreducible,
  have h2 : (p ≠ 0),
  {
    from and.elim_left h1,
  },
  have h3 : (¬ is_unit p),
  from and.elim_left (and.elim_right h1),
  rw [irreducible_iff_irreducible', irreducible'],
  have h4 : ∀ (a b : α), p = a * b → is_unit a ∨ is_unit b,
  {
    intros b c h4a,
    by_cases h4b : (b = 0),
    {
      simp [h4b] at h4a,
      contradiction,
    },
    {
      by_cases h4c : (c = 0),
      {
        simp [h4c] at h4a,
        contradiction,       
      }, --no indent here
      have h4 : p ∣ (b * c),
      {
        simp *,
      },
      have h5 : p ∣ b ∨ p ∣ c,
      from and.elim_right (and.elim_right h1) b c h4,
      cases h5,
      {
        have h6 : b ∣ b * c,
        {simp},
        have h7 : b ∣ p,
        {
          apply dvd.trans h6,
          simp *,
        },
        have h8 : (p ~ᵤ b),
        from associated_of_dvd_dvd h5 h7,
        rw associated at h8,
        let u := some h8,
        have h9 : p = ↑u * b,
        from some_spec h8,
        rw [h9, mul_comm b c] at h4a,
        have h10 : ↑u = c,
        from eq_of_mul_eq_mul_right_of_ne_zero h4b h4a,
        have h11 : is_unit c,
        {
          fapply exists.intro u,
          exact eq.symm h10,
        },
        simp *,
      },
      {
        have h6 : c ∣ b * c,
        {simp},
        have h7 : c ∣ p,
        {
          apply dvd.trans h6,
          simp *,
        },
        have h8 : (p ~ᵤ c),
        from associated_of_dvd_dvd h5 h7,
        rw associated at h8,
        let u := some h8,
        have h9 : p = ↑u * c,
        from some_spec h8,
        rw [h9] at h4a,
        have h10 : ↑u = b,
        from eq_of_mul_eq_mul_right_of_ne_zero h4c h4a,
        have h11 : is_unit b,
        {
          fapply exists.intro u,
          exact eq.symm h10,
        },
        simp *,
      }
    }
  },
  exact ⟨h2, h3, h4 ⟩   
end

inductive rel_multiset {α β : Type u} (r : α → β → Prop) : multiset α → multiset β → Prop
| nil : rel_multiset ∅ ∅
| cons : ∀a b xs ys, r a b → rel_multiset xs ys → rel_multiset (a::xs) (b::ys)

lemma rel_multiset_def {α β : Type u} {r : α → β → Prop} {x : multiset α} {y : multiset β} :
  rel_multiset r x y ↔
    ((x = ∅ ∧ y = ∅) ∨ (∃a b x' y', r a b ∧ rel_multiset r x' y' ∧ x = a :: x' ∧ y = b :: y')) :=
iff.intro
  (assume h,
    match x, y, h with
    | _, _, (rel_multiset.nil r) := or.inl ⟨rfl, rfl⟩
    | _, _, (rel_multiset.cons a b x y r r') := or.inr ⟨a, b, x, y, r, r', rfl, rfl⟩
    end)
  (assume h,
    match x, y, h with
    | _, _, or.inl ⟨rfl, rfl⟩ := rel_multiset.nil r
    | _, _, or.inr ⟨a, b, x, y, r, r', rfl, rfl⟩ := rel_multiset.cons a b x y r r'
    end)

open multiset

lemma multiset.cons_ne_empty {α : Type u} (a : α) (as : multiset α) : a :: as ≠ ∅ :=
assume h,
have a ∈ a :: as, by simp,
have a ∈ (∅ : multiset α), from h ▸ this,
not_mem_zero a this

--Can we do an induction on rel_multiset?
lemma rel_multiset.cons_right {α β: Type u} {r : α → β → Prop} {as : multiset α} {bs : multiset β} {b : β} :
  rel_multiset r as (b :: bs) → ∃a' as', as = (a' :: as') ∧ r a' b ∧ rel_multiset r as' bs :=
begin
  generalize hbs' : (b :: bs) = bs',
  intro h,
  induction h generalizing bs,
  case rel_multiset.nil { exact (multiset.cons_ne_empty _ _ hbs').elim },
  case rel_multiset.cons : a b' as bs' hr₁ hr' ih {
    by_cases b_b' : b = b',
    { subst b_b',
      have h : bs = bs', from (cons_inj_right b).1 hbs',
      subst h,
      exact ⟨_, _, rfl, hr₁, hr'⟩ },
    exact (
      have b ∈ b' :: bs', by rw [← hbs']; simp,
      have b ∈ bs', by simpa [b_b'],
      have b :: bs'.erase b = bs', from cons_erase this,
      let ⟨a'', as'', eq, hr₂, hr''⟩ := ih this in
      have ih' : rel_multiset r (a :: as'') (b' :: bs'.erase b),
        from rel_multiset.cons _ _ _ _ hr₁ hr'',
      have b' :: bs'.erase b = bs,
        by rw [← erase_cons_tail, ← hbs', erase_cons_head]; exact ne.symm b_b',
      ⟨a'', a :: as'', by simp [eq, cons_swap], hr₂, this ▸ ih'⟩
    )
  }
end

class unique_factorization_domain (α : Type u) extends integral_domain α :=
(fac : ∀{x : α}, x ≠ 0 → ¬ is_unit x → ∃ p : multiset α, x = p.prod ∧ (∀x∈p, irreducible x))
(unique : ∀{f g : multiset α},
  (∀x∈f, irreducible x) → (∀x∈g, irreducible x) → f.prod = g.prod → rel_multiset associated f g)


--Lemma that every element not zero can be represented as a product of a unit with prod primes.
lemma factorization [unique_factorization_domain α] :
  ∀{x : α}, x ≠ 0 → ∃ u : units α, ∃ p : multiset α, x = u*p.prod ∧ (∀x∈p, irreducible x) :=
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
class has_gcd (α : Type u) [comm_semiring α] := --can we define it for comm_monoid?
(gcd : α → α → α)
(gcd_right : ∀ a b, gcd a b ∣ b)
(gcd_left  : ∀ a b, gcd a b ∣ a)
(gcd_min   : ∀ a b g, g ∣ a → g ∣ b → g ∣ gcd a b)



section gcd_sr
variables [comm_semiring α] [has_gcd α] {a b c : α}

def gcd : α → α → α := has_gcd.gcd
def gcd_min := has_gcd.gcd_min a b c  --Correct???
def gcd_left := has_gcd.gcd_left a b --use {a b : α}?
def gcd_right := has_gcd.gcd_right a b


def rel_prime (a b : α) := is_unit (gcd a b)


@[simp] lemma gcd_zero_zero_eq_zero : gcd (0 : α) 0 = 0 :=
begin
  by_contradiction,
  have h1 : (0 : α)∣0,
  {simp},
  have h2 : 0 ∣ (gcd (0 : α) 0),
  from gcd_min h1 h1,
  have : (gcd (0 : α) 0) = 0,
  from eq_zero_of_zero_dvd h2,
  contradiction
end


end gcd_sr

section gcd_id
variables [integral_domain α] [has_gcd α] {a b c : α}

lemma gcd_zero_associated_left {f : α} : (gcd f (0 : α)) ~ᵤ f :=
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

--Isn't it associated?
lemma gcd_comm : (gcd a b ~ᵤ  gcd b a) :=
begin
  apply associated_of_dvd_dvd,
  {
    have h1 : gcd a b ∣ a,
    from gcd_left,
    have h2 : gcd a b ∣ b,
    from gcd_right,
    exact gcd_min h2 h1,
  },
  {
    have h1 : gcd b a ∣ b,
    from gcd_left,
    have h2 : gcd b a ∣ a,
    from gcd_right,
    exact gcd_min h2 h1,
  }
end

end gcd_id


namespace associated -- Can we Prove the existence of a gcd here? Problem is has_dvd, why is it not defined here??
--If we can show the existence of a gcd here, we can reuse some lemmas

variables (α) [unique_factorization_domain α]

def setoid : setoid α :=
{ r := associated, iseqv := associated.eqv }
local attribute [instance] setoid

def quot : Type u := quotient (associated.setoid α)

variables {α}

@[reducible] def mk (a : α) : quot α := ⟦ a ⟧

lemma mk_def {a : α} : mk a = ⟦a⟧ := rfl
lemma mk_def' {a : α} : mk a = quot.mk setoid.r a := rfl

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

@[simp] lemma mul_zero {a : quot α} : a * 0 = 0 :=
begin
  let a' := quot.out a,
  have h1 : mk a' = a,
  from quot.out_eq _,
  rw [←h1, zero_def, ← mul_mk],
  simp,
  exact rfl,
end

@[simp] lemma zero_mul {a : quot α} : 0 * a = 0 :=
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



--correct simp?
@[simp] lemma mk_unit_eq_one {u : units α} : mk (u : α) = 1 := 
begin
  apply quot.sound,
  exact unit_associated_one
end


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

lemma some_spec_representation (a' : quot α) (h : a' ≠ 0) : 
(∀a∈(some (representation a' h)), irred a) ∧ a' = (some (representation a' h)).prod :=
some_spec (representation a' h)


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

lemma prod_eq_prod_iff_eq (p q : multiset (quot α))
  (hp : ∀a∈p, irred a) (hq : ∀a∈q, irred a) :
  p.prod = q.prod ↔ p = q :=
iff.intro 
(uniqueness p q hp hq)
(assume h, h ▸ rfl)


def to_multiset (a : quot α) : multiset (quot α) :=
if h : a = 0 then 0 else classical.some (representation a h)

@[simp] lemma to_multiset_zero : to_multiset (0 : quot α) = 0 :=
begin
  simp [to_multiset]
end

--Name is a bit wrong should have been prod_to_multiset_eq
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

lemma to_multiset_irred' (a : quot α) (h : a ≠ 0) : 
∀ x ∈ to_multiset a, irred x :=
begin
  intros x h1,
  
  have h2 : (∀ (x : quot α), x ∈ (to_multiset a) → irred x) ∧ a = multiset.prod (to_multiset a),
  {
    rw [to_multiset],
    simp * at *,
    from (some_spec (representation a h)),
  },
  apply and.elim_left h2,
  exact h1, 
end

lemma to_multiset_irred (a : quot α) : ∀x∈to_multiset a, irred x :=
begin
  by_cases h : a = 0, 
  { simp [*] },
  { exact to_multiset_irred' _ h }
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

lemma mul_ne_zero {a' b' : quot α} (h1 : a' ≠ 0) (h2 : b' ≠ 0) : a' * b' ≠ 0 :=
begin
  let a := quot.out a',
  have h3 : mk a = a',
  from quot.out_eq a',
  let b := quot.out b',
  have h4 : mk b = b',
  from quot.out_eq b',
  rw [←h3, ←h4, ← mul_mk],
  rw [←h3, ne.def, mk_eq_zero_iff_eq_zero] at h1,
  rw [← h4, ne.def, mk_eq_zero_iff_eq_zero] at h2,
  rw [ne.def, mk_eq_zero_iff_eq_zero],
  exact mul_ne_zero h1 h2,
end

--Can possibly be simplified, because we have prod_ne_zero_of_ne_zero
lemma prod_ne_zero_of_irred {q : multiset (quot α)}: (∀ (a : quot α), a ∈ q → irred a) → multiset.prod q ≠ 0 :=
begin
  apply multiset.induction_on q,
  {
    intro h1,
    simp,
    apply ne.symm,
    exact zero_ne_one,  
  },
  {
    intros a' s h1 h2,
    simp,
    have h3 : irred a',
    {
      apply h2 a',
      simp,
    },
    have h4 : (∀ (a : quot α), a ∈ s → irred a),
    {
      intros a h4,
      apply h2 a, 
      simp *,
    },
    have h5 : multiset.prod s ≠ 0,
    from h1 h4,
    let a := quot.out a',
    have h6 : mk a = a',
    from quot.out_eq a',
    rw ← h6 at h3,
    have h7 : irreducible a,
    from h3,
    have h9 : a ≠ 0,
    from and.elim_left h7,
    have h10 : mk a ≠ 0,
    {
      rw [ne.def, mk_eq_zero_iff_eq_zero],
      exact h9,
    },
    apply mul_ne_zero,
    {
      rw h6 at h10,
      exact h10,    
    },
    exact h5,

  }
end

--is eq_one better then is_unit_quot?
lemma is_unit_quot_of_mul_eq_one_left [unique_factorization_domain α] {a b : quot α} (h : a * b = 1) : is_unit_quot a :=
begin
  revert h,
  apply quot.induction_on a,
  apply quot.induction_on b,
  intros a' b' h,
  rw [←mk_def',←mk_def',←mul_mk, mk_eq_one_iff_is_unit] at h,
  have h1 : is_unit_quot (mk (b' * a')),
  from h,
  have h2 : is_unit b',
  from is_unit_left_of_is_unit_mul h1,
  exact h2,
end

lemma is_unit_quot_of_mul_eq_one_right [unique_factorization_domain α] {a b : quot α} (h : a * b = 1) : is_unit_quot b :=
begin
  rw mul_comm at h,
  exact is_unit_quot_of_mul_eq_one_left h,
end



lemma not_is_unit_quot_of_irred {a : quot α} (h : irred a) : ¬ is_unit_quot a :=
begin
  revert h,
  apply quot.induction_on a,
  intros a h,
  have : irreducible a,
  from h,
  have : ¬ is_unit a,
  from this.2.1,
  exact this,
end


@[simp] lemma to_multiset_one : to_multiset (1 : quot α) = 0 :=
begin
  by_contradiction h1,
  have h2 : ∃x, x ∈ (to_multiset 1),
  from exists_mem_of_ne_zero h1,
  rcases h2 with ⟨x, hx⟩,
  have h3 : ∃t, (to_multiset 1) = x :: t,
  from exists_cons_of_mem hx,
  rcases h3 with ⟨t, ht⟩,
  have h4 : irred x,
  from to_multiset_irred _ _ hx,
  have h5 : (to_multiset (1 : quot α)).prod = 1,
  from to_multiset_prod_eq _ (@ne.symm (quot α) _ _ zero_ne_one),
  rw ht at h5,
  simp at h5,
  have h6 : is_unit_quot x,
  from is_unit_quot_of_mul_eq_one_left h5,
  have : ¬ is_unit_quot x,
  from not_is_unit_quot_of_irred h4,
  contradiction,
end

lemma prod_ne_one_of_ne_zero_of_irred {q : multiset (quot α)} (h : q ≠ 0) : (∀ (a : quot α), a ∈ q → irred a) → multiset.prod q ≠ 1 :=
begin
  revert h,
  apply multiset.induction_on q,
  {
    simp * at *,
  },
  {
    intros a s h1 h2 h3,
    simp * at *,
    by_contradiction h4,
    have h5 : is_unit_quot a,
    from is_unit_quot_of_mul_eq_one_left h4,
    have : ¬is_unit_quot a,
    {
      apply not_is_unit_quot_of_irred,
      apply h3,
      simp,
    },
    contradiction,
  }
end

lemma to_multiset_mul {a b : quot α} (h1 : a ≠ 0) (h2 : b ≠ 0): to_multiset (a * b) = to_multiset a + to_multiset b :=
begin
  have h3 : a * b ≠ 0,
  from mul_ne_zero h1 h2,
  have h4 : multiset.prod (to_multiset (a * b)) = a * b,
  from to_multiset_prod_eq _ h3,
  have h5 : multiset.prod (to_multiset (a)) = a,
  from to_multiset_prod_eq _ h1,
  have h6 : multiset.prod (to_multiset (b)) = b,
  from to_multiset_prod_eq _ h2,
  apply uniqueness,
  {
    apply to_multiset_irred
  },
  {
    intros x h7,
    simp at h7,
    cases h7,
    {
      apply to_multiset_irred,
      exact h7,
    },
    {
      apply to_multiset_irred,
      exact h7,
    }

  },
  rw multiset.prod_add,
  simp * at *,
  end

--should be le
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
        have h5 : multiset.prod q ≠ 0,
        from prod_ne_zero_of_irred hq,
        have h6 : multiset.prod q = 0,
        from eq.symm h2,
        contradiction,        
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



lemma le_def {a b : quot α} : a ≤ b = ∃ c, a * c = b := rfl

instance : lattice.order_bot (quot α) :=
{ bot := 1,
  bot_le := assume a, ⟨a, one_mul a⟩,
  .. associated.partial_order }

instance : lattice.order_top (quot α) :=
{ top := 0,
  le_top := assume a, ⟨0, mul_zero⟩,
  .. associated.partial_order }

lemma eq_zero_of_zero_le {a : quot α} : 0 ≤ a → a = 0 := lattice.top_unique

--0 is the largest element, division order
@[simp] lemma one_le_zero : (1 : quot α) ≤ (0 : quot α) := lattice.bot_le 

def inf (a b : quot α) :=
if a = 0 then b else if b = 0 then a else (to_multiset a ∩ to_multiset b).prod



def sup (a b : quot α) := 
if a = 0 then 0 else if b = 0 then 0 else (to_multiset a ∪ to_multiset b).prod


lemma bot_def : ⊥ = (1 : quot α) := rfl
lemma top_def : ⊤ = (0 : quot α) := rfl

lemma zero_is_top (a : quot α) : a ≤ 0 := ⟨0, mul_zero⟩

lemma inf_comm (a b : quot α) : inf a b = inf b a :=
by by_cases ha0 : a = 0; by_cases hb0 : b = 0; simp [*, inf, inter_comm]

--left or right?
@[simp] lemma sup_zero_eq_zero_left {a : quot α} : sup 0 a = 0 :=
by simp [sup]

@[simp] lemma sup_zero_eq_zero_right {a : quot α} : sup a 0 = 0 :=
by simp [sup]

lemma sup_comm {a b : quot α} : sup a b = sup b a :=
by by_cases ha0 : a = 0; by_cases hb0 : b = 0; simp [*, sup, union_comm]

lemma le_sup_left {a b : quot α} : a ≤ sup a b :=
begin
  by_cases ha0 : a = 0,
  {simp *,},
  by_cases hb0 : b = 0,
  {simp [*, zero_is_top],},
  {
    simp [sup, *],
    exact calc a = (to_multiset a).prod : eq.symm $ to_multiset_prod_eq _ ha0
    ... ≤ prod (to_multiset a ∪ to_multiset b) : 
    begin
      rw prod_le_prod_iff_subset,
      exact le_union_left _ _,
      exact to_multiset_irred _,
      intros x h,
      simp at *,
      cases h ; {apply to_multiset_irred, assumption}  
    end
  }
end

lemma le_sup_right {a b : quot α} : b ≤ sup a b:=
by rw [sup_comm]; exact le_sup_left

lemma inf_le_left {a b : quot α} : inf a b ≤ a :=
begin
  by_cases ha0 : a = 0,
  { simp [ha0, zero_is_top] },
  by_cases hb0 : b = 0,
  { simp [inf, *] },
  { simp [inf, *],
    exact calc prod (to_multiset a ∩ to_multiset b) ≤ prod (to_multiset a) :
        by rw [prod_le_prod_iff_subset];
          simp [to_multiset_irred a, multiset.inter_le_left] {contextual := tt}
      ... = a : to_multiset_prod_eq _ ha0 }
end

lemma inf_le_right {a b : quot α} : inf a b ≤ b :=
by rw [inf_comm]; exact inf_le_left

lemma sup_le {a b c : quot α} (hab : b ≤ a) (hac : c ≤ a) : sup b c ≤ a  :=
begin
  by_cases hb0 : b = 0, { simp [sup, hb0, hac] at *, assumption},
  by_cases hc0 : c = 0, { simp [sup, hb0, hc0, hab] at *, assumption },
  by_cases ha0 : a = 0, {simp [*, zero_is_top] at *},
  simp [sup, *],
  rw [←to_multiset_prod_eq a ha0] at *,
  rw [←to_multiset_prod_eq b hb0] at hab,
  rw [←to_multiset_prod_eq c hc0] at hac,
  rw prod_le_prod_iff_subset at *,
  exact union_le hab hac, --union in multiset acts like the sup on our type.
  simp * at *,
  intros x h1,
  cases h1 ; {apply to_multiset_irred, assumption},
  repeat {apply to_multiset_irred},
end

lemma le_inf {a b c : quot α} (hab : a ≤ b) (hac : a ≤ c) : a ≤ inf b c :=
begin
  by_cases hb0 : b = 0, { simp [inf, hb0, hac] },
  by_cases hc0 : c = 0, { simp [inf, hb0, hc0, hab] },
  rcases hab with ⟨ab, hb⟩,
  rcases hac with ⟨ac, hc⟩,
  have ha0 : a ≠ 0, { intro ha0, simp [*, zero_mul] at * },
  have hab0 : ab ≠ 0, { intro ha0, simp [*, mul_zero] at * },
  have hac0 : ac ≠ 0, { intro ha0, simp [*, mul_zero] at * },
  simp [inf, hb0, hc0],
  rw [← hb, ← hc, to_multiset_mul ha0 hab0, to_multiset_mul ha0 hac0,
      ← add_inter_distrib, ← to_multiset_prod_eq a ha0]
    {occs := occurrences.pos [1]},
  rw [prod_le_prod_iff_subset (to_multiset_irred a)],
  exact multiset.le_add_right _ _,
  simp [or_imp_distrib, (to_multiset_irred ab)] {contextual := tt},
  exact (to_multiset_irred a)
end

open lattice

instance : semilattice_inf_top (quot α) := --We need bot aswell
{ inf := inf, 
  inf_le_left := assume a b, inf_le_left,
  inf_le_right := assume a b, inf_le_right,
  le_inf := assume a b c, le_inf,
  top := 0,
  le_top := assume a, zero_is_top _,
  .. associated.partial_order }

lemma one_le :  ∀ (a : quot α), 1 ≤ a :=
assume a, ⟨a, by simp⟩

instance : bounded_lattice (quot α) := --We need bot aswell
{ inf := inf, 
  inf_le_left := assume a b, inf_le_left,
  inf_le_right := assume a b, inf_le_right,
  le_inf := assume a b c, le_inf,
  top := 0,
  le_top := assume a, zero_is_top _,
  sup := sup,
  le_sup_left := assume a b, le_sup_left,
  le_sup_right := assume a b, le_sup_right,
  sup_le := assume a b c, sup_le,
  bot := 1,
  bot_le := assume a, one_le _,

  .. associated.partial_order }

lemma sup_def {a b : quot α} : a ⊔ b =
if a = 0 then 0 else if b = 0 then 0 else (to_multiset a ∪ to_multiset b).prod:=
rfl

lemma inf_def {a b : quot α} : a ⊓ b = if a = 0 then b else if b = 0 then a else (to_multiset a ∩ to_multiset b).prod :=
rfl

instance : semilattice_inf_bot (quot α) := --We need bot aswell
{ inf := inf, 
  inf_le_left := assume a b, inf_le_left,
  inf_le_right := assume a b, inf_le_right,
  le_inf := assume a b c, le_inf,
  bot := 1,
  bot_le := one_le,
  .. associated.partial_order }





lemma mul_mono {a b c d : quot α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
let ⟨x, hx⟩ := h₁, ⟨y, hy⟩ := h₂ in
⟨x * y, by simp [hx.symm, hy.symm, mul_comm, mul_assoc, mul_left_comm]⟩

@[simp] lemma inf_zero {a : quot α} : a ⊓ 0 = a := @inf_top_eq (quot α) _ a
@[simp] lemma zero_inf {a : quot α} : 0 ⊓ a = a := @top_inf_eq (quot α) _ a

@[simp] lemma sup_zero {a : quot α} : a ⊔ 0 = 0 := @sup_top_eq (quot α) _ a
@[simp] lemma zero_sup {a : quot α} : 0 ⊔ a = 0 := @top_sup_eq (quot α) _ a

lemma eq_of_mul_eq_mul {a b c : quot α} : a ≠ 0 → a * b = a * c → b = c :=
quotient.induction_on₃ a b c $ assume a b c h eq, 
  have a ≠ 0, from assume h', h $ mk_eq_zero_iff_eq_zero.2 h',
  let ⟨d, hd⟩ := complete eq in
  have a * b = a * (↑d * c), by simpa [mul_assoc, mul_comm, mul_left_comm] using hd,
  quotient.sound ⟨d, eq_of_mul_eq_mul_left_of_ne_zero ‹a ≠ 0› this⟩

lemma le_of_mul_le_mul {a b c : quot α} (h : a ≠ 0) : a * b ≤ a * c → b ≤ c
| ⟨d, hd⟩ :=
  have b * d = c, from eq_of_mul_eq_mul h $ by simpa [mul_assoc] using hd,
  ⟨d, this⟩

lemma le_mul_right {a b : quot α} : a ≤ a * b := ⟨b, rfl⟩ 

lemma le_mul_left {a b : quot α} : a ≤ b * a := by rw [mul_comm]; exact le_mul_right

lemma mul_inf {a b c : quot α} : a * (b ⊓ c) = (a * b) ⊓ (a * c) :=
begin
  by_cases a = 0, { simp [h, zero_mul] },
  have : a ≤ (a * b) ⊓ (a * c),
    from le_inf ⟨b, rfl⟩ ⟨c, rfl⟩,
  rcases this with ⟨x, hx⟩, 
  exact le_antisymm
    (le_inf (mul_mono (le_refl a) inf_le_left) (mul_mono (le_refl a) inf_le_right))
    begin
      rw [← hx],
      apply mul_mono (le_refl a),
      apply le_inf (le_of_mul_le_mul h _) (le_of_mul_le_mul h _),
      { rw [hx], apply inf_le_left },
      { rw [hx], apply inf_le_right }
    end
end

--Easier proof then the proof above! Note that there is a latice isomorfime, from the set of multiset of irreducible elements to α excluding 0.
--Can this be used for a more efficient omplementation.
lemma mul_inf' {a b c : quot α} : a * (b ⊓ c) = (a * b) ⊓ (a * c) :=
begin
  by_cases ha0 : a = 0, { simp * at *,},
  by_cases hb0: b = 0, {simp * at *,},
  by_cases hc0: c = 0, {simp * at *,},
  have hab : a * b ≠ 0,
  from mul_ne_zero ha0 hb0,  
  have hac : a * c ≠ 0,
  from mul_ne_zero ha0 hc0,
  simp [inf_def, sup_def, to_multiset_mul, *],
  rw [multiset.add_comm (to_multiset a) _, multiset.add_comm (to_multiset a) _],
  rw [ ←multiset.inter_add_distrib],
  rw [←prod_mul_prod_eq_add_prod, to_multiset_prod_eq _ ha0, mul_comm],
end

lemma sup_mul_inf {a b : quot α} : (a ⊔ b) * (a ⊓ b) = a * b :=
begin
  by_cases ha0 : a = 0,
    {simp [*] at *},
  by_cases hb0 : b = 0,
    {simp [*] at *},
  simp [inf_def, sup_def, *],   
  rw [←to_multiset_prod_eq a ha0, ←to_multiset_prod_eq b hb0] {occs := occurrences.pos [3]},
  rw [prod_mul_prod_eq_add_prod, prod_mul_prod_eq_add_prod],
  simp [multiset.union_add_inter], --Again the properties from multiset carry over
end

lemma dvd_of_mk_le_mk {a b : α} (h : mk a ≤ mk b) : a ∣ b :=
let ⟨c', hc'⟩ := h in
(quotient.induction_on c' $ assume c (hc : mk (a * c) = mk b),
  have (a * c) ~ᵤ b, from complete hc,
  let ⟨d, hd⟩ := this.symm in
  ⟨d * c, by simp [mul_comm, mul_assoc, hd]⟩) hc'

lemma mk_le_mk_of_dvd {a b : α} (h : a ∣ b) : mk a ≤ mk b :=
let ⟨c, hc⟩ := h in ⟨mk c, by simp [hc]; refl⟩

lemma dvd_iff_mk_le_mk {a b : α} : a ∣ b ↔ mk a ≤ mk b :=
iff.intro mk_le_mk_of_dvd dvd_of_mk_le_mk

@[simp] lemma mk_quot_out {a : quot α} : mk (quot.out a) = a :=
quot.out_eq _

--I have a duplicate of this lemma with wrong naming: see dvd_right bla bla
--Do we use the case c = 0.
lemma le_of_le_mul_of_le_of_inf_eq_one {a b c : quot α} (h1 : a ⊓ b = 1) (h2 : a ≤ (c * b)) : a ≤ c :=
begin
    have h4: (c * a) ⊓ (c * b) = c,
    {
      rw  ←mul_inf,
      simp *,
    },
    have h5 : a ≤  (c * a) ⊓ (c * b),
    from le_inf le_mul_left h2,
    simp * at *,
end

lemma inf_assoc {a b c : quot α} : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) :=
begin
  have h1 : a ⊓ b ⊓ c ≤ a ⊓ b,
  from inf_le_left,
  have h2 : a ⊓ (b ⊓ c) ≤ (b ⊓ c),
  from inf_le_right,
  apply le_antisymm,
  {
    apply le_inf,
      exact le_trans h1 inf_le_left,
      exact le_inf (le_trans h1 inf_le_right) (inf_le_right),
  },
  {
    apply le_inf,
      exact le_inf (inf_le_left) (le_trans h2 inf_le_left),
      exact le_trans h2 inf_le_right,     
  }
end


--We need to prove the following
lemma mul_inf_eq_inf_of_inf_eq_one {a b c : quot α} (h : c ⊓ b = 1) : (c * a) ⊓ b = a ⊓ b :=
begin
  
  apply le_antisymm,
  {
    apply @le_of_le_mul_of_le_of_inf_eq_one _ _ _ c,
    rw lattice.inf_comm at h,
    rw @inf_assoc _ _ (c * a ) b _,
    simp *,
    exact inf_bot_eq,
    rw [mul_comm _ c, mul_inf],
    apply lattice.le_inf,
    exact inf_le_left,
    have h1 : c * a ⊓ b ≤ b,
    from inf_le_right,
    apply le_trans h1,
    exact le_mul_left,
  },
  exact (inf_le_inf le_mul_left (le_refl b)),

end

--naming??
lemma mul_le_of_le_of_le_of_rel_prime {a b c : quot α} (h1 : a ⊓ b = 1) (h2 : a ≤ c) (h3 : b ≤ c) : a * b ≤ c :=
begin
  rw [← sup_mul_inf],
  simp * at *,
end

lemma inf_def' {a b : quot α} : a ⊓ b = inf a b := 
rfl


lemma inf_le_inf_mul {a b c : quot α} : a ⊓ b ≤ a ⊓ (b * c) :=
begin
  apply le_inf,
  exact inf_le_left,
  exact le_trans inf_le_right le_mul_right
end

lemma inf_le_mul_inf {a b c : quot α} : a ⊓ b ≤ (a * c)  ⊓ b:=
begin
  rw [@lattice.inf_comm _ _ a _, @lattice.inf_comm _ _ _ b],
  exact inf_le_inf_mul,
end

lemma inf_mul_eq_one_iff_inf_eq_one_and_inf_eq_one {a b c : quot α} : a ⊓ (b * c) = 1 ↔ (a ⊓ b = 1 ∧ a ⊓ c = 1) :=
begin
  split,
  {
    intro h,
    have h1 : a ⊓ b ≤ a ⊓ (b * c),
    from inf_le_inf_mul,
    have h2 : a ⊓ c ≤ a ⊓ (b * c),
    {
      rw mul_comm at *,
      exact inf_le_inf_mul,
    },
    rw h at *,
    simp [bot_unique h1, bot_unique h2, bot_def, *] at *,
  },
  {
    intro h,
    rw [lattice.inf_comm],
    rw [mul_inf_eq_inf_of_inf_eq_one] ;
    simp [lattice.inf_comm, *] at *,
  }
end

--le_antisymm
  --_
  --(inf_le_inf le_mul_left (le_refl b))

lemma inf_eq_zero_iff_eq_zero_and_eq_zero {a b : quot α} : a ⊓ b = 0 ↔ a = 0 ∧ b = 0 :=
begin
  split,
  {
    by_cases ha : a = 0,
      {simp * at *},
      by_cases hb : b = 0,
        {simp * at *},
        simp [inf_def, *],
        intro h,
        have : prod (to_multiset a ∩ to_multiset b) ≠ 0,
        {
          apply prod_ne_zero_of_irred,
          intros x h1,
          simp at h1,
          apply to_multiset_irred a,
          exact h1.1,
        },
        contradiction,
  },
  {
    intro h,
    rw [h.1, h.2],
    simp [inf_def]    
  }     
end

lemma prod_to_mulitset_eq_one_iff_to_multiset_eq_zero {a : quot α} : (to_multiset a).prod = 1 ↔ (to_multiset a) = 0 :=
begin 
  split,
    {
      intro h,
      by_contradiction h4,
      have : prod (to_multiset a) ≠ 1,
      from prod_ne_one_of_ne_zero_of_irred h4 (to_multiset_irred _),
      contradiction,  
    },
    {
      intro h,
      simp * at *,
    } 
end



lemma to_multiset_ne_zero_of_ne_zero_of_ne_one {a : quot α} (h : a ≠ 0) (h1 : a ≠ 1): to_multiset a ≠ 0 :=
begin
  by_contradiction h2,
  simp at h2,
  have h3 : prod (to_multiset a) = a,
  from to_multiset_prod_eq _ h,
  simp * at *,
end

lemma to_multiset_eq_zero_iff_eq_zero_or_eq_one{a : quot α} : to_multiset a = 0 ↔ (a = 0 ∨ a = 1) :=
begin
  split,
  {
    rw [←not_imp_not, not_or_distrib],
    intro h,
    exact to_multiset_ne_zero_of_ne_zero_of_ne_one h.1 h.2,
  },
  {
    intro h,
    cases h,
      simp * at *,
      simp * at *,
  }
end

--Should be made stronger: all factors that are in a are in b --We might delete this one, because we have a stronger statement with a smaller proof.
lemma exists_mem_to_multiset_of_le {a b : quot α} (ha : a ≠ 0) (ha1 : a ≠ 1) (hb : b ≠ 0) (hb1 : b ≠ 1) (h : a ≤ b) : ∃x, x ∈ to_multiset a ∧ x ∈ to_multiset b :=
begin
  rw [le_def] at h,
  rcases h with ⟨c, hc⟩,
  by_cases h1 : c = 0,
    {simp * at *},
    rw [←to_multiset_prod_eq a ha, ←to_multiset_prod_eq b hb, ← to_multiset_prod_eq c h1] at hc,
    rw [prod_mul_prod_eq_add_prod, prod_eq_prod_iff_eq] at hc,
    have h2 :  (to_multiset a + to_multiset c).to_finset = (to_multiset b).to_finset,
    {simp * at *},
    rw finset.ext at h2,
    have h3 : to_multiset a ≠ 0,
    from to_multiset_ne_zero_of_ne_zero_of_ne_one ha ha1,
    rcases (exists_mem_of_ne_zero h3) with ⟨x, hx⟩,
    have h4 : x ∈ to_multiset b,
    {
      rw ← hc,
      simp [hx],
    },
    exact ⟨x, hx, h4⟩,
    {--Bad structuring
      simp,
      intros a h,
      cases h ;
        exact to_multiset_irred _ _ h,
    },
    exact to_multiset_irred _,
end

--Can this one be a iff?
lemma to_multiset_le_to_multiset_of_le {a b : quot α} (hb : b ≠ 0) (h : a ≤ b) : to_multiset a ≤ to_multiset b :=
begin
  by_cases ha : a = 0,
    {simp * at *},
    {
      rcases h with ⟨c, hc⟩,
      rw [←hc, to_multiset_mul],
      simp,
      exact ha,
      by_contradiction h1,
      simp * at *,
    }
end

lemma le_of_to_multiset_le_to_multiset {a b : quot α} (ha : a ≠ 0) (h : to_multiset a ≤ to_multiset b) : a ≤ b :=
begin
  by_cases hb : b = 0,
    {simp [*, zero_is_top] at *,},
    rw [←to_multiset_prod_eq a ha, ←to_multiset_prod_eq b hb, prod_le_prod_iff_subset],
    simp [*],
    exact to_multiset_irred _,
    exact to_multiset_irred _,
end

lemma le_iff_to_multiset_le_to_multiset_of_ne_zero_of_ne_zero {a b : quot α} (ha : a ≠ 0) (hb : b ≠ 0) : a ≤ b ↔ to_multiset a ≤ to_multiset b :=
iff.intro
  (to_multiset_le_to_multiset_of_le hb)
  (le_of_to_multiset_le_to_multiset ha)


lemma exists_mem_to_multiset_inf_ne_zero_of_inf_ne_one {a b : quot α} (ha : a ≠ 0) (hb : b ≠ 0) (h1 : a ⊓ b ≠ 0) (h2 : a ⊓ b ≠ 1) : ∃x, x ∈ to_multiset a ∧ x ∈ to_multiset b :=
begin
  have h3 : a ⊓ b ≤ a,
  from inf_le_left,
  have h4 : a ⊓ b ≤ b,
  from inf_le_right,
  have h5 : to_multiset (a ⊓ b) ≤ to_multiset a,
  {rw ←le_iff_to_multiset_le_to_multiset_of_ne_zero_of_ne_zero ; assumption},
  have h6 : to_multiset (a ⊓ b) ≤ to_multiset b,
  {rw ←le_iff_to_multiset_le_to_multiset_of_ne_zero_of_ne_zero ; assumption},
  have h7 : to_multiset (a ⊓ b) ≠ 0,
  from to_multiset_ne_zero_of_ne_zero_of_ne_one h1 h2,
  rcases (exists_mem_of_ne_zero h7) with ⟨x, hx⟩,
  have h8 : x ∈ to_multiset a,
  from mem_of_le h5 hx,
  have h9 : x ∈ to_multiset b,
  from mem_of_le h6 hx,
  exact ⟨x, (by simp *)⟩,
end

@[simp] lemma le_self {a : quot α} : a ≤ a:=
begin
  exact ⟨1, by simp⟩,
end

--Do we need a right variant here?
lemma mul_inf_eq_self {a b  : quot α}: a * b ⊓ a = a :=
begin
  apply le_antisymm inf_le_right,
  apply le_inf le_mul_right; simp,
end

/- We already have this one and problem in naming
lemma dvd_right_of_dvd_mul_inf_eq_one [unique_factorization_domain α] {a b c : quot α} (h1 : a ≤ b * c) (h2 : a ⊓ b = 1) : a ≤ c :=
begin
  apply lattice.le_of_inf_eq,
  rcases h1 with ⟨d, hd⟩,
  have h3 : (a * d) ⊓ a = (b * c) ⊓ a,
  {
    rw hd,
  },
  simp [mul_inf_eq_self, mul_inf_eq_inf_of_inf_eq_one h2] at h3,
  rw lattice.inf_comm at h2,
  rw [mul_inf_eq_inf_of_inf_eq_one h2, lattice.inf_comm] at h3,
  exact h3.symm,
end
-/


end associated

open associated


lemma is_unit_mul_div {a b : α} [comm_semiring α] (h : is_unit a) : a * b ∣ b :=
begin
  by_cases h1 : (b = 0),
  {
    simp * at *,
  },
  {
    rcases h with ⟨u, hu ⟩,
    have h1 : b = a * b * u.inv,
    {
      exact calc b = 1 * b : by simp
      ... = (u.val*u.inv) * b : by rw [u.val_inv]
      ... = (a * u.inv) * b : by rw [←units.val_coe u, ← hu]
      ... = _ : by simp [mul_assoc, mul_comm u.inv b],
    },
    exact ⟨u.inv, h1⟩
  }
end

lemma associated_of_mul_is_unit {a b c : α} [integral_domain α] (h1 : is_unit b) (h2 : a * b = c) : (a ~ᵤ c) :=
begin
  apply associated.symm,
  fapply exists.intro,
  exact to_unit h1,
  rw [← h2, mul_comm a b],
  simp,
end

lemma mul_is_unit_div {a b : α} [comm_semiring α] (h : is_unit a) : b * a ∣ b :=
begin
  rw mul_comm b a,
  exact is_unit_mul_div h,
end

lemma irreducible_of_mul_is_unit {a b c : α} [integral_domain α] (h1 : irreducible a) (h2 : is_unit b) (h3 : a * b = c) : irreducible c :=
begin
  apply irreducible_of_associated h1,
  exact associated_of_mul_is_unit h2 h3,
end

lemma dvd_of_mem_prod [comm_semiring α] {a x : α}{b : multiset α} (h1 : a = b.prod) (h2 : x ∈ b) : x ∣ a :=
begin
  rw ←cons_erase h2 at h1,
  simp at h1,
  split,
  exact h1,
end

lemma associated.dvd_of_associated {a b c : α} [integral_domain α] (h1 : a ~ᵤ b) (h2 : b ∣ c) : a ∣ c :=
begin
  rcases h1 with ⟨u, hu⟩,
  rcases h2 with ⟨d, hd⟩,
  fapply exists.intro,
  exact u.inv * d,
  rw mul_comm _ b at hu,
  rw [hu,←mul_assoc],
  apply eq.symm,
  exact calc b * ↑u * u.inv * d = b * (↑u * u.inv) * d : by simp [mul_assoc]
  ... = c : by simp [units.val_coe, u.val_inv, hd]
end


open unique_factorization_domain

lemma prime_of_irreducible {α : Type u}[unique_factorization_domain α] {p : α}
  (h1 : irreducible p) : prime p :=
begin
  constructor,
  exact and.elim_left h1,
  constructor,
  exact and.elim_left (and.elim_right h1),
  {
    intros b c h2,
    by_cases h3 : (b = 0),
    { simp *},
    {
      by_cases h4 : (c = 0),
      {simp *},
      {
        by_cases h5 : (is_unit b),
        {
          have h6 : b * c ∣ c,
          from is_unit_mul_div h5,          
          have h7 : p ∣ c,
          {exact dvd.trans h2 h6},
          simp *,
        },
        {
          by_cases h5b : (is_unit c),
          {
            have h6 : b * c ∣ b,
            from mul_is_unit_div h5b,           
            have h7 : p ∣ b,
            from dvd.trans h2 h6,
            simp *,
          },
          {
            rcases h2 with ⟨ d, h6 ⟩,
            by_cases h7 : (d = 0),
            {
              simp * at *,
              have : b * c ≠ 0,
              from mul_ne_zero h3 h4,
              contradiction,
            },
            {
              by_cases h8 : (is_unit d),
              {
                revert h6,
                generalize h9 : p * d = p',
                intros h10,
                have h11 : irreducible p',
                {
                  apply irreducible_of_associated h1,
                  exact associated_of_mul_is_unit h8 h9,
                },
                rw [irreducible_iff_irreducible', irreducible'] at h11,
                have h12 : is_unit b ∨ is_unit c,
                from h11.2.2 b c h10.symm,
                cases h12 ; contradiction,
              },
              { 
                rcases (fac h3 h5) with ⟨b', h9⟩,
                rcases (fac h4 h5b) with ⟨c', h10⟩,
                rcases (fac h7 h8) with ⟨d', h11⟩,
                rw [and.elim_left h9, and.elim_left h10, and.elim_left h11, multiset.prod_mul_prod_eq_add_prod, ← multiset.prod_cons] at h6,            
                have h12 : ∀ x ∈ b' + c', irreducible x,
                {
                  simp,
                  intros x h12,
                  cases h12,
                    exact h9.right _ h12,
                    exact h10.right _ h12,
                },
                have h13 : ∀ (x : α), x ∈ p :: d' → irreducible x,
                {
                  simp,
                  intros x h13,
                  cases h13,
                    rwa h13,
                    exact h11.right _ h13,
                },
                have h14 : rel_multiset associated (b' + c') (p :: d'),
                {apply unique_factorization_domain.unique ; assumption},
                have h15 : b' ≠ 0,
                {
                  by_contradiction h15,
                  simp at h15,
                  simp [h15] at h9,
                  have h16 : is_unit b,
                  {simp [h9]},
                  contradiction,
                },
                have h16 : ∃a' as', (b' + c') = (a' :: as') ∧ associated a' p ∧ rel_multiset associated as' d',
                from rel_multiset.cons_right h14,
                rcases h16 with ⟨e', es', h17, h18, h19⟩,
                have h20 : e' ∈ b' + c',
                {simp [h17]},
                simp at h20,
                cases h20,
                {
                  left,
                  apply associated.dvd_of_associated h18.symm,
                  apply dvd_of_mem_prod h9.1 h20,
                },
                {
                  right,
                  apply associated.dvd_of_associated h18.symm,
                  apply dvd_of_mem_prod h10.1 h20,                 
                }
              }
            }
          }
        }
      }
    }
  }
end

section ufd
variables [unique_factorization_domain α] {a b c : α}

instance unique_factorization_domain.has_gcd : has_gcd α :=
{
  gcd := assume a b : α, quot.out (inf (mk a) (mk b)),
  gcd_right := by simp [dvd_iff_mk_le_mk, inf_le_right],
  gcd_left  := by simp [dvd_iff_mk_le_mk, inf_le_left],
  gcd_min   := by simp [dvd_iff_mk_le_mk, le_inf] {contextual := tt}
}

@[simp] lemma mk_gcd_eq_inf : associated.mk (gcd a b) = (mk a) ⊓ (mk b) :=
associated.mk_quot_out

lemma mul_gcd : a * gcd b c ~ᵤ gcd (a * b) (a * c) :=
complete $ show mk a * mk (gcd b c) = _, by simp; exact associated.mul_inf

lemma rel_prime_def : (rel_prime a b) = (is_unit $ gcd a b) :=
rfl

--Is in isa lib
lemma gcd_mul_cancel (h1 : rel_prime c b) : (gcd (c * a) b ~ᵤ gcd a b) :=
begin
  rw [rel_prime,←mk_eq_one_iff_is_unit] at h1,
  apply complete,
  simp [mul_mk] at *,
  exact mul_inf_eq_inf_of_inf_eq_one h1,
end

lemma rel_prime_mul_of_rel_prime_of_rel_prime_of_rel_prime 
   (h1 : rel_prime a c) (h2 :  rel_prime b c ) : rel_prime (a * b) c :=
begin
  rw [rel_prime,←mk_eq_one_iff_is_unit] at *, --duplicate line with gcd_mul_cancel 
  simp [mul_mk] at *,
  rw mul_inf_eq_inf_of_inf_eq_one; assumption
end

/-

a ⊓ b = 1
b ⊓ c = 1
c ⊓ a = 1

(a * b) ⊓ c = 1

a ⊓ b = 1
(a * b) ⊓ c = (a ⊓ c) * (b ⊓ c)

(a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c)

[ (Ma + Mb) ∩ Mc ] = [ Ma ∩ Mc + Mb ∩ Mc ]

a ⊓ b = 1
gcd (a * b) c = (gcd a c) * (gcd b c)

-/
--open associated

--lemma asso

lemma is_unit_quot_iff_eq_one {a : quot α} : is_unit_quot a ↔ a = 1 :=
begin
  split,
  apply quot.induction_on a,  
  {
    intros a h,
    apply quot.sound,
    apply (asssociated_one_iff_is_unit).2,
    exact h,
  },
  {
    intros h,
    rw [h, one_def, ←mk_def],
    exact is_unit_one,  
  }
end

--open associated
lemma mul_eq_one_iff_eq_one_and_eq_one {a b : quot α} : a * b = 1 ↔ a = 1 ∧ b = 1 :=
begin
  apply @quotient.induction_on₂ _ _ (setoid α) (setoid α) _ a b,
  intros a b,
  rw [←mk_def, ←mk_def] {occs := occurrences.all},
  split,
  {
    intro h,
    rw [←mul_mk, one_def, ←mk_def] at h,
    have h1 : (a * b ~ᵤ 1),
    from complete h,
    have h2 : is_unit (a * b),
    from is_unit_of_associated is_unit_one h1.symm,
    have h3 : is_unit a,
    from is_unit_left_of_is_unit_mul h2,
    have h4 : is_unit b,
    from is_unit_right_of_is_unit_mul h2,
    repeat {rw ←is_unit_quot_iff_eq_one},
    split; assumption,
  },
  {
    intro h,
    simp * at *,
  }
end

/-
lemma mk_eq_zero_iff_eq_zero {a : α} : mk a = 0 ↔ a = 0:=
begin
  split,
  {
    intro h,
    rw [zero_def, ←mk_def] at h,
    have : (a ~ᵤ 0),
    from complete h,
    rw associated_zero_iff_eq_zero at this ; assumption,
  },
  {
    intro h,
    simp * at *,
  }
end
-/

lemma ne_zero_of_irred {a : quot α} (h : irred a) : a ≠ 0 :=
begin
  revert h,
  apply quot.induction_on a,
  intros a h,
  simp,
  have h1 : irreducible a,
  from h,
  have h2 : a ≠ 0,
  from h1.1,
  rw [←mk_def'],
  rw @mk_eq_zero_iff_eq_zero _ _ a,
  exact h2,
end

lemma to_multiset_eq_singleton_of_irred {a : quot α} (h : irred a) : to_multiset a = a::0 :=
begin
  apply uniqueness,
  exact to_multiset_irred _,
  {
    intros x h1,
    simp [mem_singleton, *] at *,
  },
  rw [to_multiset_prod_eq a (ne_zero_of_irred h)],
  simp,
end


lemma inf_eq_one_of_irred_of_irred_of_ne {a b : quot α} (ha : irred a) (hb : irred b) (h : a ≠ b) : a ⊓ b = 1 :=
begin
  by_cases h1 : a = 0,
    {
      have h2 : a ≠ 0,
      from ne_zero_of_irred ha,
      contradiction,
    },
    by_cases h2 : b = 0,
    {
        have h3 : b ≠ 0,
        from ne_zero_of_irred hb,
        contradiction,    
    },
    {
      simp [inf_def, *],
      rw [to_multiset_eq_singleton_of_irred ha, to_multiset_eq_singleton_of_irred hb], --Need to proof the to_multiset of a single irreducible element.
      have h3 : (a :: 0) ∩ (b :: 0) = 0,
      {
        apply eq_zero_of_forall_not_mem,
        intros x h3,
        simp at h3,
        rw [←h3.1, ←h3.2] at h,
        contradiction,
      },
      simp *,
    }
end

lemma rel_prime_iff_mk_inf_mk_eq_one {a b : α} : rel_prime a b ↔ (mk a) ⊓ (mk b) = 1 :=
begin
  split,
  {
    intro h,
    simp [rel_prime, gcd, has_gcd.gcd] at h,
    have h1 : is_unit_quot (inf (mk a) (mk b)),
    {
      rw ←quot.out_eq (inf (mk a) (mk b)),
      exact h,
    },
    rw is_unit_quot_iff_eq_one at h1,
    exact h1,
  },
  {
    intro h,
    simp [rel_prime, gcd, has_gcd.gcd],
    have h1 : inf (mk a) (mk b) = 1, --anoying, that this step needs to be made.
    from h,
    rw h1,
    apply is_unit_of_associated is_unit_one,
    apply complete,
    simp [one_def]
  }
end


lemma mul_dvd_of_dvd_of_dvd_of_rel_prime {α : Type u}{a b c: α} [unique_factorization_domain α] (h1 : rel_prime a b)(h2 : a ∣ c)(h3 : b ∣ c) : (a * b) ∣ c:=
begin
  rw dvd_iff_mk_le_mk at *,
  rw [mul_mk],
  rw rel_prime_iff_mk_inf_mk_eq_one at h1, 
  exact mul_le_of_le_of_le_of_rel_prime h1 h2 h3,
end

lemma rel_prime_comm {γ : Type u} [unique_factorization_domain γ] {a b : γ} : rel_prime a b → rel_prime b a :=
begin
  intro h1,
  rw rel_prime at *,
  apply is_unit_of_associated h1 gcd_comm
end

lemma one_def' : mk (1 : α) = 1 := rfl

def facs_to_pow  [monoid α] (p : α →₀ ℕ ) : finset α:= p.support.image (λ a, a^(p a))

--Was not consistant everywhere --I think the left should refer to the variable
@[simp] lemma gcd_one_left {a : α} : (gcd 1 a ~ᵤ 1) :=
begin
  apply complete,
  simp [one_def'],
  exact lattice.bot_inf_eq,
end

@[simp] lemma gcd_one_right {a : α} : (gcd a 1 ~ᵤ 1) :=
begin
  apply complete,
  simp [one_def'],
  exact lattice.inf_bot_eq,
end

@[simp] lemma is_unit_gcd_one_left {a : α } : is_unit (gcd 1 a) :=
begin
  apply is_unit_of_associated is_unit_one gcd_one_left.symm,
end

@[simp] lemma is_unit_gcd_one_right {a : α } : is_unit (gcd a 1) :=
begin
  apply is_unit_of_associated is_unit_one gcd_one_right.symm,
end

lemma rel_prime_mul_iff_rel_prime_and_rel_prime {a b c : α} : rel_prime a (b * c) ↔ rel_prime a b ∧ rel_prime a c :=
begin
  repeat {rw [rel_prime_iff_mk_inf_mk_eq_one]},
  rw mul_mk,
  exact inf_mul_eq_one_iff_inf_eq_one_and_inf_eq_one,
end


lemma rel_prime_pow {x y : α } {n : ℕ} (h : n ≠ 0) : rel_prime x (y ^ n) ↔ rel_prime x y :=
begin
  induction n with n ih,
  {
    contradiction,
  },
  { 
    by_cases hn : n = 0,
      simp [hn], --clear?
    simp only [pow_succ] at *,   
    split,
    {
      intro h,
      rw rel_prime_mul_iff_rel_prime_and_rel_prime at h,
      exact h.1,
    },
    {
      intro h1,
      rw rel_prime_mul_iff_rel_prime_and_rel_prime,
      split,
        exact h1,
      {
        exact (ih hn).2 h1,
      }
    }
  }
end

@[simp] lemma rel_prime_one_left {x : α} : rel_prime x 1 :=
begin
  simp [rel_prime],
end

@[simp] lemma rel_prime_one_right{x : α} : rel_prime 1 x :=
begin
  simp [rel_prime],
end

lemma rel_prime_pow_pow_of_rel_prime {x y : α}{n m : ℕ}(h  : rel_prime x y) : rel_prime (x ^ n) (y ^ m) :=
begin
  by_cases h1 : n = 0,
    {simp [h1]},
    by_cases h2 : m = 0,
      {simp [h2]},
      {
        rw [rel_prime_pow h2],
        apply rel_prime_comm,
        rw [rel_prime_pow h1],
        exact rel_prime_comm h,
      }
end

--This could simplify things
lemma associated_iff_mk_eq_mk {x y : α} : x ~ᵤ y ↔ mk x = mk y :=
iff.intro
  quot.sound
  complete

lemma rel_prime_of_irreducible_of_irreducible_of_not_associated {x y : α} (hx : irreducible x) (hy : irreducible y) (h : ¬ (x ~ᵤ y)) : rel_prime x y :=
begin
  rw associated_iff_mk_eq_mk at h,
  rw [rel_prime_iff_mk_inf_mk_eq_one],
  apply inf_eq_one_of_irred_of_irred_of_ne _ _ h ; assumption,
end

lemma pow_mul_pow_dvd [unique_factorization_domain α] {x y z : α} {n m : ℕ}
  (hx : irreducible x) (hy : irreducible y) (hxz: x ^ n ∣ z) (hyz : y ^ m ∣ z) (h : ¬ (x ~ᵤ y)) :
  (x ^ n * y ^ m) ∣ z :=
begin
  apply @mul_dvd_of_dvd_of_dvd_of_rel_prime _ (x ^ n) (y ^ m) z,
  apply rel_prime_pow_pow_of_rel_prime,
  apply rel_prime_of_irreducible_of_irreducible_of_not_associated,
  repeat {assumption},
end

lemma prod_eq_zero_iff_zero_mem {s : multiset (quot α)} : prod s = 0 ↔ (0 : quot α) ∈ s :=
begin
  split,
  {
    apply multiset.induction_on s,
    {
      simp * at *,
      intro h1,
      exact zero_ne_one h1.symm,      
    },
    {
      intros a s h1 h2,
      simp * at *,
      by_cases ha : a = 0,
      {
        simp * at *,
      },
      {
        have h3 : prod s = 0,
        {
          by_contradiction h4,
          have : a * prod s ≠ 0,
          from mul_ne_zero ha h4,
          contradiction,
        },
        simp [h1 h3],
      }
    }
  },
  {
    intro h,
    rcases (exists_cons_of_mem h) with ⟨t, ht⟩,
    subst ht,
    simp * at *,
  }
end

lemma to_multiset_prod_of_zero_not_mem {s : multiset (quot α)} (h0 : (0 : quot α) ∉ s) : to_multiset (s.prod) = (multiset.map to_multiset s).sum :=
begin --We need some non_zero constraint here
  by_cases hs : s = 0,
    {simp * at *},
    {
      
      by_cases hs1 : s.prod = 1,
      {
        simp * at *,
        apply eq.symm,
        rw sum_map_eq_zero_iff_forall_eq_zero,
        intros x h1,
        rw to_multiset_eq_zero_iff_eq_zero_or_eq_one,
        rcases (exists_cons_of_mem h1) with ⟨t, ht⟩,
        subst ht,
        simp * at *,
        have : is_unit_quot x,
        from is_unit_quot_of_mul_eq_one_left hs1,
        rw is_unit_quot_iff_eq_one at this,
        simp * at *,        
      },
      {
        by_cases hs2 : prod s = 0,
        {
          rw prod_eq_zero_iff_zero_mem at hs2,
          contradiction,
        },
        {
          revert hs1 hs2 hs h0,
          apply multiset.induction_on s,
          {
            simp * at *,
          },
          {
            intros a s h1 h2 h3 h4 h5,
            simp * at *,
            rw not_or_distrib at h5,
            have h6 : ¬prod s = 0,
            {
              by_contradiction h6,
              simp * at *,
            },
            rw to_multiset_mul (ne.symm h5.1) h6,
            simp,
            by_cases hs1 : prod s = 1,
            {

              simp * at *, --Complete duplication!
              apply eq.symm,
              rw sum_map_eq_zero_iff_forall_eq_zero,
              intros x h1,
              rw to_multiset_eq_zero_iff_eq_zero_or_eq_one,
              rcases (exists_cons_of_mem h1) with ⟨t, ht⟩,
              subst ht,
              simp * at *,
              have : is_unit_quot x,
              from is_unit_quot_of_mul_eq_one_left hs1,
              rw is_unit_quot_iff_eq_one at this,
              simp * at *, 

            },
            {
              apply h1 hs1 h6,
              {
                by_contradiction h7,
                simp * at *,
              },
              exact h5.2
            }
          }
        }
      }
    }


end

--Maybe we need a general lemma for to multiset prod?
lemma to_multiset_prod_eq_of_irred {s : multiset (quot α)} (h : ∀x, x ∈ s → irred x) : (to_multiset (s.prod)) = s :=
begin
  rw to_multiset_prod_of_zero_not_mem,
  rw [←@sum_map_singleton _ s] {occs := occurrences.pos [2]},
  apply congr_arg,
  apply map_congr,
  {
    intros x h1,
    exact to_multiset_eq_singleton_of_irred (h x h1),
  },
  {
    by_contradiction h1,
    have : irred 0,
    from h _ h1,
    have : (0 : quot α) ≠ 0,
    from ne_zero_of_irred this,
    contradiction,
  }
end

lemma le_of_mem_to_multiset {y : quot α} : ∀x ∈ to_multiset y, x ≤ y :=
begin
  intros x h1,
  by_cases h2 : y = 0,
  {
    simp * at *,
  },
  {
    rw ←to_multiset_prod_eq y h2,
    rcases (exists_cons_of_mem h1) with ⟨t, ht⟩,
    rw ht,
    simp * at *,
    exact le_mul_right,
  }
end

lemma inf_prod_eq_one_iff_forall_inf_eq_one {y: quot α} {s : multiset (quot α)} : y ⊓ s.prod = 1 ↔ ∀x ∈ s, y ⊓ x = 1 :=
begin
  split,
  {
    apply multiset.induction_on s,
    {
      intros h x h1,
      simp * at *,
    },
    {
      intros a s h1 h2 x h3,
      simp * at *,
      rw inf_mul_eq_one_iff_inf_eq_one_and_inf_eq_one at h2,
      cases h3,
      {
        subst h3,
        exact h2.1,
      },
      {
        exact h1 h2.2 x h3,
      }
    }
  },
  {
    apply multiset.induction_on s,
    {
      intros x,
      simp * at *,
      exact lattice.inf_bot_eq,
    },
    {
      intros a t h1 h2,
      simp * at *,
      rw inf_mul_eq_one_iff_inf_eq_one_and_inf_eq_one,
      split,
      {
        apply h2 a,
        simp,
      },
      {
        apply h1,
        intros x h,
        apply h2,
        simp *,
      }
    }
  }
end




lemma forall_map_mk_irred_of_forall_irreducible {s : multiset α}(h : ∀x ∈ s, irreducible x) : ∀ x ∈ map mk s, irred x :=
begin
  intros x,
  apply quot.induction_on x,
  intros a h1,
  rw mem_map at h1,
  rcases h1 with ⟨b, hb⟩,
  rw ← hb.2,
  exact h b hb.1,
end

--Why do we need irreucible here?? (h : ∀x ∈ s, irreducible x)
lemma rel_prime_prod_iff_forall_rel_prime  {y: α} {s : multiset α}: rel_prime y s.prod ↔ ∀x ∈ s, rel_prime y x :=
begin
  rw rel_prime_iff_mk_inf_mk_eq_one,
  rw [mk_def, mk_def],
  rw [←prod_mk],
  --have h4 : ∀ x, x ∈ map mk s → irred x,
  --from forall_map_mk_irred_of_forall_irreducible h,
  rw inf_prod_eq_one_iff_forall_inf_eq_one, -- h4,
  split,
  {
    intros h1 z h3,
    rw rel_prime_iff_mk_inf_mk_eq_one,
    apply h1 (mk z),
    rw mem_map,
    exact ⟨z, h3, rfl⟩,
  },
  {
    intros h1 x,
    apply quot.induction_on x,
    intros a h2,
    rw mem_map at h2,
    rcases h2 with ⟨b, hb⟩,
    rw ←hb.2,
    have h2: rel_prime y b,
    from h1 b hb.1,
    rw rel_prime_iff_mk_inf_mk_eq_one at h2,
    exact h2,
  }
end



lemma succ_eq_succ_iff_eq {n m : ℕ} : nat.succ n = nat.succ m ↔ n = m :=
begin
  split,
    exact nat.succ_inj,
    intro h,
    simp *,
end

lemma eq_zero_or_exists_eq_succ_succ_of_ne_one {n : ℕ} (h : n ≠ 1) : n = 0 ∨ ∃ m, n = nat.succ (nat.succ m) := 
begin
  by_cases h2 : n = 0,
    {simp *},
    {
      rcases (nat.exists_eq_succ_of_ne_zero h2) with ⟨m, hm⟩,
      subst hm,
      simp * at *,
      rw succ_eq_succ_iff_eq at h,     
      rcases (nat.exists_eq_succ_of_ne_zero h) with ⟨s, hs⟩,
      subst hs,
      exact ⟨s, rfl⟩,
    }     
end

lemma not_irreducible_one : ¬ irreducible (1 : α) :=
begin
  by_contradiction h,
  have : ¬is_unit (1 : α),
  from (h.2).1,
  have : is_unit (1 : α),
  from is_unit_one,
  contradiction,
end

lemma is_unit_of_mul_is_unit_left {a b : α} (h : is_unit (a * b)) : is_unit a :=
begin
  rcases h with ⟨c, hc⟩,
  have h1: a * b * c.inv = 1,
  {
    rw [hc, units.val_coe c, c.val_inv],      
  },
  rw mul_assoc at h1,
  exact is_unit_of_mul_eq_one_left h1,     
end

lemma is_unit_of_mul_is_unit_right {a b : α} (h : is_unit (a * b)) : is_unit b :=
begin
  rw mul_comm at h,
  exact is_unit_of_mul_is_unit_left h,  
end


lemma is_unit_mul_iff_is_unit_and_is_unit {a b : α} : is_unit (a * b) ↔ is_unit a ∧ is_unit b :=
begin
  split,
  {
    intros h,
    exact ⟨is_unit_of_mul_is_unit_left h, is_unit_of_mul_is_unit_right h⟩,  
  },
  {
    intros h,
    exact is_unit_mul_of_is_unit_of_is_unit h.1 h.2,
  }
end

lemma irreducible_pow {a : α} {n : ℕ} (h : irreducible a) : irreducible (a^n) ↔ n = 1 :=
begin
  split,
  {
    intros h1,
    by_contradiction h2,
    have h3 : n = 0 ∨ ∃ m, n = nat.succ (nat.succ m),
    from eq_zero_or_exists_eq_succ_succ_of_ne_one h2,
    cases h3,
    {
      simp * at *,
      have : ¬ irreducible (1 : α),
      from  not_irreducible_one,
      contradiction,
    },
    {
      rcases h3 with ⟨m, hm⟩,
      subst hm,
      rw pow_succ at *,
      rw irreducible_iff_irreducible' at h1,
      unfold irreducible' at h1,
      have h4: is_unit a ∨ is_unit (a ^ nat.succ m),
      from h1.2.2 _ _ rfl,
      cases h4,
      {
        have : ¬is_unit a,
        from h.2.1,
        contradiction,
      },
      {
        rw pow_succ at h4,
        rw is_unit_mul_iff_is_unit_and_is_unit at h4,
        have : ¬is_unit a,
        from h.2.1,
        exact this h4.1,
      }
    }

  },
  {
    intro h,
    simp * at *,
  }
end 

--Problem? could be that I need it for intergral domain?? [integral_domain α] 
lemma facs_to_pow_prod_dvd {f : α →₀ ℕ} {z : α}
  (h1 : ∀x∈f.support, irreducible x ∧ (x^(f x)) ∣ z ∧ ∀y∈f.support, x ≠ y → ¬ (x ~ᵤ y)) :
  f.prod (λx y, x^y) ∣ z :=
begin




  revert h1,
  rw finsupp.prod,
  apply @finset.induction_on _ _ (λ b, (∀ (x : α),
     x ∈ b →
     irreducible x ∧ x ^ f x ∣ z ∧ ∀ (y : α), y ∈ b → x ≠ y → ¬(x~ᵤ y)) →
  finset.prod (b) (λ (a : α), a ^ f a) ∣ z) (finsupp.support f),
  {
    simp * at *,
  },
  {
    intros a s h2 h3 h4,
    simp [finset.prod_insert h2],
    apply mul_dvd_of_dvd_of_dvd_of_rel_prime,
    {
      rw finset_prod_eq_map_prod,
      rw rel_prime_prod_iff_forall_rel_prime,
      {
        intros y h5,
        rw mem_map at h5,
        rcases h5 with ⟨b, hb⟩,
        rw ←hb.2,
        apply rel_prime_pow_pow_of_rel_prime,
        have h5 : a ∈ insert a s,
        {simp},
        have h6 : b ∈ s,
        from hb.1,        
        have h7 : b ∈ insert a s,
        {simp *},
        have h8 : (¬(a ~ᵤ b)),
        {
          apply (h4 a h5).2.2 b h7,
          by_contradiction h9,
          simp at h9,
          subst h9,
          exact h2 h6,
        },
        exact rel_prime_of_irreducible_of_irreducible_of_not_associated (h4 a h5).1 (h4 b h7).1 h8,
      },


      --admit,  --separate induction prove?
    },
    {
      have h5 : a ∈ insert a s,
      {
        rw finset.mem_insert,
        simp,
      },
      exact (h4 a h5).2.1,
    },
    {
      apply h3,
      intros x h5,
      have h6 : x ∈ insert a s,
      {
        rw finset.mem_insert,
        simp *,
      },
      have h5 : irreducible x ∧ x ^ f x ∣ z ∧ ∀ (y : α), y ∈ insert a s → x ≠ y → ¬(x~ᵤ y),
      from h4 x h6,
      {
        split,
        exact h5.1,
        split,
        exact h5.2.1,
        intros q h6,
        have : q ∈ insert a s, --duplicate
        {
          rw finset.mem_insert,
          simp *,
        },
        apply h5.2.2 q this,
      }
    }

    
  }

end

lemma dvd_of_dvd_mul_of_rel_prime {a b c : α} (h1 : a ∣ b * c) (h2 : rel_prime a b) : a ∣ c :=
begin
  rw rel_prime_iff_mk_inf_mk_eq_one at h2,
  rw dvd_iff_mk_le_mk at *,
  rw [mul_mk] at h1,
  apply le_of_le_mul_of_le_of_inf_eq_one h2,
  have h3 : mk c ≤ mk b * mk c,
  from le_mul_left,
  cc,
end

end ufd
