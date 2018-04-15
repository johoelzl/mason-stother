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

def associated [semiring α] (x y : α) : Prop:=
∃u : units α, x = u * y


--can the priority be set better? Because now we often have to provide parentheses
local notation a `~ᵤ` b : 50 := associated a b

namespace associated

section semiring
variable [semiring α]

def is_unit (a : α) : Prop := ∃b : units α, a = b

/- is used once in UFD, but I don't understand what it does
-/
lemma is_unit_unit  (u : units α) : @is_unit α _ u :=
⟨u, rfl⟩


@[simp] lemma is_unit_one : is_unit (1 : α ) := ⟨1, rfl⟩

--Should I do all these lemmas using the zero_ne_one class?
@[simp] lemma not_is_unit_zero (h : (0 : α) ≠ 1) : ¬ is_unit (0 : α) := --Do we need semiring?
begin
  intro h,
  rcases h with ⟨u, hu⟩,
  have h2: u.val*u.inv = 1,
    from u.val_inv,
  simp [units.val_coe] at *,
  rw [←hu, _root_.zero_mul] at h2,
  contradiction,
end

lemma ne_zero_of_is_unit {a : α} (h : (0 : α) ≠ 1) : is_unit a → a ≠ 0 :=
begin
  intros h1 h2,
  subst h2,
  exact not_is_unit_zero h h1,
end

lemma is_unit_mul_of_is_unit_of_is_unit {a b : α} (h1 : is_unit a) (h2 : is_unit b) : is_unit (a * b) :=
let ⟨aᵤ, ha⟩ := h1 in
let ⟨bᵤ, hb⟩ := h2 in ⟨aᵤ*bᵤ, by simp [units.mul_coe, *]⟩


lemma zero_associated_zero   : (0 : α) ~ᵤ 0 := ⟨1, by simp⟩


lemma unit_associated_one {u : units α}: (u : α) ~ᵤ 1 := ⟨u, by simp⟩




end semiring



section comm_semiring
variable [comm_semiring α]

--removed protected
@[refl] lemma refl : ∀ (x : α), x ~ᵤ x :=
assume x, let ⟨u, hu⟩ := is_unit_one in ⟨u, by {rw [←hu], rw [one_mul]}⟩

@[symm] lemma symm {x y : α} (h : x ~ᵤ y) : y ~ᵤ x :=
let ⟨u, hu⟩ := h in ⟨u⁻¹, by rw [hu, ←mul_assoc, units.inv_mul, one_mul]⟩

--Why protected??
@[trans] lemma trans {x y z: α} (h1 : x ~ᵤ y)(h2 : y ~ᵤ z): x ~ᵤ z :=
let ⟨u1, hu1⟩ := h1 in
let ⟨u2, hu2⟩ := h2 in
exists.intro (u1 * u2) $ by rw [hu1, hu2, ←mul_assoc, units.mul_coe]



lemma associated.eqv : equivalence (@associated α _) :=
mk_equivalence (@associated α _) (@associated.refl α _) (@associated.symm α _) (@associated.trans α _)

--correct simp?
@[simp] lemma associated_zero_iff_eq_zero {a : α} : (a ~ᵤ (0 : α)) ↔ a = 0 :=
iff.intro
  (assume h1, let ⟨u, h2⟩ := h1 in by simp [h2, *])
  (assume h1, by rw h1)


lemma associated_of_mul_eq_one {a b : α} (h1 : a * b = 1) : a ~ᵤ b :=
begin
  have h2 : b * a = 1,
  { rwa mul_comm a b at h1},
  have h3 : a * a * (b * b) = 1,
  { rwa [←mul_assoc, @mul_assoc _ _ a a _, h1, mul_one]},
  have h4 : b * b * (a * a) = 1,
  { rwa [mul_comm _ _] at h3},
  exact ⟨units.mk (a * a) (b * b) h3 h4, by {rw [units.val_coe], simp [mul_assoc, h1]}⟩,
end

def unit_of_mul_eq_one  {a b : α} (h1 : a * b = 1) : units α :=
units.mk a b h1 (by {rw mul_comm _ _ at h1, exact h1})

end comm_semiring

def setoid (β : Type u) [comm_semiring β] : setoid β :=
{ r := associated, iseqv := associated.eqv }
local attribute [instance] setoid

section comm_semiring
variable [comm_semiring α]

#check setoid α

def quot (β : Type u) [comm_semiring β] : Type u := quotient (setoid β)

@[reducible] def mk (a : α) : quot α := ⟦ a ⟧ --important: Why did we define this? As we already have: ⟦ a ⟧?

lemma mk_def {a : α} : mk a = ⟦a⟧ := rfl
lemma mk_def' {a : α} : mk a = quot.mk setoid.r a := rfl


--naming?
lemma complete {a b : α} : mk a = mk b → (a ~ᵤ b) :=
begin
 intro h1,
 simp * at *,
 exact h1,
end

--This could simplify things
lemma associated_iff_mk_eq_mk {x y : α} : x ~ᵤ y ↔ mk x = mk y :=
iff.intro
  quot.sound
  complete

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

@[simp] lemma mk_zero_eq_zero : mk (0 : α) = 0 := rfl

--Would be nice to introduce a less strict order earlier on
instance : preorder (quot α) :=
{ le := λa b, ∃c, a * c = b,
  le_refl := assume a, ⟨1, by simp⟩,
  le_trans := assume a b c ⟨f₁, h₁⟩ ⟨f₂, h₂⟩,
    ⟨f₁ * f₂, h₂ ▸ h₁ ▸ (mul_assoc _ _ _).symm⟩}


lemma is_unit_left_iff_exists_mul_eq_one [comm_semiring α] {a: α} : (is_unit a) ↔ ∃ b, a * b = 1 :=
begin
  apply iff.intro,
  {
    intro h1,
    rcases h1 with ⟨aᵤ, ha⟩,
    subst ha,
    exact ⟨aᵤ.inv, by {rw [←units.inv_coe, units.mul_inv]}⟩,
  },
  {
    intro h1,
    rcases h1 with ⟨b, h2⟩,
    have h3 : b * a = 1,
    { rw [mul_comm a b]at h2, exact h2},
    exact ⟨⟨a, b, h2, h3⟩, rfl⟩,
  }
end


lemma is_unit_right_iff_exists_mul_eq_one {b: α} : (is_unit b) ↔ ∃ a, a * b = 1 :=
begin
  have h1 : (is_unit b) ↔ ∃ a, b * a = 1,
  from @is_unit_left_iff_exists_mul_eq_one _ _ _ b,
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

lemma is_unit_of_associated {p b : α}(h1 : is_unit p)(h2 : p ~ᵤ b) : is_unit b :=
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


--Should also make a right.
lemma is_unit_left_of_is_unit_mul {a b : α} : is_unit (a * b) → is_unit a :=
begin
  intro h1,
  rcases h1 with ⟨u, hu⟩,

  have h2 : a * (b* (↑u⁻¹ : α) ) = 1,
  {
    exact calc a * (b* (↑u⁻¹ : α) ) = (a * b) * (↑u⁻¹ : α) : by rw ← mul_assoc
    ... = u.val * (↑u⁻¹ : α) : by simp [units.val_coe, *]
    ... = u.val * u.inv : by rw units.inv_coe
    ... = 1 : u.val_inv,
  },
  rw @is_unit_left_iff_exists_mul_eq_one _ _ _ a,
  exact ⟨(b * ↑u⁻¹), h2 ⟩,
end

lemma is_unit_right_of_is_unit_mul {a b : α} : is_unit (a * b) → is_unit b :=
begin
  rw mul_comm a b,
  exact is_unit_left_of_is_unit_mul,
end

lemma is_unit_of_mul_eq_one_left {a b : α} (h : a * b = 1): is_unit a :=
begin
  rw is_unit_left_iff_exists_mul_eq_one,
  exact ⟨b , h⟩
end

lemma is_unit_of_mul_eq_one_right {a b : α} (h : a * b = 1): is_unit b :=
begin
  rw is_unit_right_iff_exists_mul_eq_one,
  exact ⟨a , h⟩
end

/-
lemma associated_of_mul_eq_one {a b : α} (h1 : a * b = 1) : a ~ᵤ b :=
begin
  have h2 : b * a = 1,
  { rwa mul_comm a b at h1},
  have h3 : a * a * (b * b) = 1,
  { rwa [←mul_assoc, @mul_assoc _ _ a a _, h1, mul_one]},
  have h4 : b * b * (a * a) = 1,
  { rwa [mul_comm _ _] at h3},
  exact ⟨units.mk (a * a) (b * b) h3 h4, by {rw [units.val_coe], simp [mul_assoc, h1]}⟩,
end-/


lemma dvd_dvd_of_associated {a b : α}
   : (a ~ᵤ b) → ( a ∣ b) ∧ ( b ∣ a):=
assume h1, let ⟨u, h2⟩ := h1 in
and.intro
  (have h3 : u.inv * a = b, from 
    (calc u.inv * a = u.inv * (↑u * b) : by rw h2
        ... = (u.inv * u.val) * b : by {simp [units.val_coe, mul_assoc]}
        ... = b : by simp [u.inv_val]),
   dvd.intro_left _ h3)
  (dvd.intro_left _ h2.symm)


lemma asssociated_one_iff_is_unit {a : α} : (a ~ᵤ 1) ↔ is_unit a :=
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
    rcases h1 with ⟨aᵤ, ha⟩,
    exact ⟨aᵤ, by simp *⟩,
  }
end

--naming
lemma prod_not_is_unit_eq_one_iff_eq_zero {p : multiset α}: (∀ a, a ∈ p → (¬ (is_unit a))) → (p.prod = 1 ↔ p = 0) :=
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



lemma mul_associated_mul_of_associated_of_associated {α : Type u} [integral_domain α] {a b c d : α} (h1 : a ~ᵤ c) (h2: b ~ᵤ d) : (a * b) ~ᵤ (c * d) :=
begin
  rcases h1 with ⟨u1, hu1⟩,
  rcases h2 with ⟨u2, hu2⟩,
  fapply exists.intro,
  exact u1 * u2,
  rw [hu1, hu2, mul_assoc],
  exact calc ↑u1 * (c * (↑u2 * d)) = ↑u1 * ((c * ↑u2) * d): by simp [mul_assoc]
    ... = ↑u1 * ((↑u2 * c) * d): by simp [mul_comm]
    ... = ↑u1 * ↑u2 * c * d: by simp [mul_assoc]
    ... = _ : by rw [units.mul_coe, mul_assoc]
end




end comm_semiring



section integral_domain
variable [integral_domain α]

lemma associated_of_dvd_dvd {a b : α}
  (h1 : a ∣ b) (h2 : b ∣ a) : a ~ᵤ b :=
begin
  rcases h2 with ⟨c, h3⟩,
  rcases h1 with ⟨d, h4⟩,
  by_cases h6 : (a = 0),
  {
    have h7 : (b = 0),
    {
      simp [h6] at h4,
      assumption,
    },
    simp * at *,
  },
  {
    have h3b : a = a * (d * c),
    { rwa [h4, mul_assoc] at h3},
    have h5 : a * 1 = a * (d * c),
    { simpa},
    have h7 : 1 = (d * c),
      from eq_of_mul_eq_mul_left h6 h5,
    rw mul_comm _ _ at h7,
    exact ⟨unit_of_mul_eq_one (h7.symm), by rw [h4, unit_of_mul_eq_one, units.val_coe, ←mul_assoc, mul_comm c, mul_assoc, ←h7, mul_one]⟩,
  }
end

lemma dvd_dvd_iff_associated {a b : α}
   : (a ~ᵤ b) ↔ ( a ∣ b) ∧ ( b ∣ a):=
⟨dvd_dvd_of_associated, assume h1, associated_of_dvd_dvd h1.1 h1.2⟩

instance : partial_order (quot α) :=
{ 
  le_antisymm := assume a' b',
    quotient.induction_on₂ a' b' $ assume a b ⟨f₁', h₁⟩ ⟨f₂', h₂⟩,
    (quotient.induction_on₂ f₁' f₂' $ assume f₁ f₂ h₁ h₂,
      let ⟨c₁, h₁⟩ := quotient.exact h₁.symm, ⟨c₂, h₂⟩ := quotient.exact h₂.symm in
      quotient.sound $ associated_of_dvd_dvd
        (h₁.symm ▸ dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
        (h₂.symm ▸ dvd_mul_of_dvd_right (dvd_mul_right _ _) _)) h₁ h₂ 
  .. associated.preorder
}


end integral_domain




-- Can we Prove the existence of a gcd here? Problem is has_dvd, why is it not defined here??
--If we can show the existence of a gcd here, we can reuse some lemmas









end associated