import data.finsupp
import algebra.ring
import .to_finset
import .to_multiset
import to_semiring



noncomputable theory

local infix ^ := monoid.pow

open classical multiset
local attribute [instance] prop_decidable
--can the priority be set better? Because now we often have to provide parentheses
local notation a `~ᵤ` b : 50 := associated a b

universe u
variable {α : Type u}
variable [comm_semiring α]


def unit_of_mul_eq_one  {a b : α} (h1 : a * b = 1) : units α :=
units.mk a b h1 (by {rw mul_comm _ _ at h1, exact h1})


--removed protected
@[refl] lemma associated.refl : ∀ (x : α), x ~ᵤ x :=
assume x, let ⟨u, hu⟩ := is_unit_one in ⟨u, by {rw [←hu], rw [one_mul]}⟩

@[symm] lemma associated.symm {x y : α} (h : x ~ᵤ y) : y ~ᵤ x :=
let ⟨u, hu⟩ := h in ⟨u⁻¹, by rw [hu, ←mul_assoc, units.inv_mul, one_mul]⟩

--Why protected??
@[trans] lemma associated.trans {x y z: α} (h1 : x ~ᵤ y)(h2 : y ~ᵤ z): x ~ᵤ z :=
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

lemma is_unit_mul_div {a b : α} (h : is_unit a) : a * b ∣ b :=
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


lemma mul_is_unit_div {a b : α} (h : is_unit a) : b * a ∣ b :=
begin
  rw mul_comm b a,
  exact is_unit_mul_div h,
end


lemma dvd_of_mem_prod {a x : α} {b : multiset α} (h1 : a = b.prod) (h2 : x ∈ b) : x ∣ a :=
begin
  rw ←cons_erase h2 at h1,
  simp at h1,
  split,
  exact h1,
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
      ... = (↑u⁻¹ * ↑u) * 1 : by simp 
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



lemma mul_associated_mul_of_associated_of_associated {a b c d : α} (h1 : a ~ᵤ c) (h2: b ~ᵤ d) : (a * b) ~ᵤ (c * d) :=
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



lemma associated_of_mul_is_unit {a b c : α} (h1 : is_unit b) (h2 : a * b = c) : (a ~ᵤ c) :=
begin
  apply associated.symm,
  rcases h1 with ⟨u, hu⟩,
  apply exists.intro u,
  subst hu,
  simp [mul_comm, *],
end


lemma associated.dvd_of_associated {a b c : α} (h1 : a ~ᵤ b) (h2 : b ∣ c) : a ∣ c :=
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


--Naming?
lemma not_is_unit_of_not_is_unit_dvd {a b : α} (h1 : ¬is_unit a) (h2 : a ∣ b) : ¬is_unit b :=
begin
  rcases h2 with ⟨c, hc⟩,
  subst hc,
  by_contradiction h2,
  have : is_unit a,
    from is_unit_left_of_is_unit_mul h2,
  contradiction,
end


---Gcds

--gcds
class has_gcd (α : Type u) [comm_semiring α] := --can we define it for comm_monoid?
(gcd : α → α → α)
(gcd_right : ∀ a b, gcd a b ∣ b)
(gcd_left  : ∀ a b, gcd a b ∣ a)
(gcd_min   : ∀ a b g, g ∣ a → g ∣ b → g ∣ gcd a b)



section gcd_sr
variables [has_gcd α] {a b c : α}

def gcd : α → α → α := has_gcd.gcd
def gcd_min := has_gcd.gcd_min a b c  --Correct???
def gcd_left := has_gcd.gcd_left a b --use {a b : α}?
def gcd_right := has_gcd.gcd_right a b


def coprime (a b : α) := is_unit (gcd a b)

lemma coprime_def : (coprime a b) = (is_unit $ gcd a b) :=
rfl

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