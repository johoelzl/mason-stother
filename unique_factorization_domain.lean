import data.finsupp
import algebra.ring
import .to_finset
import .to_multiset
import associated_quotient

noncomputable theory

local infix ^ := monoid.pow

open classical
local attribute [instance] prop_decidable

universe u
variable {α : Type u}

--Would it have been smart to define units as a type that lives in Prop??
--Or would this have been pointless because a Prop cannot contain data? It could have been made with exisential quatifier, but than we are in the same situation that we are in now.

/-
lemma is_unit_unit {t : Type u}[h : semiring t] (u : units t) : @is_unit t h u :=
⟨u, rfl⟩
-/
open associated
open multiset

--can the priority be set better? Because now we often have to provide parentheses
local notation a `~ᵤ` b : 50 := associated a b

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
    rcases h2 with ⟨u, hu⟩,
    refine ⟨u, 0, by simp * at *⟩,
  },
  {
    rcases (unique_factorization_domain.fac h1 h2) with ⟨f, hf⟩,
    rcases is_unit_one with ⟨u, hu⟩,
    refine ⟨u, f, _⟩,
    rwa [←hu, one_mul],
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







namespace associated
local attribute [instance] setoid
-- Can we Prove the existence of a gcd here? Problem is has_dvd, why is it not defined here??
--If we can show the existence of a gcd here, we can reuse some lemmas

variables {α} [unique_factorization_domain α]


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
         --rw is_unit,
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




def inf (a b : quot α) :=
if a = 0 then b else if b = 0 then a else (to_multiset a ∩ to_multiset b).prod



def sup (a b : quot α) :=
if a = 0 then 0 else if b = 0 then 0 else (to_multiset a ∪ to_multiset b).prod



lemma inf_comm (a b : quot α) : inf a b = inf b a :=
by by_cases ha0 : a = 0; by_cases hb0 : b = 0; simp [*, inf, inter_comm]

--left or right?
@[simp] lemma sup_zero_eq_zero_left {a : quot α} : sup 0 a = 0 :=
by simp [sup]

@[simp] lemma sup_zero_eq_zero_right {a : quot α} : sup a 0 = 0 :=
by simp [sup]

lemma sup_comm {a b : quot α} : sup a b = sup b a :=
by by_cases ha0 : a = 0; by_cases hb0 : b = 0; simp [*, sup, union_comm]


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

instance : bounded_lattice (quot α) :=
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

lemma sup_def {a b : quot α} :
  a ⊔ b = if a = 0 then 0 else if b = 0 then 0 else (to_multiset a ∪ to_multiset b).prod :=
rfl

lemma inf_def {a b : quot α} :
  a ⊓ b = if a = 0 then b else if b = 0 then a else (to_multiset a ∩ to_multiset b).prod :=
rfl



@[simp] lemma inf_zero {a : quot α} : a ⊓ 0 = a := @inf_top_eq (quot α) _ a
@[simp] lemma zero_inf {a : quot α} : 0 ⊓ a = a := @top_inf_eq (quot α) _ a

@[simp] lemma sup_zero {a : quot α} : a ⊔ 0 = 0 := @sup_top_eq (quot α) _ a
@[simp] lemma zero_sup {a : quot α} : 0 ⊔ a = 0 := @top_sup_eq (quot α) _ a



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
lattice.inf_assoc

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
lemma mul_le_of_le_of_le_of_coprime {a b c : quot α} (h1 : a ⊓ b = 1) (h2 : a ≤ c) (h3 : b ≤ c) : a * b ≤ c :=
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

lemma mul_inf_eq_one_iff_inf_eq_one_and_inf_eq_one {a b c : quot α} : a * b ⊓ c = 1 ↔ (a ⊓ c = 1 ∧ b ⊓ c = 1) :=
begin
  rw [@lattice.inf_comm _ _ (a * b) c, @lattice.inf_comm _ _ a c, @lattice.inf_comm _ _ b c],
  exact inf_mul_eq_one_iff_inf_eq_one_and_inf_eq_one,
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




--Do we need a right variant here?
lemma mul_inf_eq_self {a b  : quot α}: a * b ⊓ a = a :=
begin
  apply le_antisymm,
  apply inf_le_right,
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


--Instead of writing inf everywhere, could we use the symbols for the meet and the join?
--Or do we want to keep inf and sup because they generalize to sets?
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



--Is in isa lib
lemma gcd_mul_cancel (h1 : coprime c b) : (gcd (c * a) b ~ᵤ gcd a b) :=
begin
  rw [coprime,←mk_eq_one_iff_is_unit] at h1,
  apply complete,
  simp [mul_mk] at *,
  exact mul_inf_eq_inf_of_inf_eq_one h1,
end

lemma coprime_mul_of_coprime_of_coprime_of_coprime
   (h1 : coprime a c) (h2 :  coprime b c ) : coprime (a * b) c :=
begin
  rw [coprime,←mk_eq_one_iff_is_unit] at *, --duplicate line with gcd_mul_cancel
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







lemma inf_eq_one_iff_ne_eq_of_irred_of_irred  {a b : quot α} (ha : irred a) (hb : irred b) : a ⊓ b = 1 ↔ a ≠ b :=
begin
  split,
  {
    intro h,
    by_contradiction,
    simp * at *,
  },
  {
    intro h,
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
  }
end




lemma coprime_iff_mk_inf_mk_eq_one {a b : α} : coprime a b ↔ (mk a) ⊓ (mk b) = 1 :=
begin
  split,
  {
    intro h,
    simp [coprime, gcd, has_gcd.gcd] at h,
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
    simp [coprime, gcd, has_gcd.gcd],
    have h1 : inf (mk a) (mk b) = 1, --anoying, that this step needs to be made.
    from h,
    rw h1,
    apply is_unit_of_associated is_unit_one,
    apply complete,
    simp [one_def]
  }
end


lemma mul_dvd_of_dvd_of_dvd_of_coprime {α : Type u}{a b c: α} [unique_factorization_domain α] (h1 : coprime a b)(h2 : a ∣ c)(h3 : b ∣ c) : (a * b) ∣ c:=
begin
  rw dvd_iff_mk_le_mk at *,
  rw [mul_mk],
  rw coprime_iff_mk_inf_mk_eq_one at h1,
  exact mul_le_of_le_of_le_of_coprime h1 h2 h3,
end



@[symm] protected lemma coprime.symm {γ : Type u} [unique_factorization_domain γ] {a b : γ} (h1: coprime a b ): coprime b a :=
begin
  rw coprime at *,
  apply is_unit_of_associated h1 gcd_comm
end



def facs_to_pow  [monoid α] (p : α →₀ ℕ ) : finset α:= p.support.image (λ a, a^(p a))

--Was not consistant everywhere --I think the left should refer to the variable
@[simp] lemma gcd_one_left (a : α) : (gcd 1 a ~ᵤ 1) :=
begin
  apply complete,
  simp [one_def'],
  exact lattice.bot_inf_eq,
end

@[simp] lemma gcd_one_right (a : α) : (gcd a 1 ~ᵤ 1) :=
begin
  apply complete,
  simp [one_def'],
  exact lattice.inf_bot_eq,
end

@[simp] lemma is_unit_gcd_one_left {a : α } : is_unit (gcd 1 a) :=
begin
  apply is_unit_of_associated,
  apply is_unit_one,
  apply (gcd_one_left a).symm,
end

@[simp] lemma is_unit_gcd_one_right {a : α } : is_unit (gcd a 1) :=
begin
  apply is_unit_of_associated is_unit_one (gcd_one_right a).symm,
end

lemma coprime_mul_iff_coprime_and_coprime {a b c : α} : coprime a (b * c) ↔ coprime a b ∧ coprime a c :=
begin
  repeat {rw [coprime_iff_mk_inf_mk_eq_one]},
  rw mul_mk,
  exact inf_mul_eq_one_iff_inf_eq_one_and_inf_eq_one,
end


lemma coprime_pow {x y : α } {n : ℕ} (h : n ≠ 0) : coprime x (y ^ n) ↔ coprime x y :=
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
      rw coprime_mul_iff_coprime_and_coprime at h,
      exact h.1,
    },
    {
      intro h1,
      rw coprime_mul_iff_coprime_and_coprime,
      split,
        exact h1,
      {
        exact (ih hn).2 h1,
      }
    }
  }
end

@[simp] lemma coprime_one_left {x : α} : coprime x 1 :=
begin
  simp [coprime],
end

@[simp] lemma coprime_one_right{x : α} : coprime 1 x :=
begin
  simp [coprime],
end

lemma coprime_pow_pow_of_coprime {x y : α}{n m : ℕ}(h  : coprime x y) : coprime (x ^ n) (y ^ m) :=
begin
  by_cases h1 : n = 0,
    {simp [h1]},
    by_cases h2 : m = 0,
      {simp [h2]},
      {
        rw [coprime_pow h2],
        apply coprime.symm,
        rw [coprime_pow h1],
        exact h.symm,
      }
end


lemma coprime_of_irreducible_of_irreducible_of_not_associated {x y : α} (hx : irreducible x) (hy : irreducible y) (h : ¬ (x ~ᵤ y)) : coprime x y :=
begin
  rw associated_iff_mk_eq_mk at h,
  rw [coprime_iff_mk_inf_mk_eq_one],
  rw inf_eq_one_iff_ne_eq_of_irred_of_irred; assumption,
end

lemma coprime_iff_not_associated_of_irreducible_of_irreducible {x y : α} (hx : irreducible x) (hy : irreducible y) : coprime x y ↔ ¬ (x ~ᵤ y) :=
begin
  rw [coprime_iff_mk_inf_mk_eq_one, inf_eq_one_iff_ne_eq_of_irred_of_irred, associated_iff_mk_eq_mk],
  exact hx,
  exact hy,
end

lemma pow_mul_pow_dvd [unique_factorization_domain α] {x y z : α} {n m : ℕ}
  (hx : irreducible x) (hy : irreducible y) (hxz: x ^ n ∣ z) (hyz : y ^ m ∣ z) (h : ¬ (x ~ᵤ y)) :
  (x ^ n * y ^ m) ∣ z :=
begin
  apply @mul_dvd_of_dvd_of_dvd_of_coprime _ (x ^ n) (y ^ m) z,
  apply coprime_pow_pow_of_coprime,
  rw coprime_iff_not_associated_of_irreducible_of_irreducible,
  repeat {assumption},
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

lemma prod_inf_prod_eq_one_iff_forall_forall_inf_eq_one {t s : multiset (quot α)} : t.prod ⊓ s.prod = 1 ↔ (∀y ∈ t, (∀x ∈ s, y ⊓ x = (1 : quot α))) :=
begin
  split,
  {
    intros h y hy x hx,
    rw inf_prod_eq_one_iff_forall_inf_eq_one at h,
    have : prod t ⊓ x = 1,
      from h x hx,
    rw lattice.inf_comm at this,
    rw inf_prod_eq_one_iff_forall_inf_eq_one at this,
    have : x ⊓ y = 1,
      from this y hy,
    rw lattice.inf_comm at this,
    exact this,
  },
  {
    intros h,
    rw inf_prod_eq_one_iff_forall_inf_eq_one,
    intros x hx,
    rw lattice.inf_comm,
    rw inf_prod_eq_one_iff_forall_inf_eq_one,
    intros y hy,
    have : y ⊓ x = 1,
      from h y hy x hx,
    rw lattice.inf_comm at this,
    exact this,
  }
end


--Why do we need irreucible here?? (h : ∀x ∈ s, irreducible x)
lemma coprime_prod_iff_forall_coprime  {y: α} {s : multiset α}: coprime y s.prod ↔ ∀x ∈ s, coprime y x :=
begin
  rw coprime_iff_mk_inf_mk_eq_one,
  rw [mk_def, mk_def],
  rw [←prod_mk],
  --have h4 : ∀ x, x ∈ map mk s → irred x,
  --from forall_map_mk_irred_of_forall_irreducible h,
  rw inf_prod_eq_one_iff_forall_inf_eq_one, -- h4,
  split,
  {
    intros h1 z h3,
    rw coprime_iff_mk_inf_mk_eq_one,
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
    have h2: coprime y b,
    from h1 b hb.1,
    rw coprime_iff_mk_inf_mk_eq_one at h2,
    exact h2,
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
    apply mul_dvd_of_dvd_of_dvd_of_coprime,
    {
      rw finset_prod_eq_map_prod,
      rw coprime_prod_iff_forall_coprime,
      {
        intros y h5,
        rw mem_map at h5,
        rcases h5 with ⟨b, hb⟩,
        rw ←hb.2,
        apply coprime_pow_pow_of_coprime,
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
        rwa coprime_iff_not_associated_of_irreducible_of_irreducible (h4 a h5).1 (h4 b h7).1,
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

--Problem? could be that I need it for intergral domain?? [integral_domain α]
lemma facs_to_pow_prod_dvd_multiset {s : multiset α} {z : α}
  (h1 : ∀x∈s, irreducible x ∧ (x^(count x s)) ∣ z ∧ ∀y∈s, x ≠ y → ¬ (x ~ᵤ y)) :
  s.prod∣ z :=
begin
  revert h1,
  apply multiset.induction_on s,
  {
    simp * at *,
  },
  {
    intros a t h1 h2,
    simp * at *,
    have : repeat a (count a t) ≤ t,
    {
      rw ←multiset.le_count_iff_repeat_le,
    },
    have h3 : t - repeat a (count a t) + repeat a (count a t) = t,
      from multiset.sub_add_cancel this,
    rw [←h3, ←prod_mul_prod_eq_add_prod, mul_comm a, mul_assoc],
    apply mul_dvd_of_dvd_of_dvd_of_coprime,
    {
      apply coprime.symm,
      rw [coprime_prod_iff_forall_coprime],
      intros x h,
      have : x ≠ a,
      {
        by_contradiction hc,
        simp at hc,
        subst hc,
        rw ←count_pos at h,
        have : count x (t - repeat x (count x t)) = 0,
        {
          simp [nat.sub_self],
        },
        rw this at h,
        exact nat.not_lt_zero 0 h,
      },
      rw [prod_repeat, mul_comm, ←pow_succ, ←pow_one x],
      apply coprime_pow_pow_of_coprime,
      have ht : x ∈ t,
      {
        refine mem_of_le _ h,
        apply multiset.sub_le_self,
      },
      refine (coprime_iff_not_associated_of_irreducible_of_irreducible _ _).2 _,
      {
        refine (h2 a _).1,
        simp,
      },
      {
        refine (h2 x _).1,
        simp *,
      },
      {
        refine (h2 a _).2.2 x _ _,
        simp *,
        simp *,
        simp [ne.symm, *],
      }
    },
    {
      have : prod (t - repeat a (count a t)) ∣ prod t,
        from prod_sub_dvd_prod _,
      apply dvd_trans this,
      apply h1,
      intros x h,
      split,
      {
        refine (h2 x _).1,
        simp *,
      },
      split,
      {
        have : x ^ count x (a :: t) ∣ z,
        {
          refine (h2 x _).2.1,
          simp *,
        },
        {
          by_cases ha : x = a, --Could be done nicer
          {
            subst ha,
            rw [count_cons_self, pow_succ] at this,
            have ha2:  x ^ count x t ∣ x * x ^ count x t,
              from dvd.intro_left x (rfl),
            exact dvd_trans ha2 this,
          },
          {
            rw [count_cons_of_ne ha] at this,
            exact this,
          }

        },

      },
      {
        intros y hy,
        refine (h2 x _).2.2 y _,
        simp *,
        simp *,
      }
    },
    {
      rw [prod_repeat, mul_comm, ←pow_succ],
      have : a ^ count a (a :: t) ∣ z,
      {
        refine (h2 a _).2.1,
        simp *,
      },
      simp at this,
      exact this,
    }

  }


end


lemma dvd_of_dvd_mul_of_coprime {a b c : α} (h1 : a ∣ b * c) (h2 : coprime a b) : a ∣ c :=
begin
  rw coprime_iff_mk_inf_mk_eq_one at h2,
  rw dvd_iff_mk_le_mk at *,
  rw [mul_mk] at h1,
  apply le_of_le_mul_of_le_of_inf_eq_one h2,
  have h3 : mk c ≤ mk b * mk c,
  from le_mul_left,
  cc,
end

def composite (a : α) : Prop := a ≠ 0 ∧ (∃ b c : α, (a = b * c ∧ ¬is_unit b ∧ ¬is_unit c))

--naming? --Is this needed?
lemma eq_zero_or_is_unit_or_irreducible_or_composite (b : α) : b = 0 ∨ is_unit b ∨ irreducible b ∨ composite b :=
begin
  rw [or_iff_not_imp_left, or_iff_not_imp_left, or_iff_not_imp_left],
  intros h1 h2 h3,
  rw composite,
  rw [irreducible_iff_irreducible', irreducible'] at h3,
  simp at h3,
  simp *,
  have h4 : (¬∀ (a b_1 : α), b = a * b_1 → is_unit a ∨ is_unit b_1),
    from h3 h1 h2,
  rw _root_.not_forall at h4,
  rcases h4 with ⟨x, hx⟩,
  rw _root_.not_forall at hx,
  fapply exists.intro,
  exact x,
  rcases hx with ⟨y, hy⟩,
  fapply exists.intro,
  exact y,
  simp [not_or_distrib] at hy,
  exact hy,
end


/-
lemma classification (a : α) : a = 0 ∨ is_unit a ∨ irreducible a ∨ composite a :=
begin
  rw [or_iff_not_imp_left, or_iff_not_imp_left, or_iff_not_imp_left],
  intros h1 h2 h3,
  by_contradiction h4,
  rw composite at h4,
  simp at h4,
  have h5: ∀ (x y : α), a = x * y → ¬is_unit a → is_unit x
   -- https://github.com/leanprover/lean/issues/1822
-/



lemma coprime_of_coprime_of_associated_left {a a' b : α} (h1 : coprime a b)  (h2 : a' ~ᵤ a) : coprime a' b :=
begin
  rw coprime_iff_mk_inf_mk_eq_one at *,
  have : mk a' = mk a,
    from quot.sound h2,
  simp * at *,
end

lemma coprime_of_coprime_of_associated_right {a b b': α} (h1 : coprime a b)  (h2 : b' ~ᵤ b) : coprime a b' :=
begin
  have h3 : coprime b a,
    from h1.symm,
  apply coprime.symm,
  exact coprime_of_coprime_of_associated_left h3 h2,
end

end ufd
