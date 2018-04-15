import data.finsupp
import algebra.ring
import .to_finset
import .to_multiset
import to_semiring
import to_comm_semiring
import to_integral_domain

noncomputable theory

local infix ^ := monoid.pow

open classical
local attribute [instance] prop_decidable

universe u
variable {α : Type u}


--can the priority be set better? Because now we often have to provide parentheses
local notation a `~ᵤ` b : 50 := associated a b

namespace associated
open multiset







def setoid (β : Type u) [comm_semiring β] : setoid β :=
{ r := associated, iseqv := associated.eqv }
local attribute [instance] setoid

section comm_semiring
variable [comm_semiring α]


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
    rcases h1 with ⟨u, hu⟩,
    subst hu,
    exact mk_unit_eq_one,
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


--is eq_one better then is_unit_quot?
lemma is_unit_quot_of_mul_eq_one_left {a b : quot α} (h : a * b = 1) : is_unit_quot a :=
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

lemma is_unit_quot_of_mul_eq_one_right {a b : quot α} (h : a * b = 1) : is_unit_quot b :=
begin
  rw mul_comm at h,
  exact is_unit_quot_of_mul_eq_one_left h,
end

lemma mul_mono {a b c d : quot α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
let ⟨x, hx⟩ := h₁, ⟨y, hy⟩ := h₂ in
⟨x * y, by simp [hx.symm, hy.symm, mul_comm, mul_assoc, mul_left_comm]⟩

lemma le_mul_right {a b : quot α} : a ≤ a * b := ⟨b, rfl⟩

lemma le_mul_left {a b : quot α} : a ≤ b * a := by rw [mul_comm]; exact le_mul_right


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

@[simp] lemma le_self {a : quot α} : a ≤ a:=
begin
  exact ⟨1, by simp⟩,
end





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
-/


end comm_semiring



section integral_domain
variable [integral_domain α]


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

--Think it should be le not subset
--lemma prod_le_prod_of_subset {p q : multiset (quot α)} (h : p ⊆ q) : p.prod ≤ q.prod :=
--Could we work with  lattice morphism?
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


lemma bot_def : ⊥ = (1 : quot α) := rfl
lemma top_def : ⊤ = (0 : quot α) := rfl

lemma zero_is_top (a : quot α) : a ≤ 0 := ⟨0, mul_zero⟩

lemma one_le :  ∀ (a : quot α), 1 ≤ a :=
assume a, ⟨a, by simp⟩


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

--irred



def irred (a : quot α) : Prop :=
quotient.lift_on a irreducible $
assume a b h, propext $ iff.intro
  (assume h', irreducible_of_associated h' h)
  (assume h', irreducible_of_associated h' h.symm)

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

@[simp] lemma not_irred_one : ¬ irred (1 : quot α) :=
not_irreducible_one

lemma one_def' : mk (1 : α) = 1 := rfl


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

end integral_domain




-- Can we Prove the existence of a gcd here? Problem is has_dvd, why is it not defined here??
--If we can show the existence of a gcd here, we can reuse some lemmas









end associated