import data.multiset data.finset .to_multiset algebra.big_operators

open classical multiset finset
local attribute [instance] prop_decidable

universe u
variable α : Type u
--set_option pp.implicit true
--set_option pp.notation false

--Should this be made into 0???
lemma eq_zero_iff_to_finset_eq_empty {g : multiset α} : g = 0 ↔ g.to_finset = ∅ :=
begin
  apply iff.intro,
  {
    intro h1,
    rw finset.ext,
    intro a,
    simp [*]
  },
  {
    intro h1,
    by_contradiction h2,
    rw ←ne.def at h2,
    have h2 : ∃a : α, a ∈ g,
    from exists_mem_of_ne_zero h2,
    let m := some h2,
    have : m ∈ g,
    from some_spec h2,
    rw [←mem_to_finset, h1] at this,
    have : ¬ m ∈ ∅,
    from finset.not_mem_empty m,
    contradiction
  }
end

/-
 apply finset.induction_on f,
  {
    simp *,
  },
  {
    intros a s h1 h2 h3,
    have h4 : (∀ (x : polynomial α), x ∈ s → x ≠ 0),
    {
      intros x h4,
      apply h3 x,
      simp *,
    },
    rw finset.prod_insert h1,
    have h5 : finset.prod s id ≠ 0,
    from h2 h4,
    have h6 : a ≠ 0,
    {
      apply h3,
      simp,
    },
    simp,
    exact mul_ne_zero h6 h5,
-/

lemma prod_ne_zero_of_forall_mem_ne_zero' {β : Type u} [has_zero α] [integral_domain β] {f : finset α } {g : α → β} (ha : ∀ x : α, x ≠ 0 → g x ≠ 0)(hb : (0 : β) ≠ 1): (∀ x ∈ f, x ≠ (0 :α)) → (finset.prod f g ≠ 0) :=
begin
 apply finset.induction_on f,
  {
    simp *,
  },
  {
    intros a s h1 h2 h3,
    have h4 : (∀ (x : α), x ∈ s → x ≠ 0),
    {
      intros x h4,
      apply h3 x,
      simp *,
    },
    rw finset.prod_insert h1,
    have h5 : finset.prod s g ≠ 0,
    from h2 h4,
    have h6 : a ≠ 0,
    {
      apply h3,
      simp,
    },
    have h7 : g a ≠ 0,
    from ha _ h6,
    exact mul_ne_zero h7 h5,
  }
end