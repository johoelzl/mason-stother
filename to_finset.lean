import data.multiset data.finset .to_multiset

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