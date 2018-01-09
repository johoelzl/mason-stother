import data.multiset data.finset

open classical multiset finset
local attribute [instance] prop_decidable

universe u
variable α : Type u 

--simp correct?
@[simp] theorem multiset.not_mem_empty (a : α) : a ∉ (∅ : finset α) := id --why does this work?