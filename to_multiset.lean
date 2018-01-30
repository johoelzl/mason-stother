import data.multiset data.finset

open classical multiset finset
local attribute [instance] prop_decidable

universe u
variable α : Type u 
namespace multiset
--simp correct?
theorem multiset.not_mem_empty (a : α) : a ∉ (∅ : finset α) := id --why does this work?

lemma map_id_eq {f : multiset α} : f.map id = f :=
begin
  apply multiset.induction_on f,
  {
    simp
  },
  {
    simp
  }
end

lemma prod_mul_prod_eq_add_prod [comm_monoid α] {a b : multiset α} : a.prod * b.prod = (a + b).prod :=
begin
  simp,
end

end multiset