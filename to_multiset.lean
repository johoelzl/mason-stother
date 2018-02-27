import data.finsupp .to_finsupp
open classical 
local attribute [instance] prop_decidable
noncomputable theory
local infix ^ := monoid.pow
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

open finsupp 

def to_finsupp {α : Type u} (m : multiset α) : α →₀ ℕ := 
(m.map $ λa, single a 1).sum


lemma to_finsupp_add {α : Type u} (m n : multiset α) :
   (m + n).to_finsupp = m.to_finsupp + n.to_finsupp :=
calc (m + n).to_finsupp = ((m.map $ λa, single a 1) + (n.map $ λa, single a 1)).sum :
    by rw [← multiset.map_add]; refl
  ... = m.to_finsupp + n.to_finsupp :
    by rw [multiset.sum_add]; refl

lemma to_finsupp_prod {α : Type*} [comm_monoid α] (m : multiset α) :
m.prod = (finsupp.prod (m.to_finsupp) (λ k n, k ^ n) ) := 
begin
  apply multiset.induction_on m,
  {
    simp [to_finsupp, prod_zero_index], 
  },
  {
    intros a s h1,
    simp [*, to_finsupp] at *,
    rw [prod_add_index, prod_single_index],
    repeat {simp [pow_add]}
  }
end



lemma to_finsupp_support {α : Type u} (m : multiset α) : m.to_finsupp.support = m.to_finset :=
begin
  apply multiset.induction_on m,
  {
    simp [*, to_finsupp, to_finset] at *,
    exact rfl,
  },
  {
    intros a s h1,
    simp [*, to_finsupp, to_finset] at *,
    apply finset.subset.antisymm,
    {
       intros y h2,
       have h3 : support (single a 1 + sum (map (λ (a : α), single a 1) s)) ⊆ support (single a 1) ∪ support (sum (map (λ (a : α), single a 1) s)),
       from support_add,
       have h4 : y ∈ support (single a 1) ∪ support (sum (map (λ (a : α), single a 1) s)),
       from mem_of_subset h3 h2,
       rw [h1, finset.mem_union] at h4,
       cases h4,
       {
         rw [support_single_ne_zero] at h4,
         simp * at *,
         exact ne.symm zero_ne_one,
       },
       {
         simp,
         by_cases h5 : (y = a),
         {
           simp *,
         },
         {
           have h5 : y ∈ s,
           {
             rw ←mem_erase_dup,
             exact h4,
           },
           simp *,           
         }
       }
    },
    {
      intros y h2,
      have h3 : support (single a 1 + sum (map (λ (a : α), single a 1) s)) ⊆ support (single a 1) ∪ support (sum (map (λ (a : α), single a 1) s)),
      from support_add,

      have h4 : y ∈ support (single a 1) ∪ support (sum (map (λ (a : α), single a 1) s)),
      {
        rw [finset.mem_union],
        by_cases h4 : (y = a),
        {
          subst h4,
          rw [support_single_ne_zero],
          simp,
          exact ne.symm zero_ne_one,
        },
        {
          rw h1,
          have h5 :  y ∈  erase_dup s,
          {
            rw mem_erase_dup,
            have : y ∈ erase_dup (a :: s),
            exact h2,
            rw mem_erase_dup at this,
            simp * at *,

          },
          simp * at *,
        }
      },
      rw [h1, finset.mem_union] at h4,
      have h5 :   support (single a 1 + sum (map (λ (a : α), single a 1) s)) =
      support (single a 1) ∪ support (sum (map (λ (a : α), single a 1) s)),
      {
        apply finset.subset.antisymm,
        {
          exact h3,
        },
        {
          intros x h5,
          simp at h5,
          cases h5,
          {
            simp,
            by_contradiction h6,
            have : (single a 1).val x = 0,
            from nat.eq_zero_of_add_eq_zero_right h6,
            exact h5 this,
          },
          {
            simp,
            by_contradiction h6,
            have : (sum (map (λ (a : α), single a 1) s)).val x = 0,
            from nat.eq_zero_of_add_eq_zero_left h6,
            exact h5 this,           
          },
        }
      },
      rw h5,
      simp * at *,   
    }
  },

end

lemma to_finsupp_support_subset {α : Type u} (m : multiset α) : m.to_finsupp.support.val ⊆ m :=
begin
  intros x h1,
  rw to_finsupp_support at h1,
  rw ← mem_to_finset,
  exact h1,
end
lemma to_finsupp_predicate {α : Type u} (m : multiset α) (p : α → Prop) : 
(∀x ∈ m, p x) ↔ (∀x ∈ (m.to_finsupp).support, p x) :=
iff.intro
  begin
    intros h1 x h2,
    rw [to_finsupp_support, mem_to_finset] at h2,
    exact h1 _ h2,
  end
  begin
    intros h1 x h2,
    rw [to_finsupp_support] at h1,
    have h3 : x ∈ to_finset m → p x,
    from h1 x,
    rw [mem_to_finset] at h3,
    exact h3 h2,
  end

lemma sum_map_eq_zero_iff_forall_eq_zero (f : α → multiset α) (s : multiset α) : sum (map f s) = 0 ↔ ∀ x ∈ s, f x = 0 :=
begin
  split,
  {
    apply multiset.induction_on s,
    {
      simp * at *,
    },
    {
      intros a s h1 h2 y h3,
      simp * at *,
      cases h3,
      {
        simp * at *,
      },
      {
        exact h1 y h3,
      }    
    }
  },
  {
    intros h1,
    revert h1,
    apply multiset.induction_on s,
    {
      simp * at *,
    },
    {
      intros a s h1 h2,
      simp * at *,
      apply h1,
      intros x h3,
      apply h2,
      simp * at *,
    }
  }
end

lemma sum_map_singleton {α : Type u} {s : multiset α} : sum (map (λ x, {x}) s) = s :=
begin
  apply multiset.induction_on s,
  {
    simp * at *,
  },
  {
    intros a s h1,
    simp * at *,
    rw add_comm,
    exact singleton_add _ _,
  }
end

lemma finset_prod_eq_map_prod {α β : Type u} [comm_monoid β] {s : finset α} (f : α → β) : finset.prod s f = (map f s.val).prod :=
begin
  exact rfl, --nice
end

lemma prod_ne_zero_of_forall_mem_ne_zero {α : Type u} [integral_domain α] (s : multiset α) (h : ∀x : α, x ∈ s → x ≠ 0) : s.prod ≠ 0 :=
begin
  revert h,
  apply multiset.induction_on s,
  {
    simp, 
  },
  {
    intros a s h1 h2,
    simp * at *,
    apply mul_ne_zero,
    {
      apply h2 a,
      simp,
    },
    {
      apply h1,
      intros x h3,
      apply h2 x,
      simp *,
    }
  }
end

lemma sub_erase_dup_add_erase_dup_eq {α : Type u} (s : multiset α) : s - s.erase_dup + s.erase_dup = s :=
multiset.sub_add_cancel (erase_dup_le _)

lemma sum_map_mul {α β: Type u} [semiring β] (a : β) (f : α → β) (s : multiset α): 
  multiset.sum (multiset.map (λ (b : α), a * f b) s) =
  a * multiset.sum (multiset.map (λ (b : α), f b) s):=
begin
  apply multiset.induction_on s,
  {
    simp * at *,
  },
  {
    intros a s h,
    simp [*, mul_add],
  }
end

--Naming correct or dvd_sum_of_forall_mem_dvd
lemma dvd_sum [comm_semiring α] (s : multiset α) (p : α) : (∀x ∈ s, p ∣ x) → p ∣ s.sum :=
begin
  apply multiset.induction_on s,
  {
    simp * at *,
  },
  {
    intros a s h1 h2,
    simp * at *,
    apply dvd_add,
    {
      apply h2,
      simp,
    },
    {
      apply h1,
      intros x h3,
      apply h2,
      simp [h3],
    }
  }
end


lemma forall_pow_count_dvd_prod {α : Type u} [comm_semiring α] (s : multiset α) : ∀x : α , x ^ count x s ∣ prod s :=
begin
  intros x,
  by_cases hx : x ∈ s,
  {
    apply multiset.induction_on s,
    {
      simp,
    },
    {
      intros a s h,
      simp,
      by_cases h1 : x = a,
      {
        subst h1,
        rw [count_cons_self, pow_succ],
        apply mul_dvd_mul_left,
        assumption,  
      },
      {
        rw count_cons_of_ne h1,
        apply dvd_mul_of_dvd_right,
        exact h,
      }
    }
  },
  {
    rw ←count_eq_zero at hx,
    simp *,
  }
end

lemma pow_count_sub_one_dvd_pow_count {α : Type u} [comm_semiring α] (s : multiset α) (x : α) : x ^ (count x s - 1) ∣ x ^ count x s :=
begin
  by_cases h1 : (count x s) ≥ 1,
  {
    rw [←nat.sub_add_cancel h1] {occs := occurrences.pos [2]},
    rw [pow_add],
    apply dvd_mul_of_dvd_left,
    simp,
  },
  {
    have : count x s < 1,
      from lt_of_not_ge h1,
    have : nat.succ (count x s) ≤ 1,
      from this,
    have : count x s ≤ 0,
      from nat.le_of_succ_le_succ this,
    have : count x s = 0,
      from nat.eq_zero_of_le_zero this,
    simp *,
  }
end

lemma prod_dvd_prod_of_le [comm_semiring α] {p q : multiset (α)} (h : p ≤ q) : p.prod ∣ q.prod :=
begin
  have h1 : p + (q - p) = q,
  from multiset.add_sub_of_le h,
  rw ← h1,
  simp,
end

lemma prod_sub_dvd_prod [comm_semiring α] {s t : multiset α} : (s - t).prod ∣ s.prod :=
begin
  apply prod_dvd_prod_of_le,
  apply sub_le_self,
end

end multiset