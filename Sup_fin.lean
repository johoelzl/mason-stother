import order.lattice data.finset
universes u v w

noncomputable theory

open classical set function lattice

instance {α : Type u} [semilattice_sup α] : is_idempotent α (⊔) := ⟨assume a, sup_idem⟩

namespace finset
section general


variables {α : Type u} {β : Type w} [decidable_eq β] [semilattice_sup_bot α]

def Sup_fin (s : finset β) (f : β → α) : α := s.fold (⊔) ⊥ f

variables {s s₁ s₂ : finset β} {f : β → α}

@[simp] lemma Sup_fin_empty : (∅ : finset β).Sup_fin f = ⊥ :=
fold_empty

@[simp] lemma Sup_fin_insert {b : β} : (insert b s : finset β).Sup_fin f = f b ⊔ s.Sup_fin f :=
fold_insert_idem

@[simp] lemma Sup_fin_singleton {b : β} : (finset.singleton b).Sup_fin f = f b :=
calc _ = f b ⊔ (∅:finset β).Sup_fin f : Sup_fin_insert
  ... = f b : by simp

lemma Sup_fin_union : (s₁ ∪ s₂).Sup_fin f = s₁.Sup_fin f ⊔ s₂.Sup_fin f :=
finset.induction_on s₁ (by simp) (by simp {contextual := tt}; cc)

lemma Sup_fin_mono_fun {g : β → α} : (∀b∈s, f b ≤ g b) → s.Sup_fin f ≤ s.Sup_fin g :=
finset.induction_on s (by simp) (by simp [-sup_le_iff, sup_le_sup] {contextual := tt})

lemma le_Sup_fin {b : β} (hb : b ∈ s) : f b ≤ s.Sup_fin f :=
calc f b ≤ f b ⊔ s.Sup_fin f : le_sup_left
  ... = (insert b s).Sup_fin f : by simp
  ... = s.Sup_fin f : by simp [hb]

lemma Sup_fin_le {a : α} : (∀b ∈ s, f b ≤ a) → s.Sup_fin f ≤ a :=
finset.induction_on s (by simp) (by simp {contextual := tt})

lemma Sup_fin_mono (h : s₁ ⊆ s₂) : s₁.Sup_fin f ≤ s₂.Sup_fin f :=
Sup_fin_le $ assume b hb, le_Sup_fin (finset.subset_iff.mpr h hb)

end general


end finset

instance nat.distrib_lattice : distrib_lattice ℕ :=
by apply_instance

instance nat.semilattice_sup_bot : semilattice_sup_bot ℕ :=
{ bot := 0, bot_le := nat.zero_le , .. nat.distrib_lattice }

lemma nat.sup_eq_max {n m : ℕ} : n ⊔ m = max n m := rfl

namespace finset

lemma Sup_fin_mem_of_id_nat {s : finset ℕ} : s ≠ ∅ → Sup_fin s id ∈ s :=
finset.induction_on s
  (by contradiction)
  (by intros a s; by_cases s = ∅; cases le_total a (Sup_fin s id);
      simp [*, nat.sup_eq_max, max_eq_left, max_eq_right] {contextual := tt})

end finset
