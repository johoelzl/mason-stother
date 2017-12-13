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

@[simp] lemma Sup_fin_singleton {b : β} : ({b} : finset β).Sup_fin f = f b :=
calc _ = f b ⊔ (∅:finset β).Sup_fin f : Sup_fin_insert
  ... = f b : by simp

lemma Sup_fin_union : (s₁ ∪ s₂).Sup_fin f = s₁.Sup_fin f ⊔ s₂.Sup_fin f :=
s₁.induction_on (by simp) (by simp {contextual := tt}; cc)

lemma Sup_fin_mono_fun {g : β → α} : (∀b∈s, f b ≤ g b) → s.Sup_fin f ≤ s.Sup_fin g :=
s.induction_on (by simp) (by simp [-sup_le_iff, sup_le_sup] {contextual := tt})

lemma le_Sup_fin {b : β} (hb : b ∈ s) : f b ≤ s.Sup_fin f :=
calc f b ≤ f b ⊔ s.Sup_fin f : le_sup_left
  ... = (insert b s).Sup_fin f : by simp
  ... = s.Sup_fin f : by simp [hb]

lemma Sup_fin_le {a : α} : (∀b ∈ s, f b ≤ a) → s.Sup_fin f ≤ a :=
s.induction_on (by simp) (by simp {contextual := tt})

lemma Sup_fin_mono (h : s₁ ⊆ s₂) : s₁.Sup_fin f ≤ s₂.Sup_fin f :=
Sup_fin_le $ assume b hb, le_Sup_fin (mem_of_subset_of_mem h hb)

end general


end finset


instance nat.distrib_lattice : distrib_lattice ℕ :=
by apply_instance

instance nat.semilattice_sup_bot : semilattice_sup_bot ℕ :=
{ bot := 0, bot_le := nat.zero_le , .. nat.distrib_lattice }

namespace finset

lemma Sup_fin_mem_of_id_nat : ∀ (s : finset ℕ),s ≠ ∅ →  (Sup_fin s id) ∈ s :=
begin
refine @finset.induction _ _ (λs : finset ℕ, s ≠ ∅ →  (Sup_fin s id) ∈ s ) _ _,
intros,
{contradiction},
{intros,
have htmp : s = ∅ ∨ s ≠ ∅, from classical.em _,
cases (htmp),
{
  have : insert a ∅  = {a}, 
  apply rfl, 
  rw ←a_4 at this,
  rw this,
  have : Sup_fin {a} id = id a,
  apply Sup_fin_singleton,
  simp [id]
},
{ 
  have hdec : Sup_fin (insert a s) id = id a ⊔ s.Sup_fin id,
  apply Sup_fin_insert,
  have : Sup_fin s id ∈ s, simp [a_2, a_4],
  cases (le_total a (Sup_fin s id)) with h1 h1,
  {
    have h2: (Sup_fin s id) ≤ (Sup_fin s id), from le_refl _,
    have h3: (a ⊔ Sup_fin s id) ≤ Sup_fin s id, 
    apply sup_le _ _, assumption, apply le_refl,
    have h4: (Sup_fin s id) ≤ (a ⊔ (Sup_fin s id)), from le_sup_right,
    have h5: (a ⊔ (Sup_fin s id)) = (Sup_fin s id), from le_antisymm h3 h4,
    rw [hdec],
    have : id a = a, from rfl, 
    rw this,   
    apply mem_insert_of_mem, 
    rw [h5],
    assumption
  },
  {
    have h2: (a) ≤ (a), from le_refl _,
    have h3: (a ⊔ Sup_fin s id) ≤ a,
    apply sup_le _ _, assumption, from h1,
    have h4: a ≤ (a ⊔ (Sup_fin s id)), from le_sup_left,
    have h5: (a ⊔ (Sup_fin s id)) = (a), from le_antisymm h3 h4,
    rw [hdec],
    have : id a = a, from rfl, 
    rw this,   
    rw h5,
    simp
  }
}
}

end

end finset
