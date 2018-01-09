import data.finsupp
universes u v w

open classical finsupp finset
local attribute [instance] prop_decidable

namespace polynomial


--This lemma should be placed in finsupp
--Maybe only keep the iff version?
lemma eq_zero_of_support_eq_empty {α : Type u} {β : Type v} [has_zero β] (s : α →₀ β): 
s.support = ∅ → s = 0 :=
begin 
  intro h,
  refine @finsupp.ext _ _ _ s 0 _,
  intro q,
  by_cases h1 : (q ∈ support s),
  {
    have : q ∉ ∅, from not_mem_empty q,
    rw h at h1,
    contradiction
  },
  { 
    have h2: (s q ≠ 0) → (q ∈ s.support), from  iff.elim_right  (mem_support_iff s),
    rw [←not_imp_not,not_not] at h2,
    have : s q = 0, from h2 h1,
    have : (0 : α →₀ β) q = 0, 
    all_goals {simp * at *}
  }
end

--This lemma should be placed in finsupp
lemma eq_zero_iff_support_eq_empty {α : Type u} {β : Type v} [has_zero β] (s : α →₀ β): 
s = 0 ↔ s.support = ∅ :=
begin
  constructor,
  {
    intro h1,
    rw h1,
    simp,
  },
  exact eq_zero_of_support_eq_empty s
end

--This lemma should be placed in finsupp
lemma eq_single_of_support_eq_singleton {α : Type u} {β : Type v} [has_zero β] (s : α →₀ β){q : α}:
s.support = {q} → ∃w : β, s = single q w :=
begin 
  intro h1,
  fapply exists.intro,
  apply s q,
  refine @finsupp.ext _ _ _ s (single q (s q)) _,
  intro w,
  by_cases h3 : (w = q),
  {
    simp * at *,
  },
  {
    have h2 : q ∈ support s,
    rw h1,
    simp,
    simp * at *,
    have h4: w ∉ finset.singleton q,
    from iff.elim_right not_imp_not (iff.elim_left finset.mem_singleton) h3,
    rw ←h1 at h4,
    have h5 : ¬ s w ≠ 0,
    from iff.elim_right not_imp_not (iff.elim_right (finsupp.mem_support_iff s)) h4,
    rw not_not at h5,
    have h6: ((single q (s q)) : α → β) w = 0,
    simp [single_apply],
    apply if_neg,
    simp [ne.symm h3],
    simp * at *
  },
end


--Should be in finsupp --can't add congr attribute, is this a proper congr lemma?
lemma finsupp.sum_congr {α : Type u}{β : Type v}{γ : Type w} [has_zero β] [add_comm_monoid γ] {s₁ s₂ : α →₀ β}{f g : α → β → γ}(h : support s₁ = support s₂) : 
(∀x ∈ support s₂, f x (s₁ x) = g x (s₂ x)) → s₁.sum f = s₂.sum g :=
begin
  exact finset.sum_congr h
end

--can't add congr attribute, is this a proper congr lemma?
lemma finsupp.sum_congr_2 {α : Type u}{β : Type v}{γ : Type w} [has_zero β] [add_comm_monoid γ] {s₁ s₂ : α →₀ β}{f g : α → β → γ}(h : s₁ = s₂) : 
(∀x ∈ support s₂, f x (s₁ x) = g x (s₂ x)) → s₁.sum f = s₂.sum g :=
begin
  have h1 : s₁.support = s₂.support,
  simp [h],
  exact finset.sum_congr h1
end


--Should be placed in finset
lemma finset.sum_ite {α : Type u} {β : Type v} [add_comm_monoid β] {x : α} {y : β} (s : finset α) : 
s.sum (λ z, if (z = x) then y else 0) = if (x ∈ s) then y else 0:=
begin 
  fapply finset.induction_on s,
  simp,
  intros a s h1a h2,
  have h1: finset.sum (insert a s) (λ (z : α), ite (z = x) y 0) =  (λ (z : α), ite (z = x) y 0) a + finset.sum (s) (λ (z : α), ite (z = x) y 0),
  apply finset.sum_insert,
  assumption,
  rw h1,
  rw h2,
  simp,
  by_cases h3 :(a = x),
  {
    simp [*, if_pos],
    rw h3 at h1a,
    simp [*, if_neg],
  },
  {
    simp [*, if_neg],
    by_cases h4 : (x ∈ s),
    {
      simp [*, if_pos]
    },
    {
      simp [*, if_neg],
      have : ¬ x = a,
      intro h5,
      rw h5 at h3,
      have : a = a,
      simp,
      contradiction,
      simp [*, if_neg]
    }
  }
end

lemma finset.sum_ite_general' {α : Type u} {β : Type v} [add_comm_monoid β] {f g : α → β} (s : finset α) 
  (p : α → Prop) [decidable_pred p] : 
s.sum (λ z, if p z then f z else g z) = (s.filter p).sum f + (s.filter $ λx, ¬ p x).sum g :=
sorry

--Should be placed in finset -should the more specific lemma be local?
lemma finset.sum_ite_general {α : Type u} {β : Type v} [add_comm_monoid β] {x : α} {f : α → β} (s : finset α) : 
s.sum (λ z, if (z = x) then f z else 0) = if (x ∈ s) then f x else 0:=
begin
  have :  s.sum (λ z, if (z = x) then f z else 0) = s.sum (λ z, if (z = x) then f x else 0),
  apply finset.sum_congr,
  simp,
  intros y h1,
  by_cases h2: (y = x),
  {
    simp [*, if_pos]
  },
  {
    simp [*, if_neg]
  },
  rw this,
  apply @finset.sum_ite _ _ _ x (f x) s,
end



-- should be placed in finsupp
lemma finsupp.sum_ite {α : Type u}{β : Type v}{γ : Type w} [has_zero β] [add_comm_monoid γ] {x : α}{s : α →₀ β} {f : α → β → γ} :
s.sum (λ a b, if (a = x) then f a b else 0) = if (x ∈ s.support) then f x (s x) else 0 :=
begin
  unfold finsupp.sum,
  refine @finset.sum_ite_general _ _ _ x (λ y, f y (s y)) s.support
end

--should be placed in finsupp
lemma finsupp.sum_mul {α : Type u}{β : Type v}{γ : Type w}  [semiring β] [semiring γ] {b : γ} {s : α →₀ β} {f : α → β → γ} :
(s.sum f) * b = s.sum (λ a c, (f a (s a)) * b) :=
by simp [finsupp.sum,finset.sum_mul]

--should be placed in finsupp
lemma finsupp.mul_sum {α : Type u}{β : Type v}{γ : Type w}  [semiring β] [semiring γ] {b : γ} {s : α →₀ β} {f : α → β → γ} :
b * (s.sum f) = s.sum (λ a c, b * (f a (s a))) :=
by simp [finsupp.sum,finset.mul_sum]

--should be placed in finset

lemma erase_insert_eq_insert_erase {α : Type u} {s : finset α} {a b : α} (h : a ≠ b) :
  erase (insert a s) b = insert a (erase s b) :=
finset.ext.mpr begin intro c, by_cases c = a; by_cases c = b; simp [h, *] at * end


end polynomial