import  .Sup_fin data.finsupp order.lattice data.nat.cast .euclidean_domain unique_factorization_domain
universes u v w

noncomputable theory

open classical set function finsupp lattice
local attribute [instance] prop_decidable
local attribute [instance] finsupp.to_comm_semiring
local attribute [instance] finsupp.to_semiring
local infix ^ := monoid.pow

namespace finset
--Why is this here?
lemma erase_insert_eq_insert_erase {α : Type u} {s : finset α} {a b : α} (h : a ≠ b) :
  erase (insert a s) b = insert a (erase s b) :=
finset.ext.mpr begin intro c, by_cases c = a; by_cases c = b; simp [h, *] at * end

end finset

-- TODO: relax semiring to semi-algebra?
def polynomial (α : Type u) [semiring α] := ℕ →₀ α

namespace polynomial
variables {α : Type u} {a a' a₁ a₂ : α} {n m : ℕ}

section semiring
variable [semiring α]

instance : has_coe_to_fun (polynomial α) := finsupp.has_coe_to_fun
instance : has_zero (polynomial α) := finsupp.has_zero
instance : has_one (polynomial α) := finsupp.has_one
instance : has_add (polynomial α) := finsupp.has_add
instance : has_mul (polynomial α) := finsupp.has_mul
instance : semiring (polynomial α) := finsupp.to_semiring


@[simp] lemma one_apply_zero : (1 : polynomial α) 0 = 1 :=
single_eq_same

@[simp] lemma zero_apply {n : ℕ} : (0 : polynomial α) n = 0 :=
zero_apply

def C (a : α) : polynomial α := finsupp.single 0 a

--embed R in R[x]
instance : has_coe (α) (polynomial α) := ⟨C⟩ -- Is this embedding correct?

lemma embedding {a : α} : (a : polynomial α) = C a := rfl

@[simp] lemma C_0 : C 0 = (0:polynomial α) := single_zero

@[simp] lemma C_1 : C 1 = (1:polynomial α) := rfl

lemma C_apply {c : α } {n : ℕ}: ((C c) : ℕ → α) n = (if 0 = n then c else 0) :=
rfl


--naming?
lemma eq_zero_iff_embed_eq_zero {f : α} : f = 0 ↔ (f : polynomial α) = 0 :=
begin 
  rw embedding,
  constructor,
  {
    intro h,
    rw h,
    simp, -- added to simp, why does simp not work? maybe because it doesn't backtrack?
  },
  {
    intro h,
    have : ((C f) : ℕ → α) 0 = f,
    simp [C_apply],
    rw h at this,
    rw ←this,
    simp
  }

end

def X : polynomial α := finsupp.single 1 1

lemma X_apply {n : ℕ}: ((X : polynomial α): ℕ → α) n = (if 1 = n then 1 else 0) :=
rfl

lemma single_eq_X_pow : ∀{n:ℕ}, single n a = C a * X ^ n
| 0       := by simp [C]
| (n + 1) :=
  calc single (n + 1) a = single n a * X : by simp [X, single_mul_single]
    ... = C a * X ^ (n + 1) : by rw [@single_eq_X_pow n]; simp [pow_add, pow_one, mul_assoc]

lemma X_pow_eq_single {n:ℕ} : (X ^ n : polynomial α) = single n 1 :=
begin  
  calc (X ^ n : polynomial α) = C 1 * X ^ n : by simp [C_apply]
  ... = single n 1 : eq.symm single_eq_X_pow,
end
--naming?
lemma sum_const_mul_pow_X  {f : polynomial α} : @finsupp.sum ℕ  α  (polynomial α) _ _ (f : ℕ →₀ α) (λ n a, C a * X ^ n) = f :=
begin
  have h1: f.sum single = f, from sum_single,
  simp [finsupp.sum] at h1,
  have h2 : finset.sum (support f) (λ (a : ℕ), single a (f a)) =  sum f (λ (n : ℕ) (a : α), C a * X ^ n),
  apply finset.sum_congr,
  simp,
  intros x h2,
  apply single_eq_X_pow,
  rw ←h2,
  exact h1
end

lemma induction_on {M : polynomial α → Prop} (p : polynomial α)
  (M_C : ∀(a : α), M (C a)) (M_X : M X)
  (M_add : ∀{p q}, M p → M q → M (p + q))
  (M_mul : ∀{p q}, M p → M q → M (p * q)) :
  M p :=
have M_0 : M 0, by rw [←C_0]; exact M_C 0,
have M_1 : M 1, from M_C 1,
have M_single : ∀n c, M (single n c),
begin
  assume n a,
  rw [single_eq_X_pow],
  apply M_mul (M_C a),
  induction n; simp [M_1, pow_add, pow_one, nat.succ_eq_add_one, *]; exact M_1
end,
have M_sum : ∀{s:finset ℕ} {f : ℕ → polynomial α}, (∀a∈s, M (f a)) → M (s.sum f),
  from assume s f, finset.induction_on s (by simp [M_0]) (by simp * {contextual := tt}),
begin
  rw [←@sum_single _ _ _ p],
  apply M_sum,
  exact (assume a ha, M_single _ _)
end


lemma induction_on_X {M : polynomial α → Prop} (p : polynomial α)
  (M_C : ∀(a : α), M (C a))
  (M_X : M X)
  (M_add : ∀{p q}, M p → M q → M (p + q))
  (M_mul_X : ∀{p}, M p → M (p * X) ):
  M p :=
have M_0 : M 0, by rw [←C_0]; exact M_C 0,
have M_1 : M 1, from M_C 1,
have M_single : ∀n c, M (single n c),
begin
assume n a, simp [single_eq_X_pow ],
induction n, have htmp : C a * X ^ 0 = C a, simp [pow_zero], simp [pow_zero], exact M_C _, simp [pow_succ'],
have htmp3 : (C a * (X ^ n_n * X)) = (C a * (X ^ n_n) * X), simp [mul_assoc], rw [htmp3], apply M_mul_X, assumption
end,
have M_sum : ∀{s:finset ℕ} {f : ℕ → polynomial α}, (∀a∈s, M (f a)) → M (s.sum f),
  from assume s f, finset.induction_on s (by simp [M_0]) (by simp * {contextual := tt}),
begin
  rw [←@sum_single _ _ _ p],
  apply M_sum,
  exact (assume a ha, M_single _ _)
end


def eval (p : polynomial α) (a : α) : α := p.sum $ λn c, c * a ^ n

def degree (p : polynomial α) : ℕ := p.support.Sup_fin id

def leading_coeff (p : polynomial α) : α := p (degree p)

lemma ext : ∀{f g : polynomial α}, (∀a, f a = g a) → f = g:=
begin
  apply @finsupp.ext
end

lemma exists_coeff_ne_zero_of_ne_zero {f : polynomial α}: f ≠ 0 → ∃m, f m ≠ 0:=
begin
  intro h,
  have : ¬(∀k, f k = (0 : polynomial α) k),
  apply (iff.elim_right not_imp_not ext),
  exact h,
  exact (classical.prop_decidable _),
  apply (iff.elim_left classical.not_forall this)
end



lemma le_degree {p : polynomial α} {n : ℕ} (h : p n ≠ 0) : n ≤ degree p :=
show id n ≤ degree p, from finset.le_Sup_fin (by simp [h])

@[simp] lemma degree_zero : degree (0 : polynomial α) = 0 :=
have (0 : polynomial α).support = ∅, from support_zero,
by simp [degree, this]; refl

lemma degree_single {a : α} {n : ℕ} : degree (single n a) ≤ n :=
calc degree (single n a) = (single n a).support.Sup_fin id : by simp [degree]
  ... ≤ (finset.singleton n).Sup_fin id : finset.Sup_fin_mono finsupp.support_single_subset
  ... ≤ _ : by simp [finset.Sup_fin_singleton]

@[simp] lemma degree_X (h : 0 ≠ (1:α)) : degree (X : polynomial α) = 1 :=
le_antisymm
  degree_single
  (le_degree $ show (single (1:ℕ) (1:α) : ℕ →₀ α) 1 ≠ 0, begin simp [h.symm] end)

@[simp] lemma degree_C {a : α} : degree (C a) = 0 :=
nat.eq_zero_of_le_zero degree_single

lemma degree_add {f g : polynomial α} : degree (f + g) ≤ max (degree f) (degree g) :=
calc degree (f + g) ≤ (f.support ∪ g.support).Sup_fin id : finset.Sup_fin_mono finsupp.support_add
  ... = max (degree f) (degree g) : finset.Sup_fin_union

lemma degree_sum {β : Type w} {s : finset β} {f : β → polynomial α} :
  degree (s.sum f) ≤ s.Sup_fin (λi, degree (f i)) :=
finset.induction_on s (by simp; refl) $
  assume b s hbs ih,
  calc degree ((insert b s).sum f) = degree (f b + s.sum f) : by simp [hbs]
    ... ≤ degree (f b) ⊔ degree (s.sum f) : degree_add
    ... ≤ degree (f b) ⊔ s.Sup_fin (λi, degree (f i)) : sup_le_sup (le_refl _) ih
    ... = (insert b s).Sup_fin (λi, degree (f i)) : by simp

lemma degree_mul {f g : polynomial α} : degree (f * g) ≤ degree f + degree g :=
calc degree (f * g) ≤ _ : degree_sum
  ... ≤ _ : finset.Sup_fin_mono_fun $ assume a ha, degree_sum
  ... ≤ _ : finset.Sup_fin_le $ assume b₁ hb₁, finset.Sup_fin_le $ assume b₂ hb₂,
    calc _ ≤ b₁ + b₂ : degree_single
      ... ≤ degree f + degree g : add_le_add (finset.le_Sup_fin hb₁) (finset.le_Sup_fin hb₂)

lemma ne_zero_of_degree_ne_zero {f : polynomial α} : degree f ≠ 0 → f ≠ 0 :=--I want to apply normal by_cpntradiction here, but I don't know how to apply that, due to ambiguous overload.
begin intro, apply (@classical.by_contradiction (f ≠ 0) _), intro,
have h3: (f = 0), from iff.elim_left not_not a_1,
have h4: degree f = 0, calc degree f = degree 0 : by rw [h3] ... = 0 : degree_zero,
apply a h4
 end -- Contradiction not needed



def root_of (a : polynomial α) (b : α) := polynomial.eval a b = 0




lemma C_mul_X {c : α} : C c * X = single 1 c :=
calc C c * X = single 0 c * single 1 1 : rfl
... = single (0 + 1) (c * 1) : single_mul_single
... = single 1 c : by simp

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


lemma eq_const_of_degree_eq_zero {p : polynomial α} : degree p = 0 → ∃c, p = C c :=
begin
  intro h,
  have h1 : support p = {0} ∨ support p = ∅,
  apply eq_singleton_or_eq_empty_of_sup_fin_eq_bot h,
  cases h1,
  {
    apply eq_single_of_support_eq_singleton,
    assumption
  },
  {
    have : p = 0,
    apply eq_zero_of_support_eq_empty,
    assumption,
    fapply exists.intro,
    apply (0 : α),
    simp * at *,

  }

end



lemma eq_zero_of_leading_coef_eq_zero {p : polynomial α} : leading_coeff p = 0 → p = 0 :=
begin
  intro h1,
  unfold leading_coeff at h1 ,
  by_cases h2 : (degree p = 0),
  {
    have h3: ∃c, p = C c,
    from eq_const_of_degree_eq_zero h2,
    have h4: p = C (some h3), 
    from some_spec h3,
    have h5: (some h3) = 0,
    rw [h2, h4] at h1,
    simp [C_apply] at h1,
    assumption,
    simp * at *
  },
  {
    have h3 : support p ≠ ∅,
      have h3a : p ≠ 0,
      from ne_zero_of_degree_ne_zero h2,
      simp * at *,
      have h3b: ¬p = 0 → ¬support p = ∅,
      apply iff.elim_right not_imp_not,
      exact iff.elim_right (eq_zero_iff_support_eq_empty p),
      exact classical.prop_decidable _,
      exact h3b h3a,
    have h4 : degree p ∈ support p,
    from Sup_fin_mem_of_id_nat h3,
    have h5 : p (degree p) ≠  0,
    rw ←mem_support_iff p,
    assumption,
    contradiction
  }
end

lemma leading_coef_zero_eq_zero : leading_coeff 0 = (0 : α):=
by simp [leading_coeff]

--Should we remove the sublemmas?
lemma leading_coef_eq_zero_iff_eq_zero {p : polynomial α} : leading_coeff p = 0 ↔ p = 0 :=
begin
  constructor,
  exact eq_zero_of_leading_coef_eq_zero,
  intro h,
  rw h,
  exact leading_coef_zero_eq_zero
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


 
lemma eq_zero_of_gt_degree : ∀{h : polynomial α}, ∀{x : ℕ}, x > degree h → h x = 0 :=
begin
  intros h x h1,
  by_contradiction h2,
  have h9: x ≤ degree h,
  from le_degree h2,
  have : ¬ x ≤ degree h,
  from not_le_of_gt h1,
  contradiction,
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



--Naming?
lemma mul_add_degree_eq_add_leading_coeff {f g : polynomial α} : (f * g) (degree f + degree g) = (leading_coeff f) * (leading_coeff g):=
begin
  --local lemma
  have add_lemma : ∀ {a b c d : ℕ}, a < c → a + b = c + d → b > d,-- should this be placed elsewhere?
    intros a b c d h1 h2,
    by_contradiction h3,
    have h4 : b ≤ d,
    from le_of_not_gt h3,
    have : a + b < c + d,
    calc a + b < c + b : add_lt_add_right h1 b
      ... ≤ c + d : add_le_add_left h4 c,
    have : a + b ≥ c + d,
    simp [h2],
    exact le_refl _,
    have : ¬ a + b < c + d,
    simp [*, not_lt_of_ge],
    contradiction,

  rw mul_def, --I think we need a congrunce rule for sum,congr for the finsupp sum
  simp,
  simp [single_apply], 
  have h_sum : sum f
      (λ (a₁ : ℕ) (b : α),
         sum g (λ (a₁_1 : ℕ) (b_1 : α), ite (a₁ + a₁_1 = degree f + degree g) (b * b_1) 0)) =
         sum f
      (λ (a₁ : ℕ) (b : α),
         sum g (λ (a₁_1 : ℕ) (b_1 : α), (ite (a₁ = degree f) (b) 0)*(ite (a₁_1 = degree g) (b_1) 0)    )),
  apply finsupp.sum_congr,
  simp,
  intros x h1,
  apply finsupp.sum_congr,
  simp,
  intros y h2,
  by_cases h3 : (x = degree f),
  {
    by_cases h4 : (y = degree g),
    {
      rw [h3, h4], 
      rw if_pos,
      simp
    },
    {
      rw h3,
      simp,
      rw if_neg,
      rw if_neg,
      simp,
      assumption,
      assumption,
    }
  },
  {
    by_cases h4 : (y = degree g),
    {
      rw h4,
      simp,
      rw if_neg,
      rw if_neg,
      simp,
      assumption,
      assumption,
    },
    {
      by_cases h5 : (x + y = degree f + degree g),
      {
        rw if_pos,
        rw if_neg,
        rw if_neg,
        by_cases h6 : (x < degree f),
        {
          have h7 : (y > degree g),
          from add_lemma h6 h5,
          have h8 : g y = 0,
            from eq_zero_of_gt_degree h7,
          simp *,
        },
        { 
          have h7 : ¬ x ≤ degree f,
            by_contradiction h7,
            have h8 : x = degree f ∨ x < degree f,
            from eq_or_lt_of_le h7,
            cases h8 ; contradiction,
          have h8 : x > degree f,
          from lt_of_not_ge h7,
          have h9 : f x = 0,
          from eq_zero_of_gt_degree h8,
          simp *
        },
        repeat {assumption},
      },
      {
        rw if_neg,
        rw if_neg,
        rw if_neg,
        simp,
        repeat {assumption}
      }
    }
  },
  rw h_sum,
  have h_sum_2:  sum f
      (λ (a₁ : ℕ) (b : α),
         sum g (λ (a₁_1 : ℕ) (b_1 : α), ite (a₁ = degree f) b 0 * ite (a₁_1 = degree g) b_1 0)) =
     sum f
      (λ (a₁ : ℕ) (b : α),
         ite (a₁ = degree f) b 0 * sum g (λ (a₁_1 : ℕ) (b_1 : α), ite (a₁_1 = degree g) b_1 0)),
  {
    apply finsupp.sum_congr,
    simp,
    intros x h1,
    exact eq.symm finset.mul_sum,
  },
  rw h_sum_2,
  have h_sum_3 : sum f
      (λ (a₁ : ℕ) (b : α),
         ite (a₁ = degree f) b 0 * sum g (λ (a₁_1 : ℕ) (b_1 : α), ite (a₁_1 = degree g) b_1 0)) =
      (sum f
      (λ (a₁ : ℕ) (b : α),
         ite (a₁ = degree f) b 0)) * sum g (λ (a₁_1 : ℕ) (b_1 : α), ite (a₁_1 = degree g) b_1 0),
    apply (eq.symm (@finsupp.sum_mul _ _ _ _ _ ( sum g (λ (a₁_1 : ℕ) (b_1 : α), ite (a₁_1 = degree g) b_1 0)) f (λ (a₁ : ℕ) (b : α), ite (a₁ = degree f) b 0))),
  rw h_sum_3, 
  have h_sum_g: sum g (λ (a₁_1 : ℕ) (b_1 : α), ite (a₁_1 = degree g) b_1 0) = if (degree g ∈ g.support) then g (degree g) else 0,
    apply finsupp.sum_ite,
    rw h_sum_g,
  have h_sum_f: sum f (λ (a₁_1 : ℕ) (b_1 : α), ite (a₁_1 = degree f) b_1 0) = if (degree f ∈ f.support) then f (degree f) else 0,
    apply finsupp.sum_ite,
    rw h_sum_f,
  by_cases h1 : (f = 0),
  {
    have h2 : support f = ∅,
    simp [h1],
    exact support_zero,
    have h3 : degree f ∉ support f,
    simp *,
    simp [*, if_neg, leading_coef_zero_eq_zero],
  },
  { 

    have h2 : support f ≠ ∅,
    from iff.elim_right not_imp_not (eq_zero_of_support_eq_empty _) h1,
    have h3: degree f ∈ support f,
    from Sup_fin_mem_of_id_nat h2,
    rw [if_pos],
    by_cases h4 : (g = 0),
    {
      have h5 : support g = ∅,
        simp [h4],
        exact support_zero,
        have h5 : degree g ∉ support g,
        simp *,
        simp [*, if_neg, leading_coef_zero_eq_zero],
    },
    {
      have h5 : support g ≠ ∅,
        from iff.elim_right not_imp_not (eq_zero_of_support_eq_empty _) h4,
        have h6: degree g ∈ support g,
        from Sup_fin_mem_of_id_nat h5,
        rw [if_pos],
        simp [leading_coeff],
        assumption,

    },
    assumption,  
  }

end


def derivative (p : polynomial α) : polynomial α :=
p.sum (λn a, match n with 0 := 0 | (n + 1) := single n (a * (n + 1)) end)

@[simp] lemma derivative_zero : derivative (0 : polynomial α) = 0 :=
finsupp.sum_zero_index

lemma derivative_single {n : ℕ} {a : α} :
  derivative (single n a) = @nat.cases_on (λn, polynomial α) n 0 (λn, single n (a * (n + 1))) :=
finsupp.sum_single_index $ match n with 0 := rfl | n + 1 := by simp [derivative]; refl end

@[simp] lemma derivative_single_zero {a : α} : derivative (single 0 a) = 0 :=
derivative_single

@[simp] lemma derivative_single_one {n : ℕ} {a : α} :
  derivative (single (n + 1) a) = single n (a * (n + 1)) :=
derivative_single

@[simp] lemma derivative_C {a : α} : derivative (C a) = 0 :=
by simp [C]; refl

@[simp] lemma derivative_one : derivative (1 : polynomial α) = 0 :=
derivative_C

@[simp] lemma derivative_X : derivative (X : polynomial α) = 1 :=
by simp [X]; refl

@[simp] lemma derivative_add {f g : polynomial α} :
  derivative (f + g) = derivative f + derivative g :=
finsupp.sum_add_index
  (assume n, match n with 0 := by simp [derivative] | n + 1 := by simp [derivative]; refl end)
  (assume n, match n with 0 := by simp [derivative] | n + 1 := by simp [derivative, add_mul] end)

@[simp] lemma derivative_sum {β : Type w} {s : finset β} {f : β → polynomial α} :
  derivative (s.sum f) = s.sum (λb, derivative (f b)) :=
begin
  apply (finset.sum_hom derivative _ _).symm,
  exact derivative_zero,
  exact assume x y, derivative_add
end



lemma C_mul_C {a b : α} : C (a * b) = C a * C b :=
by simp [C, single_mul_single]




end semiring




section comm_semiring
variable [comm_semiring α]

instance : comm_semiring (polynomial α) := finsupp.to_comm_semiring


lemma mul_C_eq_sum {f : polynomial α} {a : α} :
  f * C a = f.sum (λi c, single i (a * c)) :=
calc f * C a = (f.sum single) * C a : by rw [sum_single]
  ... = f.sum (λi c, single i c * C a) : finset.sum_mul
  ... = f.sum (λi c, single i (a * c)) :
    by simp [single_eq_X_pow, C_mul_C, mul_assoc, mul_comm, mul_left_comm]

lemma mul_X_eq_sum {f : polynomial α} :
  f * X = f.sum (λi c, single (i + 1) c) :=
calc f * X = (f.sum single) * X : by rw [sum_single]
  ... = f.sum (λi c, single i c * X) : finset.sum_mul
  ... = f.sum (λi c, single (i + 1) c) :
    by simp [single_eq_X_pow, pow_add, pow_one, mul_assoc, mul_comm, mul_left_comm]

lemma derivative_mul_C {f : polynomial α} :
  derivative (f * C a) = derivative f * C a :=
have ∀i c, derivative (single i (a * c)) = derivative (single i c) * C a,
  by intros i c; cases i; simp [C, single_mul_single, mul_comm, mul_left_comm, mul_assoc],
calc derivative (f * C a) = derivative (f.sum (λi c, single i (a * c))) :
    by rw [mul_C_eq_sum]
  ... = f.sum (λi c, derivative (single i (a * c))) : derivative_sum
  ... = f.sum (λi c, derivative (single i c) * C a) : by simp [this]
  ... = f.sum (λi c, derivative (single i c)) * C a : finset.sum_mul.symm
  ... = derivative (f.sum single) * C a : by simp [finsupp.sum, derivative_sum]
  ... = _ : by rw [sum_single]

lemma derivative_C_mul {f : polynomial α} : 
  derivative (C a * f) = C a * (derivative f) :=
   by rw [mul_comm,derivative_mul_C,mul_comm]
 


lemma derivative_mul_X {f : polynomial α} :
  derivative (f * X) = derivative f * X + f:=
  have temp: derivative f * X = f.sum (λi c, single i (c * i)), from
have ∀ a (b : α ),(  finsupp.sum (derivative._match_1 b a) (λ (i : ℕ), single (i + 1)) = single a (b * a) ),from
begin
  intros,
  cases a,
  { simp [derivative._match_1], apply sum_zero_index },
  { simp [derivative._match_1], simp [sum_single_index] }
end,
have (λ (a : ℕ) (b : α ),(  finsupp.sum (derivative._match_1 b a) (λ (i : ℕ), single (i + 1)) ) ) = (λ (a : ℕ) (b : α ),  single a (b * a) ), from
(funext(λ _, funext $ this _)),
calc (derivative f) * X = sum (derivative f) (λi c, single (i + 1) c) : by rw [mul_X_eq_sum]
  ... = sum (sum f (λ (n : ℕ) (a : α), derivative._match_1 a n)) (λ (i : ℕ), single (i + 1)) : by rw [derivative]
  ... = sum f (λa b, sum ((λ n d, derivative._match_1 d n) a b) (λ i, single (i + 1))  ) :  begin rw [sum_sum_index  ], {intro, apply single_zero}, {intros, apply (@single_add _ _ _ _ _ _)}  end
  ... = sum f (λa b, sum (derivative._match_1 b a) (λ i, single (i + 1))) : rfl
  ... = f.sum (λi c, single i (c * i)) : begin rw [this] end,


calc derivative (f * X) = derivative (f.sum (λi c, single (i + 1) c)) :
    by rw [mul_X_eq_sum]
  ... = f.sum (λi c, derivative (single (i + 1) c)) :
    derivative_sum
  ... = f.sum (λi c, single i (c * (i + 1))) :
    by simp [derivative_single, (nat.succ_eq_add_one _).symm]
  ... = f.sum (λi c, single i (c * i) + single i c) : by simp [single_add, mul_add]
  ... = f.sum (λi c, single i (c * i)) + f: by simp [sum_add, sum_single]
  ... = derivative f * X + f : by rw [temp]




lemma derivative_mul {f : polynomial α} :
  ∀{g}, derivative (f * g) = derivative f * g + f * derivative g :=
begin
  apply f.induction_on,
  { simp [derivative_mul_C, mul_assoc, mul_comm, mul_left_comm] },
  { simp [derivative_mul_X, mul_assoc, mul_comm, mul_left_comm] },
  { simp [add_mul, mul_add] {contextual := tt} },
  { simp [add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm] {contextual := tt} }
end

open finset


lemma derivative_prod {β : Type w} {s : finset β} {f : β → polynomial α} :
  derivative (s.prod f) = s.sum (λb, derivative (f b) * (erase s b).prod f) :=
begin
  apply finset.induction_on s,
  { simp },
  { intros a s has ih,
    have : ∀b∈s, ((insert a s).erase b).prod f = f a * (s.erase b).prod f,
    begin
      assume b hb,
      have : a ≠ b, { assume h, simp * at * },
      rw [erase_insert_eq_insert_erase, finset.prod_insert]; simp *
    end,
    have : s.sum (λb, derivative (f b) * (erase (insert a s) b).prod f) =
      f a * s.sum (λb, derivative (f b) * (erase s b).prod f),
    from calc s.sum (λb, derivative (f b) * (erase (insert a s) b).prod f) =
      s.sum (λb, f a * (derivative (f b) * (s.erase b).prod f)) :
        sum_congr rfl $ by simp [this, mul_assoc, mul_comm, mul_left_comm] {contextual := tt}
      ... = f a * s.sum (λb, derivative (f b) * (erase s b).prod f) :
        by rw [mul_sum],
    simp [ih, has, finset.prod_insert, derivative_mul, sum_insert, erase_insert, this] }
end

lemma derivative_pow {n : ℕ} {p : polynomial α}:
   derivative (p^n) = ite (n = 0) 0 (n*p^(n-1)*derivative p) :=
begin
  induction n with n h,
  {simp},
  {
    simp,
    have : ¬ nat.succ n = 0, from nat.succ_ne_zero _,  
    simp [if_neg, *], 
    rw [pow_succ'],
    simp [derivative_mul],
    rw [h],
    cases n,
    simp,
    have : ¬ nat.succ n = 0, from nat.succ_ne_zero _,  
    simp [if_neg, *],
    rw [pow_succ'],
    exact calc p ^ n * p * derivative p + (1 + ↑n) * p ^ n * derivative p * p = 
    1 * p ^ n * p * derivative p + (1 + ↑n) * p ^ n * derivative p * p : by simp
    ... = 1 * p ^ n * p * derivative p + (1 + ↑n) * p ^ n * (derivative p * p) : by simp [mul_assoc]
    ... = 1 * p ^ n * p * derivative p + (1 + ↑n) * p ^ n * (p * derivative p) : by simp [mul_comm]
    ... = 1 * p ^ n * p * derivative p + (1 + ↑n) * p ^ n * p * derivative p   : by simp [mul_assoc]
    ... = 1 * (p ^ n * p * derivative p) + (1 + ↑n) * (p ^ n * p * derivative p)   : by simp [mul_assoc]
    ... = (1 + (1 + ↑n)) * (p ^ n * p * derivative p): by rw [←( add_mul 1 (1 + ↑n) (p ^ n * p * derivative p))]
    ... = (1 + (1 + ↑n)) * (p ^ n * p) * derivative p : by simp [mul_assoc]
  }

end

--Naming correct or dvd_sum_of_forall_mem_dvd
lemma dvd_sum {β : Type w}{p : polynomial α}{s : finset β}{f : β → polynomial α} :--should be placed in finset.
   (∀ x ∈ s, p ∣ f x) → p ∣ (s.sum f) :=
begin
  apply finset.induction_on s,
  {simp},
  {
    intros a s h1 h2 h3,
    simp [finset.sum_insert h1],
    have htmp: (∀ (x : β), x ∈ s → p ∣ f x),
    {
      intros y h4,
      have : y ∈ insert a s, 
      rw [finset.mem_insert],
      simp [h4],
      exact h3 y this,
    },
    have ha_mem : a ∈ insert a s,
    rw [finset.mem_insert],
    simp,
    have ha: p ∣ f a,
    exact h3 a ha_mem,
    have hsum: p ∣ sum s f,
    exact h2 htmp,
    simp [dvd_add ha hsum]
  }
end

lemma dvd_prod_of_dvd_mem {β : Type w}{p : polynomial α}{s : finset β}{x : β}{h_mem :  x ∈ s}{f : β → polynomial α}{h_div : p ∣ f x} :
p∣ s.prod f :=
begin
  have : insert x (erase s x) = s,
  exact insert_erase h_mem,
  rw ←this,
  rw finset.prod_insert,
  apply dvd_mul_of_dvd_left h_div (finset.prod (erase s x) f),
  simp
end


lemma dvd_pow_sub_one_pow --naming correct?/
{p : polynomial α} {n : ℕ} : monoid.pow p (n - 1) ∣ (monoid.pow p n) :=
begin
  cases n,
  simp,
  rw nat.succ_sub_one,
  refine  dvd_of_mul_left_eq p _,
  exact rfl,
end


end comm_semiring

section ring
variable [ring α]

@[priority 1100] instance : ring (polynomial α) := finsupp.to_ring
@[priority 1100] instance : add_comm_group (polynomial α) := by apply_instance

lemma neg_apply_poly (a : polynomial α) (n : ℕ):  (- a) n = - (a n) :=
begin intros, simp [coe_fn], simp [has_coe_to_fun.coe], simp [has_neg.neg, add_group.neg, add_comm_group.neg, ring.neg] , apply rfl
end


lemma degree_neg {f : polynomial α} : degree (-f) = degree f:=
by simp [degree]

lemma degree_sub {f g : polynomial α} : degree (f - g) ≤ max (degree f) (degree g) :=
calc degree (f - g) = degree (f  + (- g)) : by simp
     ... ≤ max (degree f) (degree (-g)) : degree_add
     ...= max (degree f) (degree g) : by rw (@degree_neg _ _ g)

end ring

section comm_ring
variable [comm_ring α]

instance : comm_ring (polynomial α) := finsupp.to_comm_ring
end comm_ring

section integral_domain
variable [integral_domain α]
lemma zero_ne_one : (0:polynomial α) ≠ 1:=
begin
  intro h,
  have : (0 : polynomial α) 0 = (1 : polynomial α) 0, by rw [h],
  simp * at *
end

instance {α : Type u} [integral_domain α] : zero_ne_one_class (polynomial α):=
{ zero_ne_one := zero_ne_one, .. polynomial.comm_ring }

/-
lemma eq_zero_or_eq_zero_of_mul_eq_zero_tmp {a b : α} (h : a * b = 0) : a = 0 ∨ b = 0 :=
begin
  by_contradiction h,
  rw decidable.not_or_iff_and_not at h,
  have ha : a ≠ 0, 
  simp [h],

end
-/

lemma eq_zero_or_eq_zero_of_mul_eq_zero : ∀ f g : polynomial α, f * g = 0 → f = 0 ∨ g = 0 :=
begin
  intros f g h1,
  by_contradiction h2,
  rw not_or_distrib at h2,
  have h3 : f ≠ 0,
  simp [h2],
  have h4 : g ≠ 0,
  simp [h2],
  have h5 : leading_coeff f ≠ 0,
  simp [*, leading_coef_eq_zero_iff_eq_zero],
  have h6 : leading_coeff g ≠ 0,
  simp [*, leading_coef_eq_zero_iff_eq_zero],
  have h7 : (leading_coeff f) * (leading_coeff g) ≠ 0,
    by_contradiction h8,
    rw not_not at h8,
    have h9 : leading_coeff f = 0 ∨  leading_coeff g = 0,
    from eq_zero_or_eq_zero_of_mul_eq_zero h8,
    cases h9,
    contradiction,
    contradiction,
  have h8 : (f * g) (degree f + degree g) ≠ 0,
  calc  (f * g) (degree f + degree g) = (leading_coeff f) * (leading_coeff g) : mul_add_degree_eq_add_leading_coeff
      ... ≠ 0 : h7,
  rw h1 at h8,
  simp [zero_apply] at h8,
  contradiction
end

instance {α : Type u} [integral_domain α] : no_zero_divisors (polynomial α):=
{eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero

.. polynomial.comm_ring}


instance {α : Type u} [integral_domain α]: integral_domain (polynomial α) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero,
  .. polynomial.comm_ring, .. polynomial.zero_ne_one_class }


lemma mul_eq_zero_iff_mul_leading_coef_eq_zero {f g : polynomial α} : f * g = 0 ↔ (leading_coeff f) * (leading_coeff g) = 0 :=
begin
  constructor,
  { 
    intro h1,
    rw ←mul_add_degree_eq_add_leading_coeff,
    rw h1,
    simp,
  },
  {
    intro h1,
    have h2 : leading_coeff f = 0 ∨ leading_coeff g = 0,
    from _root_.eq_zero_or_eq_zero_of_mul_eq_zero  h1,
    cases h2,
    repeat {
      rw leading_coef_eq_zero_iff_eq_zero at h2,
      simp [h2],      
    }
  }

end

lemma degree_mul_integral_domain {f g : polynomial α} : f * g ≠ 0 → degree (f * g) = degree f + degree g :=
begin

  intro h1, 
  have h2 : f ≠ 0,
  from ne_zero_of_mul_ne_zero_right h1,
  have h3 : g ≠ 0,
  from ne_zero_of_mul_ne_zero_left h1,
  have h4 : (f * g) (degree f + degree g) ≠ 0,
  calc (f * g) (degree f + degree g) = (leading_coeff f) * (leading_coeff g) : mul_add_degree_eq_add_leading_coeff
     ... ≠ 0 : by {simp,rw [←not_iff_not_of_iff mul_eq_zero_iff_mul_leading_coef_eq_zero], exact h1},
  have h5 : (degree f + degree g) ≤ degree (f * g),
  from le_degree h4,
  have h6 : degree (f * g) ≤ (degree f + degree g),
  from degree_mul,
  apply le_antisymm; simp * at *

end

end integral_domain

section field
variable [field α]


--naming!?
lemma division_with_remainder_polynomials {f g : polynomial α} : g ≠ 0 → (∃ q r : polynomial α,( (f = q * g + r) ∧ ((r = 0)  ∨  ( (degree r ) < (degree g)) )  ) ) :=
begin
  by_cases h1 : (f = 0),
  {
    intro h2,
    rw h1,
    fapply exists.intro,
    apply (0 : polynomial α),
    fapply exists.intro,
    apply (0 : polynomial α),
    simp
  },
  {
    intro h2,
    let n := degree f,
    induction h_n : n,
    {
      let m := degree g,
      by_cases h3 : (n < m),
      {
        fapply exists.intro,
        apply (0: polynomial α),
        fapply exists.intro,
        apply (f),
        simp *
      },
      { --have defined the embedding of R in R[x]?
         let a' := f - (((leading_coeff f) * (leading_coeff g)⁻¹) :  α) * X ^ (n - m) * g,
         let a'' := ↑(((leading_coeff f) * (leading_coeff g)⁻¹) :  α) * X ^ (n - m) * g,
         have h3a : f * g ≠ 0, 
         from mul_ne_zero h1 h2,

         have h3b : (X ^ (n - m) : polynomial α) ≠ 0,
           rw X_pow_eq_single,
           by_contradiction h3b2,
           rw not_not at h3b2,
           have : n - m = n - m,
           trivial,
           have h3b3: (single (n - m) 1 : polynomial α) (n - m) = 1,
           calc (single (n - m) 1 : polynomial α) (n - m) = if ((n - m) = (n - m)) then 1 else 0 : single_apply
              ... = 1 : by rw [if_pos this],
           have h3b4: (single (n - m) 1 : polynomial α) (n - m) = 0,
           rw h3b2,
           exact @zero_apply _ _ (n - m),
           rw h3b4 at h3b3,
           have : (0 : α) ≠ 1,
           exact _root_.zero_ne_one,
           exact this h3b3,

         have h3c : (↑(((leading_coeff f) * (leading_coeff g)⁻¹) :  α) : polynomial α) ≠ 0,
           have h3a2: (leading_coeff f) ≠ 0,
           simp [h1, leading_coef_eq_zero_iff_eq_zero],
           have h3a3: (leading_coeff g) ≠ 0,
             simp [h1, leading_coef_eq_zero_iff_eq_zero],
             assumption,
           have h3a4: (leading_coeff g)⁻¹ ≠ 0,
           simp [h3a3, inv_ne_zero],
           simp,
           rw ←not_iff_not_of_iff eq_zero_iff_embed_eq_zero,
           exact mul_ne_zero h3a2 h3a4,

         have h3d : ↑(((leading_coeff f) * (leading_coeff g)⁻¹) :  α) * (X ^ (n - m) : polynomial α) ≠ 0,
         exact mul_ne_zero h3c h3b,
         have h3e : ↑(((leading_coeff f) * (leading_coeff g)⁻¹) :  α) * (X ^ (n - m) : polynomial α) * g ≠ 0,
         exact mul_ne_zero h3d h2,
         have h3f : degree (↑(((leading_coeff f) * (leading_coeff g)⁻¹)) * X ^ (n - m)) =
               ( @degree α _ ↑(((leading_coeff f) * (leading_coeff g)⁻¹)) + @degree α _ X ^ (n - m) ),
         rotate_left 1,

         },
         from  degree_mul_integral_domain h3d,
         have h4 : degree a'' = n,
         calc degree a'' = degree ( ↑(((leading_coeff f) * (leading_coeff g)⁻¹) :  α) * (X ^ (n - m) : polynomial α) * g ): rfl
            ... = degree (↑(((leading_coeff f) * (leading_coeff g)⁻¹) :  α) * X ^ (n - m)) + degree g : degree_mul_integral_domain h3e
            ... = ( degree ↑(((leading_coeff f) * (leading_coeff g)⁻¹) :  α) + degree X ^ (n - m) ) + degree g 
            :
            --... = ( @degree α _ ↑(((leading_coeff f) * (leading_coeff g)⁻¹) :  α) + degree X ^ (n - m) ) + degree g : _
            ... = _ : _,
         have h4 : degree a' < n,
         ---calc degree a' ≤ max f ((((leading_coeff f) * (leading_coeff g)⁻¹) :  α) * X ^ (n - m) * g)
         
      }
    },
    {

    }
  }
end

#check @X


--Still need to obtain an integral domain from field α 
instance {α : Type u} [field α] : euclidean_domain (polynomial α) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero,
  zero_ne_one := zero_ne_one, --correct?
  norm := degree,
  h1 := degree_zero,
  h_norm := sorry,
  .. polynomial.comm_ring }


end field
end polynomial
