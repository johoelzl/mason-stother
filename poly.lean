import  .Sup_fin data.finsupp order.lattice data.nat.cast .euclidean_domain unique_factorization_domain
import .to_finsupp .to_finset
universes u v w

noncomputable theory

open classical set function finsupp lattice

local attribute [instance] finsupp.to_comm_semiring
local attribute [instance] finsupp.to_semiring
local infix ^ := monoid.pow

-- TODO: for some reasons these rules don't work
@[simp] lemma nat_rec_zero {C : ℕ → Sort u} (h₁ : C 0) (h₂ : Π (n : ℕ), C n → C (nat.succ n)) :
  @nat.rec C h₁ h₂ 0 = h₁ := rfl

@[simp] lemma nat_rec_add_one {C : ℕ → Sort u} (h₁ : C 0) (h₂ : Π (n : ℕ), C n → C (nat.succ n)) {n : ℕ} :
  @nat.rec C h₁ h₂ (n + 1) = h₂ n (nat.rec h₁ h₂ n) := rfl

-- TODO: relax semiring to semi-algebra?
def polynomial (α : Type u) [semiring α] := ℕ →₀ α

--correct? should have an explicit argument
def characteristic_zero (α : Type u) [semiring α] : Prop :=  ∀ n : ℕ, n ≠ 0 → (↑n : α) ≠ 0

namespace polynomial
local attribute [instance] prop_decidable
variables {α : Type u} {a a' a₁ a₂ : α} --{n m : ℕ} --do we want n and m?

section semiring
variable [semiring α]

instance : has_coe_to_fun (polynomial α) := finsupp.has_coe_to_fun
instance : has_zero (polynomial α) := finsupp.has_zero
instance : has_one (polynomial α) := finsupp.has_one
instance : has_add (polynomial α) := finsupp.has_add
instance : has_mul (polynomial α) := finsupp.has_mul
instance : semiring (polynomial α) := finsupp.to_semiring

@[simp] lemma one_apply_zero : (1 : polynomial α) 0 = 1 := single_eq_same

@[simp] lemma zero_apply {n : ℕ} : (0 : polynomial α) n = 0 := zero_apply

def C (a : α) : polynomial α := finsupp.single 0 a

--embed R in R[x] --use has_lift, because has_coe is heavy on performance
instance : has_lift (α) (polynomial α) := ⟨C⟩ -- Is this embedding correct?

lemma embedding {a : α} : ↑a = C a := rfl --Where do we use this?

@[simp] lemma C_0 : C 0 = (0:polynomial α) := single_zero

@[simp] lemma C_1 : C 1 = (1:polynomial α) := rfl

lemma C_apply {c : α } {n : ℕ}: ((C c) : ℕ → α) n = (if 0 = n then c else 0) := rfl

lemma C_eq_zero_iff_eq_zero (c : α) : C c = 0 ↔ c = 0 :=
begin
  split,
  { intro h,
    have : ((C c) : ℕ → α) 0 = (0 : polynomial α) 0,
      { rw h},
    rw [C_apply, if_pos] at this,
    simp * },
  { intro h,
    simp * }
end

lemma C_add_C (a b : α) : C a + C b = C (a + b) :=
begin
  apply eq.symm,
  exact single_add,
end

def is_constant (p : polynomial α) : Prop := ∃ c : α, p = C c

@[simp] lemma is_constant_zero : is_constant (0 : polynomial α) :=  ⟨0, C_0.symm⟩

@[simp] lemma is_constant_C {c : α} : is_constant (C c) := ⟨c, rfl⟩

--naming?
lemma eq_zero_iff_embed_eq_zero {f : α} : f = 0 ↔ (↑f : polynomial α) = 0 :=
begin
  rw embedding,
  constructor, --Do we prefer constructor or split?
  {
    intro h,
    simp *,
  },
  {
    intro h,
    have : ((C f) : ℕ → α) 0 = f,
      {simp [C_apply]},
    rw h at this,
    simp * at *,
  }
end

def X : polynomial α := finsupp.single 1 1

lemma X_apply {n : ℕ}: ((X : polynomial α): ℕ → α) n = (if 1 = n then 1 else 0) :=  rfl

lemma single_eq_X_pow : ∀{n:ℕ}, single n a = C a * X ^ n
| 0       := by simp [C]
| (n + 1) :=
  calc single (n + 1) a = single n a * X : by simp [X, single_mul_single]
    ... = C a * X ^ (n + 1) : by rw [@single_eq_X_pow n]; simp [pow_add, pow_one, mul_assoc]

lemma X_pow_eq_single {n:ℕ} : (X ^ (n) : polynomial α) = single n 1 :=
begin
  calc (X ^ n : polynomial α) = C 1 * X ^ n : by simp [C_apply]
  ... = single n 1 : eq.symm single_eq_X_pow,
end

lemma X_pow_apply {n m : ℕ} : ((X  ^ n : polynomial α): ℕ → α) m = (if n = m then 1 else 0) :=
by rw [X_pow_eq_single, single_apply]

--naming?
lemma sum_const_mul_pow_X  {f : polynomial α} : finsupp.sum f (λ n a, C a * X ^ n) = f :=
begin
  have h1: f.sum single = f,
    from sum_single,
  simp [finsupp.sum] at h1,
  have h2 : finset.sum (support f) (λ (a : ℕ), single a (f a)) =  sum f (λ (n : ℕ) (a : α), C a * X ^ n),
    {
    apply finset.sum_congr (eq.refl f.support),
    intros x h2,
    apply single_eq_X_pow
    },
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

lemma leading_coeff_def {p : polynomial α } : leading_coeff p = p (degree p) := rfl

--Can you add the simp attribute to a definition?
def monic (p : polynomial α):= leading_coeff p = 1

--Does this work? No leads to deep recursion??
--@[simp] lemma monic_def {f : polynomial α} {h : monic f} : leading_coeff f = 1 := h --Should we make monic reducible instead?

lemma ext : ∀{f g : polynomial α}, (∀a, f a = g a) → f = g:= @finsupp.ext _ _ _

lemma exists_coeff_ne_zero_of_ne_zero {f : polynomial α}: f ≠ 0 → ∃m, f m ≠ 0:=
assume h,
  have ¬(∀k, f k = (0 : polynomial α) k),
    from (iff.elim_right not_imp_not ext) h,
  classical.not_forall.1 this

lemma le_degree {p : polynomial α} {n : ℕ} (h : p n ≠ 0) : n ≤ degree p :=
show id n ≤ degree p, from finset.le_Sup_fin (by simp [h])

lemma le_degree_of_mem_support {p : polynomial α} {n : ℕ} : n ∈ support p → n ≤ degree p :=
begin
  intro h1,
  apply le_degree,
  rwa [mem_support_iff] at h1,
end

@[simp] lemma degree_zero : degree (0 : polynomial α) = 0 :=
have (0 : polynomial α).support = ∅, from support_zero,
by simp [degree, this]; refl

--naming?
lemma degree_single {a : α} {n : ℕ} : degree (single n a) ≤ n :=
calc degree (single n a) = (single n a).support.Sup_fin id : by simp [degree]
  ... ≤ (finset.singleton n).Sup_fin id : finset.Sup_fin_mono finsupp.support_single_subset
  ... ≤ _ : by simp [finset.Sup_fin_singleton]


lemma degree_single_eq {a : α} (n : ℕ): degree ((single n a) : polynomial α) = (if a = 0 then (0 : ℕ) else n) :=
begin
  by_cases h : a = 0,
  {
    simp [h],
    apply degree_zero, --Why didn't the simplifier do this?
  },
  {
    simp [if_neg, *],
    apply le_antisymm (degree_single),
    {
      apply le_degree, --Why can't I give this to the simplifier?
      simpa,
    }
  }
end

@[simp] lemma degree_X (h : 0 ≠ (1:α)) : degree (X : polynomial α) = 1 :=
by rwa [X, degree_single_eq, if_neg h.symm]

lemma degree_X_eq_zero_of_zero_eq_one (h : 0 = (1:α)) : degree (X : polynomial α) = 0 :=
by rwa [X, degree_single_eq, if_pos h.symm]

--correct simp?
@[simp] lemma degree_X_pow (h : 0 ≠ (1:α)) {n : ℕ} : degree ((X : polynomial α) ^ n) = n :=
by rw [X_pow_eq_single, degree_single_eq, if_neg h.symm]

@[simp] lemma degree_C {a : α} : degree (C a) = 0 :=
nat.eq_zero_of_le_zero degree_single

@[simp] lemma degree_one : degree (1: polynomial α)  = 0 := degree_C

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

lemma ne_zero_of_degree_ne_zero {f : polynomial α} : degree f ≠ 0 → f ≠ 0 :=
begin
  intros h1 h2,
  simp * at *,
end

--application lemmas --correct?
@[simp] lemma add_apply {g₁ g₂ : polynomial α} {a : ℕ} :
  (g₁ + g₂) a = g₁ a + g₂ a := finsupp.add_apply

/-leading coef lemmas-/

@[simp] lemma leading_coeff_single {a : α} {n : ℕ} : leading_coeff (single n a) = a :=
begin
  rw [leading_coeff, degree_single_eq],
  by_cases h1 : a = 0 ; simp [*, single_apply]
end

@[simp] lemma leading_coeff_C {a : α} : leading_coeff (C a) = a :=
by simp [leading_coeff_def, degree_C, C_apply]

@[simp] lemma leading_coeff_zero : leading_coeff (0 : polynomial α) = 0 := rfl

@[simp] lemma leading_coeff_one : leading_coeff (1 : polynomial α) = 1 := leading_coeff_C

@[simp] lemma leading_coeff_X : leading_coeff (X : polynomial α) = 1 :=
by rw [X, leading_coeff_single]

--Are we using the interference here correctly? --Correct simp?
lemma not_monic_zero (h : (0 : α) ≠ 1) : ¬monic (0 : polynomial α) :=
by simpa [monic]

lemma ne_zero_of_monic (h0 : (0 : α) ≠ 1) (p : polynomial α) (h : monic p) : p ≠ 0 :=
begin
  intro h1,
  subst h1,
  exact not_monic_zero h0 h,
end

lemma monic_X : monic (X : polynomial α) :=
by rw [monic, leading_coeff_X]

@[simp] lemma monic_one : monic (1 : polynomial α) := leading_coeff_one

lemma leading_coeff_X_pow {n : ℕ} : leading_coeff ((X ^ n) : polynomial α) = (1 : α) :=
by  rw [X_pow_eq_single, leading_coeff_single]

lemma monic_X_pow {n : ℕ }: monic ((X ^ n) : polynomial α) :=
by rw [monic, leading_coeff_X_pow]

def root_of (a : polynomial α) (b : α) := polynomial.eval a b = 0

lemma C_mul_X {c : α} : C c * X = single 1 c :=
calc C c * X = single 0 c * single 1 1 : rfl
... = single (0 + 1) (c * 1) : single_mul_single
... = single 1 c : by simp

--Should we remove the implication lemmas? and only keep the IFF?
lemma is_constant_of_degree_eq_zero {p : polynomial α} : degree p = 0 → is_constant p :=
begin
  intro h,
  have h1 : support p = {0} ∨ support p = ∅,
    from eq_singleton_or_eq_empty_of_sup_fin_eq_bot h,
  cases h1,
  {
    exact eq_single_of_support_eq_singleton _ h1,
  },
  {
    have : p = 0,
    {
      exact eq_zero_of_support_eq_empty _ h1,
    },
    exact ⟨0, by simp * at *⟩,
  }
end

lemma is_constant_iff_degree_eq_zero {p : polynomial α} : is_constant p ↔ degree p = 0 :=
begin
  constructor,
  {
    intro h1,
    rcases h1 with ⟨c, h2⟩,
    simp *,
  },
  {
    exact is_constant_of_degree_eq_zero
  }
end

lemma eq_zero_of_leading_coef_eq_zero {p : polynomial α} : leading_coeff p = 0 → p = 0 :=
begin
  intro h1,
  by_cases h2 : (degree p = 0),
  {
    rw ←is_constant_iff_degree_eq_zero at h2,
    rcases h2 with ⟨c, h3⟩,
    subst h3,
    simp [*, C_apply] at *,
  },
  {
  have h3 : support p ≠ ∅,
    {
      have h3a : p ≠ 0,
        from ne_zero_of_degree_ne_zero h2,
      rwa [ne.def, ←eq_zero_iff_support_eq_empty p],
    },
    have h4 : degree p ∈ support p,
      from Sup_fin_mem_of_id_nat h3,
    have h5 : p (degree p) ≠  0,
      {rwa ←mem_support_iff p},
    contradiction
  }
end

@[simp] lemma leading_coef_zero_eq_zero : leading_coeff 0 = (0 : α):=
by simp [leading_coeff]

--Should we remove the sublemmas?
lemma leading_coef_eq_zero_iff_eq_zero {p : polynomial α} : leading_coeff p = 0 ↔ p = 0 :=
iff.intro eq_zero_of_leading_coef_eq_zero (by simp {contextual := tt})


--lt maybe better?
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

private lemma add_lemma {a b c d : ℕ} : a < c → a + b = c + d → b > d :=
begin
    intros h1 h2,
    by_contradiction h3,
    have h4 : b ≤ d,
      from le_of_not_gt h3,
    have : a + b < c + d,
    {
      calc a + b < c + b : add_lt_add_right h1 b
      ... ≤ c + d : add_le_add_left h4 c,
    },
    have : a + b ≥ c + d,
    {
      simp [h2],
      exact le_refl _,
    },
    have : ¬ a + b < c + d,
      {simp [*, not_lt_of_ge]},
    contradiction
end

private lemma h_sum (f g : polynomial α) :
sum f (λ (n : ℕ) (b : α), sum g (λ (m : ℕ) (c : α), ite (n + m = degree f + degree g) (b * c) 0)) =
sum f (λ (n : ℕ) (b : α), sum g (λ (m : ℕ) (c : α), (ite (n = degree f) b 0) * (ite (m = degree g) c 0))) :=
begin
  apply finsupp.sum_congr (eq.refl (support f)),
  intros n h1,
  apply finsupp.sum_congr (eq.refl (support g)),
  intros m h2,

  by_cases h5 : (n + m = degree f + degree g),
  {
    by_cases h3 : (n = degree f),
    {
      subst h3,
      have h4 : m = degree g,
        from nat.add_left_cancel h5,
      simp *,
    },
    {
      have h6 : n ≤ degree f,
        from le_degree_of_mem_support h1,
      have h8 : n < degree f,
        from nat.lt_of_le_and_ne h6 h3,
      have h7 : (m > degree g),
        from add_lemma h8 h5,
      have h8 : g m = 0,
        from eq_zero_of_gt_degree h7,
      simp *,
    },
  },
  {
    have h5 : ¬ ((n = degree f) ∧ (m = degree g)),
    {
      by_contradiction h6,
      simp * at *,
    },
    rw not_and_distrib at h5,
    cases h5 ; simp *,
  }
end

private lemma h_sum_2 (f g : polynomial α) :
sum f (λ (n : ℕ) (b : α), sum g (λ (m : ℕ) (c : α), ite (n = degree f) b 0 * ite (m = degree g) c 0)) =
sum f (λ (n : ℕ) (b : α), ite (n = degree f) b 0 * sum g (λ (m : ℕ) (c : α), ite (m = degree g) c 0)):=
finsupp.sum_congr (eq.refl f.support) (assume x h1, eq.symm finset.mul_sum)

private lemma h_sum_3 (f g : polynomial α) :
sum f (λ (n : ℕ) (b : α), ite (n = degree f) b 0 * sum g (λ (m : ℕ) (c : α), ite (m = degree g) c 0)) =
(sum f (λ (n : ℕ) (b : α), ite (n = degree f) b 0)) * sum g (λ (m : ℕ) (c : α), ite (m = degree g) c 0):=
eq.symm finsupp.sum_mul

private lemma h_sum_g (f g : polynomial α):
sum g (λ (m : ℕ) (c : α), ite (m = degree g) c 0) = if (degree g ∈ g.support) then g (degree g) else 0 :=
finsupp.sum_ite


private lemma h_sum_f (f g : polynomial α): sum f (λ (m : ℕ) (c : α), ite (m = degree f) c 0) = if (degree f ∈ f.support) then f (degree f) else 0 :=
finsupp.sum_ite

lemma degree_mem_support_of_ne_zero {p : polynomial α} (h1 : p ≠ 0) : degree p ∈ support p :=
begin
  apply Sup_fin_mem_of_id_nat,
  simp,
  rw ←eq_zero_iff_support_eq_empty,
  exact h1
end

lemma mul_degree_add_degree_eq_leading_coeff_mul_leading_coeff {f g : polynomial α} : (f * g) (degree f + degree g) = (leading_coeff f) * (leading_coeff g):=
begin
  rw mul_def,
  simp [single_apply],
  rw [h_sum, h_sum_2, h_sum_3,h_sum_g f g, h_sum_f f g],
  by_cases h1 : (f = 0),
  {
    subst h1,
    simp *,
  },
  {
    rw [if_pos (degree_mem_support_of_ne_zero h1)],
    by_cases h4 : (g = 0),
    {
      subst h4,
      simp *,
    },
    {
      rw [if_pos (degree_mem_support_of_ne_zero h4)],
      exact rfl,
    },
  }
end

lemma degree_mul_eq_degree_add_degree_of_leading_coeff_mul_leading_coeff_ne_zero
{f g : polynomial α} (h : leading_coeff f * leading_coeff g ≠ 0) : degree (f * g) = degree f + degree g :=
begin
  have h4: (f * g) (degree f + degree g) ≠  0,
  {
    calc (f * g) (degree f + degree g) = leading_coeff f * leading_coeff g : mul_degree_add_degree_eq_leading_coeff_mul_leading_coeff
    ... ≠ 0 : h,
  },
  have h5 : degree f + degree g ≤ degree (f * g),
    from le_degree h4,
  have h6: degree (f * g) ≤ degree f + degree g,
    from degree_mul,
  exact le_antisymm h6 h5
end

lemma degree_monic_mul {f g : polynomial α}(h1 : monic f) (h2 : (0 : α) ≠ 1)(h3 : g ≠ 0): degree (f * g) = degree f + degree g :=
begin
  have h3 : leading_coeff f * leading_coeff g ≠ 0,
  {
    rw [ne.def, ←leading_coef_eq_zero_iff_eq_zero] at h3,
    simp [monic, *] at *,
  },
  exact degree_mul_eq_degree_add_degree_of_leading_coeff_mul_leading_coeff_ne_zero h3,
end

--naming?
lemma leading_coeff_monic_mul{f g: polynomial α} {h1 : monic f} (h2 : (0 : α) ≠ 1): leading_coeff (f * g) = leading_coeff g :=
begin
  by_cases h3 : (g = 0),
  {
   simp *,
  },
  {
    have h4 : degree (f * g) = degree f + degree g,
      from degree_monic_mul h1 h2 h3,
    rw [leading_coeff, h4, mul_degree_add_degree_eq_leading_coeff_mul_leading_coeff],
    simp [monic, *] at *,
  }
end




--naming incorrect?
lemma C_mul_C {a b : α} : C (a * b) = C a * C b :=
by simp [C, single_mul_single]

end semiring


section comm_semiring
variable [comm_semiring α]

instance : comm_semiring (polynomial α) := finsupp.to_comm_semiring

lemma C_prod_eq_map_C_prod {f : multiset α} : C (f.prod) = (f.map C).prod :=
begin
  fapply multiset.induction_on f,
  {
    simp
  },
  {
    intros a s h1,
    simp [C_mul_C, *]
  }
end

lemma mul_C_eq_sum {f : polynomial α} {a : α} : f * C a = f.sum (λi c, single i (a * c)) :=
calc f * C a = (f.sum single) * C a : by rw [sum_single]
  ... = f.sum (λi c, single i c * C a) : finset.sum_mul
  ... = f.sum (λi c, single i (a * c)) :
    by simp [single_eq_X_pow, C_mul_C, mul_assoc, mul_comm, mul_left_comm]

lemma mul_X_eq_sum {f : polynomial α} : f * X = f.sum (λi c, single (i + 1) c) :=
calc f * X = (f.sum single) * X : by rw [sum_single]
  ... = f.sum (λi c, single i c * X) : finset.sum_mul
  ... = f.sum (λi c, single (i + 1) c) :
    by simp [single_eq_X_pow, pow_add, pow_one, mul_assoc, mul_comm, mul_left_comm]

lemma degree_le {p : polynomial α} {n : ℕ} (h : ∀ m > n, p m = 0) : degree p ≤ n :=
begin
  by_cases h1 : (p = 0),
  {
    simp [*, nat.zero_le]
  },
  {
    have h2 : degree p ∈ support p,
      from degree_mem_support_of_ne_zero h1,
    rw [mem_support_iff] at h2,
    by_contradiction h3,
    have h4 : degree p > n,
      from lt_of_not_ge h3,
    have : p (degree p) = 0,
      from h _ h4,
    contradiction,
  }
end

open finset

--Are these used in MS 2? That is more general using multisets.
--Where to place this?
lemma dvd_sum_of_forall_mem_dvd [comm_semiring α] {β : Type u} {p : α} {s : finset β} {f : β → α} :
   (∀ x ∈ s, p ∣ f x) → p ∣ (s.sum f) :=
begin
  apply finset.induction_on s,
  {simp},
  {
    intros a s h1 h2 h3,
    have htmp: (∀ (x : β), x ∈ s → p ∣ f x),
    {
      intros y h4,
      have : y ∈ insert a s,
      {
        simp [finset.mem_insert, h4],
      },
      exact h3 y this,
    },
    have ha_mem : a ∈ insert a s,
    {
      simp [finset.mem_insert],
    },
    have ha: p ∣ f a,
      from h3 a ha_mem,
    have hsum: p ∣ sum s f,
      from h2 htmp,
    simp [finset.sum_insert h1, dvd_add ha hsum],
  }
end

--Is this used?
lemma dvd_prod_of_dvd_mem {β : Type w} {p : polynomial α} {s : finset β} {x : β} {f : β → polynomial α} (h_mem :  x ∈ s) (h_dvd : p ∣ f x) :
p∣ s.prod f :=
begin
  rw ←(insert_erase h_mem),
  simp [finset.prod_insert, dvd_mul_of_dvd_left h_dvd (finset.prod (erase s x) f)],
end

--Is this used?
lemma pow_sub_one_dvd_pow
{p : polynomial α} {n : ℕ} : monoid.pow p (n - 1) ∣ (monoid.pow p n) :=
begin
  cases n,
  {
    simp,
  },
  {
    rw nat.succ_sub_one,
    refine  dvd_of_mul_left_eq p _,
    exact rfl,
  },
end


end comm_semiring


section ring
variable [ring α]

--made priority local,but doesn't solve the problem..
instance : ring (polynomial α) := finsupp.to_ring
instance : add_comm_group (polynomial α) := by apply_instance

local attribute [priority 1100]  polynomial.ring
local attribute [priority 1100]  polynomial.add_comm_group

--application lemmas

@[simp] lemma neg_apply  {g : polynomial α } {a : ℕ } : (- g) a = - g a := finsupp.neg_apply

@[simp] lemma sub_apply {g₁ g₂ : polynomial α } {a : ℕ} : (g₁ - g₂) a = g₁ a - g₂ a := finsupp.sub_apply

--correct simp?
@[simp] lemma degree_neg {f : polynomial α} : degree (-f) = degree f:=
by simp [degree]

lemma degree_sub {f g : polynomial α} : degree (f - g) ≤ max (degree f) (degree g) :=
calc degree (f - g) = degree (f  + (- g)) : by simp
     ... ≤ max (degree f) (degree (-g)) : degree_add
     ...= max (degree f) (degree g) : by rw (@degree_neg _ _ g)

lemma neg_C_eq_C_neg (c : α) : - C c = C (- c) :=
begin
  apply eq.symm,
  simp [eq_neg_iff_add_eq_zero, C_add_C],
end

/-Why doesn't this work? It produces deep recursion?
@[simp] lemma is_constant_of_is_constant_neg (p : polynomial α) (h : is_constant (-p)) : is_constant p :=
begin
  rcases h with ⟨c, hc⟩,
  have : p = - C c,
  {
    exact calc p = - - p : by simp
    ... = _ : by rw hc,
  },
  subst this,
  simp [neg_C_eq_C_neg],
end-/

lemma is_constant_neg_iff_is_constant (p : polynomial α) : is_constant (-p) ↔ is_constant p :=
begin
  split,
  {
    intro h,
    rcases h with ⟨c, hc⟩,
    have : p = - C c,
    {
      exact calc p = - - p : by simp
      ... = _ : by rw hc,
    },
    subst this,
    simp [neg_C_eq_C_neg],
  },
  {
    intro h,
    rcases h with ⟨c, hc⟩,
    subst hc,
    exact ⟨-c, neg_C_eq_C_neg c⟩,
  }
end

end ring


section comm_ring
variable [comm_ring α]

instance : comm_ring (polynomial α) := finsupp.to_comm_ring

end comm_ring


end polynomial
