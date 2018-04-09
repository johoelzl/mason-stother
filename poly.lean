import  .Sup_fin data.finsupp order.lattice data.nat.cast .euclidean_domain unique_factorization_domain
import .to_finsupp
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
  {
    intro h,
    have : ((C c) : ℕ → α) 0 = (0 : polynomial α) 0,
      { rw h},
    rw [C_apply, if_pos] at this,
    simp *,
  },
  {
    intro h,
    simp *,
  }
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
begin
  constructor, --Should we use constructor or split
  {
    exact eq_zero_of_leading_coef_eq_zero,
  },
  {
    intro h,
    simp *,
  }
end

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


--Formal derivatives

def derivative (p : polynomial α) : polynomial α :=
p.sum (λn a, nat.cases_on n 0 (λn, single n (a * (n + 1))))
-- TODO: the following form breaks derivative_single
-- p.sum (λn a, match n with 0 := 0 | n + 1 := single n (a * (n + 1)) end)

@[simp] lemma derivative_zero : derivative (0 : polynomial α) = 0 :=
finsupp.sum_zero_index

lemma derivative_single {n : ℕ} {a : α} :
  derivative (single n a) = nat.cases_on n 0 (λn, single n (a * (n + 1))) :=
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
  (assume n, match n with 0 := rfl | n + 1 := by simp [derivative]; refl end)
  (assume n, match n with
    0     := assume b₁ b₂, (add_zero _).symm
  | n + 1 := assume b₁ b₂, begin rw [← nat.succ_eq_add_one], simp [add_mul] end end)

@[simp] lemma derivative_sum {β : Type w} {s : finset β} {f : β → polynomial α} :
  derivative (s.sum f) = s.sum (λb, derivative (f b)) :=
begin
  apply (finset.sum_hom derivative _ _).symm,
  exact derivative_zero,
  exact assume x y, derivative_add
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

@[simp] lemma derivative_mul_C {f : polynomial α} : derivative (f * C a) = derivative f * C a :=
have ∀i c, derivative (single i (a * c)) = derivative (single i c) * C a,
  by intros i c; cases i; simp [C, single_mul_single, mul_comm, mul_left_comm, mul_assoc],
calc derivative (f * C a) = derivative (f.sum (λi c, single i (a * c))) :
    by rw [mul_C_eq_sum]
  ... = f.sum (λi c, derivative (single i (a * c))) : derivative_sum
  ... = f.sum (λi c, derivative (single i c) * C a) : by simp [this]
  ... = f.sum (λi c, derivative (single i c)) * C a : finset.sum_mul.symm
  ... = derivative (f.sum single) * C a : by simp [finsupp.sum, derivative_sum]
  ... = _ : by rw [sum_single]

@[simp] lemma derivative_C_mul {f : polynomial α} : derivative (C a * f) = C a * (derivative f) :=
by rw [mul_comm, derivative_mul_C, mul_comm]

private lemma derivative_mul_X_aux {f : polynomial α} : sum (derivative f) (λ (i : ℕ) (c : α), single (i + 1) c) = sum f (λ (i : ℕ) (c : α), single i (c * ↑i)) :=
begin
simp [derivative, sum_sum_index],
{ 
  apply finsupp.sum_congr rfl, 
  { 
    intros n hnf,
    cases n,
    { simp, apply sum_zero_index },
    { simp [sum_single_index]}
  } 
},
end

lemma derivative_mul_X {f : polynomial α} : derivative (f * X) = derivative f * X + f :=
calc derivative (f * X) = derivative (f.sum (λi c, single (i + 1) c)) :
    by rw [mul_X_eq_sum]
  ... = f.sum (λi c, derivative (single (i + 1) c)) :
    derivative_sum
  ... = f.sum (λi c, single i (c * (i + 1))) :
    by simp [derivative_single, (nat.succ_eq_add_one _).symm]
  ... = f.sum (λi c, single i (c * i) + single i c) : by simp [single_add, mul_add]
  ... = f.sum (λi c, single i (c * i)) + f: by simp [sum_add, sum_single]
  ... = derivative f * X + f : by rw [mul_X_eq_sum, derivative_mul_X_aux]

lemma derivative_mul {f : polynomial α} :
  ∀{g}, derivative (f * g) = derivative f * g + f * derivative g :=
begin
  apply f.induction_on_X,
  { simp [derivative_mul_C, mul_assoc, mul_comm, mul_left_comm] },
  { simp [add_mul, mul_add] {contextual := tt} },
  { intros p hp q,
    rw [mul_assoc, hp, hp, mul_comm X q, derivative_mul_X],
    simp [mul_add, add_mul, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm] }
end

open finset


lemma derivative_prod {β : Type w} {s : finset β} {f : β → polynomial α} :
  derivative (s.prod f) = s.sum (λb, derivative (f b) * (erase s b).prod f) :=
begin
  apply finset.induction_on s,
  { simp },
  { 
    intros a s has ih,
    have : ∀b∈s, ((insert a s).erase b).prod f = f a * (s.erase b).prod f,
    {
      assume b hb,
      have : a ≠ b, 
      { 
        assume h, simp * at * 
      },
      rw [erase_insert_eq_insert_erase, finset.prod_insert]; simp *
    },
    have : s.sum (λb, derivative (f b) * (erase (insert a s) b).prod f) =
      f a * s.sum (λb, derivative (f b) * (erase s b).prod f),
    {
      exact calc s.sum (λb, derivative (f b) * (erase (insert a s) b).prod f) =
        s.sum (λb, f a * (derivative (f b) * (s.erase b).prod f)) :
        sum_congr rfl $ by simp [this, mul_assoc, mul_comm, mul_left_comm] {contextual := tt}
        ... = f a * s.sum (λb, derivative (f b) * (erase s b).prod f) : by rw [mul_sum],
    },
    simp [ih, has, finset.prod_insert, derivative_mul, sum_insert, erase_insert, this] 
  }
end


--Clean up done till here 9 april 2018



lemma derivative_prod_multiset {s : multiset (polynomial α)} :
  derivative (s.prod) = (s.map (λb, derivative (b) * (s.erase b).prod)).sum :=
begin
  apply multiset.induction_on s,
  {
    simp * at *,    
  },
  {
    intros a s has,
    simp * at *,
    rw derivative_mul,
    have h : multiset.sum (multiset.map (λ (b : polynomial α), derivative b * multiset.prod (multiset.erase (a :: s) b)) s) =
    a * multiset.sum (multiset.map (λ (b : polynomial α), derivative b * multiset.prod (multiset.erase s b)) s),
    {
      exact calc multiset.sum (multiset.map (λ (b : polynomial α), derivative b * multiset.prod (multiset.erase (a :: s) b)) s) =
      multiset.sum (multiset.map (λ (b : polynomial α), a * (derivative b * multiset.prod (multiset.erase (s) b))) s) : 
      begin
        apply congr_arg,
        apply multiset.map_congr,
        intros x h,
        by_cases h2 : x = a,
        {
          subst h2,
          rw multiset.erase_cons_head,
          rcases multiset.exists_cons_of_mem h with ⟨t, h⟩,
          subst h,
          simp [mul_comm x (derivative x)],
          rw [←mul_assoc, ←mul_assoc, mul_comm x _], 
        },
        {
          simp [multiset.erase_cons_tail s (ne.symm h2), mul_comm a _,mul_assoc],
        }
      end
      ... = _ : @multiset.sum_map_mul (polynomial α) _ _ a _ s,     
    },
    rw [h, has],   
  }
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

--made priority local,but doesn't solve the problem..
instance : ring (polynomial α) := finsupp.to_ring
instance : add_comm_group (polynomial α) := by apply_instance

local attribute [priority 1100]  polynomial.ring
local attribute [priority 1100]  polynomial.add_comm_group

--application lemmas

@[simp] lemma neg_apply  {g : polynomial α } {a : ℕ } : (- g) a = - g a := finsupp.neg_apply

@[simp] lemma sub_apply {g₁ g₂ : polynomial α } {a : ℕ} : (g₁ - g₂) a = g₁ a - g₂ a := finsupp.sub_apply

lemma degree_neg {f : polynomial α} : degree (-f) = degree f:=
by simp [degree]

lemma degree_sub {f g : polynomial α} : degree (f - g) ≤ max (degree f) (degree g) :=
calc degree (f - g) = degree (f  + (- g)) : by simp
     ... ≤ max (degree f) (degree (-g)) : degree_add
     ...= max (degree f) (degree g) : by rw (@degree_neg _ _ g)

lemma neg_C_eq_C_neg (c : α) : - C c = C (- c) :=
begin
  apply eq.symm,
  rw eq_neg_iff_add_eq_zero,
  rw C_add_C,
  simp,
end

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
    rw neg_C_eq_C_neg,
    simp,    
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


section integral_domain
variable [integral_domain α]

lemma X_pow_ne_zero {n : ℕ}: (X ^ n : polynomial α) ≠ 0 :=
begin
  rw X_pow_eq_single,
  by_contradiction h2,
  rw not_not at h2,
  have h3: (single n 1 : polynomial α ) n = 1,
  simp,
  rw h2 at h3,
  simp at h3,
  exact h3,
end

lemma zero_ne_one : (0:polynomial α) ≠ 1:=
begin
  intro h,
  have : (0 : polynomial α) 0 = (1 : polynomial α) 0, by rw [h],
  simp * at *
end

instance {α : Type u} [integral_domain α] : zero_ne_one_class (polynomial α):=
{ zero_ne_one := zero_ne_one, .. polynomial.comm_ring }

/- Can we use this to reduce the lemma below?
lemma leading_coeff_mul_leading_coeff_eq_zero_of_mul_eq_zero (f g : polynomial α) (h : f * g = 0) : (leading_coeff f) * (leading_coeff g) = 0 :=
begin
  have h1 : leading_coeff f = 0 ∨  leading_coeff g = 0,
  {
    by_contradiction h2,
    rw [not_or_distrib, leading_coef_eq_zero_iff_eq_zero, leading_coef_eq_zero_iff_eq_zero] at h2,
  }
end
-/

lemma eq_zero_or_eq_zero_of_mul_eq_zero : ∀ f g : polynomial α, f * g = 0 → f = 0 ∨ g = 0 :=
begin
  intros f g h1,
  by_contradiction h2,
  rw [not_or_distrib, ←leading_coef_eq_zero_iff_eq_zero, ←leading_coef_eq_zero_iff_eq_zero] at h2,
  have h7 : (leading_coeff f) * (leading_coeff g) ≠ 0,
  {
    intro h8,
    have h9 : leading_coeff f = 0 ∨  leading_coeff g = 0,
      from eq_zero_or_eq_zero_of_mul_eq_zero h8,
    cases h9 ; simp * at *,
  },
  have h8 : (f * g) (degree f + degree g) ≠ 0,
  {
    simpa [mul_degree_add_degree_eq_leading_coeff_mul_leading_coeff],   
  },
  rw [h1, zero_apply] at h8,
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
    rw ←mul_degree_add_degree_eq_leading_coeff_mul_leading_coeff,
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

lemma degree_mul_eq_add_of_mul_ne_zero {f g : polynomial α} : f * g ≠ 0 → degree (f * g) = degree f + degree g :=
begin

  intro h1, 
  have h2 : f ≠ 0,
  from ne_zero_of_mul_ne_zero_right h1,
  have h3 : g ≠ 0,
  from ne_zero_of_mul_ne_zero_left h1,
  have h4 : (f * g) (degree f + degree g) ≠ 0,
  calc (f * g) (degree f + degree g) = (leading_coeff f) * (leading_coeff g) : mul_degree_add_degree_eq_leading_coeff_mul_leading_coeff
     ... ≠ 0 : by {simp,rw [←not_iff_not_of_iff mul_eq_zero_iff_mul_leading_coef_eq_zero], exact h1},
  have h5 : (degree f + degree g) ≤ degree (f * g),
  from le_degree h4,
  have h6 : degree (f * g) ≤ (degree f + degree g),
  from degree_mul,
  apply le_antisymm; simp * at *
end


lemma degree_dvd {f g : polynomial α} (h1 : f ∣ g)(h4 : g ≠ 0) : degree f ≤ degree g :=
begin
  let c := some h1,
  have h2 : g = f * c,
  from some_spec h1,
  by_cases h : (f = 0),
  {
    rw h,
    simp,
    exact nat.zero_le _
  },
  {
    rw h2 at h4,
    have h3 : degree (f * c) = degree f + degree c,
    from degree_mul_eq_add_of_mul_ne_zero h4,
    rw ←h2 at h3,
    exact (nat.le.intro (eq.symm h3)),
  }
end

lemma prod_ne_zero_of_forall_mem_ne_zero {f : finset (polynomial α)} : (∀ x ∈ f, x ≠ (0 : polynomial α)) → f.prod id ≠ 0 :=
begin
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
  }
end


lemma degree_prod {β : Type u} {s : finset β} {f : β → polynomial α} : finset.prod s f ≠ 0 → degree (s.prod f) = s.sum (degree ∘ f) :=
begin
  fapply finset.induction_on s,
  {
    simp *,
  },
  {
    intros a s h1 h2 h3,
    simp *,
    have h4 : finset.prod s f ≠ 0,
    {
      rw [finset.prod_insert h1] at h3,
      exact ne_zero_of_mul_ne_zero_left h3,      
    },
    have h5 : degree (finset.prod s f) = finset.sum s (degree ∘ f),
    from h2 h4,
    rw [degree_mul_eq_add_of_mul_ne_zero, h5],
    rw [finset.prod_insert h1] at h3,
    exact h3,
  },

end

lemma degree_prod_eq_sum_degree_of_prod_ne_zero {f : finset (polynomial α)} : (f.prod id ≠ 0) → degree (f.prod id) = f.sum (degree) :=
begin
  fapply finset.induction_on f,
  {
    simp *
  },
  {
    intros a s h1 h2 h3,
    simp,
    rw [finset.prod_insert h1, finset.sum_insert h1],
    have h4: finset.prod (s) id ≠ 0,
    {
      rw finset.prod_insert at h3,
      exact ne_zero_of_mul_ne_zero_left h3,
      exact h1,
    },
    have h5: degree (finset.prod s id) = finset.sum s degree,
    from h2 h4,
    simp at h5,
    have h6 : a * finset.prod s (λ (x : polynomial α), x) ≠ 0,
    {
      rw finset.prod_insert h1 at h3,
      simp at h3,
      exact h3    
    },
    rw degree_mul_eq_add_of_mul_ne_zero h6,
    rw h5
  }
end

lemma degree_pow {x : polynomial α}{n : ℕ} : degree (x ^ n) = n * degree x :=
begin
  
  induction n with n h1,
  {
    simp *,
  },
  {
    by_cases h : (x = 0),
    {
      simp * at *,
      simp [pow_succ]
    },
    {
      rw [pow_succ, degree_mul_eq_add_of_mul_ne_zero, h1],
      exact calc degree x + n * degree x = 1 * degree x + n * degree x : by simp
          ... = n * degree x + 1 * degree x : by rw add_comm (1 * degree x) (n * degree x)
          ... = (n + 1) * degree x : by rw [add_mul]
          ... = nat.succ n * degree x : rfl,
      have : (x ^ n ≠ 0),
      from pow_ne_zero _ h,
      exact mul_ne_zero h this,
    },   
  }
end

lemma degree_finsupp_prod {f : polynomial α →₀ ℕ} (h1 : finsupp.prod f (λ x n, x^n) ≠ 0): degree (finsupp.prod f (λ x n, x^n)) = finsupp.sum f (λ x n, n*(degree x)):=
begin
  rw [finsupp.prod, degree_prod h1, finsupp.sum],
  simp [(∘), * , degree_pow],
end


lemma leading_coeff_mul_eq_mul_leading_coef {f g : polynomial α} : leading_coeff (f * g) = leading_coeff f * leading_coeff g :=
begin
  by_cases h1 : (f * g = 0),
  {
    simp * at *,
    cases eq_zero_or_eq_zero_of_mul_eq_zero _ _ h1 with h2,
    {
      simp *,
    },
    {
      simp *,
    }
  },
  {
    have : degree (f * g) = degree f + degree g,
    from degree_mul_eq_add_of_mul_ne_zero h1,
    simp [leading_coeff, this, mul_degree_add_degree_eq_leading_coeff_mul_leading_coeff]
  }    
end


lemma monic_mul_of_monic_of_monic {a b : polynomial α} (ha : monic a) (hb : monic b) : monic (a * b) :=
begin
  simp only [monic] at *,
  rw leading_coeff_mul_eq_mul_leading_coef,
  simp *,
end


lemma monic_prod_of_forall_mem_monic [comm_semiring α] {s : multiset (polynomial α)} (hs: ∀x ∈ s, monic x) : monic s.prod :=
begin
  revert hs,
  apply multiset.induction_on s,
  {
    simp * at *,
  },
  {
    intros a s h1 h2,
    simp * at *,
    apply monic_mul_of_monic_of_monic,
    {
      apply h2 a,
      simp,
    },
    {
      apply h1,
      intros x s,
      apply h2,
      simp *,
    }
  }
end



--Should be in lib, used it on two spots already.
lemma one_le_of_ne_zero {n : ℕ} : n ≠ 0 → 1 ≤ n :=
begin
  intro h1,
  induction n,
  {
    have : 0 = 0,
    from rfl,
    contradiction,
  },
  {
    apply nat.succ_le_succ,
    exact nat.zero_le _,
  }
end

lemma derivative_apply {p : polynomial α} {n : ℕ} : derivative p n = (n + 1) * p (n + 1) :=
calc derivative p n = ({n + 1} : finset ℕ).sum (λm, (nat.cases_on m 0 (λn, single n (p m * (↑n + 1))) : polynomial α) n) :
  begin
    rw [derivative, sum_apply],
    apply finset.sum_bij_ne_zero (λx _ _, x),
    { intro m, cases m,
      { dsimp, simp },
      { by_cases m = n,
        { dsimp, simp [single_apply, h] },
        { dsimp, simp [single_apply, h] } } },
    { intros m hm, exact id },
    { intros a₁ a₂ _ _ _ _, exact id },
    { dsimp, simp,
      intro h,
      refine ⟨n + 1, _, _, _⟩, 
      { change (single n (p (n + 1) * (n + 1)) n ≠ 0) at h,
        simp [mul_eq_zero, not_or_distrib] at h,
        exact h.left },
      { assumption },
      { refl } },
    { dsimp, simp }
  end
  ... = _ :
  begin
    simp,
    change single n (p (n + 1) * (n + 1)) n = (1 + n) * p (n + 1),
    simp [mul_comm]
  end

--Problem with decidability propagated
lemma derivative_degree_sub_one_eq_degree_mul_leading_coeff {p : polynomial α} :
  derivative p (degree p - 1) = degree p * (leading_coeff p) :=
begin
  rw [leading_coeff],
  cases h : degree p,
  { have : is_constant p, { rwa [is_constant_iff_degree_eq_zero] },
    rcases this with ⟨a, ha⟩,
    rw [ha, derivative_C],
    simp },
  exact derivative_apply
end

--set_option pp.notation false
lemma derivative_eq_zero_of_is_constant {p : polynomial α} : (is_constant p) → (derivative p = 0) :=
begin
  intro h1,
  rw [is_constant] at h1,
  let c := some h1,
  have h2: p = C c,
  from some_spec h1,
  rw h2,
  simp
end

--We need characteristic_zero for derivative_eq_zero -> is_constant
lemma derivative_eq_zero_iff_is_constant {p : polynomial α} (h : characteristic_zero α) :
  (derivative p = 0) ↔ (is_constant p) :=
begin
  constructor,
  {
    by_cases h1 : (p = 0),
    {
      intro h2,
      simp *,
    },
    {
      rw ←not_imp_not,
      intros h2,
      rw is_constant_iff_degree_eq_zero at h2,
      have h3 : degree p ∈ support p,
      from degree_mem_support_of_ne_zero h1,
      rw mem_support_iff at h3,
      have h4 : (derivative p) ((degree p)-1) = (degree p * (leading_coeff p)),
      from derivative_degree_sub_one_eq_degree_mul_leading_coeff,
      have h5 : (derivative p) (degree p - 1) ≠ 0,
      {
        rw h4,
        apply mul_ne_zero,
        apply h,
        exact h2,
        have h5 : leading_coeff p ≠ 0,
        {
          rw [←leading_coef_eq_zero_iff_eq_zero] at h1,
          exact h1,
        },
        --simp only [coe, lift_t, has_lift_t.lift, coe_t,has_coe_t.coe, coe_b, has_coe.coe, nat.cast],
        exact h5,

      },
      by_contradiction h6,
      rw h6 at h5,
      rw [zero_apply] at h5,
      contradiction
    }

    
    
  },
  {
    exact derivative_eq_zero_of_is_constant
  }
end

lemma is_constant_add {a b c : polynomial α} (h1 : is_constant a) (h2 : is_constant b) (h_add : a + b = c): is_constant c :=
begin
  rw is_constant_iff_degree_eq_zero at *,
  have h3 : degree (a + b) ≤ max (degree a) (degree b),
  from degree_add,
  simp * at *,
  exact nat.eq_zero_of_le_zero h3,
end

--Why placed here?
lemma degree_derivative_le {p : polynomial α} : degree (derivative p) ≤ degree p - 1 :=
degree_le $ assume m hm,
  have degree p < m + 1,
    from calc degree p ≤ (degree p - 1) + 1 : nat.le_sub_add (degree p) 1
      ... ≤ m : hm
      ... < m + 1 : nat.lt_succ_self _,
  have p (m + 1) = 0,
    from eq_zero_of_gt_degree this,
  by rw [derivative_apply, this, mul_zero]

end integral_domain
end polynomial
