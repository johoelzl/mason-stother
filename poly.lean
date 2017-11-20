import .finsupp .Sup_fin order.lattice data.nat.cast
universes u v w

noncomputable theory

open classical set function finsupp lattice
local attribute [instance] decidable_inhabited prop_decidable


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
instance : semiring (polynomial α) := finsupp.semiring

def C (a : α) : polynomial α := finsupp.single 0 a

@[simp] lemma C_0 : C 0 = (0:polynomial α) := single_zero

@[simp] lemma C_1 : C 1 = (1:polynomial α) := rfl

def X : polynomial α := finsupp.single 1 1

lemma single_eq_X_pow : ∀{n}, single n a = C a * X ^ n
| 0       := by simp [C]
| (n + 1) :=
  calc single (n + 1) a = single n a * X : by simp [X, single_mul_single]
    ... = C a * X ^ (n + 1) : by rw [@single_eq_X_pow n]; simp [pow_add]

lemma induction_on [semiring α] {M : polynomial α → Prop} (p : polynomial α)
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
  induction n; simp [pow_add, nat.succ_eq_add_one, *]; exact M_1
end,
have M_sum : ∀{s:finset ℕ} {f : ℕ → polynomial α}, (∀a∈s, M (f a)) → M (s.sum f),
  from assume s f, s.induction_on (by simp [M_0]) (by simp * {contextual := tt}),
begin
  rw [←@sum_single _ _ _ p],
  apply M_sum,
  exact (assume a ha, M_single _ _)
end

def eval (p : polynomial α) (a : α) : α := p.sum $ λn c, c * a ^ n

def degree (p : polynomial α) : ℕ := p.support.Sup_fin id

lemma le_degree {p : polynomial α} {n : ℕ} (h : p n ≠ 0) : n ≤ degree p :=
show id n ≤ degree p, from finset.le_Sup_fin (by simp [h])

@[simp] lemma degree_zero : degree (0 : polynomial α) = 0 :=
have (0 : polynomial α).support = ∅, from support_zero,
by simp [degree, this]; refl

lemma degree_single {a : α} {n : ℕ} : degree (single n a) ≤ n :=
calc degree (single n a) = (single n a).support.Sup_fin id : by simp [degree]
  ... ≤ ({n} : finset ℕ).Sup_fin id : finset.Sup_fin_mono finsupp.support_single_subset
  ... ≤ _ : by simp

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
s.induction_on (by simp; refl) $
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
  apply_instance,
  exact derivative_zero,
  exact assume x y, derivative_add
end

/-
@[simp] lemma derivative_mul {f g : polynomial α} :
  derivative (f * g) = derivative f * g + f * derivative g :=
calc _ = _ : derivative_sum
  ... = _ : begin simp [derivative_sum, finsupp.sum] end
-/

end semiring

instance [comm_semiring α] : comm_semiring (polynomial α) := finsupp.comm_semiring
instance [ring α] : ring (polynomial α) := finsupp.ring
instance [comm_ring α] : comm_ring (polynomial α) := finsupp.comm_ring

end polynomial
