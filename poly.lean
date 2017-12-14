import  .Sup_fin data.finsupp order.lattice data.nat.cast .euclidean_domain
universes u v w

noncomputable theory

open classical set function finsupp lattice
local attribute [instance] prop_decidable
local attribute [instance] finsupp.to_comm_semiring
local attribute [instance] finsupp.to_semiring
local infix ^ := monoid.pow

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

@[simp] lemma C_0 : C 0 = (0:polynomial α) := single_zero

@[simp] lemma C_1 : C 1 = (1:polynomial α) := rfl

def X : polynomial α := finsupp.single 1 1

lemma single_eq_X_pow : ∀{n:ℕ}, single n a = C a * X ^ n
| 0       := by simp [C]
| (n + 1) :=
  calc single (n + 1) a = single n a * X : by simp [X, single_mul_single]
    ... = C a * X ^ (n + 1) : by rw [@single_eq_X_pow n]; simp [pow_add, pow_one, mul_assoc]

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

--set_option pp.notation false
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

lemma degree_ne_zero_ne_zero {f : polynomial α} : degree f ≠ 0 → f ≠ 0 :=--I want to apply normal by_cpntradiction here, but I don't know how to apply that, due to ambiguous overload.
begin intro, apply (@classical.by_contradiction (f ≠ 0) _), intro,
have h3: (f = 0), from iff.elim_left not_not a_1,
have h4: degree f = 0, calc degree f = degree 0 : by rw [h3] ... = 0 : degree_zero,
apply a h4
 end -- Contradiction not needed

lemma less_degree_imp {f : polynomial α} {k : ℕ} : k < degree f → ∃m, m>k ∧f m ≠ 0:=
begin
intro,
apply classical.by_contradiction,
intro,
have :  ∀m, ¬(m > k ∧ f m ≠ 0),
apply forall_not_of_not_exists a_1,
have : ¬((degree f) > k ∧ f (degree f) ≠ 0),
from (this (degree f)),
have : ¬((degree f) > k) ∨ ¬ ( f (degree f) ≠ 0),
rw ←not_and_distrib,
exact this,
cases this,
{admit},
{}--weer terug bij af.


end


--set_option pp.notation false

lemma leading_coeff_ne_zero {p : polynomial α} : p ≠ 0 → (leading_coeff p) ≠ 0 :=
/-
begin
  intro,
  cases n : degree p,
  {
    have : ∃m, p m ≠ 0,
    apply exists_coeff_ne_zero_of_ne_zero a,
    apply (exists.elim this),
    intros,
    have h1 : a_1 ≤ degree p,
    apply (le_degree a_2),
    have h2 : a_1 = 0,
    apply nat.eq_zero_of_le_zero,
    exact calc a_1 ≤ degree p : h1
    ... = 0 : n,
    exact calc p (degree p) = p 0 : by rw n
      ... = p a_1 : by rw h2
      ... ≠ 0 : a_2
  },
  {
    have : a_1 < degree p,
    apply nat.lt_of_succ_le,
    simp *,




  }
  -/
/-
begin
  intro,


  dunfold leading_coeff,
  dunfold degree,
  have : ∃m, p m ≠ 0,
  apply exists_coeff_ne_zero_of_ne_zero a,
  apply (exists.elim this),
  intros,
  have : a_1 ∈ (support p),
  apply (iff.elim_right (mem_support_iff _)),
  exact a_2,

  have : id a_1 ≤ (finset.Sup_fin (support p) id),
  apply (finset.le_Sup_fin _),
  exact this,
  intro,
  cases k : (finset.Sup_fin (support p) id),
  have : p = 0,
  apply ext,
  intro,
  rw [zero_apply],
  cases a_4,
  rw [←k],
  rw [a_3],
  have : 0 < (nat.succ a_4),
  simp [nat.zero_lt_succ],
  apply classical.by_contradiction,
  intro,
  have : (nat.succ a_4) ∈ support p,
  apply (iff.elim_right (mem_support_iff _)),
  exact a_5,
  have h1: id (nat.succ a_4)≤ (finset.Sup_fin (support p) id),
  apply (finset.le_Sup_fin _),
  exact this,
  have : (nat.succ a_4) ≤ 0,
  exact calc (nat.succ a_4) = id (nat.succ a_4) : by simp
    ... ≤ (finset.Sup_fin (support p) id) : h1
    ... = 0 : k,
  apply (nat.not_succ_le_zero _ this),
  contradiction,
-/
begin
intro,
have : (degree p) ∈ (support p),
dunfold degree, dunfold finset.Sup_fin,
cases test : (support p),
--ginduction test : (p),
--apply (iff.elim_right (mem_support_iff _)),
--Maybe something with the image? To remove the id?
--Can we do an induction on the (support p), as a finset?





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
  { simp[derivative_mul_X, mul_assoc, mul_comm, mul_left_comm] },
  { simp [add_mul, mul_add] {contextual := tt} },
  { simp [add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm] {contextual := tt} }
end

end comm_semiring

section ring
variable [ring α]

instance : ring (polynomial α) := finsupp.to_ring

lemma neg_apply_poly (a : polynomial α) (n : ℕ):  (- a) n = - (a n) :=
begin intros, simp [coe_fn], simp [has_coe_to_fun.coe], simp [has_neg.neg, add_group.neg, add_comm_group.neg, ring.neg] , apply rfl
end


lemma degree_neg {f : polynomial α} : degree f = degree (-f):=
by simp [degree]

end ring

section comm_ring
variable [comm_ring α]

instance : comm_ring (polynomial α) := finsupp.to_comm_ring
end comm_ring
--set_option pp.all true
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

lemma eq_zero_or_eq_zero_of_mul_eq_zero_tmp {a b : α} (h : a * b = 0) : a = 0 ∨ b = 0 :=
begin

end


instance {α : Type u} [integral_domain α] : no_zero_divisors (polynomial α):=
{eq_zero_or_eq_zero_of_mul_eq_zero := sorry

.. polynomial.comm_ring}

set_option pp.numerals false
instance {α : Type u} [integral_domain α]: integral_domain (polynomial α) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := sorry,
  .. polynomial.comm_ring, .. polynomial.zero_ne_one_class }

end integral_domain




instance {α : Type u} [field α] : euclidean_domain (polynomial α) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := sorry,
  zero_ne_one := sorry,
  norm := sorry,
  h1 := sorry,
  h_norm := sorry,
  .. polynomial.comm_ring }

end polynomial
