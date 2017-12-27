import  .Sup_fin data.finsupp order.lattice data.nat.cast .euclidean_domain
universes u v w

noncomputable theory

open classical set function finsupp lattice
local attribute [instance] prop_decidable
local attribute [instance] finsupp.to_comm_semiring
local attribute [instance] finsupp.to_semiring
local infix ^ := monoid.pow

namespace finset

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



def root_of (a : polynomial α) (b : α) := polynomial.eval a b = 0



lemma less_degree_imp {f : polynomial α} {k : ℕ} : k < degree f → ∃m, m>k ∧ f m ≠ 0:=
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

lemma C_mul_X {c : α} : C c * X = single 1 c :=
calc C c * X = single 0 c * single 1 1 : rfl
... = single (0 + 1) (c * 1) : single_mul_single
... = single 1 c : by simp


lemma constant_of_degree_eq_zero (h_zero_ne_one : (0 : α) ≠ 1) {p : polynomial α} : degree p = 0 → ∃c, p = C c :=
begin 
 fapply induction_on_X p,
 {
   intros,
   exact ⟨ a, rfl⟩ 
 },
 {
   have : degree X = 1, from degree_X h_zero_ne_one,
   intro,
   have : @degree α _ X ≠ 0, simp [this],
   contradiction,
 },
 {
   intros p q hp hq hpq,
   have : degree p = 0,
   admit,
   admit
 },
 {
   intros p hp hpx,
   have : degree p = 0,
   admit,
   have h_fac: (∃ (c : α), p = C c),
   exact hp this,
   have h_some: p = C (some h_fac), exact some_spec h_fac,
   have hpX: p * X = single 1 (some h_fac),
   exact calc p * X = C (some h_fac) * X : by rw [←h_some]
   ... = single 1 (some h_fac) : C_mul_X,
   by_cases h_cases : ((some h_fac) = 0),
   {
     have : p = 0,
     rw h_cases at h_some,
     simp [h_some],
     exact ⟨0, by simp [this]⟩
   },
   {
     
     have : 1 ≤ @degree α _ (p * X),
     fapply @le_degree α _ _ _ _,
     rw [hpX], 
     simp [h_cases],
     have h1: (1 : ℕ) ≤ 0,
     simp * at *,
     have h2: ¬ (1 : ℕ) ≤ 0,
     from nat.not_succ_le_zero 0,
     contradiction
   }
 }

end



lemma constant_of_leading_coef_eq_zero {p : polynomial α} : leading_coeff p = 0 → ∃c : α, p = C c :=
begin
  intro h1,
  by_cases  h :  p = 0,
  {
    fapply exists.intro,
    apply (0 : α),
    simp [h],
  },
  {
    
  }
end

/--/
lemma leading_coeff_ne_zero_of_ne_zero {p : polynomial α} : p ≠ 0 → (leading_coeff p) ≠ 0 := --incorrect!
begin
  rw not_imp_not,

end
-/
/-
begin
intro,
have : (degree p) ∈ (support p),
dunfold degree, dunfold finset.Sup_fin,
cases test : (support p),
-/
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


lemma degree_neg {f : polynomial α} : degree f = degree (-f):=
by simp [degree]

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

lemma eq_zero_or_eq_zero_of_mul_eq_zero_tmp {a b : α} (h : a * b = 0) : a = 0 ∨ b = 0 :=
begin
  by_contradiction h,
  rw decidable.not_or_iff_and_not at h,
  have ha : a ≠ 0, 
  simp [h],

end


instance {α : Type u} [integral_domain α] : no_zero_divisors (polynomial α):=
{eq_zero_or_eq_zero_of_mul_eq_zero := sorry

.. polynomial.comm_ring}


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
