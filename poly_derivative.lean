import  .Sup_fin data.finsupp order.lattice data.nat.cast .euclidean_domain unique_factorization_domain
import .to_finsupp .to_finset poly
universes u v w

noncomputable theory

open classical set function finsupp lattice

local attribute [instance] finsupp.to_comm_semiring
local attribute [instance] finsupp.to_semiring
local infix ^ := monoid.pow

namespace polynomial
local attribute [instance] prop_decidable
variables {α : Type u} {a a' a₁ a₂ : α} --{n m : ℕ} --do we want n and m?

--Formal derivatives

section semiring
variable [semiring α]

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






lemma derivative_eq_zero_of_is_constant {p : polynomial α} : (is_constant p) → (derivative p = 0) :=
begin
  intro h1,
  rw [is_constant] at h1,
  rcases h1 with ⟨c, h2⟩,
  simp [h2],
end

--We need characteristic_zero for derivative_eq_zero -> is_constant





end semiring

section comm_semiring
variable [comm_semiring α]

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

--For the lemmas below I did not try to refactor them yet.


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
  { simp},
  {
    simp [if_neg, pow_succ', derivative_mul, nat.succ_ne_zero, *], 
    cases n,
    {
      simp,
    },
    {
      simp [nat.succ_ne_zero, if_neg, pow_succ', *],
      exact calc p ^ n * p * derivative p + (1 + ↑n) * p ^ n * derivative p * p = 
      1 * p ^ n * p * derivative p + (1 + ↑n) * p ^ n * derivative p * p : by simp
      ... = 1 * p ^ n * p * derivative p + (1 + ↑n) * p ^ n * (derivative p * p) : by simp [mul_assoc]
      ... = 1 * p ^ n * p * derivative p + (1 + ↑n) * p ^ n * (p * derivative p) : by simp [mul_comm]
      ... = 1 * p ^ n * p * derivative p + (1 + ↑n) * p ^ n * p * derivative p   : by simp [mul_assoc]
      ... = 1 * (p ^ n * p * derivative p) + (1 + ↑n) * (p ^ n * p * derivative p)   : by simp [mul_assoc]
      ... = (1 + (1 + ↑n)) * (p ^ n * p * derivative p): by rw [←( add_mul 1 (1 + ↑n) (p ^ n * p * derivative p))]
      ... = (1 + (1 + ↑n)) * (p ^ n * p) * derivative p : by simp [mul_assoc]
    }
  }
end






end comm_semiring

section integral_domain
variable [integral_domain α]


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


--Problem with decidability propagated
lemma derivative_degree_sub_one_eq_degree_mul_leading_coeff {p : polynomial α} :
  derivative p (degree p - 1) = degree p * (leading_coeff p) :=
begin
  rw [leading_coeff],
  cases h : degree p,
  { 
    have : is_constant p, 
    { rwa [is_constant_iff_degree_eq_zero] },
    rcases this with ⟨a, ha⟩,
    rw [ha, derivative_C],
    simp
  },
  {  exact derivative_apply}
end

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
        exact h5,
      },
      by_contradiction h6,
      rw [h6, zero_apply] at h5,
      contradiction
    }
  },
  {
    exact derivative_eq_zero_of_is_constant
  }
end

end integral_domain

end polynomial