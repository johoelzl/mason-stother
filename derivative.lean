import data.finsupp poly
universes u v w

noncomputable theory

open classical set function finsupp lattice
local attribute [instance] prop_decidable
local attribute [instance] finsupp.to_comm_semiring
local attribute [instance] finsupp.to_semiring
local infix ^ := monoid.pow

namespace polynomial
variables {α : Type u} {a a' a₁ a₂ : α} --{n m : ℕ} --do we want n and m?

section semiring
variable [semiring α]


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
end semiring

section comm_semiring
variable [comm_semiring α]


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


end comm_semiring