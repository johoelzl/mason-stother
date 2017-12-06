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

lemma C_mul_C {a b : α} : C (a * b) = C a * C b :=
by simp [C, single_mul_single]

end semiring

section comm_semiring
variable [comm_semiring α]

instance : comm_semiring (polynomial α) := finsupp.comm_semiring

lemma mul_C_eq_sum {f : polynomial α} {a : α} :
  f * C a = f.sum (λi c, single i (a * c)) :=
calc f * C a = (f.sum single) * C a : by rw [sum_single]
  ... = f.sum (λi c, single i c * C a) : finset.sum_mul
  ... = f.sum (λi c, single i (a * c)) : by simp [single_eq_X_pow, C_mul_C]

lemma mul_X_eq_sum {f : polynomial α} :
  f * X = f.sum (λi c, single (i + 1) c) :=
calc f * X = (f.sum single) * X : by rw [sum_single]
  ... = f.sum (λi c, single i c * X) : finset.sum_mul
  ... = f.sum (λi c, single (i + 1) c) : by simp [single_eq_X_pow, pow_add]

lemma derivative_mul_C {f : polynomial α} :
  derivative (f * C a) = derivative f * C a :=
have ∀i c, derivative (single i (a * c)) = derivative (single i c) * C a,
  by intros i c; cases i; simp [C, single_mul_single],
calc derivative (f * C a) = derivative (f.sum (λi c, single i (a * c))) :
    by rw [mul_C_eq_sum]
  ... = f.sum (λi c, derivative (single i (a * c))) : derivative_sum
  ... = f.sum (λi c, derivative (single i c) * C a) : by simp [this]
  ... = f.sum (λi c, derivative (single i c)) * C a : finset.sum_mul.symm
  ... = derivative (f.sum single) * C a : by simp [finsupp.sum, derivative_sum]
  ... = _ : by rw [sum_single]

lemma temp {f : polynomial α}: derivative f * X = f.sum (λi c, single i (c * i)):=
have ∀ a (b : α ),(  finsupp.sum (derivative._match_1 b a) (λ (i : ℕ), single (i + 1)) = single a (b * a) ),from 
begin
intros,
cases a,
{simp [derivative._match_1], apply sum_zero_index},
{simp [derivative._match_1], simp [sum_single_index]}
end,
have (λ (a : ℕ) (b : α ),(  finsupp.sum (derivative._match_1 b a) (λ (i : ℕ), single (i + 1)) ) ) = (λ (a : ℕ) (b : α ),  single a (b * a) ), from
(funext(λ _, funext $ this _)),
calc (derivative f) * X = sum (derivative f) (λi c, single (i + 1) c) : by rw [mul_X_eq_sum]
  ... = sum (sum f (λ (n : ℕ) (a : α), derivative._match_1 a n)) (λ (i : ℕ), single (i + 1)) : by rw [derivative]
  ... = sum f (λa b, sum ((λ n d, derivative._match_1 d n) a b) (λ i, single (i + 1))  ) :  begin rw [sum_sum_index  ], {intro, apply single_zero}, {intros, apply (@single_add _ _ _ _ _ _)}  end
  ... = sum f (λa b, sum (derivative._match_1 b a) (λ i, single (i + 1))) : rfl -- Nu moet ik een case match doen in a.
  ... = f.sum (λi c, single i (c * i)) : begin rw [this] end

lemma derivative_mul_X2 {f : polynomial α} :
  derivative (f * X) = derivative f * X + f * derivative X:=
calc derivative (f * X) = derivative (f.sum (λi c, single (i + 1) c)) :
    by rw [mul_X_eq_sum]
  ... = f.sum (λi c, derivative (single (i + 1) c)) :
    derivative_sum
  ... = f.sum (λi c, single i (c * (i + 1))) :
    by simp [derivative_single, (nat.succ_eq_add_one _).symm]
  ... = f.sum (λi c, single i (c * i) + single i c) : by simp [single_add, mul_add]
  ... = f.sum (λi c, single i (c * i)) + f: by simp [sum_add, sum_single]
  ... = derivative f * X + f : by rw [temp]
  ... = _ : by simp 

/-
lemma derivative_mul_X {f : polynomial α} :
  derivative (f * X) = derivative f * X + f :=
calc derivative (f * X) = derivative (f.sum (λi c, single (i + 1) c)) :
    by rw [mul_X_eq_sum]
  ... = f.sum (λi c, derivative (single (i + 1) c)) :
    derivative_sum
  ... = f.sum (λi c, single i (c * (i + 1))) :
    by simp [derivative_single, (nat.succ_eq_add_one _).symm]
  ... = f.sum (λi c, single i (c * i) + single i c) : _
  ... = _ : _
-/


lemma derivative_mul :
  ∀ {f g : polynomial α},
  derivative (f * g) = derivative f * g + f * derivative g :=
begin
  intros f g,
  apply polynomial.induction_on g,
  { simp [derivative_mul_C] },
  {apply derivative_mul_X2},
  {intros, 
  calc
  derivative (f * (p + q)) = derivative (f * (p + q)) : rfl
  ... =  derivative ((f * p) + (f * q)) : by rw [mul_add]
  ... =  derivative (f * p) + derivative (f * q) : derivative_add
  ... =  (derivative f * p + f * derivative p) + (derivative f * q + f * derivative q) : by rw [a, a_1]
  ... =  (derivative f * p + derivative f * q) + (f * derivative p + f * derivative q) : by simp
  ... =  derivative f * (p + q) + (f * (derivative p + derivative q)) : by simp [mul_add]
  ... = _ : by rw [derivative_add]
  },
  {
  calc
  derivative (f * (p * q)) = derivative (f * (p * q)) : rfl
  ... _ : _

  }
end

  

lemma derivative_mul2 :
  ∀ {f g : polynomial α},
  derivative (f * g) = derivative f * g + f * derivative g :=





/-
lemma temp2 {f : polynomial α} : derivative (f.sum (λi c, single i c)) = f.sum (λi c, derivative (single i c)) :=
calc derivative (f.sum (λi c, single i c)) = f.sum (λi c, derivative (single i c)) : by simp [derivative_sum]


lemma temp3 {f: polynomial α} :
derivative (f.sum (λi c, single (i) c)) = f.sum (λi c, derivative (single (i) c)) :=
calc derivative (f.sum (λi c, single (i) c)) = f.sum (λi c, derivative (single (i) c)) : by simp [-sum_single, derivative_sum,finsupp.sum]


lemma temp3 {f:  polynomial α} : sum f (λa b, sum (derivative._match_1 b a) (λ i, single (i + 1))) = f.sum (λi c, single i (c * i)) :=
calc 
sum f (λa b, sum (derivative._match_1 b a) (λ i, single (i + 1))) = sum f (λa b, sum (derivative._match_1 b a) (λ i, single (i + 1))) : rfl
... _ = _ :
begin 
apply rfl
end



lemma temp5 : ∀ a (b : α ),(  finsupp.sum (derivative._match_1 b a) (λ (i : ℕ), single (i + 1)) = single a (b * a) )
:= 
begin
intros,
cases a,
{simp [derivative._match_1], apply sum_zero_index},
{simp [derivative._match_1], simp [sum_single_index]}
end

#check assume a b , temp5 a b
lemma temp6 (a : ℕ): (λ (b : α ),(  finsupp.sum (derivative._match_1 b a) (λ (i : ℕ), single (i + 1)) ) ) = (λ (b : α ),  single a (b * a) ):=
funext $ temp5 a


lemma temp7 : (λ (x : ℕ) (b : α ),(  finsupp.sum (derivative._match_1 b x) (λ (i : ℕ), single (i + 1)) ) ) = λ (x : ℕ) (b : α ),  single x (b * x) :=
funext temp6

#check funext(λ _, funext $ temp5 _)


lemma temp8 : (λ (a : ℕ) (b : α ),(  finsupp.sum (derivative._match_1 b a) (λ (i : ℕ), single (i + 1)) ) ) = (λ (a : ℕ) (b : α ),  single a (b * a) ) :=
funext (λ a, funext $ temp5 a)
-/
/-
lemma temp {f : polynomial α}: derivative f * X = f.sum (λi c, single i (c * i)):=
have ∀ a (b : α ),(  finsupp.sum (derivative._match_1 b a) (λ (i : ℕ), single (i + 1)) = single a (b * a) ),from 
begin
intros,
cases a,
{simp [derivative._match_1], apply sum_zero_index},
{simp [derivative._match_1], simp [sum_single_index]}
end,
have (λ (a : ℕ) (b : α ),(  finsupp.sum (derivative._match_1 b a) (λ (i : ℕ), single (i + 1)) ) ) = (λ (a : ℕ) (b : α ),  single a (b * a) ), from
(funext(λ _, funext $ this _)),
calc (derivative f) * X = sum (derivative f) (λi c, single (i + 1) c) : by rw [mul_X_eq_sum]
  ... = sum (sum f (λ (n : ℕ) (a : α), derivative._match_1 a n)) (λ (i : ℕ), single (i + 1)) : by rw [derivative]
  ... = sum f (λa b, sum ((λ n d, derivative._match_1 d n) a b) (λ i, single (i + 1))  ) :  begin rw [sum_sum_index  ], {intro, apply single_zero}, {intros, apply (@single_add _ _ _ _ _ _)}  end
  ... = sum f (λa b, sum (derivative._match_1 b a) (λ i, single (i + 1))) : rfl -- Nu moet ik een case match doen in a.
  ... = f.sum (λi c, single i (c * i)) : begin rw [this] end
-/

-- must show the equality of:
--(λi c, single i (c * i)) and (λa b, sum ((λ n d, derivative._match_1 d n) a b) (λ i, single (i + 1))  )
-- We can do an application

-- sum (sum f (λ (n : ℕ) (a : α), derivative._match_1 a n)) (λ (i : ℕ), single (i + 1)) = 
--sum f (λa b, ((λ (n : ℕ) (a : α), derivative._match_1 a n) a b).sum (λ (i : ℕ), single (i + 1)))

-- (f.sum g).sum h = f.sum (λa b, (g a b).sum h)

/-
calc derivative f * X = (derivative (f.sum (λi c, single i c))) * X : by simp [sum_single]
  ... = (f.sum (λi c, derivative (single i c))) * X : by simp [-sum_single, derivative_sum,finsupp.sum]
  ... = sum (f.sum (λi c, derivative (single i c))) (λi c, single (i + 1) c) : by rw [mul_X_eq_sum]
  ... = : by rw [sum_sum_index]
  -- (f.sum g).sum h = f.sum (λa b, (g a b).sum h)


  ... = _ : _
-/


lemma derivative_mul_X2 {f : polynomial α} :
  derivative (f * X) = derivative f * X + f :=
calc derivative (f * X) = derivative (f.sum (λi c, single (i + 1) c)) :
    by rw [mul_X_eq_sum]
  ... = f.sum (λi c, derivative (single (i + 1) c)) :
    derivative_sum
  ... = f.sum (λi c, single i (c * (i + 1))) :
    by simp [derivative_single, (nat.succ_eq_add_one _).symm]
  ... = f.sum (λi c, single i (c * i) + single i c) : by simp [single_add, mul_add]
  ... = f.sum (λi c, single i (c * i)) + f: by simp [sum_add, sum_single]
  ... = _ : by rw [temp]


@[simp] lemma derivative_sum2 {β : Type w} {s : polynomial α} {f :ℕ  →  α  → polynomial α} :
  derivative (s.sum f) = s.sum (λi c, derivative (f i c)) :=
begin
apply (finset.sum_hom derivative _ _).symm,
apply_instance,
apply derivative_zero,
apply derivative_add
end

/-
@[simp] lemma derivative_mul {f g : polynomial α} :
  derivative (f * g) = derivative f * g + f * derivative g :=
calc _ = _ : derivative_sum
  ... = _ : begin simp [derivative_sum, finsupp.sum] end
-/

/-
derivative_mul could be done with the induction lemma. if we 
let M := (λ p : polynomial α, ∀ f : polynomial α, 
derivative (p * f) = derivative p * f + p * derivative f)
-/


lemma induction_on2 [semiring α] {M : polynomial α → Prop}
  (M_C : ∀(a : α), M (C a)) (M_X : M X)
  (M_add : ∀(p q), M p → M q → M (p + q))
  (M_mul : ∀(p q), M p → M q → M (p * q)) :
   ∀ (p : polynomial α), M p := assume p, induction_on p M_C M_X M_add M_mul

#check induction_on
#check induction_on2

def M : polynomial α -> Prop :=  (λ g : polynomial α, ∀ f, derivative (f * g) = derivative f * g + f * derivative g ) 

/-
lemma derivative_mul_C {f : polynomial α} :
  derivative (f * C a) = derivative f * C a :=
-/

lemma derivative_mul3 :
  ∀ {f g : polynomial α},
  derivative (f * g) = derivative f * g + f * derivative g :=
  
  (@induction_on2 _ _ _ M 
  /-
  begin simp [M], intros,
   exact eq.symm ( calc derivative f * C a + f * 0 = derivative f * C a + f * (0 : polynomial α) : rfl
      ... = derivative f * C a : by simp 
      ... = derivative (f * C a) : eq.symm derivative_mul_C
    )
   end-/ begin end
  /-
   calc (0 : polynomial α) * g + C a * derivative g = 0 * g + C a * derivative g : rfl
    ... = C a * derivative g : by simp [zero_mul]
    ... = derivative g * C a : by simp
    ... = C a
-/

     
  
   --derivative_mul_C 

   /-
  begin simp [M], intro, 
  calc
  derivative (f * X) = derivative (f * X) : rfl
   ... = derivative f * X + f * derivative X: derivative_mul_X2
   ... = derivative f * X + f : by simp [derivative_X]
   ... = _ : by simp
   end -/ begin end
   /-
  begin simp [M], intros,  
  calc
  derivative (f * (p + q)) = derivative (f * (p + q)) : rfl
  ... =  derivative ((f * p) + (f * q)) : by rw [mul_add]
  ... =  derivative (f * p) + derivative (f * q) : derivative_add
  ... =  (derivative f * p + f * derivative p) + (derivative f * q + f * derivative q) : by simp [a, a_1]
  ... =  (derivative f * p + derivative f * q) + (f * derivative p + f * derivative q) : by simp
  ... =  derivative f * (p + q) + (f * (derivative p + derivative q)) : by simp [mul_add]
  --... =  derivative f * (p + q) + (f * (derivative (p + q))) : by rw [derivative_add]
  end -/ begin end
  /-
  begin simp [M], intros, 
    calc derivative (p * (q * f)) = derivative (p * (q * f)) : rfl
    ... = p * derivative (q * f) + (q * f) * derivative p : by rw [a]
    ... = p * (q * derivative f + f * derivative q) + (q * f) * derivative p : by rw [a_1]
    ... = p * (q * derivative f) + (p * derivative q + q * derivative p) * f : by simp [mul_add]
    ... = p * (q * derivative f) + (p * derivative q + q * derivative p ) * f : by simp
    ... = p * (q * derivative f) + (derivative (p * q)) * f : by rw [a]
    ... = p * (q * derivative f) + f * (derivative (p * q)) : by simp
   end-/ begin end
  )
  

/-  
  intro a, 
  simp [derivative_C],
  simp [mul_def],
  simp [derivative_sum2],



  simp [],
  simp [derivative],
  simp [C],
  simp [mul_def],


  simp [sum_single_index],
  simp [(sum_sum_index _  _)],
  simp [single],

  simp [derivative, derivative_single, derivative_sum, derivative._match_1 ],
  simp [derivative, mul_def],
  simp [derivative, derivative_sum,  mul_def, derivative_C]
  end

  _ 
  _ /- hier moet de M komen (λ g : polynomial α, ∀ f , derivative (f * g) = derivative f * g + f * derivative g )-/
 -- _ 
---/




end semiring

#print prefix polynomial.derivative

instance [comm_semiring α] : comm_semiring (polynomial α) := finsupp.comm_semiring
instance [ring α] : ring (polynomial α) := finsupp.ring
instance [comm_ring α] : comm_ring (polynomial α) := finsupp.comm_ring

end polynomial
