
universe u

variable {α : Type u}
variable [integral_domain α ]


structure has_norm (α : Type u) [integral_domain α]: Type u:= -- Can this be made into a  type class?
(norm : α  → nat) (h1 : norm 0 = 0) -- (h2 : ∀ a : α, a ≠ 0 → norm a ≠ 0)


class euclidian_domain (α : Type u) extends integral_domain α :=
(x : has_norm α ) (h: ∀ a b : α, b ≠ 0 → (∃ q : α, ∃ r : α,( (a = q * b + r) ∧ ((r = 0)  ∨  ( (x.norm r ) < (x.norm b)) )  ) ) )

