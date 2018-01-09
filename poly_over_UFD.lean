import  .Sup_fin data.finsupp order.lattice data.nat.cast .euclidean_domain unique_factorization_domain
import .to_finsupp poly
universes u v w

noncomputable theory

open classical set function finsupp lattice
local attribute [instance] prop_decidable
local attribute [instance] finsupp.to_comm_semiring
local attribute [instance] finsupp.to_semiring
local infix ^ := monoid.pow

namespace polynomial
variables {α : Type u} {a a' a₁ a₂ : α} --{n m : ℕ} --do we want n and m?



instance {α : Type u} [unique_factorization_domain α]: unique_factorization_domain (polynomial α) :=
{ fac := sorry,
  unique := sorry,
  .. polynomial.integral_domain}

  end polynomial