#exit -- currently not used

import poly
import euclidean_domain
import unique_factorization_domain
import data.finsupp
import algebraically_closed_field
import poly_over_UFD


noncomputable theory
local infix ^ := monoid.pow
local notation `d[`a`]` := polynomial.derivative a
local notation Σ := finset.sum
local notation Π := finset.prod
local notation `Π₀` := finsupp.prod
local notation `~`a:=polynomial a

open polynomial
open classical
local attribute [instance] prop_decidable


-- TODO: there is some problem with the module instances for module.to_add_comm_group ...
-- force ring.to_add_comm_group to be stronger
attribute [instance] ring.to_add_comm_group

universe u


variable {α : Type u}

def rel_prime [comm_semiring α][has_gcd α] (a b : α) := is_unit (gcd a b)

variable [field α]

--Def rad p: the product of primes dividing p: Sander's notes
def rad (p : polynomial α) : polynomial α  := 