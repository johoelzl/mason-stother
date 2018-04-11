#exit
example : (2 + 3) * 4 + 5 = 2 * 4 + 3 * 4 + 5 :=
begin
  rewrite [add_mul],
end

#check  @eq.subst ℕ _ _ _ (add_mul 2 3 4) (eq.refl ((2 + 3) * 4 + 5))

example : (2 + 3) * 4 + 5 = 2 * 4 + 3 * 4 + 5 :=
  have h1 : (2 + 3) * 4 + 5 = (2 + 3) * 4 + 5,
    from eq.refl _,
  have h2 : (2 + 3) * 4  = 2 * 4 + 3 * 4,
    from add_mul _ _ _,
  eq.subst (add_mul 2 3 4) (eq.refl ((2 + 3) * 4 + 5))

#check (eq.refl ((2 + 3) * 4 + 5))
#check (add_mul 2 3 4)

example : (2 + 3) * 4 + 5 = 2 * 4 + 3 * 4 + 5 :=
  have h1 : (2 + 3) * 4 + 5 = (2 + 3) * 4 + 5,
    from eq.refl _,
  eq.subst (add_mul 2 3 4) h1

example : (2 + 3) * 4 + 5 = 2 * 4 + 3 * 4 + 5 :=
  have h1 : (2 + 3) * 4 + 5 = (2 + 3) * 4 + 5,
    from eq.refl _,
  have h2 : (2 + 3) * 4  = 2 * 4 + 3 * 4,
    from add_mul _ _ _,
  eq.subst h2 h1
  
