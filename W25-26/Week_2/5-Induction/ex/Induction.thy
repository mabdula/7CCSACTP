text \<open>\section*{Mathematical Induction in Isabelle/HOL}\<close>

theory Induction
  imports Main
begin

text \<open>The following proof shows how perform an induction on natural numbers in Isabelle. After
      reproducing it, take a close look in the base case and into the step case, including the
      induction hypothesis.
      In the base case, one usually tries to use previously proved facts or just unfold defining
      equations.
      In the step case, one tries to manipulate the goal until the induction hypothesis is applicable,
      in this case we can substitute it. \<close>

lemma add_0_left: "(0::nat) + x = x"
  using add_0
  .

lemma Suc_add_2: "x + Suc y = Suc (x + y)"
  using add_Suc_right
  .

lemma "(x::nat) + y = y + x"
proof(induction y)
  case 0
  have "x + 0 = x"
    apply(subst add_0_right)
    ..
  also have "... = 0 + x"
    apply(subst add_0_left)
    ..
  finally show ?case
    .
next
  case (Suc y)

  have "x + Suc y = Suc (x + y)"
    apply(subst Suc_add_2)
    ..

  also have "... = Suc (y + x)"
    apply(subst Suc.IH)
    ..
  also have "... = (Suc y) + x"
    apply(subst add_Suc)
    ..

  finally show ?case
    .
qed


end