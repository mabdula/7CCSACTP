text \<open>\section*{Mathematical Induction in Isabelle/HOL}\<close>

theory Induction
  imports Main
begin

lemma add_0_left: "(0::nat) + x = x"
  sorry

lemma Suc_add_2: "x + Suc y = Suc (x + y)"
  sorry


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