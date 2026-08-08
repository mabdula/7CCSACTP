text \<open>\section*{Substitution in Isabelle/HOL}\<close>

theory Subst
  imports Main
begin

lemma
  "((x::nat) + y) * (a + b) = x * a + y * a + x * b + y * b"
proof-
  have 1: "(x + y) * (a + b) = (x + y) * a + (x + y) * b"
    apply(subst distrib_left)
    ..
  also have 2: "... = x * a + y * a + (x + y) * b"
    apply(subst distrib_right) 
    ..
  also have 3: "... = x * a + y * a + (x * b + y * b)"
    apply(subst distrib_right)
    ..
  also have 4: "... = x * a + y * a + x * b + y * b"
    apply(subst add.assoc[symmetric])
    ..
  finally show ?thesis
    .
qed


end