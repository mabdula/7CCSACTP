theory Sledgehammer_Demo
  imports Main
begin

(* Old Proof (Week 2): Manual step-by-step equational reasoning *)
lemma distrib_old: "((x::nat) + y) * (a + b) = a * x + a * y + b * x + b * y"
proof-
  have "(x + y) * (a + b) = (x + y) * a + (x + y) * b"
    apply (subst semiring_class.distrib_left)
    ..
  also have "... = a * (x + y) + (x + y) * b"
    apply (subst (1) mult.commute)
    ..
  also have "... = a * (x + y) + b * (x + y)"
    apply (subst (2) mult.commute)
    ..
  also have "... = a * x + a * y + b * (x + y)"
    apply (subst (1) semiring_class.distrib_left)
    ..
  also have "... = a * x + a * y + (b * x + b * y)"
    apply (subst (1) semiring_class.distrib_left)
    ..
  also have "... = a * x + a * y + b * x + b * y"
    apply (subst add.assoc[symmetric])
    ..
  finally show ?thesis
    .
qed

fun rev'::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev' [] acc = acc"
| "rev' (x # xs) acc = rev' xs (x # acc)"

(* Old Proof (Week 3): Manual formulation of intermediate lemmas *)
lemma rev'_append_old: "rev' xs ys = (rev' xs []) @ ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a xs)
  show ?case
qed

end
