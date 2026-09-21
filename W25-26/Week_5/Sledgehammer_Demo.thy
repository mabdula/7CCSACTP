theory Sledgehammer_Demo
  imports Complex_Main
begin

(*===================================================================*)
(* Example 1: Algebraic Distributivity & Rearrangement               *)
(* Source: Week 2 Lecture Tutorial (Distrib_Eg.thy)                  *)
(*===================================================================*)

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

(* New Proof (Week 5): 1-line proof found automatically by Sledgehammer *)
lemma distrib_sledgehammer: "((x::nat) + y) * (a + b) = a * x + a * y + b * x + b * y"
  by (metis add.assoc add.commute distrib_left distrib_right mult.commute)


(*===================================================================*)
(* Example 2: Step Case in Tail-Recursive Reverse Generalisation     *)
(* Source: Week 3 Exercise Sheet (Exercise 2, Week_3_sol.thy)         *)
(*===================================================================*)

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
  have 1: "rev' xs (a # ys) = (rev' xs []) @ (a # ys)"
    apply (subst Cons)
    ..
  have 2: "rev' xs [a] = (rev' xs []) @ [a]"
    apply (subst Cons)
    ..
  show ?case
    using 1 2
    by simp
qed

(* New Proof (Week 5): Sledgehammer discharges the step case directly *)
lemma rev'_append_sledgehammer: "rev' xs ys = (rev' xs []) @ ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (metis Cons.IH append.assoc append_Cons append_Nil rev'.simps)
qed

end
