text \<open>\section*{Proofs by Mathematical Induction on Lists}\<close>

theory List_Induction
  imports Main
begin
text \<open>In analogy to natural numbers, facts about lists can be proved by induction. However, instead
      of the base case being \<open>0\<close>, we use the empty list \<open>[]\<close>, and the step case is proved for \<open>x # xs\<close>
      instead of \<open>Suc n\<close>. The induction principle is 

  \[\frac{P\; [];\;\;\; [\forall\; x.\; P\; xs;\; \Longrightarrow\; P\; x#xs]}{P\; t}.\]

The following is a proof of the associativity of Isabelle's list append \<open>@\<close>. Reproduce it and note
base case and the step-case. In the base case we almost always unfold defining equations and in the
step-case we always manipulate the goal until the induction hypothesis is applicable.
\<close> 

thm append.simps

lemma "(xs @ ys) @ zs = (xs @ (ys @ zs))"
proof(induction xs)
  case Nil
  have "([] @ ys) @ zs = ys @ zs"
    apply (subst append.simps)
    ..
  also have "... = ([] @ ( ys @ zs))"
    apply(subst append.simps)
    ..
  finally show ?case
    .
next
  case (Cons x xs)
  have "((x # xs) @ ys) @ zs = (x # (xs @ ys)) @ zs"
    apply (subst append.simps)
    ..

  also have "... = x # ((xs @ ys) @ zs)"
    apply(subst append.simps)
    ..
  also have "... = x # (xs @ (ys @ zs))"
    apply(subst Cons.IH)
    ..
  also have "... = (x # xs) @ ys @ zs"
    apply(subst append.simps)
    ..
  finally show ?case
    .
qed


end