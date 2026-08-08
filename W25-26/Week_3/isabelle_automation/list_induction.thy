theory list_induction
  imports Main "../list_recursion/list_recursion"
begin


text \<open>Simplification\<close>
lemma "(5::nat) = 2 + 3"
  apply simp.

thm length_append


lemma "length (xs @ ys @ zs) = length xs + length ys + length zs"
  apply (simp  del: length_append add: length_append)
  sorry

fun List_set::"'a list \<Rightarrow> 'a set" where
  "List_set [] = {}"
| "List_set (x # xs) = insert x (List_set xs)"


thm Max_list'.simps

lemma "x \<in> List_set xs \<Longrightarrow> x \<le> Max_list' xs"
proof (induction xs)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a xs)
  show ?case
  proof(cases "x = a")
    case True
    then show ?thesis
      by simp
  next
    case False
    then show ?thesis
      using Cons.IH Cons(2)
      by simp
  qed 
qed

text \<open>auto\<close>

lemma "x \<in> List_set xs \<Longrightarrow> x \<le> Max_list' xs"
proof (induction xs)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a xs)
  show ?case
    using  Cons(2)
    by (auto dest: Cons.IH)
qed

lemma "x \<in> List_set xs \<Longrightarrow> x \<le> Max_list' xs"
  apply (induction xs)
  apply auto
  .


lemma lemma4: "a \<le> b \<Longrightarrow> Suc a \<le> Suc b"
  apply(induction a)
  apply auto
  .

find_theorems "0 \<le> ?a"

lemma "(x::nat) - y \<le> x"
  apply(induction x)
  apply auto
  .

text \<open>fastforce\<close>

lemma "x \<in> List_set xs \<Longrightarrow> x \<le> Max_list' xs"
  apply (induction xs)
  apply fastforce
  apply fastforce
  .


end