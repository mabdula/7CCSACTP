
theory Week_3_sol
imports Main
begin

text \<open>\vspace{15ex}\ExerciseSheet{3}{}\<close>

text \<open>\paragraph{About these solutions.} Every Isabelle proof method (e.g.\ \<open>rule\<close>, \<open>simp\<close>),
      Isar keyword (e.g.\ \<open>have\<close>, \<open>also\<close>), attribute (e.g.\ \<open>OF\<close>, \<open>of\<close>) and method modifier
      (e.g.\ \<open>arbitrary:\<close>, \<open>simp add:\<close>) is explained in a short comment, marked ---, the first
      time it appears in the solutions, in sheet order from Week 1. Later uses are not explained
      again, so if you meet an unfamiliar construct, look for its first use in an earlier solution.
      Each proof is also labelled with its style; the module's preferred style is declarative (Isar),
      where every step states what it proves.\<close>


text \<open>\Exercise{Fold function}
  The fold function is a very generic function, that can be used to express 
  multiple other interesting functions over lists.
\<close>

text \<open>Have a look at Isabelle/HOL's standard function @{const \<open>fold\<close>}, defined as follows:\<close>

fun fold::"('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
"fold f [] acc = acc"
| "fold f (x #xs) acc = fold f xs (f x acc)"

text \<open>
  Write a function to compute the sum of the elements of a list. 
  Define two versions, one direct recursive definition, and one using fold.
  Show that both are equal.

  Hint: use automation!
\<close>  

fun list_sum :: "nat list \<Rightarrow> nat" 
    
  where
    "list_sum [] = 0"
  | "list_sum (x#xs) = x + list_sum xs"  
      


(*
  Mention that definition can be used for non-recursive functions. It does not add the function
  definition to the simp set.
*)
definition list_sum' :: "nat list \<Rightarrow> nat"
    
  where "list_sum' xs \<equiv> fold (+) xs 0"
      

    

text \<open>These are three proofs of the key fact relating \<open>fold\<close> and \<open>list_sum\<close>, in different styles.
      The first is an apply script using only substitutions, the second is a declarative Isar proof
      with equational reasoning, and the third uses automation. In this module we prefer the
      declarative style: every step states what it proves, so the proof can be read and checked
      without running Isabelle, like a pen-and-paper proof.\<close>

lemma "fold (+) xs acc = acc + list_sum xs"
proof(induction xs arbitrary: acc)
  \<comment> \<open>Style: apply-style (procedural), shown only for contrast; generalised list induction (new). Each case is a
     sequence of \<open>subst\<close> commands, and the intermediate goals are visible only in Isabelle.\<close>
  case Nil
  show ?case
    apply(subst fold.simps(1))
    apply(subst list_sum.simps(1))
    apply(subst add_0_right)
    ..
next
  case (Cons a xs)
  show ?case
    apply(subst fold.simps(2))
    apply(subst Cons.IH)
    apply(subst list_sum.simps(2))
    apply(subst add.assoc[symmetric])
    apply(subst add.commute)
    ..
qed

lemma "fold (+) xs acc = acc + list_sum xs"
proof(induction xs arbitrary: acc)
  \<comment> \<open>Style: declarative (Isar), the preferred style; the same \<open>subst\<close> steps as above, but each
     intermediate equation is stated explicitly with \<open>also have \<dots> finally\<close>.\<close>
  case Nil
  have "fold (+) [] acc = acc"
    apply(subst fold.simps(1))
    ..
  also have "... = acc + 0"
    apply(subst add_0_right)
    ..
  also have "... = acc + list_sum []"
    apply(subst list_sum.simps(1))
    ..
  finally show ?case
    .
next
  case (Cons a xs)
  have "fold (+) (a#xs) acc = fold (+) xs (a+acc)"
    apply(subst fold.simps(2))
    ..
  also have "... = a + acc + list_sum xs"
    apply(subst Cons.IH)
    ..
  also have "... = acc + a + list_sum xs"
    apply(subst add.commute)
    ..
  also have "... = acc + (a + list_sum xs)"
    apply(subst add.assoc[symmetric])
    ..
  also have "... = acc + list_sum (a#xs)"
    apply(subst list_sum.simps(2))
    ..
  finally show ?case
    .
qed

lemma aux: "fold (+) xs acc = acc + list_sum xs"
proof(induction xs arbitrary: acc)
  \<comment> \<open>Style: declarative (Isar) skeleton, each case closed by automation (\<open>auto\<close>, new): shortest,
     but the individual reasoning steps are hidden inside \<open>auto\<close>.\<close>
  case Nil
  show ?case
    by auto
    \<comment> \<open>\<open>by m\<close> proves the goal in one step with method \<open>m\<close>, which must solve it completely.\<close>
    \<comment> \<open>\<open>auto\<close> tries to solve all goals automatically, combining simplification with logical reasoning.\<close>
next
  case (Cons x xs)
  show ?case
    using Cons.IH
    by auto
qed


lemma "list_sum xs = list_sum' xs"
  
  by (simp add: aux list_sum'_def)
  \<comment> \<open>\<open>simp\<close> rewrites the goal with simplification rules such as function equations; \<open>add:\<close>
     supplies extra rules, here \<open>aux\<close> and the definition of \<open>list_sum'\<close>.\<close>
  \<comment> \<open>Style: declarative one-step proof: \<open>simp\<close> with extra lemmas and a definition (new).\<close>
  

text \<open>\Exercise{Tail recursive \<open>reverse\<close>}
In Isabelle, there is the reverse function @{const rev}, which, given a list, computes another list
with the same elements but in reverse order.
Take a loot into its definition:
\<close>

thm rev.simps  

text \<open>
  Recall tail recursion: a function is tail recursive if in all recursive calls it does not call 
  anything after itself\footnote{See \url{https://en.wikipedia.org/wiki/Tail_call.} for a quick review.}.
  For instance, the implementaion of @{const rev} in Isabelle is not tail recursive, because it calls
  @{const append} after it calls @{const rev} in the second equation.
  
  Write an alternative implementation of the reverse function that is tail recursive.

  Hint: recall that you can most of the times derive a tail recursive function using an accumulator
        argument. 

\<close>  


fun rev'::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev' [] acc = acc"
| "rev' (x #xs) acc = rev' xs (x # acc)"



(*show definition vs fun*)
fun rev_tr::"'a list \<Rightarrow> 'a list" where

  "rev_tr xs = rev' xs []"


text \<open>Show that the two implementations are equivalent.\<close>


(*Discuss how the automation fails because the induction hypothesis can be applied infinitely many
times*)
lemma rev'_append: "rev' xs ys = (rev' xs []) @ ys"
proof (induction xs arbitrary: ys)
  \<comment> \<open>Style: declarative (Isar); generalised list induction (\<open>arbitrary\<close>); \<open>subst\<close> with the IH; \<open>auto\<close>/\<open>simp\<close>.\<close>
  case Nil
  then show ?case
    \<comment> \<open>\<open>then\<close> passes the facts just obtained (here those of the current case) to the next
       statement, like \<open>using\<close>.\<close>
    by auto
next
  case (Cons a xs)
  have 1: "rev' xs (a # ys) = (rev' xs []) @ (a # ys)"
    apply(subst Cons)
    ..
  have 2: "rev' xs [a] = (rev' xs []) @ [a]"
    apply(subst Cons)
    ..
  show ?case
    using 1 2
   by simp
qed

 
lemma "rev_tr xs = rev xs"

proof(induction xs)
  \<comment> \<open>Style: declarative (Isar); list induction; equational reasoning with \<open>simp\<close>, \<open>subst\<close> and \<open>auto\<close>.\<close>
  case Nil
  then show ?case
    by auto
next
  case (Cons a xs)
  have "rev_tr (a # xs) = rev' xs [a]"
    by simp
  also have "... = rev' xs [] @ [a]"
    apply(subst rev'_append)
    ..
  also have "... = rev (a # xs)"
    using Cons.IH
    by auto
  finally show ?case
    .
qed



end
