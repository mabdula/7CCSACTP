(*<*)
theory Week_3
imports Main
begin
(*>*)
text \<open>\ExerciseSheet{8}{}\<close>

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
  (*<*)  
  where
    "list_sum [] = 0"
  | "list_sum (x#xs) = x + list_sum xs"  
    (*>*)  


(*
  Mention that definition can be used for non-recursive functions. It does not add the function
  definition to the simp set.
*)
definition list_sum' :: "nat list \<Rightarrow> nat"
  (*<*)  
  where "list_sum' xs \<equiv> fold (+) xs 0"
  (*>*)    

(*<*)    

text \<open>These are three equivalent proofs of the same lemma. The first one only uses substitution in
      an apply script, the second uses Isar equational reasoning, and the third uses automation. The
      second one looks like what you would write on pen-and-paper.\<close>

lemma "\<And>acc. acc + list_sum xs = fold (+) xs acc"
proof(induction xs)
  case Nil
  thm list_sum.simps(1)
  thm fold.simps(1)
  show ?case
    apply(subst list_sum.simps(1))
    apply(subst fold.simps(1))
    apply(subst add_0_right)
    ..
next
  case (Cons a xs)

  show ?case
    apply(subst list_sum.simps(2))
    apply(subst fold.simps(2))
    apply(subst add.assoc[symmetric])
    apply(subst add.commute)
    apply(subst Cons.IH)
    ..  
qed

lemma "\<And>acc. acc + list_sum xs = fold (+) xs acc"
proof(induction xs)
  case Nil
  have "acc + list_sum [] = acc + 0"
    apply(subst list_sum.simps(1))
    ..
  also have "... = acc"
    apply(subst add_0_right)
    ..
  also have "... = fold (+) [] acc"
    apply(subst fold.simps(1))
    ..
  finally show ?case
    .
next
  case (Cons a xs)

  have "acc + list_sum (a#xs) = acc + (a + list_sum xs)"
    apply(subst list_sum.simps(2))
    ..
  also have "... = acc + a + list_sum xs"
    apply(subst add.assoc[symmetric])
    ..
  also have "... = a + acc + list_sum xs"
    apply(subst add.commute)
    ..
  also have "... = fold (+) xs (a+acc)"
    apply(subst Cons.IH)
    ..
  also have "... = fold (+) (a#xs) acc"
    apply(subst fold.simps(2)[symmetric])
    ..

  finally show ?case
    .
qed

lemma aux: "\<And>a. fold (+) xs a = list_sum xs + a"  
  by (induction xs) auto
(*>*)    

lemma "list_sum xs = list_sum' xs"
  (*<*)    
  by (simp add: aux list_sum'_def)
  (*>*)    

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

(*<*)
fun rev'::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev' [] acc = acc"
| "rev' (x #xs) acc = rev' xs (x # acc)"
(*>*)


(*show definition vs fun*)
fun rev_tr::"'a list \<Rightarrow> 'a list" where
(*<*)
  "rev_tr xs = rev' xs []"
(*>*)

text \<open>Show that the two implementations are equivalent.\<close>

(*<*)
(*Discuss how the automation fails because the induction hypothesis can be applied infinitely many
times*)
lemma rev'_append: "rev' xs ys = (rev' xs []) @ ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case 
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
(*>*)
 
lemma "rev_tr xs = rev xs"
(*<*)
proof(induction xs)
  case Nil
  then show ?case
    by auto
next
  case (Cons a xs)
  then show ?case
    apply simp
    apply(subst rev'_append)
    by auto
qed
(*>*)

(*<*)
end
(*>*)