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

fun list_sum :: "nat list \<Rightarrow> nat" where
  "list_sum [] = 0"
| "list_sum (x#xs) = x + list_sum xs"

definition list_sum' :: "nat list \<Rightarrow> nat" where
  "list_sum' xs \<equiv> fold (+) xs 0"

lemma "list_sum xs = list_sum' xs"
  sorry

text \<open>\Exercise{Tail recursive \<open>reverse\<close>}
In Isabelle, there is the reverse function @{const rev}, which, given a list, computes another list
with the same elements but in reverse order.
Take a look into its definition:
\<close>

thm rev.simps  

text \<open>
  Recall tail recursion: a function is tail recursive if in all recursive calls it does not call 
  anything after itself.
  For instance, the implementation of @{const rev} in Isabelle is not tail recursive, because it calls
  @{const append} after it calls @{const rev} in the second equation.
  
  Write an alternative implementation of the reverse function that is tail recursive.

  Hint: recall that you can most of the time derive a tail recursive function using an accumulator
        argument.
\<close>  

fun rev'::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev' [] acc = acc"
| "rev' (x #xs) acc = rev' xs (x # acc)"

fun rev_tr::"'a list \<Rightarrow> 'a list" where
  "rev_tr xs = rev' xs []"

text \<open>Show that the two implementations are equivalent.\<close>

lemma "rev_tr xs = rev xs"
  sorry

(*<*)
end
(*>*)