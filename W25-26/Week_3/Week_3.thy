
theory Week_3
imports Main
begin

text \<open>\ExerciseSheet{3}{}\<close>

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
  
  (* TODO: complete this definition *)
  


(*
  Mention that definition can be used for non-recursive functions. It does not add the function
  definition to the simp set.
*)
definition list_sum' :: "nat list \<Rightarrow> nat"
  
  (* TODO: complete this definition *)
    

    

lemma "list_sum xs = list_sum' xs"
  
  sorry
    

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


(*show definition vs fun*)
fun rev_tr::"'a list \<Rightarrow> 'a list" where

  (* TODO: complete this definition *)


text \<open>Show that the two implementations are equivalent.\<close>


 
lemma "rev_tr xs = rev xs"

  sorry


end
