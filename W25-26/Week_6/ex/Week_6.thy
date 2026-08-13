(*<*)
theory Week_6
  imports Main "HOL-Library.Multiset"
begin
(*>*)

text \<open>\ExerciseSheet{6}{Algorithm Correctness \& Locales}\<close>

text \<open>
  Important Note: Please bring a laptop with Isabelle/HOL installed to the Large Group Tutorial (LGT).
  Performing these proofs in Isabelle will be an integral part of the tutorial.
\<close>


text \<open>\Exercise{In-place Merge Sort / Multiset Preservation}\<close>

text \<open>
  Recall the merge sort function \<open>msort\<close> discussed in the lecture, which splits a list into balanced
  halves, recursively sorts them, and merges the sorted results.

  Prove that \<open>msort\<close> preserves the elements of the input list (i.e.\ it is in-place with respect to
  element multiset equality).
\<close>

fun merge :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge [] ys = ys"
| "merge xs [] = xs"
| "merge (x#xs) (y#ys) = (if x \<le> y then x # merge xs (y#ys) else y # merge (x#xs) ys)"

fun msort :: "'a::linorder list \<Rightarrow> 'a list" where
  "msort [] = []"
| "msort [x] = [x]"
| "msort xs = (let n = length xs div 2 in merge (msort (take n xs)) (msort (drop n xs)))"

text \<open>Prove that merging two lists preserves their combined multiset of elements.\<close>

lemma mset_merge: "mset (merge xs ys) = mset xs + mset ys"
  sorry

text \<open>Prove that merge sort preserves the multiset of elements from the original list.\<close>

lemma mset_msort: "mset (msort xs) = mset xs"
  sorry


text \<open>\Exercise{Abstract Data Types via Locales: Map ADT}\<close>

text \<open>
  In the lecture, we introduced Isabelle \emph{locales} to formalise an Abstract Data Type (ADT) for sets.
  In this exercise, you will define a parameterised locale for a \emph{Map ADT} that maps keys of type \<open>'k\<close>
  to values of type \<open>'v\<close>.

  The locale should declare:
   1. An empty map constant \<open>empty_map\<close>,
   2. An update operation \<open>update :: 'k \<Rightarrow> 'v \<Rightarrow> 'm \<Rightarrow> 'm\<close>, and
   3. A lookup operation \<open>lookup :: 'k \<Rightarrow> 'm \<Rightarrow> 'v option\<close>.

  It must enforce the standard lookup-after-update invariants as locale assumptions.
\<close>

locale Map_ADT =
  fixes empty_map :: "'m"
    and update :: "'k \<Rightarrow> 'v \<Rightarrow> 'm \<Rightarrow> 'm"
    and lookup :: "'k \<Rightarrow> 'm \<Rightarrow> 'v option"
  assumes lookup_empty: "lookup k empty_map = None"
      and lookup_update_same: "lookup k (update k v m) = Some v"
      and lookup_update_diff: "k \<ne> k' \<Longrightarrow> lookup k (update k' v m) = lookup k m"

text \<open>
  Prove that inserting a key-value pair and immediately overriding the same key yields the same lookup result.
\<close>

lemma (in Map_ADT) lookup_override:
  "lookup k (update k v2 (update k v1 m)) = Some v2"
  sorry

(*<*)
end
(*>*)
