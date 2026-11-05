
theory Week_7
  imports Main
begin


text \<open>\ExerciseSheet{7}{Abstract Data Types \& Locales}\<close>

text \<open>
  Important Note: Please bring a laptop with Isabelle/HOL installed to the Large Group Tutorial (LGT).
  Performing these proofs in Isabelle will be an integral part of the tutorial.
\<close>

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
      and lookup_update_diff: "k \<noteq> k' \<Longrightarrow> lookup k (update k' v m) = lookup k m"

text \<open>
  Prove that inserting a key-value pair and immediately overriding the same key yields the same lookup result.
\<close>

lemma (in Map_ADT) lookup_override:
  "lookup k (update k v2 (update k v1 m)) = Some v2"
  sorry


end

