
theory Week_6
  imports Main "HOL-Library.Multiset"
begin


text \<open>\ExerciseSheet{6}{Correctness and Running Time Analysis}\<close>

text \<open>
  Important Note: Please bring a laptop with Isabelle/HOL installed to the Large Group Tutorial (LGT).
  Performing these proofs in Isabelle will be an integral part of the tutorial.
\<close>


text \<open>\Exercise{Merge Sort}\<close>

text \<open>
  Consider the following version of merge sort: it splits a list into two halves, sorts them
  recursively and merges the results. Unlike the version in the lecture, it treats the empty and the
  one-element list by separate equations.

  \paragraph{(a) Elements.} Prove that \<open>msort\<close> preserves the elements of its input: the output has
  the same multiset of elements as the input.
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

text \<open>
  \paragraph{(b) Sortedness.} Part (a) showed that \<open>msort\<close> keeps the elements of its input. The other half of its
  correctness is that its output is sorted. Prove the following lemmas, first pen-and-paper, then
  in Isabelle.
\<close>

lemma set_merge: "set (merge xs ys) = set xs \<union> set ys"
  sorry

lemma sorted_merge: "sorted (merge xs ys) \<longleftrightarrow> sorted xs \<and> sorted ys"
  sorry

lemma sorted_msort: "sorted (msort xs)"
  sorry

text \<open>\paragraph{Hints:}
 1. All three lemmas are proved by computation induction.

 2. \<open>sorted (x # ys)\<close> requires \<open>x\<close> to be at most every element of \<open>ys\<close>; this is why
    \<open>sorted_merge\<close> needs \<open>set_merge\<close>.
\<close>

text \<open>\Exercise{Running Time}\<close>

text \<open>
  Consider list append, the naive reverse function, which appends each element at the end, and the
  tail-recursive reverse function from Week 3:
\<close>

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app [] ys = ys"
| "app (x # xs) ys = x # app xs ys"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []"
| "reverse (x # xs) = app (reverse xs) [x]"

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] acc = acc"
| "itrev (x # xs) acc = itrev xs (x # acc)"

text \<open>
 \paragraph{(a)} Using the counting rules from the lecture, with all constants reduced to 1 (count
  the time functions of the defined functions that are called, plus 1 for the call itself), define
  the time functions \<open>t_app\<close>, \<open>t_reverse\<close> and \<open>t_itrev\<close> in Isabelle.

 \paragraph{(b)} Prove, first pen-and-paper and then in Isabelle, that \<open>reverse\<close> takes quadratic and
  \<open>itrev\<close> linear time:
  \<open>t_reverse xs \<le> (length xs + 1)^2\<close> and \<open>t_itrev xs acc = length xs + 1\<close>.

\paragraph{Hints:}
 1. First prove \<open>t_app xs ys = length xs + 1\<close> and \<open>length (reverse xs) = length xs\<close>.

 2. For \<open>t_itrev\<close>, think about which variable the induction hypothesis must be generalised over.

 3. See Section 1.2 (Running Time) of the FDS book.
\<close>

text \<open>
  \paragraph{(c) Comparisons.} For sorting algorithms that compare list elements, a common cost
  measure is the number of comparisons between list elements, instead of all function calls. The
  following functions count the comparisons (the tests \<open>x \<le> y\<close>) that \<open>merge\<close> and \<open>msort\<close> from
  Exercise 6.1 make:
\<close>

fun c_merge :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> nat" where
  "c_merge [] ys = 0"
| "c_merge xs [] = 0"
| "c_merge (x#xs) (y#ys) = 1 + (if x \<le> y then c_merge xs (y#ys) else c_merge (x#xs) ys)"

fun c_msort :: "'a::linorder list \<Rightarrow> nat" where
  "c_msort [] = 0"
| "c_msort [x] = 0"
| "c_msort xs = (let n = length xs div 2; ys = take n xs; zs = drop n xs
                 in c_msort ys + c_msort zs + c_merge (msort ys) (msort zs))"

text \<open>
  Prove, first pen-and-paper and then in Isabelle, that sorting a list of length \<open>2^k\<close> takes at
  most \<open>k * 2^k\<close> comparisons.
\<close>

lemma c_merge_ub: "c_merge xs ys \<le> length xs + length ys"
  sorry

lemma length_msort: "length (msort xs) = length xs"
  sorry

lemma c_msort_le: "length xs = 2 ^ k \<Longrightarrow> c_msort xs \<le> k * 2 ^ k"
  sorry

text \<open>\paragraph{Hints:}
 1. \<open>c_merge_ub\<close> and \<open>length_msort\<close> are proved by computation induction; \<open>length_msort\<close> needs
    \<open>length (merge xs ys) = length xs + length ys\<close>.

 2. Prove \<open>c_msort_le\<close> by induction on \<open>k\<close>, generalising over \<open>xs\<close>. In the step case, both
    halves of \<open>xs\<close> have length \<open>2^k\<close>.

 3. The number of comparisons of merge sort is analysed in Chapter 2 of the FDS book.
\<close>

text \<open>\Exercise{Bottom-Up Merge Sort}\<close>

text \<open>
  Bottom-up merge sort does not split the list. It starts from singleton lists and repeatedly merges
  adjacent pairs of lists until a single list is left.
\<close>

fun merge_adj :: "('a::linorder) list list \<Rightarrow> 'a list list" where
  "merge_adj [] = []"
| "merge_adj [xs] = [xs]"
| "merge_adj (xs # ys # zss) = merge xs ys # merge_adj zss"

text \<open>Isabelle needs the following lemma to show that \<open>merge_all\<close> below terminates.\<close>

lemma length_merge_adjacent[simp]: "length (merge_adj xss) = (length xss + 1) div 2"
  by (induction xss rule: merge_adj.induct) auto

fun merge_all :: "('a::linorder) list list \<Rightarrow> 'a list" where
  "merge_all [] = []"
| "merge_all [xs] = xs"
| "merge_all xss = merge_all (merge_adj xss)"

definition msort_bu :: "('a::linorder) list \<Rightarrow> 'a list" where
  "msort_bu xs = merge_all (map (\<lambda>x. [x]) xs)"

text \<open>\paragraph{(a) Correctness.} Prove that \<open>msort_bu\<close> preserves the elements of its input and
  that its output is sorted, first pen-and-paper, then in Isabelle.\<close>

lemma mset_msort_bu: "mset (msort_bu xs) = mset xs"
  sorry

lemma sorted_msort_bu: "sorted (msort_bu xs)"
  sorry

text \<open>\paragraph{Hints:}
 1. Neither lemma follows by induction on \<open>xs\<close> directly. First prove lemmas about \<open>merge_adj\<close> and
    \<open>merge_all\<close> on an arbitrary list of lists \<open>xss\<close>: that they preserve \<open>mset (concat xss)\<close>, and
    that they produce sorted lists if all lists in \<open>xss\<close> are sorted.

 2. Prove those lemmas by computation induction, with \<open>merge_adj.induct\<close> and \<open>merge_all.induct\<close>.
\<close>

text \<open>\paragraph{(b) Running time.} We count comparisons as in Exercise 6.2(c):\<close>

fun c_merge_adj :: "('a::linorder) list list \<Rightarrow> nat" where
  "c_merge_adj [] = 0"
| "c_merge_adj [xs] = 0"
| "c_merge_adj (xs # ys # zss) = c_merge xs ys + c_merge_adj zss"

fun c_merge_all :: "('a::linorder) list list \<Rightarrow> nat" where
  "c_merge_all [] = 0"
| "c_merge_all [xs] = 0"
| "c_merge_all xss = c_merge_adj xss + c_merge_all (merge_adj xss)"

definition c_msort_bu :: "('a::linorder) list \<Rightarrow> nat" where
  "c_msort_bu xs = c_merge_all (map (\<lambda>x. [x]) xs)"

text \<open>Prove that sorting a list of length \<open>2^k\<close> takes at most \<open>k * 2^k\<close> comparisons.\<close>

lemma c_msort_bu: "length xs = 2 ^ k \<Longrightarrow> c_msort_bu xs \<le> k * 2 ^ k"
  sorry

text \<open>\paragraph{Hints:}
 1. Use \<open>c_merge_ub\<close> from Exercise 6.2(c).

 2. If all lists in \<open>xss\<close> have length \<open>m\<close>, then \<open>c_merge_adj xss \<le> m * length xss\<close>; if moreover
    \<open>length xss\<close> is even, all lists in \<open>merge_adj xss\<close> have length \<open>2 * m\<close>.

 3. Generalise the statement to \<open>c_merge_all\<close>: if all lists in \<open>xss\<close> have length \<open>m\<close> and
    \<open>length xss = 2^k\<close>, then \<open>c_merge_all xss \<le> m * k * 2^k\<close>. Prove it by computation induction
    (\<open>c_merge_all.induct\<close>), generalising over \<open>k\<close> and \<open>m\<close>.
\<close>


end

