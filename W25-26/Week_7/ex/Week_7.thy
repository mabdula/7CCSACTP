
theory Week_7
  imports Complex_Main
begin


text \<open>\ExerciseSheet{7}{Balanced Search Trees: 2-3 Trees}\<close>

text \<open>
  Important Note: Please bring a laptop with Isabelle/HOL installed to the Large Group Tutorial (LGT).
  Performing these proofs in Isabelle will be an integral part of the tutorial.
\<close>

text \<open>
  In this sheet we use the 2-3 trees from the lecture: their height, the structural invariant
  \<open>complete\<close>, and their in-order traversal.
\<close>

datatype 'a tree23 = Leaf
  | Node2 "'a tree23" 'a "'a tree23"
  | Node3 "'a tree23" 'a "'a tree23" 'a "'a tree23"

fun height :: "'a tree23 \<Rightarrow> nat" where
  "height Leaf = 0"
| "height (Node2 l _ r) = max (height l) (height r) + 1"
| "height (Node3 l _ m _ r) = max (height l) (max (height m) (height r)) + 1"

text \<open>
  HOL already has a constant \<open>complete\<close> (for complete metric spaces); \<open>hide_const\<close> hides it,
  so that we can use the name for 2-3 trees.
\<close>

hide_const (open) Topological_Spaces.complete

fun complete :: "'a tree23 \<Rightarrow> bool" where
  "complete Leaf = True"
| "complete (Node2 l _ r) = (height l = height r \<and> complete l \<and> complete r)"
| "complete (Node3 l _ m _ r) =
     (height l = height m \<and> height m = height r \<and> complete l \<and> complete m \<and> complete r)"

fun inorder :: "'a tree23 \<Rightarrow> 'a list" where
  "inorder Leaf = []"
| "inorder (Node2 l a r) = inorder l @ a # inorder r"
| "inorder (Node3 l a m b r) = inorder l @ a # inorder m @ b # inorder r"

text \<open>
  Insertion, as in the lecture. HOL already has a function \<open>insert\<close>, which inserts an element
  into a set; \<open>hide_const\<close> hides it, so that we can use the name for 2-3 trees.
\<close>

datatype 'a up\<^sub>i = Eq\<^sub>i "'a tree23" | Of "'a tree23" 'a "'a tree23"

fun tree\<^sub>i :: "'a up\<^sub>i \<Rightarrow> 'a tree23" where
  "tree\<^sub>i (Eq\<^sub>i t) = t"
| "tree\<^sub>i (Of l a r) = Node2 l a r"

fun ins :: "'a::linorder \<Rightarrow> 'a tree23 \<Rightarrow> 'a up\<^sub>i" where
  "ins x Leaf = Of Leaf x Leaf"
| "ins x (Node2 l a r) =
     (if x < a then (case ins x l of
                       Eq\<^sub>i l' \<Rightarrow> Eq\<^sub>i (Node2 l' a r)
                     | Of l1 b l2 \<Rightarrow> Eq\<^sub>i (Node3 l1 b l2 a r)) else
      if x > a then (case ins x r of
                       Eq\<^sub>i r' \<Rightarrow> Eq\<^sub>i (Node2 l a r')
                     | Of r1 b r2 \<Rightarrow> Eq\<^sub>i (Node3 l a r1 b r2))
      else Eq\<^sub>i (Node2 l a r))"
| "ins x (Node3 l a m b r) =
     (if x < a then (case ins x l of
                       Eq\<^sub>i l' \<Rightarrow> Eq\<^sub>i (Node3 l' a m b r)
                     | Of l1 c l2 \<Rightarrow> Of (Node2 l1 c l2) a (Node2 m b r)) else
      if x = a then Eq\<^sub>i (Node3 l a m b r) else
      if x < b then (case ins x m of
                       Eq\<^sub>i m' \<Rightarrow> Eq\<^sub>i (Node3 l a m' b r)
                     | Of m1 c m2 \<Rightarrow> Of (Node2 l a m1) c (Node2 m2 b r)) else
      if x = b then Eq\<^sub>i (Node3 l a m b r)
      else (case ins x r of
              Eq\<^sub>i r' \<Rightarrow> Eq\<^sub>i (Node3 l a m b r')
            | Of r1 c r2 \<Rightarrow> Of (Node2 l a m) b (Node2 r1 c r2)))"

hide_const insert

definition insert :: "'a::linorder \<Rightarrow> 'a tree23 \<Rightarrow> 'a tree23" where
  "insert x t = tree\<^sub>i (ins x t)"

text \<open>\Exercise{Insertion Preserves Completeness}\<close>

text \<open>
  We use the following function, which returns the height of a result of \<open>ins\<close>:
\<close>

fun h\<^sub>i :: "'a up\<^sub>i \<Rightarrow> nat" where
  "h\<^sub>i (Eq\<^sub>i t) = height t"
| "h\<^sub>i (Of l a r) = height l"

text \<open>
  Prove that insertion preserves completeness, first pen-and-paper, then in Isabelle.
\<close>

lemma complete_insert: "complete t \<Longrightarrow> complete (insert a t)"
  sorry

text \<open>\paragraph{Hints:}
 1. Induction on \<open>t\<close> directly for this statement gets stuck: in the step, you need to know that
    inserting into a subtree did not change its height. As in the lecture, first prove a stronger
    lemma about \<open>ins\<close>, which also says what happens to the height (use \<open>h\<^sub>i\<close>).

 2. \<open>auto split: up\<^sub>i.splits\<close> lets \<open>auto\<close> split the \<open>case\<close> expressions on the result of \<open>ins\<close>.
    With it, the proof from the lecture takes about a minute. \<open>auto split!: if_split up\<^sub>i.split\<close>,
    which breaks up the goal after every split of an \<open>if\<close> or \<open>case\<close>, takes a few seconds.
\<close>

text \<open>\Exercise{The Height of 2-3 Trees}\<close>

text \<open>
  The height of a complete 2-3 tree is logarithmic in its size:
  \[\log_3(|t|+1) \le h(t) \le \log_2(|t|+1)\]
  In Isabelle, \<open>|t|\<close> is \<open>size t\<close>, the number of nodes, which the \<open>datatype\<close> command defines
  automatically.

  \paragraph{(a)} Prove, first pen-and-paper and then in Isabelle:
\<close>

lemma size_lb: "complete t \<Longrightarrow> 2 ^ height t \<le> size t + 1"
  sorry

lemma size_ub: "complete t \<Longrightarrow> size t + 1 \<le> 3 ^ height t"
  sorry

text \<open>\paragraph{(b)} Derive the logarithmic bounds:\<close>

lemma height_ub: "complete t \<Longrightarrow> height t \<le> log 2 (size t + 1)"
  sorry

lemma height_lb: "complete t \<Longrightarrow> log 3 (size t + 1) \<le> height t"
  sorry

text \<open>\paragraph{Hints:}
 1. \<open>size_lb\<close> is the lemma from the lecture.

 2. For (b), use (a) and sledgehammer. \<open>find_theorems "log" "_ ^ _"\<close> lists library lemmas
    relating logarithms and powers. \<open>log\<close> works on real numbers: Isabelle converts \<open>size t + 1\<close>
    to a real number automatically, written \<open>real (size t + 1)\<close>. To turn an inequality between
    natural numbers into one between real numbers, use \<open>of_nat_mono\<close>.
\<close>

text \<open>\Exercise{Joining 2-3 Trees}\<close>

text \<open>
  Define a function \<open>join\<close> that combines two complete 2-3 trees of the same height into one
  tree. The in-order traversal of the result must be the in-order traversal of the first tree
  followed by that of the second, and the height of the result must be either the height of the
  arguments or one more. As for \<open>ins\<close>, use \<open>'a up\<^sub>i\<close> to return the result: \<open>Of\<close> signals that
  the height has increased.
\<close>

fun join :: "'a tree23 \<Rightarrow> 'a tree23 \<Rightarrow> 'a up\<^sub>i" where

  (* TODO: complete this definition *)


text \<open>Prove that your function is correct:\<close>

lemma join_inorder:
  assumes "height t1 = height t2" "complete t1" "complete t2"
  shows "inorder (tree\<^sub>i (join t1 t2)) = inorder t1 @ inorder t2"
  sorry

lemma join_complete:
  assumes "height t1 = height t2" "complete t1" "complete t2"
  shows "complete (tree\<^sub>i (join t1 t2)) \<and> h\<^sub>i (join t1 t2) = height t2"
  sorry

text \<open>\paragraph{Hints:}
 1. Combine the two trees in the middle: recursively join the rightmost subtree of the first tree
    with the leftmost subtree of the second, then rebuild the outer nodes, splitting them if the
    result overflows.

 2. Prove both lemmas by computation induction (\<open>join.induct\<close>), with \<open>auto split: up\<^sub>i.splits\<close>.
    There are many cases: if \<open>auto\<close> fails, use an Isar proof to look at the cases one by one.
    This also helps to find mistakes in your definition of \<open>join\<close>.
\<close>


end

