(*<*)
theory Week_7_sol
  imports Complex_Main
begin
(*>*)

text \<open>\ExerciseSheet{7}{Balanced Search Trees: 2-3 Trees (Solutions)}\<close>

text \<open>\paragraph{About these solutions.} Every Isabelle proof method (e.g.\ \<open>rule\<close>, \<open>simp\<close>),
      Isar keyword (e.g.\ \<open>have\<close>, \<open>also\<close>), attribute (e.g.\ \<open>OF\<close>, \<open>of\<close>) and method modifier
      (e.g.\ \<open>arbitrary:\<close>, \<open>simp add:\<close>) is explained in a short comment, marked ---, the first
      time it appears in the solutions, in sheet order from Week 1. Later uses are not explained
      again, so if you meet an unfamiliar construct, look for its first use in an earlier solution.
      Each proof is also labelled with its style; the module's preferred style is declarative (Isar),
      where every step states what it proves.\<close>

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

lemma complete_ins: "complete t \<Longrightarrow> complete (tree\<^sub>i (ins a t)) \<and> h\<^sub>i (ins a t) = height t"
  by (induction t) (auto split!: if_split up\<^sub>i.split)
  \<comment> \<open>\<open>split: up\<^sub>i.split\<close> lets \<open>auto\<close> split every \<open>case\<close> expression on a value of type
     \<open>'a up\<^sub>i\<close> into one goal per constructor (\<open>Eq\<^sub>i\<close>, \<open>Of\<close>); \<open>if_split\<close> does the same for \<open>if\<close>
     expressions (\<open>simp\<close> and \<open>auto\<close> use it by default). Writing \<open>split!\<close> instead of \<open>split\<close> makes
     \<open>auto\<close> apply its safe rules (which break up the goal) after every split, which is much faster when there are many \<open>if\<close> and
     \<open>case\<close> expressions, as in \<open>ins\<close>: this proof takes a few seconds, while the lecture's
     \<open>auto split: up\<^sub>i.splits\<close> also works but takes about a minute.\<close>
  \<comment> \<open>Style: procedural one-liner: structural induction on the generalised statement; \<open>auto\<close> with
     case splitting (\<open>split:\<close>, \<open>split!:\<close>, new).\<close>

lemma complete_insert: "complete t \<Longrightarrow> complete (insert a t)"
  by (simp add: insert_def complete_ins)
  \<comment> \<open>Style: procedural one-liner: \<open>simp\<close> with the definition of \<open>insert\<close> and the generalised lemma.\<close>

text \<open>\Exercise{Joining 2-3 Trees}\<close>

text \<open>
  Define a function \<open>join\<^sub>i\<close> that combines two complete 2-3 trees of the same height into one
  tree. The in-order traversal of the result must be the in-order traversal of the first tree
  followed by that of the second, and the height of the result must be either the height of the
  arguments or one more. As for \<open>ins\<close>, use \<open>'a up\<^sub>i\<close> to return the result: \<open>Of\<close> signals that
  the height has increased.
\<close>

fun join\<^sub>i :: "'a tree23 \<Rightarrow> 'a tree23 \<Rightarrow> 'a up\<^sub>i" where
  "join\<^sub>i Leaf Leaf = Eq\<^sub>i Leaf"
| "join\<^sub>i (Node2 l1 a r1) (Node2 l2 b r2) =
     (case join\<^sub>i r1 l2 of
        Eq\<^sub>i t \<Rightarrow> Eq\<^sub>i (Node3 l1 a t b r2)
      | Of t1 c t2 \<Rightarrow> Of (Node2 l1 a t1) c (Node2 t2 b r2))"
| "join\<^sub>i (Node2 l1 a r1) (Node3 l2 b m2 c r2) =
     (case join\<^sub>i r1 l2 of
        Eq\<^sub>i t \<Rightarrow> Of (Node2 l1 a t) b (Node2 m2 c r2)
      | Of t1 d t2 \<Rightarrow> Of (Node2 l1 a t1) d (Node3 t2 b m2 c r2))"
| "join\<^sub>i (Node3 l1 a m1 b r1) (Node2 l2 c r2) =
     (case join\<^sub>i r1 l2 of
        Eq\<^sub>i t \<Rightarrow> Of (Node2 l1 a m1) b (Node2 t c r2)
      | Of t1 d t2 \<Rightarrow> Of (Node3 l1 a m1 b t1) d (Node2 t2 c r2))"
| "join\<^sub>i (Node3 l1 a m1 b r1) (Node3 l2 c m2 d r2) =
     (case join\<^sub>i r1 l2 of
        Eq\<^sub>i t \<Rightarrow> Of (Node3 l1 a m1 b t) c (Node2 m2 d r2)
      | Of t1 e t2 \<Rightarrow> Of (Node3 l1 a m1 b t1) e (Node3 t2 c m2 d r2))"

text \<open>
  Using \<open>join\<^sub>i\<close>, define a function \<open>join\<close> that returns the joined tree as a 2-3 tree,
  as \<open>insert\<close> does for \<open>ins\<close>:
\<close>

definition join :: "'a tree23 \<Rightarrow> 'a tree23 \<Rightarrow> 'a tree23" where
  "join t1 t2 = tree\<^sub>i (join\<^sub>i t1 t2)"

text \<open>Prove that your function is correct. First prove these lemmas about \<open>join\<^sub>i\<close>:\<close>

lemma inorder_join\<^sub>i:
  assumes "height t1 = height t2" "complete t1" "complete t2"
  shows "inorder (tree\<^sub>i (join\<^sub>i t1 t2)) = inorder t1 @ inorder t2"
  using assms by (induction t1 t2 rule: join\<^sub>i.induct) (auto split: up\<^sub>i.splits)
  \<comment> \<open>The assumptions are passed with \<open>using\<close> before the induction, so that every case of the
     induction gets them, for the subtrees as well (in the induction hypotheses).\<close>
  \<comment> \<open>Style: procedural one-liner: computation induction on \<open>join\<^sub>i\<close>; \<open>auto\<close> with case splitting.\<close>

lemma complete_join\<^sub>i:
  assumes "height t1 = height t2" "complete t1" "complete t2"
  shows "complete (tree\<^sub>i (join\<^sub>i t1 t2)) \<and> h\<^sub>i (join\<^sub>i t1 t2) = height t2"
  using assms by (induction t1 t2 rule: join\<^sub>i.induct) (auto split: up\<^sub>i.splits)
  \<comment> \<open>Style: as above.\<close>

text \<open>Then use them to prove that \<open>join\<close> is correct:\<close>

lemma inorder_join:
  assumes "height t1 = height t2" "complete t1" "complete t2"
  shows "inorder (join t1 t2) = inorder t1 @ inorder t2"
  using assms by (simp add: join_def inorder_join\<^sub>i)
  \<comment> \<open>Style: procedural one-liner: \<open>simp\<close> with the definition of \<open>join\<close> and the
     lemma about \<open>join\<^sub>i\<close>, as for \<open>complete_insert\<close>.\<close>

lemma complete_join:
  assumes "height t1 = height t2" "complete t1" "complete t2"
  shows "complete (join t1 t2)"
  using assms by (simp add: join_def complete_join\<^sub>i)
  \<comment> \<open>Style: as above.\<close>

text \<open>\Exercise{The Height of 2-3 Trees}\<close>

text \<open>
  The height of a complete 2-3 tree is logarithmic in its size:
  \[\log_3(|t|+1) \le h(t) \le \log_2(|t|+1)\]
  In Isabelle, \<open>|t|\<close> is \<open>size t\<close>, the number of nodes, which the \<open>datatype\<close> command defines
  automatically.

  \paragraph{(a)} Prove, first pen-and-paper and then in Isabelle:
\<close>

lemma size_lb: "complete t \<Longrightarrow> 2 ^ height t \<le> size t + 1"
  by (induction t) auto
  \<comment> \<open>Style: procedural one-liner: structural induction; \<open>auto\<close>.\<close>

lemma size_ub: "complete t \<Longrightarrow> size t + 1 \<le> 3 ^ height t"
  by (induction t) auto
  \<comment> \<open>Style: as above.\<close>

text \<open>\paragraph{(b)} Derive the logarithmic bounds:\<close>

lemma height_ub: "complete t \<Longrightarrow> height t \<le> log 2 (size t + 1)"
  using size_lb le_log2_of_power by blast
  \<comment> \<open>\<open>blast\<close> is an automatic prover for pure logic: here it chains \<open>size_lb\<close> with the library
     lemma \<open>le_log2_of_power: 2 ^ n \<le> m \<Longrightarrow> n \<le> log 2 m\<close>, found by sledgehammer.\<close>
  \<comment> \<open>Style: declarative one-step proof: library lemma found by sledgehammer; \<open>blast\<close> (new).\<close>

lemma height_lb: "complete t \<Longrightarrow> log 3 (size t + 1) \<le> height t"
proof -
  assume "complete t"
  then have "size t + 1 \<le> 3 ^ height t" by (rule size_ub)
  then have "real (size t + 1) \<le> real (3 ^ height t)" by (rule of_nat_mono)
  \<comment> \<open>\<open>log\<close> works on real numbers, so we move the inequality from \<open>nat\<close> to \<open>real\<close>:
     \<open>real\<close> converts a natural number into a real number, and the library lemma
     \<open>of_nat_mono: i \<le> j \<Longrightarrow> of_nat i \<le> of_nat j\<close> says that this preserves \<open>\<le>\<close>.\<close>
  then have "real (size t + 1) \<le> 3 ^ height t" by simp
  from log_of_power_le[OF this] show ?thesis by simp
qed
  \<comment> \<open>Style: declarative (Isar): \<open>size_ub\<close>, moved to the reals, then the library lemma
     \<open>log_of_power_le: m \<le> b ^ n \<Longrightarrow> b > 1 \<Longrightarrow> m > 0 \<Longrightarrow> log b m \<le> n\<close>.\<close>

(*<*)
end
(*>*)
