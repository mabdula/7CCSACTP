
theory Week_8
  imports Main
begin


text \<open>\ExerciseSheet{8}{Abstract Data Types}\<close>

text \<open>
  Important Note: Please bring a laptop with Isabelle/HOL installed to the Large Group Tutorial (LGT).
  Performing these proofs in Isabelle will be an integral part of the tutorial.
\<close>

text \<open>
  In this sheet we implement two abstract data types with the 2-3 trees of Week 7: the Set ADT
  from the lecture, and a Map ADT.
\<close>

text \<open>The Set ADT from the lecture:\<close>

locale Set =
  fixes empty :: "'s"
  fixes insert :: "'a \<Rightarrow> 's \<Rightarrow> 's"
  fixes isin :: "'s \<Rightarrow> 'a \<Rightarrow> bool"
  fixes set :: "'s \<Rightarrow> 'a set"
  fixes invar :: "'s \<Rightarrow> bool"
  assumes set_empty: "set empty = {}"
  assumes set_isin: "invar s \<Longrightarrow> isin s x = (x \<in> set s)"
  assumes set_insert: "invar s \<Longrightarrow> set (insert x s) = set s \<union> {x}"
  assumes invar_empty: "invar empty"
  assumes invar_insert: "invar s \<Longrightarrow> invar (insert x s)"

text \<open>
  The 2-3 trees of Week 7, with search and insertion as in the lecture, and the structural
  invariant \<open>complete\<close>:
\<close>

datatype 'a tree23 = Leaf
  | Node2 "'a tree23" 'a "'a tree23"
  | Node3 "'a tree23" 'a "'a tree23" 'a "'a tree23"

fun height :: "'a tree23 \<Rightarrow> nat" where
  "height Leaf = 0"
| "height (Node2 l _ r) = max (height l) (height r) + 1"
| "height (Node3 l _ m _ r) = max (height l) (max (height m) (height r)) + 1"

fun complete :: "'a tree23 \<Rightarrow> bool" where
  "complete Leaf = True"
| "complete (Node2 l _ r) = (height l = height r \<and> complete l \<and> complete r)"
| "complete (Node3 l _ m _ r) =
     (height l = height m \<and> height m = height r \<and> complete l \<and> complete m \<and> complete r)"

fun isin :: "'a::linorder tree23 \<Rightarrow> 'a \<Rightarrow> bool" where
  "isin Leaf x = False"
| "isin (Node2 l a r) x =
     (if x < a then isin l x else
      if x > a then isin r x
      else True)"
| "isin (Node3 l a m b r) x =
     (if x < a then isin l x else
      if x = a then True else
      if x < b then isin m x else
      if x = b then True
      else isin r x)"

datatype 'a up\<^sub>i = Eq\<^sub>i "'a tree23" | Of "'a tree23" 'a "'a tree23"

fun tree\<^sub>i :: "'a up\<^sub>i \<Rightarrow> 'a tree23" where
  "tree\<^sub>i (Eq\<^sub>i t) = t"
| "tree\<^sub>i (Of l a r) = Node2 l a r"

fun h\<^sub>i :: "'a up\<^sub>i \<Rightarrow> nat" where
  "h\<^sub>i (Eq\<^sub>i t) = height t"
| "h\<^sub>i (Of l a r) = height l"

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

text \<open>
  HOL already has a function \<open>insert\<close>, which inserts an element into a set; \<open>hide_const\<close> hides
  it, so that we can use the name for 2-3 trees.
\<close>

hide_const insert

definition insert :: "'a::linorder \<Rightarrow> 'a tree23 \<Rightarrow> 'a tree23" where
  "insert x t = tree\<^sub>i (ins x t)"

text \<open>Insertion preserves completeness (Exercise 7.1):\<close>

lemma complete_ins: "complete t \<Longrightarrow> complete (tree\<^sub>i (ins a t)) \<and> h\<^sub>i (ins a t) = height t"
  by (induction t) (auto split!: if_split up\<^sub>i.split)

lemma complete_insert: "complete t \<Longrightarrow> complete (insert a t)"
  by (simp add: insert_def complete_ins)

text \<open>\Exercise{Implementing the Set ADT with 2-3 Trees}\<close>

text \<open>
  In the lecture, we implemented the Set ADT with 2-3 trees:
  \begin{center}
  \begin{tabular}{l}
  \<^theory_text>\<open>interpretation T23: Set\<close>\\
  \quad\<^theory_text>\<open>where empty = Leaf and isin = isin and insert = insert and set = set_tree23\<close>\\
  \quad\<^theory_text>\<open>and invar = "\<lambda>t. bst23 t \<and> complete t"\<close>
  \end{tabular}
  \end{center}
  Here \<open>set_tree23 t\<close> is the set of elements of the tree \<open>t\<close>, which the \<open>datatype\<close> command
  defines automatically, and \<open>bst23\<close> is the ordering invariant of 2-3 trees.

  \paragraph{(a)} Define \<open>bst23\<close>, first pen-and-paper and then in Isabelle: in a node
  \<open>Node2 l a r\<close>, the elements of \<open>l\<close> are smaller than \<open>a\<close> and those of \<open>r\<close> are greater; in a
  node \<open>Node3 l a m b r\<close>, the elements of \<open>l\<close> are smaller than \<open>a\<close>, those of \<open>m\<close> lie between \<open>a\<close>
  and \<open>b\<close>, those of \<open>r\<close> are greater than \<open>b\<close>, and \<open>a < b\<close>. State the condition on \<open>m\<close> as two
  separate conditions, \<open>a < x\<close> and \<open>x < b\<close> for all \<open>x\<close> in \<open>m\<close>: this makes the proofs below
  easier.
\<close>

fun bst23 :: "'a::linorder tree23 \<Rightarrow> bool" where

  (* TODO: complete this definition *)


text \<open>\paragraph{(b)} Prove that \<open>isin\<close> and \<open>insert\<close> are correct:\<close>

lemma isin_set_tree23: "bst23 t \<Longrightarrow> isin t x = (x \<in> set_tree23 t)"
  sorry

lemma set_ins: "set_tree23 (tree\<^sub>i (ins x t)) = set_tree23 t \<union> {x}"
  sorry

lemma set_tree23_insert: "set_tree23 (insert x t) = set_tree23 t \<union> {x}"
  sorry

text \<open>
  For the ordering invariant we need to know that the elements of the tree returned by \<open>ins\<close> are
  still bounded, and that bounds are transitive:
\<close>

lemma ball_ins: "\<forall>y \<in> set_tree23 t. P y \<Longrightarrow> P x \<Longrightarrow> \<forall>y \<in> set_tree23 (tree\<^sub>i (ins x t)). P y"
  sorry

lemma ball_less_trans: "\<forall>y \<in> A. y < a \<Longrightarrow> a < b \<Longrightarrow> \<forall>y \<in> A. y < (b::'a::linorder)"
  by auto

lemma ball_greater_trans: "\<forall>y \<in> A. b < y \<Longrightarrow> a < b \<Longrightarrow> \<forall>y \<in> A. (a::'a::linorder) < y"
  by auto

lemma bst23_ins: "bst23 t \<Longrightarrow> bst23 (tree\<^sub>i (ins x t))"
  sorry

lemma bst23_insert: "bst23 t \<Longrightarrow> bst23 (insert x t)"
  sorry

text \<open>\paragraph{Hints:}
 1. \<open>isin_set_tree23\<close> is proved like Week 4's \<open>tree_set_isin\<close>.

 2. For \<open>set_ins\<close>, use induction on \<open>t\<close>. In a node, \<open>auto\<close> needs to know which of the two
    possible results \<open>ins\<close> returned for a subtree: \<open>cases "ins x l"\<close> splits the goal into the case
    \<open>ins x l = Eq\<^sub>i l'\<close> and the case \<open>ins x l = Of l1 b l2\<close>. The combinator \<open>m\<^sub>1; m\<^sub>2\<close> applies the
    method \<open>m\<^sub>2\<close> to all goals produced by \<open>m\<^sub>1\<close>, so that, for example,
    \<open>(cases "ins x l"; cases "ins x r") auto\<close> treats all four combinations.

 3. For \<open>bst23_ins\<close>, instantiate \<open>ball_ins\<close> with the bounds of a node, for example
    \<open>ball_ins[of l "\<lambda>y. y < a" x]\<close>: if all elements of \<open>l\<close> and \<open>x\<close> are smaller than \<open>a\<close>, then so
    are all elements of \<open>tree\<^sub>i (ins x l)\<close>. For a 3-node, \<open>auto\<close> alone has too many cases:
    distinguish the five positions of \<open>x\<close> with
    \<^theory_text>\<open>consider "x < a" | "x = a" | "a < x" "x < b" | "x = b" | "b < x"\<close>, proved by
    \<open>fastforce\<close>, and treat them one by one with \<^theory_text>\<open>proof cases\<close>. When a 3-node is split, its keys
    move: \<open>ball_less_trans\<close> and \<open>ball_greater_trans\<close>, given to \<open>auto\<close> as introduction rules
    (\<open>auto intro: ball_less_trans ball_greater_trans\<close>), let it carry the bounds over.
\<close>

text \<open>\paragraph{(c)} Prove the interpretation:\<close>

interpretation T23: Set
  where empty = Leaf and isin = isin and insert = insert and set = set_tree23
    and invar = "\<lambda>t. bst23 t \<and> complete t"
  sorry

text \<open>\paragraph{Hint:} Start with \<^theory_text>\<open>proof (standard, goal_cases)\<close>: the method \<open>standard\<close> turns the
  assumptions of the locale into one goal each, in the order of the \<^theory_text>\<open>assumes\<close>, and
  \<open>goal_cases\<close> names them \<open>1\<close>, \<open>2\<close> and so on, so that \<^theory_text>\<open>case (2 s x)\<close> picks the second goal.
\<close>

text \<open>
  Every definition and lemma of the locale is now available for 2-3 trees, with the prefix \<open>T23\<close>:
  for example, \<open>T23.set_insert\<close> is the lemma @{thm T23.set_insert}.
\<close>

text \<open>\Exercise{A Map ADT, Implemented with 2-3 Trees}\<close>

text \<open>
  A map associates keys of type \<open>'k\<close> with values of type \<open>'v\<close>. Its interface consists of the empty
  map \<open>empty\<close>, an operation \<open>update k v m\<close> that associates the key \<open>k\<close> with the value \<open>v\<close> in the
  map \<open>m\<close>, and an operation \<open>lookup m k\<close> that returns the value associated with \<open>k\<close>: \<open>Some v\<close>,
  or \<open>None\<close> if there is none.

  As the model we use HOL's maps, which are functions of type \<open>'k \<Rightarrow> 'v option\<close>. The function
  \<open>lookup\<close> itself serves as the abstraction function: \<open>lookup m\<close> is the map that \<open>m\<close> represents.
  The empty map is \<open>\<lambda>_. None\<close>, and \<open>f(k := Some v)\<close> is the function \<open>f\<close> with the value at
  \<open>k\<close> changed to \<open>Some v\<close>.

  \paragraph{(a)} Complete the specification of the Map ADT: add the assumptions to the
  locale below, in the style of the Set ADT.
\<close>

locale Map =
  fixes empty :: "'m"
  fixes update :: "'k \<Rightarrow> 'v \<Rightarrow> 'm \<Rightarrow> 'm"
  fixes lookup :: "'m \<Rightarrow> 'k \<Rightarrow> 'v option"
  fixes invar :: "'m \<Rightarrow> bool"
  (* TODO: add the specification as assumptions *)


text \<open>
  \paragraph{(b)} Implement the Map ADT with 2-3 trees whose elements are pairs \<open>(k, v)\<close> of a
  key and a value, ordered by the keys. Define \<open>lookup\<close>, like \<open>isin\<close>, and \<open>upd\<close>, like \<open>ins\<close>:
  if the key is already in the tree, \<open>upd\<close> replaces its value.
\<close>

fun lookup :: "('k::linorder \<times> 'v) tree23 \<Rightarrow> 'k \<Rightarrow> 'v option" where

  (* TODO: complete this definition *)


fun upd :: "'k::linorder \<Rightarrow> 'v \<Rightarrow> ('k \<times> 'v) tree23 \<Rightarrow> ('k \<times> 'v) up\<^sub>i" where

  (* TODO: complete this definition *)


definition update :: "'k::linorder \<Rightarrow> 'v \<Rightarrow> ('k \<times> 'v) tree23 \<Rightarrow> ('k \<times> 'v) tree23" where
  "update x y t = tree\<^sub>i (upd x y t)"

text \<open>
  The invariant: the keys are ordered, and the tree is complete. The tree of the keys of \<open>t\<close> is
  \<open>map_tree23 fst t\<close>, where \<open>map_tree23 f t\<close> applies \<open>f\<close> to every element of \<open>t\<close> and
  \<open>fst (k, v) = k\<close>; the \<open>datatype\<close> command defines \<open>map_tree23\<close> automatically, like
  \<open>set_tree23\<close>. So the invariant is \<open>bst23 (map_tree23 fst t) \<and> complete t\<close>.

  Similarly, \<open>map_up\<^sub>i f u\<close> applies \<open>f\<close> to every element of \<open>u :: 'a up\<^sub>i\<close>. The library lemma
  @{thm tree23.set_map} relates \<open>map_tree23\<close> and \<open>set_tree23\<close>, where \<open>f ` A\<close> is the image of the
  set \<open>A\<close> under \<open>f\<close>; we add it to the simplifier:
\<close>

declare tree23.set_map [simp]

text \<open>
  \paragraph{(c)} Prove the interpretation
  \begin{center}
  \begin{tabular}{l}
  \<^theory_text>\<open>interpretation T23_Map: Map\<close>\\
  \quad\<^theory_text>\<open>where empty = Leaf and update = update and lookup = lookup\<close>\\
  \quad\<^theory_text>\<open>and invar = "\<lambda>t. bst23 (map_tree23 fst t) \<and> complete t"\<close>
  \end{tabular}
  \end{center}
  through the following lemmas. On the keys, \<open>upd\<close> does exactly what \<open>ins\<close> does:
\<close>

lemma keys_upd: "map_up\<^sub>i fst (upd x y t) = ins x (map_tree23 fst t)"
  sorry

lemma map_tree\<^sub>i: "map_tree23 f (tree\<^sub>i u) = tree\<^sub>i (map_up\<^sub>i f u)"
  by (cases u) auto

lemma keys_tree_upd: "map_tree23 fst (tree\<^sub>i (upd x y t)) = tree\<^sub>i (ins x (map_tree23 fst t))"
  sorry

lemma bst23_update: "bst23 (map_tree23 fst t) \<Longrightarrow> bst23 (map_tree23 fst (update x y t))"
  sorry

lemma complete_upd: "complete t \<Longrightarrow> complete (tree\<^sub>i (upd x y t)) \<and> h\<^sub>i (upd x y t) = height t"
  sorry

lemma complete_update: "complete t \<Longrightarrow> complete (update x y t)"
  sorry

lemma ball_upd:
  assumes "\<forall>p \<in> set_tree23 t. P (fst p)" and "P x"
  shows "\<forall>p \<in> set_tree23 (tree\<^sub>i (upd x y t)). P (fst p)"
  sorry

lemma lookup_upd:
  "bst23 (map_tree23 fst t) \<Longrightarrow>
     lookup (tree\<^sub>i (upd x y t)) z = (if z = x then Some y else lookup t z)"
  sorry

lemma lookup_update:
  "bst23 (map_tree23 fst t) \<Longrightarrow> lookup (update x y t) = (lookup t)(x := Some y)"
  sorry

interpretation T23_Map: Map
  where empty = Leaf and update = update and lookup = lookup
    and invar = "\<lambda>t. bst23 (map_tree23 fst t) \<and> complete t"
  sorry

text \<open>\paragraph{Hints:}
 1. \<open>keys_upd\<close> and \<open>complete_upd\<close> are proved like \<open>complete_ins\<close>. \<open>keys_tree_upd\<close> and
    \<open>bst23_update\<close> then follow by \<open>simp\<close>, using \<open>map_tree\<^sub>i\<close> and Exercise 1.

 2. \<open>ball_upd\<close> is \<open>ball_ins\<close> for the keys: use \<open>ball_ins[of "map_tree23 fst t" P x]\<close> and
    \<open>keys_tree_upd\<close>.

 3. Prove \<open>lookup_upd\<close> by computation induction, \<^theory_text>\<open>proof (induction x y t rule: upd.induct)\<close>,
    which splits the pairs in the nodes into keys and values. Structure the proof like that of
    \<open>bst23_ins\<close>, now also for 2-nodes. When a node is split, the search for \<open>z\<close> compares \<open>z\<close>
    with the key moved up: \<open>ball_upd\<close> tells you where it lies. After \<open>lookup\<close> is unfolded, the
    induction hypotheses contain \<open>if\<close> expressions: \<open>auto split!: if_split split: if_split_asm\<close>
    also splits these.

 4. \<open>lookup_update\<close> is an equation between functions: \<open>fun_eq_iff\<close> states that
    \<open>(f = g) = (\<forall>x. f x = g x)\<close>.
\<close>


end

