
theory Week_9
  imports "HOL-Data_Structures.Set2_Join_RBT" "HOL-Data_Structures.RBT_Map"
begin


text \<open>\ExerciseSheet{9}{Graph Algorithms: Modelling Depth-First Search}\<close>

text \<open>
  Important Note: Please bring a laptop with Isabelle/HOL installed to the Large Group Tutorial (LGT).
  Performing these proofs in Isabelle will be an integral part of the tutorial.
\<close>

text \<open>
  In the lecture we modelled depth-first search (DFS) on top of abstract data types. In this sheet
  we do the same for \emph{breadth-first search} (BFS), implement the graph ADT with red-black
  trees, and run BFS on the example graph of the lecture.
\<close>

text \<open>\Exercise{Breadth-First Search on Paper}\<close>

text \<open>
  BFS explores a graph in layers. Starting from a source vertex \<open>s\<close>, it first visits \<open>s\<close>, then all
  neighbours of \<open>s\<close>, then all their neighbours that have not been visited yet, and so on. The set
  of vertices of the current layer is called the \emph{frontier}. In pseudocode:
  \begin{center}
  \begin{tabular}{l}
  $\mathit{visited} := \emptyset$\\
  $\mathit{current} := \{s\}$\\
  \textbf{while} $\mathit{current} \neq \emptyset$ \textbf{do}\\
  \quad $\mathit{visited} := \mathit{visited} \cup \mathit{current}$\\
  \quad $\mathit{current} := \big(\bigcup_{u \in \mathit{current}} N(u)\big) - \mathit{visited}$\\
  \textbf{od}\\
  \textbf{return} $\mathit{visited}$
  \end{tabular}
  \end{center}
  Here $N(u)$ is the neighbourhood of \<open>u\<close>. When the loop stops, \<open>visited\<close> is the set of vertices
  reachable from \<open>s\<close>. We use the graph \<open>G\<close> of the lecture:
  \begin{center}
  \begin{tikzpicture}[scale=0.9,
      vertex/.style={circle,draw=black!50,minimum size=18pt,inner sep=0pt},
      edge/.style={draw,thick,->,>=stealth}]
    \foreach \pos/\name in {{(0,0)/a}, {(2,1)/b}, {(2,-1)/c}, {(4,0.5)/d}, {(5,-1)/e}}
      \node[vertex] (\name) at \pos {$\name$};
    \foreach \source/\dest in {a/b, a/c, b/d, c/e, d/c, d/e}
      \path[edge] (\source) -- (\dest);
    \foreach \source/\dest in {b/c, c/b, c/d}
      \path[edge] (\source) edge [bend right] (\dest);
  \end{tikzpicture}
  \end{center}

  Run BFS on \<open>G\<close> from \<open>s = a\<close>. Give \<open>visited\<close> and \<open>current\<close> before the loop and after each
  iteration.
\<close>

text \<open>\Exercise{Modelling BFS in Isabelle}\<close>

text \<open>
  We model BFS as in the lecture. First the definitions we need from the lecture. The mathematical
  model of graphs:
\<close>

definition dVs :: "('v \<times> 'v) set \<Rightarrow> 'v set" where
  "dVs G = \<Union> {{v1, v2} | v1 v2. (v1, v2) \<in> G}"

definition neighbourhood :: "('v \<times> 'v) set \<Rightarrow> 'v \<Rightarrow> 'v set" where
  "neighbourhood G u = {v. (u, v) \<in> G}"

text \<open>
  For the ADTs we use the locales \<^locale>\<open>Set\<close>, \<^locale>\<open>Set2\<close> and \<^locale>\<open>Map\<close> of the
  library \<open>HOL-Data_Structures\<close>, where the lecture's ADTs come from. They also have an operation
  \<open>delete\<close>, which we do not use. Sets with a choice operator, and the graph ADT, with its
  abstraction function and invariant:
\<close>

locale Set_Choose = Set where set = t_set for t_set :: "'s \<Rightarrow> 'a set" +
  fixes sel :: "'s \<Rightarrow> 'a"
  assumes choose: "s \<noteq> empty \<Longrightarrow> isin s (sel s)"

locale Pair_Graph_Specs =
  adjmap: Map where update = update and invar = adjmap_inv +
  vset: Set_Choose where empty = vset_empty and delete = vset_delete and invar = vset_inv
  for update :: "'v \<Rightarrow> 'vset \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap" and adjmap_inv :: "'adjmap \<Rightarrow> bool"
    and vset_empty :: "'vset" and vset_delete :: "'v \<Rightarrow> 'vset \<Rightarrow> 'vset"
    and vset_inv :: "'vset \<Rightarrow> bool"
begin

notation vset_empty ("\<emptyset>\<^sub>V")

definition neighb :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset" where
  "neighb G v = (case lookup G v of Some vs \<Rightarrow> vs | None \<Rightarrow> \<emptyset>\<^sub>V)"

definition add_edge :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'adjmap" where
  "add_edge G u v = (case lookup G u of
                       Some vs \<Rightarrow> update u (insert v vs) G
                     | None \<Rightarrow> update u (insert v \<emptyset>\<^sub>V) G)"

definition digraph_abs :: "'adjmap \<Rightarrow> ('v \<times> 'v) set" where
  "digraph_abs G = {(u, v). isin (neighb G u) v}"

definition graph_inv :: "'adjmap \<Rightarrow> bool" where
  "graph_inv G = (adjmap_inv G \<and> (\<forall>v vs. lookup G v = Some vs \<longrightarrow> vset_inv vs))"

definition finite_graph :: "'adjmap \<Rightarrow> bool" where
  "finite_graph G = finite {v. lookup G v \<noteq> None}"

definition finite_vsets :: "bool" where
  "finite_vsets = (\<forall>vs. finite (t_set vs))"

text \<open>Facts about these definitions that we need below:\<close>

lemma vset_inv_neighb: "graph_inv G \<Longrightarrow> vset_inv (neighb G u)"
  by (auto simp: graph_inv_def neighb_def vset.invar_empty split: option.split)

lemma neighbourhood_abs: "graph_inv G \<Longrightarrow> t_set (neighb G u) = neighbourhood (digraph_abs G) u"
  using vset_inv_neighb by (auto simp: digraph_abs_def neighbourhood_def vset.set_isin)

lemma graph_inv_empty: "graph_inv empty"
  by (simp add: graph_inv_def adjmap.invar_empty adjmap.map_empty)

lemma graph_inv_add_edge: "graph_inv G \<Longrightarrow> graph_inv (add_edge G u v)"
  by (auto simp: graph_inv_def add_edge_def adjmap.invar_update adjmap.map_update
                 vset.invar_insert vset.invar_empty split: option.split)

lemma finite_graph_empty: "finite_graph empty"
  by (simp add: finite_graph_def adjmap.map_empty)

lemma finite_graph_add_edge:
  assumes "graph_inv G" "finite_graph G"
  shows "finite_graph (add_edge G u v)"
proof -
  have "{x. lookup (add_edge G u v) x \<noteq> None} = Set.insert u {x. lookup G x \<noteq> None}"
    using assms(1)
    by (auto simp: add_edge_def graph_inv_def adjmap.map_update split: option.split)
  then show ?thesis
    using assms(2) by (simp add: finite_graph_def)
qed

end

text \<open>
  BFS is defined in a locale that combines the graph ADT with the binary set operations, as DFS
  in the lecture. It fixes the graph \<open>G\<close> and the source \<open>s\<close>.

  To compute the next frontier, BFS needs the union of the neighbourhoods of all vertices of the
  current frontier. The Set ADT cannot iterate over the elements of a set, so we cannot define
  this function from the interface. Instead, the locale fixes a function \<open>next_frontier\<close> and
  assumes its specification: \<open>next_frontier f vis\<close> is the set of neighbours of the vertices of
  \<open>f\<close> that are not in \<open>vis\<close>. The last assumptions, \<open>BFS_assms\<close>, say that \<open>G\<close> satisfies the graph
  invariant and that the graph and all sets are finite.
\<close>

locale BFS =
  Graph: Pair_Graph_Specs where lookup = lookup +
  set_ops: Set2 vset_empty vset_delete _ t_set vset_inv insert
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
  fixes G :: "'adjmap" and s :: "'v"
  fixes next_frontier :: "'vset \<Rightarrow> 'vset \<Rightarrow> 'vset"
  assumes invar_next_frontier:
    "\<lbrakk>vset_inv f; vset_inv vis\<rbrakk> \<Longrightarrow> vset_inv (next_frontier f vis)"
  assumes set_next_frontier:
    "\<lbrakk>vset_inv f; vset_inv vis\<rbrakk> \<Longrightarrow>
       t_set (next_frontier f vis) = (\<Union>u \<in> t_set f. neighbourhood (Graph.digraph_abs G) u) - t_set vis"
  assumes BFS_assms: "Graph.graph_inv G" "Graph.finite_graph G" "Graph.finite_vsets"

text \<open>The state of BFS consists of the two variables of the pseudocode:\<close>

record ('v, 'vset) BFS_state =
  visited :: "'vset"
  current :: "'vset"

context BFS
begin

text \<open>
  \paragraph{(a)} Define BFS, following the pseudocode, as a recursive function on states that
  models the while loop. Use \<^theory_text>\<open>function (domintros)\<close>, as for DFS, and \<open>union\<close> for the union of
  vertex sets.
\<close>

function (domintros) BFS :: "('v, 'vset) BFS_state \<Rightarrow> ('v, 'vset) BFS_state" where

  (* TODO: complete this definition *)


text \<open>\paragraph{(b)} Define the initial state: nothing visited, and \<open>s\<close> in the frontier.\<close>

definition initial_state :: "('v, 'vset) BFS_state" where

  (* TODO: complete this definition *)


text \<open>
  \paragraph{(c)} BFS has two execution paths: a recursive call and a return. Define the condition
  of the recursive call, the update it performs on the state, and the condition of the return:
\<close>

definition BFS_call_1_conds :: "('v, 'vset) BFS_state \<Rightarrow> bool" where

  (* TODO: complete this definition *)


definition BFS_upd1 :: "('v, 'vset) BFS_state \<Rightarrow> ('v, 'vset) BFS_state" where

  (* TODO: complete this definition *)


definition BFS_ret_1_conds :: "('v, 'vset) BFS_state \<Rightarrow> bool" where

  (* TODO: complete this definition *)


text \<open>
  \paragraph{(d)} Since we have not proved that \<open>BFS\<close> terminates, Isabelle cannot execute it.
  To run BFS on examples, define a copy \<open>BFS_exec\<close> of \<open>BFS\<close> with the same body, using
  \<^theory_text>\<open>partial_function (tailrec)\<close> instead of \<^theory_text>\<open>function (domintros)\<close>.
\<close>

partial_function (tailrec) BFS_exec :: "('v, 'vset) BFS_state \<Rightarrow> ('v, 'vset) BFS_state" where

  (* TODO: complete this definition *)


text \<open>\paragraph{Hints:}
 1. In \<open>BFS\<close>, write the two updates of the loop body with \<^theory_text>\<open>let\<close>, as in the lecture's DFS. A
    record is built with \<open>\<lparr>visited = v, current = c\<rparr>\<close>, a field is read with \<open>visited st\<close>, and
    \<open>st\<lparr>visited := v, current := c\<rparr>\<close> is \<open>st\<close> with both fields changed. Discharge the proof
    obligations of \<^theory_text>\<open>function\<close> with \<^theory_text>\<open>by pat_completeness auto\<close>: the equations cover all
    arguments and do not contradict each other.

 2. \<^theory_text>\<open>partial_function (tailrec)\<close> needs no proof. It accepts the definition if the recursive
    call is the last thing the function does, which is the case for the body of \<open>BFS\<close>.
\<close>

end

text \<open>\Exercise{Implementing the Graph ADT and Running BFS}\<close>

text \<open>
  We implement vertex sets with the red-black trees of \<open>HOL-Data_Structures\<close>: \<open>'v rbt\<close>, with
  \<open>Leaf\<close> for the empty set, \<open>insert_rbt\<close>, \<open>delete_rbt\<close>, \<open>isin\<close>, \<open>union_rbt\<close>, \<open>inter_rbt\<close> and
  \<open>diff_rbt\<close>. The library proves that they implement the \<^locale>\<open>Set2\<close> ADT, with the
  abstraction function \<open>set_tree\<close> and the invariant \<open>\<lambda>t. (invc t \<and> invh t) \<and> bst t\<close>. We
  implement the adjacency map with red-black trees too: \<open>('v \<times> 'v rbt) rbt\<close>, with
  \<open>RBT_Set.empty\<close>, \<open>RBT_Map.update\<close>, \<open>RBT_Map.delete\<close> and \<open>lookup\<close>, which implement the
  \<^locale>\<open>Map\<close> ADT with the invariant \<open>M.invar\<close>.

  \paragraph{(a)} For the choice operator, define \<open>sel_rbt\<close>, which returns the element at the root
  of a red-black tree, and prove its specification:
\<close>

fun sel_rbt :: "'a rbt \<Rightarrow> 'a" where

  (* TODO: complete this definition *)


lemma choose_rbt: "t \<noteq> Leaf \<Longrightarrow> isin t (sel_rbt t)"
  sorry

text \<open>
  \paragraph{(b)} Prove that red-black trees implement the graph ADT. Since the library has
  already proved that they implement \<^locale>\<open>Map\<close> and \<^locale>\<open>Set\<close>, the only proof
  obligation left is the specification of \<open>sel\<close>.
\<close>

global_interpretation G_RBT: Pair_Graph_Specs
  where empty = RBT_Set.empty and update = RBT_Map.update and delete = RBT_Map.delete
    and lookup = lookup and adjmap_inv = M.invar
    and vset_empty = Leaf and insert = insert_rbt and vset_delete = delete_rbt and isin = isin
    and t_set = set_tree and vset_inv = "\<lambda>t. (invc t \<and> invh t) \<and> bst t" and sel = sel_rbt
  defines neighb_rbt = G_RBT.neighb and add_edge_rbt = G_RBT.add_edge
    and graph_inv_rbt = G_RBT.graph_inv
  sorry

text \<open>\paragraph{Hints:} For (a), a red-black tree is either \<open>Leaf\<close> or \<open>Node l (a, c) r\<close>, where
  \<open>c\<close> is the colour of the node; give \<open>sel_rbt Leaf\<close> the value \<open>undefined\<close>. For (b), start
  with \<open>unfold_locales\<close>: it leaves exactly the goals that the library has not proved yet.
\<close>

text \<open>
  The next frontier is computed by \<open>next_frontier_rbt\<close>. It goes through the vertices \<open>u\<close> of the
  frontier in order, with \<open>fold\<close> over the list \<open>inorder f\<close>, and collects their neighbourhoods
  with \<open>union_rbt\<close>. It then removes the visited vertices. We prove its specification:
\<close>

definition next_frontier_rbt :: "('v::linorder \<times> 'v rbt) rbt \<Rightarrow> 'v rbt \<Rightarrow> 'v rbt \<Rightarrow> 'v rbt" where
  "next_frontier_rbt G f vis =
     diff_rbt (fold (\<lambda>u acc. union_rbt (neighb_rbt G u) acc) (inorder f) Leaf) vis"

abbreviation rbt_inv :: "'a::linorder rbt \<Rightarrow> bool" where
  "rbt_inv t \<equiv> (invc t \<and> invh t) \<and> bst t"

lemma fold_union_rbt:
  assumes "graph_inv_rbt G" "rbt_inv acc"
  shows "rbt_inv (fold (\<lambda>u acc. union_rbt (neighb_rbt G u) acc) xs acc) \<and>
         set_tree (fold (\<lambda>u acc. union_rbt (neighb_rbt G u) acc) xs acc) =
           (\<Union>u \<in> set xs. set_tree (neighb_rbt G u)) \<union> set_tree acc"
  using assms(2)
proof (induction xs arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons u xs)
  have "rbt_inv (neighb_rbt G u)"
    using assms(1) by (rule G_RBT.vset_inv_neighb)
  then show ?case
    using Cons by (auto simp: RBT.invar_union RBT.set_union)
qed

lemma next_frontier_rbt:
  assumes "graph_inv_rbt G" "rbt_inv f" "rbt_inv vis"
  shows "rbt_inv (next_frontier_rbt G f vis)"
    and "set_tree (next_frontier_rbt G f vis) =
           (\<Union>u \<in> set_tree f. neighbourhood (G_RBT.digraph_abs G) u) - set_tree vis"
  using fold_union_rbt[OF assms(1), of Leaf "inorder f"] assms
  by (auto simp: next_frontier_rbt_def RBT.invar_diff RBT.set_diff G_RBT.neighbourhood_abs)

text \<open>
  The example graph of the lecture, with the vertices $a, b, c, d, e$ numbered $1, 2, 3, 4, 5$:
\<close>

definition example_edges :: "(nat \<times> nat) list" where
  "example_edges = [(1, 2), (1, 3), (2, 3), (2, 4), (3, 2), (3, 4), (3, 5), (4, 3), (4, 5)]"

definition example_graph :: "(nat \<times> nat rbt) rbt" where
  "example_graph = fold (\<lambda>(u, v) G. add_edge_rbt G u v) example_edges RBT_Set.empty"

lemma example_graph_inv: "graph_inv_rbt example_graph \<and> G_RBT.finite_graph example_graph"
proof -
  have "graph_inv_rbt G \<and> G_RBT.finite_graph G \<Longrightarrow>
        graph_inv_rbt (fold (\<lambda>(u, v) G. add_edge_rbt G u v) es G) \<and>
        G_RBT.finite_graph (fold (\<lambda>(u, v) G. add_edge_rbt G u v) es G)"
    for es :: "(nat \<times> nat) list" and G :: "(nat \<times> nat rbt) rbt"
  proof (induction es arbitrary: G)
    case Nil
    then show ?case by simp
  next
    case (Cons e es)
    obtain u v where "e = (u, v)"
      by fastforce
    then show ?case
      using Cons.prems Cons.IH[of "add_edge_rbt G u v"]
      by (simp add: G_RBT.graph_inv_add_edge G_RBT.finite_graph_add_edge)
  qed
  then show ?thesis
    by (simp add: example_graph_def G_RBT.graph_inv_empty G_RBT.finite_graph_empty)
qed

text \<open>BFS on the example graph from \<open>a\<close>, with red-black trees, is an interpretation of the locale
  \<^locale>\<open>BFS\<close>:\<close>

global_interpretation BFS_ex: BFS
  where empty = RBT_Set.empty and update = RBT_Map.update and delete = RBT_Map.delete
    and lookup = lookup and adjmap_inv = M.invar
    and vset_empty = Leaf and insert = insert_rbt and vset_delete = delete_rbt and isin = isin
    and t_set = set_tree and vset_inv = "\<lambda>t. (invc t \<and> invh t) \<and> bst t" and sel = sel_rbt
    and union = union_rbt and inter = inter_rbt and diff = diff_rbt
    and G = example_graph and s = 1 and next_frontier = "next_frontier_rbt example_graph"
  defines BFS_example = BFS_ex.BFS_exec and initial_example = BFS_ex.initial_state
    and upd_example = BFS_ex.BFS_upd1
proof unfold_locales
  show "rbt_inv (next_frontier_rbt example_graph f vis)" if "rbt_inv f" "rbt_inv vis" for f vis
    using example_graph_inv that by (simp add: next_frontier_rbt)
  show "set_tree (next_frontier_rbt example_graph f vis) =
          (\<Union>u \<in> set_tree f. neighbourhood (G_RBT.digraph_abs example_graph) u) - set_tree vis"
    if "rbt_inv f" "rbt_inv vis" for f vis
    using example_graph_inv that by (simp add: next_frontier_rbt)
  show "Pair_Graph_Specs.graph_inv lookup M.invar rbt_inv example_graph"
    using example_graph_inv by (simp add: graph_inv_rbt_def)
  show "G_RBT.finite_graph example_graph"
    using example_graph_inv by auto
  show "Pair_Graph_Specs.finite_vsets (set_tree :: nat rbt \<Rightarrow> nat set)"
    by (simp add: G_RBT.finite_vsets_def)
qed

declare BFS_ex.BFS_exec.simps [code]

text \<open>
  \paragraph{(c)} Run BFS on the example graph with \<^theory_text>\<open>value\<close>, and compare the result with
  your run of Exercise 9.1. \<open>inorder\<close> turns a red-black tree into the sorted list of its
  elements. Look at the frontier after each iteration, using \<open>upd_example\<close>, and at the final
  state, using \<open>BFS_example\<close>. Then run BFS from \<open>b\<close>, by applying \<open>BFS_example\<close> to a state
  of your own. Which vertices are reachable from \<open>b\<close>?
\<close>


end

