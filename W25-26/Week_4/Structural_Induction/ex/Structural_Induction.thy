text \<open>\section*{Proofs by Structural Induction}\<close>

theory Structural_Induction
  imports Main
begin

text \<open>Defining a well-formed (recursive) algebraic data type automatically, in Isabelle/HOL, leads
      to the generation of an induction principle. For instance, for the following binary trees data type
\<close>

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

text \<open>    

that induction principle is 

  \[\frac{P\; \text{Leaf};\;\;\; [\forall\; t_1\; t_2\; a.\; P\; t_1;\; P\; t_2\; \Longrightarrow\; P\; \text{Node t1 a t2}]}{P\; t}.\]

As a general rule of thumb, you should follow the same heuristics for induction: manipulate the goal
until you can apply the Induction Hypothesis (I.H.). In this example, you have two induction hypotheses, one
for each subtree. 

\<close>


(*<*)
datatype Nat = Zero | Succ Nat

term "Zero"
term "Succ (Succ Zero)"

datatype 'a List = Nill | Conss 'a "'a List"

term "Nill"
term "Conss (2::nat) (Conss 3 Nill)"

definition tree_eg where "tree_eg \<equiv> Node (Node  Leaf 1 (Node Leaf 2 Leaf)) (4::nat) (Node Leaf 3 Leaf)"

fun tree_set::"'a tree \<Rightarrow> 'a set" where
"tree_set Leaf = {}"
| "tree_set (Node l a r) = insert a ((tree_set l) \<union> (tree_set r))"

value "tree_set tree_eg"

fun inorder::"'a tree \<Rightarrow> 'a list" where
  "inorder Leaf = []"
| "inorder (Node l a r) = (inorder l) @ [a] @ (inorder r)"

value "inorder tree_eg"

datatype 'a tree' = Leaf' 'a | Node' "'a tree'" "'a tree'"

term "Node' (Node' (Leaf' (2::nat)) (Leaf' 1)) (Leaf' 3)"

term set
thm set_simps
(*>*)
text \<open>The following is an example proof by structural induction on trees.
      After replicating it on your own, take a close look at the two goals: the base case and the step case, and note the two I.H.'s,
      each corresponding to a subtree.

      \emph{Exercise}: write down a detailed manual Isabelle/HOL proof using only forward reasoning
                (i.e.\ @{verbatim OF}), backward reasoning (i.e.\ @{verbatim rule}), and
                substitution (i.e.\ @{verbatim subst}).\<close>

lemma "set (inorder t) = tree_set t"
proof(induction t)
  case Leaf
  then show ?case
    by auto
next
  case (Node t1 x2 t2)
  then show ?case
    by auto
qed




end