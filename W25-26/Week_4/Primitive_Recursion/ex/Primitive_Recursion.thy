text \<open>\section*{Primitive Recursion on Algebraic Data Types}\<close>

theory Primitive_Recursion
  imports Main
begin

text \<open>We can define functions recursively on algebraic data types in a way that is analogous to 
      previous recursive functions we discussed on natural numbers or lists. Below is a function
      that recursively computes the set of elements in a tree, and the list of elements in the
      tree traversed in order. Note that in primitive recursion, we have a defining equation for
      every case of our data type: e.g.\ if it is a leaf or an inner node.\<close>

(*<*)datatype Nat = Zero | Succ Nat

term "Zero"
term "Succ (Succ Zero)"

datatype 'a List = Nill | Conss 'a "'a List"

term "Nill"
term "Conss (2::nat) (Conss 3 Nill)"

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

(*>*)

fun tree_set::"'a tree \<Rightarrow> 'a set" where
"tree_set Leaf = {}"
| "tree_set (Node l a r) = insert a ((tree_set l) \<union> (tree_set r))"

definition tree_eg where "tree_eg \<equiv> Node (Node  Leaf 1 (Node Leaf 2 Leaf)) (4::nat) (Node Leaf 3 Leaf)"

value "tree_set tree_eg"

fun inorder::"'a tree \<Rightarrow> 'a list" where
  "inorder Leaf = []"
| "inorder (Node l a r) = (inorder l) @ [a] @ (inorder r)"

value "inorder tree_eg"

end