text \<open>\section*{Algebraic Datatypes in Isabelle/HOL}\<close>
theory Algebraic_Datatypes
  imports Main
begin

text \<open>Algebraic data types are a fundamental way to model data in functional programming. The
      following examples show how we model natural numbers, lists, binary trees with data in the
      inner nodes, and binary trees with data in the leaves.\<close>

datatype Nat = Zero | Succ Nat

term "Zero"
term "Succ (Succ Zero)"

datatype 'a List = Nill | Conss 'a "'a List"

term "Nill"
term "Conss (2::nat) (Conss 3 Nill)"

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

term "Node (Node  Leaf 2 Leaf) (1::nat) (Node Leaf 3 Leaf)"

datatype 'a tree' = Leaf' 'a | Node' "'a tree'" "'a tree'"

term "Node' (Node' (Leaf' (2::nat)) (Leaf' 1)) (Leaf' 3)"

end