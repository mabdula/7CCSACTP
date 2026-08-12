(*<*)
theory Week_4
  imports Main
begin
(*>*)

text \<open>\ExerciseSheet{10}{}\<close>

text \<open>
  Recall the binary trees which we discussed in the lecture and the function \<open>tree_set\<close>.
\<close>

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

fun tree_set where
"tree_set Leaf = {}"
| "tree_set (Node l a r) = insert a (tree_set l) \<union> (tree_set r)"


text \<open>\Exercise{Binary Search Trees: Invariant}\<close>

text \<open>
    Recall that a binary tree can be used to make searching for elements easier by imposing the
    following constraint: the content \<open>a\<close> of every node @{term "Node l a r"} in the binary tree has to be:

     1. Strictly greater than the content of all nodes in the left sub-tree \<open>l\<close> of that node, and

     2. Strictly smaller than the content of all nodes in the right sub-tree \<open>r\<close> of that node.

    A tree satisfying such conditions is called a \<open>binary search tree\<close>, and the above conditions
    are called the binary search tree invariant.

    Write a functional program \<open>bst\<close>, both pen-and-paper and in Isabelle, which can check whether a given
    tree is a binary search tree.
\<close>

fun bst::"nat tree \<Rightarrow> bool" where
"bst Leaf = True"
| "bst (Node l a r) = ((\<forall>x\<in>tree_set l. x < a) \<and> bst l \<and> (\<forall>x\<in>tree_set r. a < x) \<and> bst r)"


text \<open>\Exercise{Binary Search Trees: Search}\<close>

text \<open>
   If a binary tree satisfies the constraints of a binary search tree, then it can make searching 
   for an element easier. In particular, you can avoid searching in one of the subtrees based on 
   how the value you are looking for compares to the root:
    
    - if it is bigger then you only search in the right sub-tree,

    - if it is smaller, then you only search in the left sub-tree, and

    - if it is the same as the root then you know the element you look for is in the tree. 

    Write a functional program \<open>isin\<close>, both pen-and-paper and in Isabelle, which can check if
    a given value is present in a given binary search tree. The program should not search in a
    sub-tree where you know the element will not be present.
\<close>

fun isin :: "('a::linorder) tree \<Rightarrow> 'a \<Rightarrow> bool" where
"isin Leaf x = False" |
"isin (Node l a r) x =
  (if x < a then isin l x else
   if x > a then isin r x
   else True)"

text \<open>Prove that this program is correct.\<close>

lemma tree_set_isin: "bst t \<Longrightarrow> isin t x = (x \<in> tree_set t)"
  sorry


text \<open>\Exercise{Binary Search Trees: Inserting an Element}\<close>

text \<open>Write a functional program that inserts an element into a binary search tree. Make sure that
      the new tree computed by the program is also a binary search tree.\<close>

fun ins :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"ins x Leaf = Node Leaf x Leaf" |
"ins x (Node l a r) =
  (if x < a then Node (ins x l) a r else
   if x > a then Node l a (ins x r)
   else Node l a r)"

text \<open>Prove that your program is correct by showing that the inserted element is actually in the 
      resulting tree, and that the resulting tree is a binary search tree.\<close>

lemma tree_set_ins: "tree_set (ins x t) = {x} \<union> tree_set t"
  sorry

lemma bst_ins: "bst t \<Longrightarrow> bst (ins x t)"
  sorry

(*<*)
end
(*>*)