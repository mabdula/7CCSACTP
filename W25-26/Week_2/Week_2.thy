
theory Week_2
imports Main
begin

text \<open>\ExerciseSheet{2}{}\<close>

text \<open>Important Note: Please download Isabelle from the link provided in the slides and bring a 
      laptop to the large group tutorial. Performing the proofs in Isabelle will be an integral part
      of those tutorials.\<close>


text \<open>Before you start, please open a new Isabelle/HOL theory file called Week\_1.thy and add the
       following to its beginning.

\noindent theory Week\_2\\
imports Main\\
begin
\<close>

text\<open>\Exercise{Addition is Associative}\<close>


text\<open>
Consider the function @{term "(+)"} defined in Isabelle/HOL for natural numbers.

Prove the following theorem, first pen-and-paper, and then formally in Isabelle.
\<close>
(*
thm add_0_left

(*Note that 0 is also overloaded*)

thm add_Suc
*)
(*
  Note that when we prove this lemma, we will have a lemma where there is a universal quantification
  on a, b and c
*)
lemma add_associative: "((a::nat) + b) + c = a + (b + c)"

text \<open>\paragraph{Hints:}

 1. Perform the proof by induction, using substitutions \<open>subst\<close>, backward reasoning using the method
   \<open>rule\<close>, and forward reasoning using \<open>OF\<close>.

 2. Think about which variable to perform induction on. Addition on natural numbers is defined by
    recursion on its first argument: look at \<open>thm add_0_left add_Suc\<close>.

 3. You will need to identify multiple lemmas about how \<open>add\<close> works. Do not prove those lemmas. Use
    \<open>sorry\<close> as the proof. This is the top-down approach.

 4. There is a proof which uses only the following lemmas: \<open>add_0_left, add_Suc, nat.inject, iffD2\<close>
\<close>

  sorry


text \<open>\Exercise{Multiplication is Monotone}\<close>

text \<open>Consider the multiplication function @{term "(*)"} defined in Isabelle. Prove the following
      property of it, i.e.\ that it is monotonically increasing in both arguments. You should prove
      it both, pen-and-paper and in Isabelle.\<close>
(*

thm le_0_eq

thm mult_zero_right

thm le_refl

thm le_SucE

thm le_SucI

thm mult_le_mono1

thm mult_le_mono2

thm le_trans

*)

lemma mult_mono:
  fixes a b c d:: nat \<comment> \<open>Note the alternative way of fixing the types of the constants\<close>
  assumes "a \<le> b" "c \<le> d"
  shows "a * c \<le> b * d"

text \<open>
Your pen-and-paper proof should indicate

 1. what lemmas are you assuming,

 2. on what variable are you preforming induction,

 3. what are assumptions and the proof goals in the base case and the step case, and what is the
    induction hypothesis, and

 4. how are you instantiating the induction hypothesis, i.e. how do you show that its assumptions
    hold and which quantified variables are instantiated with which constants.

\paragraph{Hints:}
 1. The proof should be by induction

 2. The following lemmas suffice to prove the goal with only substitution, forward reasoning using
     \<open>OF\<close>, backward reasoning using \<open>rule\<close>, and induction:

     \<open>le_0_eq, iffD1, mult_zero_right, le_refl, le_SucE, le_SucI, mult_le_mono1, mult_le_mono2, le_trans\<close>

 3. In the step case, the assumption \<open>c \<le> Suc d\<close> leaves two possibilities: \<open>c \<le> d\<close> or
     \<open>c = Suc d\<close>. Look at \<open>thm le_SucE\<close>, and use it with \<open>rule\<close> to split the proof into these two
     cases.
\<close>

(*Note that finding the proof is like solving a puzzle where all the pieces fit together*)


  sorry


text \<open>\Exercise{Induction Hypothesis Generalisation}\<close>

text \<open>Consider the following function, which adds two natural numbers using an accumulator: in
      each recursive call it moves one @{term Suc} from its first argument to its second.\<close>

fun add_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add_acc 0 m = m"
| "add_acc (Suc n) m = add_acc n (Suc m)"

text \<open>We want to prove that \<open>add_acc\<close> computes addition.\<close>

lemma add_acc_correct: "add_acc n m = n + m"

text \<open>
 \paragraph{(a)} First try to prove the lemma by plain induction on \<open>n\<close>, i.e.\ with
  \<open>proof(induction n)\<close>. Write down the goal of the step case and the induction hypothesis. Explain,
  pen-and-paper, why the induction hypothesis is not strong enough to prove the step case.

 \paragraph{(b)} Now prove the lemma, first pen-and-paper and then formally in Isabelle, by
  generalising the induction hypothesis over \<open>m\<close>, i.e.\ with \<open>proof(induction n arbitrary: m)\<close>.
  Your pen-and-paper proof should state the generalised induction hypothesis and say with which term
  you instantiate its universally quantified variable in the step case.

\paragraph{Hints:}
 1. Use \<open>thm Suc.IH\<close> in the step case to compare the induction hypothesis you get with and without
    \<open>arbitrary: m\<close>.

 2. An instance of a universally quantified fact can be obtained with \<open>of\<close>, e.g.\
    \<open>Suc.IH[of "Suc m"]\<close>.

 3. The following lemmas suffice: \<open>add_acc.simps, add_0_left, add_Suc, add_Suc_right\<close>.
\<close>

  sorry


text \<open>
 \paragraph{(c) Challenge (optional)} The following function multiplies using an accumulator.
  Prove, pen-and-paper and in Isabelle, that it computes \<open>acc + n * m\<close>. Which variable must you
  generalise over this time, and why?\<close>

fun mult_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mult_acc 0 m acc = acc"
| "mult_acc (Suc n) m acc = mult_acc n m (acc + m)"

lemma mult_acc_correct: "mult_acc n m acc = acc + n * m"

text \<open>\paragraph{Hint:} The following lemmas suffice:
      \<open>mult_acc.simps, mult_0, add_0_right, mult_Suc, add.assoc\<close>.\<close>

  sorry


end
