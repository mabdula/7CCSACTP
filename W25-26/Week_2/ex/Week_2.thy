
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

 1. Perform the proof by induction, using substitutions \<open>subst\<close>.

 2. Think about which variable to perform induction on. Addition on natural numbers is defined by
    recursion on its first argument: look at \<open>thm add_0_left add_Suc\<close>.

 3. You will need to identify multiple lemmas about how \<open>add\<close> works. Do not prove those lemmas. Use
    \<open>sorry\<close> as the proof. This is the top-down approach.

 4. There is a proof which uses only the following lemmas: \<open>add_0_left, add_Suc\<close>
\<close>

  sorry


text \<open>\Exercise{Truncated Subtraction}\<close>

text \<open>Subtraction on natural numbers is truncated: \<open>n - m = 0\<close> whenever \<open>n \<le> m\<close>. Prove that, as long
      as \<open>m \<le> n\<close>, subtracting \<open>m\<close> and adding it back gives \<open>n\<close> again. You should prove it both,
      pen-and-paper and in Isabelle, by induction on \<open>n\<close>.\<close>

lemma sub_add: "(m::nat) \<le> n \<Longrightarrow> (n - m) + m = n"

text \<open>
\paragraph{Hints:}
 1. In the step case, perform a case analysis with \<open>proof(cases "m \<le> n")\<close>. In the second case,
    together with the assumption \<open>m \<le> Suc n\<close>, you can derive \<open>m = Suc n\<close>.

 2. Use \<open>thm Suc.IH\<close> in the step case to look at the induction hypothesis. It has an assumption,
    which you can discharge with \<open>OF\<close>.

 3. The following lemmas suffice: \<open>le0, le_antisym, diff_self_eq_0, add_0_left, Suc_diff_le,
    add_Suc, not_le_imp_less, Suc_leI\<close>.
\<close>

  sorry


text \<open>\Exercise{Induction Hypothesis Generalisation with an Accumulator}\<close>

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
 1. \<open>add_acc\<close> is a recursive function defined with \<open>fun\<close>, like \<open>add\<close> in Section 2.2.2 of
    Concrete Semantics. Its defining equations are available as \<open>add_acc.simps(1)\<close> and
    \<open>add_acc.simps(2)\<close> (look at \<open>thm add_acc.simps\<close>), and can be used with \<open>subst\<close> like any
    other equation.

 2. Use \<open>thm Suc.IH\<close> in the step case to compare the induction hypothesis you get with and without
    \<open>arbitrary: m\<close>.

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
