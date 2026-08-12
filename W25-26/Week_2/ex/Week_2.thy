(*<*)
theory Week_2
imports Main
begin
(*>*)
text \<open>\ExerciseSheet{7}{}\<close>

text \<open>Important Note: Please download Isabelle from the link provided in the slides and bring a 
      laptop to the large group tutorial. Performing the proofs in Isabelle will be an integral part
      of those tutorials.\<close>


text \<open>Before you start, please open a new Isabelle/HOL theory file called Week\_2.thy and add the
       following to its beginning.

\noindent theory Week\_2\\
imports Main\\
begin
\<close>

text\<open>\Exercise{Addition Commutes}\<close>


text\<open>
Consider the function @{term "(+)"} defined in Isabelle/HOL for natural numbers.

Prove the following theorem, first pen-and-paper, and then formally in Isabelle.
\<close>

lemma add_commutes: "(n::nat) + m = m + n"
  sorry

text \<open>\paragraph{Hints:} 

 1. Perform the proof by induction on \<open>n\<close>, using substitutions \<open{subst}\<close>, and forward reasoning using
   the method \<open>rule\<close>.

 2. You will need to identify multiple lemmas about how \<open>add\<close> works. Do not prove those lemmas. Use 
    \<open>sorry\<close> as the proof. This is the top-down approach. 

 3. There is a proof which uses the following lemmas:

    \<open>add_0_right, add_0_left, add_Suc_right, add_Suc\<close>
\<close>


text \<open>\Exercise{Multiplication is Monotone}\<close>

text \<open>Consider the multiplication function @{term "(*)"} defined in Isabelle. Prove the following
      property of it, i.e.\ that it is monotonically increasing in both arguments. You should prove
      it both, pen-and-paper and in Isabelle.\<close>

lemma mult_mono:
  fixes a b c d:: nat
  assumes "a \<le> b" "c \<le> d"
  shows "a * c \<le> b * d"
  sorry

text \<open>
Your pen-and-paper proof should indicate

 1. what lemmas are you assuming,

 2. on what variable are you performing induction,

 3. what are assumptions and the proof goals in the base case and the step case, and what is the
    induction hypothesis, and

 4. how are you instantiating the induction hypothesis, i.e. how do you show that its assumptions
    hold and which quantified variables are instantiated with which constants.

\paragraph{Hints:}
 1. The proof should be by induction

 2. The following lemmas suffice to prove the goal with only substitution, forward reasoning, and
     induction:

     \<open>refl, diff_le_self, mult_le_mono2, mult_zero_right, le0, mult_Suc_right, add_mono, Suc_eq_plus1,
      le_diff_conv\<close>

 3. When you have a term like \<open>x - y\<close>, where \<open>x\<close> is a \<open>nat\<close>, in the goal or the assumptions, you 
     should perform proof by case analysis on whether \<open>y \<le> x\<close>. This is because of the way \<open>-\<close> is
     defined for natural numbers, where \<open>x - y = 0\<close>, for any \<open>x \<le> y\<close>.
\<close>

(*<*)
end
(*>*)