
theory Week_1_sol
imports Main
begin

text \<open>\vspace{15ex}\ExerciseSheet{6}{}\<close>

text \<open>Before you start, please open a new Isabelle/HOL theory file called Week\_1.thy and add the
       following to its beginning.

\noindent theory Week\_1\\
imports Main\\
begin
\<close>

text\<open>\Exercise{Addition Commutes}\<close>


text\<open>
Consider the function @{term "(+)"} defined in Isabelle/HOL for natural numbers.

Prove the following theorem, first pen-and-paper, and then formally in Isabelle.
\<close>
(*
thm add_0_right

(*Note that 0 is also overloaded*)

thm add_0_left

thm add_Suc_right

thm add_Suc
*)
(*
  Note that when we prove this lemma, we will have a lemma where there is a universal quantification
  on n and m
*)
lemma add_commutes: "(n::nat) + m = m + n"

text \<open>\paragraph{Hints:} 

 1. Perform the proof by inuction on \<open>n\<close>, using substitutions \<open>subst\<close>, and forward reasoning using
   the method \<open>rule\<close>.

 2. You will need to identify multiple lemmas about how \<open>add\<close> works. Do not prove those lemmas. Use 
    \<open>sorry\<close> as the proof. This is the top-down approach. 

 3. There is a proof which uses the following lemmas:

   \<open>add_0_right, add_0_left, add_Suc_right, add_Suc\<close>
\<close>

proof(induction m)
  case 0
  have 2: "n + 0 = n"
    apply(subst (1) add_0_right)
    ..
  have 4: "0 + n = n"
    apply(subst (1) add_0_left)
    ..

  have 5: "n + 0 = n"
    using 2
    .
  from 5 show ?case
    by(subst 4)
next
  case (Suc m)

  hence 2: "n + (Suc m) = Suc (n + m)"
    apply(subst add_Suc_right)
    ..

  hence 4: "(Suc m) + n = Suc (m + n)"
    apply(subst add_Suc)
    ..

  hence 6: "Suc (n + m) = Suc (m + n)"
    (*Show IH*)
    thm Suc.IH
    (*Note that in order for the IH to apply here, we do not have to do any instantiations*)
    apply(subst Suc.IH)
    ..

  hence 7: "n + (Suc m) = Suc (m + n)"
    by(subst (asm) 2[symmetric])

  thus ?case
    by(subst (asm) 4[symmetric])

qed

(*show them how to use then and hence*)
(*Show them how the lemma is universally quantified*)
(*Tell them it is an exercise to perform the proof with the equational style*)


text \<open>\Exercise{Multiplication is Monotone}\<close>

text \<open>Consider the multiplication function @{term "(*)"} defined in Isabelle. Prove the following
      property of it, i.e.\ that it is monotonically increasing in both arguments. You should prove
      it both, pen-and-paper and in Isabelle.\<close>
(*

thm refl 

thm diff_le_self

thm mult_le_mono2

thm mult_zero_right

thm le0

thm mult_Suc_right

thm add_mono

thm Suc_eq_plus1

thm le_diff_conv

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

  2. If the induction hypothesis is too week, you might need to strengthen by generalising/
     universally quantifying over one of the variables. E.g. if you want to universally quantify on
     a variable \<open>x\<close>, then you can use \<open>induction .. arbitrary: x\<close>.

  3. The following lemmas suffice to prove the goal with only substitution, forward reasoning, and
     induction:

     \<open>refl, diff_le_self, mult_le_mono2, mult_zero_right, le0, mult_Suc_right, add_mono, Suc_eq_plus1,
      le_diff_conv\<close>

  4. When you have a term like \<open>x - y\<close>, where \<open>x\<close> is a \<open>nat\<close>, in the goal or the assumptions, you 
     should perform proof by case analysis on whether \<open>y \<le> x\<close>. This is because of the way \<open>-\<close> is
     defined for natural numbers, where \<open>x - y = 0\<close>, for any \<open>x \<le> y\<close>.
\<close>

(*Note that finding the proof is like solving a puzzle where all the pieces fit together*)


  using assms
proof(induction d arbitrary: c)
  case 0
  then show ?case
    by auto
next
  case (Suc d)
  from \<open>c \<le> Suc d\<close> have 1: "c \<le> d + 1"
    apply (subst Suc_eq_plus1[symmetric])
    .
  hence "c - 1 \<le> d"
    apply(subst le_diff_conv)
    .

  (*We can instantiate the I.H. with what we have, and then get the following: *)

  hence 2: "a * (c - 1) \<le> b * d"
    (*forward reasaoning exampe*)
    apply(rule Suc.IH[OF \<open>a \<le> b\<close>])
    .

  (*However, we cannot directly with the available lemmas go from this to the goal.*) 
  (*o show this, we have to consider two cases, c = 0 and not *)
  show ?case
  proof(cases c)
    case 0
    have "a * c = a * 0"
      apply(subst 0)
      ..
    hence 3: "a * c = 0"
      apply(subst mult_zero_right[symmetric])
      .
    have 4: "0 \<le> b * (Suc d)"
      using le0
      .
    thus ?thesis
      apply (subst 3)
      .
  next
    case (Suc nat)
    hence 3: "a * nat \<le> b * d"
      using 2
      by auto
    have "a * c = a * (Suc nat)"
      apply(subst  Suc)
      ..
    hence 4: "a * c = a + a * nat"
      by(subst (asm) mult_Suc_right)

    hence 5: "b * Suc d = b + b * d"
      apply (subst mult_Suc_right)
      ..
    have "a + a * nat \<le> b + b * d"
      by(rule add_mono[OF \<open>a \<le> b\<close> 3])
    then have "a * c \<le> b + b * d"
      apply(subst 4)
      .
    then show ?thesis
      apply(subst 5)
      .
  qed
qed 




end
