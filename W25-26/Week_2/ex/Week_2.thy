(*<*)
theory Week_2
imports Main
begin
(*>*)
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
(*<*)
proof(induction n)
  case 0
  have 1: "0 + m = m"
    using Groups.comm_monoid_add_class.add_0[where ?a = m]
    .

  have 2: "m + 0 = m"
    using Groups.monoid_add_class.add_0_right
    .

  show ?case
    apply(subst 1)
    apply(subst 2)
    ..

next
  case (Suc n)
  have 1: "(Suc n) + m = Suc (n + m)"
    using Nat.plus_nat.add_Suc
    .

  have 2: "m + Suc n = Suc (m + n)"
    using Nat.add_Suc_right
    .

  show ?case
    apply(subst 1)
    apply(subst 2)
    apply(subst Suc.IH)
    ..

qed
(*show them how to use then and hence*)
(*Show them how the lemma is universally quantified*)
(*Tell them it is an exercise to perform the proof with the equational style*)
(*>*)

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

 2. The following lemmas suffice to prove the goal with only substitution, forward reasoning, and
     induction:

     \<open>refl, diff_le_self, mult_le_mono2, mult_zero_right, le0, mult_Suc_right, add_mono, Suc_eq_plus1,
      le_diff_conv\<close>

 3. When you have a term like \<open>x - y\<close>, where \<open>x\<close> is a \<open>nat\<close>, in the goal or the assumptions, you 
     should perform proof by case analysis on whether \<open>y \<le> x\<close>. This is because of the way \<open>-\<close> is
     defined for natural numbers, where \<open>x - y = 0\<close>, for any \<open>x \<le> y\<close>.
\<close>

(*Note that finding the proof is like solving a puzzle where all the pieces fit together*)

(*<*)
  using assms
proof(induction d)
  case assms: 0
  have 1: "c = 0"
    using  Nat.bot_nat_0.extremum_uniqueI[OF assms(2)]
    .
    find_theorems "?x \<le> ?x"

  show ?case
    apply(subst 1) 
    apply(subst mult_zero_right)
    apply(subst mult_zero_right)
    using preorder_class.order.refl
    .

next
  case Suc: (Suc d)

  show ?case
  proof(cases "c = Suc d")
    case c_eq_sucd: True
    show ?thesis
      apply(subst c_eq_sucd)
      using mult_le_mono1[OF assms(1)]
      .

  next
    case c_lt_sucd: False

    have 1: "c > Suc d \<or> c < Suc d"
      apply(subst neq_iff[symmetric])
      using c_lt_sucd[symmetric]
      .
    have 2: "\<not> c > Suc d"
      using leD[OF Suc(3)]
      .
    have 3: "c < Suc d"
      using Meson.make_pos_rule'[OF 1 2]
      .

    have 4: "c \<le> d"
      apply(subst less_Suc_eq_le[symmetric])
      using 3
      .
                 

    have 5: "a * c \<le> b * d"
      using Suc.IH[OF assms(1) 4]
      .

    have 6: "b * d \<le> b * (Suc d)"
      apply(rule mult_le_mono2)
      apply(rule order.strict_implies_order)
      using Nat.lessI
      .
    show ?thesis
      using le_trans[OF 5 6]
      .

  qed


qed
(*>*)


(*<*)
end
(*>*)