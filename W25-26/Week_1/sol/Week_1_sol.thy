
theory Week_1_sol
imports Main
begin

text \<open>\vspace{15ex}\ExerciseSheet{6}{}\<close>

text \<open>Important Note: Please download Isabelle from the link provided in the slides and bring a 
      laptop to the large group tutorial. Performing the proofs in Isabelle will be an integral part
      of those tutorials.\<close>


text \<open>Before you start, please open a new Isabelle/HOL theory file called Week\_1.thy and add the
       following to its beginning.

\noindent theory Week\_1\\
imports Main\\
begin
\<close>

text\<open>\Exercise{Trying out Isabelle}\<close>


text\<open>
In this sheet, you should try out the Isabelle theorem prover.
Prove the following theorem, first on pen-and-paper, then formally in Isabelle.
\<close>

lemma
  assumes T: "T b"
          and A: "A a \<and> A b \<Longrightarrow> a = b"
          and TA: "\<And>x. T x \<Longrightarrow> A x"
          and Aab: "A a"
  shows "T a"

proof-

  have 1: "A b"
    using TA[OF T]
    .

  have 2: "A a \<and> A b"
    apply(rule conjI)
    using Aab 1
    .


  have 3: "a = b"
    apply(rule A)
    using 2 
    .

  show ?thesis
    using T
    apply(subst 3)
    .
qed



end
