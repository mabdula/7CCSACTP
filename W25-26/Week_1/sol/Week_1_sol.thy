theory Week_1_sol
imports Main
begin

text \<open>\vspace{15ex}\ExerciseSheet{1}{}\<close>

text \<open>\paragraph{About these solutions.} Every Isabelle proof method (e.g.\ \<open>rule\<close>, \<open>simp\<close>),
      Isar keyword (e.g.\ \<open>have\<close>, \<open>also\<close>), attribute (e.g.\ \<open>OF\<close>, \<open>of\<close>) and method modifier
      (e.g.\ \<open>arbitrary:\<close>, \<open>simp add:\<close>) is explained in a short comment, marked ---, the first
      time it appears in the solutions, in sheet order from Week 1. Later uses are not explained
      again, so if you meet an unfamiliar construct, look for its first use in an earlier solution.
      Each proof is also labelled with its style; the module's preferred style is declarative (Isar),
      where every step states what it proves.\<close>


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
  \<comment> \<open>\<open>proof -\<close> starts a structured proof without applying any method, leaving the goal unchanged.\<close>
  \<comment> \<open>Style: declarative (Isar \<open>have\<close>/\<open>show\<close>) with apply-style steps; forward (\<open>OF\<close>); backward (\<open>rule\<close>); \<open>subst\<close>.\<close>

  have 1: "A b"
    \<comment> \<open>\<open>have\<close> states an intermediate fact (here named \<open>1\<close>) and proves it.\<close>
    using TA[OF T]
    \<comment> \<open>\<open>using\<close> passes facts to the proof method that follows.\<close>
    \<comment> \<open>\<open>r[OF f]\<close> discharges the first premise of rule \<open>r\<close> with fact \<open>f\<close> (forward reasoning);
       here \<open>TA[OF T]\<close> is \<open>A b\<close>.\<close>
    .
    \<comment> \<open>\<open>.\<close> proves the goal directly by a fact given with \<open>using\<close>, instantiating its variables if needed.\<close>

  have 2: "A a \<and> A b"
    apply(rule conjI)
    \<comment> \<open>\<open>rule r\<close> matches the conclusion of \<open>r\<close> with the goal and replaces the goal by \<open>r\<close>'s
       premises (backward reasoning); here \<open>conjI\<close> leaves \<open>A a\<close> and \<open>A b\<close>.\<close>
    using Aab 1
    .


  have 3: "a = b"
    apply(rule A)
    using 2
    .

  show ?thesis
    \<comment> \<open>\<open>show\<close> proves the goal of the enclosing proof; \<open>?thesis\<close> abbreviates that goal.\<close>
    using T
    apply(subst 3)
    \<comment> \<open>\<open>subst eq\<close> rewrites the goal with the equation \<open>eq\<close>, left to right; here \<open>a\<close> becomes \<open>b\<close>.\<close>
    .
qed
\<comment> \<open>\<open>qed\<close> closes the proof block, once \<open>show\<close> has proved its goal.\<close>


end
