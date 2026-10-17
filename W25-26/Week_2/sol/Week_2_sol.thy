
theory Week_2_sol
imports Main
begin

text \<open>\vspace{15ex}\ExerciseSheet{2}{}\<close>

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

proof(induction a)
  \<comment> \<open>\<open>induction a\<close> splits the goal into a base case \<open>0\<close> and a step case \<open>Suc a\<close>, whose
     induction hypothesis is \<open>Suc.IH\<close>; each case is entered with \<open>case\<close>.\<close>
  \<comment> \<open>Style: declarative (Isar); induction (new); equational reasoning (\<open>also\<close>/\<open>finally\<close>); \<open>subst\<close>.\<close>
  case 0
  \<comment> \<open>\<open>case 0\<close> enters the base case; \<open>?case\<close> abbreviates its goal, and \<open>next\<close> moves on to the
     next case.\<close>
  have i: "(0 + b) + c = b + c"
    apply(subst add_0_left) ..
    \<comment> \<open>\<open>..\<close> finishes the goal by applying a standard rule; here \<open>refl\<close> closes \<open>b + c = b + c\<close>.\<close>
  also have "... = 0 + (b + c)"
    \<comment> \<open>\<open>also\<close> chains this step to the previous one, with \<open>...\<close> standing for its right-hand side;
       \<open>finally\<close> combines the whole chain into one fact.\<close>
    apply(subst add_0_left) ..
  finally show "(0 + b) + c = 0 + (b + c)"
    .
next
  case (Suc a)
  thm Suc.IH
  have i: "(Suc a + b) + c = Suc (a + b) + c"
    apply(subst add_Suc) ..
  also have "... = Suc ((a + b) + c)"
    apply(subst add_Suc) ..
  also have "... = Suc (a + (b + c))"
    apply(subst Suc.IH) ..
  also have "... = Suc a + (b + c)" thm add_Suc[symmetric]
    apply(subst add_Suc[symmetric]) ..
    \<comment> \<open>\<open>th[symmetric]\<close> swaps the two sides of the equation \<open>th\<close>, so \<open>subst\<close> rewrites
       right to left; here \<open>Suc (a + (b + c))\<close> becomes \<open>Suc a + (b + c)\<close>.\<close>
  finally show ?case  .
qed
(*show them how to use then and hence*)
(*Show them how the lemma is universally quantified*)


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

proof(induction n)
  \<comment> \<open>Style: declarative (Isar); induction for a lemma with an assumption (new); case analysis on a
     formula with \<open>cases\<close> (new) in the step case; equational reasoning; \<open>OF\<close>; \<open>subst\<close>.\<close>
  case 0
  have 1: "m = 0"
    using le_antisym[OF "0" le0]
    .
  have "0 - m + m = 0 - 0 + m"
    apply(subst 1)
    ..
  also have "... = 0 + m"
    apply(subst diff_self_eq_0)
    ..
  also have "... = m"
    apply(subst add_0_left)
    ..
  also have "... = 0"
    using 1
    .
  finally show ?case
    .
next
  case (Suc n)
  show ?case
  proof(cases "m \<le> n")
    \<comment> \<open>For a formula \<open>P\<close>, \<open>cases P\<close> gives the cases \<open>True\<close>, assuming \<open>P\<close>, and \<open>False\<close>,
       assuming \<open>\<not> P\<close>; the assumption is available under the case name.\<close>
    case True
    have "Suc n - m + m = Suc (n - m) + m"
      apply(subst Suc_diff_le[OF True])
      ..
    also have "... = Suc (n - m + m)"
      apply(subst add_Suc)
      ..
    also have "... = Suc n"
      apply(subst Suc.IH[OF True])
      ..
    finally show ?thesis
      .
  next
    case False
    have m_eq: "m = Suc n"
      using le_antisym[OF Suc.prems Suc_leI[OF not_le_imp_less[OF False]]]
      \<comment> \<open>\<open>Suc.prems\<close> are the assumptions of the current case, here \<open>m \<le> Suc n\<close>.\<close>
      .
    have "Suc n - m + m = Suc n - Suc n + m"
      apply(subst m_eq)
      ..
    also have "... = 0 + m"
      apply(subst diff_self_eq_0)
      ..
    also have "... = m"
      apply(subst add_0_left)
      ..
    also have "... = Suc n"
      using m_eq
      .
    finally show ?thesis
      .
  qed
qed


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

text \<open>
 \paragraph{Solution (a).} With \<open>proof(induction n)\<close>, the step case has to show
  \<open>add_acc (Suc n) m = Suc n + m\<close>, i.e.\ after unfolding \<open>add_acc\<close>,
  \<open>add_acc n (Suc m) = Suc n + m\<close>. The induction hypothesis is \<open>add_acc n m = n + m\<close> for the
  same, fixed \<open>m\<close>. It talks about \<open>add_acc n m\<close>, but the goal is about \<open>add_acc n (Suc m)\<close>, so
  the induction hypothesis cannot be applied: the second argument changes in the recursive call.

 \paragraph{Solution (b).} With \<open>arbitrary: m\<close> the induction hypothesis becomes
  \<open>\<And>m. add_acc n m = n + m\<close>. In the step case we instantiate it with \<open>Suc m\<close>, giving
  \<open>add_acc n (Suc m) = n + Suc m = Suc (n + m) = Suc n + m\<close>.
\<close>
proof(induction n arbitrary: m)
  \<comment> \<open>\<open>arbitrary: m\<close> generalises \<open>m\<close>, so the induction hypothesis holds for every \<open>m\<close>.\<close>
  \<comment> \<open>Style: declarative (Isar); generalised induction with \<open>arbitrary\<close> (new) for a recursive function;
     IH instantiated with \<open>of\<close> (new); equational reasoning.\<close>
  case 0
  have "add_acc 0 m = m"
    apply(subst add_acc.simps(1))
    ..
  also have "... = 0 + m"
    apply(subst add_0_left)
    ..
  finally show ?case
    .
next
  case (Suc n)
  have "add_acc (Suc n) m = add_acc n (Suc m)"
    apply(subst add_acc.simps(2))
    ..
  also have "... = n + Suc m"
    apply(subst Suc.IH[of "Suc m"])
    \<comment> \<open>\<open>th[of t]\<close> instantiates the first variable of \<open>th\<close> with the term \<open>t\<close>; here the IH
       with \<open>Suc m\<close> for \<open>m\<close>.\<close>
    ..
  also have "... = Suc (n + m)"
    apply(subst add_Suc_right)
    ..
  also have "... = Suc n + m"
    apply(subst add_Suc)
    ..
  finally show ?case
    .
qed


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

text \<open>
 \paragraph{Solution (c).} We generalise over \<open>acc\<close>: the recursive call changes the accumulator
  from \<open>acc\<close> to \<open>acc + m\<close>, so the induction hypothesis is needed for \<open>acc + m\<close>. The argument
  \<open>m\<close> stays the same in the recursive call, so it does not need to be generalised.
\<close>
proof(induction n arbitrary: acc)
  \<comment> \<open>Style: as in (b).\<close>
  case 0
  have "mult_acc 0 m acc = acc"
    apply(subst mult_acc.simps(1))
    ..
  also have "... = acc + 0"
    apply(subst add_0_right)
    ..
  also have "... = acc + 0 * m"
    apply(subst mult_0)
    ..
  finally show ?case
    .
next
  case (Suc n)
  have "mult_acc (Suc n) m acc = mult_acc n m (acc + m)"
    apply(subst mult_acc.simps(2))
    ..
  also have "... = (acc + m) + n * m"
    apply(subst Suc.IH)
    ..
  also have "... = acc + (m + n * m)"
    apply(subst add.assoc)
    ..
  also have "... = acc + Suc n * m"
    apply(subst mult_Suc)
    ..
  finally show ?case
    .
qed




end
