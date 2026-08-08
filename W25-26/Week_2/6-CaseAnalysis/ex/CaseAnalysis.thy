text \<open>\section*{Case Analysis in Isabelle/HOL}\<close>

theory CaseAnalysis
  imports Main
begin

text \<open>Another standard way to prove facts is by \<open>case analysis\<close>. In this method you prove a theorem
      by showing that the theorem's statement holds for a finite number of cases. Those cases
      need to be exhaustive, i.e.\ at least one of has to hold.

      In the following example, the proof is by considering two cases: \<open>x \<ge> y\<close> and \<open>\<not> x \<ge> y\<close>. This
      is done in the step case.\<close>

lemma lemma4: "a \<le> b \<Longrightarrow> Suc a \<le> Suc b"
  apply(subst Suc_le_mono)
  .

lemma "(x::nat) - y \<le> x"
proof(induction x)
  case 0
  have "0 - y = 0"
    using zero_diff
    .
  also have "... \<le> 0"
    using order.refl
    .
  finally show ?case
    . 
next
  case (Suc x)
  show ?case
  proof(cases "x \<ge> y")
    case True
    have 1: "(Suc x) - y = Suc (x - y)"
      using Suc_diff_le[OF True]
      .
    have "Suc x - y \<le> Suc x - y"
      using order.refl
      .
    then have 3: "Suc x - y \<le> Suc (x - y)"
      apply(subst 1[symmetric])
      .
    also have "... \<le> Suc x"
      using lemma4[OF Suc.IH]
      .
    finally show ?thesis
      .
  next
    case False
    have 1: "x < y"
      using not_le_imp_less[OF False]
      .
    have 2: "Suc x \<le> y"
      using Suc_leI[OF 1]
      .
    have 3: "Suc x - y = 0"
      using diff_is_0_eq'[OF 2]
      . 
    have 4: "0 \<le> Suc x"
      using zero_le
      .
    show ?thesis
      using 4
      apply(subst 3)
      .
  qed
qed


end