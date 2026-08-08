theory induction_hyp_generalisation
  imports Main
begin


find_theorems "?y \<le> Suc ?x"

lemma lem1: "x \<le> Suc y \<Longrightarrow> x - 1 \<le> y"
  sorry

lemma lem2: "x \<le> y \<Longrightarrow> x * l \<le> y * m \<Longrightarrow> x * (Suc l) \<le> y * (Suc m)"
  sorry

lemma lem3: "x \<ge> (1::nat) \<Longrightarrow> Suc (x - 1) = x"
  sorry

lemma lem4: "\<not> (x::nat) \<ge> y \<Longrightarrow> x < y"
  sorry

lemma lem5: "(x::nat) < 1 \<Longrightarrow> x = 0"
  sorry

lemma 
  fixes a b c d:: nat
  assumes "a \<le> b" "c \<le> d"
  shows "a * c \<le> b * d"
  using assms
proof(induction d arbitrary: c)
  case 0

  have 1: "c = 0"
    using bot_nat_0.extremum_uniqueI[OF "0"(2)]
    .
  have 2: "a * 0 = 0"
    using mult_zero_right
    . 

  have 3: "a * c = 0"
    using 2
    apply(subst 1)
    .

  have 4: "0 \<le> b * 0"
    using zero_le
    .

  show ?case
    using 4
    apply(subst 3)
    .
        
next
  case (Suc d)
  thm Suc.IH
  thm Suc (2)
  thm Suc (3)

  have 1: "c - 1 \<le> d"
    using lem1[OF Suc(3)]
    .
  have 2: "a*(c - 1) \<le> b * d"
    using Suc.IH[OF Suc(2) 1]
    .

  have 3: "a * (Suc (c - 1)) \<le> b * (Suc d)"
    using lem2[OF \<open>a \<le> b\<close> 2]
    .

  show ?case
  proof(cases "c \<ge> 1")
    case True
    have 4: "Suc (c - 1) = c"
      using lem3[OF \<open>1 \<le> c\<close>]
      .

    show ?thesis
      using 3
      apply(subst 4[symmetric])
      .

  next
    case False

    have 4: "c < 1"
      using lem4[OF \<open>\<not> 1 \<le> c\<close>]
      .

    have 5: "c = 0"
      using lem5[OF 4]
      .


  have 6: "a * 0 = 0"
    using mult_zero_right
    . 

  have 7: "a * c = 0"
    using 6
    apply(subst 5)
    .

  have 8: "0 \<le> b * (Suc d)"
    using zero_le
    .

  show ?thesis
    using 8
    apply(subst 7)
    .
        

  qed
qed


end
