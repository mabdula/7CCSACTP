text \<open>\section*{Backward Reasoning in Isabelle/HOL}\<close>

theory BW
imports Main
begin

lemma implication_introduction:
  "X \<Longrightarrow> (Y \<longrightarrow> X)"
  sorry

lemma neg_intro:
 "(X \<longrightarrow> Y) \<Longrightarrow> (X \<longrightarrow> \<not> Y) \<Longrightarrow> \<not> X"
  sorry

lemma assumes
   assum1: "P \<longrightarrow> Q" and assum2: "Q \<longrightarrow> R" and assum3: "\<not> R"
  shows "\<not>P"
proof-
  
  have 1: "\<not>R"
    using assum3
    .
  have 2: "Q \<longrightarrow> R"
    using assum2
    .
  have 3: "Q \<longrightarrow> \<not> R"
    apply(rule implication_introduction)
    using 1
    .
  have 4: "\<not>Q"
    apply(rule neg_intro)
    using 2 3
    .

  have 5: "P \<longrightarrow> \<not> Q"
    apply(rule implication_introduction)
    using 4
    .

  show "\<not> P"
    apply(rule neg_intro)
    using assum1 5
    .

qed


end