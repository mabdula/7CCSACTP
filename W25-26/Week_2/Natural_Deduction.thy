theory Natural_Deduction
  imports Main
begin

text \<open>Lemmas which need for natural deduction: \<close>

text \<open>Negation introduction:\<close>

lemma notI: "\<lbrakk>q \<longrightarrow> r; q \<longrightarrow> \<not>r\<rbrakk> \<Longrightarrow> \<not>q"
  by auto

text \<open>Implication introduction:\<close>

lemma impI: "\<lbrakk>P\<rbrakk> \<Longrightarrow> Q \<longrightarrow> P"
  by auto

lemma
  assumes "P \<longrightarrow> Q" "Q \<longrightarrow> R" "\<not> R"
  shows "\<not> P"
proof-

  have 1: "\<not>R"
    using assms(3)
    .

  have 2: "Q \<longrightarrow> R"
    using assms(2)
    .

  have 3: "Q \<longrightarrow> \<not> R"
    using 1
    by(rule impI)

  have 4: "\<not>Q"
    using 2 3
    by(rule notI)

  have 5: "P \<longrightarrow> \<not>Q"
    using 4
    by(rule impI)

  have 6: "P \<longrightarrow> Q"
    using assms(1)
    .

  show "\<not>P"
    using 6 5
    by(rule notI)

qed

end