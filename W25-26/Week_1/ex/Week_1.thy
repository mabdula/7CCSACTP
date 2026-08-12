theory Week_1
imports Main
begin

lemma impI: assumes "P"
  shows "Q \<Longrightarrow> P"
  sorry

lemma lem2: 
  assumes "Q \<Longrightarrow> \<not>R"
  shows "\<not>Q"
  sorry

lemma assumes assum1: "P \<Longrightarrow> Q"
  assumes assum2: "Q \<Longrightarrow> R"
  shows "\<not> R \<Longrightarrow> \<not> P"
  sorry
  
lemma assumes assum1: "b = a"
  assumes assum2: "a \<and> c"
  shows "b \<and> c"
  sorry

lemma assumes assum1: "T y"
  assumes assum2: "A x \<and> A y \<Longrightarrow> x = y"
  assumes assum3: "\<And>z. T z \<Longrightarrow> A z"
  assumes assum4: "A x"
  shows "T x"
  sorry

end
