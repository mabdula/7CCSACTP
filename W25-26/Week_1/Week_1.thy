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



thm impI


lemma assumes assum1: "P \<Longrightarrow> Q"
  assumes assum2: "Q \<Longrightarrow> R"
  shows "\<not> R \<Longrightarrow> \<not> P"
proof-
  assume 1: "\<not>R"

  have 2: "Q \<Longrightarrow> R"
    using assum2
    . 

  find_theorems "?P \<Longrightarrow> (?Q \<Longrightarrow> ?P)"

  have 3: "Q \<Longrightarrow> \<not>R"
    using impI[OF 1]
    .

  have 4: "\<not> Q"
  thm lem2
    apply(rule lem2)
  using 3
  .

  have 5: "P \<Longrightarrow> \<not> Q"
    using impI[where ?P = "\<not>Q" and
                        ?Q = P,
               OF 4]
    .

  have 6: "\<not> P"
    using lem2[where ?R = Q and ?Q = P, OF 5]
    .

  show "\<not>P"
    using 6
    .
qed
  
lemma assumes assum1: "b = a"
  assumes assum2: "a \<and> c"
  shows "b \<and> c"
proof-
  have "b \<and> c"
    apply(subst assum1)
    using assum2
    .

  oops

lemma assumes assum1: "T y"
  assumes assum2: "A x \<and> A y \<Longrightarrow> x = y"
  assumes assum3: "\<And>z. T z \<Longrightarrow> A z"
  assumes assum4: "A x"
  shows "T x"
proof-
  have 1: "A y"
    using assum3[where z = y, OF assum1]
    .


  find_theorems "?x \<Longrightarrow> ?y \<Longrightarrow> ?x \<and> ?y"


  have 5: "A x \<and> A y"
    using HOL.conjI[where ?P = "A x" and ?Q = "A y", OF assum4 1]
    .
 
  have 2: "x = y"
    apply(rule assum2)
    using 5
    .

  have 3: "T x"
    apply(subst 2)
    using assum1
    .

  show "T x"
    using 3
    .


