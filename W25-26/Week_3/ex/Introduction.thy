theory Introduction
  imports Main
begin

term "True"
term "False"
term "0::int" term "1::nat"

term "(+)::nat \<Rightarrow> (nat \<Rightarrow> nat)"

term "fst::(nat * int) \<Rightarrow> nat"

term "snd::(nat * int) \<Rightarrow> int"

term "[]"

term "[a, b, c]"

term "append::nat list \<Rightarrow> nat list \<Rightarrow> nat list"

term "[a,b] @ [c]"

term "hd [a,b]"

term "tl [a,b]"

term "{}"

term "{a::nat}"

term "union"

term "union s t"

term "inter"

term "s \<inter> t"

term "0::nat"
term "Suc 0"
term "Suc (Suc 0)"

term "[]"
term "Cons a []"
term "a # []"

term "a # b #c #[]"


term "a = b"

term "a \<noteq> b"

term "a \<and> b"

term "a \<or> b"

term "a \<longrightarrow> b" (*HOL implication*)

term "a = b \<longrightarrow> [a] = [b]"

(*A , B |- C*)

lemma "A \<Longrightarrow> B \<Longrightarrow> C"
  sorry

(*X \<longrightarrow> Y, X |- Y modus ponens*)

lemma "X \<longrightarrow> Y \<Longrightarrow> X \<Longrightarrow> Y"
  sorry

end
