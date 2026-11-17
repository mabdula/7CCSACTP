(*<*)
theory Week_6_sol
  imports Main "HOL-Library.Multiset"
begin
(*>*)

text \<open>\ExerciseSheet{6}{Correctness and Running Time Analysis (Solutions)}\<close>

text \<open>\paragraph{About these solutions.} Every Isabelle proof method (e.g.\ \<open>rule\<close>, \<open>simp\<close>),
      Isar keyword (e.g.\ \<open>have\<close>, \<open>also\<close>), attribute (e.g.\ \<open>OF\<close>, \<open>of\<close>) and method modifier
      (e.g.\ \<open>arbitrary:\<close>, \<open>simp add:\<close>) is explained in a short comment, marked ---, the first
      time it appears in the solutions, in sheet order from Week 1. Later uses are not explained
      again, so if you meet an unfamiliar construct, look for its first use in an earlier solution.
      Each proof is also labelled with its style; the module's preferred style is declarative (Isar),
      where every step states what it proves.\<close>

text \<open>\Exercise{Merge Sort}\<close>

text \<open>\paragraph{(a) Elements.}\<close>

fun merge :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge [] ys = ys"
| "merge xs [] = xs"
| "merge (x#xs) (y#ys) = (if x \<le> y then x # merge xs (y#ys) else y # merge (x#xs) ys)"

fun msort :: "'a::linorder list \<Rightarrow> 'a list" where
  "msort [] = []"
| "msort [x] = [x]"
| "msort xs = (let n = length xs div 2 in merge (msort (take n xs)) (msort (drop n xs)))"

lemma mset_merge: "mset (merge xs ys) = mset xs + mset ys"
proof(induction xs ys rule: merge.induct)
  \<comment> \<open>\<open>induction \<dots> rule: f.induct\<close> inducts along the recursion of function \<open>f\<close>, using the
     induction rule Isabelle generated for it.\<close>
  \<comment> \<open>Style: declarative (Isar) skeleton; computation induction (\<open>rule: merge.induct\<close>, new), one case
     per equation of \<open>merge\<close>; each case by \<open>auto\<close>.\<close>
  case (1 ys)
  then show ?case by auto
next
  case (2 x xs)
  then show ?case by auto
next
  case (3 x xs y ys)
  then show ?case by auto
qed

lemma mset_msort: "mset (msort xs) = mset xs"
proof(induction xs rule: msort.induct)
  \<comment> \<open>Style: declarative (Isar); computation induction; \<open>let ?n\<close> abbreviation (new); the two IHs
     stated explicitly; equational reasoning; \<open>auto\<close>, \<open>metis\<close>, \<open>simp\<close>.\<close>
  case 1
  then show ?case by auto
next
  case (2 x)
  then show ?case by auto
next
  case (3 x x' xs)
  let ?n = "length (x#x'#xs) div 2"
  \<comment> \<open>\<open>let ?n = t\<close> introduces \<open>?n\<close> as an abbreviation for the term \<open>t\<close>.\<close>
  have IH1: "mset (msort (take ?n (x # x' # xs))) = mset (take ?n (x # x' # xs))"
    using "3"(1) by auto
  \<comment> \<open>Case names that are numbers need quotes when used in a fact name: \<open>"3"(1)\<close> is the first IH
     of case 3.\<close>
  have IH2: "mset (msort (drop ?n (x # x' # xs))) = mset (drop ?n (x # x' # xs))"
    using "3"(2) by auto
  have "mset (msort (x # x' # xs)) = mset (merge (msort (take ?n (x # x' # xs))) (msort (drop ?n (x # x' # xs))))"
    by auto
  also have "... = mset (msort (take ?n (x # x' # xs))) + mset (msort (drop ?n (x # x' # xs)))"
    by (auto simp: mset_merge)
  also have "... = mset (take ?n (x # x' # xs)) + mset (drop ?n (x # x' # xs))"
    by (metis IH1 IH2)
    \<comment> \<open>\<open>metis\<close> is an automatic prover that derives the goal from the listed facts; such calls
       are typically found by \<open>sledgehammer\<close>.\<close>
  also have "... = mset (x # x' # xs)"
    by (simp add: union_code)
  finally have "mset (msort (x # x' # xs)) = mset (x # x' # xs)"
    .
  then show ?case .
qed

text \<open>\paragraph{(b) Sortedness.}\<close>

lemma set_merge: "set (merge xs ys) = set xs \<union> set ys"
  by (induction xs ys rule: merge.induct) auto
  \<comment> \<open>Style: procedural one-liner: computation induction; \<open>auto\<close>.\<close>

lemma sorted_merge: "sorted (merge xs ys) \<longleftrightarrow> sorted xs \<and> sorted ys"
  by (induction xs ys rule: merge.induct) (auto simp: set_merge)
  \<comment> \<open>Style: as above, giving \<open>auto\<close> the lemma \<open>set_merge\<close>.\<close>

lemma sorted_msort: "sorted (msort xs)"
proof (induction xs rule: msort.induct)
  \<comment> \<open>Style: declarative (Isar) skeleton; computation induction; each case by \<open>simp\<close>.\<close>
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x v vb)
  then show ?case
    by (simp add: sorted_merge Let_def)
qed

text \<open>\Exercise{Running Time}\<close>

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app [] ys = ys"
| "app (x # xs) ys = x # app xs ys"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []"
| "reverse (x # xs) = app (reverse xs) [x]"

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] acc = acc"
| "itrev (x # xs) acc = itrev xs (x # acc)"

text \<open>\paragraph{(a)}\<close>

fun t_app :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_app [] ys = 1"
| "t_app (x # xs) ys = t_app xs ys + 1"

fun t_reverse :: "'a list \<Rightarrow> nat" where
  "t_reverse [] = 1"
| "t_reverse (x # xs) = t_reverse xs + t_app (reverse xs) [x] + 1"

fun t_itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
  "t_itrev [] acc = 1"
| "t_itrev (x # xs) acc = t_itrev xs (x # acc) + 1"

text \<open>\paragraph{(b)}\<close>

lemma t_app: "t_app xs ys = length xs + 1"
proof(induction xs)
  \<comment> \<open>Style: declarative (Isar) skeleton; structural induction; each case by \<open>auto\<close>.\<close>
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case by auto
qed

lemma length_app: "length (app xs ys) = length xs + length ys"
proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case by auto
qed

lemma length_reverse: "length (reverse xs) = length xs"
proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
    by (auto simp: length_app)
qed

lemma t_reverse: "t_reverse xs \<le> (length xs + 1) * (length xs + 1)"
proof(induction xs)
  \<comment> \<open>Style: as above, giving \<open>auto\<close> the two lemmas \<open>t_app\<close> and \<open>length_reverse\<close>.\<close>
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case by (auto simp: t_app length_reverse)
qed

lemma t_itrev: "t_itrev xs acc = length xs + 1"
  by (induction xs arbitrary: acc) auto
  \<comment> \<open>Style: procedural one-liner: induction generalised over the accumulator, as for \<open>itrev\<close> itself.\<close>

text \<open>\paragraph{(c) Comparisons.}\<close>

fun c_merge :: "'a::linorder list \<Rightarrow> 'a list \<Rightarrow> nat" where
  "c_merge [] ys = 0"
| "c_merge xs [] = 0"
| "c_merge (x#xs) (y#ys) = 1 + (if x \<le> y then c_merge xs (y#ys) else c_merge (x#xs) ys)"

fun c_msort :: "'a::linorder list \<Rightarrow> nat" where
  "c_msort [] = 0"
| "c_msort [x] = 0"
| "c_msort xs = (let n = length xs div 2; ys = take n xs; zs = drop n xs
                 in c_msort ys + c_msort zs + c_merge (msort ys) (msort zs))"

lemma c_merge_ub: "c_merge xs ys \<le> length xs + length ys"
  by (induction xs ys rule: c_merge.induct) auto
  \<comment> \<open>Style: procedural one-liner: computation induction, as in the lecture.\<close>

lemma length_merge: "length (merge xs ys) = length xs + length ys"
  by (induction xs ys rule: merge.induct) auto

lemma length_msort: "length (msort xs) = length xs"
  by (induction xs rule: msort.induct) (auto simp: length_merge Let_def)

lemma c_msort_le: "length xs = 2 ^ k \<Longrightarrow> c_msort xs \<le> k * 2 ^ k"
proof (induction k arbitrary: xs)
  \<comment> \<open>Style: declarative (Isar); induction on \<open>k\<close>, generalised over \<open>xs\<close>; a chain of \<open>\<le>\<close> and
     \<open>=\<close> steps with \<open>also\<close>/\<open>finally\<close>.\<close>
  case 0
  then show ?case
    by (cases xs rule: c_msort.cases) auto
next
  case (Suc k)
  let ?n = "length xs div 2"
  let ?ys = "take ?n xs"
  let ?zs = "drop ?n xs"
  have ys: "length ?ys = 2 ^ k" and zs: "length ?zs = 2 ^ k"
    using Suc.prems by simp_all
  have "c_msort xs = c_msort ?ys + c_msort ?zs + c_merge (msort ?ys) (msort ?zs)"
    using Suc.prems by (cases xs rule: c_msort.cases) (auto simp: Let_def)
  also have "... \<le> c_msort ?ys + c_msort ?zs + length ?ys + length ?zs"
    using c_merge_ub[of "msort ?ys" "msort ?zs"] by (simp add: length_msort)
  also have "... \<le> k * 2 ^ k + k * 2 ^ k + 2 ^ k + 2 ^ k"
    using Suc.IH[OF ys] Suc.IH[OF zs] ys zs by simp
  also have "... = Suc k * 2 ^ Suc k"
    by simp
  finally show ?case .
qed

text \<open>\Exercise{Bottom-Up Merge Sort}\<close>

text \<open>
  Bottom-up merge sort does not split the list. It starts from singleton lists and repeatedly merges
  adjacent pairs of lists until a single list is left.
\<close>

fun merge_adj :: "('a::linorder) list list \<Rightarrow> 'a list list" where
  "merge_adj [] = []"
| "merge_adj [xs] = [xs]"
| "merge_adj (xs # ys # zss) = merge xs ys # merge_adj zss"

text \<open>Isabelle needs the following lemma to show that \<open>merge_all\<close> below terminates.\<close>

lemma length_merge_adjacent[simp]: "length (merge_adj xss) = (length xss + 1) div 2"
  by (induction xss rule: merge_adj.induct) auto

fun merge_all :: "('a::linorder) list list \<Rightarrow> 'a list" where
  "merge_all [] = []"
| "merge_all [xs] = xs"
| "merge_all xss = merge_all (merge_adj xss)"

definition msort_bu :: "('a::linorder) list \<Rightarrow> 'a list" where
  "msort_bu xs = merge_all (map (\<lambda>x. [x]) xs)"

text \<open>\paragraph{(a) Correctness.}\<close>

lemma mset_merge_adj: "mset (concat (merge_adj xss)) = mset (concat xss)"
  by (induction xss rule: merge_adj.induct) (auto simp: mset_merge)
  \<comment> \<open>Style: procedural one-liner: computation induction on \<open>merge_adj\<close>.\<close>

lemma mset_merge_all: "mset (merge_all xss) = mset (concat xss)"
  by (induction xss rule: merge_all.induct) (auto simp: mset_merge mset_merge_adj)
  \<comment> \<open>Style: as above, on \<open>merge_all\<close>; the statement is about any list of lists \<open>xss\<close>, not just
     the singleton lists that \<open>msort_bu\<close> starts from.\<close>

lemma mset_msort_bu: "mset (msort_bu xs) = mset xs"
  by (simp add: msort_bu_def mset_merge_all)

lemma sorted_merge_adj: "\<forall>xs \<in> set xss. sorted xs \<Longrightarrow> \<forall>xs \<in> set (merge_adj xss). sorted xs"
  by (induction xss rule: merge_adj.induct) (auto simp: sorted_merge)

lemma sorted_merge_all: "\<forall>xs \<in> set xss. sorted xs \<Longrightarrow> sorted (merge_all xss)"
  by (induction xss rule: merge_all.induct) (auto simp: sorted_merge_adj)

lemma sorted_msort_bu: "sorted (msort_bu xs)"
  by (simp add: msort_bu_def sorted_merge_all)

text \<open>\paragraph{(b) Running time.}\<close>

fun c_merge_adj :: "('a::linorder) list list \<Rightarrow> nat" where
  "c_merge_adj [] = 0"
| "c_merge_adj [xs] = 0"
| "c_merge_adj (xs # ys # zss) = c_merge xs ys + c_merge_adj zss"

fun c_merge_all :: "('a::linorder) list list \<Rightarrow> nat" where
  "c_merge_all [] = 0"
| "c_merge_all [xs] = 0"
| "c_merge_all xss = c_merge_adj xss + c_merge_all (merge_adj xss)"

definition c_msort_bu :: "('a::linorder) list \<Rightarrow> nat" where
  "c_msort_bu xs = c_merge_all (map (\<lambda>x. [x]) xs)"

lemma lengths_merge_adj:
  "even (length xss) \<Longrightarrow> \<forall>xs \<in> set xss. length xs = m \<Longrightarrow> \<forall>xs \<in> set (merge_adj xss). length xs = 2 * m"
  by (induction xss rule: merge_adj.induct) (auto simp: length_merge)

lemma c_merge_adj: "\<forall>xs \<in> set xss. length xs = m \<Longrightarrow> c_merge_adj xss \<le> m * length xss"
proof (induction xss rule: c_merge_adj.induct)
  \<comment> \<open>Style: declarative (Isar) skeleton; computation induction; each case by \<open>simp\<close>.\<close>
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 xs ys zss)
  then show ?case
    using c_merge_ub[of xs ys]
    by (simp add: algebra_simps)
qed

lemma c_merge_all:
  "\<forall>xs \<in> set xss. length xs = m \<Longrightarrow> length xss = 2 ^ k \<Longrightarrow> c_merge_all xss \<le> m * k * 2 ^ k"
proof (induction xss arbitrary: k m rule: c_merge_all.induct)
  \<comment> \<open>Style: declarative (Isar); computation induction generalised over \<open>k\<close> and \<open>m\<close>; \<open>obtain\<close> (new);
     a chain of \<open>\<le>\<close> and \<open>=\<close> steps with \<open>also\<close>/\<open>finally\<close>.\<close>
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 xs ys xss)
  let ?xss = "xs # ys # xss"
  let ?xss2 = "merge_adj ?xss"
  obtain k' where k': "k = Suc k'"
    using "3.prems"(2)
    by (metis length_Cons nat.inject nat_power_eq_Suc_0_iff nat.exhaust)
    \<comment> \<open>\<open>obtain x where "P x"\<close> introduces a new variable \<open>x\<close> together with the fact \<open>P x\<close>, after
       proving that such an \<open>x\<close> exists.\<close>
  have even: "even (length ?xss)"
    using "3.prems"(2) k' by auto
  have lengths: "\<forall>x \<in> set ?xss2. length x = 2 * m"
    using lengths_merge_adj[OF even "3.prems"(1)] .
  have length: "length ?xss2 = 2 ^ k'"
    using "3.prems"(2) k' by auto
  have "c_merge_all ?xss = c_merge_adj ?xss + c_merge_all ?xss2"
    by simp
  also have "... \<le> m * 2 ^ k + c_merge_all ?xss2"
    using "3.prems"(2) c_merge_adj[OF "3.prems"(1)] by (auto simp: algebra_simps)
  also have "... \<le> m * 2 ^ k + (2 * m) * k' * 2 ^ k'"
    using "3.IH"[OF lengths length] by simp
  also have "... = m * k * 2 ^ k"
    using k' by (simp add: algebra_simps)
  finally show ?case .
qed

lemma c_msort_bu: "length xs = 2 ^ k \<Longrightarrow> c_msort_bu xs \<le> k * 2 ^ k"
  using c_merge_all[of "map (\<lambda>x. [x]) xs" 1] by (simp add: c_msort_bu_def)
  \<comment> \<open>Style: procedural one-liner: the generalised lemma, instantiated for singleton lists (\<open>m = 1\<close>).\<close>

(*<*)
end
(*>*)
