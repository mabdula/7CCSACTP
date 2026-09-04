theory MCP_Demo
  imports Main
begin

section \<open>Demo 1: Interactive Exploration & Counterexample Detection\<close>

text \<open>
  Scenario: The agent is prompted to prove a false or non-generalised conjecture.
  The agent checks the state via PIDE-MCP and receives instant feedback from
  Quickcheck/Nitpick or sees stuck subgoals, then refines the statement.
\<close>

(* Flawed conjecture: student forgot that reverse flips the order *)
lemma rev_distrib_flawed: "rev (xs @ ys) = rev xs @ rev ys"
  oops (* In the demo: agent inspects proof state, sees Quickcheck counterexample, and corrects it *)

lemma rev_distrib_correct: "rev (xs @ ys) = rev ys @ rev xs"
  by simp


section \<open>Demo 2: Two-Stage "Draft, Sketch, and Prove" (DSP)\<close>

text \<open>
  Scenario: A non-trivial inductive property where the agent drafts an Isar
  skeleton using 'sorry' subgoals, validates the proof structure via PIDE-MCP,
  and then interactively discharges each step.
\<close>

fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0"
| "sum_upto (Suc n) = Suc n + sum_upto n"

(* Goal: Gauss summation formula: 2 * sum_upto n = n * (n + 1) *)
lemma sum_upto_formula: "2 * sum_upto n = n * (n + 1)"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  (* In the DSP demo:
     Stage 1 (Sketch): write intermediate steps with 'sorry'
     Stage 2 (Prove): replace 'sorry' with algebraic/simplification steps *)
  have "2 * sum_upto (Suc n) = 2 * (Suc n + sum_upto n)"
    by simp
  also have "... = 2 * Suc n + 2 * sum_upto n"
    by simp
  also have "... = 2 * (n + 1) + n * (n + 1)"
    using Suc.IH by simp
  also have "... = (n + 2) * (n + 1)"
    by (simp add: algebra_simps)
  also have "... = Suc n * (Suc n + 1)"
    by (simp add: algebra_simps)
  finally show ?case .
qed


section \<open>Demo 3: Interactive Tactic Search & Error Repair\<close>

text \<open>
  Scenario: An agent attempts 'by auto', gets stuck with a residual subgoal,
  inspects the remaining goal via get_state, and patches it.
\<close>

lemma map_filter_commute:
  "map f (filter (\<lambda>x. P (f x)) xs) = filter P (map f xs)"
  by (induction xs) auto

end
