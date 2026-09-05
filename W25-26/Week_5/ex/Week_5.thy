(*<*)
theory Week_5
imports Main
begin
(*>*)
text \<open>\ExerciseSheet{5}{}\<close>

text \<open>
  \paragraph{Setup Instructions: Isabelle PIDE MCP and Coding Agents}
  In this tutorial, we explore AI-assisted theorem proving, interactive proof development,
  and automated reasoning in Isabelle/HOL.

  To enable an AI coding agent to interact directly with your Isabelle environment:
  \begin{enumerate}
    \item \textbf{Clone PIDE MCP}: Clone the repository from
      \url{https://github.com/kappelmann/isabelle-pide-mcp}
      and switch to branch \texttt{Isabelle2025-2}:
      \begin{center}
        \texttt{git clone -b Isabelle2025-2 https://github.com/kappelmann/isabelle-pide-mcp}
      \end{center}
    \item \textbf{Register Component}: Follow the instructions in the repository's
      \texttt{README.md} to register the MCP server as an Isabelle component:
      \begin{center}
        \texttt{isabelle components -u <path-to-isabelle-pide-mcp>}
      \end{center}
      Please read the \texttt{README.md} carefully for full setup and agent configuration options.
    \item \textbf{Recommended Coding Agent}: We recommend using \textbf{OpenCode} (\url{https://opencode.ai}),
      an open-source terminal coding agent supporting MCP. OpenCode connects to free model tiers
      (such as \texttt{opencode/big-pickle}, Google Gemini 2.5 Flash / Flash-Lite, or local models via Ollama),
      allowing you to complete the exercises completely free of charge.
    \item \textbf{Building Skill Files \& Agent Definitions}:
      In OpenCode, you can define specialized \textbf{skills} and \textbf{subagents}:
      \begin{itemize}
        \item \emph{Skills}: Stored in \texttt{.opencode/skills/<name>/SKILL.md} or \texttt{\textasciitilde/.agents/skills/<name>/SKILL.md}
          with YAML frontmatter (\texttt{name}, \texttt{description}) followed by instructions.
        \item \emph{Subagents}: Stored in \texttt{.opencode/agents/<name>.md} or \texttt{\textasciitilde/.config/opencode/agents/<name>.md}
          with frontmatter specifying \texttt{mode: all}, \texttt{model}, and a dedicated system prompt.
      \end{itemize}
    \item \textbf{The Four Agent Proving Roles}:
      As discussed in the lectures on agentic proving architectures, complex formal proofs benefit from
      coordinating four specialized roles:
      \begin{enumerate}
        \item \textbf{Planner / Sketcher Agent}: High-level architectural reasoning, decomposing main goals,
          discovering auxiliary invariant lemmas, and sketching Isar proof skeletons with \texttt{sorry}.
        \item \textbf{Prover / Coder Agent}: Tactical execution, expanding equations, and filling routine subgoals.
        \item \textbf{Repairer Agent}: Interactive compiler feedback loop via \texttt{isabelle-pide-mcp}, inspecting
          goal states, diagnosing type/syntax errors and failed tactics, generalizing variables, and eliminating \texttt{sorry}.
        \item \textbf{Critic / Sledgehammer Agent}: Soundness evaluation, circularity checks, and invoking automated
          provers (E, Vampire, Z3, CVC4) to compress multi-line proofs into single-line automated steps.
      \end{enumerate}
  \end{enumerate}
\<close>

text \<open>\Exercise{Recursive Summation and Counterexample Finding}\<close>

text \<open>
  Define a recursive function \<open>sum_upto :: nat \<Rightarrow> nat\<close> that calculates the sum of the
  first \<open>n\<close> natural numbers:
  \[
    \text{sum\_upto}(n) = \sum_{i=1}^n i = 1 + 2 + \dots + n
  \]
  such that $\text{sum\_upto}(0) = 0$ and $\text{sum\_upto}(n+1) = (n+1) + \text{sum\_upto}(n)$.
\<close>

fun sum_upto :: "nat \<Rightarrow> nat" where
(*<*)
  "sum_upto 0 = 0"
| "sum_upto (Suc n) = Suc n + sum_upto n"
(*>*)

text \<open>
  Before trying to prove a theorem, it is good practice to test conjectures with automated
  counterexample generators such as \<open>quickcheck\<close> and \<open>nitpick\<close>.
  Consider the erroneous conjecture:
  \[
    \text{sum\_upto}(n) = n \cdot (n + 1)
  \]
  In Isabelle, one can formulate this conjecture and run \<open>quickcheck\<close> or \<open>nitpick\<close> to
  automatically find a counterexample (e.g., for $n = 1$, $\text{sum\_upto}(1) = 1 \neq 2$).
\<close>


text \<open>\Exercise{Draft, Sketch, and Prove (DSP): Gauss Summation Formula}\<close>

text \<open>
  Gauss' famous summation formula states that:
  \[
    2 \cdot \text{sum\_upto}(n) = n \cdot (n + 1)
  \]
  In the two-stage ``Draft, Sketch, and Prove'' (DSP) architecture used by modern AI proving agents,
  one first drafts a high-level proof sketch with intermediate goals marked with \<open>sorry\<close>,
  verifying that the structural flow of the proof is sound, before completing each individual step.

  Prove this formula by induction on \<open>n\<close> using a structured Isar proof with explicit equational
  reasoning (\<open>also have ... finally show ?case\<close>).
\<close>

lemma sum_upto_gauss: "2 * sum_upto n = n * (n + 1)"
(*<*)
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
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
(*>*)

text \<open>\Exercise{Proof Automation and Sledgehammer}\<close>

text \<open>
  While the step-by-step equational proof in the previous exercise makes every algebraic transformation
  explicit, automated reasoning tools can dramatically shorten proof construction.

  Use Isabelle's automated proof tools (such as \<open>sledgehammer\<close> or the simplifier with
  algebraic simplification rules) to prove the Gauss summation theorem in a single line.
\<close>

lemma sum_upto_gauss_auto: "2 * sum_upto n = n * (n + 1)"
(*<*)
  by (induction n) (auto simp: algebra_simps)
(*>*)

text \<open>\Exercise{Accumulator-Based Tail-Recursive Summation}\<close>

text \<open>
  In Week 3, we discussed accumulator generalisation for list recursion. The same technique applies
  to numerical recursion.
  
  Define a tail-recursive function \<open>sum_upto_acc :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> that accumulates the
  running sum in an extra argument:
  \[
    \text{sum\_upto\_acc}(0, \text{acc}) = \text{acc} \quad \text{and} \quad
    \text{sum\_upto\_acc}(n+1, \text{acc}) = \text{sum\_upto\_acc}(n, n + 1 + \text{acc})
  \]
\<close>

fun sum_upto_acc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
(*<*)
  "sum_upto_acc 0 acc = acc"
| "sum_upto_acc (Suc n) acc = sum_upto_acc n (Suc n + acc)"
(*>*)

text \<open>
  Prove the invariant generalisation lemma relating \<open>sum_upto\_acc\<close> to \<open>sum_upto\<close>:
  \[
    \forall \text{acc}.\ \text{sum\_upto\_acc}(n, \text{acc}) = \text{sum\_upto}(n) + \text{acc}
  \]
  Use induction on \<open>n\<close> with an arbitrary accumulator \<open>acc\<close>.
\<close>

lemma sum_upto_acc_eq: "sum_upto_acc n acc = sum_upto n + acc"
(*<*)
  by (induction n arbitrary: acc) auto
(*>*)

text \<open>
  Conclude that the tail-recursive summation starting with an accumulator of 0 satisfies the
  closed-form Gauss formula.
\<close>

lemma sum_upto_acc_gauss: "2 * sum_upto_acc n 0 = n * (n + 1)"
(*<*)
  using sum_upto_acc_eq[of n 0] sum_upto_gauss by simp
(*>*)

text \<open>\Exercise{Multi-Agent Proof Engineering: Stack Machine Compiler Correctness}\<close>

text \<open>
  A classic benchmark in verified compilation is the correctness of an expression compiler targeting
  a stack machine.
  Consider an expression datatype supporting integer constants, addition, and multiplication:
\<close>

datatype exp = Val int | Plus exp exp | Mult exp exp

datatype instr = PUSH int | ADD | MULT

fun eval :: "exp \<Rightarrow> int" where
  "eval (Val n) = n"
| "eval (Plus e1 e2) = eval e1 + eval e2"
| "eval (Mult e1 e2) = eval e1 * eval e2"

text \<open>
  The stack machine executes a sequence of instructions on an integer stack:
\<close>

fun exec :: "instr list \<Rightarrow> int list \<Rightarrow> int list" where
  "exec [] s = s"
| "exec (PUSH n # ins) s = exec ins (n # s)"
| "exec (ADD # ins) (n2 # n1 # s) = exec ins ((n1 + n2) # s)"
| "exec (ADD # ins) _ = []"
| "exec (MULT # ins) (n2 # n1 # s) = exec ins ((n1 * n2) # s)"
| "exec (MULT # ins) _ = []"

text \<open>
  The compiler compiles an expression into a list of postfix instructions:
\<close>

fun compile :: "exp \<Rightarrow> instr list" where
  "compile (Val n) = [PUSH n]"
| "compile (Plus e1 e2) = compile e1 @ compile e2 @ [ADD]"
| "compile (Mult e1 e2) = compile e1 @ compile e2 @ [MULT]"

text \<open>
  \paragraph{Task A: Direct Proof Failure with a Single LLM Agent}
  The target correctness theorem states:
  \[
    \text{exec}(\text{compile}(e), []) = [\text{eval}(e)]
  \]
  \begin{enumerate}
    \item Attempt to prove this theorem directly in one shot using OpenCode with a free model tier
      (e.g., \texttt{opencode/big-pickle} or Gemini Flash) via the Isabelle PIDE MCP server.
    \item \textbf{Observe and document the failure}: Direct structural induction on $e$ fails because
      \texttt{compile} concatenates instruction sequences with \texttt{@}, whereas \texttt{exec} is
      defined recursively on instruction lists. Without an append-distribution or continuation lemma,
      the induction hypothesis cannot be applied to recursive subexpressions. A single-shot LLM typically
      gets stuck in infinite repair loops, generates invalid Isar scopes, or hallucinates non-existent lemmas.
  \end{enumerate}

  \paragraph{Task B: Skill Engineering for Multi-Agent Proving}
  Now, build two cooperating skill files (or subagent definitions) in OpenCode:
  \begin{enumerate}
    \item \textbf{Planner Skill (\texttt{isabelle-planner})}:
      Creates a proof plan by discovering the necessary generalized invariant:
      \[
        \text{exec}(\text{compile}(e) @ \text{ins}, s) = \text{exec}(\text{ins}, \text{eval}(e) \# s)
      \]
      The planner drafts this lemma with \texttt{sorry}, and completes the proof of
      \texttt{compiler\_correct} by instantiating the helper lemma with empty lists (\texttt{ins = []}, \texttt{s = []}).
      \emph{Important}: Name the instruction stream variable \texttt{ins} or \texttt{ils}; do \textbf{not}
      name it \texttt{is}, because \texttt{is} is a reserved Isar keyword!
    \item \textbf{Repairer Skill (\texttt{isabelle-repairer})}:
      Connects to \texttt{isabelle-pide-mcp} to inspect compiler diagnostics and remaining subgoals.
      The repairer reads the sorried lemma, supplies the generalization variables
      (\texttt{induction e arbitrary: ins s}), handles algebraic properties, and verifies that the proof
      reaches 0 errors and eliminates all \texttt{sorry} statements.
  \end{enumerate}
  Verify that chaining your Planner agent followed by your Repairer agent successfully solves the theorem!
\<close>

lemma exec_compile: "exec (compile e @ ins) s = exec ins (eval e # s)"
(*<*)
  by (induction e arbitrary: ins s) simp_all
(*>*)

theorem compiler_correct: "exec (compile e) [] = [eval e]"
(*<*)
  using exec_compile[where ins="[]" and s="[]"] by simp
(*>*)

(*<*)
end
(*>*)
