(*
  Goal verification framework
  - Logic
*)

\<comment> \<open>This theory sets up syntax, semantics and a sequent for classical logic with no quantifiers.
    The type for atoms is arbitrary to allow reuse in different logic languages to be defined.\<close>

theory Gvf_Logic imports "HOL-Library.Multiset" begin

section \<open>Syntax\<close> 

\<comment> \<open>The usual infix operators are in bold to avoid conflict with Isabelle's built-in operators.\<close>
datatype 'a \<Phi>\<^sub>P = Atom 'a | Negation \<open>'a \<Phi>\<^sub>P\<close> (\<open>\<^bold>\<not>\<close>) | 
                Implication \<open>'a \<Phi>\<^sub>P\<close> \<open>'a \<Phi>\<^sub>P\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 60) | 
                Disjunction \<open>'a \<Phi>\<^sub>P\<close> \<open>'a \<Phi>\<^sub>P\<close> (infixl \<open>\<^bold>\<or>\<close> 70) | 
                Conjunction \<open>'a \<Phi>\<^sub>P\<close> \<open>'a \<Phi>\<^sub>P\<close> (infixl \<open>\<^bold>\<and>\<close> 80)
\<comment> \<open>'a is a type variable for the type of atoms. 
    An element of this type is parsed to the constructor for Atom.
    The Boolean operators take one (or two) formula(s) as input (having the same type for atoms).\<close>

\<comment> \<open>Bi-implication is defined from conjunction and implication.\<close>
abbreviation Equiv\<^sub>P :: \<open>'a \<Phi>\<^sub>P \<Rightarrow> 'a \<Phi>\<^sub>P \<Rightarrow> 'a \<Phi>\<^sub>P\<close> (infix \<open>\<^bold>\<longleftrightarrow>\<close> 60) where
  \<open>P \<^bold>\<longleftrightarrow> Q \<equiv> P \<^bold>\<longrightarrow> Q \<^bold>\<and> Q \<^bold>\<longrightarrow> P\<close>

\<comment> \<open>Example (untyped free variable atoms).\<close>
value \<open>Atom P \<^bold>\<longrightarrow> (Atom P \<^bold>\<longrightarrow> Atom Q) \<^bold>\<longrightarrow> Atom Q\<close>

section \<open>Semantics\<close>

\<comment> \<open>The semantics function takes an interpretation and a formula and returns a Boolean.\<close>
primrec semantics\<^sub>P :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a \<Phi>\<^sub>P \<Rightarrow> bool\<close> where
  \<open>semantics\<^sub>P f (Atom x) = f x\<close> |
  \<open>semantics\<^sub>P f (\<^bold>\<not> p) = (\<not>semantics\<^sub>P f p)\<close> |
  \<open>semantics\<^sub>P f (p \<^bold>\<longrightarrow> q) = (semantics\<^sub>P f p \<longrightarrow> semantics\<^sub>P f q)\<close> |
  \<open>semantics\<^sub>P f (p \<^bold>\<or> q) = (semantics\<^sub>P f p \<or> semantics\<^sub>P f q)\<close> |
  \<open>semantics\<^sub>P f (p \<^bold>\<and> q) = (semantics\<^sub>P f p \<and> semantics\<^sub>P f q)\<close>
\<comment> \<open>The interpretation f is a function from atom (element of type 'a) to Boolean.
    In the case of an atom the value is looked up and returned.
    In case of a Boolean operator, we can exploit Isabelle's built-in operators.
    This could also be achieved by proper coding of if-then structures.\<close>

\<comment> \<open>Example (holds for any f, P and Q).\<close>
lemma \<open>semantics\<^sub>P f (Atom P \<^bold>\<longrightarrow> (Atom P \<^bold>\<longrightarrow> Atom Q) \<^bold>\<longrightarrow> Atom Q)\<close> by simp

\<comment> \<open>Entailment.\<close>
abbreviation entails :: \<open>'a \<Phi>\<^sub>P set \<Rightarrow> 'a \<Phi>\<^sub>P set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>P#\<close> 50) where
  \<open>\<Gamma> \<Turnstile>\<^sub>P# \<Delta> \<equiv> (\<forall>f. (\<forall>p\<in>\<Gamma>. semantics\<^sub>P f p) \<longrightarrow> (\<exists>p\<in>\<Delta>. semantics\<^sub>P f p))\<close>
\<comment> \<open>L entails R if, for all interpretations, all formulas in L true implies at least one in R true.\<close>

\<comment> \<open>Example.\<close>
lemma \<open>{ Atom P } \<Turnstile>\<^sub>P# { Atom P, Atom Q }\<close> by simp

\<comment> \<open>Entailment for a singleton on rhs.\<close>
abbreviation entails_singleton :: \<open>'a \<Phi>\<^sub>P set \<Rightarrow> 'a \<Phi>\<^sub>P \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>P\<close> 50) where
  \<open>\<Gamma> \<Turnstile>\<^sub>P \<Phi> \<equiv> \<Gamma> \<Turnstile>\<^sub>P# { \<Phi> }\<close>

\<comment> \<open>Example.\<close>
lemma \<open>{ Atom P \<^bold>\<and> Atom Q } \<Turnstile>\<^sub>P Atom P\<close> by simp

\<comment> \<open>Example.\<close>
lemma \<open>Q \<noteq> P \<longrightarrow> \<not> { Atom Q } \<Turnstile>\<^sub>P Atom P\<close> by auto

\<comment> \<open>Weakening of assumptions for entailment\<close>
lemma weakening_entailment: \<open>\<Sigma>' \<subseteq> \<Sigma> \<longrightarrow> \<Sigma>' \<Turnstile>\<^sub>P# \<Gamma> \<longrightarrow> \<Sigma> \<Turnstile>\<^sub>P# \<Gamma>\<close>  by blast

\<comment> \<open>Example.\<close>
lemma \<open>{ P\<^sub>1, P\<^sub>2 } \<Turnstile>\<^sub>P# { Q } \<longrightarrow> { P\<^sub>1, P\<^sub>2, P\<^sub>3 } \<Turnstile>\<^sub>P# { Q }\<close> using weakening_entailment by simp

section \<open>Sequent calculus\<close>

\<comment> \<open>A standard sequent calculus proof system.\<close>
inductive sequent_calculus :: \<open>'a \<Phi>\<^sub>P multiset \<Rightarrow> 'a \<Phi>\<^sub>P multiset \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<^sub>P#\<close> 40) where
  \<comment> \<open>Non-branching\<close>
  Axiom:  \<open>{# p #} + \<Gamma> \<turnstile>\<^sub>P# \<Delta> + {# p #}\<close> |
  L_Neg:  \<open>\<Gamma> \<turnstile>\<^sub>P# \<Delta> + {# p #} \<Longrightarrow> \<Gamma> + {# \<^bold>\<not> p #} \<turnstile>\<^sub>P# \<Delta>\<close> |
  R_Neg:  \<open>\<Gamma> + {# p #} \<turnstile>\<^sub>P# \<Delta> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>P# \<Delta> + {# \<^bold>\<not> p #}\<close> |
  R_Imp:  \<open>\<Gamma> + {# p #} \<turnstile>\<^sub>P# \<Delta> + {# q #} \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>P# \<Delta> + {# p \<^bold>\<longrightarrow> q #}\<close> |
  R_Or:   \<open>\<Gamma> \<turnstile>\<^sub>P# \<Delta> + {# p, q #} \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>P# \<Delta> + {# p \<^bold>\<or> q #}\<close> |
  L_And:  \<open>\<Gamma> + {# p, q #} \<turnstile>\<^sub>P# \<Delta> \<Longrightarrow> \<Gamma> + {# p \<^bold>\<and> q #} \<turnstile>\<^sub>P# \<Delta>\<close> |
  \<comment> \<open>Branching\<close>
  R_And:  \<open>\<Gamma> \<turnstile>\<^sub>P# \<Delta> + {# p #} \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>P# \<Delta> + {# q #} \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>P# \<Delta> + {# p \<^bold>\<and> q #}\<close> |
  L_Or:   \<open>\<Gamma> + {# p #} \<turnstile>\<^sub>P# \<Delta> \<Longrightarrow> \<Gamma> + {# q #} \<turnstile>\<^sub>P# \<Delta> \<Longrightarrow> \<Gamma> + {# p \<^bold>\<or> q #} \<turnstile>\<^sub>P# \<Delta>\<close> |
  L_Imp:  \<open>\<Gamma> \<turnstile>\<^sub>P# \<Delta> + {# p #} \<Longrightarrow> \<Gamma> + {# q #} \<turnstile>\<^sub>P# \<Delta> \<Longrightarrow> \<Gamma> + {# p \<^bold>\<longrightarrow> q #} \<turnstile>\<^sub>P# \<Delta>\<close>
\<comment> \<open>The arrow ==> signifies that the rightmost predicate (must be of the inductive type) may be
    introduced following proof of the assumptions. Axioms may either be directly introduced,
    or follow from non-inductive preconditions. The inductive rules specify the construction of
    more complex proofs from existing ones.\<close>

\<comment> \<open>Example.\<close>
lemma \<open>{# Atom P \<^bold>\<and> Atom Q #} \<turnstile>\<^sub>P# {# Atom P #}\<close> using L_And Axiom by fastforce

\<comment> \<open>Notation for empty lhs and singleton rhs.\<close>
abbreviation provable :: \<open>'a \<Phi>\<^sub>P \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>P _\<close> 40) where
  \<open>\<turnstile>\<^sub>P p \<equiv> {#} \<turnstile>\<^sub>P# {# p #}\<close>

\<comment> \<open>Example single-step.\<close>
lemma \<open>\<turnstile>\<^sub>P Atom P \<^bold>\<longrightarrow> (Atom P \<^bold>\<longrightarrow> Atom Q) \<^bold>\<longrightarrow> Atom Q\<close> 
proof -
  from R_Imp have \<open>{#} \<turnstile>\<^sub>P# {# Atom P \<^bold>\<longrightarrow> (Atom P \<^bold>\<longrightarrow> Atom Q) \<^bold>\<longrightarrow> Atom Q #}\<close>
    if \<open>{# Atom P #} \<turnstile>\<^sub>P# {# (Atom P \<^bold>\<longrightarrow> Atom Q) \<^bold>\<longrightarrow> Atom Q #}\<close> using that by simp
  with R_Imp have ?thesis 
    if \<open>{# Atom P \<^bold>\<longrightarrow> Atom Q, Atom P #} \<turnstile>\<^sub>P# {# Atom Q #}\<close> using that by auto
  with L_Imp have ?thesis 
    if  \<open>{# Atom P #} \<turnstile>\<^sub>P# {# Atom Q #} + {# Atom P #}\<close>
    and \<open>{# Atom P #} + {# Atom Q #} \<turnstile>\<^sub>P# {# Atom Q #}\<close> using that by auto
  with Axiom show ?thesis by auto
qed
\<comment> \<open>The hassle of manually proving even simple formulas calls for an implementation of proof tactics.
    The deep embedding of the logic means that trivial formulas cannot be proved using Isabelle's
    vast knowledge about logic formulas, however I am not sure if there is a good way around this.\<close>

section \<open>Soundness\<close>

\<comment> \<open>The soundness theorem.\<close>
theorem soundness\<^sub>P: \<open>\<Gamma> \<turnstile>\<^sub>P# \<Delta> \<Longrightarrow> set_mset \<Gamma> \<Turnstile>\<^sub>P# set_mset \<Delta>\<close>
  by (induct rule: sequent_calculus.induct) (auto)
\<comment> \<open>Proving the formula implies that it is valid. Because the sequent calculus is based on the use
    of multisets, whereas the semantics is based on regular sets, a conversion is required.
    In general going from multisets to sets is more clean due to the former always being finite.\<close>

section \<open>Collection of semantic rules\<close>

\<comment> \<open>Proofs about the formulas that are not entailed are in general harder, so the idea is to collect
    a number of proofs in a small library as we encounter the need to complete such proofs.\<close>
lemma neq_atom_not_entail: 
  assumes \<open>x \<noteq> y\<close> 
  shows   \<open>\<not> { Atom x } \<Turnstile>\<^sub>P Atom y\<close> 
  using assms by auto

end