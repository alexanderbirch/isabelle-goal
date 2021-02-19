(*

  Goal verification framework
    - Logic
  
  This theory sets up syntax, semantics and a sequent for classical logic with no quantifiers.
  The type for atoms is arbitrary to allow reuse in different logic languages to be defined.

*)
theory Gvf_Logic imports "HOL-Library.Multiset" begin

section \<open>Syntax\<close> 

\<comment> \<open>The usual operators in bold are used for a recognizable notation\<close>
datatype 'a \<Phi>\<^sub>P = Atom 'a | Negation \<open>'a \<Phi>\<^sub>P\<close> (\<open>\<^bold>\<not>\<close>) | 
                Implication \<open>'a \<Phi>\<^sub>P\<close> \<open>'a \<Phi>\<^sub>P\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 60) | 
                Disjunction \<open>'a \<Phi>\<^sub>P\<close> \<open>'a \<Phi>\<^sub>P\<close> (infixl \<open>\<^bold>\<or>\<close> 70) | 
                Conjunction \<open>'a \<Phi>\<^sub>P\<close> \<open>'a \<Phi>\<^sub>P\<close> (infixl \<open>\<^bold>\<and>\<close> 80)

\<comment> \<open>Equivalence is defined from existing operators\<close>
abbreviation Equiv\<^sub>P :: \<open>'a \<Phi>\<^sub>P \<Rightarrow> 'a \<Phi>\<^sub>P \<Rightarrow> 'a \<Phi>\<^sub>P\<close> (infix \<open>\<^bold>\<longleftrightarrow>\<close> 60) where
  \<open>P \<^bold>\<longleftrightarrow> Q \<equiv> P \<^bold>\<longrightarrow> Q \<^bold>\<and> Q \<^bold>\<longrightarrow> P\<close>

section \<open>Semantics\<close>

\<comment> \<open>The semantics of formulas depend on a given interpretation for atoms\<close>
primrec semantics\<^sub>P :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a \<Phi>\<^sub>P \<Rightarrow> bool\<close> where
  \<open>semantics\<^sub>P f (Atom x) = f x\<close> |
  \<open>semantics\<^sub>P f (\<^bold>\<not> p) = (\<not>semantics\<^sub>P f p)\<close> |
  \<open>semantics\<^sub>P f (p \<^bold>\<longrightarrow> q) = (semantics\<^sub>P f p \<longrightarrow> semantics\<^sub>P f q)\<close> |
  \<open>semantics\<^sub>P f (p \<^bold>\<or> q) = (semantics\<^sub>P f p \<or> semantics\<^sub>P f q)\<close> |
  \<open>semantics\<^sub>P f (p \<^bold>\<and> q) = (semantics\<^sub>P f p \<and> semantics\<^sub>P f q)\<close>

\<comment> \<open>Entailment is defined\<close>
abbreviation entails :: \<open>'a \<Phi>\<^sub>P set \<Rightarrow> 'a \<Phi>\<^sub>P set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>P#\<close> 50) where
  \<open>\<Gamma> \<Turnstile>\<^sub>P# \<Delta> \<equiv> (\<forall>f. (\<forall>p\<in>\<Gamma>. semantics\<^sub>P f p) \<longrightarrow> (\<exists>p\<in>\<Delta>. semantics\<^sub>P f p))\<close>

\<comment> \<open>Entailment for a singleton rhs\<close>
abbreviation entails_singleton :: \<open>'a \<Phi>\<^sub>P set \<Rightarrow> 'a \<Phi>\<^sub>P \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>P\<close> 50) where
  \<open>\<Gamma> \<Turnstile>\<^sub>P \<Phi> \<equiv> \<Gamma> \<Turnstile>\<^sub>P# { \<Phi> }\<close>

\<comment> \<open>Not entailed, for a singleton rhs\<close>
abbreviation not_entails :: \<open>'a \<Phi>\<^sub>P set \<Rightarrow> 'a \<Phi>\<^sub>P \<Rightarrow> bool\<close> (infix \<open>\<not>\<Turnstile>\<^sub>P\<close> 50) where
  \<open>\<Gamma> \<not>\<Turnstile>\<^sub>P \<Phi> \<equiv> \<not>(\<forall>f. (\<forall>p\<in>\<Gamma>. semantics\<^sub>P f p) \<longrightarrow> semantics\<^sub>P f \<Phi>)\<close>

\<comment> \<open>Weakening of assumptions for entailment\<close>
lemma weakening_entailment: \<open>\<Sigma>' \<subseteq> \<Sigma> \<longrightarrow> \<Sigma>' \<Turnstile>\<^sub>P# \<Gamma> \<longrightarrow> \<Sigma> \<Turnstile>\<^sub>P# \<Gamma>\<close>
  by blast

section \<open>Sequent calculus\<close>

\<comment> \<open>A standard sequent calculus proof system\<close>
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

\<comment> \<open>Notation for empty lhs and singleton rhs\<close>
abbreviation provable :: \<open>'a \<Phi>\<^sub>P \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>P _\<close> 40) where
  \<open>\<turnstile>\<^sub>P p \<equiv> {#} \<turnstile>\<^sub>P# {# p #}\<close>

section \<open>Soundness\<close>

\<comment> \<open>The soundness theorem requires multiset to set conversion\<close>
theorem soundness\<^sub>P: \<open>\<Gamma> \<turnstile>\<^sub>P# \<Delta> \<Longrightarrow> set_mset \<Gamma> \<Turnstile>\<^sub>P# set_mset \<Delta>\<close>
  by (induct rule: sequent_calculus.induct) (auto)

section \<open>Collection of semantic rules\<close>

lemma neq_atom_not_entail: 
  assumes \<open>x \<noteq> y\<close> 
  shows   \<open>{ Atom x } \<not>\<Turnstile>\<^sub>P Atom y\<close> 
using assms by auto

end