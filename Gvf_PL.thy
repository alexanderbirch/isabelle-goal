(*

  Goal verification framework
    - Propositional Logic
  
  This theory is an instance of the general logic for propositions that are natural numbers.

*)
theory Gvf_PL imports Gvf_Logic begin

\<comment> \<open>Define the type for propositional logic\<close>
type_synonym \<Phi>\<^sub>L = \<open>nat \<Phi>\<^sub>P\<close>

\<comment> \<open>Truth and falsity are individually defined requiring a set type for atoms\<close>
abbreviation Truth\<^sub>L :: \<open>\<Phi>\<^sub>L\<close> (\<open>\<top>\<^sub>L\<close>) where 
  \<open>\<top>\<^sub>L \<equiv> \<^bold>\<not> (Atom 0) \<^bold>\<or> (Atom 0)\<close>
abbreviation Falsity\<^sub>L :: \<open>\<Phi>\<^sub>L\<close> (\<open>\<bottom>\<^sub>L\<close>) where 
  \<open>\<bottom>\<^sub>L \<equiv> \<^bold>\<not> \<top>\<^sub>L\<close>

section \<open>Semantics\<close>

\<comment> \<open>The semantics is easily obtained from the general definition\<close>
abbreviation semantics\<^sub>L :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> \<Phi>\<^sub>L \<Rightarrow> bool\<close> where
  \<open>semantics\<^sub>L f p \<equiv> semantics\<^sub>P f p\<close>

\<comment> \<open>The soundness result is easily proved from the general case\<close>
lemma soundness\<^sub>L: \<open>\<turnstile>\<^sub>P p \<Longrightarrow> semantics\<^sub>L f p\<close>
  using soundness\<^sub>P by fastforce

\<comment> \<open>Entailment for propositional logic\<close>
abbreviation entails :: \<open>\<Phi>\<^sub>L set \<Rightarrow> \<Phi>\<^sub>L set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>L#\<close> 50) where
  \<open>\<Gamma> \<Turnstile>\<^sub>L# \<Delta> \<equiv> \<Gamma> \<Turnstile>\<^sub>P# \<Delta>\<close>

abbreviation not_entails :: \<open>\<Phi>\<^sub>L set \<Rightarrow> \<Phi>\<^sub>L \<Rightarrow> bool\<close> (infix \<open>\<not>\<Turnstile>\<^sub>L\<close> 50) where
  \<open>\<Gamma> \<not>\<Turnstile>\<^sub>L \<Phi> \<equiv> \<Gamma> \<not>\<Turnstile>\<^sub>P \<Phi>\<close>

abbreviation entails_singleton :: \<open>\<Phi>\<^sub>L set \<Rightarrow> \<Phi>\<^sub>L \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>L\<close> 50) where
  \<open>\<Gamma> \<Turnstile>\<^sub>L \<Phi> \<equiv> \<Gamma> \<Turnstile>\<^sub>P \<Phi>\<close>

end