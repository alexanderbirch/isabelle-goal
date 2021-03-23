(*
  Goal verification framework
    - Propositional Logic
*)  
 \<comment> \<open>This theory is an instance of the general classical logic for atoms that are natural numbers.\<close> 
                            
theory Gvf_PL imports Gvf_Logic begin

\<comment> \<open>Define the type for propositional logic formulas.\<close>
type_synonym \<Phi>\<^sub>L = \<open>nat \<Phi>\<^sub>P\<close>
\<comment> \<open>We parse the type for natural numbers to the general logic type and create a type synonym
   for this instance.\<close>

\<comment> \<open>Truth and falsity are defined.\<close>
abbreviation Truth\<^sub>L :: \<open>\<Phi>\<^sub>L\<close> (\<open>\<top>\<^sub>L\<close>) where 
  \<open>\<top>\<^sub>L \<equiv> \<^bold>\<not> (Atom 0) \<^bold>\<or> (Atom 0)\<close>
abbreviation Falsity\<^sub>L :: \<open>\<Phi>\<^sub>L\<close> (\<open>\<bottom>\<^sub>L\<close>) where 
  \<open>\<bottom>\<^sub>L \<equiv> \<^bold>\<not> \<top>\<^sub>L\<close>
\<comment> \<open>Since we base the definition on a simple tautology, we can only define this for one instance
    of the general classical logic as we need to be able to specify atoms.\<close>

section \<open>Semantics\<close>

\<comment> \<open>The semantics is easily obtained from the definition for general classical logic.\<close>
abbreviation semantics\<^sub>L :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> \<Phi>\<^sub>L \<Rightarrow> bool\<close> where
  \<open>semantics\<^sub>L f p \<equiv> semantics\<^sub>P f p\<close>
\<comment> \<open>The semantics of PL is computed the same as for the general case with the interpretation being
    a function from natural numbers (proposition identifiers) to truth values.\<close>

\<comment> \<open>The soundness result is easily proved from the general case.\<close>
theorem soundness\<^sub>L: \<open>\<turnstile>\<^sub>P p \<Longrightarrow> semantics\<^sub>L f p\<close>
  using soundness\<^sub>P by fastforce

\<comment> \<open>Entailment for propositional logic.\<close>
abbreviation entails :: \<open>\<Phi>\<^sub>L set \<Rightarrow> \<Phi>\<^sub>L set \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>L#\<close> 50) where
  \<open>\<Gamma> \<Turnstile>\<^sub>L# \<Delta> \<equiv> \<Gamma> \<Turnstile>\<^sub>P# \<Delta>\<close>

\<comment> \<open>Cleaner notation for entailment for of singleton rhs.\<close>
abbreviation entails_singleton :: \<open>\<Phi>\<^sub>L set \<Rightarrow> \<Phi>\<^sub>L \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>L\<close> 50) where
  \<open>\<Gamma> \<Turnstile>\<^sub>L \<Phi> \<equiv> \<Gamma> \<Turnstile>\<^sub>P \<Phi>\<close>

end