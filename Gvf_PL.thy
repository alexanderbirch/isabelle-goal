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

end