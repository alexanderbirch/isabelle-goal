(*

  Goal verification framework
    - Agent Specification
  
  This theory sets up the framework for specifying agents by means of predicates for enabledness 
  and Hoare triple axioms  instead of providing a function for \<T>. Instead, adopt the idea that 
  we may assume the agent specification reflects the actual model, i.e. the \<T> function complies 
  to our specification.

  TODO: Proof system and more

*)
theory Gvf_Agent_Specification imports Gvf_Hoare_Logic begin

\<comment> \<open>A type for the specification of enabledness and Hoare triple axioms\<close>
type_synonym ht_specification = \<open>(\<Phi>\<^sub>M \<times> hoare_triple) set\<close>

\<comment> \<open>State that a given \<T> complies to our assumptions, partly due to semantics of Hoare triples
    and partly due to the properties about the fixed agent\<close>
definition complies :: \<open>cond_act set \<Rightarrow> ht_specification \<Rightarrow> bel_upd_t \<Rightarrow> bool\<close> where
  \<open>complies \<Pi> S \<T> \<equiv>
    (\<forall>\<Sigma> a. \<Sigma> \<not>\<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> \<T> a \<Sigma> \<noteq> None \<longrightarrow> the (\<T> a \<Sigma>) \<not>\<Turnstile>\<^sub>L \<bottom>\<^sub>L) \<and>
    (\<forall>\<Sigma> a. \<T> a \<Sigma> \<noteq> None \<longrightarrow> (\<exists>\<phi>'. (\<phi>', basic a) \<in> \<Pi>)) \<and> 
    (\<forall>(\<Phi>, ht)\<in>S. 
      (case ht of htb \<phi> (basic n) \<psi> \<Rightarrow>
        (\<forall>M. M \<Turnstile>\<^sub>M \<Phi> \<^bold>\<and> \<phi> \<longrightarrow> (the (\<T> n (fst M)), snd M) \<Turnstile>\<^sub>M \<psi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not>\<Phi> \<^bold>\<and> \<phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)))\<close>

locale single_agent_program = single_agent + 
  fixes
    S :: ht_specification
  assumes
    \<T>_complies: \<open>complies \<Pi> S \<T>\<close>

context single_agent_program begin

(* TODO import rules from specification *)
section \<open>Proof System\<close>

inductive derive\<^sub>H :: \<open>hoare_triple \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>H\<close>) where
  \<comment> \<open>Agent specific rule import\<close>
  \<comment> \<open>Persistence of goals\<close>
  persist:  \<open>a \<noteq> (drop \<Phi>) \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ G \<Phi> \<^bold>} a \<^bold>{ (B \<Phi>) \<^bold>\<or> (G \<Phi>) \<^bold>}\<close> |
  \<comment> \<open>Infeasible actions\<close>
  inf:  \<open>\<turnstile>\<^sub>E ((\<phi>\<^sup>E) \<^bold>\<longrightarrow> \<^bold>\<not>(enabledb a)) \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>} a \<^bold>{ \<psi> \<^bold>}\<close> |
  \<comment> \<open>Frame properties on beliefs for adopt and drop\<close>
  adoptB: \<open>\<turnstile>\<^sub>H \<^bold>{ B \<Phi> \<^bold>} (adopt \<psi>) \<^bold>{ B \<Phi> \<^bold>}\<close> |
  adoptNegB: \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not> (B \<Phi>) \<^bold>} (adopt \<psi>) \<^bold>{ \<^bold>\<not> (B \<Phi>) \<^bold>}\<close> |
  dropB: \<open>\<turnstile>\<^sub>H \<^bold>{ B \<Phi> \<^bold>} (drop \<psi>) \<^bold>{ B \<Phi> \<^bold>}\<close> |
  dropNegB: \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not> (B \<Phi>) \<^bold>} (drop \<psi>) \<^bold>{ \<^bold>\<not> (B \<Phi>) \<^bold>}\<close> |
  \<comment> \<open>Effects of adopt\<close>
  adoptBG: \<open>\<not> \<turnstile>\<^sub>P (\<^bold>\<not> \<Phi>) \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ B \<Phi> \<^bold>} (adopt \<Phi>) \<^bold>{ G \<Phi> \<^bold>}\<close> |
  \<comment> \<open>Non-effect of adopt\<close>
  adoptG: \<open>\<turnstile>\<^sub>H \<^bold>{ G \<Phi> \<^bold>} (adopt \<psi>) \<^bold>{ G \<Phi> \<^bold>}\<close> |
  adoptNegG: \<open>\<not> \<turnstile>\<^sub>P \<psi> \<^bold>\<longrightarrow> \<Phi> \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not> (G \<Phi>) \<^bold>} (adopt \<psi>) \<^bold>{ \<^bold>\<not> (G \<Phi>) \<^bold>}\<close> |
  \<comment> \<open>Effects of drop\<close>
  dropG: \<open>\<turnstile>\<^sub>P \<Phi> \<^bold>\<longrightarrow> \<psi> \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ G \<Phi> \<^bold>} (drop \<psi>) \<^bold>{ \<^bold>\<not> (G \<Phi>) \<^bold>}\<close> |
  \<comment> \<open>Non-effects of drop\<close>
  dropNegG: \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not>(G \<Phi>) \<^bold>} (drop \<psi>) \<^bold>{ \<^bold>\<not>(G \<Phi>) \<^bold>}\<close> |
  dropGCon: \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not>(G (\<Phi> \<^bold>\<and> \<psi>)) \<^bold>\<and> (G \<Phi>) \<^bold>} (drop \<psi>) \<^bold>{ G \<Phi> \<^bold>}\<close> |
  \<comment> \<open>Rule for conditional actions\<close>
  rCondAct: \<open>\<turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>\<and> \<psi> \<^bold>} a \<^bold>{ \<phi>' \<^bold>} \<Longrightarrow> \<turnstile>\<^sub>M (\<phi> \<^bold>\<and> \<^bold>\<not>\<psi>) \<^bold>\<longrightarrow> \<phi>' \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>} (\<psi> \<triangleright> do a) \<^bold>{ \<phi>' \<^bold>}\<close> |
  \<comment> \<open>Structural rules\<close>
  rImp: \<open>\<turnstile>\<^sub>M \<phi>' \<^bold>\<longrightarrow> \<phi> \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>} a \<^bold>{ \<psi> \<^bold>} \<Longrightarrow> \<turnstile>\<^sub>M \<psi> \<^bold>\<longrightarrow> \<psi>' \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi>' \<^bold>} a \<^bold>{ \<psi>' \<^bold>}\<close> |
  rCon: \<open>\<turnstile>\<^sub>H \<^bold>{ \<phi>\<^sub>1 \<^bold>} a \<^bold>{ \<psi>\<^sub>1 \<^bold>} \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi>\<^sub>2 \<^bold>} a \<^bold>{ \<psi>\<^sub>2 \<^bold>} \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2 \<^bold>} a \<^bold>{ \<psi>\<^sub>1 \<^bold>\<and> \<psi>\<^sub>2 \<^bold>}\<close> |
  rDis: \<open>\<turnstile>\<^sub>H \<^bold>{ \<phi>\<^sub>1 \<^bold>} a \<^bold>{ \<psi> \<^bold>} \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi>\<^sub>2 \<^bold>} a \<^bold>{ \<psi> \<^bold>} \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2 \<^bold>} a \<^bold>{ \<psi> \<^bold>}\<close>

theorem soundness\<^sub>H: \<open>\<turnstile>\<^sub>H H \<Longrightarrow> \<Turnstile>\<^sub>H H\<close> 
  sorry

theorem completeness\<^sub>H: \<open>\<Turnstile>\<^sub>H H \<Longrightarrow> \<turnstile>\<^sub>H H\<close>
  sorry


end

section \<open>Example\<close>

\<comment> \<open>To be moved to an example theory file. Proof of concept.\<close>

\<comment> \<open>Set up some notation\<close>
abbreviation \<open>in_dropzone::\<Phi>\<^sub>L \<equiv> Atom 0\<close>
abbreviation \<open>in_room::\<Phi>\<^sub>L \<equiv> Atom 1\<close>
abbreviation \<open>collect_red::\<Phi>\<^sub>L \<equiv> Atom 2\<close>
abbreviation \<open>goto_dropzone::cap \<equiv> basic 0\<close>
abbreviation \<open>goto_room::cap \<equiv> basic 1\<close>

\<comment> \<open>Specification of the program\<close>
abbreviation \<open>\<Pi>\<^sub>x \<equiv> { (B in_dropzone) \<triangleright> do goto_room }\<close>
abbreviation \<open>M\<^sub>0\<^sub>x \<equiv> ( { in_dropzone }, { collect_red } )\<close>
abbreviation \<open>S\<^sub>x \<equiv> {(\<top>\<^sub>M, \<^bold>{ B in_dropzone \<^bold>} goto_room \<^bold>{ B in_room \<^bold>})}\<close>

\<comment> \<open>Prove that the example is an instance of the single agent program locale\<close>
\<comment> \<open>We use a trick where \<T> is simply some function that complies to our definition due Hilbert's epsilon operator i.e. the axiom of choice\<close>
interpretation example: single_agent_program \<open>SOME \<T>. complies \<Pi>\<^sub>x S\<^sub>x \<T>\<close> \<Pi>\<^sub>x M\<^sub>0\<^sub>x S\<^sub>x
proof -
  let ?\<T> = \<open>SOME \<T>. complies \<Pi>\<^sub>x S\<^sub>x \<T>\<close>
  have \<open>\<exists>x. complies \<Pi>\<^sub>x S\<^sub>x x\<close> unfolding complies_def by auto
  with someI_ex[where ?P=\<open>complies \<Pi>\<^sub>x S\<^sub>x\<close>] have complies\<^sub>x: \<open>complies \<Pi>\<^sub>x S\<^sub>x ?\<T>\<close> .
  show \<open>single_agent_program (SOME \<T>. complies \<Pi>\<^sub>x S\<^sub>x \<T>) \<Pi>\<^sub>x M\<^sub>0\<^sub>x S\<^sub>x\<close>
  proof 
    show \<open>complies \<Pi>\<^sub>x S\<^sub>x ?\<T>\<close> using complies\<^sub>x .
  next
    have \<open>\<nabla> M\<^sub>0\<^sub>x\<close>
    proof - 
      have \<open>{in_dropzone} \<not>\<Turnstile>\<^sub>L \<bottom>\<^sub>L\<close> by auto
      moreover have \<open>in_dropzone \<noteq> collect_red\<close> by simp
      with neq_atom_not_entail have \<open>{in_dropzone} \<not>\<Turnstile>\<^sub>L collect_red\<close> by metis
      moreover have \<open>{} \<not>\<Turnstile>\<^sub>L \<^bold>\<not> in_dropzone\<close> by auto
      ultimately show ?thesis unfolding is_mental_state_def by auto
    qed
    then show \<open>\<Pi>\<^sub>x \<noteq> {} \<and> \<nabla> M\<^sub>0\<^sub>x\<close> by simp
  next
    from complies\<^sub>x show \<open>\<forall>\<Sigma> a. \<Sigma> \<not>\<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> ?\<T> a \<Sigma> \<noteq> None \<longrightarrow> the (?\<T> a \<Sigma>) \<not>\<Turnstile>\<^sub>L \<bottom>\<^sub>L\<close>
      unfolding complies_def by simp    
  next
    fix a \<Sigma>
    from complies\<^sub>x show \<open>?\<T> a \<Sigma> \<noteq> None \<longrightarrow> (\<exists>\<phi>. (\<phi>, basic a) \<in> \<Pi>\<^sub>x)\<close> 
      unfolding complies_def by simp
  qed
qed


end