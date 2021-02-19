(*

  Goal verification framework
    - Mental States
  
  This theory introduces mental states and mental state formulas.
  The syntax and semantics of mental state formulas is defined.
  A proof system for mental state formulas is proved sound.

*)
theory Gvf_Mental_States imports Gvf_PL begin
                                      
section \<open>Properties of mental states\<close>

\<comment> \<open>We set up a type for mental states\<close>
type_synonym mental_state = \<open>(\<Phi>\<^sub>L set \<times> \<Phi>\<^sub>L set)\<close> 

\<comment> \<open>The definition constrains elements of the type and may be introduced where needed.\<close>
definition is_mental_state :: \<open>mental_state \<Rightarrow> bool\<close> (\<open>\<nabla>\<close>) where
  \<open>\<nabla> x \<equiv> let (\<Sigma>, \<Gamma>) = x in 
    \<Sigma> \<not>\<Turnstile>\<^sub>L \<bottom>\<^sub>L           \<comment> \<open>\<Sigma> is consistent\<close>
      \<and> (\<forall>\<gamma>\<in>\<Gamma>.                    \<comment> \<open>for any \<gamma> \<in> \<Gamma>\<close>
        \<Sigma> \<not>\<Turnstile>\<^sub>L \<gamma>              \<comment> \<open>(i) \<gamma> is not entailed by the agent's beliefs\<close> 
        \<and> {} \<not>\<Turnstile>\<^sub>L \<^bold>\<not> \<gamma>)\<close>   \<comment> \<open>(ii) \<gamma> is consistent\<close>

\<comment> \<open>If \<gamma>' is weaker than a consistent formula \<gamma>, it must itself be consistent\<close>
lemma \<open>\<not> {} \<Turnstile>\<^sub>L \<^bold>\<not> \<gamma> \<longrightarrow> {} \<Turnstile>\<^sub>L \<gamma> \<^bold>\<longrightarrow> \<gamma>' \<longrightarrow> \<not> {} \<Turnstile>\<^sub>L \<^bold>\<not> \<gamma>'\<close>
  by force

\<comment> \<open>Every member (of the goal set) must be weaker than \<bottom>, but not weaker than any belief \<sigma>\<close>
lemma \<open>\<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<forall>\<gamma>\<in>\<Gamma>. {} \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<^bold>\<longrightarrow> \<gamma> \<and> \<not> (\<exists>\<sigma>\<in>\<Sigma>. {} \<Turnstile>\<^sub>L \<sigma> \<^bold>\<longrightarrow> \<gamma>))\<close>
  unfolding is_mental_state_def by fastforce

section \<open>Syntax of mental state formulas\<close>

\<comment> \<open>Atoms are now the special belief and goal modalities\<close>
datatype Atoms\<^sub>M = Bl \<Phi>\<^sub>L | Gl \<Phi>\<^sub>L

\<comment> \<open>We set up a type for mental state formulas\<close>
type_synonym \<Phi>\<^sub>M = \<open>Atoms\<^sub>M \<Phi>\<^sub>P\<close>

\<comment> \<open>We hide the nesting in the notation\<close>
syntax
  "_G" :: \<open>\<Phi>\<^sub>L \<Rightarrow> \<Phi>\<^sub>M\<close>  (\<open>G _\<close> 55)
  "_B" :: \<open>\<Phi>\<^sub>L \<Rightarrow> \<Phi>\<^sub>M\<close>  (\<open>B _\<close> 55)
translations
  "G \<Phi>" \<rightharpoonup> "(Gvf_Logic.Atom (Atoms\<^sub>M.Gl \<Phi>))"
  "B \<Phi>" \<rightharpoonup> "(Gvf_Logic.Atom (Atoms\<^sub>M.Bl \<Phi>))"

abbreviation Truth\<^sub>M :: \<open>\<Phi>\<^sub>M\<close> (\<open>\<top>\<^sub>M\<close>) where 
  \<open>\<top>\<^sub>M \<equiv> \<^bold>\<not> (B (Atom 0)) \<^bold>\<or> (B (Atom 0))\<close>
abbreviation Falsity\<^sub>L :: \<open>\<Phi>\<^sub>M\<close> (\<open>\<bottom>\<^sub>M\<close>) where 
  \<open>\<bottom>\<^sub>M \<equiv> \<^bold>\<not> \<top>\<^sub>M\<close>

section \<open>Semantics\<close>

\<comment> \<open>Semantics of atoms for mental state formulas is derived given a mental state\<close>
primrec semantics\<^sub>M' :: \<open>mental_state \<Rightarrow> Atoms\<^sub>M \<Rightarrow> bool\<close> where
  \<open>semantics\<^sub>M' M (Bl \<Phi>) = (let (\<Sigma>, _) = M in \<Sigma> \<Turnstile>\<^sub>L \<Phi>)\<close> |
  \<comment> \<open>The subgoal property for goals is defined in the semantics to avoid problems\<close>
  \<open>semantics\<^sub>M' M (Gl \<Phi>) = (let (\<Sigma>, \<Gamma>) = M in \<Sigma> \<not>\<Turnstile>\<^sub>L \<Phi> \<and> (\<exists>\<gamma>\<in>\<Gamma>. {} \<Turnstile>\<^sub>L \<gamma> \<^bold>\<longrightarrow> \<Phi>))\<close>

\<comment> \<open>We reuse the semantics of the usual logical operators\<close>
abbreviation semantics\<^sub>M :: \<open>mental_state \<Rightarrow> \<Phi>\<^sub>M \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>M\<close> 50) where
  \<open>M \<Turnstile>\<^sub>M \<phi> \<equiv> semantics\<^sub>P (semantics\<^sub>M' M) \<phi>\<close>

section \<open>Various proofs\<close>

\<comment> \<open>An agent cannot have a goal to achieve a tautology\<close>
lemma \<open>\<nabla> M \<longrightarrow> \<not> M \<Turnstile>\<^sub>M G \<top>\<^sub>L\<close> 
  unfolding is_mental_state_def by auto

\<comment> \<open>An agent does not have inconsistent beliefs/goals\<close>
lemma not_modal_False: \<open>\<nabla> M \<longrightarrow> M \<Turnstile>\<^sub>M \<^bold>\<not> (B \<bottom>\<^sub>L)\<close> \<open>\<nabla> M \<longrightarrow> M \<Turnstile>\<^sub>M \<^bold>\<not> (G \<bottom>\<^sub>L)\<close>
  unfolding is_mental_state_def by auto

\<comment> \<open>Properties of the goal modality\<close>
lemma G_properties:
  shows \<open>\<not> (\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M (G \<Phi> \<^bold>\<longrightarrow> \<psi>) \<^bold>\<longrightarrow> (G \<Phi>) \<^bold>\<longrightarrow> (G \<psi>))\<close>
    and \<open>\<not> (\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M (G \<Phi> \<^bold>\<and> (\<Phi> \<^bold>\<longrightarrow> \<psi>)) \<^bold>\<longrightarrow> (G \<psi>))\<close>
    and \<open>\<not> (\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M (G \<Phi>) \<^bold>\<and> (G \<psi>) \<^bold>\<longrightarrow> (G \<Phi> \<^bold>\<and> \<psi>))\<close>
    and \<open>{} \<Turnstile>\<^sub>L \<Phi> \<^bold>\<longleftrightarrow> \<psi> \<longrightarrow> \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M (G \<Phi>) \<^bold>\<longleftrightarrow> (G \<psi>)\<close>
proof -
  let ?\<psi> = \<open>Atom 0\<close> and
      ?\<Phi> = \<open>Atom 1\<close>
  show \<open>\<not> (\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M (G (\<Phi> \<^bold>\<longrightarrow> \<psi>)) \<^bold>\<longrightarrow> (G \<Phi>) \<^bold>\<longrightarrow> (G \<psi>))\<close>
  proof 
    assume *: \<open>\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M (G \<Phi> \<^bold>\<longrightarrow> \<psi>) \<^bold>\<longrightarrow> (G \<Phi>) \<^bold>\<longrightarrow> (G \<psi>)\<close>
    \<comment> \<open>Counter example\<close>
    let ?\<Sigma> = \<open>{}\<close> and ?\<Gamma> = \<open>{ ?\<Phi> \<^bold>\<longrightarrow> ?\<psi>, ?\<Phi> }\<close>
    have \<open>\<not> (?\<Sigma>, ?\<Gamma>) \<Turnstile>\<^sub>M (G ?\<Phi> \<^bold>\<longrightarrow> ?\<psi>) \<^bold>\<longrightarrow> (G ?\<Phi>) \<^bold>\<longrightarrow> (G ?\<psi>)\<close> by auto
    moreover have \<open>\<nabla> (?\<Sigma>, ?\<Gamma>)\<close> unfolding is_mental_state_def by auto
    ultimately show False using * by blast      
  qed
  show \<open>\<not> (\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M (G \<Phi> \<^bold>\<and> (\<Phi> \<^bold>\<longrightarrow> \<psi>)) \<^bold>\<longrightarrow> (G \<psi>))\<close>
  proof
    assume *: \<open>\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M (G \<Phi> \<^bold>\<and> (\<Phi> \<^bold>\<longrightarrow> \<psi>)) \<^bold>\<longrightarrow> (G \<psi>)\<close>
    \<comment> \<open>Counter example\<close>
    let ?\<Sigma> = \<open>{ ?\<psi> }\<close> and ?\<Gamma> = \<open>{ ?\<Phi> \<^bold>\<and> (?\<Phi> \<^bold>\<longrightarrow> ?\<psi>) }\<close>
    have \<open>\<not> (?\<Sigma>, ?\<Gamma>) \<Turnstile>\<^sub>M (G ?\<Phi> \<^bold>\<and> (?\<Phi> \<^bold>\<longrightarrow> ?\<psi>)) \<^bold>\<longrightarrow> (G ?\<psi>)\<close>
      by auto
    moreover have \<open>\<nabla> (?\<Sigma>, ?\<Gamma>)\<close> unfolding is_mental_state_def by auto
    ultimately show False using * by blast
    qed
  show \<open>\<not> (\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M (G \<Phi>) \<^bold>\<and> (G \<psi>) \<^bold>\<longrightarrow> (G \<Phi> \<^bold>\<and> \<psi>))\<close>
  proof
    assume *: \<open>\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M (G \<Phi>) \<^bold>\<and> (G \<psi>) \<^bold>\<longrightarrow> (G \<Phi> \<^bold>\<and> \<psi>)\<close>
    \<comment> \<open>Counter example\<close>
    let ?\<Sigma> = \<open>{}\<close> and 
        ?\<Gamma> = \<open>{ ?\<Phi>, ?\<psi> }\<close>
    have \<open>\<not> (?\<Sigma>, ?\<Gamma>) \<Turnstile>\<^sub>M (G ?\<Phi>) \<^bold>\<and> (G ?\<psi>) \<^bold>\<longrightarrow> (G ?\<Phi> \<^bold>\<and> ?\<psi>)\<close>
      by auto
    moreover have \<open>\<nabla> (?\<Sigma>, ?\<Gamma>)\<close>
      unfolding is_mental_state_def by auto
    ultimately show False 
      using * by blast
  qed
  show \<open>{} \<Turnstile>\<^sub>L \<Phi> \<^bold>\<longleftrightarrow> \<psi> \<longrightarrow> \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M (G \<Phi>) \<^bold>\<longleftrightarrow> (G \<psi>)\<close>
    by simp
qed

section \<open>Provability\<close>

\<comment> \<open>A proof system for mental state formulas\<close>
inductive derive\<^sub>M :: \<open>\<Phi>\<^sub>M \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>M _\<close> 40) where
  \<comment> \<open>Derive classical tautologies\<close>
  R1: \<open>\<turnstile>\<^sub>P \<phi> \<Longrightarrow> \<turnstile>\<^sub>M \<phi>\<close> |
  \<comment> \<open>Properties of beliefs\<close> 
  R2: \<open>\<turnstile>\<^sub>P \<Phi> \<Longrightarrow> \<turnstile>\<^sub>M (B \<Phi>)\<close> |
  A1: \<open>\<turnstile>\<^sub>M ((B \<Phi> \<^bold>\<longrightarrow> \<psi>) \<^bold>\<longrightarrow> (B \<Phi>) \<^bold>\<longrightarrow> (B \<psi>))\<close> |
  A2: \<open>\<turnstile>\<^sub>M (\<^bold>\<not> (B \<bottom>\<^sub>L))\<close> |
  \<comment> \<open>Properties of goals\<close>
  A3: \<open>\<turnstile>\<^sub>M (\<^bold>\<not> (G \<bottom>\<^sub>L))\<close> |
  A4: \<open>\<turnstile>\<^sub>M ((B \<Phi>) \<^bold>\<longrightarrow> (\<^bold>\<not> (G \<Phi>)))\<close> |
  A5: \<open>\<turnstile>\<^sub>P (\<Phi> \<^bold>\<longrightarrow> \<psi>) \<Longrightarrow> \<turnstile>\<^sub>M ((\<^bold>\<not> (B \<psi>)) \<^bold>\<longrightarrow> (G \<Phi>) \<^bold>\<longrightarrow> (G \<psi>))\<close>

section\<open>Soundness\<close>

\<comment> \<open>For the soundness theorem we assume the mental state properties for M\<close>
theorem soundness\<^sub>M: 
  assumes \<open>\<nabla> M\<close> 
  shows \<open>\<turnstile>\<^sub>M \<Phi> \<Longrightarrow> M \<Turnstile>\<^sub>M \<Phi>\<close>
proof (induct rule: derive\<^sub>M.induct)
  case (R1 \<phi>)
  with soundness\<^sub>P show ?case by fastforce
next
  case (R2 \<Phi>)
  with soundness\<^sub>P show ?case by fastforce
next
  case (A1 \<Phi> \<psi>)
  then show ?case by auto
next
  case A2
  from not_modal_False(1) show ?case
    using \<open>\<nabla> M\<close> ..
next
  case A3
  from not_modal_False(2) show ?case
    using \<open>\<nabla> M\<close> ..
next
  case (A4 \<Phi>)
  with \<open>\<nabla> M\<close> show ?case unfolding is_mental_state_def by auto
next
  case (A5 \<Phi> \<psi>)
  with soundness\<^sub>P have \<open>{} \<Turnstile>\<^sub>L \<Phi> \<^bold>\<longrightarrow> \<psi>\<close> by fastforce
  show ?case
  proof -
    have \<open>M \<Turnstile>\<^sub>M \<^bold>\<not> (B \<psi>) \<longrightarrow> M \<Turnstile>\<^sub>M (G \<Phi>) \<longrightarrow> M \<Turnstile>\<^sub>M G \<psi>\<close>
    proof (cases M)
      case (Pair \<Sigma> \<Gamma>)
      have \<open>(\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<^bold>\<not> (B \<psi>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M (G \<Phi>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G \<psi>\<close>
      proof
        assume \<open>(\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<^bold>\<not> (B \<psi>)\<close>
        then have \<open>\<Sigma> \<not>\<Turnstile>\<^sub>L \<psi>\<close> by simp
        show \<open>(\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M (G \<Phi>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G \<psi>\<close>
        proof
          assume \<open>(\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G \<Phi>\<close>
          then have \<open>\<Phi>\<in>\<Gamma> \<or> \<Sigma> \<not>\<Turnstile>\<^sub>L \<Phi> \<and> (\<exists>\<gamma>\<in>\<Gamma>. {} \<Turnstile>\<^sub>L \<gamma> \<^bold>\<longrightarrow> \<Phi>)\<close> by simp
          then show \<open>(\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G \<psi>\<close> 
          proof
            assume \<open>\<Phi> \<in> \<Gamma>\<close>
            with \<open>{} \<Turnstile>\<^sub>L \<Phi> \<^bold>\<longrightarrow> \<psi>\<close> have \<open>(\<exists>\<gamma>\<in>\<Gamma>. {} \<Turnstile>\<^sub>L \<gamma> \<^bold>\<longrightarrow> \<psi>)\<close> by auto
            with \<open>\<Sigma> \<not>\<Turnstile>\<^sub>L \<psi>\<close> show ?thesis by simp
          next
            assume \<open>\<Sigma> \<not>\<Turnstile>\<^sub>L \<Phi> \<and> (\<exists>\<gamma>\<in>\<Gamma>. {} \<Turnstile>\<^sub>L \<gamma> \<^bold>\<longrightarrow> \<Phi>)\<close>
            then have \<open>\<Sigma> \<not>\<Turnstile>\<^sub>L \<Phi>\<close> \<open>(\<exists>\<gamma>\<in>\<Gamma>. {} \<Turnstile>\<^sub>L \<gamma> \<^bold>\<longrightarrow> \<Phi>)\<close> by simp+
            from \<open>(\<exists>\<gamma>\<in>\<Gamma>. {} \<Turnstile>\<^sub>L \<gamma> \<^bold>\<longrightarrow> \<Phi>)\<close> have \<open>(\<exists>\<gamma>\<in>\<Gamma>. {} \<Turnstile>\<^sub>L \<gamma> \<^bold>\<longrightarrow> \<psi>)\<close> 
              using \<open>{} \<Turnstile>\<^sub>L \<Phi> \<^bold>\<longrightarrow> \<psi>\<close> by auto
            with \<open>\<Sigma> \<not>\<Turnstile>\<^sub>L \<psi>\<close> show ?thesis by simp
          qed 
        qed
      qed
      with \<open>M = (\<Sigma>, \<Gamma>) \<close> show ?thesis by simp
    qed
    then show ?thesis by simp
  qed
qed

end