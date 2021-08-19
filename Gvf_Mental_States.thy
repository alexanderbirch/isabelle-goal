(*
  Goal verification framework
    - Mental States
*)

\<comment> \<open>This theory introduces mental states and mental state formulas.
  The syntax and semantics of mental state formulas is defined.
  A proof system for mental state formulas is proved sound.\<close>

theory Gvf_Mental_States imports Gvf_Logic begin
                                      
section \<open>Properties of mental states\<close>

\<comment> \<open>We set up a type for mental states.\<close>
type_synonym mental_state = \<open>(\<Phi>\<^sub>L set \<times> \<Phi>\<^sub>L set)\<close>
\<comment> \<open>A mental state is a tuple of sets of propositional logic formulas.\<close>

\<comment> \<open>The definition filters those elements that are 'tuples of sets of propositional logic formulas'.
    Not all elements of this type are in fact mental states: a number of restrictions apply.\<close>
definition is_mental_state :: \<open>mental_state \<Rightarrow> bool\<close> (\<open>\<nabla>\<close>) where
  \<open>\<nabla> M \<equiv> let (\<Sigma>, \<Gamma>) = M in \<comment> \<open>Pattern matching to have variables for belief and goal base.\<close> 
    \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<comment> \<open>\<Sigma> is consistent.\<close>
      \<and> (\<forall>\<gamma>\<in>\<Gamma>. \<comment> \<open>for all goals \<gamma> \<in> \<Gamma>:\<close>
        \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<gamma> \<comment> \<open>(i) \<gamma> is not entailed by the agent's beliefs,\<close> 
        \<and> \<not> \<Turnstile>\<^sub>P (\<^bold>\<not> \<gamma>))\<close> \<comment> \<open>(ii) \<gamma> is consistent.\<close>
\<comment> \<open>Note that the subgoal property for goals is missing. It will be defined in the semantics.\<close>

\<comment> \<open>Every member (of the goal set) must be weaker than \<bottom>, but not weaker than any belief \<sigma>.\<close>
lemma \<open>\<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<forall>\<gamma>\<in>\<Gamma>. \<Turnstile>\<^sub>P (\<^bold>\<bottom> \<^bold>\<longrightarrow> \<gamma>) \<and> \<not> (\<exists>\<sigma>\<in>\<Sigma>. \<Turnstile>\<^sub>P (\<sigma> \<^bold>\<longrightarrow> \<gamma>)))\<close>  
  unfolding is_mental_state_def by fastforce

section \<open>Syntax of mental state formulas\<close>

\<comment> \<open>Atoms are now the special belief and goal modalities.\<close>
datatype Atom\<^sub>M = Bl \<Phi>\<^sub>L | Gl \<Phi>\<^sub>L
\<comment> \<open>We now use a more complex type for atoms compared to simply natural numbers.
    Bl and Gl are the constructors taking a propositional logic formula as input.
    We introduce a nicer syntax below that hides the nesting of constructors.\<close>

\<comment> \<open>We set up a type for mental state formulas.\<close>
type_synonym \<Phi>\<^sub>M = \<open>Atom\<^sub>M \<Phi>\<^sub>P\<close>
\<comment> \<open>We instantiate the general logic parsing the type for atoms.\<close>

abbreviation \<open>B \<Phi> \<equiv> Atom (Bl \<Phi>)\<close>
abbreviation \<open>G \<Phi> \<equiv> Atom (Gl \<Phi>)\<close>

section \<open>Semantics\<close>

\<comment> \<open>Semantics of atoms for mental state formulas is derived given a mental state.\<close>
fun semantics\<^sub>M' :: \<open>mental_state \<Rightarrow> Atom\<^sub>M \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>M*\<close> 50) where
\<comment> \<open>Does the belief base entail \<Phi>?\<close>
  \<open>(\<Sigma>, _) \<Turnstile>\<^sub>M* Bl \<Phi> = (\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<Phi>)\<close> |
\<comment> \<open>Is \<Phi> not entailed by the belief base and a (sub)goal?\<close>
  \<open>(\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M* Gl \<Phi> = (\<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<Phi> \<and> (\<exists>\<gamma>\<in>\<Gamma>. \<Turnstile>\<^sub>P (\<gamma> \<^bold>\<longrightarrow> \<Phi>)))\<close>

\<comment> \<open>Semantics of formulas.\<close>
abbreviation semantics\<^sub>M :: \<open>mental_state \<Rightarrow> \<Phi>\<^sub>M \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>M\<close> 50) where
  \<open>M \<Turnstile>\<^sub>M \<phi> \<equiv> semantics\<^sub>P (semantics\<^sub>M' M) \<phi>\<close>
\<comment> \<open>The semantics for atoms, given a mental state, matches the type for an interpretation.
    The curried function is parsed on to the general semantics as an interpretation which allows
    reuse of the existing definition.\<close>

abbreviation semantics\<^sub>_all\<^sub>M :: \<open>\<Phi>\<^sub>M \<Rightarrow> bool\<close> (\<open>\<^bold>\<Turnstile>\<^sub>M\<close>) where
  \<open>\<^bold>\<Turnstile>\<^sub>M \<phi> \<equiv> (\<forall>M. M \<Turnstile>\<^sub>M \<phi>)\<close>
\<comment> \<open>The semantics for atoms, given a mental state, matches the type for an interpretation.
    The curried function is parsed on to the general semantics as an interpretation which allows
    reuse of the existing definition.\<close>

\<comment> \<open>Examples.\<close>
lemma \<open>({ \<Phi> }, {}) \<Turnstile>\<^sub>M B \<Phi>\<close> by simp

lemma \<open>({ Atom ''0'' }, { Atom ''2'' }) \<Turnstile>\<^sub>M G (Atom ''1'' \<^bold>\<longrightarrow> Atom ''2'')\<close> (is \<open>({ ?R }, { ?Q }) \<Turnstile>\<^sub>M G (?P \<^bold>\<longrightarrow> ?Q)\<close>)
proof -
  have \<open>?R \<noteq> ?Q\<close> by simp
  have \<open>\<not> { ?R } \<^bold>\<Turnstile>\<^sub>P ?P \<^bold>\<longrightarrow> ?Q\<close>
  proof 
    assume \<open>{ ?R } \<^bold>\<Turnstile>\<^sub>P ?P \<^bold>\<longrightarrow> ?Q\<close>
    then have \<open>\<forall>f. semantics\<^sub>P f ?R \<longrightarrow> semantics\<^sub>P f (?P \<^bold>\<longrightarrow> ?Q)\<close> by auto
    moreover have \<open>\<exists>f. \<not> (semantics\<^sub>P f ?R \<longrightarrow> semantics\<^sub>P f (?P \<^bold>\<longrightarrow> ?Q))\<close>
    proof
      let ?f = \<open>(\<lambda>_. True)(''0'' := True, ''1'' := True, ''2'' := False)\<close>
      show \<open>\<not> (semantics\<^sub>P ?f ?R \<longrightarrow> semantics\<^sub>P ?f (?P \<^bold>\<longrightarrow> ?Q))\<close> by simp
    qed
    ultimately show False by auto
  qed
  then show ?thesis by simp
qed

section \<open>Various proofs\<close>

\<comment> \<open>An agent cannot have a goal to achieve a tautology.\<close>
lemma \<open>\<nabla> M \<longrightarrow> \<not> M \<Turnstile>\<^sub>M G \<^bold>\<top>\<close> 
  unfolding is_mental_state_def by auto

\<comment> \<open>An agent does not have inconsistent beliefs/goals.\<close>
lemma not_modal_False: \<open>\<nabla> M \<longrightarrow> M \<Turnstile>\<^sub>M \<^bold>\<not> (B \<^bold>\<bottom>)\<close> \<open>\<nabla> M \<longrightarrow> M \<Turnstile>\<^sub>M \<^bold>\<not> (G \<^bold>\<bottom>)\<close>
  unfolding is_mental_state_def by fastforce+

lemma bel_dist_conj: \<open>M \<Turnstile>\<^sub>M B (\<phi> \<^bold>\<and> \<psi>) \<longleftrightarrow> M \<Turnstile>\<^sub>M B \<phi> \<and> M \<Turnstile>\<^sub>M B \<psi>\<close>
  using semantics\<^sub>M'.elims(2) by fastforce

\<comment> \<open>Properties of the goal modality.\<close>
lemma G_properties:
  shows \<open>\<not> (\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G (\<Phi> \<^bold>\<longrightarrow> \<psi>) \<^bold>\<longrightarrow> G \<Phi> \<^bold>\<longrightarrow> G \<psi>)\<close>
    and \<open>\<not> (\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G (\<Phi> \<^bold>\<and> (\<Phi> \<^bold>\<longrightarrow> \<psi>)) \<^bold>\<longrightarrow> G \<psi>)\<close>
    and \<open>\<not> (\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G \<Phi> \<^bold>\<and> G \<psi> \<^bold>\<longrightarrow> G (\<Phi> \<^bold>\<and> \<psi>))\<close>
    and \<open>\<Turnstile>\<^sub>P (\<Phi> \<^bold>\<longleftrightarrow> \<psi>) \<longrightarrow> \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G \<Phi> \<^bold>\<longleftrightarrow> G \<psi>\<close>
proof -
  let ?\<Phi> = \<open>Atom ''0''\<close> and ?\<psi> = \<open>Atom ''1''\<close>
  show \<open>\<not> (\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G (\<Phi> \<^bold>\<longrightarrow> \<psi>) \<^bold>\<longrightarrow> G \<Phi> \<^bold>\<longrightarrow> G \<psi>)\<close>
  proof 
    assume *: \<open>\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G (\<Phi> \<^bold>\<longrightarrow> \<psi>) \<^bold>\<longrightarrow> G \<Phi> \<^bold>\<longrightarrow> G \<psi>\<close> 
    \<comment> \<open>Counter example.\<close>
    moreover have \<open>\<exists>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<and> \<not> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G (\<Phi> \<^bold>\<longrightarrow> \<psi>) \<^bold>\<longrightarrow> G \<Phi> \<^bold>\<longrightarrow> G \<psi>\<close>
    proof -
      let ?\<Sigma> = \<open>{}\<close> and ?\<Gamma> = \<open>{ ?\<Phi> \<^bold>\<longrightarrow> ?\<psi>, ?\<Phi> }\<close>
      have \<open>?\<Phi> \<noteq> ?\<psi>\<close> by simp
      then have \<open>\<not> (?\<Sigma>, ?\<Gamma>) \<Turnstile>\<^sub>M G (?\<Phi> \<^bold>\<longrightarrow> ?\<psi>) \<^bold>\<longrightarrow> G ?\<Phi> \<^bold>\<longrightarrow> G ?\<psi>\<close> by auto
      moreover have \<open>\<nabla> (?\<Sigma>, ?\<Gamma>)\<close> unfolding is_mental_state_def by auto
      ultimately show ?thesis by blast
    qed
    ultimately show False by blast
  qed
  show \<open>\<not> (\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G (\<Phi> \<^bold>\<and> (\<Phi> \<^bold>\<longrightarrow> \<psi>)) \<^bold>\<longrightarrow> G \<psi>)\<close>
  proof
    assume *: \<open>\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G (\<Phi> \<^bold>\<and> (\<Phi> \<^bold>\<longrightarrow> \<psi>)) \<^bold>\<longrightarrow> G \<psi>\<close>
    \<comment> \<open>Counter example.\<close>
    let ?\<Sigma> = \<open>{ ?\<psi> }\<close> and ?\<Gamma> = \<open>{ ?\<Phi> \<^bold>\<and> (?\<Phi> \<^bold>\<longrightarrow> ?\<psi>) }\<close>
    have \<open>\<not> (?\<Sigma>, ?\<Gamma>) \<Turnstile>\<^sub>M G (?\<Phi> \<^bold>\<and> (?\<Phi> \<^bold>\<longrightarrow> ?\<psi>)) \<^bold>\<longrightarrow> G ?\<psi>\<close> by auto
    moreover have \<open>\<nabla> (?\<Sigma>, ?\<Gamma>)\<close> unfolding is_mental_state_def by auto
    ultimately show False using * by blast
  qed
  show \<open>\<not> (\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G \<Phi> \<^bold>\<and> G \<psi> \<^bold>\<longrightarrow> G (\<Phi> \<^bold>\<and> \<psi>))\<close>
  proof
    assume *: \<open>\<forall>\<Sigma> \<Gamma> \<Phi> \<psi>. \<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M (G \<Phi>) \<^bold>\<and> (G \<psi>) \<^bold>\<longrightarrow> G (\<Phi> \<^bold>\<and> \<psi>)\<close>
    \<comment> \<open>Counter example.\<close>
    let ?\<Sigma> = \<open>{}\<close> and 
        ?\<Gamma> = \<open>{ ?\<Phi>, ?\<psi> }\<close>
    have \<open>\<not> (?\<Sigma>, ?\<Gamma>) \<Turnstile>\<^sub>M (G ?\<Phi>) \<^bold>\<and> (G ?\<psi>) \<^bold>\<longrightarrow> G (?\<Phi> \<^bold>\<and> ?\<psi>)\<close>
      by auto
    moreover have \<open>\<nabla> (?\<Sigma>, ?\<Gamma>)\<close>
      unfolding is_mental_state_def by auto
    ultimately show False 
      using * by blast
  qed
qed simp

section \<open>Provability\<close>

\<comment> \<open>A proof system for mental state formulas.\<close>
inductive derive\<^sub>M :: \<open>\<Phi>\<^sub>M \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>M _\<close> 40) where
  \<comment> \<open>Derive classical tautologies.\<close>
  R1: \<open>\<Turnstile>\<^sub>P \<phi> \<Longrightarrow> \<turnstile>\<^sub>M \<phi>\<close> |
  \<comment> \<open>Properties of beliefs.\<close> 
  R2: \<open>\<Turnstile>\<^sub>P \<Phi> \<Longrightarrow> \<turnstile>\<^sub>M B \<Phi>\<close> |
  A1: \<open>\<turnstile>\<^sub>M B (\<Phi> \<^bold>\<longrightarrow> \<psi>) \<^bold>\<longrightarrow> B \<Phi> \<^bold>\<longrightarrow> B \<psi>\<close> |
  A2: \<open>\<turnstile>\<^sub>M \<^bold>\<not> (B \<^bold>\<bottom>)\<close> |
  \<comment> \<open>Properties of goals.\<close>
  A3: \<open>\<turnstile>\<^sub>M \<^bold>\<not> (G \<^bold>\<bottom>)\<close> |
  A4: \<open>\<turnstile>\<^sub>M B \<Phi> \<^bold>\<longrightarrow> \<^bold>\<not> (G \<Phi>)\<close> |
  A5: \<open>\<Turnstile>\<^sub>P (\<Phi> \<^bold>\<longrightarrow> \<psi>) \<Longrightarrow> \<turnstile>\<^sub>M \<^bold>\<not> (B \<psi>) \<^bold>\<longrightarrow> G \<Phi> \<^bold>\<longrightarrow> G \<psi>\<close>
\<comment> \<open>The original definition uses semantic arguments in e.g. A5. Since we have soundness, but
    not completeness (yet), it may be an idea to switch back. Initially I preferred to keep
    semantics arguments out of the proof system.\<close>

\<comment> \<open>Example.\<close>
lemma \<open>\<turnstile>\<^sub>M B \<Phi> \<^bold>\<or> \<^bold>\<not> (B \<Phi>)\<close> (is \<open>\<turnstile>\<^sub>M ?P \<^bold>\<or> \<^bold>\<not> ?P\<close>) 
proof
  from R_Or have \<open>\<turnstile>\<^sub>P ?P \<^bold>\<or> \<^bold>\<not> ?P\<close> if \<open>{#} \<turnstile>\<^sub>P# {#} + {# ?P, \<^bold>\<not> ?P #}\<close> using that by auto
  with R_Neg have \<open>\<turnstile>\<^sub>P ?P \<^bold>\<or> \<^bold>\<not> ?P\<close> if \<open>{# ?P #} \<turnstile>\<^sub>P# {# ?P #}\<close> using that
    by (metis add_mset_add_single empty_neutral(1) union_commute)
    (* Multiset is giving some problems with single stepping it seems... *)
  with Axiom show \<open>\<Turnstile>\<^sub>P (?P \<^bold>\<or> \<^bold>\<not> ?P)\<close> by auto
qed

section \<open>Soundness\<close>

\<comment> \<open>For the soundness theorem we assume the mental state properties for M.\<close>
theorem soundness\<^sub>M: 
  assumes \<open>\<nabla> M\<close> 
  shows \<open>\<turnstile>\<^sub>M \<Phi> \<Longrightarrow> M \<Turnstile>\<^sub>M \<Phi>\<close>
proof (induct rule: derive\<^sub>M.induct)
  case R1
  then show ?case by fastforce
next
  case R2
  then show ?case by (cases M) fastforce
next
  case A1
  then show ?case by (cases M) auto
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
  show ?case
  proof -
    have \<open>M \<Turnstile>\<^sub>M \<^bold>\<not> (B \<psi>) \<longrightarrow> M \<Turnstile>\<^sub>M G \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M G \<psi>\<close>
    proof (cases M)
      case (Pair \<Sigma> \<Gamma>)
      have \<open>(\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<^bold>\<not> (B \<psi>) \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G \<Phi> \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G \<psi>\<close>
      proof
        assume \<open>(\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<^bold>\<not> (B \<psi>)\<close>
        then have \<open>\<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>\<close> by simp
        show \<open>(\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G \<Phi> \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G \<psi>\<close>
        proof
          assume \<open>(\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G \<Phi>\<close>
          then have \<open>\<Phi>\<in>\<Gamma> \<or> \<not>\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<Phi> \<and> (\<exists>\<gamma>\<in>\<Gamma>. \<Turnstile>\<^sub>P (\<gamma> \<^bold>\<longrightarrow> \<Phi>))\<close> by simp
          then show \<open>(\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G \<psi>\<close> 
          proof
            assume \<open>\<Phi> \<in> \<Gamma>\<close>
            with \<open>\<Turnstile>\<^sub>P (\<Phi> \<^bold>\<longrightarrow> \<psi>)\<close> have \<open>\<exists>\<gamma>\<in>\<Gamma>. \<Turnstile>\<^sub>P (\<gamma> \<^bold>\<longrightarrow> \<psi>)\<close> by auto
            with \<open>\<not>\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>\<close> show ?thesis by simp
          next
            assume \<open>\<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<Phi> \<and> (\<exists>\<gamma>\<in>\<Gamma>. \<Turnstile>\<^sub>P (\<gamma> \<^bold>\<longrightarrow> \<Phi>))\<close>
            then have \<open>\<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<Phi>\<close> \<open>\<exists>\<gamma>\<in>\<Gamma>. \<Turnstile>\<^sub>P (\<gamma> \<^bold>\<longrightarrow> \<Phi>)\<close> by simp+
            from \<open>\<exists>\<gamma>\<in>\<Gamma>. \<Turnstile>\<^sub>P (\<gamma> \<^bold>\<longrightarrow> \<Phi>)\<close> have \<open>\<exists>\<gamma>\<in>\<Gamma>. \<Turnstile>\<^sub>P (\<gamma> \<^bold>\<longrightarrow> \<psi>)\<close> 
              using \<open>\<Turnstile>\<^sub>P (\<Phi> \<^bold>\<longrightarrow> \<psi>)\<close> by auto
            with \<open>\<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>\<close> show ?thesis by simp
          qed 
        qed
      qed
      with \<open>M = (\<Sigma>, \<Gamma>) \<close> show ?thesis by simp
    qed
    then show ?thesis by simp
  qed
qed

end