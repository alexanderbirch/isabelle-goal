theory Gvf_Example_BW4T imports Gvf_Temporal_Logic Gvf_Solver begin

section \<open>Example BW4T single agent specification.\<close>

subsection \<open>Agent specification setup\<close>

\<comment> \<open>Propositions.\<close>
abbreviation \<open>in_dropzone \<equiv> \<Phi>\<^sub>P.Atom ''in_dropzone''\<close>
abbreviation \<open>in_r\<^sub>1 \<equiv> \<Phi>\<^sub>P.Atom ''in_r1''\<close>
abbreviation \<open>holding_b\<^sub>1 \<equiv> \<Phi>\<^sub>P.Atom ''holding''\<close>
abbreviation \<open>atBlock_b\<^sub>1 \<equiv> \<Phi>\<^sub>P.Atom ''atBlock''\<close>
abbreviation \<open>collect_red \<equiv> \<Phi>\<^sub>P.Atom ''collect''\<close>

\<comment> \<open>Actions.\<close>
abbreviation \<open>goTo_dropzone::cap \<equiv> basic ''0''\<close>
abbreviation \<open>goTo_r\<^sub>1::cap \<equiv> basic ''1''\<close>
abbreviation \<open>goToBlock_b\<^sub>1::cap \<equiv> basic ''2''\<close>
abbreviation \<open>pickUp_b\<^sub>1::cap \<equiv> basic ''3''\<close>
abbreviation \<open>putDown::cap \<equiv> basic ''4''\<close>

abbreviation \<open>goTo_dropzone_c \<equiv> (B in_r\<^sub>1 \<^bold>\<and> B holding_b\<^sub>1) \<triangleright> do goTo_dropzone\<close>
abbreviation \<open>goTo_r\<^sub>1_c \<equiv> (B in_dropzone \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1)) \<triangleright> do goTo_r\<^sub>1\<close>
abbreviation \<open>goToBlock_b\<^sub>1_c \<equiv> (B in_r\<^sub>1 \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>\<and> \<^bold>\<not> (B atBlock_b\<^sub>1)) \<triangleright> do goToBlock_b\<^sub>1\<close>
abbreviation \<open>pickUp_b\<^sub>1_c \<equiv> (B atBlock_b\<^sub>1 \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1)) \<triangleright> do pickUp_b\<^sub>1\<close>
abbreviation \<open>putDown_c \<equiv> (B holding_b\<^sub>1 \<^bold>\<and> B in_dropzone) \<triangleright> do putDown\<close>

\<comment> \<open>Specification of the program.\<close>
abbreviation \<open>\<Pi>\<^sub>x \<equiv> [ goTo_dropzone_c, goTo_r\<^sub>1_c, goToBlock_b\<^sub>1_c, pickUp_b\<^sub>1_c, putDown_c]\<close>

abbreviation \<open>invariants \<equiv> [in_dropzone \<^bold>\<longrightarrow> \<^bold>\<not> in_r\<^sub>1, in_r\<^sub>1 \<^bold>\<longrightarrow> \<^bold>\<not> in_dropzone, in_dropzone \<^bold>\<longrightarrow> \<^bold>\<not> atBlock_b\<^sub>1]\<close>

abbreviation
  \<open>M\<^sub>0\<^sub>x::mental_state \<equiv> ( [ in_dropzone, \<^bold>\<not> in_r\<^sub>1, \<^bold>\<not> holding_b\<^sub>1, \<^bold>\<not> atBlock_b\<^sub>1 ] @ invariants, [ collect_red ] )\<close>

abbreviation \<open>S\<^sub>x' \<equiv>
  [
    (bcap goTo_dropzone, fst goTo_dropzone_c, 
      [
        \<^bold>{ B in_r\<^sub>1 \<^bold>\<and> B holding_b\<^sub>1 \<^bold>} goTo_dropzone \<^bold>{ B in_dropzone \<^bold>}
      ]),

    (bcap goTo_r\<^sub>1, fst goTo_r\<^sub>1_c, 
      [
        \<^bold>{ B in_dropzone \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>} goTo_r\<^sub>1 \<^bold>{ B in_r\<^sub>1 \<^bold>}
      ]),

    (bcap goToBlock_b\<^sub>1, fst goToBlock_b\<^sub>1_c, 
      [
        \<^bold>{ B in_r\<^sub>1 \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>\<and> \<^bold>\<not> (B atBlock_b\<^sub>1) \<^bold>} goToBlock_b\<^sub>1 \<^bold>{ B atBlock_b\<^sub>1 \<^bold>}
      ]),

    (bcap pickUp_b\<^sub>1, fst pickUp_b\<^sub>1_c, 
      [
        \<^bold>{ B atBlock_b\<^sub>1 \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>} pickUp_b\<^sub>1 \<^bold>{ B holding_b\<^sub>1 \<^bold>}
      ]),

    (bcap putDown, fst putDown_c, 
      [
        \<^bold>{ B in_dropzone \<^bold>\<and> B holding_b\<^sub>1 \<^bold>} putDown \<^bold>{ B collect_red \<^bold>}
      ])
  ]\<close>

 \<comment> \<open>Invariants\<close>
abbreviation \<open>L\<^sub>x \<equiv>
  [
    ((\<lambda>_. True), map B invariants),
    ((\<lambda>b. b \<notin> {bcap pickUp_b\<^sub>1, bcap putDown}), [ B holding_b\<^sub>1, \<^bold>\<not> (B holding_b\<^sub>1) ]),
    ((\<lambda>b. b \<noteq> bcap putDown), [ \<^bold>\<not> (B collect_red)])
  ]\<close>

abbreviation
  \<open>S\<^sub>x \<equiv> from_frax (S\<^sub>x', L\<^sub>x)\<close>

\<comment> \<open>Prove that the example is an instance of the single agent program locale.\<close>
\<comment> \<open>We use a trick where \<T> is simply some function that complies to our definition due to Hilbert's epsilon operator i.e. the axiom of choice.\<close>
definition \<open>\<T>\<^sub>x \<equiv> SOME \<T>. complies S\<^sub>x \<T>\<close>

interpretation bw4t: single_agent_program \<T>\<^sub>x \<open>set \<Pi>\<^sub>x\<close> M\<^sub>0\<^sub>x S\<^sub>x
proof -
  have \<open>\<nabla> M\<^sub>0\<^sub>x\<close>
  proof -
    let ?f = \<open>(\<lambda>_. False)(the_atom in_dropzone := True)\<close>
    have \<open>\<forall>p \<in> set (fst M\<^sub>0\<^sub>x). semantics\<^sub>P ?f p\<close> by simp
    then have \<open>\<exists>f. \<forall>p \<in> set (fst M\<^sub>0\<^sub>x). semantics\<^sub>P f p\<close> by blast
    with not_contradict have \<open>\<not> fst M\<^sub>0\<^sub>x \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> by auto
    moreover have \<open>\<not> semantics\<^sub>P ?f collect_red\<close> by simp
    with \<open>\<forall>p \<in> set (fst M\<^sub>0\<^sub>x). semantics\<^sub>P ?f p\<close> have \<open>\<not> fst M\<^sub>0\<^sub>x \<^bold>\<Turnstile>\<^sub>P collect_red\<close> by blast
    moreover have \<open>\<not> \<Turnstile>\<^sub>P (\<^bold>\<not> collect_red)\<close> by fastforce
    ultimately show ?thesis using is_mental_state_def by auto
  qed
  moreover have \<open>satisfiable S\<^sub>x\<close> unfolding satisfiable_def
  proof
    fix M
    let ?sat = \<open>\<lambda>\<Sigma> s. (M \<Turnstile>\<^sub>M fst (snd s) \<longrightarrow> satisfiable_base M (snd (snd s)) \<Sigma>)\<close>
    have \<open>\<nabla> M \<longrightarrow> (\<forall>s\<in>set S\<^sub>x. \<exists>M. ?sat M s)\<close>
    proof 
      assume \<open>\<nabla> M\<close>
      let ?inh = \<open>\<lambda>M p. if M \<Turnstile>\<^sub>M B p then p else \<^bold>\<not> p\<close>
      let ?\<Sigma>\<^sub>0 = \<open>[\<^bold>\<not> in_r\<^sub>1, in_dropzone, \<^bold>\<not> atBlock_b\<^sub>1, ?inh M holding_b\<^sub>1, \<^bold>\<not> collect_red]\<close>
      let ?\<Sigma>\<^sub>1 = \<open>[in_r\<^sub>1, \<^bold>\<not> in_dropzone, ?inh M holding_b\<^sub>1]\<close>
      let ?\<Sigma>\<^sub>2 = \<open>[atBlock_b\<^sub>1, in_r\<^sub>1, \<^bold>\<not> in_dropzone, ?inh M holding_b\<^sub>1]\<close>
      let ?\<Sigma>\<^sub>3 = \<open>[holding_b\<^sub>1, in_r\<^sub>1, \<^bold>\<not> in_dropzone]\<close>
      let ?\<Sigma>\<^sub>4 = \<open>[collect_red, \<^bold>\<not> in_r\<^sub>1, in_dropzone]\<close>
      \<comment> \<open>Invariants for action\<close>
      let ?ht_L\<^sub>1 = \<open>\<lambda>a. \<^bold>{ B (in_dropzone \<^bold>\<longrightarrow> \<^bold>\<not> in_r\<^sub>1) \<^bold>} a \<^bold>{ B (in_dropzone \<^bold>\<longrightarrow> \<^bold>\<not> in_r\<^sub>1) \<^bold>}\<close>
      let ?ht_L\<^sub>2 = \<open>\<lambda>a. \<^bold>{ B (in_r\<^sub>1 \<^bold>\<longrightarrow> \<^bold>\<not> in_dropzone) \<^bold>} a \<^bold>{ B (in_r\<^sub>1 \<^bold>\<longrightarrow> \<^bold>\<not> in_dropzone) \<^bold>}\<close>
      let ?ht_L\<^sub>3 = \<open>\<lambda>a. \<^bold>{ B (in_dropzone \<^bold>\<longrightarrow> \<^bold>\<not> atBlock_b\<^sub>1) \<^bold>} a \<^bold>{ B (in_dropzone \<^bold>\<longrightarrow> \<^bold>\<not> atBlock_b\<^sub>1) \<^bold>}\<close>
      let ?ht_L\<^sub>4 = \<open>\<lambda>a. \<^bold>{ B holding_b\<^sub>1 \<^bold>} a \<^bold>{ B holding_b\<^sub>1 \<^bold>}\<close>
      let ?ht_L\<^sub>5 = \<open>\<lambda>a. \<^bold>{ \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>} a \<^bold>{ \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>}\<close>
      let ?ht_L\<^sub>6 = \<open>\<lambda>a. \<^bold>{ \<^bold>\<not> (B collect_red) \<^bold>} a \<^bold>{ \<^bold>\<not> (B collect_red) \<^bold>}\<close>
      \<comment> \<open>goTo_dropzone\<close>
      have \<open>?sat ?\<Sigma>\<^sub>0 (S\<^sub>x!0)\<close>
      proof
        assume \<open>M \<Turnstile>\<^sub>M fst (snd (S\<^sub>x ! 0))\<close>
        show \<open>satisfiable_base M (snd (snd (S\<^sub>x ! 0))) ?\<Sigma>\<^sub>0\<close> unfolding satisfiable_base_def
        proof
          show \<open>\<not> fst M \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> \<not> ?\<Sigma>\<^sub>0 \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close>
          proof
            let ?f = \<open>(\<lambda>_. True)(the_atom in_r\<^sub>1 := False, the_atom holding_b\<^sub>1 := M \<Turnstile>\<^sub>M B holding_b\<^sub>1)\<close>
            have \<open>\<forall>p \<in> set ?\<Sigma>\<^sub>0. semantics\<^sub>P ?f p\<close> by simp
            then have \<open>\<exists>f. \<forall>p \<in> set ?\<Sigma>\<^sub>0. semantics\<^sub>P f p\<close> by blast
            with not_contradict show \<open>\<not> ?\<Sigma>\<^sub>0 \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> by auto
          qed
          show \<open>\<forall>ht\<in>set (snd (snd (S\<^sub>x ! 0))). M \<Turnstile>\<^sub>M pre ht \<longrightarrow> (?\<Sigma>\<^sub>0, [\<psi><-snd M. \<not> ?\<Sigma>\<^sub>0 \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ht\<close>
          proof -
            let ?ht\<^sub>1 = \<open>\<^bold>{ B in_r\<^sub>1 \<^bold>\<and> B holding_b\<^sub>1 \<^bold>} goTo_dropzone \<^bold>{ B in_dropzone \<^bold>}\<close>
            have \<open>M \<Turnstile>\<^sub>M pre ?ht\<^sub>1 \<longrightarrow> (?\<Sigma>\<^sub>0, [\<psi><-snd M. \<not> ?\<Sigma>\<^sub>0 \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht\<^sub>1\<close> by simp
            moreover have \<open>M \<Turnstile>\<^sub>M pre (?ht_L\<^sub>1 goTo_dropzone) \<longrightarrow> (?\<Sigma>\<^sub>0, [\<psi><-snd M. \<not> ?\<Sigma>\<^sub>0 \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post (?ht_L\<^sub>1 goTo_dropzone)\<close> by simp
            moreover have \<open>M \<Turnstile>\<^sub>M pre (?ht_L\<^sub>2 goTo_dropzone) \<longrightarrow> (?\<Sigma>\<^sub>0, [\<psi><-snd M. \<not> ?\<Sigma>\<^sub>0 \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post (?ht_L\<^sub>2 goTo_dropzone)\<close> by simp
            moreover have \<open>M \<Turnstile>\<^sub>M pre (?ht_L\<^sub>3 goTo_dropzone) \<longrightarrow> (?\<Sigma>\<^sub>0, [\<psi><-snd M. \<not> ?\<Sigma>\<^sub>0 \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post (?ht_L\<^sub>3 goTo_dropzone)\<close> by simp
            moreover have \<open>M \<Turnstile>\<^sub>M pre (?ht_L\<^sub>4 goTo_dropzone) \<longrightarrow> (?\<Sigma>\<^sub>0, [\<psi><-snd M. \<not> ?\<Sigma>\<^sub>0 \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post (?ht_L\<^sub>4 goTo_dropzone)\<close> by simp
            moreover have \<open>M \<Turnstile>\<^sub>M pre (?ht_L\<^sub>5 goTo_dropzone) \<longrightarrow> (?\<Sigma>\<^sub>0, [\<psi><-snd M. \<not> ?\<Sigma>\<^sub>0 \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post (?ht_L\<^sub>5 goTo_dropzone)\<close> by auto
            moreover from is_mst_negB have \<open>M \<Turnstile>\<^sub>M pre (?ht_L\<^sub>6 goTo_dropzone) \<longrightarrow> (?\<Sigma>\<^sub>0, [\<psi><-snd M. \<not> ?\<Sigma>\<^sub>0 \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post (?ht_L\<^sub>6 goTo_dropzone)\<close> using \<open>\<nabla>M\<close> apply simp
            ultimately show ?thesis by auto
          qed
        qed
      qed
      then have \<open>\<exists>M. ?sat M (S\<^sub>x!0)\<close> by auto
      \<comment> \<open>goTo_r\<^sub>1\<close>
      moreover have \<open>?sat ?\<Sigma>\<^sub>1 (S\<^sub>x!1)\<close>
      proof
        assume \<open>M \<Turnstile>\<^sub>M fst (snd (S\<^sub>x ! 1))\<close>
        show \<open>satisfiable_base M (snd (snd (S\<^sub>x ! 1))) ?\<Sigma>\<^sub>1\<close> unfolding satisfiable_base_def
        proof
          show \<open>\<not> fst M \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> \<not> ?\<Sigma>\<^sub>1 \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close>
          proof
            let ?f = \<open>(\<lambda>_. True)(the_atom in_dropzone := False, the_atom holding_b\<^sub>1 := M \<Turnstile>\<^sub>M B holding_b\<^sub>1)\<close>
            have \<open>\<forall>p \<in> set ?\<Sigma>\<^sub>1. semantics\<^sub>P ?f p\<close> by simp
            then have \<open>\<exists>f. \<forall>p \<in> set ?\<Sigma>\<^sub>1. semantics\<^sub>P f p\<close> by blast
            with not_contradict show \<open>\<not> ?\<Sigma>\<^sub>1 \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> by auto
          qed
          show \<open>\<forall>ht\<in>set (snd (snd (S\<^sub>x ! 1))). M \<Turnstile>\<^sub>M pre ht \<longrightarrow> (?\<Sigma>\<^sub>1, [\<psi><-snd M. \<not> ?\<Sigma>\<^sub>1 \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ht\<close> sorry
        qed
      qed
      then have \<open>\<exists>M. ?sat M (S\<^sub>x!1)\<close> by auto
      \<comment> \<open>goToBlock_b\<^sub>1\<close>
      moreover have \<open>?sat ?\<Sigma>\<^sub>2 (S\<^sub>x!2)\<close> 
      proof
        assume \<open>M \<Turnstile>\<^sub>M fst (snd (S\<^sub>x ! 2))\<close>
        let ?f = \<open>(\<lambda>_. True)(the_atom in_dropzone := False, the_atom holding_b\<^sub>1 := M \<Turnstile>\<^sub>M B holding_b\<^sub>1)\<close>
        show \<open>satisfiable_base M (snd (snd (S\<^sub>x ! 2))) ?\<Sigma>\<^sub>2\<close> unfolding satisfiable_base_def
        proof
          show \<open>\<not> fst M \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> \<not> ?\<Sigma>\<^sub>2 \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close>
          proof
            have \<open>\<forall>p \<in> set ?\<Sigma>\<^sub>2. semantics\<^sub>P ?f p\<close> by simp
            then have \<open>\<exists>f. \<forall>p \<in> set ?\<Sigma>\<^sub>2. semantics\<^sub>P f p\<close> by blast
            with not_contradict show \<open>\<not> ?\<Sigma>\<^sub>2 \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> by auto
          qed
          show \<open>\<forall>ht\<in>set (snd (snd (S\<^sub>x ! 2))). M \<Turnstile>\<^sub>M pre ht \<longrightarrow> (?\<Sigma>\<^sub>2, [\<psi><-snd M. \<not> ?\<Sigma>\<^sub>2 \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ht\<close>
          proof -
            have \<open>M \<Turnstile>\<^sub>M \<^bold>\<not> (B holding_b\<^sub>1) \<longrightarrow> (?\<Sigma>\<^sub>2, [\<psi><-snd M. \<not> ?\<Sigma>\<^sub>2 \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M \<^bold>\<not> (B holding_b\<^sub>1)\<close>
            proof
              assume \<open>M \<Turnstile>\<^sub>M \<^bold>\<not> (B holding_b\<^sub>1)\<close>
              then have \<open>(?\<Sigma>\<^sub>2, [\<psi><-snd M. \<not> ?\<Sigma>\<^sub>2 \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M B (\<^bold>\<not> holding_b\<^sub>1)\<close> by simp
              moreover 
              { 
                have \<open>\<forall>p\<in>set ?\<Sigma>\<^sub>2. semantics\<^sub>P ?f p\<close> by simp
                then have \<open>\<exists>f. \<forall>p\<in>set ?\<Sigma>\<^sub>2. semantics\<^sub>P f p\<close> by blast
                with not_contradict have \<open>\<not> ?\<Sigma>\<^sub>2 \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> by auto
                moreover have \<open>\<nabla>(fst M, snd M)\<close> using \<open>\<nabla>M\<close> by simp
                ultimately have \<open>\<nabla>(?\<Sigma>\<^sub>2, [\<psi><-snd M. \<not> ?\<Sigma>\<^sub>2 \<^bold>\<Turnstile>\<^sub>P \<psi>])\<close> 
                  using new_base_is_mst by blast
              }
              ultimately show \<open>(?\<Sigma>\<^sub>2, [\<psi><-snd M. \<not> ?\<Sigma>\<^sub>2 \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M \<^bold>\<not> (B holding_b\<^sub>1)\<close> 
                using is_mst_negB by blast
            qed
            then show ?thesis sorry
          qed
        qed
      qed
      then have \<open>\<exists>M. ?sat M (S\<^sub>x!2)\<close> by auto
      \<comment> \<open>pickUp_b\<^sub>1\<close>
      moreover have \<open>?sat ?\<Sigma>\<^sub>3 (S\<^sub>x!3)\<close> 
      proof
        assume \<open>M \<Turnstile>\<^sub>M fst (snd (S\<^sub>x ! 3))\<close>
        show \<open>satisfiable_base M (snd (snd (S\<^sub>x ! 3))) ?\<Sigma>\<^sub>3\<close> unfolding satisfiable_base_def
        proof
          show \<open>\<not> fst M \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> \<not> ?\<Sigma>\<^sub>3 \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close>
          proof
            let ?f = \<open>(\<lambda>_. True)(the_atom in_dropzone := False)\<close>
            have \<open>\<forall>p \<in> set ?\<Sigma>\<^sub>3. semantics\<^sub>P ?f p\<close> by simp
            then have \<open>\<exists>f. \<forall>p \<in> set ?\<Sigma>\<^sub>3. semantics\<^sub>P f p\<close> by blast
            with not_contradict show \<open>\<not> ?\<Sigma>\<^sub>3 \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> by auto
          qed
          show \<open>\<forall>ht\<in>set (snd (snd (S\<^sub>x ! 3))). M \<Turnstile>\<^sub>M pre ht \<longrightarrow> (?\<Sigma>\<^sub>3, [\<psi><-snd M. \<not> ?\<Sigma>\<^sub>3 \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ht\<close> sorry
        qed
      qed
      then have \<open>\<exists>M. ?sat M (S\<^sub>x!3)\<close> by auto
      \<comment> \<open>putDown\<close>
      moreover have \<open>?sat ?\<Sigma>\<^sub>4 (S\<^sub>x!4)\<close> 
      proof
        assume \<open>M \<Turnstile>\<^sub>M fst (snd (S\<^sub>x ! 4))\<close>
        show \<open>satisfiable_base M (snd (snd (S\<^sub>x ! 4))) ?\<Sigma>\<^sub>4\<close> unfolding satisfiable_base_def
        proof
          show \<open>\<not> fst M \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> \<not> ?\<Sigma>\<^sub>4 \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close>
          proof
            let ?f = \<open>(\<lambda>_. True)(the_atom in_r\<^sub>1 := False)\<close>
            have \<open>\<forall>p \<in> set ?\<Sigma>\<^sub>4. semantics\<^sub>P ?f p\<close> by simp
            then have \<open>\<exists>f. \<forall>p \<in> set ?\<Sigma>\<^sub>4. semantics\<^sub>P f p\<close> by blast
            with not_contradict show \<open>\<not> ?\<Sigma>\<^sub>4 \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> by auto
          qed
          show \<open>\<forall>ht\<in>set (snd (snd (S\<^sub>x ! 4))). M \<Turnstile>\<^sub>M pre ht \<longrightarrow> (?\<Sigma>\<^sub>4, [\<psi><-snd M. \<not> ?\<Sigma>\<^sub>4 \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ht\<close> sorry
        qed
      qed
      then have \<open>\<exists>M. ?sat M (S\<^sub>x!4)\<close> by auto
      \<comment> \<open>Combine\<close>
      ultimately show \<open>\<forall>s\<in>set S\<^sub>x. \<exists>M. ?sat M s\<close> by simp
    qed
    then have \<open>\<nabla>M \<longrightarrow> (\<forall>s\<in>set S\<^sub>x. satisfiable_l M s)\<close> by simp
    moreover have \<open>\<nabla>M \<longrightarrow> (\<forall>s\<in>set S\<^sub>x. satisfiable_r M s)\<close>
    proof 
      assume \<open>\<nabla>M\<close>
      show \<open>\<forall>s\<in>set S\<^sub>x. satisfiable_r M s\<close>
      proof
        fix s
        assume \<open>s \<in> set S\<^sub>x\<close>
        then have \<open>s = S\<^sub>x!0 \<or> s = S\<^sub>x!1 \<or> s = S\<^sub>x!2 \<or> s = S\<^sub>x!3 \<or> s = S\<^sub>x!4\<close> by simp
        moreover have \<open>satisfiable_r M (S\<^sub>x!0)\<close> by auto
        moreover have \<open>satisfiable_r M (S\<^sub>x!1)\<close> by auto
        moreover have \<open>satisfiable_r M (S\<^sub>x!2)\<close> by auto
        moreover have \<open>satisfiable_r M (S\<^sub>x!3)\<close> by auto
        moreover have \<open>satisfiable_r M (S\<^sub>x!4)\<close> by auto
        ultimately show \<open>satisfiable_r M s\<close> by blast
      qed
    qed
    ultimately show \<open>\<nabla>M \<longrightarrow> (\<forall>s\<in>set S\<^sub>x. satisfiable_l M s \<and> satisfiable_r M s)\<close> using satisfiable_r_frax by blast
  qed
  then have \<open>is_ht_specification S\<^sub>x\<close> unfolding is_ht_specification_def by simp
  moreover have \<open>\<forall>a. (\<exists>\<phi>. (\<phi>, basic a) \<in> set \<Pi>\<^sub>x) = (a \<in> set (map fst S\<^sub>x))\<close> by fastforce
  ultimately show \<open>single_agent_program \<T>\<^sub>x (set \<Pi>\<^sub>x) M\<^sub>0\<^sub>x S\<^sub>x\<close> using is_ht_spec_single_agent_program unfolding \<T>\<^sub>x_def by simp
qed

\<comment> \<open>Abbreviations useful for working with the interpretation seamlessly in the global scope\<close>
abbreviation semantics\<^sub>H (\<open>\<Turnstile>\<^sub>H\<close>) where \<open>\<Turnstile>\<^sub>H \<equiv> bw4t.semantics\<^sub>H\<close>
abbreviation derive\<^sub>H (\<open>\<turnstile>\<^sub>H\<close>) where \<open>\<turnstile>\<^sub>H \<equiv> bw4t.derive\<^sub>H\<close>
abbreviation semantics\<^sub>E (infix \<open>\<Turnstile>\<^sub>E\<close> 50) where \<open>M \<Turnstile>\<^sub>E \<phi> \<equiv> bw4t.semantics\<^sub>E M \<phi>\<close>
abbreviation semantics\<^sub>_all\<^sub>E (\<open>\<^bold>\<Turnstile>\<^sub>E\<close>) where \<open>\<^bold>\<Turnstile>\<^sub>E \<equiv> bw4t.semantics\<^sub>_all\<^sub>E\<close>
abbreviation semantics\<^sub>_all\<^sub>M (\<open>\<^bold>\<Turnstile>\<^sub>M\<close>) where \<open>\<^bold>\<Turnstile>\<^sub>M \<equiv> bw4t.semantics\<^sub>_all\<^sub>M\<close>
abbreviation leads_to (infix \<open>\<mapsto>\<close> 55) where \<open>x \<mapsto> y \<equiv> bw4t.leads_to x y\<close>

subsection \<open>Correctness proof\<close>
abbreviation \<open>M\<^sub>0 \<equiv> B in_dropzone \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>\<and> G collect_red\<close>
abbreviation \<open>M\<^sub>1 \<equiv> B in_r\<^sub>1 \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>\<and> G collect_red\<close>
abbreviation \<open>M\<^sub>2 \<equiv> B in_r\<^sub>1 \<^bold>\<and> B atBlock_b\<^sub>1 \<^bold>\<and> G collect_red\<close>
abbreviation \<open>M\<^sub>3 \<equiv> B in_r\<^sub>1 \<^bold>\<and> B holding_b\<^sub>1 \<^bold>\<and> G collect_red\<close>
abbreviation \<open>M\<^sub>4 \<equiv> B in_dropzone \<^bold>\<and> B holding_b\<^sub>1 \<^bold>\<and> G collect_red\<close>
abbreviation \<open>M\<^sub>5 \<equiv> B collect_red\<close>

lemma invariants_ht: \<open>\<phi> \<in> set invariants \<Longrightarrow> (n, \<Phi>, hts) \<in> set S\<^sub>x \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ B \<phi> \<^bold>} basic n \<^bold>{ B \<phi> \<^bold>}\<close>
  by (rule bw4t.import) auto

(* Kan vi få fat i invariants fra M0? *)

lemma bw4t_lt: \<open>M\<^sub>0\<^sup>T \<mapsto> M\<^sub>5\<^sup>T\<close>
proof -
  have \<open>M\<^sub>0\<^sup>T \<mapsto> M\<^sub>1\<^sup>T\<close>
  proof (rule bw4t.ensures)
    show \<open>\<forall>s \<in> bw4t.Agent. \<forall>i. s, i \<Turnstile>\<^sub>T (M\<^sub>0\<^sup>T ensures M\<^sub>1\<^sup>T)\<close>
    proof
      fix s
      assume \<open>s \<in> bw4t.Agent\<close>
      show \<open>\<forall>i. s, i \<Turnstile>\<^sub>T (M\<^sub>0\<^sup>T ensures M\<^sub>1\<^sup>T)\<close>
      proof
        fix i
        show \<open>s, i \<Turnstile>\<^sub>T (M\<^sub>0\<^sup>T ensures M\<^sub>1\<^sup>T)\<close>
        proof-
        have eff: \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>\<and> fst goTo_r\<^sub>1_c \<^bold>} snd goTo_r\<^sub>1_c \<^bold>{ M\<^sub>1 \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<^bold>\<Turnstile>\<^sub>M (M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>\<and> fst goTo_r\<^sub>1_c \<^bold>\<longrightarrow> M\<^sub>0)\<close> by simp
          show \<open>\<^bold>\<Turnstile>\<^sub>M (M\<^sub>1 \<^bold>\<longrightarrow> M\<^sub>1)\<close> by simp
          show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>} snd goTo_r\<^sub>1_c \<^bold>{ M\<^sub>1 \<^bold>}\<close>
          proof
            show \<open>\<turnstile>\<^sub>H \<^bold>{ B in_dropzone \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>} snd goTo_r\<^sub>1_c \<^bold>{ B in_r\<^sub>1 \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>}\<close>
            proof (rule bw4t.rImp)
              have \<open>\<turnstile>\<^sub>H \<^bold>{ B in_dropzone \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>} snd goTo_r\<^sub>1_c \<^bold>{ B in_r\<^sub>1 \<^bold>}\<close> 
                using bw4t.import by simp
              moreover have \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>} snd goTo_r\<^sub>1_c \<^bold>{ \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>}\<close> 
                using bw4t.import by simp
              ultimately show \<open>\<turnstile>\<^sub>H \<^bold>{ B in_dropzone \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>} snd goTo_r\<^sub>1_c \<^bold>{ B in_r\<^sub>1 \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>}\<close>
                using bw4t.rCon by simp
            next
              show \<open>\<^bold>\<Turnstile>\<^sub>M (B in_dropzone \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>\<longrightarrow> B in_dropzone \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1))\<close> by simp
              show \<open>\<^bold>\<Turnstile>\<^sub>M (B in_r\<^sub>1 \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>\<longrightarrow> B in_r\<^sub>1 \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1))\<close> by simp
            qed
            have \<open>\<turnstile>\<^sub>H \<^bold>{ G collect_red \<^bold>} snd goTo_r\<^sub>1_c \<^bold>{ B collect_red \<^bold>\<or> G collect_red \<^bold>}\<close> 
              using bw4t.persist by simp
            moreover have \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not> (B collect_red) \<^bold>} snd goTo_r\<^sub>1_c \<^bold>{ \<^bold>\<not> (B collect_red) \<^bold>}\<close> 
              using bw4t.import by simp
            ultimately have \<open>\<turnstile>\<^sub>H \<^bold>{ G collect_red \<^bold>\<and> \<^bold>\<not> (B collect_red) \<^bold>} snd goTo_r\<^sub>1_c \<^bold>{ (B collect_red \<^bold>\<or> G collect_red) \<^bold>\<and> \<^bold>\<not> (B collect_red) \<^bold>}\<close> 
              using bw4t.rCon by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (G collect_red \<^bold>\<longrightarrow> G collect_red \<^bold>\<and> \<^bold>\<not> (B collect_red))\<close> by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M ((B collect_red \<^bold>\<or> G collect_red) \<^bold>\<and> \<^bold>\<not> (B collect_red) \<^bold>\<longrightarrow> G collect_red)\<close> by auto
            ultimately show \<open>\<turnstile>\<^sub>H \<^bold>{ G collect_red \<^bold>} snd goTo_r\<^sub>1_c \<^bold>{ G collect_red \<^bold>}\<close>
              using bw4t.rImp by blast
          qed
        qed
        have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst goTo_r\<^sub>1_c) \<triangleright> do (snd goTo_r\<^sub>1_c)) \<^bold>{ M\<^sub>1 \<^bold>}\<close>
        proof
          from eff show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>\<and> fst goTo_r\<^sub>1_c \<^bold>} snd goTo_r\<^sub>1_c \<^bold>{ M\<^sub>1 \<^bold>}\<close> .
          show \<open>\<^bold>\<Turnstile>\<^sub>M (M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>\<and> \<^bold>\<not> (fst goTo_r\<^sub>1_c) \<^bold>\<longrightarrow> M\<^sub>1)\<close> by auto
        qed
        then have \<open>\<Turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst goTo_r\<^sub>1_c) \<triangleright> do (snd goTo_r\<^sub>1_c)) \<^bold>{ M\<^sub>1 \<^bold>}\<close> 
          using bw4t.soundness\<^sub>H by blast
        then have \<open>\<exists>b \<in> set \<Pi>\<^sub>x. \<Turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>1 \<^bold>}\<close> by auto
        moreover have \<open>\<forall>b \<in> set \<Pi>\<^sub>x. \<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>
        proof -
          have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst goTo_dropzone_c) \<triangleright> do goTo_dropzone) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>
           (is \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>)
          proof
            show \<open>\<turnstile>\<^sub>H \<^bold>{ (M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1) \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>
            proof (rule bw4t.rImp)
              show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>} ?b \<^bold>{ M\<^sub>0 \<^bold>}\<close>
              proof (rule bw4t.inf)
                obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
                moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (M\<^sub>0 \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close> by simp
                ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (M\<^sub>0\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
                  using bw4t.not_enabled_ht_spec  by blast
                moreover have \<open>?b = basic (bcap ?b)\<close> by simp
                ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (M\<^sub>0\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
              qed
            qed auto
          qed auto
          moreover 
          have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst goToBlock_b\<^sub>1_c) \<triangleright> do goToBlock_b\<^sub>1) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>
           (is \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>)
          proof
            show \<open>\<turnstile>\<^sub>H \<^bold>{ (M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1) \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>
            proof (rule bw4t.rImp)
              show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>} ?b \<^bold>{ M\<^sub>0 \<^bold>}\<close>
              proof (rule bw4t.inf)
                have \<open>M\<^sub>0\<^sub>x \<Turnstile>\<^sub>M B (invariants!0)\<close> by simp
                moreover from invariants_ht have \<open>\<turnstile>\<^sub>H \<^bold>{ B (invariants!0) \<^bold>} ?b \<^bold>{ B (invariants!0) \<^bold>}\<close> by simp
                with bw4t.soundness\<^sub>H have \<open>\<Turnstile>\<^sub>H \<^bold>{ B (invariants!0) \<^bold>} ?b \<^bold>{ B (invariants!0) \<^bold>}\<close> by simp
                ultimately have \<open>\<^bold>\<Turnstile>\<^sub>M (B (invariants!0))\<close> using bw4t.mst_basic_trace_ht_invariant by blast
                have \<open>\<^bold>\<Turnstile>\<^sub>M (M\<^sub>0 \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close>
                proof
                  fix M
                  show \<open>bw4t.mst_reachable_basic M \<longrightarrow> M \<Turnstile>\<^sub>M (M\<^sub>0 \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close>
                  proof
                    assume \<open>bw4t.mst_reachable_basic M\<close>
                    with bw4t.mst_reachable_basic_is_mst have \<open>\<nabla> M\<close> by simp
                    from \<open>bw4t.mst_reachable_basic M\<close> \<open>\<^bold>\<Turnstile>\<^sub>M (B (invariants!0))\<close> have \<open>M \<Turnstile>\<^sub>M B (invariants!0)\<close> by blast
                    then have \<open>M \<Turnstile>\<^sub>M B in_dropzone \<^bold>\<longrightarrow> B (\<^bold>\<not> in_r\<^sub>1)\<close> by (cases M) auto
                    with is_mst_negB have \<open>M \<Turnstile>\<^sub>M B in_dropzone \<^bold>\<longrightarrow> \<^bold>\<not> (B in_r\<^sub>1)\<close> using \<open>\<nabla> M\<close> by simp
                    then show \<open>M \<Turnstile>\<^sub>M (M\<^sub>0 \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close> by simp
                  qed
                qed
                moreover obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
                ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (M\<^sub>0\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
                  using bw4t.not_enabled_ht_spec by blast
                moreover have \<open>?b = basic (bcap ?b)\<close> by simp
                ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (M\<^sub>0\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
              qed
            qed auto
          qed auto
          moreover 
          have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst pickUp_b\<^sub>1_c) \<triangleright> do pickUp_b\<^sub>1) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>
           (is \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>)
          proof
            show \<open>\<turnstile>\<^sub>H \<^bold>{ (M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1) \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>
            proof (rule bw4t.rImp)
              show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>} ?b \<^bold>{ M\<^sub>0 \<^bold>}\<close>
              proof (rule bw4t.inf)
                have \<open>M\<^sub>0\<^sub>x \<Turnstile>\<^sub>M B (invariants!2)\<close> by simp
                moreover from invariants_ht have \<open>\<turnstile>\<^sub>H \<^bold>{ B (invariants!2) \<^bold>} ?b \<^bold>{ B (invariants!2) \<^bold>}\<close> by simp
                with bw4t.soundness\<^sub>H have \<open>\<Turnstile>\<^sub>H \<^bold>{ B (invariants!2) \<^bold>} ?b \<^bold>{ B (invariants!2) \<^bold>}\<close> by simp
                ultimately have \<open>\<^bold>\<Turnstile>\<^sub>M (B (invariants!2))\<close> using bw4t.mst_basic_trace_ht_invariant by blast
                have \<open>\<^bold>\<Turnstile>\<^sub>M (M\<^sub>0 \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close>
                proof
                  fix M
                  show \<open>bw4t.mst_reachable_basic M \<longrightarrow> M \<Turnstile>\<^sub>M (M\<^sub>0 \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close>
                  proof
                    assume \<open>bw4t.mst_reachable_basic M\<close>
                    with bw4t.mst_reachable_basic_is_mst have \<open>\<nabla> M\<close> by simp
                    from \<open>bw4t.mst_reachable_basic M\<close> \<open>\<^bold>\<Turnstile>\<^sub>M (B (invariants!2))\<close> have \<open>M \<Turnstile>\<^sub>M B (invariants!2)\<close> by blast
                    then have \<open>M \<Turnstile>\<^sub>M B in_dropzone \<^bold>\<longrightarrow> B (\<^bold>\<not> atBlock_b\<^sub>1)\<close> by (cases M) auto
                    with is_mst_negB have \<open>M \<Turnstile>\<^sub>M B in_dropzone \<^bold>\<longrightarrow> \<^bold>\<not> (B atBlock_b\<^sub>1)\<close> using \<open>\<nabla> M\<close> by simp
                    then show \<open>M \<Turnstile>\<^sub>M (M\<^sub>0 \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close> by simp
                  qed
                qed
                moreover obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
                ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (M\<^sub>0\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
                  using bw4t.not_enabled_ht_spec by blast
                moreover have \<open>?b = basic (bcap ?b)\<close> by simp
                ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (M\<^sub>0\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
              qed
            qed auto
          qed auto
          moreover 
          have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst putDown_c) \<triangleright> do putDown) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>
           (is \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>)
          proof
            show \<open>\<turnstile>\<^sub>H \<^bold>{ (M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1) \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>
            proof (rule bw4t.rImp)
              show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>} ?b \<^bold>{ M\<^sub>0 \<^bold>}\<close>
              proof (rule bw4t.inf)
                obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
                moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (M\<^sub>0 \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close> by simp
                ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (M\<^sub>0\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
                  using bw4t.not_enabled_ht_spec by blast
                moreover have \<open>?b = basic (bcap ?b)\<close> by simp
                ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (M\<^sub>0\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
              qed
            qed auto
          qed auto
          moreover have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst goTo_r\<^sub>1_c) \<triangleright> do goTo_r\<^sub>1) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>
          proof
            show \<open>\<^bold>\<Turnstile>\<^sub>M (((M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1) \<^bold>\<and> \<^bold>\<not> (fst goTo_r\<^sub>1_c)) \<^bold>\<longrightarrow> M\<^sub>0 \<^bold>\<or> M\<^sub>1)\<close> by simp
            show \<open>\<turnstile>\<^sub>H \<^bold>{ (M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1) \<^bold>\<and> fst goTo_r\<^sub>1_c \<^bold>} goTo_r\<^sub>1 \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close> 
            proof (rule bw4t.rImp)
              from eff show \<open>\<turnstile>\<^sub>H \<^bold>{ (M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1) \<^bold>\<and> fst goTo_r\<^sub>1_c \<^bold>} goTo_r\<^sub>1 \<^bold>{ M\<^sub>1 \<^bold>}\<close> by simp
            qed auto
          qed
          ultimately show ?thesis by simp
        qed
        then have \<open>\<forall>b \<in> set \<Pi>\<^sub>x. \<Turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>
          using bw4t.soundness\<^sub>H by blast
        ultimately have \<open>bw4t.Agent \<Turnstile>\<^sub>T# M\<^sub>0\<^sup>T ensures M\<^sub>1\<^sup>T\<close> using bw4t.ex_ensures[where \<phi>=M\<^sub>0 and \<psi>=M\<^sub>1] by simp
        with \<open>s \<in> bw4t.Agent\<close> show ?thesis by simp
    qed
  qed
  moreover have \<open>\<dots> \<mapsto> M\<^sub>2\<^sup>T\<close>
  proof -
    have \<open>\<forall>b \<in> set \<Pi>\<^sub>x. (\<Turnstile>\<^sub>H \<^bold>{ M\<^sub>1 \<^bold>\<and> \<^bold>\<not> M\<^sub>2 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>1 \<^bold>\<or> M\<^sub>2 \<^bold>})\<close> sorry
    moreover have \<open>\<exists>b \<in> set \<Pi>\<^sub>x. \<Turnstile>\<^sub>H \<^bold>{ M\<^sub>1 \<^bold>\<and> \<^bold>\<not> M\<^sub>2 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>2 \<^bold>}\<close> sorry
    ultimately have \<open>\<forall>s \<in> bw4t.Agent. \<forall>i. s, i \<Turnstile>\<^sub>T (M\<^sub>1\<^sup>T ensures M\<^sub>2\<^sup>T)\<close> using bw4t.ex_ensures by blast
    then show ?thesis using bw4t.ensures by simp
  qed    
  moreover have \<open>\<dots> \<mapsto> M\<^sub>3\<^sup>T\<close>
  proof -
    have \<open>\<forall>b \<in> set \<Pi>\<^sub>x. (\<Turnstile>\<^sub>H \<^bold>{ M\<^sub>2 \<^bold>\<and> \<^bold>\<not> M\<^sub>3 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>2 \<^bold>\<or> M\<^sub>3 \<^bold>})\<close> sorry
    moreover have \<open>\<exists>b \<in> set \<Pi>\<^sub>x. \<Turnstile>\<^sub>H \<^bold>{ M\<^sub>2 \<^bold>\<and> \<^bold>\<not> M\<^sub>3 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>3 \<^bold>}\<close> sorry
    ultimately have \<open>\<forall>s \<in> bw4t.Agent. \<forall>i. s, i \<Turnstile>\<^sub>T (M\<^sub>2\<^sup>T ensures M\<^sub>3\<^sup>T)\<close> using bw4t.ex_ensures by blast
    then show ?thesis using bw4t.ensures by simp
  qed    
  moreover have \<open>\<dots> \<mapsto> M\<^sub>4\<^sup>T\<close>
  proof -
    have \<open>\<forall>b \<in> set \<Pi>\<^sub>x. (\<Turnstile>\<^sub>H \<^bold>{ M\<^sub>3 \<^bold>\<and> \<^bold>\<not> M\<^sub>4 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>3 \<^bold>\<or> M\<^sub>4 \<^bold>})\<close> sorry
    moreover have \<open>\<exists>b \<in> set \<Pi>\<^sub>x. \<Turnstile>\<^sub>H \<^bold>{ M\<^sub>3 \<^bold>\<and> \<^bold>\<not> M\<^sub>4 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>4 \<^bold>}\<close> sorry
    ultimately have \<open>\<forall>s \<in> bw4t.Agent. \<forall>i. s, i \<Turnstile>\<^sub>T (M\<^sub>3\<^sup>T ensures M\<^sub>4\<^sup>T)\<close> using bw4t.ex_ensures by blast
    then show ?thesis using bw4t.ensures by simp
  qed    
  moreover have \<open>\<dots> \<mapsto> M\<^sub>5\<^sup>T\<close>
  proof -
    have \<open>\<forall>b \<in> set \<Pi>\<^sub>x. (\<Turnstile>\<^sub>H \<^bold>{ M\<^sub>4 \<^bold>\<and> \<^bold>\<not> M\<^sub>5 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>4 \<^bold>\<or> M\<^sub>5 \<^bold>})\<close> sorry
    moreover have \<open>\<exists>b \<in> set \<Pi>\<^sub>x. \<Turnstile>\<^sub>H \<^bold>{ M\<^sub>4 \<^bold>\<and> \<^bold>\<not> M\<^sub>5 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>5 \<^bold>}\<close> sorry
    ultimately have \<open>\<forall>s \<in> bw4t.Agent. \<forall>i. s, i \<Turnstile>\<^sub>T (M\<^sub>4\<^sup>T ensures M\<^sub>5\<^sup>T)\<close> using bw4t.ex_ensures by blast
    then show ?thesis using bw4t.ensures by simp
  qed    
  ultimately show ?thesis using bw4t.imp by blast
qed

lemma \<open>s \<in> bw4t.Agent \<Longrightarrow> s, i \<Turnstile>\<^sub>T ((B in_dropzone \<^bold>\<and> \<^bold>\<not> (B holding_b\<^sub>1) \<^bold>\<and> G collect_red)\<^sup>T \<longrightarrow>\<^sub>T \<diamondop> ((B collect_red)\<^sup>T))\<close>
  using bw4t_lt bw4t.leads_to_temp by simp

end