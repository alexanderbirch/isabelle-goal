theory Gvf_Example_BW4T imports Gvf_Temporal_Logic Gvf_Solver begin

section \<open>Example BW4T single agent specification.\<close>

subsection \<open>Agent specification setup\<close>

\<comment> \<open>Propositions.\<close>
abbreviation \<open>in_dropzone \<equiv> \<Phi>\<^sub>P.Atom ''in_dropzone''\<close>
abbreviation \<open>in_r1 \<equiv> \<Phi>\<^sub>P.Atom ''in_r1''\<close>
abbreviation \<open>holding_b1 \<equiv> \<Phi>\<^sub>P.Atom ''holding_b1''\<close>
abbreviation \<open>atBlock_b1 \<equiv> \<Phi>\<^sub>P.Atom ''atBlock_b1''\<close>
abbreviation \<open>collect_red \<equiv> \<Phi>\<^sub>P.Atom ''collect''\<close>

\<comment> \<open>Actions.\<close>
abbreviation \<open>goTo_dropzone::cap \<equiv> basic ''0''\<close>
abbreviation \<open>goTo_r1::cap \<equiv> basic ''1''\<close>
abbreviation \<open>goToBlock_b1::cap \<equiv> basic ''2''\<close>
abbreviation \<open>pickUp_b1::cap \<equiv> basic ''3''\<close>
abbreviation \<open>putDown::cap \<equiv> basic ''4''\<close>

abbreviation \<open>goTo_dropzone_c \<equiv> (B in_r1 \<^bold>\<and> B holding_b1) \<triangleright> do goTo_dropzone\<close>
abbreviation \<open>goTo_r1_c \<equiv> (B in_dropzone \<^bold>\<and> \<^bold>\<not> (B holding_b1)) \<triangleright> do goTo_r1\<close>
abbreviation \<open>goToBlock_b1_c \<equiv> (B in_r1 \<^bold>\<and> \<^bold>\<not> (B atBlock_b1) \<^bold>\<and> \<^bold>\<not> (B holding_b1)) \<triangleright> do goToBlock_b1\<close>
abbreviation \<open>pickUp_b1_c \<equiv> (B atBlock_b1 \<^bold>\<and> \<^bold>\<not> (B holding_b1)) \<triangleright> do pickUp_b1\<close>
abbreviation \<open>putDown_c \<equiv> (B holding_b1 \<^bold>\<and> B in_dropzone) \<triangleright> do putDown\<close>

\<comment> \<open>Specification of the program.\<close>
abbreviation \<open>\<Pi>\<^sub>x \<equiv> [ goTo_dropzone_c, goTo_r1_c, goToBlock_b1_c, pickUp_b1_c, putDown_c]\<close>

abbreviation \<open>invariants \<equiv> [in_dropzone \<^bold>\<longrightarrow> \<^bold>\<not> in_r1, in_r1 \<^bold>\<longrightarrow> \<^bold>\<not> in_dropzone]\<close>

abbreviation
  \<open>M\<^sub>0\<^sub>x::mental_state \<equiv> ( [ in_dropzone, \<^bold>\<not> in_r1, \<^bold>\<not> holding_b1, \<^bold>\<not> atBlock_b1 ] @ invariants, [ collect_red ] )\<close>

abbreviation \<open>S\<^sub>x' \<equiv>
  [
    (bcap goTo_dropzone, fst goTo_dropzone_c, 
      [
        \<^bold>{ B in_r1 \<^bold>\<and> B holding_b1 \<^bold>} goTo_dropzone \<^bold>{ B in_dropzone \<^bold>}
      ]),

    (bcap goTo_r1, fst goTo_r1_c, 
      [
        \<^bold>{ B in_dropzone \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>} goTo_r1 \<^bold>{ B in_r1 \<^bold>}
      ]),

    (bcap goToBlock_b1, fst goToBlock_b1_c, 
      [
        \<^bold>{ B in_r1 \<^bold>\<and> \<^bold>\<not> (B atBlock_b1) \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>} goToBlock_b1 \<^bold>{ B atBlock_b1 \<^bold>}
      ]),

    (bcap pickUp_b1, fst pickUp_b1_c, 
      [
        \<^bold>{ B atBlock_b1 \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>} pickUp_b1 \<^bold>{ B holding_b1 \<^bold>}
      ]),

    (bcap putDown, fst putDown_c, 
      [
        \<^bold>{ B in_dropzone \<^bold>\<and> B holding_b1 \<^bold>} putDown \<^bold>{ B collect_red \<^bold>}
      ])
  ]\<close>

 \<comment> \<open>Invariants\<close>
abbreviation \<open>L\<^sub>x \<equiv>
  [
    ((\<lambda>_. True), map B invariants),
    ((\<lambda>b. b \<notin> bcap ` {pickUp_b1, putDown}), [ B holding_b1, \<^bold>\<not> (B holding_b1) ]),
    ((\<lambda>b. b \<noteq> bcap putDown), [ \<^bold>\<not> (B collect_red)]),
    ((\<lambda>b. b \<noteq> bcap goToBlock_b1), [ \<^bold>\<not> (B atBlock_b1) ]),
    ((\<lambda>b. b \<in> bcap ` {goToBlock_b1, pickUp_b1}, [ B in_r1 ]))
  ]\<close>

abbreviation
  \<open>S\<^sub>x \<equiv> from_frax (S\<^sub>x', L\<^sub>x)\<close>

\<comment> \<open>Prove that the example is an instance of the single agent program locale.\<close>
\<comment> \<open>We use a trick where \<T> is simply some function that complies to our definition due to Hilbert's epsilon operator i.e. the axiom of choice.\<close>
definition \<open>\<T>\<^sub>x \<equiv> SOME \<T>. complies S\<^sub>x \<T>\<close>

fun f_construct :: \<open>\<Phi>\<^sub>L list \<Rightarrow> (string \<Rightarrow> bool)\<close> where
  \<open>f_construct [] = (\<lambda>_. False)\<close> |
  \<open>f_construct ((\<Phi>\<^sub>P.Atom s)#S) = (f_construct S)(s := True)\<close> |
  \<open>f_construct (_#S) = f_construct S\<close>

abbreviation sat where \<open>sat M \<Sigma> s \<equiv> (M \<Turnstile>\<^sub>M fst (snd s) \<longrightarrow> satisfiable_base M (snd (snd s)) \<Sigma>)\<close>

interpretation bw4t: single_agent_program \<T>\<^sub>x \<open>set \<Pi>\<^sub>x\<close> M\<^sub>0\<^sub>x S\<^sub>x
proof -
  have \<open>\<nabla> M\<^sub>0\<^sub>x\<close>
  proof -
    let ?f = \<open>f_construct (fst M\<^sub>0\<^sub>x)\<close>
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
    have \<open>\<nabla> M \<longrightarrow> (\<forall>s\<in>set S\<^sub>x. \<exists>\<Sigma>. sat M \<Sigma> s)\<close>
    proof 
      assume \<open>\<nabla> M\<close>
      \<comment> \<open>All generated hts for actions\<close>
      let ?ht_L\<^sub>1 = \<open>\<^bold>{ B (in_dropzone \<^bold>\<longrightarrow> \<^bold>\<not> in_r1) \<^bold>} (basic ''dummy'') \<^bold>{ B (in_dropzone \<^bold>\<longrightarrow> \<^bold>\<not> in_r1) \<^bold>}\<close>
      let ?ht_L\<^sub>2 = \<open>\<^bold>{ B (in_r1 \<^bold>\<longrightarrow> \<^bold>\<not> in_dropzone) \<^bold>} (basic ''dummy'') \<^bold>{ B (in_r1 \<^bold>\<longrightarrow> \<^bold>\<not> in_dropzone) \<^bold>}\<close>
      let ?ht_L\<^sub>3 = \<open>\<^bold>{ B holding_b1 \<^bold>} (basic ''dummy'') \<^bold>{ B holding_b1 \<^bold>}\<close>
      let ?ht_L\<^sub>4 = \<open>\<^bold>{ \<^bold>\<not> (B holding_b1) \<^bold>} (basic ''dummy'') \<^bold>{ \<^bold>\<not> (B holding_b1) \<^bold>}\<close>
      let ?ht_L\<^sub>5 = \<open>\<^bold>{ \<^bold>\<not> (B collect_red) \<^bold>} (basic ''dummy'') \<^bold>{ \<^bold>\<not> (B collect_red) \<^bold>}\<close>
      let ?ht_L\<^sub>6 = \<open>\<^bold>{ B in_r1 \<^bold>} (basic ''dummy'') \<^bold>{ B in_r1 \<^bold>}\<close>
      let ?ht_L\<^sub>7 = \<open>\<^bold>{ \<^bold>\<not> (B atBlock_b1) \<^bold>} (basic ''dummy'') \<^bold>{ \<^bold>\<not> (B atBlock_b1) \<^bold>}\<close>
      \<comment> \<open>goTo_dropzone\<close>
      have \<open>sat M [\<^bold>\<not> in_r1, in_dropzone, \<^bold>\<not> atBlock_b1, holding_b1] (S\<^sub>x!0)\<close>
      (is \<open>sat M ?\<Sigma> ?x\<close>)
      proof
        assume *: \<open>M \<Turnstile>\<^sub>M fst (snd ?x)\<close>
        show \<open>satisfiable_base M (snd (snd ?x)) ?\<Sigma>\<close> unfolding satisfiable_base_def
        proof
          show \<open>\<not> fst M \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close>
          proof
            let ?f = \<open>f_construct ?\<Sigma>\<close>
            have \<open>\<forall>p \<in> set ?\<Sigma>. semantics\<^sub>P ?f p\<close> by simp
            then have \<open>\<exists>f. \<forall>p \<in> set ?\<Sigma>. semantics\<^sub>P f p\<close> by blast
            with not_contradict show \<open>\<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> by auto
          qed
          show \<open>\<forall>ht\<in>set (snd (snd ?x)). M \<Turnstile>\<^sub>M pre ht \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ht\<close>
          proof -
            from * have \<open>M \<Turnstile>\<^sub>M pre ((snd (snd ?x))!0) \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ((snd (snd ?x))!0)\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>1 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>1\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>2 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>2\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>3 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>3\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>4 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>4\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>5 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>5\<close>
            proof -
              have \<open>\<exists>f. \<not> f ''in_r1'' \<and> f ''in_dropzone'' \<and> \<not> f ''atBlock_b1'' \<and> f ''holding_b1'' \<and> \<not> f ''collect''\<close>
                by (rule exI[where x=\<open>f_construct ?\<Sigma>\<close>], simp)
              then show ?thesis by simp
            qed
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>7 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>7\<close>
            proof -
              have \<open>\<exists>f. f ''in_dropzone'' \<and> \<not> f ''in_r1'' \<and> \<not> f ''atBlock_b1'' \<and> f ''holding_b1''\<close>
                by (rule exI[where x=\<open>f_construct ?\<Sigma>\<close>], simp)
              then show ?thesis by simp
            qed
            ultimately show ?thesis by auto
          qed
        qed
      qed
      then have \<open>\<exists>\<Sigma>. sat M \<Sigma> (S\<^sub>x!0)\<close> by auto
      \<comment> \<open>goTo_r1\<close>
      moreover have \<open>sat M [in_r1, \<^bold>\<not> in_dropzone, \<^bold>\<not> atBlock_b1, \<^bold>\<not> holding_b1] (S\<^sub>x!1)\<close>
      (is \<open>sat M ?\<Sigma> ?x\<close>)
      proof
        assume *: \<open>M \<Turnstile>\<^sub>M fst (snd ?x)\<close>
        show \<open>satisfiable_base M (snd (snd ?x)) ?\<Sigma>\<close> unfolding satisfiable_base_def
        proof
          show \<open>\<not> fst M \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close>
          proof
            let ?f = \<open>f_construct ?\<Sigma>\<close>
            have \<open>\<forall>p \<in> set ?\<Sigma>. semantics\<^sub>P ?f p\<close> by simp
            then have \<open>\<exists>f. \<forall>p \<in> set ?\<Sigma>. semantics\<^sub>P f p\<close> by blast
            with not_contradict show \<open>\<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> by auto
          qed
          show \<open>\<forall>ht\<in>set (snd (snd ?x)). M \<Turnstile>\<^sub>M pre ht \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ht\<close>
          proof -
            from * have \<open>M \<Turnstile>\<^sub>M pre ((snd (snd ?x))!0) \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ((snd (snd ?x))!0)\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>1 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>1\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>2 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>2\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>3 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>3\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>4 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>4\<close> 
            proof -
              have \<open>\<exists>f. f ''in_r1'' \<and> \<not> f ''in_dropzone'' \<and> \<not> f ''atBlock_b1'' \<and> \<not> f ''holding_b1''\<close>
                by (rule exI[where x=\<open>f_construct ?\<Sigma>\<close>], simp)
              then show ?thesis by simp
            qed
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>5 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>5\<close>
            proof -
              have \<open>\<exists>f. f ''in_r1'' \<and> \<not> f ''in_dropzone'' \<and> \<not> f ''atBlock_b1'' \<and> \<not> f ''holding_b1'' \<and> \<not> f ''collect''\<close>
                by (rule exI[where x=\<open>f_construct ?\<Sigma>\<close>], simp)
              then show ?thesis by simp
            qed
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>7 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>7\<close>
            proof -
              have \<open>\<exists>f. f ''in_r1'' \<and> \<not> f ''in_dropzone'' \<and> \<not> f ''atBlock_b1'' \<and> \<not> f ''holding_b1''\<close>
                by (rule exI[where x=\<open>f_construct ?\<Sigma>\<close>], simp)
              then show ?thesis by simp
            qed
            ultimately show ?thesis by auto
          qed
        qed
      qed
      then have \<open>\<exists>\<Sigma>. sat M \<Sigma> (S\<^sub>x!1)\<close> by auto
      \<comment> \<open>goToBlock_b1\<close>
      moreover have \<open>sat M [in_r1, \<^bold>\<not> in_dropzone, atBlock_b1, \<^bold>\<not> holding_b1] (S\<^sub>x!2)\<close>
      (is \<open>sat M ?\<Sigma> ?x\<close>)
      proof
        assume *: \<open>M \<Turnstile>\<^sub>M fst (snd ?x)\<close>
        show \<open>satisfiable_base M (snd (snd ?x)) ?\<Sigma>\<close> unfolding satisfiable_base_def
        proof
          show \<open>\<not> fst M \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close>
          proof
            let ?f = \<open>f_construct ?\<Sigma>\<close>
            have \<open>\<forall>p \<in> set ?\<Sigma>. semantics\<^sub>P ?f p\<close> by simp
            then have \<open>\<exists>f. \<forall>p \<in> set ?\<Sigma>. semantics\<^sub>P f p\<close> by blast
            with not_contradict show \<open>\<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> by auto
          qed
          show \<open>\<forall>ht\<in>set (snd (snd ?x)). M \<Turnstile>\<^sub>M pre ht \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ht\<close>
          proof -
            from * have \<open>M \<Turnstile>\<^sub>M pre ((snd (snd ?x))!0) \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ((snd (snd ?x))!0)\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>1 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>1\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>1 \<longrightarrow>(?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>2\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>3 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>3\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>4 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>4\<close>
            proof -
              have \<open>\<exists>f. f ''atBlock_b1'' \<and> f ''in_r1'' \<and> \<not> f ''in_dropzone'' \<and> \<not> f ''holding_b1''\<close>
                by (rule exI[where x=\<open>f_construct ?\<Sigma>\<close>], simp)
              then show ?thesis by simp
            qed
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>5 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>5\<close>
            proof -
              have \<open>\<exists>f. f ''in_r1'' \<and> \<not> f ''in_dropzone'' \<and> f ''atBlock_b1'' \<and> \<not> f ''holding_b1'' \<and> \<not> f ''collect''\<close>
                by (rule exI[where x=\<open>f_construct ?\<Sigma>\<close>], simp)
              then show ?thesis by simp
            qed
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>6 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>6\<close> by simp
            ultimately show ?thesis by auto
          qed
        qed
      qed
      then have \<open>\<exists>\<Sigma>. sat M \<Sigma> (S\<^sub>x!2)\<close> by auto
      \<comment> \<open>pickUp_b1\<close>
      moreover have \<open>sat M [in_r1, \<^bold>\<not> in_dropzone, holding_b1] (S\<^sub>x!3)\<close>
      (is \<open>sat M ?\<Sigma> ?x\<close>)
      proof
        assume *: \<open>M \<Turnstile>\<^sub>M fst (snd ?x)\<close>
        show \<open>satisfiable_base M (snd (snd ?x)) ?\<Sigma>\<close> unfolding satisfiable_base_def
        proof
          show \<open>\<not> fst M \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close>
          proof
            let ?f = \<open>f_construct ?\<Sigma>\<close>
            have \<open>\<forall>p \<in> set ?\<Sigma>. semantics\<^sub>P ?f p\<close> by simp
            then have \<open>\<exists>f. \<forall>p \<in> set ?\<Sigma>. semantics\<^sub>P f p\<close> by blast
            with not_contradict show \<open>\<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> by auto
          qed
          show \<open>\<forall>ht\<in>set (snd (snd ?x)). M \<Turnstile>\<^sub>M pre ht \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ht\<close>
          proof -
            from * have \<open>M \<Turnstile>\<^sub>M pre ((snd (snd ?x))!0) \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ((snd (snd ?x))!0)\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>1 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>1\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>2 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>2\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>5 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>5\<close> 
            proof -
              have \<open>\<exists>f. f ''in_r1'' \<and> \<not> f ''in_dropzone'' \<and> f ''holding_b1'' \<and> \<not> f ''collect''\<close>
                by (rule exI[where x=\<open>f_construct ?\<Sigma>\<close>], simp)
              then show ?thesis by simp
            qed
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>6 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>6\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>7 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>7\<close> by simp
            ultimately show ?thesis by auto
          qed
        qed
      qed
      then have \<open>\<exists>\<Sigma>. sat M \<Sigma> (S\<^sub>x!3)\<close> by auto
      \<comment> \<open>putDown\<close>
      moreover have \<open>sat M [\<^bold>\<not> in_r1, in_dropzone, collect_red] (S\<^sub>x!4)\<close>
      (is \<open>sat M ?\<Sigma> ?x\<close>)
      proof
        assume *: \<open>M \<Turnstile>\<^sub>M fst (snd ?x)\<close>
        show \<open>satisfiable_base M (snd (snd ?x)) ?\<Sigma>\<close> unfolding satisfiable_base_def
        proof
          show \<open>\<not> fst M \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close>
          proof
            let ?f = \<open>f_construct ?\<Sigma>\<close>
            have \<open>\<forall>p \<in> set ?\<Sigma>. semantics\<^sub>P ?f p\<close> by simp
            then have \<open>\<exists>f. \<forall>p \<in> set ?\<Sigma>. semantics\<^sub>P f p\<close> by blast
            with not_contradict show \<open>\<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> by auto
          qed
          show \<open>\<forall>ht\<in>set (snd (snd ?x)). M \<Turnstile>\<^sub>M pre ht \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ht\<close>
          proof -
            from * have \<open>M \<Turnstile>\<^sub>M pre ((snd (snd ?x))!0) \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ((snd (snd ?x))!0)\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>1 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>1\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>2 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>2\<close> by simp
            moreover from * have \<open>M \<Turnstile>\<^sub>M pre ?ht_L\<^sub>7 \<longrightarrow> (?\<Sigma>, [\<psi><-snd M. \<not> ?\<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ?ht_L\<^sub>7\<close>
            proof -
              have \<open>\<exists>f. \<not> f ''in_r1'' \<and> f ''in_dropzone'' \<and> f ''collect'' \<and> \<not> f ''atBlock_b1''\<close>
                by (rule exI[where x=\<open>f_construct ?\<Sigma>\<close>], simp)
              then show ?thesis by simp
            qed
            ultimately show ?thesis by auto
          qed
        qed
      qed
      then have \<open>\<exists>\<Sigma>. sat M \<Sigma> (S\<^sub>x!4)\<close> by auto
      \<comment> \<open>Combine\<close>
      ultimately show \<open>\<forall>s\<in>set S\<^sub>x. \<exists>\<Sigma>. sat M \<Sigma> s\<close> by simp
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
abbreviation \<open>M\<^sub>0 \<equiv> B in_dropzone \<^bold>\<and> \<^bold>\<not> (B atBlock_b1) \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>\<and> G collect_red\<close>
abbreviation \<open>M\<^sub>1 \<equiv> B in_r1 \<^bold>\<and> \<^bold>\<not> (B atBlock_b1) \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>\<and> G collect_red\<close>
abbreviation \<open>M\<^sub>2 \<equiv> B in_r1 \<^bold>\<and> B atBlock_b1 \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>\<and> G collect_red\<close>
abbreviation \<open>M\<^sub>3 \<equiv> B in_r1 \<^bold>\<and> B holding_b1 \<^bold>\<and> G collect_red\<close>
abbreviation \<open>M\<^sub>4 \<equiv> B in_dropzone \<^bold>\<and> B holding_b1 \<^bold>\<and> G collect_red\<close>
abbreviation \<open>M\<^sub>5 \<equiv> B collect_red\<close>

lemma \<Pi>\<^sub>x_exists_hts: \<open>(\<Phi>, basic n) \<in> set \<Pi>\<^sub>x \<Longrightarrow> \<exists>hts. (n, \<Phi>, hts) \<in> set S\<^sub>x\<close> by fastforce

lemma invariants_ht': \<open>(n, \<Phi>, hts) \<in> set S\<^sub>x \<Longrightarrow> \<phi> \<in> set invariants \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ B \<phi> \<^bold>} (basic n) \<^bold>{ B \<phi> \<^bold>}\<close> 
  by (rule bw4t.import) auto

lemma invariants_ht: \<open>\<phi> \<in> set invariants \<Longrightarrow> a \<in> bw4t.Cap \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ B \<phi> \<^bold>} a \<^bold>{ B \<phi> \<^bold>}\<close>
proof (cases a)
  case (basic n)
  assume \<open>\<phi> \<in> set invariants\<close>
  moreover assume \<open>a \<in> bw4t.Cap\<close>
  with basic have \<open>a \<in> {basic a | a. \<exists>\<phi>. (\<phi>, basic a) \<in> set \<Pi>\<^sub>x}\<close> unfolding bw4t.Cap_def by auto
  with basic obtain \<Phi> where \<open>(\<Phi>, basic n) \<in> set \<Pi>\<^sub>x\<close> by blast
  with \<Pi>\<^sub>x_exists_hts obtain hts where \<open>(n, \<Phi>, hts) \<in> set S\<^sub>x\<close> by blast
  ultimately have \<open>\<turnstile>\<^sub>H \<^bold>{ B \<phi> \<^bold>} (basic n) \<^bold>{ B \<phi> \<^bold>}\<close> using invariants_ht' by simp
  with basic show ?thesis by simp
next
  case adopt 
  with bw4t.adoptB show ?thesis by simp
next
  case drop 
  with bw4t.dropB show ?thesis by simp
qed

lemma G_collect_red_ht:
  assumes \<open>basic a \<in> set (map snd \<Pi>\<^sub>x)\<close>
    shows \<open>basic a \<noteq> putDown \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ G collect_red \<^bold>} (basic a) \<^bold>{ G collect_red \<^bold>}\<close>
proof -
  assume \<open>basic a \<noteq> putDown\<close>
  with assms obtain \<Phi> hts where *: \<open>(a, \<Phi>, hts) \<in> set S\<^sub>x\<close> by fastforce
  with \<open>basic a \<noteq> putDown\<close> have \<open>\<^bold>{ \<^bold>\<not> (B collect_red) \<^bold>} (basic a) \<^bold>{ \<^bold>\<not> (B collect_red) \<^bold>} \<in> set hts\<close>
    by auto
  with bw4t.import have \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not> (B collect_red) \<^bold>} (basic a) \<^bold>{ \<^bold>\<not> (B collect_red) \<^bold>}\<close> using * by auto
  moreover have \<open>\<turnstile>\<^sub>H \<^bold>{ G collect_red \<^bold>} (basic a) \<^bold>{ B collect_red \<^bold>\<or> G collect_red \<^bold>}\<close> 
    using bw4t.persist by simp
  ultimately have \<open>\<turnstile>\<^sub>H \<^bold>{ G collect_red \<^bold>\<and> \<^bold>\<not> (B collect_red) \<^bold>} (basic a) \<^bold>{ (B collect_red \<^bold>\<or> G collect_red) \<^bold>\<and> \<^bold>\<not> (B collect_red) \<^bold>}\<close> 
    using bw4t.rCon by simp
  moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (G collect_red \<^bold>\<longrightarrow> G collect_red \<^bold>\<and> \<^bold>\<not> (B collect_red))\<close> by simp
  moreover have \<open>\<^bold>\<Turnstile>\<^sub>M ((B collect_red \<^bold>\<or> G collect_red) \<^bold>\<and> \<^bold>\<not> (B collect_red) \<^bold>\<longrightarrow> G collect_red)\<close> by auto
  ultimately show \<open>\<turnstile>\<^sub>H \<^bold>{ G collect_red \<^bold>} (basic a) \<^bold>{ G collect_red \<^bold>}\<close> using bw4t.rImp by blast
qed

lemma bw4t_lt: \<open>M\<^sub>0\<^sup>T \<mapsto> M\<^sub>5\<^sup>T\<close>
proof -
  \<comment> \<open>Step 1\<close>
  have \<open>M\<^sub>0\<^sup>T \<mapsto> M\<^sub>1\<^sup>T\<close>
  proof (rule bw4t.ensures)
    have eff: \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>\<and> fst goTo_r1_c \<^bold>} goTo_r1 \<^bold>{ M\<^sub>1 \<^bold>}\<close>
    proof (rule bw4t.rImp)
      show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>} goTo_r1 \<^bold>{ M\<^sub>1 \<^bold>}\<close>
      proof
        have \<open>goTo_r1 \<in> set (map snd \<Pi>\<^sub>x)\<close> unfolding bw4t.Cap_def by simp
        then show \<open>\<turnstile>\<^sub>H \<^bold>{ G collect_red \<^bold>} goTo_r1 \<^bold>{ G collect_red \<^bold>}\<close>
          using G_collect_red_ht by simp
      next
        show \<open>\<turnstile>\<^sub>H \<^bold>{ B in_dropzone \<^bold>\<and> \<^bold>\<not> (B atBlock_b1) \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>} goTo_r1 \<^bold>{ B in_r1 \<^bold>\<and> \<^bold>\<not> (B atBlock_b1) \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ B in_dropzone \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>\<and> \<^bold>\<not> (B atBlock_b1) \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>} goTo_r1 \<^bold>{ B in_r1 \<^bold>\<and> \<^bold>\<not> (B atBlock_b1) \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>}\<close>
          proof
            show \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not> (B holding_b1) \<^bold>} goTo_r1 \<^bold>{ \<^bold>\<not> (B holding_b1) \<^bold>}\<close> using bw4t.import by simp
          next
            show \<open>\<turnstile>\<^sub>H \<^bold>{ B in_dropzone \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>\<and> \<^bold>\<not> (B atBlock_b1) \<^bold>} goTo_r1 \<^bold>{ B in_r1 \<^bold>\<and> \<^bold>\<not> (B atBlock_b1) \<^bold>}\<close>
            proof
              show \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not> (B atBlock_b1) \<^bold>} goTo_r1 \<^bold>{ \<^bold>\<not> (B atBlock_b1) \<^bold>}\<close> using bw4t.import by simp
            next
              show  \<open>\<turnstile>\<^sub>H \<^bold>{ B in_dropzone \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>} goTo_r1 \<^bold>{ B in_r1 \<^bold>}\<close> 
                using bw4t.import by simp
            qed
          qed
        qed auto
      qed 
    qed auto
    have \<open>\<exists>b \<in> set \<Pi>\<^sub>x. \<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>1 \<^bold>}\<close>
    proof
      show \<open>goTo_r1_c \<in> set \<Pi>\<^sub>x\<close> by simp
      show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst goTo_r1_c) \<triangleright> do (snd goTo_r1_c)) \<^bold>{ M\<^sub>1 \<^bold>}\<close>
      proof
        from eff show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>\<and> fst goTo_r1_c \<^bold>} (snd goTo_r1_c) \<^bold>{ M\<^sub>1 \<^bold>}\<close> by simp
        show \<open>\<^bold>\<Turnstile>\<^sub>M (M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>\<and> \<^bold>\<not> (fst goTo_r1_c) \<^bold>\<longrightarrow> M\<^sub>1)\<close> by auto
      qed
    qed
    with bw4t.soundness\<^sub>H have \<open>\<exists>b \<in> set \<Pi>\<^sub>x. \<Turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>1 \<^bold>}\<close> by auto
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
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst goToBlock_b1_c) \<triangleright> do goToBlock_b1) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ (M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1) \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>} ?b \<^bold>{ M\<^sub>0 \<^bold>}\<close>
          proof (rule bw4t.inf)
            have \<open>M\<^sub>0\<^sub>x \<Turnstile>\<^sub>M B (invariants!0)\<close> by simp
            moreover have \<open>\<forall>a\<in>bw4t.Cap. \<turnstile>\<^sub>H \<^bold>{ B (invariants!0) \<^bold>} a \<^bold>{ B (invariants!0) \<^bold>}\<close> 
              using invariants_ht by simp
            ultimately have \<open>\<^bold>\<Turnstile>\<^sub>M (B (invariants!0))\<close> 
              using bw4t.mst_basic_trace_ht_invariant bw4t.soundness\<^sub>H by blast
            have \<open>\<^bold>\<Turnstile>\<^sub>M (M\<^sub>0 \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close>
            proof
              fix M
              show \<open>bw4t.mst_reachable_basic M \<longrightarrow> M \<Turnstile>\<^sub>M (M\<^sub>0 \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close>
              proof
                assume \<open>bw4t.mst_reachable_basic M\<close>
                with bw4t.mst_reachable_basic_is_mst have \<open>\<nabla> M\<close> by simp
                from \<open>bw4t.mst_reachable_basic M\<close> \<open>\<^bold>\<Turnstile>\<^sub>M (B (invariants!0))\<close> have \<open>M \<Turnstile>\<^sub>M B (invariants!0)\<close> by blast
                then have \<open>M \<Turnstile>\<^sub>M B in_dropzone \<^bold>\<longrightarrow> B (\<^bold>\<not> in_r1)\<close> by (cases M) auto
                with is_mst_negB have \<open>M \<Turnstile>\<^sub>M B in_dropzone \<^bold>\<longrightarrow> \<^bold>\<not> (B in_r1)\<close> using \<open>\<nabla> M\<close> by simp
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
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst pickUp_b1_c) \<triangleright> do pickUp_b1) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ (M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1) \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>} ?b \<^bold>{ M\<^sub>0 \<^bold>}\<close>
          proof (rule bw4t.inf)
            have \<open>\<^bold>\<Turnstile>\<^sub>M (M\<^sub>0 \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close> by simp
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
      moreover have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst goTo_r1_c) \<triangleright> do goTo_r1) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>
      proof
        show \<open>\<^bold>\<Turnstile>\<^sub>M (((M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1) \<^bold>\<and> \<^bold>\<not> (fst goTo_r1_c)) \<^bold>\<longrightarrow> M\<^sub>0 \<^bold>\<or> M\<^sub>1)\<close> by simp
        show \<open>\<turnstile>\<^sub>H \<^bold>{ (M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1) \<^bold>\<and> fst goTo_r1_c \<^bold>} goTo_r1 \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close> 
        proof (rule bw4t.rImp)
          from eff show \<open>\<turnstile>\<^sub>H \<^bold>{ (M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1) \<^bold>\<and> fst goTo_r1_c \<^bold>} goTo_r1 \<^bold>{ M\<^sub>1 \<^bold>}\<close> by simp
        qed auto
      qed
      ultimately show ?thesis by simp
    qed
    then have \<open>\<forall>b \<in> set \<Pi>\<^sub>x. \<Turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close>
      using bw4t.soundness\<^sub>H by blast
    ultimately show \<open>\<forall>s\<in>bw4t.Agent. \<forall>i. s, i \<Turnstile>\<^sub>T (M\<^sub>0\<^sup>T ensures M\<^sub>1\<^sup>T)\<close> using bw4t.ex_ensures[where \<phi>=M\<^sub>0 and \<psi>=M\<^sub>1] by simp
  qed
  \<comment> \<open>Step 2\<close>
  moreover have \<open>\<dots> \<mapsto> M\<^sub>2\<^sup>T\<close>
  proof (rule bw4t.ensures)
    have eff: \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>1 \<^bold>\<and> \<^bold>\<not> M\<^sub>2 \<^bold>\<and> fst goToBlock_b1_c \<^bold>} goToBlock_b1 \<^bold>{ M\<^sub>2 \<^bold>}\<close>
    proof (rule bw4t.rImp)
      have imp: \<open>\<turnstile>\<^sub>H \<^bold>{ B in_r1 \<^bold>\<and> \<^bold>\<not> (B atBlock_b1) \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>} goToBlock_b1 \<^bold>{ B atBlock_b1 \<^bold>}\<close>
        by (rule bw4t.import) auto
      show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>1 \<^bold>} goToBlock_b1 \<^bold>{ M\<^sub>2 \<^bold>}\<close>
      proof
        have \<open>goToBlock_b1 \<in> bw4t.Cap\<close> unfolding bw4t.Cap_def by simp
        then show \<open>\<turnstile>\<^sub>H \<^bold>{ G collect_red \<^bold>} goToBlock_b1 \<^bold>{ G collect_red \<^bold>}\<close>
          using G_collect_red_ht by simp
      next
        show \<open>\<turnstile>\<^sub>H \<^bold>{ B in_r1 \<^bold>\<and> \<^bold>\<not> (B atBlock_b1) \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>} goToBlock_b1 \<^bold>{ B in_r1 \<^bold>\<and> B atBlock_b1 \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ B in_r1 \<^bold>\<and> \<^bold>\<not> (B atBlock_b1) \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>} goToBlock_b1 \<^bold>{ B in_r1 \<^bold>\<and> B atBlock_b1 \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>}\<close>
          proof 
            show \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not> (B holding_b1) \<^bold>} goToBlock_b1 \<^bold>{ \<^bold>\<not> (B holding_b1) \<^bold>}\<close> using bw4t.import by simp
          next
            show \<open>\<turnstile>\<^sub>H \<^bold>{ B in_r1 \<^bold>\<and> \<^bold>\<not> (B atBlock_b1) \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>} goToBlock_b1 \<^bold>{ B in_r1 \<^bold>\<and> B atBlock_b1 \<^bold>}\<close>            
            proof (rule bw4t.rImp)
              show \<open>\<turnstile>\<^sub>H \<^bold>{ B in_r1 \<^bold>\<and> \<^bold>\<not> (B atBlock_b1) \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>\<and> B in_r1 \<^bold>} goToBlock_b1 \<^bold>{ B atBlock_b1 \<^bold>\<and> B in_r1 \<^bold>}\<close>
              proof
                show \<open>\<turnstile>\<^sub>H \<^bold>{ B in_r1 \<^bold>} goToBlock_b1 \<^bold>{ B in_r1 \<^bold>}\<close> using bw4t.import by simp
              next
                show \<open>\<turnstile>\<^sub>H \<^bold>{ B in_r1 \<^bold>\<and> \<^bold>\<not> (B atBlock_b1) \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>} goToBlock_b1 \<^bold>{ B atBlock_b1 \<^bold>}\<close>
                  using bw4t.import by simp
              qed
            qed auto
          qed
        qed auto
      qed
    qed auto
    have \<open>\<forall>b \<in> set \<Pi>\<^sub>x. (\<turnstile>\<^sub>H \<^bold>{ M\<^sub>1 \<^bold>\<and> \<^bold>\<not> M\<^sub>2 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>1 \<^bold>\<or> M\<^sub>2 \<^bold>})\<close>
    proof -
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>1 \<^bold>\<and> \<^bold>\<not> M\<^sub>2 \<^bold>} ((fst goTo_dropzone_c) \<triangleright> do goTo_dropzone) \<^bold>{ M\<^sub>1 \<^bold>\<or> M\<^sub>2 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>}\<close>
          proof (rule bw4t.inf)
            obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close> by simp
            ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
              using bw4t.not_enabled_ht_spec by blast
            moreover have \<open>?b = basic (bcap ?b)\<close> by simp
            ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
          qed
        qed auto
      qed auto
      moreover 
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>1 \<^bold>\<and> \<^bold>\<not> M\<^sub>2 \<^bold>} ((fst goTo_r1_c) \<triangleright> do goTo_r1) \<^bold>{ M\<^sub>1 \<^bold>\<or> M\<^sub>2 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>}\<close>
          proof (rule bw4t.inf)
            obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close>
            proof
              fix M
              show \<open>bw4t.mst_reachable_basic M \<longrightarrow> M \<Turnstile>\<^sub>M ?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>\<close>
              proof
                assume \<open>bw4t.mst_reachable_basic M\<close>
                with bw4t.mst_reachable_basic_is_mst have \<open>\<nabla> M\<close> by simp
                moreover { 
                  have \<open>M\<^sub>0\<^sub>x \<Turnstile>\<^sub>M B (invariants!1)\<close> by simp
                  moreover have \<open>\<forall>a\<in>bw4t.Cap. \<turnstile>\<^sub>H \<^bold>{ B (invariants!1) \<^bold>} a \<^bold>{ B (invariants!1) \<^bold>}\<close> 
                    using invariants_ht by simp
                  ultimately have \<open>\<^bold>\<Turnstile>\<^sub>M (B (invariants!1))\<close> 
                    using bw4t.mst_basic_trace_ht_invariant bw4t.soundness\<^sub>H by blast
                }
                ultimately have \<open>M \<Turnstile>\<^sub>M B (invariants!1)\<close> using \<open>bw4t.mst_reachable_basic M\<close> by blast
                then have \<open>M \<Turnstile>\<^sub>M B in_r1 \<^bold>\<longrightarrow> B (\<^bold>\<not> in_dropzone)\<close> by (cases M) auto
                with is_mst_negB have \<open>M \<Turnstile>\<^sub>M B in_r1 \<^bold>\<longrightarrow> \<^bold>\<not> (B in_dropzone)\<close> using \<open>\<nabla> M\<close> by simp
                have \<open>M \<Turnstile>\<^sub>M ?M\<^sub>L \<longrightarrow> M \<Turnstile>\<^sub>M \<^bold>\<not> ?\<psi>\<close>
                proof
                  assume \<open>M \<Turnstile>\<^sub>M ?M\<^sub>L\<close>
                  moreover from this have \<open>M \<Turnstile>\<^sub>M \<^bold>\<not> (B in_dropzone)\<close> 
                    using \<open>M \<Turnstile>\<^sub>M B in_r1 \<^bold>\<longrightarrow> \<^bold>\<not> (B in_dropzone)\<close> by simp
                  ultimately show \<open>M \<Turnstile>\<^sub>M \<^bold>\<not> ?\<psi>\<close> by simp
                qed
                then show \<open>M \<Turnstile>\<^sub>M ?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>\<close> by simp
              qed
            qed
            ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
              using bw4t.not_enabled_ht_spec by blast
            moreover have \<open>?b = basic (bcap ?b)\<close> by simp
            ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
          qed
        qed auto
      qed auto
      moreover 
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>1 \<^bold>\<and> \<^bold>\<not> M\<^sub>2 \<^bold>} ((fst goToBlock_b1_c) \<triangleright> do goToBlock_b1) \<^bold>{ M\<^sub>1 \<^bold>\<or> M\<^sub>2 \<^bold>}\<close>
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>1 \<^bold>\<and> \<^bold>\<not> M\<^sub>2 \<^bold>\<and> fst goToBlock_b1_c \<^bold>} goToBlock_b1 \<^bold>{ M\<^sub>1 \<^bold>\<or> M\<^sub>2 \<^bold>}\<close>
        proof (rule bw4t.rImp)
          from eff show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>1 \<^bold>\<and> \<^bold>\<not> M\<^sub>2 \<^bold>\<and> fst goToBlock_b1_c \<^bold>} goToBlock_b1 \<^bold>{ M\<^sub>2 \<^bold>}\<close> .
        qed auto
      qed auto
      moreover 
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>1 \<^bold>\<and> \<^bold>\<not> M\<^sub>2 \<^bold>} ((fst pickUp_b1_c) \<triangleright> do pickUp_b1) \<^bold>{ M\<^sub>1 \<^bold>\<or> M\<^sub>2 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>}\<close>
          proof (rule bw4t.inf)
            obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close> by simp
            ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
              using bw4t.not_enabled_ht_spec by blast
            moreover have \<open>?b = basic (bcap ?b)\<close> by simp
            ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
          qed
        qed auto
      qed auto
      moreover 
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>1 \<^bold>\<and> \<^bold>\<not> M\<^sub>2 \<^bold>} ((fst putDown_c) \<triangleright> do putDown) \<^bold>{ M\<^sub>1 \<^bold>\<or> M\<^sub>2 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>}\<close>
          proof (rule bw4t.inf)
            obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close> by simp
            ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
              using bw4t.not_enabled_ht_spec by blast
            moreover have \<open>?b = basic (bcap ?b)\<close> by simp
            ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
          qed
        qed auto
      qed auto
      ultimately show ?thesis by simp
    qed
    with bw4t.soundness\<^sub>H have \<open>\<forall>b \<in> set \<Pi>\<^sub>x. (\<Turnstile>\<^sub>H \<^bold>{ M\<^sub>1 \<^bold>\<and> \<^bold>\<not> M\<^sub>2 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>1 \<^bold>\<or> M\<^sub>2 \<^bold>})\<close> 
      by auto
    moreover have \<open>\<exists>b \<in> set \<Pi>\<^sub>x. \<turnstile>\<^sub>H \<^bold>{ M\<^sub>1 \<^bold>\<and> \<^bold>\<not> M\<^sub>2 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>2 \<^bold>}\<close>
    proof
      show \<open>goToBlock_b1_c \<in> set \<Pi>\<^sub>x\<close> by simp
      show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>1 \<^bold>\<and> \<^bold>\<not> M\<^sub>2 \<^bold>} ((fst goToBlock_b1_c) \<triangleright> do (snd goToBlock_b1_c)) \<^bold>{ M\<^sub>2 \<^bold>}\<close>
      proof
        from eff show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>1 \<^bold>\<and> \<^bold>\<not> M\<^sub>2 \<^bold>\<and> fst goToBlock_b1_c \<^bold>} (snd goToBlock_b1_c) \<^bold>{ M\<^sub>2 \<^bold>}\<close> by simp
      qed auto
    qed
    with bw4t.soundness\<^sub>H have \<open>\<exists>b \<in> set \<Pi>\<^sub>x. \<Turnstile>\<^sub>H \<^bold>{ M\<^sub>1 \<^bold>\<and> \<^bold>\<not> M\<^sub>2 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>2 \<^bold>}\<close> by auto
    ultimately show \<open>\<forall>s \<in> bw4t.Agent. \<forall>i. s, i \<Turnstile>\<^sub>T (M\<^sub>1\<^sup>T ensures M\<^sub>2\<^sup>T)\<close> using bw4t.ex_ensures by blast
  qed
  \<comment> \<open>Step 3\<close>
  moreover have \<open>M\<^sub>2\<^sup>T \<mapsto> M\<^sub>3\<^sup>T\<close>
  proof (rule bw4t.ensures)
    have eff: \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>2 \<^bold>\<and> \<^bold>\<not> M\<^sub>3 \<^bold>\<and> fst pickUp_b1_c \<^bold>} pickUp_b1 \<^bold>{ M\<^sub>3 \<^bold>}\<close>    
    proof (rule bw4t.rImp)
      have imp: \<open>\<turnstile>\<^sub>H \<^bold>{ B atBlock_b1 \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>} pickUp_b1 \<^bold>{ B holding_b1 \<^bold>}\<close>
        by (rule bw4t.import) auto
      show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>2 \<^bold>} pickUp_b1 \<^bold>{ M\<^sub>3 \<^bold>}\<close>
      proof
        have \<open>pickUp_b1 \<in> bw4t.Cap\<close> unfolding bw4t.Cap_def by simp
        then show \<open>\<turnstile>\<^sub>H \<^bold>{ G collect_red \<^bold>} pickUp_b1 \<^bold>{ G collect_red \<^bold>}\<close>
          using G_collect_red_ht by simp
      next
        show \<open>\<turnstile>\<^sub>H \<^bold>{ B in_r1 \<^bold>\<and> B atBlock_b1 \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>} pickUp_b1 \<^bold>{ B in_r1 \<^bold>\<and> B holding_b1 \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ B atBlock_b1 \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>\<and> B in_r1 \<^bold>} pickUp_b1 \<^bold>{ B holding_b1 \<^bold>\<and> B in_r1 \<^bold>}\<close> 
          proof
            show \<open>\<turnstile>\<^sub>H \<^bold>{ B in_r1 \<^bold>} pickUp_b1 \<^bold>{ B in_r1 \<^bold>}\<close> using bw4t.import by simp
          next
            from imp show \<open>\<turnstile>\<^sub>H \<^bold>{ B atBlock_b1 \<^bold>\<and> \<^bold>\<not> (B holding_b1) \<^bold>} pickUp_b1 \<^bold>{ B holding_b1 \<^bold>}\<close> .
          qed
        qed auto
      qed
    qed auto
    have \<open>\<forall>b \<in> set \<Pi>\<^sub>x. (\<turnstile>\<^sub>H \<^bold>{ M\<^sub>2 \<^bold>\<and> \<^bold>\<not> M\<^sub>3 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>2 \<^bold>\<or> M\<^sub>3 \<^bold>})\<close>
    proof -
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>2 \<^bold>\<and> \<^bold>\<not> M\<^sub>3 \<^bold>} ((fst goTo_dropzone_c) \<triangleright> do goTo_dropzone) \<^bold>{ M\<^sub>2 \<^bold>\<or> M\<^sub>3 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>}\<close>
          proof (rule bw4t.inf)
            obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close> by simp
            ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
              using bw4t.not_enabled_ht_spec by blast
            moreover have \<open>?b = basic (bcap ?b)\<close> by simp
            ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
          qed
        qed auto
      qed auto
      moreover 
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>2 \<^bold>\<and> \<^bold>\<not> M\<^sub>3 \<^bold>} ((fst goTo_r1_c) \<triangleright> do goTo_r1) \<^bold>{ M\<^sub>2 \<^bold>\<or> M\<^sub>3 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>}\<close>
          proof (rule bw4t.inf)
            obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close>            
            proof
              fix M
              show \<open>bw4t.mst_reachable_basic M \<longrightarrow> M \<Turnstile>\<^sub>M ?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>\<close>
              proof
                assume \<open>bw4t.mst_reachable_basic M\<close>
                with bw4t.mst_reachable_basic_is_mst have \<open>\<nabla> M\<close> by simp
                moreover { 
                  have \<open>M\<^sub>0\<^sub>x \<Turnstile>\<^sub>M B (invariants!1)\<close> by simp
                  moreover have \<open>\<forall>a\<in>bw4t.Cap. \<turnstile>\<^sub>H \<^bold>{ B (invariants!1) \<^bold>} a \<^bold>{ B (invariants!1) \<^bold>}\<close> 
                    using invariants_ht by simp
                  ultimately have \<open>\<^bold>\<Turnstile>\<^sub>M (B (invariants!1))\<close> 
                    using bw4t.mst_basic_trace_ht_invariant bw4t.soundness\<^sub>H by blast
                }
                ultimately have \<open>M \<Turnstile>\<^sub>M B (invariants!1)\<close> using \<open>bw4t.mst_reachable_basic M\<close> by blast
                then have \<open>M \<Turnstile>\<^sub>M B in_r1 \<^bold>\<longrightarrow> B (\<^bold>\<not> in_dropzone)\<close> by (cases M) auto
                with is_mst_negB have \<open>M \<Turnstile>\<^sub>M B in_r1 \<^bold>\<longrightarrow> \<^bold>\<not> (B in_dropzone)\<close> using \<open>\<nabla> M\<close> by simp
                have \<open>M \<Turnstile>\<^sub>M ?M\<^sub>L \<longrightarrow> M \<Turnstile>\<^sub>M \<^bold>\<not> ?\<psi>\<close>
                proof
                  assume \<open>M \<Turnstile>\<^sub>M ?M\<^sub>L\<close>
                  moreover from this have \<open>M \<Turnstile>\<^sub>M \<^bold>\<not> (B in_dropzone)\<close> 
                    using \<open>M \<Turnstile>\<^sub>M B in_r1 \<^bold>\<longrightarrow> \<^bold>\<not> (B in_dropzone)\<close> by simp
                  ultimately show \<open>M \<Turnstile>\<^sub>M \<^bold>\<not> ?\<psi>\<close> by simp
                qed
                then show \<open>M \<Turnstile>\<^sub>M ?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>\<close> by simp
              qed
            qed
            ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
              using bw4t.not_enabled_ht_spec by blast
            moreover have \<open>?b = basic (bcap ?b)\<close> by simp
            ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
          qed
        qed auto
      qed auto
      moreover 
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>2 \<^bold>\<and> \<^bold>\<not> M\<^sub>3 \<^bold>} ((fst goToBlock_b1_c) \<triangleright> do goToBlock_b1) \<^bold>{ M\<^sub>2 \<^bold>\<or> M\<^sub>3 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>}\<close>
          proof (rule bw4t.inf)
            obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close> by simp
            ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
              using bw4t.not_enabled_ht_spec by blast
            moreover have \<open>?b = basic (bcap ?b)\<close> by simp
            ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
          qed
        qed auto
      qed auto
      moreover 
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>2 \<^bold>\<and> \<^bold>\<not> M\<^sub>3 \<^bold>} ((fst pickUp_b1_c) \<triangleright> do pickUp_b1) \<^bold>{ M\<^sub>2 \<^bold>\<or> M\<^sub>3 \<^bold>}\<close>
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>2 \<^bold>\<and> \<^bold>\<not> M\<^sub>3 \<^bold>\<and> fst pickUp_b1_c \<^bold>} pickUp_b1 \<^bold>{ M\<^sub>2 \<^bold>\<or> M\<^sub>3 \<^bold>}\<close>
        proof (rule bw4t.rImp)
          from eff show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>2 \<^bold>\<and> \<^bold>\<not> M\<^sub>3 \<^bold>\<and> fst pickUp_b1_c \<^bold>} pickUp_b1 \<^bold>{ M\<^sub>3 \<^bold>}\<close> .
        qed auto
      qed auto
      moreover 
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>2 \<^bold>\<and> \<^bold>\<not> M\<^sub>3 \<^bold>} ((fst putDown_c) \<triangleright> do putDown) \<^bold>{ M\<^sub>2 \<^bold>\<or> M\<^sub>3 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>}\<close>
          proof (rule bw4t.inf)
            obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close> by simp
            ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
              using bw4t.not_enabled_ht_spec by blast
            moreover have \<open>?b = basic (bcap ?b)\<close> by simp
            ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
          qed
        qed auto
      qed auto
      ultimately show ?thesis by simp
    qed
    with bw4t.soundness\<^sub>H have \<open>\<forall>b \<in> set \<Pi>\<^sub>x. (\<Turnstile>\<^sub>H \<^bold>{ M\<^sub>2 \<^bold>\<and> \<^bold>\<not> M\<^sub>3 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>2 \<^bold>\<or> M\<^sub>3 \<^bold>})\<close> 
      by auto
    moreover have \<open>\<exists>b \<in> set \<Pi>\<^sub>x. \<turnstile>\<^sub>H \<^bold>{ M\<^sub>2 \<^bold>\<and> \<^bold>\<not> M\<^sub>3 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>3 \<^bold>}\<close>
    proof
      show \<open>pickUp_b1_c \<in> set \<Pi>\<^sub>x\<close> by simp
      show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>2 \<^bold>\<and> \<^bold>\<not> M\<^sub>3 \<^bold>} ((fst pickUp_b1_c) \<triangleright> do (snd pickUp_b1_c)) \<^bold>{ M\<^sub>3 \<^bold>}\<close>
      proof
        from eff show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>2 \<^bold>\<and> \<^bold>\<not> M\<^sub>3 \<^bold>\<and> fst pickUp_b1_c \<^bold>} (snd pickUp_b1_c) \<^bold>{ M\<^sub>3 \<^bold>}\<close> by simp
        show \<open>\<^bold>\<Turnstile>\<^sub>M (M\<^sub>2 \<^bold>\<and> \<^bold>\<not> M\<^sub>3 \<^bold>\<and> \<^bold>\<not> (fst pickUp_b1_c) \<^bold>\<longrightarrow> M\<^sub>3)\<close> by auto
      qed
    qed
    with bw4t.soundness\<^sub>H have \<open>\<exists>b \<in> set \<Pi>\<^sub>x. \<Turnstile>\<^sub>H \<^bold>{ M\<^sub>2 \<^bold>\<and> \<^bold>\<not> M\<^sub>3 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>3 \<^bold>}\<close> by auto
    ultimately show \<open>\<forall>s \<in> bw4t.Agent. \<forall>i. s, i \<Turnstile>\<^sub>T (M\<^sub>2\<^sup>T ensures M\<^sub>3\<^sup>T)\<close> using bw4t.ex_ensures by blast
  qed
  \<comment> \<open>Step 4\<close>
  moreover have \<open>M\<^sub>3\<^sup>T \<mapsto> M\<^sub>4\<^sup>T\<close>
  proof (rule bw4t.ensures)
    have eff: \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>3 \<^bold>\<and> \<^bold>\<not> M\<^sub>4 \<^bold>\<and> fst goTo_dropzone_c \<^bold>} goTo_dropzone \<^bold>{ M\<^sub>4 \<^bold>}\<close>
    proof (rule bw4t.rImp)
      have imp: \<open>\<turnstile>\<^sub>H \<^bold>{ B in_r1 \<^bold>\<and> B holding_b1 \<^bold>} goTo_dropzone \<^bold>{ B in_dropzone \<^bold>}\<close>
        by (rule bw4t.import) auto
      show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>3 \<^bold>} goTo_dropzone \<^bold>{ M\<^sub>4 \<^bold>}\<close>
      proof
        have \<open>goTo_dropzone \<in> bw4t.Cap\<close> unfolding bw4t.Cap_def by simp
        then show \<open>\<turnstile>\<^sub>H \<^bold>{ G collect_red \<^bold>} goTo_dropzone \<^bold>{ G collect_red \<^bold>}\<close>
          using G_collect_red_ht by simp
      next
        show \<open>\<turnstile>\<^sub>H \<^bold>{ B in_r1 \<^bold>\<and> B holding_b1 \<^bold>} goTo_dropzone \<^bold>{ B in_dropzone \<^bold>\<and> B holding_b1 \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ B in_r1 \<^bold>\<and> B holding_b1 \<^bold>\<and> B holding_b1 \<^bold>} goTo_dropzone \<^bold>{ B in_dropzone \<^bold>\<and> B holding_b1 \<^bold>}\<close>
          proof
            show \<open>\<turnstile>\<^sub>H \<^bold>{ B holding_b1 \<^bold>} goTo_dropzone \<^bold>{ B holding_b1 \<^bold>}\<close> using bw4t.import by simp
          next
            from imp show \<open>\<turnstile>\<^sub>H \<^bold>{ B in_r1 \<^bold>\<and> B holding_b1 \<^bold>} goTo_dropzone \<^bold>{ B in_dropzone \<^bold>}\<close> .
          qed
        qed auto
      qed
    qed auto
    have \<open>\<forall>b \<in> set \<Pi>\<^sub>x. (\<turnstile>\<^sub>H \<^bold>{ M\<^sub>3 \<^bold>\<and> \<^bold>\<not> M\<^sub>4 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>3 \<^bold>\<or> M\<^sub>4 \<^bold>})\<close>
    proof -
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>3 \<^bold>\<and> \<^bold>\<not> M\<^sub>4 \<^bold>} ((fst goTo_dropzone_c) \<triangleright> do goTo_dropzone) \<^bold>{ M\<^sub>3 \<^bold>\<or> M\<^sub>4 \<^bold>}\<close>
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>3 \<^bold>\<and> \<^bold>\<not> M\<^sub>4 \<^bold>\<and> fst goTo_dropzone_c \<^bold>} goTo_dropzone \<^bold>{ M\<^sub>3 \<^bold>\<or> M\<^sub>4 \<^bold>}\<close>
        proof (rule bw4t.rImp)
          from eff show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>3 \<^bold>\<and> \<^bold>\<not> M\<^sub>4 \<^bold>\<and> fst goTo_dropzone_c \<^bold>} goTo_dropzone \<^bold>{ M\<^sub>4 \<^bold>}\<close> .
        qed auto
      qed auto
      moreover 
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>3 \<^bold>\<and> \<^bold>\<not> M\<^sub>4 \<^bold>} ((fst goTo_r1_c) \<triangleright> do goTo_r1) \<^bold>{ M\<^sub>3 \<^bold>\<or> M\<^sub>4 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>}\<close>
          proof (rule bw4t.inf)
            obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close> by simp
            ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
              using bw4t.not_enabled_ht_spec by blast
            moreover have \<open>?b = basic (bcap ?b)\<close> by simp
            ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
          qed
        qed auto
      qed auto
      moreover 
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>3 \<^bold>\<and> \<^bold>\<not> M\<^sub>4 \<^bold>} ((fst goToBlock_b1_c) \<triangleright> do goToBlock_b1) \<^bold>{ M\<^sub>3 \<^bold>\<or> M\<^sub>4 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>}\<close>
          proof (rule bw4t.inf)
            obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close> by simp
            ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
              using bw4t.not_enabled_ht_spec by blast
            moreover have \<open>?b = basic (bcap ?b)\<close> by simp
            ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
          qed
        qed auto
      qed auto
      moreover 
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>3 \<^bold>\<and> \<^bold>\<not> M\<^sub>4 \<^bold>} ((fst pickUp_b1_c) \<triangleright> do pickUp_b1) \<^bold>{ M\<^sub>3 \<^bold>\<or> M\<^sub>4 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>}\<close>
          proof (rule bw4t.inf)
            obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close> by simp
            ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
              using bw4t.not_enabled_ht_spec by blast
            moreover have \<open>?b = basic (bcap ?b)\<close> by simp
            ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
          qed
        qed auto
      qed auto
      moreover 
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>3 \<^bold>\<and> \<^bold>\<not> M\<^sub>4 \<^bold>} ((fst putDown_c) \<triangleright> do putDown) \<^bold>{ M\<^sub>3 \<^bold>\<or> M\<^sub>4 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>}\<close>
          proof (rule bw4t.inf)
            obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close>
            proof
              fix M
              show \<open>bw4t.mst_reachable_basic M \<longrightarrow> M \<Turnstile>\<^sub>M ?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>\<close>
              proof
                assume \<open>bw4t.mst_reachable_basic M\<close>
                with bw4t.mst_reachable_basic_is_mst have \<open>\<nabla> M\<close> by simp
                moreover { 
                  have \<open>M\<^sub>0\<^sub>x \<Turnstile>\<^sub>M B (invariants!1)\<close> by simp
                  moreover have \<open>\<forall>a\<in>bw4t.Cap. \<turnstile>\<^sub>H \<^bold>{ B (invariants!1) \<^bold>} a \<^bold>{ B (invariants!1) \<^bold>}\<close> 
                    using invariants_ht by simp
                  ultimately have \<open>\<^bold>\<Turnstile>\<^sub>M (B (invariants!1))\<close> 
                    using bw4t.mst_basic_trace_ht_invariant bw4t.soundness\<^sub>H by blast
                }
                ultimately have \<open>M \<Turnstile>\<^sub>M B (invariants!1)\<close> using \<open>bw4t.mst_reachable_basic M\<close> by blast
                then have \<open>M \<Turnstile>\<^sub>M B in_r1 \<^bold>\<longrightarrow> B (\<^bold>\<not> in_dropzone)\<close> by (cases M) auto
                with is_mst_negB have \<open>M \<Turnstile>\<^sub>M B in_r1 \<^bold>\<longrightarrow> \<^bold>\<not> (B in_dropzone)\<close> using \<open>\<nabla> M\<close> by simp
                have \<open>M \<Turnstile>\<^sub>M ?M\<^sub>L \<longrightarrow> M \<Turnstile>\<^sub>M \<^bold>\<not> ?\<psi>\<close>
                proof
                  assume \<open>M \<Turnstile>\<^sub>M ?M\<^sub>L\<close>
                  moreover from this have \<open>M \<Turnstile>\<^sub>M \<^bold>\<not> (B in_dropzone)\<close> 
                    using \<open>M \<Turnstile>\<^sub>M B in_r1 \<^bold>\<longrightarrow> \<^bold>\<not> (B in_dropzone)\<close> by simp
                  ultimately show \<open>M \<Turnstile>\<^sub>M \<^bold>\<not> ?\<psi>\<close> by simp
                qed
                then show \<open>M \<Turnstile>\<^sub>M ?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>\<close> by simp
              qed
            qed
            ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
              using bw4t.not_enabled_ht_spec by blast
            moreover have \<open>?b = basic (bcap ?b)\<close> by simp
            ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
          qed
        qed auto
      qed auto
      ultimately show ?thesis by simp
    qed
    with bw4t.soundness\<^sub>H have \<open>\<forall>b \<in> set \<Pi>\<^sub>x. (\<Turnstile>\<^sub>H \<^bold>{ M\<^sub>3 \<^bold>\<and> \<^bold>\<not> M\<^sub>4 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>3 \<^bold>\<or> M\<^sub>4 \<^bold>})\<close> 
      by auto
    moreover have \<open>\<exists>b \<in> set \<Pi>\<^sub>x. \<turnstile>\<^sub>H \<^bold>{ M\<^sub>3 \<^bold>\<and> \<^bold>\<not> M\<^sub>4 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>4 \<^bold>}\<close>
    proof
      show \<open>goTo_dropzone_c \<in> set \<Pi>\<^sub>x\<close> by simp
      show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>3 \<^bold>\<and> \<^bold>\<not> M\<^sub>4 \<^bold>} ((fst goTo_dropzone_c) \<triangleright> do (snd goTo_dropzone_c)) \<^bold>{ M\<^sub>4 \<^bold>}\<close>
      proof
        from eff show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>3 \<^bold>\<and> \<^bold>\<not> M\<^sub>4 \<^bold>\<and> fst goTo_dropzone_c \<^bold>} (snd goTo_dropzone_c) \<^bold>{ M\<^sub>4 \<^bold>}\<close> by simp
        show \<open>\<^bold>\<Turnstile>\<^sub>M (M\<^sub>3 \<^bold>\<and> \<^bold>\<not> M\<^sub>4 \<^bold>\<and> \<^bold>\<not> (fst goTo_dropzone_c) \<^bold>\<longrightarrow> M\<^sub>4)\<close> by auto
      qed
    qed
    with bw4t.soundness\<^sub>H have \<open>\<exists>b \<in> set \<Pi>\<^sub>x. \<Turnstile>\<^sub>H \<^bold>{ M\<^sub>3 \<^bold>\<and> \<^bold>\<not> M\<^sub>4 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>4 \<^bold>}\<close> by auto
    ultimately show \<open>\<forall>s \<in> bw4t.Agent. \<forall>i. s, i \<Turnstile>\<^sub>T (M\<^sub>3\<^sup>T ensures M\<^sub>4\<^sup>T)\<close> using bw4t.ex_ensures by blast
  qed
  \<comment> \<open>Step 5\<close>
  moreover have \<open>M\<^sub>4\<^sup>T \<mapsto> M\<^sub>5\<^sup>T\<close>
  proof (rule bw4t.ensures)
    have eff: \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>4 \<^bold>\<and> \<^bold>\<not> M\<^sub>5 \<^bold>\<and> fst putDown_c \<^bold>} putDown \<^bold>{ M\<^sub>5 \<^bold>}\<close>
    proof (rule bw4t.rImp)
      have imp: \<open>\<turnstile>\<^sub>H \<^bold>{ B in_dropzone \<^bold>\<and> B holding_b1 \<^bold>} putDown \<^bold>{ B collect_red \<^bold>}\<close>
        by (rule bw4t.import) auto
      show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>4 \<^bold>} putDown \<^bold>{ M\<^sub>5 \<^bold>}\<close>
      proof (rule bw4t.rImp)
        from imp show \<open>\<turnstile>\<^sub>H \<^bold>{ B in_dropzone \<^bold>\<and> B holding_b1 \<^bold>} putDown \<^bold>{ B collect_red \<^bold>}\<close> .
      qed auto
    qed auto
    have \<open>\<forall>b \<in> set \<Pi>\<^sub>x. (\<turnstile>\<^sub>H \<^bold>{ M\<^sub>4 \<^bold>\<and> \<^bold>\<not> M\<^sub>5 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>4 \<^bold>\<or> M\<^sub>5 \<^bold>})\<close>
    proof -
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>4 \<^bold>\<and> \<^bold>\<not> M\<^sub>5 \<^bold>} ((fst goTo_dropzone_c) \<triangleright> do goTo_dropzone) \<^bold>{ M\<^sub>4 \<^bold>\<or> M\<^sub>5 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>}\<close>
          proof (rule bw4t.inf)
            obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close>
            proof
              fix M
              show \<open>bw4t.mst_reachable_basic M \<longrightarrow> M \<Turnstile>\<^sub>M ?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>\<close>
              proof
                assume \<open>bw4t.mst_reachable_basic M\<close>
                with bw4t.mst_reachable_basic_is_mst have \<open>\<nabla> M\<close> by simp
                moreover { 
                  have \<open>M\<^sub>0\<^sub>x \<Turnstile>\<^sub>M B (invariants!0)\<close> by simp
                  moreover have \<open>\<forall>a\<in>bw4t.Cap. \<turnstile>\<^sub>H \<^bold>{ B (invariants!0) \<^bold>} a \<^bold>{ B (invariants!0) \<^bold>}\<close> 
                    using invariants_ht by simp
                  ultimately have \<open>\<^bold>\<Turnstile>\<^sub>M (B (invariants!0))\<close> 
                    using bw4t.mst_basic_trace_ht_invariant bw4t.soundness\<^sub>H by blast
                }
                ultimately have \<open>M \<Turnstile>\<^sub>M B (invariants!0)\<close> using \<open>bw4t.mst_reachable_basic M\<close> by blast
                then have \<open>M \<Turnstile>\<^sub>M B in_dropzone \<^bold>\<longrightarrow> B (\<^bold>\<not> in_r1)\<close> by (cases M) auto
                with is_mst_negB have \<open>M \<Turnstile>\<^sub>M B in_dropzone \<^bold>\<longrightarrow> \<^bold>\<not> (B in_r1)\<close> using \<open>\<nabla> M\<close> by simp
                have \<open>M \<Turnstile>\<^sub>M ?M\<^sub>L \<longrightarrow> M \<Turnstile>\<^sub>M \<^bold>\<not> ?\<psi>\<close>
                proof
                  assume \<open>M \<Turnstile>\<^sub>M ?M\<^sub>L\<close>
                  moreover from this have \<open>M \<Turnstile>\<^sub>M \<^bold>\<not> (B in_r1)\<close> 
                    using \<open>M \<Turnstile>\<^sub>M B in_dropzone \<^bold>\<longrightarrow> \<^bold>\<not> (B in_r1)\<close> by simp
                  ultimately show \<open>M \<Turnstile>\<^sub>M \<^bold>\<not> ?\<psi>\<close> by simp
                qed
                then show \<open>M \<Turnstile>\<^sub>M ?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>\<close> by simp
              qed
            qed
            ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
              using bw4t.not_enabled_ht_spec by blast
            moreover have \<open>?b = basic (bcap ?b)\<close> by simp
            ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
          qed
        qed auto
      qed auto
      moreover 
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>4 \<^bold>\<and> \<^bold>\<not> M\<^sub>5 \<^bold>} ((fst goTo_r1_c) \<triangleright> do goTo_r1) \<^bold>{ M\<^sub>4 \<^bold>\<or> M\<^sub>5 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>}\<close>
          proof (rule bw4t.inf)
            obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close> by simp
            ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
              using bw4t.not_enabled_ht_spec by blast
            moreover have \<open>?b = basic (bcap ?b)\<close> by simp
            ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
          qed
        qed auto
      qed auto
      moreover 
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>4 \<^bold>\<and> \<^bold>\<not> M\<^sub>5 \<^bold>} ((fst goToBlock_b1_c) \<triangleright> do goToBlock_b1) \<^bold>{ M\<^sub>4 \<^bold>\<or> M\<^sub>5 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>}\<close>
          proof (rule bw4t.inf)
            obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close> by simp
            ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
              using bw4t.not_enabled_ht_spec by blast
            moreover have \<open>?b = basic (bcap ?b)\<close> by simp
            ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
          qed
        qed auto
      qed auto
      moreover 
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>4 \<^bold>\<and> \<^bold>\<not> M\<^sub>5 \<^bold>} ((fst pickUp_b1_c) \<triangleright> do pickUp_b1) \<^bold>{ M\<^sub>4 \<^bold>\<or> M\<^sub>5 \<^bold>}\<close>
       (is \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>} (?\<psi> \<triangleright> do ?b) \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>)
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>\<and> \<^bold>\<not> ?M\<^sub>R \<^bold>\<and> ?\<psi> \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>\<or> ?M\<^sub>R \<^bold>}\<close>
        proof (rule bw4t.rImp)
          show \<open>\<turnstile>\<^sub>H \<^bold>{ ?M\<^sub>L \<^bold>} ?b \<^bold>{ ?M\<^sub>L \<^bold>}\<close>
          proof (rule bw4t.inf)
            obtain hts where \<open>(bcap ?b, ?\<psi>, hts) \<in> set S\<^sub>x\<close> by simp
            moreover have \<open>\<^bold>\<Turnstile>\<^sub>M (?M\<^sub>L \<^bold>\<longrightarrow> \<^bold>\<not> ?\<psi>)\<close> by simp
            ultimately have \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic (bcap ?b))))\<close>
              using bw4t.not_enabled_ht_spec by blast
            moreover have \<open>?b = basic (bcap ?b)\<close> by simp
            ultimately show \<open>\<^bold>\<Turnstile>\<^sub>E (?M\<^sub>L\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ?b))\<close> by simp
          qed
        qed auto
      qed auto
      moreover 
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>4 \<^bold>\<and> \<^bold>\<not> M\<^sub>5 \<^bold>} ((fst putDown_c) \<triangleright> do putDown) \<^bold>{ M\<^sub>4 \<^bold>\<or> M\<^sub>5 \<^bold>}\<close>
      proof
        show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>4 \<^bold>\<and> \<^bold>\<not> M\<^sub>5 \<^bold>\<and> fst putDown_c \<^bold>} putDown \<^bold>{ M\<^sub>4 \<^bold>\<or> M\<^sub>5 \<^bold>}\<close>
        proof (rule bw4t.rImp)
          from eff show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>4 \<^bold>\<and> \<^bold>\<not> M\<^sub>5 \<^bold>\<and> fst putDown_c \<^bold>} putDown \<^bold>{ M\<^sub>5 \<^bold>}\<close> .
        qed auto
      qed auto
      ultimately show ?thesis by simp
    qed
    with bw4t.soundness\<^sub>H have \<open>\<forall>b \<in> set \<Pi>\<^sub>x. (\<Turnstile>\<^sub>H \<^bold>{ M\<^sub>4 \<^bold>\<and> \<^bold>\<not> M\<^sub>5 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>4 \<^bold>\<or> M\<^sub>5 \<^bold>})\<close> 
      by auto
    moreover have \<open>\<exists>b \<in> set \<Pi>\<^sub>x. \<turnstile>\<^sub>H \<^bold>{ M\<^sub>4 \<^bold>\<and> \<^bold>\<not> M\<^sub>5 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>5 \<^bold>}\<close>
    proof
      show \<open>putDown_c \<in> set \<Pi>\<^sub>x\<close> by simp
      show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>4 \<^bold>\<and> \<^bold>\<not> M\<^sub>5 \<^bold>} ((fst putDown_c) \<triangleright> do (snd putDown_c)) \<^bold>{ M\<^sub>5 \<^bold>}\<close>
      proof
        from eff show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>4 \<^bold>\<and> \<^bold>\<not> M\<^sub>5 \<^bold>\<and> fst putDown_c \<^bold>} (snd putDown_c) \<^bold>{ M\<^sub>5 \<^bold>}\<close> by simp
        show \<open>\<^bold>\<Turnstile>\<^sub>M (M\<^sub>4 \<^bold>\<and> \<^bold>\<not> M\<^sub>5 \<^bold>\<and> \<^bold>\<not> (fst putDown_c) \<^bold>\<longrightarrow> M\<^sub>5)\<close> by auto
      qed
    qed
    with bw4t.soundness\<^sub>H have \<open>\<exists>b \<in> set \<Pi>\<^sub>x. \<Turnstile>\<^sub>H \<^bold>{ M\<^sub>4 \<^bold>\<and> \<^bold>\<not> M\<^sub>5 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>5 \<^bold>}\<close> by auto
    ultimately show \<open>\<forall>s \<in> bw4t.Agent. \<forall>i. s, i \<Turnstile>\<^sub>T (M\<^sub>4\<^sup>T ensures M\<^sub>5\<^sup>T)\<close> using bw4t.ex_ensures by blast
  qed    
  ultimately show ?thesis using bw4t.imp by blast
qed

lemma \<open>s \<in> bw4t.Agent \<Longrightarrow> s, i \<Turnstile>\<^sub>T ((M\<^sub>0\<^sup>T) \<longrightarrow>\<^sub>T \<diamondop> (M\<^sub>5\<^sup>T))\<close>
  using bw4t_lt bw4t.leads_to_temp by simp

end