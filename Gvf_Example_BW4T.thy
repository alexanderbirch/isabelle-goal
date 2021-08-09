theory Gvf_Example_BW4T imports Gvf_Temporal_Logic begin

section \<open>Example BW4T single agent specification.\<close>

subsection \<open>Agent specification setup\<close>

\<comment> \<open>Propositions.\<close>
abbreviation \<open>in_dropzone::\<Phi>\<^sub>L \<equiv> \<Phi>\<^sub>P.Atom 0\<close>
abbreviation \<open>in_r\<^sub>1::\<Phi>\<^sub>L \<equiv> \<Phi>\<^sub>P.Atom 1\<close>
abbreviation \<open>collect_red::\<Phi>\<^sub>L \<equiv> \<Phi>\<^sub>P.Atom 2\<close>
abbreviation \<open>holding_b\<^sub>1::\<Phi>\<^sub>L \<equiv> \<Phi>\<^sub>P.Atom 3\<close>
abbreviation \<open>atBlock_b\<^sub>1::\<Phi>\<^sub>L \<equiv> \<Phi>\<^sub>P.Atom 4\<close>

\<comment> \<open>Actions.\<close>
abbreviation \<open>goTo_dropzone \<equiv> basic 0\<close>
abbreviation \<open>goTo_r\<^sub>1::cap \<equiv> basic 1\<close>
abbreviation \<open>goToBlock_b\<^sub>1::cap \<equiv> basic 2\<close>
abbreviation \<open>pickUp_b\<^sub>1::cap \<equiv> basic 3\<close>
abbreviation \<open>putDown::cap \<equiv> basic 4\<close>

\<comment> \<open>Specification of the program.\<close>
abbreviation 
  \<open>\<Pi>\<^sub>x \<equiv> [ 
    (B in_r\<^sub>1 \<^bold>\<and> B holding_b\<^sub>1) \<triangleright> do goTo_dropzone,
    (B (\<^bold>\<not> in_r\<^sub>1) \<^bold>\<and> B (\<^bold>\<not> holding_b\<^sub>1) ) \<triangleright> do goTo_r\<^sub>1,
    (B in_r\<^sub>1 \<^bold>\<and> B (\<^bold>\<not> holding_b\<^sub>1) \<^bold>\<and> B (\<^bold>\<not> atBlock_b\<^sub>1)) \<triangleright> do goToBlock_b\<^sub>1,
    (B atBlock_b\<^sub>1 \<^bold>\<and> B (\<^bold>\<not> holding_b\<^sub>1)) \<triangleright> do pickUp_b\<^sub>1,
    (B holding_b\<^sub>1 \<^bold>\<and> B in_dropzone) \<triangleright> do putDown
  ]\<close>

abbreviation 
  \<open>M\<^sub>0\<^sub>x \<equiv> ( { in_dropzone, \<^bold>\<not> in_r\<^sub>1, \<^bold>\<not> holding_b\<^sub>1, \<^bold>\<not> atBlock_b\<^sub>1 }, { collect_red } )\<close>

abbreviation 
  \<open>S\<^sub>x' \<equiv> [
    (0, fst (\<Pi>\<^sub>x!0), 
      [
        \<^bold>{ B in_r\<^sub>1 \<^bold>\<and> B (\<^bold>\<not> in_dropzone) \<^bold>\<and> B holding_b\<^sub>1 \<^bold>} goTo_dropzone \<^bold>{ B (\<^bold>\<not> in_r\<^sub>1) \<^bold>\<and> B in_dropzone \<^bold>}
      ]),

    (1, fst (\<Pi>\<^sub>x!1), 
      [
        \<^bold>{ B (\<^bold>\<not> in_r\<^sub>1) \<^bold>\<and> B in_dropzone \<^bold>\<and> B (\<^bold>\<not> holding_b\<^sub>1) \<^bold>} goTo_r\<^sub>1 \<^bold>{ B in_r\<^sub>1 \<^bold>\<and> B (\<^bold>\<not> in_dropzone) \<^bold>}
      ]),

    (2, fst (\<Pi>\<^sub>x!2), 
      [
        \<^bold>{ B in_r\<^sub>1 \<^bold>\<and> B (\<^bold>\<not> atBlock_b\<^sub>1) \<^bold>\<and> B (\<^bold>\<not> holding_b\<^sub>1) \<^bold>} goToBlock_b\<^sub>1 \<^bold>{ B atBlock_b\<^sub>1 \<^bold>}
      ]),

    (3, fst (\<Pi>\<^sub>x!3), 
      [
        \<^bold>{ B atBlock_b\<^sub>1 \<^bold>\<and> B (\<^bold>\<not> holding_b\<^sub>1) \<^bold>} pickUp_b\<^sub>1 \<^bold>{ B holding_b\<^sub>1 \<^bold>}
      ]),

    (4, fst (\<Pi>\<^sub>x!4), 
      [
        \<^bold>{ B in_dropzone \<^bold>\<and> B holding_b\<^sub>1 \<^bold>} putDown \<^bold>{ B collect_red \<^bold>}
      ])
  ]\<close>


abbreviation 
  \<open>inv\<^sub>x \<equiv> [
    B in_dropzone \<^bold>\<longrightarrow> B (\<^bold>\<not> in_r\<^sub>1),
    B in_r\<^sub>1 \<^bold>\<longrightarrow> B (\<^bold>\<not> in_dropzone)
  ]\<close>

abbreviation
  \<open>S\<^sub>x \<equiv> add_invariants S\<^sub>x' inv\<^sub>x\<close>

\<comment> \<open>Prove that the example is an instance of the single agent program locale.\<close>
\<comment> \<open>We use a trick where \<T> is simply some function that complies to our definition due to Hilbert's epsilon operator i.e. the axiom of choice.\<close>
global_interpretation bw4t: single_agent_program \<open>SOME \<T>. complies S\<^sub>x \<T>\<close> \<open>set \<Pi>\<^sub>x\<close> M\<^sub>0\<^sub>x S\<^sub>x
  defines semantics\<^sub>H (\<open>\<Turnstile>\<^sub>H\<close>) = bw4t.semantics\<^sub>H
      and derive\<^sub>H (\<open>\<turnstile>\<^sub>H\<close>) = bw4t.derive\<^sub>H
      and leads_to (infix \<open>\<mapsto>\<close> 55) = bw4t.leads_to
proof -
  let ?\<T> = \<open>SOME \<T>. complies S\<^sub>x \<T>\<close>
  have \<open>\<nabla> M\<^sub>0\<^sub>x\<close> unfolding is_mental_state_def by fastforce
  moreover have \<open>satisfiable S\<^sub>x\<close> unfolding satisfiable_def
  proof
    fix M
    let ?sat = \<open>\<lambda>s \<Sigma>. (M \<Turnstile>\<^sub>M fst (snd s) \<longrightarrow> satisfiable_base M (snd (snd s)) \<Sigma>) \<and> (M \<Turnstile>\<^sub>M \<^bold>\<not> (fst (snd s)) \<longrightarrow> (\<forall>ht \<in> set (snd (snd s)). M \<Turnstile>\<^sub>M pre ht \<longrightarrow> M \<Turnstile>\<^sub>M post ht))\<close>
    \<comment> \<open>0\<close>
    have \<open>?sat (S\<^sub>x!0) {\<^bold>\<not> in_r\<^sub>1 \<^bold>\<and> in_dropzone}\<close>
      unfolding satisfiable_base_def using bel_dist_conj by auto
    then have \<open>satisfiable_elem M (S\<^sub>x!0)\<close> using satisfiable_elem_def by auto
    \<comment> \<open>1\<close>
    moreover have \<open>?sat (S\<^sub>x!1) {in_r\<^sub>1 \<^bold>\<and> \<^bold>\<not> in_dropzone}\<close>
      unfolding satisfiable_base_def using bel_dist_conj by auto
    then have \<open>satisfiable_elem M (S\<^sub>x!1)\<close> using satisfiable_elem_def by auto
    \<comment> \<open>2\<close>
    moreover have \<open>?sat (S\<^sub>x!2) {atBlock_b\<^sub>1}\<close>
      unfolding satisfiable_base_def using bel_dist_conj by auto
    then have \<open>satisfiable_elem M (S\<^sub>x!2)\<close> using satisfiable_elem_def by auto
    \<comment> \<open>3\<close>
    moreover have \<open>?sat (S\<^sub>x!3) {holding_b\<^sub>1}\<close> 
      unfolding satisfiable_base_def using bel_dist_conj by auto
    then have \<open>satisfiable_elem M (S\<^sub>x!3)\<close> using satisfiable_elem_def by auto
    \<comment> \<open>4\<close>
    moreover have \<open>?sat (S\<^sub>x!4) {collect_red}\<close> 
      unfolding satisfiable_base_def using bel_dist_conj by auto
    then have \<open>satisfiable_elem M (S\<^sub>x!4)\<close> using satisfiable_elem_def by auto
    \<comment> \<open>Combine\<close>
    ultimately show \<open>\<forall>s\<in>set S\<^sub>x. satisfiable_elem M s\<close> by simp
  qed
  then have \<open>is_ht_specification S\<^sub>x\<close> unfolding is_ht_specification_def by simp
  moreover have \<open>\<forall>a. (\<exists>\<phi>. (\<phi>, basic a) \<in> set \<Pi>\<^sub>x) = (a \<in> set (map fst S\<^sub>x))\<close> by fastforce
  ultimately show \<open>single_agent_program ?\<T> (set \<Pi>\<^sub>x) M\<^sub>0\<^sub>x S\<^sub>x\<close> using is_ht_spec_single_agent_program by simp
qed

subsection \<open>Correctness proof\<close>

abbreviation \<open>M\<^sub>0 \<equiv> B in_dropzone \<^bold>\<and> G collect_red\<close>
abbreviation \<open>M\<^sub>1 \<equiv> B in_r\<^sub>1 \<^bold>\<and> G collect_red\<close>
abbreviation \<open>M\<^sub>2 \<equiv> B in_r\<^sub>1 \<^bold>\<and> B atBlock_b\<^sub>1 \<^bold>\<and> G collect_red\<close>
abbreviation \<open>M\<^sub>3 \<equiv> B in_r\<^sub>1 \<^bold>\<and> B holding_b\<^sub>1 \<^bold>\<and> G collect_red\<close>
abbreviation \<open>M\<^sub>4 \<equiv> B in_dropzone \<^bold>\<and> B holding_b\<^sub>1 \<^bold>\<and> G collect_red\<close>
abbreviation \<open>M\<^sub>5 \<equiv> B collect_red\<close>

lemma bw4t_lt: \<open>M\<^sub>0\<^sup>T \<mapsto> M\<^sub>5\<^sup>T\<close>
proof -
  have \<open>M\<^sub>0\<^sup>T \<mapsto> M\<^sub>1\<^sup>T\<close>
  proof -
    have \<open>\<forall>b \<in> set \<Pi>\<^sub>x. \<Turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>0 \<^bold>\<or> M\<^sub>1 \<^bold>}\<close> sorry
    moreover have \<open>\<exists>b \<in> set \<Pi>\<^sub>x. \<Turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ M\<^sub>1 \<^bold>}\<close>
    proof -
      let ?b = \<open>\<Pi>\<^sub>x!0\<close>
      have \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst ?b) \<triangleright> do (snd ?b)) \<^bold>{ M\<^sub>1 \<^bold>}\<close>
      proof 
        show \<open>\<turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>\<and> fst ?b \<^bold>} (snd ?b) \<^bold>{ M\<^sub>1 \<^bold>}\<close> sorry
        show \<open>\<turnstile>\<^sub>M M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>\<and> \<^bold>\<not> (fst ?b) \<^bold>\<longrightarrow> M\<^sub>1\<close> 
        proof 
          have \<open>\<Turnstile>\<^sub>P (M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>\<and> \<^bold>\<not> (fst ?b) \<^bold>\<longrightarrow> M\<^sub>1)\<close> try
          show \<open>\<turnstile>\<^sub>P M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>\<and> \<^bold>\<not> (fst ?b) \<^bold>\<longrightarrow> M\<^sub>1\<close> sorry
        qed
      qed
      then have \<open>\<Turnstile>\<^sub>H \<^bold>{ M\<^sub>0 \<^bold>\<and> \<^bold>\<not> M\<^sub>1 \<^bold>} ((fst ?b) \<triangleright> do (snd ?b)) \<^bold>{ M\<^sub>1 \<^bold>}\<close> using bw4t.soundness\<^sub>H by blast
      then show ?thesis by auto
    qed
    ultimately have \<open>\<forall>s \<in> bw4t.Agent. \<forall>i. s, i \<Turnstile>\<^sub>T (M\<^sub>0\<^sup>T ensures M\<^sub>1\<^sup>T)\<close> using bw4t.ex_ensures by blast
    then show ?thesis using bw4t.ensures by simp
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

lemma \<open>s \<in> bw4t.Agent \<Longrightarrow> s, i \<Turnstile>\<^sub>T (M\<^sub>0\<^sup>T \<longrightarrow>\<^sub>T \<diamondop> (M\<^sub>5\<^sup>T))\<close>
  using bw4t_lt bw4t.leads_to_temp by simp

end