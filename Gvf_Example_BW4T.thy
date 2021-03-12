theory Gvf_Example_BW4T imports Gvf_Agent_Specification begin

section \<open>Example BW4T single agent specification.\<close>

\<comment> \<open>Proof of concept. Only part of the specification is included so far and proofs are missing.
   Mainly due to the temporal logic layer still missing.\<close>

\<comment> \<open>Set up agent specification-\<close>
\<comment> \<open>Propositions:\<close>
abbreviation \<open>in_dropzone::\<Phi>\<^sub>L \<equiv> Atom 0\<close>
abbreviation \<open>in_room::\<Phi>\<^sub>L \<equiv> Atom 1\<close>
abbreviation \<open>collect_red::\<Phi>\<^sub>L \<equiv> Atom 2\<close>

\<comment> \<open>Actions:\<close>
abbreviation \<open>goto_dropzone_Bcap \<equiv> 0::nat\<close>
abbreviation \<open>goto_dropzone \<equiv> basic goto_dropzone_Bcap\<close>

abbreviation \<open>goto_room_Bcap \<equiv> 1::nat\<close>
abbreviation \<open>goto_room::cap \<equiv> basic goto_room_Bcap\<close>

\<comment> \<open>Specification of the program:\<close>
abbreviation \<open>\<Pi>\<^sub>x \<equiv> { (B in_dropzone) \<triangleright> do goto_room }\<close>
abbreviation \<open>M\<^sub>0\<^sub>x \<equiv> ( { in_dropzone }, { collect_red } )\<close>
abbreviation \<open>S\<^sub>x \<equiv> [(goto_room_Bcap, \<top>\<^sub>M, [\<^bold>{ B in_dropzone \<^bold>} goto_room \<^bold>{ B in_room \<^bold>}])]\<close>

\<comment> \<open>Prove that the example is an instance of the single agent program locale.\<close>
\<comment> \<open>We use a trick where \<T> is simply some function that complies to our definition due to Hilbert's epsilon operator i.e. the axiom of choice.\<close>
interpretation example: single_agent_program \<open>SOME \<T>. complies S\<^sub>x \<T>\<close> \<Pi>\<^sub>x M\<^sub>0\<^sub>x S\<^sub>x
proof -
  let ?\<T> = \<open>SOME \<T>. complies S\<^sub>x \<T>\<close>
  (* This could be harder to proof than suggested since S\<^sub>x here has one element *)
  have satisfiable: \<open>satisfiable S\<^sub>x\<close> unfolding satisfiable_def 
  proof 
    fix M
    let ?n = \<open>goto_room_Bcap\<close> and ?\<Phi> = \<open>\<top>\<^sub>M\<close> and ?hts = \<open>[\<^bold>{ B in_dropzone \<^bold>} goto_room \<^bold>{ B in_room \<^bold>}]\<close>
    let ?sat_hts = \<open>{ht \<in> set ?hts. M \<Turnstile>\<^sub>M pre ht }\<close>
    have \<open>\<exists>M'. M' \<Turnstile>\<^sub>M (B in_room) \<and> \<not> fst M' \<Turnstile>\<^sub>L \<bottom>\<^sub>L\<close> 
    proof -
      have \<open>({in_room}, {}) \<Turnstile>\<^sub>M B in_room\<close> by simp
      moreover have \<open>\<not> fst ({in_room}, {}) \<Turnstile>\<^sub>L \<bottom>\<^sub>L\<close> by auto
      ultimately show ?thesis by blast
    qed
    then have \<open>(M \<Turnstile>\<^sub>M ?\<Phi> \<longrightarrow> (\<exists>\<Sigma>'. (\<not> fst M \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> \<not> \<Sigma>' \<Turnstile>\<^sub>L \<bottom>\<^sub>L) \<and> (let \<Gamma>' = snd M - {\<psi> \<in> snd M. \<Sigma>' \<Turnstile>\<^sub>L \<psi>} in (\<forall>ht \<in> ?sat_hts. (\<Sigma>', \<Gamma>') \<Turnstile>\<^sub>M post ht)))) \<and> (M \<Turnstile>\<^sub>M \<^bold>\<not> ?\<Phi> \<longrightarrow> (\<forall>ht\<in>?sat_hts. M \<Turnstile>\<^sub>M post ht))\<close> by auto
    then show 
      \<open>\<forall>s\<in>set S\<^sub>x. let (_, \<Phi>, hts) = s; sat_hts = {ht \<in> set hts. M \<Turnstile>\<^sub>M pre ht} in 
        (M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> (\<exists>M'. (\<not> fst M \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> \<not> fst M' \<Turnstile>\<^sub>L \<bottom>\<^sub>L) \<and> (snd M' = snd M - {\<psi> \<in> snd M. fst M' \<Turnstile>\<^sub>L \<psi>}) \<and> (\<forall>ht \<in> sat_hts. M' \<Turnstile>\<^sub>M post ht))) \<and> 
        (M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> (\<forall>ht\<in>sat_hts. M \<Turnstile>\<^sub>M post ht))\<close>
      by simp
  qed
  then have s: \<open>is_ht_specification S\<^sub>x\<close> unfolding is_ht_specification_def by simp
  then have c: \<open>complies S\<^sub>x ?\<T>\<close> using model_exists by (simp add: someI2_ex)
  show \<open>single_agent_program ?\<T> \<Pi>\<^sub>x M\<^sub>0\<^sub>x S\<^sub>x\<close>
  proof
    have \<open>\<nabla> M\<^sub>0\<^sub>x\<close>
    proof - 
      have \<open>\<not> {in_dropzone} \<Turnstile>\<^sub>L \<bottom>\<^sub>L\<close> by auto
      moreover have \<open>in_dropzone \<noteq> collect_red\<close> by simp
      with neq_atom_not_entail have \<open>\<not> {in_dropzone} \<Turnstile>\<^sub>L collect_red\<close> by metis
      moreover have \<open>\<not> {} \<Turnstile>\<^sub>L \<^bold>\<not> in_dropzone\<close> by auto
      ultimately show ?thesis unfolding is_mental_state_def by auto
    qed
    then show \<open>\<Pi>\<^sub>x \<noteq> {} \<and> \<nabla> M\<^sub>0\<^sub>x\<close> by simp
  next
    fix \<Sigma> \<Gamma> n
    show \<open>(\<exists>\<phi>. (\<phi>, basic n) \<in> \<Pi>\<^sub>x) \<longrightarrow> \<not> \<Sigma> \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> ?\<T> n (\<Sigma>, \<Gamma>) \<noteq> None \<longrightarrow> \<not> the (?\<T> n (\<Sigma>, \<Gamma>)) \<Turnstile>\<^sub>L \<bottom>\<^sub>L\<close> 
    proof
      assume \<open>\<exists>\<phi>. (\<phi>, basic n) \<in> \<Pi>\<^sub>x\<close>
      from c have \<open>\<forall>s\<in>set S\<^sub>x. complies_hts s ?\<T>\<close> unfolding complies_def by simp
      then have \<open>\<forall>s\<in>set S\<^sub>x. \<forall>ht\<in>set (snd (snd s)). complies_ht (\<Sigma>, \<Gamma>) ?\<T> (fst (snd s)) (the (htb_basic_unpack ht))\<close> unfolding complies_hts_def by blast
      moreover have \<open>\<forall>s\<in>set S\<^sub>x. \<forall>ht\<in>set (snd (snd s)). fst s = (fst (snd ((the (htb_basic_unpack ht)))))\<close> by simp
      ultimately have \<open>\<forall>s\<in>set S\<^sub>x. \<forall>ht\<in>set (snd (snd s)). \<not> \<Sigma> \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> ?\<T> (fst s) (\<Sigma>, \<Gamma>) \<noteq> None \<longrightarrow> \<not>the (?\<T> (fst s) (\<Sigma>, \<Gamma>)) \<Turnstile>\<^sub>L \<bottom>\<^sub>L\<close> by simp
      then have \<open>\<forall>s\<in>set S\<^sub>x. \<not> \<Sigma> \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> ?\<T> (fst s) (\<Sigma>, \<Gamma>) \<noteq> None \<longrightarrow> \<not>the (?\<T> (fst s) (\<Sigma>, \<Gamma>)) \<Turnstile>\<^sub>L \<bottom>\<^sub>L\<close> by simp
      with \<open>\<exists>\<phi>. (\<phi>, basic n) \<in> \<Pi>\<^sub>x\<close> show \<open>\<not> \<Sigma> \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> ?\<T> n (\<Sigma>, \<Gamma>) \<noteq> None \<longrightarrow> \<not> the (?\<T> n (\<Sigma>, \<Gamma>)) \<Turnstile>\<^sub>L \<bottom>\<^sub>L\<close> by simp
    qed
  next
    fix n M
    have *: \<open>n \<notin> set (map fst S\<^sub>x) \<longrightarrow> (\<forall>M. ?\<T> n M = None)\<close> using c unfolding complies_def by simp
    then have \<open>n \<notin> set (map fst S\<^sub>x) \<longrightarrow> ?\<T> n M = None\<close> by blast
    show \<open>?\<T> n M \<noteq> None \<longrightarrow> (\<exists>\<phi>. (\<phi>, basic n) \<in> \<Pi>\<^sub>x)\<close>
    proof
      assume \<open>?\<T> n M \<noteq> None\<close>
      then have \<open>n \<in> set (map fst S\<^sub>x)\<close> using * by metis
      then show \<open>\<exists>\<phi>. (\<phi>, basic n) \<in> \<Pi>\<^sub>x\<close> by simp
    qed
  next
    show \<open>is_ht_specification S\<^sub>x\<close> using s .
    show \<open>complies S\<^sub>x ?\<T>\<close> using c .
  qed
qed

end