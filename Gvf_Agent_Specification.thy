(*
  Goal verification framework
    - Agent Specification  
*)
\<comment> \<open>This theory sets up the framework for specifying agents by means of predicates for enabledness 
    and Hoare triple axioms  instead of providing a function for \<T>. Instead, adopt the idea that 
    we may assume the agent specification reflects the actual model, i.e. the \<T> function complies 
    to our specification.\<close>

theory Gvf_Agent_Specification imports Gvf_Hoare_Logic begin

\<comment> \<open>A type for the specification of enabledness and Hoare triple axioms.\<close>
type_synonym ht_specification = \<open>(Bcap \<times> \<Phi>\<^sub>M \<times> hoare_triple list) list\<close>
\<comment> \<open>Set of pairs of mental state formula (enabled) and set of Hoare triple axioms.\<close>

section \<open>Satisfiability of specification\<close>

\<comment> \<open>The main idea behind this, and the following, section is that we now base agents on specifications.
    We do not want to state the belief update function for an agent specifically. As such, we need
    a link between agent specification and belief update function. We can reduce this problem to the
    problem of proving the existence of a belief update function (model) given a specification.\<close>

\<comment> \<open>Satisfiability of a specification.\<close>
definition satisfiable :: \<open>ht_specification \<Rightarrow> bool\<close> where
  \<open>satisfiable S \<equiv> 
    \<comment> \<open>Quantify over all mental states. Go through each element s in S.\<close>
    \<forall>M. \<forall>s \<in> set S. 
      \<comment> \<open>Get fields in s. Define a variable for the set of preconditions satisfied by M.\<close>
      (let (_, \<Phi>, hts) = s; sat_hts = { ht \<in> set hts. M \<Turnstile>\<^sub>M pre ht } in
        \<comment> \<open>If the basic action is enabled (\<Phi>)\<close>
        (M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> 
          \<comment> \<open>There exists a mental state M'...\<close>
          (\<exists>M'. 
            \<comment> \<open>That preserves consistency, and ...\<close>
            (\<not> fst M \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> \<not> fst M' \<Turnstile>\<^sub>L \<bottom>\<^sub>L) \<and> 
            \<comment> \<open>Where the goal base is obtained by removing achieved goals, and ...\<close>
            (snd M' = snd M - {\<psi> \<in> snd M. fst M' \<Turnstile>\<^sub>L \<psi>}) \<and> 
            \<comment> \<open>That satisfy all of the Hoare triples for this basic action.\<close>
            (\<forall>ht \<in> sat_hts. M' \<Turnstile>\<^sub>M post ht))) \<and>
        \<comment> \<open>If the basic action is not enabled, the Hoare triples should be satisfied by M.\<close>
        (M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> (\<forall>ht \<in> sat_hts. M \<Turnstile>\<^sub>M post ht)))\<close>


\<comment> \<open>We restrict those elements of the type 'ht_specification' that are valid specifications.\<close>
\<comment> \<open>Hoare triples only for basic actions and should be for grouped for actions.\<close>
fun is_ht_specification_hts :: \<open>Bcap \<Rightarrow> hoare_triple list \<Rightarrow> bool\<close>  where
  \<open>is_ht_specification_hts n hts = 
    (\<forall>ht\<in> set hts. is_htb_basic ht \<and> fst (snd (the (htb_basic_unpack ht))) = n)\<close>

\<comment> \<open>Main definition. Each action (group) can only appear once, S is satisfiable and each element
   s of S satisfy the function defined above.\<close>
definition is_ht_specification :: \<open>ht_specification \<Rightarrow> bool\<close> where
  \<open>is_ht_specification S \<equiv> distinct (map fst S) \<and> satisfiable S \<and> 
                            (\<forall>s \<in> set S. is_ht_specification_hts (fst s) (snd (snd s)))\<close>

\<comment> \<open>State that a given \<T> complies to our assumptions, partly due to semantics of Hoare triples
    and partly due to the properties about the fixed agent\<close>
fun complies_ht :: \<open>mental_state \<Rightarrow> bel_upd_t \<Rightarrow> \<Phi>\<^sub>M \<Rightarrow> (\<Phi>\<^sub>M \<times> Bcap \<times> \<Phi>\<^sub>M) \<Rightarrow> bool\<close> where
  \<open>complies_ht M \<T> \<Phi> (\<phi>, n, \<psi>) =
    \<comment> \<open>\<Phi> specify if the action is enabled\<close>
    ((M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> \<T> n M \<noteq> None) \<and>
    \<comment> \<open>Transitions preserves consistency.\<close>
    (\<not> (fst M) \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> \<T> n M \<noteq> None \<longrightarrow> \<not>the (\<T> n M) \<Turnstile>\<^sub>L \<bottom>\<^sub>L) \<and>
    \<comment> \<open>Basic Hoare triple semantics for action enabled.\<close>
    (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M>* \<T> (basic n) M) \<Turnstile>\<^sub>M \<psi>) \<and>
    \<comment> \<open>Basic Hoare triple semantics for action not enabled.\<close>
    (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>))\<close>

\<comment> \<open>Does an element s of S comply to a given belief update function?\<close>
definition complies_hts :: \<open>(Bcap \<times> \<Phi>\<^sub>M \<times> hoare_triple list) \<Rightarrow> bel_upd_t \<Rightarrow> bool\<close> where
  \<open>complies_hts s \<T> \<equiv>
    \<comment> \<open>For all Hoare triples for this action...\<close>
    \<forall>ht\<in>set (snd (snd s)). 
      \<comment> \<open>It is for basic actions, and ...\<close>  
      is_htb_basic ht \<and> 
      \<comment> \<open>It complies for all mental states.\<close>
      (\<forall>M. complies_ht M \<T> (fst (snd s)) (the (htb_basic_unpack ht)))\<close>

\<comment> \<open>Main definition. Does the specification comply to a given belief update function?\<close>
definition complies :: \<open>ht_specification \<Rightarrow> bel_upd_t \<Rightarrow> bool\<close> where
  \<open>complies S \<T> \<equiv> (\<forall>s\<in>set S. complies_hts s \<T> \<and> (\<forall>n. n \<notin> set (map fst S) \<longrightarrow> (\<forall>M. \<T> n M = None)))\<close>

section \<open>Model existence\<close>

\<comment> \<open>Showing existence of a model that complies can be done separately for each group of Hoare triples.\<close>
lemma model_exists_disjoint: 
  assumes \<open>is_ht_specification S\<close>
     and  \<open>\<forall>s\<in>set S. \<exists>\<T>. complies_hts s \<T>\<close>
    shows \<open>\<exists>\<T>. complies S \<T>\<close>
proof 
  from assms(1) have \<open>distinct (map fst S)\<close> unfolding is_ht_specification_def by simp
  let ?\<T> = \<open>\<lambda>n. if n \<in> set (map fst S) then (SOME \<T>. complies_hts (THE s'. s'\<in>set S \<and> n = fst s') \<T>) n else (\<lambda>M. None)\<close>
  show \<open>complies S ?\<T>\<close> unfolding complies_def 
  proof
    fix s   
    assume member: \<open>s \<in> set S\<close>
    have \<open>complies_hts s ?\<T>\<close>    
    proof (cases s)
      case f1: (fields n \<Phi> hts)
      have \<open>\<forall>ht\<in>set hts. \<forall>M. complies_ht M ?\<T> \<Phi> (the (htb_basic_unpack ht))\<close>
      proof
        fix ht
        assume \<open>ht \<in> set hts\<close>
        show \<open>\<forall>M. complies_ht M ?\<T> \<Phi> (the (htb_basic_unpack ht))\<close>
        proof
          fix M
          show \<open>complies_ht M ?\<T> \<Phi> (the (htb_basic_unpack ht))\<close>
          proof (cases \<open>(the (htb_basic_unpack ht))\<close>)
            case (fields \<phi> n' \<psi>)
            have \<open>s\<in>set S \<and> fst s = fst s\<close> using \<open>s \<in> set S\<close> by simp
            moreover have \<open>\<forall>s'. s'\<in>set S \<and> fst s = fst s' \<longrightarrow> s' = s\<close> using \<open>distinct (map fst S)\<close>
              by (metis member eq_key_imp_eq_value prod.collapse)
            ultimately have \<open>(THE s'. s'\<in>set S \<and> fst s = fst s') = s\<close> using the_equality by auto
            then have \<open>?\<T> (fst s) = (SOME \<T>. complies_hts s \<T>) (fst s)\<close> (is \<open>?\<T> (fst s) = ?\<T>' (fst s)\<close>) using member by simp
            have \<open>\<exists>\<T>. complies_hts s \<T>\<close> using assms(2) member by simp
            then have \<open>complies_hts s ?\<T>'\<close> using someI_ex[where ?P=\<open>complies_hts s\<close>] by simp
            then have \<open>\<forall>ht\<in>set hts. is_htb_basic ht \<and> (\<forall>M. complies_ht M ?\<T>' \<Phi> (the (htb_basic_unpack ht)))\<close> 
              using f1 complies_hts_def by fastforce
            with f1 \<open>ht \<in> set hts\<close> have \<open>\<forall>M. complies_ht M ?\<T>' \<Phi> (the (htb_basic_unpack ht))\<close> by simp
            then have \<open>complies_ht M ?\<T>' \<Phi> (the (htb_basic_unpack ht))\<close> by blast
            moreover have \<open>n = n'\<close> 
              using fields assms(1) f1 member \<open>ht \<in> set hts\<close> unfolding is_ht_specification_def by fastforce
            ultimately have \<open>complies_ht M ?\<T>' \<Phi> (\<phi>, n, \<psi>)\<close> using fields by simp
            then have 
              \<open>(M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> ?\<T>' n M \<noteq> None) \<and>
              (\<not> (fst M) \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> ?\<T>' n M \<noteq> None \<longrightarrow> \<not>the (?\<T>' n M) \<Turnstile>\<^sub>L \<bottom>\<^sub>L) \<and>
              (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M>* ?\<T>' (basic n) M) \<Turnstile>\<^sub>M \<psi>) \<and>
              (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close> by simp
            moreover have \<open>n = fst s\<close> using f1 by simp
            then have \<open>?\<T> n = ?\<T>' n\<close> using \<open>?\<T> (fst s) = ?\<T>' (fst s)\<close> by blast
            moreover have \<open>\<M>* ?\<T> (basic n) M = \<M>* ?\<T>' (basic n) M\<close> 
            proof (cases M)
              case (Pair \<Sigma> \<Gamma>)
              then have \<open>\<M>* ?\<T> (basic n) M = \<M>* ?\<T> (basic n) (\<Sigma>, \<Gamma>)\<close> by simp
              also have \<open>\<M>* ?\<T> (basic n) (\<Sigma>, \<Gamma>) = (case ?\<T> n (\<Sigma>, \<Gamma>) of Some \<Sigma>' \<Rightarrow> Some (\<Sigma>', \<Gamma> - {\<psi> \<in> \<Gamma>. \<Sigma>' \<Turnstile>\<^sub>L \<psi>}) | _ \<Rightarrow> None)\<close> by simp
              also have \<open>\<dots> = (case ?\<T>' n (\<Sigma>, \<Gamma>) of Some \<Sigma>' \<Rightarrow> Some (\<Sigma>', \<Gamma> - {\<psi> \<in> \<Gamma>. \<Sigma>' \<Turnstile>\<^sub>L \<psi>}) | _ \<Rightarrow> None)\<close> using \<open>?\<T> n = ?\<T>' n\<close> by simp
              also have \<open>\<dots> = \<M>* ?\<T>' (basic n) (\<Sigma>, \<Gamma>)\<close> by simp
              finally show \<open>\<M>* ?\<T> (basic n) M = \<M>* ?\<T>' (basic n) M\<close> using Pair by simp
            qed
            ultimately have 
              \<open>(M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> ?\<T> n M \<noteq> None) \<and>
              (\<not> (fst M) \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> ?\<T> n M \<noteq> None \<longrightarrow> \<not>the (?\<T> n M) \<Turnstile>\<^sub>L \<bottom>\<^sub>L) \<and>
              (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M>* ?\<T> (basic n) M) \<Turnstile>\<^sub>M \<psi>) \<and>
              (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close> by simp
            then have \<open>complies_ht M ?\<T> \<Phi> (\<phi>, n, \<psi>)\<close> by simp
            with \<open>n = n'\<close> show ?thesis using fields by simp
          qed
        qed
      qed
      moreover have \<open>\<forall>ht\<in>set hts. is_htb_basic ht\<close> 
        using assms(1) f1 \<open>s \<in> set S\<close> unfolding is_ht_specification_def by simp
      ultimately show ?thesis using f1 complies_hts_def by simp
    qed
    then show \<open>complies_hts s ?\<T> \<and> (\<forall>n. n \<notin> set (map fst S) \<longrightarrow> (\<forall>M. ?\<T> n M = None))\<close> by simp
  qed
qed

\<comment> \<open>Definition used in proofs to put less strain on Isabelle's simplification methods.\<close>
definition next_state_reqs where
\<open>next_state_reqs M hts M' \<equiv> 
  (\<not> fst M \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> \<not> fst M' \<Turnstile>\<^sub>L \<bottom>\<^sub>L) \<and> 
  (snd M' = snd M - {\<psi> \<in> snd M. fst M' \<Turnstile>\<^sub>L \<psi>}) \<and> 
  (\<forall>ht \<in> { ht \<in> set hts. M \<Turnstile>\<^sub>M pre ht }. M' \<Turnstile>\<^sub>M post ht)\<close>

\<comment> \<open>If S is a valid specification, there exists a belief update function (model) that S complies to.\<close>
lemma model_exists: \<open>is_ht_specification S \<Longrightarrow> \<exists>\<T>. complies S \<T>\<close>
proof -
  assume spec: \<open>is_ht_specification S\<close>
  then have sat: \<open>satisfiable S\<close> unfolding is_ht_specification_def by simp
  have \<open>\<forall>s\<in>set S. \<exists>\<T>. complies_hts s \<T>\<close> proof
    fix s
    assume \<open>s \<in> set S\<close>
    show \<open>\<exists>\<T>. complies_hts s \<T>\<close> 
    proof (cases s)
      case f1: (fields n \<Phi> hts)
      have \<open>\<exists>\<T>. complies_hts (n, \<Phi>, hts) \<T>\<close> 
      proof
        let ?\<T> = \<open>\<lambda>n M. if M \<Turnstile>\<^sub>M \<Phi> then Some (fst (SOME M'. next_state_reqs M hts M')) else None\<close>
        have \<open>\<forall>ht\<in>set hts. is_htb_basic ht \<and> (\<forall>M. complies_ht M ?\<T> \<Phi> (the (htb_basic_unpack ht)))\<close>
        proof
          fix ht
          assume \<open>ht \<in> set hts\<close>
          show \<open>is_htb_basic ht \<and> (\<forall>M. complies_ht M ?\<T> \<Phi> (the (htb_basic_unpack ht)))\<close> 
          proof
            from spec show \<open>is_htb_basic ht\<close> 
              using \<open>ht \<in> set hts\<close> \<open>s \<in> set S\<close> f1 unfolding is_ht_specification_def by simp
            show \<open>\<forall>M. complies_ht M ?\<T> \<Phi> (the (htb_basic_unpack ht))\<close> 
            proof
              fix M
              show \<open>complies_ht M ?\<T> \<Phi> (the (htb_basic_unpack ht))\<close>  
              proof (cases \<open>the (htb_basic_unpack ht)\<close>)
                case (fields \<phi> n' \<psi>)
                moreover have \<open>complies_ht M ?\<T> \<Phi> (\<phi>, n, \<psi>)\<close>
                proof (cases \<open>M \<Turnstile>\<^sub>M \<Phi>\<close>)
                  case True
                  then have nM: \<open>?\<T> n M = Some (fst (SOME M'. next_state_reqs M hts M'))\<close> by simp
                  moreover from sat have 
                    \<open>let (_, \<Phi>, hts) = s; sat_hts = { ht \<in> set hts. M \<Turnstile>\<^sub>M pre ht } in
                      (M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> (\<exists>M'. (\<not> fst M \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> \<not> fst M' \<Turnstile>\<^sub>L \<bottom>\<^sub>L) \<and> 
                        (snd M' = snd M - {\<psi> \<in> snd M. fst M' \<Turnstile>\<^sub>L \<psi>}) \<and> 
                        (\<forall>ht \<in> sat_hts. M' \<Turnstile>\<^sub>M post ht))) \<and>
                      (M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> (\<forall>ht \<in> sat_hts. M \<Turnstile>\<^sub>M post ht))\<close> 
                    using \<open>s \<in> set S\<close> unfolding satisfiable_def by blast
                  with f1 True have ex:
                    \<open>\<exists>M'. next_state_reqs M hts M'\<close>
                    unfolding next_state_reqs_def by simp
                  have \<open>\<forall>M'. next_state_reqs M hts M' \<longrightarrow> \<not> (fst M) \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> ?\<T> n M \<noteq> None \<longrightarrow> \<not> fst M' \<Turnstile>\<^sub>L \<bottom>\<^sub>L\<close>
                  proof
                    fix M'
                    show \<open>next_state_reqs M hts M' \<longrightarrow> \<not> (fst M) \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> ?\<T> n M \<noteq> None \<longrightarrow> \<not> fst M' \<Turnstile>\<^sub>L \<bottom>\<^sub>L\<close> 
                    proof
                      assume \<open>next_state_reqs M hts M'\<close>
                      then show \<open>\<not> (fst M) \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> ?\<T> n M \<noteq> None \<longrightarrow> \<not> fst M' \<Turnstile>\<^sub>L \<bottom>\<^sub>L\<close> 
                        unfolding next_state_reqs_def by simp
                    qed
                  qed
                  with ex have \<open>\<not> (fst M) \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> ?\<T> n M \<noteq> None \<longrightarrow> \<not> fst (SOME M'. next_state_reqs M hts M') \<Turnstile>\<^sub>L \<bottom>\<^sub>L\<close>  
                    using someI2[where ?P=\<open>next_state_reqs M hts\<close>] by blast
                  moreover have \<open>\<forall>M'. next_state_reqs M hts M' \<longrightarrow> (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> M' \<Turnstile>\<^sub>M \<psi>)\<close>
                  proof
                    fix M'
                    show \<open>next_state_reqs M hts M' \<longrightarrow> (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> M' \<Turnstile>\<^sub>M \<psi>)\<close> 
                    proof
                      assume \<open>next_state_reqs M hts M'\<close>
                      with \<open>ht \<in> set hts\<close> have \<open>M \<Turnstile>\<^sub>M pre ht \<longrightarrow> M' \<Turnstile>\<^sub>M post ht\<close> unfolding next_state_reqs_def by simp
                      moreover from \<open>is_htb_basic ht\<close> have \<open>pre ht = \<phi>\<close> 
                        using fields unpack_sel(1) by fastforce
                      moreover from \<open>is_htb_basic ht\<close> have \<open>post ht = \<psi>\<close> 
                        using fields unpack_sel(2) by fastforce
                      ultimately have \<open>M \<Turnstile>\<^sub>M \<phi> \<longrightarrow> M' \<Turnstile>\<^sub>M \<psi>\<close> by simp
                      then show \<open>M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> M' \<Turnstile>\<^sub>M \<psi>\<close> by simp
                    qed
                  qed
                  with ex have \<open>(M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> (SOME M'. next_state_reqs M hts M') \<Turnstile>\<^sub>M \<psi>)\<close>
                    using someI2[where ?P=\<open>next_state_reqs M hts\<close>] by blast
                  ultimately have 
                    \<open>(M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> Some (fst (SOME M'. next_state_reqs M hts M')) \<noteq> None) \<and>
                      (\<not> (fst M) \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> \<not> fst (SOME M'. next_state_reqs M hts M') \<Turnstile>\<^sub>L \<bottom>\<^sub>L) \<and>
                      (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> (SOME M'. next_state_reqs M hts M') \<Turnstile>\<^sub>M \<psi>) \<and> 
                      (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close> 
                    using True by auto
                  moreover have \<open>(SOME M'. next_state_reqs M hts M') \<Turnstile>\<^sub>M \<psi> \<longrightarrow> the (\<M>* ?\<T> (basic n) M) \<Turnstile>\<^sub>M \<psi>\<close> 
                  proof (cases M)
                    case (Pair \<Sigma> \<Gamma>)
                    show ?thesis 
                    proof
                      assume entails: \<open>(SOME M'. next_state_reqs M hts M') \<Turnstile>\<^sub>M \<psi>\<close>
                      from Pair have \<open>\<forall>M'. next_state_reqs M hts M' \<longrightarrow> snd M' = (snd M - {\<psi> \<in> snd M. fst M' \<Turnstile>\<^sub>L \<psi>})\<close> 
                        unfolding next_state_reqs_def by simp
                      with ex have \<open>snd (SOME M'. next_state_reqs M hts M') = snd M - {\<psi> \<in> snd M. fst (SOME M'. next_state_reqs M hts M') \<Turnstile>\<^sub>L \<psi>}\<close>  
                        using someI2[where ?P=\<open>next_state_reqs M hts\<close>] by blast
                      with entails have \<open>(fst (SOME M'. next_state_reqs M hts M'), snd M - {\<psi> \<in> snd M. fst (SOME M'. next_state_reqs M hts M') \<Turnstile>\<^sub>L \<psi>}) \<Turnstile>\<^sub>M \<psi>\<close>
                        by (metis prod.collapse)
                      with nM Pair show \<open>the (\<M>* ?\<T> (basic n) M) \<Turnstile>\<^sub>M \<psi>\<close> by auto
                    qed
                  qed
                  ultimately have 
                    \<open>(M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> ?\<T> n M \<noteq> None) \<and>
                      (\<not> (fst M) \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> ?\<T> n M \<noteq> None \<longrightarrow> \<not> the (?\<T> n M) \<Turnstile>\<^sub>L \<bottom>\<^sub>L) \<and>
                      (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M>* ?\<T> (basic n) M) \<Turnstile>\<^sub>M \<psi>) \<and> 
                      (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close> 
                    using nM by simp
                  then show ?thesis using complies_ht.simps by blast
                next
                  case False
                  then have \<open>?\<T> n M = None\<close> by simp 
                  then have \<open>M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>\<close> 
                  proof -
                    from sat have 
                      \<open>let (_, \<Phi>, hts) = s; sat_hts = { ht \<in> set hts. M \<Turnstile>\<^sub>M pre ht } in
                        (M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> (\<exists>M'. (\<not> fst M \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> \<not> fst M' \<Turnstile>\<^sub>L \<bottom>\<^sub>L) \<and> 
                          (snd M' = snd M - {\<psi> \<in> snd M. fst M' \<Turnstile>\<^sub>L \<psi>}) \<and> 
                          (\<forall>ht \<in> sat_hts. M' \<Turnstile>\<^sub>M post ht))) \<and>
                        (M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> (\<forall>ht \<in> sat_hts. M \<Turnstile>\<^sub>M post ht))\<close> 
                      using \<open>s \<in> set S\<close> unfolding satisfiable_def by blast
                    then have \<open>\<forall>ht \<in> { ht \<in> set hts. M \<Turnstile>\<^sub>M pre ht }. M \<Turnstile>\<^sub>M post ht\<close> 
                      using False f1 by simp
                    with \<open>ht \<in> set hts\<close> have \<open>M \<Turnstile>\<^sub>M pre ht \<longrightarrow> M \<Turnstile>\<^sub>M post ht\<close> by simp
                    moreover from \<open>is_htb_basic ht\<close> have \<open>pre ht = \<phi>\<close> 
                      using fields unpack_sel(1) by fastforce
                    moreover from \<open>is_htb_basic ht\<close> have \<open>post ht = \<psi>\<close> 
                      using fields unpack_sel(2) by fastforce
                    ultimately have \<open>M \<Turnstile>\<^sub>M \<phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>\<close> by simp
                    then show ?thesis by simp
                  qed
                  with False show ?thesis by simp
                qed
                moreover from spec have \<open>n = n'\<close> 
                  using \<open>s \<in> set S\<close> \<open>ht \<in> set hts\<close> f1 fields 
                  unfolding is_ht_specification_def by fastforce
                ultimately show ?thesis by metis
              qed              
            qed
          qed
        qed
        then show \<open>complies_hts (n, \<Phi>, hts) ?\<T>\<close> unfolding complies_hts_def by simp
      qed
      with f1 show ?thesis by simp
    qed
  qed
  with model_exists_disjoint \<open>is_ht_specification S\<close> show ?thesis .
qed

section \<open>Single agent program given by specification\<close>

locale single_agent_program = single_agent + 
  fixes
    Sp :: ht_specification
  assumes
    Sp_valid: \<open>is_ht_specification Sp\<close> and 
    \<T>_complies: \<open>complies Sp \<T>\<close>

context single_agent_program begin

subsection \<open>Proof System\<close>

\<comment> \<open>Derive (the) valid Hoare triples.\<close>

inductive derive\<^sub>H :: \<open>hoare_triple \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>H\<close>) where
  \<comment> \<open>Agent specific rule import\<close>
  import: \<open>(n, \<Phi>, hts) \<in> set Sp \<Longrightarrow> \<^bold>{ \<phi> \<^bold>} (basic n) \<^bold>{ \<psi> \<^bold>} \<in> set hts \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>} (basic n) \<^bold>{ \<psi> \<^bold>}\<close> |
  \<comment> \<open>Persistence of goals\<close>
  (*persist: \<open>\<not> is_drop a \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ G \<Phi> \<^bold>} a \<^bold>{ (B \<Phi>) \<^bold>\<or> (G \<Phi>) \<^bold>}\<close> |*)
  persist: \<open>\<not> is_drop a \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ (G \<Phi>)  \<^bold>} a \<^bold>{ (B \<Phi>) \<^bold>\<or> (G \<Phi>) \<^bold>}\<close> |
  \<comment> \<open>Infeasible actions\<close>
  inf:  \<open>\<turnstile>\<^sub>E ((\<phi>\<^sup>E) \<^bold>\<longrightarrow> \<^bold>\<not>(enabledb a)) \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>} a \<^bold>{ \<phi> \<^bold>}\<close> |
  \<comment> \<open>Frame properties on beliefs for adopt and drop\<close>
  adoptB: \<open>\<turnstile>\<^sub>H \<^bold>{ B \<Phi> \<^bold>} (adopt \<psi>) \<^bold>{ B \<Phi> \<^bold>}\<close> |
  adoptNegB: \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not> (B \<Phi>) \<^bold>} (adopt \<psi>) \<^bold>{ \<^bold>\<not> (B \<Phi>) \<^bold>}\<close> |
  dropB: \<open>\<turnstile>\<^sub>H \<^bold>{ B \<Phi> \<^bold>} (drop \<psi>) \<^bold>{ B \<Phi> \<^bold>}\<close> |
  dropNegB: \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not> (B \<Phi>) \<^bold>} (drop \<psi>) \<^bold>{ \<^bold>\<not> (B \<Phi>) \<^bold>}\<close> |
  \<comment> \<open>Effects of adopt\<close>
  adoptBG: \<open>\<not> {} \<Turnstile>\<^sub>P (\<^bold>\<not> \<Phi>) \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not> (B \<Phi>) \<^bold>} (adopt \<Phi>) \<^bold>{ G \<Phi> \<^bold>}\<close> |
  \<comment> \<open>Non-effect of adopt\<close>
  adoptG: \<open>\<turnstile>\<^sub>H \<^bold>{ G \<Phi> \<^bold>} (adopt \<psi>) \<^bold>{ G \<Phi> \<^bold>}\<close> |
  adoptNegG: \<open>\<not> {} \<Turnstile>\<^sub>P \<psi> \<^bold>\<longrightarrow> \<Phi> \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not> (G \<Phi>) \<^bold>} (adopt \<psi>) \<^bold>{ \<^bold>\<not> (G \<Phi>) \<^bold>}\<close> |
  \<comment> \<open>Effects of drop\<close>
  dropG: \<open>{} \<Turnstile>\<^sub>P \<Phi> \<^bold>\<longrightarrow> \<psi> \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ G \<Phi> \<^bold>} (drop \<psi>) \<^bold>{ \<^bold>\<not> (G \<Phi>) \<^bold>}\<close> |
  \<comment> \<open>Non-effects of drop\<close>
  dropNegG: \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not>(G \<Phi>) \<^bold>} (drop \<psi>) \<^bold>{ \<^bold>\<not>(G \<Phi>) \<^bold>}\<close> |
  dropGCon: \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not>(G (\<Phi> \<^bold>\<and> \<psi>)) \<^bold>\<and> (G \<Phi>) \<^bold>} (drop \<psi>) \<^bold>{ G \<Phi> \<^bold>}\<close> |
  \<comment> \<open>Rule for conditional actions\<close>
  rCondAct: \<open>\<turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>\<and> \<psi> \<^bold>} a \<^bold>{ \<phi>' \<^bold>} \<Longrightarrow> \<turnstile>\<^sub>M (\<phi> \<^bold>\<and> \<^bold>\<not>\<psi>) \<^bold>\<longrightarrow> \<phi>' \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>} (\<psi> \<triangleright> do a) \<^bold>{ \<phi>' \<^bold>}\<close> |
  \<comment> \<open>Structural rules\<close>
  rImp: \<open>\<turnstile>\<^sub>M \<phi>' \<^bold>\<longrightarrow> \<phi> \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>} a \<^bold>{ \<psi> \<^bold>} \<Longrightarrow> \<turnstile>\<^sub>M \<psi> \<^bold>\<longrightarrow> \<psi>' \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi>' \<^bold>} a \<^bold>{ \<psi>' \<^bold>}\<close> |
  rCon: \<open>\<turnstile>\<^sub>H \<^bold>{ \<phi>\<^sub>1 \<^bold>} a \<^bold>{ \<psi>\<^sub>1 \<^bold>} \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi>\<^sub>2 \<^bold>} a \<^bold>{ \<psi>\<^sub>2 \<^bold>} \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2 \<^bold>} a \<^bold>{ \<psi>\<^sub>1 \<^bold>\<and> \<psi>\<^sub>2 \<^bold>}\<close> |
  rDis: \<open>\<turnstile>\<^sub>H \<^bold>{ \<phi>\<^sub>1 \<^bold>} a \<^bold>{ \<psi> \<^bold>} \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi>\<^sub>2 \<^bold>} a \<^bold>{ \<psi> \<^bold>} \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2 \<^bold>} a \<^bold>{ \<psi> \<^bold>}\<close>

\<comment> \<open>A proof of a Hoare triple ensures validity.\<close>
\<comment> \<open>Induction over each rule.\<close>
theorem soundness\<^sub>H: \<open>\<turnstile>\<^sub>H H \<Longrightarrow> \<Turnstile>\<^sub>H H\<close> 
proof (induct rule: derive\<^sub>H.induct)
  case (import n \<Phi> hts \<phi> \<psi>)
  let ?a = \<open>basic n\<close> 
  let ?ht = \<open>\<^bold>{ \<phi> \<^bold>} ?a \<^bold>{ \<psi> \<^bold>}\<close>
  have \<open>\<forall>s\<in>set Sp. complies_hts s \<T>\<close> using \<T>_complies unfolding complies_def by simp
  with import(1) have \<open>\<forall>ht\<in>set hts. is_htb_basic ht \<and> (\<forall>M. complies_ht M \<T> \<Phi> (the (htb_basic_unpack ht)))\<close> 
    unfolding complies_hts_def by auto
  with bspec have \<open>is_htb_basic ?ht \<and> (\<forall>M. complies_ht M \<T> \<Phi> (the (htb_basic_unpack ?ht)))\<close> 
    using import(2) .
  then have **: 
    \<open>\<forall>M. (M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> \<T> n M \<noteq> None) \<and>
         (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M>* \<T> (basic n) M) \<Turnstile>\<^sub>M \<psi>) \<and>
         (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close>
    by simp
  have *:
    \<open>\<forall>M. (M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> \<T> n M \<noteq> None) \<and>
         (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M \<psi>) \<and>
         (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close>
  proof 
    fix M
    show \<open>(M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> \<T> n M \<noteq> None) \<and>
          (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M \<psi>) \<and>
          (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close>
    proof (cases M)
      case (Pair \<Sigma> \<Gamma>)
      with ** have \<open>((\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> \<T> n M \<noteq> None) \<and>
         ((\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<phi> \<and> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M>* \<T> (basic n) M) \<Turnstile>\<^sub>M \<psi>) \<and>
         ((\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<phi> \<and> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<psi>)\<close> by simp
      then show ?thesis using Pair by simp
    qed
  qed
  have \<open>\<forall>M. (M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and> (enabledb ?a) \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M \<psi>) \<and> (M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and> \<^bold>\<not>(enabledb ?a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close>
  proof
    fix M
    from * have 
      \<open>(M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M \<psi>) \<and>
       (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close> 
      by blast
    moreover have \<open>M \<Turnstile>\<^sub>E (enabledb ?a) \<longleftrightarrow> M \<Turnstile>\<^sub>M \<Phi>\<close> 
    proof (cases M)
      case (Pair \<Sigma> \<Gamma>)
      with * have \<open>(\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> \<T> n (\<Sigma>, \<Gamma>) \<noteq> None\<close> by blast
      moreover have \<open>\<T> n (\<Sigma>, \<Gamma>) \<noteq> None \<longrightarrow> \<M> (basic n) (\<Sigma>, \<Gamma>) \<noteq> None\<close> by auto
      moreover have \<open>\<dots> \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>E (enabledb ?a)\<close> by simp
      ultimately show ?thesis using Pair by auto
    qed
    ultimately have 
      \<open>(M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>E (enabledb ?a) \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M \<psi>) \<and> 
       (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>E \<^bold>\<not> (enabledb ?a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close> by simp
    then show \<open>(M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and> (enabledb ?a) \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M \<psi>) \<and> (M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and> \<^bold>\<not>(enabledb ?a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close>  
      using transfer_semantics\<^sub>M by simp
  qed
  then show ?case by simp
next
  case (persist a \<Phi>)
  have \<open>\<forall>M. (M \<Turnstile>\<^sub>M (G \<Phi>) \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M (B \<Phi>) \<^bold>\<or> (G \<Phi>)) \<and> 
            (M \<Turnstile>\<^sub>M (G \<Phi>) \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M (B \<Phi>) \<^bold>\<or> (G \<Phi>))\<close>
  proof
    fix M
    show \<open>(M \<Turnstile>\<^sub>M (G \<Phi>) \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M (B \<Phi>) \<^bold>\<or> (G \<Phi>)) \<and> 
          (M \<Turnstile>\<^sub>M (G \<Phi>) \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M (B \<Phi>) \<^bold>\<or> (G \<Phi>))\<close>
    proof (cases M)
      case (Pair \<Sigma> \<Gamma>)
      show ?thesis
      proof
        show \<open>M \<Turnstile>\<^sub>M (G \<Phi>) \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M (B \<Phi>) \<^bold>\<or> (G \<Phi>)\<close> 
        proof
          assume asm: \<open>M \<Turnstile>\<^sub>M (G \<Phi>) \<and> M \<Turnstile>\<^sub>E (enabledb a)\<close>
          with Pair have notNone: \<open>\<M> a (\<Sigma>, \<Gamma>) \<noteq> None\<close> by simp
          show \<open>the (\<M> a M) \<Turnstile>\<^sub>M (B \<Phi>) \<^bold>\<or> (G \<Phi>)\<close> 
          proof (cases a)
            case (basic n)
            with notNone have \<open>\<M> (basic n) (\<Sigma>, \<Gamma>) \<noteq> None\<close> by simp
            then obtain \<Sigma>' where \<Sigma>': \<open>\<T> n (\<Sigma>, \<Gamma>) = Some \<Sigma>'\<close> by fastforce
            then have mst_unfold: \<open>\<M> (basic n) (\<Sigma>, \<Gamma>) = Some (\<Sigma>', \<Gamma> - {\<psi> \<in> \<Gamma>. \<Sigma>' \<Turnstile>\<^sub>L \<psi>})\<close>
                              (is \<open>\<M> (basic n) (\<Sigma>, \<Gamma>) = Some (\<Sigma>', ?\<Gamma>')\<close>) 
              by simp
            then show ?thesis 
            proof (cases \<open>\<Sigma>' \<Turnstile>\<^sub>L \<Phi>\<close>)
              case True
              then have \<open>(\<Sigma>', ?\<Gamma>') \<Turnstile>\<^sub>M (B \<Phi>) \<^bold>\<or> (G \<Phi>)\<close> by auto
              with mst_unfold show ?thesis using basic Pair by simp
            next
              case False
              moreover from asm have \<open>(\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M G \<Phi>\<close> using Pair by simp
              ultimately have \<open>(\<Sigma>', ?\<Gamma>') \<Turnstile>\<^sub>M G \<Phi>\<close> by auto
              with mst_unfold show ?thesis using basic Pair by simp
            qed
          next
            case (adopt \<Phi>')
            have \<open>\<M> (adopt \<Phi>') (\<Sigma>, \<Gamma>) = (if \<not> {} \<Turnstile>\<^sub>L \<^bold>\<not> \<Phi>' \<and> \<not> \<Sigma> \<Turnstile>\<^sub>L \<Phi>' then Some (\<Sigma>, \<Gamma> \<union> {\<Phi>'}) else None)\<close> 
              by simp
            with notNone have \<open>\<M> (adopt \<Phi>') (\<Sigma>, \<Gamma>) = Some (\<Sigma>, \<Gamma> \<union> {\<Phi>'})\<close> using adopt by metis
            then show ?thesis using adopt Pair asm by simp
          next 
            case (drop \<psi>)  
            with persist show ?thesis by simp
          qed
        qed
      qed simp 
    qed
  qed
  then show ?case by simp
next
  case (inf \<phi> a)
  then have \<open>\<forall>M. \<nabla>M \<longrightarrow> M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb a)\<close> using soundness\<^sub>E by blast
  then have \<open>\<forall>M. \<nabla>M \<longrightarrow> (M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and>  (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<phi>) \<and> 
                         (M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and> \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<phi>)\<close>
    using transfer_semantics\<^sub>M by auto
  then show ?case by auto
next
  case (adoptBG \<Phi>)
  let ?\<phi> = \<open>\<^bold>\<not> (B \<Phi>)\<close> and ?\<psi> = \<open>G \<Phi>\<close> and ?a = \<open>adopt \<Phi>\<close>
  have \<open>\<forall>M. \<nabla>M \<longrightarrow> 
        (M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E) \<^bold>\<and>  (enabledb ?a) \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi>) \<and> 
        (M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E) \<^bold>\<and> \<^bold>\<not>(enabledb ?a) \<longrightarrow> M \<Turnstile>\<^sub>M ?\<psi>)\<close>
  proof
    fix M 
    have \<open>\<nabla>M \<longrightarrow> M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E) \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi> \<and> M \<Turnstile>\<^sub>E enabledb ?a\<close>
    proof
      assume \<open>\<nabla> M\<close>
      show \<open>M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E) \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi> \<and> M \<Turnstile>\<^sub>E enabledb ?a\<close>
      proof
        assume \<open>M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E)\<close>
        show \<open>the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi> \<and> M \<Turnstile>\<^sub>E enabledb ?a\<close>
        proof
          from \<open>M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E)\<close> show \<open>M \<Turnstile>\<^sub>E enabledb ?a\<close> using adoptBG by (cases M) simp
          with \<open>M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E)\<close> adoptBG have s: \<open>\<M> ?a M = Some (fst M, snd M \<union> {\<Phi>})\<close> by (cases M) simp
          then have \<open>\<exists>\<gamma>\<in>snd (the (\<M> ?a M)). {} \<Turnstile>\<^sub>L \<gamma> \<^bold>\<longrightarrow> \<Phi>\<close> by simp
          moreover {
            from s have \<open>fst (the (\<M> ?a M)) = fst M\<close> by simp
            moreover have \<open>\<not> fst M \<Turnstile>\<^sub>L \<Phi>\<close> using \<open>M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E)\<close> by (cases M) simp
            ultimately have \<open>\<not> fst (the (\<M> ?a M)) \<Turnstile>\<^sub>L \<Phi>\<close> by simp
          }
          ultimately show \<open>the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi>\<close> 
            using semantics\<^sub>M'.simps(2)[where \<Sigma>=\<open>fst (the (\<M> ?a M))\<close> and \<Gamma>=\<open>snd (the (\<M> ?a M))\<close>] 
            by simp
        qed
      qed
    qed
    then show 
      \<open>\<nabla>M \<longrightarrow>
        (M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E) \<^bold>\<and>  (enabledb ?a) \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi>) \<and> 
        (M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E) \<^bold>\<and> \<^bold>\<not>(enabledb ?a) \<longrightarrow> M \<Turnstile>\<^sub>M ?\<psi>)\<close> 
      by auto
  qed
  then show ?case by simp
next
  case (dropGCon \<Phi> \<psi>)
  let ?\<phi> = \<open>\<^bold>\<not> (G (\<Phi> \<^bold>\<and> \<psi>)) \<^bold>\<and> (G \<Phi>)\<close> and ?\<psi> = \<open>G \<Phi>\<close> and ?a = \<open>drop \<psi>\<close>
  have \<open>\<forall>M. \<nabla>M \<longrightarrow> (M \<Turnstile>\<^sub>M ?\<phi> \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi>)\<close> 
  proof
    fix M
    show \<open>\<nabla>M \<longrightarrow> (M \<Turnstile>\<^sub>M ?\<phi> \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi>)\<close>
    proof
      assume \<open>\<nabla>M\<close>
      show \<open>M \<Turnstile>\<^sub>M ?\<phi> \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi>\<close>
      proof
        assume \<open>M \<Turnstile>\<^sub>M ?\<phi>\<close>      
        with dropGCon have pre:
          \<open>\<not> fst M \<Turnstile>\<^sub>L \<Phi> \<and> 
           \<not> (\<exists>\<gamma>\<in>snd M. {} \<Turnstile>\<^sub>L \<gamma> \<^bold>\<longrightarrow> (\<Phi> \<^bold>\<and> \<psi>)) \<and> 
              (\<exists>\<gamma>\<in>snd M. {} \<Turnstile>\<^sub>L \<gamma> \<^bold>\<longrightarrow> \<Phi>)\<close>  
          by (cases M) auto
        moreover from pre obtain \<gamma> where gamma: \<open>\<gamma> \<in> snd M \<and> {} \<Turnstile>\<^sub>L \<gamma> \<^bold>\<longrightarrow> \<Phi>\<close> by auto
        moreover have aM: \<open>\<M> ?a M = Some (fst M, snd M - {\<gamma> \<in> snd M. {\<gamma>} \<Turnstile>\<^sub>L \<psi>})\<close> (is \<open>\<dots> = Some ?M'\<close>) 
          by (cases M) simp
        ultimately have \<open>\<not> fst ?M' \<Turnstile>\<^sub>L \<Phi>\<close> by simp
        moreover from pre gamma have \<open>\<not> {\<gamma>} \<Turnstile>\<^sub>L \<Phi> \<^bold>\<and> \<psi>\<close> by auto
        with gamma have \<open>\<exists>\<gamma>\<in>snd ?M'. {} \<Turnstile>\<^sub>L \<gamma> \<^bold>\<longrightarrow> \<Phi>\<close> by auto
        ultimately show \<open>the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi>\<close> using aM by simp
      qed
    qed
  qed
  then show ?case by simp
next
  case (rCondAct \<phi> \<psi> a \<phi>')
  have \<open>\<forall> s \<in> Agent. \<forall>i. ((\<phi>\<^bold>[s i\<^bold>]\<^sub>M) \<and> (\<psi> \<triangleright> do a) = (act_nth s i) \<longrightarrow> (\<phi>'\<^bold>[s (i+1)\<^bold>]\<^sub>M))\<close>
  proof
    fix s
    assume \<open>s \<in> Agent\<close>
    show \<open>\<forall>i. ((\<phi>\<^bold>[s i\<^bold>]\<^sub>M) \<and> (\<psi> \<triangleright> do a) = (act_nth s i) \<longrightarrow> (\<phi>'\<^bold>[s (i+1)\<^bold>]\<^sub>M))\<close>
    proof
      fix i
      have \<open>\<nabla> (st_nth s i)\<close> using is_mst_trace \<open>s \<in> Agent\<close> .
      with rCondAct have a:
        \<open>((\<phi> \<^bold>\<and> \<^bold>\<not>\<psi>) \<^bold>\<longrightarrow> \<phi>')\<^bold>[s i\<^bold>]\<^sub>M\<close> 
        \<open>(st_nth s i \<Turnstile>\<^sub>E ((\<phi> \<^bold>\<and> \<psi>)\<^sup>E) \<^bold>\<and>  (enabledb a) \<longrightarrow> the (\<M> a (st_nth s i)) \<Turnstile>\<^sub>M \<phi>') \<and>
         (st_nth s i \<Turnstile>\<^sub>E ((\<phi> \<^bold>\<and> \<psi>)\<^sup>E) \<^bold>\<and> \<^bold>\<not>(enabledb a) \<longrightarrow> st_nth s i \<Turnstile>\<^sub>M \<phi>')\<close>
        using soundness\<^sub>M semantics\<^sub>H.simps(1) by blast+
      show \<open>(\<phi>\<^bold>[s i\<^bold>]\<^sub>M) \<and> (\<psi> \<triangleright> do a) = (act_nth s i) \<longrightarrow> (\<phi>'\<^bold>[s (i+1)\<^bold>]\<^sub>M)\<close> 
      proof
        assume pre: \<open>st_nth s i \<Turnstile>\<^sub>M \<phi> \<and> (\<psi>, a) = act_nth s i\<close>
        then have bact: \<open>(\<psi>, a) = act_nth s i\<close> by simp
        show \<open>\<phi>'\<^bold>[s (i+1)\<^bold>]\<^sub>M\<close>
        proof (cases \<open>(st_nth s i) \<rightarrow>(\<psi>, a) (st_nth s (i+1))\<close>)
          case True
          then have \<open>st_nth s i \<Turnstile>\<^sub>M \<psi>\<close> unfolding transition_def by simp
          with pre have \<open>st_nth s i \<Turnstile>\<^sub>E ((\<phi> \<^bold>\<and> \<psi>)\<^sup>E)\<close> using transfer_semantics\<^sub>M by simp
          moreover from True have \<open>\<M> a (st_nth s i) \<noteq> None\<close> unfolding transition_def by simp
          moreover from this have \<open>st_nth s i \<Turnstile>\<^sub>E enabledb a\<close> by simp
          ultimately show ?thesis using \<M>_suc_state \<open>s \<in> Agent\<close> bact a(2) by auto
        next
          case False
          moreover from \<open>s \<in> Agent\<close> have \<open>is_trace s\<close> unfolding Agent_def by simp
          ultimately have \<open>st_nth s i = st_nth s (i+1)\<close> using not_transition_eq bact by simp
          moreover from \<open>is_trace s\<close> have 
            \<open>let (M, M', \<phi>, a) = (st_nth s i, st_nth s (i + 1), act_nth s i) in 
              (\<phi>, a) \<in> \<Pi> \<and> ((M \<rightarrow>(\<phi>, a) M') \<or> \<M> a M = None \<and> M = M')\<close> 
            unfolding is_trace_def by simp
          with False bact have \<open>\<M> a (st_nth s i) = None\<close> by auto
          ultimately show ?thesis using a pre transfer_semantics\<^sub>M by auto
        qed
      qed
    qed
  qed
  then show ?case by simp
next
  case (rImp \<phi>' \<phi> a \<psi> \<psi>')
  have 
    \<open>\<forall>M. \<nabla>M \<longrightarrow>
      (M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>') \<and> 
      (M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>')\<close> 
  proof
    fix M
    show \<open>\<nabla>M \<longrightarrow>
      (M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>') \<and> 
      (M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>')\<close>
    proof
      assume \<open>\<nabla>M\<close>
      show 
        \<open>(M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>') \<and> 
         (M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>')\<close> 
      proof
        show \<open>M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>'\<close> 
        proof
          assume pre: \<open>M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E (enabledb a)\<close>
          moreover from rImp have \<open>M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>\<close> 
            using \<open>\<nabla>M\<close> transfer_semantics\<^sub>M semantics\<^sub>H.simps(1) semantics\<^sub>P.simps(5) by blast
          moreover from soundness\<^sub>M  have \<open>M \<Turnstile>\<^sub>M \<phi>' \<^bold>\<longrightarrow> \<phi>\<close> 
            using \<open>\<nabla>M\<close> rImp(1) by blast
          moreover have \<open>\<nabla> (the (\<M> a M))\<close> using \<open>\<nabla>M\<close> \<M>_preserves_mst pre by (cases M) simp
          with soundness\<^sub>M  have \<open>the (\<M> a M) \<Turnstile>\<^sub>M \<psi> \<^bold>\<longrightarrow> \<psi>'\<close> using rImp(4) by blast
          ultimately show \<open>the (\<M> a M) \<Turnstile>\<^sub>M \<psi>'\<close> by simp
        qed
        show \<open>M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>'\<close>
        proof
          assume pre: \<open>M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a)\<close>
          from rImp(3) have \<open>M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>\<close> 
            using \<open>\<nabla>M\<close> transfer_semantics\<^sub>M semantics\<^sub>H.simps(1) semantics\<^sub>P.simps(5) by blast
          moreover from soundness\<^sub>M  have \<open>M \<Turnstile>\<^sub>M \<phi>' \<^bold>\<longrightarrow> \<phi>\<close> 
            using \<open>\<nabla>M\<close> rImp(1) by blast
          moreover from soundness\<^sub>M  have \<open>M \<Turnstile>\<^sub>M \<psi> \<^bold>\<longrightarrow> \<psi>'\<close>
            using \<open>\<nabla>M\<close> rImp(4) by blast
          ultimately show \<open>M \<Turnstile>\<^sub>M \<psi>'\<close> using pre by simp
        qed
      qed
    qed
  qed
  with transfer_semantics\<^sub>M show ?case by simp
next
  case (rDis \<phi>\<^sub>1 a \<psi> \<phi>\<^sub>2)
  have 
    \<open>\<forall>M. \<nabla>M \<longrightarrow>
      (M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>) \<and> 
      (M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close>
  proof
    fix M
    show \<open>\<nabla>M \<longrightarrow>
      (M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>) \<and> 
      (M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close>
    proof
      assume \<open>\<nabla>M\<close>
      show 
        \<open>(M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>) \<and> 
         (M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close> 
      proof
        show \<open>M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>\<close> 
        proof
          assume \<open>M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E (enabledb a)\<close> 
          moreover from rDis(2) have \<open>M \<Turnstile>\<^sub>M \<phi>\<^sub>1 \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>\<close>
            using \<open>\<nabla>M\<close> transfer_semantics\<^sub>M semantics\<^sub>H.simps(1) semantics\<^sub>P.simps(5) by blast
          moreover from rDis(4) have \<open>M \<Turnstile>\<^sub>M \<phi>\<^sub>2 \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>\<close>
            using \<open>\<nabla>M\<close> transfer_semantics\<^sub>M semantics\<^sub>H.simps(1) semantics\<^sub>P.simps(5) by blast
          ultimately show \<open>the (\<M> a M) \<Turnstile>\<^sub>M \<psi>\<close> by auto
        qed
        show \<open>M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>\<close>
        proof
          assume \<open>M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a)\<close> 
          moreover from rDis(2) have \<open>M \<Turnstile>\<^sub>M \<phi>\<^sub>1 \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>\<close>
            using \<open>\<nabla>M\<close> transfer_semantics\<^sub>M semantics\<^sub>H.simps(1) semantics\<^sub>P.simps(5) by blast
          moreover from rDis(4) have \<open>M \<Turnstile>\<^sub>M \<phi>\<^sub>2 \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>\<close>
            using \<open>\<nabla>M\<close> transfer_semantics\<^sub>M semantics\<^sub>H.simps(1) semantics\<^sub>P.simps(5) by blast
          ultimately show \<open>M \<Turnstile>\<^sub>M \<psi>\<close> by auto
        qed
      qed
    qed
  qed
  with transfer_semantics\<^sub>M show ?case by simp
qed auto

end
end