(*
  Goal verification framework
    - Agent Specification  
*)
\<comment> \<open>This theory sets up the framework for specifying agents by means of predicates for enabledness 
    and Hoare triple axioms  instead of providing a function for \<T>. Instead, adopt the idea that 
    we may assume the agent specification reflects the actual model, i.e. the \<T> function complies 
    to our specification.\<close>

theory Gvf_Agent_Specification imports Gvf_Hoare_Logic begin

\<comment> \<open>A type for the specification of actions, enabledness and ht axioms.\<close>
type_synonym ht_spec_elem = \<open>Bcap \<times> \<Phi>\<^sub>M \<times> hoare_triple list\<close>
type_synonym ht_specification = \<open>ht_spec_elem list\<close>

section \<open>Satisfiability of specification\<close>

\<comment> \<open>The main idea behind this, and the following, section is that we now base agents on specifications.
    We do not want to state the belief update function for an agent specifically. As such, we need
    a link between agent specification and belief update function. We can reduce this problem to the
    problem of proving the existence of a belief update function (model) given a specification.\<close>

definition satisfiable_base :: \<open>mental_state \<Rightarrow> hoare_triple list \<Rightarrow> \<Phi>\<^sub>L list \<Rightarrow> bool\<close> where
  \<open>satisfiable_base M hts \<Sigma> \<equiv>
    (\<not> fst M \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>) \<and> 
    (\<forall>ht \<in> set hts. M \<Turnstile>\<^sub>M pre ht \<longrightarrow> (\<Sigma>, [\<psi>\<leftarrow>snd M. \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>] ) \<Turnstile>\<^sub>M post ht)\<close>

fun satisfiable_l :: \<open>mental_state \<Rightarrow> ht_spec_elem \<Rightarrow> bool\<close> where
 \<open>satisfiable_l M (a, \<Phi>, hts) = (M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> (\<exists> \<Sigma>. satisfiable_base M hts \<Sigma>))\<close>

fun satisfiable_r :: \<open>mental_state \<Rightarrow> ht_spec_elem \<Rightarrow> bool\<close> where
 \<open>satisfiable_r M (_, \<Phi>, hts) =
    (M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> (\<forall>ht \<in> set hts. M \<Turnstile>\<^sub>M pre ht \<longrightarrow> M \<Turnstile>\<^sub>M post ht))\<close>

definition satisfiable :: \<open>ht_specification \<Rightarrow> bool\<close> where
  \<open>satisfiable S \<equiv>  \<forall>M. \<nabla> M \<longrightarrow> (\<forall>s \<in> set S. satisfiable_l M s \<and> satisfiable_r M s)\<close>

subsection \<open>Frame Axioms\<close>
\<comment> \<open>It is more practical to distinguish effect and frame axioms during specification.\<close>
type_synonym ht_specification_frax = \<open>ht_specification \<times> ((Bcap \<Rightarrow> bool) \<times> \<Phi>\<^sub>M list) list\<close>

fun add_hts :: \<open>ht_spec_elem \<Rightarrow> ((Bcap \<Rightarrow> bool) \<times> \<Phi>\<^sub>M list) list \<Rightarrow> ht_spec_elem\<close> where
  \<open>add_hts (a, \<Phi>, hts) L = (a, \<Phi>, hts @ concat (map (\<lambda>(p, fms). if p a then map (\<lambda>x. \<^bold>{ x \<^bold>} (basic a) \<^bold>{ x \<^bold>}) fms else []) L))\<close>

fun from_frax :: \<open>ht_specification_frax \<Rightarrow> ht_specification\<close> where
  \<open>from_frax ([], _) = []\<close> |
  \<open>from_frax (s # S, L) = add_hts s L # from_frax (S, L)\<close>

lemma satisfiable_r_frax: 
  \<open>\<forall>s \<in> set S. satisfiable_r M s \<Longrightarrow> \<forall>s \<in> set (from_frax (S, L)). satisfiable_r M s\<close>
  by (induct S) auto

subsection \<open>Compliance\<close>

\<comment> \<open>We restrict those elements of the type 'ht_specification' that are valid specifications.\<close>
\<comment> \<open>Hoare triples only for basic actions and should be for grouped for actions.\<close>
fun is_ht_specification_hts :: \<open>Bcap \<Rightarrow> hoare_triple list \<Rightarrow> bool\<close>  where
  \<open>is_ht_specification_hts n hts = 
    (hts \<noteq> [] \<and> (\<forall>ht\<in> set hts. is_htb_basic ht \<and> fst (snd (the (htb_basic_unpack ht))) = n))\<close>

\<comment> \<open>Main definition. Each action (group) can only appear once, S is satisfiable and each element
   s of S satisfy the function defined above.\<close>
definition is_ht_specification :: \<open>ht_specification \<Rightarrow> bool\<close> where
  \<open>is_ht_specification S \<equiv> S \<noteq> [] \<and> distinct (map fst S) \<and> satisfiable S \<and> 
                            (\<forall>s \<in> set S. is_ht_specification_hts (fst s) (snd (snd s)))\<close>

\<comment> \<open>State that a given \<T> complies to our assumptions, partly due to semantics of Hoare triples
    and partly due to the properties about the fixed agent\<close>
fun complies_ht :: \<open>mental_state \<Rightarrow> bel_upd_t \<Rightarrow> \<Phi>\<^sub>M \<Rightarrow> (\<Phi>\<^sub>M \<times> Bcap \<times> \<Phi>\<^sub>M) \<Rightarrow> bool\<close> where
  \<open>complies_ht M \<T> \<Phi> (\<phi>, n, \<psi>) =
    \<comment> \<open>\<Phi> specify if the action is enabled\<close>
    ((M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> \<T> n M \<noteq> None) \<and>
    \<comment> \<open>Transitions preserves consistency.\<close>
    (\<not> (fst M) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> \<T> n M \<noteq> None \<longrightarrow> \<not>the (\<T> n M) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>) \<and>
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
      \<comment> \<open>It complies for all reachable mental states.\<close>
      (\<forall>M. \<nabla>M \<longrightarrow> complies_ht M \<T> (fst (snd s)) (the (htb_basic_unpack ht)))\<close>

\<comment> \<open>Main definition. Does the specification comply to a given belief update function?\<close>
definition complies :: \<open>ht_specification \<Rightarrow> bel_upd_t \<Rightarrow> bool\<close> where
  \<open>complies S \<T> \<equiv> (\<forall>s\<in>set S. complies_hts s \<T>) \<and> (\<forall>n. n \<notin> set (map fst S) \<longrightarrow> (\<forall>M. \<T> n M = None))\<close>

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
    show \<open>\<forall>s\<in>set S. complies_hts s ?\<T>\<close>
    proof
      fix s   
      assume member: \<open>s \<in> set S\<close>
      show \<open>complies_hts s ?\<T>\<close>    
      proof (cases s)
        case f1: (fields n \<Phi> hts)
        have \<open>\<forall>ht\<in>set hts. \<forall>M. \<nabla>M \<longrightarrow> complies_ht M ?\<T> \<Phi> (the (htb_basic_unpack ht))\<close>
        proof
          fix ht
          assume \<open>ht \<in> set hts\<close>
          show \<open>\<forall>M. \<nabla>M \<longrightarrow> complies_ht M ?\<T> \<Phi> (the (htb_basic_unpack ht))\<close>
          proof
            fix M
            show \<open>\<nabla>M \<longrightarrow> complies_ht M ?\<T> \<Phi> (the (htb_basic_unpack ht))\<close>
            proof
              assume \<open>\<nabla>M\<close>
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
                then have \<open>\<forall>ht\<in>set hts. is_htb_basic ht \<and> (\<forall>M. \<nabla>M \<longrightarrow> complies_ht M ?\<T>' \<Phi> (the (htb_basic_unpack ht)))\<close> 
                  using f1 complies_hts_def by fastforce
                with f1 \<open>ht \<in> set hts\<close> have \<open>\<forall>M. \<nabla>M \<longrightarrow> complies_ht M ?\<T>' \<Phi> (the (htb_basic_unpack ht))\<close> by simp
                with \<open>\<nabla>M\<close> have \<open>complies_ht M ?\<T>' \<Phi> (the (htb_basic_unpack ht))\<close> by blast
                moreover have \<open>n = n'\<close> 
                  using fields assms(1) f1 member \<open>ht \<in> set hts\<close> unfolding is_ht_specification_def by fastforce
                ultimately have \<open>complies_ht M ?\<T>' \<Phi> (\<phi>, n, \<psi>)\<close> using fields by simp
                then have 
                  \<open>(M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> ?\<T>' n M \<noteq> None) \<and>
                  (\<not> (fst M) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> ?\<T>' n M \<noteq> None \<longrightarrow> \<not>the (?\<T>' n M) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>) \<and>
                  (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M>* ?\<T>' (basic n) M) \<Turnstile>\<^sub>M \<psi>) \<and>
                  (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close> by simp
                moreover have \<open>n = fst s\<close> using f1 by simp
                then have \<open>?\<T> n = ?\<T>' n\<close> using \<open>?\<T> (fst s) = ?\<T>' (fst s)\<close> by blast
                moreover have \<open>\<M>* ?\<T> (basic n) M = \<M>* ?\<T>' (basic n) M\<close> 
                proof (cases M)
                  case (Pair \<Sigma> \<Gamma>)
                  then have \<open>\<M>* ?\<T> (basic n) M = \<M>* ?\<T> (basic n) (\<Sigma>, \<Gamma>)\<close> by simp
                  also have \<open>\<M>* ?\<T> (basic n) (\<Sigma>, \<Gamma>) = (case ?\<T> n (\<Sigma>, \<Gamma>) of Some \<Sigma>' \<Rightarrow> Some (\<Sigma>', [\<psi>\<leftarrow>\<Gamma>. \<not> \<Sigma>' \<^bold>\<Turnstile>\<^sub>P \<psi>]) | _ \<Rightarrow> None)\<close> by simp
                  also have \<open>\<dots> = (case ?\<T>' n (\<Sigma>, \<Gamma>) of Some \<Sigma>' \<Rightarrow> Some (\<Sigma>', [\<psi>\<leftarrow>\<Gamma>. \<not> \<Sigma>' \<^bold>\<Turnstile>\<^sub>P \<psi>]) | _ \<Rightarrow> None)\<close> using \<open>?\<T> n = ?\<T>' n\<close> by simp
                  also have \<open>\<dots> = \<M>* ?\<T>' (basic n) (\<Sigma>, \<Gamma>)\<close> by simp
                  finally show \<open>\<M>* ?\<T> (basic n) M = \<M>* ?\<T>' (basic n) M\<close> using Pair by simp
                qed
                ultimately have 
                  \<open>(M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> ?\<T> n M \<noteq> None) \<and>
                  (\<not> (fst M) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> ?\<T> n M \<noteq> None \<longrightarrow> \<not>the (?\<T> n M) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>) \<and>
                  (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M>* ?\<T> (basic n) M) \<Turnstile>\<^sub>M \<psi>) \<and>
                  (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close> by simp
                then have \<open>complies_ht M ?\<T> \<Phi> (\<phi>, n, \<psi>)\<close> by simp
                with \<open>n = n'\<close> show ?thesis using fields by simp
              qed
            qed
          qed
        qed
        moreover have \<open>\<forall>ht\<in>set hts. is_htb_basic ht\<close> 
          using assms(1) f1 \<open>s \<in> set S\<close> unfolding is_ht_specification_def by simp
        ultimately show ?thesis using f1 complies_hts_def by simp
      qed
    qed
  next
    show \<open>\<forall>n. n \<notin> set (map fst S) \<longrightarrow> (\<forall>M. ?\<T> n M = None)\<close> by simp
  qed
qed

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
        let ?\<T> = \<open>\<lambda>n M. if M \<Turnstile>\<^sub>M \<Phi> then Some (SOME \<Sigma>. satisfiable_base M hts \<Sigma>) else None\<close>
        have \<open>\<forall>ht\<in>set hts. is_htb_basic ht \<and> (\<forall>M. \<nabla>M \<longrightarrow> complies_ht M ?\<T> \<Phi> (the (htb_basic_unpack ht)))\<close>
        proof
          fix ht
          assume \<open>ht \<in> set hts\<close>
          show \<open>is_htb_basic ht \<and> (\<forall>M. \<nabla>M \<longrightarrow> complies_ht M ?\<T> \<Phi> (the (htb_basic_unpack ht)))\<close> 
          proof
            from spec show \<open>is_htb_basic ht\<close> 
              using \<open>ht \<in> set hts\<close> \<open>s \<in> set S\<close> f1 unfolding is_ht_specification_def by simp
            show \<open>\<forall>M. \<nabla>M \<longrightarrow> complies_ht M ?\<T> \<Phi> (the (htb_basic_unpack ht))\<close> 
            proof
              fix M
              show \<open>\<nabla>M \<longrightarrow> complies_ht M ?\<T> \<Phi> (the (htb_basic_unpack ht))\<close>
              proof 
                assume \<open>\<nabla>M\<close>
                show \<open>complies_ht M ?\<T> \<Phi> (the (htb_basic_unpack ht))\<close>
                proof (cases \<open>the (htb_basic_unpack ht)\<close>)
                  case (fields \<phi> n' \<psi>)
                  moreover have \<open>complies_ht M ?\<T> \<Phi> (\<phi>, n, \<psi>)\<close>
                  proof (cases \<open>M \<Turnstile>\<^sub>M \<Phi>\<close>)
                    case True
                    then have nM: \<open>?\<T> n M = Some (SOME \<Sigma>. satisfiable_base M hts \<Sigma>)\<close> by simp
                    moreover from sat have \<open>satisfiable_l M s \<and> satisfiable_r M s\<close> 
                      unfolding satisfiable_def using \<open>s \<in> set S\<close> \<open>\<nabla>M\<close> by blast
                    with f1 True have ex: \<open>\<exists>\<Sigma>. satisfiable_base M hts \<Sigma>\<close> by simp
                    have \<open>\<forall>\<Sigma>. satisfiable_base M hts \<Sigma> \<longrightarrow> \<not> (fst M) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> ?\<T> n M \<noteq> None \<longrightarrow> \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close>
                    proof
                      fix \<Sigma>
                      show \<open>satisfiable_base M hts \<Sigma> \<longrightarrow> \<not> (fst M) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> ?\<T> n M \<noteq> None \<longrightarrow> \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> 
                      proof
                        assume \<open>satisfiable_base M hts \<Sigma>\<close>
                        then show \<open>\<not> (fst M) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> ?\<T> n M \<noteq> None \<longrightarrow> \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> 
                          unfolding satisfiable_base_def by simp
                      qed
                    qed
                    with ex have \<open>\<not> (fst M) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> ?\<T> n M \<noteq> None \<longrightarrow> \<not> (SOME \<Sigma>. satisfiable_base M hts \<Sigma>) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close>  
                      using someI2[where ?P=\<open>satisfiable_base M hts\<close>] by blast
                    moreover have \<open>\<forall>\<Sigma>. satisfiable_base M hts \<Sigma> \<longrightarrow> (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> (\<Sigma>, [\<psi>\<leftarrow>snd M. \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M \<psi>)\<close>
                    proof
                      fix \<Sigma>
                      show \<open>satisfiable_base M hts \<Sigma> \<longrightarrow> (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> (\<Sigma>, [\<psi>\<leftarrow>snd M. \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M \<psi>)\<close> 
                      proof
                        assume \<open>satisfiable_base M hts \<Sigma>\<close>
                        with \<open>ht \<in> set hts\<close> have \<open>M \<Turnstile>\<^sub>M pre ht \<longrightarrow> (\<Sigma>, [\<psi>\<leftarrow>snd M. \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M post ht\<close> unfolding satisfiable_base_def by simp
                        moreover from \<open>is_htb_basic ht\<close> have \<open>pre ht = \<phi>\<close> 
                          using fields unpack_sel(1) by fastforce
                        moreover from \<open>is_htb_basic ht\<close> have \<open>post ht = \<psi>\<close> 
                          using fields unpack_sel(2) by fastforce
                        ultimately have \<open>M \<Turnstile>\<^sub>M \<phi> \<longrightarrow> (\<Sigma>, [\<psi>\<leftarrow>snd M. \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M \<psi>\<close> by simp
                        then show \<open>M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> (\<Sigma>, [\<psi>\<leftarrow>snd M. \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M \<psi>\<close> by simp
                      qed
                    qed
                    with ex have \<open>(M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> ((SOME \<Sigma>. satisfiable_base M hts \<Sigma>), [\<psi>\<leftarrow>snd M. \<not> (SOME \<Sigma>. satisfiable_base M hts \<Sigma>) \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M \<psi>)\<close>
                      using someI2[where ?P=\<open>satisfiable_base M hts\<close>] by blast
                    ultimately have 
                      \<open>(M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> Some (SOME \<Sigma>. satisfiable_base M hts \<Sigma>) \<noteq> None) \<and>
                        (\<not> (fst M) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> \<not> (SOME \<Sigma>. satisfiable_base M hts \<Sigma>) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>) \<and>
                        (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> ((SOME \<Sigma>. satisfiable_base M hts \<Sigma>),  [\<psi>\<leftarrow>snd M. \<not> (SOME \<Sigma>. satisfiable_base M hts \<Sigma>) \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M \<psi>) \<and> 
                        (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close> 
                      using True by auto
                    moreover have \<open>((SOME \<Sigma>. satisfiable_base M hts \<Sigma>),  [\<psi>\<leftarrow>snd M. \<not> (SOME \<Sigma>. satisfiable_base M hts \<Sigma>) \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M \<psi> \<longrightarrow> the (\<M>* ?\<T> (basic n) M) \<Turnstile>\<^sub>M \<psi>\<close> 
                    proof (cases M)
                      case (Pair \<Sigma> \<Gamma>)
                      show ?thesis 
                      proof
                        assume entails: \<open>((SOME \<Sigma>. satisfiable_base M hts \<Sigma>),  [\<psi>\<leftarrow>snd M. \<not> (SOME \<Sigma>. satisfiable_base M hts \<Sigma>) \<^bold>\<Turnstile>\<^sub>P \<psi>]) \<Turnstile>\<^sub>M \<psi>\<close>
                        with nM Pair show \<open>the (\<M>* ?\<T> (basic n) M) \<Turnstile>\<^sub>M \<psi>\<close> by auto
                      qed
                    qed
                    ultimately have 
                      \<open>(M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> ?\<T> n M \<noteq> None) \<and>
                        (\<not> (fst M) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> ?\<T> n M \<noteq> None \<longrightarrow> \<not> the (?\<T> n M) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>) \<and>
                        (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M>* ?\<T> (basic n) M) \<Turnstile>\<^sub>M \<psi>) \<and> 
                        (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close> 
                      using nM by simp
                    then show ?thesis using complies_ht.simps by blast
                  next
                    case False
                    then have \<open>?\<T> n M = None\<close> by simp 
                    then have \<open>M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>\<close> 
                    proof -
                      from sat \<open>s \<in> set S\<close> False have 
                        \<open>\<forall>ht \<in> set hts. M \<Turnstile>\<^sub>M pre ht \<longrightarrow> M \<Turnstile>\<^sub>M post ht\<close> 
                        using f1 \<open>\<nabla>M\<close> unfolding satisfiable_def by fastforce
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
    is_ht_specification: \<open>is_ht_specification Sp\<close> and
    \<T>_complies: \<open>complies Sp \<T>\<close>

context single_agent_program begin

\<comment> \<open>Enabledness\<close> (* can this shorten other proofs? *)
lemma \<T>_None_ht_spec: \<open>\<nabla>M \<Longrightarrow> (a, \<Phi>, hts) \<in> set Sp \<Longrightarrow> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<Longrightarrow> \<T> a M = None\<close>
proof -
  assume \<open>(a, \<Phi>, hts) \<in> set Sp\<close>
  then have \<open>complies_hts (a, \<Phi>, hts) \<T>\<close> using \<T>_complies complies_def by simp
  then have \<open>\<forall>ht\<in>set hts. \<forall>M. \<nabla>M \<longrightarrow> complies_ht M \<T> \<Phi> (the (htb_basic_unpack ht))\<close> 
    unfolding complies_hts_def by simp
  then have \<open>\<forall>ht\<in>set hts. \<nabla>M \<longrightarrow> complies_ht M \<T> \<Phi> (the (htb_basic_unpack ht))\<close> by blast
  then have \<open>\<forall>ht\<in>set hts. \<nabla>M \<longrightarrow> (let (\<phi>, n, \<psi>) = the (htb_basic_unpack ht) in
    ((M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> \<T> n M \<noteq> None) \<and>
    (\<not> (fst M) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> \<T> n M \<noteq> None \<longrightarrow> \<not>the (\<T> n M) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>) \<and>
    (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M>* \<T> (basic n) M) \<Turnstile>\<^sub>M \<psi>) \<and>
    (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)))\<close> by fastforce
  then have \<open>\<forall>ht\<in>set hts. \<nabla>M \<longrightarrow> (let (\<phi>, n, \<psi>) = the (htb_basic_unpack ht) in M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> \<T> n M \<noteq> None)\<close>
    by auto
  moreover from is_ht_specification have \<open>hts \<noteq> [] \<and> (\<forall>ht\<in> set hts. fst (snd (the (htb_basic_unpack ht))) = a)\<close> 
    using \<open>(a, \<Phi>, hts) \<in> set Sp\<close> unfolding is_ht_specification_def by auto
  ultimately have \<open>hts \<noteq> []\<close> \<open>\<forall>ht\<in>set hts. \<nabla>M \<longrightarrow> (M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> \<T> a M \<noteq> None)\<close> by (simp, fastforce)
  then have \<open>\<nabla>M \<longrightarrow> (M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> \<T> a M \<noteq> None)\<close> by auto
  moreover assume \<open>M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi>\<close> \<open>\<nabla>M\<close>
  ultimately show \<open>\<T> a M = None\<close> by simp
qed

lemma not_enabled_ht_spec:
  assumes \<open>(a, \<Phi>, hts) \<in> set Sp\<close> 
      and \<open>\<^bold>\<Turnstile>\<^sub>M (\<psi> \<^bold>\<longrightarrow> \<^bold>\<not> \<Phi>)\<close>
    shows \<open>\<^bold>\<Turnstile>\<^sub>E (\<psi>\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb (basic a)))\<close>
proof
  fix M
  have \<open>mst_reachable_basic M \<longrightarrow> M \<Turnstile>\<^sub>M (\<psi> \<^bold>\<longrightarrow> \<^bold>\<not> \<Phi>)\<close> using assms(2) by blast
  have \<open>mst_reachable_basic M \<longrightarrow> M \<Turnstile>\<^sub>M \<psi> \<longrightarrow> M \<Turnstile>\<^sub>E \<^bold>\<not> (enabledb (basic a))\<close> 
  proof
    assume \<open>mst_reachable_basic M\<close>
    with assms(2) have \<open>M \<Turnstile>\<^sub>M (\<psi> \<^bold>\<longrightarrow> \<^bold>\<not> \<Phi>)\<close> by blast
    show \<open>M \<Turnstile>\<^sub>M \<psi> \<longrightarrow> M \<Turnstile>\<^sub>E \<^bold>\<not> (enabledb (basic a))\<close>
    proof
      assume \<open>M \<Turnstile>\<^sub>M \<psi>\<close>
      from mst_reachable_basic_is_mst have \<open>\<nabla>M\<close> using \<open>mst_reachable_basic M\<close> .
      then have \<open>\<T> a M = None\<close>
      proof (rule \<T>_None_ht_spec)
        from assms(1) show \<open>(a, \<Phi>, hts) \<in> set Sp\<close> .
        from \<open>M \<Turnstile>\<^sub>M \<psi>\<close> \<open>M \<Turnstile>\<^sub>M (\<psi> \<^bold>\<longrightarrow> \<^bold>\<not> \<Phi>)\<close> show \<open>M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi>\<close> by simp
      qed
      with bel_upd_not_enabled show \<open>M \<Turnstile>\<^sub>E \<^bold>\<not> (enabledb (basic a))\<close> by simp
    qed
  qed
  with transfer_semantics\<^sub>M show \<open>mst_reachable_basic M \<longrightarrow> M \<Turnstile>\<^sub>E (\<psi>\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not> (enabledb ((basic a))))\<close>
    using semantics\<^sub>P.simps(4) by metis
qed

subsection \<open>Proof System\<close>

\<comment> \<open>Derive (the) valid Hoare triples.\<close>

inductive derive\<^sub>H :: \<open>hoare_triple \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>H\<close>) where
  \<comment> \<open>Agent specific rule import\<close>
  import: \<open>(n, \<Phi>, hts) \<in> set Sp \<Longrightarrow> \<^bold>{ \<phi> \<^bold>} (basic n) \<^bold>{ \<psi> \<^bold>} \<in> set hts \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>} (basic n) \<^bold>{ \<psi> \<^bold>}\<close> |
  \<comment> \<open>Persistence of goals\<close>
  persist: \<open>\<not> is_drop a \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ G \<Phi> \<^bold>} a \<^bold>{ B \<Phi> \<^bold>\<or> G \<Phi> \<^bold>}\<close> |
  \<comment> \<open>Infeasible actions\<close>
  inf: \<open>\<^bold>\<Turnstile>\<^sub>E (\<phi>\<^sup>E \<^bold>\<longrightarrow> \<^bold>\<not>(enabledb a)) \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>} a \<^bold>{ \<phi> \<^bold>}\<close> |
  \<comment> \<open>Frame properties on beliefs for adopt and drop\<close>
  adoptB: \<open>\<turnstile>\<^sub>H \<^bold>{ B \<Phi> \<^bold>} (adopt \<psi>) \<^bold>{ B \<Phi> \<^bold>}\<close> |
  adoptNegB: \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not> (B \<Phi>) \<^bold>} (adopt \<psi>) \<^bold>{ \<^bold>\<not> (B \<Phi>) \<^bold>}\<close> |
  dropB: \<open>\<turnstile>\<^sub>H \<^bold>{ B \<Phi> \<^bold>} (drop \<psi>) \<^bold>{ B \<Phi> \<^bold>}\<close> |
  dropNegB: \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not> (B \<Phi>) \<^bold>} (drop \<psi>) \<^bold>{ \<^bold>\<not> (B \<Phi>) \<^bold>}\<close> |
  \<comment> \<open>Effects of adopt\<close>
  adoptBG: \<open>\<not> \<Turnstile>\<^sub>P (\<^bold>\<not> \<Phi>) \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not> (B \<Phi>) \<^bold>} (adopt \<Phi>) \<^bold>{ G \<Phi> \<^bold>}\<close> |
  \<comment> \<open>Non-effect of adopt\<close>
  adoptG: \<open>\<turnstile>\<^sub>H \<^bold>{ G \<Phi> \<^bold>} (adopt \<psi>) \<^bold>{ G \<Phi> \<^bold>}\<close> |
  adoptNegG: \<open>\<not> \<Turnstile>\<^sub>P (\<psi> \<^bold>\<longrightarrow> \<Phi>) \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not> (G \<Phi>) \<^bold>} (adopt \<psi>) \<^bold>{ \<^bold>\<not> (G \<Phi>) \<^bold>}\<close> |
  \<comment> \<open>Effects of drop\<close>
  dropG: \<open>\<Turnstile>\<^sub>P (\<Phi> \<^bold>\<longrightarrow> \<psi>) \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ G \<Phi> \<^bold>} (drop \<psi>) \<^bold>{ \<^bold>\<not> (G \<Phi>) \<^bold>}\<close> |
  \<comment> \<open>Non-effects of drop\<close>
  dropNegG: \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not>(G \<Phi>) \<^bold>} (drop \<psi>) \<^bold>{ \<^bold>\<not> (G \<Phi>) \<^bold>}\<close> |
  dropGCon: \<open>\<turnstile>\<^sub>H \<^bold>{ \<^bold>\<not>(G (\<Phi> \<^bold>\<and> \<psi>)) \<^bold>\<and> (G \<Phi>) \<^bold>} (drop \<psi>) \<^bold>{ G \<Phi> \<^bold>}\<close> |
  \<comment> \<open>Rule for conditional actions\<close>
  rCondAct: \<open>\<turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>\<and> \<psi> \<^bold>} a \<^bold>{ \<phi>' \<^bold>} \<Longrightarrow> \<^bold>\<Turnstile>\<^sub>M (\<phi> \<^bold>\<and> \<^bold>\<not>\<psi> \<^bold>\<longrightarrow> \<phi>') \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>} (\<psi> \<triangleright> do a) \<^bold>{ \<phi>' \<^bold>}\<close> |
  \<comment> \<open>Structural rules\<close>
  rImp: \<open>\<^bold>\<Turnstile>\<^sub>M (\<phi>' \<^bold>\<longrightarrow> \<phi>) \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>} a \<^bold>{ \<psi> \<^bold>} \<Longrightarrow> \<^bold>\<Turnstile>\<^sub>M (\<psi> \<^bold>\<longrightarrow> \<psi>') \<Longrightarrow> \<turnstile>\<^sub>H \<^bold>{ \<phi>' \<^bold>} a \<^bold>{ \<psi>' \<^bold>}\<close> |
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
  with import(1) have \<open>\<forall>ht\<in>set hts. is_htb_basic ht \<and> (\<forall>M. \<nabla>M \<longrightarrow> complies_ht M \<T> \<Phi> (the (htb_basic_unpack ht)))\<close> 
    unfolding complies_hts_def by auto
  with bspec have \<open>is_htb_basic ?ht \<and> (\<forall>M. \<nabla>M \<longrightarrow> complies_ht M \<T> \<Phi> (the (htb_basic_unpack ?ht)))\<close> 
    using import(2) .
  then have **: 
    \<open>\<forall>M. \<nabla>M \<longrightarrow> (M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> \<T> n M \<noteq> None) \<and>
         (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M>* \<T> (basic n) M) \<Turnstile>\<^sub>M \<psi>) \<and>
         (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close>
    by simp
  have *:
    \<open>\<forall>M. \<nabla>M \<longrightarrow> (M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> \<T> n M \<noteq> None) \<and>
         (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M \<psi>) \<and>
         (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close>
  proof 
    fix M
    show \<open>\<nabla>M \<longrightarrow> (M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> \<T> n M \<noteq> None) \<and>
          (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M \<psi>) \<and>
          (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close>
    proof 
      assume \<open>\<nabla>M\<close>
      show \<open>(M \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> \<T> n M \<noteq> None) \<and>
          (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M \<psi>) \<and>
          (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close>
      proof (cases M)
        case (Pair \<Sigma> \<Gamma>)
        with ** \<open>\<nabla>M\<close> have \<open>((\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> \<T> n M \<noteq> None) \<and>
           ((\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<phi> \<and> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M>* \<T> (basic n) M) \<Turnstile>\<^sub>M \<psi>) \<and>
           ((\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<phi> \<and> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<psi>)\<close> by simp
        then show ?thesis using Pair by simp
      qed
    qed
  qed
  have \<open>\<forall>M. \<nabla>M \<longrightarrow> (M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and> (enabledb ?a) \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M \<psi>) \<and> (M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and> \<^bold>\<not>(enabledb ?a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close>
  proof
    fix M
    show \<open>\<nabla>M \<longrightarrow> (M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and> (enabledb ?a) \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M \<psi>) \<and> (M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and> \<^bold>\<not>(enabledb ?a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close>
    proof 
      assume \<open>\<nabla>M\<close>
      with * have 
      \<open>(M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<Phi> \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M \<psi>) \<and>
       (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>M \<^bold>\<not> \<Phi> \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close> 
      by blast
      moreover have \<open>M \<Turnstile>\<^sub>E (enabledb ?a) \<longleftrightarrow> M \<Turnstile>\<^sub>M \<Phi>\<close> 
      proof (cases M)
        case (Pair \<Sigma> \<Gamma>)
        with * \<open>\<nabla>M\<close> have \<open>(\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>M \<Phi> \<longleftrightarrow> \<T> n (\<Sigma>, \<Gamma>) \<noteq> None\<close> by blast
        moreover have \<open>\<T> n (\<Sigma>, \<Gamma>) \<noteq> None \<longrightarrow> \<M> (basic n) (\<Sigma>, \<Gamma>) \<noteq> None\<close> by auto
        moreover have \<open>\<dots> \<longrightarrow> (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>E (enabledb ?a)\<close> using \<M>_some_Cap by fastforce
        ultimately show ?thesis using Pair by auto
      qed
      ultimately have 
        \<open>(M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>E (enabledb ?a) \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M \<psi>) \<and> 
         (M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>E \<^bold>\<not> (enabledb ?a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close> by simp
      then show \<open>(M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and> (enabledb ?a) \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M \<psi>) \<and> (M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and> \<^bold>\<not>(enabledb ?a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close>  
        using transfer_semantics\<^sub>M by simp
    qed
  qed
  with mst_reachable_basic_is_mst show ?case  by simp
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
            then have mst_unfold: \<open>\<M> (basic n) (\<Sigma>, \<Gamma>) = Some (\<Sigma>', [\<psi>\<leftarrow>\<Gamma>. \<not> \<Sigma>' \<^bold>\<Turnstile>\<^sub>P \<psi>])\<close>
                              (is \<open>\<M> (basic n) (\<Sigma>, \<Gamma>) = Some (\<Sigma>', ?\<Gamma>')\<close>) 
              by simp
            then show ?thesis 
            proof (cases \<open>\<Sigma>' \<^bold>\<Turnstile>\<^sub>P \<Phi>\<close>)
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
            have \<open>\<M> (adopt \<Phi>') (\<Sigma>, \<Gamma>) = (if \<not> \<Turnstile>\<^sub>P (\<^bold>\<not> \<Phi>') \<and> \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<Phi>' then Some (\<Sigma>, List.insert \<Phi>' \<Gamma>) else None)\<close> 
              by simp
            with notNone have \<open>\<M> (adopt \<Phi>') (\<Sigma>, \<Gamma>) = Some (\<Sigma>, List.insert \<Phi>' \<Gamma>)\<close> using adopt by metis
            then show ?thesis using adopt Pair asm by simp
          next 
            case (drop \<psi>)  
            with persist show ?thesis by simp
          qed
        qed
      qed simp 
    qed
  qed
  with semantics\<^sub>H.simps(1) show ?case using semantics\<^sub>P.simps(6) transfer_semantics\<^sub>M by blast
next
  case (inf \<phi> a)
  then have \<open>\<forall>M. mst_reachable_basic M \<longrightarrow> 
              (M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and>  (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<phi>) \<and> 
              (M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and> \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<phi>)\<close>
    using transfer_semantics\<^sub>M by auto  
  with mst_reachable_basic_is_mst show ?case by auto
next
  case (adoptB \<Phi> \<psi>)
  let ?\<phi> = \<open>B \<Phi>\<close> and ?\<phi>' = \<open>B \<Phi>\<close> and ?\<psi> = \<open>adopt \<psi>\<close>
  from adoptB have \<open>\<forall>M. (M \<Turnstile>\<^sub>E ?\<phi>\<^sup>E \<^bold>\<and> (enabledb ?\<psi>) \<longrightarrow> the (\<M> ?\<psi> M) \<Turnstile>\<^sub>M ?\<phi>') \<and> 
                          (M \<Turnstile>\<^sub>E ?\<phi>\<^sup>E \<^bold>\<and> \<^bold>\<not>(enabledb ?\<psi>) \<longrightarrow> M \<Turnstile>\<^sub>M ?\<phi>')\<close> by simp
  then show ?case by force
next
  case adoptNegB
  then show ?case by simp
next
  case dropB
  then show ?case by simp
next
  case dropNegB
  then show ?case by simp
next
  case (adoptBG \<Phi>)
  let ?\<phi> = \<open>\<^bold>\<not> (B \<Phi>)\<close> and ?\<psi> = \<open>G \<Phi>\<close> and ?a = \<open>adopt \<Phi>\<close>
  have \<open>\<forall>M. mst_reachable_basic M \<longrightarrow>
        (M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E) \<^bold>\<and>  (enabledb ?a) \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi>) \<and> 
        (M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E) \<^bold>\<and> \<^bold>\<not>(enabledb ?a) \<longrightarrow> M \<Turnstile>\<^sub>M ?\<psi>)\<close>
  proof
    fix M
    have \<open>M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E) \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi> \<and> M \<Turnstile>\<^sub>E enabledb ?a\<close>
    proof
      assume \<open>M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E)\<close>
      show \<open>the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi> \<and> M \<Turnstile>\<^sub>E enabledb ?a\<close>
      proof
        from \<open>M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E)\<close> show \<open>M \<Turnstile>\<^sub>E enabledb ?a\<close> using adoptBG adopt_Cap by (cases M) simp
        with \<open>M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E)\<close> adoptBG have s: \<open>\<M> ?a M = Some (fst M, List.insert \<Phi> (snd M))\<close> by (cases M) simp
        then have \<open>\<exists>\<gamma>\<in>set (snd (the (\<M> ?a M))). \<Turnstile>\<^sub>P (\<gamma> \<^bold>\<longrightarrow> \<Phi>)\<close> by simp
        moreover {
          from s have \<open>fst (the (\<M> ?a M)) = fst M\<close> by simp
          moreover have \<open>\<not> fst M \<^bold>\<Turnstile>\<^sub>P \<Phi>\<close> using \<open>M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E)\<close> by (cases M) simp
          ultimately have \<open>\<not> fst (the (\<M> ?a M)) \<^bold>\<Turnstile>\<^sub>P \<Phi>\<close> by simp
        }
        ultimately show \<open>the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi>\<close> 
          using semantics\<^sub>M'.simps(2)[where \<Sigma>=\<open>fst (the (\<M> ?a M))\<close> and \<Gamma>=\<open>snd (the (\<M> ?a M))\<close>] 
          by simp
      qed
    qed
    then show 
      \<open>mst_reachable_basic M \<longrightarrow> (M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E) \<^bold>\<and>  (enabledb ?a) \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi>) \<and> 
       (M \<Turnstile>\<^sub>E (?\<phi>\<^sup>E) \<^bold>\<and> \<^bold>\<not>(enabledb ?a) \<longrightarrow> M \<Turnstile>\<^sub>M ?\<psi>)\<close> 
      by auto
  qed
  then show ?case by simp
next
  case adoptG
  then show ?case by simp
next
  case adoptNegG
  then show ?case by simp
next
  case dropG
  with drop_Cap show ?case by auto
next
  case dropNegG
  with drop_Cap show ?case by simp
next
  case (dropGCon \<Phi> \<psi>)
  let ?\<phi> = \<open>\<^bold>\<not> (G (\<Phi> \<^bold>\<and> \<psi>)) \<^bold>\<and> (G \<Phi>)\<close> and ?\<psi> = \<open>G \<Phi>\<close> and ?a = \<open>drop \<psi>\<close>
  have \<open>\<forall>M. M \<Turnstile>\<^sub>M ?\<phi> \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi>\<close> 
  proof
    fix M
    show \<open>M \<Turnstile>\<^sub>M ?\<phi> \<longrightarrow> the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi>\<close>
    proof
      assume \<open>M \<Turnstile>\<^sub>M ?\<phi>\<close>      
      with dropGCon have pre:
        \<open>\<not> fst M \<^bold>\<Turnstile>\<^sub>P \<Phi> \<and> 
         \<not> (\<exists>\<gamma>\<in>set (snd M). \<Turnstile>\<^sub>P (\<gamma> \<^bold>\<longrightarrow> (\<Phi> \<^bold>\<and> \<psi>))) \<and> 
            (\<exists>\<gamma>\<in>set (snd M). \<Turnstile>\<^sub>P (\<gamma> \<^bold>\<longrightarrow> \<Phi>))\<close>  
        by (cases M) auto
      moreover from pre obtain \<gamma> where gamma: \<open>\<gamma> \<in> set (snd M) \<and> \<Turnstile>\<^sub>P (\<gamma> \<^bold>\<longrightarrow> \<Phi>)\<close> by auto
      moreover have aM: \<open>\<M> ?a M = Some (fst M, [\<gamma>\<leftarrow>snd M. \<not> [\<gamma>] \<^bold>\<Turnstile>\<^sub>P \<psi>])\<close> (is \<open>\<dots> = Some ?M'\<close>) 
        by (cases M) simp
      ultimately have \<open>\<not> fst ?M' \<^bold>\<Turnstile>\<^sub>P \<Phi>\<close> by simp
      moreover from pre gamma have \<open>\<not> [\<gamma>] \<^bold>\<Turnstile>\<^sub>P (\<Phi> \<^bold>\<and> \<psi>)\<close> by auto
      with gamma have \<open>\<exists>\<gamma>\<in>set (snd ?M'). \<Turnstile>\<^sub>P (\<gamma> \<^bold>\<longrightarrow> \<Phi>)\<close> by auto
      ultimately show \<open>the (\<M> ?a M) \<Turnstile>\<^sub>M ?\<psi>\<close> using aM by simp
    qed
  qed
  then show ?case by (meson semantics\<^sub>H.simps(1) semantics\<^sub>P.simps(6) transfer_semantics\<^sub>M)
next
  case (rCondAct \<phi> \<psi> a \<phi>')
  have \<open>\<forall> s \<in> Agent. \<forall>i. ((\<phi>\<^bold>[s i\<^bold>]\<^sub>M) \<and> (\<psi> \<triangleright> do a) = (act_nth s i) \<longrightarrow> (\<phi>'\<^bold>[s (i+1)\<^bold>]\<^sub>M))\<close>
  proof
    fix s
    assume \<open>s \<in> Agent\<close>
    show \<open>\<forall>i. ((\<phi>\<^bold>[s i\<^bold>]\<^sub>M) \<and> (\<psi> \<triangleright> do a) = (act_nth s i) \<longrightarrow> (\<phi>'\<^bold>[s (i+1)\<^bold>]\<^sub>M))\<close>
    proof
      fix i
      from mst_reachable_basic_trace have \<open>mst_reachable_basic (st_nth s i)\<close> using \<open>s \<in> Agent\<close> .
      with rCondAct have a:
        \<open>((\<phi> \<^bold>\<and> \<^bold>\<not>\<psi>) \<^bold>\<longrightarrow> \<phi>')\<^bold>[s i\<^bold>]\<^sub>M\<close> 
        \<open>(st_nth s i \<Turnstile>\<^sub>E ((\<phi> \<^bold>\<and> \<psi>)\<^sup>E) \<^bold>\<and>  (enabledb a) \<longrightarrow> the (\<M> a (st_nth s i)) \<Turnstile>\<^sub>M \<phi>') \<and>
         (st_nth s i \<Turnstile>\<^sub>E ((\<phi> \<^bold>\<and> \<psi>)\<^sup>E) \<^bold>\<and> \<^bold>\<not>(enabledb a) \<longrightarrow> st_nth s i \<Turnstile>\<^sub>M \<phi>')\<close>
        using rCondAct.hyps(2) semantics\<^sub>H.simps(1) by blast+
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
          moreover from this have \<open>st_nth s i \<Turnstile>\<^sub>E enabledb a\<close> using \<M>_some_Cap by simp
          ultimately show ?thesis using \<M>_suc_state \<open>s \<in> Agent\<close> bact a(2) 
            using snd_act_nth fst_act_nth transfer_semantics\<^sub>M by auto
        next
          case f: False
          moreover from \<open>s \<in> Agent\<close> have \<open>is_trace s\<close> unfolding Agent_def by simp
          ultimately have \<open>st_nth s i = st_nth s (i+1)\<close> using not_transition_eq bact by simp
          then show ?thesis
          proof (cases \<open>st_nth s i \<Turnstile>\<^sub>M \<psi>\<close>)
            case True
            then have \<open>\<not> ((enabledb a)\<^bold>[s i\<^bold>]\<^sub>E)\<close>
            proof -
              from \<open>is_trace s\<close> have 
                \<open>((st_nth s i) \<rightarrow>(act_nth s i) (st_nth s (i+1))) \<or> 
                \<not>(\<exists>M. ((st_nth s i) \<rightarrow>(act_nth s i) M)) \<and> (st_nth s i) = (st_nth s (i+1))\<close> 
                unfolding is_trace_def by simp
              with f True bact have \<open>\<not>(\<exists>M. ((st_nth s i) \<rightarrow>(\<psi> \<triangleright> do a) M))\<close> by auto
              moreover have \<open>(\<psi> \<triangleright> do a) \<in> \<Pi>\<close> using \<open>is_trace s\<close> bact trace_in_\<Pi> by force
              ultimately have \<open>\<not> (st_nth s i) \<Turnstile>\<^sub>M \<psi> \<or> \<M> a (st_nth s i) = None\<close> 
                unfolding transition_def by fastforce
              with True show \<open>\<not> ((enabledb a)\<^bold>[s i\<^bold>]\<^sub>E)\<close> by simp
            qed
            then have \<open>st_nth s i \<Turnstile>\<^sub>M \<phi>'\<close> using a pre transfer_semantics\<^sub>M by auto
            with \<open>st_nth s i = st_nth s (i+1)\<close> show ?thesis by simp
          next
            case False
            with bact have \<open>\<phi>'\<^bold>[s i\<^bold>]\<^sub>M\<close> using a(1) pre by auto
            with \<open>st_nth s i = st_nth s (i+1)\<close> show ?thesis by simp
          qed
        qed
      qed
    qed
  qed
  then show ?case by simp
next
  case (rImp \<phi>' \<phi> a \<psi> \<psi>')
  have 
    \<open>\<forall>M. mst_reachable_basic M \<longrightarrow>
      (M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>') \<and> 
      (M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>')\<close> 
  proof
    fix M
    show \<open>mst_reachable_basic M \<longrightarrow> 
          (M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>') \<and> 
          (M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>')\<close>
    proof
      assume \<open>mst_reachable_basic M\<close>
      show \<open>(M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>') \<and> 
            (M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>')\<close>
      proof
        show \<open>M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>'\<close> 
        proof
          assume pre: \<open>M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E (enabledb a)\<close>
          moreover from rImp(3) have \<open>M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>\<close> 
            using \<open>mst_reachable_basic M\<close> transfer_semantics\<^sub>M semantics\<^sub>H.simps(1) semantics\<^sub>P.simps(6) by blast
          moreover have \<open>M \<Turnstile>\<^sub>M \<phi>' \<^bold>\<longrightarrow> \<phi>\<close>  
            using \<open>mst_reachable_basic M\<close> rImp(1) by blast
          ultimately have \<open>the (\<M> a M) \<Turnstile>\<^sub>M \<psi>\<close> by simp
          moreover from pre have \<open>\<M> a M \<noteq> None\<close> by simp
          with mst_reachable_basic_\<M> have \<open>mst_reachable_basic (the (\<M> a M))\<close> 
            using \<open>mst_reachable_basic M\<close> unfolding mst_reachable_basic_def by simp
          with rImp have \<open>the (\<M> a M) \<Turnstile>\<^sub>M \<psi> \<^bold>\<longrightarrow> \<psi>'\<close> by blast
          ultimately show \<open>the (\<M> a M) \<Turnstile>\<^sub>M \<psi>'\<close> by simp
        qed
        show \<open>M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>'\<close>
        proof
          assume pre: \<open>M \<Turnstile>\<^sub>M \<phi>' \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a)\<close>
          from rImp(3) have \<open>M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>\<close> 
            using \<open>mst_reachable_basic M\<close> transfer_semantics\<^sub>M semantics\<^sub>H.simps(1) semantics\<^sub>P.simps(6) by blast
          moreover have \<open>M \<Turnstile>\<^sub>M \<phi>' \<^bold>\<longrightarrow> \<phi>\<close> 
            using \<open>mst_reachable_basic M\<close> rImp(1) by blast
          moreover have \<open>M \<Turnstile>\<^sub>M \<psi> \<^bold>\<longrightarrow> \<psi>'\<close>
            using \<open>mst_reachable_basic M\<close> rImp(4) by blast
          ultimately show \<open>M \<Turnstile>\<^sub>M \<psi>'\<close> using pre by simp
        qed
      qed
    qed
  qed
  with transfer_semantics\<^sub>M show ?case by simp
next
  case rCon
  then show ?case by simp
next
  case (rDis \<phi>\<^sub>1 a \<psi> \<phi>\<^sub>2)
  have 
    \<open>\<forall>M. mst_reachable_basic M \<longrightarrow> 
      (M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>) \<and> 
      (M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close>
  proof
    fix M
    show \<open>mst_reachable_basic M \<longrightarrow> 
            (M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>) \<and> 
            (M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close>
    proof
      assume \<open>mst_reachable_basic M\<close>
      show \<open>(M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>) \<and> 
            (M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>)\<close>
      proof
        show \<open>M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>\<close> 
        proof
          assume \<open>M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E (enabledb a)\<close> 
          moreover from rDis(2) have \<open>M \<Turnstile>\<^sub>M \<phi>\<^sub>1 \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>\<close>
            using \<open>mst_reachable_basic M\<close> transfer_semantics\<^sub>M semantics\<^sub>H.simps(1) semantics\<^sub>P.simps(6) by blast
          moreover from rDis(4) have \<open>M \<Turnstile>\<^sub>M \<phi>\<^sub>2 \<and> M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>\<close>
            using \<open>mst_reachable_basic M\<close> transfer_semantics\<^sub>M semantics\<^sub>H.simps(1) semantics\<^sub>P.simps(6) by blast
          ultimately show \<open>the (\<M> a M) \<Turnstile>\<^sub>M \<psi>\<close> by auto
        qed
        show \<open>M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>\<close>
        proof
          assume \<open>M \<Turnstile>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a)\<close> 
          moreover from rDis(2) have \<open>M \<Turnstile>\<^sub>M \<phi>\<^sub>1 \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>\<close>
            using \<open>mst_reachable_basic M\<close> transfer_semantics\<^sub>M semantics\<^sub>H.simps(1) semantics\<^sub>P.simps(6) by blast
          moreover from rDis(4) have \<open>M \<Turnstile>\<^sub>M \<phi>\<^sub>2 \<and> M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>\<close>
            using \<open>mst_reachable_basic M\<close> transfer_semantics\<^sub>M semantics\<^sub>H.simps(1) semantics\<^sub>P.simps(6) by blast
          ultimately show \<open>M \<Turnstile>\<^sub>M \<psi>\<close> by auto
        qed
      qed
    qed
  qed
  with transfer_semantics\<^sub>M show ?case by simp
qed

end

lemma is_ht_spec_single_agent_program:
  assumes \<open>\<Pi> \<noteq> {} \<and> \<nabla> M\<close>
      and \<open>is_ht_specification S\<close>
      and \<open>\<forall>a. (\<exists>\<phi>. (\<phi>, basic a) \<in> \<Pi>) \<longleftrightarrow> a \<in> set (map fst S)\<close>
    shows \<open>single_agent_program (SOME \<T>. complies S \<T>) \<Pi> M S\<close> (is \<open>single_agent_program ?\<T> \<Pi> M S\<close>) 
proof -                     
  from assms(2) have c: \<open>complies S ?\<T>\<close> using model_exists by (simp add: someI2_ex)
  moreover have \<open>single_agent ?\<T> \<Pi> M\<close>
  proof
    fix a \<Sigma> \<Gamma>
    show \<open>\<nabla>(\<Sigma>, \<Gamma>) \<longrightarrow> (\<exists>\<phi>. (\<phi>, basic a) \<in> \<Pi>) \<longrightarrow> \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> ?\<T> a (\<Sigma>, \<Gamma>) \<noteq> None \<longrightarrow> \<not> the (?\<T> a (\<Sigma>, \<Gamma>)) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close>
    proof 
      assume \<open>\<nabla>(\<Sigma>, \<Gamma>)\<close>
      show \<open>(\<exists>\<phi>. (\<phi>, basic a) \<in> \<Pi>) \<longrightarrow> \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> ?\<T> a (\<Sigma>, \<Gamma>) \<noteq> None \<longrightarrow> \<not> the (?\<T> a (\<Sigma>, \<Gamma>)) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close>
      proof
        assume \<open>\<exists>\<phi>. (\<phi>, basic a) \<in> \<Pi>\<close>
        with assms(3) have a: \<open>a \<in> set (map fst S)\<close> by simp
        then obtain \<Phi> hts where \<open>(a, \<Phi>, hts) \<in> set S\<close> by auto
        with assms(2) have \<open>complies_hts (a, \<Phi>, hts) ?\<T>\<close> using c unfolding complies_def by simp
        have \<open>\<forall>ht\<in>set hts. \<nabla>(\<Sigma>, \<Gamma>) \<longrightarrow> \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> ?\<T> a (\<Sigma>, \<Gamma>) \<noteq> None \<longrightarrow> \<not>the (?\<T> a (\<Sigma>, \<Gamma>)) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close>
        proof
          fix ht
          assume \<open>ht \<in> set hts\<close>
          with \<open>complies_hts (a, \<Phi>, hts) ?\<T>\<close> \<open>\<nabla>(\<Sigma>, \<Gamma>)\<close> assms(1) have \<open>complies_ht (\<Sigma>, \<Gamma>) ?\<T> \<Phi> (the (htb_basic_unpack ht))\<close> 
            (is \<open>complies_ht (\<Sigma>, \<Gamma>) ?\<T> \<Phi> ?ht\<close>)
            unfolding complies_hts_def by simp
          then have \<open>complies_ht (\<Sigma>, \<Gamma>) ?\<T> \<Phi> (fst ?ht, fst (snd ?ht), snd (snd ?ht))\<close> by simp
          then have \<open>(\<not> fst (\<Sigma>, \<Gamma>) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> ?\<T> (fst (snd ?ht)) (\<Sigma>, \<Gamma>) \<noteq> None \<longrightarrow> \<not>the (?\<T> (fst (snd ?ht)) (\<Sigma>, \<Gamma>)) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>)\<close> 
            using complies_ht.simps by blast
          moreover from assms(2) have \<open>fst (snd (the (htb_basic_unpack ht))) = a\<close> 
            using \<open>(a, \<Phi>, hts) \<in> set S\<close> \<open>ht \<in> set hts\<close> unfolding is_ht_specification_def by simp
          ultimately show \<open>\<nabla> (\<Sigma>, \<Gamma>) \<longrightarrow> \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> ?\<T> a (\<Sigma>, \<Gamma>) \<noteq> None \<longrightarrow> \<not>the (?\<T> a (\<Sigma>, \<Gamma>)) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> by simp
        qed
        with assms(2) \<open>\<nabla>(\<Sigma>, \<Gamma>)\<close> show \<open>\<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> ?\<T> a (\<Sigma>, \<Gamma>) \<noteq> None \<longrightarrow> \<not>the (?\<T> a (\<Sigma>, \<Gamma>)) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close>
          using \<open>(a, \<Phi>, hts) \<in> set S\<close> unfolding is_ht_specification_def by auto
      qed
    qed
    show \<open>?\<T> a (\<Sigma>, \<Gamma>) \<noteq> None \<longrightarrow> (\<exists>\<phi>. (\<phi>, basic a) \<in> \<Pi>)\<close> 
      using c assms(3) unfolding complies_def by auto
  qed (simp add: assms(1))
  ultimately show \<open>single_agent_program ?\<T> \<Pi> M S\<close> 
    using assms(2) single_agent_program_axioms.intro single_agent_program.intro by simp
qed    

end