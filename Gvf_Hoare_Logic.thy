(*
  Goal verification framework
    - Hoare Logic
*)
  
\<comment> \<open>This theory sets up the reasoning about programs using Hoare triples.
    We give the syntax and semantics of Hoare triples, given an agent.
    We prove a relation between Hoare triples for basic and conditional actions.\<close>

theory Gvf_Hoare_Logic imports Gvf_Actions begin

section \<open>Syntax\<close>

\<comment> \<open>Hoare triples for basic and conditional actions, respectively.\<close>
datatype hoare_triple = htb (pre: \<Phi>\<^sub>M) cap (post: \<Phi>\<^sub>M) | htc \<Phi>\<^sub>M cond_act \<Phi>\<^sub>M

\<comment> \<open>Is basic Hoare triple?\<close>
fun is_htb_basic :: \<open>hoare_triple \<Rightarrow> bool\<close> where
  \<open>is_htb_basic (htb _ (basic _) _) = True\<close> |
  \<open>is_htb_basic _ = False\<close>

\<comment> \<open>Unpack basic Hoare triple fields into an optional triple.\<close>
fun htb_basic_unpack :: \<open>hoare_triple \<Rightarrow> (\<Phi>\<^sub>M \<times> Bcap \<times> \<Phi>\<^sub>M) option\<close> where
  \<open>htb_basic_unpack (htb \<phi> (basic n) \<psi>) = Some (\<phi>, n, \<psi>)\<close> |
  \<open>htb_basic_unpack _ = None\<close>

\<comment> \<open>Unpacking gives some value if the Hoare triple is for basic actions.\<close>
lemma htb_unpack_some: \<open>is_htb_basic ht = (\<exists>t. htb_basic_unpack ht = Some t)\<close>
proof (induct)
  case (htb \<phi> n \<psi>)
  then show ?case by (cases n) simp_all 
qed simp

\<comment> \<open>Link first and third field of the unpacking triple to the selectors defined for the datatype.\<close>
lemma unpack_sel:
  assumes \<open>is_htb_basic ht\<close>
  shows \<open>fst (the (htb_basic_unpack ht)) = pre ht\<close>
    and \<open>snd (snd (the (htb_basic_unpack ht))) = post ht\<close>
  using assms htb_basic_unpack.simps(1) is_htb_basic.elims(2) option.sel
  by (metis fst_conv hoare_triple.sel(1), metis snd_conv hoare_triple.sel(3))

\<comment> \<open>Notation for Hoare triples.\<close>
syntax
  "_hoare_triple_cond" :: \<open>\<Phi>\<^sub>M \<Rightarrow> \<Phi>\<^sub>M \<Rightarrow> cap \<Rightarrow> \<Phi>\<^sub>M \<Rightarrow> hoare_triple\<close>  ("\<^bold>{_\<^bold>} _ \<triangleright> do _ \<^bold>{_\<^bold>}")
  "_hoare_triple_basic" :: \<open>\<Phi>\<^sub>M \<Rightarrow> cap \<Rightarrow> \<Phi>\<^sub>M \<Rightarrow> hoare_triple\<close>  ("\<^bold>{_\<^bold>} _ \<^bold>{_\<^bold>}")
translations
  "\<^bold>{ \<phi> \<^bold>} (\<upsilon> \<triangleright> do b) \<^bold>{ \<psi> \<^bold>}" \<rightharpoonup> "hoare_triple.htc \<phi> (\<upsilon>, b) \<psi>"
  "\<^bold>{ \<phi> \<^bold>} a \<^bold>{ \<psi> \<^bold>}" \<rightharpoonup>  "hoare_triple.htb \<phi> a \<psi>"

\<comment> \<open>Start single_agent context block. Proofs, definitions etc. only apply for this context.\<close>
context single_agent
begin

\<comment> \<open>Notation for mental state formula evaluated in state.\<close>
\<comment> \<open>Mental state formulas with enabled.\<close>
abbreviation mst_in_state\<^sub>E :: \<open>\<Phi>\<^sub>E \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool\<close> (\<open>_\<^bold>[_ _\<^bold>]\<^sub>E\<close>) where
  \<open>\<phi>\<^bold>[s i\<^bold>]\<^sub>E \<equiv> st_nth s i \<Turnstile>\<^sub>E \<phi>\<close>
\<comment> \<open>Mental state formulas without enabled.\<close>
abbreviation mst_in_state\<^sub>M :: \<open>\<Phi>\<^sub>M \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool\<close> (\<open>_\<^bold>[_ _\<^bold>]\<^sub>M\<close>) where
  \<open>\<phi>\<^bold>[s i\<^bold>]\<^sub>M \<equiv> st_nth s i \<Turnstile>\<^sub>M \<phi>\<close>

section \<open>Semantics\<close>

\<comment> \<open>Semantics of Hoare triples is not evaluated in a specific state but for the agent.\<close>
fun semantics\<^sub>H :: \<open>hoare_triple \<Rightarrow> bool\<close> (\<open>\<Turnstile>\<^sub>H\<close>) where
\<comment> \<open>Basic action. Precondition holds and enabled => evaluate in successor state; else same state.\<close>
  \<open>\<Turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>} a \<^bold>{ \<psi> \<^bold>} = (\<forall>M. mst_reachable_basic M \<longrightarrow>
                             (M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and>  (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>) \<and> 
                             (M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and> \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>))\<close> | 
\<comment> \<open>Conditional action. If \<upsilon> \<triangleright> do b is conditional action i in the trace and the precondition holds
    in state i, then the postcondition must hold in state i+1.\<close>
  \<open>\<Turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>} (\<upsilon> \<triangleright> do b) \<^bold>{ \<psi> \<^bold>} = (\<forall> s \<in> Agent. \<forall>i. ((\<phi>\<^bold>[s i\<^bold>]\<^sub>M) \<and> (\<upsilon> \<triangleright> do b) = (act_nth s i) \<longrightarrow> (\<psi>\<^bold>[s (i+1)\<^bold>]\<^sub>M)))\<close>

\<comment> \<open>Example.\<close>
lemma \<open>\<Turnstile>\<^sub>H \<^bold>{ p \<^bold>\<or> \<^bold>\<not> p \<^bold>} a \<^bold>{ p \<^bold>\<or> \<^bold>\<not> p \<^bold>}\<close> by simp
lemma \<open>\<Turnstile>\<^sub>H \<^bold>{ p \<^bold>\<or> \<^bold>\<not> p \<^bold>} (\<upsilon> \<triangleright> do b) \<^bold>{ p \<^bold>\<or> \<^bold>\<not> p \<^bold>}\<close> by simp

\<comment> \<open>Lemma 4.3: Hoare triple for conditional action from basic action.\<close>
lemma hoare_triple_cond_from_basic: 
  assumes \<open>\<Turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>\<and> \<psi> \<^bold>} a \<^bold>{ \<phi>' \<^bold>}\<close> 
      and \<open>\<forall> s \<in> Agent. \<forall>i. st_nth s i \<Turnstile>\<^sub>M (\<phi> \<^bold>\<and> \<^bold>\<not>\<psi>) \<^bold>\<longrightarrow> \<phi>'\<close> 
    shows \<open>\<Turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>} (\<psi> \<triangleright> do a) \<^bold>{ \<phi>' \<^bold>}\<close>
proof -
  have \<open>\<forall> s \<in> Agent. \<forall>i. (\<phi>\<^bold>[s i\<^bold>]\<^sub>M \<and> (\<psi> \<triangleright> do a) = (act_nth s i) \<longrightarrow> (\<phi>'\<^bold>[s (i+1)\<^bold>]\<^sub>M))\<close>
  (is \<open>\<forall> s \<in> Agent. \<forall>i. (\<phi>\<^bold>[s i\<^bold>]\<^sub>M \<and> ?b = (act_nth s i) \<longrightarrow> (\<phi>'\<^bold>[s (i+1)\<^bold>]\<^sub>M))\<close>)
  proof
    fix s
    assume \<open>s \<in> Agent\<close>
    then have \<open>is_trace s\<close> unfolding Agent_def by simp
    show \<open>\<forall>i. (\<phi>\<^bold>[s i\<^bold>]\<^sub>M \<and> ?b = act_nth s i \<longrightarrow> (\<phi>'\<^bold>[s (i+1)\<^bold>]\<^sub>M))\<close> 
    proof
      fix i
      let ?M = \<open>st_nth s i\<close> and ?M' = \<open>st_nth s (i+1)\<close>
      show \<open>\<phi>\<^bold>[s i\<^bold>]\<^sub>M \<and> ?b = act_nth s i \<longrightarrow> (\<phi>'\<^bold>[s (i+1)\<^bold>]\<^sub>M)\<close>
      proof
        assume \<open>\<phi>\<^bold>[s i\<^bold>]\<^sub>M \<and> ?b = act_nth s i\<close>
        with conjunct2 have \<open>?b = act_nth s i\<close> .
        show \<open>\<phi>'\<^bold>[s (i+1)\<^bold>]\<^sub>M\<close>
        proof (cases \<open>\<psi>\<^bold>[s i\<^bold>]\<^sub>M\<close>)
          case \<phi>: True
          from \<open>\<phi>\<^bold>[s i\<^bold>]\<^sub>M \<and> ?b = act_nth s i\<close> have \<open>?M \<Turnstile>\<^sub>M \<phi>\<close> by simp
          moreover from \<phi> have \<open>?M \<Turnstile>\<^sub>M \<psi>\<close> by simp
          ultimately have \<open>?M \<Turnstile>\<^sub>E ((\<phi> \<^bold>\<and> \<psi>)\<^sup>E)\<close> using transfer_semantics\<^sub>M by simp
          moreover from mst_reachable_basic_trace have \<open>mst_reachable_basic ?M\<close> using \<open>s \<in> Agent\<close> by auto          
          then have \<open>(?M \<Turnstile>\<^sub>E ((\<phi> \<^bold>\<and> \<psi>)\<^sup>E) \<^bold>\<and> (enabledb a) \<longrightarrow> the (\<M> a ?M) \<Turnstile>\<^sub>M \<phi>')
                                \<and> (?M \<Turnstile>\<^sub>E ((\<phi> \<^bold>\<and> \<psi>)\<^sup>E) \<^bold>\<and> \<^bold>\<not>(enabledb a) \<longrightarrow> ?M \<Turnstile>\<^sub>M \<phi>')\<close>
            using assms(1) semantics\<^sub>H.simps(1) by blast
          ultimately have *: \<open>(?M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a ?M) \<Turnstile>\<^sub>M \<phi>')
                        \<and> (?M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> ?M \<Turnstile>\<^sub>M \<phi>')\<close> by simp
          show ?thesis
          proof (cases \<open>?M \<Turnstile>\<^sub>E enabledb a\<close>)
            case enabled: True
            with * have \<open>the (\<M> a ?M) \<Turnstile>\<^sub>M \<phi>'\<close> by simp
            moreover from enabled have \<open>\<M> a ?M \<noteq> None\<close> by (cases a) simp_all
            ultimately show \<open>?M' \<Turnstile>\<^sub>M \<phi>'\<close> using \<M>_suc_state \<open>s \<in> Agent\<close> \<open>?b = act_nth s i\<close> 
              using snd_act_nth by fastforce
          next
            case not_enabled: False
            with * have \<open>?M \<Turnstile>\<^sub>M \<phi>'\<close> by simp
            moreover have \<open>\<M> a ?M = None\<close>
            proof (cases a)
              case (basic n)
              with not_enabled have \<open>\<not> ((enabledb (basic n))\<^bold>[s i\<^bold>]\<^sub>E)\<close> by simp
              with semantics\<^sub>E'.simps(3) have \<open>\<not> \<M> (basic n) ?M \<noteq> None\<close> using \<M>_some_Cap by fastforce
              then have \<open>\<M> (basic n) ?M = None\<close> by blast
              with basic show ?thesis by simp
            next
              case (adopt \<Phi>)
              with not_enabled have \<open>\<not> \<M> (adopt \<Phi>) ?M \<noteq> None\<close> using \<open>?b = act_nth s i\<close> adopt_Cap by simp
              with adopt show ?thesis by blast 
            next
              case (drop \<Phi>)
              with not_enabled have \<open>\<not> \<M> (drop \<Phi>) ?M \<noteq> None\<close> using \<open>?b = act_nth s i\<close> drop_Cap by simp
              with drop show ?thesis by blast
            qed
            then have \<open>\<not>(?M \<rightarrow>?b ?M')\<close> unfolding transition_def by simp
            with \<open>is_trace s\<close> \<open>?b = act_nth s i\<close> have \<open>?M' = ?M\<close> using not_transition_eq by metis
            ultimately show ?thesis by simp
          qed
        next
          case not_\<phi>: False 
          then have \<open>\<not> (?M \<rightarrow>?b ?M')\<close> unfolding transition_def by simp
          with \<open>is_trace s\<close> \<open>?b = act_nth s i\<close> have \<open>?M' = ?M\<close> using not_transition_eq by metis
          moreover from assms(2) have \<open>?M \<Turnstile>\<^sub>M (\<phi> \<^bold>\<and> \<^bold>\<not>\<psi>) \<^bold>\<longrightarrow> \<phi>'\<close> using \<open>s \<in> Agent\<close> by simp
          with not_\<phi> \<open>\<phi>\<^bold>[s i\<^bold>]\<^sub>M \<and> ?b = act_nth s i\<close> have \<open>?M \<Turnstile>\<^sub>M \<phi>'\<close> by simp
          ultimately show ?thesis by simp
        qed
      qed
    qed
  qed
  then show ?thesis by simp
qed

lemma mst_basic_trace_ht_invariant:
  assumes \<open>\<forall>a\<in>Cap. \<Turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>} a \<^bold>{ \<phi> \<^bold>}\<close> 
      and \<open>M\<^sub>0 \<Turnstile>\<^sub>M \<phi>\<close>
    shows \<open>\<^bold>\<Turnstile>\<^sub>M \<phi>\<close>
proof
  fix M
  show \<open>mst_reachable_basic M \<longrightarrow> M \<Turnstile>\<^sub>M \<phi>\<close>
  proof 
    assume \<open>mst_reachable_basic M\<close>
    then obtain S where *: \<open>mst_basic_trace S M\<^sub>0 = M\<close> unfolding mst_reachable_basic_def by auto
    moreover have \<open>mst_basic_trace S M\<^sub>0 \<Turnstile>\<^sub>M \<phi>\<close>
    proof (induct S)
      case Nil
      with assms(2) show ?case by simp
    next
      case (Cons a S')
      let ?M = \<open>mst_basic_trace S' M\<^sub>0\<close>
      show ?case
      proof (cases \<open>\<M> a ?M\<close>)
        case None
        with Cons show ?thesis by simp
      next
        case Some
        with \<M>_some_Cap have \<open>a \<in> Cap\<close> by blast
        with assms(1) have \<open>?M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and> (enabledb a) \<longrightarrow> the (\<M> a ?M) \<Turnstile>\<^sub>M \<phi>\<close> 
          using mst_reachable_basic_def semantics\<^sub>H.simps(1) by blast
        moreover from semantics\<^sub>E'.simps(3) have \<open>?M \<Turnstile>\<^sub>E enabledb a\<close> using \<open>a \<in> Cap\<close> Some * by simp
        ultimately have \<open>?M \<Turnstile>\<^sub>M \<phi> \<longrightarrow> the (\<M> a ?M) \<Turnstile>\<^sub>M \<phi>\<close> using transfer_semantics\<^sub>M by simp
        with Cons have \<open>the (\<M> a ?M) \<Turnstile>\<^sub>M \<phi>\<close> by simp
        with Some show ?thesis by simp
      qed
    qed
    ultimately show \<open>M \<Turnstile>\<^sub>M \<phi>\<close> by simp
  qed
qed

end
end
