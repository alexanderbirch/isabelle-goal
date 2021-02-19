(*

  Goal verification framework
    - Hoare Logic
  
  This theory sets up the reasoning about programs using Hoare triples.
  We give the syntax and semantics of Hoare triples, given an agent.
  We prove a relation between Hoare triples for basic and conditional actions.

*)
theory Gvf_Hoare_Logic imports Gvf_Actions Gvf_Hoare_Logic_Core begin

section \<open>Syntax\<close>

\<comment> \<open>Hoare triples for basic and conditional actions, respectively\<close>
datatype hoare_triple = htb (pre: \<Phi>\<^sub>M) (actb: cap) (post: \<Phi>\<^sub>M) | htc (pre: \<Phi>\<^sub>M) (actc: cond_act) (post: \<Phi>\<^sub>M)

\<comment> \<open>Introduce the usual notation\<close>
syntax
  "_hoare_triple_cond" :: \<open>\<Phi>\<^sub>M \<Rightarrow> \<Phi>\<^sub>M \<Rightarrow> cap \<Rightarrow> \<Phi>\<^sub>M \<Rightarrow> hoare_triple\<close>  ("\<^bold>{_\<^bold>} _ \<triangleright> do _ \<^bold>{_\<^bold>}")
  "_hoare_triple_basic" :: \<open>\<Phi>\<^sub>M \<Rightarrow> cap \<Rightarrow> \<Phi>\<^sub>M \<Rightarrow> hoare_triple\<close>  ("\<^bold>{_\<^bold>} _ \<^bold>{_\<^bold>}")
translations
  "\<^bold>{ \<phi> \<^bold>} (\<upsilon> \<triangleright> do b) \<^bold>{ \<psi> \<^bold>}" \<rightharpoonup> "hoare_triple.htc \<phi> (\<upsilon>, b) \<psi>"
  "\<^bold>{ \<phi> \<^bold>} a \<^bold>{ \<psi> \<^bold>}" \<rightharpoonup>  "hoare_triple.htb \<phi> a \<psi>"

context single_agent
begin

\<comment> \<open>Mental state formula evaluated in state\<close>
abbreviation mst_in_state\<^sub>E :: \<open>\<Phi>\<^sub>E \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool\<close> (\<open>_\<^bold>[_ _\<^bold>]\<^sub>E\<close>) where
  \<open>\<phi>\<^bold>[s i\<^bold>]\<^sub>E \<equiv> st_nth s i \<Turnstile>\<^sub>E \<phi>\<close>
abbreviation mst_in_state\<^sub>M :: \<open>\<Phi>\<^sub>M \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool\<close> (\<open>_\<^bold>[_ _\<^bold>]\<^sub>M\<close>) where
  \<open>\<phi>\<^bold>[s i\<^bold>]\<^sub>M \<equiv> st_nth s i \<Turnstile>\<^sub>M \<phi>\<close>

section \<open>Semantics\<close>

fun semantics\<^sub>H :: \<open>hoare_triple \<Rightarrow> bool\<close> (\<open>\<Turnstile>\<^sub>H\<close>) where
\<comment> \<open>Basic action\<close>
  \<open>\<Turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>} a \<^bold>{ \<psi> \<^bold>} = (\<forall>M. (M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and>  (enabledb a) \<longrightarrow> the (\<M> a M) \<Turnstile>\<^sub>M \<psi>) \<and> 
                            (M \<Turnstile>\<^sub>E (\<phi>\<^sup>E) \<^bold>\<and> \<^bold>\<not>(enabledb a) \<longrightarrow> M \<Turnstile>\<^sub>M \<psi>))\<close> | 
\<comment> \<open>Conditional action\<close>
  \<open>\<Turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>} (\<upsilon> \<triangleright> do b) \<^bold>{ \<psi> \<^bold>} = (\<forall> s \<in> Agent. \<forall>i. ((\<phi>\<^bold>[s i\<^bold>]\<^sub>M) \<and> (\<upsilon> \<triangleright> do b) = (act_nth s i) \<longrightarrow> (\<psi>\<^bold>[s (i+1)\<^bold>]\<^sub>M)))\<close>

\<comment> \<open>Lemma 4.3\<close>
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
      let ?M = \<open>st_nth s i\<close>
      and ?M' = \<open>st_nth s (i+1)\<close>
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
          moreover have \<open>(?M \<Turnstile>\<^sub>E ((\<phi> \<^bold>\<and> \<psi>)\<^sup>E) \<^bold>\<and> (enabledb a) \<longrightarrow> the (\<M> a ?M) \<Turnstile>\<^sub>M \<phi>')
                        \<and> (?M \<Turnstile>\<^sub>E ((\<phi> \<^bold>\<and> \<psi>)\<^sup>E) \<^bold>\<and> \<^bold>\<not>(enabledb a) \<longrightarrow> ?M \<Turnstile>\<^sub>M \<phi>')\<close>
            using assms(1) semantics\<^sub>H.simps(1) by blast 
          ultimately have *: \<open>(?M \<Turnstile>\<^sub>E (enabledb a) \<longrightarrow> the (\<M> a ?M) \<Turnstile>\<^sub>M \<phi>')
                        \<and> (?M \<Turnstile>\<^sub>E \<^bold>\<not>(enabledb a) \<longrightarrow> ?M \<Turnstile>\<^sub>M \<phi>')\<close> by simp
          show ?thesis
          proof (cases \<open>?M \<Turnstile>\<^sub>E enabledb a\<close>)
            case enabled: True
            with * have \<open>the (\<M> a ?M) \<Turnstile>\<^sub>M \<phi>'\<close> by simp
            moreover from enabled have \<open>\<M> a ?M \<noteq> None\<close> by (cases a) simp_all
            ultimately show \<open>?M' \<Turnstile>\<^sub>M \<phi>'\<close> using \<M>_suc_state \<open>s \<in> Agent\<close> \<open>?b = act_nth s i\<close> by simp
          next
            case not_enabled: False
            with * have \<open>?M \<Turnstile>\<^sub>M \<phi>'\<close> by simp
            moreover have \<open>\<M> a ?M = None\<close>
            proof (cases a)
              case (basic n)
              moreover from \<open>is_trace s\<close> have \<open>act_nth s i \<in> \<Pi>\<close> using trace_in_\<Pi> by simp
              ultimately have \<open>(\<psi>, (basic n)) \<in> \<Pi>\<close> using \<open>?b = act_nth s i\<close> by simp
              then have \<open>n \<in> Cap\<close> unfolding Cap_def by auto
              moreover have \<open>\<not>(n \<in> Cap \<and> \<M> a ?M \<noteq> None)\<close> using basic not_enabled by fastforce
              ultimately show ?thesis by blast
            next
              case (adopt \<Phi>)
              with not_enabled have \<open>\<not> \<M> (adopt \<Phi>) ?M \<noteq> None\<close> using \<open>?b = act_nth s i\<close> by simp
              with adopt show ?thesis by blast 
            next
              case (drop \<Phi>)
              with not_enabled have \<open>\<not> \<M> (drop \<Phi>) ?M \<noteq> None\<close> using \<open>?b = act_nth s i\<close> by simp
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

end
end