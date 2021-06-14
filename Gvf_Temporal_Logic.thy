(*
  Goal verification framework
    - Temporal Logic
*)
\<comment> \<open>This theory ...\<close>

theory Gvf_Temporal_Logic imports Gvf_Agent_Specification begin

section \<open>Syntax\<close> 

datatype 'a \<Phi>\<^sub>T =
  Falsity (\<open>\<bottom>\<^sub>T\<close>) |
  Atom 'a |
  Negation \<open>'a \<Phi>\<^sub>T\<close> (\<open>\<not>\<^sub>T\<close>) | 
  Implication \<open>'a \<Phi>\<^sub>T\<close> \<open>'a \<Phi>\<^sub>T\<close> (infixr \<open>\<longrightarrow>\<^sub>T\<close> 60) | 
  Disjunction \<open>'a \<Phi>\<^sub>T\<close> \<open>'a \<Phi>\<^sub>T\<close> (infixl \<open>\<or>\<^sub>T\<close> 70) | 
  Conjunction \<open>'a \<Phi>\<^sub>T\<close> \<open>'a \<Phi>\<^sub>T\<close> (infixl \<open>\<and>\<^sub>T\<close> 80) |
  init |
  until \<open>'a \<Phi>\<^sub>T\<close> \<open>'a \<Phi>\<^sub>T\<close> (infix \<open>until\<close> 55)

\<comment> \<open>The type for temporal logic (mental state) formulas including enabledness.\<close>
type_synonym \<Phi>\<^sub>T\<^sub>E = \<open>Atom\<^sub>E \<Phi>\<^sub>T\<close>

\<comment> \<open>A number of other well known temporal operators can be defined in terms of the operator until.\<close> 

\<comment> \<open>Operator: always\<close>
definition always :: \<open>'a \<Phi>\<^sub>T \<Rightarrow> 'a \<Phi>\<^sub>T\<close> (\<open>\<box>\<close>) where
  \<open>\<box>\<phi> \<equiv> \<phi> until \<bottom>\<^sub>T\<close>

definition eventuality :: \<open>'a \<Phi>\<^sub>T \<Rightarrow> 'a \<Phi>\<^sub>T\<close> (\<open>\<diamondop>\<close>) where
  \<open>\<diamondop>\<phi> \<equiv> \<not>\<^sub>T (\<box> (\<not>\<^sub>T\<phi>))\<close>

\<comment> \<open>Operator: unless\<close>
definition unless :: \<open>'a \<Phi>\<^sub>T \<Rightarrow> 'a \<Phi>\<^sub>T \<Rightarrow> 'a \<Phi>\<^sub>T\<close> (infix \<open>unless\<close> 55) where
  \<open>\<phi> unless \<psi> \<equiv> \<phi> \<longrightarrow>\<^sub>T (\<phi> until \<psi>)\<close>

fun to_\<Phi>\<^sub>T :: \<open>'a \<Phi>\<^sub>P \<Rightarrow> 'a \<Phi>\<^sub>T\<close> (\<open>_\<^sup>T\<close> [100]) where
  \<open>(\<Phi>\<^sub>P.Atom x)\<^sup>T = Atom x\<close> |
  \<open>(\<^bold>\<not> p)\<^sup>T = (\<not>\<^sub>T (p\<^sup>T))\<close> |
  \<open>(p \<^bold>\<longrightarrow> q)\<^sup>T = (p\<^sup>T \<longrightarrow>\<^sub>T q\<^sup>T)\<close> |
  \<open>(p \<^bold>\<or> q)\<^sup>T = (p\<^sup>T \<or>\<^sub>T q\<^sup>T)\<close> |
  \<open>(p \<^bold>\<and> q)\<^sup>T = (p\<^sup>T \<and>\<^sub>T q\<^sup>T)\<close>

section \<open>Semantics\<close>

context single_agent_program begin

fun semantics\<^sub>T :: \<open>trace \<Rightarrow> nat \<Rightarrow> \<Phi>\<^sub>T\<^sub>E \<Rightarrow> bool\<close> (\<open>_, _ \<Turnstile>\<^sub>T\<close> [50]) where
  \<open>s, i \<Turnstile>\<^sub>T \<bottom>\<^sub>T = False\<close> |
  \<open>s, i \<Turnstile>\<^sub>T (Atom x) = ((\<Phi>\<^sub>P.Atom x)\<^bold>[s i\<^bold>]\<^sub>E)\<close> |
  \<open>s, i \<Turnstile>\<^sub>T (\<not>\<^sub>T p) = (\<not> (s, i \<Turnstile>\<^sub>T p))\<close> |
  \<open>s, i \<Turnstile>\<^sub>T (p \<longrightarrow>\<^sub>T q) = ((s, i \<Turnstile>\<^sub>T p) \<longrightarrow> (s, i \<Turnstile>\<^sub>T q))\<close> |
  \<open>s, i \<Turnstile>\<^sub>T (p \<or>\<^sub>T q) = ((s, i \<Turnstile>\<^sub>T p) \<or> (s, i \<Turnstile>\<^sub>T q))\<close> |
  \<open>s, i \<Turnstile>\<^sub>T (p \<and>\<^sub>T q) = ((s, i \<Turnstile>\<^sub>T p) \<and> (s, i \<Turnstile>\<^sub>T q))\<close> |
  \<open>s, i \<Turnstile>\<^sub>T init = (i = 0)\<close> |
  \<open>s, i \<Turnstile>\<^sub>T (\<phi> until \<psi>) = ((\<exists> j \<ge> i. s, j \<Turnstile>\<^sub>T \<psi> \<and> (\<forall>k \<ge> i. j > k \<longrightarrow> s, k \<Turnstile>\<^sub>T \<phi>)) \<or> (\<forall>k \<ge> i. s, k \<Turnstile>\<^sub>T \<phi>))\<close>

lemma sem\<^sub>T\<^sub>E_equiv: \<open>(\<forall>M. semantics\<^sub>E M p) \<longleftrightarrow> (\<forall>s i. (p\<^bold>[s i\<^bold>]\<^sub>E))\<close> 
  using st_nth.simps(1) by metis

lemma sem\<^sub>T\<^sub>E_equiv2: \<open>s, i \<Turnstile>\<^sub>T (p\<^sup>T) \<longleftrightarrow> (p\<^bold>[s i\<^bold>]\<^sub>E)\<close> 
  by (induct p) auto

lemma \<open>(\<forall>M. semantics\<^sub>E M p) \<longleftrightarrow> (\<forall>s i. s, i \<Turnstile>\<^sub>T (p\<^sup>T))\<close> using sem\<^sub>T\<^sub>E_equiv sem\<^sub>T\<^sub>E_equiv2 by simp

abbreviation semantics_trace\<^sub>T\<^sub>E :: \<open>trace set \<Rightarrow> \<Phi>\<^sub>T\<^sub>E \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>T#\<close> 50) where
  \<open>S \<Turnstile>\<^sub>T# \<phi> \<equiv> \<forall>s\<in>S. \<forall>i. (s, i \<Turnstile>\<^sub>T \<phi>)\<close>

section \<open>Relations between Hoare Logic and Temporal Logic\<close>

subsection \<open>Unless\<close>

\<comment> \<open>Theorem 4.15\<close>
theorem unless_ht: \<open>(\<forall>b \<in> \<Pi>. (\<Turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>\<and> \<^bold>\<not> \<psi> \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ \<phi> \<^bold>\<or> \<psi> \<^bold>})) \<longleftrightarrow> Agent \<Turnstile>\<^sub>T# \<phi>\<^sup>E\<^sup>T unless \<psi>\<^sup>E\<^sup>T\<close>
proof
  assume *: \<open>\<forall>b \<in> \<Pi>. (\<Turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>\<and> \<^bold>\<not> \<psi> \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ \<phi> \<^bold>\<or> \<psi> \<^bold>})\<close>
  show \<open>Agent \<Turnstile>\<^sub>T# \<phi>\<^sup>E\<^sup>T unless \<psi>\<^sup>E\<^sup>T\<close> (is \<open>Agent \<Turnstile>\<^sub>T# ?\<phi> unless ?\<psi>\<close>)
  proof (rule ccontr)
    assume \<open>\<not> Agent \<Turnstile>\<^sub>T# ?\<phi> unless ?\<psi>\<close>
    then obtain s i where \<open>\<not> (s, i \<Turnstile>\<^sub>T (?\<phi> unless ?\<psi>))\<close> \<open>s \<in> Agent\<close> by auto
    then have \<open>s, i \<Turnstile>\<^sub>T ?\<phi>\<close> \<open>\<not> (s, i \<Turnstile>\<^sub>T (?\<phi> until ?\<psi>))\<close> unfolding unless_def by simp_all
    then have \<open>\<not>(\<exists> j \<ge> i. s, j \<Turnstile>\<^sub>T ?\<psi>) \<and> (\<exists>k \<ge> i. s, k \<Turnstile>\<^sub>T (\<not>\<^sub>T ?\<phi>)) \<or> (\<exists> j > i. s, j \<Turnstile>\<^sub>T ?\<psi>) \<and> (\<forall> j > i. s, j \<Turnstile>\<^sub>T ?\<psi> \<longrightarrow> \<not>(\<forall>k \<ge> i. j > k \<longrightarrow> s, k \<Turnstile>\<^sub>T ?\<phi>))\<close> by auto
    then show False 
    proof
      assume a: \<open>\<not> (\<exists>j\<ge>i. s, j \<Turnstile>\<^sub>T ?\<psi>) \<and> (\<exists>k\<ge>i. s, k \<Turnstile>\<^sub>T (\<not>\<^sub>T ?\<phi>))\<close>
      let ?P = \<open>\<lambda>x. x \<ge> i \<and> s, x \<Turnstile>\<^sub>T (\<not>\<^sub>T ?\<phi>)\<close>
      have \<open>\<not> ?P 0\<close> using \<open>s, i \<Turnstile>\<^sub>T ?\<phi>\<close> by fastforce
      moreover obtain n where \<open>?P n\<close> using a by auto
      ultimately have \<open>\<exists>k\<le>n. (\<forall>i<k. \<not> ?P i) \<and> ?P k\<close> using ex_least_nat_le[where P=\<open>?P\<close>] by simp
      then obtain k where Pk: \<open>k \<le> n \<and> (\<forall>i<k. \<not> ?P i) \<and> ?P k\<close> by auto
      moreover from this have \<open>k > i\<close> using \<open>s, i \<Turnstile>\<^sub>T ?\<phi>\<close> by fastforce
      ultimately have \<open>\<not> ?P (k - 1)\<close> by simp
      with \<open>k > i\<close> have \<open>s, k - 1 \<Turnstile>\<^sub>T (?\<phi> \<and>\<^sub>T \<not>\<^sub>T ?\<psi>)\<close> using a by simp
      then have \<open>st_nth s (k - 1) \<Turnstile>\<^sub>M \<phi> \<^bold>\<and> \<^bold>\<not> \<psi>\<close> by (simp add: sem\<^sub>T\<^sub>E_equiv2 transfer_semantics\<^sub>M)
      moreover have \<open>?P k\<close> using Pk by simp
      then have \<open>s, k \<Turnstile>\<^sub>T (\<not>\<^sub>T ?\<phi> \<and>\<^sub>T \<not>\<^sub>T ?\<psi>)\<close> using a \<open>k > i\<close> by simp
      then have \<open>st_nth s k \<Turnstile>\<^sub>M \<^bold>\<not> \<phi> \<^bold>\<and> \<^bold>\<not> \<psi>\<close> by (simp add: sem\<^sub>T\<^sub>E_equiv2 transfer_semantics\<^sub>M)
      moreover obtain b where \<open>(fst b, snd b) = act_nth s (k - 1)\<close> by simp
      moreover from this have \<open>b \<in> \<Pi>\<close> using \<open>s \<in> Agent\<close> trace_in_\<Pi> unfolding Agent_def by simp
      with * have \<open>\<forall> s \<in> Agent. \<forall>i. ((\<phi> \<^bold>\<and> \<^bold>\<not> \<psi>)\<^bold>[s i\<^bold>]\<^sub>M) \<and> ((fst b) \<triangleright> do (snd b)) = (act_nth s i) \<longrightarrow> ((\<phi> \<^bold>\<or> \<psi>)\<^bold>[s (i+1)\<^bold>]\<^sub>M)\<close>
        using semantics\<^sub>H.simps(2) by blast
      then have \<open>((\<phi> \<^bold>\<and> \<^bold>\<not> \<psi>)\<^bold>[s (k-1)\<^bold>]\<^sub>M) \<and> ((fst b) \<triangleright> do (snd b)) = (act_nth s (k-1)) \<longrightarrow> ((\<phi> \<^bold>\<or> \<psi>)\<^bold>[s ((k-1)+1)\<^bold>]\<^sub>M)\<close> 
        using \<open>s \<in> Agent\<close> by simp
      with \<open>k > i\<close> have \<open>((\<phi> \<^bold>\<and> \<^bold>\<not> \<psi>)\<^bold>[s (k-1)\<^bold>]\<^sub>M) \<and> ((fst b) \<triangleright> do (snd b)) = (act_nth s (k-1)) \<longrightarrow> ((\<phi> \<^bold>\<or> \<psi>)\<^bold>[s k\<^bold>]\<^sub>M)\<close> 
        by simp
      ultimately show False by simp
    next
      assume a: \<open>(\<exists> j > i. s, j \<Turnstile>\<^sub>T ?\<psi>) \<and> (\<forall> j > i. s, j \<Turnstile>\<^sub>T ?\<psi> \<longrightarrow> \<not>(\<forall>k \<ge> i. j > k \<longrightarrow> s, k \<Turnstile>\<^sub>T ?\<phi>))\<close>
      let ?P = \<open>\<lambda>x. x > i \<and> s, x \<Turnstile>\<^sub>T ?\<psi>\<close>
      have \<open>\<not> ?P 0\<close> by simp
      moreover obtain n where \<open>?P n\<close> using a by auto
      ultimately have \<open>\<exists>k\<le>n. (\<forall>i<k. \<not> ?P i) \<and> ?P k\<close> using ex_least_nat_le[where P=\<open>?P\<close>] by simp
      then obtain k where Pk: \<open>k \<le> n \<and> (\<forall>i<k. \<not> ?P i) \<and> ?P k\<close> by auto
      let ?P' = \<open>\<lambda>x. i < x \<and> x < k \<and> \<not> s, x \<Turnstile>\<^sub>T ?\<phi>\<close>
      have \<open>\<not> ?P' 0\<close> by simp
      moreover obtain n' where \<open>?P' n'\<close> using Pk \<open>s, i \<Turnstile>\<^sub>T ?\<phi>\<close> le_neq_trans a by blast
      ultimately have \<open>\<exists>j\<le>n'. (\<forall>i<j. \<not> ?P' i) \<and> ?P' j\<close> using ex_least_nat_le[where P=\<open>?P'\<close>] by simp
      then obtain j where Pj: \<open>j \<le> n' \<and> (\<forall>i<j. \<not> ?P' i) \<and> ?P' j\<close> by auto
      then have \<open>\<not> ?P' (j - 1)\<close> by simp
      moreover have \<open>j - 1 < k\<close> using Pj by auto
      ultimately have \<open>s, j - 1 \<Turnstile>\<^sub>T ?\<phi>\<close> 
      proof (cases \<open>i < j - 1\<close>)
        case False
        then have \<open>i = j - 1\<close> using Pj by auto
        with \<open>s, i \<Turnstile>\<^sub>T ?\<phi>\<close> show ?thesis by simp
      qed simp
      moreover have \<open>\<not> ?P (j - 1)\<close> using Pk \<open>j - 1 < k\<close> by blast
      then have \<open>s, j - 1 \<Turnstile>\<^sub>T (\<not>\<^sub>T ?\<psi>)\<close>
      proof (cases \<open>i < j - 1\<close>)
        case False
        then have \<open>i = j - 1\<close> using Pj by auto
        with \<open>\<not> s, i \<Turnstile>\<^sub>T (?\<phi> until ?\<psi>)\<close> show ?thesis by fastforce
      qed simp
      ultimately have \<open>s, j - 1 \<Turnstile>\<^sub>T (?\<phi> \<and>\<^sub>T \<not>\<^sub>T ?\<psi>)\<close> by simp
      then have \<open>st_nth s (j - 1) \<Turnstile>\<^sub>M \<phi> \<^bold>\<and> \<^bold>\<not> \<psi>\<close> by (simp add: sem\<^sub>T\<^sub>E_equiv2 transfer_semantics\<^sub>M)
      moreover 
      {
        have \<open>\<not> s, j \<Turnstile>\<^sub>T ?\<phi>\<close> using Pj by simp
        moreover have \<open>j < k\<close> using Pj by simp
        then have \<open>\<not> ?P j\<close> using Pk by simp
        then have \<open>\<not> s, j \<Turnstile>\<^sub>T ?\<psi>\<close> using Pj by simp
        ultimately have \<open>s, j \<Turnstile>\<^sub>T (\<not>\<^sub>T ?\<phi> \<and>\<^sub>T \<not>\<^sub>T ?\<psi>)\<close> by simp
        then have \<open>st_nth s j \<Turnstile>\<^sub>M \<^bold>\<not> \<phi> \<^bold>\<and> \<^bold>\<not> \<psi>\<close> by (simp add: sem\<^sub>T\<^sub>E_equiv2 transfer_semantics\<^sub>M)
      }
      moreover obtain b where \<open>(fst b, snd b) = act_nth s (j - 1)\<close> by simp
      moreover from this have \<open>b \<in> \<Pi>\<close> using \<open>s \<in> Agent\<close> trace_in_\<Pi> unfolding Agent_def by simp
      with * have \<open>\<forall> s \<in> Agent. \<forall>i. ((\<phi> \<^bold>\<and> \<^bold>\<not> \<psi>)\<^bold>[s i\<^bold>]\<^sub>M) \<and> ((fst b) \<triangleright> do (snd b)) = (act_nth s i) \<longrightarrow> ((\<phi> \<^bold>\<or> \<psi>)\<^bold>[s (i+1)\<^bold>]\<^sub>M)\<close>
        using semantics\<^sub>H.simps(2) by blast
      then have \<open>((\<phi> \<^bold>\<and> \<^bold>\<not> \<psi>)\<^bold>[s (j-1)\<^bold>]\<^sub>M) \<and> ((fst b) \<triangleright> do (snd b)) = (act_nth s (j-1)) \<longrightarrow> ((\<phi> \<^bold>\<or> \<psi>)\<^bold>[s ((j-1)+1)\<^bold>]\<^sub>M)\<close> 
        using \<open>s \<in> Agent\<close> by simp
      with Pj have \<open>((\<phi> \<^bold>\<and> \<^bold>\<not> \<psi>)\<^bold>[s (j-1)\<^bold>]\<^sub>M) \<and> ((fst b) \<triangleright> do (snd b)) = (act_nth s (j-1)) \<longrightarrow> ((\<phi> \<^bold>\<or> \<psi>)\<^bold>[s j\<^bold>]\<^sub>M)\<close> 
        by simp
      ultimately show False by simp
    qed
  qed
next
  assume \<open>Agent \<Turnstile>\<^sub>T# \<phi>\<^sup>E\<^sup>T unless \<psi>\<^sup>E\<^sup>T\<close> (is \<open>Agent \<Turnstile>\<^sub>T# ?\<phi> unless ?\<psi>\<close>)
  show \<open>\<forall>b \<in> \<Pi>. (\<Turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>\<and> \<^bold>\<not> \<psi> \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ \<phi> \<^bold>\<or> \<psi> \<^bold>})\<close>
  proof 
    fix b
    assume \<open>b \<in> \<Pi>\<close>
    show \<open>\<Turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>\<and> \<^bold>\<not> \<psi> \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ \<phi> \<^bold>\<or> \<psi> \<^bold>}\<close>
    proof -
      have \<open>\<forall> s \<in> Agent. \<forall>i. ((\<phi> \<^bold>\<and> \<^bold>\<not> \<psi>)\<^bold>[s i\<^bold>]\<^sub>M) \<and> ((fst b) \<triangleright> do (snd b)) = (act_nth s i) \<longrightarrow> ((\<phi> \<^bold>\<or> \<psi>)\<^bold>[s (i+1)\<^bold>]\<^sub>M)\<close> 
      proof
        fix s
        assume \<open>s \<in> Agent\<close>
        show \<open>\<forall>i. ((\<phi> \<^bold>\<and> \<^bold>\<not> \<psi>)\<^bold>[s i\<^bold>]\<^sub>M) \<and> ((fst b) \<triangleright> do (snd b)) = (act_nth s i) \<longrightarrow> ((\<phi> \<^bold>\<or> \<psi>)\<^bold>[s (i+1)\<^bold>]\<^sub>M)\<close>
        proof
          fix i
          show \<open>((\<phi> \<^bold>\<and> \<^bold>\<not> \<psi>)\<^bold>[s i\<^bold>]\<^sub>M) \<and> ((fst b) \<triangleright> do (snd b)) = (act_nth s i) \<longrightarrow> ((\<phi> \<^bold>\<or> \<psi>)\<^bold>[s (i+1)\<^bold>]\<^sub>M)\<close>
          proof (cases \<open>st_nth s i \<Turnstile>\<^sub>M \<phi>\<close>)
            case True
            then have \<open>s, i \<Turnstile>\<^sub>T ?\<phi>\<close> by (simp add: sem\<^sub>T\<^sub>E_equiv2 transfer_semantics\<^sub>M)
            with \<open>Agent \<Turnstile>\<^sub>T# ?\<phi> unless ?\<psi>\<close> have \<open>s, i \<Turnstile>\<^sub>T (?\<phi> until ?\<psi>)\<close> using \<open>s \<in> Agent\<close> unfolding unless_def by simp
            then have \<open>(\<exists> j \<ge> i. (s, j \<Turnstile>\<^sub>T ?\<psi>) \<and> (\<forall>k \<ge> i. j > k \<longrightarrow> (s, k \<Turnstile>\<^sub>T ?\<phi>))) \<or> (\<forall>k \<ge> i. (s, k \<Turnstile>\<^sub>T ?\<phi>))\<close> by simp
            then obtain j where *: \<open>(j \<ge> i \<and> s, j \<Turnstile>\<^sub>T ?\<psi> \<and> (\<forall>k \<ge> i. j > k \<longrightarrow> s, k \<Turnstile>\<^sub>T ?\<phi>)) \<or> s, i + 1 \<Turnstile>\<^sub>T ?\<phi>\<close> by auto
            then show ?thesis
            proof (cases \<open>j > i + 1\<close>)
              case True
              with * have \<open>s, (i + 1) \<Turnstile>\<^sub>T ?\<phi>\<close> by auto
              then have \<open>st_nth s (i + 1) \<Turnstile>\<^sub>M \<phi> \<^bold>\<or> \<psi>\<close> by (simp add: sem\<^sub>T\<^sub>E_equiv2 transfer_semantics\<^sub>M)
              then show ?thesis by simp
            next
              case False
              with * have **: \<open>s, i \<Turnstile>\<^sub>T ?\<psi> \<or> s, i + 1 \<Turnstile>\<^sub>T ?\<psi> \<or> s, i + 1 \<Turnstile>\<^sub>T ?\<phi>\<close>
                by (metis discrete order.not_eq_order_implies_strict)
              then show ?thesis
              proof (cases \<open>st_nth s i \<Turnstile>\<^sub>M \<psi>\<close>)
                case False
                then have \<open>\<not> s, i \<Turnstile>\<^sub>T ?\<psi>\<close> by (simp add: sem\<^sub>T\<^sub>E_equiv2 transfer_semantics\<^sub>M)
                with ** have \<open>s, i + 1 \<Turnstile>\<^sub>T ?\<psi> \<or> s, i + 1 \<Turnstile>\<^sub>T ?\<phi>\<close> by simp
                then show ?thesis using sem\<^sub>T\<^sub>E_equiv2 transfer_semantics\<^sub>M by auto
              qed simp
            qed
          qed simp
        qed
      qed
      then show ?thesis using semantics\<^sub>H.simps(2) by blast
    qed
  qed
qed

subsection \<open>Ensures\<close>

definition ensures :: \<open>'a \<Phi>\<^sub>T \<Rightarrow> 'a \<Phi>\<^sub>T \<Rightarrow> 'a \<Phi>\<^sub>T\<close> (infix \<open>ensures\<close> 55) where
  \<open>\<phi> ensures \<psi> \<equiv> (\<phi> unless \<psi>) \<and>\<^sub>T (\<phi> \<longrightarrow>\<^sub>T \<diamondop>\<psi>)\<close>

\<comment> \<open>Theorem 4.16\<close>
theorem ex_ensures:
  assumes \<open>\<forall>b \<in> \<Pi>. (\<Turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>\<and> \<^bold>\<not> \<psi> \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ \<phi> \<^bold>\<or> \<psi> \<^bold>})\<close> 
      and \<open>\<exists>b \<in> \<Pi>. (\<Turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>\<and> \<^bold>\<not> \<psi> \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ \<psi> \<^bold>})\<close>
    shows \<open>Agent \<Turnstile>\<^sub>T# \<phi>\<^sup>E\<^sup>T ensures \<psi>\<^sup>E\<^sup>T\<close> (is \<open>Agent \<Turnstile>\<^sub>T# ?\<phi> ensures ?\<psi>\<close>)
proof
  fix s
  assume \<open>s \<in> Agent\<close>
  show \<open>\<forall>i. s, i \<Turnstile>\<^sub>T (?\<phi> ensures ?\<psi>)\<close>
  proof 
    fix i
    have \<open>\<forall>i. s, i \<Turnstile>\<^sub>T (?\<phi> unless ?\<psi>)\<close> using assms(1) \<open>s \<in> Agent\<close> unless_ht by simp
    moreover have \<open>s, i \<Turnstile>\<^sub>T (?\<phi> \<longrightarrow>\<^sub>T \<diamondop> ?\<psi>)\<close>
    proof -
      have \<open>fair_trace s\<close> using \<open>s \<in> Agent\<close> unfolding Agent_def by simp
      show ?thesis   
      proof (rule ccontr)
        assume negev: \<open>\<not> s, i \<Turnstile>\<^sub>T (?\<phi> \<longrightarrow>\<^sub>T \<diamondop> ?\<psi>)\<close>
        then have \<open>s, i \<Turnstile>\<^sub>T (?\<phi> \<and>\<^sub>T \<not>\<^sub>T ?\<psi>) \<and> (\<forall>j > i. s, j \<Turnstile>\<^sub>T (\<not>\<^sub>T ?\<psi>))\<close> 
          unfolding eventuality_def always_def by simp
        with negev \<open>\<forall>i. s, i \<Turnstile>\<^sub>T (?\<phi> unless ?\<psi>)\<close> have \<open>\<forall>j > i. s, j \<Turnstile>\<^sub>T (?\<phi> \<and>\<^sub>T \<not>\<^sub>T ?\<psi>)\<close> 
          unfolding unless_def always_def eventuality_def by auto
        moreover 
        {
          from assms(2) obtain b where \<open>b \<in> \<Pi> \<and> (\<forall>i. ((\<phi> \<^bold>\<and> \<^bold>\<not> \<psi>)\<^bold>[s i\<^bold>]\<^sub>M) \<and> ((fst b) \<triangleright> do (snd b)) = (act_nth s i) \<longrightarrow> (\<psi>\<^bold>[s (i+1)\<^bold>]\<^sub>M))\<close> 
            using \<open>s \<in> Agent\<close> by fastforce
          then have \<open>b \<in> \<Pi> \<and> (\<forall>j > i. ((\<phi> \<^bold>\<and> \<^bold>\<not> \<psi>)\<^bold>[s j\<^bold>]\<^sub>M) \<and> ((fst b) \<triangleright> do (snd b)) = (act_nth s j) \<longrightarrow> (\<psi>\<^bold>[s (j+1)\<^bold>]\<^sub>M))\<close> 
            by auto
          moreover from this have \<open>\<exists>j > i. ((fst b) \<triangleright> do (snd b)) = (act_nth s j)\<close> 
            using \<open>fair_trace s\<close> unfolding fair_trace_def by fastforce
          ultimately have \<open>\<exists>j > i. ((\<phi> \<^bold>\<and> \<^bold>\<not> \<psi>)\<^bold>[s j\<^bold>]\<^sub>M) \<longrightarrow> (\<psi>\<^bold>[s (j+1)\<^bold>]\<^sub>M)\<close> by auto
          moreover from \<open>\<forall>j > i. s, j \<Turnstile>\<^sub>T (?\<phi> \<and>\<^sub>T \<not>\<^sub>T ?\<psi>)\<close> have \<open>\<forall>j > i. ((\<phi> \<^bold>\<and> \<^bold>\<not> \<psi>)\<^bold>[s j\<^bold>]\<^sub>M)\<close> 
            using sem\<^sub>T\<^sub>E_equiv2 transfer_semantics\<^sub>M by simp
          ultimately have \<open>\<exists>j > i. (\<psi>\<^bold>[s (j+1)\<^bold>]\<^sub>M)\<close> by auto
        }
      ultimately show False using sem\<^sub>T\<^sub>E_equiv2 transfer_semantics\<^sub>M by auto
      qed
    qed
    ultimately show \<open>s, i \<Turnstile>\<^sub>T (?\<phi> ensures ?\<psi>)\<close> by (simp add: ensures_def)
  qed
qed

subsection \<open>Leads to operator\<close>

fun disL:: \<open>'a \<Phi>\<^sub>T list \<Rightarrow> 'a \<Phi>\<^sub>T\<close> where
  \<open>disL [] = \<bottom>\<^sub>T\<close> |
  \<open>disL (\<phi> # \<phi>\<^sub>L) = \<phi> \<or>\<^sub>T disL \<phi>\<^sub>L\<close>

inductive leads_to :: \<open>\<Phi>\<^sub>T\<^sub>E \<Rightarrow> \<Phi>\<^sub>T\<^sub>E \<Rightarrow> bool\<close> (infix \<open>\<mapsto>\<close> 55) where
  ensures: \<open>\<forall>s i. s, i \<Turnstile>\<^sub>T (\<phi> ensures \<psi>) \<Longrightarrow> \<phi> \<mapsto> \<psi>\<close> |
  imp: \<open>\<phi> \<mapsto> \<chi> \<Longrightarrow> \<chi> \<mapsto> \<psi> \<Longrightarrow> \<phi> \<mapsto> \<psi>\<close> |
  disj: \<open>\<forall>\<phi> \<in> set \<phi>\<^sub>L. \<phi> \<mapsto> \<psi> \<Longrightarrow> disL \<phi>\<^sub>L \<mapsto> \<psi>\<close>

\<comment> \<open>Lemma 4.18\<close>
lemma \<open>\<phi> \<mapsto> \<psi> \<Longrightarrow> s, i \<Turnstile>\<^sub>T (\<phi> \<longrightarrow>\<^sub>T \<diamondop>\<psi>)\<close>
proof (induct arbitrary: i rule: leads_to.inducts)
  case (ensures \<phi> \<psi>)
  then show ?case unfolding ensures_def always_def eventuality_def by simp
next
  case (imp \<phi> \<chi> \<psi>)
  then have \<open>s, i \<Turnstile>\<^sub>T \<phi> \<longrightarrow> s, i \<Turnstile>\<^sub>T (\<diamondop> \<chi>)\<close> by simp
  moreover have \<open>s, i \<Turnstile>\<^sub>T (\<diamondop> \<chi>) \<longrightarrow> (\<exists>j \<ge> i. s, j \<Turnstile>\<^sub>T \<chi>)\<close> 
    unfolding eventuality_def always_def by simp
  then have \<open>s, i \<Turnstile>\<^sub>T (\<diamondop> \<chi>) \<longrightarrow> (\<exists>j \<ge> i. s, j \<Turnstile>\<^sub>T \<psi>)\<close> using imp(4) unfolding eventuality_def always_def
    using order_trans by fastforce
  then have \<open>s, i \<Turnstile>\<^sub>T (\<diamondop> \<chi>) \<longrightarrow> s, i \<Turnstile>\<^sub>T (\<diamondop> \<psi>)\<close> by (simp add: eventuality_def always_def)
  ultimately have \<open>s, i \<Turnstile>\<^sub>T \<phi> \<longrightarrow> s, i \<Turnstile>\<^sub>T (\<diamondop> \<psi>)\<close> by simp
  then show ?case by simp
next
  case (disj \<phi>\<^sub>L \<psi>)
  then show ?case by (induct \<phi>\<^sub>L) simp_all
qed

end
end