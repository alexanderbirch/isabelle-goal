(*
  Goal verification framework
    - Temporal Logic
*)
\<comment> \<open>This theory ...\<close>

theory Gvf_Temporal_Logic imports Gvf_Agent_Specification begin

section \<open>Syntax\<close> 

datatype 'a \<Phi>\<^sub>T =
  Atom 'a |
  Negation \<open>'a \<Phi>\<^sub>T\<close> (\<open>\<not>\<^sub>T\<close>) | 
  Implication \<open>'a \<Phi>\<^sub>T\<close> \<open>'a \<Phi>\<^sub>T\<close> (infixr \<open>\<longrightarrow>\<^sub>T\<close> 60) | 
  Disjunction \<open>'a \<Phi>\<^sub>T\<close> \<open>'a \<Phi>\<^sub>T\<close> (infixl \<open>\<or>\<^sub>T\<close> 70) | 
  Conjunction \<open>'a \<Phi>\<^sub>T\<close> \<open>'a \<Phi>\<^sub>T\<close> (infixl \<open>\<and>\<^sub>T\<close> 80) |
  init |
  until \<open>'a \<Phi>\<^sub>T\<close> \<open>'a \<Phi>\<^sub>T\<close> (infix \<open>until\<close> 55)

\<comment> \<open>The type for temporal logic (mental state) formulas including enabledness.\<close>
type_synonym \<Phi>\<^sub>T\<^sub>E = \<open>Atom\<^sub>E \<Phi>\<^sub>T\<close>

\<comment> \<open>Operator: unless\<close>
abbreviation unless :: \<open>'a \<Phi>\<^sub>T \<Rightarrow> 'a \<Phi>\<^sub>T \<Rightarrow> 'a \<Phi>\<^sub>T\<close> (infix \<open>unless\<close> 55) where
  \<open>\<phi> unless \<psi> \<equiv> \<phi> \<longrightarrow>\<^sub>T (\<phi> until \<psi>)\<close>

fun to_\<Phi>\<^sub>T :: \<open>'a \<Phi>\<^sub>P \<Rightarrow> 'a \<Phi>\<^sub>T\<close> (\<open>_\<^sup>T\<close> [100]) where
  \<open>(\<Phi>\<^sub>P.Atom x)\<^sup>T = Atom x\<close> |
  \<open>(\<^bold>\<not> p)\<^sup>T = (\<not>\<^sub>T (p\<^sup>T))\<close> |
  \<open>(p \<^bold>\<longrightarrow> q)\<^sup>T = (p\<^sup>T \<longrightarrow>\<^sub>T q\<^sup>T)\<close> |
  \<open>(p \<^bold>\<or> q)\<^sup>T = (p\<^sup>T \<or>\<^sub>T q\<^sup>T)\<close> |
  \<open>(p \<^bold>\<and> q)\<^sup>T = (p\<^sup>T \<and>\<^sub>T q\<^sup>T)\<close>

context single_agent_program begin

fun semantics\<^sub>T :: \<open>trace \<Rightarrow> nat \<Rightarrow> \<Phi>\<^sub>T\<^sub>E \<Rightarrow> bool\<close> (\<open>_, _ \<Turnstile>\<^sub>T\<close> [50]) where
  \<open>s, i \<Turnstile>\<^sub>T (Atom x) = ((\<Phi>\<^sub>P.Atom x)\<^bold>[s i\<^bold>]\<^sub>E)\<close> |
  \<open>s, i \<Turnstile>\<^sub>T (\<not>\<^sub>T p) = (\<not> (s, i \<Turnstile>\<^sub>T p))\<close> |
  \<open>s, i \<Turnstile>\<^sub>T (p \<longrightarrow>\<^sub>T q) = ((s, i \<Turnstile>\<^sub>T p) \<longrightarrow> (s, i \<Turnstile>\<^sub>T q))\<close> |
  \<open>s, i \<Turnstile>\<^sub>T (p \<or>\<^sub>T q) = ((s, i \<Turnstile>\<^sub>T p) \<or> (s, i \<Turnstile>\<^sub>T q))\<close> |
  \<open>s, i \<Turnstile>\<^sub>T (p \<and>\<^sub>T q) = ((s, i \<Turnstile>\<^sub>T p) \<and> (s, i \<Turnstile>\<^sub>T q))\<close> |
  \<open>s, i \<Turnstile>\<^sub>T init = (i = 0)\<close> |
  \<open>s, i \<Turnstile>\<^sub>T (\<phi> until \<psi>) = ((\<exists> j \<ge> i. (s, j \<Turnstile>\<^sub>T \<psi>) \<and> (\<forall>k \<ge> i. j > k \<longrightarrow> (s, k \<Turnstile>\<^sub>T \<phi>))) \<or> (\<forall>k \<ge> i. (s, k \<Turnstile>\<^sub>T \<phi>)))\<close>

lemma sem\<^sub>T\<^sub>E_equiv: \<open>(\<forall>M. semantics\<^sub>E M p) \<longleftrightarrow> (\<forall>s i. (p\<^bold>[s i\<^bold>]\<^sub>E))\<close> 
  using st_nth.simps(1) by metis

lemma sem\<^sub>T\<^sub>E_equiv2: \<open>s, i \<Turnstile>\<^sub>T (p\<^sup>T) \<longleftrightarrow> (p\<^bold>[s i\<^bold>]\<^sub>E)\<close> 
  by (induct p) auto

lemma \<open>(\<forall>M. semantics\<^sub>E M p) \<longleftrightarrow> (\<forall>s i. s, i \<Turnstile>\<^sub>T (p\<^sup>T))\<close> using sem\<^sub>T\<^sub>E_equiv sem\<^sub>T\<^sub>E_equiv2 by simp

abbreviation semantics_trace\<^sub>T\<^sub>E :: \<open>trace set \<Rightarrow> \<Phi>\<^sub>T\<^sub>E \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>T#\<close> 50) where
  \<open>S \<Turnstile>\<^sub>T# \<phi> \<equiv> \<forall>s\<in>S. \<forall>i. (s, i \<Turnstile>\<^sub>T \<phi>)\<close>

\<comment> \<open>Theorem 4.15\<close>
theorem unless_ht: \<open>(\<forall>b \<in> \<Pi>. (\<Turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>\<and> \<^bold>\<not> \<psi> \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ \<phi> \<^bold>\<or> \<psi> \<^bold>})) \<longleftrightarrow> Agent \<Turnstile>\<^sub>T# \<phi>\<^sup>E\<^sup>T unless \<psi>\<^sup>E\<^sup>T\<close>
proof
  assume \<open>\<forall>b \<in> \<Pi>. (\<Turnstile>\<^sub>H \<^bold>{ \<phi> \<^bold>\<and> \<^bold>\<not> \<psi> \<^bold>} ((fst b) \<triangleright> do (snd b)) \<^bold>{ \<phi> \<^bold>\<or> \<psi> \<^bold>})\<close>
  show \<open>Agent \<Turnstile>\<^sub>T# \<phi>\<^sup>E\<^sup>T unless \<psi>\<^sup>E\<^sup>T\<close> sorry
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
            with \<open>Agent \<Turnstile>\<^sub>T# ?\<phi> unless ?\<psi>\<close> have \<open>s, i \<Turnstile>\<^sub>T (?\<phi> until ?\<psi>)\<close> using \<open>s \<in> Agent\<close> by simp
            then show ?thesis
            proof (cases \<open>st_nth s i \<Turnstile>\<^sub>M \<psi>\<close>)
              case False
              show ?thesis
              proof
                assume \<open>st_nth s i \<Turnstile>\<^sub>M \<phi> \<^bold>\<and> \<^bold>\<not> \<psi> \<and> (fst b, snd b) = act_nth s i\<close>
                then have \<open>(fst b, snd b) = act_nth s i\<close> by simp
                show \<open>st_nth s (i + 1) \<Turnstile>\<^sub>M \<phi> \<^bold>\<or> \<psi>\<close> sorry
              qed
            qed simp
          qed simp
        qed
      qed
      then show ?thesis using semantics\<^sub>H.simps(2) by blast
    qed
  qed
qed

end
end