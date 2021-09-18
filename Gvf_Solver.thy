theory Gvf_Solver imports Gvf_Logic "HOL-Eisbach.Eisbach" begin

method sc_decompose_L_h = (rule L_Neg | rule L_And | rule L_Or | rule L_Imp)
method sc_decompose_R_h = (rule R_Neg | rule R_Imp | rule R_Or | rule R_And)

fun can_decompose :: \<open>'a \<Phi>\<^sub>P \<Rightarrow> bool\<close> where
  \<open>can_decompose (\<^bold>\<not> _) = True\<close> |
  \<open>can_decompose (_ \<^bold>\<longrightarrow> _) = True\<close> |
  \<open>can_decompose (_ \<^bold>\<and> _) = True\<close> |
  \<open>can_decompose (_ \<^bold>\<or> _) = True\<close> |
  \<open>can_decompose _ = False\<close>

lemma L_Shift_meaningful: \<open>\<exists>p \<in> set \<Gamma>. can_decompose p \<Longrightarrow> gen_sc R (rotate1 \<Gamma>) \<Delta> \<Longrightarrow> gen_sc R \<Gamma> \<Delta>\<close>
  using L_Shift .

lemma R_Shift_meaningful: \<open>\<exists>p \<in> set \<Delta>. can_decompose p \<Longrightarrow> gen_sc R \<Gamma> (rotate1 \<Delta>) \<Longrightarrow> gen_sc R \<Gamma> \<Delta>\<close>
  using R_Shift .

method sc_shift_L = rule L_Shift_meaningful; simp_all; (match conclusion in \<open>gen_sc _ _ _\<close> \<Rightarrow> succeed)
method sc_shift_R = rule R_Shift_meaningful; simp_all; (match conclusion in \<open>gen_sc _ _ _\<close> \<Rightarrow> succeed)
method sc_decompose_h = (sc_decompose_L_h | sc_decompose_R_h)+
method try_shift = sc_shift_L | sc_shift_R

method try_axiom = (match conclusion in \<open>gen_sc R \<Gamma> (p # \<Delta>)\<close> for R \<Gamma> \<Delta> p \<Rightarrow> \<open>rule Axiom[where R=R and \<Gamma>=\<Gamma> and \<Delta>=\<open>(p # \<Delta>)\<close> and p=p]; simp_all; match conclusion in False \<Rightarrow> fail\<close>)
method try_axiom_all = (try_axiom | (match conclusion in \<open>gen_sc R \<Gamma> (p # \<Delta>)\<close> for R \<Gamma> \<Delta> p \<Rightarrow> \<open>rule weakening_h(2)[where R=R and \<Gamma>=\<Gamma> and p=p and \<Delta>=\<Delta>]; try_axiom_all\<close>))+

method sc_decompose = (sc_decompose_h?, ((try_shift, sc_decompose_h?)+)?)

method sc_solver = (sc_decompose, try_axiom_all+)+

\<comment> \<open>Simple example\<close>
lemma \<open>\<turnstile>\<^sub>P (P \<^bold>\<longrightarrow> Q) \<^bold>\<longrightarrow> P \<^bold>\<longrightarrow> Q\<close> by sc_solver

(*  Does not work for all rules, in particular generic ones, weakening and cut *)

end