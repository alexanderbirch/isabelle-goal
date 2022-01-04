theory Gvf_Example imports Gvf_Temporal_Logic begin

fun all_models_aux :: \<open>string list \<Rightarrow> (string \<Rightarrow> bool) list\<close> where
  \<open>all_models_aux [] = [\<lambda>_. False]\<close> |
  \<open>all_models_aux (h # t) = map (\<lambda>l. l(h:= True)) (all_models_aux t) @ map (\<lambda>l. l(h := False)) (all_models_aux t)\<close>

locale fixed_propositions =
  fixes propositions :: \<open>string list\<close>
  assumes \<open>propositions \<noteq> []\<close>

context fixed_propositions begin

abbreviation \<open>all_models \<equiv> all_models_aux propositions\<close>

fun semantics\<^sub>p_eval :: \<open>string \<Phi>\<^sub>P list \<Rightarrow> string \<Phi>\<^sub>P \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>P\<^sup>e\<close> 50) where 
  \<open>\<Gamma> \<Turnstile>\<^sub>P\<^sup>e \<Phi> = (\<forall>f \<in> set all_models. (\<forall>p\<in>set \<Gamma>. semantics\<^sub>P f p) \<longrightarrow> semantics\<^sub>P f \<Phi>)\<close>

fun collect_atoms :: \<open>\<Phi>\<^sub>L \<Rightarrow> string set\<close> where
  \<open>collect_atoms (\<Phi>\<^sub>P.Atom x) = {x}\<close> |
  \<open>collect_atoms \<^bold>\<bottom> = {}\<close> |
  \<open>collect_atoms (\<^bold>\<not> p) = collect_atoms p\<close> |
  \<open>collect_atoms (p \<^bold>\<longrightarrow> q) = (collect_atoms p \<union> collect_atoms q)\<close> |
  \<open>collect_atoms (p \<^bold>\<or> q) = (collect_atoms p \<union> collect_atoms q)\<close> |
  \<open>collect_atoms (p \<^bold>\<and> q) = (collect_atoms p \<union> collect_atoms q)\<close>

definition formula_of_propositions :: \<open>\<Phi>\<^sub>L \<Rightarrow> bool\<close> where
 \<open>formula_of_propositions p \<equiv> collect_atoms p \<subseteq> set propositions\<close>

lemma model_unused_atom_eq: \<open>a \<notin> collect_atoms p \<Longrightarrow> semantics\<^sub>P (f(a := b)) p = semantics\<^sub>P f p\<close>
  by (induct p) auto 

lemma semantics\<^sub>p_eval_equiv: \<open>\<forall>q \<in> set \<Gamma>. formula_of_propositions q \<Longrightarrow> formula_of_propositions p \<Longrightarrow> \<Gamma> \<Turnstile>\<^sub>P\<^sup>e p \<longleftrightarrow> \<Gamma> \<^bold>\<Turnstile>\<^sub>P p\<close> 
  sorry 

fun is_mental_state_eval :: \<open>mental_state \<Rightarrow> bool\<close> (\<open>\<nabla>\<^sup>e\<close>) where
  \<open>\<nabla>\<^sup>e (\<Sigma>, \<Gamma>) = (\<not> \<Sigma> \<Turnstile>\<^sub>P\<^sup>e \<^bold>\<bottom> \<and> (\<forall>\<gamma>\<in>set \<Gamma>. \<not> \<Sigma> \<Turnstile>\<^sub>P\<^sup>e \<gamma> \<and> \<not> [] \<Turnstile>\<^sub>P\<^sup>e (\<^bold>\<not> \<gamma>)))\<close>

lemma is_mental_state_eval_eq: \<open>\<forall>q \<in> set \<Sigma>. formula_of_propositions q \<Longrightarrow> \<forall>q \<in> set \<Gamma>. formula_of_propositions q \<Longrightarrow> \<nabla>\<^sup>e (\<Sigma>, \<Gamma>) \<longleftrightarrow> \<nabla> (\<Sigma>, \<Gamma>)\<close>
  unfolding is_mental_state_def using semantics\<^sub>p_eval_equiv sorry

fun semantics\<^sub>M'_eval :: \<open>mental_state \<Rightarrow> Atom\<^sub>M \<Rightarrow> bool\<close> where
  \<open>semantics\<^sub>M'_eval (\<Sigma>, _) (Bl \<Phi>) = (\<Sigma> \<Turnstile>\<^sub>P\<^sup>e \<Phi>)\<close> |
  \<open>semantics\<^sub>M'_eval (\<Sigma>, \<Gamma>) (Gl \<Phi>) = (\<not> \<Sigma> \<Turnstile>\<^sub>P\<^sup>e \<Phi> \<and> (\<exists>\<gamma>\<in>set \<Gamma>. [] \<Turnstile>\<^sub>P\<^sup>e (\<gamma> \<^bold>\<longrightarrow> \<Phi>)))\<close>

abbreviation semantics\<^sub>M_eval :: \<open>mental_state \<Rightarrow> \<Phi>\<^sub>M \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>M\<^sup>e\<close> 50) where
  \<open>M \<Turnstile>\<^sub>M\<^sup>e \<phi> \<equiv> semantics\<^sub>P (semantics\<^sub>M'_eval M) \<phi>\<close>

fun satisfiable_base_eval :: \<open>mental_state \<Rightarrow> hoare_triple list \<Rightarrow> \<Phi>\<^sub>L list \<Rightarrow> bool\<close> where
  \<open>satisfiable_base_eval M hts \<Sigma> =
    ((\<not> fst M \<Turnstile>\<^sub>P\<^sup>e \<^bold>\<bottom> \<longrightarrow> \<not> \<Sigma> \<Turnstile>\<^sub>P\<^sup>e \<^bold>\<bottom>) \<and> 
    (\<forall>ht \<in> set hts. M \<Turnstile>\<^sub>M\<^sup>e pre ht \<longrightarrow> (\<Sigma>, [\<psi><-snd M. \<not> \<Sigma> \<Turnstile>\<^sub>P\<^sup>e \<psi>] ) \<Turnstile>\<^sub>M\<^sup>e post ht))\<close>


end
end