(*
  Goal verification framework
    - Actions
*)

\<comment> \<open>This theory sets up the concepts of agents, actions, transitions and traces.
    We extend the language for mental state formulas with enabledness of actions.
    We provide its syntax, semantics and a sound proof system.\<close>

theory Gvf_Actions imports Gvf_Mental_States begin

section \<open>Actions\<close>

\<comment> \<open>The identifier for basic actions is a natural number.\<close>
type_synonym Bcap = nat

\<comment> \<open>Agent capability is a basic capability, adopt or drop (the latter two are built into GOAL).\<close>
datatype cap = basic Bcap | adopt (cget: \<Phi>\<^sub>L) | drop (cget: \<Phi>\<^sub>L)

\<comment> \<open>Auxiliary function.\<close>
fun is_drop :: \<open>cap \<Rightarrow> bool\<close> where
  \<open>is_drop (drop _) = True\<close> |
  \<open>is_drop _ = False\<close>

\<comment> \<open>Type for conditional action that is a pair: a condition on the mental state and a basic action.\<close>
type_synonym cond_act = \<open>\<Phi>\<^sub>M \<times> cap\<close>

\<comment> \<open>Atoms are extended with enabled for basic/conditional actions.\<close>
datatype Atoms\<^sub>E = Bl \<Phi>\<^sub>L | Gl \<Phi>\<^sub>L | enabled_basic cap | enabled_cond cond_act
\<comment> \<open>The simple type theory makes it less delicate to extend types, so we redefine the belief
    and goal operators while adding two new options: one for basic and one for conditional actions.\<close>

\<comment> \<open>The type for mental state formulas concerning enabledness.\<close>
type_synonym \<Phi>\<^sub>E = \<open>Atoms\<^sub>E \<Phi>\<^sub>P\<close>

\<comment> \<open>Introducing some notation.\<close>
syntax
  "_G" :: \<open>\<Phi>\<^sub>L \<Rightarrow> \<Phi>\<^sub>E\<close> (\<open>G _\<close> 55)
  "_B" :: \<open>\<Phi>\<^sub>L \<Rightarrow> \<Phi>\<^sub>E\<close> (\<open>B _\<close> 55)
  "_enabled_basic" :: \<open>Atoms\<^sub>E \<Rightarrow> \<Phi>\<^sub>E\<close> (\<open>enabledb _\<close> 55)
  "_enabled_cond" :: \<open>Atoms\<^sub>E \<Rightarrow> \<Phi>\<^sub>E\<close> (\<open>enabled _\<close> 55)
  "_cond_act" :: \<open>\<Phi>\<^sub>M \<Rightarrow> cap \<Rightarrow> \<Phi>\<^sub>M \<times> cap\<close>  (\<open>_ \<triangleright> do _\<close>)
translations
  "enabledb c" \<rightharpoonup> "(Gvf_Logic.Atom (Atoms\<^sub>E.enabled_basic c))"
  "enabled c" \<rightharpoonup> "(Gvf_Logic.Atom (Atoms\<^sub>E.enabled_cond c))"
  "\<phi> \<triangleright> do a" \<rightharpoonup> "(\<phi>, a)"

section \<open>Semantics of GOAL\<close>

\<comment> \<open>The type for the function \<T> that gives the agent's belief update capabilities.\<close>
type_synonym bel_upd_t = \<open>Bcap \<Rightarrow> mental_state \<Rightarrow> \<Phi>\<^sub>L set option\<close>
\<comment> \<open>We replace notion of undefined (from paper) with an optional value, i.e. \<T> a \<Sigma> = None means
    that basic action a is not defined for \<Sigma>.
    We further assume that the goal base (entire mental state) is added to the input.\<close>

\<comment> \<open>The mental state transformer gives the agent's mental state update capabilities.\<close>
fun mental_state_transformer :: \<open>bel_upd_t \<Rightarrow> cap \<Rightarrow> mental_state \<Rightarrow> mental_state option\<close> (\<open>\<M>*\<close>) where
  \<comment> \<open>If \<T> a \<Sigma> is defined, update the goal base accordingly.\<close>
  \<open>\<M>* \<T> (basic n) (\<Sigma>, \<Gamma>) = (case \<T> n (\<Sigma>, \<Gamma>) of Some \<Sigma>' \<Rightarrow> Some (\<Sigma>', \<Gamma> - {\<psi> \<in> \<Gamma>. \<Sigma>' \<Turnstile>\<^sub>L \<psi>}) | _ \<Rightarrow> None)\<close> |
  \<comment> \<open>Remove the goals that entail \<Phi>.\<close>
  \<open>\<M>* \<T> (drop \<Phi>) (\<Sigma>, \<Gamma>) = Some (\<Sigma>, \<Gamma> - {\<psi> \<in> \<Gamma>. {\<psi>} \<Turnstile>\<^sub>L \<Phi>})\<close> |
  \<comment> \<open>Add the goal \<Phi> if it is consistent and not entailed by the belief base.\<close>
  \<open>\<M>* \<T> (adopt \<Phi>) (\<Sigma>, \<Gamma>) = (if \<not> {} \<Turnstile>\<^sub>L \<^bold>\<not> \<Phi> \<and> \<not> \<Sigma> \<Turnstile>\<^sub>L \<Phi> then Some (\<Sigma>, \<Gamma> \<union> {\<Phi>}) else None)\<close>

\<comment> \<open>We fix to a single agent and assume a given belief update function, 
    a set of conditional actions and an initial state.\<close>
locale single_agent = 
  fixes
    \<T>  :: bel_upd_t and
    \<Pi> :: \<open>cond_act set\<close> and
    M\<^sub>0 :: mental_state
  assumes
    \<comment> \<open>Non-empty set of conditional actions and initial state is a mental state.\<close>
    is_agent: \<open>\<Pi> \<noteq> {} \<and> \<nabla> M\<^sub>0\<close> and
    \<comment> \<open>\<T> preserves consistency.\<close>
    \<T>_consistent: \<open>(\<exists>\<phi>. (\<phi>, basic a) \<in> \<Pi>) \<longrightarrow> \<not> \<Sigma> \<Turnstile>\<^sub>L \<bottom>\<^sub>L \<longrightarrow> \<T> a (\<Sigma>, \<Gamma>) \<noteq> None \<longrightarrow> \<not> the (\<T> a (\<Sigma>, \<Gamma>)) \<Turnstile>\<^sub>L \<bottom>\<^sub>L\<close> and
    \<comment> \<open>\<T> only for defined actions.\<close>
    \<T>_in_domain: \<open>\<T> a (\<Sigma>, \<Gamma>) \<noteq> None \<longrightarrow> (\<exists>\<phi>. (\<phi>, basic a) \<in> \<Pi>)\<close>

\<comment> \<open>Working in the context of single_agent, means that we can base definitions, proofs etc. around
    fixed variables for which a number of assumptions apply. For a specific agent, we need to prove
    that the assumptions apply for the given input variables. By doing so, we get immediate access
    to everything defined within the single_agent context.\<close>
context single_agent
begin

\<comment> \<open>Basic capabilities derived from the set of conditional actions.\<close>
definition Cap :: \<open>Bcap set\<close> where
  \<open>Cap \<equiv> { a. \<exists>\<phi>. (\<phi>, (basic a)) \<in> \<Pi> }\<close>
\<comment> \<open>We assume that a basic capability is represented by at least one conditional action.\<close>

\<comment> \<open>Define mental state transformer local to the agent.\<close>
abbreviation \<open>\<M> a M \<equiv> \<M>* \<T> a M\<close>

\<comment> \<open>Examples.\<close>
lemma 
  assumes \<open>\<T> n ({P}, {Q}) = Some {P, Q}\<close>
  shows \<open>\<M> (basic n) ({P}, {Q}) = Some ({P, Q}, {})\<close>
using assms by simp
 
lemma \<open>\<M> (drop \<top>\<^sub>L) ({}, {P, Q}) = Some ({}, {})\<close> by simp

lemma
  assumes \<open>\<not> {} \<Turnstile>\<^sub>L \<^bold>\<not> Q\<close> and \<open>\<not> {} \<Turnstile>\<^sub>L Q\<close>
  shows \<open>\<M> (adopt Q) ({}, {P}) = Some ({}, {P, Q})\<close> 
proof -
  have \<open>\<M> (adopt Q) ({}, {P}) = Some ({}, {P} \<union> {Q})\<close> using assms by simp
  then show ?thesis by auto
qed

\<comment> \<open>The mental state transformer is only defined for actions of \<Pi>.\<close>
lemma \<M>_some_in_\<Pi>: 
  assumes \<open>\<M> (basic n) M \<noteq> None\<close> 
    shows \<open>\<exists>\<phi>. (\<phi>, basic n) \<in> \<Pi>\<close>
proof (cases M)
  case (Pair \<Sigma> \<Gamma>)
  with assms obtain \<Sigma>' \<Gamma>' where someM: \<open>\<M> (basic n) (\<Sigma>, \<Gamma>) = Some (\<Sigma>', \<Gamma>')\<close> by auto
  then have \<open>\<T> n (\<Sigma>, \<Gamma>) = Some \<Sigma>'\<close>
  proof (cases \<open>\<T> n (\<Sigma>, \<Gamma>)\<close>)
    case None
    then have \<open>\<M> (basic n) (\<Sigma>, \<Gamma>) = None\<close> by simp
    with someM show ?thesis by simp
  next
    case (Some \<Sigma>'')
    moreover have \<open>fst (the (\<M> (basic n) (\<Sigma>, \<Gamma>))) = \<Sigma>''\<close> using Some by simp
    moreover have \<open>fst (the (\<M> (basic n) (\<Sigma>, \<Gamma>))) = \<Sigma>'\<close> using someM by simp
    ultimately show ?thesis by simp
  qed    
  with \<T>_in_domain show ?thesis by blast
qed

\<comment> \<open>The mental state transformer is only defined for basic capabilities of Cap.\<close>
lemma \<M>_some_Cap:
  assumes \<open>\<M> (basic a) M \<noteq> None\<close> 
  shows \<open>a \<in> Cap\<close>
using assms \<M>_some_in_\<Pi> Cap_def by auto

\<comment> \<open>Mental state transformer preserves properties of mental states (when \<T> preserves consistency).\<close>
lemma \<M>_preserves_mst: \<open>\<nabla> (\<Sigma>, \<Gamma>) \<Longrightarrow> \<M> c (\<Sigma>, \<Gamma>) \<noteq> None \<Longrightarrow> \<nabla> (the (\<M> c (\<Sigma>, \<Gamma>)))\<close>
proof (induct c)
  case basic: (basic a)
  then obtain \<Sigma>' where \<Sigma>': \<open>\<T> a (\<Sigma>, \<Gamma>) = Some \<Sigma>'\<close> by fastforce
  have \<open>\<nabla> (\<Sigma>', \<Gamma> - {\<psi> \<in> \<Gamma>. \<Sigma>' \<Turnstile>\<^sub>L \<psi>})\<close> (is \<open>\<nabla> (\<Sigma>', ?\<Gamma>')\<close>)
  proof -
    have \<open>\<not> \<Sigma>' \<Turnstile>\<^sub>L \<bottom>\<^sub>L\<close>
    proof -
      from basic(1) have \<open>\<not> \<Sigma> \<Turnstile>\<^sub>L \<bottom>\<^sub>L\<close> unfolding is_mental_state_def by simp
      moreover have \<open>\<exists>\<phi>. (\<phi>, basic a) \<in> \<Pi>\<close> using \<M>_some_in_\<Pi> basic.prems(2) by blast
      ultimately have \<open>\<not> the (\<T> a (\<Sigma>, \<Gamma>)) \<Turnstile>\<^sub>L \<bottom>\<^sub>L\<close> using \<Sigma>' \<T>_consistent basic(2) by blast
      with \<Sigma>' show ?thesis by simp
    qed
    moreover from basic(1) have \<open>\<forall>\<gamma>\<in>?\<Gamma>'. \<not> \<Sigma> \<Turnstile>\<^sub>L \<gamma> \<and> \<not> {} \<Turnstile>\<^sub>L \<^bold>\<not> \<gamma>\<close> 
      unfolding is_mental_state_def by simp
    ultimately show ?thesis unfolding is_mental_state_def by simp
  qed
  with \<Sigma>' show ?case by simp 
next
  case adopt: (adopt \<Phi>)
  with mental_state_transformer.simps(3) have mst_goal: \<open>\<not> {} \<Turnstile>\<^sub>L \<^bold>\<not> \<Phi> \<and> \<not> \<Sigma> \<Turnstile>\<^sub>L \<Phi>\<close> by metis
  with adopt(1) have \<open>\<nabla> (\<Sigma>, \<Gamma> \<union> {\<Phi>})\<close> unfolding is_mental_state_def by simp 
  with mst_goal show ?case by simp
next
  case (drop \<Phi>)
  then have \<open>\<nabla> (\<Sigma>, \<Gamma> - {\<psi> \<in> \<Gamma>. {\<psi>} \<Turnstile>\<^sub>L \<Phi>})\<close> unfolding is_mental_state_def by simp
  then show ?case by simp
qed

section \<open>Traces\<close>

\<comment> \<open>Transition relation between states due to an action.\<close>
definition transition :: \<open>mental_state \<Rightarrow> cond_act \<Rightarrow> mental_state \<Rightarrow> bool\<close> (\<open>_ \<rightarrow>_ _\<close>) where
  \<open>M \<rightarrow>b M' \<equiv> let (\<phi>, a) = b in b \<in> \<Pi> \<and> M \<Turnstile>\<^sub>M \<phi> \<and> \<M> a M = Some M'\<close>
\<comment> \<open>If b is a conditional action, and the condition true in M, then there is possible transition
    between M and M' where M' is the result of applying \<M> for a to M.\<close>

\<comment> \<open>Chain of transitions (computation steps) gives the computation relation.\<close>
inductive computation :: \<open>mental_state \<Rightarrow> mental_state \<Rightarrow> bool\<close> (\<open>_ \<rightarrow>* _\<close>) where
  \<comment> \<open>The base step from the initial mental state.\<close>
  basis: \<open>M\<^sub>0 \<rightarrow>b M' \<Longrightarrow> M\<^sub>0 \<rightarrow>* M'\<close> |
  \<comment> \<open>Inductive step from an existing computation given a transition.\<close>
  step: \<open>M \<rightarrow>* M' \<Longrightarrow> M' \<rightarrow>b M'' \<Longrightarrow> M \<rightarrow>* M''\<close>

\<comment> \<open>Example\<close>
lemma \<open>M\<^sub>0 \<rightarrow>a M\<^sub>1 \<Longrightarrow> M\<^sub>1 \<rightarrow>b M\<^sub>2 \<Longrightarrow> M\<^sub>0 \<rightarrow>* M\<^sub>2\<close>
  using basis step by blast

\<comment> \<open>Traces are infinite structures.\<close>
codatatype trace = Trace mental_state \<open>cond_act \<times> trace\<close>
\<comment> \<open>trace := mental state, conditional action, trace\<close>

\<comment> \<open>Example.\<close>
value \<open>Trace M\<^sub>0 (a, (Trace M\<^sub>1 (b, (Trace M\<^sub>2 X))))\<close>

\<comment> \<open>Retrieve the nth conditional action of the trace.\<close>
fun act_nth :: \<open>trace \<Rightarrow> nat \<Rightarrow> cond_act\<close> where
  \<open>act_nth (Trace _ (b, _)) 0 = b\<close> |
  \<open>act_nth (Trace _ (_, S)) n = act_nth S (n-1)\<close>

\<comment> \<open>Example.\<close>
lemma \<open>b = act_nth (Trace M\<^sub>0 (a, (Trace M\<^sub>1 (b, (Trace M\<^sub>2 X))))) 1\<close> by simp

\<comment> \<open>Retrieve the nth mental state of the trace.\<close>
fun st_nth :: \<open>trace \<Rightarrow> nat \<Rightarrow> mental_state\<close> where
  \<open>st_nth (Trace M (_, _)) 0 = M\<close> |
  \<open>st_nth (Trace _ (_, S)) n = st_nth S (n-1)\<close>

\<comment> \<open>Example.\<close>
lemma \<open>M\<^sub>1 = st_nth (Trace M\<^sub>0 (a, (Trace M\<^sub>1 (b, (Trace M\<^sub>2 X))))) 1\<close> by simp

\<comment> \<open>if (\<psi>, a) is the ith conditional action of trace s, then the first value of (act_nth s i)
    is \<psi>. This is intuitively easy to see, but pattern matching using equality can be problematic.\<close>
lemma fst_act_nth: \<open>(\<psi>, a) = act_nth s i \<Longrightarrow> fst (act_nth s i) = \<psi>\<close>
  by (metis fstI)

\<comment> \<open>The same as above but for the second value.\<close>
lemma snd_act_nth: \<open>(\<psi>, a) = act_nth s i \<Longrightarrow> snd (act_nth s i) = a\<close>
  by (metis sndI)

\<comment> \<open>The definition of a trace (not every element of the datatype trace qualifies).\<close>
definition is_trace :: \<open>trace \<Rightarrow> bool\<close> where
  \<open>is_trace s \<equiv> 
    \<forall>i. (let (M, M', (\<phi>, a)) = (st_nth s i, st_nth s (i+1), act_nth s i) in 
          (\<phi>, a) \<in> \<Pi> \<and> ((M \<rightarrow>(\<phi>, a) M') \<or> \<M> a M = None \<and> M = M'))\<close>
\<comment> \<open>For all i there is a transition between M_i and M_(i+1) due to an action, or the action
    is not enabled and the successor state (M_(i+1)) is equal to the current (M_i).\<close>

\<comment> \<open>The nth conditional action of a trace is in \<Pi>.\<close>
lemma trace_in_\<Pi>:
  assumes \<open>is_trace s\<close>
  shows \<open>\<forall>i. (act_nth s i) \<in> \<Pi>\<close>
proof
  fix i
  let ?M  = \<open>st_nth s i\<close> and
      ?M' = \<open>st_nth s (i+1)\<close> 
  from assms(1) have \<open>let (\<phi>, a) = (act_nth s i) in (\<phi>, a) \<in> \<Pi> \<and> ((?M \<rightarrow>(\<phi>, a) ?M') \<or> \<M> a ?M = None \<and> ?M = ?M')\<close> 
    unfolding is_trace_def by simp
  then have \<open>let (\<phi>, a) = (act_nth s i) in (\<phi>, a) \<in> \<Pi>\<close> by auto
  then show \<open>(act_nth s i) \<in> \<Pi>\<close> by simp
qed

\<comment> \<open>If there is no transition between a state and its successor in a trace, they must be equal.\<close>
lemma not_transition_eq:
  assumes \<open>is_trace s\<close>
  shows \<open>\<not>((st_nth s i) \<rightarrow>(act_nth s i) (st_nth s (i+1))) \<longrightarrow> (st_nth s i) = (st_nth s (i+1))\<close>
  (is \<open>\<not>(?M \<rightarrow>?b ?M') \<longrightarrow> ?M = ?M'\<close>)
proof
  assume \<open>\<not>(?M \<rightarrow>?b ?M')\<close>
  moreover from assms have \<open>let (\<phi>, a) = act_nth s i in 
          (\<phi>, a) \<in> \<Pi> \<and> ((?M \<rightarrow>(\<phi>, a) ?M') \<or> \<M> a ?M = None \<and> ?M = ?M')\<close> 
    unfolding is_trace_def by simp
  ultimately have \<open>let (\<phi>, a) = act_nth s i in (\<phi>, a) \<in> \<Pi> \<and> \<M> a ?M = None \<and> ?M = ?M'\<close> by auto
  then show \<open>?M = ?M'\<close> by auto
qed

\<comment> \<open>A fair trace ensures that there always is a future point where an actions is scheduled.\<close>
definition fair_trace :: \<open>trace \<Rightarrow> bool\<close> where
  \<open>fair_trace s \<equiv> \<forall> b \<in> \<Pi> . \<forall>i . \<exists> j > i. act_nth s j = b\<close>

\<comment> \<open>An agent is defined as the set of fair traces starting from the initial state.\<close>
definition Agent :: \<open>trace set\<close> where
  \<open>Agent \<equiv> {s . is_trace s \<and> fair_trace s \<and> st_nth s 0 = M\<^sub>0}\<close>

\<comment> \<open>If the mental state transformer is defined for a state in the trace, then it gives the successor state.\<close>
lemma \<M>_suc_state:
  assumes \<open>s \<in> Agent\<close>
      and \<open>(\<phi>, a) = act_nth s i\<close>
      and \<open>\<M> a (st_nth s i) \<noteq> None\<close>
    shows \<open>st_nth s (i+1) = the (\<M> a (st_nth s i))\<close>
      (is \<open>?M' = the (\<M> a ?M)\<close>)
proof -
  from assms(1) have \<open>is_trace s\<close> unfolding Agent_def by simp
  then have \<open>let (M, M', (\<phi>, a)) = (?M, ?M', act_nth s i) in 
        (\<phi>, a) \<in> \<Pi> \<and> ((M \<rightarrow>(\<phi>, a) M') \<or> \<M> a M = None \<and> M = M')\<close> unfolding is_trace_def by simp
  with assms(2) have \<open>(?M \<rightarrow>(\<phi>, a) ?M') \<or> \<M> a ?M = None \<and> ?M = ?M'\<close> by auto
  with assms(3) have \<open>?M \<rightarrow>(\<phi>, a) ?M'\<close> by auto
  then show ?thesis unfolding transition_def by simp
qed

\<comment> \<open>All states in trace comply to mental state definition.\<close>
lemma is_mst_trace: 
  assumes \<open>s \<in> Agent\<close>
  shows   \<open>\<nabla> (st_nth s n)\<close>
proof (induct n)
  case 0
  with assms show ?case using is_agent unfolding Agent_def by simp
next
  case (Suc n)
  let ?M = \<open>st_nth s n\<close> and ?M' = \<open>st_nth s (Suc n)\<close> and ?b = \<open>act_nth s n\<close>
  have trace_n: \<open>(?M \<rightarrow>?b ?M') \<or> \<M> (snd ?b) ?M = None \<and> ?M = ?M'\<close>
  proof -
    from assms(1) have \<open>is_trace s\<close> unfolding Agent_def by simp
    then have \<open>let (\<phi>, a) = ?b in (\<phi>, a) \<in> \<Pi> \<and> ((?M \<rightarrow>(\<phi>, a) ?M') \<or> \<M> a ?M = None \<and> ?M = ?M')\<close>
      unfolding is_trace_def by simp
    then show ?thesis by auto
  qed
  then show ?case 
  proof (cases \<open>\<M> (snd ?b) ?M = None\<close>)
    case True
    with Suc trace_n show ?thesis unfolding transition_def by auto
  next
    case False
    with \<M>_preserves_mst have \<open>\<nabla> (the (\<M> (snd ?b) ?M))\<close> 
      using Suc by (cases ?M) simp
    with \<M>_suc_state trace_n show ?thesis using assms False unfolding Agent_def
      by (metis (no_types, lifting) Suc_eq_plus1 prod.collapse)
  qed
qed

section \<open>Derivability\<close>

\<comment> \<open>Auxiliary function that converts mental state formulas to the type including enabledness.\<close>
fun to_\<Phi>\<^sub>E :: \<open>\<Phi>\<^sub>M \<Rightarrow> \<Phi>\<^sub>E\<close> (\<open>_\<^sup>E\<close>) where
  \<open>(Atom (Atoms\<^sub>M.Bl \<Phi>))\<^sup>E = Atom (Bl \<Phi>)\<close> |
  \<open>(Atom (Atoms\<^sub>M.Gl \<Phi>))\<^sup>E = Atom (Gl \<Phi>)\<close> |
  \<open>(\<^bold>\<not> \<phi>)\<^sup>E = \<^bold>\<not> (\<phi>\<^sup>E)\<close> |
  \<open>(\<phi>\<^sub>1 \<^bold>\<longrightarrow> \<phi>\<^sub>2)\<^sup>E = (\<phi>\<^sub>1\<^sup>E) \<^bold>\<longrightarrow> (\<phi>\<^sub>2\<^sup>E)\<close> |
  \<open>(\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2)\<^sup>E = (\<phi>\<^sub>1\<^sup>E) \<^bold>\<or> (\<phi>\<^sub>2\<^sup>E)\<close> |
  \<open>(\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2)\<^sup>E = (\<phi>\<^sub>1\<^sup>E) \<^bold>\<and> (\<phi>\<^sub>2\<^sup>E)\<close>

\<comment> \<open>Truth of enabledness (semantics).\<close>
fun semantics\<^sub>E' :: \<open>mental_state \<Rightarrow> Atoms\<^sub>E \<Rightarrow> bool\<close> where
  \<comment> \<open>Semantics of B and G are the same as for mental state formulas without enabled.\<close>
  \<open>semantics\<^sub>E' M (Bl \<Phi>) = semantics\<^sub>M' M (Atoms\<^sub>M.Bl \<Phi>)\<close> |
  \<open>semantics\<^sub>E' M (Gl \<Phi>) = semantics\<^sub>M' M (Atoms\<^sub>M.Gl \<Phi>)\<close> |
  \<comment> \<open>a is defined for the action and \<M> a is defined for  M.\<close>
  \<open>semantics\<^sub>E' M (enabled_basic a) = (\<M> a M \<noteq> None)\<close> |
  \<comment> \<open>Conditional action b is enabled if there exists a transition from M to M' using b for some M'.\<close>
  \<open>semantics\<^sub>E' M (enabled_cond b) = (\<exists>M'. (M \<rightarrow>b M'))\<close>

\<comment> \<open>Semantics of atoms with enabled can be seen as an interpretation given a mental state.\<close>
abbreviation semantics\<^sub>E :: \<open>mental_state \<Rightarrow> \<Phi>\<^sub>E \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>E\<close> 50) where
  \<open>M \<Turnstile>\<^sub>E \<phi> \<equiv> semantics\<^sub>P (semantics\<^sub>E' M) \<phi>\<close>

\<comment> \<open>Example.\<close>
lemma \<open>(M\<^sub>0 \<rightarrow>b M\<^sub>1) \<Longrightarrow> M\<^sub>0 \<Turnstile>\<^sub>E enabled b\<close> 
proof -
  assume \<open>M\<^sub>0 \<rightarrow>b M\<^sub>1\<close>
  then have \<open>\<exists>M'. (M\<^sub>0 \<rightarrow>b M')\<close> by blast
  then show \<open>M\<^sub>0 \<Turnstile>\<^sub>E enabled b\<close> by simp
qed

\<comment> \<open>Proof system.\<close>
inductive provable\<^sub>E :: \<open>\<Phi>\<^sub>E \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>E _\<close> 40) where
  \<comment> \<open>Derive classical tautologies.\<close>
  R1: \<open>\<turnstile>\<^sub>P \<phi> \<Longrightarrow> \<turnstile>\<^sub>E \<phi>\<close> |
  \<comment> \<open>Properties of beliefs and goals. Imported from proof system for mental state formulas.\<close>
  R\<^sub>M: \<open>\<turnstile>\<^sub>M \<phi> \<Longrightarrow> \<turnstile>\<^sub>E (\<phi>\<^sup>E)\<close> |
  \<comment> \<open>Properties of enabled.\<close>
  E1: \<open>\<turnstile>\<^sub>P \<phi> \<Longrightarrow> \<turnstile>\<^sub>E (enabledb a) \<Longrightarrow> (\<phi> \<triangleright> do a) \<in> \<Pi> \<Longrightarrow> \<turnstile>\<^sub>E (enabled (\<phi> \<triangleright> do a))\<close> |
  E2: \<open>\<turnstile>\<^sub>E (enabledb (drop \<Phi>))\<close> |
  R3: \<open>\<not> \<turnstile>\<^sub>P \<^bold>\<not> \<Phi> \<Longrightarrow> \<turnstile>\<^sub>E (\<^bold>\<not> ((B \<Phi>)\<^sup>E) \<^bold>\<longleftrightarrow> (enabledb (adopt \<Phi>)))\<close> |
  R4: \<open>\<turnstile>\<^sub>P (\<^bold>\<not> \<Phi>) \<Longrightarrow> \<turnstile>\<^sub>E (\<^bold>\<not> (enabledb (adopt \<Phi>)))\<close> |
  R5: \<open>\<forall>M. \<T> a M \<noteq> None \<Longrightarrow> \<turnstile>\<^sub>E (enabledb (basic a))\<close>

section \<open>Soundness\<close>

lemma soundness\<^sub>E:
  assumes \<open>\<nabla> M\<close>
  shows \<open>\<turnstile>\<^sub>E \<phi> \<Longrightarrow> M \<Turnstile>\<^sub>E \<phi>\<close>
proof (induct rule: provable\<^sub>E.induct)
  case (R1 \<phi>)
  with soundness\<^sub>P show ?case by fastforce
next
  case (R\<^sub>M \<phi>)
  with soundness\<^sub>M have \<open>M \<Turnstile>\<^sub>M \<phi>\<close> using \<open>\<nabla> M\<close> by simp
  moreover have \<open>M \<Turnstile>\<^sub>M \<phi> = (M \<Turnstile>\<^sub>E (\<phi>\<^sup>E))\<close> 
  proof (induct \<phi>)
    case (Atom x)
    then show ?case by (cases x) simp_all
  qed auto
  ultimately show ?case by simp
next
  case (E1 \<phi> a)
  with soundness\<^sub>P have \<open>M \<Turnstile>\<^sub>M \<phi>\<close> by fastforce
  then show ?case 
  proof (cases a)
    case (basic n)
    with E1.hyps(3) obtain M' where \<open>\<M> a M = Some M'\<close> by auto
    with \<open>M \<Turnstile>\<^sub>M \<phi>\<close> have \<open>M \<rightarrow>(\<phi> \<triangleright> do a) M'\<close> using E1(4) 
      unfolding transition_def by simp
    then have \<open>\<exists>M'. (M \<rightarrow>(\<phi> \<triangleright> do a) M')\<close> by blast
    then show ?thesis by simp
  next
    case (adopt \<Phi>)
    with E1.hyps(3) obtain M' where \<open>\<M> a M = Some M'\<close> by auto
    with \<open>M \<Turnstile>\<^sub>M \<phi>\<close> have \<open>M \<rightarrow>(\<phi> \<triangleright> do a) M'\<close> using E1(4) 
      unfolding transition_def by simp
    then have \<open>\<exists>M'. (M \<rightarrow>(\<phi> \<triangleright> do a) M')\<close> by blast
    then show ?thesis by simp
  next
    case (drop \<Phi>)
    with E1.hyps(3) obtain M' where \<open>\<M> a M = Some M'\<close> by auto
    with \<open>M \<Turnstile>\<^sub>M \<phi>\<close> have \<open>M \<rightarrow>(\<phi> \<triangleright> do a) M'\<close> using E1(4) 
      unfolding transition_def by simp
    then have \<open>\<exists>M'. (M \<rightarrow>(\<phi> \<triangleright> do a) M')\<close> by blast
    then show ?thesis by simp
  qed
next
  case (E2 \<Phi>)
  have \<open>\<M> (drop \<Phi>) M \<noteq> None\<close> using mental_state_transformer.simps(2) by (cases M) simp
  then show ?case by simp
next
  case (R3 \<Phi>)
  then show ?case by simp
next
  case (R4 \<Phi>)
  with soundness\<^sub>L have \<open>\<forall>M. \<M> (adopt \<Phi>) M = None\<close> by fastforce
  then have \<open>\<M> (adopt \<Phi>) M = None\<close> by blast
  then show ?case by simp
next
  case (R5 a)
  have \<open>\<forall>\<Sigma> \<Gamma>. (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>E Atom (enabled_basic (basic a))\<close>
  proof 
    fix \<Sigma>
    show \<open>\<forall>\<Gamma>. (\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>E Atom (enabled_basic (basic a))\<close>
    proof
      fix \<Gamma>
      from \<open>\<forall>M. \<T> a M \<noteq> None\<close> have \<open>\<T> a (\<Sigma>, \<Gamma>) \<noteq> None\<close> \<open>a \<in> Cap\<close> 
        using \<T>_in_domain unfolding Cap_def by simp_all
      then show \<open>(\<Sigma>, \<Gamma>) \<Turnstile>\<^sub>E Atom (enabled_basic (basic a))\<close> by auto
    qed
  qed
  then have \<open>\<forall>M. M \<Turnstile>\<^sub>E Atom (enabled_basic (basic a))\<close> by simp
  then show ?case by blast
qed

\<comment> \<open>The semantics of a converted formula is equal to the original.\<close>
lemma transfer_semantics\<^sub>M: \<open>M \<Turnstile>\<^sub>M \<phi> \<longleftrightarrow> M \<Turnstile>\<^sub>E (\<phi>\<^sup>E)\<close> 
proof (induct \<phi>)
  case (Atom x)
  show ?case by (cases x) simp_all
qed simp_all

end
end