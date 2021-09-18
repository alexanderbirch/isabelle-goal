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
type_synonym Bcap = string

\<comment> \<open>Agent capability is a basic capability, adopt or drop (the latter two are built into GOAL).\<close>
datatype cap = basic (bcap: Bcap) | adopt (cget: \<Phi>\<^sub>L) | drop (cget: \<Phi>\<^sub>L)

\<comment> \<open>Type for conditional action that is a pair: a condition on the mental state and a basic action.\<close>
type_synonym cond_act = \<open>\<Phi>\<^sub>M \<times> cap\<close>

\<comment> \<open>Atoms are extended with enabled for basic/conditional actions.\<close>
datatype Atom\<^sub>E = Bl\<^sub>E \<Phi>\<^sub>L | Gl\<^sub>E \<Phi>\<^sub>L | enabled_basic cap | enabled_cond cond_act
\<comment> \<open>The simple type theory makes it less delicate to extend types, so we redefine the belief
    and goal operators while adding two new options: one for basic and one for conditional actions.\<close>

\<comment> \<open>The type for mental state formulas concerning enabledness.\<close>
type_synonym \<Phi>\<^sub>E = \<open>Atom\<^sub>E \<Phi>\<^sub>P\<close>

\<comment> \<open>Introducing some notation.\<close>
abbreviation \<open>B\<^sub>E \<Phi> \<equiv> Atom (Bl\<^sub>E \<Phi>)\<close>
abbreviation \<open>G\<^sub>E \<Phi> \<equiv> Atom (Gl\<^sub>E \<Phi>)\<close>
abbreviation \<open>enabledb\<^sub>E c \<equiv> Atom (enabled_basic c)\<close>
abbreviation \<open>enabled\<^sub>E c \<equiv> Atom (enabled_cond c)\<close>
abbreviation \<open>enabledb c \<equiv> Atom (enabled_basic c)\<close>
abbreviation \<open>enabled c \<equiv> Atom (enabled_cond c)\<close>
abbreviation cond_act_pair :: \<open>\<Phi>\<^sub>M \<Rightarrow> cap \<Rightarrow> cond_act\<close> (\<open>_ \<triangleright> do _\<close>) where \<open>\<phi> \<triangleright> do a \<equiv> (\<phi>, a)\<close>

\<comment> \<open>Auxiliary function that converts mental state formulas to the type including enabledness.\<close>
fun to_\<Phi>\<^sub>E :: \<open>\<Phi>\<^sub>M \<Rightarrow> \<Phi>\<^sub>E\<close> (\<open>_\<^sup>E\<close> [100]) where
  \<open>(Atom (Bl \<Phi>))\<^sup>E = Atom (Bl\<^sub>E \<Phi>)\<close> |
  \<open>(Atom (Gl \<Phi>))\<^sup>E = Atom (Gl\<^sub>E \<Phi>)\<close> |
  \<open>\<^bold>\<bottom>\<^sup>E = \<^bold>\<bottom>\<close> |
  \<open>(\<^bold>\<not> \<phi>)\<^sup>E = \<^bold>\<not> (\<phi>\<^sup>E)\<close> |
  \<open>(\<phi>\<^sub>1 \<^bold>\<longrightarrow> \<phi>\<^sub>2)\<^sup>E = \<phi>\<^sub>1\<^sup>E \<^bold>\<longrightarrow> \<phi>\<^sub>2\<^sup>E\<close> |
  \<open>(\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2)\<^sup>E = \<phi>\<^sub>1\<^sup>E \<^bold>\<or> \<phi>\<^sub>2\<^sup>E\<close> |
  \<open>(\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2)\<^sup>E = \<phi>\<^sub>1\<^sup>E \<^bold>\<and> \<phi>\<^sub>2\<^sup>E\<close>

fun to_\<Phi>\<^sub>M :: \<open>\<Phi>\<^sub>E \<Rightarrow> \<Phi>\<^sub>M option\<close> where
  \<open>to_\<Phi>\<^sub>M (Atom (Bl\<^sub>E \<Phi>)) = Some (Atom (Bl \<Phi>))\<close> |
  \<open>to_\<Phi>\<^sub>M (Atom (Gl\<^sub>E \<Phi>)) = Some (Atom (Gl \<Phi>))\<close> |
  \<open>to_\<Phi>\<^sub>M \<^bold>\<bottom> = Some \<^bold>\<bottom>\<close> |
  \<open>to_\<Phi>\<^sub>M (\<^bold>\<not> \<phi>) = (case to_\<Phi>\<^sub>M \<phi> of Some \<phi>' \<Rightarrow> Some (\<^bold>\<not> \<phi>') | _ \<Rightarrow> None)\<close> |
  \<open>to_\<Phi>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<longrightarrow> \<phi>\<^sub>2) = (case (to_\<Phi>\<^sub>M \<phi>\<^sub>1, to_\<Phi>\<^sub>M \<phi>\<^sub>2) of (Some \<phi>\<^sub>1', Some \<phi>\<^sub>2') \<Rightarrow> Some (\<phi>\<^sub>1' \<^bold>\<longrightarrow> \<phi>\<^sub>2') | _ \<Rightarrow> None)\<close> |
  \<open>to_\<Phi>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) = (case (to_\<Phi>\<^sub>M \<phi>\<^sub>1, to_\<Phi>\<^sub>M \<phi>\<^sub>2) of (Some \<phi>\<^sub>1', Some \<phi>\<^sub>2') \<Rightarrow> Some (\<phi>\<^sub>1' \<^bold>\<or> \<phi>\<^sub>2') | _ \<Rightarrow> None)\<close> |
  \<open>to_\<Phi>\<^sub>M (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = (case (to_\<Phi>\<^sub>M \<phi>\<^sub>1, to_\<Phi>\<^sub>M \<phi>\<^sub>2) of (Some \<phi>\<^sub>1', Some \<phi>\<^sub>2') \<Rightarrow> Some (\<phi>\<^sub>1' \<^bold>\<and> \<phi>\<^sub>2') | _ \<Rightarrow> None)\<close> |
  \<open>to_\<Phi>\<^sub>M _ = None\<close>

section \<open>Semantics of GOAL\<close>

\<comment> \<open>The type for the function \<T> that gives the agent's belief update capabilities.\<close>
type_synonym bel_upd_t = \<open>Bcap \<Rightarrow> mental_state \<Rightarrow> \<Phi>\<^sub>L list option\<close>
\<comment> \<open>We replace notion of undefined (from paper) with an optional value, i.e. \<T> a \<Sigma> = None means
    that basic action a is not defined for \<Sigma>.
    We further assume that the goal base (entire mental state) is added to the input.\<close>

\<comment> \<open>The mental state transformer gives the agent's mental state update capabilities.\<close>
fun mental_state_transformer :: \<open>bel_upd_t \<Rightarrow> cap \<Rightarrow> mental_state \<Rightarrow> mental_state option\<close> (\<open>\<M>*\<close>) where
  \<comment> \<open>If \<T> a \<Sigma> is defined, update the goal base accordingly.\<close>
  \<open>\<M>* \<T> (basic n) (\<Sigma>, \<Gamma>) = (case \<T> n (\<Sigma>, \<Gamma>) of Some \<Sigma>' \<Rightarrow> Some (\<Sigma>', [\<psi><-\<Gamma>. \<not> \<Sigma>' \<^bold>\<Turnstile>\<^sub>P \<psi>]) | _ \<Rightarrow> None)\<close> |
  \<comment> \<open>Remove the goals that entail \<Phi>.\<close>
  \<open>\<M>* \<T> (drop \<Phi>) (\<Sigma>, \<Gamma>) = Some (\<Sigma>, [\<psi><-\<Gamma>. \<not> [\<psi>] \<^bold>\<Turnstile>\<^sub>P \<Phi>])\<close> |
  \<comment> \<open>Add the goal \<Phi> if it is consistent and not entailed by the belief base.\<close>
  \<open>\<M>* \<T> (adopt \<Phi>) (\<Sigma>, \<Gamma>) = (if \<not> \<Turnstile>\<^sub>P (\<^bold>\<not> \<Phi>) \<and> \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<Phi> then Some (\<Sigma>, List.insert \<Phi> \<Gamma>) else None)\<close>

lemma mst_none: \<open>\<M>* \<T> (basic a) M = None \<longleftrightarrow> \<T> a M = None\<close>
proof (cases M)
  case (Pair \<Sigma> \<Gamma>)
  have \<open>\<M>* \<T> (basic a) (\<Sigma>, \<Gamma>) = None \<longleftrightarrow> \<T> a (\<Sigma>, \<Gamma>) = None\<close> by (cases \<open>\<T> a (\<Sigma>, \<Gamma>)\<close>) auto
  with Pair show ?thesis by simp
qed

\<comment> \<open>XXX: Poorly placed and commented.\<close>
lemma new_base_is_mst: \<open>\<not> \<Sigma>' \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<Longrightarrow> \<nabla>(\<Sigma>, \<Gamma>) \<Longrightarrow> \<nabla>(\<Sigma>', [\<psi><-\<Gamma>. \<not> \<Sigma>' \<^bold>\<Turnstile>\<^sub>P \<psi>])\<close>
  unfolding is_mental_state_def by simp

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
    \<T>_consistent: \<open>\<nabla>(\<Sigma>, \<Gamma>) \<longrightarrow> (\<exists>\<phi>. (\<phi>, basic a) \<in> \<Pi>) \<longrightarrow> \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom> \<longrightarrow> \<T> a (\<Sigma>, \<Gamma>) \<noteq> None \<longrightarrow> \<not> the (\<T> a (\<Sigma>, \<Gamma>)) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> and
    \<comment> \<open>\<T> only for defined actions.\<close>
    \<T>_in_domain: \<open>\<T> a (\<Sigma>, \<Gamma>) \<noteq> None \<longrightarrow> (\<exists>\<phi>. (\<phi>, basic a) \<in> \<Pi>)\<close>

\<comment> \<open>Working in the context of single_agent, means that we can base definitions, proofs etc. around
    fixed variables for which a number of assumptions apply. For a specific agent, we need to prove
    that the assumptions apply for the given input variables. By doing so, we get immediate access
    to everything defined within the single_agent context.\<close>
context single_agent
begin

\<comment> \<open>Basic capabilities derived from the set of conditional actions.\<close>
definition Cap :: \<open>cap set\<close> where
  \<open>Cap \<equiv> { basic a | a. \<exists>\<phi>. (\<phi>, basic a) \<in> \<Pi> } \<union> range adopt \<union> range drop\<close>
\<comment> \<open>We assume that a basic capability is represented by at least one conditional action.\<close>

lemma adopt_Cap: \<open>adopt \<Phi> \<in> Cap\<close> unfolding Cap_def by simp
lemma drop_Cap: \<open>drop \<Phi> \<in> Cap\<close> unfolding Cap_def by simp

\<comment> \<open>Define mental state transformer local to the agent.\<close>
abbreviation \<open>\<M> a M \<equiv> \<M>* \<T> a M\<close>

\<comment> \<open>Examples.\<close>
lemma 
  assumes \<open>\<T> n ([P], [Q]) = Some [P, Q]\<close>
  shows \<open>\<M> (basic n) ([P], [Q]) = Some ([P, Q], [])\<close>
using assms by simp
 
lemma \<open>\<M> (drop \<^bold>\<top>) ([], [P, Q]) = Some ([], [])\<close> by simp

lemma
  assumes \<open>\<not> \<Turnstile>\<^sub>P (\<^bold>\<not> Q)\<close> and \<open>\<not> \<Turnstile>\<^sub>P Q\<close>
  shows \<open>\<M> (adopt Q) ([], [P]) = Some ([], List.insert Q [P])\<close> 
  using assms by simp

\<comment> \<open>The mental state transformer is only defined for actions of \<Pi>.\<close>
lemma \<M>_some_in_\<Pi>: 
  assumes \<open>\<M> (basic a) M \<noteq> None\<close> 
    shows \<open>\<exists>\<phi>. (\<phi>, (basic a)) \<in> \<Pi>\<close>
proof (cases M)
  case (Pair \<Sigma> \<Gamma>)
  with assms obtain \<Sigma>' \<Gamma>' where someM: \<open>\<M> (basic a) (\<Sigma>, \<Gamma>) = Some (\<Sigma>', \<Gamma>')\<close> by auto
  then have \<open>\<T> a (\<Sigma>, \<Gamma>) = Some \<Sigma>'\<close>
  proof (cases \<open>\<T> a (\<Sigma>, \<Gamma>)\<close>)
    case None
    then have \<open>\<M> (basic a) (\<Sigma>, \<Gamma>) = None\<close> by simp
    with someM show ?thesis by simp
  next
    case (Some \<Sigma>'')
    moreover have \<open>fst (the (\<M> (basic a) (\<Sigma>, \<Gamma>))) = \<Sigma>''\<close> using Some by simp
    moreover have \<open>fst (the (\<M> (basic a) (\<Sigma>, \<Gamma>))) = \<Sigma>'\<close> using someM by simp
    ultimately show ?thesis by simp
  qed    
  with \<T>_in_domain show ?thesis by blast
qed

\<comment> \<open>The mental state transformer is only defined for basic capabilities of Cap.\<close>
lemma \<M>_some_Cap:
  assumes \<open>\<M> a M \<noteq> None\<close> 
  shows \<open>a \<in> Cap\<close>
  using assms \<M>_some_in_\<Pi>
  unfolding Cap_def 
  by (cases a) auto

\<comment> \<open>Mental state transformer preserves properties of mental states (when \<T> preserves consistency).\<close>
lemma \<M>_preserves_mst: \<open>\<nabla> (\<Sigma>, \<Gamma>) \<Longrightarrow> \<M> c (\<Sigma>, \<Gamma>) \<noteq> None \<Longrightarrow> \<nabla> (the (\<M> c (\<Sigma>, \<Gamma>)))\<close>
proof (induct c)
  case basic: (basic a)
  then obtain \<Sigma>' where \<Sigma>': \<open>\<T> a (\<Sigma>, \<Gamma>) = Some \<Sigma>'\<close> by fastforce
  have \<open>\<nabla> (\<Sigma>', [\<psi><-\<Gamma>. \<not> \<Sigma>' \<^bold>\<Turnstile>\<^sub>P \<psi>])\<close> (is \<open>\<nabla> (\<Sigma>', ?\<Gamma>')\<close>)
  proof -
    have \<open>\<not> \<Sigma>' \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close>
    proof -
      from basic(1) have \<open>\<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> unfolding is_mental_state_def by simp
      moreover have \<open>\<exists>\<phi>. (\<phi>, basic a) \<in> \<Pi>\<close> using \<M>_some_in_\<Pi> basic.prems(2) by blast
      ultimately have \<open>\<not> the (\<T> a (\<Sigma>, \<Gamma>)) \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> using \<Sigma>' \<T>_consistent basic by blast
      with \<Sigma>' show ?thesis by simp
    qed
    moreover from basic(1) have \<open>\<forall>\<gamma>\<in> set ?\<Gamma>'. \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<gamma> \<and> \<not> \<Turnstile>\<^sub>P (\<^bold>\<not> \<gamma>)\<close> 
      unfolding is_mental_state_def by simp
    ultimately show ?thesis unfolding is_mental_state_def by simp
  qed
  with \<Sigma>' show ?case by simp 
next
  case adopt: (adopt \<Phi>)
  with mental_state_transformer.simps(3) have mst_goal: \<open>\<not> \<Turnstile>\<^sub>P (\<^bold>\<not> \<Phi>) \<and> \<not> \<Sigma> \<^bold>\<Turnstile>\<^sub>P \<Phi>\<close> by metis
  with adopt(1) have \<open>\<nabla> (\<Sigma>, List.insert \<Phi> \<Gamma>)\<close> unfolding is_mental_state_def by simp 
  with mst_goal show ?case by simp
next
  case (drop \<Phi>)
  then have \<open>\<nabla> (\<Sigma>, [\<psi><-\<Gamma>. \<not> [\<psi>] \<^bold>\<Turnstile>\<^sub>P \<Phi>])\<close> unfolding is_mental_state_def by simp
  then show ?case by simp
qed

section \<open>Traces\<close>

\<comment> \<open>Transition relation between states due to an action.\<close>
definition transition :: \<open>mental_state \<Rightarrow> cond_act \<Rightarrow> mental_state \<Rightarrow> bool\<close> (\<open>_ \<rightarrow>_ _\<close>) where
  \<open>M \<rightarrow>b M' \<equiv> b \<in> \<Pi> \<and> M \<Turnstile>\<^sub>M (fst b) \<and> \<M> (snd b) M = Some M'\<close>
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
    \<forall>i. ((st_nth s i) \<rightarrow>(act_nth s i) (st_nth s (i+1))) \<or> 
        (act_nth s i) \<in> \<Pi> \<and> \<M> (snd (act_nth s i)) (st_nth s i) = None \<and> (st_nth s i) = (st_nth s (i+1))\<close>
\<comment> \<open>For all i there is a transition between M_i and M_(i+1) due to an action, or the action
    is not enabled and the successor state (M_(i+1)) is equal to the current (M_i).\<close>

\<comment> \<open>The nth conditional action of a trace is in \<Pi>.\<close>
lemma trace_in_\<Pi>:
  assumes \<open>is_trace s\<close>
  shows \<open>act_nth s i \<in> \<Pi>\<close>
  using assms unfolding is_trace_def transition_def by auto

\<comment> \<open>If there is no transition between a state and its successor in a trace, they must be equal.\<close>
lemma not_transition_eq:
  assumes \<open>is_trace s\<close>
  shows \<open>\<not>((st_nth s i) \<rightarrow>(act_nth s i) (st_nth s (i+1))) \<longrightarrow> (st_nth s i) = (st_nth s (i+1))\<close>
  (is \<open>\<not>(?M \<rightarrow>?b ?M') \<longrightarrow> ?M = ?M'\<close>)
proof
  assume \<open>\<not>(?M \<rightarrow>?b ?M')\<close>
  with assms show \<open>?M = ?M'\<close> unfolding is_trace_def by auto
qed

\<comment> \<open>A fair trace ensures that there always is a future point where an actions is scheduled.\<close>
definition fair_trace :: \<open>trace \<Rightarrow> bool\<close> where
  \<open>fair_trace s \<equiv> \<forall> b \<in> \<Pi>. \<forall>i. \<exists> j > i. act_nth s j = b\<close>

\<comment> \<open>An agent is defined as the set of fair traces starting from the initial state.\<close>
definition Agent :: \<open>trace set\<close> where
  \<open>Agent \<equiv> {s . is_trace s \<and> fair_trace s \<and> st_nth s 0 = M\<^sub>0}\<close>

\<comment> \<open>Set of all possible mental states.\<close>
(*definition Agent_all_mst :: \<open>mental_state set\<close> where
  \<open>Agent_all_mst \<equiv> \<Union> (range ` st_nth ` Agent)\<close> *)

(*definition descendant :: \<open>mental_state \<Rightarrow> mental_state \<Rightarrow> bool\<close> where
  \<open>descendant M M' \<equiv> \<exists>s \<in> Agent. \<exists>i. st_nth s i = M \<and> (\<exists>j \<ge> i. st_nth s j = M')\<close>

lemma descendant_M0: \<open>s \<in> Agent \<Longrightarrow> descendant M\<^sub>0 (st_nth s i)\<close> 
  unfolding descendant_def Agent_def by auto*)

(* lemma st_nth_Agent_all_mst: \<open>s \<in> Agent \<Longrightarrow> st_nth s i \<in> Agent_all_mst\<close>
  unfolding Agent_all_mst_def by auto *)

\<comment> \<open>If the mental state transformer is defined for a state in the trace, then it gives the successor state.\<close>
lemma \<M>_suc_state:
  assumes \<open>s \<in> Agent\<close>
      and \<open>\<M> (snd (act_nth s i)) (st_nth s i) \<noteq> None\<close>
    shows \<open>st_nth s (i+1) = the (\<M> (snd (act_nth s i)) (st_nth s i))\<close>
      (is \<open>?M = the (\<M> ?a ?M')\<close>)
proof -
  from assms(1) have \<open>is_trace s\<close> unfolding Agent_def by simp
  with assms(2) have \<open>(((st_nth s i) \<rightarrow>(act_nth s i) (st_nth s (i+1))) \<or> 
        (act_nth s i) \<in> \<Pi> \<and> \<M> (snd (act_nth s i)) (st_nth s i) = None \<and> (st_nth s i) = (st_nth s (i+1)))\<close>
    unfolding is_trace_def by simp
  moreover from trace_in_\<Pi> have \<open>act_nth s i \<in> \<Pi>\<close> using \<open>is_trace s\<close> assms(2) by simp
  ultimately show ?thesis using assms(2) unfolding transition_def by simp
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
    then show ?thesis unfolding is_trace_def by auto
  qed
  then show ?case 
  proof (cases \<open>\<M> (snd ?b) ?M = None\<close>)
    case True
    with Suc trace_n show ?thesis unfolding transition_def by auto
  next
    case False
    with \<M>_preserves_mst have \<open>\<nabla> (the (\<M> (snd ?b) ?M))\<close> 
      using Suc by (cases ?M) simp
    with \<M>_suc_state trace_n show ?thesis using assms False unfolding Agent_def by simp
  qed
qed

fun the_Some :: \<open>('a \<Rightarrow> 'a option) \<Rightarrow> ('a \<Rightarrow> 'a)\<close> where
  \<open>the_Some f x = (if f x = None then x else the (f x))\<close>

abbreviation mst_basic_trace where
  \<open>mst_basic_trace \<equiv> foldr (\<lambda>a M. the_Some (\<M> a) M)\<close>

definition mst_reachable_basic :: \<open>mental_state \<Rightarrow> bool\<close> where
 \<open>mst_reachable_basic M \<equiv> \<exists>S. mst_basic_trace S M\<^sub>0 = M\<close>

lemma \<open>mst_basic_trace [a,b,c] M\<^sub>0 = the_Some (\<M> a) (the_Some (\<M> b) (the_Some (\<M> c) M\<^sub>0))\<close> by simp

lemma mst_basic_trace_preserves_mst: \<open>\<nabla>(mst_basic_trace s M\<^sub>0) \<Longrightarrow> \<M> a (mst_basic_trace s M\<^sub>0) \<noteq> None \<Longrightarrow> \<nabla>(mst_basic_trace (a # s) M\<^sub>0)\<close>
proof -
  assume \<open>\<nabla>(mst_basic_trace s M\<^sub>0)\<close> (is \<open>\<nabla>?M\<close>)
  moreover assume \<open>\<M> a ?M \<noteq> None\<close>
  ultimately have \<open>\<nabla>(the (\<M> a ?M))\<close> using \<M>_preserves_mst by (cases ?M) simp
  with \<open>\<nabla>?M\<close> show ?thesis by simp
qed

lemma mst_reachable_basic_is_mst: \<open>mst_reachable_basic M \<Longrightarrow> \<nabla>M\<close>
  unfolding mst_reachable_basic_def 
proof -
  assume \<open>\<exists>s. mst_basic_trace s M\<^sub>0 = M\<close>
  then obtain s where \<open>mst_basic_trace s M\<^sub>0 = M\<close> by auto
  moreover from is_agent have \<open>\<nabla> M\<^sub>0\<close> by simp
  then have \<open>\<nabla>(mst_basic_trace s M\<^sub>0)\<close>
  proof (induct s)
    case (Cons a s)
    then have \<open>\<nabla>(mst_basic_trace s M\<^sub>0)\<close> .
    with mst_basic_trace_preserves_mst show ?case by (cases \<open>\<M> a (mst_basic_trace s M\<^sub>0)\<close>) (simp, blast)
  qed simp
  ultimately show ?thesis by simp
qed

lemma mst_reachable_basic_\<M>: \<open>mst_reachable_basic M \<Longrightarrow> \<M> a M \<noteq> None \<Longrightarrow> mst_reachable_basic (the (\<M> a M))\<close>
proof -
  assume \<open>mst_reachable_basic M\<close>
  then obtain S where \<open>mst_basic_trace S M\<^sub>0 = M\<close> unfolding mst_reachable_basic_def by auto
  moreover assume \<open>\<M> a M \<noteq> None\<close>
  ultimately have \<open>mst_basic_trace (a # S) M\<^sub>0 = the (\<M> a M)\<close> by auto
  then show ?thesis unfolding mst_reachable_basic_def by blast
qed

lemma mst_reachable_basic_trace: 
  assumes \<open>s \<in> Agent\<close>
  shows   \<open>mst_reachable_basic (st_nth s i)\<close>
proof (induct i)
  case 0
  with assms have \<open>st_nth s 0 = M\<^sub>0\<close> unfolding Agent_def by simp
  then have \<open>mst_basic_trace [] M\<^sub>0 = (st_nth s 0)\<close> by simp
  then show ?case unfolding mst_reachable_basic_def by blast
next
  case (Suc i)
  then obtain S where *: \<open>mst_basic_trace S M\<^sub>0 = st_nth s i\<close> unfolding mst_reachable_basic_def by auto
  from assms have \<open>is_trace s\<close> unfolding Agent_def by simp
  then have 
    \<open>((st_nth s i) \<rightarrow>(act_nth s i) (st_nth s (i+1))) \<or> 
      \<M> (snd (act_nth s i)) (st_nth s i) = None \<and> (st_nth s i) = (st_nth s (i+1))\<close> 
    unfolding is_trace_def by auto
  then have 
    \<open>st_nth s (i+1) = st_nth s i \<or> \<M> (snd (act_nth s i)) (st_nth s i) \<noteq> None\<close> unfolding transition_def by auto
  then show ?case
  proof
    assume \<open>st_nth s (i + 1) = st_nth s i\<close>
    with * show ?thesis unfolding mst_reachable_basic_def by auto
  next
    assume \<open>\<M> (snd (act_nth s i)) (st_nth s i) \<noteq> None\<close>
    moreover from this \<M>_suc_state have \<open>(st_nth s (i+1)) = the (\<M> (snd (act_nth s i)) (st_nth s i))\<close> 
      using \<open>s \<in> Agent\<close> by simp
    ultimately show ?thesis using Suc mst_reachable_basic_\<M> by simp
  qed
qed

section \<open>Semantics\<close>

\<comment> \<open>Truth of enabledness (semantics).\<close>
fun semantics\<^sub>E' :: \<open>mental_state \<Rightarrow> Atom\<^sub>E \<Rightarrow> bool\<close> where
  \<comment> \<open>Semantics of B and G are the same as for mental state formulas without enabled.\<close>
  \<open>semantics\<^sub>E' M (Bl\<^sub>E \<Phi>) = (M \<Turnstile>\<^sub>M* Atom\<^sub>M.Bl \<Phi>)\<close> |
  \<open>semantics\<^sub>E' M (Gl\<^sub>E \<Phi>) = (M \<Turnstile>\<^sub>M* Atom\<^sub>M.Gl \<Phi>)\<close> |
  \<comment> \<open>a is defined for the action and \<M> a is defined for M.\<close>
  \<open>semantics\<^sub>E' M (enabled_basic a) = (a \<in> Cap \<and> \<M> a M \<noteq> None)\<close> |
  \<comment> \<open>Conditional action b is enabled if there exists a transition from M to M' using b for some M'.\<close>
  \<open>semantics\<^sub>E' M (enabled_cond b) = (\<exists>M'. (M \<rightarrow>b M'))\<close>

\<comment> \<open>Semantics of atoms with enabled can be seen as an interpretation given a mental state.\<close>
abbreviation semantics\<^sub>E :: \<open>mental_state \<Rightarrow> \<Phi>\<^sub>E \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>E\<close> 50) where
  \<open>M \<Turnstile>\<^sub>E \<phi> \<equiv> semantics\<^sub>P (semantics\<^sub>E' M) \<phi>\<close>

abbreviation semantics\<^sub>_all\<^sub>E :: \<open>\<Phi>\<^sub>E \<Rightarrow> bool\<close> (\<open>\<^bold>\<Turnstile>\<^sub>E\<close>) where
  \<open>\<^bold>\<Turnstile>\<^sub>E \<phi> \<equiv> (\<forall>M. mst_reachable_basic M \<longrightarrow> M \<Turnstile>\<^sub>E \<phi>)\<close>

abbreviation semantics\<^sub>_all\<^sub>M :: \<open>\<Phi>\<^sub>M \<Rightarrow> bool\<close> (\<open>\<^bold>\<Turnstile>\<^sub>M\<close>) where
  \<open>\<^bold>\<Turnstile>\<^sub>M \<phi> \<equiv> (\<forall>M. mst_reachable_basic M \<longrightarrow> M \<Turnstile>\<^sub>M \<phi>)\<close>

\<comment> \<open>Bel-upd-t not enabled\<close>
lemma bel_upd_not_enabled: \<open>\<T> a M = None \<Longrightarrow> \<not> M \<Turnstile>\<^sub>E enabledb (basic a)\<close>
proof -
  assume \<open>\<T> a M = None\<close>
  with mst_none have \<open>\<M> (basic a) M = None\<close> by simp
  then show \<open>\<not> M \<Turnstile>\<^sub>E enabledb (basic a)\<close> by simp
qed

\<comment> \<open>The semantics of a converted formula is equal to the original.\<close>
lemma transfer_semantics\<^sub>M: \<open>M \<Turnstile>\<^sub>M \<phi> \<longleftrightarrow> M \<Turnstile>\<^sub>E \<phi>\<^sup>E\<close> 
proof (induct \<phi>)
  case (Atom x)
  show ?case by (cases x) simp_all
qed simp_all

\<comment> \<open>Formula conversion preserves semantics\<close>
lemma sem_preserve_to_\<Phi>\<^sub>M: \<open>to_\<Phi>\<^sub>M \<phi> \<noteq> None \<Longrightarrow> M \<Turnstile>\<^sub>E \<phi> \<longleftrightarrow> M \<Turnstile>\<^sub>M (the (to_\<Phi>\<^sub>M \<phi>))\<close>
proof (induct \<phi>)
  case (Atom x)
  then show ?case by (induct x) auto
next
  case (Negation \<phi>)
  moreover from this have \<open>to_\<Phi>\<^sub>M \<phi> \<noteq> None\<close> by (metis option.simps(4) to_\<Phi>\<^sub>M.simps(4))
  ultimately show ?case by auto
next
  case (Implication \<phi>\<^sub>1 \<phi>\<^sub>2)
  moreover from this have \<open>to_\<Phi>\<^sub>M \<phi>\<^sub>1 \<noteq> None\<close> \<open>to_\<Phi>\<^sub>M \<phi>\<^sub>2 \<noteq> None\<close> 
    using case_prod_conv to_\<Phi>\<^sub>M.simps(5)
      by (metis option.simps(4), metis (no_types, lifting) option.case_eq_if)
    ultimately show ?case by auto
next
  case (Disjunction \<phi>\<^sub>1 \<phi>\<^sub>2)
  moreover from this have \<open>to_\<Phi>\<^sub>M \<phi>\<^sub>1 \<noteq> None\<close> \<open>to_\<Phi>\<^sub>M \<phi>\<^sub>2 \<noteq> None\<close> 
    using case_prod_conv to_\<Phi>\<^sub>M.simps(6)
      by (metis option.simps(4), metis (no_types, lifting) option.case_eq_if)
    ultimately show ?case by auto
next
  case (Conjunction \<phi>\<^sub>1 \<phi>\<^sub>2)
  moreover from this have \<open>to_\<Phi>\<^sub>M \<phi>\<^sub>1 \<noteq> None\<close> \<open>to_\<Phi>\<^sub>M \<phi>\<^sub>2 \<noteq> None\<close> 
    using case_prod_conv to_\<Phi>\<^sub>M.simps(7)
      by (metis option.simps(4), metis (no_types, lifting) option.case_eq_if)
    ultimately show ?case by auto
qed simp

lemma sem_set_preserve_to_\<Phi>\<^sub>M:
  assumes \<open>None \<notin> set (map to_\<Phi>\<^sub>M \<Delta>)\<close>
  shows   \<open>\<forall>\<phi> \<in> set \<Delta>. M \<Turnstile>\<^sub>E \<phi> \<longleftrightarrow> M \<Turnstile>\<^sub>M (the (to_\<Phi>\<^sub>M \<phi>))\<close>
proof
  fix \<phi>
  assume \<open>\<phi> \<in> set \<Delta>\<close> 
  with assms have \<open>to_\<Phi>\<^sub>M \<phi> \<noteq> None\<close> by force
  with sem_preserve_to_\<Phi>\<^sub>M show \<open>(M \<Turnstile>\<^sub>E \<phi>) = (M \<Turnstile>\<^sub>M the (to_\<Phi>\<^sub>M \<phi>))\<close> by simp
qed

\<comment> \<open>Example.\<close>
lemma \<open>(M\<^sub>0 \<rightarrow>b M\<^sub>1) \<Longrightarrow> M\<^sub>0 \<Turnstile>\<^sub>E enabled b\<close> 
proof -
  assume \<open>M\<^sub>0 \<rightarrow>b M\<^sub>1\<close>
  then have \<open>\<exists>M'. (M\<^sub>0 \<rightarrow>b M')\<close> by blast
  then show \<open>M\<^sub>0 \<Turnstile>\<^sub>E enabled b\<close> by simp
qed

section \<open>Proof system\<close>

inductive gen\<^sub>E :: \<open>Atom\<^sub>E gen_rules\<close> where
  E1\<^sub>E: \<open>(\<phi> \<triangleright> do a) \<in> \<Pi> \<Longrightarrow> enabled (\<phi> \<triangleright> do a) \<^bold>\<longleftrightarrow> (\<phi>\<^sup>E \<^bold>\<and> enabledb a) \<in> set \<Delta> \<Longrightarrow> gen\<^sub>E \<Gamma> \<Delta>\<close> |
  E2\<^sub>E: \<open>enabledb (drop \<Phi>) \<in> set \<Delta> \<Longrightarrow> gen\<^sub>E \<Gamma> \<Delta>\<close> |
  R3\<^sub>E: \<open>\<not> \<Turnstile>\<^sub>P (\<^bold>\<not> \<Phi>) \<Longrightarrow> \<^bold>\<not> (B\<^sub>E \<Phi>) \<^bold>\<longleftrightarrow> enabledb (adopt \<Phi>) \<in> set \<Delta> \<Longrightarrow> gen\<^sub>E \<Gamma> \<Delta>\<close> |
  R4\<^sub>E: \<open>\<Turnstile>\<^sub>P (\<^bold>\<not> \<Phi>) \<Longrightarrow> \<^bold>\<not> (enabledb (adopt \<Phi>)) \<in> set \<Delta> \<Longrightarrow> gen\<^sub>E \<Gamma> \<Delta>\<close> |
  R5\<^sub>E: \<open>\<forall>M. \<nabla>M \<longrightarrow> \<T> a M \<noteq> None \<Longrightarrow> enabledb (basic a) \<in> set \<Delta> \<Longrightarrow> gen\<^sub>E \<Gamma> \<Delta>\<close> |
  R_M: \<open>gen\<^sub>M \<Gamma> \<Delta> \<Longrightarrow> gen\<^sub>E (map to_\<Phi>\<^sub>E \<Gamma>) (map to_\<Phi>\<^sub>E \<Delta>)\<close>

abbreviation derive\<^sub>M_multi :: \<open>\<Phi>\<^sub>E list \<Rightarrow> \<Phi>\<^sub>E list \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<^sub>E#\<close> 40) where
  \<open>\<Gamma> \<turnstile>\<^sub>E# \<Delta> \<equiv> gen_sc (Some gen\<^sub>E) \<Gamma> \<Delta>\<close>

abbreviation derive\<^sub>E :: \<open>\<Phi>\<^sub>E \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>E _\<close> 40) where
  \<open>\<turnstile>\<^sub>E \<phi> \<equiv> [] \<turnstile>\<^sub>E# [ \<phi> ]\<close>

section \<open>Soundness\<close>

\<comment> \<open>The soundness theorem.\<close>

lemma soundness\<^sub>_gen\<^sub>E:
  assumes \<open>\<nabla> M\<close>
  shows \<open>gen\<^sub>E \<Gamma> \<Delta> \<Longrightarrow> \<forall>\<gamma> \<in> set \<Gamma>. M \<Turnstile>\<^sub>E \<gamma> \<Longrightarrow> \<exists>\<Phi> \<in> set \<Delta>. M \<Turnstile>\<^sub>E \<Phi>\<close>
proof (induct rule: gen\<^sub>E.induct)
  case (E1\<^sub>E \<phi> a \<Gamma> \<Delta>)
  have \<open>M \<Turnstile>\<^sub>E enabled (\<phi> \<triangleright> do a) \<longleftrightarrow> M \<Turnstile>\<^sub>M \<phi> \<and> M \<Turnstile>\<^sub>E enabledb a\<close>
  proof -
    have \<open>M \<Turnstile>\<^sub>E enabled (\<phi> \<triangleright> do a) \<longleftrightarrow> (\<exists>M'. (M \<rightarrow>(\<phi> \<triangleright> do a) M'))\<close> by simp
    also have \<open>\<dots> \<longleftrightarrow> (\<exists>M'. (\<phi> \<triangleright> do a) \<in> \<Pi> \<and> M \<Turnstile>\<^sub>M \<phi> \<and> \<M> a M = Some M')\<close> 
      unfolding transition_def by simp
    finally show ?thesis using \<open>(\<phi> \<triangleright> do a) \<in> \<Pi>\<close> \<M>_some_Cap by fastforce
  qed
  with transfer_semantics\<^sub>M have \<open>M \<Turnstile>\<^sub>E enabled (\<phi> \<triangleright> do a) \<^bold>\<longleftrightarrow> (\<phi>\<^sup>E \<^bold>\<and> enabledb a)\<close> by simp
  with E1\<^sub>E show ?case by blast
next
  case (E2\<^sub>E \<Phi> \<Delta> \<Gamma>)
  moreover have \<open>\<M> (drop \<Phi>) M \<noteq> None\<close> using mental_state_transformer.simps(2) by (cases M) simp
  ultimately show ?case using \<M>_some_Cap by (metis semantics\<^sub>E'.simps(3) semantics\<^sub>P.simps(1))
next
  case (R3\<^sub>E \<Phi>)
  with adopt_Cap have \<open>M \<Turnstile>\<^sub>E \<^bold>\<not> (B\<^sub>E \<Phi>) \<^bold>\<longleftrightarrow> enabledb (adopt \<Phi>)\<close> using \<M>_some_Cap by (cases M) simp
  with R3\<^sub>E show ?case by blast
next
  case (R4\<^sub>E \<Phi> \<Delta> \<Gamma>)
  then have \<open>\<forall>M. \<M> (adopt \<Phi>) M = None\<close> by fastforce
  then have \<open>\<M> (adopt \<Phi>) M = None\<close> by blast
  then have \<open>M \<Turnstile>\<^sub>E \<^bold>\<not> (enabledb (adopt \<Phi>))\<close> by simp
  with R4\<^sub>E show ?case by blast
next
  case (R5\<^sub>E a \<Delta> \<Gamma>)
  then have \<open>\<T> a M \<noteq> None\<close> using \<open>\<nabla>M\<close> by blast
  then have \<open>\<M> (basic a) M \<noteq> None\<close> by (cases M) auto
  with \<M>_some_Cap have \<open>M \<Turnstile>\<^sub>E enabledb (basic a)\<close> by simp
  with R5\<^sub>E show ?case by blast
next
  case (R_M \<Gamma> \<Delta>)
  with transfer_semantics\<^sub>M have \<open>\<forall>\<gamma> \<in> set \<Gamma>. M \<Turnstile>\<^sub>M \<gamma>\<close> by simp
  with soundness\<^sub>_gen\<^sub>M have \<open>\<exists>\<Phi> \<in> set \<Delta>. M \<Turnstile>\<^sub>M \<Phi>\<close>  using R_M assms by simp
  with transfer_semantics\<^sub>M show ?case by simp
qed

lemma soundness\<^sub>E':
  assumes \<open>\<nabla> M\<close>
  shows \<open>gen_sc R \<Gamma> \<Delta> \<Longrightarrow> R = Some gen\<^sub>E \<Longrightarrow> \<forall>\<gamma> \<in> set \<Gamma>. M \<Turnstile>\<^sub>E \<gamma> \<Longrightarrow> \<exists>\<Phi> \<in> set \<Delta>. M \<Turnstile>\<^sub>E \<Phi>\<close>
proof (induct rule: gen_sc.induct)
  case (Gen R \<Gamma> \<Delta>)
  with soundness\<^sub>_gen\<^sub>E show ?case using assms by simp
qed auto

theorem soundness\<^sub>E:
  assumes \<open>\<nabla> M\<close>
  shows \<open>\<turnstile>\<^sub>E \<phi> \<Longrightarrow> M \<Turnstile>\<^sub>E \<phi>\<close>
  using soundness\<^sub>E' assms by fastforce

end
end