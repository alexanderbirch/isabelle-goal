(*
  Goal verification framework
  - Logic
*)

\<comment> \<open>This theory sets up syntax, semantics and a sequent for classical logic with no quantifiers.
    The type for an extension is arbitrary to allow reuse in different logic languages to be defined.\<close>

theory Gvf_Logic imports Main begin

section \<open>Syntax\<close> 

\<comment> \<open>The usual infix operators are in bold to avoid conflict with Isabelle's built-in operators.\<close>
datatype 'a \<Phi>\<^sub>P = Atom (the_atom: 'a) | F (\<open>\<^bold>\<bottom>\<close>) | Negation \<open>'a \<Phi>\<^sub>P\<close> (\<open>\<^bold>\<not>\<close>) | 
                 Implication \<open>'a \<Phi>\<^sub>P\<close> \<open>'a \<Phi>\<^sub>P\<close> (infixr \<open>\<^bold>\<longrightarrow>\<close> 60) | 
                 Disjunction \<open>'a \<Phi>\<^sub>P\<close> \<open>'a \<Phi>\<^sub>P\<close> (infixl \<open>\<^bold>\<or>\<close> 70) | 
                 Conjunction \<open>'a \<Phi>\<^sub>P\<close> \<open>'a \<Phi>\<^sub>P\<close> (infixl \<open>\<^bold>\<and>\<close> 80)
\<comment> \<open>'a is a type variable for the type of the extension. 
    An element of this type is parsed to the constructor for Atom.
    The Boolean operators take one (or two) formula(s) as input (parsing on the type variable).\<close>

\<comment> \<open>Define a type for propositional logic formulas using string symbols.\<close>
type_synonym \<Phi>\<^sub>L = \<open>string \<Phi>\<^sub>P\<close>

\<comment> \<open>Bi-implication is defined from conjunction and implication.\<close>
abbreviation Equiv\<^sub>P :: \<open>'a \<Phi>\<^sub>P \<Rightarrow> 'a \<Phi>\<^sub>P \<Rightarrow> 'a \<Phi>\<^sub>P\<close> (infix \<open>\<^bold>\<longleftrightarrow>\<close> 60) where
  \<open>P \<^bold>\<longleftrightarrow> Q \<equiv> (P \<^bold>\<longrightarrow> Q) \<^bold>\<and> (Q \<^bold>\<longrightarrow> P)\<close>

abbreviation Truth\<^sub>L :: \<open>'a \<Phi>\<^sub>P\<close> (\<open>\<^bold>\<top>\<close>) 
  where \<open>\<^bold>\<top> \<equiv> \<^bold>\<not> \<^bold>\<bottom>\<close>

\<comment> \<open>Example.\<close>
value \<open>P \<^bold>\<longrightarrow> (P \<^bold>\<longrightarrow> Q) \<^bold>\<longrightarrow> Q\<close>

section \<open>Semantics\<close>

\<comment> \<open>The semantics function takes an interpretation and a formula and returns a Boolean.\<close>
primrec semantics\<^sub>P :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a \<Phi>\<^sub>P \<Rightarrow> bool\<close> where
  \<open>semantics\<^sub>P f (Atom x) = f x\<close> |
  \<open>semantics\<^sub>P f \<^bold>\<bottom> = False\<close> |
  \<open>semantics\<^sub>P f (\<^bold>\<not> p) = (\<not>semantics\<^sub>P f p)\<close> |
  \<open>semantics\<^sub>P f (p \<^bold>\<longrightarrow> q) = (semantics\<^sub>P f p \<longrightarrow> semantics\<^sub>P f q)\<close> |
  \<open>semantics\<^sub>P f (p \<^bold>\<or> q) = (semantics\<^sub>P f p \<or> semantics\<^sub>P f q)\<close> |
  \<open>semantics\<^sub>P f (p \<^bold>\<and> q) = (semantics\<^sub>P f p \<and> semantics\<^sub>P f q)\<close>
\<comment> \<open>The interpretation f is a function from elements of type 'a to Booleans.
    In the case of Atom the value is looked up and returned.
    In case of a Boolean operator, we can exploit Isabelle's built-in operators.
    This could also be achieved by proper coding of if-then structures.\<close>

\<comment> \<open>Example (holds for any f, P and Q).\<close>
lemma \<open>semantics\<^sub>P f (P \<^bold>\<longrightarrow> (P \<^bold>\<longrightarrow> Q) \<^bold>\<longrightarrow> Q)\<close> by simp

\<comment> \<open>Entailment.\<close>
abbreviation entails :: \<open>'a \<Phi>\<^sub>P list \<Rightarrow> 'a \<Phi>\<^sub>P list \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>P#\<close> 50) where
  \<open>\<Gamma> \<Turnstile>\<^sub>P# \<Delta> \<equiv> (\<forall>f. (\<forall>p\<in>set \<Gamma>. semantics\<^sub>P f p) \<longrightarrow> (\<exists>p\<in>set \<Delta>. semantics\<^sub>P f p))\<close>
\<comment> \<open>L entails R if, for all interpretations, all formulas in L true implies at least one in R true.\<close>

\<comment> \<open>Example.\<close>
lemma \<open>[ P ] \<Turnstile>\<^sub>P# [ P, Q ]\<close> by simp

\<comment> \<open>Entailment for a singleton on rhs.\<close>
abbreviation entails_singleton :: \<open>'a \<Phi>\<^sub>P list \<Rightarrow> 'a \<Phi>\<^sub>P \<Rightarrow> bool\<close> (infix \<open>\<^bold>\<Turnstile>\<^sub>P\<close> 50) where
  \<open>\<Gamma> \<^bold>\<Turnstile>\<^sub>P \<Phi> \<equiv> (\<forall>f. (\<forall>p\<in>set \<Gamma>. semantics\<^sub>P f p) \<longrightarrow> semantics\<^sub>P f \<Phi>)\<close>

abbreviation entails_all_singleton :: \<open>'a \<Phi>\<^sub>P \<Rightarrow> bool\<close> (\<open>\<Turnstile>\<^sub>P\<close>) where
  \<open>\<Turnstile>\<^sub>P \<Phi> \<equiv> (\<forall>f. semantics\<^sub>P f \<Phi>)\<close>

\<comment> \<open>Not derive contradiction\<close>
lemma not_contradict: \<open>\<exists>f. \<forall>p\<in>set P. semantics\<^sub>P f p \<Longrightarrow> \<not> P \<^bold>\<Turnstile>\<^sub>P \<^bold>\<bottom>\<close> by simp

\<comment> \<open>Example.\<close>
lemma \<open>[ P \<^bold>\<and> Q ] \<^bold>\<Turnstile>\<^sub>P P\<close> by simp

\<comment> \<open>Example.\<close>
lemma \<open>Q \<noteq> P \<longrightarrow> \<not> [ Atom Q ] \<^bold>\<Turnstile>\<^sub>P Atom P\<close> by auto

\<comment> \<open>Weakening of assumptions for entailment\<close>
lemma weakening_entailment: \<open>set \<Sigma>' \<subseteq> set \<Sigma> \<longrightarrow> \<Sigma>' \<Turnstile>\<^sub>P# \<Gamma> \<longrightarrow> \<Sigma> \<Turnstile>\<^sub>P# \<Gamma>\<close> by blast

\<comment> \<open>Example.\<close>
lemma \<open>[ P\<^sub>1, P\<^sub>2 ] \<Turnstile>\<^sub>P# [ Q ] \<longrightarrow> [ P\<^sub>1, P\<^sub>2, P\<^sub>3 ] \<Turnstile>\<^sub>P# [ Q ]\<close> using weakening_entailment by simp

section \<open>Sequent calculus\<close>

abbreviation append_new :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>append_new L R \<equiv> L @ (filter (\<lambda>x. x \<notin> set L) R)\<close>

type_synonym 'a gen_rules = \<open>'a \<Phi>\<^sub>P list \<Rightarrow> 'a \<Phi>\<^sub>P list \<Rightarrow> bool\<close>

\<comment> \<open>Generic sequent calculus proof system.\<close>
inductive gen_sc :: \<open>'a gen_rules option \<Rightarrow> 'a \<Phi>\<^sub>P list \<Rightarrow> 'a \<Phi>\<^sub>P list \<Rightarrow> bool\<close> where
  \<comment> \<open>Base axiom\<close>
  Axiom:  \<open>p \<in> set \<Gamma> \<Longrightarrow> p \<in> set \<Delta> \<Longrightarrow> gen_sc R \<Gamma> \<Delta>\<close> |
  \<comment> \<open>Logical non-branching\<close>
  L_Neg:  \<open>gen_sc R \<Gamma> (p # \<Delta>) \<Longrightarrow> gen_sc R ((\<^bold>\<not> p) # \<Gamma>) \<Delta>\<close> |
  R_Neg:  \<open>gen_sc R (p # \<Gamma>) \<Delta> \<Longrightarrow> gen_sc R \<Gamma> ((\<^bold>\<not> p) # \<Delta>)\<close> |
  R_Imp:  \<open>gen_sc R (p # \<Gamma>) (q # \<Delta>) \<Longrightarrow> gen_sc R \<Gamma> ((p \<^bold>\<longrightarrow> q) # \<Delta>)\<close> |
  R_Or:   \<open>gen_sc R \<Gamma> (p # q # \<Delta>) \<Longrightarrow> gen_sc R \<Gamma> ((p \<^bold>\<or> q) # \<Delta>)\<close> |
  L_And:  \<open>gen_sc R (p # q # \<Gamma>) \<Delta> \<Longrightarrow> gen_sc R ((p \<^bold>\<and> q) # \<Gamma>) \<Delta>\<close> |
  \<comment> \<open>Logical branching\<close>
  R_And:  \<open>gen_sc R \<Gamma> (p # \<Delta>) \<Longrightarrow> gen_sc R \<Gamma> (q # \<Delta>) \<Longrightarrow> gen_sc R \<Gamma> ((p \<^bold>\<and> q) # \<Delta>)\<close> |
  L_Or:   \<open>gen_sc R (p # \<Gamma>) \<Delta> \<Longrightarrow> gen_sc R (q # \<Gamma>) \<Delta> \<Longrightarrow> gen_sc R ((p \<^bold>\<or> q) # \<Gamma>) \<Delta>\<close> |
  L_Imp:  \<open>gen_sc R \<Gamma> (p # \<Delta>) \<Longrightarrow> gen_sc R (q # \<Gamma>) \<Delta> \<Longrightarrow> gen_sc R ((p \<^bold>\<longrightarrow> q) # \<Gamma>) \<Delta>\<close> |
  \<comment> \<open>Cut\<close>
  Cut:    \<open>gen_sc R \<Gamma> (p # \<Delta>) \<Longrightarrow> gen_sc R (p # \<Sigma>) \<Pi> \<Longrightarrow> gen_sc R (append_new \<Gamma> \<Sigma>) (append_new \<Delta> \<Pi>)\<close> |
  \<comment> \<open>Weakening\<close>
  L_W:    \<open>gen_sc R \<Gamma> \<Delta> \<Longrightarrow> gen_sc R (\<Sigma> @ \<Gamma>) \<Delta>\<close> |
  R_W:    \<open>gen_sc R \<Gamma> \<Delta> \<Longrightarrow> gen_sc R \<Gamma> (\<Pi> @ \<Delta>)\<close> |
  \<comment> \<open>Shift\<close>
  L_Shift: \<open>gen_sc R (rotate1 \<Gamma>) \<Delta> \<Longrightarrow> gen_sc R \<Gamma> \<Delta>\<close> |
  R_Shift: \<open>gen_sc R \<Gamma> (rotate1 \<Delta>) \<Longrightarrow> gen_sc R \<Gamma> \<Delta>\<close> |
  \<comment> \<open>Generic\<close>
  Gen:    \<open>R \<noteq> None \<Longrightarrow> the R \<Gamma> \<Delta> \<Longrightarrow> gen_sc R \<Gamma> \<Delta>\<close>

lemma weakening_h:
  assumes \<open>gen_sc R \<Gamma> \<Delta>\<close>
  shows \<open>gen_sc R (p # \<Gamma>) \<Delta>\<close> \<open>gen_sc R \<Gamma> (p # \<Delta>)\<close>
proof -
  from L_W have \<open>gen_sc R ([p] @ \<Gamma>) \<Delta>\<close> using assms by blast
  then show \<open>gen_sc R (p # \<Gamma>) \<Delta>\<close> by simp
  from R_W have \<open>gen_sc R \<Gamma> ([p] @ \<Delta>)\<close> using assms by blast
  then show \<open>gen_sc R \<Gamma> (p # \<Delta>)\<close> by simp
qed 

\<comment> \<open>XXX\<close>
lemma gen_sc_None: \<open>gen_sc R \<Gamma> \<Delta> \<Longrightarrow> R = None \<Longrightarrow> gen_sc R' \<Gamma> \<Delta>\<close>
proof (induct rule: gen_sc.induct)
  case (Axiom R \<Gamma> p \<Delta>)
  with gen_sc.Axiom show ?case by auto
next
  case (L_Neg R \<Gamma> \<Delta> p)
  with gen_sc.L_Neg show ?case by simp
next
  case (R_Neg R \<Gamma> p \<Delta>)
  with gen_sc.R_Neg show ?case by simp
next
  case (R_Imp R \<Gamma> p \<Delta> q)
  with gen_sc.R_Imp show ?case by simp
next
  case (R_Or R \<Gamma> \<Delta> p q)
  with gen_sc.R_Or show ?case by simp
next
  case (L_And R \<Gamma> p q \<Delta>)
  with gen_sc.L_And show ?case by simp
next
  case (R_And R \<Gamma> \<Delta> p q)
  with gen_sc.R_And show ?case by simp
next
  case (L_Or R \<Gamma> p \<Delta> q)
  with gen_sc.L_Or show ?case by simp
next
  case (L_Imp R \<Gamma> \<Delta> p q)
  with gen_sc.L_Imp show ?case by simp
next
  case (Cut R \<Gamma> p \<Delta> \<Sigma> \<Pi>)
  with gen_sc.Cut show ?case by simp
next
  case (L_W R \<Gamma> \<Delta> \<Sigma>)
  with gen_sc.L_W show ?case by simp
next
  case (R_W R \<Gamma> \<Delta> \<Pi>)
  with gen_sc.R_W show ?case by simp
next
  case (Gen r \<Gamma> \<Delta>)
  with gen_sc.Gen show ?case by simp
next
  case (L_Shift R \<Gamma> \<Delta>)
  with gen_sc.L_Shift show ?case by simp
next
  case (R_Shift R \<Gamma> \<Delta>)
  with gen_sc.R_Shift show ?case by simp
qed

abbreviation sequent_calculus :: \<open>'a \<Phi>\<^sub>P list \<Rightarrow> 'a \<Phi>\<^sub>P list \<Rightarrow> bool\<close> (infix \<open>\<turnstile>\<^sub>P#\<close> 40) where
  \<open>\<Gamma> \<turnstile>\<^sub>P# \<Delta> \<equiv> gen_sc None \<Gamma> \<Delta>\<close>

\<comment> \<open>Example.\<close>
lemma \<open>[ P \<^bold>\<and> Q ] \<turnstile>\<^sub>P# [ P ]\<close>
proof -
  from Axiom[where p=P] have \<open>[ P, Q ] \<turnstile>\<^sub>P# [ P ]\<close> by simp
  then show ?thesis using L_And by force
qed

\<comment> \<open>Notation for empty lhs and singleton rhs.\<close>
abbreviation provable :: \<open>'a \<Phi>\<^sub>P \<Rightarrow> bool\<close> (\<open>\<turnstile>\<^sub>P _\<close> 40) where
  \<open>\<turnstile>\<^sub>P p \<equiv> [] \<turnstile>\<^sub>P# [ p ]\<close>

\<comment> \<open>Modus ponens\<close>
lemma gen_sc_mp: \<open>gen_sc R \<Gamma> [ p \<^bold>\<longrightarrow> q ] \<Longrightarrow> gen_sc R \<Gamma> [ p ] \<Longrightarrow> gen_sc R \<Gamma> [ q ]\<close> 
proof -
  assume \<open>gen_sc R \<Gamma> [ p \<^bold>\<longrightarrow> q ]\<close>
  moreover assume \<open>gen_sc R \<Gamma> [ p ]\<close>
  with weakening_h(2) have \<open>gen_sc R \<Gamma> [q, p]\<close> by auto
  with R_Shift have \<open>gen_sc R \<Gamma> [p, q]\<close> by force
  from Axiom[where p=q] have \<open>gen_sc R (q # \<Gamma>) [ q ]\<close> by simp  
  with \<open>gen_sc R \<Gamma> [p, q]\<close> have \<open>gen_sc R ((p \<^bold>\<longrightarrow> q) # \<Gamma>) [ q ]\<close> using L_Imp by blast
  ultimately show \<open>gen_sc R \<Gamma> [ q ]\<close> using Cut by fastforce
qed

\<comment> \<open>Example single-step.\<close>
lemma \<open>\<turnstile>\<^sub>P P \<^bold>\<longrightarrow> (P \<^bold>\<longrightarrow> Q) \<^bold>\<longrightarrow> Q\<close> 
proof -
  from R_Imp have \<open>[] \<turnstile>\<^sub>P# [ P \<^bold>\<longrightarrow> (P \<^bold>\<longrightarrow> Q) \<^bold>\<longrightarrow> Q ]\<close>
    if \<open>[ P ] \<turnstile>\<^sub>P# [ (P \<^bold>\<longrightarrow> Q) \<^bold>\<longrightarrow> Q ]\<close> using that by blast
  with R_Imp have ?thesis 
    if \<open>[ P \<^bold>\<longrightarrow> Q, P ] \<turnstile>\<^sub>P# [ Q ]\<close> using that by fastforce
  with L_Imp have ?thesis 
    if  \<open>[ P ] \<turnstile>\<^sub>P# [ P, Q ]\<close>
    and \<open>[ Q, P ] \<turnstile>\<^sub>P# [ Q ]\<close> using that by fastforce
  moreover have \<open>[ P ] \<turnstile>\<^sub>P# [ P, Q ]\<close> using Axiom[where p=P] by simp
  moreover have \<open>([ Q, P ]) \<turnstile>\<^sub>P# [ Q ]\<close> using Axiom[where p=Q] by simp
  ultimately show ?thesis by simp
qed
\<comment> \<open>The hassle of manually proving even simple formulas calls for an implementation of proof tactics.
    The deep embedding of the logic means that trivial formulas cannot be proved using Isabelle's
    vast knowledge about logic formulas, however I am not sure if there is a good way around this.\<close>

section \<open>Misc.\<close>

lemma neg_imp: \<open>\<turnstile>\<^sub>P (p \<^bold>\<longrightarrow> \<^bold>\<not> q) \<^bold>\<longrightarrow> q \<^bold>\<longrightarrow> \<^bold>\<not> p\<close>
proof -
  from R_Imp have ?thesis
    if \<open>[ p \<^bold>\<longrightarrow> \<^bold>\<not> q ] \<turnstile>\<^sub>P# [ q \<^bold>\<longrightarrow> \<^bold>\<not> p ]\<close> using that by blast
  with R_Imp have ?thesis
    if \<open>[ q, p \<^bold>\<longrightarrow> \<^bold>\<not> q ] \<turnstile>\<^sub>P# [ \<^bold>\<not> p ]\<close> using that by blast
  with R_Neg have ?thesis
    if \<open>[ p, q, p \<^bold>\<longrightarrow> \<^bold>\<not> q ] \<turnstile>\<^sub>P# []\<close> using that by fastforce
  moreover have \<open>rotate1 (rotate1 [ p, q, p \<^bold>\<longrightarrow> \<^bold>\<not> q ]) = [ p \<^bold>\<longrightarrow> \<^bold>\<not> q, p, q ]\<close> by simp
  ultimately have ?thesis 
    if \<open>[ p \<^bold>\<longrightarrow> \<^bold>\<not> q, p, q ] \<turnstile>\<^sub>P# []\<close> using that L_Shift by metis
  with L_Imp have ?thesis
    if \<open>[ p, q ] \<turnstile>\<^sub>P# [ p ]\<close> and \<open>[ \<^bold>\<not> q, p, q ] \<turnstile>\<^sub>P# []\<close> using that by blast
  with L_Neg have ?thesis
    if \<open>[ p, q ] \<turnstile>\<^sub>P# [ p ]\<close> and \<open>[ p, q ] \<turnstile>\<^sub>P# [ q ]\<close> using that by blast
  with Axiom[where p=p] Axiom[where p=q] show ?thesis by simp
qed

\<comment> \<open>Proofs about the formulas that are not entailed are in general harder, so the idea is to collect
    a number of proofs in a small library as we encounter the need to complete such proofs.\<close>
lemma neq_ext_not_entail: 
  assumes \<open>x \<noteq> y\<close> 
  shows   \<open>\<not> [ Atom x ] \<^bold>\<Turnstile>\<^sub>P Atom y\<close> 
  using assms by auto

fun distinct_ground_atoms_aux :: \<open>'a \<Phi>\<^sub>P list \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  \<open>distinct_ground_atoms_aux (Atom p # L) P = distinct_ground_atoms_aux L (p#P)\<close> |
  \<open>distinct_ground_atoms_aux (\<^bold>\<not> (Atom p) # L) P = (p \<notin> set P \<and> distinct_ground_atoms_aux L P)\<close> |
  \<open>distinct_ground_atoms_aux _ _ = False\<close>

fun distinct_ground_atoms :: \<open>'a \<Phi>\<^sub>P list \<Rightarrow> bool\<close> where
  \<open>distinct_ground_atoms L = distinct_ground_atoms_aux L []\<close>

section \<open>Soundness\<close>

\<comment> \<open>Proving the formula implies that it is valid. Because the sequent calculus is based on the use
    of multisets, whereas the semantics is based on regular sets, a conversion is required.
    In general going from multisets to sets is more clean due to the former always being finite.\<close>

\<comment> \<open>The soundness theorem.\<close>
lemma soundness\<^sub>P': \<open>gen_sc R \<Gamma> \<Delta> \<Longrightarrow> R = None \<Longrightarrow> \<Gamma> \<Turnstile>\<^sub>P# \<Delta>\<close>
proof (induct rule: gen_sc.induct)
  case (Cut R \<Gamma> \<Delta> p \<Sigma> \<Pi>)
  then show ?case by fastforce
qed auto

theorem soundness\<^sub>P: \<open>\<Gamma> \<turnstile>\<^sub>P# \<Delta> \<Longrightarrow> \<Gamma> \<Turnstile>\<^sub>P# \<Delta>\<close>
  using soundness\<^sub>P' by blast

end