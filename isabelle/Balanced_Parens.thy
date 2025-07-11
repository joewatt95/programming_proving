theory Balanced_Parens

imports
  "HOL-Library.Pattern_Aliases"
  Utils_Basic

begin

datatype paren = open_paren | close_paren

type_synonym parens = \<open>paren list\<close>

inductive balanced_ind :: \<open>parens \<Rightarrow> bool\<close> where
  empty [simp]: \<open>balanced_ind []\<close> |
  balanced_ind_pair:
    \<open>balanced_ind <| open_paren # parens @ [close_paren]\<close>
    if \<open>balanced_ind parens\<close> |
  balanced'_append:
    \<open>balanced_ind <| parens @ parens'\<close>
    if \<open>balanced_ind parens\<close> \<open>balanced_ind parens'\<close>

lemma even_length_of_balanced_ind:
  assumes \<open>balanced_ind parens\<close>
  shows \<open>even <| length parens\<close>
  using assms by (induction parens) auto

definition
  \<open>empty_or_balanced \<equiv> \<lambda> parens.
    parens = [] \<or> (\<exists> parens'. parens = open_paren # parens' @ [close_paren])\<close>

(* lemma
  assumes \<open>\<And> parens. parens \<in> set parenss \<Longrightarrow> balanced_ind parens\<close>
  shows \<open>balanced_ind <| concat parenss\<close>
  using assms by (induction parenss) (auto intro: balanced_ind.intros) *)

lemma
  \<open>balanced_ind parens \<longleftrightarrow> (
    \<exists> parens' parens''.
      empty_or_balanced parens' \<and> empty_or_balanced parens'' \<and>
      parens = parens' @ parens'')\<close>
proof (induction parens)
  case Nil
  then show ?case by (simp add: empty_or_balanced_def)
next
  case (Cons a parens)
  then show ?case
    apply (simp add: empty_or_balanced_def)
    sorry
qed

(* lemma
  assumes
    \<open>balanced_ind <| open_paren # parens @ [close_paren]\<close>
    (is \<open>balanced_ind ?parens'\<close>)
  shows \<open>balanced_ind parens\<close>
  using assms
  apply (induction ?parens' rule: balanced_ind.induct)
  apply auto
  sorry *)

definition balanced :: \<open>nat \<Rightarrow> parens \<Rightarrow> bool\<close> where
  \<open>balanced n = (
    let
      is_empty = (=) [];
      op = \<lambda> seen_parens paren. case (seen_parens, paren) of
        (open_paren # seen_parens, close_paren) \<Rightarrow> seen_parens |
        _ \<Rightarrow> paren # seen_parens;
      seen_parens = replicate n open_paren
    in foldl op seen_parens >>> is_empty)\<close>

lemma
  \<open>balanced 0 parens \<longleftrightarrow> balanced_ind parens\<close>
  (is \<open>?L \<longleftrightarrow> ?R\<close>)
proof (intro iffI)
  assume ?L
  then show ?R
    sorry
next
  assume ?R
  then show ?L
    apply (induction parens rule: balanced_ind.induct)
    sorry
qed

lemma
  \<open>balanced n parens \<longleftrightarrow> balanced_ind (replicate n open_paren @ parens)\<close>
  (is \<open>?L \<longleftrightarrow> ?R\<close>)
proof (intro iffI)
  assume ?L
  then show ?R
    sorry
next
  assume ?R
  then show ?L
    sorry
qed

end