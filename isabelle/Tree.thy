theory Tree

imports
  "HOL-Library.Pattern_Aliases"
  Utils_Basic

begin

context
  includes pattern_aliases
begin

(* Exercise 3.1 of
https://isabelle.in.tum.de/doc/prog-prove.pdf *)

datatype 'a tree =
  Tip |
  Node (left: \<open>'a tree\<close>) (item: 'a) (right: \<open>'a tree\<close>)

abbreviation \<open>Leaf \<equiv> flip (Node Tip) Tip\<close>

abbreviation \<open>tree_to_set \<equiv> rec_tree \<emptyset> (\<lambda> _ item' _. insert item' >>> (\<union>))\<close>

definition tree_ordered :: \<open>'a::{linorder} tree \<Rightarrow> bool\<close> where
  \<open>tree_ordered \<equiv> rec_tree True (
    \<lambda> left' item' right' left_ordered right_ordered.
      left_ordered \<and> right_ordered \<and>
      (\<forall> x \<in> tree_to_set left'. x \<le> item') \<and>
      (\<forall> x \<in> tree_to_set right'. x \<ge> item'))\<close>

fun ins :: \<open>'a::{linorder} \<Rightarrow> 'a tree \<Rightarrow> 'a tree\<close> where
  \<open>ins x Tip = Leaf x\<close> |
  \<open>ins x (Node left' val' right' =: tree) = (
    if x = val' then tree
    else if x < val' then Node (ins x left') val' right'
    else Node left' val' (ins x right'))\<close>

lemma tree_to_set_ins_eq_insert_tree_to_set [simp]:
  \<open>tree_to_set (ins x tree) = insert x (tree_to_set tree)\<close>
  by (induction tree) auto

lemma tree_ordered_ins_of_ordered:
  \<open>tree_ordered tree \<Longrightarrow> tree_ordered (ins x tree)\<close>
  by (induction tree) (auto simp add: tree_ordered_def)

end

end