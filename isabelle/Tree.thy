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

lemma tree_ne_Tip_iff_eq_Node:
  \<open>tree \<noteq> Tip \<longleftrightarrow> (\<exists> left' item' right'. tree = Node left' item' right')\<close>
  by (blast intro: tree.exhaust_sel)

lemmas tree_simps = tree.case_eq_if tree_ne_Tip_iff_eq_Node

abbreviation \<open>Leaf \<equiv> flip (Node Tip) Tip\<close>

abbreviation
  \<open>tree_to_set \<equiv>
    rec_tree \<emptyset> (\<lambda> _ item' _ left_set. insert item' <<< (\<union>) left_set)\<close>

(* abbreviation \<open>min_tree \<equiv> Min <<< tree_to_set\<close>
abbreviation \<open>max_tree \<equiv> Max <<< tree_to_set\<close> *)

fun tree_ordered :: \<open>'a::{linorder} tree \<Rightarrow> bool\<close> where
  \<open>tree_ordered Tip = True\<close> |
  \<open>tree_ordered (Node left' item' right') = (
    tree_ordered left' \<and>
    tree_ordered right' \<and> (
    let cmp = \<lambda> x ord tree. case tree of
      Tip \<Rightarrow> True |
      Node _ item' _ \<Rightarrow> ord x item'
    in cmp item' (\<ge>) left' \<and> cmp item' (\<le>) right'))\<close>

fun ins :: \<open>'a::{linorder} \<Rightarrow> 'a tree \<Rightarrow> 'a tree\<close> where
  \<open>ins x Tip = Leaf x\<close> |
  \<open>ins x (Node left' val' right' =: tree) = (
    if x = val' then tree
    else if x < val' then Node (ins x left') val' right'
    else Node left' val' (ins x right'))\<close>

lemma ins_correct_1:
  \<open>tree_to_set (ins x tree) = insert x (tree_to_set tree)\<close>
  apply (induction tree) by auto

lemma ins_correct_2:
  assumes \<open>tree_ordered tree\<close>
  shows \<open>tree_ordered <| ins x tree\<close>
 using assms
 apply (induction tree)
 by (auto simp add: tree_simps elim!: ins.elims)

end

end