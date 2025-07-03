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

definition tree_to_set :: \<open>'a tree \<Rightarrow> 'a set\<close> where
  \<open>tree_to_set \<equiv> rec_tree \<emptyset> (\<lambda> _ item' _. insert item' >>> (\<union>))\<close>

(* abbreviation \<open>min_tree \<equiv> Min <<< tree_to_set\<close>
abbreviation \<open>max_tree \<equiv> Max <<< tree_to_set\<close> *)

definition tree_ordered :: \<open>'a::{linorder} tree \<Rightarrow> bool\<close> where
  \<open>tree_ordered \<equiv> rec_tree True (
    \<lambda> left' item' right' left_ordered right_ordered.
      left_ordered \<and> right_ordered \<and> (
      let cmp = \<lambda> x ord tree. tree = Tip \<or> ord x (item tree)
      in cmp item' (\<ge>) left' \<and> cmp item' (\<le>) right'))\<close>

fun ins :: \<open>'a::{linorder} \<Rightarrow> 'a tree \<Rightarrow> 'a tree\<close> where
  \<open>ins x Tip = Leaf x\<close> |
  \<open>ins x (Node left' val' right' =: tree) = (
    if x = val' then tree
    else if x < val' then Node (ins x left') val' right'
    else Node left' val' (ins x right'))\<close>

lemma item_ins_eq:
  \<open>item (ins x tree) = (if tree = Tip then x else item tree)\<close>
  by (cases tree) auto

(* lemma ins_ne_tip [simp]:
  \<open>ins x tree \<noteq> Tip\<close>
  by (cases tree) auto *)

lemma ins_correct_1:
  \<open>tree_to_set (ins x tree) = insert x (tree_to_set tree)\<close>
  by (induction tree) (auto simp add: tree_to_set_def)

lemma ins_correct_2:
  \<open>tree_ordered tree \<Longrightarrow> tree_ordered (ins x tree)\<close>
  by (induction tree) (auto simp add: tree_ordered_def item_ins_eq)

end

end