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

definition ord :: \<open>'a::ord tree \<Rightarrow> bool\<close> where
  \<open>ord \<equiv> rec_tree True (
    \<lambda> left' item' right' left_ord right_ord.
      left_ord \<and> right_ord \<and> (
        let cmp_item = \<lambda> cmp tree. \<forall> x \<in> tree_to_set tree. cmp item' x
        in cmp_item (\<ge>) left' \<and> cmp_item (\<le>) right'))\<close>

fun ins :: \<open>'a::ord \<Rightarrow> 'a tree \<Rightarrow> 'a tree\<close> where
  \<open>ins x Tip = Leaf x\<close> |
  \<open>ins x (Node left' val' right' =: tree) = (
    if x = val' then tree
    else if x < val' then Node (ins x left') val' right'
    else Node left' val' (ins x right'))\<close>

lemma tree_to_set_ins_eq_insert_tree_to_set [simp]:
  \<open>tree_to_set (ins x tree) = insert x (tree_to_set tree)\<close>
  by (induction tree) auto

lemma tree_ordered_ins_of_ordered:
  fixes tree :: \<open>'a::linorder tree\<close>
  assumes \<open>ord tree\<close>
  shows \<open>ord <| ins x tree\<close>
  using assms by (induction tree) (auto simp add: ord_def)

end

end