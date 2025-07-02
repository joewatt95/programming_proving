section \<open>Basic utilities\<close>

text
  \<open>This provides basic, general utilities that are used throughout the rest
  of this development.\<close>

theory Utils_Basic

imports
  "HOL-Library.Monad_Syntax"

begin

abbreviation (input) flip :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c\<close> where
  \<open>flip \<equiv> \<lambda> f x y. f y x\<close>

abbreviation (input) app :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b\<close>
  (infixr \<open><|\<close> 0) where
  \<open>(<|) \<equiv> (\<lambda> f. f)\<close>

abbreviation (input) pipe :: \<open>'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b\<close>
  (infixl \<open>|>\<close> 0) where
  \<open>(|>) \<equiv> flip (<|)\<close>

abbreviation (input) comp_left :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c\<close>
  (infixl \<open><<<\<close> 55) where
  \<open>(g <<< f) \<equiv> (\<lambda> x. g (f x))\<close>

abbreviation (input) comp_right :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'c\<close>
  (infixl \<open>>>>\<close> 55) where
  \<open>(f >>> g) \<equiv> g <<< f\<close>

abbreviation (input) \<open>uncurry \<equiv> case_prod\<close>

notation restrict_map (infixl \<open>\<restriction>\<close> 110)

notation empty (\<open>\<emptyset>\<close>)

declare [[coercion \<open>\<lambda> P. {x. P x}\<close>]]

(* syntax
  "_flip_bind" :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'b\<close>
  (infixl \<open>=<<\<close> 54)
  "_kleisli_comp_right" :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'c\<close>
  (infixl \<open>>=>\<close> 50)
  "_kleisli_comp_left" :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c\<close>
  (infixr \<open><=<\<close> 50)

syntax_consts
  "_flip_bind" "_kleisli_comp_right" "_kleisli_comp_left" \<rightleftharpoons> Monad_Syntax.bind

translations
  "_flip_bind" \<rightharpoonup> "CONST flip Monad_Syntax.bind"
  "_kleisli_comp_right f g" \<rightharpoonup> "f >>> (=<<) g"
  "_kleisli_comp_left f g" \<rightharpoonup> "g >=> f"

abbreviation is_None_or_pred :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>is_None_or_pred \<equiv> case_option True\<close>

abbreviation is_Some_and_pred :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>is_Some_and_pred \<equiv> case_option False\<close>

lemma is_Some_and_pred_eq [simp]:
  \<open>is_Some_and_pred (\<lambda> x. x = x\<^sub>0) = (\<lambda> x. x = Some x\<^sub>0)\<close>
  by (auto elim: case_optionE)

lemma Pow_UNIV_bool_eq:
  \<open>Pow UNIV = {\<emptyset>, {True}, {False}, {True, False}}\<close>
  by (simp add: Pow_insert UNIV_bool insert_commute) *)

end