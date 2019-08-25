(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2011 Victor Porton

    This program is free software; Redistribution and use in source and binary forms, 
    with or without modification, are permitted provided that the following conditions are met:

   1. Redistributions of source code must retain the above copyright notice, 
   this list of conditions and the following disclaimer.
   2. Redistributions in binary form must reproduce the above copyright notice, 
   this list of conditions and the following disclaimer in the documentation and/or 
   other materials provided with the distribution.
   3. The name of the author may not be used to endorse or promote products 
   derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED 
WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF 
MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. 
IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, 
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, 
PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; 
OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, 
WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR 
OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, 
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. *)

section \<open>Generalizations\<close>

theory Generalization_ZF imports func1

begin

text\<open>
  This theory formalizes the intuitive notion of \emph{generalization}.

  See http://www.mathematics21.org/generalization.html for more details.

  Contributed by Victor Porton.
\<close>


subsection\<open>Generalization situation\<close>

text\<open>In mathematics it is often encountered that a small set $S$ 
  naturally bijectively corresponds to a
  subset $R$ of a larger set $B$. (In other words, there is specified an injection 
  $E$ from $S$ to $B$.) It is a widespread practice to equate $S$ with $R$.
  But strictly speaking this equating may contradict to the axioms of ZF/ZFC 
  because we are not insured against $S\cap B\neq \emptyset$ incidents.
  To work around of this (and formulate things exactly what could benefit 
  computer proof assistants) we will replace the set B with a new set B 
  having a bijection $M : B \rightarrow B$ such that $M \circ E = id_S$. 
  (I call this bijection $M$ from the first letter of the word "move" 
  which signifies the move from the old set $B$ to a new set $B$.
  This section contains some basic lemmas holding in this setup. 
\<close>

text\<open>The next locale defines our assumptions.\<close>

locale generalization =
  fixes small and big
  fixes embed
  assumes embed_inj: "embed \<in> inj(small, big)"

text\<open>We define the \<open>small2\<close> set as the range of \<open>embed\<close>.\<close>

definition (in generalization) "small2 \<equiv> range(embed)"

text\<open>We define \<open>spec\<close> as the converse of \<open>embed\<close>.\<close>

definition (in generalization) "spec \<equiv> converse(embed)"

text\<open>Spec is an injection from range of \<open>embed\<close> to \<open>small\<close>.\<close>

lemma (in generalization) spec_inj: shows "spec \<in> inj(small2, small)"
  using embed_inj inj_converse_inj small2_def spec_def by simp

text\<open>Spec maps range of \<open>embed\<close> to \<open>small\<close>.\<close>

lemma (in generalization) spec_fun: shows "spec: small2\<rightarrow>small"
  using embed_inj inj_converse_fun small2_def spec_def by simp

text\<open>Embed maps \<open>small\<close>small to \<open>big\<close>.\<close>

lemma (in generalization) embed_fun: shows "embed: small\<rightarrow>big"
  using  embed_inj inj_is_fun by simp

text\<open>Embed is a surjection from \<open>small\<close> to \<open>small2\<close>.\<close>

lemma (in generalization) embed_surj: shows "embed \<in> surj(small, small2)"
  using fun_is_surj embed_fun small2_def by simp

text\<open>Embed is a bijection between \<open>small\<close> and \<open>small2\<close>.\<close>

theorem (in generalization) embed_bij: shows "embed \<in> bij(small, small2)"
  using embed_inj inj_bij_range small2_def by simp

text\<open>\<open>small2\<close> (i.e. range of \<open>embed\<close>) is a 
  subset of \<open>big\<close>.\<close>

theorem (in generalization) small2_sub_big: shows "small2 \<subseteq> big"
  using embed_fun func1_1_L5B small2_def by simp

text\<open>\<open>spec\<close> is a bijection beween \<open>small2\<close> and \<open>small\<close>.\<close>

theorem (in generalization) spec_bij: shows "spec \<in> bij(small2, small)"
  using bij_converse_bij embed_bij spec_def by simp

subsection\<open>Arbitrary generalizations\<close>

text\<open>This section considers a more general situation.\<close>

text\<open>The next locale extends \<open>generalization\<close> 
  adding another big set and the \<open>move\<close> operation.\<close>

locale generalization1 = generalization +
  fixes newbig
  fixes move
  assumes move_bij: "move \<in> bij(big, newbig)"
  assumes move_embed: "move O embed = id(small)"

text\<open>in \<open>generalization1\<close> context we define \<open>ret\<close> 
  as the converse of \<open>move\<close>.\<close>

definition (in generalization1) "ret \<equiv> converse(move)"

text\<open>\<open>move\<close> is a map from \<open>big\<close> to \<open>newbig\<close>.\<close>

lemma (in generalization1) move_fun: shows "move: big\<rightarrow>newbig" 
  using move_bij bij_is_fun by simp

text\<open>\<open>move\<close> is an injection from \<open>big\<close> to \<open>newbig\<close>.\<close>

lemma (in generalization1) move_inj: shows "move\<in>inj(big, newbig)" 
  using move_bij bij_is_inj by simp

text\<open>Move is a surjection \<open>big\<close> to \<open>newbig\<close>.\<close>

lemma (in generalization1) move_surj: shows "move\<in>surj(big, newbig)" 
  using move_bij bij_is_surj by simp

text\<open>\<open>big\<close> is the domain of \<open>move\<close>.\<close>

lemma (in generalization1) move_domain: shows "domain(move) = big" 
  using domain_of_fun move_fun by simp

text\<open>Composing \<open>move\<close> with \<open>embed\<close> takes elements of 
  \<open>small\<close> to themselves.\<close>

theorem (in generalization1) move_embed_plain: assumes "x\<in>small" 
  shows "move`(embed`(x)) = x"
proof -
  from assms have "move`(embed`(x)) = (move O embed)`(x)"
    using embed_fun comp_fun_apply by simp
  with assms show ?thesis using move_embed by simp
qed

text\<open>\<open>ret\<close> is a bijection from \<open>newbig\<close>newbig to \<open>big\<close>.\<close>

lemma (in generalization1) ret_bij: shows "ret\<in>bij(newbig, big)" 
  using move_bij ret_def by simp

text\<open>\<open>ret\<close> is a injection from \<open>newbig\<close> onto \<open>big\<close>.\<close>

lemma (in generalization1) ret_inj: shows "ret \<in> inj(newbig,big)" 
  using ret_bij bij_is_inj by simp

text\<open>\<open>ret\<close> is a surjection from \<open>newbig\<close> onto \<open>big\<close>.\<close>

lemma (in generalization1) ret_surj: shows "ret \<in> surj(newbig,big)" 
  using ret_bij bij_is_surj by simp

text\<open>\<open>embed\<close> is a restriciton of \<open>ret\<close> to \<open>small\<close>.\<close>

lemma (in generalization1) ret_restrict: shows "embed = restrict(ret, small)"
proof -
  have "embed\<subseteq>small\<times>big" 
    using fun_is_rel embed_fun by auto
  moreover
  have "(converse(move) O move) O embed = converse(move) O id(small)" 
    using  move_embed comp_assoc by auto
  then have a: "id(big) O embed = converse(move) O id(small)"
    using left_comp_inverse move_inj by simp
  ultimately show ?thesis using left_comp_id right_comp_id_any ret_def
    by auto
qed

subsection\<open>ZF generalization\<close>

text\<open>We continue material from the previous section.\<close>


text\<open>We will need this lemma to assert that ZF generalization 
  is an arbitrary generalization:\<close>

lemma mem_not_refl_2: shows "{t} \<notin> t"
  using foundation by auto

text\<open>Definition of token.\<close>

definition (in generalization) "token \<equiv> Pow(\<Union>(\<Union>(small)))"

text\<open>Definition of function moving the \<open>small\<close> set into \<open>big\<close>.\<close>

definition (in generalization) 
  "zf_move_fun(x) \<equiv> if x\<in>small2 then spec`(x) else \<langle>token,x\<rangle>"

text\<open>Definition of \<open>zf_move\<close> - the ZF version of \<open>zf_move_fun\<close>.\<close>

definition (in generalization)
  "zf_move \<equiv> {\<langle>x,zf_move_fun(x)\<rangle>. x\<in>big}"

text\<open>Definition of \<open>zf_newbig\<close> as the range of \<open>zf_move\<close>.\<close>

definition (in generalization) "zf_newbig \<equiv> range(zf_move)"

text\<open>\<open>zf_move\<close> is a function that maps \<open>big\<close> to \<open>newbig\<close>.\<close>

lemma (in generalization) zf_move_fun: shows "zf_move: big\<rightarrow>zf_newbig"
  using lam_is_fun_range zf_move_def zf_newbig_def by simp

text\<open>\<open>token\<close> is not in \<open>small\<close>.\<close>

lemma (in generalization) token_not_small: shows "\<langle>token,x\<rangle>\<notin>small"
proof
  assume "\<langle>token,x\<rangle>\<in>small"
  then have "{token}\<in>token" using token_def Pair_def by auto
  then show False using mem_not_refl_2 by blast
qed

text\<open>Domain of \<open>zf_move\<close> is \<open>big\<close>.\<close>

lemma (in generalization) zf_move_domain: shows "domain(zf_move) = big"
  using  zf_move_fun func1_1_L1 by simp

text\<open>\<open>small\<close> is a subset of \<open>big\<close>.\<close>

theorem (in generalization) small_less_zf_newbig: 
  shows "small \<subseteq> zf_newbig"
proof
  fix x
  assume s: "x \<in> small"
  then have s1: "embed`(x) \<in> small2" 
    using embed_fun apply_rangeI small2_def
    by simp
  then have s2: "embed`(x)\<in>big" using small2_sub_big by auto
  with s1 s have x_val: "zf_move`(embed`(x)) = x" 
    using ZF_fun_from_tot_val zf_move_fun embed_inj 
      left_inverse spec_def zf_move_def zf_move_fun_def 
    by simp
  from s2 have "zf_move`(embed`(x))\<in>range(zf_move)" 
    using zf_move_fun apply_rangeI by simp
  with x_val show "x \<in> zf_newbig" using zf_newbig_def by auto
qed
  
text\<open>\<open>zf_move\<close> is an injection from \<open>big\<close>
  to \<open>zf_newbig\<close>.\<close>

theorem (in generalization) zf_move_inj: shows "zf_move\<in>inj(big, zf_newbig)"
proof -
  have "\<forall>a\<in>big. \<forall>b\<in>big. 
    zf_move`(a) = zf_move`(b) \<longrightarrow> a=b"
  proof -
    {
      fix a b
      assume "a\<in>big" and "b\<in>big"
      then have spec1_a: "a\<in>small2  \<longrightarrow>  zf_move`(a) = spec`(a)" and
        spec2_a: "a\<notin>small2 \<longrightarrow> zf_move`a = \<langle>token,a\<rangle>" and
        spec1_b: "b\<in>small2  \<longrightarrow> zf_move`(b) = spec`(b)" and
        spec2_b: "b\<notin>small2 \<longrightarrow> zf_move`(b) = \<langle>token,b\<rangle>"
        using ZF_fun_from_tot_val1 zf_move_fun_def zf_move_def 
        by auto
      assume move_eq: "zf_move`(a) = zf_move`(b)"
      have "a=b"
      proof -
        { assume "a\<in>small2" and "b\<in>small2"
          with \<open>a\<in>small2\<close> spec1_a \<open>b\<in>small2\<close> spec1_b move_eq
          have I: "spec`(a) = spec`(b)" by simp
          have "spec \<in> inj(small2,small)"
            using spec_inj by simp
          then have "spec \<in> 
            {f:small2 \<rightarrow> small. \<forall>w\<in>small2. \<forall>x\<in>small2. f`(w)=f`(x) \<longrightarrow> w=x}"
            unfolding inj_def by auto
          hence "\<forall>w\<in>small2. \<forall>x\<in>small2. spec`(w)=spec`(x) \<longrightarrow> w=x" by auto
          with \<open>a\<in>small2\<close> \<open>b\<in>small2\<close> I have "a=b" by auto
        }
        moreover
        { assume "a\<in>small2" "b\<notin>small2"
          with spec1_a spec_fun have ma_s: "zf_move`a\<in>small"
            using apply_funtype by auto
          from \<open>b\<notin>small2\<close> spec2_b have "zf_move`b\<notin>small"
            using token_not_small by auto
           with move_eq ma_s have False by auto
        }
        moreover
        { assume "a\<notin>small2" and "b\<in>small2"
          with spec1_b spec_fun have mb_s: "zf_move`(b)\<in>small" 
            using apply_funtype by auto
          from \<open>a\<notin>small2\<close> spec2_a  have "zf_move`(a)\<notin>small"
            using token_not_small by auto
          with move_eq mb_s have False by auto
        }
        moreover
        { assume "a\<notin>small2" and "b\<notin>small2"
          with spec2_a spec2_b have 
            "zf_move`(a) = \<langle>token,a\<rangle>" and
            "zf_move`(b) = \<langle>token,b\<rangle>"
            by auto
          with move_eq have "a=b" by auto 
        }
        ultimately show "a=b" by auto
      qed
    }
    thus ?thesis by auto
  qed
  with zf_move_fun show ?thesis using inj_def by simp
qed

text\<open>\<open>zf_move\<close> is a surjection of \<open>big\<close> onto  \<open>zf_newbig\<close>.\<close>

theorem (in generalization) zf_move_surj: 
  shows "zf_move \<in> surj(big,zf_newbig)"
  using zf_move_fun fun_is_surj zf_newbig_def by simp

text\<open>\<open>zf_move\<close> is a bijection from \<open>big\<close> to  \<open>zf_newbig\<close>.\<close>

theorem (in generalization) zf_move_bij: shows "zf_move \<in> bij(big, zf_newbig)"
  using zf_move_inj inj_bij_range zf_newbig_def by simp

text\<open>The essential condition to prove that composition of \<open>zf_move\<close> 
  and \<open>embed\<close> is identity.\<close>

theorem (in generalization) zf_move_embed: 
  assumes "x \<in> small" shows "zf_move`(embed`(x)) = x"
  using assms embed_fun apply_rangeI small2_sub_big ZF_fun_from_tot_val1
    embed_inj small2_def spec_def zf_move_def zf_move_fun_def by auto

text\<open>Composition of \<open>zf_move\<close>  and \<open>embed\<close> is identity.\<close>

theorem (in generalization) zf_embed_move: shows "zf_move O embed = id(small)"
proof -
  have "\<forall>y\<in>small. zf_move`(embed`y) = y" and 
     "embed: small\<rightarrow>big" and "zf_move: big\<rightarrow>zf_newbig"
    using zf_move_embed embed_fun zf_move_fun by auto
  then show ?thesis using comp_eq_id_iff1 by blast
qed


end