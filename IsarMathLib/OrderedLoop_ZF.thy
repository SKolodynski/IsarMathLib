(*    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2021 Slawomir Kolodynski

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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open> Ordered loops \<close>

theory OrderedLoop_ZF imports Loop_ZF Order_ZF

begin

text\<open> This theory file is about properties of loops (the algebraic structures introduced 
  in IsarMathLib in the \<open>Loop_ZF\<close> theory) with an additional order relation that is in
  a way compatible with the loop's binary operation. The oldest reference I have found on the subject is
  \cite{Zelinski1948}. \<close>

subsection\<open>Definition and notation\<close>

text\<open> An ordered loop $(G,A)$ is a loop with a partial order relation r that is 
  "translation invariant" with respect to the loop operation $A$.\<close>
  
text\<open> A triple $(G,A,r)$ is an ordered loop if $(G,A)$ is a loop and $r$ is a relation
  on $G$ (i.e. a subset of $G\times G$ with is a partial order and for all elements $x,y,z \in G$
  the condition $\langle x,y\rangle \in r$ is equivalent to both
  $\langle A\langle x,z\rangle, A\langle x,z\rangle\rangle \in r$ and 
  $\langle A\langle z,x\rangle, A\langle z,x\rangle\rangle \in r$. 
  This looks a bit awkward in the basic set theory notation, but using the additive notation 
  for the group operation and $x\leq y$ to instead of $\langle x,y \rangle \in r$ this just means that
  $x\leq y$ if and only if $x+z\leq y+z$ and $x\leq y$ if and only if $z+x\leq z+y$. \<close>

definition
  "IsAnOrdLoop(L,A,r) \<equiv> 
  IsAloop(L,A) \<and> r\<subseteq>L\<times>L \<and> IsPartOrder(L,r) \<and> (\<forall>x\<in>L. \<forall>y\<in>L. \<forall>z\<in>L. 
  ((\<langle>x,y\<rangle> \<in> r \<longleftrightarrow> \<langle>A`\<langle> x,z\<rangle>,A`\<langle>y,z\<rangle>\<rangle> \<in> r) \<and> (\<langle>x,y\<rangle> \<in> r \<longleftrightarrow> \<langle>A`\<langle>z,x\<rangle>,A`\<langle>z,y\<rangle>\<rangle> \<in> r )))"

text\<open>We define the set of nonnegative elements  in the obvious way as $L^+ =\{x\in L: 0 \leq x\}$.\<close>

definition
  "Nonnegative(L,A,r) \<equiv> {x\<in>L. \<langle> TheNeutralElement(L,A),x\<rangle> \<in> r}"

text\<open>The \<open>PositiveSet(L,A,r)\<close> is a set similar to  \<open>Nonnegative(L,A,r)\<close>, but without the neutral element.\<close>

definition
  "PositiveSet(L,A,r) \<equiv> 
  {x\<in>L. \<langle> TheNeutralElement(L,A),x\<rangle> \<in> r \<and> TheNeutralElement(L,A)\<noteq> x}"

text\<open> We will use the additive notation for ordered loops.\<close>

locale loop1 =
  fixes L and A and r

  assumes ordLoopAssum: "IsAnOrdLoop(L,A,r)"

  fixes neut ("\<zero>")
  defines neut_def[simp]: "\<zero> \<equiv> TheNeutralElement(L,A)"
  
  fixes looper (infixl "\<ra>" 69)
  defines looper_def[simp]: "x \<ra> y \<equiv> A`\<langle> x,y\<rangle>"
  
  fixes lesseq (infix "\<lsq>" 68)
  defines lesseq_def [simp]: "x \<lsq> y \<equiv> \<langle>x,y\<rangle> \<in> r"
  
  fixes sless (infix "\<ls>" 68)
  defines sless_def[simp]: "x \<ls> y \<equiv> x\<lsq>y \<and> x\<noteq>y"
  
  fixes nonnegative ("L\<^sup>+")
  defines nonnegative_def [simp]: "L\<^sup>+ \<equiv> Nonnegative(L,A,r)"
  
  fixes positive ("L\<^sub>+")
  defines positive_def[simp]: "L\<^sub>+ \<equiv> PositiveSet(L,A,r)"
  
  fixes leftdiv ("\<rm> _ \<ad> _")
  defines leftdiv_def[simp]: "\<rm>x\<ad>y \<equiv> LeftDiv(L,A)`\<langle>x,y\<rangle>"
  
  fixes rightdiv (infixl "\<rs>" 69)
  defines rightdiv_def[simp]:"x\<rs>y \<equiv> RightDiv(L,A)`\<langle>y,x\<rangle>"
    
text\<open>Theorems proven in the \<open>loop0\<close> locale are valid in the \<open>loop1\<close> locale\<close>

sublocale loop1 < loop0 L A looper  
  using ordLoopAssum loop_loop0_valid unfolding IsAnOrdLoop_def by auto

text\<open>The notation $-x+y$ and $x-y$ denotes left and right division, resp. 
  These two operations are closed in a loop, see lemma \<open>lrdiv_binop\<close> in the \<open>Quasigroup_ZF\<close> theory.
  The next lemma reiterates that fact using the notation of the \<open>loop1\<close> context. \<close>

lemma (in loop1) left_right_sub_closed: assumes "x\<in>L" "y\<in>L"
  shows "(\<rm>x\<ad>y) \<in> L" and "x\<rs>y \<in> L"
proof -
  from qgroupassum have "LeftDiv(L,A):L\<times>L \<rightarrow>L" and  "RightDiv(L,A):L\<times>L \<rightarrow>L"
    using lrdiv_binop by simp_all
  with assms show "(\<rm>x\<ad>y) \<in> L" and "x\<rs>y \<in> L"
    using apply_funtype by simp_all
qed

text\<open>In this context $x \leq y$ implies that both $x$ and $y$ belong
  to $L$.\<close>

lemma (in loop1) lsq_members: assumes "x\<lsq>y" shows "x\<in>L" and "y\<in>L" 
  using ordLoopAssum assms IsAnOrdLoop_def by auto

text\<open>In this context $x < y$ implies that both $x$ and $y$ belong
  to $L$.\<close>

lemma (in loop1) less_members: assumes "x\<ls>y" shows "x\<in>L" and "y\<in>L" 
  using ordLoopAssum assms IsAnOrdLoop_def by auto

text\<open> In an ordered loop the order is translation invariant. \<close>

lemma (in loop1) ord_trans_inv: assumes "x\<lsq>y" "z\<in>L"
  shows "x\<ra>z \<lsq> y\<ra>z" and "z\<ra>x \<lsq> z\<ra>y"
proof -
  from ordLoopAssum assms have 
    "(\<langle>x,y\<rangle> \<in> r \<longleftrightarrow> \<langle>A`\<langle> x,z\<rangle>,A`\<langle>y,z\<rangle>\<rangle> \<in> r) \<and> (\<langle>x,y\<rangle> \<in> r \<longleftrightarrow> \<langle>A`\<langle>z,x\<rangle>,A`\<langle>z,y\<rangle>\<rangle> \<in> r )"
    using lsq_members unfolding IsAnOrdLoop_def by blast
  with assms(1) show "x\<ra>z \<lsq> y\<ra>z" and "z\<ra>x \<lsq> z\<ra>y" by auto
qed

text\<open> In an ordered loop the strict order is translation invariant. \<close>

lemma (in loop1) strict_ord_trans_inv: assumes "x\<ls>y" "z\<in>L"
  shows "x\<ra>z \<ls> y\<ra>z" and "z\<ra>x \<ls> z\<ra>y"
proof -
  from assms have "x\<ra>z \<lsq> y\<ra>z" and "z\<ra>x \<lsq> z\<ra>y"
    using ord_trans_inv by auto
  moreover have "x\<ra>z \<noteq> y\<ra>z" and "z\<ra>x \<noteq> z\<ra>y"
  proof -
    { assume "x\<ra>z = y\<ra>z"
      with assms have "x=y" using less_members qg_cancel_right by blast
      with assms(1) have False by simp
    } thus "x\<ra>z \<noteq> y\<ra>z" by auto
    { assume "z\<ra>x = z\<ra>y"
      with assms have "x=y" using less_members qg_cancel_left by blast
      with assms(1) have False by simp
    } thus "z\<ra>x \<noteq> z\<ra>y" by auto
  qed
  ultimately show "x\<ra>z \<ls> y\<ra>z" and "z\<ra>x \<ls> z\<ra>y"
    by auto
qed

text\<open>We can cancel an element from both sides of an inequality on the right side. \<close>

lemma (in loop1) ineq_cancel_right: assumes "x\<in>L" "y\<in>L" "z\<in>L" and "x\<ra>z \<lsq> y\<ra>z" 
  shows  "x\<lsq>y"
proof -
  from ordLoopAssum assms(1,2,3) have "\<langle>x,y\<rangle> \<in> r \<longleftrightarrow> \<langle>A`\<langle> x,z\<rangle>,A`\<langle>y,z\<rangle>\<rangle> \<in> r"
    unfolding IsAnOrdLoop_def by blast
  with assms(4) show "x\<lsq>y" by simp
qed

text\<open>We can cancel an element from both sides of a strict inequality on the right side. \<close>

lemma (in loop1) strict_ineq_cancel_right: assumes "x\<in>L" "y\<in>L" "z\<in>L" and "x\<ra>z \<ls> y\<ra>z" 
  shows  "x\<ls>y"
  using assms ineq_cancel_right by auto

text\<open>We can cancel an element from both sides of an inequality on the left side. \<close>

lemma (in loop1) ineq_cancel_left: assumes "x\<in>L" "y\<in>L" "z\<in>L" and "z\<ra>x \<lsq> z\<ra>y" 
  shows  "x\<lsq>y"
proof -
  from ordLoopAssum assms(1,2,3) have "\<langle>x,y\<rangle> \<in> r \<longleftrightarrow> \<langle>A`\<langle>z,x\<rangle>,A`\<langle>z,y\<rangle>\<rangle> \<in> r"
    unfolding IsAnOrdLoop_def by blast
  with assms(4) show "x\<lsq>y" by simp
qed

text\<open>We can cancel an element from both sides of a strict inequality on the left side. \<close>

lemma (in loop1) strict_ineq_cancel_left: 
  assumes "x\<in>L" "y\<in>L" "z\<in>L" and "z\<ra>x \<ls> z\<ra>y" 
  shows  "x\<ls>y"
  using assms ineq_cancel_left by auto

text\<open>The definition of the nonnegative set in the notation used in the \<open>loop1\<close> locale: \<close>

lemma (in loop1) nonneg_definition: 
  shows "x \<in> L\<^sup>+ \<longleftrightarrow> \<zero> \<lsq> x" using ordLoopAssum IsAnOrdLoop_def Nonnegative_def by auto

text\<open>The nonnegative set is contained in the loop.\<close>

lemma (in loop1) nonneg_subset: shows "L\<^sup>+ \<subseteq> L"
  using Nonnegative_def by auto 

text\<open>The positive set is contained in the loop.\<close>

lemma (in loop1) positive_subset: shows "L\<^sub>+ \<subseteq> L"
  using PositiveSet_def by auto

text\<open>The definition of the positive set in the notation used in the \<open>loop1\<close> locale: \<close>

lemma (in loop1) posset_definition: 
  shows "x \<in> L\<^sub>+ \<longleftrightarrow> (\<zero>\<lsq>x \<and> x\<noteq>\<zero>)" 
  using ordLoopAssum IsAnOrdLoop_def PositiveSet_def by auto

text\<open>Another form of the definition of the positive set in the notation used in the \<open>loop1\<close> locale: \<close>

lemma (in loop1) posset_definition1: 
  shows "x \<in> L\<^sub>+ \<longleftrightarrow> \<zero>\<ls>x" 
  using ordLoopAssum IsAnOrdLoop_def PositiveSet_def by auto

text\<open> The order in an ordered loop is antisymmeric. \<close>

lemma (in loop1) loop_ord_antisym: assumes "x\<lsq>y" and "y\<lsq>x"
  shows "x=y"
proof -
  from ordLoopAssum assms have "antisym(r)" "\<langle>x,y\<rangle> \<in> r" "\<langle>y,x\<rangle> \<in> r" 
    unfolding IsAnOrdLoop_def IsPartOrder_def by auto
  then show "x=y" by (rule Fol1_L4)
qed

text\<open> The loop order is transitive. \<close>

lemma (in loop1) loop_ord_trans: assumes "x\<lsq>y" and "y\<lsq>z" shows "x\<lsq>z"
proof - 
  from ordLoopAssum assms have "trans(r)" and "\<langle>x,y\<rangle> \<in> r \<and> \<langle>y,z\<rangle> \<in> r"
    unfolding IsAnOrdLoop_def IsPartOrder_def by auto
  then have "\<langle>x,z\<rangle> \<in> r" by (rule Fol1_L3)
  thus ?thesis by simp
qed

text\<open> The loop order is reflexive. \<close>

lemma (in loop1) loop_ord_refl: assumes "x\<in>L" shows "x\<lsq>x"
  using assms ordLoopAssum unfolding IsAnOrdLoop_def IsPartOrder_def refl_def 
  by simp

text\<open>The neutral element is nonnegative.\<close>

lemma (in loop1) loop_zero_nonneg: shows "\<zero>\<in>L\<^sup>+"
  using neut_props_loop(1) loop_ord_refl nonneg_definition
  by simp

text\<open> A form of mixed transitivity for the strict order: \<close>

lemma (in loop1) loop_strict_ord_trans: assumes "x\<lsq>y" and "y\<ls>z"
  shows "x\<ls>z"
proof -
  from assms have "x\<lsq>y" and "y\<lsq>z" by auto
  then have "x\<lsq>z" by (rule loop_ord_trans)
  with assms show "x\<ls>z" using loop_ord_antisym by auto
qed

text\<open> Another form of mixed transitivity for the strict order: \<close>

lemma (in loop1) loop_strict_ord_trans1: assumes "x\<ls>y" and "y\<lsq>z"
  shows "x\<ls>z"
proof -
  from assms have "x\<lsq>y" and "y\<lsq>z" by auto
  then have "x\<lsq>z" by (rule loop_ord_trans)
  with assms show "x\<ls>z" using loop_ord_antisym by auto
qed

text\<open> Yet another form of mixed transitivity for the strict order: \<close>

lemma (in loop1) loop_strict_ord_trans2: assumes "x\<ls>y" and "y\<ls>z"
  shows "x\<ls>z"
proof -
  from assms have "x\<lsq>y" and "y\<lsq>z" by auto
  then have "x\<lsq>z" by (rule loop_ord_trans)
  with assms show "x\<ls>z" using loop_ord_antisym by auto
qed

text\<open> We can move an element to the other side of an inequality. Well, not exactly, but
  our notation creates an illusion to that effect. \<close>

lemma (in loop1) lsq_other_side: assumes "x\<lsq>y" 
  shows "\<zero> \<lsq> \<rm>x\<ad>y"  "(\<rm>x\<ad>y) \<in> L\<^sup>+" "\<zero> \<lsq> y\<rs>x" "(y\<rs>x) \<in> L\<^sup>+"
proof -
  from assms have "x\<in>L" "y\<in>L" "\<zero>\<in>L" "(\<rm>x\<ad>y) \<in> L" "(y\<rs>x) \<in> L" 
    using lsq_members neut_props_loop(1) lrdiv_props(2,5) by auto
  then have "x = x\<ra>\<zero>" and "y = x\<ra>(\<rm>x\<ad>y)" using neut_props_loop(2) lrdiv_props(6)
    by auto
  with assms have "x\<ra>\<zero> \<lsq> x\<ra>(\<rm>x\<ad>y)" by simp
  with \<open>x\<in>L\<close> \<open>\<zero>\<in>L\<close> \<open>(\<rm>x\<ad>y) \<in> L\<close> show "\<zero> \<lsq> \<rm>x\<ad>y" using ineq_cancel_left
    by simp
  then show "(\<rm>x\<ad>y) \<in> L\<^sup>+" using nonneg_definition by simp
  from \<open>x\<in>L\<close> \<open>y\<in>L\<close> have "x = \<zero>\<ra>x" and "y = (y\<rs>x)\<ra>x"
    using neut_props_loop(2) lrdiv_props(3) by auto
  with assms have "\<zero>\<ra>x \<lsq> (y\<rs>x)\<ra>x" by simp
  with \<open>x\<in>L\<close> \<open>\<zero>\<in>L\<close> \<open>(y\<rs>x) \<in> L\<close> show "\<zero> \<lsq> y\<rs>x" using ineq_cancel_right
    by simp
  then show "(y\<rs>x) \<in> L\<^sup>+" using  nonneg_definition by simp
qed

text\<open> We can move an element to the other side of a strict inequality. \<close>

lemma (in loop1) ls_other_side: assumes "x\<ls>y" 
  shows "\<zero> \<ls> \<rm>x\<ad>y"  "(\<rm>x\<ad>y) \<in> L\<^sub>+" "\<zero> \<ls> y\<rs>x" "(y\<rs>x) \<in> L\<^sub>+"
proof -
  from assms have "x\<in>L" "y\<in>L" "\<zero>\<in>L" "(\<rm>x\<ad>y) \<in> L" "(y\<rs>x) \<in> L" 
    using lsq_members neut_props_loop(1) lrdiv_props(2,5) by auto
  then have "x = x\<ra>\<zero>" and "y = x\<ra>(\<rm>x\<ad>y)" using neut_props_loop(2) lrdiv_props(6)
    by auto
  with assms have "x\<ra>\<zero> \<ls> x\<ra>(\<rm>x\<ad>y)" by simp
  with \<open>x\<in>L\<close> \<open>\<zero>\<in>L\<close> \<open>(\<rm>x\<ad>y) \<in> L\<close> show "\<zero> \<ls> \<rm>x\<ad>y" using strict_ineq_cancel_left
    by simp
  then show "(\<rm>x\<ad>y) \<in> L\<^sub>+" using posset_definition1 by simp
  from \<open>x\<in>L\<close> \<open>y\<in>L\<close> have "x = \<zero>\<ra>x" and "y = (y\<rs>x)\<ra>x"
    using neut_props_loop(2) lrdiv_props(3) by auto
  with assms have "\<zero>\<ra>x \<ls> (y\<rs>x)\<ra>x" by simp
  with \<open>x\<in>L\<close> \<open>\<zero>\<in>L\<close> \<open>(y\<rs>x) \<in> L\<close> show "\<zero> \<ls> y\<rs>x" using strict_ineq_cancel_right
    by simp
  then show "(y\<rs>x) \<in> L\<^sub>+" using posset_definition1 by simp
qed

text\<open>We can add sides of inequalities.\<close>

lemma (in loop1) add_ineq: assumes "x\<lsq>y" "z\<lsq>t" 
  shows "x\<ra>z \<lsq> y\<ra>t"
proof -
  from assms have "x\<ra>z \<lsq> y\<ra>z" 
    using lsq_members(1) ord_trans_inv(1) by simp
  with assms show ?thesis using lsq_members(2) ord_trans_inv(2) loop_ord_trans
    by simp
qed

text\<open>We can add sides of strict inequalities. The proof uses a lemma that
  relies on the antisymmetry of the order relation.\<close>

lemma (in loop1) add_ineq_strict: assumes "x\<ls>y" "z\<ls>t" 
  shows "x\<ra>z \<ls> y\<ra>t"
proof -
  from assms have "x\<ra>z \<ls> y\<ra>z" 
    using less_members(1) strict_ord_trans_inv(1) by auto
  moreover from assms have "y\<ra>z \<ls> y\<ra>t"
    using less_members(2) strict_ord_trans_inv(2) by auto
  ultimately show ?thesis by (rule loop_strict_ord_trans2)
qed

text\<open>We can add sides of inequalities one of which is strict. \<close>

lemma (in loop1) add_ineq_strict1: assumes "x\<lsq>y" "z\<ls>t" 
  shows "x\<ra>z \<ls> y\<ra>t" and "z\<ra>x \<ls> t\<ra>y" 
proof -
    from assms have "x\<ra>z \<lsq> y\<ra>z" 
      using less_members(1) ord_trans_inv(1) by auto
    with assms show "x\<ra>z \<ls> y\<ra>t"
      using lsq_members(2) strict_ord_trans_inv(2) loop_strict_ord_trans
      by blast
    from assms have "z\<ra>x \<ls> t\<ra>x"
      using lsq_members(1) strict_ord_trans_inv(1) by simp
    with assms show "z\<ra>x \<ls> t\<ra>y"
      using less_members(2) ord_trans_inv(2) loop_strict_ord_trans1
      by blast
qed

text\<open>Subtracting a positive element decreases the value, while adding a positive element
  increases the value. \<close>

lemma (in loop1) add_subtract_pos: assumes "x\<in>L" "\<zero>\<ls>y"
  shows  
    "x\<rs>y \<ls> x" "(\<rm>y\<ad>x) \<ls> x" "x \<ls> x\<ra>y" "x \<ls> y\<ra>x"
proof -
  from assms(2) have "y\<in>L" using less_members(2) by simp
  from assms(1) have "x\<lsq>x" 
    using ordLoopAssum unfolding IsAnOrdLoop_def IsPartOrder_def refl_def
    by simp
  with assms(2) have "x\<ra>\<zero> \<ls> x\<ra>y"
    using add_ineq_strict1(1) by simp 
  with assms \<open>y\<in>L\<close> show "x\<rs>y \<ls> x"
    using neut_props_loop(2) lrdiv_props(3) lrdiv_props(2) strict_ineq_cancel_right
    by simp
  from assms(2) \<open>x\<lsq>x\<close> have "\<zero>\<ra>x \<ls> y\<ra>x"
    using add_ineq_strict1(2) by simp
  with assms \<open>y\<in>L\<close> show "(\<rm>y\<ad>x) \<ls> x"
    using neut_props_loop(2) lrdiv_props(6) lrdiv_props(5) strict_ineq_cancel_left
    by simp
  from assms(1) \<open>x\<ra>\<zero> \<ls> x\<ra>y\<close> \<open>\<zero>\<ra>x \<ls> y\<ra>x\<close> 
    show "x \<ls> x\<ra>y" "x \<ls> y\<ra>x"
    using neut_props_loop(2) by simp_all
qed

text\<open>In ordered loop if the order relation down-directs the set of positive elements $L_+$
  then $L_+$ is a down-directed set (see \<open>Order_ZF\<close> for definitions of those related but different
  notions).\<close>

lemma (in loop1) down_directs_directed: assumes "r {down-directs} L\<^sub>+"
  shows "IsDownDirectedSet(L\<^sub>+,r)"
  using ordLoopAssum assms positive_subset down_directs_subset
  unfolding IsAnOrdLoop_def by auto

end
