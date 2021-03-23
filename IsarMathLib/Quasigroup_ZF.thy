(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. *)

section \<open> Quasigroups \<close>

theory Quasigroup_ZF imports func1

begin

text\<open> A quasigroup is an algebraic structure that that one gets after adding (sort of)
   divsibility to magma. Quasigroups differ from groups in that they are not necessarily 
   associative and they do not have to have the neutral element. \<close>

subsection\<open> Definitions and notation \<close>

text\<open> According to Wikipedia there are at least two approaches to defining a quasigroup. 
  One defines a quasigroup as a set with a binary operation, and the other, 
  from universal algebra, defines a quasigroup as having three primitive operations. We will use 
  the first approach.  \<close>

text\<open> A quasigroup operation does not  have to have the neutral element. The left division is defined 
  as the only solution to the equation $a\cdot x=b$ (using multiplicative notation). 
  The next definition specifies
  what does it mean that an operation $A$ has a left division on a set $G$. \<close>

definition
  "HasLeftDiv(G,A) \<equiv> \<forall>a\<in>G.\<forall>b\<in>G.\<exists>!x. (x\<in>G \<and> A`\<langle>a,x\<rangle> = b)" 


text\<open> An operation $A$ has the right inverse if for all elements $a,b \in G$ the equation $x\cdot a=b$ 
  has a unique solution. \<close>

definition
  "HasRightDiv(G,A) \<equiv> \<forall>a\<in>G.\<forall>b\<in>G.\<exists>!x. (x\<in>G \<and> A`\<langle>x,a\<rangle> = b)" 

text\<open>An operation that has both left and right division is said to have the Latin square property. \<close>

definition
  HasLatinSquareProp (infix "{has Latin square property on}" 65) where
    "A {has Latin square property on} G \<equiv> HasLeftDiv(G,A) \<and> HasRightDiv(G,A)"

text\<open> A quasigroup is a set with a binary operation that has the Latin square property. \<close>

definition
  "IsAquasigroup(G,A) \<equiv> A:G\<times>G\<rightarrow>G \<and> A {has Latin square property on} G"

text\<open> The uniqueness of the left inverse allows us to define the left division as a function.
  The union expression as the value of the function extracts the only element
  of the set of solutions of the equation $x\cdot z = y$ for given 
  $\langle x,y \rangle = p \in G\times G$ using the identity $\bigcup \{x\} =x$. \<close>

definition
  "LeftDiv(G,A) \<equiv> {\<langle>p,\<Union>{z\<in>G. A`\<langle>fst(p),z\<rangle> = snd(p)}\<rangle>.p\<in>G\<times>G}"

text\<open>Similarly the right division is defined as a function on $G\times G$.  \<close>

definition
  "RightDiv(G,A) \<equiv> {\<langle>p,\<Union>{z\<in>G. A`\<langle>z,fst(p)\<rangle> = snd(p)}\<rangle>.p\<in>G\<times>G}"

text\<open>Left and right divisions are binary operations on $G$. \<close>

lemma lrdiv_binop: assumes "IsAquasigroup(G,A)" shows 
  "LeftDiv(G,A):G\<times>G\<rightarrow>G" and  "RightDiv(G,A):G\<times>G\<rightarrow>G"
proof -
  { fix p assume "p\<in>G\<times>G"
    with assms have 
      "\<Union>{x\<in>G. A`\<langle>fst(p),x\<rangle> = snd(p)} \<in> G" and  "\<Union>{x\<in>G. A`\<langle>x,fst(p)\<rangle> = snd(p)} \<in> G"
      unfolding IsAquasigroup_def HasLatinSquareProp_def HasLeftDiv_def HasRightDiv_def
      using ZF1_1_L9(2) by auto
  } then show  "LeftDiv(G,A):G\<times>G\<rightarrow>G" and "RightDiv(G,A):G\<times>G\<rightarrow>G" 
    unfolding LeftDiv_def RightDiv_def using ZF_fun_from_total by auto
qed

text\<open> We will use multiplicative notation for the quasigroup operation. The right and left division will
  be denoted $a/b$ and $a\backslash b$, resp.\<close>

locale quasigroup0 =
  fixes G A
  assumes qgroupassum: "IsAquasigroup(G,A)"

  fixes qgroper (infixl "\<cdot>" 70)
  defines qgroper_def[simp]: "x\<cdot>y \<equiv> A`\<langle>x,y\<rangle>"

  fixes leftdiv (infixl "\<ld>" 70)
  defines leftdiv_def[simp]: "x\<ld>y \<equiv>LeftDiv(G,A)`\<langle>x,y\<rangle>"

  fixes rightdev (infixl "\<rd>" 70)
  defines rightdev_def[simp]:"x\<rd>y \<equiv>RightDiv(G,A)`\<langle>y,x\<rangle>"

text\<open> The quasigroup operation is closed on $G$. \<close>

lemma (in quasigroup0) qg_op_closed: assumes "x\<in>G" "y\<in>G"
  shows "x\<cdot>y \<in> G"
  using qgroupassum assms IsAquasigroup_def apply_funtype by auto

text\<open> A couple of properties of right and left division: \<close>

lemma (in quasigroup0) lrdiv_props: assumes "x\<in>G" "y\<in>G"
  shows 
  "\<exists>!z. z\<in>G \<and> z\<cdot>x = y" "y\<rd>x \<in> G" "(y\<rd>x)\<cdot>x = y" and
  "\<exists>!z. z\<in>G \<and> x\<cdot>z = y" "x\<ld>y \<in> G" "x\<cdot>(x\<ld>y) = y"
proof -
  let ?z\<^sub>r = "\<Union>{z\<in>G. z\<cdot>x = y}"
  from qgroupassum have I: "RightDiv(G,A):G\<times>G\<rightarrow>G" using lrdiv_binop(2) by simp
  with assms have "RightDiv(G,A)`\<langle>x,y\<rangle> = ?z\<^sub>r"
    unfolding RightDiv_def using ZF_fun_from_tot_val by auto
  moreover
  from qgroupassum assms show "\<exists>!z. z\<in>G \<and> z\<cdot>x = y"
    unfolding IsAquasigroup_def HasLatinSquareProp_def HasRightDiv_def by simp
  then have "?z\<^sub>r\<cdot>x = y" by (rule ZF1_1_L9)
  ultimately show "(y\<rd>x)\<cdot>x = y" by simp
  let ?z\<^sub>l = "\<Union>{z\<in>G. x\<cdot>z = y}"
  from qgroupassum have II: "LeftDiv(G,A):G\<times>G\<rightarrow>G" using lrdiv_binop(1) by simp
  with assms have "LeftDiv(G,A)`\<langle>x,y\<rangle> = ?z\<^sub>l"
    unfolding LeftDiv_def using ZF_fun_from_tot_val by auto
  moreover
  from qgroupassum assms show "\<exists>!z. z\<in>G \<and> x\<cdot>z = y"
    unfolding IsAquasigroup_def HasLatinSquareProp_def HasLeftDiv_def by simp
  then have "x\<cdot>?z\<^sub>l = y" by (rule ZF1_1_L9)
  ultimately show "x\<cdot>(x\<ld>y) = y" by simp
  from assms I II show "y\<rd>x \<in> G" and "x\<ld>y \<in> G" using apply_funtype by auto
qed

text\<open> We can cancel the left element on both sides of an equation. \<close>

lemma (in quasigroup0) qg_cancel_left: 
  assumes "x\<in>G" "y\<in>G" "z\<in>G" and "x\<cdot>y = x\<cdot>z"
  shows "y=z"
  using qgroupassum assms qg_op_closed lrdiv_props(4) by blast

text\<open> We can cancel the right element on both sides of an equation. \<close>

lemma (in quasigroup0) qg_cancel_right: 
  assumes "x\<in>G" "y\<in>G" "z\<in>G" and "y\<cdot>x = z\<cdot>x"
  shows "y=z"
  using qgroupassum assms qg_op_closed lrdiv_props(1) by blast

text\<open> Two additional identities for right and left division: \<close>

lemma (in quasigroup0) lrdiv_ident: assumes "x\<in>G" "y\<in>G"
  shows "(y\<cdot>x)\<rd>x = y" and "x\<ld>(x\<cdot>y) = y"
proof -
  from assms have "(y\<cdot>x)\<rd>x \<in> G" and "((y\<cdot>x)\<rd>x)\<cdot>x = y\<cdot>x"
    using qg_op_closed lrdiv_props(2,3) by auto
  with assms show "(y\<cdot>x)\<rd>x = y" using qg_cancel_right by simp
  from assms have "x\<ld>(x\<cdot>y) \<in> G" and "x\<cdot>(x\<ld>(x\<cdot>y)) = x\<cdot>y"
    using qg_op_closed lrdiv_props(5,6) by auto
  with assms show "x\<ld>(x\<cdot>y) = y" using qg_cancel_left by simp
qed
  
end
