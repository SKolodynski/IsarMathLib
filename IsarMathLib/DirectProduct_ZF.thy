(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2008 Seo Sanghyeon

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

section \<open>Direct product\<close>

theory DirectProduct_ZF imports func_ZF

begin

text\<open>This theory considers the direct product of binary operations. 
  Contributed by Seo Sanghyeon.\<close>

subsection\<open>Definition\<close>

text\<open>In group theory the notion of direct product provides a natural 
  way of creating a new group from two given groups.\<close>

text\<open>Given $(G,\cdot)$  and $(H,\circ)$
  a new operation $(G\times H, \times )$ is defined as
  $(g, h) \times (g', h') = (g \cdot g', h \circ h')$.\<close>

definition
  "DirectProduct(P,Q,G,H) \<equiv> 
  {\<langle>x,\<langle>P`\<langle>fst(fst(x)),fst(snd(x))\<rangle> , Q`\<langle>snd(fst(x)),snd(snd(x))\<rangle>\<rangle>\<rangle>.
  x \<in> (G\<times>H)\<times>(G\<times>H)}"

text\<open>We define a context called \<open>direct0\<close> which
  holds an assumption that $P, Q$ are binary operations on
  $G,H$, resp. and denotes $R$ as the direct product of 
  $(G,P)$ and $(H,Q)$.\<close>

locale direct0 =
  fixes P Q G H 
  assumes Pfun: "P : G\<times>G\<rightarrow>G"
  assumes Qfun: "Q : H\<times>H\<rightarrow>H"
  fixes R
  defines Rdef [simp]: "R \<equiv> DirectProduct(P,Q,G,H)"

text\<open>The direct product of binary operations is a binary operation.\<close>

lemma (in direct0) DirectProduct_ZF_1_L1:
  shows "R : (G\<times>H)\<times>(G\<times>H)\<rightarrow>G\<times>H"
proof -
  from Pfun Qfun have "\<forall>x\<in>(G\<times>H)\<times>(G\<times>H).
    \<langle>P`\<langle>fst(fst(x)),fst(snd(x))\<rangle>,Q`\<langle>snd(fst(x)),snd(snd(x))\<rangle>\<rangle> \<in> G\<times>H"
    by auto
  then show ?thesis using ZF_fun_from_total DirectProduct_def
    by simp
qed

text\<open>And it has the intended value.\<close>

lemma (in direct0) DirectProduct_ZF_1_L2:
  shows "\<forall>x\<in>(G\<times>H). \<forall>y\<in>(G\<times>H). 
  R`\<langle>x,y\<rangle> = \<langle>P`\<langle>fst(x),fst(y)\<rangle>,Q`\<langle>snd(x),snd(y)\<rangle>\<rangle>"
  using DirectProduct_def DirectProduct_ZF_1_L1 ZF_fun_from_tot_val 
  by simp

text\<open>And the value belongs to the set the operation is defined on.\<close>

lemma (in direct0) DirectProduct_ZF_1_L3:
  shows "\<forall>x\<in>(G\<times>H). \<forall>y\<in>(G\<times>H). R`\<langle>x,y\<rangle> \<in> G\<times>H"
  using DirectProduct_ZF_1_L1 by simp

subsection\<open>Associative and commutative operations\<close>

text\<open>If P and Q are both associative or commutative operations,
  the direct product of P and Q has the same property.\<close>

text\<open>Direct product of commutative operations is commutative.\<close>

lemma (in direct0) DirectProduct_ZF_2_L1:
  assumes "P {is commutative on} G" and "Q {is commutative on} H"
  shows "R {is commutative on} G\<times>H"
proof -
  from assms have "\<forall>x\<in>(G\<times>H). \<forall>y\<in>(G\<times>H). R`\<langle>x,y\<rangle> = R`\<langle>y,x\<rangle>"
    using DirectProduct_ZF_1_L2 IsCommutative_def by simp
  then show ?thesis using IsCommutative_def by simp
qed

text\<open>Direct product of associative operations is associative.\<close>

lemma (in direct0) DirectProduct_ZF_2_L2:
  assumes "P {is associative on} G" and "Q {is associative on} H"
  shows "R {is associative on} G\<times>H"
proof -
  have "\<forall>x\<in>G\<times>H. \<forall>y\<in>G\<times>H. \<forall>z\<in>G\<times>H. R`\<langle>R`\<langle>x,y\<rangle>,z\<rangle> =
    \<langle>P`\<langle>P`\<langle>fst(x),fst(y)\<rangle>,fst(z)\<rangle>,Q`\<langle>Q`\<langle>snd(x),snd(y)\<rangle>,snd(z)\<rangle>\<rangle>"
    using DirectProduct_ZF_1_L2 DirectProduct_ZF_1_L3 
    by auto
  moreover have "\<forall>x\<in>G\<times>H. \<forall>y\<in>G\<times>H. \<forall>z\<in>G\<times>H. R`\<langle>x,R`\<langle>y,z\<rangle>\<rangle> =
    \<langle>P`\<langle>fst(x),P`\<langle>fst(y),fst(z)\<rangle>\<rangle>,Q`\<langle>snd(x),Q`\<langle>snd(y),snd(z)\<rangle>\<rangle>\<rangle>"
    using DirectProduct_ZF_1_L2 DirectProduct_ZF_1_L3 by auto
  ultimately have "\<forall>x\<in>G\<times>H. \<forall>y\<in>G\<times>H. \<forall>z\<in>G\<times>H. R`\<langle>R`\<langle>x,y\<rangle>,z\<rangle> = R`\<langle>x,R`\<langle>y,z\<rangle>\<rangle>"
    using assms IsAssociative_def by simp
  then show ?thesis
    using DirectProduct_ZF_1_L1 IsAssociative_def by simp
qed

end
