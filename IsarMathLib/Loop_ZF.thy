(* 
This file is a part of IsarMathLib - 
a library of formalized mathematics for Isabelle/Isar.

Copyright (C) 2021  Slawomir Kolodynski

This program is free software; Redistribution and use in source and binary forms, 
with or without modification, are permitted provided that the 
following conditions are met:

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

section \<open> Loops \<close>

theory Loop_ZF imports Quasigroup_ZF Fold_ZF

begin

text\<open>This theory specifies the definition and proves basic  properites of loops. 
  Loops are very similar to groups, the only property that is missing is associativity 
  of the operation.\<close>

subsection\<open>Definitions and notation\<close>

text\<open> In this section we define the notions of identity element and left and right inverse. \<close>

text\<open> A loop is a quasigroup with an identity element. \<close>

definition "IsAloop(G,A) \<equiv> IsAquasigroup(G,A) \<and> (\<exists>e\<in>G. \<forall>x\<in>G. A`\<langle>e,x\<rangle> = x \<and> A`\<langle>x,e\<rangle> = x)"

text\<open> The neutral element for a binary operation $A:G\times G \rightarrow G $ is defined
  as the only element $e$ of $G$ such that $A\langle x,e\rangle = x$ and $A\langle e,x\rangle = x$
  for all $x\in G$. Note that although the loop definition guarantees the existence of (some) 
  such element(s) at this point we do not know if this element is unique. 
  We can define this notion   h ere but it will become usable only after we prove uniqueness. \<close> 

definition 
 "TheNeutralElement(G,f) \<equiv> 
  ( THE e. e\<in>G \<and> (\<forall> g\<in>G. f`\<langle>e,g\<rangle> = g \<and> f`\<langle>g,e\<rangle> = g))"

text\<open>We will reuse the notation defined in the \<open>quasigroup0\<close> locale, 
  just adding the assumption about the existence of a neutral element and notation for it.\<close>

locale loop0 = quasigroup0 + 
  assumes ex_ident: "\<exists>e\<in>G. \<forall>x\<in>G. e\<cdot>x = x \<and> x\<cdot>e = x"

  fixes neut ("\<one>")
  defines neut_def[simp]: "\<one> \<equiv> TheNeutralElement(G,A)"

  fixes listprod ("\<Prod> _" 70)
  defines listprod_def [simp]: "\<Prod>s \<equiv> Fold(A,\<one>,s)"

  fixes pow
  defines pow_def [simp]: "pow(n,x) \<equiv> \<Prod>{\<langle>k,x\<rangle>. k\<in>n}"

text\<open> In the loop context the pair \<open>(G,A)\<close> forms a loop. \<close>

lemma (in loop0) is_loop: shows "IsAloop(G,A)"
  unfolding IsAloop_def using ex_ident qgroupassum by simp

text\<open>If we know that a pair \<open>(G,A)\<close> forms a loop then the assumptions of the \<open>loop0\<close> locale hold. \<close>

lemma loop_loop0_valid: assumes "IsAloop(G,A)" shows "loop0(G,A)"
  using assms unfolding IsAloop_def loop0_axioms_def quasigroup0_def loop0_def
  by auto

text\<open>The neutral element is unique in the loop. \<close>

lemma (in loop0) neut_uniq_loop: shows 
  "\<exists>!e. e\<in>G \<and> (\<forall>x\<in>G. e\<cdot>x = x \<and> x\<cdot>e = x)"
proof
  from ex_ident show "\<exists>e. e \<in> G \<and> (\<forall>x\<in>G. e \<cdot> x = x \<and> x \<cdot> e = x)" by auto
next
  fix e y 
  assume "e \<in> G \<and> (\<forall>x\<in>G. e \<cdot> x = x \<and> x \<cdot> e = x)"  "y \<in> G \<and> (\<forall>x\<in>G. y \<cdot> x = x \<and> x \<cdot> y = x)"
  then have "e\<cdot>y =y" and "e\<cdot>y = e" by auto
  thus "e=y" by simp
qed

text\<open> The neutral element as defined in the \<open>loop0\<close> locale is indeed neutral. \<close>

lemma (in loop0) neut_props_loop: shows "\<one>\<in>G" and "\<forall>x\<in>G. \<one>\<cdot>x =x \<and> x\<cdot>\<one> = x"
proof -  
  let ?n = "THE e. e\<in>G \<and> (\<forall>x\<in>G. e\<cdot>x = x \<and> x\<cdot>e = x)"
  have "\<one> = TheNeutralElement(G,A)" by simp
  then have "\<one> = ?n" unfolding TheNeutralElement_def by simp
  moreover have "?n\<in>G \<and> (\<forall>x\<in>G. ?n\<cdot>x = x \<and> x\<cdot>?n = x)" using neut_uniq_loop theI
    by simp
  ultimately show "\<one>\<in>G" and "\<forall>x\<in>G. \<one>\<cdot>x = x \<and> x\<cdot>\<one> = x"
    by auto
qed

text\<open>A loop is not empty as it contains the neutral element.\<close>

corollary (in loop0) loop_not_empty: shows "G\<noteq>\<emptyset>" using neut_props_loop(1) 
  by auto

text\<open>Every element of a loop has unique left and right inverse (which need not be the same). 
  Here we define the left inverse as a function on $G$. \<close>

definition
  "LeftInv(G,A) \<equiv> {\<langle>x,\<Union>{y\<in>G. A`\<langle>y,x\<rangle> = TheNeutralElement(G,A)}\<rangle>. x\<in>G}"

text\<open>Definition of the right inverse as a function on $G$: \<close>

definition
  "RightInv(G,A) \<equiv> {\<langle>x,\<Union>{y\<in>G. A`\<langle>x,y\<rangle> = TheNeutralElement(G,A)}\<rangle>. x\<in>G}"

text\<open>In a loop $G$ right and left inverses are functions on $G$. \<close>

lemma (in loop0) lr_inv_fun: shows "LeftInv(G,A):G\<rightarrow>G" "RightInv(G,A):G\<rightarrow>G"
  unfolding LeftInv_def RightInv_def
  using neut_props_loop lrdiv_props(1,4) ZF1_1_L9 ZF_fun_from_total
  by auto

text\<open>Right and left inverses have desired properties.\<close>

lemma (in loop0) lr_inv_props: assumes "x\<in>G"
  shows 
    "LeftInv(G,A)`(x) \<in> G" "(LeftInv(G,A)`(x))\<cdot>x = \<one>" 
    "RightInv(G,A)`(x) \<in> G" "x\<cdot>(RightInv(G,A)`(x)) = \<one>"
proof -
  from assms show "LeftInv(G,A)`(x) \<in> G" and "RightInv(G,A)`(x) \<in> G"
    using lr_inv_fun apply_funtype by auto
  from assms have "\<exists>!y. y\<in>G \<and> y\<cdot>x = \<one>"
    using neut_props_loop(1) lrdiv_props(1) by simp
  then have "(\<Union>{y\<in>G.  y\<cdot>x = \<one>})\<cdot>x = \<one>"
    by (rule ZF1_1_L9)
  with assms show "(LeftInv(G,A)`(x))\<cdot>x = \<one>" 
    using lr_inv_fun(1) ZF_fun_from_tot_val unfolding LeftInv_def by simp
  from assms have "\<exists>!y. y\<in>G \<and> x\<cdot>y = \<one>"
    using neut_props_loop(1) lrdiv_props(4) by simp
  then have "x\<cdot>(\<Union>{y\<in>G.  x\<cdot>y = \<one>}) = \<one>"
    by (rule ZF1_1_L9)
  with assms show "x\<cdot>(RightInv(G,A)`(x)) = \<one>" 
    using lr_inv_fun(2) ZF_fun_from_tot_val unfolding RightInv_def by simp
qed

subsection\<open>Product of a list of loop elements\<close>

text\<open>Given a list $s:n\rightarrow L$ of loop elements we can define the product of the elements
  $s=[x_0,x_1,...,x_{n-1}]$ as the fold of loop operation over that list. 
  The \<open>loop0\<close> locale defined a notation for such fold as $\prod s$.
  That locale also defines a notation for the special case when the list is constant i.e. 
  $x_0 = x_1 = ... x_{n-1} = x$. In such case $\prod s$ becomes $x^{n-1}$. 
  There are similar sections on this subject in \<open>Semigroup_ZF\<close>, \<open>Monoid_ZF\<close> and \<open>Group_ZF\<close>.
  \<close>

text\<open>The product of a list of loop elements is an element of the loop.\<close>

lemma (in loop0) list_prod_in_loop: assumes "n\<in>nat" "s:n\<rightarrow>G" 
  shows "(\<Prod>s) \<in> G"
  using qgroupassum assms neut_props_loop(1) fold_props(2)
  unfolding IsAquasigroup_def by force

text\<open>In particular a natural power of a loop element is an element of the loop.\<close>

lemma (in loop0) loop_prod_type: assumes "n\<in>nat" "x\<in>G" shows "pow(n,x) \<in> G"
  using assms ZF_fun_from_total list_prod_in_loop by simp

text\<open>For a nonempty list of loop element the last element of the list can be pulled out
  of the product and put after the product. In other words 
  $\prod{k=0}^n s(n) = (\prod{k=0}^{n-1} s(n))\cdot s(n)$.\<close>

lemma (in loop0) loop_prod_pull_last: assumes "n \<in> nat" "\<forall>k\<in>n #+ 1. s(k) \<in> G"
  shows "(\<Prod>{\<langle>k,s(k)\<rangle>. k\<in>n #+ 1}) = (\<Prod>{\<langle>k,s(k)\<rangle>. k\<in>n}) \<cdot> s(n)"
  using qgroupassum assms neut_props_loop(1) fold_detach_last
  unfolding IsAquasigroup_def by auto

text\<open>The way we defined the product notation implies that the product of an empty list is the
  neutral element of the loop. \<close>

lemma (in loop0) loop_prod_empty: assumes "s:\<emptyset>\<rightarrow>G" shows "(\<Prod>s) = \<one>"
  using qgroupassum assms neut_props_loop(1) fold_empty
  unfolding IsAquasigroup_def by force

text\<open>In particular, any loop element raised to the natural zero'th power is the 
  neutral element of the loop. In other words $x^0=1$.\<close>

corollary (in loop0) loop_zero_pow: shows "pow(0,x) = \<one>" using loop_prod_empty by simp
  
text\<open>Raising a loop element to a power greater by one corresponds to multiplying the power 
  by that loop element.\<close>

lemma (in loop0) loop_pow_mult_one: assumes "n\<in>nat" "x\<in>G"
  shows "pow(n #+ 1,x) = pow(n,x)\<cdot>x"
proof -
  from assms(2) have "\<forall>k\<in>n #+ 1. x \<in> G" by simp
  with assms(1) have "(\<Prod>{\<langle>k,x\<rangle>. k\<in>n #+ 1}) = (\<Prod>{\<langle>k,x\<rangle>. k\<in>n})\<cdot>x"
    by (rule loop_prod_pull_last)
  thus "pow(n #+ 1,x) = pow(n,x)\<cdot>x" by simp
qed

end
