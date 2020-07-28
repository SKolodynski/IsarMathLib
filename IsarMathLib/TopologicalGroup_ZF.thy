(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2009-2020  Slawomir Kolodynski

    This program is free software; Redistribution and use in source and binary forms, 
    with or without modification, are permitted provided that the following conditions are met:

   1. Redistributions of source code must retain the above copyright notice, 
   this list of conditions and the following disclaimer.
   2. Redistributions in binary form must reproduce the above copyright notice, 
   this list of conditions and the following disclaimer in the documentation and/or 
   other materials provided with the distribution.
   3. The name of the author may not be used to endorse or promote products 
   derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES,
INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT,
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES LOSS OF USE, DATA, OR PROFITS OR
BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open>Topological groups - introduction\<close>

theory TopologicalGroup_ZF imports Topology_ZF_3 Group_ZF_1 Semigroup_ZF

begin

text\<open>This theory is about the first subject of algebraic topology:
  topological groups.\<close>

subsection\<open>Topological group: definition and notation\<close>

text\<open>Topological group is a group that is a topological space 
  at the same time. This means that a topological group is a triple of sets, 
  say $(G,f,T)$ such that $T$ is a topology on $G$, $f$ is a group 
  operation on $G$ and both $f$ and the operation of taking inverse in $G$ 
  are continuous. Since IsarMathLib defines topology without using the carrier,
  (see \<open>Topology_ZF\<close>), in our setup we just use $\bigcup T$ instead
  of $G$ and say that the  pair of sets $(\bigcup T , f)$ is a group.
  This way our definition of being a topological group is a statement about two
  sets: the topology $T$ and the group operation $f$ on $G=\bigcup T$.
  Since the domain of the group operation is $G\times G$, the pair of 
  topologies in which $f$ is supposed to be continuous is $T$ and
  the product topology on $G\times G$ (which we will call $\tau$ below).\<close>

text\<open>This way we arrive at the following definition of a predicate that
  states that pair of sets is a topological group.\<close>

definition
  "IsAtopologicalGroup(T,f) \<equiv> (T {is a topology}) \<and> IsAgroup(\<Union>T,f) \<and>
  IsContinuous(ProductTopology(T,T),T,f) \<and> 
  IsContinuous(T,T,GroupInv(\<Union>T,f))"

text\<open>We will inherit notation from the \<open>topology0\<close> locale. That locale assumes that
  $T$ is a topology. For convenience we will denote $G=\bigcup T$ and $\tau$ to be 
  the product topology on $G\times G$. To that we add some
  notation specific to groups. We will use additive notation
  for the group operation, even though we don't assume that the group is abelian.
  The notation $g+A$ will mean the left translation of the set $A$ by element $g$, i.e.
  $g+A=\{g+a|a\in A\}$.
  The group operation $G$ induces a natural operation on the subsets of $G$
  defined as $\langle A,B\rangle \mapsto \{x+y | x\in A, y\in B \}$.
  Such operation has been considered in \<open>func_ZF\<close> and called 
  $f$ ''lifted to subsets of'' $G$. We will denote the value of such operation 
  on sets $A,B$ as $A+B$.
  The set of neigboorhoods of zero (denoted \<open>\<N>\<^sub>0\<close>) is the 
  collection of (not necessarily open) sets whose interior contains the neutral
  element of the group.\<close>

locale topgroup = topology0 +

  fixes G
  defines G_def [simp]: "G \<equiv> \<Union>T"

  fixes prodtop ("\<tau>")
  defines prodtop_def [simp]: "\<tau> \<equiv> ProductTopology(T,T)"

  fixes f

  assumes Ggroup: "IsAgroup(G,f)"

  assumes fcon: "IsContinuous(\<tau>,T,f)"

  assumes inv_cont: "IsContinuous(T,T,GroupInv(G,f))"

  fixes grop (infixl "\<ra>" 90)
  defines grop_def [simp]: "x\<ra>y \<equiv> f`\<langle>x,y\<rangle>"

  fixes grinv ("\<rm> _" 89)
  defines grinv_def [simp]: "(\<rm>x) \<equiv> GroupInv(G,f)`(x)"

  fixes grsub (infixl "\<rs>" 90)
  defines grsub_def [simp]: "x\<rs>y \<equiv> x\<ra>(\<rm>y)"

  fixes setinv ("\<sm> _" 72)
  defines setninv_def [simp]: "\<sm>A \<equiv> GroupInv(G,f)``(A)"

  fixes ltrans (infix "\<ltr>" 73)
  defines ltrans_def [simp]: "x \<ltr> A \<equiv> LeftTranslation(G,f,x)``(A)"

  fixes rtrans (infix "\<rtr>" 73)
  defines rtrans_def [simp]: "A \<rtr> x \<equiv> RightTranslation(G,f,x)``(A)"

  fixes setadd (infixl "\<sad>" 71)
  defines setadd_def [simp]: "A\<sad>B \<equiv> (f {lifted to subsets of} G)`\<langle>A,B\<rangle>"

  fixes gzero ("\<zero>")
  defines gzero_def [simp]: "\<zero> \<equiv> TheNeutralElement(G,f)"

  fixes zerohoods ("\<N>\<^sub>0")
  defines zerohoods_def [simp]: "\<N>\<^sub>0 \<equiv> {A \<in> Pow(G). \<zero> \<in> int(A)}"

  fixes listsum ("\<Sum> _" 70)
  defines listsum_def[simp]: "\<Sum>k \<equiv> Fold1(f,k)"

text\<open>The first lemma states that we indeeed talk about topological group
  in the context of \<open>topgroup\<close> locale.\<close>

lemma (in topgroup) topGroup: shows "IsAtopologicalGroup(T,f)"
  using topSpaceAssum Ggroup fcon inv_cont IsAtopologicalGroup_def 
  by simp

text\<open>If a pair of sets $(T,f)$ forms a topological group, then
 all theorems proven in the \<open>topgroup\<close> context are valid as applied to 
 $(T,f)$.\<close>

lemma topGroupLocale: assumes "IsAtopologicalGroup(T,f)"
  shows "topgroup(T,f)"
  using assms IsAtopologicalGroup_def topgroup_def 
    topgroup_axioms.intro topology0_def by simp

text\<open>We can use the \<open>group0\<close> locale in the context of \<open>topgroup\<close>.\<close>

lemma (in topgroup) group0_valid_in_tgroup: shows "group0(G,f)"
  using Ggroup group0_def by simp

text\<open>We can use the \<open>group0\<close> locale in the context of \<open>topgroup\<close>.\<close>

sublocale topgroup < group0 G f gzero grop grinv 
    unfolding group0_def gzero_def grop_def grinv_def using Ggroup by auto

text\<open>We can use \<open>semigr0\<close> locale in the context of \<open>topgroup\<close>.\<close>

lemma (in topgroup) semigr0_valid_in_tgroup: shows "semigr0(G,f)"
  using Ggroup IsAgroup_def IsAmonoid_def semigr0_def by simp 

text\<open>We can use the \<open>prod_top_spaces0\<close> locale in the context of \<open>topgroup\<close>.\<close>

lemma (in topgroup) prod_top_spaces0_valid: shows "prod_top_spaces0(T,T,T)"
  using topSpaceAssum prod_top_spaces0_def by simp

text\<open>Negative of a group element is in group.\<close>

lemma (in topgroup) neg_in_tgroup: assumes "g\<in>G" shows "(\<rm>g) \<in> G"
proof -
  from assms have "GroupInv(G,f)`(g) \<in> G" 
    using group0_valid_in_tgroup group0.inverse_in_group by blast
  thus ?thesis by simp
qed

text\<open>Sum of two group elements is in the group.\<close>

lemma (in topgroup) group_op_closed_add:  assumes "x\<^sub>1 \<in> G"  "x\<^sub>2 \<in> G"
  shows "x\<^sub>1\<ra>x\<^sub>2 \<in> G" 
proof -
  from assms have "f`\<langle>x\<^sub>1,x\<^sub>2\<rangle> \<in> G" using assms group0_valid_in_tgroup group0.group_op_closed 
    by blast
  thus ?thesis by simp
qed

text\<open>Zero is in the group.\<close>

lemma (in topgroup) zero_in_tgroup: shows "\<zero>\<in>G"
proof -
  have "TheNeutralElement(G,f) \<in> G" 
    using group0_valid_in_tgroup group0.group0_2_L2 by blast
  then show "\<zero>\<in>G" by simp
qed

text\<open> Another lemma about canceling with two group elements written in additive notation \<close>

lemma (in topgroup) inv_cancel_two_add: 
  assumes "x\<^sub>1 \<in> G"  "x\<^sub>2 \<in> G" 
  shows 
    "x\<^sub>1\<ra>(\<rm>x\<^sub>2)\<ra>x\<^sub>2 = x\<^sub>1"
    "x\<^sub>1\<ra>x\<^sub>2\<ra>(\<rm>x\<^sub>2) = x\<^sub>1"
    "(\<rm>x\<^sub>1)\<ra>(x\<^sub>1\<ra>x\<^sub>2) = x\<^sub>2"
    "x\<^sub>1\<ra>((\<rm>x\<^sub>1)\<ra>x\<^sub>2) = x\<^sub>2"
  using assms group0_valid_in_tgroup group0.inv_cancel_two by auto

text\<open>Useful identities proven in the \<open>Group_ZF\<close> theory, rewritten here in additive notation.
  Note since the group operation notation is left associative we don't really need the first set
  of parentheses in some cases.\<close>

lemma (in topgroup) cancel_middle_add:assumes "x\<^sub>1 \<in> G"  "x\<^sub>2 \<in> G"  "x\<^sub>3 \<in> G"
  shows 
    "(x\<^sub>1\<ra>(\<rm>x\<^sub>2))\<ra>(x\<^sub>2\<ra>(\<rm>x\<^sub>3)) = x\<^sub>1\<ra> (\<rm>x\<^sub>3)"
    "((\<rm>x\<^sub>1)\<ra>x\<^sub>2)\<ra>((\<rm>x\<^sub>2)\<ra>x\<^sub>3) = (\<rm>x\<^sub>1)\<ra> x\<^sub>3" 
    "(\<rm> (x\<^sub>1\<ra>x\<^sub>2)) \<ra> (x\<^sub>1\<ra>x\<^sub>3) = (\<rm>x\<^sub>2)\<ra>x\<^sub>3"
    "(x\<^sub>1\<ra>x\<^sub>2) \<ra> (\<rm>(x\<^sub>3\<ra>x\<^sub>2)) =x\<^sub>1\<ra> (\<rm>x\<^sub>3)"
    "(\<rm>x\<^sub>1) \<ra> (x\<^sub>1\<ra>x\<^sub>2\<ra>x\<^sub>3) \<ra> (\<rm>x\<^sub>3) = x\<^sub>2"
proof - 
  from assms have "f`\<langle>x\<^sub>1,GroupInv(G,f)`(x\<^sub>3)\<rangle> = f`\<langle>f`\<langle>x\<^sub>1,GroupInv(G,f)`(x\<^sub>2)\<rangle>,f`\<langle>x\<^sub>2,GroupInv(G,f)`(x\<^sub>3)\<rangle>\<rangle>"
    using group0_valid_in_tgroup group0.group0_2_L14A(1) by blast
  thus "(x\<^sub>1\<ra>(\<rm>x\<^sub>2))\<ra>(x\<^sub>2\<ra>(\<rm>x\<^sub>3)) = x\<^sub>1\<ra> (\<rm>x\<^sub>3)" by simp 
  from assms have "f`\<langle>GroupInv(G,f)`(x\<^sub>1),x\<^sub>3\<rangle> = f`\<langle>f`\<langle>GroupInv(G,f)`(x\<^sub>1),x\<^sub>2\<rangle>,f`\<langle>GroupInv(G,f)`(x\<^sub>2),x\<^sub>3\<rangle>\<rangle>"
    using group0_valid_in_tgroup group0.group0_2_L14A(2) by blast
  thus "((\<rm>x\<^sub>1)\<ra>x\<^sub>2)\<ra>((\<rm>x\<^sub>2)\<ra>x\<^sub>3) = (\<rm>x\<^sub>1)\<ra> x\<^sub>3" by simp
  from assms show "(\<rm> (x\<^sub>1\<ra>x\<^sub>2)) \<ra> (x\<^sub>1\<ra>x\<^sub>3) = (\<rm>x\<^sub>2)\<ra>x\<^sub>3"
    using cancel_middle(1) by simp
  from assms show "(x\<^sub>1\<ra>x\<^sub>2) \<ra> (\<rm>(x\<^sub>3\<ra>x\<^sub>2)) =x\<^sub>1\<ra> (\<rm>x\<^sub>3)"
    using cancel_middle(2) by simp
  from assms show "(\<rm>x\<^sub>1) \<ra> (x\<^sub>1\<ra>x\<^sub>2\<ra>x\<^sub>3) \<ra> (\<rm>x\<^sub>3) = x\<^sub>2"
    using cancel_middle(3) by simp
qed

text\<open> We can cancel an element on the right from both sides of an equation. \<close>

lemma (in topgroup) cancel_right_add: 
  assumes "x\<^sub>1 \<in> G"  "x\<^sub>2 \<in> G"  "x\<^sub>3 \<in> G" "x\<^sub>1\<ra>x\<^sub>2 = x\<^sub>3\<ra>x\<^sub>2" 
  shows "x\<^sub>1 = x\<^sub>3"
  using assms cancel_right by simp

text\<open> We can cancel an element on the left from both sides of an equation. \<close>

lemma (in topgroup) cancel_left_add: 
  assumes "x\<^sub>1 \<in> G"  "x\<^sub>2 \<in> G"  "x\<^sub>3 \<in> G" "x\<^sub>1\<ra>x\<^sub>2 = x\<^sub>1\<ra>x\<^sub>3" 
  shows "x\<^sub>2 = x\<^sub>3"
  using assms cancel_left by simp

text\<open>We can put an element on the other side of an equation.\<close>

lemma (in topgroup) put_on_the_other_side: 
  assumes "x\<^sub>1 \<in> G"  "x\<^sub>2 \<in> G" "x\<^sub>3 = x\<^sub>1\<ra>x\<^sub>2"
  shows "x\<^sub>3\<ra>(\<rm>x\<^sub>2) = x\<^sub>1" and "(\<rm>x\<^sub>1)\<ra>x\<^sub>3 = x\<^sub>2" 
  using assms group0_2_L18 by auto 

text\<open>A simple equation from lemma \<open>simple_equation0\<close> in \<open>Group_ZF\<close> in additive notation \<close>

lemma (in topgroup) simple_equation0_add: 
  assumes "x\<^sub>1 \<in> G"  "x\<^sub>2 \<in> G"  "x\<^sub>3 \<in> G" "x\<^sub>1\<ra>(\<rm>x\<^sub>2) = (\<rm>x\<^sub>3)"
  shows "x\<^sub>3 = x\<^sub>2 \<ra> (\<rm>x\<^sub>1)"
  using assms simple_equation0 by blast

text\<open>A simple equation from lemma \<open>simple_equation1\<close> in \<open>Group_ZF\<close> in additive notation \<close>

lemma (in topgroup) simple_equation1_add: 
  assumes "x\<^sub>1 \<in> G"  "x\<^sub>2 \<in> G"  "x\<^sub>3 \<in> G" "(\<rm>x\<^sub>1)\<ra>x\<^sub>2 = (\<rm>x\<^sub>3)"
  shows "x\<^sub>3 = (\<rm>x\<^sub>2) \<ra> x\<^sub>1"
proof -
  from assms(4) have "f`\<langle>GroupInv(G,f)`(x\<^sub>1),x\<^sub>2\<rangle> = GroupInv(G,f)`(x\<^sub>3)" by simp 
  with assms(1,2,3) have "x\<^sub>3 = f`\<langle>GroupInv(G,f)`(x\<^sub>2),x\<^sub>1\<rangle>" 
    using group0_valid_in_tgroup group0.simple_equation1 by blast
  thus ?thesis by simp
qed

text\<open>The set comprehension form of negative of a set. The proof uses the \<open>ginv_image\<close> lemma from 
  \<open>Group_ZF\<close> theory which states the same thing in multiplicative notation. \<close>

lemma (in topgroup) ginv_image_add: assumes "V\<subseteq>G" 
  shows "(\<sm>V)\<subseteq>G" and "(\<sm>V) = {\<rm>x. x \<in> V}" 
  using assms group0_valid_in_tgroup group0.ginv_image by auto

text\<open> The additive notation version of \<open>ginv_image_el\<close> lemma from \<open>Group_ZF\<close> theory \<close>

lemma (in topgroup) ginv_image_el_add: assumes "V\<subseteq>G" "x \<in> (\<sm>V)"
  shows "(\<rm>x) \<in> V"
  using assms group0_valid_in_tgroup group0.ginv_image_el by simp

text\<open>Of course the product topology is a topology (on $G\times G$).\<close>

lemma (in topgroup) prod_top_on_G:
  shows "\<tau> {is a topology}" and "\<Union>\<tau> = G\<times>G"
  using topSpaceAssum Top_1_4_T1 by auto

text\<open>Let's recall that $f$ is a binary operation on $G$ in this context.\<close>

lemma (in topgroup) topgroup_f_binop: shows "f : G\<times>G \<rightarrow> G"
  using Ggroup group0_def group0.group_oper_assocA by simp

text\<open>A subgroup of a topological group is a topological group 
  with relative topology
  and restricted operation. Relative topology is the same
  as \<open>T {restricted to} H\<close>
  which is defined to be $\{V \cap H: V\in T\}$ in \<open>ZF1\<close> theory.\<close>

lemma (in topgroup) top_subgroup: assumes A1: "IsAsubgroup(H,f)"
  shows "IsAtopologicalGroup(T {restricted to} H,restrict(f,H\<times>H))"
proof -
  let ?\<tau>\<^sub>0 = "T {restricted to} H"
  let ?f\<^sub>H = "restrict(f,H\<times>H)"
  have "\<Union>?\<tau>\<^sub>0 = G \<inter> H" using union_restrict by simp
  also from A1 have "\<dots> = H" 
    using group0_valid_in_tgroup group0.group0_3_L2 by blast
  finally have "\<Union>?\<tau>\<^sub>0 = H" by simp
  have "?\<tau>\<^sub>0 {is a topology}" using Top_1_L4 by simp
  moreover from A1 \<open>\<Union>?\<tau>\<^sub>0 = H\<close> have "IsAgroup(\<Union>?\<tau>\<^sub>0,?f\<^sub>H)"
    using IsAsubgroup_def by simp
  moreover have "IsContinuous(ProductTopology(?\<tau>\<^sub>0,?\<tau>\<^sub>0),?\<tau>\<^sub>0,?f\<^sub>H)"
  proof -
    have "two_top_spaces0(\<tau>, T,f)"
      using topSpaceAssum prod_top_on_G topgroup_f_binop prod_top_on_G
	two_top_spaces0_def by simp
    moreover 
    from A1 have "H \<subseteq> G" using group0_valid_in_tgroup group0.group0_3_L2
      by simp
    then have "H\<times>H \<subseteq> \<Union>\<tau>" using prod_top_on_G by auto
    moreover have "IsContinuous(\<tau>,T,f)" using fcon by simp
    ultimately have 
      "IsContinuous(\<tau> {restricted to} H\<times>H, T {restricted to} ?f\<^sub>H``(H\<times>H),?f\<^sub>H)" using two_top_spaces0.restr_restr_image_cont
      by simp
    moreover have
      "ProductTopology(?\<tau>\<^sub>0,?\<tau>\<^sub>0) = \<tau> {restricted to} H\<times>H" using topSpaceAssum prod_top_restr_comm
      by simp
    moreover from A1 have "?f\<^sub>H``(H\<times>H) = H" using image_subgr_op
      by simp
    ultimately show ?thesis by simp
  qed 
  moreover have "IsContinuous(?\<tau>\<^sub>0,?\<tau>\<^sub>0,GroupInv(\<Union>?\<tau>\<^sub>0,?f\<^sub>H))"
  proof -
    let ?g = "restrict(GroupInv(G,f),H)"
    have "GroupInv(G,f) : G \<rightarrow> G"
      using Ggroup group0_2_T2 by simp
    then have "two_top_spaces0(T,T,GroupInv(G,f))"
      using topSpaceAssum two_top_spaces0_def by simp
    moreover from A1 have "H \<subseteq> \<Union>T" 
      using group0_valid_in_tgroup group0.group0_3_L2
      by simp
    ultimately have 
      "IsContinuous(?\<tau>\<^sub>0,T {restricted to} ?g``(H),?g)"
      using inv_cont two_top_spaces0.restr_restr_image_cont
      by simp
    moreover from A1 have "?g``(H) = H"
      using group0_valid_in_tgroup group0.restr_inv_onto
      by simp  
    moreover
    from A1 have "GroupInv(H,?f\<^sub>H) = ?g"
      using group0_valid_in_tgroup group0.group0_3_T1
      by simp
    with \<open>\<Union>?\<tau>\<^sub>0 = H\<close> have "?g = GroupInv(\<Union>?\<tau>\<^sub>0,?f\<^sub>H)" by simp
    ultimately show ?thesis by simp
  qed
  ultimately show ?thesis unfolding IsAtopologicalGroup_def by simp
qed

subsection\<open>Interval arithmetic, translations and inverse of set\<close>

text\<open>In this section we list some properties of operations of translating a
  set and reflecting it around the neutral element of the group. Many of the results
  are proven in other theories, here we just collect them and rewrite in notation
  specific to the \<open>topgroup\<close> context.\<close>

text\<open>Different ways of looking at adding sets.\<close>

lemma (in topgroup) interval_add: assumes "A\<subseteq>G" "B\<subseteq>G" shows
  "A\<sad>B \<subseteq> G" 
  "A\<sad>B = f``(A\<times>B)"  
  "A\<sad>B = (\<Union>x\<in>A. x\<ltr>B)"
  "A\<sad>B = {x\<ra>y. \<langle>x,y\<rangle> \<in> A\<times>B}" 
proof -
  from assms show "A\<sad>B \<subseteq> G" and "A\<sad>B = f``(A\<times>B)" and "A\<sad>B = {x\<ra>y. \<langle>x,y\<rangle> \<in> A\<times>B}"
    using topgroup_f_binop lift_subsets_explained by auto
  from assms show "A\<sad>B = (\<Union>x\<in>A. x\<ltr>B)"
    using group0_valid_in_tgroup group0.image_ltrans_union by simp
qed

text\<open> If the neutral element is in a set, then it is in the sum of the sets. \<close>

lemma (in topgroup) interval_add_zero: assumes "A\<subseteq>G" "\<zero>\<in>A"
  shows "\<zero> \<in> A\<sad>A"
proof -
  from assms have "\<zero>\<ra>\<zero> \<in> A\<sad>A" using interval_add(4) by auto
  then show "\<zero> \<in> A\<sad>A" using group0_2_L2 by auto
qed

text\<open>Some lemmas from \<open>Group_ZF_1\<close> about images of set by translations 
  written in additive notation\<close>

lemma (in topgroup) lrtrans_image: assumes "V\<subseteq>G" "x\<in>G"
  shows 
    "x\<ltr>V = {x\<ra>v. v\<in>V}" 
    "V\<rtr>x = {v\<ra>x. v\<in>V}"
proof -
  from assms have "LeftTranslation(G,f,x)``(V) = {f`\<langle>x,v\<rangle>. v\<in>V}"
    using group0_valid_in_tgroup group0.ltrans_image by blast
  thus "x\<ltr>V = {x\<ra>v. v\<in>V}" by simp
  from assms have "RightTranslation(G,f,x)``(V) = {f`\<langle>v,x\<rangle>. v\<in>V}"
    using group0_valid_in_tgroup group0.rtrans_image by blast
  thus "V\<rtr>x = {v\<ra>x. v\<in>V}" by simp
qed  
  
text\<open> Right and left translations of a set are subsets of the group. 
  This is of course typically applied to the subsets of the group, but formally we don't
  need to assume that. \<close>

lemma (in topgroup) lrtrans_in_group_add: assumes "x\<in>G" 
  shows  "x\<ltr>V \<subseteq> G" and "V\<rtr>x \<subseteq>G"
  using assms lrtrans_in_group by auto
    
text\<open> A corollary from \<open>interval_add\<close> \<close>

corollary (in topgroup) elements_in_set_sum: assumes "A\<subseteq>G" "B\<subseteq>G"
  "t \<in> A\<sad>B" shows "\<exists>s\<in>A. \<exists>q\<in>B. t=s\<ra>q"
  using assms interval_add(4) by auto 

text\<open> A corollary from \<open> lrtrans_image\<close> \<close> 

corollary (in topgroup) elements_in_ltrans: 
  assumes "B\<subseteq>G" "g\<in>G" "t \<in> g\<ltr>B" 
  shows "\<exists>q\<in>B. t=g\<ra>q"
  using assms lrtrans_image(1) by simp 

text\<open> Another corollary of \<open>lrtrans_image\<close> \<close>

corollary (in topgroup) elements_in_rtrans: 
  assumes "B\<subseteq>G" "g\<in>G"  "t \<in> B\<rtr>g" shows "\<exists>q\<in>B. t=q\<ra>g"
  using assms lrtrans_image(2) by simp

text\<open>Another corollary from \<open>interval_add\<close> \<close>

corollary (in topgroup) elements_in_set_sum_inv: 
  assumes "A\<subseteq>G" "B\<subseteq>G" "t=s\<ra>q" "s\<in>A" "q\<in>B"
  shows "t \<in> A\<sad>B"
  using assms interval_add by auto 

text\<open>Another corollary of \<open>lrtrans_image\<close> \<close>

corollary (in topgroup) elements_in_ltrans_inv: assumes "B\<subseteq>G" "g\<in>G" "q\<in>B" "t=g\<ra>q"
  shows "t \<in> g\<ltr>B"
  using assms lrtrans_image(1) by auto 

text\<open>Another corollary of \<open>rtrans_image_add\<close> \<close>

lemma (in topgroup) elements_in_rtrans_inv:
  assumes "B\<subseteq>G" "g\<in>G" "q\<in>B" "t=q\<ra>g"
  shows "t \<in> B\<rtr>g"
  using assms lrtrans_image(2) by auto 

text\<open>Right and left translations are continuous.\<close>

lemma (in topgroup) trans_cont: assumes "g\<in>G" shows
  "IsContinuous(T,T,RightTranslation(G,f,g))" and
  "IsContinuous(T,T,LeftTranslation(G,f,g))"
using assms group0_valid_in_tgroup group0.trans_eq_section
  topgroup_f_binop fcon prod_top_spaces0_valid 
  prod_top_spaces0.fix_1st_var_cont prod_top_spaces0.fix_2nd_var_cont
  by auto

text\<open>Left and right translations of an open set are open.\<close>

lemma (in topgroup) open_tr_open: assumes "g\<in>G" and "V\<in>T"
  shows "g\<ltr>V \<in> T" and  "V\<rtr>g \<in> T"
  using assms neg_in_tgroup trans_cont IsContinuous_def 
    group0_valid_in_tgroup group0.trans_image_vimage by auto

text\<open>Right and left translations are homeomorphisms.\<close>

lemma (in topgroup) tr_homeo: assumes "g\<in>G" shows
  "IsAhomeomorphism(T,T,RightTranslation(G,f,g))" and
  "IsAhomeomorphism(T,T,LeftTranslation(G,f,g))"
  using assms group0_valid_in_tgroup group0.trans_bij trans_cont open_tr_open
    bij_cont_open_homeo by auto

text\<open>Left translations preserve interior.\<close>

lemma (in topgroup) ltrans_interior: assumes A1: "g\<in>G" and A2: "A\<subseteq>G" 
  shows "g \<ltr> int(A) = int(g\<ltr>A)"
proof -
  from assms have "A \<subseteq> \<Union>T" and "IsAhomeomorphism(T,T,LeftTranslation(G,f,g))" using tr_homeo 
    by auto
  then show ?thesis using int_top_invariant by simp
qed

text\<open>Right translations preserve interior.\<close>

lemma (in topgroup) rtrans_interior: assumes A1: "g\<in>G" and A2: "A\<subseteq>G" 
  shows "int(A) \<rtr> g = int(A\<rtr>g)"
proof -
  from assms have "A \<subseteq> \<Union>T" and "IsAhomeomorphism(T,T,RightTranslation(G,f,g))" using tr_homeo 
    by auto
  then show ?thesis using int_top_invariant by simp
qed

text\<open>Translating by an inverse and then by an element cancels out.\<close>

lemma (in topgroup) trans_inverse_elem: assumes "g\<in>G" and "A\<subseteq>G"
  shows "g\<ltr>((\<rm>g)\<ltr>A) = A"
using assms neg_in_tgroup group0_valid_in_tgroup group0.trans_comp_image
  group0.group0_2_L6 group0.trans_neutral image_id_same by simp

text\<open>Inverse of an open set is open.\<close>

lemma (in topgroup) open_inv_open: assumes "V\<in>T" shows "(\<sm>V) \<in> T"
  using assms group0_valid_in_tgroup group0.inv_image_vimage
    inv_cont IsContinuous_def by simp

text\<open>Inverse is a homeomorphism.\<close>

lemma (in topgroup) inv_homeo: shows "IsAhomeomorphism(T,T,GroupInv(G,f))"
  using group0_valid_in_tgroup group0.group_inv_bij inv_cont open_inv_open
  bij_cont_open_homeo by simp

text\<open>Taking negative preserves interior.\<close>

lemma (in topgroup) int_inv_inv_int: assumes "A \<subseteq> G" 
  shows "int(\<sm>A) = \<sm>(int(A))"
  using assms inv_homeo int_top_invariant by simp

subsection\<open>Neighborhoods of zero\<close>

text\<open>Zero neighborhoods are (not necessarily open) sets whose interior
  contains the neutral element of the group. In the \<open>topgroup\<close> locale
  the collection of neighboorhoods of zero is denoted \<open>\<N>\<^sub>0\<close>. \<close>

text\<open>The whole space is a neighborhood of zero.\<close>

lemma (in topgroup) zneigh_not_empty: shows "G \<in> \<N>\<^sub>0"
  using topSpaceAssum IsATopology_def Top_2_L3 zero_in_tgroup
  by simp


text\<open>Any element that belongs to a subset of the group belongs to that subset with the 
  interior of a neighborhood of zero added. \<close>

lemma (in topgroup) elem_in_int_sad: assumes "A\<subseteq>G" "g\<in>A" "H \<in> \<N>\<^sub>0"
  shows "g \<in> A\<sad>int(H)"
proof -
  from assms(3) have "\<zero> \<in> int(H)" and "int(H) \<subseteq> G" using Top_2_L2 by auto
  with assms(1,2) have "g\<ra>\<zero> \<in> A\<sad>int(H)" using elements_in_set_sum_inv
    by simp
  with assms(1,2) show ?thesis using group0_2_L2 by auto
qed

text\<open>Any element belongs to the interior of any neighboorhood of zero
  left translated by that element.\<close>

lemma (in topgroup) elem_in_int_ltrans:
  assumes "g\<in>G" and "H \<in> \<N>\<^sub>0"
  shows "g \<in> int(g\<ltr>H)" and "g \<in> int(g\<ltr>H) \<sad> int(H)"
proof -
  from assms(2) have "\<zero> \<in> int(H)" and "int(H) \<subseteq> G" using Top_2_L2 by auto
  with assms(1) have "g \<in> g \<ltr> int(H)"
    using group0_valid_in_tgroup group0.neut_trans_elem by simp
  with assms show "g \<in> int(g\<ltr>H)" using ltrans_interior by simp
  from assms(1) have "int(g\<ltr>H) \<subseteq> G" using lrtrans_in_group_add(1) Top_2_L1
    by blast
  with \<open>g \<in> int(g\<ltr>H)\<close> assms(2) show "g \<in> int(g\<ltr>H) \<sad> int(H)" 
    using elem_in_int_sad by simp
qed

text\<open>Any element belongs to the interior of any neighboorhood of zero
  right translated by that element.\<close>

lemma (in topgroup) elem_in_int_rtrans:
  assumes A1: "g\<in>G" and A2: "H \<in> \<N>\<^sub>0"
  shows "g \<in> int(H\<rtr>g)" and "g \<in> int(H\<rtr>g) \<sad> int(H)"
proof -
  from A2 have "\<zero> \<in> int(H)" and "int(H) \<subseteq> G" using Top_2_L2 by auto
  with A1 have "g \<in> int(H) \<rtr> g"
    using group0_valid_in_tgroup group0.neut_trans_elem by simp
  with assms show "g \<in> int(H\<rtr>g)" using rtrans_interior by simp
  from assms(1) have "int(H\<rtr>g) \<subseteq> G" using lrtrans_in_group_add(2) Top_2_L1
    by blast
  with \<open>g \<in> int(H\<rtr>g)\<close> assms(2) show "g \<in> int(H\<rtr>g) \<sad> int(H)" 
    using elem_in_int_sad by simp
qed

text\<open>Negative of a neighborhood of zero is a neighborhood of zero.\<close>

lemma (in topgroup) neg_neigh_neigh: assumes "H \<in> \<N>\<^sub>0"
  shows "(\<sm>H) \<in> \<N>\<^sub>0"
proof -
  from assms have "int(H) \<subseteq> G" and "\<zero> \<in> int(H)" using Top_2_L1 by auto
  with assms have "\<zero> \<in> int(\<sm>H)" using group0_valid_in_tgroup group0.neut_inv_neut
    int_inv_inv_int by simp
  moreover
  have "GroupInv(G,f):G\<rightarrow>G" using Ggroup group0_2_T2 by simp
  then have "(\<sm>H) \<subseteq> G" using func1_1_L6 by simp
  ultimately show ?thesis by simp
qed

text\<open>Left translating an open set by a negative of a point that belongs to it
  makes it a neighboorhood of zero.\<close>

lemma (in topgroup) open_trans_neigh: assumes A1: "U\<in>T" and "g\<in>U"
  shows "(\<rm>g)\<ltr>U \<in> \<N>\<^sub>0"
proof -
  let ?H = "(\<rm>g)\<ltr>U"
  from assms have "g\<in>G" by auto
  then have "(\<rm>g) \<in> G" using neg_in_tgroup by simp
  with A1 have "?H\<in>T" using open_tr_open by simp
  hence "?H \<subseteq> G" by auto
  moreover have "\<zero> \<in> int(?H)"
  proof -
    from assms have "U\<subseteq>G" and "g\<in>U" by auto
    with \<open>?H\<in>T\<close> show "\<zero> \<in> int(?H)" 
      using group0_valid_in_tgroup group0.elem_trans_neut Top_2_L3
        by auto
  qed
  ultimately show ?thesis by simp
qed

text\<open>Right translating an open set by a negative of a point that belongs to it
  makes it a neighboorhood of zero.\<close>

lemma (in topgroup) open_trans_neigh_2: assumes A1: "U\<in>T" and "g\<in>U"
  shows "U\<rtr>(\<rm>g) \<in> \<N>\<^sub>0"
proof -
  let ?H = "U\<rtr>(\<rm>g)"
  from assms have "g\<in>G" by auto
  then have "(\<rm>g) \<in> G" using neg_in_tgroup by simp
  with A1 have "?H\<in>T" using open_tr_open by simp
  hence "?H \<subseteq> G" by auto
  moreover have "\<zero> \<in> int(?H)"
  proof -
    from assms have "U\<subseteq>G" and "g\<in>U" by auto
    with \<open>?H\<in>T\<close> show "\<zero> \<in> int(?H)" 
      using group0_valid_in_tgroup group0.elem_trans_neut Top_2_L3
        by auto
  qed
  ultimately show ?thesis by simp
qed

text\<open>Right and left translating an neighboorhood of zero by a point and its negative 
  makes it back a neighboorhood of zero.\<close>

lemma (in topgroup) lrtrans_neigh: assumes "W\<in>\<N>\<^sub>0" and "x\<in>G"
  shows "x\<ltr>(W\<rtr>(\<rm>x)) \<in> \<N>\<^sub>0" and "(x\<ltr>W)\<rtr>(\<rm>x) \<in> \<N>\<^sub>0"
proof -
  from assms(2) have "x\<ltr>(W\<rtr>(\<rm>x)) \<subseteq> G" using lrtrans_in_group_add(1) by simp
  moreover have "\<zero> \<in> int(x\<ltr>(W\<rtr>(\<rm>x)))"
  proof -
    from assms(2) have "int(W\<rtr>(\<rm>x)) \<subseteq> G" 
      using neg_in_tgroup lrtrans_in_group_add(2) Top_2_L1 by blast
    with assms(2) have "(x\<ltr>int((W\<rtr>(\<rm>x)))) = {x\<ra>y. y\<in>int(W\<rtr>(\<rm>x))}"
      using lrtrans_image(1) by simp
    moreover from assms have "(\<rm>x) \<in> int(W\<rtr>(\<rm>x))" 
      using neg_in_tgroup elem_in_int_rtrans(1) by simp
    ultimately have "x\<ra>(\<rm>x) \<in> x\<ltr>int(W\<rtr>(\<rm>x))" by auto
    with assms show ?thesis using group0_2_L6 neg_in_tgroup lrtrans_in_group_add(2) ltrans_interior 
      by simp
  qed
  ultimately show "x\<ltr>(W\<rtr>(\<rm>x)) \<in> \<N>\<^sub>0" by simp
  from assms(2) have "(x\<ltr>W)\<rtr>(\<rm>x) \<subseteq> G" using lrtrans_in_group_add(2) neg_in_tgroup 
    by simp
  moreover have "\<zero> \<in> int((x\<ltr>W)\<rtr>(\<rm>x))"
  proof -
    from assms(2) have "int((x\<ltr>W)) \<subseteq> G" using lrtrans_in_group_add(1) Top_2_L1 by blast
    with assms(2) have "int(x\<ltr>W) \<rtr> (\<rm>x) = {y\<ra>(\<rm>x).y\<in>int(x\<ltr>W)}"
      using neg_in_tgroup  lrtrans_image(2) by simp
    moreover from assms have "x \<in> int(x\<ltr>W)" using elem_in_int_ltrans(1) by simp
    ultimately have "x\<ra>(\<rm>x) \<in> int(x\<ltr>W) \<rtr> (\<rm>x)" by auto
    with assms(2) have "\<zero> \<in> int(x\<ltr>W) \<rtr> (\<rm>x)" using group0_2_L6 by simp
    with assms show ?thesis using group0_2_L6 neg_in_tgroup lrtrans_in_group_add(1) rtrans_interior
      by auto
  qed
  ultimately show "(x\<ltr>W)\<rtr>(\<rm>x) \<in> \<N>\<^sub>0" by simp
qed
 
subsection\<open>Closure in topological groups\<close>

text\<open>This section is devoted to a characterization of closure
  in topological groups.\<close>

text\<open>Closure of a set is contained in the sum of the set and any
  neighboorhood of zero.\<close>

lemma (in topgroup) cl_contains_zneigh:
  assumes A1: "A\<subseteq>G" and A2: "H \<in> \<N>\<^sub>0"
  shows "cl(A) \<subseteq> A\<sad>H"
proof
  fix x assume "x \<in> cl(A)"
  from A1 have "cl(A) \<subseteq> G" using Top_3_L11 by simp
  with \<open>x \<in> cl(A)\<close> have "x\<in>G" by auto
  have "int(H) \<subseteq> G" using Top_2_L2 by auto
  let ?V = "int(x \<ltr> (\<sm>H))"
  have "?V = x \<ltr> (\<sm>int(H))"
  proof -
    from A2 \<open>x\<in>G\<close> have "?V = x \<ltr> int(\<sm>H)" 
      using neg_neigh_neigh ltrans_interior by simp
    with A2 show ?thesis  using int_inv_inv_int by simp
  qed
  have "A\<inter>?V \<noteq> 0"
  proof -
    from A2 \<open>x\<in>G\<close> \<open>x \<in> cl(A)\<close> have "?V\<in>T" and "x \<in> cl(A) \<inter> ?V" 
      using neg_neigh_neigh elem_in_int_ltrans(1) Top_2_L2 by auto
    with A1 show "A\<inter>?V \<noteq> 0" using cl_inter_neigh by simp
  qed
  then obtain y where "y\<in>A" and "y\<in>?V" by auto
  with \<open>?V = x \<ltr> (\<sm>int(H))\<close> \<open>int(H) \<subseteq> G\<close> \<open>x\<in>G\<close> have "x \<in> y\<ltr>int(H)"
    using group0_valid_in_tgroup group0.ltrans_inv_in by simp
  with \<open>y\<in>A\<close> have "x \<in> (\<Union>y\<in>A. y\<ltr>H)" using Top_2_L1 func1_1_L8 by auto
  with assms show "x \<in> A\<sad>H" using interval_add(3) by simp
qed

text\<open>The next theorem provides a characterization of closure in topological
  groups in terms of neighborhoods of zero.\<close>

theorem (in topgroup) cl_topgroup:
  assumes "A\<subseteq>G" shows "cl(A) = (\<Inter>H\<in>\<N>\<^sub>0. A\<sad>H)"
proof
  from assms show "cl(A) \<subseteq> (\<Inter>H\<in>\<N>\<^sub>0. A\<sad>H)" 
    using zneigh_not_empty cl_contains_zneigh by auto
next
  { fix x assume "x \<in> (\<Inter>H\<in>\<N>\<^sub>0. A\<sad>H)"
    then have "x \<in> A\<sad>G" using zneigh_not_empty by auto
    with assms have "x\<in>G" using interval_add by blast
    have "\<forall>U\<in>T. x\<in>U \<longrightarrow> U\<inter>A \<noteq> 0"
    proof -
      { fix U assume "U\<in>T" and "x\<in>U"
        let ?H = "\<sm>((\<rm>x)\<ltr>U)"
        from \<open>U\<in>T\<close> and \<open>x\<in>U\<close> have "(\<rm>x)\<ltr>U \<subseteq> G" and "?H \<in> \<N>\<^sub>0" 
          using open_trans_neigh neg_neigh_neigh by auto
        with \<open>x \<in> (\<Inter>H\<in>\<N>\<^sub>0. A\<sad>H)\<close> have "x \<in> A\<sad>?H" by auto
        with assms \<open>?H \<in> \<N>\<^sub>0\<close> obtain y where "y\<in>A" and "x \<in> y\<ltr>?H"
          using interval_add(3) by auto
        have "y\<in>U"
        proof -
          from assms \<open>y\<in>A\<close> have "y\<in>G" by auto
          with \<open>(\<rm>x)\<ltr>U \<subseteq> G\<close> and \<open>x \<in> y\<ltr>?H\<close> have "y \<in> x\<ltr>((\<rm>x)\<ltr>U)"
            using group0_valid_in_tgroup group0.ltrans_inv_in by simp
          with \<open>U\<in>T\<close> \<open>x\<in>G\<close> show "y\<in>U" 
            using neg_in_tgroup group0_valid_in_tgroup group0.trans_comp_image
              group0.group0_2_L6 group0.trans_neutral image_id_same
              by auto
        qed
        with \<open>y\<in>A\<close> have "U\<inter>A \<noteq> 0" by auto
      } thus ?thesis by simp
    qed
    with assms \<open>x\<in>G\<close> have "x \<in> cl(A)" using inter_neigh_cl by simp
  } thus "(\<Inter>H\<in>\<N>\<^sub>0. A\<sad>H) \<subseteq> cl(A)" by auto
qed

subsection\<open>Sums of sequences of elements and subsets\<close>

text\<open>In this section we consider properties of the function $G^n\rightarrow G$, 
  $x=(x_0,x_1,...,x_{n-1})\mapsto \sum_{i=0}^{n-1}x_i$. We will model the cartesian product
  $G^n$ by the space of sequences $n\rightarrow G$, where $n=\{0,1,...,n-1 \}$ is a natural number. 
  This space is equipped with a natural product topology defined in \<open>Topology_ZF_3\<close>.\<close>

text\<open>Let's recall first that the sum of elements of a group is an element of the group.\<close>

lemma (in topgroup) sum_list_in_group:
  assumes "n \<in> nat" and "x: succ(n)\<rightarrow>G"
  shows "(\<Sum>x) \<in> G"
proof -
  from assms have "semigr0(G,f)" and "n \<in> nat" "x: succ(n)\<rightarrow>G"
    using semigr0_valid_in_tgroup by auto
  then have "Fold1(f,x) \<in> G" by (rule semigr0.prod_type)
  thus "(\<Sum>x) \<in> G" by simp
qed

text\<open>In this context \<open>x\<ra>y\<close> is the same as the value of the group operation
  on the elements $x$ and $y$. Normally we shouldn't need to state this a s separate lemma.\<close>

lemma (in topgroup) grop_def1: shows "f`\<langle>x,y\<rangle> = x\<ra>y" by simp 

text\<open>Another theorem from \<open>Semigroup_ZF\<close> theory that is useful to have in the
  additive notation.\<close>

lemma (in topgroup) shorter_set_add:
  assumes "n \<in> nat" and "x: succ(succ(n))\<rightarrow>G"
  shows "(\<Sum>x) = (\<Sum>Init(x)) \<ra> (x`(succ(n)))"
proof -
  from assms have "semigr0(G,f)" and "n \<in> nat" "x: succ(succ(n))\<rightarrow>G"
    using semigr0_valid_in_tgroup by auto
  then have "Fold1(f,x) = f`\<langle>Fold1(f,Init(x)),x`(succ(n))\<rangle>"
    by (rule semigr0.shorter_seq)
  thus ?thesis by simp   
qed

text\<open>Sum is a continuous function in the product topology.\<close>

theorem (in topgroup) sum_continuous: assumes "n \<in> nat"
  shows "IsContinuous(SeqProductTopology(succ(n),T),T,{\<langle>x,\<Sum>x\<rangle>.x\<in>succ(n)\<rightarrow>G})"
  proof -
    note \<open>n \<in> nat\<close>
    moreover have "IsContinuous(SeqProductTopology(succ(0),T),T,{\<langle>x,\<Sum>x\<rangle>.x\<in>succ(0)\<rightarrow>G})"
    proof -
      have "{\<langle>x,\<Sum>x\<rangle>.x\<in>succ(0)\<rightarrow>G} = {\<langle>x,x`(0)\<rangle>. x\<in>1\<rightarrow>G}"
        using semigr0_valid_in_tgroup semigr0.prod_of_1elem by simp
      moreover have
        "IsAhomeomorphism(SeqProductTopology(1,T),T,{\<langle>x,x`(0)\<rangle>. x\<in>1\<rightarrow>\<Union>T})" using topSpaceAssum singleton_prod_top1
          by simp
      ultimately show ?thesis using IsAhomeomorphism_def by simp
    qed
    moreover have "\<forall>k\<in>nat.
      IsContinuous(SeqProductTopology(succ(k),T),T,{\<langle>x,\<Sum>x\<rangle>.x\<in>succ(k)\<rightarrow>G})
      \<longrightarrow>
      IsContinuous(SeqProductTopology(succ(succ(k)),T),T,{\<langle>x,\<Sum>x\<rangle>.x\<in>succ(succ(k))\<rightarrow>G})"
      proof -
        { fix k assume "k \<in> nat"
          let ?s = "{\<langle>x,\<Sum>x\<rangle>.x\<in>succ(k)\<rightarrow>G}"
          let ?g = "{\<langle>p,\<langle>?s`(fst(p)),snd(p)\<rangle>\<rangle>. p \<in> (succ(k)\<rightarrow>G)\<times>G}"
          let ?h = "{\<langle>x,\<langle>Init(x),x`(succ(k))\<rangle>\<rangle>. x \<in> succ(succ(k))\<rightarrow>G}"
          let ?\<phi> = "SeqProductTopology(succ(k),T)"
          let ?\<psi> = "SeqProductTopology(succ(succ(k)),T)"
          assume "IsContinuous(?\<phi>,T,?s)"
          from \<open>k \<in> nat\<close> have "?s: (succ(k)\<rightarrow>G) \<rightarrow> G"
            using sum_list_in_group ZF_fun_from_total by simp 
          have "?h: (succ(succ(k))\<rightarrow>G)\<rightarrow>(succ(k)\<rightarrow>G)\<times>G"
          proof -
            { fix x assume "x \<in> succ(succ(k))\<rightarrow>G"
              with \<open>k \<in> nat\<close> have "Init(x) \<in> (succ(k)\<rightarrow>G)"
                using init_props by simp
              with \<open>k \<in> nat\<close> \<open>x : succ(succ(k))\<rightarrow>G\<close> 
                have "\<langle>Init(x),x`(succ(k))\<rangle> \<in> (succ(k)\<rightarrow>G)\<times>G" using apply_funtype
                  by blast 
           } then show ?thesis using ZF_fun_from_total by simp
          qed
          moreover have "?g:((succ(k)\<rightarrow>G)\<times>G)\<rightarrow>(G\<times>G)"
          proof -
            { fix p assume "p \<in> (succ(k)\<rightarrow>G)\<times>G"
              hence "fst(p): succ(k)\<rightarrow>G" and "snd(p) \<in> G" by auto
              with \<open>?s: (succ(k)\<rightarrow>G) \<rightarrow> G\<close> have "\<langle>?s`(fst(p)),snd(p)\<rangle> \<in> G\<times>G"
                using apply_funtype by blast 
            } then show "?g:((succ(k)\<rightarrow>G)\<times>G)\<rightarrow>(G\<times>G)" using ZF_fun_from_total
              by simp
          qed
          moreover have "f : G\<times>G \<rightarrow> G" using topgroup_f_binop by simp
          ultimately have "f O ?g O ?h :(succ(succ(k))\<rightarrow>G)\<rightarrow>G" using comp_fun
            by blast 
          from \<open>k \<in> nat\<close> have "IsContinuous(?\<psi>,ProductTopology(?\<phi>,T),?h)"
            using topSpaceAssum finite_top_prod_homeo IsAhomeomorphism_def
            by simp
          moreover have "IsContinuous(ProductTopology(?\<phi>,T),\<tau>,?g)"
          proof -
            from topSpaceAssum have 
               "T {is a topology}" "?\<phi> {is a topology}" "\<Union>?\<phi> = succ(k)\<rightarrow>G"
               using seq_prod_top_is_top by auto
            moreover from \<open>\<Union>?\<phi> = succ(k)\<rightarrow>G\<close> \<open>?s: (succ(k)\<rightarrow>G) \<rightarrow> G\<close> 
              have "?s:\<Union>?\<phi>\<rightarrow>\<Union>T" by simp 
            moreover note \<open>IsContinuous(?\<phi>,T,?s)\<close>
            moreover from \<open>\<Union>?\<phi> = succ(k)\<rightarrow>G\<close> 
              have "?g = {\<langle>p,\<langle>?s`(fst(p)),snd(p)\<rangle>\<rangle>. p \<in> \<Union>?\<phi>\<times>\<Union>T}"
              by simp
            ultimately have "IsContinuous(ProductTopology(?\<phi>,T),ProductTopology(T,T),?g)"
              using cart_prod_cont1 by blast 
            thus ?thesis by simp
          qed         
          moreover have "IsContinuous(\<tau>,T,f)" using fcon by simp
          moreover have "{\<langle>x,\<Sum>x\<rangle>.x\<in>succ(succ(k))\<rightarrow>G} = f O ?g O ?h"
          proof -
            let ?d = "{\<langle>x,\<Sum>x\<rangle>.x\<in>succ(succ(k))\<rightarrow>G}"
            from \<open>k\<in>nat\<close> have "\<forall>x\<in>succ(succ(k))\<rightarrow>G. (\<Sum>x) \<in> G"
              using sum_list_in_group by blast 
            then have "?d:(succ(succ(k))\<rightarrow>G)\<rightarrow>G" 
              using sum_list_in_group ZF_fun_from_total by simp
            moreover note \<open>f O ?g O ?h :(succ(succ(k))\<rightarrow>G)\<rightarrow>G\<close>
            moreover have "\<forall>x\<in>succ(succ(k))\<rightarrow>G. ?d`(x) = (f O ?g O ?h)`(x)"
            proof
              fix x assume "x\<in>succ(succ(k))\<rightarrow>G"
              then have I: "?h`(x) = \<langle>Init(x),x`(succ(k))\<rangle>"
                using ZF_fun_from_tot_val1 by simp
              moreover from \<open>k\<in>nat\<close> \<open>x\<in>succ(succ(k))\<rightarrow>G\<close> 
                have "Init(x): succ(k)\<rightarrow>G" 
                using init_props by simp
              moreover from \<open>k\<in>nat\<close> \<open>x:succ(succ(k))\<rightarrow>G\<close> 
                have II: "x`(succ(k)) \<in> G"
                using apply_funtype by blast
              ultimately have "?h`(x) \<in> (succ(k)\<rightarrow>G)\<times>G" by simp
              then have "?g`(?h`(x)) = \<langle>?s`(fst(?h`(x))),snd(?h`(x))\<rangle>"
                using ZF_fun_from_tot_val1 by simp
              with I have "?g`(?h`(x)) = \<langle>?s`(Init(x)),x`(succ(k))\<rangle>"
                by simp
              with \<open>Init(x): succ(k)\<rightarrow>G\<close> have "?g`(?h`(x)) = \<langle>\<Sum>Init(x),x`(succ(k))\<rangle>"
                using ZF_fun_from_tot_val1 by simp
              with \<open>k \<in> nat\<close> \<open>x: succ(succ(k))\<rightarrow>G\<close> 
                have "f`(?g`(?h`(x))) = (\<Sum>x)"
                using shorter_set_add by simp
              with \<open>x \<in> succ(succ(k))\<rightarrow>G\<close> have "f`(?g`(?h`(x))) = ?d`(x)"
                using ZF_fun_from_tot_val1 by simp
              moreover from 
                \<open>?h: (succ(succ(k))\<rightarrow>G)\<rightarrow>(succ(k)\<rightarrow>G)\<times>G\<close>
                \<open>?g:((succ(k)\<rightarrow>G)\<times>G)\<rightarrow>(G\<times>G)\<close>
                \<open>f:(G\<times>G)\<rightarrow>G\<close> \<open>x\<in>succ(succ(k))\<rightarrow>G\<close>
                have "(f O ?g O ?h)`(x) = f`(?g`(?h`(x)))" by (rule func1_1_L18)
              ultimately show "?d`(x) = (f O ?g O ?h)`(x)" by simp 
            qed
            ultimately show "{\<langle>x,\<Sum>x\<rangle>.x\<in>succ(succ(k))\<rightarrow>G} = f O ?g O ?h" 
              using func_eq by simp
          qed
          moreover note \<open>IsContinuous(\<tau>,T,f)\<close>
          ultimately have "IsContinuous(?\<psi>,T,{\<langle>x,\<Sum>x\<rangle>.x\<in>succ(succ(k))\<rightarrow>G})"
            using comp_cont3 by simp
        } thus ?thesis by simp
      qed
    ultimately show ?thesis by (rule ind_on_nat)
  qed
end
