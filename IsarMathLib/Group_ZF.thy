(* 
This file is a part of IsarMathLib - 
a library of formalized mathematics for Isabelle/Isar.

Copyright (C) 2005 - 2008  Slawomir Kolodynski

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

section \<open>Groups - introduction\<close>

theory Group_ZF imports Monoid_ZF

begin

text\<open>This theory file covers basics of group theory.\<close>

subsection\<open>Definition and basic properties of groups\<close>

text\<open>In this section we define the notion of a group and set up the 
   notation for discussing groups. We prove some basic theorems about
   groups.\<close>

text\<open>To define a group we take a monoid and add a requirement 
  that the right inverse needs to exist for every element of the group.\<close>
  
definition
  "IsAgroup(G,f) \<equiv> 
  (IsAmonoid(G,f) \<and> (\<forall>g\<in>G. \<exists>b\<in>G. f`\<langle>g,b\<rangle> = TheNeutralElement(G,f)))"

text\<open>We define the group inverse as the set
  $\{\langle x,y \rangle \in G\times G: x\cdot y = e \}$, where $e$ is the
  neutral element of the group. This set (which can be written as 
  $(\cdot)^{-1}\{ e\}$) is a certain relation on the group (carrier). 
  Since, as we show later, for every $x\in G$ there is exactly one $y\in G$
  such that $x \cdot y = e$  this relation is in fact a function from $G$ to $G$.\<close>

definition
  "GroupInv(G,f) \<equiv> {\<langle>x,y\<rangle> \<in> G\<times>G. f`\<langle>x,y\<rangle> = TheNeutralElement(G,f)}"

text\<open>We will use the miltiplicative notation for groups. The neutral
  element is denoted $1$.\<close>

locale group0 =
  fixes G 
  fixes P
  assumes groupAssum: "IsAgroup(G,P)"

  fixes neut ("\<one>")
  defines neut_def[simp]: "\<one> \<equiv> TheNeutralElement(G,P)"
  
  fixes groper (infixl "\<cdot>" 70)
  defines groper_def[simp]: "a \<cdot> b \<equiv> P`\<langle>a,b\<rangle>"
  
  fixes inv ("_\<inverse> " [90] 91)
  defines inv_def[simp]: "x\<inverse> \<equiv> GroupInv(G,P)`(x)"

text\<open>First we show a lemma that says that we can use theorems proven in
  the \<open>monoid0\<close> context (locale).\<close>

lemma (in group0) group0_2_L1: shows "monoid0(G,P)"
  using groupAssum IsAgroup_def monoid0_def by simp

sublocale group0 < monoid: monoid0 G P groper
  unfolding groper_def using group0_2_L1 by auto

text\<open>In some strange cases Isabelle has difficulties with applying
  the definition of a group. The next lemma defines a rule to be applied
  in such cases.\<close>

lemma definition_of_group: assumes "IsAmonoid(G,f)" 
  and "\<forall>g\<in>G. \<exists>b\<in>G. f`\<langle>g,b\<rangle> = TheNeutralElement(G,f)"
  shows "IsAgroup(G,f)" 
  using assms IsAgroup_def by simp

text\<open>A technical lemma that allows to use $1$ as the neutral element of 
  the group without referencing a list of lemmas and definitions.\<close>

lemma (in group0) group0_2_L2: 
  shows "\<one>\<in>G \<and> (\<forall>g\<in>G.(\<one>\<cdot>g = g \<and> g\<cdot>\<one> = g))"
  using group0_2_L1 monoid.unit_is_neutral by simp

text\<open>The group is closed under the group operation. Used all the time,
  useful to have handy.\<close>

lemma (in group0) group_op_closed: assumes "a\<in>G"  "b\<in>G"
  shows "a\<cdot>b \<in> G" using assms monoid.group0_1_L1 
  by simp

text\<open>The group operation is associative. This is another technical lemma 
  that allows to shorten the list of referenced lemmas in some proofs.\<close>

lemma (in group0) group_oper_assoc: 
  assumes "a\<in>G"  "b\<in>G"  "c\<in>G" shows "a\<cdot>(b\<cdot>c) = a\<cdot>b\<cdot>c"
  using groupAssum assms IsAgroup_def IsAmonoid_def 
    IsAssociative_def group_op_closed by simp

text\<open>The group operation maps $G\times G$ into $G$. It is conveniet to have
  this fact easily accessible in the \<open>group0\<close> context.\<close>

lemma (in group0) group_oper_fun: shows "P : G\<times>G\<rightarrow>G"
  using groupAssum IsAgroup_def IsAmonoid_def IsAssociative_def
  by simp
  
text\<open>The definition of a group requires the existence of the right inverse.
  We show that this is also the left inverse.\<close>

theorem (in group0) group0_2_T1: 
  assumes A1: "g\<in>G" and A2: "b\<in>G" and A3: "g\<cdot>b = \<one>"
  shows "b\<cdot>g = \<one>"
proof -
  from A2 groupAssum obtain c where I: "c \<in> G \<and> b\<cdot>c = \<one>" 
    using IsAgroup_def by auto
  then have "c\<in>G" by simp
  have "\<one>\<in>G" using group0_2_L2 by simp
  with A1 A2 I have "b\<cdot>g =  b\<cdot>(g\<cdot>(b\<cdot>c))"
    using group_op_closed group0_2_L2 group_oper_assoc 
    by simp
  also from  A1 A2 \<open>c\<in>G\<close> have "b\<cdot>(g\<cdot>(b\<cdot>c)) = b\<cdot>(g\<cdot>b\<cdot>c)"
    using group_oper_assoc by simp
  also from A3 A2 I have "b\<cdot>(g\<cdot>b\<cdot>c)= \<one>" using group0_2_L2 by simp
  finally show "b\<cdot>g = \<one>" by simp
qed

text\<open>For every element of a group there is only one inverse.\<close>

lemma (in group0) group0_2_L4: 
  assumes A1: "x\<in>G" shows "\<exists>!y. y\<in>G \<and> x\<cdot>y = \<one>"
proof
  from A1 groupAssum show "\<exists>y. y\<in>G \<and>  x\<cdot>y = \<one>" 
    using IsAgroup_def by auto
  fix y n
  assume A2: "y\<in>G \<and>  x\<cdot>y = \<one>" and A3:"n\<in>G \<and> x\<cdot>n = \<one>" show "y=n"
  proof -
    from A1 A2 have T1: "y\<cdot>x = \<one>"
      using group0_2_T1 by simp
    from A2 A3 have "y = y\<cdot>(x\<cdot>n)" 
      using group0_2_L2 by simp
    also from A1 A2 A3 have "\<dots> = (y\<cdot>x)\<cdot>n" 
      using group_oper_assoc by blast
    also from T1 A3 have "\<dots> = n" 
      using group0_2_L2 by simp
    finally show "y=n" by simp
  qed
qed

text\<open>The group inverse is a function that maps G into G.\<close>

theorem group0_2_T2: 
  assumes A1: "IsAgroup(G,f)" shows "GroupInv(G,f) : G\<rightarrow>G"
proof -
  have "GroupInv(G,f) \<subseteq> G\<times>G" using GroupInv_def by auto
  moreover from A1 have
    "\<forall>x\<in>G. \<exists>!y. y\<in>G \<and> \<langle>x,y\<rangle> \<in> GroupInv(G,f)"
    using group0_def group0.group0_2_L4 GroupInv_def by simp
  ultimately show ?thesis using func1_1_L11 by simp
qed

text\<open>We can think about the group inverse (the function) 
  as the inverse image of the neutral element. Recall that
  in Isabelle \<open>f-``(A)\<close> denotes the inverse image of
  the set $A$.\<close>

theorem (in group0) group0_2_T3: shows "P-``{\<one>} = GroupInv(G,P)"
proof -
  from groupAssum have "P : G\<times>G \<rightarrow> G" 
    using IsAgroup_def IsAmonoid_def IsAssociative_def 
    by simp
  then show "P-``{\<one>} = GroupInv(G,P)"
    using func1_1_L14 GroupInv_def by auto
qed

text\<open>The inverse is in the group.\<close>

lemma (in group0) inverse_in_group: assumes A1: "x\<in>G" shows "x\<inverse>\<in>G"
proof -
  from groupAssum have "GroupInv(G,P) : G\<rightarrow>G" using group0_2_T2 by simp
  with A1 show ?thesis using apply_type by simp
qed

text\<open>The notation for the inverse means what it is supposed to mean.\<close>

lemma (in group0) group0_2_L6: 
  assumes A1: "x\<in>G" shows "x\<cdot>x\<inverse> = \<one> \<and> x\<inverse>\<cdot>x = \<one>"
proof
  from groupAssum have "GroupInv(G,P) : G\<rightarrow>G" 
    using group0_2_T2 by simp 
  with A1 have "\<langle>x,x\<inverse>\<rangle> \<in>  GroupInv(G,P)" 
    using apply_Pair by simp
  then show "x\<cdot>x\<inverse> = \<one>" using GroupInv_def by simp
  with A1 show "x\<inverse>\<cdot>x = \<one>" using inverse_in_group group0_2_T1 
    by blast 
qed

text\<open>The next two lemmas state that unless we multiply by 
  the neutral element, the result is always 
  different than any of the operands.\<close>

lemma (in group0) group0_2_L7: 
  assumes A1: "a\<in>G" and A2: "b\<in>G" and A3: "a\<cdot>b = a"
  shows "b=\<one>"
proof -
  from A3 have "a\<inverse> \<cdot> (a\<cdot>b) = a\<inverse>\<cdot>a" by simp
  with A1 A2 show ?thesis using
    inverse_in_group group_oper_assoc group0_2_L6 group0_2_L2
    by simp
qed

text\<open>See the comment to \<open>group0_2_L7\<close>.\<close>

lemma (in group0) group0_2_L8: 
  assumes A1: "a\<in>G" and A2: "b\<in>G" and A3: "a\<cdot>b = b"
  shows "a=\<one>"
proof -
  from A3 have "(a\<cdot>b)\<cdot>b\<inverse>  = b\<cdot>b\<inverse>" by simp
  with A1 A2 have "a\<cdot>(b\<cdot>b\<inverse>)  = b\<cdot>b\<inverse>" using
    inverse_in_group group_oper_assoc by simp
  with A1 A2 show ?thesis 
    using group0_2_L6 group0_2_L2 by simp
qed

text\<open>The inverse of the neutral element is the neutral element.\<close>

lemma (in group0) group_inv_of_one: shows "\<one>\<inverse> = \<one>"
  using group0_2_L2 inverse_in_group group0_2_L6 group0_2_L7 by blast

text\<open>if $a^{-1} = 1$, then $a=1$.\<close>

lemma (in group0) group0_2_L8A:  
  assumes A1: "a\<in>G" and A2: "a\<inverse> = \<one>"
  shows "a = \<one>"
proof -
  from A1 have "a\<cdot>a\<inverse> = \<one>" using group0_2_L6 by simp
  with A1 A2 show "a = \<one>" using group0_2_L2 by simp
qed

text\<open>If $a$ is not a unit, then its inverse is not a unit either.\<close>

lemma (in group0) group0_2_L8B:
  assumes "a\<in>G" and "a \<noteq> \<one>"
  shows "a\<inverse> \<noteq> \<one>" using assms group0_2_L8A by auto

text\<open>If $a^{-1}$ is not a unit, then a is not a unit either.\<close>

lemma (in group0) group0_2_L8C:
  assumes "a\<in>G" and "a\<inverse> \<noteq> \<one>"
  shows "a\<noteq>\<one>"
  using assms group0_2_L8A group_inv_of_one by auto

text\<open>If a product of two elements of a group is equal to the neutral
element then they are inverses of each other.\<close>

lemma (in group0) group0_2_L9: 
  assumes A1: "a\<in>G" and A2: "b\<in>G" and A3: "a\<cdot>b = \<one>" 
  shows "a = b\<inverse>" and "b = a\<inverse>"
proof -
  from A3 have "a\<cdot>b\<cdot>b\<inverse> = \<one>\<cdot>b\<inverse>" by simp 
  with A1 A2 have "a\<cdot>(b\<cdot>b\<inverse>) = \<one>\<cdot>b\<inverse>" using
    inverse_in_group group_oper_assoc by simp
  with A1 A2 show "a = b\<inverse>" using
    group0_2_L6 inverse_in_group group0_2_L2 by simp
  from A3 have "a\<inverse>\<cdot>(a\<cdot>b) = a\<inverse>\<cdot>\<one>" by simp
  with A1 A2 show "b = a\<inverse>" using 
    inverse_in_group group_oper_assoc group0_2_L6 group0_2_L2
    by simp
qed

text\<open>It happens quite often that we know what is (have a meta-function for) 
  the right inverse in a group. The next lemma shows that the value 
  of the group inverse (function) is equal to the right inverse 
  (meta-function).\<close>

lemma (in group0) group0_2_L9A: 
  assumes A1: "\<forall>g\<in>G. b(g) \<in> G \<and> g\<cdot>b(g) = \<one>"
  shows "\<forall>g\<in>G. b(g) = g\<inverse>"
proof
  fix g assume "g\<in>G"
  moreover from A1 \<open>g\<in>G\<close> have "b(g) \<in> G" by simp
  moreover from A1 \<open>g\<in>G\<close> have "g\<cdot>b(g) = \<one>" by simp
  ultimately show "b(g) = g\<inverse>" by (rule group0_2_L9)
qed
 
text\<open>What is the inverse of a product?\<close>

lemma (in group0) group_inv_of_two:
  assumes A1: "a\<in>G" and A2: "b\<in>G" 
  shows " b\<inverse>\<cdot>a\<inverse> = (a\<cdot>b)\<inverse>"
proof -
  from A1 A2 have 
    "b\<inverse>\<in>G"  "a\<inverse>\<in>G"  "a\<cdot>b\<in>G"  "b\<inverse>\<cdot>a\<inverse> \<in> G"
    using inverse_in_group group_op_closed 
    by auto
  from A1 A2 \<open>b\<inverse>\<cdot>a\<inverse> \<in> G\<close>  have "a\<cdot>b\<cdot>(b\<inverse>\<cdot>a\<inverse>) = a\<cdot>(b\<cdot>(b\<inverse>\<cdot>a\<inverse>))"
    using group_oper_assoc by simp
  moreover from A2 \<open>b\<inverse>\<in>G\<close> \<open>a\<inverse>\<in>G\<close> have "b\<cdot>(b\<inverse>\<cdot>a\<inverse>) = b\<cdot>b\<inverse>\<cdot>a\<inverse>"
    using group_oper_assoc by simp
  moreover from A2 \<open>a\<inverse>\<in>G\<close> have "b\<cdot>b\<inverse>\<cdot>a\<inverse> = a\<inverse>"
     using group0_2_L6 group0_2_L2 by simp
  ultimately have "a\<cdot>b\<cdot>(b\<inverse>\<cdot>a\<inverse>) = a\<cdot>a\<inverse>"
    by simp
  with A1 have "a\<cdot>b\<cdot>(b\<inverse>\<cdot>a\<inverse>) = \<one>"
    using group0_2_L6 by simp
  with \<open>a\<cdot>b \<in> G\<close>  \<open>b\<inverse>\<cdot>a\<inverse> \<in> G\<close> show "b\<inverse>\<cdot>a\<inverse> = (a\<cdot>b)\<inverse>"
    using group0_2_L9 by simp
qed

text\<open>What is the inverse of a product of three elements?\<close>

lemma (in group0) group_inv_of_three:
  assumes A1: "a\<in>G"  "b\<in>G"  "c\<in>G"
  shows
  "(a\<cdot>b\<cdot>c)\<inverse> = c\<inverse>\<cdot>(a\<cdot>b)\<inverse>"
  "(a\<cdot>b\<cdot>c)\<inverse> = c\<inverse>\<cdot>(b\<inverse>\<cdot>a\<inverse>)"
  "(a\<cdot>b\<cdot>c)\<inverse> = c\<inverse>\<cdot>b\<inverse>\<cdot>a\<inverse>"
proof -
  from A1 have T: 
    "a\<cdot>b \<in> G"  "a\<inverse> \<in> G"  "b\<inverse> \<in> G"   "c\<inverse> \<in> G"  
    using group_op_closed inverse_in_group by auto
  with A1 show 
    "(a\<cdot>b\<cdot>c)\<inverse> = c\<inverse>\<cdot>(a\<cdot>b)\<inverse>" and "(a\<cdot>b\<cdot>c)\<inverse> = c\<inverse>\<cdot>(b\<inverse>\<cdot>a\<inverse>)"
     using group_inv_of_two by auto
   with T show "(a\<cdot>b\<cdot>c)\<inverse> = c\<inverse>\<cdot>b\<inverse>\<cdot>a\<inverse>" using group_oper_assoc
     by simp
qed

text\<open>The inverse of the inverse is the element.\<close>

lemma (in group0) group_inv_of_inv:
  assumes "a\<in>G" shows "a = (a\<inverse>)\<inverse>"
  using assms inverse_in_group group0_2_L6 group0_2_L9 
  by simp

text\<open>Group inverse is nilpotent, therefore a bijection and involution.\<close>

lemma (in group0) group_inv_bij: 
  shows "GroupInv(G,P) O GroupInv(G,P) = id(G)" and "GroupInv(G,P) \<in> bij(G,G)" and
  "GroupInv(G,P) = converse(GroupInv(G,P))"
proof -
  have I: "GroupInv(G,P): G\<rightarrow>G" using groupAssum group0_2_T2 by simp
  then have "GroupInv(G,P) O GroupInv(G,P): G\<rightarrow>G" and "id(G):G\<rightarrow>G"
    using comp_fun id_type by auto
  moreover 
  { fix g assume "g\<in>G"
    with I have "(GroupInv(G,P) O GroupInv(G,P))`(g) = id(G)`(g)"
      using comp_fun_apply group_inv_of_inv id_conv by simp
  } hence "\<forall>g\<in>G. (GroupInv(G,P) O GroupInv(G,P))`(g) = id(G)`(g)" by simp
  ultimately show "GroupInv(G,P) O GroupInv(G,P) = id(G)"
    by (rule func_eq)
  with I show "GroupInv(G,P) \<in> bij(G,G)" using nilpotent_imp_bijective
    by simp
  with \<open>GroupInv(G,P) O GroupInv(G,P) = id(G)\<close> show
    "GroupInv(G,P) = converse(GroupInv(G,P))" using comp_id_conv by simp
qed

text\<open>A set comprehension form of the image of a set under the group inverse. \<close>

lemma (in group0) ginv_image: assumes "V\<subseteq>G" 
  shows "GroupInv(G,P)``(V) \<subseteq> G" and "GroupInv(G,P)``(V) = {g\<inverse>. g \<in> V}"  
proof -
  from assms have I: "GroupInv(G,P)``(V) = {GroupInv(G,P)`(g). g\<in>V}" 
    using groupAssum group0_2_T2 func_imagedef by blast 
  thus "GroupInv(G,P)``(V) = {g\<inverse>. g \<in> V}"  by simp
  show "GroupInv(G,P)``(V) \<subseteq> G" using groupAssum group0_2_T2 func1_1_L6(2) by blast
qed

text\<open>Inverse of an element that belongs to the inverse of the set belongs to the set. \<close>

lemma (in group0) ginv_image_el: assumes "V\<subseteq>G" "g \<in> GroupInv(G,P)``(V)"
  shows "g\<inverse> \<in> V"
  using assms ginv_image group_inv_of_inv by auto 

text\<open>For the group inverse the image is the same as inverse image.\<close>

lemma (in group0) inv_image_vimage: shows "GroupInv(G,P)``(V) = GroupInv(G,P)-``(V)"
  using group_inv_bij vimage_converse by simp

text\<open>If the unit is in a set then it is in the inverse of that set.\<close>

lemma (in group0) neut_inv_neut: assumes "A\<subseteq>G" and "\<one>\<in>A"
  shows "\<one> \<in> GroupInv(G,P)``(A)"
proof -
  have "GroupInv(G,P):G\<rightarrow>G" using groupAssum group0_2_T2 by simp
  with assms have "\<one>\<inverse> \<in> GroupInv(G,P)``(A)" using func_imagedef by auto
  then show ?thesis using group_inv_of_one by simp
qed

text\<open>The group inverse is onto.\<close>

lemma (in group0) group_inv_surj: shows "GroupInv(G,P)``(G) = G"
  using group_inv_bij bij_def surj_range_image_domain by auto

text\<open>If $a^{-1}\cdot b=1$, then $a=b$.\<close>

lemma (in group0) group0_2_L11:
  assumes A1: "a\<in>G"  "b\<in>G" and A2: "a\<inverse>\<cdot>b = \<one>"
  shows "a=b"
proof -
  from A1 A2 have "a\<inverse> \<in> G"  "b\<in>G"  "a\<inverse>\<cdot>b = \<one>" 
    using inverse_in_group by auto
  then have "b = (a\<inverse>)\<inverse>" by (rule group0_2_L9)
  with A1 show "a=b" using group_inv_of_inv by simp
qed

text\<open>If $a\cdot b^{-1}=1$, then $a=b$.\<close>

lemma (in group0) group0_2_L11A: 
  assumes A1: "a\<in>G"  "b\<in>G" and A2: "a\<cdot>b\<inverse> = \<one>"
  shows "a=b"
proof -
  from A1 A2 have "a \<in> G"  "b\<inverse>\<in>G"  "a\<cdot>b\<inverse> = \<one>"
    using inverse_in_group by auto
  then have "a = (b\<inverse>)\<inverse>" by (rule group0_2_L9)
  with A1 show "a=b" using group_inv_of_inv by simp
qed

text\<open>If if the inverse of $b$ is different than $a$, then the
  inverse of $a$ is different than $b$.\<close>

lemma (in group0) group0_2_L11B:
  assumes A1: "a\<in>G" and A2: "b\<inverse> \<noteq> a"
  shows "a\<inverse> \<noteq> b"
proof -
  { assume "a\<inverse> = b"
    then have "(a\<inverse>)\<inverse> = b\<inverse>" by simp
    with A1 A2 have False using group_inv_of_inv
      by simp
  } then show "a\<inverse> \<noteq> b" by auto
qed

text\<open>What is the inverse of $ab^{-1}$ ?\<close>

lemma (in group0) group0_2_L12:
  assumes A1: "a\<in>G"  "b\<in>G" 
  shows 
  "(a\<cdot>b\<inverse>)\<inverse> = b\<cdot>a\<inverse>"
  "(a\<inverse>\<cdot>b)\<inverse> = b\<inverse>\<cdot>a"
proof -
  from A1 have 
    "(a\<cdot>b\<inverse>)\<inverse> = (b\<inverse>)\<inverse>\<cdot> a\<inverse>" and "(a\<inverse>\<cdot>b)\<inverse> = b\<inverse>\<cdot>(a\<inverse>)\<inverse>"
    using inverse_in_group group_inv_of_two by auto
  with A1 show  "(a\<cdot>b\<inverse>)\<inverse> = b\<cdot>a\<inverse>"  "(a\<inverse>\<cdot>b)\<inverse> = b\<inverse>\<cdot>a"
    using group_inv_of_inv by auto
qed

text\<open>A couple useful rearrangements with three elements: 
  we can insert a $b\cdot b^{-1}$ 
  between two group elements (another version) and one about a product of 
  an element and inverse of a product, and two others.\<close>

lemma (in group0) group0_2_L14A:
  assumes A1: "a\<in>G"  "b\<in>G"  "c\<in>G"
  shows 
  "a\<cdot>c\<inverse>= (a\<cdot>b\<inverse>)\<cdot>(b\<cdot>c\<inverse>)"
  "a\<inverse>\<cdot>c = (a\<inverse>\<cdot>b)\<cdot>(b\<inverse>\<cdot>c)"
  "a\<cdot>(b\<cdot>c)\<inverse> = a\<cdot>c\<inverse>\<cdot>b\<inverse>"
  "a\<cdot>(b\<cdot>c\<inverse>) = a\<cdot>b\<cdot>c\<inverse>"
  "(a\<cdot>b\<inverse>\<cdot>c\<inverse>)\<inverse> = c\<cdot>b\<cdot>a\<inverse>"
  "a\<cdot>b\<cdot>c\<inverse>\<cdot>(c\<cdot>b\<inverse>) = a"
  "a\<cdot>(b\<cdot>c)\<cdot>c\<inverse> = a\<cdot>b"
proof -
  from A1 have T: 
    "a\<inverse> \<in> G"  "b\<inverse>\<in>G"  "c\<inverse>\<in>G"  
    "a\<inverse>\<cdot>b \<in> G"  "a\<cdot>b\<inverse> \<in> G"  "a\<cdot>b \<in> G"  
    "c\<cdot>b\<inverse> \<in> G"  "b\<cdot>c \<in> G"
    using inverse_in_group group_op_closed
    by auto
   from A1 T have 
     "a\<cdot>c\<inverse> =  a\<cdot>(b\<inverse>\<cdot>b)\<cdot>c\<inverse>"
     "a\<inverse>\<cdot>c =  a\<inverse>\<cdot>(b\<cdot>b\<inverse>)\<cdot>c"
    using group0_2_L2 group0_2_L6 by auto
   with A1 T show 
     "a\<cdot>c\<inverse>= (a\<cdot>b\<inverse>)\<cdot>(b\<cdot>c\<inverse>)"
     "a\<inverse>\<cdot>c = (a\<inverse>\<cdot>b)\<cdot>(b\<inverse>\<cdot>c)"
     using group_oper_assoc by auto
  from A1 have "a\<cdot>(b\<cdot>c)\<inverse> = a\<cdot>(c\<inverse>\<cdot>b\<inverse>)"
    using group_inv_of_two by simp
  with A1 T show "a\<cdot>(b\<cdot>c)\<inverse> =a\<cdot>c\<inverse>\<cdot>b\<inverse>" 
    using group_oper_assoc by simp
  from A1 T show "a\<cdot>(b\<cdot>c\<inverse>) = a\<cdot>b\<cdot>c\<inverse>"
    using group_oper_assoc by simp
  from A1 T show  "(a\<cdot>b\<inverse>\<cdot>c\<inverse>)\<inverse> = c\<cdot>b\<cdot>a\<inverse>"
    using group_inv_of_three  group_inv_of_inv
    by simp
  from T have "a\<cdot>b\<cdot>c\<inverse>\<cdot>(c\<cdot>b\<inverse>) = a\<cdot>b\<cdot>(c\<inverse>\<cdot>(c\<cdot>b\<inverse>))"
    using group_oper_assoc by simp
  also from A1 T have "\<dots> =  a\<cdot>b\<cdot>b\<inverse>"
    using group_oper_assoc group0_2_L6 group0_2_L2
    by simp
  also from A1 T have "\<dots> = a\<cdot>(b\<cdot>b\<inverse>)"
    using group_oper_assoc by simp
  also from A1 have "\<dots> = a"
    using group0_2_L6 group0_2_L2 by simp
  finally show "a\<cdot>b\<cdot>c\<inverse>\<cdot>(c\<cdot>b\<inverse>) = a" by simp
  from A1 T have "a\<cdot>(b\<cdot>c)\<cdot>c\<inverse> =  a\<cdot>(b\<cdot>(c\<cdot>c\<inverse>))"
    using group_oper_assoc by simp
  also from A1 T have "\<dots> = a\<cdot>b"
    using  group0_2_L6 group0_2_L2 by simp
  finally show "a\<cdot>(b\<cdot>c)\<cdot>c\<inverse> = a\<cdot>b"
    by simp
qed

text\<open> A simple equation to solve \<close>

lemma (in group0) simple_equation0: 
  assumes "a\<in>G"  "b\<in>G" "c\<in>G" "a\<cdot>b\<inverse> = c\<inverse>"
  shows "c = b\<cdot>a\<inverse>" 
proof - 
  from assms(4) have "(a\<cdot>b\<inverse>)\<inverse> = (c\<inverse>)\<inverse>" by simp
  with assms(1,2,3) show "c = b\<cdot>a\<inverse>" using group0_2_L12(1) group_inv_of_inv by simp
qed

text\<open> Another simple equation \<close>

lemma (in group0) simple_equation1: 
  assumes "a\<in>G"  "b\<in>G" "c\<in>G" "a\<inverse>\<cdot>b = c\<inverse>"
  shows "c = b\<inverse>\<cdot>a" 
proof - 
  from assms(4) have "(a\<inverse>\<cdot>b)\<inverse> = (c\<inverse>)\<inverse>" by simp
  with assms(1,2,3) show "c = b\<inverse>\<cdot>a" using group0_2_L12(2) group_inv_of_inv by simp
qed
     
text\<open>Another lemma about rearranging a product of four group
  elements.\<close>

lemma (in group0) group0_2_L15:
  assumes A1: "a\<in>G"  "b\<in>G"  "c\<in>G"  "d\<in>G"
  shows "(a\<cdot>b)\<cdot>(c\<cdot>d)\<inverse> = a\<cdot>(b\<cdot>d\<inverse>)\<cdot>a\<inverse>\<cdot>(a\<cdot>c\<inverse>)"
proof -
  from A1 have T1:
    "d\<inverse>\<in>G"  "c\<inverse>\<in>G" "a\<cdot>b\<in>G" "a\<cdot>(b\<cdot>d\<inverse>)\<in>G"
    using inverse_in_group group_op_closed
    by auto
  with A1 have "(a\<cdot>b)\<cdot>(c\<cdot>d)\<inverse> = (a\<cdot>b)\<cdot>(d\<inverse>\<cdot>c\<inverse>)"
    using group_inv_of_two by simp
  also from A1 T1 have "\<dots> = a\<cdot>(b\<cdot>d\<inverse>)\<cdot>c\<inverse>"
    using group_oper_assoc by simp
  also from A1 T1 have "\<dots> = a\<cdot>(b\<cdot>d\<inverse>)\<cdot>a\<inverse>\<cdot>(a\<cdot>c\<inverse>)"
    using group0_2_L14A by blast
  finally show ?thesis by simp
qed

text\<open>We can cancel an element with its inverse that is written next to it.\<close>

lemma (in group0) inv_cancel_two:
  assumes A1: "a\<in>G"  "b\<in>G"
  shows 
  "a\<cdot>b\<inverse>\<cdot>b = a"  
  "a\<cdot>b\<cdot>b\<inverse> = a"
  "a\<inverse>\<cdot>(a\<cdot>b) = b"
  "a\<cdot>(a\<inverse>\<cdot>b) = b"
proof -
  from A1 have 
    "a\<cdot>b\<inverse>\<cdot>b = a\<cdot>(b\<inverse>\<cdot>b)"   "a\<cdot>b\<cdot>b\<inverse> = a\<cdot>(b\<cdot>b\<inverse>)"
    "a\<inverse>\<cdot>(a\<cdot>b) = a\<inverse>\<cdot>a\<cdot>b"   "a\<cdot>(a\<inverse>\<cdot>b) = a\<cdot>a\<inverse>\<cdot>b"
    using inverse_in_group group_oper_assoc by auto
  with A1 show
    "a\<cdot>b\<inverse>\<cdot>b = a"
    "a\<cdot>b\<cdot>b\<inverse> = a"
    "a\<inverse>\<cdot>(a\<cdot>b) = b"
    "a\<cdot>(a\<inverse>\<cdot>b) = b"
    using group0_2_L6 group0_2_L2 by auto
qed

text\<open>Another lemma about cancelling with two group elements.\<close>

lemma (in group0) group0_2_L16A:
  assumes A1: "a\<in>G"  "b\<in>G"
  shows "a\<cdot>(b\<cdot>a)\<inverse> = b\<inverse>"
proof -
  from A1 have "(b\<cdot>a)\<inverse> = a\<inverse>\<cdot>b\<inverse>"  "b\<inverse> \<in> G"
    using group_inv_of_two inverse_in_group by auto
  with A1 show "a\<cdot>(b\<cdot>a)\<inverse> = b\<inverse>" using inv_cancel_two
    by simp
qed

text\<open> Some other identities with three element and cancelling. \<close>

lemma (in group0) cancel_middle:
  assumes "a\<in>G"  "b\<in>G" "c\<in>G"
  shows 
    "(a\<cdot>b)\<inverse>\<cdot>(a\<cdot>c) = b\<inverse>\<cdot>c"
    "(a\<cdot>b)\<cdot>(c\<cdot>b)\<inverse> = a\<cdot>c\<inverse>"
    "a\<inverse>\<cdot>(a\<cdot>b\<cdot>c)\<cdot>c\<inverse> = b"
    "a\<cdot>(b\<cdot>c\<inverse>)\<cdot>c = a\<cdot>b"
    "a\<cdot>b\<inverse>\<cdot>(b\<cdot>c\<inverse>) = a\<cdot>c\<inverse>"
proof -
  from assms have "(a\<cdot>b)\<inverse>\<cdot>(a\<cdot>c) = b\<inverse>\<cdot>(a\<inverse>\<cdot>(a\<cdot>c))"
    using group_inv_of_two inverse_in_group group_oper_assoc group_op_closed by auto
  with assms(1,3) show "(a\<cdot>b)\<inverse>\<cdot>(a\<cdot>c) = b\<inverse>\<cdot>c" using inv_cancel_two(3) by simp
  from assms have "(a\<cdot>b)\<cdot>(c\<cdot>b)\<inverse> = a\<cdot>(b\<cdot>(b\<inverse>\<cdot>c\<inverse>))"
    using group_inv_of_two inverse_in_group group_oper_assoc group_op_closed by auto
  with assms show "(a\<cdot>b)\<cdot>(c\<cdot>b)\<inverse> =a\<cdot>c\<inverse>" using inverse_in_group inv_cancel_two(4) by simp
  from assms have "a\<inverse>\<cdot>(a\<cdot>b\<cdot>c)\<cdot>c\<inverse> = (a\<inverse>\<cdot>a)\<cdot>b\<cdot>(c\<cdot>c\<inverse>)" 
    using inverse_in_group group_oper_assoc group_op_closed by auto
  with assms show "a\<inverse>\<cdot>(a\<cdot>b\<cdot>c)\<cdot>c\<inverse> = b" using group0_2_L6 group0_2_L2 by simp
  from assms have "a\<cdot>(b\<cdot>c\<inverse>)\<cdot>c = a\<cdot>b\<cdot>(c\<inverse>\<cdot>c)" using inverse_in_group group_oper_assoc group_op_closed
    by simp
  with assms show "a\<cdot>(b\<cdot>c\<inverse>)\<cdot>c = a\<cdot>b" using group_op_closed group0_2_L6 group0_2_L2 by simp
  from assms have "a\<cdot>b\<inverse>\<cdot>(b\<cdot>c\<inverse>) = a\<cdot>(b\<inverse>\<cdot>b)\<cdot>c\<inverse>" using inverse_in_group group_oper_assoc group_op_closed
    by simp
  with assms  show "a\<cdot>b\<inverse>\<cdot>(b\<cdot>c\<inverse>) = a\<cdot>c\<inverse>" using group0_2_L6 group0_2_L2 by simp
qed

text\<open>Adding a neutral element to a set that is 
  closed under the group operation results in a set that is closed under the 
  group operation.\<close>

lemma (in group0) group0_2_L17: 
  assumes "H\<subseteq>G"
  and "H {is closed under} P"
  shows "(H \<union> {\<one>}) {is closed under} P"
  using assms IsOpClosed_def group0_2_L2 by auto

text\<open>We can put an element on the other side of an equation.\<close>

lemma (in group0) group0_2_L18:
  assumes A1: "a\<in>G"  "b\<in>G"
  and A2: "c = a\<cdot>b"
  shows "c\<cdot>b\<inverse> = a"  "a\<inverse>\<cdot>c = b" 
proof-
  from A2 A1 have "c\<cdot>b\<inverse> =  a\<cdot>(b\<cdot>b\<inverse>)"  "a\<inverse>\<cdot>c = (a\<inverse>\<cdot>a)\<cdot>b"
    using inverse_in_group group_oper_assoc by auto
  moreover from A1 have "a\<cdot>(b\<cdot>b\<inverse>) = a"  "(a\<inverse>\<cdot>a)\<cdot>b = b"
    using group0_2_L6 group0_2_L2 by auto
  ultimately show "c\<cdot>b\<inverse> = a"  "a\<inverse>\<cdot>c = b" 
    by auto
qed

text\<open> We can cancel an element on the right from both sides of an equation. \<close>

lemma (in group0) cancel_right: assumes "a\<in>G"  "b\<in>G"  "c\<in>G" "a\<cdot>b = c\<cdot>b"
  shows "a = c" 
proof -
  from assms(4) have "a\<cdot>b\<cdot>b\<inverse> = c\<cdot>b\<cdot>b\<inverse>" by simp
  with assms(1,2,3) show ?thesis using inv_cancel_two(2) by simp
qed

text\<open> We can cancel an element on the left from both sides of an equation. \<close>

lemma (in group0) cancel_left: assumes "a\<in>G"  "b\<in>G"  "c\<in>G" "a\<cdot>b = a\<cdot>c"
  shows "b=c"
proof -
  from assms(4) have "a\<inverse>\<cdot>(a\<cdot>b) = a\<inverse>\<cdot>(a\<cdot>c)" by simp
  with assms(1,2,3) show ?thesis using inv_cancel_two(3) by simp
qed

text\<open>Multiplying different group elements by the same factor results
  in different group elements.\<close>

lemma (in group0) group0_2_L19: 
  assumes A1: "a\<in>G"  "b\<in>G"  "c\<in>G" and A2: "a\<noteq>b"
  shows "a\<cdot>c \<noteq> b\<cdot>c" and "c\<cdot>a \<noteq> c\<cdot>b"
proof -
  { assume "a\<cdot>c = b\<cdot>c \<or> c\<cdot>a =c\<cdot>b"
    then have "a\<cdot>c\<cdot>c\<inverse> = b\<cdot>c\<cdot>c\<inverse> \<or> c\<inverse>\<cdot>(c\<cdot>a) = c\<inverse>\<cdot>(c\<cdot>b)"
      by auto
    with A1 A2 have False using inv_cancel_two by simp
  } then show "a\<cdot>c \<noteq> b\<cdot>c" and "c\<cdot>a \<noteq> c\<cdot>b" by auto
qed

subsection\<open>Subgroups\<close>

text\<open>There are two common ways to define subgroups. One requires that the
  group operation is closed in the subgroup. The second one defines subgroup 
  as a subset of a group which is itself a group under the group operations.
  We use the second approach because it results in shorter definition. 
  
  The rest of this section is devoted to proving the equivalence of these two
  definitions of the notion of a subgroup. 
\<close>

text\<open>A pair $(H,P)$ is a subgroup if $H$ forms a group with the 
  operation $P$ restricted to $H\times H$. It may be surprising that 
  we don't require $H$ to be a subset of $G$. This however can be inferred
  from the definition if the pair $(G,P)$ is a group, 
  see lemma \<open>group0_3_L2\<close>.\<close>

definition
  "IsAsubgroup(H,P) \<equiv> IsAgroup(H, restrict(P,H\<times>H))"

text\<open>Formally the group operation in a subgroup is different than in the
  group as they have different domains. Of course we want to use the original 
  operation with the associated notation in the subgroup. The next couple of 
  lemmas will allow for that. 

  The next lemma states that the neutral element of 
  a subgroup is in the subgroup and it is 
  both right and left neutral there. The notation is very ugly because
  we don't want to introduce a separate notation for the subgroup operation.
\<close>

lemma group0_3_L1: 
  assumes A1: "IsAsubgroup(H,f)"
  and A2: "n = TheNeutralElement(H,restrict(f,H\<times>H))"
  shows "n \<in> H"
  "\<forall>h\<in>H. restrict(f,H\<times>H)`\<langle>n,h \<rangle> = h"
  "\<forall>h\<in>H. restrict(f,H\<times>H)`\<langle>h,n\<rangle> = h"
proof -
  let ?b = "restrict(f,H\<times>H)"
  let ?e = "TheNeutralElement(H,restrict(f,H\<times>H))"
  from A1 have "group0(H,?b)"
    using IsAsubgroup_def group0_def by simp
  then have I:
    "?e \<in> H \<and> (\<forall>h\<in>H. (?b`\<langle>?e,h \<rangle> = h \<and> ?b`\<langle>h,?e\<rangle> = h))"
    by (rule group0.group0_2_L2)
  with A2 show "n \<in> H" by simp
  from A2 I show "\<forall>h\<in>H. ?b`\<langle>n,h\<rangle> = h" and "\<forall>h\<in>H. ?b`\<langle>h,n\<rangle> = h"
    by auto
qed

text\<open>A subgroup is contained in the group.\<close>

lemma (in group0) group0_3_L2: 
  assumes A1: "IsAsubgroup(H,P)"
  shows "H \<subseteq> G"
proof
  fix h assume "h\<in>H"
  let ?b = "restrict(P,H\<times>H)"
  let ?n = "TheNeutralElement(H,restrict(P,H\<times>H))"
   from A1 have "?b \<in> H\<times>H\<rightarrow>H" 
    using IsAsubgroup_def IsAgroup_def 
      IsAmonoid_def IsAssociative_def by simp
  moreover from A1 \<open>h\<in>H\<close> have "\<langle> ?n,h\<rangle> \<in> H\<times>H" 
    using group0_3_L1 by simp
  moreover from A1 \<open>h\<in>H\<close> have "h = ?b`\<langle>?n,h \<rangle>" 
    using group0_3_L1 by simp
  ultimately have "\<langle>\<langle>?n,h\<rangle>,h\<rangle> \<in> ?b" 
    using func1_1_L5A by blast
  then have "\<langle>\<langle>?n,h\<rangle>,h\<rangle> \<in> P" using restrict_subset by auto
  moreover from groupAssum have "P:G\<times>G\<rightarrow>G"
    using IsAgroup_def IsAmonoid_def IsAssociative_def 
    by simp
  ultimately show "h\<in>G" using func1_1_L5 
    by blast
qed

text\<open>The group's neutral element (denoted $1$ in the group0 context)
  is a neutral element for the subgroup with respect to the group action.\<close>

lemma (in group0) group0_3_L3:
  assumes "IsAsubgroup(H,P)"
  shows "\<forall>h\<in>H. \<one>\<cdot>h = h \<and> h\<cdot>\<one> = h"
  using assms groupAssum group0_3_L2 group0_2_L2
  by auto

text\<open>The neutral element of a subgroup is the same as that of the group.\<close>

lemma (in group0) group0_3_L4: assumes A1: "IsAsubgroup(H,P)"
  shows "TheNeutralElement(H,restrict(P,H\<times>H)) = \<one>"
proof -
  let ?n = "TheNeutralElement(H,restrict(P,H\<times>H))"
  from A1 have "?n \<in> H" using group0_3_L1 by simp
  with groupAssum A1 have "?n\<in>G" using  group0_3_L2 by auto
  with A1 \<open>?n \<in> H\<close> show ?thesis using 
     group0_3_L1 restrict_if group0_2_L7 by simp
qed

text\<open>The neutral element of the group (denoted $1$ in the group0 context)
  belongs to every subgroup.\<close>

lemma (in group0) group0_3_L5: assumes A1: "IsAsubgroup(H,P)"
  shows "\<one> \<in> H"
proof -
  from A1 show "\<one>\<in>H" using group0_3_L1 group0_3_L4 
    by fast
qed

text\<open>Subgroups are closed with respect to the group operation.\<close>

lemma (in group0) group0_3_L6: assumes A1: "IsAsubgroup(H,P)"
  and A2: "a\<in>H" "b\<in>H"
  shows "a\<cdot>b \<in> H"
proof - 
  let ?f = "restrict(P,H\<times>H)"
  from A1 have "monoid0(H,?f)" using
    IsAsubgroup_def IsAgroup_def monoid0_def by simp
  with A2 have "?f` (\<langle>a,b\<rangle>) \<in> H" using monoid0.group0_1_L1
    by blast
 with A2 show "a\<cdot>b \<in> H" using restrict_if by simp
qed

text\<open>A preliminary lemma that we need to show that taking the inverse 
  in the subgroup is the same as taking the inverse
  in the group.\<close>

lemma group0_3_L7A: 
  assumes A1: "IsAgroup(G,f)" 
  and A2: "IsAsubgroup(H,f)" and A3: "g = restrict(f,H\<times>H)"
  shows "GroupInv(G,f) \<inter> H\<times>H = GroupInv(H,g)"
proof -
  let ?e = "TheNeutralElement(G,f)"
  let ?e\<^sub>1 = "TheNeutralElement(H,g)"
  from A1 have "group0(G,f)" using group0_def by simp
  from A2 A3 have "group0(H,g)" 
    using IsAsubgroup_def group0_def by simp
  from \<open>group0(G,f)\<close> A2 A3  have "GroupInv(G,f) = f-``{?e\<^sub>1}" 
    using group0.group0_3_L4 group0.group0_2_T3
    by simp
  moreover have "g-``{?e\<^sub>1} = f-``{?e\<^sub>1} \<inter> H\<times>H"
  proof -
    from A1 have "f \<in> G\<times>G\<rightarrow>G" 
      using IsAgroup_def IsAmonoid_def IsAssociative_def 
      by simp
    moreover from A2 \<open>group0(G,f)\<close> have "H\<times>H \<subseteq> G\<times>G" 
      using group0.group0_3_L2 by auto
    ultimately show "g-``{?e\<^sub>1} = f-``{?e\<^sub>1} \<inter> H\<times>H"
      using A3 func1_2_L1 by simp
  qed
  moreover from A3 \<open>group0(H,g)\<close> have "GroupInv(H,g) = g-``{?e\<^sub>1}" 
    using group0.group0_2_T3 by simp
  ultimately show ?thesis by simp
qed

text\<open>Using the lemma above we can show the actual statement: 
  taking the inverse in the subgroup is the same as taking the inverse
  in the group.\<close>

theorem (in group0) group0_3_T1:
  assumes A1: "IsAsubgroup(H,P)" 
  and A2: "g = restrict(P,H\<times>H)"
  shows "GroupInv(H,g) = restrict(GroupInv(G,P),H)"
proof -
  from groupAssum have "GroupInv(G,P) : G\<rightarrow>G" 
    using group0_2_T2 by simp
  moreover from A1 A2 have "GroupInv(H,g) : H\<rightarrow>H"
    using IsAsubgroup_def group0_2_T2 by simp
  moreover from A1 have "H \<subseteq> G" 
    using group0_3_L2 by simp
  moreover from groupAssum A1 A2 have 
    "GroupInv(G,P) \<inter> H\<times>H = GroupInv(H,g)"
    using group0_3_L7A by simp
  ultimately show ?thesis
    using func1_2_L3 by simp
qed

text\<open>A sligtly weaker, but more convenient in applications,
  reformulation of the above theorem.\<close>

theorem (in group0) group0_3_T2: 
  assumes "IsAsubgroup(H,P)" 
  and "g = restrict(P,H\<times>H)"
  shows "\<forall>h\<in>H. GroupInv(H,g)`(h) = h\<inverse>"
  using assms group0_3_T1 restrict_if by simp

text\<open>Subgroups are closed with respect to taking the group inverse.\<close>

theorem (in group0) group0_3_T3A: 
  assumes A1: "IsAsubgroup(H,P)" and A2: "h\<in>H"
  shows "h\<inverse>\<in> H"
proof -
  let ?g = "restrict(P,H\<times>H)"
  from A1 have  "GroupInv(H,?g) \<in> H\<rightarrow>H"
    using IsAsubgroup_def group0_2_T2 by simp
  with A2 have "GroupInv(H,?g)`(h) \<in> H"
    using apply_type by simp
  with A1 A2 show "h\<inverse>\<in> H" using group0_3_T2 by simp
qed

text\<open>The next theorem states that a nonempty subset of 
  a group $G$ that is closed under the group operation and 
  taking the inverse is a subgroup of the group.\<close>

theorem (in group0) group0_3_T3:
  assumes A1: "H\<noteq>0"
  and A2: "H\<subseteq>G"
  and A3: "H {is closed under} P"
  and A4: "\<forall>x\<in>H. x\<inverse> \<in> H"
  shows "IsAsubgroup(H,P)"
proof -
  let ?g = "restrict(P,H\<times>H)"
  let ?n = "TheNeutralElement(H,?g)"
  from A3 have I: "\<forall>x\<in>H.\<forall>y\<in>H. x\<cdot>y \<in> H"
    using IsOpClosed_def by simp
  from A1 obtain x where "x\<in>H" by auto
  with A4 I A2 have "\<one>\<in>H"
    using group0_2_L6 by blast
  with A3 A2 have T2: "IsAmonoid(H,?g)"
    using monoid.group0_1_T1
    by simp
  moreover have "\<forall>h\<in>H.\<exists>b\<in>H. ?g`\<langle>h,b\<rangle> = ?n"
  proof
    fix h assume "h\<in>H"
    with A4 A2 have "h\<cdot>h\<inverse> = \<one>"
      using group0_2_L6 by auto
    moreover from groupAssum A2 A3 \<open>\<one>\<in>H\<close> have "\<one> = ?n"
      using IsAgroup_def group0_1_L6 by auto
    moreover from A4 \<open>h\<in>H\<close> have "?g`\<langle>h,h\<inverse>\<rangle> = h\<cdot>h\<inverse>"
      using restrict_if by simp
    ultimately have "?g`\<langle>h,h\<inverse>\<rangle> = ?n" by simp
    with A4 \<open>h\<in>H\<close> show "\<exists>b\<in>H. ?g`\<langle>h,b\<rangle> = ?n" by auto
  qed
  ultimately show "IsAsubgroup(H,P)" using 
    IsAsubgroup_def IsAgroup_def by simp
qed

corollary (in group0) group0_3_T4:
  shows "IsAsubgroup({\<one>},P)"
proof (rule group0_3_T3)
  show "{\<one>} \<noteq> 0" by simp
  show "{\<one>} \<subseteq> G" using group0_2_L2 by auto
  show "\<forall>x\<in>{\<one>}. x\<inverse>  \<in> {\<one>}" using group_inv_of_one by auto
  show "{\<one>} {is closed under} P" unfolding IsOpClosed_def
    using group0_2_L2 by auto
qed

text\<open>Intersection of subgroups is a subgroup. This lemma is obsolete and should be replaced by 
  \<open>subgroup_inter\<close>. \<close>

lemma group0_3_L7:
  assumes A1: "IsAgroup(G,f)"
  and A2: "IsAsubgroup(H\<^sub>1,f)"
  and A3: "IsAsubgroup(H\<^sub>2,f)"
  shows "IsAsubgroup(H\<^sub>1\<inter>H\<^sub>2,restrict(f,H\<^sub>1\<times>H\<^sub>1))"
proof -
  let ?e = "TheNeutralElement(G,f)"
  let ?g = "restrict(f,H\<^sub>1\<times>H\<^sub>1)"
  from A1 have I: "group0(G,f)"
    using group0_def by simp
  from A2 have "group0(H\<^sub>1,?g)"
    using IsAsubgroup_def group0_def by simp
  moreover have "H\<^sub>1\<inter>H\<^sub>2 \<noteq> 0"
  proof -
    from A1 A2 A3 have "?e \<in> H\<^sub>1\<inter>H\<^sub>2"
      using group0_def group0.group0_3_L5 by simp
    thus ?thesis by auto
  qed
  moreover have "H\<^sub>1\<inter>H\<^sub>2 \<subseteq> H\<^sub>1" by auto
  moreover from A2 A3 I \<open>H\<^sub>1\<inter>H\<^sub>2 \<subseteq> H\<^sub>1\<close> have 
    "H\<^sub>1\<inter>H\<^sub>2 {is closed under} ?g"
    using group0.group0_3_L6 IsOpClosed_def 
      func_ZF_4_L7 func_ZF_4_L5 by simp
  moreover from A2 A3 I have 
    "\<forall>x \<in> H\<^sub>1\<inter>H\<^sub>2. GroupInv(H\<^sub>1,?g)`(x) \<in> H\<^sub>1\<inter>H\<^sub>2"
    using group0.group0_3_T2 group0.group0_3_T3A
    by simp
  ultimately show ?thesis
    using group0.group0_3_T3 by simp
qed

text\<open>Intersection of subgroups is a subgroup.\<close>

lemma (in group0) subgroup_inter: assumes "\<H>\<noteq>0"
  and "\<forall>H\<in>\<H>. IsAsubgroup(H,P)"
  shows "IsAsubgroup(\<Inter>\<H>,P)"
proof -
  {
    fix H assume "H:\<H>"
    with assms(2) have "\<one>:H" using group0_3_L5 by auto
  }
  then have "\<Inter>\<H> \<noteq> 0" using assms(1) by auto moreover
  {
    fix t assume "t:\<Inter>\<H>"
    then have "\<forall>H\<in>\<H>. t:H" by auto
    with assms have "t:G" using group0_3_L2 by blast
  }
  then have "\<Inter>\<H> \<subseteq> G" by auto moreover
  {
    fix x y assume xy:"x:\<Inter>\<H>" "y:\<Inter>\<H>"
    {
      fix J assume J:"J:\<H>"
      with xy have "x:J" "y:J" by auto
      with J have "P`\<langle>x,y\<rangle>:J" using assms(2) group0_3_L6 by auto
    }
    then have "P`\<langle>x,y\<rangle>:\<Inter>\<H>" using assms(1) by auto
  }
  then have "\<Inter>\<H> {is closed under} P" unfolding IsOpClosed_def by simp
  moreover
  {
    fix x assume x:"x:\<Inter>\<H>"
    {
      fix J assume J:"J:\<H>"
      with x have "x:J" by auto
      with J assms(2) have "x\<inverse> \<in> J" using group0_3_T3A by auto
    }
    then have "x\<inverse> \<in> \<Inter>\<H>" using assms(1) by auto
  }
  then have "\<forall>x \<in> \<Inter>\<H>. x\<inverse> \<in> \<Inter>\<H>" by simp
  ultimately show ?thesis using group0_3_T3 by auto
qed

text\<open>The range of the subgroup operation is the whole subgroup.\<close>

lemma image_subgr_op: assumes A1: "IsAsubgroup(H,P)"
  shows "restrict(P,H\<times>H)``(H\<times>H) = H"
proof -
  from A1 have "monoid0(H,restrict(P,H\<times>H))"
    using IsAsubgroup_def IsAgroup_def monoid0_def 
    by simp
  then show ?thesis by (rule monoid0.range_carr)
qed

text\<open>If we restrict the inverse to a subgroup, then the restricted 
  inverse is onto the subgroup.\<close>

lemma (in group0) restr_inv_onto: assumes A1: "IsAsubgroup(H,P)"
  shows "restrict(GroupInv(G,P),H)``(H) = H"
proof -
  from A1 have "GroupInv(H,restrict(P,H\<times>H))``(H) = H"
    using IsAsubgroup_def group0_def group0.group_inv_surj
    by simp
  with A1 show ?thesis using group0_3_T1 by simp
qed

text\<open>A union of two subgroups is a subgroup iff 
  one of the subgroups is a subset of the other subgroup.\<close>

lemma (in group0) union_subgroups: 
  assumes "IsAsubgroup(H\<^sub>1,P)" and "IsAsubgroup(H\<^sub>2,P)"
  shows "IsAsubgroup(H\<^sub>1\<union>H\<^sub>2,P) \<longleftrightarrow> (H\<^sub>1\<subseteq>H\<^sub>2 \<or> H\<^sub>2\<subseteq>H\<^sub>1)"
proof 
  assume "H\<^sub>1\<subseteq>H\<^sub>2 \<or> H\<^sub>2\<subseteq>H\<^sub>1" show "IsAsubgroup(H\<^sub>1\<union>H\<^sub>2,P)"
  proof -
    from \<open>H\<^sub>1\<subseteq>H\<^sub>2 \<or> H\<^sub>2\<subseteq>H\<^sub>1\<close> have "H\<^sub>2 = H\<^sub>1\<union>H\<^sub>2 \<or> H\<^sub>1 = H\<^sub>1\<union>H\<^sub>2" by auto
    with assms show "IsAsubgroup(H\<^sub>1\<union>H\<^sub>2,P)" by auto
  qed
next
  assume "IsAsubgroup(H\<^sub>1\<union>H\<^sub>2, P)" show "H\<^sub>1\<subseteq>H\<^sub>2 \<or> H\<^sub>2\<subseteq>H\<^sub>1"
  proof -
    { assume "\<not> H\<^sub>1\<subseteq>H\<^sub>2"
      then obtain x where "x\<in>H\<^sub>1" and "x\<notin>H\<^sub>2" by auto
      with assms(1) have "x\<inverse> \<in> H\<^sub>1" using group0_3_T3A by simp
      { fix y assume "y\<in>H\<^sub>2"
        let ?z = "x\<cdot>y"
        from \<open>x\<in>H\<^sub>1\<close> \<open>y\<in>H\<^sub>2\<close> have "x \<in> H\<^sub>1\<union>H\<^sub>2" and "y \<in> H\<^sub>1\<union>H\<^sub>2" by auto
        with \<open>IsAsubgroup(H\<^sub>1\<union>H\<^sub>2,P)\<close> have "?z \<in> H\<^sub>1\<union>H\<^sub>2" using group0_3_L6 by blast
        from assms \<open>x \<in> H\<^sub>1\<union>H\<^sub>2\<close>  \<open>y\<in>H\<^sub>2\<close> have "x\<in>G" "y\<in>G" and "y\<inverse>\<in>H\<^sub>2"
          using group0_3_T3A group0_3_L2 by auto
        then have "?z\<cdot>y\<inverse> = x" and "x\<inverse>\<cdot>?z = y" using inv_cancel_two(2,3) by auto
        { assume "?z \<in> H\<^sub>2"
          with \<open>IsAsubgroup(H\<^sub>2,P)\<close> \<open>y\<inverse>\<in>H\<^sub>2\<close> have "?z\<cdot>y\<inverse> \<in> H\<^sub>2" using group0_3_L6 by simp
          with \<open>?z\<cdot>y\<inverse> = x\<close> \<open>x\<notin>H\<^sub>2\<close> have False by auto
        } hence "?z \<notin> H\<^sub>2" by auto
        with assms(1) \<open>x\<inverse> \<in> H\<^sub>1\<close> \<open>?z \<in> H\<^sub>1\<union>H\<^sub>2\<close> have "x\<inverse>\<cdot>?z \<in> H\<^sub>1" using group0_3_L6 by simp
        with \<open>x\<inverse>\<cdot>?z = y\<close> have "y\<in>H\<^sub>1" by simp
      } hence "H\<^sub>2\<subseteq>H\<^sub>1" by blast
    } thus ?thesis by blast
  qed
qed

text\<open>Transitivity for "is a subgroup of" relation. The proof (probably) uses the lemma 
  \<open>restrict_restrict\<close> from standard Isabelle/ZF library which states that 
  \<open>restrict(restrict(f,A),B) = restrict(f,A\<inter>B)\<close>. That lemma is added to the simplifier, so it does
  not have to be referenced explicitly in the proof below. \<close>

lemma subgroup_transitive: 
  assumes "IsAgroup(G\<^sub>3,P)" "IsAsubgroup(G\<^sub>2,P)" "IsAsubgroup(G\<^sub>1,restrict(P,G\<^sub>2\<times>G\<^sub>2))"
  shows "IsAsubgroup(G\<^sub>1,P)"
proof -
  from assms(2) have "group0(G\<^sub>2,restrict(P,G\<^sub>2\<times>G\<^sub>2))" unfolding IsAsubgroup_def group0_def by simp
  with assms(3) have "G\<^sub>1\<subseteq>G\<^sub>2" using group0.group0_3_L2 by simp
  hence "G\<^sub>2\<times>G\<^sub>2 \<inter> G\<^sub>1\<times>G\<^sub>1 = G\<^sub>1\<times>G\<^sub>1" by auto
  with assms(3) show "IsAsubgroup(G\<^sub>1,P)" unfolding IsAsubgroup_def by simp
qed

subsection\<open>Groups vs. loops\<close>

text\<open>We defined groups as monoids with the inverse operation. An alternative way of defining a group
  is as a loop whose operation is associative. \<close>

text\<open> Groups have left and right division. \<close>

lemma (in group0) gr_has_lr_div: shows "HasLeftDiv(G,P)" and "HasRightDiv(G,P)"
proof -
  { fix x y assume "x\<in>G" "y\<in>G" 
    then have "x\<inverse>\<cdot>y \<in> G \<and> x\<cdot>(x\<inverse>\<cdot>y) = y" using group_op_closed inverse_in_group inv_cancel_two(4)
      by simp
    hence "\<exists>z. z\<in>G \<and> x\<cdot>z =y" by auto
    moreover 
    { fix z\<^sub>1 z\<^sub>2 assume "z\<^sub>1\<in>G \<and> x\<cdot>z\<^sub>1 =y" and "z\<^sub>2\<in>G \<and> x\<cdot>z\<^sub>2 =y"
      with \<open>x\<in>G\<close> have "z\<^sub>1 = z\<^sub>2" using cancel_left by blast
    }
    ultimately have "\<exists>!z. z\<in>G \<and> x\<cdot>z =y" by auto
  } then show "HasLeftDiv(G,P)" unfolding HasLeftDiv_def by simp
  { fix x y assume "x\<in>G" "y\<in>G" 
    then have "y\<cdot>x\<inverse> \<in> G \<and> (y\<cdot>x\<inverse>)\<cdot>x = y" using group_op_closed inverse_in_group inv_cancel_two(1)
      by simp
    hence "\<exists>z. z\<in>G \<and> z\<cdot>x =y" by auto
    moreover 
    { fix z\<^sub>1 z\<^sub>2 assume "z\<^sub>1\<in>G \<and> z\<^sub>1\<cdot>x =y" and "z\<^sub>2\<in>G \<and> z\<^sub>2\<cdot>x =y"
      with \<open>x\<in>G\<close> have "z\<^sub>1 = z\<^sub>2" using cancel_right by blast
    }
    ultimately have "\<exists>!z. z\<in>G \<and> z\<cdot>x =y" by auto
  } then show "HasRightDiv(G,P)" unfolding HasRightDiv_def by simp
qed

text\<open>A group is a quasigroup and a loop.\<close>

lemma (in group0) group_is_loop: shows "IsAquasigroup(G,P)" and "IsAloop(G,P)"
proof -
  show "IsAquasigroup(G,P)" unfolding IsAquasigroup_def HasLatinSquareProp_def
    using gr_has_lr_div group_oper_fun by simp
  then show "IsAloop(G,P)" unfolding IsAloop_def using group0_2_L2 by auto
qed

text\<open> An associative loop is a group.\<close>

theorem assoc_loop_is_gr: assumes "IsAloop(G,P)" and "P {is associative on} G"
  shows "IsAgroup(G,P)" 
proof -
  from assms(1) have "\<exists>e\<in>G. \<forall>x\<in>G. P`\<langle>e,x\<rangle> = x \<and> P`\<langle>x,e\<rangle> = x"
    unfolding IsAloop_def by simp
  with assms(2) have "IsAmonoid(G,P)" unfolding IsAmonoid_def by simp
  { fix x assume "x\<in>G" 
    let ?y = "RightInv(G,P)`(x)"
    from assms(1) \<open>x\<in>G\<close> have "?y \<in> G" and "P`\<langle>x,?y\<rangle> = TheNeutralElement(G,P)"
      using loop_loop0_valid loop0.lr_inv_props(3,4) by auto
    hence "\<exists>y\<in>G. P`\<langle>x,y\<rangle> = TheNeutralElement(G,P)" by auto
  }
  with \<open>IsAmonoid(G,P)\<close> show "IsAgroup(G,P)" unfolding IsAgroup_def by simp
qed

text\<open>For groups the left and right inverse are the same as the group inverse. \<close>

lemma (in group0) lr_inv_gr_inv: 
  shows "LeftInv(G,P) = GroupInv(G,P)" and "RightInv(G,P) = GroupInv(G,P)"
proof -
  have "LeftInv(G,P):G\<rightarrow>G" using group_is_loop loop_loop0_valid loop0.lr_inv_fun(1)
    by simp
  moreover from groupAssum have "GroupInv(G,P):G\<rightarrow>G" using group0_2_T2 by simp
  moreover
  { fix x assume "x\<in>G"
    let ?y = "LeftInv(G,P)`(x)"
    from \<open>x\<in>G\<close> have "?y \<in> G" and "?y\<cdot>x = \<one>"
      using group_is_loop(2) loop_loop0_valid loop0.lr_inv_props(1,2) by auto
    with \<open>x\<in>G\<close> have "LeftInv(G,P)`(x) = GroupInv(G,P)`(x)" using group0_2_L9(1) by simp
  }
  ultimately show "LeftInv(G,P) = GroupInv(G,P)" using func_eq by blast
  have "RightInv(G,P):G\<rightarrow>G" using group_is_loop loop_loop0_valid loop0.lr_inv_fun(2)
    by simp
  moreover from groupAssum have "GroupInv(G,P):G\<rightarrow>G" using group0_2_T2 by simp
  moreover
  { fix x assume "x\<in>G"
    let ?y = "RightInv(G,P)`(x)"
    from \<open>x\<in>G\<close> have "?y \<in> G" and "x\<cdot>?y = \<one>"
      using group_is_loop(2) loop_loop0_valid loop0.lr_inv_props(3,4) by auto
    with \<open>x\<in>G\<close> have "RightInv(G,P)`(x) = GroupInv(G,P)`(x)" using group0_2_L9(2) by simp
  }
  ultimately show "RightInv(G,P) = GroupInv(G,P)" using func_eq by blast  
qed


end
