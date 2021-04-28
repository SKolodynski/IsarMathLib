(*    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2005, 2006  Slawomir Kolodynski

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

section \<open>Ordered groups - introduction\<close>

theory OrderedGroup_ZF imports Group_ZF_1 AbelianGroup_ZF Finite_ZF_1 OrderedLoop_ZF

begin

text\<open>This theory file defines and shows the basic properties of (partially
  or linearly) ordered groups. 
  We show that in linearly ordered groups finite sets are bounded 
  and provide a sufficient condition for bounded sets to be finite. This 
  allows to show in \<open>Int_ZF_IML.thy\<close> that subsets of integers are 
  bounded iff they are finite.
  Some theorems proven here are properties of ordered loops rather that groups.
  However, for now the development is independent from the material in the \<open>OrderedLoop_ZF\<close> theory,
  we just import the definitions of \<open>NonnegativeSet\<close> and \<open>PositiveSet\<close> from there.\<close>

subsection\<open>Ordered groups\<close>

text\<open>This section defines ordered groups and various related notions.\<close>

text\<open>An ordered group is a group equipped with a partial order that is
  "translation invariant", that is if $a\leq b$ then $a\cdot g \leq b\cdot g$
  and $g\cdot a \leq g\cdot b$.\<close>

definition
  "IsAnOrdGroup(G,P,r) \<equiv> 
  (IsAgroup(G,P) \<and> r\<subseteq>G\<times>G \<and> IsPartOrder(G,r) \<and> (\<forall>g\<in>G. \<forall>a b. 
  \<langle>a,b\<rangle> \<in> r \<longrightarrow> \<langle>P`\<langle> a,g\<rangle>,P`\<langle> b,g\<rangle> \<rangle> \<in> r \<and> \<langle> P`\<langle> g,a\<rangle>,P`\<langle> g,b\<rangle> \<rangle> \<in> r ) )"


text\<open>We also define 
  the absolute value as a ZF-function that is the 
  identity on $G^+$ and the group inverse on the rest of the group.\<close>

definition
  "AbsoluteValue(G,P,r) \<equiv> id(Nonnegative(G,P,r)) \<union> 
  restrict(GroupInv(G,P),G - Nonnegative(G,P,r))"

text\<open>The odd functions are defined as those having property 
  $f(a^{-1})=(f(a))^{-1}$. This looks a bit strange in the 
  multiplicative notation, I have to admit.
  For linearly oredered groups a function $f$ defined on the set of positive
  elements iniquely defines an odd function of the whole group. This function
  is called an odd extension of $f$\<close>

definition
  "OddExtension(G,P,r,f) \<equiv> 
  (f \<union> {\<langle>a, GroupInv(G,P)`(f`(GroupInv(G,P)`(a)))\<rangle>. 
  a \<in> GroupInv(G,P)``(PositiveSet(G,P,r))} \<union> 
  {\<langle>TheNeutralElement(G,P),TheNeutralElement(G,P)\<rangle>})"

text\<open>We will use a similar notation for ordered groups as for the generic 
  groups. \<open>G\<^sup>+\<close> denotes the set of nonnegative elements 
  (that satisfy $1\leq a$) and \<open>G\<^sub>+\<close> is the set of (strictly) positive
  elements. \<open>\<sm>A\<close> is the set inverses of elements from $A$. I hope 
  that using additive notation for this notion is not too shocking here. 
  The symbol \<open>f\<degree>\<close> denotes the odd extension of $f$. For a function
  defined on $G_+$ this is the unique odd function on $G$ that is 
  equal to $f$ on $G_+$.\<close>

locale group3 =

  fixes G and P and r

  assumes ordGroupAssum: "IsAnOrdGroup(G,P,r)"

  fixes unit ("\<one>")
  defines unit_def [simp]: "\<one> \<equiv> TheNeutralElement(G,P)"

  fixes groper (infixl "\<cdot>" 70)
  defines groper_def [simp]: "a \<cdot> b \<equiv> P`\<langle> a,b\<rangle>"

  fixes inv ("_\<inverse> " [90] 91)
  defines inv_def [simp]: "x\<inverse> \<equiv> GroupInv(G,P)`(x)"

  fixes lesseq (infix "\<lsq>" 68)
  defines lesseq_def [simp]: "a \<lsq> b \<equiv> \<langle> a,b\<rangle> \<in> r"

  fixes sless (infix "\<ls>" 68)
  defines sless_def [simp]: "a \<ls> b \<equiv> a\<lsq>b \<and> a\<noteq>b"

  fixes nonnegative ("G\<^sup>+")
  defines nonnegative_def [simp]: "G\<^sup>+ \<equiv> Nonnegative(G,P,r)"

  fixes positive ("G\<^sub>+")
  defines positive_def [simp]: "G\<^sub>+ \<equiv> PositiveSet(G,P,r)"
  
  fixes setinv ("\<sm> _" 72)
  defines setninv_def [simp]: "\<sm>A \<equiv> GroupInv(G,P)``(A)"

  fixes abs ("| _ |")
  defines abs_def [simp]: "|a| \<equiv> AbsoluteValue(G,P,r)`(a)"

  fixes oddext ("_ \<degree>")
  defines oddext_def [simp]: "f\<degree> \<equiv> OddExtension(G,P,r,f)"


text\<open>In \<open>group3\<close> context we can use the theorems proven in the 
  \<open>group0\<close> context.\<close>

lemma (in group3) OrderedGroup_ZF_1_L1: shows "group0(G,P)"
  using ordGroupAssum IsAnOrdGroup_def group0_def by simp

text\<open>Ordered group (carrier) is not empty. This is a property of
  monoids, but it is good to have it handy in the \<open>group3\<close> context.\<close>

lemma (in group3) OrderedGroup_ZF_1_L1A: shows "G\<noteq>0"
  using OrderedGroup_ZF_1_L1 group0.group0_2_L1 monoid0.group0_1_L3A
  by blast
  
text\<open>The next lemma is just to see the definition of the nonnegative set
  in our notation.\<close>

lemma (in group3) OrderedGroup_ZF_1_L2: 
  shows "g\<in>G\<^sup>+ \<longleftrightarrow> \<one>\<lsq>g"
  using ordGroupAssum IsAnOrdGroup_def Nonnegative_def 
  by auto

text\<open>The next lemma is just to see the definition of the positive set
  in our notation.\<close>

lemma (in group3) OrderedGroup_ZF_1_L2A: 
  shows "g\<in>G\<^sub>+ \<longleftrightarrow> (\<one>\<lsq>g \<and> g\<noteq>\<one>)"
  using ordGroupAssum IsAnOrdGroup_def PositiveSet_def 
  by auto

text\<open>For total order if $g$ is not in $G^{+}$, then it has to be 
  less or equal the unit.\<close>

lemma (in group3) OrderedGroup_ZF_1_L2B: 
  assumes A1: "r {is total on} G" and A2: "a\<in>G-G\<^sup>+"
  shows "a\<lsq>\<one>"
proof -
  from A2 have "a\<in>G"   "\<one> \<in> G"  "\<not>(\<one>\<lsq>a)" 
    using OrderedGroup_ZF_1_L1 group0.group0_2_L2 OrderedGroup_ZF_1_L2 
    by auto
  with A1 show ?thesis using IsTotal_def by auto
qed

text\<open>The group order is reflexive.\<close>

lemma (in group3) OrderedGroup_ZF_1_L3: assumes "g\<in>G"
  shows "g\<lsq>g"
  using ordGroupAssum assms IsAnOrdGroup_def IsPartOrder_def refl_def
  by simp

text\<open>$1$ is nonnegative.\<close>

lemma (in group3) OrderedGroup_ZF_1_L3A: shows "\<one>\<in>G\<^sup>+"
  using OrderedGroup_ZF_1_L2 OrderedGroup_ZF_1_L3
    OrderedGroup_ZF_1_L1 group0.group0_2_L2 by simp
  
text\<open>In this context $a \leq b$ implies that both $a$ and $b$ belong 
  to $G$.\<close>

lemma (in group3) OrderedGroup_ZF_1_L4: 
  assumes "a\<lsq>b" shows "a\<in>G" "b\<in>G"
  using ordGroupAssum assms IsAnOrdGroup_def by auto

text\<open>Similarly in this context $a \le b$ implies that both $a$ and $b$ belong 
  to $G$.\<close>

lemma (in group3) less_are_members: 
  assumes "a\<ls>b" shows "a\<in>G" "b\<in>G"
  using ordGroupAssum assms IsAnOrdGroup_def by auto

text\<open>It is good to have transitivity handy.\<close>

lemma (in group3) Group_order_transitive:
  assumes A1: "a\<lsq>b"  "b\<lsq>c" shows "a\<lsq>c"
proof -
  from ordGroupAssum have "trans(r)"
    using IsAnOrdGroup_def IsPartOrder_def
    by simp
  moreover from A1 have "\<langle> a,b\<rangle> \<in> r \<and> \<langle> b,c\<rangle> \<in> r" by simp
  ultimately have "\<langle> a,c\<rangle> \<in> r" by (rule Fol1_L3)
  thus ?thesis by simp
qed

text\<open>The order in an ordered group is antisymmetric.\<close>

lemma (in group3) group_order_antisym:
  assumes A1: "a\<lsq>b"  "b\<lsq>a" shows "a=b"
proof -
  from ordGroupAssum A1 have 
    "antisym(r)"  "\<langle> a,b\<rangle> \<in> r"  "\<langle> b,a\<rangle> \<in> r"
    using IsAnOrdGroup_def IsPartOrder_def by auto
  then show "a=b" by (rule Fol1_L4) 
qed

text\<open>Transitivity for the strict order: if $a < b$ and $b\leq c$, then $a < c$.\<close>

lemma (in group3) OrderedGroup_ZF_1_L4A:
  assumes A1: "a\<ls>b"  and A2: "b\<lsq>c"
  shows "a\<ls>c"
proof -
  from A1 A2 have "a\<lsq>b"  "b\<lsq>c" by auto
  then have "a\<lsq>c" by (rule Group_order_transitive)
  moreover from A1 A2 have "a\<noteq>c" using group_order_antisym by auto
  ultimately show "a\<ls>c" by simp
qed

text\<open>Another version of transitivity for the strict order: 
  if $a\leq b$ and $b < c$, then $a < c$.\<close>

lemma (in group3) group_strict_ord_transit:
  assumes A1: "a\<lsq>b" and A2: "b\<ls>c"
  shows "a\<ls>c"
proof -
  from A1 A2 have "a\<lsq>b"  "b\<lsq>c" by auto
  then have  "a\<lsq>c" by (rule Group_order_transitive)
  moreover from A1 A2 have "a\<noteq>c" using group_order_antisym by auto
  ultimately show "a\<ls>c" by simp
qed

text\<open>The order is translation invariant. \<close>

lemma (in group3) ord_transl_inv: assumes "a\<lsq>b" "c\<in>G"
  shows "a\<cdot>c \<lsq> b\<cdot>c" and "c\<cdot>a \<lsq> c\<cdot>b"
  using ordGroupAssum assms unfolding IsAnOrdGroup_def by auto

text\<open>Strict order is preserved by translations.\<close>

lemma (in group3) group_strict_ord_transl_inv: 
  assumes "a\<ls>b" and "c\<in>G"
  shows "a\<cdot>c \<ls> b\<cdot>c" and "c\<cdot>a \<ls> c\<cdot>b"
  using assms ord_transl_inv OrderedGroup_ZF_1_L4 OrderedGroup_ZF_1_L1 group0.group0_2_L19 
  by auto

text\<open>If the group order is total, then the group is ordered linearly.\<close>

lemma (in group3) group_ord_total_is_lin:
  assumes "r {is total on} G"
  shows "IsLinOrder(G,r)"
  using assms ordGroupAssum IsAnOrdGroup_def Order_ZF_1_L3
  by simp

text\<open>For linearly ordered groups elements in the nonnegative set are
  greater than those in the complement.\<close>

lemma (in group3) OrderedGroup_ZF_1_L4B:
  assumes "r {is total on} G" 
  and "a\<in>G\<^sup>+" and "b \<in> G-G\<^sup>+"
  shows "b\<lsq>a"
proof -
  from assms have "b\<lsq>\<one>" "\<one>\<lsq>a"
    using OrderedGroup_ZF_1_L2 OrderedGroup_ZF_1_L2B by auto
  then show ?thesis by (rule Group_order_transitive)
qed

text\<open>If $a\leq 1$ and $a\neq 1$, then $a \in G\setminus G^{+}$.\<close>

lemma (in group3) OrderedGroup_ZF_1_L4C:
  assumes A1: "a\<lsq>\<one>" and A2: "a\<noteq>\<one>"
  shows "a \<in> G-G\<^sup>+"
proof - 
  { assume "a \<notin> G-G\<^sup>+" 
    with ordGroupAssum A1 A2 have False 
      using OrderedGroup_ZF_1_L4 OrderedGroup_ZF_1_L2
	OrderedGroup_ZF_1_L4 IsAnOrdGroup_def IsPartOrder_def antisym_def
      by auto
  } thus ?thesis by auto
qed

text\<open>An element smaller than an element in $G\setminus G^+$ is in 
  $G\setminus G^+$.\<close>

lemma (in group3) OrderedGroup_ZF_1_L4D:
  assumes A1: "a\<in>G-G\<^sup>+" and A2: "b\<lsq>a"
  shows "b\<in>G-G\<^sup>+"
proof - 
  { assume "b \<notin> G - G\<^sup>+"
    with A2 have "\<one>\<lsq>b" "b\<lsq>a"
      using OrderedGroup_ZF_1_L4 OrderedGroup_ZF_1_L2 by auto
    then have "\<one>\<lsq>a" by (rule Group_order_transitive)
    with A1 have False using OrderedGroup_ZF_1_L2 by simp
  } thus ?thesis by auto
qed

text\<open>The nonnegative set is contained in the group.\<close>

lemma (in group3) OrderedGroup_ZF_1_L4E: shows "G\<^sup>+ \<subseteq> G"
  using OrderedGroup_ZF_1_L2 OrderedGroup_ZF_1_L4 by auto

text\<open>The positive set is contained in the nonnegative set, hence in the group.\<close>

lemma (in group3) pos_set_in_gr: shows "G\<^sub>+ \<subseteq> G\<^sup>+" and "G\<^sub>+ \<subseteq> G"
  using OrderedGroup_ZF_1_L2A OrderedGroup_ZF_1_L2 OrderedGroup_ZF_1_L4E
  by auto  

text\<open>Taking the inverse on both sides reverses the inequality.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5:
  assumes A1: "a\<lsq>b" shows "b\<inverse>\<lsq>a\<inverse>"
proof -
  from A1 have T1: "a\<in>G" "b\<in>G" "a\<inverse>\<in>G" "b\<inverse>\<in>G" 
    using OrderedGroup_ZF_1_L4 OrderedGroup_ZF_1_L1 
      group0.inverse_in_group by auto
  with A1 ordGroupAssum have "a\<cdot>a\<inverse>\<lsq>b\<cdot>a\<inverse>" using IsAnOrdGroup_def
    by simp
  with T1 ordGroupAssum have "b\<inverse>\<cdot>\<one>\<lsq>b\<inverse>\<cdot>(b\<cdot>a\<inverse>)"
    using OrderedGroup_ZF_1_L1 group0.group0_2_L6 IsAnOrdGroup_def
    by simp
  with T1 show ?thesis using
    OrderedGroup_ZF_1_L1 group0.group0_2_L2 group0.group_oper_assoc
    group0.group0_2_L6 by simp
qed

text\<open>If an element is smaller that the unit, then its inverse is greater.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5A: 
  assumes A1: "a\<lsq>\<one>" shows "\<one>\<lsq>a\<inverse>"
proof -
  from A1 have "\<one>\<inverse>\<lsq>a\<inverse>" using OrderedGroup_ZF_1_L5
    by simp
  then show ?thesis using OrderedGroup_ZF_1_L1 group0.group_inv_of_one 
    by simp
qed

text\<open>If an the inverse of an element is greater that the unit, 
  then the element is smaller.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5AA: 
  assumes A1: "a\<in>G" and A2: "\<one>\<lsq>a\<inverse>"  
  shows "a\<lsq>\<one>"
proof -
  from A2 have "(a\<inverse>)\<inverse>\<lsq>\<one>\<inverse>" using OrderedGroup_ZF_1_L5
    by simp
  with A1 show "a\<lsq>\<one>"
    using OrderedGroup_ZF_1_L1 group0.group_inv_of_inv group0.group_inv_of_one
    by simp
qed

text\<open>If an element is nonnegative, then the inverse is 
  not greater that the unit.
  Also shows that nonnegative elements cannot be negative\<close>

lemma (in group3) OrderedGroup_ZF_1_L5AB:
  assumes A1: "\<one>\<lsq>a" shows "a\<inverse>\<lsq>\<one>" and "\<not>(a\<lsq>\<one> \<and> a\<noteq>\<one>)"
proof -
  from A1 have "a\<inverse>\<lsq>\<one>\<inverse>"
    using OrderedGroup_ZF_1_L5 by simp
  then show "a\<inverse>\<lsq>\<one>" using OrderedGroup_ZF_1_L1 group0.group_inv_of_one
    by simp
  { assume "a\<lsq>\<one>" and "a\<noteq>\<one>"
    with A1 have False using group_order_antisym
      by blast
  } then show "\<not>(a\<lsq>\<one> \<and> a\<noteq>\<one>)" by auto
qed

text\<open>If two elements are greater or equal than the unit, then the inverse
  of one is not greater than the other.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5AC:
  assumes A1: "\<one>\<lsq>a"  "\<one>\<lsq>b"
  shows "a\<inverse> \<lsq> b"
proof -
  from A1 have "a\<inverse>\<lsq>\<one>"  "\<one>\<lsq>b"
    using OrderedGroup_ZF_1_L5AB by auto
  then show "a\<inverse> \<lsq> b" by (rule Group_order_transitive)
qed

subsection\<open>Inequalities\<close>

text\<open>This section developes some simple tools to deal with inequalities.\<close>


text\<open>Taking negative on both sides reverses the inequality, case with
  an inverse on one side.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5AD:
  assumes A1: "b \<in> G" and A2: "a\<lsq>b\<inverse>"
  shows "b \<lsq> a\<inverse>"
proof -
  from A2 have "(b\<inverse>)\<inverse> \<lsq> a\<inverse>"
    using OrderedGroup_ZF_1_L5 by simp
  with A1 show "b \<lsq> a\<inverse>"
    using OrderedGroup_ZF_1_L1 group0.group_inv_of_inv
    by simp
qed

text\<open>We can cancel the same element on both sides of an inequality.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5AE:
  assumes A1: "a\<in>G"  "b\<in>G"  "c\<in>G" and A2: "a\<cdot>b \<lsq> a\<cdot>c"
  shows "b\<lsq>c"
proof -
  from ordGroupAssum A1 A2 have "a\<inverse>\<cdot>(a\<cdot>b) \<lsq> a\<inverse>\<cdot>(a\<cdot>c)"
    using OrderedGroup_ZF_1_L1 group0.inverse_in_group IsAnOrdGroup_def 
    by simp
  with A1 show "b\<lsq>c" 
    using OrderedGroup_ZF_1_L1 group0.inv_cancel_two
    by simp
qed

text\<open>We can cancel the same element on both sides of an inequality, right side.\<close>

lemma (in group3) ineq_cancel_right:
  assumes "a\<in>G"  "b\<in>G"  "c\<in>G" and "a\<cdot>b \<lsq> c\<cdot>b"
  shows "a\<lsq>c"
proof -
  from assms(2,4) have "(a\<cdot>b)\<cdot>b\<inverse> \<lsq> (c\<cdot>b)\<cdot>b\<inverse>"
    using OrderedGroup_ZF_1_L1 group0.inverse_in_group ord_transl_inv(1) by simp
  with assms(1,2,3) show "a\<lsq>c" using OrderedGroup_ZF_1_L1 group0.inv_cancel_two(2) 
    by auto
qed

text\<open>We can cancel the same element on both sides of an inequality,
  a version with an inverse on both sides.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5AF:
  assumes A1: "a\<in>G"  "b\<in>G"  "c\<in>G" and A2: "a\<cdot>b\<inverse> \<lsq> a\<cdot>c\<inverse>"
  shows "c\<lsq>b"
proof -
  from A1 A2 have "(c\<inverse>)\<inverse> \<lsq> (b\<inverse>)\<inverse>"
     using OrderedGroup_ZF_1_L1 group0.inverse_in_group 
      OrderedGroup_ZF_1_L5AE OrderedGroup_ZF_1_L5 by simp
  with A1 show "c\<lsq>b" 
    using OrderedGroup_ZF_1_L1 group0.group_inv_of_inv by simp
qed

text\<open>Taking negative on both sides reverses the inequality, another case with
  an inverse on one side.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5AG:
  assumes A1: "a \<in> G" and A2: "a\<inverse>\<lsq>b"
  shows "b\<inverse> \<lsq> a"
proof -
  from A2 have "b\<inverse> \<lsq> (a\<inverse>)\<inverse>"
    using OrderedGroup_ZF_1_L5 by simp
  with A1 show "b\<inverse> \<lsq> a"
    using OrderedGroup_ZF_1_L1 group0.group_inv_of_inv
    by simp
qed
  
text\<open>We can multiply the sides of two inequalities.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5B:
  assumes A1: "a\<lsq>b" and A2: "c\<lsq>d"
  shows "a\<cdot>c \<lsq> b\<cdot>d"
proof -
  from A1 A2 have "c\<in>G" "b\<in>G" using OrderedGroup_ZF_1_L4 by auto
  with A1 A2 ordGroupAssum have "a\<cdot>c\<lsq> b\<cdot>c" "b\<cdot>c\<lsq>b\<cdot>d"
    using IsAnOrdGroup_def by auto
  then show "a\<cdot>c \<lsq> b\<cdot>d" by (rule Group_order_transitive)
qed

text\<open>We can replace first of the factors on one side of an inequality 
  with a greater one.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5C: 
  assumes A1: "c\<in>G" and A2: "a\<lsq>b\<cdot>c" and A3: "b\<lsq>b\<^sub>1" 
  shows "a\<lsq>b\<^sub>1\<cdot>c"
proof -
  from A1 A3 have "b\<cdot>c \<lsq> b\<^sub>1\<cdot>c"
    using OrderedGroup_ZF_1_L3 OrderedGroup_ZF_1_L5B by simp
  with A2 show "a\<lsq>b\<^sub>1\<cdot>c" by (rule Group_order_transitive)
qed

text\<open>We can replace second of the factors on one side of an inequality 
  with a greater one.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5D: 
  assumes A1: "b\<in>G" and A2: "a \<lsq> b\<cdot>c" and A3: "c\<lsq>b\<^sub>1" 
  shows "a \<lsq> b\<cdot>b\<^sub>1"
proof -
  from A1 A3 have "b\<cdot>c \<lsq> b\<cdot>b\<^sub>1"
    using OrderedGroup_ZF_1_L3 OrderedGroup_ZF_1_L5B by auto
  with A2 show "a\<lsq>b\<cdot>b\<^sub>1" by (rule Group_order_transitive)
qed

text\<open>We can replace factors on one side of an inequality 
  with greater ones.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5E: 
  assumes A1: "a \<lsq> b\<cdot>c" and A2: "b\<lsq>b\<^sub>1"  "c\<lsq>c\<^sub>1"  
  shows "a \<lsq> b\<^sub>1\<cdot>c\<^sub>1"
proof -
  from A2 have "b\<cdot>c \<lsq> b\<^sub>1\<cdot>c\<^sub>1" using OrderedGroup_ZF_1_L5B 
    by simp
  with A1 show "a\<lsq>b\<^sub>1\<cdot>c\<^sub>1" by (rule Group_order_transitive)
qed

text\<open>We don't decrease an element of the group by multiplying by one that is
  nonnegative.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5F:
  assumes A1: "\<one>\<lsq>a" and A2: "b\<in>G"
  shows "b\<lsq>a\<cdot>b"  "b\<lsq>b\<cdot>a" 
proof -
  from ordGroupAssum A1 A2 have  
    "\<one>\<cdot>b\<lsq>a\<cdot>b"  "b\<cdot>\<one>\<lsq>b\<cdot>a"
    using IsAnOrdGroup_def by auto
  with A2 show "b\<lsq>a\<cdot>b"  "b\<lsq>b\<cdot>a"
    using OrderedGroup_ZF_1_L1 group0.group0_2_L2
    by auto
qed

text\<open>We can multiply the right hand side of an inequality by a nonnegative
  element.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5G: assumes A1: "a\<lsq>b"
  and A2: "\<one>\<lsq>c" shows "a\<lsq>b\<cdot>c"  "a\<lsq>c\<cdot>b" 
proof -
  from A1 A2 have I: "b\<lsq>b\<cdot>c"  and II: "b\<lsq>c\<cdot>b"
    using OrderedGroup_ZF_1_L4 OrderedGroup_ZF_1_L5F by auto
  from A1 I show "a\<lsq>b\<cdot>c" by (rule Group_order_transitive)
  from A1 II show "a\<lsq>c\<cdot>b" by (rule Group_order_transitive)
qed

text\<open>We can put two elements on the other side of inequality, 
  changing their sign.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5H: 
  assumes A1: "a\<in>G"  "b\<in>G" and A2: "a\<cdot>b\<inverse> \<lsq> c"
  shows 
  "a \<lsq> c\<cdot>b"
  "c\<inverse>\<cdot>a \<lsq> b"
proof -
  from A2 have T: "c\<in>G"  "c\<inverse> \<in> G"
    using OrderedGroup_ZF_1_L4 OrderedGroup_ZF_1_L1 
      group0.inverse_in_group by auto
  from ordGroupAssum A1 A2 have "a\<cdot>b\<inverse>\<cdot>b \<lsq> c\<cdot>b"
    using IsAnOrdGroup_def by simp
  with A1 show "a \<lsq> c\<cdot>b" 
    using OrderedGroup_ZF_1_L1 group0.inv_cancel_two
    by simp
  with ordGroupAssum A2 T have "c\<inverse>\<cdot>a \<lsq> c\<inverse>\<cdot>(c\<cdot>b)"
    using IsAnOrdGroup_def by simp
  with A1 T show "c\<inverse>\<cdot>a \<lsq> b"  
    using OrderedGroup_ZF_1_L1 group0.inv_cancel_two
    by simp
qed

text\<open>We can multiply the sides of one inequality by inverse of another.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5I: 
  assumes "a\<lsq>b" and "c\<lsq>d"
  shows "a\<cdot>d\<inverse> \<lsq> b\<cdot>c\<inverse>"
  using assms OrderedGroup_ZF_1_L5 OrderedGroup_ZF_1_L5B
  by simp

text\<open>We can put an element on the other side of an inequality
  changing its sign, version with the inverse.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5J:
  assumes A1: "a\<in>G"  "b\<in>G" and A2: "c \<lsq> a\<cdot>b\<inverse>"
  shows "c\<cdot>b \<lsq> a"
proof -
  from ordGroupAssum A1 A2 have "c\<cdot>b \<lsq> a\<cdot>b\<inverse>\<cdot>b"
    using IsAnOrdGroup_def by simp
  with A1 show "c\<cdot>b \<lsq> a" 
    using OrderedGroup_ZF_1_L1 group0.inv_cancel_two
    by simp
qed

text\<open>We can put an element on the other side of an inequality
  changing its sign, version with the inverse.\<close>

lemma (in group3) OrderedGroup_ZF_1_L5JA:
  assumes A1: "a\<in>G"  "b\<in>G" and A2: "c \<lsq> a\<inverse>\<cdot>b"
  shows "a\<cdot>c\<lsq> b"
proof -
  from ordGroupAssum A1 A2 have "a\<cdot>c \<lsq> a\<cdot>(a\<inverse>\<cdot>b)"
    using IsAnOrdGroup_def by simp
  with A1 show "a\<cdot>c\<lsq> b" 
    using OrderedGroup_ZF_1_L1 group0.inv_cancel_two
    by simp
qed
    

text\<open>A special case of \<open>OrderedGroup_ZF_1_L5J\<close> where $c=1$.\<close>

corollary (in group3) OrderedGroup_ZF_1_L5K: 
  assumes A1: "a\<in>G"  "b\<in>G" and A2: "\<one> \<lsq> a\<cdot>b\<inverse>"
  shows "b \<lsq> a"
proof -
  from A1 A2 have "\<one>\<cdot>b \<lsq> a"
    using OrderedGroup_ZF_1_L5J by simp
  with A1 show "b \<lsq> a"
    using OrderedGroup_ZF_1_L1 group0.group0_2_L2
    by simp
qed

text\<open>A special case of \<open>OrderedGroup_ZF_1_L5JA\<close> where $c=1$.\<close>

corollary (in group3) OrderedGroup_ZF_1_L5KA: 
  assumes A1: "a\<in>G"  "b\<in>G" and A2: "\<one> \<lsq> a\<inverse>\<cdot>b"
  shows "a \<lsq> b"
proof -
  from A1 A2 have "a\<cdot>\<one> \<lsq> b"
    using OrderedGroup_ZF_1_L5JA by simp
  with A1 show "a \<lsq> b"
    using OrderedGroup_ZF_1_L1 group0.group0_2_L2
    by simp
qed

text\<open>If the order is total, the elements that do not belong
  to the positive set are negative. We also show here that the group inverse
  of an element that does not belong to the nonnegative set does belong to the
  nonnegative set.\<close>

lemma (in group3) OrderedGroup_ZF_1_L6: 
  assumes A1: "r {is total on} G" and A2: "a\<in>G-G\<^sup>+"
  shows "a\<lsq>\<one>"  "a\<inverse> \<in> G\<^sup>+"  "restrict(GroupInv(G,P),G-G\<^sup>+)`(a) \<in> G\<^sup>+" 
proof - 
  from A2 have T1: "a\<in>G" "a\<notin>G\<^sup>+" "\<one>\<in>G" 
    using OrderedGroup_ZF_1_L1 group0.group0_2_L2 by auto
  with A1 show "a\<lsq>\<one>" using OrderedGroup_ZF_1_L2 IsTotal_def
    by auto
  then show "a\<inverse> \<in> G\<^sup>+" using OrderedGroup_ZF_1_L5A OrderedGroup_ZF_1_L2
    by simp
  with A2 show "restrict(GroupInv(G,P),G-G\<^sup>+)`(a) \<in> G\<^sup>+"
    using restrict by simp
qed

text\<open>If a property is invariant with respect to taking the inverse
  and it is true on the nonnegative set, than it is true on the whole
  group.\<close>

lemma (in group3) OrderedGroup_ZF_1_L7:
  assumes A1: "r {is total on} G"
  and A2: "\<forall>a\<in>G\<^sup>+.\<forall>b\<in>G\<^sup>+. Q(a,b)"
  and A3: "\<forall>a\<in>G.\<forall>b\<in>G. Q(a,b)\<longrightarrow>Q(a\<inverse>,b)"
  and A4: "\<forall>a\<in>G.\<forall>b\<in>G. Q(a,b)\<longrightarrow>Q(a,b\<inverse>)"
  and A5: "a\<in>G" "b\<in>G"
  shows "Q(a,b)"
proof -
  { assume A6: "a\<in>G\<^sup>+" have "Q(a,b)"
    proof -
      { assume "b\<in>G\<^sup>+" 
	with A6 A2 have "Q(a,b)" by simp }
      moreover
      { assume "b\<notin>G\<^sup>+"
	with A1 A2 A4 A5 A6 have "Q(a,(b\<inverse>)\<inverse>)"  
	  using OrderedGroup_ZF_1_L6 OrderedGroup_ZF_1_L1 group0.inverse_in_group
	  by simp
	with A5 have "Q(a,b)" using OrderedGroup_ZF_1_L1 group0.group_inv_of_inv
	  by simp }
      ultimately show "Q(a,b)" by auto
    qed }
  moreover
  { assume "a\<notin>G\<^sup>+"
    with A1 A5 have T1: "a\<inverse> \<in> G\<^sup>+" using OrderedGroup_ZF_1_L6 by simp
    have "Q(a,b)"
    proof -
      { assume "b\<in>G\<^sup>+"
	with A2 A3 A5 T1 have "Q((a\<inverse>)\<inverse>,b)" 
	  using OrderedGroup_ZF_1_L1 group0.inverse_in_group by simp
	with A5 have "Q(a,b)" using OrderedGroup_ZF_1_L1 group0.group_inv_of_inv
	  by simp }
      moreover
      { assume "b\<notin>G\<^sup>+"
	with A1 A2 A3 A4 A5 T1 have "Q((a\<inverse>)\<inverse>,(b\<inverse>)\<inverse>)"
	  using OrderedGroup_ZF_1_L6 OrderedGroup_ZF_1_L1 group0.inverse_in_group
	  by simp
	with A5 have "Q(a,b)" using OrderedGroup_ZF_1_L1 group0.group_inv_of_inv
	  by simp }
      ultimately show "Q(a,b)" by auto
    qed }
  ultimately show "Q(a,b)" by auto
qed

text\<open>A lemma about splitting the ordered group "plane" into 6 subsets. Useful
  for proofs by cases.\<close>

lemma (in group3) OrdGroup_6cases: assumes A1: "r {is total on} G" 
  and A2:  "a\<in>G"  "b\<in>G"
  shows 
  "\<one>\<lsq>a \<and> \<one>\<lsq>b  \<or>  a\<lsq>\<one> \<and> b\<lsq>\<one>  \<or>  
  a\<lsq>\<one> \<and> \<one>\<lsq>b \<and> \<one> \<lsq> a\<cdot>b  \<or> a\<lsq>\<one> \<and> \<one>\<lsq>b \<and> a\<cdot>b \<lsq> \<one>  \<or>  
  \<one>\<lsq>a \<and> b\<lsq>\<one> \<and> \<one> \<lsq> a\<cdot>b  \<or>  \<one>\<lsq>a \<and> b\<lsq>\<one> \<and> a\<cdot>b \<lsq> \<one>"
proof -
  from A1 A2 have 
    "\<one>\<lsq>a \<or> a\<lsq>\<one>"   
    "\<one>\<lsq>b \<or> b\<lsq>\<one>"
    "\<one> \<lsq> a\<cdot>b \<or> a\<cdot>b \<lsq> \<one>"
    using OrderedGroup_ZF_1_L1 group0.group_op_closed group0.group0_2_L2
      IsTotal_def by auto
  then show ?thesis by auto
qed

text\<open>The next lemma shows what happens when one element of a totally 
  ordered group is not greater or equal than another.\<close>

lemma (in group3) OrderedGroup_ZF_1_L8:
  assumes A1: "r {is total on} G"
  and A2: "a\<in>G"  "b\<in>G"
  and A3: "\<not>(a\<lsq>b)"
  shows "b \<lsq> a"  "a\<inverse> \<lsq> b\<inverse>"  "a\<noteq>b"  "b\<ls>a"
 
proof -
  from A1 A2 A3 show I: "b \<lsq> a" using IsTotal_def
    by auto
  then show "a\<inverse> \<lsq> b\<inverse>" using OrderedGroup_ZF_1_L5 by simp
  from A2 have "a \<lsq> a" using OrderedGroup_ZF_1_L3 by simp
  with I A3 show "a\<noteq>b"  "b \<ls> a" by auto
qed

text\<open>If one element is greater or equal and not equal to another,
  then it is not smaller or equal.\<close>

lemma (in group3) OrderedGroup_ZF_1_L8AA: 
  assumes A1: "a\<lsq>b" and A2: "a\<noteq>b"
  shows "\<not>(b\<lsq>a)"
proof -
  { note A1
    moreover assume "b\<lsq>a"
    ultimately have "a=b" by (rule group_order_antisym)
    with A2 have False by simp
  } thus "\<not>(b\<lsq>a)" by auto
qed

text\<open>A special case of \<open>OrderedGroup_ZF_1_L8\<close> when one of 
  the elements is the unit.\<close>

corollary (in group3) OrderedGroup_ZF_1_L8A:
  assumes A1: "r {is total on} G"
  and A2: "a\<in>G" and A3: "\<not>(\<one>\<lsq>a)"
  shows "\<one> \<lsq> a\<inverse>"  "\<one>\<noteq>a"  "a\<lsq>\<one>"
proof -
  from A1 A2 A3 have I:
    "r {is total on} G"
    "\<one>\<in>G"  "a\<in>G"
     "\<not>(\<one>\<lsq>a)"
    using OrderedGroup_ZF_1_L1 group0.group0_2_L2
    by auto
  then have "\<one>\<inverse> \<lsq> a\<inverse>"
    by (rule OrderedGroup_ZF_1_L8)
  then show "\<one> \<lsq> a\<inverse>"
    using OrderedGroup_ZF_1_L1 group0.group_inv_of_one by simp
  from I show "\<one>\<noteq>a" by (rule OrderedGroup_ZF_1_L8)
  from A1 I show "a\<lsq>\<one>" using IsTotal_def
    by auto
qed

text\<open>A negative element can not be nonnegative.\<close>

lemma (in group3) OrderedGroup_ZF_1_L8B:
  assumes A1: "a\<lsq>\<one>"  and A2: "a\<noteq>\<one>" shows "\<not>(\<one>\<lsq>a)"
proof -
  { assume  "\<one>\<lsq>a" 
    with A1 have "a=\<one>" using group_order_antisym
      by auto
    with A2 have False by simp
  } thus ?thesis by auto
qed

text\<open>An element is greater or equal than another iff the difference is 
  nonpositive.\<close>

lemma (in group3) OrderedGroup_ZF_1_L9:
  assumes A1: "a\<in>G"  "b\<in>G"
  shows "a\<lsq>b \<longleftrightarrow> a\<cdot>b\<inverse> \<lsq> \<one>"
proof
  assume "a \<lsq> b"
  with ordGroupAssum A1 have "a\<cdot>b\<inverse> \<lsq> b\<cdot>b\<inverse>"
    using OrderedGroup_ZF_1_L1 group0.inverse_in_group
    IsAnOrdGroup_def by simp
  with A1 show "a\<cdot>b\<inverse> \<lsq> \<one>" 
    using OrderedGroup_ZF_1_L1 group0.group0_2_L6
    by simp
next assume A2: "a\<cdot>b\<inverse> \<lsq> \<one>"
  with ordGroupAssum A1 have "a\<cdot>b\<inverse>\<cdot>b \<lsq> \<one>\<cdot>b"
    using IsAnOrdGroup_def by simp
  with A1 show "a \<lsq> b"
    using OrderedGroup_ZF_1_L1 
      group0.inv_cancel_two group0.group0_2_L2 
    by simp
qed

text\<open>We can move an element to the other side of an inequality.\<close>

lemma (in group3) OrderedGroup_ZF_1_L9A:
  assumes A1: "a\<in>G"  "b\<in>G"  "c\<in>G"
  shows "a\<cdot>b \<lsq> c  \<longleftrightarrow> a \<lsq> c\<cdot>b\<inverse>"
proof
  assume "a\<cdot>b \<lsq> c"
  with ordGroupAssum A1 have "a\<cdot>b\<cdot>b\<inverse> \<lsq> c\<cdot>b\<inverse>"
    using OrderedGroup_ZF_1_L1 group0.inverse_in_group IsAnOrdGroup_def
    by simp
  with A1 show "a \<lsq> c\<cdot>b\<inverse>"
    using OrderedGroup_ZF_1_L1 group0.inv_cancel_two by simp
next assume "a \<lsq> c\<cdot>b\<inverse>"
  with ordGroupAssum A1 have "a\<cdot>b \<lsq> c\<cdot>b\<inverse>\<cdot>b"
    using OrderedGroup_ZF_1_L1 group0.inverse_in_group IsAnOrdGroup_def
    by simp
  with A1 show "a\<cdot>b \<lsq> c"
     using OrderedGroup_ZF_1_L1 group0.inv_cancel_two by simp
qed

text\<open>A one side version of the previous lemma with weaker assuptions.\<close>

lemma (in group3) OrderedGroup_ZF_1_L9B:
  assumes A1: "a\<in>G"  "b\<in>G" and A2: "a\<cdot>b\<inverse> \<lsq> c"
  shows "a \<lsq> c\<cdot>b"
proof - 
  from A1 A2 have "a\<in>G"  "b\<inverse>\<in>G"  "c\<in>G"
    using OrderedGroup_ZF_1_L1 group0.inverse_in_group 
      OrderedGroup_ZF_1_L4 by auto
  with A1 A2 show "a \<lsq> c\<cdot>b"
    using OrderedGroup_ZF_1_L9A OrderedGroup_ZF_1_L1 
      group0.group_inv_of_inv by simp
qed

text\<open>We can put en element on the other side of inequality, 
  changing its sign.\<close>

lemma (in group3) OrderedGroup_ZF_1_L9C:
  assumes A1: "a\<in>G"  "b\<in>G" and A2: "c\<lsq>a\<cdot>b"
  shows 
  "c\<cdot>b\<inverse> \<lsq> a"
  "a\<inverse>\<cdot>c \<lsq> b"
proof -
  from ordGroupAssum A1 A2 have
    "c\<cdot>b\<inverse> \<lsq> a\<cdot>b\<cdot>b\<inverse>"
    "a\<inverse>\<cdot>c \<lsq> a\<inverse>\<cdot>(a\<cdot>b)"
    using OrderedGroup_ZF_1_L1 group0.inverse_in_group IsAnOrdGroup_def
    by auto
  with A1 show  
    "c\<cdot>b\<inverse> \<lsq> a"
    "a\<inverse>\<cdot>c \<lsq> b"
    using OrderedGroup_ZF_1_L1 group0.inv_cancel_two
    by auto
qed

text\<open>If an element is greater or equal than another then the difference is 
  nonnegative.\<close>

lemma (in group3) OrderedGroup_ZF_1_L9D: assumes A1: "a\<lsq>b"
  shows "\<one> \<lsq> b\<cdot>a\<inverse>"
proof -
  from A1 have T: "a\<in>G"  "b\<in>G"   "a\<inverse> \<in> G" 
    using OrderedGroup_ZF_1_L4 OrderedGroup_ZF_1_L1 
      group0.inverse_in_group by auto
  with ordGroupAssum A1 have "a\<cdot>a\<inverse> \<lsq> b\<cdot>a\<inverse>"
    using IsAnOrdGroup_def by simp
  with T show "\<one> \<lsq> b\<cdot>a\<inverse>" 
    using OrderedGroup_ZF_1_L1 group0.group0_2_L6
    by simp
qed

text\<open>If an element is greater than another then the difference is 
  positive.\<close>

lemma (in group3) OrderedGroup_ZF_1_L9E: 
  assumes A1: "a\<lsq>b"  "a\<noteq>b"
  shows "\<one> \<lsq> b\<cdot>a\<inverse>"  "\<one> \<noteq> b\<cdot>a\<inverse>"  "b\<cdot>a\<inverse> \<in> G\<^sub>+"
proof -
  from A1 have T: "a\<in>G"  "b\<in>G" using OrderedGroup_ZF_1_L4
    by auto
  from A1 show I: "\<one> \<lsq> b\<cdot>a\<inverse>" using OrderedGroup_ZF_1_L9D
    by simp
  { assume "b\<cdot>a\<inverse> = \<one>" 
    with T have "a=b"
      using OrderedGroup_ZF_1_L1 group0.group0_2_L11A
      by auto
    with A1 have False by simp 
  } then show "\<one> \<noteq> b\<cdot>a\<inverse>" by auto
  then have "b\<cdot>a\<inverse> \<noteq> \<one>" by auto
  with I show "b\<cdot>a\<inverse> \<in> G\<^sub>+" using OrderedGroup_ZF_1_L2A
    by simp
qed

text\<open>If the difference is nonnegative, then $a\leq b$.\<close>

lemma (in group3) OrderedGroup_ZF_1_L9F: 
  assumes A1: "a\<in>G"  "b\<in>G" and A2: "\<one> \<lsq> b\<cdot>a\<inverse>"
  shows "a\<lsq>b"
proof -
  from A1 A2 have "\<one>\<cdot>a \<lsq> b"
    using OrderedGroup_ZF_1_L4 OrderedGroup_ZF_1_L9A
    by simp
  with A1 show "a\<lsq>b" 
    using OrderedGroup_ZF_1_L1 group0.group0_2_L2
    by simp
qed


text\<open>If we increase the middle term in a product, the whole product 
  increases.\<close>

lemma (in group3) OrderedGroup_ZF_1_L10: 
  assumes "a\<in>G"  "b\<in>G" and "c\<lsq>d"
  shows "a\<cdot>c\<cdot>b \<lsq> a\<cdot>d\<cdot>b"
  using ordGroupAssum assms IsAnOrdGroup_def by simp

text\<open>A product of (strictly) positive elements is not the unit.\<close>

lemma (in group3) OrderedGroup_ZF_1_L11: 
  assumes A1: "\<one>\<lsq>a"  "\<one>\<lsq>b"
  and A2: "\<one> \<noteq> a"  "\<one> \<noteq> b"
  shows "\<one> \<noteq> a\<cdot>b"
proof -
  from A1 have T1: "a\<in>G"  "b\<in>G"
    using OrderedGroup_ZF_1_L4 by auto
  { assume "\<one> = a\<cdot>b"
    with A1 T1 have "a\<lsq>\<one>"  "\<one>\<lsq>a"
      using OrderedGroup_ZF_1_L1 group0.group0_2_L9 OrderedGroup_ZF_1_L5AA 
      by auto
    then have "a = \<one>" by (rule group_order_antisym)
    with A2 have False by simp
  } then show "\<one> \<noteq> a\<cdot>b" by auto
qed

text\<open>A product of nonnegative elements is nonnegative.\<close>

lemma (in group3) OrderedGroup_ZF_1_L12:
  assumes A1: "\<one> \<lsq> a"  "\<one> \<lsq> b"
  shows "\<one> \<lsq> a\<cdot>b"
proof -
  from A1 have "\<one>\<cdot>\<one> \<lsq> a\<cdot>b"
    using  OrderedGroup_ZF_1_L5B by simp
  then show "\<one> \<lsq> a\<cdot>b" 
    using OrderedGroup_ZF_1_L1 group0.group0_2_L2 
    by simp
qed

text\<open>If $a$ is not greater than $b$, then $1$ is not greater than
  $b\cdot a^{-1}$.\<close>

lemma (in group3) OrderedGroup_ZF_1_L12A:
  assumes A1: "a\<lsq>b" shows "\<one> \<lsq> b\<cdot>a\<inverse>"
proof -
  from A1 have T: "\<one> \<in> G"  "a\<in>G"  "b\<in>G" 
    using OrderedGroup_ZF_1_L4 OrderedGroup_ZF_1_L1 group0.group0_2_L2
    by auto
  with A1 have "\<one>\<cdot>a \<lsq> b" 
    using OrderedGroup_ZF_1_L1 group0.group0_2_L2
    by simp
  with T show "\<one> \<lsq> b\<cdot>a\<inverse>" using OrderedGroup_ZF_1_L9A
    by simp
qed
  
text\<open>We can move an element to the other side of a strict inequality.\<close>

lemma (in group3) OrderedGroup_ZF_1_L12B:  
  assumes A1: "a\<in>G"  "b\<in>G" and  A2: "a\<cdot>b\<inverse> \<ls> c"
  shows "a \<ls> c\<cdot>b"
proof -
  from A1 A2 have "a\<cdot>b\<inverse>\<cdot>b \<ls> c\<cdot>b"
    using group_strict_ord_transl_inv by auto
  moreover from A1 have "a\<cdot>b\<inverse>\<cdot>b = a"
    using OrderedGroup_ZF_1_L1 group0.inv_cancel_two
    by simp
  ultimately show "a \<ls> c\<cdot>b"
    by auto
qed

(*lemma (in group3) OrderedGroup_ZF_1_L12B:  
  assumes A1: "a\<in>G"  "b\<in>G" and  A2: "a\<cdot>b\<inverse> \<lsq> c"  "a\<cdot>b\<inverse> \<noteq> c"
  shows "a \<lsq> c\<cdot>b"  "a \<noteq> c\<cdot>b"
proof -
  from A1 A2 have "a\<cdot>b\<inverse>\<cdot>b \<lsq> c\<cdot>b"  "a\<cdot>b\<inverse>\<cdot>b \<noteq> c\<cdot>b"
    using group_strict_ord_transl_inv by auto
  moreover from A1 have "a\<cdot>b\<inverse>\<cdot>b = a"
    using OrderedGroup_ZF_1_L1 group0.inv_cancel_two
    by simp
  ultimately show "a \<lsq> c\<cdot>b"  "a \<noteq> c\<cdot>b"
    by auto
qed;*)

text\<open>We can multiply the sides of two inequalities,
  first of them strict and we get a strict inequality.\<close>

lemma (in group3) OrderedGroup_ZF_1_L12C:
  assumes A1: "a\<ls>b" and A2: "c\<lsq>d"
  shows "a\<cdot>c \<ls> b\<cdot>d"
proof -
  from A1 A2 have T: "a\<in>G"  "b\<in>G"  "c\<in>G"  "d\<in>G"
    using OrderedGroup_ZF_1_L4 by auto
  with ordGroupAssum A2 have "a\<cdot>c \<lsq> a\<cdot>d"
    using IsAnOrdGroup_def by simp
  moreover from A1 T have "a\<cdot>d \<ls> b\<cdot>d"
    using group_strict_ord_transl_inv by simp
  ultimately show "a\<cdot>c \<ls> b\<cdot>d"
    by (rule group_strict_ord_transit)
qed
  
text\<open>We can multiply the sides of two inequalities,
  second of them strict and we get a strict inequality.\<close>

lemma (in group3) OrderedGroup_ZF_1_L12D:
  assumes A1: "a\<lsq>b" and A2: "c\<ls>d"
  shows "a\<cdot>c \<ls> b\<cdot>d"
proof -
  from A1 A2 have T: "a\<in>G"  "b\<in>G"  "c\<in>G"  "d\<in>G"
    using OrderedGroup_ZF_1_L4 by auto
  with A2 have "a\<cdot>c \<ls> a\<cdot>d" 
    using group_strict_ord_transl_inv by simp
  moreover from ordGroupAssum A1 T have "a\<cdot>d \<lsq> b\<cdot>d"
     using IsAnOrdGroup_def by simp
   ultimately show "a\<cdot>c \<ls> b\<cdot>d"
     by (rule OrderedGroup_ZF_1_L4A)
qed

subsection\<open>The set of positive elements\<close>

text\<open>In this section we study \<open>G\<^sub>+\<close> - the set of elements that are 
  (strictly) greater than the unit. The most important result is that every
  linearly ordered group can decomposed into $\{1\}$, \<open>G\<^sub>+\<close> and the 
  set of those elements $a\in G$ such that $a^{-1}\in$\<open>G\<^sub>+\<close>. 
  Another property of linearly ordered groups that we prove here is that 
  if \<open>G\<^sub>+\<close>$\neq \emptyset$, then it is infinite. This allows to show 
  that nontrivial linearly ordered groups are infinite.\<close>

text\<open>The positive set is closed under the group operation.\<close>

lemma (in group3) OrderedGroup_ZF_1_L13: shows "G\<^sub>+ {is closed under} P"
proof -
  { fix a b assume "a\<in>G\<^sub>+"  "b\<in>G\<^sub>+"
    then have T1: "\<one> \<lsq> a\<cdot>b"   and "\<one> \<noteq> a\<cdot>b"
      using PositiveSet_def OrderedGroup_ZF_1_L11 OrderedGroup_ZF_1_L12
      by auto
    moreover from T1 have "a\<cdot>b \<in> G"
      using OrderedGroup_ZF_1_L4 by simp
    ultimately have "a\<cdot>b \<in> G\<^sub>+" using PositiveSet_def by simp
  } then show "G\<^sub>+ {is closed under} P" using IsOpClosed_def
    by simp
qed

text\<open>For totally ordered groups every nonunit element is positive or its 
  inverse is positive.\<close>

lemma (in group3) OrderedGroup_ZF_1_L14:
  assumes A1: "r {is total on} G" and A2: "a\<in>G" 
  shows "a=\<one> \<or> a\<in>G\<^sub>+ \<or> a\<inverse>\<in>G\<^sub>+"
proof -
  { assume A3: "a\<noteq>\<one>"
    moreover from A1 A2 have "a\<lsq>\<one> \<or> \<one>\<lsq>a"
      using IsTotal_def OrderedGroup_ZF_1_L1 group0.group0_2_L2
      by simp
    moreover from A3 A2 have T1: "a\<inverse> \<noteq> \<one>"
      using OrderedGroup_ZF_1_L1 group0.group0_2_L8B
      by simp
    ultimately have "a\<inverse>\<in>G\<^sub>+ \<or> a\<in>G\<^sub>+"
      using OrderedGroup_ZF_1_L5A OrderedGroup_ZF_1_L2A
      by auto
  } thus "a=\<one> \<or> a\<in>G\<^sub>+ \<or> a\<inverse>\<in>G\<^sub>+" by auto
qed

text\<open>If an element belongs to the positive set, then it is not the unit
  and its inverse does not belong to the positive set.\<close>

lemma (in group3) OrderedGroup_ZF_1_L15:
   assumes A1: "a\<in>G\<^sub>+"  shows "a\<noteq>\<one>"  "a\<inverse>\<notin>G\<^sub>+"
proof -
  from A1 show T1: "a\<noteq>\<one>" using PositiveSet_def by auto
  { assume "a\<inverse> \<in> G\<^sub>+" 
    with A1 have "a\<lsq>\<one>"  "\<one>\<lsq>a"
      using OrderedGroup_ZF_1_L5AA PositiveSet_def by auto
    then have "a=\<one>" by (rule group_order_antisym)
    with T1 have False by simp
  } then show "a\<inverse>\<notin>G\<^sub>+" by auto
qed

text\<open>If $a^{-1}$ is positive, then $a$ can not be positive or the unit.\<close>

lemma (in group3) OrderedGroup_ZF_1_L16:
  assumes A1: "a\<in>G" and A2: "a\<inverse>\<in>G\<^sub>+" shows "a\<noteq>\<one>"  "a\<notin>G\<^sub>+"
proof -
  from A2 have "a\<inverse>\<noteq>\<one>"  "(a\<inverse>)\<inverse> \<notin> G\<^sub>+"
    using OrderedGroup_ZF_1_L15 by auto
  with A1 show "a\<noteq>\<one>"  "a\<notin>G\<^sub>+"
    using OrderedGroup_ZF_1_L1 group0.group0_2_L8C group0.group_inv_of_inv 
    by auto
qed

text\<open>For linearly ordered groups each element is either the unit, 
  positive or its inverse is positive.\<close>

lemma (in group3) OrdGroup_decomp: 
  assumes A1: "r {is total on} G" and A2: "a\<in>G" 
  shows "Exactly_1_of_3_holds (a=\<one>,a\<in>G\<^sub>+,a\<inverse>\<in>G\<^sub>+)"
proof -
  from A1 A2 have "a=\<one> \<or> a\<in>G\<^sub>+ \<or> a\<inverse>\<in>G\<^sub>+"
    using OrderedGroup_ZF_1_L14 by simp
  moreover from A2 have "a=\<one> \<longrightarrow> (a\<notin>G\<^sub>+ \<and> a\<inverse>\<notin>G\<^sub>+)"
    using OrderedGroup_ZF_1_L1 group0.group_inv_of_one
    PositiveSet_def by simp
  moreover from A2 have "a\<in>G\<^sub>+ \<longrightarrow> (a\<noteq>\<one> \<and> a\<inverse>\<notin>G\<^sub>+)"
    using OrderedGroup_ZF_1_L15 by simp
  moreover from A2 have "a\<inverse>\<in>G\<^sub>+ \<longrightarrow> (a\<noteq>\<one> \<and> a\<notin>G\<^sub>+)"
    using OrderedGroup_ZF_1_L16 by simp
  ultimately show "Exactly_1_of_3_holds (a=\<one>,a\<in>G\<^sub>+,a\<inverse>\<in>G\<^sub>+)"
    by (rule Fol1_L5)
qed

text\<open>A if $a$ is a nonunit element that is not positive, then $a^{-1}$ is 
  is positive. This is useful for some proofs by cases.\<close>

lemma (in group3) OrdGroup_cases:
  assumes A1: "r {is total on} G" and A2: "a\<in>G" 
  and A3: "a\<noteq>\<one>"  "a\<notin>G\<^sub>+"
  shows "a\<inverse> \<in> G\<^sub>+"
proof -
  from A1 A2 have "a=\<one> \<or> a\<in>G\<^sub>+ \<or> a\<inverse>\<in>G\<^sub>+"
    using OrderedGroup_ZF_1_L14 by simp
  with A3 show "a\<inverse> \<in> G\<^sub>+" by auto
qed
  
text\<open>Elements from $G\setminus G_+$ are not greater that the unit.\<close>

lemma (in group3) OrderedGroup_ZF_1_L17:
  assumes A1: "r {is total on} G" and A2: "a \<in> G-G\<^sub>+"
  shows "a\<lsq>\<one>"
proof -
  { assume "a=\<one>"
    with A2 have "a\<lsq>\<one>" using OrderedGroup_ZF_1_L3 by simp }
  moreover
  { assume "a\<noteq>\<one>"
    with A1 A2 have "a\<lsq>\<one>" 
      using PositiveSet_def OrderedGroup_ZF_1_L8A
      by auto }
  ultimately show "a\<lsq>\<one>" by auto
qed

text\<open>The next lemma allows to split proofs that something holds 
  for all $a\in G$ into cases $a=1$, $a\in G_+$, $-a\in G_+$.\<close>

lemma (in group3) OrderedGroup_ZF_1_L18: 
  assumes A1: "r {is total on} G" and A2: "b\<in>G"
  and A3: "Q(\<one>)" and A4: "\<forall>a\<in>G\<^sub>+. Q(a)" and A5: "\<forall>a\<in>G\<^sub>+. Q(a\<inverse>)"
  shows "Q(b)"
proof -
  from A1 A2 A3 A4 A5 have "Q(b) \<or> Q((b\<inverse>)\<inverse>)"
    using OrderedGroup_ZF_1_L14 by auto
  with A2 show "Q(b)" using OrderedGroup_ZF_1_L1 group0.group_inv_of_inv
    by simp
qed

text\<open>All elements greater or equal than an element of \<open>G\<^sub>+\<close>
  belong to \<open>G\<^sub>+\<close>.\<close>

lemma (in group3) OrderedGroup_ZF_1_L19:
  assumes A1: "a \<in> G\<^sub>+" and A2: "a\<lsq>b"
  shows "b \<in> G\<^sub>+"
proof -
  from A1 have I: "\<one>\<lsq>a"  and II: "a\<noteq>\<one>"
    using OrderedGroup_ZF_1_L2A by auto
  from I A2 have "\<one>\<lsq>b" by (rule Group_order_transitive)
  moreover have "b\<noteq>\<one>"
  proof -
    { assume "b=\<one>"
      with I A2 have "\<one>\<lsq>a"  "a\<lsq>\<one>"
	by auto
      then have "\<one>=a" by (rule group_order_antisym)
      with II have False by simp
    } then show "b\<noteq>\<one>" by auto
  qed
  ultimately show "b \<in> G\<^sub>+" 
    using OrderedGroup_ZF_1_L2A by simp
qed

text\<open>The inverse of an element of \<open>G\<^sub>+\<close> cannot be in \<open>G\<^sub>+\<close>.\<close>

lemma (in group3) OrderedGroup_ZF_1_L20:
  assumes A1: "r {is total on} G" and A2: "a \<in> G\<^sub>+" 
  shows "a\<inverse> \<notin> G\<^sub>+"
proof -
  from A2 have "a\<in>G" using PositiveSet_def
    by simp
  with A1 have "Exactly_1_of_3_holds (a=\<one>,a\<in>G\<^sub>+,a\<inverse>\<in>G\<^sub>+)"
    using OrdGroup_decomp by simp
  with A2 show "a\<inverse> \<notin> G\<^sub>+" by (rule Fol1_L7)
qed

text\<open>The set of positive elements of a 
  nontrivial linearly ordered group is not empty.\<close>

lemma (in group3) OrderedGroup_ZF_1_L21:
  assumes A1: "r {is total on} G" and A2: "G \<noteq> {\<one>}"
  shows "G\<^sub>+ \<noteq> 0"
proof -
  have "\<one> \<in> G" using OrderedGroup_ZF_1_L1 group0.group0_2_L2
    by simp
  with A2 obtain a where "a\<in>G"  "a\<noteq>\<one>" by auto
  with A1 have "a\<in>G\<^sub>+ \<or> a\<inverse>\<in>G\<^sub>+" 
    using OrderedGroup_ZF_1_L14 by auto
  then show "G\<^sub>+ \<noteq> 0" by auto
qed

text\<open>If $b\in$\<open>G\<^sub>+\<close>, then $a < a\cdot b$. 
  Multiplying $a$ by a positive elemnt increases $a$.\<close>

lemma (in group3) OrderedGroup_ZF_1_L22:
  assumes A1: "a\<in>G"  "b\<in>G\<^sub>+"
  shows "a\<lsq>a\<cdot>b"  "a \<noteq> a\<cdot>b"  "a\<cdot>b \<in> G"
proof -
  from ordGroupAssum A1 have "a\<cdot>\<one> \<lsq> a\<cdot>b"
    using OrderedGroup_ZF_1_L2A IsAnOrdGroup_def
    by simp
  with A1 show "a\<lsq>a\<cdot>b" 
    using OrderedGroup_ZF_1_L1 group0.group0_2_L2
    by simp
  then show "a\<cdot>b \<in> G"
    using OrderedGroup_ZF_1_L4 by simp
  { from A1 have "a\<in>G"  "b\<in>G"  
      using PositiveSet_def by auto
    moreover assume "a = a\<cdot>b"
    ultimately have "b = \<one>"
      using OrderedGroup_ZF_1_L1 group0.group0_2_L7
      by simp
    with A1 have False using PositiveSet_def
      by simp
  } then show "a \<noteq> a\<cdot>b" by auto
qed

text\<open>If $G$ is a nontrivial linearly ordered hroup, 
  then for every element of $G$ we can find one in \<open>G\<^sub>+\<close> that is
  greater or equal.\<close>

lemma (in group3) OrderedGroup_ZF_1_L23: 
  assumes A1: "r {is total on} G" and A2: "G \<noteq> {\<one>}"
  and A3: "a\<in>G"
  shows "\<exists>b\<in>G\<^sub>+. a\<lsq>b"
proof -
  { assume A4: "a\<in>G\<^sub>+" then have "a\<lsq>a"
      using PositiveSet_def OrderedGroup_ZF_1_L3
      by simp
    with A4 have "\<exists>b\<in>G\<^sub>+. a\<lsq>b" by auto }
  moreover
  { assume "a\<notin>G\<^sub>+"
    with A1 A3 have I: "a\<lsq>\<one>" using OrderedGroup_ZF_1_L17
      by simp
    from A1 A2 obtain b where II: "b\<in>G\<^sub>+" 
      using OrderedGroup_ZF_1_L21 by auto
    then have "\<one>\<lsq>b" using PositiveSet_def by simp
    with I have "a\<lsq>b" by (rule Group_order_transitive)
    with II have "\<exists>b\<in>G\<^sub>+. a\<lsq>b" by auto }
  ultimately show ?thesis by auto
qed

text\<open>The \<open>G\<^sup>+\<close> is \<open>G\<^sub>+\<close> plus the unit.\<close>
lemma (in group3) OrderedGroup_ZF_1_L24: shows "G\<^sup>+ = G\<^sub>+\<union>{\<one>}"
  using OrderedGroup_ZF_1_L2 OrderedGroup_ZF_1_L2A OrderedGroup_ZF_1_L3A
  by auto

text\<open>What is $-G_+$, really?\<close>

lemma (in group3) OrderedGroup_ZF_1_L25: shows 
  "(\<sm>G\<^sub>+) = {a\<inverse>. a\<in>G\<^sub>+}"
  "(\<sm>G\<^sub>+) \<subseteq> G"
proof -
  from ordGroupAssum have I: "GroupInv(G,P) : G\<rightarrow>G"
    using IsAnOrdGroup_def group0_2_T2 by simp
  moreover have "G\<^sub>+ \<subseteq> G" using PositiveSet_def by auto
  ultimately show 
    "(\<sm>G\<^sub>+) = {a\<inverse>. a\<in>G\<^sub>+}"
    "(\<sm>G\<^sub>+) \<subseteq> G"
    using func_imagedef func1_1_L6 by auto
qed

text\<open>If the inverse of $a$ is in \<open>G\<^sub>+\<close>, then $a$ is in the inverse
  of \<open>G\<^sub>+\<close>.\<close>

lemma (in group3) OrderedGroup_ZF_1_L26:
  assumes A1: "a\<in>G" and A2: "a\<inverse> \<in> G\<^sub>+"
  shows "a \<in> (\<sm>G\<^sub>+)"
proof -
  from A1 have "a\<inverse> \<in> G"  "a = (a\<inverse>)\<inverse>" using OrderedGroup_ZF_1_L1 
    group0.inverse_in_group group0.group_inv_of_inv
    by auto
  with A2 show "a \<in> (\<sm>G\<^sub>+)" using OrderedGroup_ZF_1_L25
    by auto
qed

text\<open>If $a$ is in the inverse of  \<open>G\<^sub>+\<close>, 
  then its inverse is in $G_+$.\<close>

lemma (in group3) OrderedGroup_ZF_1_L27:
  assumes "a \<in> (\<sm>G\<^sub>+)"
  shows "a\<inverse> \<in> G\<^sub>+"
  using assms OrderedGroup_ZF_1_L25 PositiveSet_def 
    OrderedGroup_ZF_1_L1 group0.group_inv_of_inv
  by auto

text\<open>A linearly ordered group can be decomposed into $G_+$, $\{1\}$ and
  $-G_+$\<close>

lemma (in group3) OrdGroup_decomp2: 
  assumes A1: "r {is total on} G"
  shows 
  "G = G\<^sub>+ \<union> (\<sm>G\<^sub>+)\<union> {\<one>}"
  "G\<^sub>+\<inter>(\<sm>G\<^sub>+) = 0"
  "\<one> \<notin> G\<^sub>+\<union>(\<sm>G\<^sub>+)"
proof -
  { fix a assume A2: "a\<in>G"
    with A1 have "a\<in>G\<^sub>+ \<or> a\<inverse>\<in>G\<^sub>+ \<or> a=\<one>"
      using OrderedGroup_ZF_1_L14 by auto
    with A2 have "a\<in>G\<^sub>+ \<or> a\<in>(\<sm>G\<^sub>+) \<or> a=\<one>"
      using OrderedGroup_ZF_1_L26 by auto
    then have "a \<in> (G\<^sub>+ \<union> (\<sm>G\<^sub>+)\<union> {\<one>})"
      by auto
  } then have "G \<subseteq> G\<^sub>+ \<union> (\<sm>G\<^sub>+)\<union> {\<one>}"
    by auto
  moreover have "G\<^sub>+ \<union> (\<sm>G\<^sub>+)\<union> {\<one>} \<subseteq> G"
    using OrderedGroup_ZF_1_L25 PositiveSet_def
      OrderedGroup_ZF_1_L1 group0.group0_2_L2
    by auto
  ultimately show "G = G\<^sub>+ \<union> (\<sm>G\<^sub>+)\<union> {\<one>}" by auto
  { let ?A = "G\<^sub>+\<inter>(\<sm>G\<^sub>+)"
    assume "G\<^sub>+\<inter>(\<sm>G\<^sub>+) \<noteq> 0"
    then have "?A\<noteq>0" by simp
    then obtain a where "a\<in>?A" by blast
    then have False using OrderedGroup_ZF_1_L15 OrderedGroup_ZF_1_L27
      by auto
  } then show "G\<^sub>+\<inter>(\<sm>G\<^sub>+) = 0" by auto
  show "\<one> \<notin> G\<^sub>+\<union>(\<sm>G\<^sub>+)"
    using OrderedGroup_ZF_1_L27
      OrderedGroup_ZF_1_L1 group0.group_inv_of_one
      OrderedGroup_ZF_1_L2A by auto
qed

text\<open>If $a\cdot b^{-1}$ is nonnegative, then $b \leq a$. This maybe used to
  recover the order from the set of nonnegative elements and serve as a way
  to define order by prescibing that set (see the "Alternative definitions"
  section).\<close>

lemma (in group3) OrderedGroup_ZF_1_L28:
  assumes A1: "a\<in>G"  "b\<in>G" and A2: "a\<cdot>b\<inverse> \<in> G\<^sup>+"
  shows "b\<lsq>a"
proof -
  from A2 have "\<one> \<lsq> a\<cdot>b\<inverse>" using OrderedGroup_ZF_1_L2
    by simp
  with A1 show "b\<lsq>a" using OrderedGroup_ZF_1_L5K
    by simp
qed

text\<open>A special case of \<open>OrderedGroup_ZF_1_L28\<close> when
  $a\cdot b^{-1}$ is positive.\<close>

corollary (in group3) OrderedGroup_ZF_1_L29:
  assumes A1: "a\<in>G"  "b\<in>G" and A2: "a\<cdot>b\<inverse> \<in> G\<^sub>+"
  shows "b\<lsq>a"  "b\<noteq>a"
proof -
  from A2 have "\<one> \<lsq> a\<cdot>b\<inverse>" and I: "a\<cdot>b\<inverse> \<noteq> \<one>"
    using OrderedGroup_ZF_1_L2A by auto
  with A1 show "b\<lsq>a" using OrderedGroup_ZF_1_L5K
    by simp
  from A1 I show "b\<noteq>a" 
    using OrderedGroup_ZF_1_L1 group0.group0_2_L6
    by auto
qed

text\<open>A bit stronger that \<open>OrderedGroup_ZF_1_L29\<close>, adds
   case when two elements are equal.\<close>

lemma (in group3) OrderedGroup_ZF_1_L30:
  assumes "a\<in>G"  "b\<in>G" and "a=b \<or> b\<cdot>a\<inverse> \<in> G\<^sub>+"
  shows "a\<lsq>b"
  using assms OrderedGroup_ZF_1_L3 OrderedGroup_ZF_1_L29
  by auto

text\<open>A different take on decomposition: we can have $a=b$ or $a<b$
  or $b<a$.\<close>

lemma (in group3) OrderedGroup_ZF_1_L31: 
  assumes A1: "r {is total on} G" and A2: "a\<in>G"  "b\<in>G"
  shows "a=b \<or> (a\<lsq>b \<and> a\<noteq>b) \<or> (b\<lsq>a \<and> b\<noteq>a)"
proof -
  from A2 have "a\<cdot>b\<inverse> \<in> G" using OrderedGroup_ZF_1_L1
    group0.inverse_in_group group0.group_op_closed
    by simp
  with A1 have "a\<cdot>b\<inverse> = \<one> \<or> a\<cdot>b\<inverse> \<in> G\<^sub>+ \<or> (a\<cdot>b\<inverse>)\<inverse> \<in> G\<^sub>+"
    using OrderedGroup_ZF_1_L14 by simp
  moreover
  { assume "a\<cdot>b\<inverse> = \<one>"
    then have "a\<cdot>b\<inverse>\<cdot>b = \<one>\<cdot>b" by simp
    with A2 have "a=b \<or> (a\<lsq>b \<and> a\<noteq>b) \<or> (b\<lsq>a \<and> b\<noteq>a)"
      using OrderedGroup_ZF_1_L1
	group0.inv_cancel_two group0.group0_2_L2 by auto }
  moreover
  { assume "a\<cdot>b\<inverse> \<in> G\<^sub>+"
    with A2 have "a=b \<or> (a\<lsq>b \<and> a\<noteq>b) \<or> (b\<lsq>a \<and> b\<noteq>a)"
      using OrderedGroup_ZF_1_L29 by auto }
  moreover
  { assume "(a\<cdot>b\<inverse>)\<inverse> \<in> G\<^sub>+"
    with A2 have "b\<cdot>a\<inverse> \<in> G\<^sub>+" using OrderedGroup_ZF_1_L1
      group0.group0_2_L12 by simp
    with A2 have "a=b \<or> (a\<lsq>b \<and> a\<noteq>b) \<or> (b\<lsq>a \<and> b\<noteq>a)"
      using OrderedGroup_ZF_1_L29 by auto }
  ultimately show "a=b \<or> (a\<lsq>b \<and> a\<noteq>b) \<or> (b\<lsq>a \<and> b\<noteq>a)"
    by auto
qed

subsection\<open>Intervals and bounded sets\<close>

text\<open>Intervals here are the closed intervals of the form 
 $\{x\in G. a\leq x \leq b \}$.\<close>

text\<open>A bounded set can be translated to put it in  $G^+$ and then it is 
 still bounded above.\<close>

lemma (in group3) OrderedGroup_ZF_2_L1: 
  assumes A1: "\<forall>g\<in>A. L\<lsq>g \<and> g\<lsq>M"
  and A2: "S = RightTranslation(G,P,L\<inverse>)" 
  and A3: "a \<in> S``(A)"
  shows "a \<lsq> M\<cdot>L\<inverse>"   "\<one>\<lsq>a"
proof -
  from A3 have "A\<noteq>0" using func1_1_L13A by fast
  then obtain g where "g\<in>A" by auto
  with A1 have T1: "L\<in>G" "M\<in>G" "L\<inverse>\<in>G" 
    using OrderedGroup_ZF_1_L4 OrderedGroup_ZF_1_L1 
    group0.inverse_in_group by auto
  with A2 have "S : G\<rightarrow>G" using OrderedGroup_ZF_1_L1 group0.group0_5_L1
    by simp
  moreover from A1 have T2: "A\<subseteq>G" using OrderedGroup_ZF_1_L4 by auto
  ultimately have "S``(A) = {S`(b). b\<in>A}" using func_imagedef
    by simp
  with A3 obtain b where T3: "b\<in>A" "a = S`(b)" by auto
  with A1 ordGroupAssum T1 have "b\<cdot>L\<inverse>\<lsq>M\<cdot>L\<inverse>" "L\<cdot>L\<inverse>\<lsq>b\<cdot>L\<inverse>"
    using IsAnOrdGroup_def by auto
  with T3 A2 T1 T2 show "a\<lsq>M\<cdot>L\<inverse>" "\<one>\<lsq>a"
    using OrderedGroup_ZF_1_L1 group0.group0_5_L2 group0.group0_2_L6 
    by auto
qed

text\<open>Every bounded set is an image of a subset of an interval that starts at 
  $1$.\<close>

lemma (in group3) OrderedGroup_ZF_2_L2:
  assumes A1: "IsBounded(A,r)" 
  shows "\<exists>B.\<exists>g\<in>G\<^sup>+.\<exists>T\<in>G\<rightarrow>G. A = T``(B) \<and> B \<subseteq> Interval(r,\<one>,g)"
proof - 
  { assume A2: "A=0" 
    let ?B = "0"
    let ?g = "\<one>"
    let ?T = "ConstantFunction(G,\<one>)"
    have "?g\<in>G\<^sup>+" using OrderedGroup_ZF_1_L3A by simp
    moreover have "?T : G\<rightarrow>G"
      using func1_3_L1 OrderedGroup_ZF_1_L1 group0.group0_2_L2 by simp
    moreover from A2 have "A = T``(?B)" by simp
    moreover have "?B \<subseteq> Interval(r,\<one>,?g)" by simp
    ultimately have
      "\<exists>B.\<exists>g\<in>G\<^sup>+.\<exists>T\<in>G\<rightarrow>G. A = T``(B) \<and> B \<subseteq> Interval(r,\<one>,g)"
      by auto }
  moreover
  { assume A3: "A\<noteq>0"
    with A1 have "\<exists>L. \<forall>x\<in>A. L\<lsq>x" and "\<exists>U. \<forall>x\<in>A. x\<lsq>U"
      using IsBounded_def IsBoundedBelow_def IsBoundedAbove_def 
      by auto
    then obtain L U where D1: "\<forall>x\<in>A. L\<lsq>x \<and> x\<lsq>U "
      by auto
    with A3 have T1: "A\<subseteq>G" using OrderedGroup_ZF_1_L4 by auto
    from A3 obtain a where "a\<in>A" by auto
    with D1 have T2: "L\<lsq>a" "a\<lsq>U" by auto
    then have T3: "L\<in>G" "L\<inverse>\<in> G" "U\<in>G" 
      using OrderedGroup_ZF_1_L4 OrderedGroup_ZF_1_L1 
	group0.inverse_in_group by auto
    let ?T = "RightTranslation(G,P,L)"
    let ?B = "RightTranslation(G,P,L\<inverse>)``(A)"
    let ?g = "U\<cdot>L\<inverse>"
    have "?g\<in>G\<^sup>+"
    proof -
      from T2 have "L\<lsq>U" using Group_order_transitive by fast
      with ordGroupAssum T3 have "L\<cdot>L\<inverse>\<lsq>?g" 
	using IsAnOrdGroup_def by simp
      with T3 show ?thesis using OrderedGroup_ZF_1_L1 group0.group0_2_L6
	OrderedGroup_ZF_1_L2 by simp
    qed
    moreover from T3 have "?T : G\<rightarrow>G"
      using OrderedGroup_ZF_1_L1 group0.group0_5_L1
      by simp
    moreover have "A = ?T``(?B)"
    proof -
      from T3 T1 have "?T``(?B) = {a\<cdot>L\<inverse>\<cdot>L. a\<in>A}"
	using OrderedGroup_ZF_1_L1 group0.group0_5_L6
	by simp
      moreover from T3 T1 have "\<forall>a\<in>A. a\<cdot>L\<inverse>\<cdot>L = a\<cdot>(L\<inverse>\<cdot>L)"
	using OrderedGroup_ZF_1_L1 group0.group_oper_assoc by auto
      ultimately have "?T``(?B) = {a\<cdot>(L\<inverse>\<cdot>L). a\<in>A}" by simp
      with T3 have "?T``(?B) = {a\<cdot>\<one>. a\<in>A}"
	using OrderedGroup_ZF_1_L1 group0.group0_2_L6 by simp
      moreover from T1 have "\<forall>a\<in>A. a\<cdot>\<one>=a"
	using OrderedGroup_ZF_1_L1 group0.group0_2_L2 by auto
      ultimately show ?thesis by simp
    qed
    moreover have "?B \<subseteq> Interval(r,\<one>,?g)"
    proof
      fix y assume A4: "y \<in> ?B"
      let ?S = "RightTranslation(G,P,L\<inverse>)"
      from D1 have T4: "\<forall>x\<in>A. L\<lsq>x \<and> x\<lsq>U" by simp
      moreover have T5: "?S = RightTranslation(G,P,L\<inverse>)" 
	by simp 
      moreover from A4 have T6: "y \<in> ?S``(A)" by simp
      ultimately have "y\<lsq>U\<cdot>L\<inverse>" using OrderedGroup_ZF_2_L1
	by blast
      moreover from T4 T5 T6 have "\<one>\<lsq>y" by (rule OrderedGroup_ZF_2_L1)
      ultimately show "y \<in> Interval(r,\<one>,?g)" using Interval_def by auto
    qed
    ultimately have
      "\<exists>B.\<exists>g\<in>G\<^sup>+.\<exists>T\<in>G\<rightarrow>G. A = T``(B) \<and> B \<subseteq> Interval(r,\<one>,g)"
      by auto }
  ultimately show ?thesis by auto
qed
      
text\<open>If every interval starting at $1$ is finite, then every bounded set is 
  finite. I find it interesting that this does not require the group to be 
  linearly ordered (the order to be total).\<close>

theorem (in group3) OrderedGroup_ZF_2_T1:
  assumes A1: "\<forall>g\<in>G\<^sup>+. Interval(r,\<one>,g) \<in> Fin(G)"
  and A2: "IsBounded(A,r)" 
  shows "A \<in> Fin(G)"
proof -
  from A2 have
    "\<exists>B.\<exists>g\<in>G\<^sup>+.\<exists>T\<in>G\<rightarrow>G. A = T``(B) \<and> B \<subseteq> Interval(r,\<one>,g)"
    using OrderedGroup_ZF_2_L2 by simp
  then obtain B g T where D1: "g\<in>G\<^sup>+" "B \<subseteq> Interval(r,\<one>,g)" 
    and D2: "T : G\<rightarrow>G" "A = T``(B)" by auto
  from D1 A1 have "B\<in>Fin(G)" using Fin_subset_lemma by blast
  with D2 show ?thesis using Finite1_L6A by simp
qed

text\<open>In linearly ordered groups finite sets are bounded.\<close>

theorem (in group3) ord_group_fin_bounded:
  assumes "r {is total on} G" and "B\<in>Fin(G)" 
  shows "IsBounded(B,r)"
  using ordGroupAssum assms IsAnOrdGroup_def IsPartOrder_def Finite_ZF_1_T1
  by simp

text\<open>For nontrivial linearly ordered groups  if for every element $G$ 
  we can find one in $A$ 
  that is greater or equal (not necessarily strictly greater), then $A$
  can neither be finite nor bounded above.\<close>

lemma (in group3) OrderedGroup_ZF_2_L2A:
  assumes A1: "r {is total on} G" and A2: "G \<noteq> {\<one>}"
  and A3: "\<forall>a\<in>G. \<exists>b\<in>A. a\<lsq>b"
  shows 
  "\<forall>a\<in>G. \<exists>b\<in>A. a\<noteq>b \<and> a\<lsq>b"
  "\<not>IsBoundedAbove(A,r)"
  "A \<notin> Fin(G)"
proof -
  { fix a
    from A1 A2 obtain c where "c \<in> G\<^sub>+"
      using OrderedGroup_ZF_1_L21 by auto
    moreover assume "a\<in>G"
    ultimately have 
      "a\<cdot>c \<in> G"  and I: "a \<ls> a\<cdot>c"
      using OrderedGroup_ZF_1_L22 by auto
    with A3 obtain b where II: "b\<in>A"  and III: "a\<cdot>c \<lsq> b"
      by auto
    moreover from I III have "a\<ls>b" by (rule OrderedGroup_ZF_1_L4A)
    ultimately have "\<exists>b\<in>A. a\<noteq>b \<and> a\<lsq>b" by auto
  } thus "\<forall>a\<in>G. \<exists>b\<in>A. a\<noteq>b \<and> a\<lsq>b" by simp
  with ordGroupAssum A1 show 
    "\<not>IsBoundedAbove(A,r)"
    "A \<notin> Fin(G)"
    using IsAnOrdGroup_def IsPartOrder_def 
    OrderedGroup_ZF_1_L1A Order_ZF_3_L14 Finite_ZF_1_1_L3
    by auto
qed


text\<open>Nontrivial linearly ordered groups are infinite. Recall 
  that \<open>Fin(A)\<close> is the collection of finite subsets of $A$. 
  In this lemma we show that $G\notin$ \<open>Fin(G)\<close>, that is that
  $G$ is not a finite subset of itself. This is a way of saying that $G$ 
  is infinite. We also show that for nontrivial linearly ordered groups 
  \<open>G\<^sub>+\<close> is infinite.\<close>

theorem (in group3) Linord_group_infinite:
  assumes A1: "r {is total on} G" and A2: "G \<noteq> {\<one>}"
  shows 
  "G\<^sub>+ \<notin> Fin(G)"
  "G \<notin> Fin(G)"
proof -
  from A1 A2 show I: "G\<^sub>+ \<notin> Fin(G)"
    using OrderedGroup_ZF_1_L23 OrderedGroup_ZF_2_L2A
    by simp
  { assume "G \<in> Fin(G)"
    moreover have "G\<^sub>+ \<subseteq> G" using PositiveSet_def by auto
    ultimately have "G\<^sub>+ \<in> Fin(G)" using Fin_subset_lemma
      by blast
    with I have False by simp
  } then show "G \<notin> Fin(G)" by auto
qed
  
text\<open>A property of nonempty subsets of linearly ordered groups that don't
  have a maximum: for any element in such subset we can find one that
  is strictly greater.\<close>

lemma (in group3) OrderedGroup_ZF_2_L2B:
  assumes A1: "r {is total on} G" and A2: "A\<subseteq>G" and 
  A3: "\<not>HasAmaximum(r,A)" and A4: "x\<in>A"
  shows "\<exists>y\<in>A. x\<ls>y"
proof -
  from ordGroupAssum assms have
    "antisym(r)"
    "r {is total on} G"
    "A\<subseteq>G"  "\<not>HasAmaximum(r,A)"  "x\<in>A"
    using IsAnOrdGroup_def IsPartOrder_def
    by auto
  then have "\<exists>y\<in>A. \<langle>x,y\<rangle> \<in> r \<and> y\<noteq>x"
    using Order_ZF_4_L16 by simp
  then show "\<exists>y\<in>A. x\<ls>y" by auto
qed
    
text\<open>In linearly ordered groups $G\setminus G_+$ is bounded above.\<close>

lemma (in group3) OrderedGroup_ZF_2_L3:
  assumes A1: "r {is total on} G" shows "IsBoundedAbove(G-G\<^sub>+,r)"
proof -
  from A1 have "\<forall>a\<in>G-G\<^sub>+. a\<lsq>\<one>"
    using OrderedGroup_ZF_1_L17 by simp
  then show "IsBoundedAbove(G-G\<^sub>+,r)" 
    using IsBoundedAbove_def by auto
qed

text\<open>In linearly ordered groups if $A\cap G_+$ is finite, 
  then $A$ is bounded above.\<close>

lemma (in group3) OrderedGroup_ZF_2_L4:
  assumes A1: "r {is total on} G" and A2: "A\<subseteq>G" 
  and A3: "A \<inter> G\<^sub>+ \<in> Fin(G)"
  shows "IsBoundedAbove(A,r)"
proof -
  have "A \<inter> (G-G\<^sub>+) \<subseteq> G-G\<^sub>+" by auto
  with A1 have "IsBoundedAbove(A \<inter> (G-G\<^sub>+),r)"
    using OrderedGroup_ZF_2_L3 Order_ZF_3_L13
    by blast
  moreover from A1 A3 have "IsBoundedAbove(A \<inter> G\<^sub>+,r)"
    using ord_group_fin_bounded IsBounded_def 
    by simp
  moreover from A1 ordGroupAssum have
    "r {is total on} G"  "trans(r)"  "r\<subseteq>G\<times>G"
    using IsAnOrdGroup_def IsPartOrder_def by auto
  ultimately have "IsBoundedAbove(A \<inter> (G-G\<^sub>+) \<union> A \<inter> G\<^sub>+,r)"
    using Order_ZF_3_L3 by simp
  moreover from A2 have "A = A \<inter> (G-G\<^sub>+) \<union> A \<inter> G\<^sub>+"
    by auto
  ultimately show  "IsBoundedAbove(A,r)" by simp
qed

text\<open>If a set $-A\subseteq G$ is bounded above, then $A$ is bounded below.\<close>

lemma (in group3) OrderedGroup_ZF_2_L5:
  assumes A1: "A\<subseteq>G" and A2: "IsBoundedAbove(\<sm>A,r)"
  shows "IsBoundedBelow(A,r)"
proof -
  { assume "A = 0" then have "IsBoundedBelow(A,r)"
      using IsBoundedBelow_def by auto }
  moreover
  { assume A3: "A\<noteq>0"
    from ordGroupAssum have I: "GroupInv(G,P) : G\<rightarrow>G"
      using IsAnOrdGroup_def group0_2_T2 by simp
    with A1 A2 A3 obtain u where D: "\<forall>a\<in>(\<sm>A). a\<lsq>u"
      using func1_1_L15A IsBoundedAbove_def by auto
    { fix b assume "b\<in>A"
      with A1 I D have "b\<inverse> \<lsq> u" and T: "b\<in>G"
	using func_imagedef by auto
      then have "u\<inverse>\<lsq>(b\<inverse>)\<inverse>" using OrderedGroup_ZF_1_L5
	by simp
      with T have "u\<inverse>\<lsq>b"
	using OrderedGroup_ZF_1_L1 group0.group_inv_of_inv
	by simp
    } then have "\<forall>b\<in>A. \<langle>u\<inverse>,b\<rangle> \<in> r" by simp
    then have "IsBoundedBelow(A,r)"
      using Order_ZF_3_L9 by blast }
  ultimately show ?thesis by auto
qed

text\<open>If $a\leq b$, then the image of the interval $a..b$ by any function is
  nonempty.\<close>

lemma (in group3) OrderedGroup_ZF_2_L6: 
  assumes "a\<lsq>b" and "f:G\<rightarrow>G"
  shows "f``(Interval(r,a,b)) \<noteq> 0"
  using ordGroupAssum assms OrderedGroup_ZF_1_L4 
    Order_ZF_2_L6 Order_ZF_2_L2A 
    IsAnOrdGroup_def IsPartOrder_def func1_1_L15A
  by auto
  
end
