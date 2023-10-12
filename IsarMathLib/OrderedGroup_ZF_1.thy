(*    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2005 - 2009  Slawomir Kolodynski

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

section \<open>More on ordered groups\<close>

theory OrderedGroup_ZF_1 imports OrderedGroup_ZF

begin 

text\<open>In this theory we continue the \<open>OrderedGroup_ZF\<close> 
  theory development.\<close>

subsection\<open>Absolute value and the triangle inequality\<close>

text\<open>The goal of this section is to prove the triangle inequality for 
  ordered groups.\<close>

text\<open>Absolute value maps $G$ into $G$.\<close>

lemma (in group3) OrderedGroup_ZF_3_L1: 
  shows "AbsoluteValue(G,P,r) : G\<rightarrow>G"
proof -
  let ?f = "id(G\<^sup>+)"
  let ?g = "restrict(GroupInv(G,P),G-G\<^sup>+)"
  have "?f : G\<^sup>+\<rightarrow>G\<^sup>+" using id_type by simp
  then have "?f : G\<^sup>+\<rightarrow>G" using OrderedGroup_ZF_1_L4E fun_weaken_type
    by blast
  moreover have "?g : G-G\<^sup>+\<rightarrow>G"
  proof -
    from ordGroupAssum have "GroupInv(G,P) : G\<rightarrow>G" 
      using IsAnOrdGroup_def group0_2_T2 by simp
    moreover have "G-G\<^sup>+ \<subseteq> G" by auto
    ultimately show ?thesis using restrict_type2 by simp
  qed
  moreover have "G\<^sup>+\<inter>(G-G\<^sup>+) = 0" by blast
  ultimately have "?f \<union> ?g : G\<^sup>+\<union>(G-G\<^sup>+)\<rightarrow>G\<union>G" 
    by (rule fun_disjoint_Un)
  moreover have "G\<^sup>+\<union>(G-G\<^sup>+) = G" using OrderedGroup_ZF_1_L4E
    by auto
  ultimately show "AbsoluteValue(G,P,r) : G\<rightarrow>G" 
    using AbsoluteValue_def by simp
qed

text\<open>If $a\in G^+$, then $|a| = a$.\<close>

lemma (in group3) OrderedGroup_ZF_3_L2:
  assumes A1: "a\<in>G\<^sup>+" shows "\<bar>a\<bar> = a"
proof -
  from ordGroupAssum have "GroupInv(G,P) : G\<rightarrow>G"
    using IsAnOrdGroup_def group0_2_T2 by simp
  with A1 show ?thesis using
    func1_1_L1 OrderedGroup_ZF_1_L4E fun_disjoint_apply1
    AbsoluteValue_def id_conv by simp
qed

text\<open>The absolute value of the unit is the unit. In the 
  additive totation that would be $|0| = 0$.\<close>

lemma (in group3) OrderedGroup_ZF_3_L2A: 
  shows "\<bar>\<one>\<bar> = \<one>" using OrderedGroup_ZF_1_L3A OrderedGroup_ZF_3_L2
  by simp

text\<open>If $a$ is positive, then $|a| = a$.\<close>

lemma (in group3) OrderedGroup_ZF_3_L2B:
  assumes "a\<in>G\<^sub>+" shows "\<bar>a\<bar> = a"
  using assms PositiveSet_def Nonnegative_def OrderedGroup_ZF_3_L2
  by auto

text\<open>If $a\in G\setminus G^+$, then $|a| = a^{-1}$.\<close>

lemma (in group3) OrderedGroup_ZF_3_L3:
   assumes A1: "a \<in> G-G\<^sup>+" shows "\<bar>a\<bar> = a\<inverse>"
proof -
  have "domain(id(G\<^sup>+)) = G\<^sup>+"
    using id_type func1_1_L1 by auto
  with A1 show ?thesis using fun_disjoint_apply2 AbsoluteValue_def
    restrict by simp
qed

text\<open>For elements that not greater than the unit, the absolute value is
  the inverse.\<close>

lemma (in group3) OrderedGroup_ZF_3_L3A:
  assumes A1: "a\<lsq>\<one>" 
  shows "\<bar>a\<bar> = a\<inverse>"
proof -
  { assume "a=\<one>" then have "\<bar>a\<bar> = a\<inverse>" 
      using OrderedGroup_ZF_3_L2A OrderedGroup_ZF_1_L1 group0.group_inv_of_one
      by simp }
  moreover
  { assume "a\<noteq>\<one>" 
    with A1 have "\<bar>a\<bar> = a\<inverse>" using OrderedGroup_ZF_1_L4C OrderedGroup_ZF_3_L3
      by simp }
  ultimately show "\<bar>a\<bar> = a\<inverse>" by blast
qed

text\<open>In linearly ordered groups the absolute value of any element 
  is in $G^+$.\<close>

lemma (in group3) OrderedGroup_ZF_3_L3B: 
  assumes A1: "r {is total on} G" and A2: "a\<in>G"
  shows "\<bar>a\<bar> \<in> G\<^sup>+"
proof -
  { assume "a \<in> G\<^sup>+" then have "\<bar>a\<bar> \<in> G\<^sup>+" 
      using OrderedGroup_ZF_3_L2 by simp }
  moreover
  { assume "a \<notin> G\<^sup>+" 
    with A1 A2 have "\<bar>a\<bar> \<in> G\<^sup>+" using OrderedGroup_ZF_3_L3
      OrderedGroup_ZF_1_L6 by simp }
  ultimately show "\<bar>a\<bar> \<in> G\<^sup>+" by blast
qed
  
text\<open>For linearly ordered groups (where the order is total), the absolute
  value maps the group into the positive set.\<close>

lemma (in group3) OrderedGroup_ZF_3_L3C:
  assumes A1: "r {is total on} G"
  shows "AbsoluteValue(G,P,r) : G\<rightarrow>G\<^sup>+"
proof-
  have "AbsoluteValue(G,P,r) : G\<rightarrow>G" using OrderedGroup_ZF_3_L1
    by simp
  moreover from A1 have T2: 
    "\<forall>g\<in>G. AbsoluteValue(G,P,r)`(g)  \<in> G\<^sup>+" 
    using OrderedGroup_ZF_3_L3B by simp
  ultimately show ?thesis by (rule func1_1_L1A)
qed

text\<open>If the absolute value is the unit, then the elemnent is the unit.\<close>

lemma (in group3) OrderedGroup_ZF_3_L3D: 
  assumes A1: "a\<in>G" and A2: "\<bar>a\<bar> = \<one>"
  shows "a = \<one>"
proof -
  { assume "a \<in> G\<^sup>+" 
    with A2 have "a = \<one>" using OrderedGroup_ZF_3_L2 by simp }
  moreover
  { assume "a \<notin> G\<^sup>+"
    with A1 A2 have "a = \<one>" using 
      OrderedGroup_ZF_3_L3 OrderedGroup_ZF_1_L1 group0.group0_2_L8A
      by auto }
  ultimately show "a = \<one>" by blast
qed

text\<open>In linearly ordered groups the unit is not greater than the absolute 
  value of any element.\<close>

lemma (in group3) OrderedGroup_ZF_3_L3E: 
  assumes "r {is total on} G" and "a\<in>G"
  shows "\<one> \<lsq> \<bar>a\<bar>"
  using assms OrderedGroup_ZF_3_L3B OrderedGroup_ZF_1_L2 by simp

text\<open>If $b$ is greater than both $a$ and $a^{-1}$, then $b$ is greater than
  $|a|$.\<close>

lemma (in group3) OrderedGroup_ZF_3_L4: 
  assumes A1: "a\<lsq>b" and A2: "a\<inverse>\<lsq> b" 
  shows "\<bar>a\<bar>\<lsq> b"
proof -
  { assume "a\<in>G\<^sup>+" 
    with A1 have "\<bar>a\<bar>\<lsq> b" using OrderedGroup_ZF_3_L2 by simp }
  moreover
  { assume "a\<notin>G\<^sup>+"
    with A1 A2 have "\<bar>a\<bar>\<lsq> b" 
      using OrderedGroup_ZF_1_L4 OrderedGroup_ZF_3_L3 by simp }
  ultimately show "\<bar>a\<bar>\<lsq> b" by blast
qed

text\<open>In linearly ordered groups $a\leq |a|$.\<close>

lemma (in group3) OrderedGroup_ZF_3_L5: 
  assumes A1: "r {is total on} G" and A2: "a\<in>G"
  shows "a \<lsq> \<bar>a\<bar>"
proof -
  { assume "a \<in> G\<^sup>+"
    with A2 have "a \<lsq> \<bar>a\<bar>" 
      using OrderedGroup_ZF_3_L2 OrderedGroup_ZF_1_L3 by simp }
  moreover
  { assume "a \<notin> G\<^sup>+"
    with A1 A2 have "a \<lsq> \<bar>a\<bar>"
      using OrderedGroup_ZF_3_L3B OrderedGroup_ZF_1_L4B by simp }
  ultimately show "a \<lsq> \<bar>a\<bar>" by blast
qed

text\<open> $a^{-1}\leq |a|$ (in additive notation it would be $-a\leq |a|$.\<close>

lemma (in group3) OrderedGroup_ZF_3_L6: 
  assumes A1: "a\<in>G" shows "a\<inverse> \<lsq> \<bar>a\<bar>"
proof -
  { assume "a \<in> G\<^sup>+"
    then have T1: "\<one>\<lsq>a" and T2: "\<bar>a\<bar> = a" using OrderedGroup_ZF_1_L2  
      OrderedGroup_ZF_3_L2 by auto
    then have "a\<inverse>\<lsq>\<one>\<inverse>" using OrderedGroup_ZF_1_L5 by simp
    then have T3: "a\<inverse>\<lsq>\<one>" 
      using OrderedGroup_ZF_1_L1 group0.group_inv_of_one by simp
    from T3 T1 have "a\<inverse>\<lsq>a" by (rule Group_order_transitive)
    with T2 have "a\<inverse> \<lsq> \<bar>a\<bar>" by simp }
  moreover 
  { assume A2: "a \<notin> G\<^sup>+"
    from A1 have "\<bar>a\<bar> \<in> G" 
      using OrderedGroup_ZF_3_L1 apply_funtype by auto
    with ordGroupAssum have "\<bar>a\<bar> \<lsq> \<bar>a\<bar>" 
      using IsAnOrdGroup_def IsPartOrder_def refl_def by simp
    with A1 A2 have "a\<inverse> \<lsq> \<bar>a\<bar>" using OrderedGroup_ZF_3_L3 by simp }
  ultimately show "a\<inverse> \<lsq> \<bar>a\<bar>" by blast
qed

text\<open>Some inequalities about the product of two elements of a linearly 
  ordered group and its absolute value.\<close>

lemma (in group3) OrderedGroup_ZF_3_L6A:
  assumes "r {is total on} G" and "a\<in>G"  "b\<in>G"
  shows
  "a\<cdot>b \<lsq>\<bar>a\<bar>\<cdot>\<bar>b\<bar>"
  "a\<cdot>b\<inverse> \<lsq>\<bar>a\<bar>\<cdot>\<bar>b\<bar>"
  "a\<inverse>\<cdot>b \<lsq>\<bar>a\<bar>\<cdot>\<bar>b\<bar>"
  "a\<inverse>\<cdot>b\<inverse> \<lsq>\<bar>a\<bar>\<cdot>\<bar>b\<bar>"
  using assms OrderedGroup_ZF_3_L5 OrderedGroup_ZF_3_L6
    OrderedGroup_ZF_1_L5B by auto

text\<open> $|a^{-1}|\leq |a|$.\<close>

lemma (in group3) OrderedGroup_ZF_3_L7:
  assumes "r {is total on} G" and "a\<in>G"
  shows "\<bar>a\<inverse>\<bar>\<lsq>\<bar>a\<bar>"
  using assms OrderedGroup_ZF_3_L5 OrderedGroup_ZF_1_L1 group0.group_inv_of_inv
    OrderedGroup_ZF_3_L6 OrderedGroup_ZF_3_L4 by simp

text\<open>$|a^{-1}| = |a|$.\<close>

lemma (in group3) OrderedGroup_ZF_3_L7A:
  assumes A1: "r {is total on} G" and A2: "a\<in>G"
  shows "\<bar>a\<inverse>\<bar> = \<bar>a\<bar>"
proof -
  from A2 have "a\<inverse>\<in>G" using OrderedGroup_ZF_1_L1 group0.inverse_in_group
    by simp
  with A1 have "\<bar>(a\<inverse>)\<inverse>\<bar> \<lsq> \<bar>a\<inverse>\<bar>" using OrderedGroup_ZF_3_L7 by simp
  with A1 A2 have "\<bar>a\<inverse>\<bar> \<lsq> \<bar>a\<bar>"  "\<bar>a\<bar> \<lsq> \<bar>a\<inverse>\<bar>"
    using OrderedGroup_ZF_1_L1 group0.group_inv_of_inv OrderedGroup_ZF_3_L7
    by auto
  then show ?thesis by (rule group_order_antisym)
qed

text\<open> $|a\cdot b^{-1}| = |b\cdot a^{-1}|$. It doesn't look so strange in the 
  additive notation: $|a-b| = |b-a|$.\<close>

lemma (in group3) OrderedGroup_ZF_3_L7B:
  assumes A1: "r {is total on} G" and A2: "a\<in>G" "b\<in>G"
  shows "\<bar>a\<cdot>b\<inverse>\<bar> = \<bar>b\<cdot>a\<inverse>\<bar>"
proof -
  from A1 A2 have "\<bar>(a\<cdot>b\<inverse>)\<inverse>\<bar> = \<bar>a\<cdot>b\<inverse>\<bar>" using
    OrderedGroup_ZF_1_L1 group0.inverse_in_group group0.group0_2_L1 
    monoid0.group0_1_L1 OrderedGroup_ZF_3_L7A by simp
  moreover from A2 have "(a\<cdot>b\<inverse>)\<inverse> =  b\<cdot>a\<inverse>" 
    using OrderedGroup_ZF_1_L1 group0.group0_2_L12 by simp
  ultimately show ?thesis by simp
qed

text\<open>Triangle inequality for linearly ordered abelian groups. 
  It would be nice to drop commutativity or give an example that shows we
  can't do that.\<close>

theorem (in group3) OrdGroup_triangle_ineq:
  assumes A1: "P {is commutative on} G" 
  and A2: "r {is total on} G" and A3: "a\<in>G"  "b\<in>G" 
  shows "\<bar>a\<cdot>b\<bar> \<lsq> \<bar>a\<bar>\<cdot>\<bar>b\<bar>"
proof -
  from A1 A2 A3 have 
    "a \<lsq> \<bar>a\<bar>" "b \<lsq> \<bar>b\<bar>" "a\<inverse> \<lsq> \<bar>a\<bar>" "b\<inverse> \<lsq> \<bar>b\<bar>"
    using OrderedGroup_ZF_3_L5 OrderedGroup_ZF_3_L6 by auto
  then have "a\<cdot>b \<lsq> \<bar>a\<bar>\<cdot>\<bar>b\<bar>" "a\<inverse>\<cdot>b\<inverse> \<lsq> \<bar>a\<bar>\<cdot>\<bar>b\<bar>"
    using OrderedGroup_ZF_1_L5B by auto
  with A1 A3 show "\<bar>a\<cdot>b\<bar> \<lsq> \<bar>a\<bar>\<cdot>\<bar>b\<bar>"
    using OrderedGroup_ZF_1_L1 group0.group_inv_of_two IsCommutative_def 
    OrderedGroup_ZF_3_L4 by simp
qed

text\<open>We can multiply the sides of an inequality with absolute value.\<close>

lemma (in group3) OrderedGroup_ZF_3_L7C:
  assumes "P {is commutative on} G" 
  and "r {is total on} G" "a\<in>G" "b\<in>G"
  and "\<bar>a\<bar> \<lsq> c"  "\<bar>b\<bar> \<lsq> d"
  shows "\<bar>a\<cdot>b\<bar> \<lsq> c\<cdot>d"
proof -
  from assms(1,2,3,4) have "\<bar>a\<cdot>b\<bar> \<lsq> \<bar>a\<bar>\<cdot>\<bar>b\<bar>"
    using OrdGroup_triangle_ineq by simp
  moreover from assms(5,6) have "\<bar>a\<bar>\<cdot>\<bar>b\<bar> \<lsq> c\<cdot>d"
    using OrderedGroup_ZF_1_L5B by simp
  ultimately show ?thesis by (rule Group_order_transitive)
qed

text\<open>A version of the \<open>OrderedGroup_ZF_3_L7C\<close> 
  but with multiplying by the inverse.\<close>

lemma (in group3) OrderedGroup_ZF_3_L7CA:
  assumes "P {is commutative on} G" 
  and "r {is total on} G" and "a\<in>G"  "b\<in>G"
  and "\<bar>a\<bar> \<lsq> c"  "\<bar>b\<bar> \<lsq> d"
  shows "\<bar>a\<cdot>b\<inverse>\<bar> \<lsq> c\<cdot>d"
  using assms OrderedGroup_ZF_1_L1 group0.inverse_in_group
  OrderedGroup_ZF_3_L7A OrderedGroup_ZF_3_L7C by simp

text\<open>Triangle inequality with three integers.\<close>

lemma (in group3) OrdGroup_triangle_ineq3:
  assumes A1: "P {is commutative on} G" 
  and A2: "r {is total on} G" and A3: "a\<in>G"  "b\<in>G"  "c\<in>G" 
  shows "\<bar>a\<cdot>b\<cdot>c\<bar> \<lsq> \<bar>a\<bar>\<cdot>\<bar>b\<bar>\<cdot>\<bar>c\<bar>"
proof -
  from A3 have T: "a\<cdot>b \<in> G"  "\<bar>c\<bar> \<in> G"
    using OrderedGroup_ZF_1_L1 group0.group_op_closed
      OrderedGroup_ZF_3_L1 apply_funtype by auto
  with A1 A2 A3 have "\<bar>a\<cdot>b\<cdot>c\<bar> \<lsq> \<bar>a\<cdot>b\<bar>\<cdot>\<bar>c\<bar>"
    using OrdGroup_triangle_ineq by simp
  moreover from ordGroupAssum A1 A2 A3 T have
    "\<bar>a\<cdot>b\<bar>\<cdot>\<bar>c\<bar> \<lsq> \<bar>a\<bar>\<cdot>\<bar>b\<bar>\<cdot>\<bar>c\<bar>"
    using OrdGroup_triangle_ineq IsAnOrdGroup_def by simp
  ultimately show "\<bar>a\<cdot>b\<cdot>c\<bar> \<lsq> \<bar>a\<bar>\<cdot>\<bar>b\<bar>\<cdot>\<bar>c\<bar>"
    by (rule Group_order_transitive)
qed

text\<open>Some variants of the triangle inequality.\<close>

lemma (in group3) OrderedGroup_ZF_3_L7D:
  assumes A1: "P {is commutative on} G" 
  and A2: "r {is total on} G" and A3: "a\<in>G"  "b\<in>G"
  and A4: "\<bar>a\<cdot>b\<inverse>\<bar> \<lsq> c"
  shows 
  "\<bar>a\<bar> \<lsq> c\<cdot>\<bar>b\<bar>" 
  "\<bar>a\<bar> \<lsq> \<bar>b\<bar>\<cdot>c"
  "c\<inverse>\<cdot>a \<lsq> b"
  "a\<cdot>c\<inverse> \<lsq> b"
  "a \<lsq> b\<cdot>c"
proof -
  from A3 A4 have 
    T: "a\<cdot>b\<inverse> \<in> G"  "\<bar>b\<bar> \<in> G"  "c\<in>G"  "c\<inverse> \<in> G"
    using OrderedGroup_ZF_1_L1 
      group0.inverse_in_group group0.group0_2_L1 monoid0.group0_1_L1
      OrderedGroup_ZF_3_L1 apply_funtype  OrderedGroup_ZF_1_L4 
    by auto
  from A3 have "\<bar>a\<bar> = \<bar>a\<cdot>b\<inverse>\<cdot>b\<bar>"
    using OrderedGroup_ZF_1_L1 group0.inv_cancel_two
    by simp
  with A1 A2 A3 T have "\<bar>a\<bar> \<lsq> \<bar>a\<cdot>b\<inverse>\<bar>\<cdot>\<bar>b\<bar>"
    using OrdGroup_triangle_ineq by simp
  with T A4 show "\<bar>a\<bar> \<lsq> c\<cdot>\<bar>b\<bar>" using OrderedGroup_ZF_1_L5C
    by blast
  with T A1 show "\<bar>a\<bar> \<lsq> \<bar>b\<bar>\<cdot>c"
    using IsCommutative_def by simp
  from A2 T have "a\<cdot>b\<inverse> \<lsq> \<bar>a\<cdot>b\<inverse>\<bar>"
    using OrderedGroup_ZF_3_L5 by simp
  moreover note A4
  ultimately have I: "a\<cdot>b\<inverse> \<lsq> c"
    by (rule Group_order_transitive)
  with A3 show "c\<inverse>\<cdot>a \<lsq> b"
    using OrderedGroup_ZF_1_L5H by simp
  with A1 A3 T show "a\<cdot>c\<inverse> \<lsq> b"
    using IsCommutative_def by simp
  from A1 A3 T I show "a \<lsq> b\<cdot>c"
    using OrderedGroup_ZF_1_L5H IsCommutative_def
    by auto
qed

text\<open>Some more variants of the triangle inequality.\<close>

lemma (in group3) OrderedGroup_ZF_3_L7E:
  assumes A1: "P {is commutative on} G" 
  and A2: "r {is total on} G" and A3: "a\<in>G"  "b\<in>G"
  and A4: "\<bar>a\<cdot>b\<inverse>\<bar> \<lsq> c"
  shows "b\<cdot>c\<inverse> \<lsq> a"
proof -
  from A3 have "a\<cdot>b\<inverse> \<in> G"
    using OrderedGroup_ZF_1_L1 
      group0.inverse_in_group group0.group_op_closed
    by auto
  with A2 have "\<bar>(a\<cdot>b\<inverse>)\<inverse>\<bar> = \<bar>a\<cdot>b\<inverse>\<bar>"
    using OrderedGroup_ZF_3_L7A by simp
  moreover from A3 have "(a\<cdot>b\<inverse>)\<inverse> = b\<cdot>a\<inverse>"
    using OrderedGroup_ZF_1_L1 group0.group0_2_L12
    by simp
  ultimately have "\<bar>b\<cdot>a\<inverse>\<bar> = \<bar>a\<cdot>b\<inverse>\<bar>"
    by simp
  with A1 A2 A3 A4 show "b\<cdot>c\<inverse> \<lsq> a"
    using OrderedGroup_ZF_3_L7D by simp
qed

text\<open>An application of the triangle inequality with four group
  elements.\<close>

lemma (in group3) OrderedGroup_ZF_3_L7F:
  assumes A1: "P {is commutative on} G" 
  and A2: "r {is total on} G" and 
  A3: "a\<in>G"  "b\<in>G"  "c\<in>G"  "d\<in>G"
  shows "\<bar>a\<cdot>c\<inverse>\<bar> \<lsq> \<bar>a\<cdot>b\<bar>\<cdot>\<bar>c\<cdot>d\<bar>\<cdot>\<bar>b\<cdot>d\<inverse>\<bar>"
proof -
  from A3 have T:
    "a\<cdot>c\<inverse> \<in> G"  "a\<cdot>b \<in> G"  "c\<cdot>d \<in> G"  "b\<cdot>d\<inverse> \<in> G"
    "(c\<cdot>d)\<inverse> \<in> G"  "(b\<cdot>d\<inverse>)\<inverse> \<in> G"
    using OrderedGroup_ZF_1_L1 
      group0.inverse_in_group group0.group_op_closed
    by auto
  with A1 A2 have "\<bar>(a\<cdot>b)\<cdot>(c\<cdot>d)\<inverse>\<cdot>(b\<cdot>d\<inverse>)\<inverse>\<bar> \<lsq> \<bar>a\<cdot>b\<bar>\<cdot>\<bar>(c\<cdot>d)\<inverse>\<bar>\<cdot>\<bar>(b\<cdot>d\<inverse>)\<inverse>\<bar>"
    using OrdGroup_triangle_ineq3 by simp
  moreover from A2 T have "\<bar>(c\<cdot>d)\<inverse>\<bar> =\<bar>c\<cdot>d\<bar>" and "\<bar>(b\<cdot>d\<inverse>)\<inverse>\<bar> = \<bar>b\<cdot>d\<inverse>\<bar>"
    using OrderedGroup_ZF_3_L7A by auto
  moreover from A1 A3 have "(a\<cdot>b)\<cdot>(c\<cdot>d)\<inverse>\<cdot>(b\<cdot>d\<inverse>)\<inverse> = a\<cdot>c\<inverse>"
    using OrderedGroup_ZF_1_L1 group0.group0_4_L8
    by simp
  ultimately show "\<bar>a\<cdot>c\<inverse>\<bar> \<lsq> \<bar>a\<cdot>b\<bar>\<cdot>\<bar>c\<cdot>d\<bar>\<cdot>\<bar>b\<cdot>d\<inverse>\<bar>"
    by simp
qed
    
text\<open>$|a|\leq L$ implies $L^{-1} \leq a$
  (it would be $-L \leq a$ in the additive notation).\<close>

lemma (in group3) OrderedGroup_ZF_3_L8:
  assumes A1:  "a\<in>G" and A2: "\<bar>a\<bar>\<lsq>L"
   shows 
  "L\<inverse>\<lsq>a"
proof -
  from A1 have I: "a\<inverse> \<lsq> \<bar>a\<bar>" using OrderedGroup_ZF_3_L6 by simp
  from I A2 have "a\<inverse> \<lsq> L" by (rule Group_order_transitive)
  then have "L\<inverse>\<lsq>(a\<inverse>)\<inverse>" using OrderedGroup_ZF_1_L5 by simp
  with A1 show "L\<inverse>\<lsq>a" using OrderedGroup_ZF_1_L1 group0.group_inv_of_inv
    by simp
qed

text\<open>In linearly ordered groups $|a|\leq L$ implies $a \leq L$
  (it would be $a \leq L$ in the additive notation).\<close>

lemma (in group3) OrderedGroup_ZF_3_L8A:
  assumes A1: "r {is total on} G" 
  and A2: "a\<in>G" and A3: "\<bar>a\<bar>\<lsq>L"
  shows 
  "a\<lsq>L"
  "\<one>\<lsq>L"
proof -
  from A1 A2 have I: "a \<lsq> \<bar>a\<bar>" using OrderedGroup_ZF_3_L5 by simp
  from I A3 show "a\<lsq>L" by (rule Group_order_transitive)
  from A1 A2 A3 have "\<one> \<lsq> \<bar>a\<bar>"  "\<bar>a\<bar>\<lsq>L"
     using OrderedGroup_ZF_3_L3B OrderedGroup_ZF_1_L2 by auto
   then show "\<one>\<lsq>L" by (rule Group_order_transitive)
qed

text\<open>A somewhat generalized version of the above lemma.\<close>

lemma (in group3) OrderedGroup_ZF_3_L8B:
  assumes A1: "a\<in>G" and A2: "\<bar>a\<bar>\<lsq>L" and A3: "\<one>\<lsq>c"
  shows "(L\<cdot>c)\<inverse> \<lsq> a"
proof -
  from A1 A2 A3 have "c\<inverse>\<cdot>L\<inverse> \<lsq> \<one>\<cdot>a"
    using OrderedGroup_ZF_3_L8 OrderedGroup_ZF_1_L5AB
    OrderedGroup_ZF_1_L5B by simp
  with A1 A2 A3 show "(L\<cdot>c)\<inverse> \<lsq> a"
    using OrderedGroup_ZF_1_L4 OrderedGroup_ZF_1_L1
      group0.group_inv_of_two group0.group0_2_L2
    by simp
qed

text\<open>If $b$ is between $a$ and $a\cdot c$, then $b\cdot a^{-1}\leq c$.\<close>

lemma (in group3) OrderedGroup_ZF_3_L8C:
  assumes A1: "a\<lsq>b" and A2: "c\<in>G" and A3: "b\<lsq>c\<cdot>a"
  shows "\<bar>b\<cdot>a\<inverse>\<bar> \<lsq> c"
proof -
  from A1 A2 A3 have "b\<cdot>a\<inverse> \<lsq> c"
    using OrderedGroup_ZF_1_L9C OrderedGroup_ZF_1_L4
    by simp
  moreover have "(b\<cdot>a\<inverse>)\<inverse> \<lsq> c"
  proof -
    from A1 have T: "a\<in>G"  "b\<in>G"
      using OrderedGroup_ZF_1_L4 by auto
    with A1 have "a\<cdot>b\<inverse> \<lsq> \<one>"
      using OrderedGroup_ZF_1_L9 by blast
    moreover
    from A1 A3 have "a\<lsq>c\<cdot>a"
      by (rule Group_order_transitive)
    with ordGroupAssum T have "a\<cdot>a\<inverse> \<lsq> c\<cdot>a\<cdot>a\<inverse>"
      using OrderedGroup_ZF_1_L1 group0.inverse_in_group
      IsAnOrdGroup_def by simp
    with T A2 have "\<one> \<lsq> c"
      using OrderedGroup_ZF_1_L1 
	group0.group0_2_L6 group0.inv_cancel_two
      by simp
    ultimately have "a\<cdot>b\<inverse> \<lsq> c"
      by (rule Group_order_transitive)
    with T show "(b\<cdot>a\<inverse>)\<inverse> \<lsq> c"
      using OrderedGroup_ZF_1_L1 group0.group0_2_L12
      by simp
  qed
  ultimately show "\<bar>b\<cdot>a\<inverse>\<bar> \<lsq> c"
    using OrderedGroup_ZF_3_L4 by simp
qed
  
text\<open>For linearly ordered groups if the absolute values of elements in a set
  are bounded, then the set is bounded.\<close>

lemma (in group3) OrderedGroup_ZF_3_L9:
  assumes A1: "r {is total on} G"
  and A2: "A\<subseteq>G" and A3: "\<forall>a\<in>A. \<bar>a\<bar> \<lsq> L"
  shows "IsBounded(A,r)"
proof -
  from A1 A2 A3 have 
    "\<forall>a\<in>A. a\<lsq>L"  "\<forall>a\<in>A. L\<inverse>\<lsq>a" 
    using OrderedGroup_ZF_3_L8 OrderedGroup_ZF_3_L8A by auto
  then show "IsBounded(A,r)" using
    IsBoundedAbove_def IsBoundedBelow_def IsBounded_def
    by auto
qed

text\<open>A slightly more general version of the previous lemma, stating the same
  fact for a set defined by separation.\<close>

lemma (in group3) OrderedGroup_ZF_3_L9A:
  assumes A1: "r {is total on} G"
  and A2: "\<forall>x\<in>X. b(x)\<in>G \<and> \<bar>b(x)\<bar>\<lsq>L"
  shows "IsBounded({b(x). x\<in>X},r)"
proof -
  from A2 have "{b(x). x\<in>X} \<subseteq> G" "\<forall>a\<in>{b(x). x\<in>X}. \<bar>a\<bar> \<lsq> L" 
    by auto
  with A1 show ?thesis using OrderedGroup_ZF_3_L9 by blast
qed

text\<open>A special form of the previous lemma stating a similar fact for an
  image of a set by a function with values in a linearly ordered group.\<close>

lemma (in group3) OrderedGroup_ZF_3_L9B:
  assumes A1: "r {is total on} G"
  and A2: "f:X\<rightarrow>G" and A3: "A\<subseteq>X"
  and A4: "\<forall>x\<in>A. \<bar>f`(x)\<bar> \<lsq> L"
  shows "IsBounded(f``(A),r)"
proof -
  from A2 A3 A4 have "\<forall>x\<in>A. f`(x) \<in> G \<and>  \<bar>f`(x)\<bar> \<lsq> L"
    using apply_funtype by auto
  with A1 have  "IsBounded({f`(x). x\<in>A},r)"
    by (rule OrderedGroup_ZF_3_L9A)
  with A2 A3 show "IsBounded(f``(A),r)"
    using func_imagedef by simp
qed
  
text\<open>For linearly ordered groups if $l\leq a\leq u$ then 
  $|a|$ is smaller than the greater of $|l|,|u|$.\<close>

lemma (in group3) OrderedGroup_ZF_3_L10:
  assumes A1: "r {is total on} G"
  and A2: "l\<lsq>a"  "a\<lsq>u" 
  shows 
  "\<bar>a\<bar> \<lsq> GreaterOf(r,\<bar>l\<bar>,\<bar>u\<bar>)"
proof -
  from A2 have T1: "\<bar>l\<bar> \<in> G" "\<bar>a\<bar> \<in> G" "\<bar>u\<bar> \<in> G"
    using OrderedGroup_ZF_1_L4 OrderedGroup_ZF_3_L1 apply_funtype
    by auto
  { assume A3: "a\<in>G\<^sup>+"
    with A2 have "\<one>\<lsq>a" "a\<lsq>u" 
      using OrderedGroup_ZF_1_L2 by auto
    then have "\<one>\<lsq>u" by (rule Group_order_transitive)
    with A2 A3 have "\<bar>a\<bar>\<lsq>\<bar>u\<bar>" 
      using OrderedGroup_ZF_1_L2 OrderedGroup_ZF_3_L2 by simp
    moreover from A1 T1 have "\<bar>u\<bar> \<lsq> GreaterOf(r,\<bar>l\<bar>,\<bar>u\<bar>)"
      using Order_ZF_3_L2 by simp
    ultimately have "\<bar>a\<bar> \<lsq> GreaterOf(r,\<bar>l\<bar>,\<bar>u\<bar>)"
      by (rule Group_order_transitive) }
  moreover
  { assume A4: "a\<notin>G\<^sup>+"
    with A2 have T2: 
      "l\<in>G" "\<bar>l\<bar> \<in> G" "\<bar>a\<bar> \<in> G" "\<bar>u\<bar> \<in> G" "a \<in> G-G\<^sup>+"
      using OrderedGroup_ZF_1_L4 OrderedGroup_ZF_3_L1 apply_funtype
      by auto
    with A2 have "l \<in> G-G\<^sup>+" using OrderedGroup_ZF_1_L4D by fast
    with T2 A2 have "\<bar>a\<bar> \<lsq> \<bar>l\<bar>" 
      using OrderedGroup_ZF_3_L3 OrderedGroup_ZF_1_L5
      by simp
    moreover from A1 T2 have "\<bar>l\<bar> \<lsq> GreaterOf(r,\<bar>l\<bar>,\<bar>u\<bar>)"
      using Order_ZF_3_L2 by simp 
    ultimately have "\<bar>a\<bar> \<lsq> GreaterOf(r,\<bar>l\<bar>,\<bar>u\<bar>)"
      by (rule Group_order_transitive) }
  ultimately show ?thesis by blast
qed

text\<open>For linearly ordered groups if a set is bounded then the absolute 
  values are bounded.\<close>

lemma (in group3) OrderedGroup_ZF_3_L10A:
  assumes A1: "r {is total on} G"
  and A2: "IsBounded(A,r)"
  shows "\<exists>L. \<forall>a\<in>A. \<bar>a\<bar> \<lsq> L"
proof -
  { assume "A = 0" then have ?thesis by auto }
  moreover
  { assume A3: "A\<noteq>0" 
    with A2 have "\<exists>u. \<forall>g\<in>A. g\<lsq>u" and "\<exists>l.\<forall>g\<in>A. l\<lsq>g"
      using IsBounded_def IsBoundedAbove_def IsBoundedBelow_def
      by auto
    then obtain u l where "\<forall>g\<in>A. l\<lsq>g \<and>  g\<lsq>u" 
      by auto
    with A1 have "\<forall>a\<in>A. \<bar>a\<bar> \<lsq> GreaterOf(r,\<bar>l\<bar>,\<bar>u\<bar>)"
      using OrderedGroup_ZF_3_L10 by simp
    then have ?thesis by auto }
  ultimately show ?thesis by blast
qed
  
text\<open>A slightly more general version of the previous lemma, stating the same
  fact for a set defined by separation.\<close>

lemma (in group3) OrderedGroup_ZF_3_L11:
  assumes "r {is total on} G"
  and "IsBounded({b(x).x\<in>X},r)"
  shows "\<exists>L. \<forall>x\<in>X. \<bar>b(x)\<bar> \<lsq> L"
  using assms OrderedGroup_ZF_3_L10A by blast

text\<open>Absolute values of elements of a finite image of a nonempty set are 
  bounded by an element of the group.\<close>

lemma (in group3) OrderedGroup_ZF_3_L11A:
  assumes A1: "r {is total on} G" 
  and A2: "X\<noteq>0" and A3: "{b(x). x\<in>X} \<in> Fin(G)"
  shows "\<exists>L\<in>G. \<forall>x\<in>X. \<bar>b(x)\<bar> \<lsq> L"
proof -
  from A1 A3 have "\<exists>L. \<forall>x\<in>X. \<bar>b(x)\<bar> \<lsq> L"
     using  ord_group_fin_bounded OrderedGroup_ZF_3_L11
     by simp
  then obtain L where I: "\<forall>x\<in>X. \<bar>b(x)\<bar> \<lsq> L"
    using OrderedGroup_ZF_3_L11 by auto
  from A2 obtain x where "x\<in>X" by auto
  with I show ?thesis using OrderedGroup_ZF_1_L4
    by blast
qed

text\<open>In totally ordered groups the absolute value of a 
  nonunit element is in \<open>G\<^sub>+\<close>.\<close>

lemma (in group3) OrderedGroup_ZF_3_L12:
  assumes A1: "r {is total on} G" 
  and A2: "a\<in>G"  and A3: "a\<noteq>\<one>"
  shows "\<bar>a\<bar> \<in> G\<^sub>+"
proof -
  from A1 A2 have "\<bar>a\<bar> \<in> G"  "\<one> \<lsq> \<bar>a\<bar>" 
    using OrderedGroup_ZF_3_L1 apply_funtype
      OrderedGroup_ZF_3_L3B OrderedGroup_ZF_1_L2 
    by auto
  moreover from A2 A3 have "\<bar>a\<bar> \<noteq> \<one>"
    using OrderedGroup_ZF_3_L3D by auto
  ultimately show "\<bar>a\<bar> \<in> G\<^sub>+"
    using PositiveSet_def by auto
qed

subsection\<open>Maximum absolute value of a set\<close>

text\<open>Quite often when considering inequalities we prefer to talk about
  the absolute values instead of raw elements of a set. This section formalizes
  some material that is useful for that.\<close>

text\<open>If a set has a maximum and minimum, then the greater of the 
  absolute value of the maximum and minimum belongs to the image of the set 
  by the absolute value function.\<close>

lemma (in group3) OrderedGroup_ZF_4_L1:
  assumes "A \<subseteq> G"
  and "HasAmaximum(r,A)" "HasAminimum(r,A)"
  and "M = GreaterOf(r,\<bar>Minimum(r,A)\<bar>,\<bar>Maximum(r,A)\<bar>)"
  shows "M \<in> AbsoluteValue(G,P,r)``(A)"
  using ordGroupAssum assms IsAnOrdGroup_def IsPartOrder_def 
    Order_ZF_4_L3 Order_ZF_4_L4 OrderedGroup_ZF_3_L1 
    func_imagedef GreaterOf_def by auto

text\<open>If a set has a maximum and minimum, then the greater of the 
  absolute value of the maximum and minimum bounds absolute values of all 
  elements of the set.\<close>

lemma (in group3) OrderedGroup_ZF_4_L2: 
  assumes A1: "r {is total on} G"
  and A2: "HasAmaximum(r,A)"  "HasAminimum(r,A)"
  and A3: "a\<in>A"
  shows "\<bar>a\<bar>\<lsq> GreaterOf(r,\<bar>Minimum(r,A)\<bar>,\<bar>Maximum(r,A)\<bar>)" 
proof -
  from ordGroupAssum A2 A3 have 
    "Minimum(r,A)\<lsq> a" "a\<lsq> Maximum(r,A)" 
    using IsAnOrdGroup_def IsPartOrder_def Order_ZF_4_L3 Order_ZF_4_L4
    by auto
  with A1 show ?thesis by (rule OrderedGroup_ZF_3_L10)
qed

text\<open>If a set has a maximum and minimum, then the greater of the 
  absolute value of the maximum and minimum bounds absolute values of all 
  elements of the set. In this lemma the absolute values of ekements of a 
  set are represented as the elements of the image of the set by the absolute
  value function.\<close>

lemma (in group3) OrderedGroup_ZF_4_L3: 
  assumes "r {is total on} G" and "A \<subseteq> G"
  and "HasAmaximum(r,A)" "HasAminimum(r,A)"
  and "b \<in> AbsoluteValue(G,P,r)``(A)"
  shows "b\<lsq> GreaterOf(r,\<bar>Minimum(r,A)\<bar>,\<bar>Maximum(r,A)\<bar>)"
  using assms OrderedGroup_ZF_3_L1 func_imagedef OrderedGroup_ZF_4_L2
  by auto

text\<open>If a set has a maximum and minimum, then the set of absolute values 
  also has a maximum.\<close>

lemma (in group3) OrderedGroup_ZF_4_L4:
  assumes A1: "r {is total on} G" and A2: "A \<subseteq> G"
  and A3: "HasAmaximum(r,A)" "HasAminimum(r,A)"
  shows "HasAmaximum(r,AbsoluteValue(G,P,r)``(A))"
proof -
  let ?M = "GreaterOf(r,\<bar>Minimum(r,A)\<bar>,\<bar>Maximum(r,A)\<bar>)"
  from A2 A3 have "?M \<in> AbsoluteValue(G,P,r)``(A)"
    using OrderedGroup_ZF_4_L1 by simp
  moreover from A1 A2 A3 have 
    "\<forall>b \<in> AbsoluteValue(G,P,r)``(A). b \<lsq> ?M"
    using OrderedGroup_ZF_4_L3 by simp
  ultimately show ?thesis using HasAmaximum_def by auto
qed

text\<open>If a set has a maximum and a minimum, then all absolute values are
  bounded by the maximum of the set of absolute values.\<close>

lemma (in group3) OrderedGroup_ZF_4_L5:
  assumes A1: "r {is total on} G" and A2: "A \<subseteq> G"
  and A3: "HasAmaximum(r,A)" "HasAminimum(r,A)"
  and A4: "a\<in>A"
  shows "\<bar>a\<bar> \<lsq> Maximum(r,AbsoluteValue(G,P,r)``(A))"
proof -
  from A2 A4 have "\<bar>a\<bar> \<in> AbsoluteValue(G,P,r)``(A)" 
    using OrderedGroup_ZF_3_L1 func_imagedef by auto
  with ordGroupAssum A1 A2 A3 show ?thesis using 
    IsAnOrdGroup_def IsPartOrder_def OrderedGroup_ZF_4_L4
    Order_ZF_4_L3 by simp
qed

subsection\<open>Alternative definitions\<close>

text\<open>Sometimes it is usful to define the order by prescibing the set
  of positive or nonnegative elements. This section deals with two such 
  definitions. One takes a subset $H$ of $G$ that is closed under the group
  operation, $1\notin H$ and for every $a\in H$ we have either $a\in H$ or 
  $a^{-1}\in H$. Then the order is defined as $a\leq b$ iff $a=b$ or 
  $a^{-1}b \in H$. For abelian groups this makes a linearly ordered group. 
  We will refer to order defined this way in the comments as the order 
  defined by a positive set. The context used in this section is the 
  \<open>group0\<close> context defined in \<open>Group_ZF\<close> theory. Recall that
  \<open>f\<close> in that context denotes the group operation (unlike in the 
  previous sections where the group operation was denoted \<open>P\<close>.\<close>

text\<open>The order defined by a positive set is the same as the order defined by
  a nonnegative set.\<close>

lemma (in group0) OrderedGroup_ZF_5_L1:
  assumes A1: "r = {p \<in> G\<times>G. fst(p) = snd(p) \<or> fst(p)\<inverse>\<cdot>snd(p) \<in> H}"
  shows "\<langle>a,b\<rangle> \<in> r  \<longleftrightarrow> a\<in>G \<and> b\<in>G \<and> a\<inverse>\<cdot>b \<in> H \<union> {\<one>}"
proof
  assume "\<langle>a,b\<rangle> \<in> r"
  with A1 show "a\<in>G \<and> b\<in>G \<and> a\<inverse>\<cdot>b \<in> H \<union> {\<one>}" 
    using group0_2_L6 by auto
next assume "a\<in>G \<and> b\<in>G \<and> a\<inverse>\<cdot>b \<in> H \<union> {\<one>}"
   then have "a\<in>G \<and> b\<in>G \<and> b=(a\<inverse>)\<inverse> \<or>  a\<in>G \<and> b\<in>G \<and> a\<inverse>\<cdot>b \<in> H"
    using  inverse_in_group group0_2_L9 by auto
  with A1 show "\<langle>a,b\<rangle> \<in> r" using group_inv_of_inv
    by auto
qed
  
text\<open>The relation defined by a positive set is antisymmetric.\<close>

lemma (in group0) OrderedGroup_ZF_5_L2:
  assumes A1: "r = {p \<in> G\<times>G. fst(p) = snd(p) \<or> fst(p)\<inverse>\<cdot>snd(p) \<in> H}"
  and A2: "\<forall>a\<in>G. a\<noteq>\<one> \<longrightarrow> (a\<in>H) Xor (a\<inverse>\<in>H)"
  shows "antisym(r)"
proof -
  { fix a b assume A3: "\<langle>a,b\<rangle> \<in> r"  "\<langle>b,a\<rangle> \<in> r"
    with A1 have T: "a\<in>G"  "b\<in>G" by auto
    { assume A4: "a\<noteq>b"
      with A1 A3 have "a\<inverse>\<cdot>b \<in> G"  "a\<inverse>\<cdot>b \<in> H"  "(a\<inverse>\<cdot>b)\<inverse> \<in> H"
	using inverse_in_group group0_2_L1 monoid0.group0_1_L1 group0_2_L12
	by auto
      with A2 have "a\<inverse>\<cdot>b = \<one>" using Xor_def by auto
      with T A4 have False using group0_2_L11 by auto
    } then have "a=b" by auto
  } then show "antisym(r)" by (rule antisymI)
qed

text\<open>The relation defined by a positive set is transitive.\<close>

lemma (in group0) OrderedGroup_ZF_5_L3:
  assumes A1: "r = {p \<in> G\<times>G. fst(p) = snd(p) \<or> fst(p)\<inverse>\<cdot>snd(p) \<in> H}"
  and A2: "H\<subseteq>G"  "H {is closed under} P"
  shows "trans(r)"
proof -
  { fix a b c assume "\<langle>a,b\<rangle> \<in> r"  "\<langle>b,c\<rangle> \<in> r"
    with A1 have 
      "a\<in>G \<and> b\<in>G \<and> a\<inverse>\<cdot>b \<in> H \<union> {\<one>}"
      "b\<in>G \<and> c\<in>G \<and> b\<inverse>\<cdot>c \<in> H \<union> {\<one>}"
      using OrderedGroup_ZF_5_L1 by auto
    with A2 have 
      I: "a\<in>G"  "b\<in>G"  "c\<in>G"
      and "(a\<inverse>\<cdot>b)\<cdot>(b\<inverse>\<cdot>c) \<in>  H \<union> {\<one>}"
      using inverse_in_group group0_2_L17 IsOpClosed_def
      by auto
    moreover from I have "a\<inverse>\<cdot>c = (a\<inverse>\<cdot>b)\<cdot>(b\<inverse>\<cdot>c)"
      by (rule group0_2_L14A)
    ultimately have "\<langle>a,c\<rangle> \<in> G\<times>G"  "a\<inverse>\<cdot>c  \<in>  H \<union> {\<one>}"
      by auto
    with A1 have "\<langle>a,c\<rangle> \<in> r" using OrderedGroup_ZF_5_L1
      by auto
  } then have "\<forall> a b c. \<langle>a, b\<rangle> \<in> r \<and> \<langle>b, c\<rangle> \<in> r \<longrightarrow> \<langle>a, c\<rangle> \<in> r"
    by blast
  then show  "trans(r)" by (rule Fol1_L2)
qed

text\<open>The relation defined by a positive set is translation invariant.
  With our definition this step requires the group to be abelian.\<close>

lemma (in group0) OrderedGroup_ZF_5_L4:
  assumes A1: "r = {p \<in> G\<times>G. fst(p) = snd(p) \<or> fst(p)\<inverse>\<cdot>snd(p) \<in> H}"
  and A2: "P {is commutative on} G"
  and A3: "\<langle>a,b\<rangle> \<in> r"  and A4: "c\<in>G"
  shows "\<langle>a\<cdot>c,b\<cdot>c\<rangle> \<in> r \<and> \<langle>c\<cdot>a,c\<cdot>b\<rangle> \<in> r"
proof
  from A1 A3 A4 have 
    I: "a\<in>G"  "b\<in>G"  "a\<cdot>c \<in> G"  "b\<cdot>c \<in> G"
    and II: "a\<inverse>\<cdot>b \<in> H \<union> {\<one>}"
    using OrderedGroup_ZF_5_L1 group_op_closed 
    by auto
  with A2 A4 have "(a\<cdot>c)\<inverse>\<cdot>(b\<cdot>c) \<in> H \<union> {\<one>}"
    using group0_4_L6D by simp
  with A1 I show "\<langle>a\<cdot>c,b\<cdot>c\<rangle> \<in> r" using  OrderedGroup_ZF_5_L1
    by auto
  with A2 A4 I show "\<langle>c\<cdot>a,c\<cdot>b\<rangle> \<in> r"
    using IsCommutative_def by simp
qed
  
text\<open>If $H\subseteq G$ is closed under the group operation
  $1\notin H$ and for every $a\in H$ we have either $a\in H$ or 
  $a^{-1}\in H$, then the relation "$\leq$" defined by 
  $a\leq b \Leftrightarrow a^{-1}b \in H$ orders the group $G$.
  In such order $H$ may be the set of positive or nonnegative
  elements.\<close>

lemma (in group0) OrderedGroup_ZF_5_L5: 
  assumes A1: "P {is commutative on} G"
  and A2: "H\<subseteq>G"  "H {is closed under} P"
  and A3: "\<forall>a\<in>G. a\<noteq>\<one> \<longrightarrow> (a\<in>H) Xor (a\<inverse>\<in>H)"
  and A4: "r = {p \<in> G\<times>G. fst(p) = snd(p) \<or> fst(p)\<inverse>\<cdot>snd(p) \<in> H}"
  shows 
  "IsAnOrdGroup(G,P,r)"
  "r {is total on} G"
  "Nonnegative(G,P,r) = PositiveSet(G,P,r) \<union> {\<one>}"
proof -
  from groupAssum A2 A3 A4 have 
    "IsAgroup(G,P)"  "r \<subseteq> G\<times>G"  "IsPartOrder(G,r)"
    using refl_def OrderedGroup_ZF_5_L2 OrderedGroup_ZF_5_L3
      IsPartOrder_def by auto
  moreover from A1 A4 have 
    "\<forall>g\<in>G. \<forall>a b. \<langle> a,b\<rangle> \<in> r \<longrightarrow> \<langle>a\<cdot>g,b\<cdot>g\<rangle> \<in> r \<and> \<langle>g\<cdot>a,g\<cdot>b\<rangle> \<in> r"
    using OrderedGroup_ZF_5_L4 by blast
  ultimately show "IsAnOrdGroup(G,P,r)" 
    using IsAnOrdGroup_def by simp
  then show "Nonnegative(G,P,r) = PositiveSet(G,P,r) \<union> {\<one>}"
    using group3_def group3.OrderedGroup_ZF_1_L24
    by simp
  { fix a b 
    assume T: "a\<in>G"  "b\<in>G"
    then have T1: "a\<inverse>\<cdot>b \<in> G"
      using inverse_in_group group_op_closed by simp
    { assume "\<langle> a,b\<rangle> \<notin> r"
      with A4 T have I: "a\<noteq>b" and II: "a\<inverse>\<cdot>b \<notin> H" 
	by auto
      from A3 T T1 I have "(a\<inverse>\<cdot>b \<in> H) Xor ((a\<inverse>\<cdot>b)\<inverse> \<in> H)"
	using group0_2_L11 by auto
      with A4 T II have "\<langle> b,a\<rangle> \<in> r"
	using Xor_def group0_2_L12 by simp
    } then have "\<langle> a,b\<rangle> \<in> r \<or> \<langle> b,a\<rangle> \<in> r" by auto
  } then show "r {is total on} G" using IsTotal_def
    by simp
qed

text\<open>If the set defined as in \<open>OrderedGroup_ZF_5_L4\<close> does not 
  contain the neutral element, then it is the positive set for the resulting
  order.\<close>

lemma (in group0) OrderedGroup_ZF_5_L6: 
  assumes "P {is commutative on} G"
  and "H\<subseteq>G" and "\<one> \<notin> H"
  and "r = {p \<in> G\<times>G. fst(p) = snd(p) \<or> fst(p)\<inverse>\<cdot>snd(p) \<in> H}"
  shows "PositiveSet(G,P,r) = H"
  using assms group_inv_of_one group0_2_L2 PositiveSet_def
  by auto

text\<open>The next definition describes how we construct an order relation
  from the prescribed set of positive elements.\<close>

definition
  "OrderFromPosSet(G,P,H) \<equiv> 
  {p \<in> G\<times>G. fst(p) = snd(p) \<or> P`\<langle>GroupInv(G,P)`(fst(p)),snd(p)\<rangle> \<in> H }"

text\<open>The next theorem rephrases lemmas 
  \<open>OrderedGroup_ZF_5_L5\<close> and \<open>OrderedGroup_ZF_5_L6\<close>
  using the definition of the order from the positive set 
  \<open>OrderFromPosSet\<close>. To summarize, this is what it says:
  Suppose that $H\subseteq G$ is a set closed under that group operation
  such that $1\notin H$ and for every nonunit group element $a$ either $a\in H$
  or $a^{-1}\in H$. Define the order as $a\leq b$ iff $a=b$ or 
  $a^{-1}\cdot b \in H$. Then this order makes $G$ into a linearly ordered 
  group such $H$ is the set of positive elements (and then of course 
  $H \cup \{1\}$ is the set of nonnegative elements).\<close>

theorem (in group0) Group_ord_by_positive_set: 
  assumes "P {is commutative on} G"
  and "H\<subseteq>G"   "H {is closed under} P"   "\<one> \<notin> H"
  and "\<forall>a\<in>G. a\<noteq>\<one> \<longrightarrow> (a\<in>H) Xor (a\<inverse>\<in>H)"
  shows 
  "IsAnOrdGroup(G,P,OrderFromPosSet(G,P,H))"
  "OrderFromPosSet(G,P,H) {is total on} G"
  "PositiveSet(G,P,OrderFromPosSet(G,P,H)) = H"
  "Nonnegative(G,P,OrderFromPosSet(G,P,H)) = H \<union> {\<one>}" 
  using assms OrderFromPosSet_def OrderedGroup_ZF_5_L5 OrderedGroup_ZF_5_L6
  by auto

subsection\<open>Odd Extensions\<close>

text\<open>In this section we verify properties of odd extensions of functions
  defined on $G_+$. An odd extension of a function $f: G_+ \rightarrow G$
  is a function $f^\circ : G\rightarrow G$ defined by $f^\circ (x) = f(x)$ 
  if $x\in G_+$, $f(1) = 1$ and $f^\circ (x) = (f(x^{-1}))^{-1}$ for $x < 1$.
  Such function is the unique odd function that is equal to $f$ when
  restricted to $G_+$.\<close>

text\<open>The next lemma is just to see the definition of the odd extension
  in the notation used in the \<open>group1\<close> context.\<close>

lemma (in group3) OrderedGroup_ZF_6_L1:
  shows "f\<degree> = f \<union> {\<langle>a, (f`(a\<inverse>))\<inverse>\<rangle>. a \<in> \<sm>G\<^sub>+} \<union> {\<langle>\<one>,\<one>\<rangle>}"
  using OddExtension_def by simp

text\<open>A technical lemma that states that from a function defined on 
  \<open>G\<^sub>+\<close> with values in $G$ we have $(f(a^{-1}))^{-1}\in G$.\<close>

lemma (in group3) OrderedGroup_ZF_6_L2:
  assumes "f: G\<^sub>+\<rightarrow>G" and "a\<in>\<sm>G\<^sub>+"
  shows 
  "f`(a\<inverse>) \<in> G"  
  "(f`(a\<inverse>))\<inverse> \<in> G"
  using assms OrderedGroup_ZF_1_L27 apply_funtype
    OrderedGroup_ZF_1_L1 group0.inverse_in_group
  by auto

text\<open>The main theorem about odd extensions. It basically says that the odd 
  extension of a function is what we want to to be.\<close>

lemma (in group3) odd_ext_props: 
  assumes A1: "r {is total on} G" and A2: "f: G\<^sub>+\<rightarrow>G"
  shows 
  "f\<degree> : G \<rightarrow> G"
  "\<forall>a\<in>G\<^sub>+. (f\<degree>)`(a) = f`(a)"
  "\<forall>a\<in>(\<sm>G\<^sub>+). (f\<degree>)`(a) = (f`(a\<inverse>))\<inverse>"
  "(f\<degree>)`(\<one>) = \<one>"
proof -
  from A1 A2 have I:
    "f: G\<^sub>+\<rightarrow>G"
    "\<forall>a\<in>\<sm>G\<^sub>+. (f`(a\<inverse>))\<inverse> \<in> G"
    "G\<^sub>+\<inter>(\<sm>G\<^sub>+) = 0"  
    "\<one> \<notin> G\<^sub>+\<union>(\<sm>G\<^sub>+)"
    "f\<degree> = f \<union> {\<langle>a, (f`(a\<inverse>))\<inverse>\<rangle>. a \<in> \<sm>G\<^sub>+} \<union> {\<langle>\<one>,\<one>\<rangle>}"
    using OrderedGroup_ZF_6_L2 OrdGroup_decomp2 OrderedGroup_ZF_6_L1
    by auto
  then have "f\<degree>: G\<^sub>+ \<union> (\<sm>G\<^sub>+) \<union> {\<one>} \<rightarrow>G\<union>G\<union>{\<one>}"
    by (rule func1_1_L11E)
  moreover from A1 have 
    "G\<^sub>+ \<union> (\<sm>G\<^sub>+) \<union> {\<one>} = G"
    "G\<union>G\<union>{\<one>} = G"
    using OrdGroup_decomp2 OrderedGroup_ZF_1_L1 group0.group0_2_L2
    by auto
  ultimately show "f\<degree> : G \<rightarrow> G" by simp
  from I show "\<forall>a\<in>G\<^sub>+. (f\<degree>)`(a) = f`(a)"
    by (rule func1_1_L11E)
  from I show "\<forall>a\<in>(\<sm>G\<^sub>+). (f\<degree>)`(a) = (f`(a\<inverse>))\<inverse>"
    by (rule func1_1_L11E)
  from I show "(f\<degree>)`(\<one>) = \<one>"
    by (rule func1_1_L11E)
qed

text\<open>Odd extensions are odd, of course.\<close>

lemma (in group3) oddext_is_odd:
  assumes A1: "r {is total on} G" and A2: "f: G\<^sub>+\<rightarrow>G"
  and A3: "a\<in>G"
  shows "(f\<degree>)`(a\<inverse>) = ((f\<degree>)`(a))\<inverse>"
proof -
  from A1 A3 have "a\<in>G\<^sub>+ \<or> a \<in> (\<sm>G\<^sub>+) \<or> a=\<one>"
    using OrdGroup_decomp2 by blast
  moreover
  { assume "a\<in>G\<^sub>+"  
    with A1 A2 have "a\<inverse> \<in> \<sm>G\<^sub>+" and  "(f\<degree>)`(a) = f`(a)"
      using OrderedGroup_ZF_1_L25 odd_ext_props by auto
    with A1 A2 have 
      "(f\<degree>)`(a\<inverse>) = (f`((a\<inverse>)\<inverse>))\<inverse>"  and "(f`(a))\<inverse> = ((f\<degree>)`(a))\<inverse>"
      using odd_ext_props by auto
    with A3 have "(f\<degree>)`(a\<inverse>) = ((f\<degree>)`(a))\<inverse>"
      using OrderedGroup_ZF_1_L1 group0.group_inv_of_inv
      by simp } 
  moreover
  { assume A4: "a \<in> \<sm>G\<^sub>+"
    with A1 A2  have "a\<inverse> \<in> G\<^sub>+" and  "(f\<degree>)`(a) = (f`(a\<inverse>))\<inverse>"
      using OrderedGroup_ZF_1_L27 odd_ext_props
      by auto
    with A1 A2 A4 have "(f\<degree>)`(a\<inverse>) = ((f\<degree>)`(a))\<inverse>"
      using odd_ext_props OrderedGroup_ZF_6_L2 
	OrderedGroup_ZF_1_L1 group0.group_inv_of_inv
      by simp }
  moreover
  { assume "a = \<one>" 
    with A1 A2 have "(f\<degree>)`(a\<inverse>) = ((f\<degree>)`(a))\<inverse>"
      using OrderedGroup_ZF_1_L1 group0.group_inv_of_one 
	odd_ext_props by simp
  }
  ultimately show "(f\<degree>)`(a\<inverse>) = ((f\<degree>)`(a))\<inverse>"
    by auto
qed

text\<open>Another way of saying that odd extensions are odd.\<close>

lemma (in group3) oddext_is_odd_alt:
  assumes A1: "r {is total on} G" and A2: "f: G\<^sub>+\<rightarrow>G"
  and A3: "a\<in>G"
  shows "((f\<degree>)`(a\<inverse>))\<inverse> = (f\<degree>)`(a)"
proof -
  from A1 A2 have 
    "f\<degree> : G \<rightarrow> G"
    "\<forall>a\<in>G. (f\<degree>)`(a\<inverse>) = ((f\<degree>)`(a))\<inverse>"
    using odd_ext_props oddext_is_odd by auto
  then have "\<forall>a\<in>G. ((f\<degree>)`(a\<inverse>))\<inverse> = (f\<degree>)`(a)"
    using OrderedGroup_ZF_1_L1 group0.group0_6_L2 by simp
  with A3 show "((f\<degree>)`(a\<inverse>))\<inverse> = (f\<degree>)`(a)" by simp
qed

subsection\<open>Functions with infinite limits\<close>

text\<open>In this section we consider functions $f: G\rightarrow G$ with the 
  property that for $f(x)$ is arbitrarily large for large enough $x$.
  More precisely, for every $a\in G$ there exist $b\in G_+$ such that 
  for every $x\geq b$ we have $f(x)\geq a$. In a sense this means that
  $\lim_{x\rightarrow \infty}f(x) = \infty$, hence the title of this section.
  We also prove dual statements for functions such that 
  $\lim_{x\rightarrow -\infty}f(x) = -\infty$. 
\<close>

text\<open>If an image of a set by a function with infinite positive limit 
  is bounded above, then the set itself is bounded above.\<close>

lemma (in group3) OrderedGroup_ZF_7_L1:
  assumes A1: "r {is total on} G" and A2: "G \<noteq> {\<one>}" and
  A3: "f:G\<rightarrow>G" and 
  A4: "\<forall>a\<in>G.\<exists>b\<in>G\<^sub>+.\<forall>x. b\<lsq>x \<longrightarrow> a \<lsq> f`(x)" and 
  A5: "A\<subseteq>G" and 
  A6: "IsBoundedAbove(f``(A),r)"
  shows "IsBoundedAbove(A,r)"
proof -
  { assume "\<not>IsBoundedAbove(A,r)"
    then have I: "\<forall>u. \<exists>x\<in>A. \<not>(x\<lsq>u)"
      using IsBoundedAbove_def by auto
    have "\<forall>a\<in>G. \<exists>y\<in>f``(A). a\<lsq>y"
    proof -
      { fix a assume "a\<in>G" 
	with A4 obtain b where 
	  II: "b\<in>G\<^sub>+" and III: "\<forall>x. b\<lsq>x \<longrightarrow> a \<lsq> f`(x)"
	  by auto
	from I obtain x where IV: "x\<in>A" and "\<not>(x\<lsq>b)"
	  by auto
	with A1 A5 II have 
	  "r {is total on} G"
	  "x\<in>G"  "b\<in>G"  "\<not>(x\<lsq>b)"
	  using PositiveSet_def by auto
	with III have "a \<lsq> f`(x)"
	  using OrderedGroup_ZF_1_L8 by blast
	with A3 A5 IV have "\<exists>y\<in>f``(A). a\<lsq>y"
	  using func_imagedef by auto
      } thus ?thesis by simp
    qed
    with A1 A2 A6 have False using OrderedGroup_ZF_2_L2A
      by simp
  } thus ?thesis by auto
qed

text\<open>If an image of a set defined by separation 
  by a function with infinite positive limit 
  is bounded above, then the set itself is bounded above.\<close>

lemma (in group3) OrderedGroup_ZF_7_L2:
  assumes A1: "r {is total on} G" and A2: "G \<noteq> {\<one>}" and
  A3: "X\<noteq>0" and A4: "f:G\<rightarrow>G" and 
  A5: "\<forall>a\<in>G.\<exists>b\<in>G\<^sub>+.\<forall>y. b\<lsq>y \<longrightarrow> a \<lsq> f`(y)" and 
  A6: "\<forall>x\<in>X. b(x) \<in> G \<and> f`(b(x)) \<lsq> U"
  shows "\<exists>u.\<forall>x\<in>X. b(x) \<lsq> u"
proof -
  let ?A = "{b(x). x\<in>X}"
  from A6 have I: "?A\<subseteq>G" by auto
  moreover note assms
  moreover have "IsBoundedAbove(f``(?A),r)"
  proof -
    from A4 A6 I have "\<forall>z\<in>f``(?A). \<langle>z,U\<rangle> \<in> r"
      using func_imagedef by simp
    then show "IsBoundedAbove(f``(?A),r)"
      by (rule Order_ZF_3_L10)
  qed
  ultimately have "IsBoundedAbove(?A,r)" using OrderedGroup_ZF_7_L1
    by simp
  with A3 have "\<exists>u.\<forall>y\<in>?A. y \<lsq> u"
    using IsBoundedAbove_def by simp
  then show "\<exists>u.\<forall>x\<in>X. b(x) \<lsq> u" by auto
qed

text\<open>If the image of a set defined by separation 
  by a function with infinite negative limit 
  is bounded below, then the set itself is bounded above.
  This is dual to \<open>OrderedGroup_ZF_7_L2\<close>.\<close>

lemma (in group3) OrderedGroup_ZF_7_L3:
  assumes A1: "r {is total on} G" and A2: "G \<noteq> {\<one>}" and
  A3: "X\<noteq>0" and A4: "f:G\<rightarrow>G" and 
  A5: "\<forall>a\<in>G.\<exists>b\<in>G\<^sub>+.\<forall>y. b\<lsq>y \<longrightarrow> f`(y\<inverse>) \<lsq> a" and 
  A6: "\<forall>x\<in>X. b(x) \<in> G \<and> L \<lsq> f`(b(x))"
  shows "\<exists>l.\<forall>x\<in>X. l \<lsq> b(x)"
proof -
  let ?g = "GroupInv(G,P) O f O GroupInv(G,P)"
  from ordGroupAssum have I: "GroupInv(G,P) : G\<rightarrow>G"
    using IsAnOrdGroup_def group0_2_T2 by simp
  with A4 have II: "\<forall>x\<in>G. ?g`(x) = (f`(x\<inverse>))\<inverse>"
    using func1_1_L18 by simp
  note A1 A2 A3
  moreover from A4 I have "?g : G\<rightarrow>G"
    using comp_fun by blast
  moreover have "\<forall>a\<in>G.\<exists>b\<in>G\<^sub>+.\<forall>y. b\<lsq>y \<longrightarrow> a \<lsq> ?g`(y)"
  proof -
  { fix a assume A7: "a\<in>G"
    then have "a\<inverse> \<in> G"
      using OrderedGroup_ZF_1_L1 group0.inverse_in_group
      by simp
    with A5 obtain b where 
      III: "b\<in>G\<^sub>+" and "\<forall>y. b\<lsq>y \<longrightarrow> f`(y\<inverse>) \<lsq> a\<inverse>"
      by auto
    with II A7 have "\<forall>y. b\<lsq>y \<longrightarrow> a \<lsq> ?g`(y)"
      using OrderedGroup_ZF_1_L5AD OrderedGroup_ZF_1_L4
      by simp
    with III have "\<exists>b\<in>G\<^sub>+.\<forall>y. b\<lsq>y \<longrightarrow> a \<lsq> ?g`(y)"
      by auto
  } then show "\<forall>a\<in>G.\<exists>b\<in>G\<^sub>+.\<forall>y. b\<lsq>y \<longrightarrow> a \<lsq> ?g`(y)"
    by simp
  qed
  moreover have "\<forall>x\<in>X. b(x)\<inverse> \<in> G \<and> ?g`(b(x)\<inverse>) \<lsq> L\<inverse>"
  proof-
    { fix x assume "x\<in>X"
      with A6 have 
	T: "b(x) \<in> G"  "b(x)\<inverse> \<in> G" and "L \<lsq> f`(b(x))"
	using OrderedGroup_ZF_1_L1 group0.inverse_in_group
	by auto
      then have "(f`(b(x)))\<inverse> \<lsq> L\<inverse>"
	using OrderedGroup_ZF_1_L5 by simp
      moreover from II T have "(f`(b(x)))\<inverse> =  ?g`(b(x)\<inverse>)"
	using OrderedGroup_ZF_1_L1 group0.group_inv_of_inv
	by simp
      ultimately have "?g`(b(x)\<inverse>) \<lsq> L\<inverse>" by simp
      with T have "b(x)\<inverse> \<in> G \<and> ?g`(b(x)\<inverse>) \<lsq> L\<inverse>"
	by simp
    } then show "\<forall>x\<in>X. b(x)\<inverse> \<in> G \<and> ?g`(b(x)\<inverse>) \<lsq> L\<inverse>"
      by simp
  qed
  ultimately have "\<exists>u.\<forall>x\<in>X. (b(x))\<inverse> \<lsq> u"
    by (rule OrderedGroup_ZF_7_L2)
  then have "\<exists>u.\<forall>x\<in>X. u\<inverse> \<lsq> (b(x)\<inverse>)\<inverse>"
    using OrderedGroup_ZF_1_L5 by auto
  with A6 show "\<exists>l.\<forall>x\<in>X. l \<lsq> b(x)"
    using OrderedGroup_ZF_1_L1 group0.group_inv_of_inv
    by auto
qed

text\<open>The next lemma combines \<open>OrderedGroup_ZF_7_L2\<close> and 
  \<open>OrderedGroup_ZF_7_L3\<close> to show that if an image of a set 
  defined by separation by a function with infinite limits is bounded,
  then the set itself i bounded.\<close>

lemma (in group3) OrderedGroup_ZF_7_L4:
  assumes A1: "r {is total on} G" and A2: "G \<noteq> {\<one>}" and
  A3: "X\<noteq>0" and A4: "f:G\<rightarrow>G" and 
  A5: "\<forall>a\<in>G.\<exists>b\<in>G\<^sub>+.\<forall>y. b\<lsq>y \<longrightarrow> a \<lsq> f`(y)" and 
  A6: "\<forall>a\<in>G.\<exists>b\<in>G\<^sub>+.\<forall>y. b\<lsq>y \<longrightarrow> f`(y\<inverse>) \<lsq> a" and 
  A7: "\<forall>x\<in>X. b(x) \<in> G \<and> L \<lsq> f`(b(x)) \<and> f`(b(x)) \<lsq> U"
shows "\<exists>M.\<forall>x\<in>X. \<bar>b(x)\<bar> \<lsq> M"
proof -
  from A7 have 
    I: "\<forall>x\<in>X. b(x) \<in> G \<and> f`(b(x)) \<lsq> U" and
    II: "\<forall>x\<in>X. b(x) \<in> G \<and> L \<lsq> f`(b(x))"
    by auto
  from A1 A2 A3 A4 A5 I have "\<exists>u.\<forall>x\<in>X. b(x) \<lsq> u"
    by (rule OrderedGroup_ZF_7_L2)
  moreover from  A1 A2 A3 A4 A6 II have "\<exists>l.\<forall>x\<in>X. l \<lsq> b(x)"
    by (rule OrderedGroup_ZF_7_L3)
  ultimately have "\<exists>u l. \<forall>x\<in>X. l\<lsq>b(x) \<and> b(x) \<lsq> u"
    by auto
  with A1 have "\<exists>u l.\<forall>x\<in>X. \<bar>b(x)\<bar> \<lsq> GreaterOf(r,\<bar>l\<bar>,\<bar>u\<bar>)"
    using OrderedGroup_ZF_3_L10 by blast
  then show "\<exists>M.\<forall>x\<in>X. \<bar>b(x)\<bar> \<lsq> M"
    by auto
qed

end
