(*
    This file is a part of IsarMathLib - 
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

section \<open>Rings - introduction\<close>

theory Ring_ZF imports AbelianGroup_ZF

begin

text\<open>This theory file covers basic facts about rings.\<close>

subsection\<open>Definition and basic properties\<close>

text\<open>In this section we define what is a ring and list the basic properties
  of rings.\<close>

text\<open>We say that three sets $(R,A,M)$ form a ring if $(R,A)$ is an abelian 
  group, $(R,M)$ is a monoid and $A$ is distributive with respect to $M$ on 
  $R$. $A$ represents the additive operation on $R$. 
  As such it is a subset of $(R\times R)\times R$ (recall that in ZF set theory
  functions are sets).
  Similarly $M$ represents the multiplicative operation on $R$ and is also
  a subset of $(R\times R)\times R$.
  We  don't require the multiplicative operation to be commutative in the 
  definition of a ring.\<close>


definition
  "IsAring(R,A,M) \<equiv> IsAgroup(R,A) \<and> (A {is commutative on} R) \<and> 
  IsAmonoid(R,M) \<and> IsDistributive(R,A,M)"

text\<open>We also define the notion of having no zero divisors. In
  standard notation the ring has no zero divisors if for all $a,b \in R$ we have 
  $a\cdot b = 0$ implies $a = 0$ or $b = 0$.
\<close>

definition
  "HasNoZeroDivs(R,A,M) \<equiv> (\<forall>a\<in>R. \<forall>b\<in>R. 
  M`\<langle> a,b\<rangle> = TheNeutralElement(R,A) \<longrightarrow>
  a = TheNeutralElement(R,A) \<or> b = TheNeutralElement(R,A))"

text\<open>Next we define a locale that will be used when considering rings.\<close>

locale ring0 =

  fixes R and A and M 
 
  assumes ringAssum: "IsAring(R,A,M)"

  fixes ringa (infixl "\<ra>" 90)
  defines ringa_def [simp]: "a\<ra>b \<equiv> A`\<langle> a,b\<rangle>"

  fixes ringminus ("\<rm> _" 89)
  defines ringminus_def [simp]: "(\<rm>a) \<equiv> GroupInv(R,A)`(a)"

  fixes ringsub (infixl "\<rs>" 90)
  defines ringsub_def [simp]: "a\<rs>b \<equiv> a\<ra>(\<rm>b)"

  fixes ringm (infixl "\<cdot>" 95)
  defines ringm_def [simp]: "a\<cdot>b \<equiv> M`\<langle> a,b\<rangle>"

  fixes ringzero ("\<zero>")
  defines ringzero_def [simp]: "\<zero> \<equiv> TheNeutralElement(R,A)"

  fixes ringone ("\<one>")
  defines ringone_def [simp]: "\<one> \<equiv> TheNeutralElement(R,M)"

  fixes ringtwo ("\<two>")
  defines ringtwo_def [simp]: "\<two> \<equiv> \<one>\<ra>\<one>"

  fixes ringsq ("_\<^sup>2" [96] 97)
  defines ringsq_def [simp]: "a\<^sup>2 \<equiv> a\<cdot>a"

text\<open>In the \<open>ring0\<close> context we can use theorems proven in some 
  other contexts.\<close>

lemma (in ring0) Ring_ZF_1_L1: shows 
  "monoid0(R,M)"
  "group0(R,A)" 
  "A {is commutative on} R"
  using ringAssum IsAring_def group0_def monoid0_def by auto

text\<open>The additive operation in a ring is distributive with respect to the
  multiplicative operation.\<close>

lemma (in ring0) ring_oper_distr: assumes A1: "a\<in>R"  "b\<in>R"  "c\<in>R"
  shows 
  "a\<cdot>(b\<ra>c) = a\<cdot>b \<ra> a\<cdot>c" 
  "(b\<ra>c)\<cdot>a = b\<cdot>a \<ra> c\<cdot>a"
  using ringAssum assms IsAring_def IsDistributive_def by auto

text\<open>Zero and one of the ring are elements of the ring. The negative of zero
  is zero.\<close>

lemma (in ring0) Ring_ZF_1_L2: 
  shows "\<zero>\<in>R"  "\<one>\<in>R"   "(\<rm>\<zero>) = \<zero>"
  using Ring_ZF_1_L1 group0.group0_2_L2 monoid0.unit_is_neutral 
    group0.group_inv_of_one by auto
  
text\<open>The next lemma lists some properties of a ring that require one element
  of a ring.\<close>

lemma (in ring0) Ring_ZF_1_L3: assumes "a\<in>R"
  shows 
  "(\<rm>a) \<in> R"
  "(\<rm>(\<rm>a)) = a"
  "a\<ra>\<zero> = a" 
  "\<zero>\<ra>a = a" 
  "a\<cdot>\<one> = a" 
  "\<one>\<cdot>a = a" 
  "a\<rs>a = \<zero>" 
  "a\<rs>\<zero> = a"
  "\<two>\<cdot>a = a\<ra>a"
  "(\<rm>a)\<ra>a = \<zero>"
  using assms Ring_ZF_1_L1 group0.inverse_in_group group0.group_inv_of_inv 
    group0.group0_2_L6 group0.group0_2_L2 monoid0.unit_is_neutral 
    Ring_ZF_1_L2 ring_oper_distr
  by auto

text\<open>Properties that require two elements of a ring.\<close>

lemma (in ring0) Ring_ZF_1_L4: assumes A1: "a\<in>R" "b\<in>R"
  shows 
  "a\<ra>b \<in> R" 
  "a\<rs>b \<in> R" 
  "a\<cdot>b \<in> R" 
  "a\<ra>b = b\<ra>a"
  using ringAssum assms Ring_ZF_1_L1 Ring_ZF_1_L3 
    group0.group0_2_L1 monoid0.group0_1_L1 
    IsAring_def IsCommutative_def
  by auto

text\<open>Cancellation of an element on both sides of equality. 
  This is a property of groups, written in the (additive) notation
  we use for the additive operation in rings.
\<close>

lemma (in ring0) ring_cancel_add: 
  assumes A1: "a\<in>R" "b\<in>R" and A2: "a \<ra> b = a"
  shows "b = \<zero>"
  using assms Ring_ZF_1_L1 group0.group0_2_L7 by simp

text\<open>Any element of a ring multiplied by zero is zero.\<close>

lemma (in ring0) Ring_ZF_1_L6: 
  assumes A1: "x\<in>R" shows "\<zero>\<cdot>x = \<zero>"   "x\<cdot>\<zero> = \<zero>"
proof -
  let ?a = "x\<cdot>\<one>"
  let ?b = "x\<cdot>\<zero>"
  let ?c = "\<one>\<cdot>x"
  let ?d = "\<zero>\<cdot>x"
  from A1 have 
    "?a \<ra> ?b = x\<cdot>(\<one> \<ra> \<zero>)"   "?c \<ra> ?d = (\<one> \<ra> \<zero>)\<cdot>x"
    using Ring_ZF_1_L2 ring_oper_distr by auto
  moreover have "x\<cdot>(\<one> \<ra> \<zero>) = ?a" "(\<one> \<ra> \<zero>)\<cdot>x = ?c"
    using Ring_ZF_1_L2 Ring_ZF_1_L3 by auto
  ultimately have "?a \<ra> ?b = ?a" and T1: "?c \<ra> ?d = ?c" 
    by auto
  moreover from A1 have 
    "?a \<in> R"  "?b \<in> R" and T2: "?c \<in> R"  "?d \<in> R"
    using Ring_ZF_1_L2 Ring_ZF_1_L4 by auto
  ultimately have "?b = \<zero>" using ring_cancel_add
    by blast
  moreover from T2 T1 have "?d = \<zero>" using ring_cancel_add
    by blast
  ultimately show "x\<cdot>\<zero> = \<zero>"  "\<zero>\<cdot>x = \<zero>" by auto
qed

text\<open>Negative can be pulled out of a product.\<close>

lemma (in ring0) Ring_ZF_1_L7: 
  assumes A1: "a\<in>R"  "b\<in>R"
  shows 
  "(\<rm>a)\<cdot>b = \<rm>(a\<cdot>b)" 
  "a\<cdot>(\<rm>b) = \<rm>(a\<cdot>b)"
  "(\<rm>a)\<cdot>b = a\<cdot>(\<rm>b)"
proof -
  from A1 have I: 
    "a\<cdot>b \<in> R" "(\<rm>a) \<in> R" "((\<rm>a)\<cdot>b) \<in> R" 
    "(\<rm>b) \<in> R" "a\<cdot>(\<rm>b) \<in> R"
    using Ring_ZF_1_L3 Ring_ZF_1_L4 by auto
  moreover have "(\<rm>a)\<cdot>b \<ra> a\<cdot>b = \<zero>" 
    and II: "a\<cdot>(\<rm>b) \<ra> a\<cdot>b = \<zero>"
  proof -
    from A1 I have 
      "(\<rm>a)\<cdot>b \<ra> a\<cdot>b = ((\<rm>a)\<ra> a)\<cdot>b"
      "a\<cdot>(\<rm>b) \<ra> a\<cdot>b= a\<cdot>((\<rm>b)\<ra>b)"
      using ring_oper_distr by auto
    moreover from A1 have 
      "((\<rm>a)\<ra> a)\<cdot>b = \<zero>" 
      "a\<cdot>((\<rm>b)\<ra>b) = \<zero>"
      using Ring_ZF_1_L1 group0.group0_2_L6 Ring_ZF_1_L6
      by auto
    ultimately show 
      "(\<rm>a)\<cdot>b \<ra> a\<cdot>b = \<zero>" 
      "a\<cdot>(\<rm>b) \<ra> a\<cdot>b = \<zero>" 
      by auto
  qed
  ultimately show "(\<rm>a)\<cdot>b = \<rm>(a\<cdot>b)"
    using Ring_ZF_1_L1 group0.group0_2_L9 by simp
  moreover from I II show "a\<cdot>(\<rm>b) = \<rm>(a\<cdot>b)"
    using Ring_ZF_1_L1 group0.group0_2_L9 by simp   
  ultimately show "(\<rm>a)\<cdot>b = a\<cdot>(\<rm>b)" by simp
qed

text\<open>Minus times minus is plus.\<close>

lemma (in ring0) Ring_ZF_1_L7A: assumes "a\<in>R"  "b\<in>R"
  shows "(\<rm>a)\<cdot>(\<rm>b) = a\<cdot>b"
  using assms Ring_ZF_1_L3 Ring_ZF_1_L7 Ring_ZF_1_L4
  by simp

text\<open>Subtraction is distributive with respect to multiplication.\<close>

lemma (in ring0) Ring_ZF_1_L8: assumes "a\<in>R"  "b\<in>R"  "c\<in>R"
  shows 
  "a\<cdot>(b\<rs>c) = a\<cdot>b \<rs> a\<cdot>c"  
  "(b\<rs>c)\<cdot>a = b\<cdot>a \<rs> c\<cdot>a"
  using assms Ring_ZF_1_L3 ring_oper_distr Ring_ZF_1_L7 Ring_ZF_1_L4
  by auto

text\<open>Other basic properties involving two elements of a ring.\<close>

lemma (in ring0) Ring_ZF_1_L9: assumes "a\<in>R"  "b\<in>R"
  shows 
  "(\<rm>b)\<rs>a = (\<rm>a)\<rs>b" 
  "(\<rm>(a\<ra>b)) = (\<rm>a)\<rs>b"  
  "(\<rm>(a\<rs>b)) = ((\<rm>a)\<ra>b)"
  "a\<rs>(\<rm>b) = a\<ra>b"
  using assms ringAssum IsAring_def 
    Ring_ZF_1_L1 group0.group0_4_L4  group0.group_inv_of_inv
  by auto

text\<open>If the difference of two element is zero, then those elements
  are equal.\<close>

lemma (in ring0) Ring_ZF_1_L9A: 
  assumes A1: "a\<in>R"  "b\<in>R" and A2: "a\<rs>b = \<zero>"
  shows "a=b"
proof -
  from A1 A2 have
    "group0(R,A)"
    "a\<in>R"  "b\<in>R"
    "A`\<langle>a,GroupInv(R,A)`(b)\<rangle> = TheNeutralElement(R,A)"
    using Ring_ZF_1_L1 by auto
  then show "a=b" by (rule group0.group0_2_L11A)
qed

text\<open>Other basic properties involving three elements of a ring.\<close>

lemma (in ring0) Ring_ZF_1_L10: 
  assumes "a\<in>R"  "b\<in>R"  "c\<in>R"
  shows 
  "a\<ra>(b\<ra>c) = a\<ra>b\<ra>c"
  (*"a\<ra>(b\<rs>c) = a\<ra>b\<rs>c"*)
  "a\<rs>(b\<ra>c) = a\<rs>b\<rs>c"
  "a\<rs>(b\<rs>c) = a\<rs>b\<ra>c"
  using assms ringAssum Ring_ZF_1_L1 group0.group_oper_assoc 
    IsAring_def group0.group0_4_L4A by auto

text\<open>Another property with three elements.\<close>

lemma (in ring0) Ring_ZF_1_L10A: 
  assumes A1: "a\<in>R"  "b\<in>R"  "c\<in>R"
  shows "a\<ra>(b\<rs>c) = a\<ra>b\<rs>c"
  using assms Ring_ZF_1_L3 Ring_ZF_1_L10 by simp

text\<open>Associativity of addition and multiplication.\<close>

lemma (in ring0) Ring_ZF_1_L11: 
  assumes "a\<in>R"  "b\<in>R"  "c\<in>R"
  shows 
  "a\<ra>b\<ra>c = a\<ra>(b\<ra>c)"
  "a\<cdot>b\<cdot>c = a\<cdot>(b\<cdot>c)"
  using assms ringAssum Ring_ZF_1_L1 group0.group_oper_assoc
    IsAring_def IsAmonoid_def IsAssociative_def
  by auto

text\<open>An interpretation of what it means that a ring has 
  no zero divisors.\<close>

lemma (in ring0) Ring_ZF_1_L12: 
  assumes "HasNoZeroDivs(R,A,M)"
  and "a\<in>R"  "a\<noteq>\<zero>"  "b\<in>R"  "b\<noteq>\<zero>"
  shows "a\<cdot>b\<noteq>\<zero>" 
  using assms HasNoZeroDivs_def by auto

text\<open>In rings with no zero divisors we can cancel nonzero factors.\<close>

lemma (in ring0) Ring_ZF_1_L12A: 
  assumes A1: "HasNoZeroDivs(R,A,M)" and A2: "a\<in>R"  "b\<in>R"  "c\<in>R"
  and A3: "a\<cdot>c = b\<cdot>c" and A4: "c\<noteq>\<zero>" 
  shows "a=b"
proof -
  from A2 have T: "a\<cdot>c \<in> R"  "a\<rs>b \<in> R"
    using Ring_ZF_1_L4 by auto
  with A1 A2 A3 have "a\<rs>b = \<zero> \<or> c=\<zero>"
    using Ring_ZF_1_L3 Ring_ZF_1_L8 HasNoZeroDivs_def
    by simp
  with A2 A4 have "a\<in>R"  "b\<in>R"  "a\<rs>b = \<zero>" 
    by auto
  then show "a=b" by (rule Ring_ZF_1_L9A)
qed

text\<open>In rings with no zero divisors if two elements are different, 
  then after multiplying by a nonzero element they are still different.\<close>

lemma (in ring0) Ring_ZF_1_L12B: 
  assumes A1: "HasNoZeroDivs(R,A,M)"  
  "a\<in>R"   "b\<in>R"   "c\<in>R"   "a\<noteq>b"   "c\<noteq>\<zero>" 
  shows  "a\<cdot>c \<noteq> b\<cdot>c"
  using A1 Ring_ZF_1_L12A by auto (* A1 has to be here *)

text\<open>In rings with no zero divisors multiplying a nonzero element 
  by a nonone element changes the value.\<close>

lemma (in ring0) Ring_ZF_1_L12C:
  assumes A1: "HasNoZeroDivs(R,A,M)" and 
  A2: "a\<in>R"  "b\<in>R" and A3: "\<zero>\<noteq>a"  "\<one>\<noteq>b"
  shows "a \<noteq> a\<cdot>b"
proof -
  { assume "a = a\<cdot>b"
    with A1 A2 have "a = \<zero> \<or> b\<rs>\<one> = \<zero>"
      using Ring_ZF_1_L3 Ring_ZF_1_L2 Ring_ZF_1_L8 
	Ring_ZF_1_L3 Ring_ZF_1_L2 Ring_ZF_1_L4 HasNoZeroDivs_def
      by simp
    with A2 A3 have False
      using Ring_ZF_1_L2 Ring_ZF_1_L9A by auto
  } then show "a \<noteq> a\<cdot>b" by auto
qed      

text\<open>If a square is nonzero, then the element is nonzero.\<close>

lemma (in ring0) Ring_ZF_1_L13:
  assumes "a\<in>R"  and "a\<^sup>2 \<noteq> \<zero>"
  shows "a\<noteq>\<zero>"
  using assms Ring_ZF_1_L2 Ring_ZF_1_L6 by auto

text\<open>Square of an element and its opposite are the same.\<close>

lemma (in ring0) Ring_ZF_1_L14:
  assumes "a\<in>R" shows "(\<rm>a)\<^sup>2 = ((a)\<^sup>2)"
  using assms Ring_ZF_1_L7A by simp

text\<open>Adding zero to a set that is closed under addition results
  in a set that is also closed under addition. This is a property of groups.\<close>

lemma (in ring0) Ring_ZF_1_L15: 
  assumes "H \<subseteq> R" and "H {is closed under} A"
  shows "(H \<union> {\<zero>}) {is closed under} A"
  using assms Ring_ZF_1_L1 group0.group0_2_L17 by simp

text\<open>Adding zero to a set that is closed under multiplication results
  in a set that is also closed under multiplication.\<close>

lemma (in ring0) Ring_ZF_1_L16:
  assumes A1: "H \<subseteq> R" and A2: "H {is closed under} M"
  shows "(H \<union> {\<zero>}) {is closed under} M"
  using assms Ring_ZF_1_L2 Ring_ZF_1_L6 IsOpClosed_def
  by auto

text\<open>The ring is trivial iff $0=1$.\<close>

lemma (in ring0) Ring_ZF_1_L17: shows "R = {\<zero>} \<longleftrightarrow> \<zero>=\<one>"
proof
  assume "R = {\<zero>}"
  then show "\<zero>=\<one>" using Ring_ZF_1_L2
    by blast
next assume A1: "\<zero> = \<one>"
  then have "R \<subseteq> {\<zero>}"
    using Ring_ZF_1_L3 Ring_ZF_1_L6 by auto
  moreover have "{\<zero>} \<subseteq> R" using Ring_ZF_1_L2 by auto
  ultimately show "R = {\<zero>}" by auto
qed

text\<open>The sets $\{m\cdot x. x\in R\}$ and  $\{-m\cdot x. x\in R\}$
  are the same.\<close>

lemma (in ring0) Ring_ZF_1_L18: assumes A1: "m\<in>R"
  shows "{m\<cdot>x. x\<in>R} = {(\<rm>m)\<cdot>x. x\<in>R}"
proof
  { fix a assume "a \<in> {m\<cdot>x. x\<in>R}"
    then obtain x where "x\<in>R" and "a = m\<cdot>x"
      by auto
    with A1 have "(\<rm>x) \<in> R"  and "a = (\<rm>m)\<cdot>(\<rm>x)" 
      using Ring_ZF_1_L3 Ring_ZF_1_L7A by auto
    then have "a \<in> {(\<rm>m)\<cdot>x. x\<in>R}"
      by auto
  } then show "{m\<cdot>x. x\<in>R} \<subseteq> {(\<rm>m)\<cdot>x. x\<in>R}"
    by auto
next 
  { fix a assume "a \<in> {(\<rm>m)\<cdot>x. x\<in>R}"
    then obtain x where "x\<in>R" and "a = (\<rm>m)\<cdot>x"
      by auto
    with A1 have "(\<rm>x) \<in> R" and "a = m\<cdot>(\<rm>x)"
      using Ring_ZF_1_L3 Ring_ZF_1_L7 by auto
    then have "a \<in> {m\<cdot>x. x\<in>R}" by auto
  } then show "{(\<rm>m)\<cdot>x. x\<in>R} \<subseteq> {m\<cdot>x. x\<in>R}"
    by auto
qed

subsection\<open>Rearrangement lemmas\<close>

text\<open>In happens quite often that we want to show a fact like 
  $(a+b)c+d = (ac+d-e)+(bc+e)$in rings. 
  This is trivial in romantic math and probably there is a way to make 
  it trivial in formalized math. However, I don't know any other way than to
  tediously prove each such rearrangement when it is needed. This section 
  collects facts of this type.\<close>

text\<open>Rearrangements with two elements of a ring.\<close>

lemma (in ring0) Ring_ZF_2_L1: assumes "a\<in>R" "b\<in>R" 
  shows "a\<ra>b\<cdot>a = (b\<ra>\<one>)\<cdot>a"
  using assms Ring_ZF_1_L2 ring_oper_distr Ring_ZF_1_L3 Ring_ZF_1_L4
  by simp

text\<open>Rearrangements with two elements and cancelling.\<close>

lemma (in ring0) Ring_ZF_2_L1A: assumes "a\<in>R" "b\<in>R" 
  shows
  "a\<rs>b\<ra>b = a"
  "a\<ra>b\<rs>a = b"
  "(\<rm>a)\<ra>b\<ra>a = b"
  "(\<rm>a)\<ra>(b\<ra>a) = b"
  "a\<ra>(b\<rs>a) = b"
  using assms Ring_ZF_1_L1 group0.inv_cancel_two group0.group0_4_L6A
  by auto

text\<open>In commutative rings $a-(b+1)c = (a-d-c)+(d-bc)$. For unknown reasons 
  we have to use the raw set notation in the proof, otherwise all methods 
  fail.\<close>

lemma (in ring0) Ring_ZF_2_L2: 
  assumes A1: "a\<in>R"  "b\<in>R"  "c\<in>R"  "d\<in>R"
  shows "a\<rs>(b\<ra>\<one>)\<cdot>c = (a\<rs>d\<rs>c)\<ra>(d\<rs>b\<cdot>c)"
proof -
  let ?B = "b\<cdot>c" 
  from ringAssum have "A {is commutative on} R"
    using IsAring_def by simp
  moreover from A1 have "a\<in>R" "?B \<in> R" "c\<in>R" "d\<in>R"
    using Ring_ZF_1_L4 by auto
  ultimately have "A`\<langle>a, GroupInv(R,A)`(A`\<langle>?B, c\<rangle>)\<rangle> =
    A`\<langle>A`\<langle>A`\<langle>a, GroupInv(R, A)`(d)\<rangle>,GroupInv(R, A)`(c)\<rangle>,
    A`\<langle>d,GroupInv(R, A)`(?B)\<rangle>\<rangle>"
    using Ring_ZF_1_L1 group0.group0_4_L8 by blast
  with A1 show ?thesis 
    using Ring_ZF_1_L2 ring_oper_distr Ring_ZF_1_L3 by simp
qed

text\<open>Rerrangement about adding linear functions.\<close>

lemma (in ring0) Ring_ZF_2_L3: 
  assumes A1: "a\<in>R"  "b\<in>R"  "c\<in>R"  "d\<in>R"  "x\<in>R"
  shows "(a\<cdot>x \<ra> b) \<ra> (c\<cdot>x \<ra> d) = (a\<ra>c)\<cdot>x \<ra> (b\<ra>d)"
proof -
  from A1 have 
    "group0(R,A)"
    "A {is commutative on} R"
    "a\<cdot>x \<in> R"  "b\<in>R"  "c\<cdot>x \<in> R"  "d\<in>R" 
    using Ring_ZF_1_L1 Ring_ZF_1_L4 by auto
  then have "A`\<langle>A`\<langle> a\<cdot>x,b\<rangle>,A`\<langle> c\<cdot>x,d\<rangle>\<rangle> = A`\<langle>A`\<langle> a\<cdot>x,c\<cdot>x\<rangle>,A`\<langle> b,d\<rangle>\<rangle>"
    by (rule group0.group0_4_L8)
  with A1 show 
    "(a\<cdot>x \<ra> b) \<ra> (c\<cdot>x \<ra> d) = (a\<ra>c)\<cdot>x \<ra> (b\<ra>d)"
    using ring_oper_distr by simp
qed

text\<open>Rearrangement with three elements\<close>

lemma (in ring0) Ring_ZF_2_L4: 
  assumes "M {is commutative on} R"
  and "a\<in>R"  "b\<in>R"  "c\<in>R"
  shows "a\<cdot>(b\<cdot>c) = a\<cdot>c\<cdot>b"
  using assms IsCommutative_def Ring_ZF_1_L11
  by simp

text\<open>Some other rearrangements with three elements.\<close>

lemma (in ring0) ring_rearr_3_elemA:
  assumes A1: "M {is commutative on} R" and 
  A2: "a\<in>R"  "b\<in>R"  "c\<in>R"
  shows 
  "a\<cdot>(a\<cdot>c) \<rs> b\<cdot>(\<rm>b\<cdot>c) = (a\<cdot>a \<ra> b\<cdot>b)\<cdot>c"
  "a\<cdot>(\<rm>b\<cdot>c) \<ra> b\<cdot>(a\<cdot>c) = \<zero>"
proof -
  from A2 have T: 
    "b\<cdot>c \<in> R"  "a\<cdot>a \<in> R"  "b\<cdot>b \<in> R"
    "b\<cdot>(b\<cdot>c) \<in> R"  "a\<cdot>(b\<cdot>c) \<in> R"
    using  Ring_ZF_1_L4 by auto
  with A2 show 
    "a\<cdot>(a\<cdot>c) \<rs> b\<cdot>(\<rm>b\<cdot>c) = (a\<cdot>a \<ra> b\<cdot>b)\<cdot>c"
    using Ring_ZF_1_L7 Ring_ZF_1_L3 Ring_ZF_1_L11 
      ring_oper_distr by simp
  from A2 T have 
    "a\<cdot>(\<rm>b\<cdot>c) \<ra> b\<cdot>(a\<cdot>c) = (\<rm>a\<cdot>(b\<cdot>c)) \<ra> b\<cdot>a\<cdot>c"
    using Ring_ZF_1_L7 Ring_ZF_1_L11 by simp
  also from A1 A2 T have "\<dots> = \<zero>"
    using IsCommutative_def Ring_ZF_1_L11 Ring_ZF_1_L3
    by simp
  finally show "a\<cdot>(\<rm>b\<cdot>c) \<ra> b\<cdot>(a\<cdot>c) = \<zero>"
    by simp
qed

text\<open>Some rearrangements with four elements. Properties of abelian groups.\<close>

lemma (in ring0) Ring_ZF_2_L5: 
  assumes "a\<in>R"  "b\<in>R"  "c\<in>R"  "d\<in>R"
  shows 
  "a \<rs> b \<rs> c \<rs> d = a \<rs> d \<rs> b \<rs> c"
  "a \<ra> b \<ra> c \<rs> d = a \<rs> d \<ra> b \<ra> c"
  "a \<ra> b \<rs> c \<rs> d = a \<rs> c \<ra> (b \<rs> d)"
  "a \<ra> b \<ra> c \<ra> d = a \<ra> c \<ra> (b \<ra> d)"
  using assms Ring_ZF_1_L1 group0.rearr_ab_gr_4_elemB
    group0.rearr_ab_gr_4_elemA by auto

text\<open>Two big rearranegements with six elements, useful for
  proving properties of complex addition and multiplication.\<close>

lemma (in ring0) Ring_ZF_2_L6:
  assumes A1: "a\<in>R"  "b\<in>R"  "c\<in>R"  "d\<in>R"  "e\<in>R"  "f\<in>R"
  shows
  "a\<cdot>(c\<cdot>e \<rs> d\<cdot>f) \<rs> b\<cdot>(c\<cdot>f \<ra> d\<cdot>e) =
  (a\<cdot>c \<rs> b\<cdot>d)\<cdot>e \<rs> (a\<cdot>d \<ra> b\<cdot>c)\<cdot>f"
  "a\<cdot>(c\<cdot>f \<ra> d\<cdot>e) \<ra> b\<cdot>(c\<cdot>e \<rs> d\<cdot>f) =
  (a\<cdot>c \<rs> b\<cdot>d)\<cdot>f \<ra> (a\<cdot>d \<ra> b\<cdot>c)\<cdot>e"
  "a\<cdot>(c\<ra>e) \<rs> b\<cdot>(d\<ra>f) = a\<cdot>c \<rs> b\<cdot>d \<ra> (a\<cdot>e \<rs> b\<cdot>f)"
  "a\<cdot>(d\<ra>f) \<ra> b\<cdot>(c\<ra>e) = a\<cdot>d \<ra> b\<cdot>c \<ra> (a\<cdot>f \<ra> b\<cdot>e)"
proof -
  from A1 have T:
    "c\<cdot>e \<in> R"  "d\<cdot>f \<in> R"  "c\<cdot>f \<in> R"  "d\<cdot>e \<in> R"
    "a\<cdot>c \<in> R"  "b\<cdot>d \<in> R"  "a\<cdot>d \<in> R"  "b\<cdot>c \<in> R"
    "b\<cdot>f \<in> R"  "a\<cdot>e \<in> R"  "b\<cdot>e \<in> R"  "a\<cdot>f \<in> R"
    "a\<cdot>c\<cdot>e \<in> R"  "a\<cdot>d\<cdot>f \<in> R"
    "b\<cdot>c\<cdot>f \<in> R"  "b\<cdot>d\<cdot>e \<in> R"
    "b\<cdot>c\<cdot>e \<in> R"  "b\<cdot>d\<cdot>f \<in> R"
    "a\<cdot>c\<cdot>f \<in> R"  "a\<cdot>d\<cdot>e \<in> R"
    "a\<cdot>c\<cdot>e \<rs> a\<cdot>d\<cdot>f \<in> R"
    "a\<cdot>c\<cdot>e \<rs> b\<cdot>d\<cdot>e \<in> R"
    "a\<cdot>c\<cdot>f \<ra> a\<cdot>d\<cdot>e \<in> R"
    "a\<cdot>c\<cdot>f \<rs> b\<cdot>d\<cdot>f \<in> R"
    "a\<cdot>c \<ra> a\<cdot>e \<in> R"
    "a\<cdot>d \<ra> a\<cdot>f \<in> R"
    using Ring_ZF_1_L4 by auto
  with A1 show "a\<cdot>(c\<cdot>e \<rs> d\<cdot>f) \<rs> b\<cdot>(c\<cdot>f \<ra> d\<cdot>e) =
    (a\<cdot>c \<rs> b\<cdot>d)\<cdot>e \<rs> (a\<cdot>d \<ra> b\<cdot>c)\<cdot>f"
    using Ring_ZF_1_L8 ring_oper_distr Ring_ZF_1_L11
      Ring_ZF_1_L10 Ring_ZF_2_L5 by simp
  from A1 T show 
    "a\<cdot>(c\<cdot>f \<ra> d\<cdot>e) \<ra> b\<cdot>(c\<cdot>e \<rs> d\<cdot>f) =
    (a\<cdot>c \<rs> b\<cdot>d)\<cdot>f \<ra> (a\<cdot>d \<ra> b\<cdot>c)\<cdot>e"
    using Ring_ZF_1_L8 ring_oper_distr Ring_ZF_1_L11
    Ring_ZF_1_L10A Ring_ZF_2_L5 Ring_ZF_1_L10 
    by simp
  from A1 T show 
    "a\<cdot>(c\<ra>e) \<rs> b\<cdot>(d\<ra>f) = a\<cdot>c \<rs> b\<cdot>d \<ra> (a\<cdot>e \<rs> b\<cdot>f)"
    "a\<cdot>(d\<ra>f) \<ra> b\<cdot>(c\<ra>e) = a\<cdot>d \<ra> b\<cdot>c \<ra> (a\<cdot>f \<ra> b\<cdot>e)"
    using ring_oper_distr Ring_ZF_1_L10 Ring_ZF_2_L5
    by auto
qed

end
