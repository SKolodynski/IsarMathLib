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

section \<open>Ordered rings\<close>

theory OrderedRing_ZF imports Ring_ZF OrderedGroup_ZF_1

begin

text\<open>In this theory file we consider ordered rings.\<close>

subsection\<open>Definition and notation\<close>

text\<open>This section defines ordered rings and sets up appriopriate notation.\<close>

text\<open>We define ordered ring as a commutative ring with linear order 
  that is preserved by 
  translations and such that the set of nonnegative elements is closed
  under multiplication. Note that this definition does not guarantee 
  that there are no zero divisors in the ring.\<close>

definition
  "IsAnOrdRing(R,A,M,r) \<equiv> 
  ( IsAring(R,A,M) \<and> (M {is commutative on} R) \<and> 
  r\<subseteq>R\<times>R \<and> IsLinOrder(R,r) \<and>
  (\<forall>a b. \<forall> c\<in>R. \<langle> a,b\<rangle> \<in> r \<longrightarrow> \<langle>A`\<langle> a,c\<rangle>,A`\<langle> b,c\<rangle>\<rangle> \<in> r) \<and>
  (Nonnegative(R,A,r) {is closed under} M))"

text\<open>The next context (locale) defines notation used for ordered rings. 
  We do that by extending the notation defined in the 
  \<open>ring0\<close> locale and adding some assumptions to make sure we are 
  talking about ordered rings in this context.\<close>

locale ring1 = ring0 +

  assumes mult_commut: "M {is commutative on} R" 

  fixes r
  
  assumes ordincl: "r \<subseteq> R\<times>R"

  assumes linord: "IsLinOrder(R,r)"
  
  fixes lesseq (infix "\<lsq>" 68)
  defines lesseq_def [simp]: "a \<lsq> b \<equiv> \<langle> a,b\<rangle> \<in> r"

  fixes sless (infix "\<ls>" 68)
  defines sless_def [simp]: "a \<ls> b \<equiv> a\<lsq>b \<and> a\<noteq>b"

  assumes ordgroup: "\<forall>a b. \<forall> c\<in>R. a\<lsq>b \<longrightarrow> a\<ra>c \<lsq> b\<ra>c"

  assumes pos_mult_closed: "Nonnegative(R,A,r) {is closed under} M"

  fixes abs ("\<bar> _ \<bar>")
  defines abs_def [simp]: "\<bar>a\<bar> \<equiv> AbsoluteValue(R,A,r)`(a)"

  fixes positiveset ("R\<^sub>+")
  defines positiveset_def [simp]: "R\<^sub>+ \<equiv> PositiveSet(R,A,r)"

text\<open>The next lemma assures us that we are talking about ordered rings 
  in the \<open>ring1\<close> context.\<close>

lemma (in ring1) OrdRing_ZF_1_L1: shows "IsAnOrdRing(R,A,M,r)"
  using ring0_def ringAssum mult_commut ordincl linord ordgroup 
    pos_mult_closed IsAnOrdRing_def by simp

text\<open>We can use theorems proven in the \<open>ring1\<close> context whenever we
  talk about an ordered ring.\<close>

lemma OrdRing_ZF_1_L2: assumes "IsAnOrdRing(R,A,M,r)"
  shows "ring1(R,A,M,r)"
  using assms IsAnOrdRing_def ring1_axioms.intro ring0_def ring1_def
  by simp

text\<open>In the \<open>ring1\<close> context $a\leq b$ implies that $a,b$ are
  elements of the ring.\<close>

lemma (in ring1) OrdRing_ZF_1_L3: assumes "a\<lsq>b"
  shows "a\<in>R"  "b\<in>R"
  using assms ordincl by auto

text\<open>In the \<open>ring1\<close> context $a < b$ implies that $a,b$ are
  elements of the ring.\<close>

lemma (in  ring1) ord_ring_less_members: assumes "a\<ls>b"
  shows "a\<in>R"  "b\<in>R"
  using assms OrdRing_ZF_1_L3 by auto

text\<open>Ordered ring is an ordered group, hence we can use theorems
  proven in the \<open>group3\<close> context.\<close>

lemma (in  ring1) OrdRing_ZF_1_L4: shows 
  "IsAnOrdGroup(R,A,r)"
  "r {is total on} R"
  "A {is commutative on} R"
  "group3(R,A,r)"
proof -
  { fix a b g assume A1: "g\<in>R" and A2: "a\<lsq>b" 
    with ordgroup have "a\<ra>g \<lsq> b\<ra>g"
      by simp
    moreover from ringAssum A1 A2 have 
      "a\<ra>g = g\<ra>a"  "b\<ra>g = g\<ra>b"
      using OrdRing_ZF_1_L3 IsAring_def IsCommutative_def by auto
    ultimately have
      "a\<ra>g \<lsq> b\<ra>g"  "g\<ra>a \<lsq> g\<ra>b"
      by auto
  } hence 
    "\<forall>g\<in>R. \<forall>a b. a\<lsq>b \<longrightarrow> a\<ra>g \<lsq> b\<ra>g \<and> g\<ra>a \<lsq> g\<ra>b"
    by simp
  with ringAssum ordincl linord show  
    "IsAnOrdGroup(R,A,r)"
    "group3(R,A,r)"
    "r {is total on} R"
    "A {is commutative on} R"
    using IsAring_def Order_ZF_1_L2 IsAnOrdGroup_def group3_def IsLinOrder_def
    by auto
qed

text\<open>We can express that $x$ is positive by stating that $0<x$ or by writing that $x$ is an
  element $R_+$.\<close>

lemma (in  ring1) element_pos: shows "a\<in>R\<^sub>+ \<longleftrightarrow> \<zero>\<ls>a"
  using OrdRing_ZF_1_L4(4) group3.OrderedGroup_ZF_1_L2A by auto

text\<open>The order relation in rings is transitive.\<close>

lemma (in ring1) ring_ord_transitive: assumes A1: "a\<lsq>b"  "b\<lsq>c"
  shows "a\<lsq>c"
proof -
  from A1 have 
    "group3(R,A,r)"  "\<langle>a,b\<rangle> \<in> r"   "\<langle>b,c\<rangle> \<in> r"
    using OrdRing_ZF_1_L4 by auto
  then have "\<langle>a,c\<rangle> \<in> r" by (rule group3.Group_order_transitive)
  then show  "a\<lsq>c" by simp
qed

text\<open>Transitivity for the strict order: if $a < b$ and $b\leq c$, then $a < c$. 
  Property of ordered groups.\<close>

lemma (in ring1) ring_strict_ord_trans:  
  assumes A1: "a\<ls>b" and A2: "b\<lsq>c"
  shows "a\<ls>c"
proof -
  from A1 A2 have
    "group3(R,A,r)"  
    "\<langle>a,b\<rangle> \<in> r \<and> a\<noteq>b"  "\<langle>b,c\<rangle> \<in> r"
    using OrdRing_ZF_1_L4 by auto
    then have "\<langle>a,c\<rangle> \<in> r \<and> a\<noteq>c" by (rule group3.OrderedGroup_ZF_1_L4A)
    then show "a\<ls>c" by simp
qed

text\<open>Another version of transitivity for the strict order: 
  if $a\leq b$ and $b<c$, then $a<c$. Property of ordered groups.\<close>

lemma (in ring1) ring_strict_ord_transit: 
  assumes A1: "a\<lsq>b" and A2: "b\<ls>c"
  shows "a\<ls>c"
proof -
  from A1 A2 have
    "group3(R,A,r)"  
    "\<langle>a,b\<rangle> \<in> r"  "\<langle>b,c\<rangle> \<in> r \<and> b\<noteq>c"
    using OrdRing_ZF_1_L4 by auto
  then have "\<langle>a,c\<rangle> \<in> r \<and> a\<noteq>c" by (rule group3.group_strict_ord_transit)
  then show "a\<ls>c" by simp
qed

text\<open>The ring order is reflexive.\<close>

lemma (in ring1) ring_ord_refl: assumes "a\<in>R" shows "a\<lsq>a"
  using assms OrdRing_ZF_1_L4(4) group3.OrderedGroup_ZF_1_L3 by simp

text\<open>The next lemma shows what happens when one element of an ordered
  ring is not greater or equal than another.\<close>

lemma (in ring1) OrdRing_ZF_1_L4A: assumes A1: "a\<in>R"  "b\<in>R"
  and A2: "\<not>(a\<lsq>b)"
  shows "b \<lsq> a"  "(\<rm>a) \<lsq> (\<rm>b)"  "a\<noteq>b"
proof -
  from A1 A2 have I: 
    "group3(R,A,r)"
    "r {is total on} R"
    "a \<in> R"  "b \<in> R"  "\<langle>a, b\<rangle> \<notin> r"
    using OrdRing_ZF_1_L4 by auto
  then have "\<langle>b,a\<rangle> \<in> r" by (rule group3.OrderedGroup_ZF_1_L8)
  then show "b \<lsq> a" by simp
  from I have "\<langle>GroupInv(R,A)`(a),GroupInv(R,A)`(b)\<rangle> \<in> r"
    by (rule group3.OrderedGroup_ZF_1_L8)
  then show  "(\<rm>a) \<lsq> (\<rm>b)" by simp
  from I show "a\<noteq>b" by (rule group3.OrderedGroup_ZF_1_L8)
qed

text\<open>A special case of \<open>OrdRing_ZF_1_L4A\<close> when one of the
  constants is $0$. This is useful for many proofs by cases.\<close>

corollary (in ring1) ord_ring_split2: assumes A1: "a\<in>R" 
  shows "a\<lsq>\<zero> \<or> (\<zero>\<lsq>a \<and> a\<noteq>\<zero>)"
proof -
  { from A1 have  I: "a\<in>R"  "\<zero>\<in>R"
      using Ring_ZF_1_L2 by auto 
    moreover assume A2: "\<not>(a\<lsq>\<zero>)"
    ultimately have "\<zero>\<lsq>a" by (rule OrdRing_ZF_1_L4A)
    moreover from I A2 have "a\<noteq>\<zero>" by (rule OrdRing_ZF_1_L4A)
    ultimately have "\<zero>\<lsq>a \<and> a\<noteq>\<zero>" by simp}
  then show ?thesis by auto
qed

text\<open>Taking minus on both sides reverses an inequality.\<close>

lemma (in ring1) OrdRing_ZF_1_L4B: assumes "a\<lsq>b"
  shows "(\<rm>b) \<lsq> (\<rm>a)"
  using assms OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L5
  by simp

text\<open>The next lemma just expands the condition that requires the set
  of nonnegative elements to be closed with respect to multiplication.
  These are properties of totally ordered groups.\<close>
  
lemma (in  ring1) OrdRing_ZF_1_L5: 
  assumes "\<zero>\<lsq>a"  "\<zero>\<lsq>b"
  shows "\<zero> \<lsq> a\<cdot>b"
  using pos_mult_closed assms OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L2
  IsOpClosed_def by simp

text\<open>Double nonnegative is nonnegative.\<close>

lemma (in  ring1) OrdRing_ZF_1_L5A: assumes A1: "\<zero>\<lsq>a"
  shows "\<zero>\<lsq>\<two>\<cdot>a"
  using assms OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L5G
  OrdRing_ZF_1_L3 Ring_ZF_1_L3 by simp

text\<open>A sufficient (somewhat redundant) condition for a structure to be an 
  ordered ring. It says that a commutative ring that is a totally ordered
  group with respect to the additive operation such that set of nonnegative 
  elements is closed under multiplication, is an ordered ring.\<close>

lemma OrdRing_ZF_1_L6:
  assumes  
  "IsAring(R,A,M)"   
  "M {is commutative on} R"
  "Nonnegative(R,A,r) {is closed under} M"
  "IsAnOrdGroup(R,A,r)"  
  "r {is total on} R"
  shows "IsAnOrdRing(R,A,M,r)"
  using assms IsAnOrdGroup_def Order_ZF_1_L3 IsAnOrdRing_def
  by simp

text\<open> $a\leq b$ iff $a-b\leq 0$. This is a fact from 
  \<open>OrderedGroup.thy\<close>, where it is stated in multiplicative notation.\<close>

lemma (in ring1) OrdRing_ZF_1_L7:
  assumes "a\<in>R"  "b\<in>R"
  shows "a\<lsq>b \<longleftrightarrow> a\<rs>b \<lsq> \<zero>"
  using assms OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L9
  by simp

text\<open>Negative times positive is negative.\<close>

lemma (in ring1) OrdRing_ZF_1_L8:
  assumes A1: "a\<lsq>\<zero>"  and A2: "\<zero>\<lsq>b"
  shows "a\<cdot>b \<lsq> \<zero>"
proof -
  from A1 A2 have T1: "a\<in>R"  "b\<in>R"  "a\<cdot>b \<in> R"
    using OrdRing_ZF_1_L3 Ring_ZF_1_L4 by auto
  from A1 A2 have "\<zero>\<lsq>(\<rm>a)\<cdot>b" 
    using OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L5A OrdRing_ZF_1_L5
    by simp
  with T1 show "a\<cdot>b \<lsq> \<zero>"
    using Ring_ZF_1_L7 OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L5AA
    by simp
qed

text\<open>We can multiply both sides of an inequality by a nonnegative ring
  element. This property is sometimes (not here) used to define
  ordered rings.\<close>

lemma (in ring1) OrdRing_ZF_1_L9:
  assumes A1: "a\<lsq>b" and A2: "\<zero>\<lsq>c"
  shows 
  "a\<cdot>c \<lsq> b\<cdot>c"  
  "c\<cdot>a \<lsq> c\<cdot>b"
proof -
  from A1 A2 have T1:
    "a\<in>R"  "b\<in>R"  "c\<in>R"  "a\<cdot>c \<in> R"  "b\<cdot>c \<in> R"
    using OrdRing_ZF_1_L3 Ring_ZF_1_L4 by auto
  with A1 A2 have "(a\<rs>b)\<cdot>c \<lsq> \<zero>"
    using OrdRing_ZF_1_L7 OrdRing_ZF_1_L8 by simp
  with T1 show "a\<cdot>c \<lsq> b\<cdot>c"
    using Ring_ZF_1_L8 OrdRing_ZF_1_L7 by simp
  with mult_commut T1 show "c\<cdot>a \<lsq> c\<cdot>b"
    using IsCommutative_def by simp
qed

text\<open>A special case of \<open>OrdRing_ZF_1_L9\<close>: we can multiply
  an inequality by a positive ring element.\<close>

lemma (in ring1) OrdRing_ZF_1_L9A:
  assumes A1: "a\<lsq>b" and A2: "c\<in>R\<^sub>+"
  shows  
  "a\<cdot>c \<lsq> b\<cdot>c"  
  "c\<cdot>a \<lsq> c\<cdot>b"
proof -
  from A2 have "\<zero> \<lsq> c" using PositiveSet_def
    by simp
  with A1 show "a\<cdot>c \<lsq> b\<cdot>c"  "c\<cdot>a \<lsq> c\<cdot>b"
    using OrdRing_ZF_1_L9 by auto
qed    

text\<open>A square is nonnegative.\<close>

lemma (in ring1) OrdRing_ZF_1_L10:
  assumes A1: "a\<in>R" shows "\<zero>\<lsq>(a\<^sup>2)"
proof -
  { assume "\<zero>\<lsq>a"
    then have "\<zero>\<lsq>(a\<^sup>2)" using OrdRing_ZF_1_L5 by simp}
  moreover
  { assume "\<not>(\<zero>\<lsq>a)"
    with A1 have "\<zero>\<lsq>((\<rm>a)\<^sup>2)"
      using OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L8A
	OrdRing_ZF_1_L5 by simp
    with A1 have "\<zero>\<lsq>(a\<^sup>2)" using Ring_ZF_1_L14 by simp }
  ultimately show ?thesis by blast
qed

text\<open>$1$ is nonnegative.\<close>

corollary (in ring1) ordring_one_is_nonneg: shows "\<zero> \<lsq> \<one>"
proof -
  have "\<zero> \<lsq> (\<one>\<^sup>2)" using Ring_ZF_1_L2 OrdRing_ZF_1_L10
    by simp
  then show "\<zero> \<lsq> \<one>" using Ring_ZF_1_L2 Ring_ZF_1_L3
    by simp
qed

text\<open>In nontrivial rings one is positive.\<close>

lemma (in ring1) ordring_one_is_pos: assumes "\<zero>\<noteq>\<one>"
  shows "\<one> \<in> R\<^sub>+" "\<zero>\<ls>\<one>"
  using assms Ring_ZF_1_L2 ordring_one_is_nonneg PositiveSet_def
  by simp_all
    
text\<open>Nonnegative is not negative. Property of ordered groups.\<close>

lemma (in ring1) OrdRing_ZF_1_L11: assumes "\<zero>\<lsq>a"
  shows "\<not>(a\<lsq>\<zero> \<and> a\<noteq>\<zero>)"
  using assms OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L5AB
  by simp

text\<open>A negative element cannot be a square.\<close>

lemma (in ring1) OrdRing_ZF_1_L12: 
  assumes A1: "a\<lsq>\<zero>"  "a\<noteq>\<zero>"
  shows "\<not>(\<exists>b\<in>R. a = (b\<^sup>2))"
proof -
  { assume "\<exists>b\<in>R. a = (b\<^sup>2)"
    with A1 have False using OrdRing_ZF_1_L10 OrdRing_ZF_1_L11
      by auto
  } then show ?thesis by auto
qed

text\<open>If $a\leq b$, then $0\leq b-a$.\<close>

lemma (in ring1) OrdRing_ZF_1_L13: assumes "a\<lsq>b"
  shows "\<zero> \<lsq> b\<rs>a"
  using assms OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L9D
  by simp

text\<open>If $a < b$, then $0 < b-a$.\<close>

lemma (in ring1) OrdRing_ZF_1_L14: assumes "a\<lsq>b"  "a\<noteq>b"
  shows 
  "\<zero> \<lsq> b\<rs>a"  "\<zero> \<noteq> b\<rs>a"  
  "b\<rs>a \<in> R\<^sub>+"
  using assms OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L9E
  by auto

text\<open>If the difference is nonnegative, then $a\leq b$.\<close>

lemma (in ring1) OrdRing_ZF_1_L15: 
  assumes "a\<in>R" "b\<in>R" and "\<zero> \<lsq> b\<rs>a"
  shows "a\<lsq>b"
  using assms OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L9F
  by simp
  

text\<open>A nonnegative number is does not decrease when multiplied by 
  a number greater or equal $1$.\<close>

lemma (in ring1) OrdRing_ZF_1_L16: 
  assumes A1: "\<zero>\<lsq>a" and A2: "\<one>\<lsq>b"
  shows "a\<lsq>a\<cdot>b"
proof -
  from A1 A2 have T: "a\<in>R"  "b\<in>R"  "a\<cdot>b \<in> R"
    using OrdRing_ZF_1_L3 Ring_ZF_1_L4 by auto
  from A1 A2 have "\<zero> \<lsq> a\<cdot>(b\<rs>\<one>)"
    using OrdRing_ZF_1_L13 OrdRing_ZF_1_L5 by simp
  with T show "a\<lsq>a\<cdot>b"
    using Ring_ZF_1_L8 Ring_ZF_1_L2 Ring_ZF_1_L3 OrdRing_ZF_1_L15
    by simp
qed
  
text\<open>We can multiply the right hand side of an inequality between
  nonnegative ring elements by an element greater or equal $1$.\<close>

lemma (in ring1) OrdRing_ZF_1_L17: 
  assumes A1: "\<zero>\<lsq>a" and A2: "a\<lsq>b" and A3: "\<one>\<lsq>c"
  shows "a\<lsq>b\<cdot>c"
proof -
  from A1 A2 have "\<zero>\<lsq>b" by (rule ring_ord_transitive)
  with A3 have "b\<lsq>b\<cdot>c" using OrdRing_ZF_1_L16
    by simp
  with A2 show "a\<lsq>b\<cdot>c" by (rule ring_ord_transitive)
qed

text\<open>Strict order is preserved by translations.\<close>

lemma (in ring1) ring_strict_ord_trans_inv: 
  assumes "a\<ls>b" and "c\<in>R"
  shows  
  "a\<ra>c \<ls> b\<ra>c"
  "c\<ra>a \<ls> c\<ra>b"
  using assms OrdRing_ZF_1_L4 group3.group_strict_ord_transl_inv
  by auto

text\<open>We can put an element on the other side of a strict inequality,
  changing its sign.\<close>

lemma (in ring1) OrdRing_ZF_1_L18:
  assumes "a\<in>R"  "b\<in>R" and  "a\<rs>b \<ls> c"
  shows "a \<ls> c\<ra>b"
  using assms OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L12B
  by simp

text\<open>We can add the sides of two inequalities,
  the first of them strict, and we get a strict inequality. 
  Property of ordered groups.\<close>

lemma (in ring1) OrdRing_ZF_1_L19:
  assumes "a\<ls>b" and "c\<lsq>d"
  shows "a\<ra>c \<ls> b\<ra>d"
  using assms OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L12C
  by simp

text\<open>We can add the sides of two inequalities,
  the second of them strict and we get a strict inequality. 
  Property of ordered groups.\<close>

lemma (in ring1) OrdRing_ZF_1_L20:
  assumes "a\<lsq>b" and "c\<ls>d"
  shows "a\<ra>c \<ls> b\<ra>d"
  using assms OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L12D
  by simp

text\<open>In a non-trivial ring one is less than two.\<close> 

lemma (in ring1) one_less_two: assumes "\<zero>\<noteq>\<one>" shows "\<one>\<ls>\<two>"
  using assms ordring_one_is_pos Ring_ZF_1_L2(2) ring_strict_ord_trans_inv(1) 
    Ring_ZF_1_L3(4) by force

text\<open>In a non-trivial ring two is positive.\<close>

lemma (in ring1) two_positive: assumes "\<zero>\<noteq>\<one>" shows "\<two> \<in> R\<^sub>+" "\<zero>\<ls>\<two>"
  using assms ordring_one_is_pos one_less_two ring_strict_ord_transit element_pos
    by simp_all

subsection\<open>Absolute value for ordered rings\<close>

text\<open>Absolute value is defined for ordered groups as a function 
  that is the identity on the nonnegative set and the negative of the element 
  (the inverse in the multiplicative notation) on the rest. In this section
  we consider properties of absolute value related to multiplication in 
  ordered rings.\<close>


text\<open>Absolute value of a product is the product of absolute values: 
  the case when both elements of the ring are nonnegative.\<close>

lemma (in ring1) OrdRing_ZF_2_L1: 
  assumes "\<zero>\<lsq>a" "\<zero>\<lsq>b"
  shows "\<bar>a\<cdot>b\<bar> = \<bar>a\<bar>\<cdot>\<bar>b\<bar>"
  using assms OrdRing_ZF_1_L5 OrdRing_ZF_1_L4 
    group3.OrderedGroup_ZF_1_L2 group3.OrderedGroup_ZF_3_L2
  by simp

text\<open>The absolue value of an element and its negative are the same.\<close>

lemma (in ring1) OrdRing_ZF_2_L2: assumes "a\<in>R"
  shows "\<bar>\<rm>a\<bar> = \<bar>a\<bar>"
  using assms OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_3_L7A by simp

text\<open>The next lemma states that 
  $|a\cdot (-b)| = |(-a)\cdot b| = |(-a)\cdot (-b)| = |a\cdot b|$.\<close>

lemma (in ring1) OrdRing_ZF_2_L3:
  assumes "a\<in>R"  "b\<in>R"
  shows 
  "\<bar>(\<rm>a)\<cdot>b\<bar> = \<bar>a\<cdot>b\<bar>"
  "\<bar>a\<cdot>(\<rm>b)\<bar> = \<bar>a\<cdot>b\<bar>"
  "\<bar>(\<rm>a)\<cdot>(\<rm>b)\<bar> = \<bar>a\<cdot>b\<bar>"
  using assms Ring_ZF_1_L4 Ring_ZF_1_L7 Ring_ZF_1_L7A 
   OrdRing_ZF_2_L2 by auto

text\<open>This lemma allows to prove theorems for the case of positive and 
  negative elements of the ring separately.\<close>

lemma (in ring1) OrdRing_ZF_2_L4: assumes "a\<in>R" and "\<not>(\<zero>\<lsq>a)" 
  shows "\<zero> \<lsq> (\<rm>a)"  "\<zero>\<noteq>a"
  using assms OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L8A
  by auto
  
text\<open>Absolute value of a product is the product of absolute values.\<close>

lemma (in ring1) OrdRing_ZF_2_L5:
  assumes A1: "a\<in>R" "b\<in>R"
  shows "\<bar>a\<cdot>b\<bar> = \<bar>a\<bar>\<cdot>\<bar>b\<bar>"
proof -
  { assume A2: "\<zero>\<lsq>a" have "\<bar>a\<cdot>b\<bar> = \<bar>a\<bar>\<cdot>\<bar>b\<bar>"
    proof -
      { assume "\<zero>\<lsq>b"
	with A2 have "\<bar>a\<cdot>b\<bar> = \<bar>a\<bar>\<cdot>\<bar>b\<bar>"
	  using OrdRing_ZF_2_L1 by simp }
      moreover
      { assume "\<not>(\<zero>\<lsq>b)" 
	with A1 A2 have "\<bar>a\<cdot>(\<rm>b)\<bar> = \<bar>a\<bar>\<cdot>\<bar>\<rm>b\<bar>"
	  using OrdRing_ZF_2_L4 OrdRing_ZF_2_L1 by simp
	with A1 have "\<bar>a\<cdot>b\<bar> = \<bar>a\<bar>\<cdot>\<bar>b\<bar>"
	  using OrdRing_ZF_2_L2 OrdRing_ZF_2_L3 by simp }
      ultimately show ?thesis by blast
    qed }
  moreover
  { assume "\<not>(\<zero>\<lsq>a)"
    with A1 have A3: "\<zero> \<lsq> (\<rm>a)"
      using OrdRing_ZF_2_L4 by simp
    have "\<bar>a\<cdot>b\<bar> = \<bar>a\<bar>\<cdot>\<bar>b\<bar>"
    proof -
      { assume "\<zero>\<lsq>b" 
	with A3 have "\<bar>(\<rm>a)\<cdot>b\<bar> = \<bar>\<rm>a\<bar>\<cdot>\<bar>b\<bar>"
	  using OrdRing_ZF_2_L1 by simp
	with A1 have "\<bar>a\<cdot>b\<bar> = \<bar>a\<bar>\<cdot>\<bar>b\<bar>"
	  using OrdRing_ZF_2_L2 OrdRing_ZF_2_L3 by simp }
      moreover
      { assume "\<not>(\<zero>\<lsq>b)"
	with A1 A3 have "\<bar>(\<rm>a)\<cdot>(\<rm>b)\<bar> = \<bar>\<rm>a\<bar>\<cdot>\<bar>\<rm>b\<bar>"
	  using OrdRing_ZF_2_L4 OrdRing_ZF_2_L1 by simp
	with A1 have "\<bar>a\<cdot>b\<bar> = \<bar>a\<bar>\<cdot>\<bar>b\<bar>"
	  using OrdRing_ZF_2_L2 OrdRing_ZF_2_L3 by simp }
      ultimately show ?thesis by blast
    qed }
  ultimately show ?thesis by blast
qed

text\<open>Triangle inequality. Property of linearly ordered abelian groups.\<close>

lemma (in ring1) ord_ring_triangle_ineq:  assumes "a\<in>R" "b\<in>R"
  shows "\<bar>a\<ra>b\<bar> \<lsq> \<bar>a\<bar>\<ra>\<bar>b\<bar>"
  using assms OrdRing_ZF_1_L4 group3.OrdGroup_triangle_ineq 
  by simp

text\<open>If $a\leq c$ and $b\leq c$, then $a+b\leq 2\cdot c$.\<close>

lemma (in ring1) OrdRing_ZF_2_L6:
  assumes "a\<lsq>c"  "b\<lsq>c" shows "a\<ra>b \<lsq> \<two>\<cdot>c"
  using assms OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L5B 
    OrdRing_ZF_1_L3 Ring_ZF_1_L3 by simp

subsection\<open>Positivity in ordered rings\<close>

text\<open>This section is about properties of the set of positive
  elements \<open>R\<^sub>+\<close>.\<close>

text\<open>The set of positive elements is closed under ring addition. 
  This is a property of ordered groups, we just reference a theorem
  from \<open>OrderedGroup_ZF\<close> theory in the proof.\<close>

lemma (in ring1) OrdRing_ZF_3_L1: shows "R\<^sub>+ {is closed under} A"
  using OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L13
  by simp

text\<open>Every element of a ring can be either in the postitive set, equal to
  zero or its opposite (the additive inverse) is in the positive set. 
  This is a property of ordered groups, we just reference a theorem
  from \<open>OrderedGroup_ZF\<close> theory.\<close>

lemma (in ring1) OrdRing_ZF_3_L2: assumes "a\<in>R"
  shows "Exactly_1_of_3_holds (a=\<zero>, a\<in>R\<^sub>+, (\<rm>a) \<in> R\<^sub>+)"
  using assms OrdRing_ZF_1_L4 group3.OrdGroup_decomp
  by simp

text\<open>If a ring element $a\neq 0$, and it is not positive, then 
  $-a$ is positive.\<close>

lemma (in ring1) OrdRing_ZF_3_L2A: assumes "a\<in>R"  "a\<noteq>\<zero>"  "a \<notin> R\<^sub>+"
  shows "(\<rm>a) \<in>  R\<^sub>+"
  using assms OrdRing_ZF_1_L4 group3.OrdGroup_cases
  by simp

text\<open>$R_+$ is closed under multiplication iff the ring has no zero divisors.\<close>

lemma (in ring1) OrdRing_ZF_3_L3: 
  shows "(R\<^sub>+ {is closed under} M)\<longleftrightarrow> HasNoZeroDivs(R,A,M)"
proof
  assume A1: "HasNoZeroDivs(R,A,M)"
  { fix a b assume "a\<in>R\<^sub>+"  "b\<in>R\<^sub>+"
    then have "\<zero>\<lsq>a"  "a\<noteq>\<zero>"  "\<zero>\<lsq>b"  "b\<noteq>\<zero>"
      using PositiveSet_def by auto
    with A1 have "a\<cdot>b \<in> R\<^sub>+"
      using OrdRing_ZF_1_L5 Ring_ZF_1_L2 OrdRing_ZF_1_L3 Ring_ZF_1_L12
	OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L2A
      by simp
  } then show  "R\<^sub>+ {is closed under} M" using IsOpClosed_def
    by simp
next assume A2: "R\<^sub>+ {is closed under} M"
  { fix a b assume A3: "a\<in>R"  "b\<in>R"  and "a\<noteq>\<zero>"  "b\<noteq>\<zero>"
    with A2 have "\<bar>a\<cdot>b\<bar> \<in> R\<^sub>+"
      using OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_3_L12 IsOpClosed_def
        OrdRing_ZF_2_L5 by simp
    with A3 have "a\<cdot>b \<noteq> \<zero>" 
      using PositiveSet_def Ring_ZF_1_L4 
	OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_3_L2A 
      by auto
  } then show "HasNoZeroDivs(R,A,M)" using HasNoZeroDivs_def 
    by auto
qed

text\<open>Another (in addition to \<open>OrdRing_ZF_1_L6\<close> sufficient condition 
  that defines order in an ordered ring starting from the positive set.\<close>

theorem (in ring0) ring_ord_by_positive_set:
  assumes
  A1: "M {is commutative on} R" and 
  A2: "P\<subseteq>R"  "P {is closed under} A"  "\<zero> \<notin> P" and
  A3: "\<forall>a\<in>R. a\<noteq>\<zero> \<longrightarrow> (a\<in>P) Xor ((\<rm>a) \<in> P)" and
  A4: "P {is closed under} M" and 
  A5: "r = OrderFromPosSet(R,A,P)"
  shows
  "IsAnOrdGroup(R,A,r)"
  "IsAnOrdRing(R,A,M,r)"
  "r {is total on} R"
  "PositiveSet(R,A,r) = P"
  "Nonnegative(R,A,r) = P \<union> {\<zero>}"
  "HasNoZeroDivs(R,A,M)"
proof -
  from A2 A3 A5 show
    I: "IsAnOrdGroup(R,A,r)"  "r {is total on} R" and 
    II: "PositiveSet(R,A,r) = P" and 
    III: "Nonnegative(R,A,r) = P \<union> {\<zero>}"
    using Ring_ZF_1_L1 group0.Group_ord_by_positive_set
    by auto
  from A2 A4 III have "Nonnegative(R,A,r) {is closed under} M"
    using Ring_ZF_1_L16 by simp
  with ringAssum A1 I show "IsAnOrdRing(R,A,M,r)"
    using OrdRing_ZF_1_L6 by simp
  with A4 II show "HasNoZeroDivs(R,A,M)"
    using OrdRing_ZF_1_L2 ring1.OrdRing_ZF_3_L3
    by auto
qed

text\<open>Nontrivial ordered rings are infinite. More precisely we assume 
  that the neutral
  element of the additive operation is not equal to the multiplicative neutral
  element and show that the the set of positive elements of the ring is not a 
  finite subset of the ring and the ring is not a finite subset of itself.\<close>

theorem (in ring1) ord_ring_infinite: assumes "\<zero>\<noteq>\<one>"
  shows 
  "R\<^sub>+ \<notin> Fin(R)"
  "R \<notin> Fin(R)"
  using assms Ring_ZF_1_L17 OrdRing_ZF_1_L4 group3.Linord_group_infinite
  by auto

text\<open>If every element of a nontrivial ordered ring can be dominated
  by an element from $B$, then we $B$ is not bounded and not finite.\<close>

lemma (in ring1) OrdRing_ZF_3_L4: 
  assumes "\<zero>\<noteq>\<one>" and "\<forall>a\<in>R. \<exists>b\<in>B. a\<lsq>b"
  shows 
  "\<not>IsBoundedAbove(B,r)"
  "B \<notin> Fin(R)"
  using assms Ring_ZF_1_L17 OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_2_L2A
  by auto
  

text\<open>If $m$ is greater or equal the multiplicative unit, then the set
  $\{m\cdot n: n\in R\}$ is infinite (unless the ring is trivial).\<close>

lemma (in ring1) OrdRing_ZF_3_L5: assumes A1: "\<zero>\<noteq>\<one>" and A2: "\<one>\<lsq>m"
  shows
  "{m\<cdot>x. x\<in>R\<^sub>+} \<notin> Fin(R)"
  "{m\<cdot>x. x\<in>R} \<notin> Fin(R)"
  "{(\<rm>m)\<cdot>x. x\<in>R} \<notin> Fin(R)"
proof -
  from A2 have T: "m\<in>R" using OrdRing_ZF_1_L3 by simp
  from A2 have "\<zero>\<lsq>\<one>"  "\<one>\<lsq>m"
    using ordring_one_is_nonneg by auto
  then have I: "\<zero>\<lsq>m" by (rule ring_ord_transitive)
  let ?B = "{m\<cdot>x. x\<in>R\<^sub>+}"
  { fix a assume A3: "a\<in>R"
    then have "a\<lsq>\<zero> \<or> (\<zero>\<lsq>a \<and> a\<noteq>\<zero>)"
      using ord_ring_split2 by simp
    moreover
    { assume A4: "a\<lsq>\<zero>"
      from A1 have "m\<cdot>\<one> \<in> ?B" using ordring_one_is_pos
	by auto
      with T have "m\<in>?B" using Ring_ZF_1_L3 by simp
      moreover from A4 I have "a\<lsq>m" by (rule ring_ord_transitive)
      ultimately have "\<exists>b\<in>?B. a\<lsq>b" by blast }
    moreover
    { assume A4: "\<zero>\<lsq>a \<and> a\<noteq>\<zero>"
      with A3 have "m\<cdot>a \<in> ?B" using PositiveSet_def
	by auto
      moreover
      from A2 A4 have "\<one>\<cdot>a \<lsq> m\<cdot>a" using OrdRing_ZF_1_L9
	by simp
      with A3 have "a \<lsq> m\<cdot>a" using Ring_ZF_1_L3 
	by simp
      ultimately have "\<exists>b\<in>?B. a\<lsq>b" by auto }
    ultimately have "\<exists>b\<in>?B. a\<lsq>b" by auto
  } then have "\<forall>a\<in>R. \<exists>b\<in>?B. a\<lsq>b"
    by simp
  with A1 show "?B \<notin> Fin(R)" using OrdRing_ZF_3_L4
    by simp
  moreover have "?B \<subseteq> {m\<cdot>x. x\<in>R}"
    using PositiveSet_def by auto
  ultimately show "{m\<cdot>x. x\<in>R} \<notin> Fin(R)" using Fin_subset
    by auto
  with T show "{(\<rm>m)\<cdot>x. x\<in>R} \<notin> Fin(R)" using Ring_ZF_1_L18
    by simp
qed

text\<open>If $m$ is less or equal than the negative of 
  multiplicative unit, then the set
  $\{m\cdot n: n\in R\}$ is infinite (unless the ring is trivial).\<close>

lemma (in ring1) OrdRing_ZF_3_L6: assumes A1: "\<zero>\<noteq>\<one>" and A2: "m \<lsq> \<rm>\<one>"
  shows "{m\<cdot>x. x\<in>R} \<notin> Fin(R)"
proof -
  from A2 have "(\<rm>(\<rm>\<one>)) \<lsq> \<rm>m"
    using OrdRing_ZF_1_L4B by simp
  with A1 have "{(\<rm>m)\<cdot>x. x\<in>R} \<notin> Fin(R)"
    using Ring_ZF_1_L2 Ring_ZF_1_L3 OrdRing_ZF_3_L5
    by simp
  with A2 show "{m\<cdot>x. x\<in>R} \<notin> Fin(R)"
    using OrdRing_ZF_1_L3 Ring_ZF_1_L18 by simp
qed

text\<open>All elements greater or equal than an element of \<open>R\<^sub>+\<close>
  belong to \<open>R\<^sub>+\<close>. Property of ordered groups.\<close>

lemma (in ring1) OrdRing_ZF_3_L7: assumes A1: "a \<in> R\<^sub>+" and A2: "a\<lsq>b"
  shows "b \<in> R\<^sub>+"
proof -
  from A1 A2 have 
    "group3(R,A,r)"
    "a \<in> PositiveSet(R,A,r)"
    "\<langle>a,b\<rangle> \<in> r"
    using OrdRing_ZF_1_L4 by auto
  then have "b \<in> PositiveSet(R,A,r)" 
    by (rule group3.OrderedGroup_ZF_1_L19)
  then show "b \<in> R\<^sub>+" by simp
qed

text\<open>A special case of \<open>OrdRing_ZF_3_L7\<close>: a ring element greater
  or equal than $1$ is positive.\<close>

corollary (in ring1) OrdRing_ZF_3_L8: assumes A1: "\<zero>\<noteq>\<one>" and A2: "\<one>\<lsq>a"
  shows "a \<in> R\<^sub>+"
proof -
  from A1 A2 have "\<one> \<in> R\<^sub>+"  "\<one>\<lsq>a"
    using ordring_one_is_pos by auto
  then show "a \<in> R\<^sub>+" by (rule OrdRing_ZF_3_L7)
qed

text\<open>Adding a positive element to $a$ strictly increases $a$.
  Property of ordered groups.\<close>

lemma (in ring1) OrdRing_ZF_3_L9: assumes A1: "a\<in>R"  "b\<in>R\<^sub>+"
  shows "a \<lsq> a\<ra>b"  "a \<noteq> a\<ra>b"
  using assms OrdRing_ZF_1_L4 group3.OrderedGroup_ZF_1_L22
  by auto

text\<open>A special case of \<open> OrdRing_ZF_3_L9\<close>: in nontrivial
  rings adding one to $a$ increases $a$.\<close>

corollary (in ring1) OrdRing_ZF_3_L10: assumes A1: "\<zero>\<noteq>\<one>" and A2: "a\<in>R"
  shows "a \<lsq> a\<ra>\<one>"  "a \<noteq> a\<ra>\<one>"
  using assms ordring_one_is_pos OrdRing_ZF_3_L9
  by auto

text\<open>If $a$ is not greater than $b$, then it is strictly less than
  $b+1$.\<close>

lemma (in ring1) OrdRing_ZF_3_L11: assumes A1: "\<zero>\<noteq>\<one>" and A2: "a\<lsq>b"
  shows "a\<ls> b\<ra>\<one>"
proof -
  from A1 A2 have I: "b \<ls> b\<ra>\<one>"
    using OrdRing_ZF_1_L3 OrdRing_ZF_3_L10 by auto
  with A2 show "a\<ls> b\<ra>\<one>" by (rule ring_strict_ord_transit)
qed
  

text\<open>For any ring element $a$ the greater of $a$ and $1$ is a positive
  element that is greater or equal than $m$. If we add $1$ to it we
  get a positive element that is strictly greater than $m$. This holds
  in nontrivial rings.\<close>

lemma (in ring1) OrdRing_ZF_3_L12: assumes A1: "\<zero>\<noteq>\<one>" and A2: "a\<in>R"
  shows 
  "a \<lsq> GreaterOf(r,\<one>,a)"
  "GreaterOf(r,\<one>,a) \<in> R\<^sub>+"
  "GreaterOf(r,\<one>,a) \<ra> \<one> \<in> R\<^sub>+"
  "a \<lsq> GreaterOf(r,\<one>,a) \<ra> \<one>"  "a \<noteq> GreaterOf(r,\<one>,a) \<ra> \<one>"
proof -
  from linord have "r {is total on} R" using IsLinOrder_def
    by simp
  moreover from A2 have "\<one> \<in> R"  "a\<in>R"
    using Ring_ZF_1_L2 by auto
  ultimately have
    "\<one> \<lsq> GreaterOf(r,\<one>,a)" and
    I: "a \<lsq> GreaterOf(r,\<one>,a)"
    using Order_ZF_3_L2 by auto
  with A1 show 
    "a \<lsq> GreaterOf(r,\<one>,a)" and 
    "GreaterOf(r,\<one>,a) \<in> R\<^sub>+"
    using OrdRing_ZF_3_L8 by auto
  with A1 show "GreaterOf(r,\<one>,a) \<ra> \<one> \<in> R\<^sub>+"
    using ordring_one_is_pos OrdRing_ZF_3_L1 IsOpClosed_def
    by simp
  from A1 I show 
    "a \<lsq> GreaterOf(r,\<one>,a) \<ra> \<one>"  "a \<noteq> GreaterOf(r,\<one>,a) \<ra> \<one>"
    using OrdRing_ZF_3_L11 by auto
qed

text\<open>We can multiply strict inequality by a positive element.\<close>

lemma (in ring1) OrdRing_ZF_3_L13: 
  assumes A1: "HasNoZeroDivs(R,A,M)" and 
  A2: "a\<ls>b" and A3: "c\<in>R\<^sub>+"
  shows 
  "a\<cdot>c \<ls> b\<cdot>c"
  "c\<cdot>a \<ls> c\<cdot>b"
proof -
  from A2 A3 have T: "a\<in>R"  "b\<in>R"  "c\<in>R"  "c\<noteq>\<zero>"
    using OrdRing_ZF_1_L3 PositiveSet_def by auto
  from A2 A3 have "a\<cdot>c \<lsq> b\<cdot>c" using OrdRing_ZF_1_L9A
    by simp
  moreover from A1 A2 T have "a\<cdot>c \<noteq> b\<cdot>c"
    using Ring_ZF_1_L12A by auto
  ultimately show "a\<cdot>c \<ls> b\<cdot>c" by simp
  moreover from mult_commut T have "a\<cdot>c = c\<cdot>a" and "b\<cdot>c = c\<cdot>b"
    using IsCommutative_def by auto
  ultimately show "c\<cdot>a \<ls> c\<cdot>b" by simp
qed

text\<open>A sufficient condition for an element to be in the set
  of positive ring elements.\<close>

lemma (in ring1) OrdRing_ZF_3_L14: assumes "\<zero>\<lsq>a" and "a\<noteq>\<zero>"
  shows "a \<in> R\<^sub>+"
  using assms OrdRing_ZF_1_L3 PositiveSet_def
  by auto

text\<open>If a ring has no zero divisors, the square of a nonzero
  element is positive.\<close>

lemma (in ring1) OrdRing_ZF_3_L15: 
  assumes "HasNoZeroDivs(R,A,M)" and "a\<in>R"  "a\<noteq>\<zero>"
  shows "\<zero> \<lsq> a\<^sup>2"  "a\<^sup>2 \<noteq> \<zero>"  "a\<^sup>2 \<in> R\<^sub>+"
  using assms OrdRing_ZF_1_L10 Ring_ZF_1_L12 OrdRing_ZF_3_L14
  by auto

text\<open>In rings with no zero divisors we can (strictly) increase a 
  positive element by  multiplying it by an element that is greater than $1$.\<close>

lemma (in ring1) OrdRing_ZF_3_L16: 
  assumes "HasNoZeroDivs(R,A,M)" and "a \<in> R\<^sub>+" and "\<one>\<lsq>b"  "\<one>\<noteq>b"
  shows "a\<lsq>a\<cdot>b"  "a \<noteq> a\<cdot>b"
  using assms PositiveSet_def OrdRing_ZF_1_L16 OrdRing_ZF_1_L3 
    Ring_ZF_1_L12C by auto

text\<open>If the right hand side of an inequality is positive we can multiply it 
  by a number that is greater than one.\<close>

lemma (in ring1) OrdRing_ZF_3_L17: 
   assumes A1: "HasNoZeroDivs(R,A,M)" and A2: "b\<in>R\<^sub>+" and 
  A3: "a\<lsq>b"  and A4: "\<one>\<ls>c"
  shows "a\<ls>b\<cdot>c"
proof -
  from A1 A2 A4 have "b \<ls> b\<cdot>c"
    using OrdRing_ZF_3_L16 by auto
  with A3 show "a\<ls>b\<cdot>c" by (rule ring_strict_ord_transit)
qed

text\<open>We can multiply a right hand side of an inequality between
  positive numbers by a number that is greater than one.\<close>

lemma (in ring1) OrdRing_ZF_3_L18: 
  assumes A1: "HasNoZeroDivs(R,A,M)" and A2: "a \<in> R\<^sub>+" and 
  A3: "a\<lsq>b" and A4: "\<one>\<ls>c"
  shows "a\<ls>b\<cdot>c"
proof -
  from A2 A3 have "b \<in> R\<^sub>+" using OrdRing_ZF_3_L7
    by blast
  with A1 A3 A4 show "a\<ls>b\<cdot>c"
    using OrdRing_ZF_3_L17 by simp
qed

text\<open>In ordered rings with no zero divisors if at 
  least one of $a,b$ is not zero, then
  $0 < a^2+b^2$, in particular $a^2+b^2\neq 0$.\<close>

lemma (in ring1) OrdRing_ZF_3_L19: 
  assumes A1: "HasNoZeroDivs(R,A,M)" and A2: "a\<in>R"  "b\<in>R" and
  A3: "a \<noteq> \<zero> \<or> b \<noteq> \<zero>"
  shows "\<zero> \<ls> a\<^sup>2 \<ra> b\<^sup>2"
proof -
  { assume "a \<noteq> \<zero>"
    with A1 A2 have "\<zero> \<lsq> a\<^sup>2"  "a\<^sup>2 \<noteq> \<zero>"  
      using OrdRing_ZF_3_L15 by auto
    then have "\<zero> \<ls> a\<^sup>2" by auto
    moreover from A2 have "\<zero> \<lsq> b\<^sup>2"
      using OrdRing_ZF_1_L10 by simp
    ultimately have "\<zero> \<ra> \<zero> \<ls> a\<^sup>2 \<ra> b\<^sup>2"
      using OrdRing_ZF_1_L19 by simp
    then have "\<zero> \<ls> a\<^sup>2 \<ra> b\<^sup>2"
      using Ring_ZF_1_L2 Ring_ZF_1_L3 by simp }
  moreover
  { assume A4: "a = \<zero>"
    then have "a\<^sup>2 \<ra> b\<^sup>2 = \<zero> \<ra> b\<^sup>2"
      using  Ring_ZF_1_L2 Ring_ZF_1_L6 by simp
    also from A2 have "\<dots> = b\<^sup>2"
      using Ring_ZF_1_L4 Ring_ZF_1_L3 by simp
    finally have "a\<^sup>2 \<ra> b\<^sup>2 = b\<^sup>2" by simp
    moreover 
    from A3 A4 have "b \<noteq> \<zero>" by simp
    with A1 A2 have "\<zero> \<lsq> b\<^sup>2" and "b\<^sup>2 \<noteq> \<zero>" 
      using OrdRing_ZF_3_L15 by auto
    hence "\<zero> \<ls> b\<^sup>2" by auto
    ultimately have "\<zero> \<ls> a\<^sup>2 \<ra> b\<^sup>2" by simp }
  ultimately show "\<zero> \<ls> a\<^sup>2 \<ra> b\<^sup>2"
    by auto
qed

end
