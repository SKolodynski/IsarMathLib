(*  This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2005- 2009  Slawomir Kolodynski

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

section \<open>Integers 1\<close>

theory Int_ZF_1 imports Int_ZF_IML OrderedRing_ZF

begin

text\<open>This theory file considers the set of integers as an ordered ring.\<close>

subsection\<open>Integers as a ring\<close>

text\<open>In this section we show that integers form a commutative ring.\<close>


text\<open>The next lemma provides the condition to show that addition is 
  distributive with respect to multiplication.\<close>

lemma (in int0) Int_ZF_1_1_L1: assumes A1: "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>" 
  shows 
  "a\<cdot>(b\<ra>c) = a\<cdot>b \<ra> a\<cdot>c" 
  "(b\<ra>c)\<cdot>a = b\<cdot>a \<ra> c\<cdot>a"
  using assms Int_ZF_1_L2 zadd_zmult_distrib zadd_zmult_distrib2
  by auto

text\<open>Integers form a commutative ring, hence we can use theorems proven 
  in \<open>ring0\<close> context (locale).\<close>

lemma (in int0) Int_ZF_1_1_L2: shows
  "IsAring(\<int>,IntegerAddition,IntegerMultiplication)"
  "IntegerMultiplication {is commutative on} \<int>"
  "ring0(\<int>,IntegerAddition,IntegerMultiplication)"
proof -
  have "\<forall>a\<in>\<int>.\<forall>b\<in>\<int>.\<forall>c\<in>\<int>. 
    a\<cdot>(b\<ra>c) = a\<cdot>b \<ra> a\<cdot>c \<and> (b\<ra>c)\<cdot>a = b\<cdot>a \<ra> c\<cdot>a"
    using Int_ZF_1_1_L1 by simp
  then have "IsDistributive(\<int>,IntegerAddition,IntegerMultiplication)"
    using IsDistributive_def by simp
  then show "IsAring(\<int>,IntegerAddition,IntegerMultiplication)"
    "ring0(\<int>,IntegerAddition,IntegerMultiplication)"
    using Int_ZF_1_T1 Int_ZF_1_T2 IsAring_def ring0_def 
    by auto
  have "\<forall>a\<in>\<int>.\<forall>b\<in>\<int>. a\<cdot>b = b\<cdot>a" using Int_ZF_1_L4 by simp
  then show "IntegerMultiplication {is commutative on} \<int>"
    using IsCommutative_def by simp
qed

text\<open>Zero and one are integers.\<close>

lemma (in int0) int_zero_one_are_int: shows "\<zero>\<in>\<int>"  "\<one>\<in>\<int>"
  using Int_ZF_1_1_L2 ring0.Ring_ZF_1_L2 by auto

text\<open>Negative of zero is zero.\<close>

lemma (in int0) int_zero_one_are_intA: shows "(\<rm>\<zero>) = \<zero>"
  using Int_ZF_1_T2 group0.group_inv_of_one by simp

text\<open>Properties with one integer.\<close>

lemma (in int0) Int_ZF_1_1_L4: assumes A1: "a \<in> \<int>"
  shows 
  "a\<ra>\<zero> = a" 
  "\<zero>\<ra>a = a" 
  "a\<cdot>\<one> = a"   "\<one>\<cdot>a = a"
  "\<zero>\<cdot>a = \<zero>"   "a\<cdot>\<zero> = \<zero>" 
  "(\<rm>a) \<in> \<int>"  "(\<rm>(\<rm>a)) = a"
  "a\<rs>a = \<zero>"   "a\<rs>\<zero> = a"  "\<two>\<cdot>a = a\<ra>a"
proof -
  from A1 show 
    "a\<ra>\<zero> = a"   "\<zero>\<ra>a = a"   "a\<cdot>\<one> = a" 
    "\<one>\<cdot>a = a"   "a\<rs>a = \<zero>"   "a\<rs>\<zero> = a"  
    "(\<rm>a) \<in> \<int>"  "\<two>\<cdot>a = a\<ra>a"   "(\<rm>(\<rm>a)) = a"
    using Int_ZF_1_1_L2 ring0.Ring_ZF_1_L3 by auto
  from A1 show "\<zero>\<cdot>a = \<zero>"   "a\<cdot>\<zero> = \<zero>"
    using Int_ZF_1_1_L2 ring0.Ring_ZF_1_L6 by auto
qed

text\<open>Properties that require two integers.\<close>

lemma (in int0) Int_ZF_1_1_L5: assumes "a\<in>\<int>"  "b\<in>\<int>"
  shows 
  "a\<ra>b \<in> \<int>" 
  "a\<rs>b \<in> \<int>" 
  "a\<cdot>b \<in> \<int>"
  "a\<ra>b = b\<ra>a" 
  "a\<cdot>b = b\<cdot>a" 
  "(\<rm>b)\<rs>a = (\<rm>a)\<rs>b" 
  "(\<rm>(a\<ra>b)) = (\<rm>a)\<rs>b"  
  "(\<rm>(a\<rs>b)) = ((\<rm>a)\<ra>b)"
  "(\<rm>a)\<cdot>b = \<rm>(a\<cdot>b)" 
  "a\<cdot>(\<rm>b) = \<rm>(a\<cdot>b)"
  "(\<rm>a)\<cdot>(\<rm>b) = a\<cdot>b"
  using assms Int_ZF_1_1_L2 ring0.Ring_ZF_1_L4 ring0.Ring_ZF_1_L9
    ring0.Ring_ZF_1_L7 ring0.Ring_ZF_1_L7A Int_ZF_1_L4 by auto

text\<open>$2$ and $3$ are integers.\<close>

lemma (in int0) int_two_three_are_int: shows "\<two> \<in> \<int>"  "\<three> \<in> \<int>"
    using int_zero_one_are_int Int_ZF_1_1_L5 by auto

text\<open>Another property with two integers.\<close>

lemma (in int0) Int_ZF_1_1_L5B:
  assumes "a\<in>\<int>"  "b\<in>\<int>"
  shows "a\<rs>(\<rm>b) = a\<ra>b"
  using assms Int_ZF_1_1_L2 ring0.Ring_ZF_1_L9
  by simp

text\<open>Properties that require three integers.\<close>

lemma (in int0) Int_ZF_1_1_L6: assumes "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>"
  shows 
  "a\<rs>(b\<ra>c) = a\<rs>b\<rs>c"
  "a\<rs>(b\<rs>c) = a\<rs>b\<ra>c"
  "a\<cdot>(b\<rs>c) = a\<cdot>b \<rs> a\<cdot>c"
  "(b\<rs>c)\<cdot>a = b\<cdot>a \<rs> c\<cdot>a"
  using assms Int_ZF_1_1_L2 ring0.Ring_ZF_1_L10  ring0.Ring_ZF_1_L8 
  by auto

text\<open>One more property with three integers.\<close>
(* Inclusion of a\<ra>(b\<rs>c) = a\<ra>b\<rs>c causes the previous lemma
  to be unusable by simp in some cases*)
lemma (in int0) Int_ZF_1_1_L6A: assumes "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>"
  shows "a\<ra>(b\<rs>c) = a\<ra>b\<rs>c"
  using assms Int_ZF_1_1_L2 ring0.Ring_ZF_1_L10A by simp

text\<open>Associativity of addition and multiplication.\<close>

lemma (in int0) Int_ZF_1_1_L7: assumes "a\<in>\<int>" "b\<in>\<int>" "c\<in>\<int>"
  shows 
  "a\<ra>b\<ra>c = a\<ra>(b\<ra>c)"
  "a\<cdot>b\<cdot>c = a\<cdot>(b\<cdot>c)"
  using assms Int_ZF_1_1_L2 ring0.Ring_ZF_1_L11 by auto
  
subsection\<open>Rearrangement lemmas\<close>

text\<open>In this section we collect lemmas about identities related to 
  rearranging the terms in expresssions\<close>

text\<open>A formula with a positive integer.\<close>

lemma (in int0) Int_ZF_1_2_L1: assumes "\<zero>\<lsq>a"
  shows "abs(a)\<ra>\<one> = abs(a\<ra>\<one>)"
  using assms Int_ZF_2_L16 Int_ZF_2_L12A by simp

text\<open>A formula with two integers, one positive.\<close>

lemma (in int0) Int_ZF_1_2_L2: assumes A1: "a\<in>\<int>" and A2: "\<zero>\<lsq>b"
  shows "a\<ra>(abs(b)\<ra>\<one>)\<cdot>a = (abs(b\<ra>\<one>)\<ra>\<one>)\<cdot>a"
proof -
  from A2 have "abs(b\<ra>\<one>) \<in> \<int>"
    using Int_ZF_2_L12A Int_ZF_2_L1A Int_ZF_2_L14 by blast
  with A1 A2 show ?thesis 
    using Int_ZF_1_2_L1 Int_ZF_1_1_L2 ring0.Ring_ZF_2_L1 
    by simp
qed

text\<open>A couple of formulae about canceling opposite integers.\<close>

lemma (in int0) Int_ZF_1_2_L3: assumes A1: "a\<in>\<int>"  "b\<in>\<int>"
  shows 
  "a\<ra>b\<rs>a = b"
  "a\<ra>(b\<rs>a) = b"
  "a\<ra>b\<rs>b = a" 
  "a\<rs>b\<ra>b = a"
  "(\<rm>a)\<ra>(a\<ra>b) = b"
  "a\<ra>(b\<rs>a) = b"
  "(\<rm>b)\<ra>(a\<ra>b) = a"
  "a\<rs>(b\<ra>a) = \<rm>b"
  "a\<rs>(a\<ra>b) = \<rm>b"
  "a\<rs>(a\<rs>b) = b"
  "a\<rs>b\<rs>a =  \<rm>b"
  "a\<rs>b \<rs> (a\<ra>b) = (\<rm>b)\<rs>b"
  using assms Int_ZF_1_T2 group0.group0_4_L6A group0.inv_cancel_two
    group0.group0_2_L16A group0.group0_4_L6AA group0.group0_4_L6AB
    group0.group0_4_L6F group0.group0_4_L6AC by auto

text\<open>Subtracting one does not increase integers. This may be moved to a theory
  about ordered rings one day.\<close>

lemma (in int0) Int_ZF_1_2_L3A: assumes A1: "a\<lsq>b"
  shows "a\<rs>\<one> \<lsq> b" 
proof -
  from A1 have "b\<ra>\<one>\<rs>\<one> = b"
    using Int_ZF_2_L1A int_zero_one_are_int Int_ZF_1_2_L3 by simp
  moreover from A1 have "a\<rs>\<one> \<lsq> b\<ra>\<one>\<rs>\<one>"
    using Int_ZF_2_L12A int_zero_one_are_int Int_ZF_1_1_L4 int_ord_transl_inv
    by simp
  ultimately show "a\<rs>\<one> \<lsq> b" by simp
qed

text\<open>Subtracting one does not increase integers, special case.\<close>

lemma (in int0) Int_ZF_1_2_L3AA: 
  assumes A1: "a\<in>\<int>" shows 
  "a\<rs>\<one> \<lsq>a"
  "a\<rs>\<one> \<noteq> a"
  "\<not>(a\<lsq>a\<rs>\<one>)"
  "\<not>(a\<ra>\<one> \<lsq>a)"
  "\<not>(\<one>\<ra>a \<lsq>a)"
proof -
  from A1 have "a\<lsq>a" using int_ord_is_refl refl_def
    by simp
  then show "a\<rs>\<one> \<lsq>a" using Int_ZF_1_2_L3A
    by simp
  moreover from A1 show "a\<rs>\<one> \<noteq> a" using Int_ZF_1_L14 by simp
  ultimately show I: "\<not>(a\<lsq>a\<rs>\<one>)" using Int_ZF_2_L19AA
    by blast
  with A1 show "\<not>(a\<ra>\<one> \<lsq>a)"
    using int_zero_one_are_int Int_ZF_2_L9B by simp
  with A1 show "\<not>(\<one>\<ra>a \<lsq>a)" 
    using int_zero_one_are_int Int_ZF_1_1_L5 by simp
qed

text\<open>A formula with a nonpositive integer.\<close>

lemma (in int0) Int_ZF_1_2_L4: assumes "a\<lsq>\<zero>"
  shows "abs(a)\<ra>\<one> = abs(a\<rs>\<one>)"
  using assms int_zero_one_are_int Int_ZF_1_2_L3A Int_ZF_2_T1 
      group3.OrderedGroup_ZF_3_L3A Int_ZF_2_L1A 
      int_zero_one_are_int Int_ZF_1_1_L5 by simp

text\<open>A formula with two integers, one negative.\<close>

lemma (in int0) Int_ZF_1_2_L5: assumes A1: "a\<in>\<int>" and A2: "b\<lsq>\<zero>"
  shows "a\<ra>(abs(b)\<ra>\<one>)\<cdot>a = (abs(b\<rs>\<one>)\<ra>\<one>)\<cdot>a"
proof -
  from A2 have "abs(b\<rs>\<one>) \<in> \<int>"
    using int_zero_one_are_int Int_ZF_1_2_L3A Int_ZF_2_L1A Int_ZF_2_L14 
    by blast
  with A1 A2 show ?thesis 
    using Int_ZF_1_2_L4 Int_ZF_1_1_L2 ring0.Ring_ZF_2_L1
    by simp
qed
  
text\<open>A rearrangement with four integers.\<close>

lemma (in int0) Int_ZF_1_2_L6: 
  assumes A1: "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>"  "d\<in>\<int>"
  shows 
  "a\<rs>(b\<rs>\<one>)\<cdot>c = (d\<rs>b\<cdot>c)\<rs>(d\<rs>a\<rs>c)"
proof -
  from A1 have T1: 
    "(d\<rs>b\<cdot>c) \<in> \<int>" "d\<rs>a \<in> \<int>" "(\<rm>(b\<cdot>c)) \<in> \<int>"
    using Int_ZF_1_1_L5 Int_ZF_1_1_L4 by auto   
  with A1 have 
    "(d\<rs>b\<cdot>c)\<rs>(d\<rs>a\<rs>c) = (\<rm>(b\<cdot>c))\<ra>a\<ra>c"
    using Int_ZF_1_1_L6 Int_ZF_1_2_L3 by simp
  also from A1 T1 have "(\<rm>(b\<cdot>c))\<ra>a\<ra>c = a\<rs>(b\<rs>\<one>)\<cdot>c" 
    using int_zero_one_are_int Int_ZF_1_1_L6 Int_ZF_1_1_L4 Int_ZF_1_1_L5
    by simp
  finally show ?thesis by simp
qed

text\<open>Some other rearrangements with two integers.\<close>

lemma (in int0) Int_ZF_1_2_L7: assumes "a\<in>\<int>"  "b\<in>\<int>"
  shows 
  "a\<cdot>b = (a\<rs>\<one>)\<cdot>b\<ra>b"
  "a\<cdot>(b\<ra>\<one>) = a\<cdot>b\<ra>a"
  "(b\<ra>\<one>)\<cdot>a = b\<cdot>a\<ra>a"
  "(b\<ra>\<one>)\<cdot>a = a\<ra>b\<cdot>a"
  using assms Int_ZF_1_1_L1 Int_ZF_1_1_L5 int_zero_one_are_int 
    Int_ZF_1_1_L6 Int_ZF_1_1_L4 Int_ZF_1_T2 group0.inv_cancel_two 
  by auto

(*text{*Another rearrangement with two integers and cancelling.*}

lemma (in int0) Int_ZF_1_2_L7A:  assumes A1: "a\<in>\<int>"  "b\<in>\<int>"
  shows "a\<rs>b \<ra> (a\<rs>b) = \<rm>(\<two>\<cdot>b)"
proof -
  from A1 have "a\<rs>b \<rs> (a\<ra>b) = (\<rm>b)\<rs>b"
    using Int_ZF_1_T2 group0.group0_4_L6F by simp;*)
  

text\<open>Another rearrangement with two integers.\<close>

lemma (in int0) Int_ZF_1_2_L8: 
  assumes A1: "a\<in>\<int>" "b\<in>\<int>"
  shows "a\<ra>\<one>\<ra>(b\<ra>\<one>) = b\<ra>a\<ra>\<two>"
  using assms int_zero_one_are_int Int_ZF_1_T2 group0.group0_4_L8
  by simp

text\<open>A couple of rearrangement with three integers.\<close>

lemma (in int0) Int_ZF_1_2_L9: 
  assumes "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>"
  shows 
  "(a\<rs>b)\<ra>(b\<rs>c) = a\<rs>c"
  "(a\<rs>b)\<rs>(a\<rs>c) = c\<rs>b"
  "a\<ra>(b\<ra>(c\<rs>a\<rs>b)) = c"
  "(\<rm>a)\<rs>b\<ra>c = c\<rs>a\<rs>b"
  "(\<rm>b)\<rs>a\<ra>c = c\<rs>a\<rs>b"
  "(\<rm>((\<rm>a)\<ra>b\<ra>c)) = a\<rs>b\<rs>c"
  "a\<ra>b\<ra>c\<rs>a = b\<ra>c"
  "a\<ra>b\<rs>(a\<ra>c) = b\<rs>c"
  using assms Int_ZF_1_T2 
    group0.group0_4_L4B group0.group0_4_L6D group0.group0_4_L4D
    group0.group0_4_L6B group0.group0_4_L6E
  by auto

text\<open>Another couple of rearrangements with three integers.\<close>

lemma (in int0) Int_ZF_1_2_L9A: 
  assumes A1: "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>"
  shows "(\<rm>(a\<rs>b\<rs>c)) = c\<ra>b\<rs>a"
proof -
  from A1 have T: 
    "a\<rs>b \<in> \<int>"  "(\<rm>(a\<rs>b)) \<in> \<int>"  "(\<rm>b) \<in> \<int>" using 
    Int_ZF_1_1_L4 Int_ZF_1_1_L5 by auto
  with A1 have "(\<rm>(a\<rs>b\<rs>c)) = c \<rs> ((\<rm>b)\<ra>a)"
     using Int_ZF_1_1_L5 by simp
   also from A1 T have "\<dots> = c\<ra>b\<rs>a"
     using Int_ZF_1_1_L6 Int_ZF_1_1_L5B
     by simp
  finally show "(\<rm>(a\<rs>b\<rs>c)) = c\<ra>b\<rs>a" 
    by simp
qed
  
 
text\<open>Another rearrangement with three integers.\<close>

lemma (in int0) Int_ZF_1_2_L10: 
  assumes A1: "a\<in>\<int>" "b\<in>\<int>" "c\<in>\<int>"
  shows "(a\<ra>\<one>)\<cdot>b \<ra> (c\<ra>\<one>)\<cdot>b = (c\<ra>a\<ra>\<two>)\<cdot>b"
proof -
  from A1 have "a\<ra>\<one> \<in> \<int>" "c\<ra>\<one> \<in> \<int>" 
    using int_zero_one_are_int Int_ZF_1_1_L5 by auto 
  with A1 have 
    "(a\<ra>\<one>)\<cdot>b \<ra> (c\<ra>\<one>)\<cdot>b = (a\<ra>\<one>\<ra>(c\<ra>\<one>))\<cdot>b"
    using Int_ZF_1_1_L1 by simp
  also from A1 have "\<dots> = (c\<ra>a\<ra>\<two>)\<cdot>b"
    using Int_ZF_1_2_L8 by simp
  finally show ?thesis by simp
qed

text\<open>A technical rearrangement involing inequalities with absolute value.\<close>

lemma (in int0) Int_ZF_1_2_L10A: 
  assumes A1: "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>"  "e\<in>\<int>"
  and A2: "abs(a\<cdot>b\<rs>c) \<lsq> d"  "abs(b\<cdot>a\<rs>e) \<lsq> f"
  shows "abs(c\<rs>e) \<lsq>  f\<ra>d"
proof -  
  from A1 A2 have T1:
    "d\<in>\<int>"  "f\<in>\<int>"  "a\<cdot>b \<in> \<int>"  "a\<cdot>b\<rs>c \<in> \<int>"  "b\<cdot>a\<rs>e \<in> \<int>"
    using Int_ZF_2_L1A Int_ZF_1_1_L5 by auto
  with A2 have
    "abs((b\<cdot>a\<rs>e)\<rs>(a\<cdot>b\<rs>c)) \<lsq> f \<ra>d"
    using Int_ZF_2_L21 by simp
  with A1 T1 show "abs(c\<rs>e) \<lsq> f\<ra>d" 
    using Int_ZF_1_1_L5 Int_ZF_1_2_L9 by simp
qed

text\<open>Some arithmetics.\<close>

lemma (in int0) Int_ZF_1_2_L11: assumes A1: "a\<in>\<int>"
  shows 
  "a\<ra>\<one>\<ra>\<two> = a\<ra>\<three>"
  "a = \<two>\<cdot>a \<rs> a"
proof -
  from A1 show "a\<ra>\<one>\<ra>\<two> = a\<ra>\<three>"
    using int_zero_one_are_int int_two_three_are_int Int_ZF_1_T2 group0.group0_4_L4C
    by simp
  from A1 show "a = \<two>\<cdot>a \<rs> a"
    using int_zero_one_are_int Int_ZF_1_1_L1 Int_ZF_1_1_L4 Int_ZF_1_T2 group0.inv_cancel_two
    by simp
qed

text\<open>A simple rearrangement with three integers.\<close>

lemma (in int0) Int_ZF_1_2_L12: 
  assumes "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>"
  shows 
  "(b\<rs>c)\<cdot>a = a\<cdot>b \<rs> a\<cdot>c"
  using assms Int_ZF_1_1_L6 Int_ZF_1_1_L5 by simp

text\<open>A big rearrangement with five integers.\<close>

lemma (in int0) Int_ZF_1_2_L13: 
  assumes A1: "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>" "d\<in>\<int>"  "x\<in>\<int>"
  shows "(x\<ra>(a\<cdot>x\<ra>b)\<ra>c)\<cdot>d = d\<cdot>(a\<ra>\<one>)\<cdot>x \<ra> (b\<cdot>d\<ra>c\<cdot>d)"
proof -
  from A1 have T1: 
    "a\<cdot>x \<in> \<int>"   "(a\<ra>\<one>)\<cdot>x \<in> \<int>"  
    "(a\<ra>\<one>)\<cdot>x \<ra> b \<in> \<int>" 
    using Int_ZF_1_1_L5 int_zero_one_are_int by auto
  with A1 have "(x\<ra>(a\<cdot>x\<ra>b)\<ra>c)\<cdot>d = ((a\<ra>\<one>)\<cdot>x \<ra> b)\<cdot>d \<ra> c\<cdot>d"
    using Int_ZF_1_1_L7 Int_ZF_1_2_L7 Int_ZF_1_1_L1
    by simp
  also from A1 T1 have "\<dots> = (a\<ra>\<one>)\<cdot>x\<cdot>d \<ra> b \<cdot> d \<ra> c\<cdot>d"
    using Int_ZF_1_1_L1 by simp
  finally have "(x\<ra>(a\<cdot>x\<ra>b)\<ra>c)\<cdot>d = (a\<ra>\<one>)\<cdot>x\<cdot>d \<ra> b\<cdot>d \<ra> c\<cdot>d"
    by simp
  moreover from A1 T1 have "(a\<ra>\<one>)\<cdot>x\<cdot>d = d\<cdot>(a\<ra>\<one>)\<cdot>x"
    using int_zero_one_are_int Int_ZF_1_1_L5 Int_ZF_1_1_L7 by simp
  ultimately have "(x\<ra>(a\<cdot>x\<ra>b)\<ra>c)\<cdot>d = d\<cdot>(a\<ra>\<one>)\<cdot>x \<ra> b\<cdot>d \<ra> c\<cdot>d"
    by simp
  moreover from A1 T1 have 
    "d\<cdot>(a\<ra>\<one>)\<cdot>x \<in> \<int>"  "b\<cdot>d \<in> \<int>"  "c\<cdot>d \<in> \<int>"
    using int_zero_one_are_int Int_ZF_1_1_L5 by auto
  ultimately show ?thesis using Int_ZF_1_1_L7 by simp
qed

text\<open>Rerrangement about adding linear functions.\<close>

lemma (in int0) Int_ZF_1_2_L14:
  assumes "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>" "d\<in>\<int>"  "x\<in>\<int>"
  shows "(a\<cdot>x \<ra> b) \<ra> (c\<cdot>x \<ra> d) = (a\<ra>c)\<cdot>x \<ra> (b\<ra>d)"
  using assms Int_ZF_1_1_L2 ring0.Ring_ZF_2_L3 by simp

text\<open>A rearrangement with four integers. 
  Again we have to use the generic set notation to use a theorem proven in 
  different context.\<close>

lemma (in int0) Int_ZF_1_2_L15: assumes A1: "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>" "d\<in>\<int>"
  and A2: "a = b\<rs>c\<rs>d"
  shows 
  "d = b\<rs>a\<rs>c"
  "d = (\<rm>a)\<ra>b\<rs>c"
  "b = a\<ra>d\<ra>c"
proof -
  let ?G = "int"
  let ?f = "IntegerAddition"
  from A1 A2 have I:
    "group0(?G, ?f)"   "?f {is commutative on} ?G"
    "a \<in> ?G"  "b \<in> ?G" "c \<in> ?G"  "d \<in> ?G"
    "a = ?f`\<langle>?f`\<langle>b,GroupInv(?G, ?f)`(c)\<rangle>,GroupInv(?G, ?f)`(d)\<rangle>"
    using Int_ZF_1_T2 by auto
  then have  
    "d = ?f`\<langle>?f`\<langle>b,GroupInv(?G, ?f)`(a)\<rangle>,GroupInv(?G,?f)`(c)\<rangle>"
    by (rule group0.group0_4_L9)
  then show "d = b\<rs>a\<rs>c" by simp
  from I have "d = ?f`\<langle>?f`\<langle>GroupInv(?G, ?f)`(a),b\<rangle>, GroupInv(?G, ?f)`(c)\<rangle>"
    by (rule group0.group0_4_L9)
  thus "d = (\<rm>a)\<ra>b\<rs>c"
    by simp
  from I have "b = ?f`\<langle>?f`\<langle>a, d\<rangle>,c\<rangle>"
    by (rule group0.group0_4_L9)
  thus "b = a\<ra>d\<ra>c" by simp
qed

text\<open>A rearrangement with four integers. Property of groups.\<close>

lemma (in int0) Int_ZF_1_2_L16:
  assumes "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>" "d\<in>\<int>"
  shows "a\<ra>(b\<rs>c)\<ra>d = a\<ra>b\<ra>d\<rs>c"
  using assms Int_ZF_1_T2 group0.group0_4_L8 by simp

text\<open>Some rearrangements with three integers. Properties of groups.\<close>

lemma (in int0) Int_ZF_1_2_L17:
  assumes A1: "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>"
  shows 
  "a\<ra>b\<rs>c\<ra>(c\<rs>b) = a"
  "a\<ra>(b\<ra>c)\<rs>c = a\<ra>b"
proof -
  let ?G = "int"
  let ?f = "IntegerAddition"
  from A1 have I:
    "group0(?G, ?f)"
    "a \<in> ?G"  "b \<in> ?G" "c \<in> ?G"
    using Int_ZF_1_T2 by auto
  then have 
    "?f`\<langle>?f`\<langle>?f`\<langle>a,b\<rangle>,GroupInv(?G, ?f)`(c)\<rangle>,?f`\<langle>c,GroupInv(?G, ?f)`(b)\<rangle>\<rangle> = a"
    by (rule group0.group0_2_L14A)
  thus "a\<ra>b\<rs>c\<ra>(c\<rs>b) = a" by simp
  from I have
    "?f`\<langle>?f`\<langle>a,?f`\<langle>b,c\<rangle>\<rangle>,GroupInv(?G, ?f)`(c)\<rangle> = ?f`\<langle>a,b\<rangle>"
    by (rule group0.group0_2_L14A)
  thus "a\<ra>(b\<ra>c)\<rs>c = a\<ra>b" by simp
qed

text\<open>Another rearrangement with three integers. Property of abelian groups.\<close>

lemma (in int0) Int_ZF_1_2_L18:
  assumes A1: "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>"
  shows "a\<ra>b\<rs>c\<ra>(c\<rs>a) = b"
proof -
  let ?G = "int"
  let ?f = "IntegerAddition"
  from A1 have
    "group0(?G, ?f)"   "?f {is commutative on} ?G"
    "a \<in> ?G"  "b \<in> ?G" "c \<in> ?G"
    using Int_ZF_1_T2 by auto
  then have
    "?f`\<langle>?f`\<langle>?f`\<langle>a,b\<rangle>,GroupInv(?G, ?f)`(c)\<rangle>,?f`\<langle>c,GroupInv(?G, ?f)`(a)\<rangle>\<rangle> = b"
    by (rule group0.group0_4_L6D)
  thus "a\<ra>b\<rs>c\<ra>(c\<rs>a) = b" by simp
qed

subsection\<open>Integers as an ordered ring\<close>

text\<open>We already know from \<open>Int_ZF\<close> that integers with addition 
  form a linearly ordered group. To show that integers form 
  an ordered ring we need the fact that the set of nonnegative integers
  is closed under multiplication.\<close>

text\<open>We start with the property that a product of 
  nonnegative integers is nonnegative. The proof is by induction and the next
  lemma is the induction step.\<close>

lemma (in int0) Int_ZF_1_3_L1: assumes A1: "\<zero>\<lsq>a"  "\<zero>\<lsq>b"
  and A3: "\<zero> \<lsq> a\<cdot>b"
  shows "\<zero> \<lsq> a\<cdot>(b\<ra>\<one>)"
proof -
  from A1 A3 have "\<zero>\<ra>\<zero> \<lsq> a\<cdot>b\<ra>a"
    using int_ineq_add_sides by simp
  with A1 show "\<zero> \<lsq> a\<cdot>(b\<ra>\<one>)"
    using int_zero_one_are_int Int_ZF_1_1_L4 Int_ZF_2_L1A Int_ZF_1_2_L7 
    by simp
qed

text\<open>Product of nonnegative integers is nonnegative.\<close>
  
lemma (in int0) Int_ZF_1_3_L2: assumes A1: "\<zero>\<lsq>a"  "\<zero>\<lsq>b" 
  shows "\<zero>\<lsq>a\<cdot>b"
proof -
  from A1 have "\<zero>\<lsq>b" by simp
  moreover from A1 have "\<zero> \<lsq> a\<cdot>\<zero>" using
    Int_ZF_2_L1A Int_ZF_1_1_L4 int_zero_one_are_int int_ord_is_refl refl_def
    by simp
  moreover from A1 have 
    "\<forall>m. \<zero>\<lsq>m \<and> \<zero>\<lsq>a\<cdot>m \<longrightarrow> \<zero> \<lsq> a\<cdot>(m\<ra>\<one>)"
    using Int_ZF_1_3_L1 by simp
  ultimately show "\<zero>\<lsq>a\<cdot>b" by (rule Induction_on_int)
qed

text\<open>The set of nonnegative integers is closed under  multiplication.\<close>

lemma (in int0) Int_ZF_1_3_L2A: shows 
  "\<int>\<^sup>+ {is closed under} IntegerMultiplication"
proof -
  { fix a b assume "a\<in>\<int>\<^sup>+"  "b\<in>\<int>\<^sup>+"
    then have "a\<cdot>b \<in>\<int>\<^sup>+"
      using Int_ZF_1_3_L2 Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L2 
      by simp
  } then have "\<forall>a\<in>\<int>\<^sup>+.\<forall>b\<in>\<int>\<^sup>+.a\<cdot>b \<in>\<int>\<^sup>+" by simp 
  then show ?thesis using IsOpClosed_def by simp
qed

text\<open>Integers form an ordered ring. All theorems proven in the 
  \<open>ring1\<close> context are valid in \<open>int0\<close> context.\<close>

theorem (in int0) Int_ZF_1_3_T1: shows 
  "IsAnOrdRing(\<int>,IntegerAddition,IntegerMultiplication,IntegerOrder)"
  "ring1(\<int>,IntegerAddition,IntegerMultiplication,IntegerOrder)"
  using Int_ZF_1_1_L2 Int_ZF_2_L1B Int_ZF_1_3_L2A Int_ZF_2_T1
    OrdRing_ZF_1_L6 OrdRing_ZF_1_L2 by auto
  
text\<open>Product of integers that are greater that one is greater than one. 
  The proof is by induction and 
  the next step is the induction step.\<close>

lemma (in int0) Int_ZF_1_3_L3_indstep:  
  assumes A1: "\<one>\<lsq>a"  "\<one>\<lsq>b"
  and A2: "\<one> \<lsq> a\<cdot>b"
  shows "\<one> \<lsq> a\<cdot>(b\<ra>\<one>)"
proof -
   from A1 A2 have "\<one>\<lsq>\<two>" and "\<two> \<lsq> a\<cdot>(b\<ra>\<one>)"
    using Int_ZF_2_L1A int_ineq_add_sides Int_ZF_2_L16B Int_ZF_1_2_L7 
    by auto
  then show "\<one> \<lsq> a\<cdot>(b\<ra>\<one>)" by (rule Int_order_transitive)
qed

text\<open>Product of integers that are greater that one is greater than one.\<close>

lemma (in int0) Int_ZF_1_3_L3: 
  assumes A1: "\<one>\<lsq>a" "\<one>\<lsq>b"
  shows "\<one> \<lsq> a\<cdot>b"
proof -
  from A1 have "\<one>\<lsq>b"  "\<one>\<lsq>a\<cdot>\<one>"
    using Int_ZF_2_L1A Int_ZF_1_1_L4 by auto
  moreover from A1 have 
    "\<forall>m. \<one>\<lsq>m \<and> \<one> \<lsq> a\<cdot>m \<longrightarrow> \<one> \<lsq> a\<cdot>(m\<ra>\<one>)"
    using Int_ZF_1_3_L3_indstep by simp
  ultimately show "\<one> \<lsq> a\<cdot>b" by (rule Induction_on_int)
qed

text\<open>$|a\cdot (-b)| = |(-a)\cdot b| = |(-a)\cdot (-b)| = |a\cdot b|$
  This is a property of ordered rings..\<close>

lemma (in int0) Int_ZF_1_3_L4: assumes "a\<in>\<int>"  "b\<in>\<int>"
  shows 
  "abs((\<rm>a)\<cdot>b) = abs(a\<cdot>b)"
  "abs(a\<cdot>(\<rm>b)) = abs(a\<cdot>b)"
  "abs((\<rm>a)\<cdot>(\<rm>b)) = abs(a\<cdot>b)"
  using assms Int_ZF_1_1_L5 Int_ZF_2_L17 by auto

text\<open>Absolute value of a product is the product of absolute values.
  Property of ordered rings.\<close>

lemma (in int0) Int_ZF_1_3_L5:
  assumes A1: "a\<in>\<int>"  "b\<in>\<int>"
  shows "abs(a\<cdot>b) = abs(a)\<cdot>abs(b)"
  using assms Int_ZF_1_3_T1 ring1.OrdRing_ZF_2_L5 by simp

text\<open>Double nonnegative is nonnegative. Property of ordered rings.\<close>

lemma (in int0) Int_ZF_1_3_L5A: assumes "\<zero>\<lsq>a"
  shows "\<zero>\<lsq>\<two>\<cdot>a"
  using assms Int_ZF_1_3_T1 ring1.OrdRing_ZF_1_L5A by simp


text\<open>The next lemma shows what happens when one integer is not
  greater or equal than another.\<close>

lemma (in int0) Int_ZF_1_3_L6: 
  assumes A1: "a\<in>\<int>"  "b\<in>\<int>" 
  shows "\<not>(b\<lsq>a) \<longleftrightarrow> a\<ra>\<one> \<lsq> b"
proof
  assume A3: "\<not>(b\<lsq>a)"
  with A1 have  "a\<lsq>b" by (rule Int_ZF_2_L19)
  then have "a = b   \<or>  a\<ra>\<one> \<lsq> b"
    using Int_ZF_4_L1B by simp 
  moreover from A1 A3 have "a\<noteq>b" by (rule Int_ZF_2_L19)
  ultimately show "a\<ra>\<one> \<lsq> b" by simp
next assume A4: "a\<ra>\<one> \<lsq> b"
  { assume "b\<lsq>a" 
    with A4 have "a\<ra>\<one> \<lsq> a" by (rule Int_order_transitive)
    moreover from A1 have "a \<lsq> a\<ra>\<one>"
      using Int_ZF_2_L12B by simp
    ultimately have "a\<ra>\<one> = a"
      by (rule Int_ZF_2_L3) 
    with A1 have False using Int_ZF_1_L14 by simp 
  } then show "\<not>(b\<lsq>a)" by auto
qed

text\<open>Another form of stating that there are no integers
  between integers $m$ and $m+1$.\<close>

corollary (in int0) no_int_between: assumes A1: "a\<in>\<int>"  "b\<in>\<int>"
  shows "b\<lsq>a \<or> a\<ra>\<one> \<lsq> b"
  using A1 Int_ZF_1_3_L6 by auto (* A1 has to be here *)    


text\<open>Another way of saying what it means that one integer is not
  greater or equal than another.\<close>

corollary (in int0) Int_ZF_1_3_L6A:
  assumes A1: "a\<in>\<int>"  "b\<in>\<int>" and A2: "\<not>(b\<lsq>a)"
  shows "a \<lsq> b\<rs>\<one>"
proof -
  from A1 A2 have "a\<ra>\<one> \<rs> \<one> \<lsq> b \<rs> \<one>"
    using Int_ZF_1_3_L6 int_zero_one_are_int Int_ZF_1_1_L4 
      int_ord_transl_inv by simp
  with A1 show "a \<lsq> b\<rs>\<one>"
    using int_zero_one_are_int Int_ZF_1_2_L3
    by simp
qed

text\<open>Yet another form of stating that there are nointegers between
  $m$ and $m+1$.\<close>

lemma (in int0) no_int_between1: 
  assumes A1: "a\<lsq>b"  and A2: "a\<noteq>b"
  shows 
  "a\<ra>\<one> \<lsq> b"
  "a \<lsq> b\<rs>\<one>"
proof -
  from A1 have T: "a\<in>\<int>"  "b\<in>\<int>" using Int_ZF_2_L1A
    by auto
  { assume "b\<lsq>a"
    with A1 have "a=b" by (rule Int_ZF_2_L3)
    with A2 have False by simp }
  then have "\<not>(b\<lsq>a)" by auto
  with T show 
    "a\<ra>\<one> \<lsq> b" 
    "a \<lsq> b\<rs>\<one>"
    using no_int_between Int_ZF_1_3_L6A by auto
qed

text\<open>We can decompose proofs into three cases: $a=b$, $a\leq b-1b$ or 
  $a\geq b+1b$.\<close>

lemma (in int0) Int_ZF_1_3_L6B: assumes A1: "a\<in>\<int>"  "b\<in>\<int>"
  shows "a=b \<or> (a \<lsq> b\<rs>\<one>) \<or> (b\<ra>\<one> \<lsq>a)"
proof -
  from A1 have "a=b \<or> (a\<lsq>b \<and> a\<noteq>b) \<or> (b\<lsq>a \<and> b\<noteq>a)"
    using Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L31
    by simp
  then show ?thesis using no_int_between1
    by auto
qed

text\<open>A special case of \<open>Int_ZF_1_3_L6B\<close> when $b=0$. This
  allows to split the proofs in cases $a\leq -1$, $a=0$ and $a\geq 1$.\<close>

corollary (in int0) Int_ZF_1_3_L6C: assumes A1: "a\<in>\<int>"
  shows "a=\<zero> \<or> (a \<lsq> \<rm>\<one>) \<or> (\<one>\<lsq>a)"  
proof -
  from A1 have "a=\<zero> \<or> (a \<lsq> \<zero> \<rs>\<one>) \<or> (\<zero> \<ra>\<one> \<lsq>a)"
    using int_zero_one_are_int Int_ZF_1_3_L6B by simp
  then show ?thesis using Int_ZF_1_1_L4 int_zero_one_are_int
    by simp
qed
  

text\<open>An integer is not less or equal zero iff it is greater or equal one.\<close>

lemma (in int0) Int_ZF_1_3_L7: assumes "a\<in>\<int>" 
  shows "\<not>(a\<lsq>\<zero>) \<longleftrightarrow> \<one> \<lsq> a"
  using assms int_zero_one_are_int Int_ZF_1_3_L6 Int_ZF_1_1_L4
  by simp

text\<open>Product of positive integers is positive.\<close>

lemma (in int0) Int_ZF_1_3_L8: 
  assumes "a\<in>\<int>"  "b\<in>\<int>" 
  and "\<not>(a\<lsq>\<zero>)"  "\<not>(b\<lsq>\<zero>)"
  shows "\<not>((a\<cdot>b) \<lsq> \<zero>)"
  using assms Int_ZF_1_3_L7 Int_ZF_1_3_L3 Int_ZF_1_1_L5 Int_ZF_1_3_L7
  by simp

text\<open>If $a\cdot b$ is nonnegative and $b$ is positive, then $a$ is 
  nonnegative. Proof by contradiction.\<close>

lemma (in int0) Int_ZF_1_3_L9:
  assumes A1: "a\<in>\<int>"  "b\<in>\<int>"
  and A2:  "\<not>(b\<lsq>\<zero>)" and A3: "a\<cdot>b \<lsq> \<zero>" 
  shows "a\<lsq>\<zero>"
proof -
  { assume "\<not>(a\<lsq>\<zero>)"
    with A1 A2 have "\<not>((a\<cdot>b) \<lsq> \<zero>)" using Int_ZF_1_3_L8
      by simp
  } with A3 show "a\<lsq>\<zero>" by auto
qed

text\<open>One integer is less or equal another iff the difference is nonpositive.\<close>

lemma (in int0) Int_ZF_1_3_L10:
  assumes "a\<in>\<int>"  "b\<in>\<int>"
  shows "a\<lsq>b \<longleftrightarrow> a\<rs>b \<lsq> \<zero>"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L9
  by simp

text\<open>Some conclusions from the fact that one integer
  is less or equal than another.\<close>

lemma (in int0) Int_ZF_1_3_L10A: assumes "a\<lsq>b"
  shows "\<zero> \<lsq> b\<rs>a"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L12A
  by simp

text\<open>We can simplify out a positive element on both sides of an 
  inequality.\<close>

lemma (in int0) Int_ineq_simpl_positive: 
  assumes A1: "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>" 
  and A2: "a\<cdot>c \<lsq> b\<cdot>c" and A4: "\<not>(c\<lsq>\<zero>)"
  shows "a \<lsq> b"
proof -
  from A1 A4 have "a\<rs>b \<in>  \<int>"  "c\<in>\<int>"  "\<not>(c\<lsq>\<zero>)"
    using Int_ZF_1_1_L5 by auto
  moreover from A1 A2 have "(a\<rs>b)\<cdot>c \<lsq> \<zero>"
    using Int_ZF_1_1_L5 Int_ZF_1_3_L10 Int_ZF_1_1_L6
    by simp
  ultimately have "a\<rs>b \<lsq> \<zero>" by (rule Int_ZF_1_3_L9)
  with A1 show "a \<lsq> b" using Int_ZF_1_3_L10 by simp
qed

text\<open>A technical lemma about conclusion from an inequality between
  absolute values. This is a property of ordered rings.\<close>

lemma (in int0) Int_ZF_1_3_L11:
  assumes A1: "a\<in>\<int>"  "b\<in>\<int>"
  and A2: "\<not>(abs(a) \<lsq> abs(b))"
  shows "\<not>(abs(a) \<lsq> \<zero>)"
proof -
  { assume "abs(a) \<lsq> \<zero>"
    moreover from A1 have "\<zero> \<lsq> abs(a)" using int_abs_nonneg
      by simp
    ultimately have "abs(a) = \<zero>" by (rule Int_ZF_2_L3)
    with A1 A2 have False using int_abs_nonneg by simp
  } then show  "\<not>(abs(a) \<lsq> \<zero>)" by auto
qed

text\<open>Negative times positive is negative. This a property of ordered rings.\<close>

lemma (in int0) Int_ZF_1_3_L12:
  assumes "a\<lsq>\<zero>"  and "\<zero>\<lsq>b"
  shows "a\<cdot>b \<lsq> \<zero>"
  using assms Int_ZF_1_3_T1 ring1.OrdRing_ZF_1_L8 
  by simp

text\<open>We can multiply an inequality by a nonnegative number. 
  This is a property of ordered rings.\<close>

lemma (in int0) Int_ZF_1_3_L13:
  assumes A1: "a\<lsq>b" and A2: "\<zero>\<lsq>c"
  shows 
  "a\<cdot>c \<lsq> b\<cdot>c"
  "c\<cdot>a \<lsq> c\<cdot>b"
  using assms Int_ZF_1_3_T1 ring1.OrdRing_ZF_1_L9 by auto

text\<open>A technical lemma about decreasing a factor in an inequality.\<close>

lemma (in int0) Int_ZF_1_3_L13A:
  assumes "\<one>\<lsq>a" and "b\<lsq>c" and "(a\<ra>\<one>)\<cdot>c \<lsq> d"
  shows "(a\<ra>\<one>)\<cdot>b \<lsq> d"
proof -
  from assms have 
    "(a\<ra>\<one>)\<cdot>b \<lsq> (a\<ra>\<one>)\<cdot>c"
    "(a\<ra>\<one>)\<cdot>c \<lsq> d"
    using Int_ZF_2_L16C Int_ZF_1_3_L13 by auto
  then show "(a\<ra>\<one>)\<cdot>b \<lsq> d" by (rule Int_order_transitive)
qed

text\<open>We can multiply an inequality by a positive number. 
  This is a property of ordered rings.\<close>

lemma (in int0) Int_ZF_1_3_L13B:  
  assumes A1: "a\<lsq>b" and A2: "c\<in>\<int>\<^sub>+"
  shows  
  "a\<cdot>c \<lsq> b\<cdot>c"  
  "c\<cdot>a \<lsq> c\<cdot>b"
proof -
  let ?R = "\<int>"
  let ?A = "IntegerAddition"
  let ?M = "IntegerMultiplication"
  let ?r = "IntegerOrder"
  from A1 A2 have 
    "ring1(?R, ?A, ?M, ?r)" 
    "\<langle>a,b\<rangle> \<in> ?r"
    "c \<in> PositiveSet(?R, ?A, ?r)"
    using Int_ZF_1_3_T1 by auto
  then show 
    "a\<cdot>c \<lsq> b\<cdot>c"  
    "c\<cdot>a \<lsq> c\<cdot>b"
    using ring1.OrdRing_ZF_1_L9A by auto
qed

text\<open>A rearrangement with four integers and absolute value.\<close>

lemma (in int0) Int_ZF_1_3_L14:
  assumes  A1: "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>"  "d\<in>\<int>" 
  shows "abs(a\<cdot>b)\<ra>(abs(a)\<ra>c)\<cdot>d = (d\<ra>abs(b))\<cdot>abs(a)\<ra>c\<cdot>d"
proof -
  from A1 have T1: 
    "abs(a) \<in> \<int>"  "abs(b) \<in> \<int>" 
    "abs(a)\<cdot>abs(b) \<in> \<int>" 
    "abs(a)\<cdot>d \<in> \<int>" 
    "c\<cdot>d \<in> \<int>"
    "abs(b)\<ra>d \<in> \<int>" 
    using Int_ZF_2_L14 Int_ZF_1_1_L5 by auto
  with A1 have "abs(a\<cdot>b)\<ra>(abs(a)\<ra>c)\<cdot>d = abs(a)\<cdot>(abs(b)\<ra>d)\<ra>c\<cdot>d"
    using Int_ZF_1_3_L5 Int_ZF_1_1_L1 Int_ZF_1_1_L7 by simp
  with A1 T1 show ?thesis using Int_ZF_1_1_L5 by simp
qed

text\<open>A technical lemma about what happens when one absolute value is
  not greater or equal than another.\<close>

lemma (in int0) Int_ZF_1_3_L15: assumes A1: "m\<in>\<int>" "n\<in>\<int>"
  and A2: "\<not>(abs(m) \<lsq> abs(n))"
  shows "n \<lsq> abs(m)"  "m\<noteq>\<zero>" 
proof -
  from A1 have T1: "n \<lsq> abs(n)" 
    using Int_ZF_2_L19C by simp
  from A1 have "abs(n) \<in> \<int>"  "abs(m) \<in> \<int>"
    using Int_ZF_2_L14 by auto
  moreover note A2
  ultimately have "abs(n) \<lsq> abs(m)"
    by (rule Int_ZF_2_L19)
  with T1 show  "n \<lsq> abs(m)" by (rule Int_order_transitive)
  from A1 A2 show "m\<noteq>\<zero>" using Int_ZF_2_L18 int_abs_nonneg by auto
qed

text\<open>Negative of a nonnegative is nonpositive.\<close>

lemma (in int0) Int_ZF_1_3_L16: assumes A1: "\<zero> \<lsq> m"
  shows "(\<rm>m) \<lsq> \<zero>"
proof -
  from A1 have "(\<rm>m) \<lsq> (\<rm>\<zero>)"
    using Int_ZF_2_L10 by simp
  then show "(\<rm>m) \<lsq> \<zero>" using Int_ZF_1_L11
    by simp
qed

text\<open>Some statements about intervals centered at $0$.\<close>

lemma (in int0) Int_ZF_1_3_L17: assumes A1: "m\<in>\<int>"
  shows 
  "(\<rm>abs(m)) \<lsq> abs(m)"
  "(\<rm>abs(m))..abs(m) \<noteq> 0"
proof -
  from A1 have "(\<rm>abs(m)) \<lsq> \<zero>"  "\<zero> \<lsq> abs(m)" 
    using int_abs_nonneg Int_ZF_1_3_L16 by auto
  then show "(\<rm>abs(m)) \<lsq> abs(m)" by (rule Int_order_transitive)
  then have "abs(m) \<in> (\<rm>abs(m))..abs(m)"
    using int_ord_is_refl Int_ZF_2_L1A Order_ZF_2_L2 by simp
  thus "(\<rm>abs(m))..abs(m) \<noteq> 0" by auto
qed

text\<open>The greater of two integers is indeed greater than both, 
  and the smaller one is smaller that both.\<close>

lemma (in int0) Int_ZF_1_3_L18: assumes A1: "m\<in>\<int>"  "n\<in>\<int>"
  shows 
  "m \<lsq> GreaterOf(IntegerOrder,m,n)"
  "n \<lsq> GreaterOf(IntegerOrder,m,n)"
  "SmallerOf(IntegerOrder,m,n) \<lsq> m"
  "SmallerOf(IntegerOrder,m,n) \<lsq> n"
  using assms Int_ZF_2_T1 Order_ZF_3_L2 by auto

text\<open>If $|m| \leq n$, then $m \in -n..n$.\<close>

lemma (in int0) Int_ZF_1_3_L19: 
  assumes A1: "m\<in>\<int>" and A2: "abs(m) \<lsq> n"
  shows 
  "(\<rm>n) \<lsq> m"  "m \<lsq> n"
  "m \<in> (\<rm>n)..n"
  "\<zero> \<lsq> n"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_3_L8  
    group3.OrderedGroup_ZF_3_L8A Order_ZF_2_L1 
  by auto

text\<open>A slight generalization of the above lemma.\<close>

lemma (in int0) Int_ZF_1_3_L19A: 
  assumes A1: "m\<in>\<int>" and A2: "abs(m) \<lsq> n" and A3: "\<zero>\<lsq>k"
  shows "(\<rm>(n\<ra>k)) \<lsq> m"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_3_L8B
  by simp

text\<open>Sets of integers that have absolute value bounded are bounded.\<close>

lemma (in int0) Int_ZF_1_3_L20:
  assumes A1: "\<forall>x\<in>X. b(x) \<in> \<int> \<and> abs(b(x)) \<lsq> L"
  shows "IsBounded({b(x). x\<in>X},IntegerOrder)"
proof -
  let ?G = "\<int>"
  let ?P = "IntegerAddition"
  let ?r = "IntegerOrder"
  from A1 have
    "group3(?G, ?P, ?r)"
    "?r {is total on} ?G"
    "\<forall>x\<in>X. b(x) \<in> ?G \<and> \<langle>AbsoluteValue(?G, ?P, ?r) ` b(x), L\<rangle> \<in> ?r"
    using Int_ZF_2_T1 by auto
  then show "IsBounded({b(x). x\<in>X},IntegerOrder)"
    by (rule group3.OrderedGroup_ZF_3_L9A)
qed

text\<open>If a set is bounded, then the absolute values of the elements of that
  set are bounded.\<close>

lemma (in int0) Int_ZF_1_3_L20A: assumes "IsBounded(A,IntegerOrder)"
  shows "\<exists>L. \<forall>a\<in>A. abs(a) \<lsq> L"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_3_L10A 
  by simp

text\<open>Absolute vaues of integers from a finite image of integers are bounded
  by an integer.\<close>

lemma (in int0) Int_ZF_1_3_L20AA: 
  assumes A1: "{b(x). x\<in>\<int>} \<in> Fin(\<int>)"
  shows "\<exists>L\<in>\<int>. \<forall>x\<in>\<int>. abs(b(x)) \<lsq> L"
  using assms int_not_empty Int_ZF_2_T1 group3.OrderedGroup_ZF_3_L11A
  by simp

text\<open>If absolute values of values of some integer function are bounded,
  then the image a set from the domain is a bounded set.\<close>

lemma (in int0) Int_ZF_1_3_L20B:
  assumes "f:X\<rightarrow>\<int>" and "A\<subseteq>X" and "\<forall>x\<in>A. abs(f`(x)) \<lsq> L"
  shows  "IsBounded(f``(A),IntegerOrder)"
proof -
  let ?G = "\<int>"
  let ?P = "IntegerAddition"
  let ?r = "IntegerOrder"
  from assms have 
    "group3(?G, ?P, ?r)"
    "?r {is total on} ?G"
    "f:X\<rightarrow>?G"
    "A\<subseteq>X"
    "\<forall>x\<in>A. \<langle>AbsoluteValue(?G, ?P, ?r)`(f`(x)), L\<rangle> \<in> ?r"
    using Int_ZF_2_T1 by auto
  then show "IsBounded(f``(A), ?r)" 
    by (rule group3.OrderedGroup_ZF_3_L9B)
qed

text\<open>A special case of the previous lemma for a function from integers to 
  integers.\<close>

corollary (in int0) Int_ZF_1_3_L20C:
  assumes "f:\<int>\<rightarrow>\<int>" and "\<forall>m\<in>\<int>. abs(f`(m)) \<lsq> L"
  shows "f``(\<int>) \<in> Fin(\<int>)"
proof -
  from assms have "f:\<int>\<rightarrow>\<int>" "\<int> \<subseteq> \<int>"  "\<forall>m\<in>\<int>. abs(f`(m)) \<lsq> L"
    by auto
  then have "IsBounded(f``(\<int>),IntegerOrder)"
    by (rule Int_ZF_1_3_L20B)
  then show "f``(\<int>) \<in> Fin(\<int>)" using Int_bounded_iff_fin
    by simp
qed

text\<open>A triangle inequality with three integers. Property of 
  linearly ordered abelian groups.\<close>

lemma (in int0) int_triangle_ineq3: 
  assumes A1: "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>"
  shows "abs(a\<rs>b\<rs>c) \<lsq> abs(a) \<ra> abs(b) \<ra> abs(c)"
proof -
  from A1 have T: "a\<rs>b \<in> \<int>"  "abs(c) \<in> \<int>"
    using Int_ZF_1_1_L5 Int_ZF_2_L14 by auto
  with A1 have "abs(a\<rs>b\<rs>c) \<lsq> abs(a\<rs>b) \<ra> abs(c)"
    using Int_triangle_ineq1 by simp
  moreover from A1 T have 
    "abs(a\<rs>b) \<ra> abs(c) \<lsq>  abs(a) \<ra> abs(b) \<ra> abs(c)"
    using Int_triangle_ineq1 int_ord_transl_inv by simp
  ultimately show ?thesis by (rule Int_order_transitive)
qed

text\<open>If $a\leq c$ and $b\leq c$, then $a+b\leq 2\cdot c$. 
  Property of ordered rings.\<close>

lemma (in int0) Int_ZF_1_3_L21:
  assumes A1: "a\<lsq>c"  "b\<lsq>c" shows "a\<ra>b \<lsq> \<two>\<cdot>c"
  using assms Int_ZF_1_3_T1 ring1.OrdRing_ZF_2_L6 by simp

text\<open>If an integer $a$ is between $b$ and $b+c$, then
  $|b-a| \leq c$. Property of ordered groups.\<close>

lemma (in int0) Int_ZF_1_3_L22: 
  assumes "a\<lsq>b" and "c\<in>\<int>" and "b\<lsq> c\<ra>a"
  shows "abs(b\<rs>a) \<lsq> c"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_3_L8C
  by simp

text\<open>An application of the triangle inequality with four
  integers. Property of linearly ordered abelian groups.\<close>

lemma (in int0) Int_ZF_1_3_L22A: 
  assumes  "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>"  "d\<in>\<int>"
  shows "abs(a\<rs>c) \<lsq> abs(a\<ra>b) \<ra> abs(c\<ra>d) \<ra> abs(b\<rs>d)"
  using assms Int_ZF_1_T2 Int_ZF_2_T1 group3.OrderedGroup_ZF_3_L7F
  by simp

text\<open>If an integer $a$ is between $b$ and $b+c$, then
  $|b-a| \leq c$. Property of ordered groups.
  A version of \<open>Int_ZF_1_3_L22\<close> with sligtly different
  assumptions.\<close>

lemma (in int0) Int_ZF_1_3_L23: 
  assumes A1: "a\<lsq>b" and A2: "c\<in>\<int>" and A3: "b\<lsq> a\<ra>c"
  shows "abs(b\<rs>a) \<lsq> c"
proof -
  from A1 have "a \<in> \<int>"
    using Int_ZF_2_L1A by simp
  with A2 A3 have "b\<lsq> c\<ra>a"
    using Int_ZF_1_1_L5 by simp
  with A1 A2 show "abs(b\<rs>a) \<lsq> c"
    using Int_ZF_1_3_L22 by simp
qed

subsection\<open>Maximum and minimum of a set of integers\<close>

text\<open>In this section we provide some sufficient conditions for
  integer subsets to have extrema (maxima and minima).\<close>

text\<open>Finite nonempty subsets of integers attain maxima and minima.\<close>

theorem (in int0) Int_fin_have_max_min:
  assumes A1: "A \<in> Fin(\<int>)" and A2: "A\<noteq>0"
  shows 
  "HasAmaximum(IntegerOrder,A)"
  "HasAminimum(IntegerOrder,A)"  
  "Maximum(IntegerOrder,A) \<in> A"
  "Minimum(IntegerOrder,A) \<in> A"
  "\<forall>x\<in>A. x \<lsq> Maximum(IntegerOrder,A)"
  "\<forall>x\<in>A. Minimum(IntegerOrder,A) \<lsq> x"
  "Maximum(IntegerOrder,A) \<in> \<int>"
  "Minimum(IntegerOrder,A) \<in> \<int>"
proof -
  from A1 have 
    "A=0 \<or> HasAmaximum(IntegerOrder,A)" and
    "A=0 \<or> HasAminimum(IntegerOrder,A)"
    using Int_ZF_2_T1 Int_ZF_2_L6 Finite_ZF_1_1_T1A Finite_ZF_1_1_T1B
    by auto
  with A2 show 
    "HasAmaximum(IntegerOrder,A)"
    "HasAminimum(IntegerOrder,A)"  
    by auto
  from A1 A2 show 
    "Maximum(IntegerOrder,A) \<in> A"
    "Minimum(IntegerOrder,A) \<in> A"
    "\<forall>x\<in>A. x \<lsq> Maximum(IntegerOrder,A)"
    "\<forall>x\<in>A. Minimum(IntegerOrder,A) \<lsq> x"
    using Int_ZF_2_T1 Finite_ZF_1_T2 by auto
  moreover from A1 have "A\<subseteq>\<int>" using FinD by simp
  ultimately show 
    "Maximum(IntegerOrder,A) \<in> \<int>"
    "Minimum(IntegerOrder,A) \<in> \<int>"
    by auto
qed

text\<open>Bounded nonempty integer subsets attain maximum and minimum.\<close>

theorem (in int0) Int_bounded_have_max_min:
  assumes "IsBounded(A,IntegerOrder)" and "A\<noteq>0"
  shows 
  "HasAmaximum(IntegerOrder,A)"
  "HasAminimum(IntegerOrder,A)"  
  "Maximum(IntegerOrder,A) \<in> A"
  "Minimum(IntegerOrder,A) \<in> A"
  "\<forall>x\<in>A. x \<lsq> Maximum(IntegerOrder,A)"
  "\<forall>x\<in>A. Minimum(IntegerOrder,A) \<lsq> x"
  "Maximum(IntegerOrder,A) \<in> \<int>"
  "Minimum(IntegerOrder,A) \<in> \<int>"
  using assms Int_fin_have_max_min Int_bounded_iff_fin
  by auto

text\<open>Nonempty set of integers that is bounded below attains its minimum.\<close>

theorem (in int0) int_bounded_below_has_min:
  assumes A1: "IsBoundedBelow(A,IntegerOrder)" and A2: "A\<noteq>0"
  shows "
  HasAminimum(IntegerOrder,A)"
  "Minimum(IntegerOrder,A) \<in> A"
  (*"Minimum(IntegerOrder,A) \<in> \<int>"*)
  "\<forall>x\<in>A. Minimum(IntegerOrder,A) \<lsq> x"
proof -
  from A1 A2 have
    "IntegerOrder {is total on} \<int>"
    "trans(IntegerOrder)"
    "IntegerOrder \<subseteq> \<int>\<times>\<int>"
    "\<forall>A. IsBounded(A,IntegerOrder) \<and> A\<noteq>0 \<longrightarrow> HasAminimum(IntegerOrder,A)"
    "A\<noteq>0"  "IsBoundedBelow(A,IntegerOrder)"
    using Int_ZF_2_T1 Int_ZF_2_L6 Int_ZF_2_L1B Int_bounded_have_max_min
    by auto
  then show "HasAminimum(IntegerOrder,A)"
    by (rule Order_ZF_4_L11) (*blast works too*)
  then show 
    "Minimum(IntegerOrder,A) \<in> A"
    "\<forall>x\<in>A. Minimum(IntegerOrder,A) \<lsq> x"
    using Int_ZF_2_L4 Order_ZF_4_L4 by auto
qed

text\<open>Nonempty set of integers that is bounded above attains its
  maximum.\<close>

theorem (in int0) int_bounded_above_has_max:
  assumes A1: "IsBoundedAbove(A,IntegerOrder)" and A2: "A\<noteq>0"
  shows 
  "HasAmaximum(IntegerOrder,A)"
  "Maximum(IntegerOrder,A) \<in> A"
  "Maximum(IntegerOrder,A) \<in> \<int>"
  "\<forall>x\<in>A. x \<lsq> Maximum(IntegerOrder,A)"
proof -
  from A1 A2 have
    "IntegerOrder {is total on} \<int>"
    "trans(IntegerOrder)" and
    I: "IntegerOrder \<subseteq> \<int>\<times>\<int>" and
    "\<forall>A. IsBounded(A,IntegerOrder) \<and> A\<noteq>0 \<longrightarrow> HasAmaximum(IntegerOrder,A)"
    "A\<noteq>0"  "IsBoundedAbove(A,IntegerOrder)"
    using Int_ZF_2_T1 Int_ZF_2_L6 Int_ZF_2_L1B Int_bounded_have_max_min
    by auto
  then show "HasAmaximum(IntegerOrder,A)"
    by (rule Order_ZF_4_L11A)
  then show 
    II: "Maximum(IntegerOrder,A) \<in> A" and
    "\<forall>x\<in>A. x \<lsq> Maximum(IntegerOrder,A)"
    using Int_ZF_2_L4 Order_ZF_4_L3 by auto
  from I A1 have "A \<subseteq> \<int>" by (rule Order_ZF_3_L1A)
  with II show "Maximum(IntegerOrder,A) \<in> \<int>" by auto
qed
 
text\<open>A set defined by separation over a bounded set attains its maximum
  and minimum.\<close>

lemma (in int0) Int_ZF_1_4_L1:
  assumes A1: "IsBounded(A,IntegerOrder)" and A2: "A\<noteq>0"
  and A3: "\<forall>q\<in>\<int>. F(q) \<in> \<int>"
  and A4: "K = {F(q). q \<in> A}"
  shows
  "HasAmaximum(IntegerOrder,K)"
  "HasAminimum(IntegerOrder,K)"  
  "Maximum(IntegerOrder,K) \<in> K"
  "Minimum(IntegerOrder,K) \<in> K"
  "Maximum(IntegerOrder,K) \<in> \<int>"
  "Minimum(IntegerOrder,K) \<in> \<int>"
  "\<forall>q\<in>A. F(q) \<lsq> Maximum(IntegerOrder,K)"
  "\<forall>q\<in>A. Minimum(IntegerOrder,K) \<lsq> F(q)"
  "IsBounded(K,IntegerOrder)"
proof -
  from A1 have "A \<in> Fin(\<int>)" using Int_bounded_iff_fin
    by simp
  with A3 have "{F(q). q \<in> A} \<in> Fin(\<int>)"
    by (rule fin_image_fin)
  with A2 A4 have T1: "K \<in> Fin(\<int>)"  "K\<noteq>0" by auto
  then show T2: 
    "HasAmaximum(IntegerOrder,K)"
    "HasAminimum(IntegerOrder,K)"  
    and "Maximum(IntegerOrder,K) \<in> K"
    "Minimum(IntegerOrder,K) \<in> K"
    "Maximum(IntegerOrder,K) \<in> \<int>"
    "Minimum(IntegerOrder,K) \<in> \<int>"
    using Int_fin_have_max_min by auto
  { fix q assume "q\<in>A" 
    with A4 have "F(q) \<in> K" by auto
    with T1 have 
      "F(q) \<lsq> Maximum(IntegerOrder,K)"
      "Minimum(IntegerOrder,K) \<lsq> F(q)"
      using Int_fin_have_max_min by auto
  } then show 
      "\<forall>q\<in>A. F(q) \<lsq> Maximum(IntegerOrder,K)"
      "\<forall>q\<in>A. Minimum(IntegerOrder,K) \<lsq> F(q)"
    by auto
  from T2 show "IsBounded(K,IntegerOrder)"
    using Order_ZF_4_L7 Order_ZF_4_L8A IsBounded_def
    by simp
qed

text\<open>A three element set has a maximume and minimum.\<close>

lemma (in int0) Int_ZF_1_4_L1A: assumes A1: "a\<in>\<int>"  "b\<in>\<int>"  "c\<in>\<int>"
  shows 
  "Maximum(IntegerOrder,{a,b,c}) \<in>  \<int>"
  "a \<lsq> Maximum(IntegerOrder,{a,b,c})"
  "b \<lsq> Maximum(IntegerOrder,{a,b,c})"
  "c \<lsq> Maximum(IntegerOrder,{a,b,c})"
  using assms Int_ZF_2_T1 Finite_ZF_1_L2A by auto

text\<open>Integer functions attain maxima and minima over intervals.\<close>

lemma (in int0) Int_ZF_1_4_L2:
  assumes A1: "f:\<int>\<rightarrow>\<int>" and A2: "a\<lsq>b"
  shows
  "maxf(f,a..b) \<in> \<int>"
  "\<forall>c \<in> a..b. f`(c) \<lsq> maxf(f,a..b)"
  "\<exists>c \<in> a..b. f`(c) = maxf(f,a..b)"
  "minf(f,a..b) \<in> \<int>"
  "\<forall>c \<in> a..b. minf(f,a..b) \<lsq> f`(c)"
  "\<exists>c \<in> a..b. f`(c) = minf(f,a..b)"
proof -
  from A2 have T: "a\<in>\<int>"  "b\<in>\<int>"  "a..b \<subseteq> \<int>"
    using Int_ZF_2_L1A Int_ZF_2_L1B Order_ZF_2_L6 
    by auto
  with A1 A2 have
    "Maximum(IntegerOrder,f``(a..b)) \<in> f``(a..b)" 
    "\<forall>x\<in>f``(a..b). x \<lsq> Maximum(IntegerOrder,f``(a..b))"
    "Maximum(IntegerOrder,f``(a..b)) \<in> \<int>"
    "Minimum(IntegerOrder,f``(a..b)) \<in> f``(a..b)" 
    "\<forall>x\<in>f``(a..b). Minimum(IntegerOrder,f``(a..b)) \<lsq> x"
    "Minimum(IntegerOrder,f``(a..b)) \<in> \<int>"
    using Int_ZF_4_L8 Int_ZF_2_T1 group3.OrderedGroup_ZF_2_L6
      Int_fin_have_max_min by auto
  with A1 T show
    "maxf(f,a..b) \<in> \<int>"
    "\<forall>c \<in> a..b. f`(c) \<lsq> maxf(f,a..b)"
    "\<exists>c \<in> a..b. f`(c) = maxf(f,a..b)"
    "minf(f,a..b) \<in> \<int>"
    "\<forall>c \<in> a..b. minf(f,a..b) \<lsq> f`(c)"
    "\<exists>c \<in> a..b. f`(c) = minf(f,a..b)"
    using func_imagedef by auto
qed

subsection\<open>The set of nonnegative integers\<close>

text\<open>The set of nonnegative integers looks like the set of natural numbers.
  We explore that in this section. We also rephrase some lemmas about the set
  of positive integers known from the theory of ordered groups.\<close>

text\<open>The set of positive integers is closed under addition.\<close>

lemma (in int0) pos_int_closed_add: 
  shows "\<int>\<^sub>+ {is closed under} IntegerAddition"
  using Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L13 by simp

text\<open>Text expended version of the fact that the set of positive integers 
  is closed under addition\<close>

lemma (in int0) pos_int_closed_add_unfolded: 
  assumes "a\<in>\<int>\<^sub>+"  "b\<in>\<int>\<^sub>+"  shows "a\<ra>b \<in> \<int>\<^sub>+"
  using assms pos_int_closed_add IsOpClosed_def
  by simp

text\<open>\<open>\<int>\<^sup>+\<close> is bounded below.\<close>

lemma (in int0) Int_ZF_1_5_L1: shows 
  "IsBoundedBelow(\<int>\<^sup>+,IntegerOrder)"
  "IsBoundedBelow(\<int>\<^sub>+,IntegerOrder)"
  using Nonnegative_def PositiveSet_def IsBoundedBelow_def by auto

text\<open>Subsets of \<open>\<int>\<^sup>+\<close> are bounded below.\<close>

lemma (in int0) Int_ZF_1_5_L1A: assumes "A \<subseteq> \<int>\<^sup>+" 
  shows "IsBoundedBelow(A,IntegerOrder)"
  using assms Int_ZF_1_5_L1 Order_ZF_3_L12 by blast

text\<open>Subsets of \<open>\<int>\<^sub>+\<close> are bounded below.\<close>

lemma (in int0) Int_ZF_1_5_L1B: assumes A1: "A \<subseteq> \<int>\<^sub>+" 
  shows "IsBoundedBelow(A,IntegerOrder)"
  using A1 Int_ZF_1_5_L1 Order_ZF_3_L12 by blast (*A1 label has to be here*)

text\<open>Every nonempty subset of positive integers has a mimimum.\<close>

lemma (in int0) Int_ZF_1_5_L1C: assumes "A \<subseteq> \<int>\<^sub>+" and "A \<noteq> 0"
  shows 
  "HasAminimum(IntegerOrder,A)"
  "Minimum(IntegerOrder,A) \<in> A"
  "\<forall>x\<in>A. Minimum(IntegerOrder,A) \<lsq> x"
  using assms Int_ZF_1_5_L1B int_bounded_below_has_min by auto

text\<open>Infinite subsets of $Z^+$ do not have a maximum - If $A\subseteq Z^+$
  then for every integer we can find one in the set that is not smaller.\<close>

lemma (in int0) Int_ZF_1_5_L2:
  assumes A1: "A \<subseteq> \<int>\<^sup>+"  and A2: "A \<notin> Fin(\<int>)" and A3: "D\<in>\<int>"
  shows "\<exists>n\<in>A. D\<lsq>n"
proof -
  { assume "\<forall>n\<in>A. \<not>(D\<lsq>n)" 
    moreover from A1 A3 have "D\<in>\<int>"  "\<forall>n\<in>A. n\<in>\<int>" 
      using Nonnegative_def by auto
    ultimately have "\<forall>n\<in>A. n\<lsq>D"
      using Int_ZF_2_L19 by blast
    hence "\<forall>n\<in>A. \<langle>n,D\<rangle> \<in> IntegerOrder" by simp
    then have "IsBoundedAbove(A,IntegerOrder)"
      by (rule Order_ZF_3_L10)
    with A1 have "IsBounded(A,IntegerOrder)"
      using Int_ZF_1_5_L1A IsBounded_def by simp
    with A2 have False using Int_bounded_iff_fin by auto
  } thus ?thesis by auto
qed

text\<open>Infinite subsets of $Z_+$ do not have a maximum - If $A\subseteq Z_+$
  then for every integer we can find one in the set that is not smaller.  
  This is very similar to \<open>Int_ZF_1_5_L2\<close>, except we have \<open>\<int>\<^sub>+\<close>
  instead of \<open>\<int>\<^sup>+\<close> here.\<close>

lemma (in int0) Int_ZF_1_5_L2A:
  assumes A1: "A \<subseteq> \<int>\<^sub>+"  and A2: "A \<notin> Fin(\<int>)" and A3: "D\<in>\<int>"
  shows "\<exists>n\<in>A. D\<lsq>n"
proof -
{ assume "\<forall>n\<in>A. \<not>(D\<lsq>n)" 
    moreover from A1 A3 have "D\<in>\<int>"  "\<forall>n\<in>A. n\<in>\<int>" 
      using PositiveSet_def by auto
    ultimately have "\<forall>n\<in>A. n\<lsq>D"
      using Int_ZF_2_L19 by blast
    hence "\<forall>n\<in>A. \<langle>n,D\<rangle> \<in> IntegerOrder" by simp
    then have "IsBoundedAbove(A,IntegerOrder)"
      by (rule Order_ZF_3_L10)
    with A1 have "IsBounded(A,IntegerOrder)"
      using Int_ZF_1_5_L1B IsBounded_def by simp
    with A2 have False using Int_bounded_iff_fin by auto
  } thus ?thesis by auto
qed

text\<open>An integer is either positive, zero, or its opposite is postitive.\<close>

lemma (in int0) Int_decomp: assumes "m\<in>\<int>"
  shows "Exactly_1_of_3_holds (m=\<zero>,m\<in>\<int>\<^sub>+,(\<rm>m)\<in>\<int>\<^sub>+)"
  using assms Int_ZF_2_T1 group3.OrdGroup_decomp 
  by simp

text\<open>An integer is zero, positive, or it's inverse is positive.\<close>

lemma (in int0) int_decomp_cases: assumes "m\<in>\<int>"
  shows "m=\<zero> \<or> m\<in>\<int>\<^sub>+ \<or> (\<rm>m) \<in> \<int>\<^sub>+"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L14
  by simp

text\<open>An integer is in the positive set iff it is greater or equal one.\<close>

lemma (in int0) Int_ZF_1_5_L3: shows "m\<in>\<int>\<^sub>+ \<longleftrightarrow> \<one>\<lsq>m"
proof
  assume "m\<in>\<int>\<^sub>+" then have "\<zero>\<lsq>m"  "m\<noteq>\<zero>"
    using PositiveSet_def by auto
  then have "\<zero>\<ra>\<one> \<lsq> m" 
    using Int_ZF_4_L1B by auto
  then show "\<one>\<lsq>m" 
    using int_zero_one_are_int Int_ZF_1_T2 group0.group0_2_L2
    by simp
next assume "\<one>\<lsq>m"
  then have "m\<in>\<int>"  "\<zero>\<lsq>m"  "m\<noteq>\<zero>"
    using Int_ZF_2_L1A Int_ZF_2_L16C by auto
  then show "m\<in>\<int>\<^sub>+" using PositiveSet_def by auto
qed

text\<open>The set of positive integers is closed under multiplication.
  The unfolded form.\<close>

lemma (in int0) pos_int_closed_mul_unfold: 
  assumes "a\<in>\<int>\<^sub>+"  "b\<in>\<int>\<^sub>+"
  shows "a\<cdot>b \<in> \<int>\<^sub>+"
  using assms Int_ZF_1_5_L3 Int_ZF_1_3_L3 by simp

text\<open>The set of positive integers is closed under multiplication.\<close>

lemma (in int0) pos_int_closed_mul: shows
  "\<int>\<^sub>+ {is closed under} IntegerMultiplication"
  using pos_int_closed_mul_unfold IsOpClosed_def
  by simp

text\<open>It is an overkill to prove that the ring of integers has no zero
  divisors this way, but why not?\<close>

lemma (in int0) int_has_no_zero_divs: 
  shows "HasNoZeroDivs(\<int>,IntegerAddition,IntegerMultiplication)"
  using pos_int_closed_mul Int_ZF_1_3_T1 ring1.OrdRing_ZF_3_L3
  by simp

text\<open>Nonnegative integers are positive ones plus zero.\<close>

lemma (in int0) Int_ZF_1_5_L3A: shows "\<int>\<^sup>+ = \<int>\<^sub>+ \<union> {\<zero>}"
  using Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L24 by simp

text\<open>We can make a function smaller than any constant on a given interval
  of positive integers by adding another constant.\<close>


lemma (in int0) Int_ZF_1_5_L4: 
  assumes A1: "f:\<int>\<rightarrow>\<int>" and A2: "K\<in>\<int>" "N\<in>\<int>"
  shows "\<exists>C\<in>\<int>. \<forall>n\<in>\<int>\<^sub>+. K \<lsq> f`(n) \<ra> C \<longrightarrow> N\<lsq>n"
proof -
  from A2 have "N\<lsq>\<one> \<or> \<two>\<lsq>N"
    using int_zero_one_are_int no_int_between
    by simp
  moreover
  { assume A3: "N\<lsq>\<one>"
    let ?C = "\<zero>"
    have "?C \<in> \<int>" using int_zero_one_are_int
      by simp
    moreover
    { fix n assume "n\<in>\<int>\<^sub>+"
      then have "\<one> \<lsq> n" using Int_ZF_1_5_L3
	by simp	
      with A3 have "N\<lsq>n" by (rule Int_order_transitive)
    } then have  "\<forall>n\<in>\<int>\<^sub>+. K \<lsq> f`(n) \<ra> ?C \<longrightarrow> N\<lsq>n"
      by auto
    ultimately have "\<exists>C\<in>\<int>. \<forall>n\<in>\<int>\<^sub>+. K \<lsq> f`(n) \<ra> C \<longrightarrow> N\<lsq>n"
      by auto }
  moreover
  { let ?C = "K \<rs> \<one> \<rs> maxf(f,\<one>..(N\<rs>\<one>))"
    assume "\<two>\<lsq>N"
    then have "\<two>\<rs>\<one> \<lsq> N\<rs>\<one>"
      using int_zero_one_are_int Int_ZF_1_1_L4 int_ord_transl_inv
      by simp
    then have I: "\<one> \<lsq> N\<rs>\<one>"
      using int_zero_one_are_int Int_ZF_1_2_L3 by simp
    with A1 A2 have T: 
      "maxf(f,\<one>..(N\<rs>\<one>)) \<in> \<int>"  "K\<rs>\<one> \<in> \<int>"  "?C \<in> \<int>"
      using Int_ZF_1_4_L2 Int_ZF_1_1_L5 int_zero_one_are_int
      by auto
    moreover
    { fix n assume A4: "n\<in>\<int>\<^sub>+" 
      { assume A5: "K \<lsq> f`(n) \<ra> ?C" and "\<not>(N\<lsq>n)"
	with A2 A4 have "n \<lsq> N\<rs>\<one>"  
	  using PositiveSet_def Int_ZF_1_3_L6A by simp
	with A4 have "n \<in> \<one>..(N\<rs>\<one>)"
	  using Int_ZF_1_5_L3 Interval_def by auto
	with A1 I T have "f`(n)\<ra>?C \<lsq> maxf(f,\<one>..(N\<rs>\<one>)) \<ra> ?C"
	  using Int_ZF_1_4_L2 int_ord_transl_inv by simp
	with T have "f`(n)\<ra>?C \<lsq> K\<rs>\<one>"
	  using Int_ZF_1_2_L3 by simp
	with A5 have "K \<lsq>  K\<rs>\<one>"
	  by (rule Int_order_transitive)
	with A2 have False using Int_ZF_1_2_L3AA by simp
      } then have "K \<lsq> f`(n) \<ra> ?C \<longrightarrow> N\<lsq>n"
	by auto 
    } then have "\<forall>n\<in>\<int>\<^sub>+. K \<lsq> f`(n) \<ra> ?C \<longrightarrow> N\<lsq>n"
      by simp
    ultimately have "\<exists>C\<in>\<int>. \<forall>n\<in>\<int>\<^sub>+. K \<lsq> f`(n) \<ra> C \<longrightarrow> N\<lsq>n" 
      by auto } 
  ultimately show ?thesis by auto
qed

text\<open>Absolute value is identity on positive integers.\<close>

lemma (in int0) Int_ZF_1_5_L4A: 
  assumes "a\<in>\<int>\<^sub>+" shows "abs(a) = a"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_3_L2B
  by simp

text\<open>One and two are in \<open>\<int>\<^sub>+\<close>.\<close>

lemma (in int0) int_one_two_are_pos: shows "\<one> \<in> \<int>\<^sub>+"  "\<two> \<in> \<int>\<^sub>+"
  using int_zero_one_are_int int_ord_is_refl refl_def Int_ZF_1_5_L3
  Int_ZF_2_L16B by auto

text\<open>The image of \<open>\<int>\<^sub>+\<close> by a function defined on integers 
  is not empty.\<close>

lemma (in int0) Int_ZF_1_5_L5: assumes A1: "f : \<int>\<rightarrow>X"
  shows "f``(\<int>\<^sub>+) \<noteq> 0"
proof -
  have "\<int>\<^sub>+ \<subseteq> \<int>" using PositiveSet_def by auto
  with A1 show "f``(\<int>\<^sub>+) \<noteq> 0"
    using int_one_two_are_pos func_imagedef by auto
qed

text\<open>If $n$ is positive, then $n-1$ is nonnegative.\<close>

lemma (in int0) Int_ZF_1_5_L6: assumes A1: "n \<in> \<int>\<^sub>+"
  shows 
  "\<zero> \<lsq> n\<rs>\<one>"
  "\<zero> \<in> \<zero>..(n\<rs>\<one>)"
  "\<zero>..(n\<rs>\<one>) \<subseteq> \<int>"
proof -
  from A1 have "\<one> \<lsq> n"  "(\<rm>\<one>) \<in> \<int>"
    using Int_ZF_1_5_L3 int_zero_one_are_int Int_ZF_1_1_L4 
    by auto
  then have "\<one>\<rs>\<one> \<lsq> n\<rs>\<one>"
    using int_ord_transl_inv by simp
  then show "\<zero> \<lsq> n\<rs>\<one>"
    using int_zero_one_are_int Int_ZF_1_1_L4 by simp
  then show "\<zero> \<in> \<zero>..(n\<rs>\<one>)"
    using int_zero_one_are_int int_ord_is_refl refl_def Order_ZF_2_L1B
    by simp
  show "\<zero>..(n\<rs>\<one>) \<subseteq> \<int>"
    using Int_ZF_2_L1B Order_ZF_2_L6 by simp
qed

text\<open>Intgers greater than one in \<open>\<int>\<^sub>+\<close> belong to \<open>\<int>\<^sub>+\<close>.
  This is a property of ordered groups and follows from 
  \<open>OrderedGroup_ZF_1_L19\<close>, but Isabelle's simplifier has problems 
  using that result directly, so we reprove it specifically for integers.\<close>

lemma (in int0) Int_ZF_1_5_L7:  assumes "a \<in> \<int>\<^sub>+" and "a\<lsq>b"
  shows "b \<in> \<int>\<^sub>+"
proof-
  from assms have "\<one>\<lsq>a"  "a\<lsq>b"
    using Int_ZF_1_5_L3 by auto
  then have "\<one>\<lsq>b" by (rule Int_order_transitive)
  then show "b \<in> \<int>\<^sub>+" using Int_ZF_1_5_L3 by simp
qed

text\<open>Adding a positive integer increases integers.\<close>

lemma (in int0) Int_ZF_1_5_L7A: assumes "a\<in>\<int>"  "b \<in> \<int>\<^sub>+"
  shows "a \<lsq> a\<ra>b"  "a \<noteq> a\<ra>b"  "a\<ra>b \<in> \<int>"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L22
  by auto

text\<open>For any integer $m$ the greater of $m$ and $1$ is a positive
  integer that is greater or equal than $m$. If we add $1$ to it we
  get a positive integer that is strictly greater than $m$.\<close>

lemma (in int0) Int_ZF_1_5_L7B: assumes "a\<in>\<int>"
  shows 
  "a \<lsq> GreaterOf(IntegerOrder,\<one>,a)"
  "GreaterOf(IntegerOrder,\<one>,a) \<in> \<int>\<^sub>+"
  "GreaterOf(IntegerOrder,\<one>,a) \<ra> \<one> \<in> \<int>\<^sub>+"
  "a \<lsq> GreaterOf(IntegerOrder,\<one>,a) \<ra> \<one>"  
  "a \<noteq> GreaterOf(IntegerOrder,\<one>,a) \<ra> \<one>"
  using assms int_zero_not_one Int_ZF_1_3_T1 ring1.OrdRing_ZF_3_L12
  by auto


(*text{*Adding one increases integers - one more version useful
  for some proofs by contradiction.*}

lemma (in int0) Int_ZF_1_5_L7B: assumes A1: "a\<in>\<int>"
  shows 
  "\<not>(a\<ra>\<one> \<lsq>a)"
  "\<not>(\<one>\<ra>a \<lsq>a)"
proof -
  { assume A2: "a\<ra>\<one> \<lsq>a"
    moreover from A1 have "a \<lsq> a\<ra>\<one>"
      using Int_ZF_2_L12B by simp
    ultimately have "a\<ra>\<one> = a" by (rule Int_ZF_2_L3) done somewhere else*)  
text\<open>The opposite of an element of \<open>\<int>\<^sub>+\<close> cannot belong to
  \<open>\<int>\<^sub>+\<close>.\<close>

lemma (in int0) Int_ZF_1_5_L8: assumes "a \<in> \<int>\<^sub>+"
  shows "(\<rm>a) \<notin> \<int>\<^sub>+"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L20
  by simp

text\<open>For every integer there is one in \<open>\<int>\<^sub>+\<close> that is greater or 
  equal.\<close>

lemma (in int0) Int_ZF_1_5_L9: assumes "a\<in>\<int>"
  shows "\<exists>b\<in>\<int>\<^sub>+. a\<lsq>b"
  using assms int_not_trivial Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L23
  by simp

text\<open>A theorem about odd extensions. Recall from \<open>OrdereGroup_ZF.thy\<close>
  that the odd extension of an integer function $f$ defined on \<open>\<int>\<^sub>+\<close> 
  is the odd function on \<open>\<int>\<close> equal to $f$ on \<open>\<int>\<^sub>+\<close>. 
  First we show that the odd extension is defined on \<open>\<int>\<close>.\<close>

lemma (in int0) Int_ZF_1_5_L10: assumes "f : \<int>\<^sub>+\<rightarrow>\<int>"
  shows "OddExtension(\<int>,IntegerAddition,IntegerOrder,f) : \<int>\<rightarrow>\<int>"
  using assms Int_ZF_2_T1 group3.odd_ext_props by simp

text\<open>On \<open>\<int>\<^sub>+\<close>, the odd extension of $f$ is the same as $f$.\<close>

lemma (in int0) Int_ZF_1_5_L11: assumes "f : \<int>\<^sub>+\<rightarrow>\<int>" and "a \<in> \<int>\<^sub>+" and
  "g = OddExtension(\<int>,IntegerAddition,IntegerOrder,f)"
  shows "g`(a) = f`(a)"
  using assms Int_ZF_2_T1 group3.odd_ext_props by simp

text\<open>On \<open>\<sm>\<int>\<^sub>+\<close>, the value of the odd extension of $f$ 
  is the negative of $f(-a)$.\<close>

lemma (in int0) Int_ZF_1_5_L12:  
  assumes "f : \<int>\<^sub>+\<rightarrow>\<int>" and "a \<in> (\<sm>\<int>\<^sub>+)" and
  "g = OddExtension(\<int>,IntegerAddition,IntegerOrder,f)"
  shows "g`(a) = \<rm>(f`(\<rm>a))"
  using assms Int_ZF_2_T1 group3.odd_ext_props by simp

text\<open>Odd extensions are odd on \<open>\<int>\<close>.\<close>

lemma (in int0) int_oddext_is_odd:
  assumes "f : \<int>\<^sub>+\<rightarrow>\<int>" and "a\<in>\<int>" and
  "g = OddExtension(\<int>,IntegerAddition,IntegerOrder,f)"
  shows "g`(\<rm>a) = \<rm>(g`(a))"
  using assms Int_ZF_2_T1 group3.oddext_is_odd by simp


text\<open>Alternative definition of an odd function.\<close>

lemma (in int0) Int_ZF_1_5_L13:  assumes A1: "f: \<int>\<rightarrow>\<int>" shows 
  "(\<forall>a\<in>\<int>. f`(\<rm>a) = (\<rm>f`(a))) \<longleftrightarrow> (\<forall>a\<in>\<int>. (\<rm>(f`(\<rm>a))) = f`(a))"
  using assms Int_ZF_1_T2 group0.group0_6_L2 by simp

text\<open>Another way of expressing the fact that odd extensions are odd.\<close>

lemma (in int0) int_oddext_is_odd_alt:
  assumes "f : \<int>\<^sub>+\<rightarrow>\<int>" and "a\<in>\<int>" and
  "g = OddExtension(\<int>,IntegerAddition,IntegerOrder,f)"
  shows "(\<rm>g`(\<rm>a)) = g`(a)"
  using assms Int_ZF_2_T1 group3.oddext_is_odd_alt by simp

subsection\<open>Functions with infinite limits\<close>

text\<open>In this section we consider functions (integer sequences) that have
  infinite limits. An integer function has infinite positive limit if it 
  is arbitrarily
  large for large enough arguments. Similarly, a function has infinite negative limit 
  if it is arbitrarily small for small enough arguments. 
  The material in this 
  come mostly from the section in \<open>OrderedGroup_ZF.thy\<close> 
  with he same title.
  Here we rewrite the theorems from that section in the notation 
  we use for integers and
  add some results specific for the ordered group of integers.\<close>

text\<open>If an image of a set by a function with infinite positive limit 
  is bounded above, then the set itself is bounded above.\<close>

lemma (in int0) Int_ZF_1_6_L1: assumes "f: \<int>\<rightarrow>\<int>" and
  "\<forall>a\<in>\<int>.\<exists>b\<in>\<int>\<^sub>+.\<forall>x. b\<lsq>x \<longrightarrow> a \<lsq> f`(x)" and "A \<subseteq> \<int>" and
  "IsBoundedAbove(f``(A),IntegerOrder)"
  shows "IsBoundedAbove(A,IntegerOrder)"
  using assms int_not_trivial Int_ZF_2_T1 group3.OrderedGroup_ZF_7_L1
  by simp

text\<open>If an image of a set defined by separation 
  by a function with infinite positive limit 
  is bounded above, then the set itself is bounded above.\<close>

lemma (in int0) Int_ZF_1_6_L2: assumes A1: "X\<noteq>0" and A2: "f: \<int>\<rightarrow>\<int>" and 
  A3: "\<forall>a\<in>\<int>.\<exists>b\<in>\<int>\<^sub>+.\<forall>x. b\<lsq>x \<longrightarrow> a \<lsq> f`(x)" and
  A4: "\<forall>x\<in>X. b(x) \<in> \<int>  \<and> f`(b(x)) \<lsq> U"
  shows "\<exists>u.\<forall>x\<in>X. b(x) \<lsq> u"
proof -
  let ?G = "\<int>"
  let ?P = "IntegerAddition"
  let ?r = "IntegerOrder"
  from A1 A2 A3 A4 have 
    "group3(?G, ?P, ?r)" 
    "?r {is total on} ?G" 
    "?G \<noteq> {TheNeutralElement(?G, ?P)}"
    "X\<noteq>0"  "f: ?G\<rightarrow>?G"
    "\<forall>a\<in>?G. \<exists>b\<in>PositiveSet(?G, ?P, ?r). \<forall>y. \<langle>b, y\<rangle> \<in> ?r \<longrightarrow> \<langle>a, f`(y)\<rangle> \<in> ?r"
    "\<forall>x\<in>X. b(x) \<in> ?G \<and> \<langle>f`(b(x)), U\<rangle> \<in> ?r"
    using int_not_trivial Int_ZF_2_T1 by auto
  then have "\<exists>u. \<forall>x\<in>X. \<langle>b(x), u\<rangle> \<in> ?r" by (rule group3.OrderedGroup_ZF_7_L2)
  thus ?thesis by simp
qed

text\<open>If an image of a set defined by separation 
  by a integer function with infinite negative limit 
  is bounded below, then the set itself is bounded above.
  This is dual to \<open> Int_ZF_1_6_L2\<close>.\<close>

lemma (in int0) Int_ZF_1_6_L3: assumes A1: "X\<noteq>0" and A2: "f: \<int>\<rightarrow>\<int>" and 
  A3: "\<forall>a\<in>\<int>.\<exists>b\<in>\<int>\<^sub>+.\<forall>y. b\<lsq>y \<longrightarrow> f`(\<rm>y) \<lsq> a" and
  A4: "\<forall>x\<in>X. b(x) \<in> \<int>  \<and> L \<lsq> f`(b(x))"
  shows "\<exists>l.\<forall>x\<in>X. l \<lsq> b(x)"
proof -
  let ?G = "\<int>"
  let ?P = "IntegerAddition"
  let ?r = "IntegerOrder"
  from A1 A2 A3 A4 have 
    "group3(?G, ?P, ?r)" 
    "?r {is total on} ?G" 
    "?G \<noteq> {TheNeutralElement(?G, ?P)}"
    "X\<noteq>0"  "f: ?G\<rightarrow>?G"
    "\<forall>a\<in>?G. \<exists>b\<in>PositiveSet(?G, ?P, ?r). \<forall>y. 
    \<langle>b, y\<rangle> \<in> ?r \<longrightarrow> \<langle>f`(GroupInv(?G, ?P)`(y)),a\<rangle> \<in> ?r"
    "\<forall>x\<in>X. b(x) \<in> ?G \<and> \<langle>L,f`(b(x))\<rangle> \<in> ?r"
    using int_not_trivial Int_ZF_2_T1 by auto
  then have "\<exists>l. \<forall>x\<in>X. \<langle>l, b(x)\<rangle> \<in> ?r" by (rule group3.OrderedGroup_ZF_7_L3)
  thus ?thesis by simp
qed

text\<open>The next lemma combines \<open>Int_ZF_1_6_L2\<close> and 
  \<open>Int_ZF_1_6_L3\<close> to show that if the image of a set 
  defined by separation by a function with infinite limits is bounded,
  then the set itself is bounded. The proof again uses directly a fact from
  \<open>OrderedGroup_ZF\<close>.\<close>

lemma (in int0) Int_ZF_1_6_L4:
  assumes A1: "X\<noteq>0" and A2: "f: \<int>\<rightarrow>\<int>" and 
  A3: "\<forall>a\<in>\<int>.\<exists>b\<in>\<int>\<^sub>+.\<forall>x. b\<lsq>x \<longrightarrow> a \<lsq> f`(x)" and
  A4: "\<forall>a\<in>\<int>.\<exists>b\<in>\<int>\<^sub>+.\<forall>y. b\<lsq>y \<longrightarrow> f`(\<rm>y) \<lsq> a" and
  A5: "\<forall>x\<in>X. b(x) \<in> \<int> \<and> f`(b(x)) \<lsq> U \<and> L \<lsq> f`(b(x))"
  shows "\<exists>M.\<forall>x\<in>X. abs(b(x)) \<lsq> M"
proof -
  let ?G = "\<int>"
  let ?P = "IntegerAddition"
  let ?r = "IntegerOrder"
  from A1 A2 A3 A4 A5 have
    "group3(?G, ?P, ?r)" 
    "?r {is total on} ?G" 
    "?G \<noteq> {TheNeutralElement(?G, ?P)}"
    "X\<noteq>0"  "f: ?G\<rightarrow>?G"
    "\<forall>a\<in>?G. \<exists>b\<in>PositiveSet(?G, ?P, ?r). \<forall>y. \<langle>b, y\<rangle> \<in> ?r \<longrightarrow> \<langle>a, f`(y)\<rangle> \<in> ?r"
    "\<forall>a\<in>?G. \<exists>b\<in>PositiveSet(?G, ?P, ?r). \<forall>y. 
    \<langle>b, y\<rangle> \<in> ?r \<longrightarrow> \<langle>f`(GroupInv(?G, ?P)`(y)),a\<rangle> \<in> ?r"
    "\<forall>x\<in>X. b(x) \<in> ?G \<and> \<langle>L,f`(b(x))\<rangle> \<in> ?r \<and> \<langle>f`(b(x)), U\<rangle> \<in> ?r"
    using int_not_trivial Int_ZF_2_T1 by auto
  then have "\<exists>M. \<forall>x\<in>X. \<langle>AbsoluteValue(?G, ?P, ?r) ` b(x), M\<rangle> \<in> ?r"
    by (rule group3.OrderedGroup_ZF_7_L4)
  thus ?thesis by simp
qed

text\<open>If a function is larger than some constant for arguments large
  enough, then the image of a set that is bounded below is bounded below.
  This is not true for ordered groups in general, but only for those for which
  bounded sets are finite.
  This does not require the function to have infinite limit, but such 
  functions do have this property.\<close>

lemma (in int0) Int_ZF_1_6_L5:
  assumes A1: "f: \<int>\<rightarrow>\<int>" and A2: "N\<in>\<int>" and
  A3: "\<forall>m. N\<lsq>m \<longrightarrow> L \<lsq> f`(m)" and 
  A4: "IsBoundedBelow(A,IntegerOrder)"
  shows "IsBoundedBelow(f``(A),IntegerOrder)"
proof -
  from A2 A4 have "A = {x\<in>A. x\<lsq>N} \<union> {x\<in>A. N\<lsq>x}"
    using Int_ZF_2_T1 Int_ZF_2_L1C Order_ZF_1_L5 
    by simp
  moreover have 
    "f``({x\<in>A. x\<lsq>N} \<union> {x\<in>A. N\<lsq>x}) =
    f``{x\<in>A. x\<lsq>N} \<union> f``{x\<in>A. N\<lsq>x}"
    by (rule image_Un)
  ultimately have "f``(A) = f``{x\<in>A. x\<lsq>N} \<union> f``{x\<in>A. N\<lsq>x}"
    by simp
  moreover have "IsBoundedBelow(f``{x\<in>A. x\<lsq>N},IntegerOrder)"
  proof -
    let ?B = "{x\<in>A. x\<lsq>N}"
    from A4 have "?B \<in> Fin(\<int>)"
      using Order_ZF_3_L16 Int_bounded_iff_fin by auto
    with A1 have  "IsBounded(f``(?B),IntegerOrder)"
      using Finite1_L6A Int_bounded_iff_fin by simp
    then show "IsBoundedBelow(f``(?B),IntegerOrder)"
      using IsBounded_def by simp
  qed
  moreover have "IsBoundedBelow(f``{x\<in>A. N\<lsq>x},IntegerOrder)"
  proof -
    let ?C = "{x\<in>A. N\<lsq>x}"
    from A4 have "?C \<subseteq> \<int>" using Int_ZF_2_L1C by auto
    with A1 A3 have "\<forall>y \<in> f``(?C). \<langle>L,y\<rangle> \<in> IntegerOrder"
      using func_imagedef by simp
    then show "IsBoundedBelow(f``(?C),IntegerOrder)"
      by (rule Order_ZF_3_L9)
  qed
  ultimately show "IsBoundedBelow(f``(A),IntegerOrder)"
    using Int_ZF_2_T1 Int_ZF_2_L6 Int_ZF_2_L1B Order_ZF_3_L6
    by simp
qed

text\<open>A function that has an infinite limit can be made arbitrarily large
  on positive integers by adding a constant. This does not actually require
  the function to have infinite limit, just to be larger than a constant
  for arguments large enough.\<close>

lemma (in int0) Int_ZF_1_6_L6: assumes A1: "N\<in>\<int>" and
  A2: "\<forall>m. N\<lsq>m \<longrightarrow> L \<lsq> f`(m)" and
  A3: "f: \<int>\<rightarrow>\<int>" and A4: "K\<in>\<int>"
  shows "\<exists>c\<in>\<int>. \<forall>n\<in>\<int>\<^sub>+. K \<lsq> f`(n)\<ra>c"
proof -
  have "IsBoundedBelow(\<int>\<^sub>+,IntegerOrder)"
    using Int_ZF_1_5_L1 by simp
  with A3 A1 A2 have "IsBoundedBelow(f``(\<int>\<^sub>+),IntegerOrder)"
    by (rule Int_ZF_1_6_L5)
  with A1 obtain l where I: "\<forall>y\<in>f``(\<int>\<^sub>+). l \<lsq> y"
    using Int_ZF_1_5_L5 IsBoundedBelow_def by auto
  let ?c = "K\<rs>l"
  from A3 have "f``(\<int>\<^sub>+) \<noteq> 0" using Int_ZF_1_5_L5
    by simp
  then have "\<exists>y. y \<in> f``(\<int>\<^sub>+)" by (rule nonempty_has_element)
  then obtain y where "y \<in> f``(\<int>\<^sub>+)" by auto
  with A4 I have T: "l \<in> \<int>"  "?c \<in> \<int>"
    using Int_ZF_2_L1A Int_ZF_1_1_L5 by auto
  { fix n assume A5: "n\<in>\<int>\<^sub>+"
    have "\<int>\<^sub>+ \<subseteq> \<int>" using PositiveSet_def by auto
    with A3 I T A5 have "l \<ra> ?c \<lsq> f`(n) \<ra> ?c"
      using func_imagedef int_ord_transl_inv by auto
     with I T have "l \<ra> ?c \<lsq> f`(n) \<ra> ?c"
      using int_ord_transl_inv by simp
    with A4 T have "K \<lsq>  f`(n) \<ra> ?c"
      using Int_ZF_1_2_L3 by simp
  } then have "\<forall>n\<in>\<int>\<^sub>+. K \<lsq>  f`(n) \<ra> ?c" by simp
  with T show ?thesis by auto
qed

text\<open>If a function has infinite limit, then we can add such constant
  such that minimum of those arguments for which the function (plus the constant) 
  is larger than another given constant is greater than a third constant.
  It is not as complicated as it sounds.\<close>

lemma (in int0) Int_ZF_1_6_L7: 
  assumes A1: "f: \<int>\<rightarrow>\<int>" and A2: "K\<in>\<int>"  "N\<in>\<int>" and
  A3: "\<forall>a\<in>\<int>.\<exists>b\<in>\<int>\<^sub>+.\<forall>x. b\<lsq>x \<longrightarrow> a \<lsq> f`(x)"
  shows "\<exists>C\<in>\<int>. N \<lsq> Minimum(IntegerOrder,{n\<in>\<int>\<^sub>+. K \<lsq> f`(n)\<ra>C})"
proof -
  from A1 A2 have "\<exists>C\<in>\<int>. \<forall>n\<in>\<int>\<^sub>+. K \<lsq> f`(n) \<ra> C \<longrightarrow> N\<lsq>n"
    using Int_ZF_1_5_L4 by simp
  then obtain C where I: "C\<in>\<int>" and
    II: "\<forall>n\<in>\<int>\<^sub>+. K \<lsq> f`(n) \<ra> C \<longrightarrow> N\<lsq>n"
    by auto
  have "antisym(IntegerOrder)" using Int_ZF_2_L4 by simp
  moreover have "HasAminimum(IntegerOrder,{n\<in>\<int>\<^sub>+. K \<lsq> f`(n)\<ra>C})"
  proof -
    from A2 A3 I have "\<exists>n\<in>\<int>\<^sub>+.\<forall>x. n\<lsq>x \<longrightarrow> K\<rs>C \<lsq> f`(x)"
      using Int_ZF_1_1_L5 by simp
    then obtain n where 
      "n\<in>\<int>\<^sub>+" and "\<forall>x. n\<lsq>x \<longrightarrow> K\<rs>C \<lsq>  f`(x)"
      by auto
    with A2 I have 
      "{n\<in>\<int>\<^sub>+. K \<lsq> f`(n)\<ra>C} \<noteq> 0"
      "{n\<in>\<int>\<^sub>+. K \<lsq> f`(n)\<ra>C} \<subseteq> \<int>\<^sub>+"
      using int_ord_is_refl refl_def PositiveSet_def Int_ZF_2_L9C
      by auto
    then show "HasAminimum(IntegerOrder,{n\<in>\<int>\<^sub>+. K \<lsq> f`(n)\<ra>C})"
      using Int_ZF_1_5_L1C by simp
  qed
  moreover from II have 
    "\<forall>n \<in> {n\<in>\<int>\<^sub>+. K \<lsq> f`(n)\<ra>C}. \<langle>N,n\<rangle> \<in> IntegerOrder" 
    by auto (* we can not put ?A here *)
  ultimately have 
    "\<langle>N,Minimum(IntegerOrder,{n\<in>\<int>\<^sub>+. K \<lsq> f`(n)\<ra>C})\<rangle> \<in> IntegerOrder"
    by (rule Order_ZF_4_L12)
  with I show ?thesis by auto
qed

text\<open>For any integer $m$ the function $k\mapsto m\cdot k$ has an infinite limit
  (or negative of that). This is why we put some properties of these functions 
  here, even though they properly belong to a (yet nonexistent) section on 
  homomorphisms. The next lemma shows that the set $\{a\cdot x: x\in Z\}$
  can finite only if $a=0$.\<close>

lemma (in int0) Int_ZF_1_6_L8: 
  assumes A1: "a\<in>\<int>" and A2: "{a\<cdot>x. x\<in>\<int>} \<in> Fin(\<int>)"
  shows "a = \<zero>"
proof -
  from A1 have "a=\<zero> \<or> (a \<lsq> \<rm>\<one>) \<or> (\<one>\<lsq>a)"
    using Int_ZF_1_3_L6C by simp
  moreover
  { assume "a \<lsq> \<rm>\<one>"
    then have "{a\<cdot>x. x\<in>\<int>} \<notin> Fin(\<int>)"
      using int_zero_not_one Int_ZF_1_3_T1 ring1.OrdRing_ZF_3_L6
      by simp
    with A2 have False by simp }
  moreover
  { assume "\<one>\<lsq>a" 
    then have "{a\<cdot>x. x\<in>\<int>} \<notin> Fin(\<int>)"
      using int_zero_not_one Int_ZF_1_3_T1 ring1.OrdRing_ZF_3_L5
    by simp 
  with A2 have False by simp }
  ultimately show  "a = \<zero>" by auto
qed
    
subsection\<open>Miscelaneous\<close>

text\<open>In this section we put some technical lemmas needed in various other 
  places that are hard to classify.\<close>

text\<open>Suppose we have an integer expression (a meta-function)$F$ such that 
  $F(p)|p|$ is bounded by a linear function of $|p|$, that is for some integers
  $A,B$ we have $F(p)|p|\leq A|p|+B.$ We show that $F$ is then bounded. 
  The proof is easy, we just divide both sides by $|p|$ 
  and take the limit (just kidding).\<close>

lemma (in int0) Int_ZF_1_7_L1:
  assumes A1: "\<forall>q\<in>\<int>. F(q) \<in> \<int>" and 
  A2:  "\<forall>q\<in>\<int>. F(q)\<cdot>abs(q) \<lsq> A\<cdot>abs(q) \<ra> B" and 
  A3: "A\<in>\<int>"  "B\<in>\<int>"
  shows "\<exists>L. \<forall>p\<in>\<int>. F(p) \<lsq> L"
proof -
  let ?I = "(\<rm>abs(B))..abs(B)"
  let ?K = "{F(q). q \<in> ?I}"
  let ?M = "Maximum(IntegerOrder,?K)"
  let ?L = "GreaterOf(IntegerOrder,?M,A\<ra>\<one>)"
  from A3 A1 have C1:
    "IsBounded(?I,IntegerOrder)"   
    "?I \<noteq> 0"
    "\<forall>q\<in>\<int>. F(q) \<in> \<int>"
    "?K = {F(q). q \<in> ?I}"
    using Order_ZF_3_L11 Int_ZF_1_3_L17 by auto
  then have "?M \<in> \<int>" by (rule Int_ZF_1_4_L1)
  with A3 have T1: "?M \<lsq> ?L"  "A\<ra>\<one> \<lsq> ?L"
    using int_zero_one_are_int Int_ZF_1_1_L5 Int_ZF_1_3_L18
    by auto
  from C1 have T2: "\<forall>q\<in>?I. F(q) \<lsq> ?M"
    by (rule Int_ZF_1_4_L1)
  { fix p assume A4: "p\<in>\<int>" have "F(p) \<lsq> ?L" 
    proof -
      { assume "abs(p) \<lsq> abs(B)"
	with A4 T1 T2 have "F(p) \<lsq> ?M"  "?M \<lsq> ?L"
	  using Int_ZF_1_3_L19 by auto
	then have "F(p) \<lsq> ?L" by (rule Int_order_transitive) }
      moreover
      { assume A5: "\<not>(abs(p) \<lsq> abs(B))"
	from A3 A2 A4 have 
	  "A\<cdot>abs(p) \<in> \<int>"  "F(p)\<cdot>abs(p) \<lsq> A\<cdot>abs(p) \<ra> B"
	  using Int_ZF_2_L14 Int_ZF_1_1_L5 by auto
	moreover from A3 A4 A5 have "B \<lsq> abs(p)"
	  using Int_ZF_1_3_L15 by simp
	ultimately have
	  "F(p)\<cdot>abs(p) \<lsq> A\<cdot>abs(p) \<ra> abs(p)"
	  using Int_ZF_2_L15A by blast
	with A3 A4 have "F(p)\<cdot>abs(p) \<lsq> (A\<ra>\<one>)\<cdot>abs(p)"
	  using Int_ZF_2_L14 Int_ZF_1_2_L7 by simp
	moreover from A3 A1 A4 A5 have 
	  "F(p) \<in> \<int>"  "A\<ra>\<one> \<in> \<int>"  "abs(p) \<in> \<int>"
	  "\<not>(abs(p) \<lsq> \<zero>)"
	  using int_zero_one_are_int Int_ZF_1_1_L5 Int_ZF_2_L14 Int_ZF_1_3_L11
	  by auto
	ultimately have "F(p) \<lsq> A\<ra>\<one>"
	  using Int_ineq_simpl_positive by simp
	moreover from T1 have  "A\<ra>\<one> \<lsq> ?L" by simp
	ultimately have "F(p) \<lsq> ?L" by (rule Int_order_transitive) }
      ultimately show ?thesis by blast
    qed
  } then have "\<forall>p\<in>\<int>. F(p) \<lsq> ?L" by simp
  thus ?thesis by auto
qed

text\<open>A lemma about splitting (not really, there is some overlap) 
  the \<open>\<int>\<times>\<int>\<close> into six subsets (cases). The subsets are as follows:
  first and third qaudrant, and second and fourth quadrant farther split
  by the $b =-a$ line.\<close>

lemma (in int0) int_plane_split_in6: assumes "a\<in>\<int>"  "b\<in>\<int>"
  shows
  "\<zero>\<lsq>a \<and> \<zero>\<lsq>b  \<or>  a\<lsq>\<zero> \<and> b\<lsq>\<zero>  \<or>  
  a\<lsq>\<zero> \<and> \<zero>\<lsq>b \<and> \<zero> \<lsq> a\<ra>b  \<or> a\<lsq>\<zero> \<and> \<zero>\<lsq>b \<and> a\<ra>b \<lsq> \<zero>  \<or>  
  \<zero>\<lsq>a \<and> b\<lsq>\<zero> \<and> \<zero> \<lsq> a\<ra>b  \<or>  \<zero>\<lsq>a \<and> b\<lsq>\<zero> \<and> a\<ra>b \<lsq> \<zero>"
  using assms Int_ZF_2_T1 group3.OrdGroup_6cases by simp

end
