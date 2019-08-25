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
WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES 
OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. 
IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, 
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, 
PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; 
OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, 
WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) 
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, 
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

section \<open>More on rings\<close>

theory Ring_ZF_1 imports Ring_ZF Group_ZF_3

begin

text\<open>This theory is devoted to the part of ring theory specific the 
  construction of real numbers in the \<open>Real_ZF_x\<close> series of theories. 
  The goal is to 
  show that classes of almost homomorphisms form a ring.\<close>

subsection\<open>The ring of classes of almost homomorphisms\<close>

text\<open>Almost homomorphisms do not form a ring as the regular homomorphisms 
  do because the lifted group operation is not distributive with respect to 
  composition -- we have $s\circ (r\cdot q) \neq s\circ r\cdot s\circ q$ in 
  general. However, we do have 
  $s\circ (r\cdot q) \approx s\circ r\cdot s\circ q$ in the sense of the 
  equivalence relation defined by the group of finite range
  functions (that is a normal subgroup of almost homomorphisms, 
  if the group is abelian). This allows to define a natural ring structure 
  on the classes of almost homomorphisms.\<close>

text\<open>The next lemma provides a formula useful for proving that two sides 
  of the distributive law equation for almost homomorphisms are almost 
  equal.\<close>

lemma (in group1) Ring_ZF_1_1_L1: 
  assumes A1: "s\<in>AH" "r\<in>AH" "q\<in>AH" and A2: "n\<in>G"
  shows 
  "((s\<circ>(r\<bullet>q))`(n))\<cdot>(((s\<circ>r)\<bullet>(s\<circ>q))`(n))\<inverse>= \<delta>(s,\<langle> r`(n),q`(n)\<rangle>)"
  "((r\<bullet>q)\<circ>s)`(n) = ((r\<circ>s)\<bullet>(q\<circ>s))`(n)"
proof -
  from groupAssum isAbelian A1 have T1:
    "r\<bullet>q \<in> AH" "s\<circ>r \<in> AH"  "s\<circ>q \<in> AH" "(s\<circ>r)\<bullet>(s\<circ>q) \<in> AH"
    "r\<circ>s \<in> AH" "q\<circ>s \<in> AH"  "(r\<circ>s)\<bullet>(q\<circ>s) \<in> AH"
    using Group_ZF_3_2_L15 Group_ZF_3_4_T1 by auto
  from A1 A2 have T2: "r`(n) \<in> G" "q`(n) \<in> G" "s`(n) \<in> G"
    "s`(r`(n)) \<in> G" "s`(q`(n)) \<in> G" "\<delta>(s,\<langle> r`(n),q`(n)\<rangle>) \<in> G"
    "s`(r`(n))\<cdot>s`(q`(n)) \<in> G" "r`(s`(n)) \<in> G" "q`(s`(n)) \<in> G"
    "r`(s`(n))\<cdot>q`(s`(n)) \<in> G"
    using AlmostHoms_def apply_funtype Group_ZF_3_2_L4B 
    group0_2_L1 monoid0.group0_1_L1 by auto
  with T1 A1 A2 isAbelian show  
    "((s\<circ>(r\<bullet>q))`(n))\<cdot>(((s\<circ>r)\<bullet>(s\<circ>q))`(n))\<inverse>= \<delta>(s,\<langle> r`(n),q`(n)\<rangle>)"
    "((r\<bullet>q)\<circ>s)`(n) = ((r\<circ>s)\<bullet>(q\<circ>s))`(n)"
    using Group_ZF_3_2_L12 Group_ZF_3_4_L2 Group_ZF_3_4_L1 group0_4_L6A
    by auto  
qed

text\<open>The sides of the distributive law equations for almost homomorphisms 
  are almost equal.\<close>

lemma (in group1) Ring_ZF_1_1_L2:
  assumes A1: "s\<in>AH" "r\<in>AH" "q\<in>AH"
  shows 
  "s\<circ>(r\<bullet>q) \<approx> (s\<circ>r)\<bullet>(s\<circ>q)" 
  "(r\<bullet>q)\<circ>s = (r\<circ>s)\<bullet>(q\<circ>s)"
proof -
  from A1 have "\<forall>n\<in>G. \<langle> r`(n),q`(n)\<rangle> \<in> G\<times>G"
    using AlmostHoms_def apply_funtype by auto
  moreover from A1 have "{\<delta>(s,x). x \<in> G\<times>G} \<in> Fin(G)"
    using AlmostHoms_def by simp
  ultimately have "{\<delta>(s,\<langle> r`(n),q`(n)\<rangle>). n\<in>G} \<in> Fin(G)"
    by (rule Finite1_L6B)
  with A1 have 
    "{((s\<circ>(r\<bullet>q))`(n))\<cdot>(((s\<circ>r)\<bullet>(s\<circ>q))`(n))\<inverse>. n \<in> G} \<in> Fin(G)"
    using Ring_ZF_1_1_L1 by simp
  moreover from groupAssum isAbelian A1 A1 have 
    "s\<circ>(r\<bullet>q) \<in> AH" "(s\<circ>r)\<bullet>(s\<circ>q) \<in> AH"
    using Group_ZF_3_2_L15 Group_ZF_3_4_T1 by auto
  ultimately show "s\<circ>(r\<bullet>q) \<approx> (s\<circ>r)\<bullet>(s\<circ>q)"
    using Group_ZF_3_4_L12 by simp
  from groupAssum isAbelian A1 have 
    "(r\<bullet>q)\<circ>s : G\<rightarrow>G" "(r\<circ>s)\<bullet>(q\<circ>s) : G\<rightarrow>G"
    using Group_ZF_3_2_L15 Group_ZF_3_4_T1 AlmostHoms_def
    by auto
  moreover from A1 have
    "\<forall>n\<in>G. ((r\<bullet>q)\<circ>s)`(n) = ((r\<circ>s)\<bullet>(q\<circ>s))`(n)"
    using Ring_ZF_1_1_L1 by simp
  ultimately show "(r\<bullet>q)\<circ>s = (r\<circ>s)\<bullet>(q\<circ>s)"
    using fun_extension_iff by simp
qed
    
text\<open>The essential condition to show the distributivity for the 
  operations defined on classes of almost homomorphisms.\<close>

lemma (in group1) Ring_ZF_1_1_L3: 
  assumes A1: "R = QuotientGroupRel(AH,Op1,FR)"
  and A2: "a \<in> AH//R" "b \<in> AH//R" "c \<in> AH//R"
  and A3: "A = ProjFun2(AH,R,Op1)" "M = ProjFun2(AH,R,Op2)"
  shows "M`\<langle>a,A`\<langle> b,c\<rangle>\<rangle> = A`\<langle>M`\<langle> a,b\<rangle>,M`\<langle> a,c\<rangle>\<rangle> \<and> 
  M`\<langle>A`\<langle> b,c\<rangle>,a\<rangle> = A`\<langle>M`\<langle> b,a\<rangle>,M`\<langle> c,a\<rangle>\<rangle>"
proof
  from A2 obtain s q r where D1: "s\<in>AH" "r\<in>AH" "q\<in>AH"
    "a = R``{s}" "b = R``{q}" "c = R``{r}"
    using quotient_def by auto
  from A1 have T1:"equiv(AH,R)"
      using Group_ZF_3_3_L3 by simp
  with A1 A3 D1 groupAssum isAbelian have 
    "M`\<langle>  a,A`\<langle> b,c\<rangle> \<rangle> = R``{s\<circ>(q\<bullet>r)}"
    using Group_ZF_3_3_L4 EquivClass_1_L10
    Group_ZF_3_2_L15 Group_ZF_3_4_L13A by simp
  also have "R``{s\<circ>(q\<bullet>r)} = R``{(s\<circ>q)\<bullet>(s\<circ>r)}"
  proof -
    from T1 D1 have "equiv(AH,R)" "s\<circ>(q\<bullet>r)\<approx>(s\<circ>q)\<bullet>(s\<circ>r)"
      using Ring_ZF_1_1_L2 by auto
    with A1 show ?thesis using equiv_class_eq by simp
  qed
  also from A1 T1 D1 A3 have 
    "R``{(s\<circ>q)\<bullet>(s\<circ>r)} = A`\<langle>M`\<langle> a,b\<rangle>,M`\<langle> a,c\<rangle>\<rangle>"
    using Group_ZF_3_3_L4 Group_ZF_3_4_T1 EquivClass_1_L10
    Group_ZF_3_3_L3 Group_ZF_3_4_L13A EquivClass_1_L10 Group_ZF_3_4_T1
    by simp
  finally show "M`\<langle>a,A`\<langle> b,c\<rangle>\<rangle> = A`\<langle>M`\<langle> a,b\<rangle>,M`\<langle> a,c\<rangle>\<rangle>" by simp 
  from A1 A3 T1 D1 groupAssum isAbelian show 
    "M`\<langle>A`\<langle> b,c\<rangle>,a\<rangle> = A`\<langle>M`\<langle> b,a\<rangle>,M`\<langle> c,a\<rangle>\<rangle>"
    using Group_ZF_3_3_L4 EquivClass_1_L10 Group_ZF_3_4_L13A 
      Group_ZF_3_2_L15 Ring_ZF_1_1_L2 Group_ZF_3_4_T1 by simp
qed

text\<open>The projection of the first group operation on almost homomorphisms
  is distributive with respect to the second group operation.\<close>

lemma (in group1) Ring_ZF_1_1_L4: 
  assumes A1: "R = QuotientGroupRel(AH,Op1,FR)"
  and A2: "A = ProjFun2(AH,R,Op1)" "M = ProjFun2(AH,R,Op2)"
  shows "IsDistributive(AH//R,A,M)"
proof -
  from A1 A2 have "\<forall>a\<in>(AH//R).\<forall>b\<in>(AH//R).\<forall>c\<in>(AH//R).
  M`\<langle>a,A`\<langle> b,c\<rangle>\<rangle> = A`\<langle>M`\<langle> a,b\<rangle>, M`\<langle> a,c\<rangle>\<rangle> \<and> 
  M`\<langle>A`\<langle> b,c\<rangle>, a\<rangle> = A`\<langle>M`\<langle> b,a\<rangle>,M`\<langle> c,a\<rangle>\<rangle>"
    using Ring_ZF_1_1_L3 by simp
  then show ?thesis using IsDistributive_def by simp
qed

text\<open>The classes of almost homomorphisms form a ring.\<close>

theorem (in group1) Ring_ZF_1_1_T1: 
  assumes "R = QuotientGroupRel(AH,Op1,FR)"
  and "A = ProjFun2(AH,R,Op1)" "M = ProjFun2(AH,R,Op2)"
  shows "IsAring(AH//R,A,M)"
  using assms QuotientGroupOp_def Group_ZF_3_3_T1 Group_ZF_3_4_T2 
    Ring_ZF_1_1_L4 IsAring_def by simp
  
end
   
   
   
  
 