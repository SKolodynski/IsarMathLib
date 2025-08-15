(*
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2005 - 2007  Slawomir Kolodynski

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

section \<open>Finite sets 1\<close>

theory Finite_ZF_1 imports Finite1 Order_ZF_1a

begin

text\<open>This theory is based on \<open>Finite1\<close> theory and is obsolete. It 
  contains properties of finite sets related to order 
  relations. See the \<open>FinOrd\<close> theory for a better approach.\<close>

subsection\<open>Finite vs. bounded sets\<close>

text\<open>The goal of this section is to show that finite sets are bounded and 
  have maxima and minima.\<close>

text\<open>Finite set has a maximum - induction step.\<close>

lemma Finite_ZF_1_1_L1: 
  assumes A1: "r {is total on} X" and A2: "trans(r)"
  and A3: "A\<in>Fin(X)" and A4: "x\<in>X" and A5: "A=0 \<or> HasAmaximum(r,A)"
  shows "A\<union>{x} = 0 \<or> HasAmaximum(r,A\<union>{x})"
proof -
  { assume "A=0" then have T1: "A\<union>{x} = {x}" by simp
    from A1 have "refl(X,r)" using total_is_refl by simp
    with T1 A4 have "A\<union>{x} = 0 \<or> HasAmaximum(r,A\<union>{x})" 
      using Order_ZF_4_L8 by simp }
  moreover 
  { assume "A\<noteq>0" 
    with A1 A2 A3 A4 A5 have "A\<union>{x} = 0 \<or> HasAmaximum(r,A\<union>{x})" 
      using FinD Order_ZF_4_L9 by simp }
  ultimately show ?thesis by blast
qed

text\<open>For total and transitive relations finite set has a maximum.\<close>

theorem Finite_ZF_1_1_T1A: 
  assumes A1: "r {is total on} X" and A2: "trans(r)"
  and A3: "B\<in>Fin(X)"
  shows "B=0 \<or> HasAmaximum(r,B)"
proof -
  have "0=0 \<or> HasAmaximum(r,0)" by simp
  moreover note A3
  moreover from A1 A2 have "\<forall>A\<in>Fin(X). \<forall>x\<in>X. 
    x\<notin>A \<and> (A=0 \<or> HasAmaximum(r,A)) \<longrightarrow> (A\<union>{x}=0 \<or> HasAmaximum(r,A\<union>{x}))"
    using Finite_ZF_1_1_L1 by simp
  ultimately show  "B=0 \<or> HasAmaximum(r,B)" by (rule Finite1_L16B)
qed

text\<open>Finite set has a minimum - induction step.\<close>

lemma Finite_ZF_1_1_L2: 
  assumes A1: "r {is total on} X" and A2: "trans(r)"
  and A3: "A\<in>Fin(X)" and A4: "x\<in>X" and A5: "A=0 \<or> HasAminimum(r,A)"
  shows "A\<union>{x} = 0 \<or> HasAminimum(r,A\<union>{x})"
proof -
  { assume "A=0" then have T1: "A\<union>{x} = {x}" by simp
    from A1 have "refl(X,r)" using total_is_refl by simp
    with T1 A4 have "A\<union>{x} = 0 \<or> HasAminimum(r,A\<union>{x})"  
      using Order_ZF_4_L8 by simp }
  moreover
  { assume "A\<noteq>0" 
    with A1 A2 A3 A4 A5 have "A\<union>{x} = 0 \<or> HasAminimum(r,A\<union>{x})" 
      using FinD Order_ZF_4_L10 by simp }
  ultimately show ?thesis by blast
qed

text\<open>For total and transitive relations finite set has a minimum.\<close>

theorem Finite_ZF_1_1_T1B: 
  assumes A1: "r {is total on} X" and A2: "trans(r)"
  and A3: "B \<in> Fin(X)"
  shows "B=0 \<or> HasAminimum(r,B)"
proof -
  have "0=0 \<or> HasAminimum(r,0)" by simp
  moreover note A3
  moreover from A1 A2 have "\<forall>A\<in>Fin(X). \<forall>x\<in>X. 
    x\<notin>A \<and> (A=0 \<or> HasAminimum(r,A)) \<longrightarrow> (A\<union>{x}=0 \<or> HasAminimum(r,A\<union>{x}))"
    using Finite_ZF_1_1_L2 by simp
  ultimately show  "B=0 \<or> HasAminimum(r,B)" by (rule Finite1_L16B)
qed

text\<open>For transitive and total relations finite sets are bounded.\<close>

theorem Finite_ZF_1_T1: 
  assumes A1: "r {is total on} X" and A2: "trans(r)"  
  and A3: "B\<in>Fin(X)"
  shows "IsBounded(B,r)"
proof -
  from A1 A2 A3 have "B=0 \<or> HasAminimum(r,B)" "B=0 \<or> HasAmaximum(r,B)"
    using Finite_ZF_1_1_T1A Finite_ZF_1_1_T1B by auto
  then have 
    "IsBoundedBelow(B,r)" and "IsBoundedAbove(B,r)"
    using Order_ZF_4_L7 Order_ZF_4_L8A empty_bounded_above_below 
    by auto
  then show "IsBounded(B,r)" unfolding IsBounded_def by simp
qed

text\<open>For linearly ordered finite sets maximum and minimum have desired 
  properties. The reason we need linear order is that we need the order
  to be total and transitive for the finite sets to have a maximum and minimum
  and then we also need antisymmetry for the maximum and minimum to be unique.
\<close>

theorem Finite_ZF_1_T2:
  assumes A1: "IsLinOrder(X,r)" and A2: "A \<in> Fin(X)" and A3: "A\<noteq>0"
  shows 
  "Maximum(r,A) \<in> A" 
  "Minimum(r,A) \<in> A"
  "\<forall>x\<in>A. \<langle>x,Maximum(r,A)\<rangle> \<in> r" 
  "\<forall>x\<in>A. \<langle>Minimum(r,A),x\<rangle> \<in> r"
proof -
  from A1 have T1: "r {is total on} X" "trans(r)" "antisym(r)"
    using IsLinOrder_def by auto
  moreover from T1 A2 A3 have "HasAmaximum(r,A)" 
    using Finite_ZF_1_1_T1A by auto
  moreover from T1 A2 A3 have "HasAminimum(r,A)"
    using Finite_ZF_1_1_T1B by auto
  ultimately show 
    "Maximum(r,A) \<in> A" 
    "Minimum(r,A) \<in> A"
    "\<forall>x\<in>A. \<langle>x,Maximum(r,A)\<rangle> \<in> r" "\<forall>x\<in>A. \<langle>Minimum(r,A),x\<rangle> \<in> r"
    using Order_ZF_4_L3 Order_ZF_4_L4 by auto
qed

text\<open>A special case of \<open>Finite_ZF_1_T2\<close> when the set has three
  elements.\<close>

corollary Finite_ZF_1_L2A: 
  assumes A1: "IsLinOrder(X,r)" and A2: "a\<in>X"  "b\<in>X"  "c\<in>X"
  shows 
  "Maximum(r,{a,b,c}) \<in> {a,b,c}" 
  "Minimum(r,{a,b,c}) \<in> {a,b,c}"
  "Maximum(r,{a,b,c}) \<in> X" 
  "Minimum(r,{a,b,c}) \<in> X"
  "\<langle>a,Maximum(r,{a,b,c})\<rangle> \<in> r"
  "\<langle>b,Maximum(r,{a,b,c})\<rangle> \<in> r"
  "\<langle>c,Maximum(r,{a,b,c})\<rangle> \<in> r"
proof -
  from A2 have I: "{a,b,c} \<in> Fin(X)"  "{a,b,c} \<noteq> 0"
    by auto
  with A1 show II: "Maximum(r,{a,b,c}) \<in> {a,b,c}" 
    by (rule Finite_ZF_1_T2)
  moreover from A1 I show III: "Minimum(r,{a,b,c}) \<in> {a,b,c}"
    by (rule Finite_ZF_1_T2)
  moreover from A2 have "{a,b,c} \<subseteq> X"
    by auto
  ultimately show  
    "Maximum(r,{a,b,c}) \<in> X" 
    "Minimum(r,{a,b,c}) \<in> X"
    by auto
  from A1 I have "\<forall>x\<in>{a,b,c}. \<langle>x,Maximum(r,{a,b,c})\<rangle> \<in> r"
    by (rule Finite_ZF_1_T2)
  then show 
    "\<langle>a,Maximum(r,{a,b,c})\<rangle> \<in> r"
    "\<langle>b,Maximum(r,{a,b,c})\<rangle> \<in> r"
    "\<langle>c,Maximum(r,{a,b,c})\<rangle> \<in> r"
    by auto
qed


text\<open>If for every element of $X$ we can find one in $A$ 
  that is greater, then the $A$ can not be finite. Works for relations
  that are total, transitive and antisymmetric.\<close>

lemma Finite_ZF_1_1_L3: 
  assumes A1: "r {is total on} X" 
  and A2: "trans(r)" and A3: "antisym(r)"
  and A4: "r \<subseteq> X\<times>X" and A5: "X\<noteq>0" 
  and A6: "\<forall>x\<in>X. \<exists>a\<in>A. x\<noteq>a \<and> \<langle>x,a\<rangle> \<in> r"
  shows "A \<notin> Fin(X)"
proof -
  from assms have "\<not>IsBounded(A,r)"
    using Order_ZF_3_L14 IsBounded_def
    by simp
  with A1 A2 show "A \<notin> Fin(X)"
    using Finite_ZF_1_T1 by auto
qed

end
