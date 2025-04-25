(*   This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2005-2020  Slawomir Kolodynski

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

section \<open>Even more on order relations\<close>

theory Order_ZF_1a imports Order_ZF

begin

text\<open>This theory is a continuation of \<open>Order_ZF\<close> and talks
  about maximum and minimum of a set, supremum and infimum
  and strict (not reflexive) versions of order relations.\<close>

subsection\<open>Maximum and minimum of a set\<close>

text\<open>In this section we show that maximum and minimum are unique if they 
  exist. We also show that union of sets that have maxima (minima) has a 
  maximum (minimum). We also show that singletons have maximum and minimum.
  All this allows to show (in \<open>Finite_ZF\<close>) that every finite set has 
  well-defined maximum and minimum.\<close>

text\<open>A somewhat technical fact that allows to reduce the number of premises in some
  theorems: the assumption that a set has a maximum implies that it is not empty. \<close>

lemma set_max_not_empty: assumes "HasAmaximum(r,A)" shows "A\<noteq>0"
  using assms unfolding HasAmaximum_def by auto

text\<open>If a set has a maximum implies that it is not empty. \<close>

lemma set_min_not_empty: assumes "HasAminimum(r,A)" shows "A\<noteq>0"
  using assms unfolding HasAminimum_def by auto

text\<open>If a set has a supremum then it cannot be empty. We are probably using the fact that 
  $\bigcap  \emptyset = \emptyset $, which makes me a bit anxious 
  as this I think is just a convention. \<close>

lemma set_sup_not_empty: assumes "HasAsupremum(r,A)" shows "A\<noteq>0"
proof -
  from assms have "HasAminimum(r,\<Inter>a\<in>A. r``{a})" unfolding HasAsupremum_def
    by simp 
  then have "(\<Inter>a\<in>A. r``{a}) \<noteq> 0" using set_min_not_empty by simp
  then obtain x where "x \<in> (\<Inter>y\<in>A. r``{y})" by blast
  thus ?thesis by auto
qed

text\<open>If a set has an infimum then it cannot be empty.  \<close>

lemma set_inf_not_empty: assumes "HasAnInfimum(r,A)" shows "A\<noteq>0"
proof -
  from assms have "HasAmaximum(r,\<Inter>a\<in>A. r-``{a})" unfolding HasAnInfimum_def
    by simp 
  then have "(\<Inter>a\<in>A. r-``{a}) \<noteq> 0" using set_max_not_empty by simp
  then obtain x where "x \<in> (\<Inter>y\<in>A. r-``{y})" by blast
  thus ?thesis by auto
qed
  
text\<open>For antisymmetric relations maximum of a set is unique if it exists.\<close>

lemma Order_ZF_4_L1: assumes A1: "antisym(r)" and A2: "HasAmaximum(r,A)"
  shows "\<exists>!M. M\<in>A \<and> (\<forall>x\<in>A. \<langle> x,M\<rangle> \<in> r)"
proof
  from A2 show "\<exists>M. M \<in> A \<and> (\<forall>x\<in>A. \<langle>x, M\<rangle> \<in> r)"
    using HasAmaximum_def by auto
  fix M1 M2 assume 
    A2: "M1 \<in> A \<and> (\<forall>x\<in>A. \<langle>x, M1\<rangle> \<in> r)" "M2 \<in> A \<and> (\<forall>x\<in>A. \<langle>x, M2\<rangle> \<in> r)"
    then have "\<langle>M1,M2\<rangle> \<in> r" "\<langle>M2,M1\<rangle> \<in> r" by auto
    with A1 show "M1=M2" by (rule Fol1_L4)
qed

text\<open>For antisymmetric relations minimum of a set is unique if it exists.\<close>

lemma Order_ZF_4_L2: assumes A1: "antisym(r)" and A2: "HasAminimum(r,A)"
  shows "\<exists>!m. m\<in>A \<and> (\<forall>x\<in>A. \<langle> m,x\<rangle> \<in> r)"
proof
  from A2 show "\<exists>m. m \<in> A \<and> (\<forall>x\<in>A. \<langle>m, x\<rangle> \<in> r)"
    using HasAminimum_def by auto
  fix m1 m2 assume 
    A2: "m1 \<in> A \<and> (\<forall>x\<in>A. \<langle>m1, x\<rangle> \<in> r)" "m2 \<in> A \<and> (\<forall>x\<in>A. \<langle>m2, x\<rangle> \<in> r)"
    then have "\<langle>m1,m2\<rangle> \<in> r" "\<langle>m2,m1\<rangle> \<in> r" by auto
    with A1 show "m1=m2" by (rule Fol1_L4)
qed

text\<open>Maximum of a set has desired properties.\<close>

lemma Order_ZF_4_L3: assumes A1: "antisym(r)" and A2: "HasAmaximum(r,A)"
  shows "Maximum(r,A) \<in> A" "\<forall>x\<in>A. \<langle>x,Maximum(r,A)\<rangle> \<in> r"
proof - 
  let ?Max = "THE M. M\<in>A \<and> (\<forall>x\<in>A. \<langle> x,M\<rangle> \<in> r)" 
  from A1 A2 have "\<exists>!M. M\<in>A \<and> (\<forall>x\<in>A. \<langle> x,M\<rangle> \<in> r)"
    by (rule Order_ZF_4_L1)
  then have "?Max \<in> A \<and> (\<forall>x\<in>A. \<langle> x,?Max\<rangle> \<in> r)"
    by (rule theI)
  then show "Maximum(r,A) \<in> A" "\<forall>x\<in>A. \<langle>x,Maximum(r,A)\<rangle> \<in> r"
    using Maximum_def by auto
qed
  
text\<open>Minimum of a set has desired properties.\<close>
    
lemma Order_ZF_4_L4: assumes A1: "antisym(r)" and A2: "HasAminimum(r,A)"
  shows "Minimum(r,A) \<in> A" "\<forall>x\<in>A. \<langle>Minimum(r,A),x\<rangle> \<in> r"
proof - 
  let ?Min = "THE m. m\<in>A \<and> (\<forall>x\<in>A. \<langle> m,x\<rangle> \<in> r)" 
  from A1 A2 have "\<exists>!m. m\<in>A \<and> (\<forall>x\<in>A. \<langle> m,x\<rangle> \<in> r)"
    by (rule Order_ZF_4_L2)
  then have "?Min \<in> A \<and> (\<forall>x\<in>A. \<langle> ?Min,x\<rangle> \<in> r)"
    by (rule theI)
  then show "Minimum(r,A) \<in> A" "\<forall>x\<in>A. \<langle>Minimum(r,A),x\<rangle> \<in> r"
    using Minimum_def by auto
qed

text\<open>For total and transitive relations a union a of two sets that have 
  maxima has a maximum.\<close>

lemma Order_ZF_4_L5: 
  assumes A1: "r {is total on} (A\<union>B)" and A2: "trans(r)"
  and A3: "HasAmaximum(r,A)" "HasAmaximum(r,B)"
  shows "HasAmaximum(r,A\<union>B)"
proof -
  from A3 obtain M K where 
    D1: "M\<in>A \<and> (\<forall>x\<in>A. \<langle> x,M\<rangle> \<in> r)" "K\<in>B \<and> (\<forall>x\<in>B. \<langle> x,K\<rangle> \<in> r)" 
    using HasAmaximum_def by auto
  let ?L = "GreaterOf(r,M,K)"
  from D1 have T1: "M \<in> A\<union>B" "K \<in> A\<union>B" 
    "\<forall>x\<in>A. \<langle> x,M\<rangle> \<in> r" "\<forall>x\<in>B. \<langle> x,K\<rangle> \<in> r"
    by auto
  with A1 A2 have "\<forall>x\<in>A\<union>B.\<langle> x,?L\<rangle> \<in> r" by (rule Order_ZF_3_L2B)
  moreover from T1 have "?L \<in> A\<union>B" using GreaterOf_def IsTotal_def 
    by simp
  ultimately show "HasAmaximum(r,A\<union>B)" using HasAmaximum_def by auto
qed

text\<open>For total and transitive relations A union a of two sets that have 
  minima has a minimum.\<close>

lemma Order_ZF_4_L6: 
  assumes A1: "r {is total on} (A\<union>B)" and A2: "trans(r)"
  and A3: "HasAminimum(r,A)" "HasAminimum(r,B)"
  shows "HasAminimum(r,A\<union>B)"
proof -
  from A3 obtain m k where 
    D1: "m\<in>A \<and> (\<forall>x\<in>A. \<langle> m,x\<rangle> \<in> r)" "k\<in>B \<and> (\<forall>x\<in>B. \<langle> k,x\<rangle> \<in> r)" 
    using HasAminimum_def by auto
  let ?l = "SmallerOf(r,m,k)"
  from D1 have T1: "m \<in> A\<union>B" "k \<in> A\<union>B" 
    "\<forall>x\<in>A. \<langle> m,x\<rangle> \<in> r" "\<forall>x\<in>B. \<langle> k,x\<rangle> \<in> r"
    by auto
  with A1 A2 have "\<forall>x\<in>A\<union>B.\<langle> ?l,x\<rangle> \<in> r" by (rule Order_ZF_3_L5B)
  moreover from T1 have "?l \<in> A\<union>B" using SmallerOf_def IsTotal_def 
    by simp
  ultimately show "HasAminimum(r,A\<union>B)" using HasAminimum_def by auto
qed

text\<open>Set that has a maximum is bounded above.\<close>

lemma Order_ZF_4_L7:
  assumes "HasAmaximum(r,A)"
  shows "IsBoundedAbove(A,r)"
  using assms HasAmaximum_def IsBoundedAbove_def by auto

text\<open>Set that has a minimum is bounded below.\<close>

lemma Order_ZF_4_L8A:
  assumes "HasAminimum(r,A)"
  shows "IsBoundedBelow(A,r)"
  using assms HasAminimum_def IsBoundedBelow_def by auto

text\<open>A subset of a set that has a maximum is bounded above.\<close>

lemma max_subset_bounded: assumes "HasAmaximum(r,A)" and "B\<subseteq>A"
  shows "IsBoundedAbove(B,r)"
proof -
  from assms(1) obtain M where "\<forall>x\<in>A. \<langle>x,M\<rangle> \<in> r"
    unfolding HasAmaximum_def by auto
  with assms(2) show ?thesis unfolding IsBoundedAbove_def by blast
qed
  
text\<open>A subset of a set that has a minimum is bounded below.\<close>

lemma min_subset_bounded: assumes "HasAminimum(r,A)" and "B\<subseteq>A"
  shows "IsBoundedBelow(B,r)"
proof -
  from assms(1) obtain m where "\<forall>x\<in>A. \<langle>m,x\<rangle> \<in> r"
    unfolding HasAminimum_def by auto
  with assms(2) show ?thesis unfolding IsBoundedBelow_def by blast
qed

text\<open>For reflexive relations singletons have a minimum and maximum.\<close>

lemma Order_ZF_4_L8: assumes "refl(X,r)" and "a\<in>X"
  shows "HasAmaximum(r,{a})" "HasAminimum(r,{a})"
  using assms refl_def HasAmaximum_def HasAminimum_def by auto

text\<open>For total and transitive relations if we add an element to a set 
  that has a maximum, the set still has a maximum.\<close>

lemma Order_ZF_4_L9: 
  assumes A1: "r {is total on} X" and A2: "trans(r)"
  and A3: "A\<subseteq>X" and A4: "a\<in>X" and A5: "HasAmaximum(r,A)"
  shows "HasAmaximum(r,A\<union>{a})"
proof -
  from A3 A4 have "A\<union>{a} \<subseteq> X" by auto
  with A1 have "r {is total on} (A\<union>{a})"
    using Order_ZF_1_L4 by blast
  moreover from A1 A2 A4 A5 have
    "trans(r)" "HasAmaximum(r,A)" by auto
  moreover from A1 A4 have "HasAmaximum(r,{a})"
    using total_is_refl Order_ZF_4_L8 by blast
  ultimately show "HasAmaximum(r,A\<union>{a})" by (rule Order_ZF_4_L5)
qed

text\<open>For total and transitive relations if we add an element to a set 
  that has a minimum, the set still has a minimum.\<close>

lemma Order_ZF_4_L10: 
  assumes A1: "r {is total on} X" and A2: "trans(r)"
  and A3: "A\<subseteq>X" and A4: "a\<in>X" and A5: "HasAminimum(r,A)"
  shows "HasAminimum(r,A\<union>{a})"
proof -
  from A3 A4 have "A\<union>{a} \<subseteq> X" by auto
  with A1 have "r {is total on} (A\<union>{a})"
    using Order_ZF_1_L4 by blast
  moreover from A1 A2 A4 A5 have
    "trans(r)" "HasAminimum(r,A)" by auto
  moreover from A1 A4 have "HasAminimum(r,{a})"
    using total_is_refl Order_ZF_4_L8 by blast
  ultimately show "HasAminimum(r,A\<union>{a})" by (rule Order_ZF_4_L6)
qed

text\<open>If the order relation has a property that every nonempty bounded set 
  attains a minimum (for example integers are like that), 
  then every nonempty set bounded below attains a minimum.\<close>

lemma Order_ZF_4_L11: 
  assumes A1: "r {is total on} X" and 
  A2: "trans(r)" and 
  A3: "r \<subseteq> X\<times>X" and
  A4: "\<forall>A. IsBounded(A,r) \<and> A\<noteq>0 \<longrightarrow> HasAminimum(r,A)" and 
  A5: "B\<noteq>0" and A6: "IsBoundedBelow(B,r)"
  shows "HasAminimum(r,B)"
proof -
  from A5 obtain b where T: "b\<in>B" by auto
  let ?L = "{x\<in>B. \<langle>x,b\<rangle> \<in> r}"
  from A3 A6 T have T1: "b\<in>X" using Order_ZF_3_L1B by blast
  with A1 T have T2: "b \<in> ?L"
    using total_is_refl refl_def by simp
  then have "?L \<noteq> 0" by auto
  moreover have "IsBounded(?L,r)"
  proof -
    have "?L \<subseteq> B" by auto
    with A6 have "IsBoundedBelow(?L,r)"
      using Order_ZF_3_L12 by simp
    moreover have "IsBoundedAbove(?L,r)"
      by (rule Order_ZF_3_L15)
    ultimately have "IsBoundedAbove(?L,r) \<and> IsBoundedBelow(?L,r)"
      by blast
    then show "IsBounded(?L,r)" using IsBounded_def
      by simp
  qed
  ultimately have "IsBounded(?L,r) \<and> ?L \<noteq> 0" by blast
  with A4 have "HasAminimum(r,?L)" by simp
  then obtain m where I: "m\<in>?L" and II: "\<forall>x\<in>?L. \<langle> m,x\<rangle> \<in> r" 
    using HasAminimum_def by auto
  then have III: "\<langle>m,b\<rangle> \<in> r" by simp
  from I have "m\<in>B" by simp
  moreover have "\<forall>x\<in>B. \<langle>m,x\<rangle> \<in> r"
  proof
    fix x assume A7: "x\<in>B"
    from A3 A6 have "B\<subseteq>X" using Order_ZF_3_L1B by blast
    with A1 A7 T1 have "x \<in>  ?L \<union> {x\<in>B. \<langle>b,x\<rangle> \<in> r}"
      using Order_ZF_1_L5 by simp
    then have "x\<in>?L \<or> \<langle>b,x\<rangle> \<in> r" by auto
    moreover
    { assume "x\<in>?L"
      with II have "\<langle>m,x\<rangle> \<in> r" by simp }
    moreover
    { assume "\<langle>b,x\<rangle> \<in> r"
      with A2 III have "trans(r)" and "\<langle>m,b\<rangle> \<in> r \<and> \<langle>b,x\<rangle> \<in> r"
	by auto
      then have  "\<langle>m,x\<rangle> \<in> r" by (rule Fol1_L3) }
    ultimately show "\<langle>m,x\<rangle> \<in> r" by auto
  qed
  ultimately show "HasAminimum(r,B)" using HasAminimum_def
    by auto
qed

text\<open>A dual to \<open>Order_ZF_4_L11\<close>: 
  If the order relation has a property that every nonempty bounded set 
  attains a maximum (for example integers are like that), 
  then every nonempty set bounded above attains a maximum.\<close>

lemma Order_ZF_4_L11A: 
  assumes A1: "r {is total on} X" and 
  A2: "trans(r)" and 
  A3: "r \<subseteq> X\<times>X" and
  A4: "\<forall>A. IsBounded(A,r) \<and> A\<noteq>0 \<longrightarrow> HasAmaximum(r,A)" and 
  A5: "B\<noteq>0" and A6: "IsBoundedAbove(B,r)"
  shows "HasAmaximum(r,B)"
proof -
  from A5 obtain b where T: "b\<in>B" by auto
  let ?U = "{x\<in>B. \<langle>b,x\<rangle> \<in> r}"
  from A3 A6 T have T1: "b\<in>X" using Order_ZF_3_L1A by blast
  with A1 T have T2: "b \<in> ?U"
    using total_is_refl refl_def by simp
  then have "?U \<noteq> 0" by auto
  moreover have "IsBounded(?U,r)"
  proof -
    have "?U \<subseteq> B" by auto
    with A6 have "IsBoundedAbove(?U,r)"
      using Order_ZF_3_L13 by blast
    moreover have "IsBoundedBelow(?U,r)"
      using IsBoundedBelow_def by auto
    ultimately have "IsBoundedAbove(?U,r) \<and> IsBoundedBelow(?U,r)"
      by blast
    then show "IsBounded(?U,r)" using IsBounded_def
      by simp
  qed
  ultimately have "IsBounded(?U,r) \<and> ?U \<noteq> 0" by blast
  with A4 have "HasAmaximum(r,?U)" by simp
  then obtain m where I: "m\<in>?U" and II: "\<forall>x\<in>?U. \<langle>x,m\<rangle> \<in> r"
    using HasAmaximum_def by auto
  then have III: "\<langle>b,m\<rangle> \<in> r" by simp
  from I have "m\<in>B" by simp
  moreover have "\<forall>x\<in>B. \<langle>x,m\<rangle> \<in> r"
  proof
    fix x assume A7: "x\<in>B"
    from A3 A6 have "B\<subseteq>X" using Order_ZF_3_L1A by blast
    with A1 A7 T1 have "x \<in> {x\<in>B. \<langle>x,b\<rangle> \<in> r} \<union> ?U"
      using Order_ZF_1_L5 by simp
    then have "x\<in>?U \<or> \<langle>x,b\<rangle> \<in> r" by auto
    moreover
    { assume "x\<in>?U"
      with II have "\<langle>x,m\<rangle> \<in> r" by simp }
    moreover
    { assume "\<langle>x,b\<rangle> \<in> r"
      with A2 III have "trans(r)" and "\<langle>x,b\<rangle> \<in> r \<and> \<langle>b,m\<rangle> \<in> r"
	by auto
      then have  "\<langle>x,m\<rangle> \<in> r" by (rule Fol1_L3) }
    ultimately show "\<langle>x,m\<rangle> \<in> r" by auto
  qed
  ultimately show "HasAmaximum(r,B)" using HasAmaximum_def
    by auto
qed

text\<open>If a set has a minimum and $L$ is less or equal than 
  all elements of the set, then $L$ is less or equal than the minimum.\<close>

lemma Order_ZF_4_L12: 
  assumes "antisym(r)" and "HasAminimum(r,A)" and "\<forall>a\<in>A. \<langle>L,a\<rangle> \<in> r"
  shows "\<langle>L,Minimum(r,A)\<rangle> \<in> r"
  using assms Order_ZF_4_L4 by simp


text\<open>If a set has a maximum and all its elements are less or equal than 
  $M$, then the maximum of the set is less or equal than $M$.\<close>

lemma Order_ZF_4_L13: 
  assumes "antisym(r)" and "HasAmaximum(r,A)" and "\<forall>a\<in>A. \<langle>a,M\<rangle> \<in> r"
  shows "\<langle>Maximum(r,A),M\<rangle> \<in> r"
  using assms Order_ZF_4_L3 by simp

text\<open>If an element belongs to a set and is greater or equal
  than all elements of that set, then it is the maximum of that set.\<close>

lemma Order_ZF_4_L14: 
  assumes A1: "antisym(r)" and A2: "M \<in> A" and 
  A3: "\<forall>a\<in>A. \<langle>a,M\<rangle> \<in> r"
  shows "Maximum(r,A) = M"
proof -
  from A2 A3 have I: "HasAmaximum(r,A)" using HasAmaximum_def
    by auto
  with A1 have "\<exists>!M. M\<in>A \<and> (\<forall>x\<in>A. \<langle>x,M\<rangle> \<in> r)"
    using Order_ZF_4_L1 by simp
  moreover from A2 A3 have "M\<in>A \<and> (\<forall>x\<in>A. \<langle>x,M\<rangle> \<in> r)" by simp
  moreover from A1 I have 
    "Maximum(r,A) \<in> A \<and> (\<forall>x\<in>A. \<langle>x,Maximum(r,A)\<rangle> \<in> r)"
    using Order_ZF_4_L3 by simp
  ultimately show "Maximum(r,A) = M" by auto
qed

text\<open>If an element belongs to a set and is less or equal
  than all elements of that set, then it is the minimum of that set.\<close>

lemma Order_ZF_4_L15: 
  assumes A1: "antisym(r)" and A2: "m \<in> A" and 
  A3: "\<forall>a\<in>A. \<langle>m,a\<rangle> \<in> r"
  shows "Minimum(r,A) = m"
proof -
  from A2 A3 have I: "HasAminimum(r,A)" using HasAminimum_def
    by auto
  with A1 have "\<exists>!m. m\<in>A \<and> (\<forall>x\<in>A. \<langle>m,x\<rangle> \<in> r)"
    using Order_ZF_4_L2 by simp
  moreover from A2 A3 have "m\<in>A \<and> (\<forall>x\<in>A. \<langle>m,x\<rangle> \<in> r)" by simp
  moreover from A1 I have 
    "Minimum(r,A) \<in> A \<and> (\<forall>x\<in>A. \<langle>Minimum(r,A),x\<rangle> \<in> r)"
    using Order_ZF_4_L4 by simp
  ultimately show "Minimum(r,A) = m" by auto
qed

text\<open>If a set does not have a maximum, then for any its element we can
  find one that is (strictly) greater.\<close>

lemma Order_ZF_4_L16: 
  assumes A1: "antisym(r)" and A2: "r {is total on} X" and 
  A3: "A\<subseteq>X" and
  A4: "\<not>HasAmaximum(r,A)" and 
  A5: "x\<in>A"
  shows "\<exists>y\<in>A. \<langle>x,y\<rangle> \<in> r \<and> y\<noteq>x"
proof -
  { assume A6: "\<forall>y\<in>A. \<langle>x,y\<rangle> \<notin> r \<or> y=x"
    have "\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> r"
    proof
      fix y assume A7: "y\<in>A"
      with A6 have "\<langle>x,y\<rangle> \<notin> r \<or> y=x" by simp
      with A2 A3 A5 A7 show "\<langle>y,x\<rangle> \<in> r"
	using IsTotal_def Order_ZF_1_L1 by auto
    qed
    with A5 have "\<exists>x\<in>A.\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> r"
      by auto
    with A4 have False using HasAmaximum_def by simp
  } then show "\<exists>y\<in>A. \<langle>x,y\<rangle> \<in> r \<and> y\<noteq>x" by auto
qed


subsection\<open>Supremum and Infimum\<close>

text\<open>In this section we consider the notions of supremum and infimum a set.\<close>

text\<open>Elements of the set of upper bounds are indeed upper bounds.
  Isabelle also thinks it is obvious.\<close>

lemma Order_ZF_5_L1: assumes "u \<in> (\<Inter>a\<in>A. r``{a})" and "a\<in>A"
  shows "\<langle>a,u\<rangle> \<in> r"
  using assms by auto

text\<open>Elements of the set of lower bounds are indeed lower bounds.
  Isabelle also thinks it is obvious.\<close>
  
lemma Order_ZF_5_L2: assumes "l \<in> (\<Inter>a\<in>A. r-``{a})" and "a\<in>A"
  shows "\<langle>l,a\<rangle> \<in> r"
  using assms by auto

text\<open>If the set of upper bounds has a minimum, then the supremum 
  is less or equal than any upper bound. We can probably do away with
  the assumption that $A$ is not empty, (ab)using the fact that 
  intersection over an empty family is defined in Isabelle to be empty.
  This lemma is obsolete and will be removed in the future. Use \<open>sup_leq_up_bnd\<close> instead.\<close>

lemma Order_ZF_5_L3: assumes A1: "antisym(r)" and A2: "A\<noteq>0" and
  A3: "HasAminimum(r,\<Inter>a\<in>A. r``{a})" and 
  A4: "\<forall>a\<in>A. \<langle>a,u\<rangle> \<in> r"
  shows "\<langle>Supremum(r,A),u\<rangle> \<in> r"
proof -
  let ?U = "\<Inter>a\<in>A. r``{a}"
  from A4 have "\<forall>a\<in>A. u \<in> r``{a}" using image_singleton_iff
    by simp
  with A2 have "u\<in>?U" by auto
  with A1 A3 show "\<langle>Supremum(r,A),u\<rangle> \<in> r"
    using Order_ZF_4_L4 Supremum_def by simp
qed

text\<open>Supremum is less or equal than any upper bound. \<close>

lemma sup_leq_up_bnd: assumes "antisym(r)" "HasAsupremum(r,A)" "\<forall>a\<in>A. \<langle>a,u\<rangle> \<in> r"
  shows "\<langle>Supremum(r,A),u\<rangle> \<in> r"
proof -
  let ?U = "\<Inter>a\<in>A. r``{a}"
  from assms(3) have  "\<forall>a\<in>A. u \<in> r``{a}" using image_singleton_iff by simp
  with assms(2) have "u\<in>?U" using set_sup_not_empty by auto
  with assms(1,2) show "\<langle>Supremum(r,A),u\<rangle> \<in> r" 
    unfolding HasAsupremum_def Supremum_def using Order_ZF_4_L4 by simp
qed

text\<open>Infimum is greater or equal than any lower bound. 
  This lemma is obsolete and will be removed. Use \<open>inf_geq_lo_bnd\<close> instead.\<close>

lemma Order_ZF_5_L4: assumes A1: "antisym(r)" and A2: "A\<noteq>0" and
  A3: "HasAmaximum(r,\<Inter>a\<in>A. r-``{a})" and 
  A4: "\<forall>a\<in>A. \<langle>l,a\<rangle> \<in> r"
  shows "\<langle>l,Infimum(r,A)\<rangle> \<in> r"
proof -
  let ?L = "\<Inter>a\<in>A. r-``{a}"
  from A4 have "\<forall>a\<in>A. l \<in> r-``{a}" using vimage_singleton_iff
    by simp
  with A2 have "l\<in>?L" by auto 
  with A1 A3 show "\<langle>l,Infimum(r,A)\<rangle> \<in> r"
    using Order_ZF_4_L3 Infimum_def by simp
qed

text\<open>Infimum is greater or equal than any upper bound. \<close>

lemma inf_geq_lo_bnd: assumes "antisym(r)" "HasAnInfimum(r,A)" "\<forall>a\<in>A. \<langle>u,a\<rangle> \<in> r"
  shows "\<langle>u,Infimum(r,A)\<rangle> \<in> r"
proof -
  let ?U = "\<Inter>a\<in>A. r-``{a}"
  from assms(3) have  "\<forall>a\<in>A. u \<in> r-``{a}" using vimage_singleton_iff by simp
  with assms(2) have "u\<in>?U" using set_inf_not_empty by auto
  with assms(1,2) show  "\<langle>u,Infimum(r,A)\<rangle> \<in> r" 
    unfolding HasAnInfimum_def Infimum_def using Order_ZF_4_L3 by simp
qed

text\<open>If $z$ is an upper bound for $A$ and is less or equal than
  any other upper bound, then $z$ is the supremum of $A$.\<close>

lemma Order_ZF_5_L5: assumes A1: "antisym(r)" and A2: "A\<noteq>0" and
  A3: "\<forall>x\<in>A. \<langle>x,z\<rangle> \<in> r" and 
  A4: "\<forall>y. (\<forall>x\<in>A. \<langle>x,y\<rangle> \<in> r) \<longrightarrow> \<langle>z,y\<rangle> \<in> r"
  shows 
  "HasAminimum(r,\<Inter>a\<in>A. r``{a})"
  "z = Supremum(r,A)"
proof -
  let ?B = "\<Inter>a\<in>A. r``{a}"
  from A2 A3 A4 have I: "z \<in> ?B"   "\<forall>y\<in>?B. \<langle>z,y\<rangle> \<in> r"
    by auto
  then show "HasAminimum(r,\<Inter>a\<in>A. r``{a})"
    using HasAminimum_def by auto
  from A1 I show "z = Supremum(r,A)"
    using Order_ZF_4_L15 Supremum_def by simp
qed

text\<open>The dual theorem to \<open>Order_ZF_5_L5\<close>: if $z$ is an lower bound for $A$ and is 
  greater or equal than any other lower bound, then $z$ is the infimum of $A$.\<close>

lemma inf_glb: 
  assumes "antisym(r)" "A\<noteq>0" "\<forall>x\<in>A. \<langle>z,x\<rangle> \<in> r" "\<forall>y. (\<forall>x\<in>A. \<langle>y,x\<rangle> \<in> r) \<longrightarrow> \<langle>y,z\<rangle> \<in> r"
  shows 
  "HasAmaximum(r,\<Inter>a\<in>A. r-``{a})"
  "z = Infimum(r,A)"
proof -
  let ?B = "\<Inter>a\<in>A. r-``{a}"
  from assms(2,3,4) have I: "z \<in> ?B"   "\<forall>y\<in>?B. \<langle>y,z\<rangle> \<in> r"
    by auto
  then show "HasAmaximum(r,\<Inter>a\<in>A. r-``{a})"
    unfolding HasAmaximum_def by auto
  from assms(1) I show "z = Infimum(r,A)"
    using Order_ZF_4_L14 Infimum_def by simp
qed

text\<open> Supremum and infimum of a singleton is the element. \<close>

lemma sup_inf_singl: assumes "antisym(r)" "refl(X,r)" "z\<in>X"
  shows 
    "HasAsupremum(r,{z})" "Supremum(r,{z}) = z" and 
    "HasAnInfimum(r,{z})" "Infimum(r,{z}) = z"
proof -
  from assms show "Supremum(r,{z}) = z" and "Infimum(r,{z}) = z" 
    using inf_glb Order_ZF_5_L5 unfolding refl_def by auto
  from assms show  "HasAsupremum(r,{z})" 
    using Order_ZF_5_L5 unfolding HasAsupremum_def refl_def by blast
  from assms show "HasAnInfimum(r,{z})"
    using inf_glb unfolding HasAnInfimum_def refl_def by blast
qed
  
text\<open>If a set has a maximum, then the maximum is the supremum. This lemma is obsolete, use
  \<open>max_is_sup\<close> instead.\<close>

lemma Order_ZF_5_L6: 
  assumes A1:  "antisym(r)" and A2: "A\<noteq>0" and 
  A3: "HasAmaximum(r,A)"
  shows 
  "HasAminimum(r,\<Inter>a\<in>A. r``{a})"
  "Maximum(r,A) = Supremum(r,A)"
proof -
  let ?M = "Maximum(r,A)"
  from A1 A3 have I: "?M \<in> A" and II: "\<forall>x\<in>A. \<langle>x,?M\<rangle> \<in> r"
    using Order_ZF_4_L3 by auto
  from I have III: "\<forall>y. (\<forall>x\<in>A. \<langle>x,y\<rangle> \<in> r) \<longrightarrow> \<langle>?M,y\<rangle> \<in> r"
    by simp
  with A1 A2 II show "HasAminimum(r,\<Inter>a\<in>A. r``{a})"
    by (rule Order_ZF_5_L5)
  from A1 A2 II III show "?M = Supremum(r,A)"
    by (rule Order_ZF_5_L5)
qed

text\<open>Another version of \<open>Order_ZF_5_L6\<close> that: if a sat has a maximum then it has a supremum and 
  the maximum is the supremum. \<close>

lemma max_is_sup: assumes "antisym(r)" "A\<noteq>0" "HasAmaximum(r,A)"
  shows "HasAsupremum(r,A)" and "Maximum(r,A) = Supremum(r,A)"
proof -
  let ?M = "Maximum(r,A)"
  from assms(1,3) have "?M \<in> A" and I: "\<forall>x\<in>A. \<langle>x,?M\<rangle> \<in> r" using Order_ZF_4_L3 
    by auto
  with assms(1,2) have "HasAminimum(r,\<Inter>a\<in>A. r``{a})" using Order_ZF_5_L5(1) 
    by blast
  then show "HasAsupremum(r,A)" unfolding HasAsupremum_def by simp
  from assms(1,2) \<open>?M \<in> A\<close> I show "?M = Supremum(r,A)" using Order_ZF_5_L5(2) 
    by blast
qed

text\<open> Minimum is the infimum if it exists.\<close>

lemma min_is_inf: assumes "antisym(r)" "A\<noteq>0" "HasAminimum(r,A)"
  shows "HasAnInfimum(r,A)" and "Minimum(r,A) = Infimum(r,A)"
proof -
  let ?M = "Minimum(r,A)"
  from assms(1,3) have "?M\<in>A" and I: "\<forall>x\<in>A. \<langle>?M,x\<rangle> \<in> r" using  Order_ZF_4_L4 
    by auto
  with assms(1,2) have "HasAmaximum(r,\<Inter>a\<in>A. r-``{a})" using inf_glb(1) by blast
  then show "HasAnInfimum(r,A)" unfolding HasAnInfimum_def by simp
  from assms(1,2) \<open>?M \<in> A\<close> I show "?M = Infimum(r,A)" using inf_glb(2) by blast
qed

text\<open>For reflexive and total relations two-element set has a minimum and a maximum. \<close>

lemma min_max_two_el: assumes "r {is total on} X" "x\<in>X" "y\<in>X"
  shows "HasAminimum(r,{x,y})" and "HasAmaximum(r,{x,y})"
  using assms unfolding IsTotal_def HasAminimum_def HasAmaximum_def by auto

text\<open>For antisymmetric, reflexive and total relations two-element set has a supremum and infimum. \<close>

lemma inf_sup_two_el:assumes "antisym(r)" "r {is total on} X" "x\<in>X" "y\<in>X"
  shows 
    "HasAnInfimum(r,{x,y})"
    "Minimum(r,{x,y}) = Infimum(r,{x,y})"
    "HasAsupremum(r,{x,y})"
    "Maximum(r,{x,y}) = Supremum(r,{x,y})"
  using assms min_max_two_el max_is_sup min_is_inf by auto

text\<open>A sufficient condition for the supremum to be in the space.\<close>

lemma sup_in_space: 
  assumes "r \<subseteq> X\<times>X" "antisym(r)" "HasAminimum(r,\<Inter>a\<in>A. r``{a})"
  shows "Supremum(r,A) \<in> X" and "\<forall>x\<in>A. \<langle>x,Supremum(r,A)\<rangle> \<in> r"
proof -
  from assms(3) have "A\<noteq>0" using set_sup_not_empty unfolding HasAsupremum_def by simp
  then obtain a where "a\<in>A" by auto
  with assms(1,2,3) show "Supremum(r,A) \<in> X" unfolding Supremum_def 
    using Order_ZF_4_L4 Order_ZF_5_L1 by blast
  from assms(2,3) show "\<forall>x\<in>A. \<langle>x,Supremum(r,A)\<rangle> \<in> r" unfolding Supremum_def
    using Order_ZF_4_L4 by blast
qed

text\<open>A sufficient condition for the infimum to be in the space.\<close>

lemma inf_in_space: 
  assumes "r \<subseteq> X\<times>X" "antisym(r)" "HasAmaximum(r,\<Inter>a\<in>A. r-``{a})"
  shows "Infimum(r,A) \<in> X" and "\<forall>x\<in>A. \<langle>Infimum(r,A),x\<rangle> \<in> r"
proof -
  from assms(3) have "A\<noteq>0" using set_inf_not_empty unfolding HasAnInfimum_def by simp
  then obtain a where "a\<in>A" by auto
  with assms(1,2,3) show "Infimum(r,A) \<in> X" unfolding Infimum_def 
    using Order_ZF_4_L3 Order_ZF_5_L1 by blast
  from assms(2,3) show "\<forall>x\<in>A. \<langle>Infimum(r,A),x\<rangle> \<in> r" unfolding Infimum_def
    using Order_ZF_4_L3 by blast
qed

text\<open>Properties of supremum of a set for complete relations.\<close>

lemma Order_ZF_5_L7: 
  assumes A1: "r \<subseteq> X\<times>X" and A2: "antisym(r)" and 
  A3: "r {is complete}" and
  A4: "A\<noteq>0" and A5: "\<exists>x\<in>X. \<forall>y\<in>A. \<langle>y,x\<rangle> \<in> r"
  shows "Supremum(r,A) \<in> X" and "\<forall>x\<in>A. \<langle>x,Supremum(r,A)\<rangle> \<in> r"
proof -
  from A3 A4 A5 have "HasAminimum(r,\<Inter>a\<in>A. r``{a})"
    unfolding IsBoundedAbove_def IsComplete_def by blast
  with A1 A2 show "Supremum(r,A) \<in> X" and "\<forall>x\<in>A. \<langle>x,Supremum(r,A)\<rangle> \<in> r"
    using sup_in_space by auto
qed 

text\<open> Infimum of the set of infima of a collection of sets is infimum of the union. \<close>

lemma inf_inf:
  assumes 
    "r \<subseteq> X\<times>X" "antisym(r)" "trans(r)" 
    "\<forall>T\<in>\<T>. HasAnInfimum(r,T)"
    "HasAnInfimum(r,{Infimum(r,T).T\<in>\<T>})"
  shows 
    "HasAnInfimum(r,\<Union>\<T>)" and "Infimum(r,{Infimum(r,T).T\<in>\<T>}) = Infimum(r,\<Union>\<T>)"
proof -
  let ?i = "Infimum(r,{Infimum(r,T).T\<in>\<T>})"
  note assms(2)
  moreover from assms(4,5) have "\<Union>\<T> \<noteq> 0" using set_inf_not_empty by blast
  moreover
  have "\<forall>T\<in>\<T>.\<forall>t\<in>T. \<langle>?i,t\<rangle> \<in> r"
  proof -
    { fix T t assume "T\<in>\<T>" "t\<in>T"
      with assms(1,2,4) have "\<langle>Infimum(r,T),t\<rangle> \<in> r"
        unfolding HasAnInfimum_def using inf_in_space(2) by blast
      moreover from assms(1,2,5) \<open>T\<in>\<T>\<close> have "\<langle>?i,Infimum(r,T)\<rangle> \<in> r"
        unfolding HasAnInfimum_def using inf_in_space(2) by blast
      moreover note assms(3)
      ultimately have "\<langle>?i,t\<rangle> \<in> r" unfolding trans_def by blast
    } thus ?thesis by simp
  qed
  hence I: "\<forall>t\<in>\<Union>\<T>. \<langle>?i,t\<rangle> \<in> r" by auto
  moreover have J: "\<forall>y. (\<forall>x\<in>\<Union>\<T>. \<langle>y,x\<rangle> \<in> r) \<longrightarrow> \<langle>y,?i\<rangle> \<in> r"
  proof -
    { fix y x assume A: "\<forall>x\<in>\<Union>\<T>. \<langle>y,x\<rangle> \<in> r"
      with assms(2,4) have "\<forall>a\<in>{Infimum(r,T).T\<in>\<T>}. \<langle>y,a\<rangle> \<in> r" using inf_geq_lo_bnd
        by simp
      with assms(2,5) have "\<langle>y,?i\<rangle> \<in> r" by (rule inf_geq_lo_bnd)
    } thus ?thesis by simp
  qed 
  ultimately have "HasAmaximum(r,\<Inter>a\<in>\<Union>\<T>. r-``{a})" by (rule inf_glb)
  then show "HasAnInfimum(r,\<Union>\<T>)" unfolding HasAnInfimum_def by simp
  from assms(2) \<open>\<Union>\<T> \<noteq> 0\<close> I J show "?i = Infimum(r,\<Union>\<T>)" by (rule inf_glb)
qed

text\<open> Supremum of the set of suprema of a collection of sets is supremum of the union. \<close>

lemma sup_sup:
  assumes 
    "r \<subseteq> X\<times>X" "antisym(r)" "trans(r)" 
    "\<forall>T\<in>\<T>. HasAsupremum(r,T)"
    "HasAsupremum(r,{Supremum(r,T).T\<in>\<T>})"
  shows 
    "HasAsupremum(r,\<Union>\<T>)" and "Supremum(r,{Supremum(r,T).T\<in>\<T>}) = Supremum(r,\<Union>\<T>)"
proof -
  let ?s = "Supremum(r,{Supremum(r,T).T\<in>\<T>})"
  note assms(2)
  moreover from assms(4,5) have "\<Union>\<T> \<noteq> 0" using set_sup_not_empty by blast
  moreover
  have "\<forall>T\<in>\<T>.\<forall>t\<in>T. \<langle>t,?s\<rangle> \<in> r"
  proof -
    { fix T t assume "T\<in>\<T>" "t\<in>T"
      with assms(1,2,4) have "\<langle>t,Supremum(r,T)\<rangle> \<in> r"
        unfolding HasAsupremum_def using sup_in_space(2) by blast
      moreover from assms(1,2,5) \<open>T\<in>\<T>\<close> have "\<langle>Supremum(r,T),?s\<rangle> \<in> r"
        unfolding HasAsupremum_def using sup_in_space(2) by blast
      moreover note assms(3)
      ultimately have "\<langle>t,?s\<rangle> \<in> r" unfolding trans_def by blast
    } thus ?thesis by simp
  qed
  hence I: "\<forall>t\<in>\<Union>\<T>. \<langle>t,?s\<rangle> \<in> r" by auto
  moreover have J: "\<forall>y. (\<forall>x\<in>\<Union>\<T>. \<langle>x,y\<rangle> \<in> r) \<longrightarrow> \<langle>?s,y\<rangle> \<in> r"
  proof -
    { fix y x assume A: "\<forall>x\<in>\<Union>\<T>. \<langle>x,y\<rangle> \<in> r"
      with assms(2,4) have "\<forall>a\<in>{Supremum(r,T).T\<in>\<T>}. \<langle>a,y\<rangle> \<in> r" using sup_leq_up_bnd
        by simp
      with assms(2,5) have "\<langle>?s,y\<rangle> \<in> r" by (rule sup_leq_up_bnd)
    } thus ?thesis by simp
  qed 
  ultimately have "HasAminimum(r,\<Inter>a\<in>\<Union>\<T>. r``{a})" by (rule Order_ZF_5_L5)
  then show "HasAsupremum(r,\<Union>\<T>)" unfolding HasAsupremum_def by simp
  from assms(2) \<open>\<Union>\<T> \<noteq> 0\<close> I J show "?s = Supremum(r,\<Union>\<T>)" by (rule Order_ZF_5_L5)
qed

text\<open>If the relation is a linear order then for any 
  element $y$ smaller than the supremum of a set we can
  find one element of the set that is greater than $y$.\<close>

lemma Order_ZF_5_L8:
  assumes A1: "r \<subseteq> X\<times>X"  and A2: "IsLinOrder(X,r)" and 
  A3: "r {is complete}" and
  A4: "A\<subseteq>X"  "A\<noteq>0" and A5: "\<exists>x\<in>X. \<forall>y\<in>A. \<langle>y,x\<rangle> \<in> r" and
  A6: "\<langle>y,Supremum(r,A)\<rangle> \<in> r"   "y \<noteq> Supremum(r,A)"
  shows "\<exists>z\<in>A. \<langle>y,z\<rangle> \<in> r \<and> y \<noteq> z"
proof -
  from A2 have 
    I: "antisym(r)" and
    II: "trans(r)" and
    III: "r {is total on} X"
    using IsLinOrder_def by auto
  from A1 A6 have T1: "y\<in>X" by auto
  { assume A7: "\<forall>z \<in> A. \<langle>y,z\<rangle> \<notin> r \<or> y=z"
    from A4 I have "antisym(r)" and "A\<noteq>0" by auto
    moreover have "\<forall>x\<in>A. \<langle>x,y\<rangle> \<in> r"  
    proof      
      fix x assume A8: "x\<in>A"
      with A4 have T2: "x\<in>X" by auto
      from A7 A8 have "\<langle>y,x\<rangle> \<notin> r \<or> y=x" by simp
      with III T1 T2 show "\<langle>x,y\<rangle> \<in> r"
	using IsTotal_def total_is_refl refl_def by auto
    qed
    moreover have "\<forall>u. (\<forall>x\<in>A. \<langle>x,u\<rangle> \<in> r) \<longrightarrow> \<langle>y,u\<rangle> \<in> r"
    proof-
      { fix u assume A9: "\<forall>x\<in>A. \<langle>x,u\<rangle> \<in> r"
	from A4 A5 have "IsBoundedAbove(A,r)" and "A\<noteq>0"
	  using IsBoundedAbove_def by auto
	with  A3 A4 A6 I A9  have 
	  "\<langle>y,Supremum(r,A)\<rangle> \<in> r \<and> \<langle>Supremum(r,A),u\<rangle> \<in> r"
	  using IsComplete_def Order_ZF_5_L3 by simp
	with II have "\<langle>y,u\<rangle> \<in> r" by (rule Fol1_L3)
      } then show "\<forall>u. (\<forall>x\<in>A. \<langle>x,u\<rangle> \<in> r) \<longrightarrow> \<langle>y,u\<rangle> \<in> r"
	by simp
    qed
    ultimately have "y = Supremum(r,A)"
      by (rule Order_ZF_5_L5)
    with A6 have False by simp
  } then show "\<exists>z\<in>A. \<langle>y,z\<rangle> \<in> r \<and> y \<noteq> z" by auto
qed

subsection\<open>Strict versions of order relations\<close>

text\<open>One of the problems with translating formalized mathematics from
  Metamath to IsarMathLib is that Metamath uses strict orders (of the $<$ 
  type) while in IsarMathLib we mostly use nonstrict orders (of the 
  $\leq$ type). 
  This doesn't really make any difference, but is annoying as we 
  have to prove many theorems twice. In this section we prove some theorems
  to make it easier to translate the statements about strict orders to
  statements about the corresponding non-strict order and vice versa.\<close>

text\<open>We define a strict version of a relation by removing the $y=x$ line 
  from the relation.\<close>

definition
  "StrictVersion(r) \<equiv> r - {\<langle>x,x\<rangle>. x \<in> domain(r)}"

text\<open>A reformulation of the definition of a strict version of an order.
\<close>

lemma def_of_strict_ver: shows 
  "\<langle>x,y\<rangle> \<in> StrictVersion(r) \<longleftrightarrow> \<langle>x,y\<rangle> \<in> r \<and> x\<noteq>y"
  using StrictVersion_def domain_def by auto

text\<open>The next lemma is about the strict version of an antisymmetric
  relation.\<close>

lemma strict_of_antisym: 
  assumes A1: "antisym(r)" and A2: "\<langle>a,b\<rangle> \<in> StrictVersion(r)"
  shows "\<langle>b,a\<rangle> \<notin> StrictVersion(r)"
proof -
  { assume A3: "\<langle>b,a\<rangle> \<in> StrictVersion(r)"
    with A2 have "\<langle>a,b\<rangle> \<in> r"  and "\<langle>b,a\<rangle> \<in> r"
      using def_of_strict_ver by auto
    with A1 have "a=b" by (rule Fol1_L4)
    with A2 have False using def_of_strict_ver
      by simp
  } then show "\<langle>b,a\<rangle> \<notin> StrictVersion(r)" by auto
qed

text\<open>The strict version of totality.\<close>

lemma strict_of_tot:
  assumes "r {is total on} X" and "a\<in>X"  "b\<in>X"  "a\<noteq>b"
  shows "\<langle>a,b\<rangle> \<in> StrictVersion(r) \<or> \<langle>b,a\<rangle> \<in> StrictVersion(r)"
  using assms IsTotal_def def_of_strict_ver by auto

text\<open>A trichotomy law for the strict version of a total 
  and antisymmetric
  relation. It is kind of interesting that one does not need
  the full linear order for this.\<close>

lemma strict_ans_tot_trich: 
  assumes A1: "antisym(r)" and A2: "r {is total on} X"
  and A3: "a\<in>X"  "b\<in>X"
  and A4: "s = StrictVersion(r)"
  shows "Exactly_1_of_3_holds(\<langle>a,b\<rangle> \<in> s, a=b,\<langle>b,a\<rangle> \<in> s)"
proof -
  let ?p = "\<langle>a,b\<rangle> \<in> s"
  let ?q = "a=b"
  let ?r = "\<langle>b,a\<rangle> \<in> s"
  from A2 A3 A4 have "?p \<or> ?q \<or> ?r"
    using strict_of_tot by auto
  moreover from A1 A4 have "?p \<longrightarrow> \<not>?q \<and> \<not>?r"
    using def_of_strict_ver strict_of_antisym by simp
  moreover from A4 have "?q \<longrightarrow> \<not>?p \<and> \<not>?r"
    using def_of_strict_ver by simp
  moreover from A1 A4 have "?r \<longrightarrow> \<not>?p \<and> \<not>?q"
    using def_of_strict_ver strict_of_antisym by auto
  ultimately show "Exactly_1_of_3_holds(?p, ?q, ?r)"
    by (rule Fol1_L5)
qed

text\<open>A trichotomy law for linear order. This is a special
  case of \<open>strict_ans_tot_trich\<close>.\<close>

corollary strict_lin_trich: assumes A1: "IsLinOrder(X,r)" and
  A2: "a\<in>X"  "b\<in>X" and 
  A3: "s = StrictVersion(r)"
  shows "Exactly_1_of_3_holds(\<langle>a,b\<rangle> \<in> s, a=b,\<langle>b,a\<rangle> \<in> s)"
  using assms IsLinOrder_def strict_ans_tot_trich by auto

text\<open>For an antisymmetric relation if a pair is in relation then
  the reversed pair is not in the strict version of the relation. 
\<close>

lemma geq_impl_not_less: 
  assumes A1: "antisym(r)" and A2: "\<langle>a,b\<rangle> \<in> r"
  shows "\<langle>b,a\<rangle> \<notin> StrictVersion(r)"
proof -
  { assume A3: "\<langle>b,a\<rangle> \<in>  StrictVersion(r)"
    with A2 have "\<langle>a,b\<rangle> \<in> StrictVersion(r)"
      using def_of_strict_ver by auto
    with A1 A3 have False using strict_of_antisym
      by blast
  } then show "\<langle>b,a\<rangle> \<notin> StrictVersion(r)" by auto
qed
 
text\<open>If an antisymmetric relation is transitive, 
  then the strict version is also transitive, an explicit
  version \<open>strict_of_transB\<close> below.\<close>

lemma strict_of_transA: 
  assumes A1: "trans(r)" and A2: "antisym(r)" and  
  A3: "s= StrictVersion(r)" and  A4: "\<langle>a,b\<rangle> \<in> s"  "\<langle>b,c\<rangle> \<in> s"
  shows "\<langle>a,c\<rangle> \<in> s"
proof -
  from A3 A4 have I: "\<langle>a,b\<rangle> \<in> r \<and> \<langle>b,c\<rangle> \<in> r"
    using def_of_strict_ver by simp
  with A1 have "\<langle>a,c\<rangle> \<in> r" by (rule Fol1_L3)
  moreover
  { assume "a=c"
    with I have "\<langle>a,b\<rangle> \<in> r" and "\<langle>b,a\<rangle> \<in> r" by auto
    with A2 have "a=b" by (rule Fol1_L4)
    with A3 A4 have False using def_of_strict_ver by simp
  } then have "a\<noteq>c" by auto
  ultimately have  "\<langle>a,c\<rangle> \<in> StrictVersion(r)"
    using def_of_strict_ver by simp
  with A3 show ?thesis by simp
qed

text\<open>If an antisymmetric relation is transitive, 
  then the strict version is also transitive.\<close>

lemma strict_of_transB: 
  assumes A1: "trans(r)" and A2: "antisym(r)"
  shows "trans(StrictVersion(r))"
proof -
  let ?s = "StrictVersion(r)"
  from A1 A2 have 
    "\<forall> x y z. \<langle>x, y\<rangle> \<in> ?s \<and> \<langle>y, z\<rangle> \<in> ?s \<longrightarrow> \<langle>x, z\<rangle> \<in> ?s"
    using strict_of_transA by blast
  then show "trans(StrictVersion(r))" by (rule Fol1_L2)
qed

text\<open>The next lemma provides a condition that is satisfied by
  the strict version of a relation if the original relation 
  is a complete linear order.\<close>

lemma strict_of_compl: 
  assumes A1: "r \<subseteq> X\<times>X" and A2: "IsLinOrder(X,r)" and 
  A3: "r {is complete}" and 
  A4: "A\<subseteq>X"  "A\<noteq>0" and A5: "s = StrictVersion(r)" and 
  A6: "\<exists>u\<in>X. \<forall>y\<in>A. \<langle>y,u\<rangle> \<in> s"
  shows 
  "\<exists>x\<in>X. ( \<forall>y\<in>A. \<langle>x,y\<rangle> \<notin> s ) \<and> (\<forall>y\<in>X. \<langle>y,x\<rangle> \<in> s \<longrightarrow> (\<exists>z\<in>A. \<langle>y,z\<rangle> \<in> s))"
proof -
  let ?x = "Supremum(r,A)"
  from A2 have I: "antisym(r)" using IsLinOrder_def
    by simp
  moreover from A5 A6 have "\<exists>u\<in>X. \<forall>y\<in>A. \<langle>y,u\<rangle> \<in> r"
    using def_of_strict_ver by auto
  moreover note A1 A3 A4 
  ultimately have II: "?x \<in> X"   "\<forall>y\<in>A. \<langle>y,?x\<rangle> \<in> r"
    using Order_ZF_5_L7 by auto
  then have III: "\<exists>x\<in>X. \<forall>y\<in>A. \<langle>y,x\<rangle> \<in> r" by auto
  from A5 I II have "?x \<in> X"   "\<forall>y\<in>A. \<langle>?x,y\<rangle> \<notin> s"
    using geq_impl_not_less by auto
  moreover from A1 A2 A3 A4 A5 III have 
    "\<forall>y\<in>X. \<langle>y,?x\<rangle> \<in> s \<longrightarrow> (\<exists>z\<in>A. \<langle>y,z\<rangle> \<in> s)"
    using def_of_strict_ver Order_ZF_5_L8 by simp
  ultimately show
    "\<exists>x\<in>X. ( \<forall>y\<in>A. \<langle>x,y\<rangle> \<notin> s ) \<and> (\<forall>y\<in>X. \<langle>y,x\<rangle> \<in> s \<longrightarrow> (\<exists>z\<in>A. \<langle>y,z\<rangle> \<in> s))"
    by auto
qed

text\<open>Strict version of a relation on a set is a relation on that
  set.\<close>

lemma strict_ver_rel: assumes A1: "r \<subseteq> A\<times>A"
  shows "StrictVersion(r) \<subseteq> A\<times>A"
  using assms StrictVersion_def by auto

end
