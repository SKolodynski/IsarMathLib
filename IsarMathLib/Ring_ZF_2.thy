(*
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2022  Daniel de la Concepcion

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

section \<open>Rings - Ideals\<close>

theory Ring_ZF_2 imports Ring_ZF Group_ZF_2 Finite_ZF Finite1 Cardinal_ZF Semigroup_ZF

begin

text\<open>This section defines the concept of a ring ideal, and
defines some basic concepts and types, finishing with the theorem
that shows that the quotient of the additive group by the ideal
is actually a full ring.\<close>

subsection\<open>Ideals\<close>

text\<open>In ring theory ideals are special subsets of a ring that play a similar role 
  as normal subgroups in the group theory. \<close>

text\<open>An ideal is a subgroup of the additive group of the ring, which
  is closed by left and right multiplication by any ring element.\<close>

definition (in ring0) Ideal ("_\<triangleleft>R") where
  "I \<triangleleft>R \<equiv> (\<forall>x\<in>I. \<forall>y\<in>R. y\<cdot>x\<in>I \<and> x\<cdot>y\<in>I) \<and> IsAsubgroup(I,A)"

text\<open>To write less during proofs, we will write \<open>\<I>\<close> to denote 
  the set of ideals of the ring $R$. \<close>

abbreviation (in ring0) ideals ("\<I>") where "\<I> \<equiv> {J\<in>Pow(R). J\<triangleleft>R}"

text\<open>The first examples of ideals are the whole ring and the zero ring:\<close>

lemma (in ring0) ring_self_ideal:
  shows "R \<triangleleft>R"
  using add_group.group_self_subgroup Ring_ZF_1_L4(3)
  unfolding Ideal_def by simp

text\<open>The singleton containing zero is and ideal.\<close>

lemma (in ring0) zero_ideal:
  shows "{\<zero>} \<triangleleft>R" unfolding Ideal_def
  using Ring_ZF_1_L6 add_group.unit_singl_subgr by auto

text\<open>An ideal is s subset of the the ring.\<close>

lemma (in ring0) ideal_dest_subset:
  assumes "I \<triangleleft>R" 
  shows "I \<subseteq> R" using assms add_group.group0_3_L2 
  unfolding Ideal_def by auto

text\<open>Ideals are closed with respect to the ring addition.\<close>

lemma (in ring0) ideal_dest_sum:
  assumes "I \<triangleleft>R" "x\<in>I" "y\<in>I"
  shows "x\<ra>y \<in>I" using assms add_group.group0_3_L6 
  unfolding Ideal_def by auto

text\<open>Ideals are closed with respect to the ring multiplication.\<close>

lemma (in ring0) ideal_dest_mult:
  assumes "I \<triangleleft>R" "x\<in>I" "y\<in>R"
  shows "x\<cdot>y \<in>I" "y\<cdot>x \<in>I" using assms unfolding Ideal_def by auto

text\<open>Ideals are closed with respect to taking the opposite in the ring.\<close>

lemma (in ring0) ideal_dest_minus:
  assumes "I \<triangleleft>R" "x\<in>I"
  shows "(\<rm>x) \<in> I" 
  using assms add_group.group0_3_T3A unfolding Ideal_def by auto

text\<open>Every ideals contains zero.\<close>

lemma (in ring0) ideal_dest_zero:
  assumes "I \<triangleleft>R"
  shows "\<zero> \<in> I" 
  using assms add_group.group0_3_L5 unfolding Ideal_def by auto

text\<open>If the rules are satisfied, then we have an ideal\<close>

theorem (in ring0) ideal_intro:
  assumes "\<forall>x\<in>I. \<forall>y\<in>I. x\<ra>y\<in>I" 
    "\<forall>x\<in>I. \<forall>y\<in>R. x\<cdot>y \<in>I" 
    "\<forall>x\<in>I. \<forall>y\<in>R. y\<cdot>x \<in>I"
    "I \<subseteq> R" "I\<noteq>0"
  shows "I\<triangleleft>R"
proof-
  note assms(4) moreover
  have "I {is closed under} A" unfolding IsOpClosed_def using assms(1) by auto moreover
  note assms(5) moreover
  {
    fix x assume x:"x\<in>I"
    then have "(\<rm>x)\<in>R" using assms(4) Ring_ZF_1_L3(1) by auto
    then have "(\<rm>x) = \<one>\<cdot>(\<rm>x)" using Ring_ZF_1_L3(6) by auto
    then have "(\<rm>x) = \<rm>(\<one>\<cdot>x)" using Ring_ZF_1_L7(2)
      x assms(4) Ring_ZF_1_L2(2) by auto
    then have "(\<rm>x) = (\<rm>\<one>)\<cdot>x" using Ring_ZF_1_L7(1)
      x assms(4) Ring_ZF_1_L2(2) by auto
    moreover have "(\<rm>\<one>)\<in>R" using Ring_ZF_1_L2(2) Ring_ZF_1_L3(1) by auto
    ultimately have "(\<rm>x) \<in>I" using assms(3) x by auto
  }
  then have "\<forall>x\<in>I. GroupInv(R, A) ` x \<in> I" by auto ultimately
  have "IsAsubgroup(I,A)" using add_group.group0_3_T3 by auto
  moreover
  {
    fix x y assume "x\<in>I" "y\<in>R"
    then have "y \<cdot> x \<in> I \<and> x \<cdot> y \<in> I" using assms(2,3) by auto
  }
  then have "\<forall>x\<in>I. \<forall>y\<in>R. y \<cdot> x \<in> I \<and> x \<cdot> y \<in> I" by auto
  ultimately show ?thesis unfolding Ideal_def by auto
qed

text\<open>The simplest way to obtain an ideal from others is the intersection,
  since the intersection of arbitrary collection of ideals is an ideal.\<close>

theorem (in ring0) intersection_ideals:
  assumes "\<forall>J\<in>\<J>. (J \<triangleleft>R)" "\<J> \<noteq> 0"
  shows "(\<Inter>\<J>)  \<triangleleft>R"
  using assms ideal_dest_mult add_group.subgroup_inter
  unfolding Ideal_def by auto

text\<open>In particular, intersection of two ideals is an ideal.\<close>

corollary (in ring0) inter_two_ideals: assumes "I\<triangleleft>R" "J\<triangleleft>R"
  shows "(I\<inter>J) \<triangleleft>R"
proof -
  let ?\<J> = "{I,J}"
  from assms have "\<forall>J\<in>?\<J>. (J \<triangleleft>R)" and "?\<J> \<noteq> 0" by simp_all
  then have "(\<Inter>?\<J>)  \<triangleleft>R" using intersection_ideals by blast
  thus ?thesis by simp
qed

text\<open>From any set, we may construct the minimal ideal containing that set\<close>

definition (in ring0) generatedIdeal ("\<langle>_\<rangle>\<^sub>I")
  where "X\<subseteq>R \<Longrightarrow> \<langle>X\<rangle>\<^sub>I \<equiv> \<Inter>{I\<in>\<I>. X \<subseteq> I}"

text\<open>The ideal generated by a set is an ideal\<close>

corollary (in ring0) generated_ideal_is_ideal:
  assumes "X\<subseteq>R" shows "\<langle>X\<rangle>\<^sub>I \<triangleleft>R" 
proof -
  let ?\<J> = "{I\<in>\<I>. X \<subseteq> I}"
  have "\<forall>J \<in> ?\<J>. (J \<triangleleft>R)" by auto
  with assms have "(\<Inter>?\<J>)  \<triangleleft>R" using ring_self_ideal intersection_ideals by blast
  with assms show ?thesis using generatedIdeal_def by simp
qed
  
text\<open>The ideal generated by a set is contained in any ideal containing the set.\<close>

corollary (in ring0) generated_ideal_small:
  assumes "X\<subseteq>I" "I \<triangleleft>R"
  shows "\<langle>X\<rangle>\<^sub>I \<subseteq> I"
proof -
  from assms have "I\<in>{J\<in>Pow(R). J \<triangleleft>R \<and> X\<subseteq>J}" 
    using ideal_dest_subset by auto
  then have "\<Inter>{J\<in>Pow(R). J \<triangleleft>R \<and> X\<subseteq>J} \<subseteq> I" by auto 
  moreover from assms have "X\<subseteq> R" using ideal_dest_subset by auto
  ultimately show "\<langle>X\<rangle>\<^sub>I \<subseteq> I" using generatedIdeal_def by auto
qed

text\<open>The ideal generated by a set contains the set.\<close>

corollary (in ring0) generated_ideal_contains_set:
  assumes "X\<subseteq>R" shows "X\<subseteq>\<langle>X\<rangle>\<^sub>I"
  using assms ring_self_ideal generatedIdeal_def by auto

text\<open>To be able to show properties of an ideal generated by a set, we
  have the following induction result\<close>

lemma (in ring0) induction_generated_ideal:
  assumes
    "X\<noteq>0"
    "X\<subseteq>R"
    "\<forall>y\<in>R. \<forall>z\<in>R. \<forall>q\<in>\<langle>X\<rangle>\<^sub>I. P(q) \<longrightarrow> P(y\<cdot>q\<cdot>z)" 
    "\<forall>y\<in>R. \<forall>z\<in>R. P(y) \<and> P(z) \<longrightarrow> P(y\<ra>z)"  
    "\<forall>x\<in>X. P(x)"
  shows "\<forall>y\<in>\<langle>X\<rangle>\<^sub>I. P(y)"
proof -
  let ?J = "{m\<in>\<langle>X\<rangle>\<^sub>I. P(m)}"
  from assms(2,5) have "X\<subseteq>?J" 
    using generated_ideal_contains_set by auto
  from assms(2) have "?J\<subseteq>R" 
    using generated_ideal_is_ideal ideal_dest_subset by auto 
  moreover
  { fix y z assume "y\<in>R" "z\<in>?J"
    then have "y\<in>R" "\<one>\<in>R" "z\<in>\<langle>X\<rangle>\<^sub>I" "P(z)"
      using Ring_ZF_1_L2(2) by simp_all
    with assms(3) have "P(y\<cdot>z\<cdot>\<one>)" and "P(\<one>\<cdot>z\<cdot>y)" by simp_all
    with \<open>?J\<subseteq>R\<close> \<open>y\<in>R\<close> \<open>z\<in>?J\<close> have "P(y\<cdot>z)" and "P(z\<cdot>y)"
      using Ring_ZF_1_L4(3) Ring_ZF_1_L3(5,6) by auto
    with assms(2) \<open>z\<in>\<langle>X\<rangle>\<^sub>I\<close> \<open>y\<in>R\<close> have "y\<cdot>z\<in>?J" "z\<cdot>y\<in>?J"
      using ideal_dest_mult generated_ideal_is_ideal
      by auto
  } hence "\<forall>x\<in>?J. \<forall>y\<in>R. y \<cdot> x \<in> ?J \<and> x \<cdot> y \<in> ?J" by auto
  moreover have "IsAsubgroup(?J,A)"
  proof -
    from assms(1) \<open>X\<subseteq>?J\<close> \<open>?J\<subseteq>R\<close> have "?J\<noteq>0" and "?J\<subseteq>R" 
      by auto
    moreover
    { fix x y assume as: "x\<in>?J" "y\<in>?J"
      with assms(2,4) have "P(x\<ra>y)" 
        using ideal_dest_subset generated_ideal_is_ideal 
        by blast
      with assms(2) \<open>x\<in>?J\<close> \<open>y\<in>?J\<close> have "x\<ra>y \<in> ?J"
        using generated_ideal_is_ideal ideal_dest_sum 
        by auto
    } then have "?J {is closed under} A" 
      unfolding IsOpClosed_def by auto
    moreover
    { fix x assume "x\<in>?J"
      with \<open>?J\<subseteq>R\<close> have "x\<in>\<langle>X\<rangle>\<^sub>I" "x\<in>R" "P(x)" by auto
      with assms(3) have "P((\<rm>\<one>)\<cdot>x\<cdot>\<one>)"
        using Ring_ZF_1_L2(2) Ring_ZF_1_L3(1) by simp
      with assms(2) \<open>x\<in>\<langle>X\<rangle>\<^sub>I\<close> \<open>x\<in>R\<close> have "(\<rm>x)\<in>?J"
        using Ring_ZF_1_L3(1,5,6) Ring_ZF_1_L7(1) Ring_ZF_1_L2(2)
          generated_ideal_is_ideal ideal_dest_minus by auto
    } hence "\<forall>x\<in>?J. (\<rm>x)\<in>?J" by simp
    ultimately show "IsAsubgroup(?J,A)" 
      by (rule add_group.group0_3_T3)
  qed
  ultimately have "?J\<triangleleft>R" unfolding Ideal_def by auto
  with \<open>X\<subseteq>?J\<close> show ?thesis using generated_ideal_small by auto
qed

text\<open>An ideal is very particular with the elements it may contain. 
  If it contains the neutral element of multiplication then 
  it is in fact the whole ring and not a proper subset. \<close>

theorem (in ring0) ideal_with_one:
  assumes "I\<triangleleft>R" "\<one>\<in>I" shows "I = R"
  using assms ideal_dest_subset ideal_dest_mult(2) Ring_ZF_1_L3(5)
  by force

text\<open>The only ideal containing an invertible element is the whole ring. \<close>

theorem (in ring0) ideal_with_unit:
  assumes "I\<triangleleft>R" "x\<in>I" "\<exists>y\<in>R. y\<cdot>x = \<one> \<or> x\<cdot>y =\<one>"
  shows "I = R"
  using assms ideal_with_one unfolding Ideal_def by blast

text\<open>The previous result drives us to define what a maximal ideal would be:
  an ideal such that any bigger ideal is the whole ring:\<close>

definition (in ring0) maximalIdeal ("_\<triangleleft>\<^sub>mR") where
  "I\<triangleleft>\<^sub>mR \<equiv> I\<triangleleft>R \<and> I\<noteq>R \<and> (\<forall>J\<in>\<I>. I\<subseteq>J \<and> J\<noteq>R \<longrightarrow> I=J)"

text\<open>Before delving into maximal ideals, lets define some operation on ideals
  that are useful when formulating some proofs.
  The product ideal of ideals $I,J$ is the smallest ideal containing all
  products of elements from $I$ and $J$: \<close>

definition (in ring0) productIdeal (infix "\<cdot>\<^sub>I" 90) where
  "I\<triangleleft>R \<Longrightarrow> J\<triangleleft>R  \<Longrightarrow> I\<cdot>\<^sub>IJ \<equiv> \<langle>M``(I\<times>J)\<rangle>\<^sub>I"

text\<open>The sum ideal of ideals is the smallest ideal containg both $I$ and $J$: \<close>

definition (in ring0) sumIdeal (infix "+\<^sub>I" 90) where
  "I\<triangleleft>R \<Longrightarrow> J\<triangleleft>R  \<Longrightarrow> I+\<^sub>IJ \<equiv> \<langle>I\<union>J\<rangle>\<^sub>I"

text\<open>Sometimes we may need to sum an arbitrary number
  of ideals, and not just two.\<close>

definition(in ring0) sumArbitraryIdeals ("\<oplus>\<^sub>I_" 90) where
  "\<J> \<subseteq> \<I> \<Longrightarrow> \<oplus>\<^sub>I\<J> \<equiv> \<langle>\<Union>\<J>\<rangle>\<^sub>I"

text\<open>Each component of the sum of ideals is contained in the sum.\<close>

lemma (in ring0) comp_in_sum_ideals:
  assumes "I\<triangleleft>R" and "J\<triangleleft>R"
  shows "I \<subseteq> I+\<^sub>IJ" and "J \<subseteq> I+\<^sub>IJ" and "I\<union>J \<subseteq> I+\<^sub>IJ"
proof - 
  from assms have "I\<union>J \<subseteq> R" using ideal_dest_subset
    by auto
  with assms show "I \<subseteq> I+\<^sub>IJ" "J \<subseteq> I+\<^sub>IJ" "I\<union>J \<subseteq> I+\<^sub>IJ"
    using generated_ideal_contains_set sumIdeal_def 
    by auto
qed

text\<open>Every element in the arbitrary sum of ideals
  is generated by only a finite subset of those ideals\<close>

lemma (in ring0) sum_ideals_finite_sum:
  assumes "\<J> \<subseteq> \<I>" "s\<in>(\<oplus>\<^sub>I\<J>)"
  shows "\<exists>\<T>\<in>FinPow(\<J>). s\<in>(\<oplus>\<^sub>I\<T>)"
proof -
  { assume "\<Union>\<J>=0"
    then have "\<J>\<subseteq>{0}" by auto
    with assms(2) have ?thesis
      using subset_Finite nat_into_Finite
      unfolding FinPow_def by blast
  }
  moreover
  { let ?P = "\<lambda>t. \<exists>\<T>\<in>FinPow(\<J>). t\<in>(\<oplus>\<^sub>I\<T>)"
    assume "\<Union>\<J>\<noteq>0"
    moreover from assms(1) have "\<Union>\<J>\<subseteq>R" by auto
    moreover
    { fix y z q assume "?P(q)" "y\<in>R" "z\<in>R" "q\<in>\<langle>\<Union>\<J>\<rangle>\<^sub>I"
      then obtain \<T> where "\<T>\<in>FinPow(\<J>)" and "q \<in> \<oplus>\<^sub>I\<T>" 
        by auto
      from assms(1) \<open>\<T>\<in>FinPow(\<J>)\<close> have "\<Union>\<T> \<subseteq> R" "\<T>\<subseteq>\<I>" 
        unfolding FinPow_def by auto
      with \<open>q\<in>\<oplus>\<^sub>I\<T>\<close> \<open>y\<in>R\<close> \<open>z\<in>R\<close> have "y\<cdot>q\<cdot>z \<in> \<oplus>\<^sub>I\<T>"
        using generated_ideal_is_ideal sumArbitraryIdeals_def
        unfolding Ideal_def by auto
      with \<open>\<T>\<in>FinPow(\<J>)\<close> have "?P(y\<cdot>q \<cdot>z)" by auto
    } hence "\<forall>y\<in>R. \<forall>z\<in>R. \<forall>q\<in>\<langle>\<Union>\<J>\<rangle>\<^sub>I. ?P(q) \<longrightarrow> ?P(y\<cdot>q\<cdot>z)" 
      by auto 
    moreover
    { fix y z assume "?P(y)" "?P(z)"
      then obtain T\<^sub>y T\<^sub>z where T: "T\<^sub>y\<in>FinPow(\<J>)" "y \<in> \<oplus>\<^sub>IT\<^sub>y"
        "T\<^sub>z\<in>FinPow(\<J>)" "z \<in> \<oplus>\<^sub>IT\<^sub>z" by auto
      from T(1,3) have A: "T\<^sub>y\<union>T\<^sub>z \<in> FinPow(\<J>)" 
        unfolding FinPow_def using Finite_Un by auto
      with assms(1) have "\<Union>T\<^sub>y \<subseteq> \<Union>(T\<^sub>y\<union>T\<^sub>z)" "\<Union>T\<^sub>z \<subseteq> \<Union>(T\<^sub>y\<union>T\<^sub>z)" and 
        sub: "\<Union>(T\<^sub>y\<union>T\<^sub>z) \<subseteq> R"
        unfolding FinPow_def by auto
      then have "\<Union>(T\<^sub>y\<union>T\<^sub>z) \<subseteq> \<langle>\<Union>(T\<^sub>y\<union>T\<^sub>z)\<rangle>\<^sub>I" 
        using generated_ideal_contains_set by simp
      hence "\<Union>T\<^sub>y \<subseteq> \<langle>\<Union>(T\<^sub>y\<union>T\<^sub>z)\<rangle>\<^sub>I" "\<Union>T\<^sub>z \<subseteq> \<langle>\<Union>(T\<^sub>y\<union>T\<^sub>z)\<rangle>\<^sub>I" by auto
      with sub have "\<langle>\<Union>T\<^sub>y\<rangle>\<^sub>I\<subseteq> \<langle>\<Union>(T\<^sub>y\<union>T\<^sub>z)\<rangle>\<^sub>I" "\<langle>\<Union>T\<^sub>z\<rangle>\<^sub>I \<subseteq> \<langle>\<Union>(T\<^sub>y\<union>T\<^sub>z)\<rangle>\<^sub>I"
        using generated_ideal_small generated_ideal_is_ideal
        by auto
      moreover from assms(1) T(1,3) have "T\<^sub>y\<subseteq>\<I>" "T\<^sub>z\<subseteq>\<I>" 
        unfolding FinPow_def by auto
      moreover note T(2,4)
      ultimately have "y \<in> \<langle>\<Union>(T\<^sub>y\<union>T\<^sub>z)\<rangle>\<^sub>I" "z \<in> \<langle>\<Union>(T\<^sub>y\<union>T\<^sub>z)\<rangle>\<^sub>I"
        using sumArbitraryIdeals_def sumArbitraryIdeals_def 
        by auto
      with \<open>\<Union>(T\<^sub>y\<union>T\<^sub>z) \<subseteq> R\<close> have "y\<ra>z \<in> \<langle>\<Union>(T\<^sub>y\<union>T\<^sub>z)\<rangle>\<^sub>I" 
        using generated_ideal_is_ideal ideal_dest_sum by auto
      moreover
      from \<open>T\<^sub>y\<subseteq>\<I>\<close> \<open>T\<^sub>z\<subseteq>\<I>\<close> have "T\<^sub>y\<union>T\<^sub>z \<subseteq> \<I>" by auto
      then have "(\<oplus>\<^sub>I(T\<^sub>y\<union>T\<^sub>z)) = \<langle>\<Union>(T\<^sub>y\<union>T\<^sub>z)\<rangle>\<^sub>I" 
        using sumArbitraryIdeals_def by auto
      ultimately have "y\<ra>z \<in> (\<oplus>\<^sub>I(T\<^sub>y\<union>T\<^sub>z))" by simp
      with A have "?P(y\<ra>z)" by auto
    } hence "\<forall>y\<in>R. \<forall>z\<in>R. ?P(y) \<and> ?P(z) \<longrightarrow> ?P(y \<ra> z)" 
      by auto
    moreover 
    { fix t assume "t\<in>\<Union>\<J>"
      then obtain J where "t\<in>J" "J\<in>\<J>" by auto
      then have "{J}\<in>FinPow(\<J>)" unfolding FinPow_def
        using eqpoll_imp_Finite_iff nat_into_Finite
        by auto 
      moreover 
      from assms(1) \<open>J\<in>\<J>\<close> have "(\<oplus>\<^sub>I{J}) = \<langle>J\<rangle>\<^sub>I" 
        using sumArbitraryIdeals_def by auto
      with assms(1) \<open>t\<in>J\<close> \<open>J\<in>\<J>\<close> have "t\<in>(\<oplus>\<^sub>I{J})"
        using generated_ideal_contains_set by force
      ultimately have "?P(t)" by auto
    } hence "\<forall>t\<in>\<Union>\<J>. ?P(t)" by auto
    ultimately have "\<forall>t\<in>\<langle>\<Union>\<J>\<rangle>\<^sub>I. ?P(t)"
      by (rule induction_generated_ideal)
    with assms have ?thesis using sumArbitraryIdeals_def 
      by auto
  }
  ultimately show ?thesis by auto
qed

text\<open>By definition of product of ideals and of an ideal itself, it follows
  that the product of ideals is an ideal contained in the intersection\<close>

theorem (in ring0) product_in_intersection:
  assumes "I\<triangleleft>R" "J\<triangleleft>R"
  shows "I\<cdot>\<^sub>IJ \<subseteq> I\<inter>J" and "(I\<cdot>\<^sub>IJ)\<triangleleft>R" and "M``(I\<times>J) \<subseteq> I\<cdot>\<^sub>IJ"
proof -
  have "M``(I\<times>J) \<subseteq> I\<inter>J"
  proof
    fix x assume "x\<in>M``(I\<times>J)"
    then obtain y where "y\<in>I\<times>J" "\<langle>y,x\<rangle>\<in>M" unfolding image_def
      by auto
    then obtain y\<^sub>i y\<^sub>j where y: "y\<^sub>i\<in>I" "y\<^sub>j\<in>J" "\<langle>\<langle>y\<^sub>i,y\<^sub>j\<rangle>,x\<rangle> \<in> M" 
      by auto 
    from assms have "I\<subseteq>R" "J\<subseteq>R" using ideal_dest_subset by simp_all
    with ringAssum assms y show "x\<in>I\<inter>J"
      unfolding Ideal_def IsAring_def IsAmonoid_def IsAssociative_def
      using apply_equality by force
  qed
  with assms show "I\<cdot>\<^sub>IJ \<subseteq> I\<inter>J" 
    using productIdeal_def generated_ideal_small inter_two_ideals 
    by auto
  from assms \<open>M``(I\<times>J) \<subseteq> I\<inter>J\<close> have "M``(I\<times>J) \<subseteq> R" 
    using ideal_dest_subset by auto
  with assms show "(I\<cdot>\<^sub>IJ) \<triangleleft>R" and "M``(I\<times>J) \<subseteq> I\<cdot>\<^sub>IJ"
    using productIdeal_def generated_ideal_is_ideal 
      generated_ideal_contains_set by auto
qed

text\<open>We will show now that the sum of ideals is no more that the sum of 
  the ideal elements.\<close>

lemma (in ring0) sum_elements:
  assumes "I \<triangleleft>R" "J \<triangleleft>R" "x\<in>I" "y\<in>J"
  shows "x\<ra>y \<in> I+\<^sub>IJ"
proof -
  from assms(1,2) have "I\<union>J \<subseteq> R" using ideal_dest_subset 
    by auto
  with assms(3,4) have "x \<in> \<langle>I\<union>J\<rangle>\<^sub>I" "y \<in> \<langle>I\<union>J\<rangle>\<^sub>I"
    using generated_ideal_contains_set by auto
  with assms(1,2) \<open>I\<union>J \<subseteq> R\<close> show ?thesis
    using generated_ideal_is_ideal ideal_dest_subset ideal_dest_sum 
      sumIdeal_def by auto
qed

text\<open>For two ideals the set containing all sums of their elements is also an ideal.\<close>

lemma (in ring0) sum_elements_is_ideal:
  assumes "I \<triangleleft>R" "J \<triangleleft>R"
  shows "(A``(I\<times>J)) \<triangleleft>R"
proof -
  from assms have ij: "I\<times>J \<subseteq> R\<times>R" using ideal_dest_subset by auto
  have Aim: "A``(I\<times>J) \<subseteq> R" using add_group.group_oper_fun func1_1_L6(2) 
    by auto
  moreover
  { fix x y assume "x\<in>R" "y \<in> A``(I\<times>J)"
    from ij \<open>y\<in>A``(I\<times>J)\<close> obtain y\<^sub>i y\<^sub>j where 
      y: "y=y\<^sub>i\<ra>y\<^sub>j" "y\<^sub>i\<in>I" "y\<^sub>j\<in>J"
      using add_group.group_oper_fun func_imagedef by auto
    from \<open>x\<in>R\<close> y ij have 
      "x\<cdot>y = (x\<cdot>y\<^sub>i)\<ra>(x\<cdot>y\<^sub>j)" and "y\<cdot>x = (y\<^sub>i\<cdot>x)\<ra>(y\<^sub>j\<cdot>x)"
      using ring_oper_distr add_group.group_op_closed by auto
    moreover from assms \<open>x\<in>R\<close> y(2,3) have 
      "x\<cdot>y\<^sub>i \<in> I" "y\<^sub>i\<cdot>x \<in> I" "x\<cdot>y\<^sub>j \<in> J" "y\<^sub>j\<cdot>x \<in> J"
      using  ideal_dest_mult by auto
    ultimately have "x\<cdot>y\<in>A``(I\<times>J)" "y\<cdot>x\<in>A``(I\<times>J)"
      using ij add_group.group_oper_fun func_imagedef by auto
  } hence "\<forall>x\<in>A``(I\<times>J). \<forall>y\<in>R. y \<cdot> x \<in> A``(I\<times>J) \<and> x \<cdot> y \<in> A``(I\<times>J)" 
    by auto
  moreover have "IsAsubgroup(A``(I\<times>J),A)"
  proof -
    from assms ij have "\<zero>\<ra>\<zero> \<in> A `` (I \<times> J)" 
      using add_group.group_oper_fun ideal_dest_zero func_imagedef 
      by auto
    with Aim have "A``(I \<times> J) \<noteq> 0" and "A``(I \<times> J) \<subseteq> R" 
      by auto
    moreover 
    { fix x y assume xy: "x \<in> A``(I \<times> J)" "y \<in> A``(I \<times> J)"
      with ij obtain x\<^sub>i x\<^sub>j y\<^sub>i y\<^sub>j where 
        "x\<^sub>i\<in>I" "x\<^sub>j\<in>J" "x=x\<^sub>i\<ra>x\<^sub>j" "y\<^sub>i\<in>I" "y\<^sub>j\<in>J" "y=y\<^sub>i\<ra>y\<^sub>j"
        using add_group.group_oper_fun func_imagedef by auto
      from \<open>x\<in>A``(I \<times> J)\<close> \<open>A``(I \<times> J)\<subseteq>R\<close> have "x\<in>R" by auto
      from assms \<open>x\<^sub>i\<in>I\<close> \<open>x\<^sub>j\<in>J\<close> \<open>y\<^sub>i\<in>I\<close> \<open>y\<^sub>j\<in>J\<close> 
        have "x\<^sub>i\<in>R" "x\<^sub>j\<in>R" "y\<^sub>i\<in>R" "y\<^sub>j\<in>R" 
          using ideal_dest_subset by auto
      from ij \<open>x\<in>R\<close> \<open>y\<^sub>i\<in>R\<close> \<open>y\<^sub>j\<in>R\<close> \<open>y=y\<^sub>i\<ra>y\<^sub>j\<close> 
        have "x\<ra>y = (x\<ra>y\<^sub>i)\<ra>y\<^sub>j" 
        using Ring_ZF_1_L10(1) by simp
      with \<open>x=x\<^sub>i\<ra>x\<^sub>j\<close> \<open>x\<^sub>i\<in>R\<close> \<open>x\<^sub>j\<in>R\<close> \<open>y\<^sub>i\<in>R\<close> \<open>y\<^sub>j\<in>R\<close> 
        have "x\<ra>y = (x\<^sub>i\<ra>y\<^sub>i)\<ra>(x\<^sub>j\<ra>y\<^sub>j)"
        using Ring_ZF_2_L5(4) by simp
      moreover from assms \<open>x\<^sub>i\<in>I\<close> \<open>x\<^sub>j\<in>J\<close> \<open>y\<^sub>i\<in>I\<close> \<open>y\<^sub>j\<in>J\<close>
        have "x\<^sub>i\<ra>y\<^sub>i \<in> I" and "x\<^sub>j\<ra>y\<^sub>j \<in> J"
        using ideal_dest_sum by auto
      ultimately have "x\<ra>y \<in> A``(I\<times>J)" 
        using ij add_group.group_oper_fun func_imagedef 
        by auto
    } then have "A``(I \<times> J) {is closed under} A" 
      unfolding IsOpClosed_def by auto
    moreover
    { fix x assume "x \<in> A``(I \<times> J)"
      with ij obtain x\<^sub>i x\<^sub>j where "x\<^sub>i\<in>I" "x\<^sub>j\<in>J" "x=x\<^sub>i\<ra>x\<^sub>j" 
        using add_group.group_oper_fun func_imagedef by auto
      with assms have "(\<rm>x) = (\<rm>x\<^sub>i)\<rs>x\<^sub>j" 
        using Ring_ZF_1_L9(2) ideal_dest_subset by auto
      moreover from assms \<open>x\<^sub>i\<in>I\<close> \<open>x\<^sub>j\<in>J\<close> 
      have "(\<rm>x\<^sub>i)\<in>I" and "(\<rm>x\<^sub>j)\<in>J"
        using ideal_dest_minus by simp_all
      ultimately have "(\<rm>x) \<in> A``(I\<times>J)" 
        using add_group.group_oper_fun ij func_imagedef by auto
    } hence "\<forall>x\<in>A``(I \<times> J). (\<rm> x) \<in> A``(I \<times> J)" by auto
    ultimately show ?thesis using add_group.group0_3_T3
      by simp
  qed
  ultimately show "(A``(I \<times> J)) \<triangleleft>R" unfolding Ideal_def by auto
qed

text\<open>The set of all sums of elements of two ideals is their sum ideal i.e.
  the ideal generated by their union. \<close>

corollary (in ring0) sum_ideals_is_sum_elements:
  assumes  "I \<triangleleft>R" "J \<triangleleft>R"
  shows "(A``(I \<times> J)) = I+\<^sub>IJ"
proof
  from assms have ij: "I\<subseteq>R" "J\<subseteq>R" using ideal_dest_subset 
    by auto
  then have ij_prd: "I\<times>J \<subseteq> R\<times>R" by auto
  with assms show "A``(I \<times> J) \<subseteq> I +\<^sub>I J" 
    using add_group.group_oper_fun sum_elements func_imagedef 
    by auto
  { fix x assume "x\<in>I"
    with ij(1) have "x=x\<ra>\<zero>" using Ring_ZF_1_L3(3) by auto
    with assms(2) ij_prd \<open>x\<in>I\<close> have "x\<in>A `` (I \<times> J)" 
      using add_group.group0_3_L5 add_group.group_oper_fun func_imagedef
      unfolding Ideal_def by auto
  } hence "I \<subseteq> A``(I \<times> J)" by auto 
  moreover
  { fix x assume x: "x\<in>J"
    with ij(2) have "x=\<zero>\<ra>x" using Ring_ZF_1_L3(4) by auto
    with assms(1) ij_prd \<open>x\<in>J\<close> have "x \<in> A``(I \<times> J)" 
      using add_group.group0_3_L5 add_group.group_oper_fun func_imagedef
      unfolding Ideal_def by auto
  } hence "J \<subseteq> A``(I \<times> J)" by auto
  ultimately have "I\<union>J \<subseteq> A``(I \<times> J)" by auto
  with assms show "I+\<^sub>IJ \<subseteq> A``(I \<times> J)" 
    using generated_ideal_small sum_elements_is_ideal sumIdeal_def 
    by auto
qed

text\<open>The sum ideal of two ideals is indeed an ideal.\<close>

corollary (in ring0) sum_ideals_is_ideal:
  assumes "I \<triangleleft>R" "J \<triangleleft>R"
  shows "(I+\<^sub>IJ) \<triangleleft>R" using assms sum_ideals_is_sum_elements
  sum_elements_is_ideal ideal_dest_subset by auto

text\<open>The operation of taking the sum of ideals is commutative.\<close>

corollary (in ring0) sum_ideals_commute:
  assumes "I\<triangleleft>R" "J\<triangleleft>R"
  shows "(I +\<^sub>I J) = (J +\<^sub>I I)"
proof -
  have "I \<union> J = J \<union> I" by auto
  with assms show ?thesis using sumIdeal_def by auto
qed

text\<open>Now that we know what the product of ideals is, 
  we are able to define what a prime ideal is:\<close>

definition (in ring0) primeIdeal ("_\<triangleleft>\<^sub>pR") where
  "P\<triangleleft>\<^sub>pR \<equiv> P\<triangleleft>R \<and> P\<noteq>R \<and> (\<forall>I\<in>\<I>. \<forall>J\<in>\<I>. I\<cdot>\<^sub>IJ \<subseteq> P \<longrightarrow> (I\<subseteq>P \<or> J\<subseteq>P))"

text\<open>Any maximal ideal is a prime ideal.\<close>

theorem (in ring0) maximal_is_prime:
  assumes "Q\<triangleleft>\<^sub>mR" shows "Q\<triangleleft>\<^sub>pR"
proof -
  have "Q\<in>\<I>" using assms ideal_dest_subset 
    unfolding maximalIdeal_def by auto
  { fix I J assume "I\<in>\<I>" "J\<in>\<I>" "I\<cdot>\<^sub>IJ \<subseteq> Q"
    { assume K: "\<not>(I\<subseteq>Q)" "\<not>(J\<subseteq>Q)"
      from \<open>\<not>(I\<subseteq>Q)\<close> obtain x where "x\<in>I-Q" by auto
      with \<open>I\<in>\<I>\<close> have "x\<in>R" using ideal_dest_subset by auto
      from \<open>I\<in>\<I>\<close> \<open>J\<in>\<I>\<close> have sub: "I\<times>J \<subseteq> R\<times>R" by auto
      let ?K = "\<langle>Q\<union>{x}\<rangle>\<^sub>I"
      from \<open>Q\<in>\<I>\<close> \<open>x\<in>R\<close> have "Q\<union>{x} \<subseteq> R" by auto
      then have "Q\<subseteq>?K" and "x\<in>?K" using generated_ideal_contains_set
        by auto
      with \<open>x\<in>I-Q\<close> have "Q\<subseteq>?K" "?K\<noteq>Q" by auto
      from \<open>Q\<union>{x} \<subseteq> R\<close> have "?K\<in>\<I>" 
        using ideal_dest_subset generated_ideal_is_ideal by blast
      with assms \<open>Q\<subseteq>?K\<close> \<open>?K\<noteq>Q\<close> have "?K=R" unfolding maximalIdeal_def
        by auto
      let ?P = "Q+\<^sub>II"
      from \<open>Q\<in>\<I>\<close> \<open>I\<in>\<I>\<close> \<open>x\<in>I-Q\<close> have "Q\<union>{x} \<subseteq> Q+\<^sub>II"
        using comp_in_sum_ideals(3) by auto
      with \<open>Q\<in>\<I>\<close> \<open>I\<in>\<I>\<close> have "?K \<subseteq> Q+\<^sub>II" "Q+\<^sub>II \<subseteq> R"
        using sum_ideals_is_ideal generated_ideal_small ideal_dest_subset
        by simp_all
      with \<open>?K=R\<close> have "\<one>\<in>Q+\<^sub>II " using Ring_ZF_1_L2(2) by auto
      with \<open>I\<in>\<I>\<close> \<open>Q\<in>\<I>\<close> have "\<one>\<in>A``(Q\<times>I)"
        using sum_ideals_is_sum_elements by auto
      moreover from \<open>I\<in>\<I>\<close> \<open>Q\<in>\<I>\<close> have "Q\<times>I \<subseteq> R\<times>R" by auto
      ultimately obtain x\<^sub>m x\<^sub>i where "x\<^sub>m\<in>Q" "x\<^sub>i\<in>I" "\<one>=x\<^sub>m\<ra>x\<^sub>i"
        using func_imagedef add_group.group_oper_fun by auto
      { fix y assume "y\<in>J"
        with \<open>x\<^sub>m\<in>Q\<close> \<open>x\<^sub>i\<in>I\<close> \<open>Q\<in>\<I>\<close> \<open>I\<in>\<I>\<close> \<open>J\<in>\<I>\<close> 
        have "y\<in>R" "x\<^sub>m\<in>R" "x\<^sub>i\<in>R" by auto
        with \<open>y\<in>J\<close> \<open>J\<in>\<I>\<close> \<open>\<one>=x\<^sub>m\<ra>x\<^sub>i\<close> have "(x\<^sub>m\<cdot>y)\<ra>(x\<^sub>i\<cdot>y) = y"
          using Ring_ZF_1_L3(6) ring_oper_distr(2) by simp
        from \<open>Q\<in>\<I>\<close> \<open>x\<^sub>m\<in>Q\<close>  \<open>y\<in>R\<close> have "x\<^sub>m\<cdot>y\<in>Q" 
          using ideal_dest_mult(1) by auto
        from sub \<open>y\<in>J\<close> \<open>x\<^sub>i\<in>I\<close> \<open>I\<in>\<I>\<close> \<open>J\<in>\<I>\<close> \<open>I\<cdot>\<^sub>IJ\<subseteq>Q\<close> have "x\<^sub>i\<cdot>y\<in>Q"  
          using func_imagedef mult_monoid.monoid_oper_fun 
            product_in_intersection(3) by force
        with \<open>Q\<in>\<I>\<close> \<open>(x\<^sub>m\<cdot>y)\<ra>(x\<^sub>i\<cdot>y) = y\<close> \<open>x\<^sub>m\<cdot>y\<in>Q\<close> have "y\<in>Q"
          using ideal_dest_sum by force
      } hence "J \<subseteq> Q" by auto
      with K have False by auto
    } hence "(I\<subseteq>Q)\<or>(J\<subseteq>Q)" by auto
  } hence "\<forall>I\<in>\<I>. \<forall>J\<in>\<I>. I \<cdot>\<^sub>I J \<subseteq> Q \<longrightarrow> (I \<subseteq> Q \<or> J \<subseteq> Q)" by auto
  with assms show ?thesis unfolding maximalIdeal_def primeIdeal_def
    by auto
qed

text\<open>In case of non-commutative rings, the zero divisor concept is too constrictive.
  For that we define the following concept of a prime ring. Note that in case that
  our ring is commutative, this is equivalent to having no zero divisors 
  (there is no of that proof yet).\<close>

definition primeRing ("[_,_,_]{is a prime ring}") where
  "IsAring(R,A,M) \<Longrightarrow> [R,A,M]{is a prime ring} \<equiv> 
      (\<forall>x\<in>R. \<forall>y\<in>R. (\<forall>z\<in>R. M`\<langle>M`\<langle>x,z\<rangle>,y\<rangle> = TheNeutralElement(R,A)) \<longrightarrow> 
      x=TheNeutralElement(R,A) \<or> y=TheNeutralElement(R,A))"

text\<open>Prime rings appear when the zero ideal is prime.\<close>

lemma (in ring0) prime_ring_zero_prime_ideal:
  assumes "[R,A,M]{is a prime ring}" "R\<noteq>{\<zero>}"
  shows "{\<zero>} \<triangleleft>\<^sub>pR"
proof -
  {
    fix I J assume ij: "I\<in>\<I>" "J\<in>\<I>" "I\<cdot>\<^sub>IJ \<subseteq> {\<zero>}"
    from ij(1,2) have "I\<times>J \<subseteq> R\<times>R" by auto
    { assume "\<not>(I\<subseteq>{\<zero>})" "\<not>(J\<subseteq>{\<zero>})"
      then obtain x\<^sub>i x\<^sub>j where "x\<^sub>i\<noteq>\<zero>" "x\<^sub>j\<noteq>\<zero>" "x\<^sub>i\<in>I" "x\<^sub>j\<in>J" 
        by auto
      from ij(1,2) \<open>x\<^sub>i\<in>I\<close> \<open>x\<^sub>j\<in>J\<close> have "x\<^sub>i\<in>R" "x\<^sub>j\<in>R" by auto
      { fix u assume "u\<in>R"
        with \<open>I\<in>\<I>\<close> \<open>x\<^sub>i\<in>I\<close> \<open>x\<^sub>j\<in>J\<close> \<open>I\<times>J \<subseteq> R\<times>R\<close>
          have "x\<^sub>i\<cdot>u\<cdot>x\<^sub>j \<in> M``(I\<times>J)"
          using ideal_dest_mult(1) func_imagedef 
            mult_monoid.monoid_oper_fun by auto
        with ij have "x\<^sub>i\<cdot>u\<cdot>x\<^sub>j = \<zero>"
          using product_in_intersection(3) by blast
      } hence "\<forall>u\<in>R. x\<^sub>i\<cdot>u\<cdot>x\<^sub>j = \<zero>" by simp
      with ringAssum assms(1) \<open>x\<^sub>i\<in>R\<close> \<open>x\<^sub>j\<in>R\<close> \<open>x\<^sub>i\<noteq>\<zero>\<close> \<open>x\<^sub>j\<noteq>\<zero>\<close> 
        have False using primeRing_def by auto
    } hence "I\<subseteq>{\<zero>} \<or> J\<subseteq>{\<zero>}" by auto
  } hence "\<forall>I\<in>\<I>. \<forall>J\<in>\<I>. I \<cdot>\<^sub>I J \<subseteq> {\<zero>} \<longrightarrow> (I \<subseteq> {\<zero>} \<or> J \<subseteq> {\<zero>})" 
    by auto
  with assms(2) show ?thesis 
    using zero_ideal unfolding primeIdeal_def by blast
qed

text\<open>If the trivial ideal $\{ 0\}$ is a prime ideal then the ring is a prime ring.\<close>

lemma (in ring0) zero_prime_ideal_prime_ring:
  assumes "{\<zero>}\<triangleleft>\<^sub>pR"
  shows "[R,A,M]{is a prime ring}"
proof -
  { fix x y z assume "x\<in>R" "y\<in>R" "\<forall>z\<in>R. x\<cdot>z\<cdot>y = \<zero>"
    let ?X = "\<langle>{x}\<rangle>\<^sub>I"
    let ?Y = "\<langle>{y}\<rangle>\<^sub>I"
    from \<open>x\<in>R\<close> \<open>y\<in>R\<close> have "?X\<times>?Y \<subseteq> R\<times>R"
      using generated_ideal_is_ideal ideal_dest_subset 
      by auto
    let ?P = "\<lambda>q. (\<forall>z\<in>?Y. q\<cdot>z = \<zero>)"
    let ?Q = "\<lambda>q. (\<forall>z\<in>R. x\<cdot>z\<cdot>q =\<zero>)"
    have "\<forall>y\<in>?Y. ?Q(y)"
    proof -
      from \<open>y\<in>R\<close> have "{y}\<noteq>0" and "{y}\<subseteq>R" by auto
      moreover 
      { fix s t q assume yzq: "s\<in>R" "t\<in>R" "q \<in> \<langle>{y}\<rangle>\<^sub>I" "\<forall>k\<in>R. x\<cdot>k\<cdot>q = \<zero>"
        from \<open>y\<in>R\<close> yzq(3) have "q\<in>R" 
          using generated_ideal_is_ideal ideal_dest_subset by auto
        { fix u assume "u\<in>R"
          from yzq(1,2) \<open>x\<in>R\<close> \<open>q\<in>R\<close> \<open>u\<in>R\<close> 
            have "x\<cdot>u\<cdot>(s\<cdot>q\<cdot>t) = (x\<cdot>(u\<cdot>s)\<cdot>q)\<cdot>t"
            using Ring_ZF_1_L11(2) Ring_ZF_1_L4(3) by auto
          with \<open>u\<in>R\<close> yzq(1,2,4) have "x\<cdot>u\<cdot>(s\<cdot>q\<cdot>t) = \<zero>"
            using Ring_ZF_1_L4(3) Ring_ZF_1_L6(1) by simp
        } hence "\<forall>z\<^sub>a\<in>R. x\<cdot>z\<^sub>a\<cdot>(s\<cdot>q\<cdot>t) = \<zero>" by simp
      } hence "\<forall>t\<in>R. \<forall>z\<in>R. \<forall>q\<in>\<langle>{y}\<rangle>\<^sub>I. 
        (\<forall>z\<in>R. x\<cdot>z\<cdot>q = \<zero>) \<longrightarrow> (\<forall>z\<^sub>a\<in>R. x\<cdot>z\<^sub>a\<cdot>(t\<cdot>q\<cdot>z) = \<zero>)" by simp
      moreover from \<open>x\<in>R\<close> have "\<forall>y\<in>R. \<forall>z\<in>R. 
             (\<forall>z\<in>R. x\<cdot>z\<cdot>y = \<zero>) \<and> (\<forall>z\<^sub>a\<in>R. x\<cdot>z\<^sub>a\<cdot>z = \<zero>) \<longrightarrow>
             (\<forall>z\<^sub>a\<in>R. x\<cdot>z\<^sub>a\<cdot>(y\<ra>z) = \<zero>)"
        using ring_oper_distr(1) Ring_ZF_1_L4(3) Ring_ZF_1_L3(3) 
          Ring_ZF_1_L2(1) by simp        
      moreover from \<open>\<forall>z\<in>R. x\<cdot>z\<cdot>y = \<zero>\<close> have "\<forall>x\<^sub>a\<in>{y}. \<forall>z\<in>R. x\<cdot>z\<cdot>x\<^sub>a = \<zero>" by simp
      ultimately show ?thesis by (rule induction_generated_ideal)
    qed
    from \<open>x\<in>R\<close> \<open>\<forall>y\<in>?Y. ?Q(y)\<close> have "\<forall>y\<in>?Y. x\<cdot>y = \<zero>"
      using Ring_ZF_1_L2(2) Ring_ZF_1_L3(5) by force
    from \<open>y\<in>R\<close> have "?Y\<triangleleft>R" "?Y\<subseteq>R" 
      using generated_ideal_is_ideal ideal_dest_subset by auto      
    have "\<forall>y\<in>?X. ?P(y)"
    proof -
      from \<open>x\<in>R\<close> have "{x}\<noteq>0" "{x}\<subseteq>R" by auto
      moreover 
      { fix q\<^sub>1 q\<^sub>2 q\<^sub>3
        assume q: "q\<^sub>1\<in>R" "q\<^sub>2\<in>R" "q\<^sub>3 \<in> \<langle>{x}\<rangle>\<^sub>I" "\<forall>k\<in>?Y. q\<^sub>3\<cdot>k = \<zero>"
        from \<open>x\<in>R\<close> \<open>q\<^sub>3 \<in> \<langle>{x}\<rangle>\<^sub>I\<close> have "q\<^sub>3\<in>R" 
          using generated_ideal_is_ideal ideal_dest_subset by auto
        with \<open>?Y\<triangleleft>R\<close> \<open>?Y\<subseteq>R\<close> q(1,2,4) have "\<forall>z\<^sub>a\<in>\<langle>{y}\<rangle>\<^sub>I. q\<^sub>1\<cdot>q\<^sub>3\<cdot>q\<^sub>2 \<cdot> z\<^sub>a = \<zero>"
          using ideal_dest_mult(2) Ring_ZF_1_L4(3) Ring_ZF_1_L11(2) 
            Ring_ZF_1_L6(2) by auto
      } hence "\<forall>y\<^sub>a\<in>R. \<forall>z\<in>R. \<forall>q\<in>\<langle>{x}\<rangle>\<^sub>I. 
              (\<forall>z\<in>\<langle>{y}\<rangle>\<^sub>I. q\<cdot>z = \<zero>) \<longrightarrow> (\<forall>z\<^sub>a\<in>\<langle>{y}\<rangle>\<^sub>I. y\<^sub>a\<cdot>q\<cdot>z\<cdot>z\<^sub>a = \<zero>)" 
        by auto
      moreover from \<open>?Y\<subseteq>R\<close> have "\<forall>y\<^sub>a\<in>R. \<forall>z\<in>R. 
        (\<forall>z\<in>\<langle>{y}\<rangle>\<^sub>I. y\<^sub>a\<cdot>z = \<zero>) \<and> (\<forall>z\<^sub>a\<in>\<langle>{y}\<rangle>\<^sub>I. z\<cdot>z\<^sub>a = \<zero>) \<longrightarrow>
          (\<forall>z\<^sub>a\<in>\<langle>{y}\<rangle>\<^sub>I. (y\<^sub>a\<ra>z)\<cdot>z\<^sub>a = \<zero>)"
        using ring_oper_distr(2) Ring_ZF_1_L3(3) Ring_ZF_1_L2(1)
        by auto
      moreover from \<open>\<forall>y\<in>?Y. x\<cdot>y = \<zero>\<close> have "\<forall>x\<in>{x}. \<forall>z\<in>\<langle>{y}\<rangle>\<^sub>I. x\<cdot>z = \<zero>" by auto
      ultimately show ?thesis by (rule induction_generated_ideal)
    qed
    from \<open>?X\<times>?Y \<subseteq> R\<times>R\<close> \<open>\<forall>y\<in>?X. ?P(y)\<close> have "M``(?X\<times>?Y) \<subseteq> {\<zero>}"
      using mult_monoid.monoid_oper_fun func_imagedef by auto
    with \<open>x\<in>R\<close> \<open>y\<in>R\<close> have "?X\<cdot>\<^sub>I?Y \<subseteq> {\<zero>}" 
      using generated_ideal_small zero_ideal productIdeal_def 
        generated_ideal_is_ideal by auto
    with assms \<open>x\<in>R\<close> \<open>y\<in>R\<close> have "?X \<subseteq> {\<zero>} \<or> ?Y \<subseteq> {\<zero>}" 
      using generated_ideal_is_ideal ideal_dest_subset
      unfolding primeIdeal_def by auto
    with \<open>x\<in>R\<close> \<open>y\<in>R\<close> have "x=\<zero> \<or> y=\<zero>" 
      using generated_ideal_contains_set by auto
  } hence "\<forall>x\<in>R. \<forall>y\<in>R. (\<forall>z\<in>R. x\<cdot>z\<cdot>y = \<zero>) \<longrightarrow> x=\<zero> \<or> y=\<zero>" 
    by auto
  with ringAssum show ?thesis using primeRing_def by auto
qed

text\<open>We can actually use this definition of a prime ring
  as a condition to check for prime ideals.\<close>

theorem (in ring0) equivalent_prime_ideal:
  assumes "P\<triangleleft>\<^sub>pR"
  shows "\<forall>x\<in>R. \<forall>y\<in>R. (\<forall>z\<in>R. x\<cdot>z\<cdot>y\<in>P) \<longrightarrow> x\<in>P \<or> y\<in>P"
proof -
  { fix x y assume "x\<in>R" "y\<in>R" "\<forall>z\<in>R. x\<cdot>z\<cdot>y\<in>P" "y\<notin>P"
    let ?X = "\<langle>{x}\<rangle>\<^sub>I"
    let ?Y = "\<langle>{y}\<rangle>\<^sub>I"
    from \<open>y\<in>R\<close> have "{y}\<noteq>0" and "{y}\<subseteq>R" by auto
    moreover have "\<forall>y\<^sub>a\<in>R.
       \<forall>z\<in>R. \<forall>q\<in>\<langle>{y}\<rangle>\<^sub>I. (\<forall>t\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. t\<cdot>u\<cdot>q \<in> P) \<longrightarrow>
                 (\<forall>t\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. t\<cdot>u\<cdot>(y\<^sub>a\<cdot>q\<cdot>z) \<in> P)"
    proof -
      { fix y\<^sub>a z q t u 
        assume "y\<^sub>a\<in>R" "z\<in>R" "q\<in>?Y" "\<forall>t\<in>?X. \<forall>u\<in>R. t\<cdot>u\<cdot>q\<in>P" "t\<in>?X" "u\<in>R"
        from \<open>x\<in>R\<close> \<open>y\<in>R\<close> \<open>q\<in>?Y\<close> \<open>t\<in>?X\<close> have "q\<in>R" "t\<in>R" 
          using generated_ideal_is_ideal ideal_dest_subset by auto
        from \<open>y\<^sub>a\<in>R\<close> \<open>u\<in>R\<close> have "u\<cdot>y\<^sub>a\<in>R" using Ring_ZF_1_L4(3) by auto
        with assms \<open>z\<in>R\<close> \<open>\<forall>t\<in>?X. \<forall>u\<in>R. t\<cdot>u\<cdot>q\<in>P\<close> \<open>t\<in>?X\<close> 
          have "(t\<cdot>(u\<cdot>y\<^sub>a)\<cdot>q)\<cdot>z \<in> P"
          using ideal_dest_mult(1) unfolding primeIdeal_def by auto
        with \<open>y\<^sub>a\<in>R\<close> \<open>z\<in>R\<close> \<open>u\<in>R\<close> \<open>q\<in>R\<close> \<open>t\<in>R\<close> have "t\<cdot>u\<cdot>(y\<^sub>a\<cdot>q\<cdot>z) \<in> P" 
          using Ring_ZF_1_L4(3) Ring_ZF_1_L11(2) by auto
      } thus ?thesis by simp
    qed
    moreover have "\<forall>y\<in>R. \<forall>z\<in>R. 
      (\<forall>t\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. t\<cdot>u\<cdot>y \<in> P) \<and> (\<forall>t\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. t\<cdot>u\<cdot>z \<in> P) \<longrightarrow>
      (\<forall>t\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. t\<cdot>u\<cdot>(y\<ra>z) \<in> P)"
    proof -
      { fix y\<^sub>a z t u assume ass: "y\<^sub>a\<in>R" "z\<in>R" "t\<in>?X" "u\<in>R"
          "\<forall>t\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. t\<cdot>u\<cdot>y\<^sub>a\<in>P" "\<forall>t\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. t\<cdot>u\<cdot>z\<in>P"
        from \<open>x\<in>R\<close> \<open>t\<in>?X\<close> have "t\<in>R" 
          using ideal_dest_subset generated_ideal_is_ideal by auto
        from assms ass(3,4,5,6) have "(t\<cdot>u\<cdot>y\<^sub>a)\<ra>(t\<cdot>u\<cdot>z) \<in> P"
          using ideal_dest_sum unfolding primeIdeal_def by simp
        with \<open>t\<in>R\<close> \<open>y\<^sub>a\<in>R\<close> \<open>z\<in>R\<close> \<open>u\<in>R\<close> have "t\<cdot>u\<cdot>(y\<^sub>a\<ra>z) \<in> P"
          using Ring_ZF_1_L4(3) ring_oper_distr(1) by simp     
      } thus ?thesis by simp
    qed
    moreover have "\<forall>y\<^sub>a\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. y\<^sub>a\<cdot>u\<cdot>y \<in> P"
    proof -
      from \<open>x\<in>R\<close> have "{x}\<noteq>0" and "{x}\<subseteq>R" by auto
      moreover have "\<forall>y\<^sub>a\<in>R. \<forall>z\<in>R. \<forall>q\<in>?X. 
        (\<forall>u\<in>R. q\<cdot>u\<cdot>y \<in> P) \<longrightarrow> (\<forall>u\<in>R. y\<^sub>a\<cdot>q\<cdot>z\<cdot>u\<cdot>y \<in> P)"
      proof -
        { fix y\<^sub>a z q u assume
            ass: "y\<^sub>a\<in>R" "z\<in>R" "q\<in>?X" "\<forall>u\<in>R. q\<cdot>u\<cdot>y \<in> P" "u \<in> R"
          from \<open>x\<in>R\<close> \<open>q\<in>?X\<close> have q: "q\<in>R" 
            using generated_ideal_is_ideal ideal_dest_subset 
            by auto
          from assms ass(1,2,4,5) have "y\<^sub>a\<cdot>(q\<cdot>(z\<cdot>u)\<cdot>y) \<in> P"
            using Ring_ZF_1_L4(3) ideal_dest_mult(2)
            unfolding primeIdeal_def by simp
          with \<open>y\<in>R\<close> \<open>y\<^sub>a\<in>R\<close> \<open>z\<in>R\<close> \<open>u \<in> R\<close> \<open>q\<in>R\<close> 
            have "y\<^sub>a\<cdot>q\<cdot>z\<cdot>u\<cdot>y \<in> P" 
            using Ring_ZF_1_L4(3) Ring_ZF_1_L11(2) by auto
        } thus ?thesis by auto
      qed
      moreover have "\<forall>y\<^sub>a\<in>R. \<forall>z\<in>R. 
        (\<forall>u\<in>R. y\<^sub>a\<cdot>u\<cdot>y \<in> P) \<and> (\<forall>u\<in>R. z\<cdot>u\<cdot>y \<in> P) \<longrightarrow> (\<forall>u\<in>R. (y\<^sub>a\<ra>z)\<cdot>u\<cdot>y \<in> P)"
      proof -
        { fix y\<^sub>a z u assume "y\<^sub>a\<in>R" "z\<in>R" "u\<in>R"
            "\<forall>u\<in>R. y\<^sub>a\<cdot>u\<cdot>y \<in> P" "\<forall>u\<in>R. z\<cdot>u\<cdot>y \<in> P"
          with assms \<open>y\<in>R\<close> have "((y\<^sub>a\<ra>z)\<cdot>u)\<cdot>y\<in>P"
            using ideal_dest_sum ring_oper_distr(2) Ring_ZF_1_L4(3)
            unfolding primeIdeal_def by simp
        } thus ?thesis by simp
      qed
      moreover from \<open>\<forall>z\<in>R. x\<cdot>z\<cdot>y\<in>P\<close> have "\<forall>x\<in>{x}. \<forall>u\<in>R. x\<cdot>u\<cdot>y \<in> P" 
        by simp
      ultimately show ?thesis by (rule induction_generated_ideal)
    qed 
    hence "\<forall>x\<^sub>a\<in>{y}. \<forall>t\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. t\<cdot>u\<cdot>x\<^sub>a \<in> P" by auto 
    ultimately have R: "\<forall>q\<in>?Y. \<forall>t\<in>?X. \<forall>u\<in>R. t\<cdot>u\<cdot>q \<in> P"
      by (rule induction_generated_ideal)
    from \<open>x\<in>R\<close> \<open>y\<in>R\<close> have subprd: "?X\<times>?Y \<subseteq> R\<times>R"
      using ideal_dest_subset generated_ideal_is_ideal by auto
    { fix t assume "t \<in> M``(?X\<times>?Y)"
      with subprd obtain t\<^sub>x t\<^sub>y where 
        "t\<^sub>x\<in>?X" "t\<^sub>y\<in>?Y" and t: "t= t\<^sub>x\<cdot>t\<^sub>y"
        using func_imagedef mult_monoid.monoid_oper_fun 
        by auto
      with R \<open>t\<^sub>x\<in>?X\<close> \<open>t\<^sub>y\<in>?Y\<close> have "t\<^sub>x\<cdot>\<one>\<cdot>t\<^sub>y \<in>P" 
        using Ring_ZF_1_L2(2) by auto  
      moreover from \<open>x\<in>R\<close> \<open>t\<^sub>x\<in>?X\<close> have "t\<^sub>x\<in>R" 
        using generated_ideal_is_ideal ideal_dest_subset by auto
      ultimately have "t\<in>P" using Ring_ZF_1_L3(5) t by auto
    } hence "M``(?X\<times>?Y) \<subseteq> P" by auto
    with assms \<open>x\<in>R\<close> \<open>y\<in>R\<close> have "?X \<subseteq> P \<or> ?Y \<subseteq> P"
      unfolding primeIdeal_def
      using generated_ideal_small productIdeal_def 
        generated_ideal_is_ideal ideal_dest_subset by auto 
    with \<open>x\<in>R\<close> \<open>y\<in>R\<close> \<open>y\<notin>P\<close> have "x\<in>P" using generated_ideal_contains_set 
      by auto
  } thus ?thesis by auto
qed

text\<open>The next theorem provides a sufficient condition for a proper ideal $P$ to be a prime ideal:
  if for all $x,y\in R$ it holds that for all $z\in R$ $x z y \in P$ only when $x\in P$ or $y\in P$
  then $P$ is a prime ideal. \<close>
   
theorem (in ring0) equivalent_prime_ideal_2:
  assumes "\<forall>x\<in>R. \<forall>y\<in>R. (\<forall>z\<in>R. x\<cdot>z\<cdot>y\<in>P) \<longrightarrow> x\<in>P \<or> y\<in>P" "P\<triangleleft>R" "P\<noteq>R"
  shows  "P\<triangleleft>\<^sub>pR" 
proof -
  { fix I J x x\<^sub>a 
    assume "I\<triangleleft>R" "I\<subseteq>R" "J\<triangleleft>R" "J\<subseteq>R" "I\<cdot>\<^sub>IJ \<subseteq> P" "x\<in>J" "x\<notin>P" "x\<^sub>a\<in>I"
    from \<open>I\<subseteq>R\<close> \<open>J\<subseteq>R\<close> have "I\<times>J \<subseteq> R\<times>R" by auto
    { fix z assume "z\<in>R"
      with \<open>I\<triangleleft>R\<close> \<open>x\<in>J\<close> \<open>x\<^sub>a\<in>I\<close> \<open>I\<times>J \<subseteq> R\<times>R\<close> have "(x\<^sub>a\<cdot>z\<cdot>x)\<in>M``(I\<times>J)"
        using ideal_dest_mult(1) func_imagedef mult_monoid.monoid_oper_fun 
        by auto
      with \<open>I\<triangleleft>R\<close> \<open>J\<triangleleft>R\<close> \<open>I\<cdot>\<^sub>IJ \<subseteq> P\<close> have "x\<^sub>a\<cdot>z\<cdot>x \<in> P"
        using generated_ideal_contains_set func1_1_L6(2) 
          mult_monoid.monoid_oper_fun productIdeal_def by force
    } with assms(1) \<open>I\<subseteq>R\<close> \<open>J\<subseteq>R\<close> \<open>x\<in>J\<close> \<open>x\<notin>P\<close> \<open>x\<^sub>a\<in>I\<close> have "x\<^sub>a\<in>P" 
      by blast
  } with assms(2,3) show ?thesis unfolding primeIdeal_def 
    by auto
qed

subsection\<open>Ring quotient\<close>

text\<open>Similar to groups, rings can be quotiented by normal additive subgroups;
  but to keep the structure of the multiplicative monoid we need extra structure
  in the normal subgroup. This extra structure is given by the ideal.\<close>

text\<open>Any ideal is a normal subgroup.\<close>

lemma (in ring0) ideal_normal_add_subgroup:
  assumes "I\<triangleleft>R"
  shows "IsAnormalSubgroup(R,A,I)"
  using ringAssum assms Group_ZF_2_4_L6(1)
  unfolding IsAring_def Ideal_def by auto

text\<open> Each ring $R$ is a group with respect to its addition operation.
  By the lemma \<open>ideal_normal_add_subgroup\<close> above an ideal $I\subseteq R$ is a normal subgroup of that group.
  Therefore we can define the quotient of the ring $R$ by the ideal $I$ using 
  the notion of quotient of a group by its normal subgroup, see section 
  \<open>Normal subgroups and quotient groups\<close> in \<open>Group_ZF_2\<close> theory. \<close>

definition (in ring0) QuotientBy where
  "I\<triangleleft>R \<Longrightarrow> QuotientBy(I) \<equiv> R//QuotientGroupRel(R,A,I)"

text\<open>Any ideal gives rise to an equivalence relation\<close>

corollary (in ring0) ideal_equiv_rel:
  assumes "I\<triangleleft>R"
  shows "equiv(R,QuotientGroupRel(R,A,I))"
  using assms add_group.Group_ZF_2_4_L3 unfolding Ideal_def
  by auto

text\<open>Any quotient by an ideal is an abelian group.\<close>

lemma (in ring0) quotientBy_add_group:
  assumes "I\<triangleleft>R"
  shows "IsAgroup(QuotientBy(I), QuotientGroupOp(R, A, I))" and
    "QuotientGroupOp(R, A, I) {is commutative on} QuotientBy(I)"
  using assms ringAssum ideal_normal_add_subgroup Group_ZF_2_4_T1 
    Group_ZF_2_4_L6(2) QuotientBy_def QuotientBy_def Ideal_def
  unfolding IsAring_def by auto

text\<open> Since every ideal is a normal subgroup of the additive group
  of the ring it is quite obvious that that addition is congruent with respect
  to the quotient group relation. The next lemma shows something a little bit less obvious:
  that the multiplicative ring operation is also congruent with the quotient relation
  and gives rise to a monoid in the quotient. \<close>

lemma (in ring0) quotientBy_mul_monoid:
  assumes "I\<triangleleft>R"
  shows "Congruent2(QuotientGroupRel(R, A, I),M)" and
    "IsAmonoid(QuotientBy(I),ProjFun2(R, QuotientGroupRel(R,A,I), M))"
proof -
  let ?r = "QuotientGroupRel(R,A,I)"
  { fix x y s t assume "\<langle>x,y\<rangle> \<in> ?r" and "\<langle>s,t\<rangle> \<in> ?r"
    then have xyst: "x\<in>R" "y\<in>R" "s\<in>R" "t\<in>R" "x\<rs>y \<in>I" "s\<rs>t \<in>I"
      unfolding QuotientGroupRel_def by auto
    from \<open>x\<in>R\<close> \<open>y\<in>R\<close> \<open>s\<in>R\<close> have 
      "(x\<cdot>s)\<rs>(y\<cdot>t) = ((x\<cdot>s)\<ra>((\<rm>(y\<cdot>s))\<ra>(y\<cdot>s)))\<rs>(y\<cdot>t)"
      using Ring_ZF_1_L3(1,3,7) Ring_ZF_1_L4(3,4) by simp
    with \<open>x\<in>R\<close> \<open>y\<in>R\<close> \<open>s\<in>R\<close> \<open>t\<in>R\<close> have 
      "(x\<cdot>s)\<rs>(y\<cdot>t) = ((x\<cdot>s)\<rs>(y\<cdot>s))\<ra>((y\<cdot>s)\<rs>(y\<cdot>t))"
      using Ring_ZF_1_L3(1) Ring_ZF_1_L4(1,2,3) Ring_ZF_1_L10(1) 
      by simp
    with \<open>x\<in>R\<close> \<open>y\<in>R\<close> \<open>s\<in>R\<close> \<open>t\<in>R\<close> have 
      "(x\<cdot>s)\<rs>(y\<cdot>t) = ((x\<rs>y)\<cdot>s)\<ra>(y\<cdot>(s\<rs>t))"
      using Ring_ZF_1_L8 by simp
    with assms xyst have "\<langle>M`\<langle>x,s\<rangle>,M`\<langle>y,t\<rangle>\<rangle> \<in> ?r"
      using ideal_dest_sum ideal_dest_mult(1,2) Ring_ZF_1_L4(3)
      unfolding QuotientGroupRel_def by auto
  } then show "Congruent2(?r,M)" unfolding Congruent2_def by simp
  with assms show "IsAmonoid(QuotientBy(I),ProjFun2(R,?r, M))"
    using add_group.Group_ZF_2_4_L3 mult_monoid.Group_ZF_2_2_T1 QuotientBy_def 
    unfolding Ideal_def by auto
qed

text\<open>Each ideal defines an equivalence relation on the ring with which both addition and 
  multiplication are congruent. The next couple of definitions set up notation
  for the operations that result from projecting the ring addition and multiplication
  on the quotient space.
  We will write $x+_I y $ to denote the result of the quotient
  operation (with respect to an ideal I) on classes $x$ and $y$ \<close>

definition (in ring0) ideal_radd ("_{\<ra>_}_") where
  "x{\<ra>I}y \<equiv> QuotientGroupOp(R, A, I)`\<langle>x,y\<rangle>"

text\<open>Similarly $x \cdot_I y$ is the value of the projection of the ring's multiplication
  on the quotient space defined by the an ideal $I$, which as we know
  is a normal subgroup of the ring with addition. \<close>

definition (in ring0) ideal_rmult ("_{\<cdot>_}_") where
  "x{\<cdot>I}y \<equiv> ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>x,y\<rangle>"

text\<open>The value of the projection of taking the negative in the ring on the quotient space
  defined by an ideal $I$ will be denoted \<open>{\<rm>I}\<close>.  \<close>

definition (in ring0) ideal_rmin ("{\<rm>_}_") where
  "{\<rm>I}y \<equiv> GroupInv(QuotientBy(I),QuotientGroupOp(R, A, I))`(y)"

text\<open>Subtraction in the quotient space is defined by the \<open>\<ra>I\<close> and \<open>\<rm>I\<close> operations in
  the obvious way. \<close>

definition (in ring0) ideal_rsub ("_{\<rs>_}_") where
  "x{\<rs>I}y \<equiv> x{\<ra>I}({\<rm>I}y)"

text\<open>The class of the zero of the ring with respect to the equivalence relation
  defined by an ideal $I$ will be denoted $0_I$.\<close>

definition (in ring0) ideal_rzero ("\<zero>\<^sub>_") where
  "\<zero>\<^sub>I \<equiv> QuotientGroupRel(R,A,I)``{\<zero>}"

text\<open>Similarly the class of the neutral element of multiplication in the ring
  with respect to the equivalence relation defined by an ideal $I$ will be denoted $1_I$.\<close>

definition (in ring0) ideal_rone ("\<one>\<^sub>_") where
  "\<one>\<^sub>I \<equiv> QuotientGroupRel(R,A,I)``{\<one>}"

text\<open>The class of the sum of two units of the ring will be denoted $2_I$.\<close>

definition (in ring0) ideal_rtwo ("\<two>\<^sub>_") where
  "\<two>\<^sub>I \<equiv> QuotientGroupRel(R,A,I)``{\<two>}"

text\<open>The value of the projection of the ring multiplication onto the the quotient space
  defined by an ideal $I$ on a pair of the same classes $\langle x,x\rangle$ is denoted $x^{2I}$. \<close>

definition (in ring0) ideal_rsqr ("_\<^sup>2\<^sup>_") where
  "x\<^sup>2\<^sup>I \<equiv> ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>x,x\<rangle>"

text\<open>The class of the additive neutral element of the ring (i.e. $0$) with respect to the 
  equivalence relation defined by an ideal is the neutral of the projected addition. \<close>

lemma (in ring0) neutral_quotient:
  assumes "I\<triangleleft>R"
  shows 
    "QuotientGroupRel(R,A,I)``{\<zero>} = TheNeutralElement(QuotientBy(I),QuotientGroupOp(R,A,I))"
  using ringAssum assms Group_ZF_2_4_L5B ideal_normal_add_subgroup QuotientBy_def
  unfolding IsAring_def by auto

text\<open>Similarly, the class of the multiplicative neutral element of the ring (i.e. $1$) 
  with respect to the  equivalence relation defined by an ideal is the neutral of the projected 
  multiplication. \<close>

lemma (in ring0) one_quotient:
  assumes "I\<triangleleft>R"
  defines "r \<equiv> QuotientGroupRel(R,A,I)"
  shows "r``{\<one>} = TheNeutralElement(QuotientBy(I),ProjFun2(R,r,M))"
  using ringAssum assms Group_ZF_2_2_L1 ideal_equiv_rel quotientBy_mul_monoid QuotientBy_def
  unfolding IsAring_def by auto

text\<open>The class of $2$ (i.e. $1+1$) is the same as the value of the addition projected on the
  quotient space on the pair of classes of $1$. \<close>

lemma (in ring0) two_quotient:
  assumes "I\<triangleleft>R"
  defines "r \<equiv> QuotientGroupRel(R,A,I)"
  shows "r``{\<two>} = QuotientGroupOp(R,A,I)`\<langle>r``{\<one>},r``{\<one>}\<rangle>"
  using ringAssum assms EquivClass_1_L10 ideal_equiv_rel Ring_ZF_1_L2(2) Ring_ZF_1_L2(2)
      Group_ZF_2_4_L5A ideal_normal_add_subgroup
  unfolding IsAring_def QuotientGroupOp_def by simp

text\<open>The class of a square of an element of the ring is the same as the result of the 
  projected multiplication on the pair of classes of the element. \<close>

lemma (in ring0) sqrt_quotient:
  assumes "I\<triangleleft>R" "x\<in>R"
  defines "r \<equiv> QuotientGroupRel(R,A,I)"
  shows "r``{x\<^sup>2} = ProjFun2(R,r, M)`\<langle>r``{x},r``{x}\<rangle>"
  using assms EquivClass_1_L10 ideal_equiv_rel quotientBy_mul_monoid(1)
  by auto

text\<open>The projection of the ring addition is distributive with respect
  to the projection of the ring multiplication. \<close>

lemma (in ring0) quotientBy_distributive:
  assumes "I\<triangleleft>R"
  defines "r \<equiv> QuotientGroupRel(R,A,I)"
  shows 
    "IsDistributive(QuotientBy(I),QuotientGroupOp(R,A,I),ProjFun2(R,r,M))"
  using ringAssum assms QuotientBy_def ring_oper_distr(1) Ring_ZF_1_L4(1,3) 
    quotientBy_mul_monoid(1) EquivClass_1_L10 ideal_equiv_rel Group_ZF_2_4_L5A 
    ideal_normal_add_subgroup ring_oper_distr(2)
  unfolding quotient_def QuotientGroupOp_def IsAring_def IsDistributive_def 
  by auto

text\<open>The quotient group is a ring with the quotient multiplication.\<close>

theorem (in ring0) quotientBy_is_ring:
  assumes "I\<triangleleft>R"
  defines "r \<equiv> QuotientGroupRel(R,A,I)"
  shows "IsAring(QuotientBy(I), QuotientGroupOp(R, A, I), ProjFun2(R,r, M))"
  using assms quotientBy_distributive quotientBy_mul_monoid(2) quotientBy_add_group
  unfolding IsAring_def by auto

text\<open>An important property satisfied by many important rings is
  being Noetherian: every ideal is finitely generated.\<close>

definition (in ring0) isFinGen ("_{is finitely generated}") where
  "I\<triangleleft>R \<Longrightarrow> I {is finitely generated} \<equiv> \<exists>S\<in>FinPow(R). I = \<langle>S\<rangle>\<^sub>I"

text\<open>For Noetherian rings the arbitrary sum can be reduced
  to the sum of a finite subset of the initial set of ideals\<close>

theorem (in ring0) sum_ideals_noetherian:
  assumes "\<forall>I\<in>\<I>. (I{is finitely generated})" "\<J> \<subseteq> \<I>"
  shows "\<exists>\<T>\<in>FinPow(\<J>). (\<oplus>\<^sub>I\<J>) = (\<oplus>\<^sub>I\<T>)"
proof -
  from assms(2) have "\<Union>\<J> \<subseteq> R" using ideal_dest_subset by auto
  then have "\<langle>\<Union>\<J>\<rangle>\<^sub>I \<triangleleft>R" using generated_ideal_is_ideal by simp
  with assms(2) have "(\<oplus>\<^sub>I\<J>) \<triangleleft>R" using sumArbitraryIdeals_def 
    by simp
  with assms(1) have "(\<oplus>\<^sub>I\<J>) {is finitely generated}"
    using ideal_dest_subset by auto
  with \<open>(\<oplus>\<^sub>I\<J>)\<triangleleft>R\<close>  obtain S where "S\<in>FinPow(R)" "(\<oplus>\<^sub>I\<J>) = \<langle>S\<rangle>\<^sub>I"
    using isFinGen_def by auto
  let ?N = "\<lambda>s\<in>S. {J\<in>FinPow(\<J>). s\<in>(\<oplus>\<^sub>IJ)}" 
  from \<open>S\<in>FinPow(R)\<close> have "Finite(S)" unfolding FinPow_def
    by auto
  then have "(\<forall>t\<in>S. ?N`(t) \<noteq> 0) \<longrightarrow>
           (\<exists>f. f \<in> (\<Prod>t\<in>S. ?N`(t)) \<and> (\<forall>t\<in>S. f`(t) \<in> ?N`(t)))"
    using eqpoll_iff finite_choice AxiomCardinalChoiceGen_def
    unfolding Finite_def by blast  
  moreover
  { fix t assume "t\<in>S"
    then have "?N`(t) = {J\<in>FinPow(\<J>). t\<in>(\<oplus>\<^sub>IJ)}" using lamE by auto
    moreover  
    from \<open>S\<in>FinPow(R)\<close> \<open>(\<oplus>\<^sub>I\<J>) = \<langle>S\<rangle>\<^sub>I\<close> \<open>t\<in>S\<close> have "t\<in>(\<oplus>\<^sub>I\<J>)" 
      using generated_ideal_contains_set unfolding FinPow_def by auto
    with assms(2) have "\<exists>\<T>\<in>FinPow(\<J>). t\<in>(\<oplus>\<^sub>I\<T>)" 
      using sum_ideals_finite_sum by simp
    ultimately have "?N`(t)\<noteq>0" using assms(2) sum_ideals_finite_sum
      by auto
  }
  ultimately obtain f where 
    f: "f \<in> (\<Prod>t\<in>S. ?N`(t))" "\<forall>t\<in>S. f`(t) \<in> ?N`(t)"
    by auto
  { fix y assume "y \<in> f``(S)"
    with image_iff obtain x where "x\<in>S" and "\<langle>x,y\<rangle> \<in> f" by auto
    with f(1) have "y\<in>?N`(x)" unfolding Pi_def by auto
    with \<open>x\<in>S\<close> have "Finite(y)" using lamE unfolding FinPow_def 
      by simp
  }
  moreover 
  from f(1) have f_Fun: "f:S\<rightarrow> (\<Union>{?N`(t). t\<in>S})" 
    unfolding Pi_def Sigma_def by blast
  with \<open>Finite(S)\<close> have "Finite(f``(S))" 
    using Finite1_L6A Finite_Fin_iff Fin_into_Finite by blast
  ultimately have "Finite(\<Union>(f``(S)))" using Finite_Union 
    by auto
  with f_Fun f(2) have B: "(\<Union>(f``(S))) \<in> FinPow(\<J>)"
    using func_imagedef lamE unfolding FinPow_def
    by auto
  then have "(\<Union>(f``(S))) \<subseteq> \<J>" unfolding FinPow_def by auto
  with assms(2) have "(\<Union>(f``(S))) \<subseteq> \<I>"  by auto
  hence sub: "\<Union>(\<Union>(f``(S))) \<subseteq> R" by auto
  { fix t assume "t\<in>S"
    with f(2) have "f`(t) \<in> FinPow(\<J>)" "t \<in> (\<oplus>\<^sub>I(f`(t)))"
      using lamE by auto
    from assms(2) \<open>f`(t) \<in> FinPow(\<J>)\<close> have "f`(t) \<subseteq> \<I>" 
      unfolding FinPow_def by auto
    from f_Fun \<open>t\<in>S\<close> have "\<Union>(f`t) \<subseteq> \<Union>(\<Union>(f``S))" using func_imagedef
      by auto
    with sub have "\<Union>(f`(t)) \<subseteq> \<langle>\<Union>(\<Union>(f``(S)))\<rangle>\<^sub>I" 
      using generated_ideal_contains_set by blast
    with sub have "\<langle>\<Union>(f`t)\<rangle>\<^sub>I \<subseteq> \<langle>\<Union>(\<Union>(f``S))\<rangle>\<^sub>I" 
      using generated_ideal_is_ideal generated_ideal_small by auto
    with \<open>f`(t) \<subseteq> \<I>\<close> \<open>t \<in> (\<oplus>\<^sub>I(f`(t)))\<close> \<open>(\<Union>(f``(S))) \<subseteq> \<I>\<close> 
      have "t \<in> (\<oplus>\<^sub>I(\<Union>(f``(S))))" 
      using sumArbitraryIdeals_def by auto
  } hence "S \<subseteq> \<oplus>\<^sub>I(\<Union>(f``(S)))" by auto
  with sub \<open>(\<Union>(f``(S))) \<subseteq> \<I>\<close> \<open>(\<oplus>\<^sub>I\<J>) = \<langle>S\<rangle>\<^sub>I\<close> have "(\<oplus>\<^sub>I\<J>) \<subseteq> \<oplus>\<^sub>I(\<Union>(f``(S)))"
    using generated_ideal_small generated_ideal_is_ideal sumArbitraryIdeals_def 
    by auto
  moreover
  from \<open>\<Union>\<J> \<subseteq> R\<close> \<open>(\<Union>(f``(S))) \<subseteq> \<J>\<close> have "\<Union>(\<Union>(f``(S))) \<subseteq> \<langle>\<Union>\<J>\<rangle>\<^sub>I"
    using generated_ideal_contains_set by blast
  with assms(2) \<open>(\<Union>(f``(S))) \<subseteq> \<I>\<close> \<open>\<langle>\<Union>\<J>\<rangle>\<^sub>I \<triangleleft>R\<close> have "(\<oplus>\<^sub>I(\<Union>(f``(S)))) \<subseteq>(\<oplus>\<^sub>I\<J>)"
    using generated_ideal_small sumArbitraryIdeals_def sumArbitraryIdeals_def 
    by simp
  ultimately have "(\<oplus>\<^sub>I\<J>) = \<oplus>\<^sub>I(\<Union>(f``(S)))" by auto
  with B show ?thesis by auto
qed

end
