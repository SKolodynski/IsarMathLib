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

text \<open>This section defines the concept of a ring ideal, and
defines some basic concepts and types, finishing with the theorem
that shows that the quotient of the additive group by the ideal
is actually a full ring.\<close>

text\<open>An ideal is a subgroup of the additive group of the ring, which
is closed by left and right multiplication by any ring element.\<close>

definition (in ring0) Ideal ("_\<triangleleft>R") where
  "I \<triangleleft>R \<equiv> (\<forall>x\<in>I. \<forall>y\<in>R. y\<cdot>x\<in>I \<and> x\<cdot>y\<in>I) \<and> IsAsubgroup(I,A)"

text\<open>To write less during proofs, we add this small definition\<close>
abbreviation (in ring0) ideals ("\<I>") where
"\<I> \<equiv> {J\<in>Pow(R). J\<triangleleft>R}"

text\<open>The first examples of ideals are the whole ring and the zero ring:\<close>
lemma (in ring0) R_ideal:
  shows "R \<triangleleft>R" unfolding Ideal_def apply simp
  using add_group.group0_3_T3[of R]
  Ring_ZF_1_L3(1) Ring_ZF_1_L2(1) unfolding IsOpClosed_def
  using Ring_ZF_1_L4(1,3) by auto

lemma (in ring0) zero_ideal:
  shows "{\<zero>} \<triangleleft>R" unfolding Ideal_def
  using
   Ring_ZF_1_L6 add_group.unit_singl_subgr by auto

text\<open>Some small lemmas dividing the definition of ideal into small parts\<close>
lemma (in ring0) ideal_dest_subset:
  assumes "I \<triangleleft>R" 
  shows "I \<subseteq> R" using assms unfolding Ideal_def using add_group.group0_3_L2  by auto

lemma (in ring0) ideal_dest_sum:
  assumes "I \<triangleleft>R" "x\<in>I" "y\<in>I"
  shows "x\<ra>y \<in>I" using assms add_group.group0_3_L6 
    unfolding Ideal_def by auto

lemma (in ring0) ideal_dest_mult:
  assumes "I \<triangleleft>R" "x\<in>I" "y\<in>R"
  shows "x\<cdot>y \<in>I" "y\<cdot>x \<in>I" using assms unfolding Ideal_def by auto

lemma (in ring0) ideal_dest_minus:
  assumes "I \<triangleleft>R" "x\<in>I"
  shows "(\<rm>x) \<in> I" using assms unfolding Ideal_def using
    add_group.group0_3_T3A by auto

lemma (in ring0) ideal_dest_zero:
  assumes "I \<triangleleft>R"
  shows "\<zero> \<in> I" using assms unfolding Ideal_def using
    add_group.group0_3_L5 by auto

text\<open>The most simple way to obtain an ideal from others is the intersection,
since the intersection of arbitrary ideals is an ideal.\<close>
theorem (in ring0) intersection_ideals:
  assumes "\<forall>J\<in>\<J>. (J \<triangleleft>R)" "\<J> \<noteq> 0"
  shows "(\<Inter>\<J>)  \<triangleleft>R"
proof-
  {
    fix x assume x:"x:\<Inter>\<J>"
    {
      fix y assume y:"y:R"
      {
        fix J assume J:"J\<in>\<J>"
        with x have "x\<in>J" by auto
        with y J have "y\<cdot>x\<in>J \<and> x\<cdot>y\<in>J" using assms(1)
          ideal_dest_mult by auto
      }
      then have "y\<cdot>x\<in>\<Inter>\<J> \<and> x\<cdot>y\<in>\<Inter>\<J>" using assms(2) by auto
    }
    then have "\<forall>y\<in>R. y\<cdot>x\<in>\<Inter>\<J> \<and> x\<cdot>y\<in>\<Inter>\<J>" by auto
  }
  then have e2:"\<forall>x\<in>\<Inter>\<J>. \<forall>y\<in>R. y\<cdot>x\<in>\<Inter>\<J> \<and> x\<cdot>y\<in>\<Inter>\<J>" by auto
  have "IsAsubgroup(\<Inter>\<J>,A)" using add_group.subgroup_inter[OF assms(2)] assms(1)
    unfolding Ideal_def by auto
  with e2 show ?thesis unfolding Ideal_def by auto
qed

text\<open>From any set, we may construct the minimal ideal containing that set\<close>

definition (in ring0) generatedIdeal ("\<langle>_\<rangle>\<^sub>I")
  where "X\<subseteq>R \<Longrightarrow> \<langle>X\<rangle>\<^sub>I \<equiv> \<Inter>{I\<in>\<I>. X \<subseteq> I}"

text\<open>The ideal generated by a set is an ideal\<close>
corollary (in ring0) generated_ideal_is_ideal:
  assumes "X\<subseteq>R"
  shows " \<langle>X\<rangle>\<^sub>I \<triangleleft>R" unfolding generatedIdeal_def[OF assms]
  apply (rule intersection_ideals) apply simp 
  using R_ideal assms by auto

text\<open>The ideal generated by a set is contained in any ideal containing the set\<close>
corollary (in ring0) generated_ideal_small:
  assumes "X \<subseteq> I" "I \<triangleleft>R"
  shows " \<langle>X\<rangle>\<^sub>I \<subseteq> I"
proof-
  have "I\<in>{J\<in>Pow(R). J \<triangleleft>R \<and> X\<subseteq>J}" using assms(2,1)
    ideal_dest_subset by auto
  then have "\<Inter>{J\<in>Pow(R). J \<triangleleft>R \<and> X\<subseteq>J} \<subseteq> I" by auto moreover
  from assms have "X\<subseteq> R" using ideal_dest_subset by auto
  ultimately show "\<langle>X\<rangle>\<^sub>I \<subseteq> I" using generatedIdeal_def[of X]
    by auto
qed

text\<open>The ideal generated by a set contains the set\<close>
corollary (in ring0) generated_ideal_contains_set:
  assumes "X\<subseteq>R"
  shows "X\<subseteq>\<langle>X\<rangle>\<^sub>I"
proof-
  {
    fix J assume J:"J:{J\<in>\<I>. X\<subseteq>J}"
    {
      fix t assume "t:X"
      with J have "t:J" by auto
    }
    then have "X\<subseteq>J" by auto
  }
  then have "X\<subseteq>\<Inter>{J\<in>\<I>. X\<subseteq>J} \<or> {J\<in>\<I>. X\<subseteq>J}=0" by auto
  then show "X\<subseteq>\<langle>X\<rangle>\<^sub>I" unfolding generatedIdeal_def[OF assms]
    using assms R_ideal by auto
qed

text\<open>To be able to show properties of an ideal generated by a set, we
have the following induction result\<close>

lemma (in ring0) induction_generated_ideal:
  assumes "\<forall>y\<in>R. \<forall>z\<in>R. \<forall>q\<in>\<langle>X\<rangle>\<^sub>I. P(q) \<longrightarrow> P(y\<cdot>q\<cdot>z)" 
    "\<forall>y\<in>R. \<forall>z\<in>R. P(y) \<and> P(z) \<longrightarrow> P(y\<ra>z)" 
    "X \<subseteq> R" 
    "\<forall>x\<in>X. P(x)"
    "X\<noteq>0"
  shows "\<forall>y\<in>\<langle>X\<rangle>\<^sub>I. P(y)"
proof-
  let ?J="{m\<in>\<langle>X\<rangle>\<^sub>I. P(m)}"
  have XJ:"X \<subseteq> ?J" using assms(3,4) generated_ideal_contains_set by auto
  have sub:"?J \<subseteq> R" using generated_ideal_is_ideal ideal_dest_subset assms(3) by auto moreover
  {
    fix y z assume "y\<in>R" "z\<in>?J"
    then have yz:"z\<in>\<langle>X\<rangle>\<^sub>I" "y\<in>R" "P(z)" "z:R" using sub by auto
    from assms(1) yz have "P(y\<cdot>z)" using
      Ring_ZF_1_L2(2) Ring_ZF_1_L3(5)[of "y\<cdot>z"] Ring_ZF_1_L4(3)[of y]
      by force moreover
    from assms(1) yz have "P(z\<cdot>y)" using
      Ring_ZF_1_L2(2) Ring_ZF_1_L3(6) Ring_ZF_1_L4(3)[of _ y]
      by force moreover 
    from yz(1,2) have "y\<cdot>z\<in>\<langle>X\<rangle>\<^sub>I" "z\<cdot>y\<in>\<langle>X\<rangle>\<^sub>I" using 
      generated_ideal_is_ideal[OF assms(3)] ideal_dest_mult by auto
    ultimately have "y\<cdot>z\<in>?J" "z\<cdot>y\<in>?J" by auto
  }
  then have "\<forall>x\<in>?J. \<forall>y\<in>R. y \<cdot> x \<in> ?J \<and> x \<cdot> y \<in> ?J" by auto
  moreover
  have "IsAsubgroup(?J,A)"
  proof(rule add_group.group0_3_T3)
    show "?J\<noteq>0" using assms(3-5) generated_ideal_contains_set[OF assms(3)] by force
    show "?J\<subseteq>R" using sub .
    {
      fix x assume "x:?J"
      then have x:"x:\<langle>X\<rangle>\<^sub>I" "x\<in>R" "P(x)" using sub by auto moreover
      have "\<one>:R" using Ring_ZF_1_L2(2).
      then have "\<one>:R" "(\<rm>\<one>):R" using Ring_ZF_1_L3(1) by auto
      ultimately have "P((\<rm>\<one>)\<cdot>x\<cdot>\<one>)" using assms(1) by auto
      then have "P((\<rm>x)\<cdot>\<one>)" using Ring_ZF_1_L3(6)[of x]
        Ring_ZF_1_L7(1)[of \<one> x] `\<one>:R` `x:R` by auto
      then have "P(\<rm>x)" using Ring_ZF_1_L3(5)[OF Ring_ZF_1_L3(1)]
        `x:R` by auto moreover
      from x(1) have "(\<rm>x)\<in>\<langle>X\<rangle>\<^sub>I" using generated_ideal_is_ideal[OF assms(3)]
        ideal_dest_minus by auto
      ultimately have "(\<rm>x)\<in>?J" by auto
    }
    then show "\<forall>x\<in>?J. (\<rm> x) \<in> ?J" by auto
    {
      fix x y assume as:"x\<in>?J" "y\<in>?J"
      from as have "P(x\<ra>y)" using assms(2)
        ideal_dest_subset[OF generated_ideal_is_ideal[OF assms(3)]] by auto
      moreover
      have "x\<ra>y\<in>\<langle>X\<rangle>\<^sub>I" using as generated_ideal_is_ideal[OF assms(3)]
        ideal_dest_sum by auto
      ultimately have "x\<ra>y \<in> ?J" by auto
    }
    then show "?J {is closed under} A" unfolding IsOpClosed_def by auto
  qed
  ultimately have "?J\<triangleleft>R" unfolding Ideal_def by auto
  with XJ have "\<langle>X\<rangle>\<^sub>I \<subseteq> ?J" using generated_ideal_small by auto
  then show ?thesis by auto
qed

text\<open>An ideal is very particular with the elements it may contain. If it contains
any invertible element, it is in fact the whole ring and not a proper subset\<close>

theorem (in ring0) ideal_with_one:
  assumes "I\<triangleleft>R" "\<one>\<in>I"
  shows "I = R"
proof-
  from assms(1) have "I \<subseteq> R" using ideal_dest_subset by auto
  moreover
  {
    fix t assume t:"t:R"
    with assms have "t\<cdot>\<one> \<in>I" using ideal_dest_mult(2) by auto
    with t have "t:I" using Ring_ZF_1_L3(5) by auto
  }
  then have "R\<subseteq> I" by auto
  ultimately show "I=R" by auto
qed

theorem (in ring0) ideal_with_unit:
  assumes "I\<triangleleft>R" "x\<in>I" "\<exists>y\<in>R. y\<cdot>x = \<one> \<or> x\<cdot>y =\<one>"
  shows "I = R"
proof-
  from assms(3) obtain y where y:"y:R" "y\<cdot>x = \<one> \<or> x\<cdot>y =\<one>" by auto
  from this(1) assms(1,2) have "y\<cdot>x \<in>I" "x\<cdot>y\<in>I" unfolding Ideal_def by auto
  with y(2) have "\<one>\<in>I" by auto
  with ideal_with_one assms(1) show ?thesis by auto
qed

text\<open>The previous result drives us to define what a maximal ideal would be:
  an ideal such that any bigger ideal is the whole ring\<close>

definition (in ring0) maximalIdeal ("_\<triangleleft>\<^sub>mR") where
  "I\<triangleleft>\<^sub>mR \<equiv> I\<triangleleft>R \<and> I \<noteq>R \<and> (\<forall>J\<in>\<I>. I\<subseteq>J \<and> J\<noteq>R \<longrightarrow> I=J)"

text\<open>Before delving into maximal ideals, lets define some operation on ideals
  that are useful when formulating some proofs.\<close>

definition (in ring0) productIdeal (infix "\<cdot>\<^sub>I" 90) where
  "I\<triangleleft>R \<Longrightarrow> J\<triangleleft>R  \<Longrightarrow> I\<cdot>\<^sub>IJ \<equiv> \<langle>M``(I\<times>J)\<rangle>\<^sub>I"

definition (in ring0) sumIdeal (infix "+\<^sub>I" 90) where
  "I\<triangleleft>R \<Longrightarrow> J\<triangleleft>R  \<Longrightarrow> I+\<^sub>IJ \<equiv> \<langle>I\<union>J\<rangle>\<^sub>I"

text\<open>Some times, we may need to sum an arbitrary number
  of ideals, and not just two\<close>

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
    using generated_ideal_contains_set sumIdeal_def by auto
qed

text\<open>Every element in the arbitrary sum of ideals
  is generated by only a finite subset of those ideals\<close>

lemma (in ring0) sum_ideals_finite_sum:
  assumes "\<J> \<subseteq> \<I>" "s\<in>(\<oplus>\<^sub>I\<J>)"
  shows "\<exists>\<T>\<in>FinPow(\<J>). s\<in>(\<oplus>\<^sub>I\<T>)"
proof-
  {
    assume "\<Union>\<J>=0"
    then have "\<J>\<subseteq>{0}" by auto
    then have "Finite(\<J>)" using subset_Finite[OF _ nat_into_Finite[of 1]]
      by auto
    then have "\<J>\<in>FinPow(\<J>)" unfolding FinPow_def by auto
    then have ?thesis using assms(2) by auto
  }
  moreover
  {
    assume notE:"\<Union>\<J>\<noteq>0" 
    let ?P= "\<lambda>t. \<exists>\<T>\<in>FinPow(\<J>). t\<in>(\<oplus>\<^sub>I\<T>)"
    {
      fix t assume "t\<in>\<Union>\<J>"
      then obtain J where J:"t\<in>J" "J\<in>\<J>" by auto
      then have "{J}\<in>FinPow(\<J>)" unfolding FinPow_def
        using eqpoll_imp_Finite_iff[of "{J}" "1"] nat_into_Finite
        by auto moreover
      have "(\<oplus>\<^sub>I{J}) = \<langle>J\<rangle>\<^sub>I" using J(2) assms(1)
        sumArbitraryIdeals_def by auto
      with J(1) have "t\<in>(\<oplus>\<^sub>I{J})"
        using generated_ideal_contains_set[of J]
        J(2) assms(1) by auto
      ultimately have "?P(t)" by auto
    }
    then have "\<forall>t\<in>\<Union>\<J>. ?P(t)" by auto moreover
    {  
      fix y z q assume q:"?P(q)" "y:R" "z:R" "q:\<langle>\<Union>\<J>\<rangle>\<^sub>I"
      then obtain \<T> where T:"\<T>\<in>FinPow(\<J>)" "q:\<oplus>\<^sub>I\<T>" by auto
      from T(1) have "\<Union>\<T> \<subseteq> R" "\<T>\<subseteq>\<I>" using assms(1) unfolding FinPow_def by auto
      then have "(\<oplus>\<^sub>I\<T>)\<triangleleft>R" using generated_ideal_is_ideal[of "\<Union>\<T>"]
        sumArbitraryIdeals_def[of \<T>] by auto
      with T(2) q(2,3) have "y \<cdot> q \<cdot> z \<in> \<oplus>\<^sub>I\<T>"
        unfolding Ideal_def by auto
      with T(1) have "?P(y \<cdot> q \<cdot> z)" by auto
    }
    then have "\<forall>y\<in>R. \<forall>z\<in>R. \<forall>q\<in>\<langle>\<Union>\<J>\<rangle>\<^sub>I. ?P(q) \<longrightarrow> ?P(y \<cdot> q \<cdot> z)" by auto moreover
    {
      fix y z assume "?P(y)" "?P(z)"
      then obtain Ty Tz where T:"Ty\<in>FinPow(\<J>)" "y \<in> \<oplus>\<^sub>ITy"
        "Tz\<in>FinPow(\<J>)" "z \<in> \<oplus>\<^sub>ITz" by auto
      from T(1,3) have A:"Ty\<union>Tz:FinPow(\<J>)" unfolding FinPow_def
        using Finite_Un by auto
      then have "\<Union>Ty \<subseteq> \<Union>(Ty\<union>Tz)" "\<Union>Tz \<subseteq> \<Union>(Ty\<union>Tz)" and sub:"\<Union>(Ty\<union>Tz) \<subseteq>R"
        unfolding FinPow_def using assms(1) by auto
      with A have "\<Union>Ty \<subseteq> \<langle>\<Union>(Ty\<union>Tz)\<rangle>\<^sub>I" "\<Union>Tz \<subseteq> \<langle>\<Union>(Ty\<union>Tz)\<rangle>\<^sub>I" using
        generated_ideal_contains_set[of "\<Union>(Ty\<union>Tz)"] by auto
      then have "\<langle>\<Union>Ty\<rangle>\<^sub>I\<subseteq> \<langle>\<Union>(Ty\<union>Tz)\<rangle>\<^sub>I" "\<langle>\<Union>Tz\<rangle>\<^sub>I \<subseteq> \<langle>\<Union>(Ty\<union>Tz)\<rangle>\<^sub>I"
        using generated_ideal_small[OF _ generated_ideal_is_ideal]
        sub by auto
      moreover from T(1,3) have Q:"Ty \<subseteq>\<I>" "Tz\<subseteq> \<I>" using assms(1)
        unfolding FinPow_def by auto
      moreover note T(2,4)
      ultimately have "y\<in>\<langle>\<Union>(Ty\<union>Tz)\<rangle>\<^sub>I" "z\<in>\<langle>\<Union>(Ty\<union>Tz)\<rangle>\<^sub>I"
        using sumArbitraryIdeals_def[of "Ty"]
        sumArbitraryIdeals_def[of "Tz"] by auto
      then have "y\<ra>z\<in>\<langle>\<Union>(Ty\<union>Tz)\<rangle>\<^sub>I" using
        generated_ideal_is_ideal[OF sub] ideal_dest_sum
        by auto
      then have "y\<ra>z\<in>(\<oplus>\<^sub>I(Ty\<union>Tz))" using sumArbitraryIdeals_def[of "Ty\<union>Tz"]
        Q by force
      with A have "?P(y\<ra>z)" by auto
    }
    then have "\<forall>y\<in>R. \<forall>z\<in>R. ?P(y) \<and> ?P(z) \<longrightarrow> ?P(y \<ra> z)" by auto
    moreover
    have sub:"\<Union>\<J> \<subseteq> R" using assms(1) by auto
    ultimately have "\<forall>t\<in>\<langle>\<Union>\<J>\<rangle>\<^sub>I. ?P(t)"
      using induction_generated_ideal[of "\<Union>\<J>" ?P] notE by blast
    with assms(2) have ?thesis unfolding
      sumArbitraryIdeals_def[OF assms(1)] by auto
  }
  ultimately show ?thesis by auto
qed

text\<open>By definition of product of ideals and of an ideal itself, it follows
that the product of ideals is an ideal contained in the intersection\<close>
theorem (in ring0) product_in_intersection:
  assumes "I\<triangleleft>R" "J\<triangleleft>R"
  shows "I\<cdot>\<^sub>IJ \<subseteq> I\<inter>J" and "(I\<cdot>\<^sub>IJ)\<triangleleft>R" and "M``(I\<times>J) \<subseteq> I\<cdot>\<^sub>IJ"
proof-
  have s:"M``(I\<times>J) \<subseteq> I\<inter>J"
  proof
    fix x assume x:"x\<in>M``(I\<times>J)"
    then obtain y where "y:I\<times>J" "\<langle>y,x\<rangle>\<in>M" unfolding image_def
      by auto
    then obtain yi yj where y:"yi:I" "yj:J" "\<langle>\<langle>yi,yj\<rangle>,x\<rangle>\<in>M" by auto
    then have "yi\<cdot>yj:I" "yi\<cdot>yj:J" using assms ideal_dest_subset[of I]  ideal_dest_subset[of J] unfolding Ideal_def
      by auto
    with y(3) show "x\<in>I\<inter>J" using apply_equality[of _ x M]
      using ringAssum unfolding IsAring_def IsAmonoid_def IsAssociative_def
      by auto
  qed
  moreover
  have "(I\<inter>J) \<triangleleft>R" using intersection_ideals[of "{I,J}"] assms by auto
  ultimately show "I\<cdot>\<^sub>IJ \<subseteq> I\<inter>J" unfolding productIdeal_def[OF assms]
    using generated_ideal_small by auto
  from s have q:"M``(I\<times>J) \<subseteq> R" using assms ideal_dest_subset by auto
  with generated_ideal_is_ideal show "(I\<cdot>\<^sub>IJ) \<triangleleft>R" unfolding
    productIdeal_def[OF assms] by auto
  from q show "M``(I\<times>J) \<subseteq> I\<cdot>\<^sub>IJ" using generated_ideal_contains_set
    unfolding productIdeal_def[OF assms] by auto
qed

text\<open>We will show now that the sum of ideals is no more that the sum of the ideal elements\<close>
lemma (in ring0) sum_elements:
  assumes "I \<triangleleft>R" "J \<triangleleft>R" "x \<in> I" "y \<in> J"
  shows "x\<ra>y \<in> I+\<^sub>IJ"
proof-
  from assms(1,2) have "I\<union>J \<subseteq> R" using ideal_dest_subset by auto moreover
  have "x\<in> I\<union>J" "y\<in> I\<union>J" using assms(3,4) by auto
  ultimately have "x \<in> \<langle>I\<union>J\<rangle>\<^sub>I" "y \<in> \<langle>I\<union>J\<rangle>\<^sub>I" using generated_ideal_contains_set
    by auto
  moreover have "\<langle>I\<union>J\<rangle>\<^sub>I \<triangleleft>R" using generated_ideal_is_ideal[of "I\<union>J"] assms(1,2)
    using ideal_dest_subset[of I] ideal_dest_subset[of J]
    by auto
  ultimately have "x\<ra>y\<in>\<langle>I\<union>J\<rangle>\<^sub>I" using ideal_dest_sum by auto
  then show ?thesis using sumIdeal_def assms(1,2) by auto
qed

lemma (in ring0) sum_elements_is_ideal:
  assumes "I \<triangleleft>R" "J \<triangleleft>R"
  shows "(A``(I\<times>J)) \<triangleleft>R"
proof-
  have a:"A:R\<times>R \<rightarrow> R" using add_group.groupAssum IsAgroup_def 
      IsAmonoid_def IsAssociative_def by simp
  from assms have ij:"I\<times>J \<subseteq> R\<times>R" using ideal_dest_subset by auto
  from a have Aimage:"A``(I\<times>J) \<subseteq> R" using func1_1_L6(2) by auto
  moreover
  {
    fix x y assume xy:"x\<in>R" "y\<in>A``(I\<times>J)"
    from ij xy(2) obtain z where "y=A`z" "z\<in>I\<times>J" using func_imagedef[OF a, of "I\<times>J"]
      by auto
    then obtain yi yj where y:"y=yi\<ra>yj" "yi\<in>I" "yj\<in>J"
      by auto
    from y(1) have "x\<cdot>y = x\<cdot>(yi\<ra>yj)" "y\<cdot>x = (yi\<ra>yj)\<cdot>x" by auto
    then have "x\<cdot>y = (x\<cdot>yi)\<ra>(x\<cdot>yj)" "y\<cdot>x = (yi\<cdot>x)\<ra>(yj\<cdot>x)"
      using ring_oper_distr xy(1) y ij add_group.group_op_closed by auto
    moreover
    have "x\<cdot>yi \<in> I" "yi\<cdot>x \<in> I" "x\<cdot>yj \<in> J" "yj\<cdot>x \<in> J"
      using assms xy(1) y(2,3) ideal_dest_mult by auto
    ultimately have "x\<cdot>y\<in>A``(I\<times>J)" "y\<cdot>x\<in>A``(I\<times>J)"
      using func_imagedef[OF a, of "I\<times>J"] ij by auto
  }
  then have "\<forall>x\<in>A``(I\<times>J). \<forall>y\<in>R. y \<cdot> x \<in> A``(I\<times>J) \<and> x \<cdot> y \<in> A``(I\<times>J)" by auto
  moreover
  have "IsAsubgroup(A``(I\<times>J),A)"
  proof(rule add_group.group0_3_T3)
    show AsubR:"A `` (I \<times> J) \<subseteq> R" using Aimage.
    {
      fix x assume "x\<in>A `` (I \<times> J)"
      then obtain z where "x=A`z" "z\<in>I\<times>J" using func_imagedef[OF a, of "I\<times>J"]
        ij by auto
      then obtain xi xj where x:"xi\<in>I" "xj\<in>J" "x=xi\<ra>xj" by auto
      from x(3) have "(\<rm>x) = \<rm>(xi\<ra>xj)" by auto
      then have "(\<rm>x) = (\<rm>xi)\<rs>xj" using Ring_ZF_1_L9(2)
        assms x(1,2) ideal_dest_subset by auto
      moreover
      have "(\<rm>xi)\<in>I" using assms(1) ideal_dest_minus x(1) by auto
      moreover
      have "(\<rm>xj)\<in>J" using assms(2) ideal_dest_minus x(2) by auto
      ultimately have "(\<rm>x) \<in> A``(I\<times>J)" using func_imagedef[OF a, of "I\<times>J"]
        ij by auto
    }
    then show "\<forall>x\<in>A `` (I \<times> J). (\<rm> x) \<in> A `` (I \<times> J)" by auto
    have "\<zero>\<in>I" "\<zero>\<in>J" using ideal_dest_zero assms by auto
    then have "\<zero>\<ra>\<zero> \<in> A `` (I \<times> J)" using func_imagedef[OF a, of "I\<times>J"] ij by auto
    then show "A `` (I \<times> J) \<noteq> 0" by auto
    {
      fix x y assume xy:"x\<in> A `` (I \<times> J)" "y\<in> A `` (I \<times> J)"
      then obtain z g where "x=A`z" "z\<in>I\<times>J" "y=A`g" "g\<in>I\<times>J" using func_imagedef[OF a, of "I\<times>J"]
        ij by auto
      then obtain xi xj yi yj where x:"xi\<in>I" "xj\<in>J" "x=xi\<ra>xj"
        "yi\<in>I" "yj\<in>J" "y=yi\<ra>yj" by auto
      have "x\<ra>y = (x\<ra>yi)\<ra>yj" using xy(1) AsubR
        x(4-6) ij Ring_ZF_1_L10(1)[of x yi yj] by force
      then have "x\<ra>y = (xi\<ra>yi)\<ra>(xj\<ra>yj)"
        using x(1-5) ij Ring_ZF_2_L5(4)[of xi xj yi yj] by auto
      moreover have "xi\<ra>yi \<in> I" using x(1,4) assms(1)
        ideal_dest_sum by auto
      moreover have "xj\<ra>yj \<in> J" using x(2,5) assms(2)
        ideal_dest_sum by auto
      ultimately have "x\<ra>y \<in> A``(I\<times>J)" using func_imagedef[OF a, of "I\<times>J"]
        ij by auto
    }
    then show "A `` (I \<times> J) {is closed under} A" unfolding IsOpClosed_def
      by auto
  qed
  ultimately show "(A `` (I \<times> J))\<triangleleft>R" unfolding Ideal_def by auto
qed

corollary (in ring0) sum_ideals_is_sum_elements:
  assumes  "I \<triangleleft>R" "J \<triangleleft>R"
  shows "(A `` (I \<times> J)) = I+\<^sub>IJ"
proof
  have a:"A:R\<times>R \<rightarrow> R" using add_group.groupAssum IsAgroup_def 
      IsAmonoid_def IsAssociative_def by simp
  from assms have ij:"I\<subseteq>R" "J \<subseteq> R" using ideal_dest_subset by auto
  then have ij_prd:"I\<times>J \<subseteq> R\<times>R" by auto
  then show "A `` (I \<times> J) \<subseteq> I +\<^sub>I J" using sum_elements[OF assms]
    func_imagedef[OF a, of "I\<times>J"] by auto
  {
    fix x assume x:"x\<in>I"
    with ij(1) have "x=x\<ra>\<zero>" using Ring_ZF_1_L3(3)[of x] by auto
    then have "x\<in>A `` (I \<times> J)" using x assms(2) add_group.group0_3_L5[of J]
      unfolding Ideal_def using func_imagedef[OF a, of "I\<times>J"]
      ij_prd by auto
  }
  then have "I \<subseteq> A `` (I \<times> J)" by auto moreover
  {
    fix x assume x:"x\<in>J"
    with ij(2) have "x=\<zero>\<ra>x" using Ring_ZF_1_L3(4)[of x] by auto
    then have "x\<in>A `` (I \<times> J)" using x assms(1) add_group.group0_3_L5[of I]
      unfolding Ideal_def using func_imagedef[OF a, of "I\<times>J"]
      ij_prd by auto
  }
  then have "J \<subseteq> A `` (I \<times> J)" by auto
  ultimately have "I\<union>J \<subseteq> A `` (I \<times> J)" by auto
  then show "I+\<^sub>IJ \<subseteq> A `` (I \<times> J)" using generated_ideal_small
    sum_elements_is_ideal[OF assms] assms sumIdeal_def
    by auto
qed

corollary (in ring0) sum_ideals_is_ideal:
  assumes "I \<triangleleft>R" "J \<triangleleft>R"
  shows "(I +\<^sub>I J) \<triangleleft>R" using assms sum_ideals_is_sum_elements
  sum_elements_is_ideal ideal_dest_subset by auto

corollary (in ring0) sum_ideals_commute:
  assumes "I\<triangleleft>R" "J\<triangleleft>R"
  shows "(I +\<^sub>I J) = (J +\<^sub>I I)"
proof-
  have "I \<union> J = J \<union> I" by auto
  then show ?thesis unfolding
    sumIdeal_def[OF assms] sumIdeal_def[OF assms(2,1)]
    by auto
qed

text\<open>Now that we know what the product of ideals is, we are able to define
what a prime ideal is:\<close>
definition (in ring0) primeIdeal ("_\<triangleleft>\<^sub>pR") where
"P\<triangleleft>\<^sub>pR \<equiv> P\<triangleleft>R \<and> P\<noteq>R \<and> (\<forall>I\<in>\<I>. \<forall>J\<in>\<I>. I \<cdot>\<^sub>I J \<subseteq> P \<longrightarrow> (I \<subseteq> P \<or> J \<subseteq> P))"

text\<open>Any maximal ideal is prime\<close>

theorem (in ring0) maximal_is_prime:
  assumes "Q\<triangleleft>\<^sub>mR"
  shows "Q\<triangleleft>\<^sub>pR"
proof-
  have a:"A:R\<times>R \<rightarrow> R" using add_group.groupAssum IsAgroup_def 
      IsAmonoid_def IsAssociative_def by simp
  have MI:"Q \<in> \<I>" using assms unfolding maximalIdeal_def
    using ideal_dest_subset by auto
  {
    fix I J assume ij:"I\<in>\<I>" "J\<in>\<I>" "I \<cdot>\<^sub>I J \<subseteq> Q"
    {
      assume K:"\<not>(I\<subseteq>Q)" "\<not>(J\<subseteq>Q)"
      from this(1) obtain x where x:"x\<in>I-Q" by auto
      then have xR:"x\<in>R" using ij(1) ideal_dest_subset by auto
      let ?K = "\<langle>Q\<union>{x}\<rangle>\<^sub>I"
      have MK:"Q \<subseteq> ?K" "x\<in>?K" using generated_ideal_contains_set[of "Q\<union>{x}"]
        assms unfolding maximalIdeal_def using ideal_dest_subset[of Q]
        xR by auto
      with x have "Q \<subseteq> ?K" "?K\<noteq>Q" by auto
      with assms have "?K\<in>\<I> \<Longrightarrow> ?K=R" unfolding maximalIdeal_def by auto
      then have KR:"?K=R" using generated_ideal_is_ideal[of "Q\<union>{x}"] xR
        assms unfolding maximalIdeal_def using ideal_dest_subset[of Q]
        ideal_dest_subset[of "\<langle>Q\<union>{x}\<rangle>\<^sub>I"] by auto
      let ?P="Q+\<^sub>II"
      have "Q\<union>I \<subseteq> Q+\<^sub>II" using generated_ideal_contains_set[of "Q\<union>I"]
        sumIdeal_def[of Q I] assms ij(1)
        maximalIdeal_def using ideal_dest_subset by auto
      then have "Q\<union>{x} \<subseteq> Q+\<^sub>II" using x by auto
      then have "?K \<subseteq> Q+\<^sub>II" "Q+\<^sub>II \<subseteq>R" using generated_ideal_small[of "Q\<union>{x}" "Q+\<^sub>II"]
        generated_ideal_is_ideal[of "Q\<union>I"] sumIdeal_def[of Q I]
        ij(1) assms unfolding maximalIdeal_def using
        ideal_dest_subset by auto
      with KR have "Q+\<^sub>II = R" by auto
      then have "\<one>\<in>Q+\<^sub>II " using Ring_ZF_1_L2(2) by auto
      then have "\<one>\<in>A``(Q\<times>I)"
        using sum_ideals_is_sum_elements MI ij(1) by auto
      moreover have "Q\<times>I \<subseteq> R\<times>R" using MI ij(1) by auto
      ultimately obtain xm xi where mi1:"xm\<in>Q" "xi\<in>I" "\<one>=xm\<ra>xi"
        using func_imagedef[OF a, of "Q\<times>I"] by auto
      {
        fix y assume y:"y\<in>J"
        then have "\<one>\<cdot>y = y" using Ring_ZF_1_L3(6) ij(2) by auto
        with mi1(3) have "(xm\<ra>xi)\<cdot>y = y" by auto
        moreover have elems:"y:R" "xm:R" "xi:R" using y mi1(1,2)
          MI ij(1,2) by auto
        ultimately have "(xm\<cdot>y)\<ra>(xi\<cdot>y) = y" using
          ring_oper_distr(2)[of y xm xi] by auto
        moreover have "xm\<cdot>y:Q" using mi1(1) elems(1)
          MI ideal_dest_mult(1) by auto
        moreover
        have sub:"I\<times>J \<subseteq> R\<times>R" using ij(1,2) by auto
        have MR:"M:R\<times>R\<rightarrow>R" using ringAssum unfolding IsAring_def
          IsAmonoid_def IsAssociative_def by auto
        from sub MR have "xi\<cdot>y:M``(I\<times>J)"
          using func_imagedef[of M "R\<times>R" R "I\<times>J"] y mi1(2) by auto
        then have "xi\<cdot>y:I\<cdot>\<^sub>IJ" using generated_ideal_contains_set[of "M``(I\<times>J)"]
          func1_1_L6(2)[OF MR] productIdeal_def ij(1,2) by auto
        with ij(3) have "xi\<cdot>y:Q" by auto
        ultimately have "y\<in>Q" using MI ideal_dest_sum by force
      }
      then have "J \<subseteq> Q" by auto
      with K have False by auto
    }
    then have "(I\<subseteq>Q)\<or>(J\<subseteq>Q)" by auto
  }
  then have "\<forall>I\<in>\<I>. \<forall>J\<in>\<I>. I \<cdot>\<^sub>I J \<subseteq> Q \<longrightarrow> (I \<subseteq> Q \<or> J \<subseteq> Q)" by auto
  then show ?thesis using assms unfolding maximalIdeal_def primeIdeal_def
    by auto
qed

text\<open>In case of non-commutative rings, the zero divisor concept is too constrictive.
For that we define the following concept of a prime ring. Note that in case that
our ring is commutative, this is equivalent to having no zero divisors (there is no proof yet)\<close>
definition primeRing ("[_,_,_]{is a prime ring}") where
  "IsAring(R,A,M) \<Longrightarrow> [R,A,M]{is a prime ring} \<equiv> 
      (\<forall>x\<in>R. \<forall>y\<in>R. (\<forall>z\<in>R. M`\<langle>M`\<langle>x,z\<rangle>,y\<rangle> = TheNeutralElement(R,A)) \<longrightarrow> x =TheNeutralElement(R,A) \<or> y=TheNeutralElement(R,A))"

text\<open>Prime rings appear when the zero ideal is prime\<close>
lemma (in ring0) prime_ring_zero_prime_ideal:
  assumes "[R,A,M]{is a prime ring}" "R\<noteq>{\<zero>}"
  shows "{\<zero>}\<triangleleft>\<^sub>pR"
proof-
  have MR:"M:R\<times>R\<rightarrow>R" using ringAssum unfolding IsAring_def
    IsAmonoid_def IsAssociative_def by auto  
  {
    fix I J assume ij:"I\<in>\<I>" "J\<in>\<I>" "I \<cdot>\<^sub>I J \<subseteq> {\<zero>}"
    from ij(1,2) have ij_rr:"I\<times>J \<subseteq> R\<times>R" by auto
    {
      assume "\<not>(I\<subseteq>{\<zero>})" "\<not>(J\<subseteq>{\<zero>})"
      then obtain xi xj where x:"xi\<noteq>\<zero>" "xj\<noteq>\<zero>" "xi\<in>I" "xj:J" by auto
      {
        fix u assume "u\<in>R"
        with x(3) have "xi\<cdot>u\<in>I" using ij(1) ideal_dest_mult(1)
          by auto
        with x(4) have "xi\<cdot>u\<cdot>xj:M``(I\<times>J)" using func_imagedef[OF MR]
        ij_rr by auto
        then have "xi\<cdot>u\<cdot>xj:I \<cdot>\<^sub>I J" using generated_ideal_contains_set[of "M `` (I \<times> J)"]
          func1_1_L6(2)[OF MR, of "I\<times>J"] productIdeal_def ij(1,2)
          by auto
        with ij(3) have "xi\<cdot>u\<cdot>xj = \<zero>" by auto
      }
      then have "\<forall>u\<in>R. xi\<cdot>u\<cdot>xj = \<zero>" by auto moreover
      have "xi\<in>R" "xj\<in>R" using ij(1,2) x(3,4) by auto
      moreover note assms(1) ultimately have False
        using x(1,2) unfolding primeRing_def[OF ringAssum] by auto
    }
    then have "I\<subseteq>{\<zero>} \<or> J\<subseteq>{\<zero>}" by auto
  }
  then have "\<forall>I\<in>\<I>. \<forall>J\<in>\<I>. I \<cdot>\<^sub>I J \<subseteq> {\<zero>} \<longrightarrow> (I \<subseteq> {\<zero>} \<or> J \<subseteq> {\<zero>})" by auto
  moreover
  note zero_ideal assms(2) ultimately
  show ?thesis unfolding primeIdeal_def by auto
qed

lemma (in ring0) zero_prime_ideal_prime_ring:
  assumes "{\<zero>}\<triangleleft>\<^sub>pR"
  shows "[R,A,M]{is a prime ring}"
proof-
  have MR:"M:R\<times>R\<rightarrow>R" using ringAssum unfolding IsAring_def
    IsAmonoid_def IsAssociative_def by auto  
  {
    fix x y z assume as:"x\<in>R" "y\<in>R" "\<forall>z\<in>R. x\<cdot>z\<cdot>y = \<zero>"
    let ?X="\<langle>{x}\<rangle>\<^sub>I"
    let ?Y="\<langle>{y}\<rangle>\<^sub>I"
    have "?X\<subseteq>R" "?Y\<subseteq>R" using generated_ideal_is_ideal
      ideal_dest_subset as(1,2) by auto
    then have XY:"?X\<times>?Y \<subseteq> R\<times>R" by auto
    let ?P="\<lambda>q. (\<forall>z\<in>?Y. q\<cdot>z = \<zero>)"
    let ?Q="\<lambda>q. (\<forall>z\<in>R. x\<cdot>z\<cdot>q =\<zero>)"
    have Y:"\<forall>y\<in>?Y. ?Q(y)"
    proof(rule induction_generated_ideal)
      show "{y}\<subseteq>R" "{y}\<noteq>0" using as(2) by auto
      show "\<forall>xa\<in>{y}. \<forall>z\<in>R. x \<cdot> z \<cdot> xa = \<zero>" using as(3) by auto
      {
        fix s t q assume yzq:"s:R" "t:R" "q:\<langle>{y}\<rangle>\<^sub>I" "\<forall>k\<in>R. x \<cdot> k \<cdot> q = \<zero>"
        from yzq(3) have q:"q\<in>R" using generated_ideal_is_ideal
          ideal_dest_subset as(2) by auto
        {
          fix u assume "u:R"
          have "x \<cdot> u \<cdot> (s \<cdot> q \<cdot> t) = (x \<cdot> (u\<cdot>s)\<cdot>q)\<cdot>t"
            using Ring_ZF_1_L11(2) yzq(1-2) q `u:R` as(1) Ring_ZF_1_L4(3)
            by auto
          moreover have "u\<cdot>s:R" using `u:R` yzq(1) Ring_ZF_1_L4(3) by auto
          moreover note yzq(4) ultimately
          have "x \<cdot> u \<cdot> (s \<cdot> q \<cdot> t) = \<zero>\<cdot>t" by auto
          then have "x \<cdot> u \<cdot> (s \<cdot> q \<cdot> t) = \<zero>" using yzq(2) Ring_ZF_1_L6(1) by auto
        }
        then have "\<forall>za\<in>R. x \<cdot> za \<cdot> (s \<cdot> q \<cdot> t) = \<zero>" by auto
      }
      then show "\<forall>t\<in>R. \<forall>z\<in>R. \<forall>q\<in>\<langle>{y}\<rangle>\<^sub>I. (\<forall>z\<in>R. x \<cdot> z \<cdot> q = \<zero>) \<longrightarrow> (\<forall>za\<in>R. x \<cdot> za \<cdot> (t \<cdot> q \<cdot> z) = \<zero>)" by auto
      {
        fix s t assume st:"s:R" "t:R" "\<forall>k\<in>R. x \<cdot> k \<cdot> s = \<zero>"  "\<forall>k\<in>R. x \<cdot> k \<cdot> t = \<zero>"
        {
          fix u assume "u:R"
          have "x \<cdot> u \<cdot> (s \<ra> t) = (x \<cdot> u \<cdot> s) \<ra>(x \<cdot> u \<cdot> t)"
            using ring_oper_distr(1) `u:R` as(1) st(1,2) Ring_ZF_1_L4(3) by auto
          with st(3,4) `u:R` have "x \<cdot> u \<cdot> (s \<ra> t) = \<zero> \<ra> \<zero>" by auto
          then have "x \<cdot> u \<cdot> (s \<ra> t) = \<zero>" using Ring_ZF_1_L3(3) Ring_ZF_1_L2(1) by auto
        }
        then have "\<forall>za\<in>R. x \<cdot> za \<cdot> (s \<ra> t) = \<zero>" by auto
      }
      then show "\<forall>y\<in>R. \<forall>z\<in>R. (\<forall>z\<in>R. x \<cdot> z \<cdot> y = \<zero>) \<and> (\<forall>za\<in>R. x \<cdot> za \<cdot> z = \<zero>) \<longrightarrow>
                 (\<forall>za\<in>R. x \<cdot> za \<cdot> (y \<ra> z) = \<zero>)" by auto
    qed
    {
      fix yy assume "yy:?Y"
      with Y have "\<forall>z\<in>R. x \<cdot> z \<cdot> yy = \<zero>" by auto
      then have "x\<cdot>yy = \<zero>" using Ring_ZF_1_L2(2) Ring_ZF_1_L3(5)
        as(1) by auto
    }
    then have z:"\<forall>y\<in>?Y. x\<cdot>y = \<zero>" by auto
    have yy:"?Y\<triangleleft>R" "?Y \<subseteq> R" using generated_ideal_is_ideal as(2)
            ideal_dest_subset by auto      
    have xy:"\<forall>y\<in>?X. ?P(y)"
    proof(rule induction_generated_ideal)
      show "{x}\<subseteq>R" "{x}\<noteq>0" using as(1) by auto
      from z show "\<forall>x\<in>{x}. \<forall>z\<in>\<langle>{y}\<rangle>\<^sub>I. x \<cdot> z = \<zero>" by auto
      {
        fix q1 q2 q3 assume q:"q1:R" "q2:R" "q3:\<langle>{x}\<rangle>\<^sub>I"
          "\<forall>k\<in>?Y. q3 \<cdot> k = \<zero>"
        have q3:"q3\<in>R" using q(3) generated_ideal_is_ideal as(1)
          ideal_dest_subset by auto
        {
          fix q4 assume q4:"q4\<in>?Y"
          from yy q4 q(2) have "q2 \<cdot> q4 :?Y" using ideal_dest_mult(2) by auto
          moreover have "q1 \<cdot> q3 \<cdot> q2 \<cdot> q4 = q1 \<cdot> (q3 \<cdot> (q2 \<cdot> q4))"
            using q(1-2) q3 q4 yy(2) Ring_ZF_1_L4(3) Ring_ZF_1_L11(2) by auto
          moreover note q(4) ultimately
          have "q1 \<cdot> q3 \<cdot> q2 \<cdot> q4 = q1 \<cdot> \<zero>" by auto
          then have "q1 \<cdot> q3 \<cdot> q2 \<cdot> q4 = \<zero>" using Ring_ZF_1_L6(2) q(1) by auto
        }
        then have "\<forall>za\<in>\<langle>{y}\<rangle>\<^sub>I. q1 \<cdot> q3 \<cdot> q2 \<cdot> za = \<zero>" by auto
      }
      then show "\<forall>ya\<in>R. \<forall>z\<in>R. \<forall>q\<in>\<langle>{x}\<rangle>\<^sub>I. (\<forall>z\<in>\<langle>{y}\<rangle>\<^sub>I. q \<cdot> z = \<zero>) \<longrightarrow>
                    (\<forall>za\<in>\<langle>{y}\<rangle>\<^sub>I. ya \<cdot> q \<cdot> z \<cdot> za = \<zero>)" by auto
      {
        fix q1 q2 assume q:"q1:R" "q2:R" "\<forall>z\<in>\<langle>{y}\<rangle>\<^sub>I. q1 \<cdot> z = \<zero>" "\<forall>za\<in>\<langle>{y}\<rangle>\<^sub>I. q2 \<cdot> za = \<zero>"
        {
          fix q3 assume "q3\<in>?Y"
          have "(q1 \<ra> q2) \<cdot> q3 = (q1\<cdot>q3) \<ra> (q2\<cdot>q3)" using ring_oper_distr(2)
            q(1,2) `q3:?Y` yy(2) by auto
          with q(3,4) have "(q1 \<ra> q2) \<cdot> q3 = \<zero> \<ra> \<zero>" using `q3:?Y` by auto
          then have "(q1 \<ra> q2) \<cdot> q3 = \<zero>" using Ring_ZF_1_L3(3) Ring_ZF_1_L2(1) by auto
        }
        then have "\<forall>q\<in>?Y. (q1 \<ra> q2) \<cdot> q = \<zero>" by auto
      }
      then show "\<forall>ya\<in>R.
       \<forall>z\<in>R. (\<forall>z\<in>\<langle>{y}\<rangle>\<^sub>I. ya \<cdot> z = \<zero>) \<and> (\<forall>za\<in>\<langle>{y}\<rangle>\<^sub>I. z \<cdot> za = \<zero>) \<longrightarrow>
              (\<forall>za\<in>\<langle>{y}\<rangle>\<^sub>I. (ya \<ra> z) \<cdot> za = \<zero>)" by auto
    qed
    {
      fix q assume "q\<in>M``(?X\<times>?Y)"
      then obtain qx qy where q:"qx:?X" "qy:?Y" "q=qx\<cdot>qy"
        using func_imagedef[OF MR XY] by auto
      with xy have "q=\<zero>" by auto
    }
    then have "M``(?X\<times>?Y) \<subseteq> {\<zero>}" by auto
    then have "?X\<cdot>\<^sub>I?Y \<subseteq> {\<zero>}" using generated_ideal_small
      zero_ideal productIdeal_def generated_ideal_is_ideal
      as(1,2) by auto
    then have "?X \<subseteq> {\<zero>} \<or> ?Y \<subseteq> {\<zero>}" using assms unfolding primeIdeal_def
      using generated_ideal_is_ideal as(1,2) ideal_dest_subset by auto
    then have "x=\<zero> \<or> y =\<zero>" using generated_ideal_contains_set
      as(1,2) by auto
  }
  then have " \<forall>x\<in>R. \<forall>y\<in>R. (\<forall>z\<in>R. x \<cdot> z \<cdot> y = \<zero>) \<longrightarrow> x = \<zero> \<or> y = \<zero>" by auto
  then show ?thesis unfolding primeRing_def[OF ringAssum] by auto
qed

text\<open>We can actually use this definition of a prime ring,
as a condition to check for prime ideals.\<close>

theorem (in ring0) equivalent_prime_ideal:
  assumes "P\<triangleleft>\<^sub>pR"
  shows "\<forall>x\<in>R. \<forall>y\<in>R. (\<forall>z\<in>R. x\<cdot>z\<cdot>y\<in>P) \<longrightarrow> x\<in>P \<or> y\<in>P"
proof(safe)
  fix x y assume as:"x\<in>R" "y\<in>R" "\<forall>z\<in>R. x\<cdot>z\<cdot>y\<in>P" "y\<notin>P"
  let ?X="\<langle>{x}\<rangle>\<^sub>I"
  let ?Y="\<langle>{y}\<rangle>\<^sub>I"
  from as(3) have "\<forall>x\<in>{x}. \<forall>u\<in>R. x \<cdot> u \<cdot> y \<in> P" by auto moreover
  have "\<forall>ya\<in>R.
     \<forall>z\<in>R. \<forall>q\<in>?X. (\<forall>u\<in>R. q \<cdot> u \<cdot> y \<in> P) \<longrightarrow> (\<forall>u\<in>R. ya \<cdot> q \<cdot> z \<cdot> u \<cdot> y \<in> P)"
  proof(safe)
    fix ya z q u assume ass:"ya\<in>R" "z\<in>R" "q\<in>?X" "\<forall>u\<in>R. q \<cdot> u \<cdot> y \<in> P" "u \<in> R"
    from ass(3) have q:"q\<in>R" using generated_ideal_is_ideal[THEN ideal_dest_subset]
      as(1) by auto
    from ass(2,5) have "z\<cdot>u\<in>R" using Ring_ZF_1_L4(3) by auto
    with ass(4) have "q\<cdot>(z\<cdot>u)\<cdot>y:P" by auto
    with ass(1) have "ya\<cdot>(q\<cdot>(z\<cdot>u)\<cdot>y)\<in>P" using assms
      unfolding primeIdeal_def using ideal_dest_mult(2) by auto
    then show "ya\<cdot>q\<cdot>z\<cdot>u\<cdot>y\<in>P" using Ring_ZF_1_L4(3)
      Ring_ZF_1_L11(2) ass(1,2,5) as(2) q by auto
  qed
  moreover
  have "\<forall>ya\<in>R.
     \<forall>z\<in>R. (\<forall>u\<in>R. ya \<cdot> u \<cdot> y \<in> P) \<and> (\<forall>u\<in>R. z \<cdot> u \<cdot> y \<in> P) \<longrightarrow>
            (\<forall>u\<in>R. (ya \<ra> z) \<cdot> u \<cdot> y \<in> P)"
  proof(safe)
    fix ya z u assume ass:"ya\<in>R" "z\<in>R" "u\<in>R"
      "\<forall>u\<in>R. ya \<cdot> u \<cdot> y \<in> P" "\<forall>u\<in>R. z \<cdot> u \<cdot> y \<in> P"
    from ass(3-5) have "ya \<cdot> u \<cdot> y \<in> P" "z \<cdot> u \<cdot> y \<in> P" by auto
    then have "(ya \<cdot> u \<cdot> y)\<ra>(z \<cdot> u \<cdot> y) \<in> P" using
      ideal_dest_sum assms unfolding primeIdeal_def by auto
    then have "((ya\<cdot>u)\<ra>(z\<cdot>u))\<cdot>y\<in>P" using ring_oper_distr(2)
      as(2) Ring_ZF_1_L4(3) ass(1-3) by auto
    then show "((ya\<ra>z)\<cdot>u)\<cdot>y\<in>P" using ring_oper_distr(2)
      ass(1-3) by auto
  qed
  ultimately have R:"\<forall>ya\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. ya \<cdot> u \<cdot> y \<in> P"
    using induction_generated_ideal[of "{x}" "\<lambda>t. \<forall>u\<in>R. t\<cdot>u\<cdot>y \<in> P"]
    as(1) by auto
  then have "\<forall>xa\<in>{y}. \<forall>t\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. t \<cdot> u \<cdot> xa \<in> P" by auto moreover
  have "\<forall>ya\<in>R.
     \<forall>z\<in>R. \<forall>q\<in>\<langle>{y}\<rangle>\<^sub>I.
               (\<forall>t\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. t \<cdot> u \<cdot> q \<in> P) \<longrightarrow>
               (\<forall>t\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. t \<cdot> u \<cdot> (ya \<cdot> q \<cdot> z) \<in> P)"
  proof(safe)
    fix ya z q t u assume ass:"ya\<in>R" "z\<in>R" "q\<in>?Y" "\<forall>t\<in>?X. \<forall>u\<in>R. t \<cdot> u \<cdot> q \<in> P"
      "t\<in>?X" "u\<in>R"
    from ass(3,5) have qt:"q:R" "t\<in>R" using generated_ideal_is_ideal
      ideal_dest_subset as(1,2) by auto
    from ass(1,6) have "u\<cdot>ya:R" using Ring_ZF_1_L4(3) by auto
    with ass(4,5) have "t\<cdot>(u\<cdot>ya)\<cdot>q \<in>P" by auto
    then have "(t\<cdot>(u\<cdot>ya)\<cdot>q)\<cdot>z\<in>P" using ass(2) assms
      ideal_dest_mult(1) unfolding primeIdeal_def by auto
    then show "t \<cdot> u \<cdot> (ya \<cdot> q \<cdot> z) \<in>P" using
      Ring_ZF_1_L4(3) Ring_ZF_1_L11(2) ass(1,2,6) qt by auto
  qed moreover
  have "\<forall>y\<in>R. \<forall>z\<in>R. (\<forall>t\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. t \<cdot> u \<cdot> y \<in> P) \<and>
               (\<forall>t\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. t \<cdot> u \<cdot> z \<in> P) \<longrightarrow>
               (\<forall>t\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. t \<cdot> u \<cdot> (y \<ra> z) \<in> P)"
  proof(safe)
    fix ya z t u assume ass:"ya\<in>R" "z\<in>R" "t\<in>?X" "u\<in>R"
      "\<forall>t\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. t \<cdot> u \<cdot> ya \<in> P" "\<forall>t\<in>\<langle>{x}\<rangle>\<^sub>I. \<forall>u\<in>R. t \<cdot> u \<cdot> z \<in> P"
    from ass(3) have "t\<in>R" using ideal_dest_subset generated_ideal_is_ideal
      as(1) by auto
    from ass(3-6) have "t \<cdot> u \<cdot> ya \<in> P" "t \<cdot> u \<cdot> z \<in> P" by auto
    then have "(t \<cdot> u \<cdot> ya)\<ra>(t \<cdot> u \<cdot> z) \<in>P" using assms
      unfolding primeIdeal_def using ideal_dest_sum by auto
    then have "t\<cdot>((u\<cdot>ya)\<ra>(u\<cdot>z)) \<in>P" using ring_oper_distr(1)
      `t\<in>R` Ring_ZF_1_L4(3) ass(4,2,1) Ring_ZF_1_L11 by auto
    then have "t\<cdot>(u\<cdot>(ya\<ra>z)) \<in>P" using ring_oper_distr(1)
      ass(1,2,4) by auto
    then show "t\<cdot>u\<cdot>(ya\<ra>z) \<in>P" using Ring_ZF_1_L11(2)
      Ring_ZF_1_L4(1) ass(1,2,4) `t\<in>R` by auto
  qed
  ultimately have R:"\<forall>q\<in>?Y. \<forall>t\<in>?X. \<forall>u\<in>R. t\<cdot>u\<cdot>q \<in> P"
    using induction_generated_ideal[of "{y}" "\<lambda>q. \<forall>t\<in>?X. \<forall>u\<in>R. t\<cdot>u\<cdot>q \<in> P"]
    as(2) by auto
  have "?X\<subseteq>R" "?Y\<subseteq>R" using ideal_dest_subset
    generated_ideal_is_ideal as(1,2) by auto
  then have subprd:"?X\<times>?Y \<subseteq> R\<times>R" by auto
  {
    fix t assume "t\<in>M``(?X\<times>?Y)"
    then obtain tx ty where t:"tx\<in>?X" "ty\<in>?Y" "t= tx\<cdot>ty"
      using func_imagedef[of M "R\<times>R" R "?X\<times>?Y"]
        subprd ringAssum unfolding IsAring_def
        IsAmonoid_def IsAssociative_def by auto
    from this(1,2) have "tx\<cdot>\<one>\<cdot>ty \<in>P" using R Ring_ZF_1_L2(2)
      by auto moreover
    from t(1) have "tx\<in>R" using generated_ideal_is_ideal[THEN
          ideal_dest_subset] as(1) by auto
    ultimately have "t\<in>P" using Ring_ZF_1_L3(5) t(3) by auto
  }
  then have "M``(?X\<times>?Y) \<subseteq> P" by auto
  then have "?X\<cdot>\<^sub>I?Y \<subseteq> P" using generated_ideal_small
    assms unfolding primeIdeal_def using productIdeal_def[
        OF generated_ideal_is_ideal generated_ideal_is_ideal]
    as(1,2) by auto moreover
  have "?X:\<I>" "?Y:\<I>"
    using generated_ideal_is_ideal generated_ideal_is_ideal[THEN ideal_dest_subset]
    as(1,2) by auto
  ultimately have "?X \<subseteq> P \<or> ?Y \<subseteq> P" using assms
    unfolding primeIdeal_def by auto
  with as(4) generated_ideal_contains_set as(2)
  have "?X \<subseteq> P" by auto
  then show "x\<in>P" using generated_ideal_contains_set as(1) by auto
qed
    
theorem (in ring0) equivalent_prime_ideal_2:
  assumes "\<forall>x\<in>R. \<forall>y\<in>R. (\<forall>z\<in>R. x\<cdot>z\<cdot>y\<in>P) \<longrightarrow> x\<in>P \<or> y\<in>P" "P\<triangleleft>R" "P\<noteq>R"
  shows  "P\<triangleleft>\<^sub>pR" unfolding primeIdeal_def apply(safe)
  using assms(2) apply simp
  using assms(3) apply simp
proof-
  fix I J x xa assume as:"I\<triangleleft>R" "I\<subseteq>R" "J\<triangleleft>R" "J\<subseteq>R" "I \<cdot>\<^sub>I J \<subseteq> P" "x \<in> J" "x \<notin> P" "xa \<in> I"
  from as(4,2) have prdsub:"I\<times>J \<subseteq> R\<times>R" by auto
  {
    fix z assume z:"z\<in>R"
    then have "xa\<cdot>z\<in>I" using as(1,8) ideal_dest_mult(1) by auto
    then have "\<langle>xa\<cdot>z,x\<rangle>\<in>I\<times>J" using as(6) by auto
    then have "(xa\<cdot>z\<cdot>x)\<in>M``(I\<times>J)" using func_imagedef[of M "R\<times>R" R
      "I\<times>J"] prdsub ringAssum unfolding IsAring_def IsAmonoid_def
      IsAssociative_def by auto
    then have "(xa\<cdot>z\<cdot>x)\<in>\<langle>M``(I\<times>J)\<rangle>\<^sub>I" using generated_ideal_contains_set
      [OF func1_1_L6(2)[of M "R\<times>R" R]] ringAssum 
      unfolding IsAring_def IsAmonoid_def
      IsAssociative_def by force
    then have "(xa\<cdot>z\<cdot>x)\<in> I\<cdot>\<^sub>IJ" using productIdeal_def
      as(1,3) by auto
    with as(5) have "xa\<cdot>z\<cdot>x\<in>P" by auto
  }
  then have "\<forall>z\<in>R. xa\<cdot>z\<cdot>x \<in> P" by auto
  moreover have "xa\<in>R" "x\<in>R" using as(2,4,6,8) by auto
  with assms(1) have "(\<forall>z\<in>R. xa \<cdot> z \<cdot> x \<in> P) \<longrightarrow> x \<in> P \<or> xa \<in> P" by auto
  ultimately have "x\<in>P \<or> xa\<in>P" by auto
  with as(7) show "xa\<in>P" by auto
qed

subsection\<open>Ring quotient\<close>

text\<open>Similar to groups, rings can be quotiented by normal additive subgroups;
but to keep the structure of the multiplicative monoid we need extra structure
in the normal subgroup. This extra structure is given by the ideal.\<close>

text\<open>Any ideal is a normal subgroup\<close>

lemma (in ring0) ideal_normal_add_subgroup:
  assumes "I\<triangleleft>R"
  shows "IsAnormalSubgroup(R,A,I)"
  using Group_ZF_2_4_L6(1) using ringAssum
  unfolding IsAring_def using assms unfolding Ideal_def by auto

definition (in ring0) QuotientBy where
  "I\<triangleleft>R \<Longrightarrow> QuotientBy(I) \<equiv> R//QuotientGroupRel(R,A,I)"

text\<open>Any ideal gives rise to an equivalent relation\<close>
corollary (in ring0) equiv_rel:
  assumes "I\<triangleleft>R"
  shows "equiv(R,QuotientGroupRel(R,A,I))"
  using assms add_group.Group_ZF_2_4_L3 unfolding Ideal_def
  by auto

text\<open>Any quotient by an ideal is an abelian group\<close>
lemma (in ring0) quotientBy_add_group:
  assumes "I\<triangleleft>R"
  shows "IsAgroup(QuotientBy(I), QuotientGroupOp(R, A, I))" and
    "QuotientGroupOp(R, A, I) {is commutative on} QuotientBy(I)"
proof-
  from Group_ZF_2_4_T1[of R A I] show "IsAgroup(QuotientBy(I), QuotientGroupOp(R, A, I))"
    using ideal_normal_add_subgroup[OF assms]
      ringAssum unfolding QuotientBy_def[OF assms] IsAring_def by auto
  from Group_ZF_2_4_L6(2) show "QuotientGroupOp(R, A, I) {is commutative on} QuotientBy(I)"
    using ringAssum unfolding IsAring_def QuotientBy_def[OF assms]
    using assms unfolding Ideal_def by auto
qed

text\<open>The multiplicative monoid is congruent with the quotient relation
and gives rise to a monoid in the quotient\<close>
lemma (in ring0) quotientBy_mul_monoid:
  assumes "I\<triangleleft>R"
  shows "Congruent2(QuotientGroupRel(R, A, I),M)" and
 "IsAmonoid(QuotientBy(I),ProjFun2(R, QuotientGroupRel(R,A,I), M))"
proof-
  {
    fix x y s t assume "\<langle>x,y\<rangle>\<in>QuotientGroupRel(R,A,I)" "\<langle>s,t\<rangle>\<in>QuotientGroupRel(R,A,I)"
    then have xyst:"x\<in>R" "y\<in>R" "s\<in>R" "t\<in>R" "x\<rs>y \<in>I" "s\<rs>t \<in>I"
      unfolding QuotientGroupRel_def by auto
    have "(x\<cdot>s)\<rs>(y\<cdot>t) = (x\<cdot>s)\<ra>\<zero>\<rs>(y\<cdot>t)"
      using Ring_ZF_1_L3(3) Ring_ZF_1_L4(3)[OF xyst(1,3)] by auto
    then have "(x\<cdot>s)\<rs>(y\<cdot>t) = ((x\<cdot>s)\<ra>((\<rm>(y\<cdot>s))\<ra>(y\<cdot>s)))\<rs>(y\<cdot>t)"
      using Ring_ZF_1_L3(7)[of "y\<cdot>s"] Ring_ZF_1_L4(3)[OF xyst(2,3)] 
        Ring_ZF_1_L4(4)[of "\<rm>(y\<cdot>s)" "y\<cdot>s"] Ring_ZF_1_L3(1)[of "y\<cdot>s"]
      by auto
    then have "(x\<cdot>s)\<rs>(y\<cdot>t) = ((x\<cdot>s)\<rs>(y\<cdot>s))\<ra>((y\<cdot>s)\<rs>(y\<cdot>t))"
      using Ring_ZF_1_L3(1) Ring_ZF_1_L4(1,2) 
          Ring_ZF_1_L10(1)[of "x\<cdot>s" "\<rm>(y\<cdot>s)" "y\<cdot>s"] 
          Ring_ZF_1_L10(1)[of "(x\<cdot>s)\<rs>(y\<cdot>s)" "y\<cdot>s" "\<rm>(y\<cdot>t)"]
          Ring_ZF_1_L4(3)[OF xyst(1,3)] Ring_ZF_1_L4(3)[OF xyst(2,3)]
          Ring_ZF_1_L4(3)[OF xyst(2,4)] by auto
    then have "(x\<cdot>s)\<rs>(y\<cdot>t) = ((x\<rs>y)\<cdot>s)\<ra>(y\<cdot>(s\<rs>t))"
      using Ring_ZF_1_L8 xyst(1-4) by auto
    moreover
    have "(x\<rs>y)\<cdot>s \<in>I" using xyst(3,5) assms
      ideal_dest_mult(1) by auto
    moreover
    have "y\<cdot>(s\<rs>t) \<in>I" using xyst(2,6) assms
      ideal_dest_mult(2) by auto
    ultimately have "(x\<cdot>s)\<rs>(y\<cdot>t) \<in>I" using assms
      ideal_dest_sum by auto
    then have "\<langle>M ` \<langle>x, s\<rangle>, M ` \<langle>y, t\<rangle>\<rangle> \<in> QuotientGroupRel(R, A, I)"
      unfolding QuotientGroupRel_def using Ring_ZF_1_L4(3)
      xyst(1-4) by auto
  }
  then show "Congruent2(QuotientGroupRel(R, A, I),M)"
    unfolding Congruent2_def by auto moreover
  have "equiv(R,QuotientGroupRel(R,A,I))" using add_group.Group_ZF_2_4_L3
    assms unfolding Ideal_def by auto
  moreover note mult_monoid.Group_ZF_2_2_T1
  ultimately show "IsAmonoid(QuotientBy(I),ProjFun2(R, QuotientGroupRel(R,A,I), M))" unfolding QuotientBy_def[OF assms] by auto
qed

definition (in ring0) ideal_radd ("_{\<ra>_}_") where
  "x{\<ra>I}y \<equiv> QuotientGroupOp(R, A, I)`\<langle>x,y\<rangle>"

definition (in ring0) ideal_rmult ("_{\<cdot>_}_") where
  "x{\<cdot>I}y \<equiv> ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>x,y\<rangle>"

definition (in ring0) ideal_rmin ("{\<rm>_}_") where
  "{\<rm>I}y \<equiv> GroupInv(QuotientBy(I),QuotientGroupOp(R, A, I))`y"

definition (in ring0) ideal_rsub ("_{\<rs>_}_") where
  "x{\<rs>I}y \<equiv> x{\<ra>I}({\<rm>I}y)"

definition (in ring0) ideal_rzero ("\<zero>\<^sub>_") where
  "\<zero>\<^sub>I \<equiv> QuotientGroupRel(R,A,I)``{\<zero>}"

definition (in ring0) ideal_rone ("\<one>\<^sub>_") where
  "\<one>\<^sub>I \<equiv> QuotientGroupRel(R,A,I)``{\<one>}"

definition (in ring0) ideal_rtwo ("\<two>\<^sub>_") where
  "\<two>\<^sub>I \<equiv> QuotientGroupRel(R,A,I)``{\<two>}"

definition (in ring0) ideal_rsqr ("_\<^sup>2\<^sup>_") where
  "x\<^sup>2\<^sup>I \<equiv> ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>x,x\<rangle>"

lemma (in ring0) neutral_quotient:
  assumes "I\<triangleleft>R"
  shows "QuotientGroupRel(R,A,I)``{\<zero>} = TheNeutralElement(QuotientBy(I),QuotientGroupOp(R, A, I))"
  using Group_ZF_2_4_L5B[of R A I "QuotientGroupRel(R, A, I)" \<zero>] ideal_normal_add_subgroup[OF assms]
    ringAssum unfolding IsAring_def QuotientBy_def[OF assms] by auto

lemma (in ring0) one_quotient:
  assumes "I\<triangleleft>R"
  shows "QuotientGroupRel(R,A,I)``{\<one>} = TheNeutralElement(QuotientBy(I),ProjFun2(R, QuotientGroupRel(R, A, I), M))"
  using Group_ZF_2_2_L1[of R M "QuotientGroupRel(R, A, I)" 
      "ProjFun2(R, QuotientGroupRel(R, A, I), M)" \<one>]
    equiv_rel[OF assms] quotientBy_mul_monoid[OF assms]
    ringAssum unfolding IsAring_def QuotientBy_def[OF assms] by auto

lemma (in ring0) two_quotient:
  assumes "I\<triangleleft>R"
  shows "QuotientGroupRel(R,A,I)``{\<two>} = QuotientGroupOp(R, A, I)`\<langle>QuotientGroupRel(R,A,I)``{\<one>},QuotientGroupRel(R,A,I)``{\<one>}\<rangle>"
proof-
  have "QuotientGroupRel(R,A,I)``{\<two>} = QuotientGroupRel(R,A,I)``{\<one>\<ra>\<one>}"
    unfolding ringtwo_def by auto
  then show "QuotientGroupRel(R,A,I)``{\<two>} = QuotientGroupOp(R, A, I)`\<langle>QuotientGroupRel(R,A,I)``{\<one>}, QuotientGroupRel(R,A,I)``{\<one>}\<rangle>"
    using EquivClass_1_L10[OF equiv_rel[OF assms] _
        Ring_ZF_1_L2(2) Ring_ZF_1_L2(2), of A]
    Group_ZF_2_4_L5A[of R A I] ringAssum 
    ideal_normal_add_subgroup[OF assms]
    unfolding IsAring_def QuotientGroupOp_def by auto
qed

lemma (in ring0) sqrt_quotient:
  assumes "I\<triangleleft>R" "x\<in>R"
  shows "QuotientGroupRel(R,A,I)``{x\<^sup>2} = ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>QuotientGroupRel(R,A,I)``{x},QuotientGroupRel(R,A,I)``{x}\<rangle>"
proof-
  have "QuotientGroupRel(R,A,I)``{x\<^sup>2} = QuotientGroupRel(R,A,I)``{x\<cdot>x}"
    unfolding ringsq_def by auto
  then show ?thesis using EquivClass_1_L10[OF equiv_rel[OF assms(1)]
        quotientBy_mul_monoid(1)[OF assms(1)] assms(2,2)] by auto
qed

text\<open>Both quotient operations are distributive\<close>
lemma (in ring0) quotientBy_distributive:
  assumes "I\<triangleleft>R"
  shows "IsDistributive(QuotientBy(I),QuotientGroupOp(R, A, I),ProjFun2(R, QuotientGroupRel(R,A,I), M))"
proof-
  {
    fix x y z assume xyz:"x\<in>QuotientBy(I)" "y\<in>QuotientBy(I)" "z\<in>QuotientBy(I)"
    then obtain x1 y1 z1 where xyz1:"x1\<in>R" "y1\<in>R" "z1\<in>R"
      "QuotientGroupRel(R,A,I)``{x1} =x" 
      "QuotientGroupRel(R,A,I)``{y1} =y" 
      "QuotientGroupRel(R,A,I)``{z1} =z" 
      unfolding QuotientBy_def[OF assms] quotient_def by auto
    have aux:"QuotientGroupOp(R, A, I)`\<langle>y,z\<rangle> = QuotientGroupRel(R,A,I)``{y1\<ra>z1}"
      using EquivClass_1_L10[OF equiv_rel Group_ZF_2_4_L5A] unfolding
      QuotientGroupOp_def using assms ringAssum ideal_normal_add_subgroup
      unfolding IsAring_def using xyz1(2,3,5,6) by auto
    then have "ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>x,QuotientGroupOp(R, A, I)`\<langle>y,z\<rangle>\<rangle> = QuotientGroupRel(R,A,I)``{x1\<cdot>(y1\<ra>z1)}"
      using EquivClass_1_L10[OF equiv_rel quotientBy_mul_monoid(1)]
      assms xyz1(1-4) Ring_ZF_1_L4(1) by auto
    moreover have "ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>x,y\<rangle> = QuotientGroupRel(R,A,I)``{x1\<cdot>y1}"
      "ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>x,z\<rangle> = QuotientGroupRel(R,A,I)``{x1\<cdot>z1}"
      using EquivClass_1_L10[OF equiv_rel quotientBy_mul_monoid(1)]
      assms xyz1 by auto
    then have "QuotientGroupOp(R, A, I)`\<langle>ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>x,y\<rangle>,ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>x,z\<rangle>\<rangle> = QuotientGroupRel(R,A,I)``{(x1\<cdot>y1)\<ra>(x1\<cdot>z1)}"
      using EquivClass_1_L10[OF equiv_rel Group_ZF_2_4_L5A] unfolding
      QuotientGroupOp_def using assms ringAssum ideal_normal_add_subgroup
      unfolding IsAring_def using Ring_ZF_1_L4(3) xyz1(1-3) by auto
    then have "QuotientGroupOp(R, A, I)`\<langle>ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>x,y\<rangle>,ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>x,z\<rangle>\<rangle> = QuotientGroupRel(R,A,I)``{x1\<cdot>(y1\<ra>z1)}"
      using ring_oper_distr(1) xyz1 by auto
    ultimately have A:"ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>x,QuotientGroupOp(R, A, I)`\<langle>y,z\<rangle>\<rangle> = QuotientGroupOp(R, A, I)`\<langle>ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>x,y\<rangle>,ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>x,z\<rangle>\<rangle>"
      by auto
    from aux have "ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>QuotientGroupOp(R, A, I)`\<langle>y,z\<rangle>,x\<rangle> = QuotientGroupRel(R,A,I)``{(y1\<ra>z1)\<cdot>x1}"
      using EquivClass_1_L10[OF equiv_rel quotientBy_mul_monoid(1)]
      assms xyz1(1-4) Ring_ZF_1_L4(1) by auto
    moreover have "ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>y,x\<rangle> = QuotientGroupRel(R,A,I)``{y1\<cdot>x1}"
      "ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>z,x\<rangle> = QuotientGroupRel(R,A,I)``{z1\<cdot>x1}"
      using EquivClass_1_L10[OF equiv_rel quotientBy_mul_monoid(1)]
      assms xyz1 by auto
    then have "QuotientGroupOp(R, A, I)`\<langle>ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>y,x\<rangle>,ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>z,x\<rangle>\<rangle> = QuotientGroupRel(R,A,I)``{(y1\<cdot>x1)\<ra>(z1\<cdot>x1)}"
      using EquivClass_1_L10[OF equiv_rel Group_ZF_2_4_L5A] unfolding
      QuotientGroupOp_def using assms ringAssum ideal_normal_add_subgroup
      unfolding IsAring_def using Ring_ZF_1_L4(3) xyz1(1-3) by auto
    then have "QuotientGroupOp(R, A, I)`\<langle>ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>y,x\<rangle>,ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>z,x\<rangle>\<rangle> = QuotientGroupRel(R,A,I)``{(y1\<ra>z1)\<cdot>x1}"
      using ring_oper_distr(2) xyz1 by auto
    ultimately have B:"ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>QuotientGroupOp(R, A, I)`\<langle>y,z\<rangle>,x\<rangle> = QuotientGroupOp(R, A, I)`\<langle>ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>y,x\<rangle>,ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>z,x\<rangle>\<rangle>"
      by auto
    with A have "ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>x,QuotientGroupOp(R, A, I)`\<langle>y,z\<rangle>\<rangle> = QuotientGroupOp(R, A, I)`\<langle>ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>x,y\<rangle>,ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>x,z\<rangle>\<rangle>"
      "ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>QuotientGroupOp(R, A, I)`\<langle>y,z\<rangle>,x\<rangle> = QuotientGroupOp(R, A, I)`\<langle>ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>y,x\<rangle>,ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>z,x\<rangle>\<rangle>" by auto
  }
  with IsDistributive_def show "IsDistributive
     (QuotientBy(I), QuotientGroupOp(R, A, I),
      ProjFun2(R, QuotientGroupRel(R, A, I), M))" by auto
qed

text\<open>The quotient group is a ring with the quotient multiplication\<close>
theorem (in ring0) quotientBy_is_ring:
  assumes "I\<triangleleft>R"
  shows "IsAring(QuotientBy(I), QuotientGroupOp(R, A, I), ProjFun2(R, QuotientGroupRel(R, A, I), M))"
  unfolding IsAring_def using quotientBy_distributive[OF assms]
    quotientBy_mul_monoid(2)[OF assms] quotientBy_add_group[OF assms]
  by auto


text\<open>An import property satisfied by many important rings is
being Noetherian: every ideal is finitely generated.\<close>

definition (in ring0) isFinGen ("_{is finitely generated}") where
"I\<triangleleft>R \<Longrightarrow> I{is finitely generated} \<equiv> \<exists>S\<in>FinPow(R). I = \<langle>S\<rangle>\<^sub>I"


text\<open>For noetherian rings the arbitrary sum can be reduced
to the sum of a finite subset of the initial set of ideals\<close>

theorem (in ring0) sum_ideals_noetherian:
  assumes "\<forall>I\<in>\<I>. (I{is finitely generated})" "\<J> \<subseteq> \<I>"
  shows "\<exists>\<T>\<in>FinPow(\<J>). (\<oplus>\<^sub>I\<J>) = (\<oplus>\<^sub>I\<T>)"
proof-
  have JR:"(\<oplus>\<^sub>I\<J>)\<triangleleft>R" using generated_ideal_is_ideal[of "\<Union>\<J>"]
    assms(2) unfolding sumArbitraryIdeals_def[OF assms(2)]
    by auto
  with assms(1) have "(\<oplus>\<^sub>I\<J>) {is finitely generated}"
    using ideal_dest_subset by auto
  then obtain S where S:"S\<in>FinPow(R)" "(\<oplus>\<^sub>I\<J>) = \<langle>S\<rangle>\<^sub>I"
    unfolding isFinGen_def[OF JR] by auto
  from this(1) have fins:"Finite(S)" unfolding FinPow_def
    by auto
  then obtain n where n:"n\<in>nat" "S\<approx>n" unfolding Finite_def by auto
  then have "S\<lesssim>n" using eqpoll_iff by auto moreover
  let ?N = "\<lambda>s\<in>S. {J\<in>FinPow(\<J>). s\<in>(\<oplus>\<^sub>IJ)}"
  from n(1) have "{the axiom of} n {choice holds}" using finite_choice
    by auto
  ultimately have "(\<forall>t\<in>S. ?N ` t \<noteq> 0) \<longrightarrow>
           (\<exists>f. f \<in> (\<Prod>t\<in>S. ?N ` t) \<and> (\<forall>t\<in>S. f ` t \<in> ?N ` t))"
    unfolding AxiomCardinalChoiceGen_def by blast moreover
  {
    fix t assume t:"t\<in>S"
    then have "?N`t = {J\<in>FinPow(\<J>). t\<in>(\<oplus>\<^sub>IJ)}" using lamE by auto
    moreover from t have "t\<in>\<langle>S\<rangle>\<^sub>I" using generated_ideal_contains_set
      S(1) unfolding FinPow_def by auto
    with S(2) have "t\<in>(\<oplus>\<^sub>I\<J>)" by auto
    ultimately have "?N`t\<noteq>0" using sum_ideals_finite_sum[OF assms(2)]
      by auto
  }
  ultimately obtain f where f:"f:(\<Prod>t\<in>S. ?N ` t)" "\<forall>t\<in>S. f ` t \<in> ?N ` t"
    by auto
  {
    fix y assume "y\<in>f``S"
    with image_iff obtain x where x:"x\<in>S" "\<langle>x,y\<rangle>\<in>f" by auto
    with f(1) have "y\<in>?N`x" unfolding Pi_def by auto
    then have "y:{J\<in>FinPow(\<J>). x\<in>(\<oplus>\<^sub>IJ)}" using x(1) lamE by auto
    then have "Finite(y)" using lamE unfolding FinPow_def by auto
  }
  moreover 
  from f(1) have f_Fun:"f:S\<rightarrow> (\<Union>{?N`t. t:S})" unfolding Pi_def
    Sigma_def by blast
  then have "Finite(f``S)" using Finite1_L6A[of f S _ S]
    Finite_Fin_iff fins Fin_into_Finite by auto
  ultimately have A:"Finite(\<Union>(f``S))" using Finite_Union by auto
  {
    fix t assume "t\<in>\<Union>(f``S)"
    then obtain q where q:"t\<in>q" "q\<in>f``S" by auto
    then obtain s where s:"t\<in>f`s" "s\<in>S" using
      func_imagedef[OF f_Fun] by auto
    from s(2) have J:"f`s\<in>FinPow(\<J>)" "s\<in>(\<oplus>\<^sub>I(f`s))"
      using f(2) lamE by auto
    with s(1) have "t:\<J>" unfolding FinPow_def by auto
  }
  with A have B:"(\<Union>(f``S)):FinPow(\<J>)" unfolding FinPow_def by auto
  then have P:"(\<Union>(f``S)) \<subseteq> \<J>" unfolding FinPow_def by auto
  then have C:"(\<Union>(f``S)) \<subseteq> \<I>" using assms(2) by auto
  then have "(\<Union>(f``S)) \<subseteq> Pow(R)" by auto
  then have sub:"\<Union>(\<Union>(f``S)) \<subseteq> R" by auto
  {
    fix t assume t:"t\<in>S"
    then have J:"f`t\<in>FinPow(\<J>)" "t\<in>(\<oplus>\<^sub>I(f`t))"
      using f(2) lamE by auto
    from t have "\<Union>(f`t) \<subseteq> \<Union>(\<Union>(f``S))" using func_imagedef[OF f_Fun]
      by auto
    then have "\<Union>(f`t) \<subseteq> \<langle>\<Union>(\<Union>(f``S))\<rangle>\<^sub>I" using generated_ideal_contains_set
      sub by blast
    then have "\<langle>\<Union>(f`t)\<rangle>\<^sub>I \<subseteq> \<langle>\<Union>(\<Union>(f``S))\<rangle>\<^sub>I" using
      generated_ideal_is_ideal[OF sub] generated_ideal_small
      by auto
    moreover have "f`t \<subseteq> \<I>" using J(1) assms(2) unfolding FinPow_def by auto
    moreover note J(2) 
    ultimately have "t\<in>\<langle>\<Union>(\<Union>(f``S))\<rangle>\<^sub>I" using sumArbitraryIdeals_def
      by auto
    then have "t\<in>(\<oplus>\<^sub>I(\<Union>(f``S)))" using sumArbitraryIdeals_def
      C by auto
  }
  then have "S \<subseteq> \<oplus>\<^sub>I(\<Union>(f``S))" by auto
  then have "\<langle>S\<rangle>\<^sub>I \<subseteq> \<oplus>\<^sub>I(\<Union>(f``S))" using generated_ideal_small[
        OF _ generated_ideal_is_ideal[OF sub]]
    sumArbitraryIdeals_def[OF C] by auto
  with S(2) have "(\<oplus>\<^sub>I\<J>)\<subseteq> \<oplus>\<^sub>I(\<Union>(f `` S))" by auto
  moreover
  from P have "\<Union>(\<Union>(f``S)) \<subseteq> \<Union>\<J>" by auto
  then have "\<Union>(\<Union>(f``S)) \<subseteq>\<langle>\<Union>\<J>\<rangle>\<^sub>I" using 
      generated_ideal_contains_set[of "\<Union>\<J>"]
    assms(2) by blast
  then have "\<langle>\<Union>(\<Union>(f``S))\<rangle>\<^sub>I \<subseteq> \<langle>\<Union>\<J>\<rangle>\<^sub>I" using generated_ideal_small[OF _
    generated_ideal_is_ideal] assms(2) by blast
  then have "(\<oplus>\<^sub>I(\<Union>(f `` S))) \<subseteq>(\<oplus>\<^sub>I\<J>)" unfolding 
    sumArbitraryIdeals_def[OF assms(2)]
    sumArbitraryIdeals_def[OF C].
  ultimately have "(\<oplus>\<^sub>I\<J>) = \<oplus>\<^sub>I(\<Union>(f `` S))" by auto
  with B show ?thesis by auto
qed
end