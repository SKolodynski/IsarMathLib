(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

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

THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES,
INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT,
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES LOSS OF USE, DATA, OR PROFITS OR
BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open>Rings - Zariski Topology\<close>

text\<open>This file deals with the definition of the topology on the set of prime ideals\<close>

text\<open>It defines the topology, computes the closed sets and the closure and interior operators\<close>

theory Ring_Zariski_ZF imports Ring_ZF_2 Topology_ZF

begin

text\<open>The set where the topology is defined is in the spectrum
of a ring; i.e. the set of all prime ideals.\<close>

definition (in ring0) Spec where
"Spec \<equiv> {I\<in>\<I>. I\<triangleleft>\<^sub>pR}"

text\<open>The basic set that defines the topoogy is given
by the D operator\<close>

definition (in ring0) openBasic ("D") where
"S\<subseteq>R \<Longrightarrow> D(S) \<equiv> {I\<in>Spec. \<not>(S\<subseteq>I)}"

text\<open>The D operator preserves subsets\<close>

lemma (in ring0) D_operator_preserve_subset:
  assumes "S \<subseteq> T" "T\<subseteq>R"
  shows "D(S) \<subseteq> D(T)"
proof
  from assms have S:"S\<subseteq>R" by auto
  fix x assume "x\<in>D(S)"
  then have x:"x\<in>Spec" "\<not>(S\<subseteq>x)" using openBasic_def S by auto
  with assms(1) have "x\<in>Spec" "\<not>(T\<subseteq>x)" by auto
  then show "x:D(T)" using openBasic_def assms(2) by auto
qed

text\<open>The D operator values can be obtained by considering only ideals.
This is useful as we have operations on ideals that we do not have on subsets.\<close>

lemma (in ring0) D_operator_only_ideals:
  assumes "T\<subseteq>R"
  shows "D(T) = D(\<langle>T\<rangle>\<^sub>I)"
proof
  have T:"T\<subseteq>\<langle>T\<rangle>\<^sub>I" "\<langle>T\<rangle>\<^sub>I \<subseteq>R" using generated_ideal_contains_set assms
    generated_ideal_is_ideal[OF assms] ideal_dest_subset by auto
  with D_operator_preserve_subset show "D(T) \<subseteq> D(\<langle>T\<rangle>\<^sub>I)"
    by auto
  {
    fix t assume "t\<in>D(\<langle>T\<rangle>\<^sub>I)"
    with T(2) have t:"t\<in>Spec" "\<not>(\<langle>T\<rangle>\<^sub>I \<subseteq>t)" using openBasic_def by auto
    {
      assume as:"T \<subseteq> t"
      from t(1) have "t\<triangleleft>R" unfolding Spec_def primeIdeal_def by auto
      with as have "\<langle>T\<rangle>\<^sub>I \<subseteq>t" using generated_ideal_small by auto
      with t(2) have False by auto
    }
    then have "\<not>(T \<subseteq> t)" by auto
    with t(1) have "t\<in>D(T)" using openBasic_def assms by auto
  }
  then show "D(\<langle>T\<rangle>\<^sub>I) \<subseteq> D(T)" by auto
qed

text\<open>The intersection of to D-sets is the D-set on the 
product of ideals\<close>

lemma (in ring0) intersection_open_basic:
  assumes "I\<triangleleft>R" "J\<triangleleft>R"
  shows "D(I)\<inter>D(J) = D(I\<cdot>\<^sub>IJ)"
proof
  have S:"I\<cdot>\<^sub>IJ \<subseteq> R" using product_in_intersection(2) ideal_dest_subset assms by auto
  {
    fix K assume K:"K\<in>D(I)\<inter>D(J)"
    then have "K\<triangleleft>\<^sub>pR" "\<not>(I\<subseteq>K)" "\<not>(J\<subseteq>K)"
      using assms ideal_dest_subset openBasic_def 
      unfolding Spec_def by auto
    then have "\<not>(I\<subseteq>K)" "\<not>(J\<subseteq>K)" "\<forall>I\<in>\<I>. \<forall>J\<in>\<I>. I\<cdot>\<^sub>IJ\<subseteq>K \<longrightarrow> I \<subseteq> K \<or> J \<subseteq> K"
      unfolding primeIdeal_def by auto
    then have "\<not>(I\<cdot>\<^sub>IJ\<subseteq>K)" using assms unfolding ideals_def
      using ideal_dest_subset[of I] ideal_dest_subset[of J] by auto
    moreover note K
    ultimately have "K\<in>D(I\<cdot>\<^sub>IJ)" using openBasic_def[of "I"]
      ideal_dest_subset[OF assms(1)]
      unfolding Spec_def openBasic_def[OF S] by auto
  }
  then show "D(I)\<inter>D(J) \<subseteq> D(I\<cdot>\<^sub>IJ)" by auto
  {
    fix K assume Kass:"K\<in>D(I\<cdot>\<^sub>IJ)"
    then have K:"K\<triangleleft>\<^sub>pR" "\<not>(I\<cdot>\<^sub>IJ\<subseteq>K)" using openBasic_def[OF S] unfolding Spec_def by auto
    {
      assume "I \<subseteq> K \<or> J \<subseteq>K"
      then have "I\<inter>J \<subseteq> K" by auto
      then have "I\<cdot>\<^sub>IJ\<subseteq>K" using product_in_intersection assms by auto
      with K(2) have False by auto
    }
    then have "\<not>(I\<subseteq>K)" "\<not>(J\<subseteq>K)" by auto
    with Kass have "K\<in>D(I)\<inter>D(J)" using assms ideal_dest_subset
      openBasic_def[of I] openBasic_def[of J]
      unfolding openBasic_def[OF S] Spec_def by auto
  }
  then show "D(I \<cdot>\<^sub>I J) \<subseteq> D(I) \<inter> D(J)" by auto
qed

text\<open>The union of D-sets is the D-set of the sum of the ideals\<close>

lemma (in ring0) union_open_basic:
  assumes "\<J> \<subseteq> \<I>"
  shows "\<Union>{D(I). I\<in>\<J>} = D(\<oplus>\<^sub>I\<J>)"
proof
  have S:"(\<oplus>\<^sub>I\<J>) \<subseteq> R" using generated_ideal_is_ideal[of "\<Union>\<J>"] assms
      unfolding sumArbitraryIdeals_def[OF assms] ideals_def
      using ideal_dest_subset by auto
  {
    fix t assume "t\<in>\<Union>{D(I). I\<in>\<J>}"
    then obtain K where K:"K\<in>\<J>" "t\<in>D(K)" by auto
    then have t:"t\<triangleleft>\<^sub>pR" "\<not>(K\<subseteq>t)" using assms openBasic_def unfolding ideals_def Spec_def by auto
    {
      assume "(\<oplus>\<^sub>I\<J>) \<subseteq> t"
      then have "\<Union>\<J> \<subseteq> t" using generated_ideal_contains_set[of "\<Union>\<J>"]
        assms unfolding ideals_def sumArbitraryIdeals_def[OF assms] by auto
      with K(1) have "K \<subseteq> t" by auto
      with t(2) have False by auto
    }
    then have "\<not>((\<oplus>\<^sub>I\<J>) \<subseteq> t)" by auto moreover
    note K S ultimately have "t\<in>D(\<oplus>\<^sub>I\<J>)" using openBasic_def[of K] openBasic_def[of "\<oplus>\<^sub>I\<J>"]
      assms unfolding ideals_def by auto
  }
  then show "\<Union>{D(I). I\<in>\<J>} \<subseteq> D(\<oplus>\<^sub>I\<J>)" by auto
  {
    fix t assume as:"t\<in>D(\<oplus>\<^sub>I\<J>)"
    then have t:"t\<in>Spec" "\<not>((\<oplus>\<^sub>I\<J>)\<subseteq>t)" unfolding openBasic_def[OF S]
      by auto
    {
      assume "\<Union>\<J> \<subseteq> t"
      with t(1) have "\<langle>\<Union>\<J>\<rangle>\<^sub>I \<subseteq> t" using generated_ideal_small
        unfolding Spec_def primeIdeal_def
        by auto
      with t(2) have False unfolding sumArbitraryIdeals_def[OF assms]
        by auto
    }
    then obtain J where J:"\<not>(J \<subseteq> t)" "J\<in>\<J>" by auto
    note J(1) moreover have "J\<subseteq>R" using `J\<in>\<J>` assms unfolding ideals_def by auto
    moreover note t(1) ultimately have "t\<in>D(J)" using openBasic_def[of J]
      by auto
    then have "t:\<Union>{D(I). I\<in>\<J>}" using J(2) by auto
  }
  then show "D(\<oplus>\<^sub>I\<J>) \<subseteq> \<Union>{D(I). I\<in>\<J>}" by auto
qed

text\<open>From the previous results on intesertion and union,
we conclude that the D-sets we computed form a topology\<close>

corollary (in ring0) zariski_top:
  shows "{D(J). J\<in>\<I>}{is a topology}" unfolding IsATopology_def
proof(safe)
  fix M assume "M \<subseteq> {D(J). J\<in>\<I>}"
  then have "M = {D(J). J\<in>{K\<in>\<I>. D(K)\<in>M}}" by auto
  then have "\<Union>M = \<Union>{D(J). J\<in>{K\<in>\<I>. D(K)\<in>M}}" by auto
  then have "\<Union>M = D(\<oplus>\<^sub>I{K\<in>\<I>. D(K)\<in>M})" using union_open_basic by auto
  moreover have "(\<oplus>\<^sub>I{K\<in>\<I>. D(K)\<in>M})\<triangleleft>R" using
    generated_ideal_is_ideal[of "\<Union>{K\<in>\<I>. D(K)\<in>M}"]
    sumArbitraryIdeals_def [of "{K\<in>\<I>. D(K)\<in>M}"]
    unfolding ideals_def by force
  then have "(\<oplus>\<^sub>I{K\<in>\<I>. D(K)\<in>M})\<in>\<I>" using ideal_dest_subset
    unfolding ideals_def by auto
  ultimately show "\<Union>M:{D(J). J\<in>\<I>}" by auto
next
  fix x xa assume as:"x\<in>\<I>" "xa\<in>\<I>"
  then have "D(x) \<inter> D(xa) = D(x\<cdot>\<^sub>Ixa)" using intersection_open_basic
    unfolding ideals_def by auto
  moreover have "(x\<cdot>\<^sub>Ixa) \<triangleleft>R" using product_in_intersection(2)
    as unfolding ideals_def by auto
  then have "(x\<cdot>\<^sub>Ixa):\<I>" unfolding ideals_def using ideal_dest_subset by auto
  ultimately show "D(x) \<inter> D(xa)\<in>{D(J). J\<in>\<I>}" by auto
qed

text\<open>We include all the result of topology0
into ring0 under the namespace "zariski"\<close>

definition(in ring0) ZarInt ("int") where
"int(U) \<equiv> Interior(U,{D(J). J\<in>\<I>})"

definition (in ring0) ZarCl ("cl") where
"cl(U) \<equiv> Closure(U,{D(J). J\<in>\<I>})"

definition (in ring0) ZarBound ("\<partial>_") where
"\<partial>U \<equiv> Boundary(U,{D(J). J\<in>\<I>})"

sublocale ring0 < zariski:topology0 "{D(J). J\<in>\<I>}"
  ZarInt ZarCl ZarBound unfolding topology0_def
  ZarBound_def ZarInt_def ZarCl_def
  using zariski_top by auto

text\<open>The interior of a proper subset is given by the D-set
of the intersection of all the prime ideals not in that subset\<close>
lemma (in ring0) interior_zariski:
  assumes "U \<subseteq> Spec" "U\<noteq>Spec"
  shows "int(U) = D(\<Inter>(Spec-U))"
proof
  {
    fix t assume t:"t\<in>\<Inter>(Spec-U)"
    then have "\<forall>V\<in>Spec-U. t:V" by auto
    moreover from t have "(Spec-U) \<noteq>0" by auto
    ultimately obtain V where "V\<in>Spec-U" "t\<in>V" by auto
    then have "t\<in>\<Union>Spec" by auto
    then have "t\<in>R" unfolding Spec_def ideals_def by auto
  }
  then have S:"\<Inter>(Spec-U) \<subseteq> R" by auto
  {
    fix t assume "t\<in>D(\<Inter>(Spec-U))"
    then have t:"t:Spec" "\<not>(\<Inter>(Spec-U) \<subseteq> t)" using openBasic_def[OF S]
      by auto
    {
      assume "t\<notin>U"
      with t(1) have "t\<in>Spec-U" by auto
      then have "\<Inter>(Spec-U) \<subseteq> t" by auto
      then have False using t(2) by auto
    }
    then have "t\<in>U" by auto
  }
  then have "D(\<Inter>(Spec-U)) \<subseteq> U" by auto moreover
  {
    assume "Spec-U = 0"
    with assms(1) have "U=Spec" by auto
    with assms(2) have False by auto
  }
  then have P:"Spec-U \<subseteq> \<I>" "Spec-U \<noteq>0" unfolding Spec_def by auto
  then have "(\<Inter>(Spec-U))\<triangleleft>R" using intersection_ideals unfolding ideals_def by auto
  then have "(\<Inter>(Spec-U))\<in>\<I>" unfolding ideals_def using ideal_dest_subset by auto
  then have "D(\<Inter>(Spec-U)) \<in>{D(J). J\<in>\<I>}" by auto
  ultimately
  show "D(\<Inter>(Spec-U)) \<subseteq>int(U)" using zariski.Top_2_L5 by auto
  {
    fix V assume V:"V\<in>{D(J). J\<in>\<I>}" "V \<subseteq> U"
    from V(1) obtain J where J:"J:\<I>" "V=D(J)" by auto
    from V(2) have SS:"Spec-U \<subseteq> Spec-V" by auto
    {
      fix K assume K:"K\<in>Spec-U"
      {
        assume "\<not>(J\<subseteq>K)"
        with K have "K\<in>D(J)" using J(1) using openBasic_def
          unfolding ideals_def by auto
        with SS K J(2) have False by auto
      }
      then have "J\<subseteq>K" by auto
    }
    then have "J\<subseteq> \<Inter>(Spec-U)" using P(2) by auto
    then have "D(J) \<subseteq> D(\<Inter>(Spec-U))" using D_operator_preserve_subset
      S by auto
    with J(2) have "V \<subseteq>D(\<Inter>(Spec-U))" by auto
  }
  then show "int(U) \<subseteq> D(\<Inter>(Spec-U))" using
    zariski.Top_2_L1 zariski.Top_2_L2 by auto
qed

text\<open>The whole space is the D-set of the ring as an ideal of itself\<close>

lemma (in ring0) openBasic_total:
  shows "D(R) = Spec"
proof
  show "D(R) \<subseteq> Spec" using openBasic_def by auto
  {
    fix t assume t:"t\<in>Spec"
    {
      assume "R \<subseteq> t"
      then have False using t unfolding Spec_def primeIdeal_def
        using ideal_dest_subset[of t] by auto
    }
    with t have "t\<in>D(R)" using openBasic_def by auto
  }
  then show "Spec \<subseteq> D(R)" by auto
qed

corollary (in ring0) total_spec:
  shows "\<Union>{D(J). J\<in>\<I>} = Spec"
proof
  show "\<Union>{D(J). J\<in>\<I>} \<subseteq> Spec" using openBasic_def unfolding ideals_def by auto
  have "D(R)\<in>{D(J). J\<in>\<I>}" using R_ideal unfolding ideals_def by auto
  then have "D(R) \<subseteq> \<Union>{D(J). J\<in>\<I>}" by auto
  then show "Spec \<subseteq> \<Union>{D(J). J\<in>\<I>}" using openBasic_total by auto
qed

text\<open>The empty set is the D-set of the zero ideal\<close>

lemma (in ring0) openBasic_empty:
  shows "D({\<zero>}) = 0"
proof-
  {
    fix t assume t:"t\<in>D({\<zero>})"
    then have "t\<triangleleft>\<^sub>pR" "\<not>({\<zero>} \<subseteq> t)" using openBasic_def
      Ring_ZF_1_L2(1) unfolding Spec_def by auto
    then have False using ideal_dest_zero unfolding primeIdeal_def by auto
  }
  then show "D({\<zero>}) =0" by auto
qed

text\<open>A closed set is a set of primes containing a given
ideal\<close>

lemma (in ring0) closeBasic:
  assumes "U{is closed in}{D(J). J\<in>\<I>}"
  obtains J where "J\<in>\<I>" and "U={K\<in>Spec. J\<subseteq>K}"
proof-
  assume rule:"\<And>J. J \<in> \<I> \<Longrightarrow> U = {K \<in> Spec . J \<subseteq> K} \<Longrightarrow> thesis"
  from assms have U:"U\<subseteq>Spec" "Spec-U \<in> {D(J). J\<in>\<I>}" unfolding IsClosed_def
    using total_spec by auto
  then obtain J where J:"J\<in>\<I>" "Spec-U = D(J)" by auto
  moreover from U(1) have "Spec-(Spec-U) = U" by auto
  ultimately have "U = Spec-{K\<in>Spec. \<not>(J\<subseteq>K)}" using openBasic_def
    unfolding ideals_def by auto
  then have "U = {K\<in>Spec. J\<subseteq>K}" by auto
  with J show ?thesis using rule by auto
qed

text\<open>We define the closed sets as V-sets\<close>

definition (in ring0) closeBasic ("V") where
"S \<subseteq> R \<Longrightarrow> V(S) = {K\<in>Spec. S\<subseteq>K}"

text\<open>V-sets and D-sets are complementary\<close>

lemma (in ring0) V_is_closed:
  assumes "J\<in>\<I>"
  shows "Spec-V(J) = D(J)" and "V(J){is closed in}{D(J). J\<in>\<I>}"
  unfolding IsClosed_def
proof(safe)
  from assms have "V(J) \<subseteq> Spec" using closeBasic_def
    unfolding ideals_def by auto
  then show "\<And>x. x \<in> V(J) \<Longrightarrow> x \<in> \<Union>RepFun(\<I>, D)" using total_spec by auto
  show "Spec-V(J) = D(J)" using assms
    closeBasic_def openBasic_def unfolding ideals_def by auto
  with assms show "\<Union>RepFun(\<I>, D) - V(J) \<in> RepFun(\<I>, D)"
    using total_spec by auto
qed

text\<open>As with D-sets, by De Morgan's Laws we get the same result
for unions and intersections on V-sets\<close>
lemma (in ring0) V_union:
  assumes "J\<in>\<I>" "K\<in>\<I>"
  shows "V(J)\<union>V(K) = V(J\<cdot>\<^sub>IK)"
proof-
  {
    fix t assume "t\<in>V(J)"
    then have "t\<in>Spec" "J\<subseteq>t" using closeBasic_def
      assms(1) unfolding ideals_def by auto
    moreover have "J\<cdot>\<^sub>IK \<subseteq> J" using product_in_intersection(1)[of J K]
      assms unfolding ideals_def by auto
    ultimately have "t\<in>Spec" "J\<cdot>\<^sub>IK \<subseteq>t" by auto
    then have "t: V(J\<cdot>\<^sub>IK)" using closeBasic_def
      product_in_intersection(2)[of J K] assms ideal_dest_subset
      unfolding ideals_def by auto
  }
  moreover
  {
    fix t assume "t\<in>V(K)"
    then have "t\<in>Spec" "K\<subseteq>t" using closeBasic_def
      assms(2) unfolding ideals_def by auto
    moreover have "J\<cdot>\<^sub>IK \<subseteq> K" using product_in_intersection(1)[of J K]
      assms unfolding ideals_def by auto
    ultimately have "t\<in>Spec" "J\<cdot>\<^sub>IK \<subseteq>t" by auto
    then have "t: V(J\<cdot>\<^sub>IK)" using closeBasic_def
      product_in_intersection(2)[of J K] assms ideal_dest_subset
      unfolding ideals_def by auto
  }
  moreover
  {
    fix t assume "t\<in> V(J\<cdot>\<^sub>IK)"
    then have "t\<in>Spec" "J\<cdot>\<^sub>IK\<subseteq>t" using closeBasic_def
      assms product_in_intersection(2)[of J K]
      ideal_dest_subset unfolding ideals_def by auto
    then have "t\<in>Spec"  "J \<subseteq> t \<or> K \<subseteq> t" unfolding Spec_def
      primeIdeal_def using assms by auto
    then have "t\<in>V(J)\<union>V(K)" using closeBasic_def
      assms unfolding ideals_def by auto
  }
  ultimately show ?thesis by auto
qed

lemma (in ring0) V_intersect:
  assumes "\<J> \<subseteq> \<I>" "\<J> \<noteq>0"
  shows "\<Inter>{V(I). I\<in>\<J>} = V(\<oplus>\<^sub>I\<J>)"
proof-
  have "Spec - (\<Inter>{V(I). I\<in>\<J>}) = \<Union>{D(I). I\<in>\<J>}"
  proof
    {
      fix t assume "t:Spec - (\<Inter>{V(I). I\<in>\<J>})"
      then have t:"t:Spec" "t\<notin>\<Inter>{V(I). I\<in>\<J>}" by auto
      from t(2) obtain K where "(t\<notin>V(K) \<and> K\<in>\<J>) \<or> \<J>=0" by auto
      with assms(2) have "t\<notin>V(K)" "K\<in>\<J>" by auto
      with t(1) have "t\<in>Spec-V(K)" "K:\<J>" by auto moreover
      from `K:\<J>` have "Spec-V(K) = D(K)" using assms(1) V_is_closed(1) by auto
      ultimately have "t:D(K)" "K:\<J>" by auto
      then have "t\<in>\<Union>{D(I). I\<in>\<J>}" by auto
    }
    then show "Spec - (\<Inter>{V(I). I\<in>\<J>}) \<subseteq> \<Union>{D(I). I\<in>\<J>}" by auto
    {
      fix t assume "t\<in>\<Union>{D(I). I\<in>\<J>}"
      then obtain K where K:"K:\<J>" "t:D(K)" using assms(2)
        by auto
      from `K:\<J>` have "Spec-V(K) = D(K)" using assms(1) V_is_closed(1) by auto     
      with K(2) have "t:Spec-V(K)" by auto
      with K(1) have "t\<in>Spec-\<Inter>{V(I). I:\<J>}" by auto
    }
    then show "\<Union>{D(I). I\<in>\<J>} \<subseteq> Spec - (\<Inter>{V(I). I\<in>\<J>})" by auto
  qed
  then have "Spec - (\<Inter>{V(I). I\<in>\<J>}) = D(\<oplus>\<^sub>I\<J>)" using union_open_basic
    assms by auto
  then have "Spec-(Spec - (\<Inter>{V(I). I\<in>\<J>})) = Spec- D(\<oplus>\<^sub>I\<J>)" by auto
  moreover
  have JI:"(\<oplus>\<^sub>I\<J>) \<in> \<I>" using generated_ideal_is_ideal[of "\<Union>\<J>"] assms
    unfolding sumArbitraryIdeals_def[OF assms(1)] ideals_def
    using ideal_dest_subset by auto
  then have "Spec- V(\<oplus>\<^sub>I\<J>) = D(\<oplus>\<^sub>I\<J>)" using V_is_closed(1)[of "\<oplus>\<^sub>I\<J>"]
    by auto
  then have "Spec-(Spec-V(\<oplus>\<^sub>I\<J>) ) = Spec-D(\<oplus>\<^sub>I\<J>)" by auto
  ultimately have R:"Spec-(Spec - (\<Inter>{V(I). I\<in>\<J>})) = Spec-(Spec-V(\<oplus>\<^sub>I\<J>) )"
    by auto
  {
    fix t assume t:"t\<in>\<Inter>{V(I). I\<in>\<J>}"
    with assms(2) obtain I where "I:\<J>" "t:V(I)" by auto
    then have "t\<in>Spec" using closeBasic_def assms(1) unfolding ideals_def
      by auto
    with t have "t\<in>Spec-(Spec - (\<Inter>{V(I). I\<in>\<J>}))" by auto
    with R have "t\<in>Spec-(Spec-V(\<oplus>\<^sub>I\<J>) )" by auto
    then have "t\<in>V(\<oplus>\<^sub>I\<J>)" by auto
  } moreover
  {
    fix t assume t:"t\<in>V(\<oplus>\<^sub>I\<J>)"
    with JI have "t:Spec" using closeBasic_def unfolding ideals_def by auto
    with t have "t\<in>Spec-(Spec-V(\<oplus>\<^sub>I\<J>) )" by auto
    then have "t\<in>Spec-(Spec - (\<Inter>{V(I). I\<in>\<J>}))" using R by auto
    then have "t\<in>\<Inter>{V(I). I\<in>\<J>}" by auto
  }
  ultimately show ?thesis by force
qed

text\<open>The closure of a set is the V-set of the intersection
of all its points.\<close>
lemma (in ring0) closure_zariski:
  assumes "U \<subseteq> Spec" "U\<noteq>0"
  shows "cl(U) = V(\<Inter>U)"
proof
  have "U \<subseteq> \<I>" using assms(1) unfolding Spec_def by auto
  then have ideal:"(\<Inter>U)\<triangleleft>R" using intersection_ideals[of U] assms(2)
    unfolding ideals_def by auto
  {
    fix t assume t:"t\<in>V(\<Inter>U)"
    {
      fix q assume q:"q\<in>\<Inter>U"
      with q obtain M where "M:U" "q:M" using assms(2) by blast
      with assms have "q\<in>\<Union>Spec" by auto
      then have "q:R" unfolding Spec_def ideals_def by auto
    }
    then have sub:"\<Inter>U \<subseteq> R" by auto
    with t have tt:"t\<in>Spec" "\<Inter>U \<subseteq> t" using closeBasic_def by auto
    {
      fix VV assume VV:"VV\<in>{D(J). J\<in>\<I>}" "t\<in>VV"
      then obtain J where J:"VV= D(J)" "J\<in>\<I>" by auto
      from VV(2) J have jt:"\<not>(J \<subseteq> t)" using openBasic_def
        unfolding ideals_def by auto
      {
        assume "U\<inter>D(J) = 0"
        then have "\<forall>x\<in>U. x\<notin>D(J)" by auto
        with J(2) have "\<forall>x\<in>U. J\<subseteq>x" using openBasic_def[of J]
          assms(1) unfolding ideals_def by auto
        then have "J\<subseteq> \<Inter>U \<or> U=0" by auto 
        with tt(2) jt have False using assms(2) by auto
      }
      then have "U\<inter>VV \<noteq> 0" using J(1) by auto
    }
    then have R:"\<forall>VV\<in>{D(J). J\<in>\<I>}. t\<in>VV \<longrightarrow> VV\<inter>U \<noteq> 0" by auto
    from tt(1) assms(1) have RR:"t\<in>\<Union>{D(J). J\<in>\<I>}" "U \<subseteq> \<Union>{D(J). J\<in>\<I>}"
      using total_spec by auto
    have "t\<in>cl(U)" using zariski.inter_neigh_cl[OF RR(2,1) R].
  }
  then show "V(\<Inter>U) \<subseteq> cl(U)"
    apply (rule subsetI) by auto
  {
    fix p assume p:"p\<in>U"
    then have "\<Inter>U \<subseteq>p" by auto
    moreover
    from p assms(1) have "p\<in>Spec" "\<Inter>U\<subseteq>\<Union>Spec" by auto
    then have "p\<in>Spec" "\<Inter>U\<subseteq>R" unfolding Spec_def ideals_def by auto
    ultimately have "p\<in>V(\<Inter>U)" using closeBasic_def[of "\<Inter>U"]
      by auto
  }
  then have A:"U\<subseteq>V(\<Inter>U)" by auto
  have B:"V(\<Inter>U){is closed in}{D(J). J\<in>\<I>}"
    using V_is_closed(2) ideal ideal_dest_subset unfolding ideals_def by auto
  show "cl(U) \<subseteq> V(\<Inter>U)"
    apply (rule zariski.Top_3_L13[of "V(\<Inter>U)" U])
    using A B by auto
qed
end