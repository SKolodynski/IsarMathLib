(*
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2024  Daniel de la Concepcion

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

section \<open>Rings - Commutative Rings\<close>

theory Ring_ZF_4 imports Ring_ZF_2 CommutativeSemigroup_ZF

begin

text\<open>This theory develops the theory of commutative rings. We define the
  \<open>commutative_ring\<close> locale, characterize principal ideals, and study the
  relationship between prime rings, prime ideals, and the absence of zero divisors.\<close>

subsection\<open>Commutative rings\<close>

text\<open>A commutative ring is a ring in which multiplication satisfies the
  commutativity law. We establish that principal ideals take a simple form
  in this setting.\<close>

text\<open>A commutative ring is defined as a \<open>ring0\<close> in which multiplication
  is commutative.\<close>

locale commutative_ring = ring0 +
  assumes commutative:"M{is commutative on}R" 

text\<open>For any element $x$ of a commutative ring, the set $\{x \cdot y \mid y \in R\}$
  is an ideal of the ring.\<close>

lemma (in commutative_ring) mult_by_elem:
  assumes "x\<in>R"
  shows "{x\<cdot>y. y\<in>R}\<triangleleft>R"
proof-
  have "x\<cdot>\<one>\<in>{x\<cdot>y. y\<in>R}" using Ring_ZF_1_L2(2) by auto
  then have I:"{x\<cdot>y. y\<in>R}\<noteq>0" by auto
  {
    fix t assume t:"t\<in>{x \<cdot> y . y \<in> R}"
    then obtain y where y:"y\<in>R" "t=x\<cdot>y" by auto
    then have "t\<in>R" using Ring_ZF_1_L4(3) assms by auto
  }
  then have II:"{x \<cdot> y . y \<in> R} \<subseteq> R" by auto
  {
    fix t h assume ty:"t\<in>{x \<cdot> y . y \<in> R}" "h\<in>R"
    from ty(1) obtain y where y:"y:R" "t=x\<cdot>y" by auto
    from y(2) have "t\<cdot>h=(x\<cdot>y)\<cdot>h" by auto
    then have "t\<cdot>h= x\<cdot>(y\<cdot>h)" using Ring_ZF_1_L11(2)
      assms y(1) ty(2) by auto
    moreover have "y\<cdot>h\<in>R" using y(1) ty(2) using Ring_ZF_1_L4(3) by auto
    ultimately have E1:"t\<cdot>h\<in>{x \<cdot> y . y \<in> R}" by auto
  }
  then have III: "\<forall>t\<in>{x \<cdot> y . y \<in> R}. \<forall>h\<in>R. t \<cdot> h \<in> {x \<cdot> y . y \<in> R}" by auto
  {
    fix t h assume ty:"t\<in>{x \<cdot> y . y \<in> R}" "h\<in>R"
    from ty(1) obtain y where y:"y:R" "t=x\<cdot>y" by auto
    from y(2) have "h\<cdot>t = h\<cdot>(x\<cdot>y)" by auto
    then have "h\<cdot>t = h\<cdot>(y\<cdot>x)" using commutative assms y(1)
      unfolding IsCommutative_def by auto
    then have "h\<cdot>t = (h\<cdot>y)\<cdot>x" using Ring_ZF_1_L11(2)
      assms y(1) ty(2) by auto
    moreover have "h\<cdot>y\<in>R" using y(1) ty(2) using Ring_ZF_1_L4(3) by auto
    ultimately have "h\<cdot>t = x\<cdot>(h\<cdot>y)" "h\<cdot>y\<in>R" using commutative assms
      unfolding IsCommutative_def by auto
    then have "h\<cdot>t\<in>{x \<cdot> y . y \<in> R}" by auto
  }
  then have IV: " \<forall>t\<in>{x \<cdot> y . y \<in> R}. \<forall>h\<in>R. h \<cdot> t \<in> {x \<cdot> y . y \<in> R}" by auto
  {
    fix t h assume th:"t:{x \<cdot> y . y \<in> R}" "h:{x \<cdot> y . y \<in> R}"
    then obtain yt yh where y:"t=x\<cdot>yt" "yt:R" "h=x\<cdot>yh" "yh:R" by auto
    then have "t\<ra>h = (x\<cdot>yt)\<ra>(x\<cdot>yh)" by auto
    then have "t\<ra>h = x\<cdot>(yt\<ra>yh)" using ring_oper_distr(1) assms
      y(2,4) by auto
    moreover have "yt\<ra>yh :R" using y(2,4) Ring_ZF_1_L4(1) by auto
    ultimately have "t\<ra>h:{x \<cdot> y . y \<in> R}" by auto
  }
  then have V: "\<forall>xa\<in>{x \<cdot> y . y \<in> R}. \<forall>y\<in>{x \<cdot> y . y \<in> R}. xa \<ra> y \<in> {x \<cdot> y . y \<in> R}" by auto
  from I II III IV V show ?thesis using ideal_intro by auto
qed

text\<open>In a commutative ring the principal ideal generated by an element $x$
  equals $\{x \cdot y \mid y \in R\}$.\<close>

theorem (in commutative_ring) principal_ideal:
  assumes "x\<in>R"
  shows "\<langle>{x}\<rangle>\<^sub>I = {x \<cdot> y . y \<in> R}"
proof
  have "x\<cdot>\<one>\<in>{x\<cdot>y. y\<in>R}" using Ring_ZF_1_L2(2) by auto
  then have xx:"x\<in>{x\<cdot>y. y\<in>R}" using Ring_ZF_1_L3(5) assms by auto
  then show "\<langle>{x}\<rangle>\<^sub>I \<subseteq> {x \<cdot> y . y \<in> R}"
    using generated_ideal_small mult_by_elem assms by auto
  {
    fix J assume j:"{x} \<subseteq> J" "J\<triangleleft>R" "J\<in>Pow(R)"
    {
      fix t assume t:"t\<in>{x \<cdot> y . y \<in> R}"
      then obtain y where y:"y:R" "t=x\<cdot>y" by auto
      with j have "t\<in>J" using ideal_dest_mult(1) by auto
    }
    then have "{x \<cdot> y . y \<in> R} \<subseteq> J" by auto
  } moreover
  have "{x \<cdot> y . y \<in> R}\<in>{J\<in>Pow(R). J \<triangleleft>R \<and> {x}\<subseteq>J}"
    using assms Ring_ZF_1_L4(3) xx mult_by_elem by auto
  then have "{J\<in>Pow(R). J \<triangleleft>R \<and> {x}\<subseteq>J}\<noteq>0" by auto
  ultimately have "{x \<cdot> y . y \<in> R} \<subseteq> \<Inter>{J\<in>Pow(R). J \<triangleleft>R \<and> {x}\<subseteq>J}" by auto
  then show "{x \<cdot> y . y \<in> R} \<subseteq> \<langle>{x}\<rangle>\<^sub>I"
    using generatedIdeal_def assms by auto
qed

subsection\<open>Prime ideals\<close>

text\<open>We characterize prime rings in terms of zero divisors and show that
  the quotient of a ring by a prime ideal is a prime ring, or equivalently,
  has no zero divisors in the commutative case.\<close>

text\<open>Commutative prime rings are the same as
commutative rings with no zero divisors.\<close>

lemma (in commutative_ring) prime_ring_zero_divs_1:
  assumes "[R,A,M]{is a prime ring}"
  shows "HasNoZeroDivs(R,A,M)"
proof -
  {
    fix aa b assume as:"aa\<in>R" "b\<in>R" "M ` \<langle>aa, b\<rangle> =TheNeutralElement(R,A)" "b\<noteq>TheNeutralElement(R,A)"
    with assms have "(\<forall>z\<in>R. M ` \<langle>M ` \<langle>aa, z\<rangle>, b\<rangle> = \<zero>) \<longrightarrow>
                   (aa = \<zero> \<or> b = \<zero>)" using primeRing_def ringAssum by auto
    moreover
    {
      fix z assume z:"z\<in>R"
      have "(aa\<cdot>z)\<cdot>b = (z\<cdot>aa)\<cdot>b" using as(1) z(1)
        commutative unfolding IsCommutative_def by auto
      then have "(aa\<cdot>z)\<cdot>b = z\<cdot>(aa\<cdot>b)" using Ring_ZF_1_L11(2)
        as z by auto
      then have "(aa\<cdot>z)\<cdot>b = z\<cdot>\<zero>" using as(3) by auto
      then have "(aa\<cdot>z)\<cdot>b = \<zero>" using Ring_ZF_1_L6(2) z by auto
    }
    ultimately have "aa = \<zero> \<or> b = \<zero>" by auto
    with as(4) have "aa=TheNeutralElement(R,A)" by auto
  }
  then show ?thesis unfolding HasNoZeroDivs_def by auto
qed

text\<open>A commutative ring with no zero divisors is a prime ring.\<close>

lemma (in commutative_ring) prime_ring_zero_divs_2:
  assumes "HasNoZeroDivs(R,A,M)"
  shows "[R,A,M]{is a prime ring}"
proof -
  {
    fix aa b assume as:"aa\<in>R" "b\<in>R" "\<forall>z\<in>R. M ` \<langle>M ` \<langle>aa, z\<rangle>, b\<rangle> = TheNeutralElement(R, A)" 
      "b\<noteq>TheNeutralElement(R,A)"
    with assms have "\<forall>c\<in>R. \<forall>b\<in>R. M ` \<langle>c, b\<rangle> = \<zero> \<longrightarrow>
                   c = \<zero> \<or> b = \<zero>" unfolding HasNoZeroDivs_def by auto
    with as(1,2) have "M ` \<langle>aa, b\<rangle> = \<zero> \<longrightarrow> aa = \<zero> \<or> b = \<zero>" by auto
    with as(4) have "M ` \<langle>aa, b\<rangle> = \<zero> \<longrightarrow> aa = \<zero>" by auto
    moreover
    from as(3) have "M`\<langle>M ` \<langle>aa, \<one>\<rangle>, b\<rangle> = \<zero>" using Ring_ZF_1_L2(2) by auto
    then have "aa\<cdot>b = \<zero>" using Ring_ZF_1_L3(5) as(1) by auto
    ultimately have "aa = TheNeutralElement(R, A)" by auto
  }
  then show ?thesis using primeRing_def ringAssum by auto
qed

text\<open>The quotient ring of a ring by a prime ideal is a prime ring.\<close>

theorem (in ring0) prime_ideal_no_zero_divs:
  assumes "I\<triangleleft>\<^sub>pR"
  shows "[QuotientBy(I),QuotientGroupOp(R, A, I),ProjFun2(R, QuotientGroupRel(R, A, I), M)]{is a prime ring}"
proof-
  have ideal:"I\<triangleleft>R" using assms unfolding primeIdeal_def by auto
  from primeRing_def quotientBy_is_ring assms have "
    (\<forall>x\<in>QuotientBy(I).
       \<forall>y\<in>QuotientBy(I).
          (\<forall>z\<in>QuotientBy(I).
              ProjFun2(R, QuotientGroupRel(R, A, I), M) `
              \<langle>ProjFun2(R, QuotientGroupRel(R, A, I), M) ` \<langle>x, z\<rangle>, y\<rangle> =
              TheNeutralElement(QuotientBy(I), QuotientGroupOp(R, A, I))) \<longrightarrow>
          x = TheNeutralElement(QuotientBy(I), QuotientGroupOp(R, A, I)) \<or>
          y = TheNeutralElement(QuotientBy(I), QuotientGroupOp(R, A, I))) \<longrightarrow>
[QuotientBy
      (I),QuotientGroupOp
           (R, A, I),ProjFun2(R, QuotientGroupRel(R, A, I), M)]{is a prime ring}" 
    unfolding primeIdeal_def by auto moreover
  have "\<forall>x\<in>QuotientBy(I).
       \<forall>y\<in>QuotientBy(I).
          (\<forall>z\<in>QuotientBy(I).
              ProjFun2(R, QuotientGroupRel(R, A, I), M) `
              \<langle>ProjFun2(R, QuotientGroupRel(R, A, I), M) ` \<langle>x, z\<rangle>, y\<rangle> =
              TheNeutralElement(QuotientBy(I), QuotientGroupOp(R, A, I))) \<longrightarrow>
          x = TheNeutralElement(QuotientBy(I), QuotientGroupOp(R, A, I)) \<or>
          y = TheNeutralElement(QuotientBy(I), QuotientGroupOp(R, A, I))"
  proof -
    {
    fix x y assume as:"x\<in>QuotientBy(I)" "y\<in>QuotientBy(I)" "\<forall>z\<in>QuotientBy(I).
              ProjFun2(R, QuotientGroupRel(R, A, I), M) `
              \<langle>ProjFun2(R, QuotientGroupRel(R, A, I), M) ` \<langle>x, z\<rangle>, y\<rangle> =
              TheNeutralElement(QuotientBy(I), QuotientGroupOp(R, A, I))"
      "y \<noteq> TheNeutralElement(QuotientBy(I), QuotientGroupOp(R, A, I))"
    {
      fix xx assume xx:"xx\<in>R" "QuotientGroupRel(R, A, I)``{xx} = x"
      {
        fix yy assume yy:"yy\<in>R" "QuotientGroupRel(R, A, I)``{yy} = y"
        {
          fix zz assume zz:"zz\<in>R"
          from ideal have equiv:"equiv(R, QuotientGroupRel(R, A, I))" and 
            cong2:"Congruent2(QuotientGroupRel(R, A, I), M)" using ideal_equiv_rel quotientBy_mul_monoid(1) by auto
          have "\<And>x y r f. equiv(R,r) \<Longrightarrow> Congruent2(r,f) \<Longrightarrow> x\<in>R \<Longrightarrow> y\<in>R \<Longrightarrow> ProjFun2(R, r, f) ` 
              \<langle>r `` {x}, r `` {y}\<rangle> =
                r ``{f ` \<langle>x, y\<rangle>}" using EquivClass_1_L10 by auto
          then have "\<And>x y. equiv(R,  QuotientGroupRel(R, A, I)) \<Longrightarrow> Congruent2( QuotientGroupRel(R, A, I),M) \<Longrightarrow> x\<in>R \<Longrightarrow> y\<in>R
            \<Longrightarrow> ProjFun2(R, QuotientGroupRel(R, A, I), M) ` 
              \<langle>QuotientGroupRel(R, A, I) `` {x},  QuotientGroupRel(R, A, I) `` {y}\<rangle> =
                QuotientGroupRel(R, A, I) ``{M ` \<langle>x, y\<rangle>}" by auto
          with equiv cong2
          have eq:"\<And>x y. x\<in>R \<Longrightarrow> y\<in>R \<Longrightarrow> ProjFun2(R, QuotientGroupRel(R, A, I), M) ` 
              \<langle>QuotientGroupRel(R, A, I) `` {x},  QuotientGroupRel(R, A, I) `` {y}\<rangle> =
                QuotientGroupRel(R, A, I) ``{M ` \<langle>x, y\<rangle>}" by auto
          have "QuotientGroupRel(R, A, I)``{xx\<cdot>zz\<cdot>yy} = 
            ProjFun2(R, QuotientGroupRel(R, A, I), M)`\<langle>QuotientGroupRel(R, A, I)``{xx\<cdot>zz},QuotientGroupRel(R, A, I)``{yy}\<rangle>"
            using eq xx(1) yy(1) zz Ring_ZF_1_L4(3) by auto
          then have "QuotientGroupRel(R, A, I)``{xx\<cdot>zz\<cdot>yy} = 
            ProjFun2(R, QuotientGroupRel(R, A, I), M)`\<langle>ProjFun2(R, QuotientGroupRel(R, A, I), M)`\<langle>QuotientGroupRel(R, A, I)``{xx},QuotientGroupRel(R, A, I)``{zz}\<rangle>,QuotientGroupRel(R, A, I)``{yy}\<rangle>"
            using eq xx(1) zz by auto
          with xx(2) yy(2) have "QuotientGroupRel(R, A, I)``{xx\<cdot>zz\<cdot>yy} = 
            ProjFun2(R, QuotientGroupRel(R, A, I), M)`\<langle>ProjFun2(R, QuotientGroupRel(R, A, I), M)`\<langle>x,QuotientGroupRel(R, A, I)``{zz}\<rangle>,y\<rangle>"
            by auto
          moreover have "QuotientGroupRel(R, A, I)``{zz}\<in>QuotientBy(I)" using QuotientBy_def ideal zz
            unfolding quotient_def by auto
          moreover note as(3) ultimately
          have "QuotientGroupRel(R, A, I)``{xx\<cdot>zz\<cdot>yy} = TheNeutralElement(QuotientBy(I), QuotientGroupOp(R, A, I))"
            by auto
          then have "xx\<cdot>zz\<cdot>yy\<in>I" using add_group.Group_ZF_2_4_L5E ideal_normal_add_subgroup
            xx(1) yy(1) zz Ring_ZF_1_L4(3) QuotientBy_def ideal by auto
        }
        then have "\<forall>zz\<in>R. xx\<cdot>zz\<cdot>yy\<in>I" by auto
        then have D:"xx:I\<or>yy:I" using assms equivalent_prime_ideal
          xx(1) yy(1) by auto
        {
          assume "yy\<in>I"
          then have False using add_group.Group_ZF_2_4_L5E ideal_normal_add_subgroup yy as(4)
            QuotientBy_def ideal by auto
        }
        with D have "xx\<in>I" by auto
      } moreover
      have "\<And>P. y \<in> R // QuotientGroupRel(R, A, I) \<Longrightarrow>
        (\<And>x. y = QuotientGroupRel(R, A, I) `` {x} \<Longrightarrow> x \<in> R \<Longrightarrow> P) \<Longrightarrow> P" by (rule quotientE)
      then have " y \<in> R // QuotientGroupRel(R, A, I) \<Longrightarrow>
        (\<And>x. y = QuotientGroupRel(R, A, I) `` {x} \<Longrightarrow> x \<in> R \<Longrightarrow> xx\<in>I) \<Longrightarrow> xx\<in>I" by (rule quotientE)
      ultimately have "xx\<in>I" using as(2) QuotientBy_def ideal by auto
      then have "QuotientGroupRel(R, A, I)``{xx} = TheNeutralElement(QuotientBy(I), QuotientGroupOp(R, A, I))"
        using add_group.Group_ZF_2_4_L5E ideal_normal_add_subgroup 
        QuotientBy_def ideal xx(1) by auto
      with xx(2) have "x = TheNeutralElement(QuotientBy(I), QuotientGroupOp(R, A, I))" by auto
    } moreover
    have "\<And>P. x \<in> R // QuotientGroupRel(R, A, I) \<Longrightarrow>
        (\<And>t. x = QuotientGroupRel(R, A, I) `` {t} \<Longrightarrow> t \<in> R \<Longrightarrow> P) \<Longrightarrow> P" by (rule quotientE)
    then have "x \<in> R // QuotientGroupRel(R, A, I) \<Longrightarrow>
        (\<And>t. x = QuotientGroupRel(R, A, I) `` {t} \<Longrightarrow> t \<in> R \<Longrightarrow> x = TheNeutralElement(QuotientBy(I), QuotientGroupOp(R, A, I)))
         \<Longrightarrow> x = TheNeutralElement(QuotientBy(I), QuotientGroupOp(R, A, I))" by (rule quotientE)
    ultimately
    have "x = TheNeutralElement(QuotientBy(I), QuotientGroupOp(R, A, I))" using as(1) QuotientBy_def ideal by auto
    }
    then show ?thesis by auto
  qed
  ultimately show ?thesis by auto
qed

text\<open>In a commutative ring, the quotient by a prime ideal has no zero divisors.
  This is a specialization of \<open>prime_ideal_no_zero_divs\<close> using commutativity
  to convert the prime ring condition directly into the no-zero-divisors property.\<close>

theorem (in commutative_ring) comm_prime_ideal_no_zero_divs:
  assumes "I\<triangleleft>\<^sub>pR"
  shows "HasNoZeroDivs(QuotientBy(I), QuotientGroupOp(R,A,I), ProjFun2(R, QuotientGroupRel(R,A,I), M))"
proof -
  have ideal:"I\<triangleleft>R" using assms unfolding primeIdeal_def by auto
  {
    fix xx yy assume as:
      "xx\<in>QuotientBy(I)" "yy\<in>QuotientBy(I)"
      "ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>xx,yy\<rangle> =
         TheNeutralElement(QuotientBy(I), QuotientGroupOp(R,A,I))"
      "yy \<noteq> TheNeutralElement(QuotientBy(I), QuotientGroupOp(R,A,I))"
    {
      fix xx0 assume xx0:"xx0\<in>R" "QuotientGroupRel(R,A,I)``{xx0} = xx"
      {
        fix yy0 assume yy0:"yy0\<in>R" "QuotientGroupRel(R,A,I)``{yy0} = yy"
        have "ProjFun2(R, QuotientGroupRel(R,A,I), M)`\<langle>xx,yy\<rangle> =
            QuotientGroupRel(R,A,I)``{xx0\<cdot>yy0}"
          using EquivClass_1_L10 ideal_equiv_rel quotientBy_mul_monoid(1) ideal
            xx0 yy0 by auto
        with as(3) have prod_in_I:"xx0\<cdot>yy0\<in>I"
          using add_group.Group_ZF_2_4_L5E ideal_normal_add_subgroup
            xx0(1) yy0(1) Ring_ZF_1_L4(3) QuotientBy_def ideal by auto
        {
          fix zz assume zz:"zz\<in>R"
          have "xx0\<cdot>zz\<cdot>yy0 = (xx0\<cdot>zz)\<cdot>yy0" by auto
          moreover have "(xx0\<cdot>zz)\<cdot>yy0 = yy0\<cdot>(xx0\<cdot>zz)"
            using commutative xx0(1) yy0(1) zz Ring_ZF_1_L4(3)
            unfolding IsCommutative_def by auto
          moreover have "yy0\<cdot>(xx0\<cdot>zz) = (yy0\<cdot>xx0)\<cdot>zz"
            using Ring_ZF_1_L11(2) yy0(1) xx0(1) zz by auto
          moreover have "(yy0\<cdot>xx0)\<cdot>zz = (xx0\<cdot>yy0)\<cdot>zz"
            using commutative xx0(1) yy0(1) unfolding IsCommutative_def by auto
          ultimately have "xx0\<cdot>zz\<cdot>yy0 = (xx0\<cdot>yy0)\<cdot>zz" by auto
          then have "xx0\<cdot>zz\<cdot>yy0\<in>I"
            using ideal_dest_mult(1) ideal prod_in_I zz by auto
        }
        then have "\<forall>zz\<in>R. xx0\<cdot>zz\<cdot>yy0\<in>I" by auto
        then have D:"xx0\<in>I \<or> yy0\<in>I"
          using assms equivalent_prime_ideal xx0(1) yy0(1) by auto
        {
          assume "yy0\<in>I"
          then have False
            using add_group.Group_ZF_2_4_L5E ideal_normal_add_subgroup yy0 as(4)
              QuotientBy_def ideal by auto
        }
        with D have "xx0\<in>I" by auto
      } moreover
      have "\<And>P. yy \<in> R // QuotientGroupRel(R, A, I) \<Longrightarrow>
          (\<And>t. yy = QuotientGroupRel(R, A, I) `` {t} \<Longrightarrow> t \<in> R \<Longrightarrow> P) \<Longrightarrow> P" by (rule quotientE)
      then have "yy \<in> R // QuotientGroupRel(R, A, I) \<Longrightarrow>
          (\<And>t. yy = QuotientGroupRel(R, A, I) `` {t} \<Longrightarrow> t \<in> R \<Longrightarrow> xx0\<in>I)
           \<Longrightarrow> xx0\<in>I" by (rule quotientE)
      ultimately have "xx0\<in>I" using as(2) QuotientBy_def ideal by auto
      then have "QuotientGroupRel(R,A,I)``{xx0} =
          TheNeutralElement(QuotientBy(I), QuotientGroupOp(R,A,I))"
        using add_group.Group_ZF_2_4_L5E ideal_normal_add_subgroup
        QuotientBy_def ideal xx0(1) by auto
      with xx0(2) have "xx = TheNeutralElement(QuotientBy(I), QuotientGroupOp(R,A,I))" by auto
    } moreover
    have "\<And>P. xx \<in> R // QuotientGroupRel(R, A, I) \<Longrightarrow>
        (\<And>t. xx = QuotientGroupRel(R, A, I) `` {t} \<Longrightarrow> t \<in> R \<Longrightarrow> P) \<Longrightarrow> P" by (rule quotientE)
    then have "xx \<in> R // QuotientGroupRel(R, A, I) \<Longrightarrow>
        (\<And>t. xx = QuotientGroupRel(R, A, I) `` {t} \<Longrightarrow> t \<in> R \<Longrightarrow> xx = TheNeutralElement(QuotientBy(I), QuotientGroupOp(R,A,I)))
         \<Longrightarrow> xx = TheNeutralElement(QuotientBy(I), QuotientGroupOp(R,A,I))" by (rule quotientE)
    ultimately
    have "xx = TheNeutralElement(QuotientBy(I), QuotientGroupOp(R,A,I))"
      using as(1) QuotientBy_def ideal by auto
  }
  then show ?thesis unfolding HasNoZeroDivs_def by auto
qed

end