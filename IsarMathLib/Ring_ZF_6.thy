(*
    This file is a part of IsarMathLib -
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2026  Daniel de la Concepcion

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

section \<open>Rings - localization\<close>

theory Ring_ZF_6 imports Ring_ZF_4 Ring_ZF_3 EquivClass1

begin

text\<open>This theory defines the localization $S^{-1}R$ of a commutative ring $R$ at a
  multiplicatively closed subset $S$. Elements of the localization are equivalence
  classes of pairs $(r,s)\in R\times S$, thought of as fractions $r/s$.\<close>

subsection\<open>Multiplicative subsets and the fraction relation\<close>

text\<open>A multiplicative subset of a commutative ring is a subset that contains
  the unit and is closed under multiplication. The locale \<open>mult_subset\<close> adds such a set $S$
  to the \<open>commutative_ring\<close> context.\<close>

locale mult_subset = commutative_ring +
  fixes S
  assumes S_subset: "S \<subseteq> R"
  assumes S_one: "\<one> \<in> S"
  assumes S_closed_oper: "S {is closed under} M"

text\<open>Closure of $S$ under the ring multiplication, spelled out.\<close>

lemma (in mult_subset) S_closed:
  shows "\<forall>s\<in>S. \<forall>t\<in>S. s\<cdot>t \<in> S"
  using S_closed_oper unfolding IsOpClosed_def by simp

text\<open>Two fractions $r_1/s_1$ and $r_2/s_2$ are identified when
  $t\cdot (r_1 s_2) = t\cdot (r_2 s_1)$ for some $t\in S$. (The factor $t$ is needed
  when $R$ has zero divisors.)\<close>

definition
  "LocRel(R,M,S) \<equiv> {\<langle>p,q\<rangle> \<in> (R\<times>S)\<times>(R\<times>S).
  \<exists>t\<in>S. M`\<langle>t,M`\<langle>fst(p),snd(q)\<rangle>\<rangle> = M`\<langle>t,M`\<langle>fst(q),snd(p)\<rangle>\<rangle>}"

text\<open>Addition of fractions: $r_1/s_1 + r_2/s_2 = (r_1 s_2 + r_2 s_1)/(s_1 s_2)$.
  This is an operation on the set of pairs $R\times S$, to be projected to the quotient.\<close>

definition
  "LocAdd(R,A,M,S) \<equiv> {\<langle>x,\<langle>A`\<langle>M`\<langle>fst(fst(x)),snd(snd(x))\<rangle>,M`\<langle>fst(snd(x)),snd(fst(x))\<rangle>\<rangle>,
  M`\<langle>snd(fst(x)),snd(snd(x))\<rangle>\<rangle>\<rangle>. x\<in>(R\<times>S)\<times>(R\<times>S)}"

text\<open>Multiplication of fractions: $(r_1/s_1)\cdot (r_2/s_2) = (r_1 r_2)/(s_1 s_2)$.\<close>

definition
  "LocMul(R,M,S) \<equiv> {\<langle>x,\<langle>M`\<langle>fst(fst(x)),fst(snd(x))\<rangle>,
  M`\<langle>snd(fst(x)),snd(snd(x))\<rangle>\<rangle>\<rangle>. x\<in>(R\<times>S)\<times>(R\<times>S)}"

text\<open>The localization consists of the equivalence classes of the fraction relation.\<close>

definition
  "Localization(R,M,S) \<equiv> (R\<times>S)//LocRel(R,M,S)"

text\<open>The operations of the localization are the projections of \<open>LocAdd\<close>
  to the quotient.\<close>

definition
  "LocalizedAdd(R,A,M,S) \<equiv> ProjFun2(R\<times>S,LocRel(R,M,S),LocAdd(R,A,M,S))"

text\<open>The multiplication of the localization is the projection of \<open>LocMul\<close>.\<close>

definition
  "LocalizedMul(R,M,S) \<equiv> ProjFun2(R\<times>S,LocRel(R,M,S),LocMul(R,M,S))"

text\<open>The class of $(r,s)$, i.e. the fraction $r/s$.\<close>

definition
  "Fraction(R,M,S,r,s) \<equiv> LocRel(R,M,S)``{\<langle>r,s\<rangle>}"

subsection\<open>The fraction relation is an equivalence\<close>

text\<open>Membership in the fraction relation unfolds to the defining condition.\<close>

lemma (in mult_subset) loc_rel_iff:
  assumes "r1\<in>R" "s1\<in>S" "r2\<in>R" "s2\<in>S"
  shows "\<langle>\<langle>r1,s1\<rangle>,\<langle>r2,s2\<rangle>\<rangle> \<in> LocRel(R,M,S) \<longleftrightarrow>
  (\<exists>t\<in>S. t\<cdot>(r1\<cdot>s2) = t\<cdot>(r2\<cdot>s1))"
  using assms unfolding LocRel_def by auto

text\<open>The fraction relation is an equivalence relation on $R\times S$.\<close>

theorem (in mult_subset) loc_rel_equiv:
  shows "equiv(R\<times>S,LocRel(R,M,S))"
proof -
  have sub: "LocRel(R,M,S) \<subseteq> (R\<times>S)\<times>(R\<times>S)" unfolding LocRel_def by auto
  have refl: "refl(R\<times>S,LocRel(R,M,S))"
    unfolding refl_def
  proof
    fix x assume "x\<in>R\<times>S"
    then obtain r s where x: "x=\<langle>r,s\<rangle>" "r\<in>R" "s\<in>S" by auto
    with S_subset show "\<langle>x,x\<rangle>\<in>LocRel(R,M,S)"
      using loc_rel_iff S_one by auto
  qed
  have sym: "sym(LocRel(R,M,S))"
    unfolding sym_def
  proof (intro allI impI)
    fix x y assume xy: "\<langle>x,y\<rangle>\<in>LocRel(R,M,S)"
    with sub obtain r1 s1 r2 s2 where
      d: "x=\<langle>r1,s1\<rangle>" "y=\<langle>r2,s2\<rangle>" "r1\<in>R" "s1\<in>S" "r2\<in>R" "s2\<in>S" by auto
    with xy loc_rel_iff obtain t where "t\<in>S" "t\<cdot>(r1\<cdot>s2) = t\<cdot>(r2\<cdot>s1)" by auto
    then have "t\<in>S" "t\<cdot>(r2\<cdot>s1) = t\<cdot>(r1\<cdot>s2)" by auto
    with d loc_rel_iff show "\<langle>y,x\<rangle>\<in>LocRel(R,M,S)" by auto 
  qed
  have trans: "trans(LocRel(R,M,S))"
    unfolding trans_def
  proof (intro allI impI)
    fix x y z assume xy: "\<langle>x,y\<rangle>\<in>LocRel(R,M,S)" and yz: "\<langle>y,z\<rangle>\<in>LocRel(R,M,S)"
    from xy sub obtain r1 s1 r2 s2 where
      d: "x=\<langle>r1,s1\<rangle>" "y=\<langle>r2,s2\<rangle>" "r1\<in>R" "s1\<in>S" "r2\<in>R" "s2\<in>S" by auto
    from yz sub d(2) obtain r3 s3 where
      e: "z=\<langle>r3,s3\<rangle>" "r3\<in>R" "s3\<in>S" by auto
    from xy d loc_rel_iff obtain t where t: "t\<in>S" "t\<cdot>(r1\<cdot>s2) = t\<cdot>(r2\<cdot>s1)" by auto
    from yz d e loc_rel_iff obtain u where u: "u\<in>S" "u\<cdot>(r2\<cdot>s3) = u\<cdot>(r3\<cdot>s2)" by auto
    have RR: "t\<in>R" "u\<in>R" "s1\<in>R" "s2\<in>R" "s3\<in>R"
      using t(1) u(1) d(4,6) e(3) S_subset by auto
    let ?w = "t\<cdot>(u\<cdot>s2)"
    from t(1) u(1) d(6) S_closed have w: "?w\<in>S" by auto
    from RR d(3,5) e(2) have "t \<cdot> (u \<cdot> s2) \<cdot> (r1 \<cdot> s3) = (u \<cdot> s2) \<cdot> t \<cdot> (r1 \<cdot> s3)"
      using mult_ac Ring_ZF_1_L4(3) by auto
    also with RR d(3,5) e(2) have "\<dots> = (u\<cdot>t)\<cdot>s2\<cdot>(r1\<cdot>s3)"
      using mult_ac Ring_ZF_1_L4(3) by auto
    also with RR d(3,5) e(2) have "\<dots> = (u\<cdot>t)\<cdot>r1\<cdot>(s2\<cdot>s3)"
      using mult_ac Ring_ZF_1_L4(3) by auto
    also with RR d(3,5) e(2) have "\<dots> = (u\<cdot>s3)\<cdot>(t\<cdot>(r1\<cdot>s2))"
      using mult_ac Ring_ZF_1_L4(3) by auto
    also with t(2) have "\<dots> = (u\<cdot>s3)\<cdot>(t\<cdot>(r2\<cdot>s1))" by simp
    also with RR d(3,5) e(2) have "\<dots> = (t\<cdot>s1)\<cdot>(u\<cdot>(r2\<cdot>s3))"
      using mult_ac Ring_ZF_1_L4(3) by auto
    also from u(2) have "\<dots> = (t\<cdot>s1)\<cdot>(u\<cdot>(r3\<cdot>s2))" by simp
    also from RR d(3,5) e(2) have "\<dots> = ?w\<cdot>(r3\<cdot>s1)"
      using mult_ac Ring_ZF_1_L4(3) by auto
    finally have "?w\<cdot>(r1\<cdot>s3) = ?w\<cdot>(r3\<cdot>s1)" by auto
    with w d e loc_rel_iff show "\<langle>x,z\<rangle>\<in>LocRel(R,M,S)" by auto
  qed
  from sub refl sym trans show ?thesis unfolding equiv_def by simp
qed

subsection\<open>The operations on fractions are congruent\<close>

text\<open>In this section we show that \<open>LocAdd\<close> and \<open>LocMul\<close> are operations on $R\times S$
  and that they respect the fraction relation (are \<open>Congruent2\<close>). This is what is needed to
  project them to the quotient.\<close>

text\<open>Two fractions related by the fraction relation consist of elements of $R$ and $S$ and
  satisfy the defining condition for some $t\in S$.\<close>

lemma (in mult_subset) loc_rel_elim:
  assumes "\<langle>x,y\<rangle> \<in> LocRel(R,M,S)"
  shows "\<exists>r1 s1 r2 s2 t. x=\<langle>r1,s1\<rangle> \<and> y=\<langle>r2,s2\<rangle> \<and> r1\<in>R \<and> s1\<in>S \<and> r2\<in>R \<and> s2\<in>S \<and>
  t\<in>S \<and> t\<cdot>(r1\<cdot>s2) = t\<cdot>(r2\<cdot>s1)"
  using assms unfolding LocRel_def by auto

text\<open>The sum of fractions is a function on pairs of fractions with values in $R\times S$.\<close>

lemma (in mult_subset) loc_add_fun:
  shows "LocAdd(R,A,M,S) : ((R\<times>S)\<times>(R\<times>S)) \<rightarrow> R\<times>S"
proof -
  have "\<forall>x\<in>(R\<times>S)\<times>(R\<times>S).
    \<langle>A`\<langle>M`\<langle>fst(fst(x)),snd(snd(x))\<rangle>,M`\<langle>fst(snd(x)),snd(fst(x))\<rangle>\<rangle>,
    M`\<langle>snd(fst(x)),snd(snd(x))\<rangle>\<rangle> \<in> R\<times>S"
  proof
    fix x assume "x\<in>(R\<times>S)\<times>(R\<times>S)"
    then obtain r1 s1 r2 s2 where "x=\<langle>\<langle>r1,s1\<rangle>,\<langle>r2,s2\<rangle>\<rangle>" "r1\<in>R" "s1\<in>S" "r2\<in>R" "s2\<in>S"
      "s1\<in>R" "s2\<in>R" using S_subset by blast
    with S_subset S_closed show
      "\<langle>A`\<langle>M`\<langle>fst(fst(x)),snd(snd(x))\<rangle>,M`\<langle>fst(snd(x)),snd(fst(x))\<rangle>\<rangle>,
      M`\<langle>snd(fst(x)),snd(snd(x))\<rangle>\<rangle> \<in> R\<times>S"
      using Ring_ZF_1_L4(1,3) by auto
  qed
  then show ?thesis unfolding LocAdd_def by (rule ZF_fun_from_total)
qed

text\<open>The value of the sum of two fractions.\<close>

lemma (in mult_subset) loc_add_val:
  assumes "r1\<in>R" "s1\<in>S" "r2\<in>R" "s2\<in>S"
  shows "LocAdd(R,A,M,S)`\<langle>\<langle>r1,s1\<rangle>,\<langle>r2,s2\<rangle>\<rangle> = \<langle>r1\<cdot>s2 \<ra> r2\<cdot>s1, s1\<cdot>s2\<rangle>"
proof -
  from assms have "\<langle>\<langle>r1,s1\<rangle>,\<langle>r2,s2\<rangle>\<rangle> \<in> (R\<times>S)\<times>(R\<times>S)" by auto
  then have "\<langle>\<langle>\<langle>r1,s1\<rangle>,\<langle>r2,s2\<rangle>\<rangle>, \<langle>r1\<cdot>s2 \<ra> r2\<cdot>s1, s1\<cdot>s2\<rangle>\<rangle> \<in> LocAdd(R,A,M,S)"
    unfolding LocAdd_def by auto
  with loc_add_fun show ?thesis using apply_equality by auto
qed

text\<open>The product of fractions is a function on pairs of fractions with values in $R\times S$.\<close>

lemma (in mult_subset) loc_mul_fun:
  shows "LocMul(R,M,S) : ((R\<times>S)\<times>(R\<times>S)) \<rightarrow> R\<times>S"
proof -
  have "\<forall>x\<in>(R\<times>S)\<times>(R\<times>S).
    \<langle>M`\<langle>fst(fst(x)),fst(snd(x))\<rangle>, M`\<langle>snd(fst(x)),snd(snd(x))\<rangle>\<rangle> \<in> R\<times>S"
  proof
    fix x assume "x\<in>(R\<times>S)\<times>(R\<times>S)"
    then obtain r1 s1 r2 s2 where "x=\<langle>\<langle>r1,s1\<rangle>,\<langle>r2,s2\<rangle>\<rangle>" "r1\<in>R" "s1\<in>S" "r2\<in>R" "s2\<in>S"
      by auto
    with S_subset S_closed show
      "\<langle>M`\<langle>fst(fst(x)),fst(snd(x))\<rangle>, M`\<langle>snd(fst(x)),snd(snd(x))\<rangle>\<rangle> \<in> R\<times>S"
      using Ring_ZF_1_L4(3) by auto
  qed
  then show ?thesis unfolding LocMul_def by (rule ZF_fun_from_total)
qed

text\<open>The value of the product of two fractions.\<close>

lemma (in mult_subset) loc_mul_val:
  assumes "r1\<in>R" "s1\<in>S" "r2\<in>R" "s2\<in>S"
  shows "LocMul(R,M,S)`\<langle>\<langle>r1,s1\<rangle>,\<langle>r2,s2\<rangle>\<rangle> = \<langle>r1\<cdot>r2, s1\<cdot>s2\<rangle>"
proof -
  from assms have "\<langle>\<langle>r1,s1\<rangle>,\<langle>r2,s2\<rangle>\<rangle> \<in> (R\<times>S)\<times>(R\<times>S)" by auto
  then have "\<langle>\<langle>\<langle>r1,s1\<rangle>,\<langle>r2,s2\<rangle>\<rangle>, \<langle>r1\<cdot>r2, s1\<cdot>s2\<rangle>\<rangle> \<in> LocMul(R,M,S)"
    unfolding LocMul_def by auto
  with loc_mul_fun show ?thesis using apply_equality by auto
qed

text\<open>The algebraic core of the congruence of addition: if $t(a_1b_2)=t(a_2b_1)$ and
  $u(c_1d_2)=u(c_2d_1)$ then $(a_1/b_1 + c_1/d_1)$ and $(a_2/b_2 + c_2/d_2)$ are identified
  by the factor $tu$.\<close>

lemma (in mult_subset) loc_add_alg:
  assumes "a1\<in>R" "a2\<in>R" "b1\<in>R" "b2\<in>R" "c1\<in>R" "c2\<in>R" "d1\<in>R" "d2\<in>R" "t\<in>R" "u\<in>R"
  and "t\<cdot>(a1\<cdot>b2) = t\<cdot>(a2\<cdot>b1)" "u\<cdot>(c1\<cdot>d2) = u\<cdot>(c2\<cdot>d1)"
  shows "(t\<cdot>u)\<cdot>((a1\<cdot>d1 \<ra> c1\<cdot>b1)\<cdot>(b2\<cdot>d2)) = (t\<cdot>u)\<cdot>((a2\<cdot>d2 \<ra> c2\<cdot>b2)\<cdot>(b1\<cdot>d1))"
proof -
  have e1: "(t\<cdot>u)\<cdot>((a1\<cdot>d1)\<cdot>(b2\<cdot>d2)) = (t\<cdot>u)\<cdot>((a2\<cdot>d2)\<cdot>(b1\<cdot>d1))"
  proof -
    from assms(1-10) have "(t\<cdot>u)\<cdot>((a1\<cdot>d1)\<cdot>(b2\<cdot>d2)) = (t\<cdot>(a1\<cdot>b2))\<cdot>(u\<cdot>(d1\<cdot>d2))"
      using mult_ac Ring_ZF_1_L4(3) by auto
    also from assms(11) have "\<dots> = (t\<cdot>(a2\<cdot>b1))\<cdot>(u\<cdot>(d1\<cdot>d2))" by simp
    also from assms(1-10) have "\<dots> = (t\<cdot>u)\<cdot>((a2\<cdot>d2)\<cdot>(b1\<cdot>d1))"
      using mult_ac Ring_ZF_1_L4(3) by auto
    finally show ?thesis .
  qed
  have e2: "(t\<cdot>u)\<cdot>((c1\<cdot>b1)\<cdot>(b2\<cdot>d2)) = (t\<cdot>u)\<cdot>((c2\<cdot>b2)\<cdot>(b1\<cdot>d1))"
  proof -
    from assms(1-10) have "(t\<cdot>u)\<cdot>((c1\<cdot>b1)\<cdot>(b2\<cdot>d2)) = (u\<cdot>(c1\<cdot>d2))\<cdot>(t\<cdot>(b1\<cdot>b2))"
      using mult_ac Ring_ZF_1_L4(3) by auto
    also from assms(12) have "\<dots> = (u\<cdot>(c2\<cdot>d1))\<cdot>(t\<cdot>(b1\<cdot>b2))" by simp
    also from assms(1-10) have "\<dots> = (t\<cdot>u)\<cdot>((c2\<cdot>b2)\<cdot>(b1\<cdot>d1))"
      using mult_ac Ring_ZF_1_L4(3) by auto
    finally show ?thesis .
  qed
  from assms(1-10) have
    "(t\<cdot>u)\<cdot>((a1\<cdot>d1 \<ra> c1\<cdot>b1)\<cdot>(b2\<cdot>d2)) =
    (t\<cdot>u)\<cdot>((a1\<cdot>d1)\<cdot>(b2\<cdot>d2)) \<ra> (t\<cdot>u)\<cdot>((c1\<cdot>b1)\<cdot>(b2\<cdot>d2))"
    and "(t\<cdot>u)\<cdot>((a2\<cdot>d2 \<ra> c2\<cdot>b2)\<cdot>(b1\<cdot>d1)) =
    (t\<cdot>u)\<cdot>((a2\<cdot>d2)\<cdot>(b1\<cdot>d1)) \<ra> (t\<cdot>u)\<cdot>((c2\<cdot>b2)\<cdot>(b1\<cdot>d1))"
    using ring_oper_distr Ring_ZF_1_L4(1,3) by auto
  with e1 e2 show ?thesis by simp
qed

text\<open>Addition of fractions is congruent with respect to the fraction relation.\<close>

theorem (in mult_subset) loc_add_congruent:
  shows "Congruent2(LocRel(R,M,S),LocAdd(R,A,M,S))"
proof -
  { fix x1 x2 y1 y2
    assume h: "\<langle>x1,x2\<rangle> \<in> LocRel(R,M,S)" "\<langle>y1,y2\<rangle> \<in> LocRel(R,M,S)"
    from h(1) obtain a1 b1 a2 b2 t where x: "x1=\<langle>a1,b1\<rangle>" "x2=\<langle>a2,b2\<rangle>"
      "a1\<in>R" "b1\<in>S" "a2\<in>R" "b2\<in>S" "t\<in>S" "t\<cdot>(a1\<cdot>b2) = t\<cdot>(a2\<cdot>b1)"
      using loc_rel_elim by blast
    from h(2) obtain c1 d1 c2 d2 u where y: "y1=\<langle>c1,d1\<rangle>" "y2=\<langle>c2,d2\<rangle>"
      "c1\<in>R" "d1\<in>S" "c2\<in>R" "d2\<in>S" "u\<in>S" "u\<cdot>(c1\<cdot>d2) = u\<cdot>(c2\<cdot>d1)"
      using loc_rel_elim by blast
    from x(4,6) y(4,6) S_subset have RR: "b1\<in>R" "b2\<in>R" "d1\<in>R" "d2\<in>R" by auto
    from x(7) y(7) S_subset have tu: "t\<in>R" "u\<in>R" by auto
    from x(7) y(7) S_closed have w: "t\<cdot>u \<in> S" by auto
    have v1: "LocAdd(R,A,M,S)`\<langle>x1,y1\<rangle> = \<langle>a1\<cdot>d1 \<ra> c1\<cdot>b1, b1\<cdot>d1\<rangle>"
      using x(1,3,4) y(1,3,4) loc_add_val by simp
    have v2: "LocAdd(R,A,M,S)`\<langle>x2,y2\<rangle> = \<langle>a2\<cdot>d2 \<ra> c2\<cdot>b2, b2\<cdot>d2\<rangle>"
      using x(2,5,6) y(2,5,6) loc_add_val by simp
    from x(3,5) y(3,5) RR have
      "a1\<cdot>d1 \<ra> c1\<cdot>b1 \<in> R" "a2\<cdot>d2 \<ra> c2\<cdot>b2 \<in> R"
      using Ring_ZF_1_L4(1,3) by auto
    moreover from x(4,6) y(4,6) S_closed have "b1\<cdot>d1 \<in> S" "b2\<cdot>d2 \<in> S" by auto
    moreover from x(3,5) y(3,5) RR tu x(8) y(8) have
      "(t\<cdot>u)\<cdot>((a1\<cdot>d1 \<ra> c1\<cdot>b1)\<cdot>(b2\<cdot>d2)) = (t\<cdot>u)\<cdot>((a2\<cdot>d2 \<ra> c2\<cdot>b2)\<cdot>(b1\<cdot>d1))"
      using loc_add_alg[of a1 a2 b1 b2 c1 c2 d1 d2 t u] by auto
    ultimately have
      "\<langle>LocAdd(R,A,M,S)`\<langle>x1,y1\<rangle>, LocAdd(R,A,M,S)`\<langle>x2,y2\<rangle>\<rangle> \<in> LocRel(R,M,S)"
      using v1 v2 w loc_rel_iff by auto
  }
  then show ?thesis unfolding Congruent2_def by auto
qed

text\<open>Multiplication of fractions is congruent with respect to the fraction relation.\<close>

theorem (in mult_subset) loc_mul_congruent:
  shows "Congruent2(LocRel(R,M,S),LocMul(R,M,S))"
proof -
  { fix x1 x2 y1 y2
    assume h: "\<langle>x1,x2\<rangle> \<in> LocRel(R,M,S)" "\<langle>y1,y2\<rangle> \<in> LocRel(R,M,S)"
    from h(1) obtain a1 b1 a2 b2 t where x: "x1=\<langle>a1,b1\<rangle>" "x2=\<langle>a2,b2\<rangle>"
      "a1\<in>R" "b1\<in>S" "a2\<in>R" "b2\<in>S" "t\<in>S" "t\<cdot>(a1\<cdot>b2) = t\<cdot>(a2\<cdot>b1)"
      using loc_rel_elim by blast
    from h(2) obtain c1 d1 c2 d2 u where y: "y1=\<langle>c1,d1\<rangle>" "y2=\<langle>c2,d2\<rangle>"
      "c1\<in>R" "d1\<in>S" "c2\<in>R" "d2\<in>S" "u\<in>S" "u\<cdot>(c1\<cdot>d2) = u\<cdot>(c2\<cdot>d1)"
      using loc_rel_elim by blast
    from x(4,6) y(4,6) S_subset have RR: "b1\<in>R" "b2\<in>R" "d1\<in>R" "d2\<in>R" by auto
    from x(7) y(7) S_subset have tu: "t\<in>R" "u\<in>R" by auto
    from x(7) y(7) S_closed have w: "t\<cdot>u \<in> S" by auto
    have v1: "LocMul(R,M,S)`\<langle>x1,y1\<rangle> = \<langle>a1\<cdot>c1, b1\<cdot>d1\<rangle>"
      using x(1,3,4) y(1,3,4) loc_mul_val by simp
    have v2: "LocMul(R,M,S)`\<langle>x2,y2\<rangle> = \<langle>a2\<cdot>c2, b2\<cdot>d2\<rangle>"
      using x(2,5,6) y(2,5,6) loc_mul_val by simp
    from x(3,5) y(3,5) have "a1\<cdot>c1 \<in> R" "a2\<cdot>c2 \<in> R" using Ring_ZF_1_L4(3) by auto
    moreover from x(4,6) y(4,6) S_closed have "b1\<cdot>d1 \<in> S" "b2\<cdot>d2 \<in> S" by auto
    moreover from x(3,5) y(3,5) RR tu have
      "(t\<cdot>u)\<cdot>((a1\<cdot>c1)\<cdot>(b2\<cdot>d2)) = (t\<cdot>(a1\<cdot>b2))\<cdot>(u\<cdot>(c1\<cdot>d2))"
      "(t\<cdot>(a2\<cdot>b1))\<cdot>(u\<cdot>(c2\<cdot>d1)) = (t\<cdot>u)\<cdot>((a2\<cdot>c2)\<cdot>(b1\<cdot>d1))"
      using mult_ac Ring_ZF_1_L4(3) by auto
    with x(8) y(8) have
      "(t\<cdot>u)\<cdot>((a1\<cdot>c1)\<cdot>(b2\<cdot>d2)) = (t\<cdot>u)\<cdot>((a2\<cdot>c2)\<cdot>(b1\<cdot>d1))" by simp
    ultimately have
      "\<langle>LocMul(R,M,S)`\<langle>x1,y1\<rangle>, LocMul(R,M,S)`\<langle>x2,y2\<rangle>\<rangle> \<in> LocRel(R,M,S)"
      using v1 v2 w loc_rel_iff by auto
  }
  then show ?thesis unfolding Congruent2_def by auto
qed

subsection\<open>Arithmetic of fractions\<close>

text\<open>In this section we show how the projected operations act on the classes of pairs
  and that the localization is a commutative ring.\<close>

text\<open>Elements of $S$ are elements of $R$.\<close>

lemma (in mult_subset) S_in_R:
  assumes "s\<in>S"
  shows "s\<in>R"
  using assms S_subset by auto

text\<open>A fraction is an element of the localization.\<close>

lemma (in mult_subset) fraction_in_localization:
  assumes "r\<in>R" "s\<in>S"
  shows "Fraction(R,M,S,r,s) \<in> Localization(R,M,S)"
proof -
  from assms have "\<langle>r,s\<rangle> \<in> R\<times>S" by simp
  then show ?thesis unfolding Fraction_def Localization_def by (rule quotientI)
qed

text\<open>Every element of the localization is a fraction.\<close>

lemma (in mult_subset) fraction_cases:
  assumes "c \<in> Localization(R,M,S)"
  shows "\<exists>r\<in>R. \<exists>s\<in>S. c = Fraction(R,M,S,r,s)"
  using assms unfolding Localization_def Fraction_def quotient_def by auto

text\<open>Fractions related by the fraction relation are equal.\<close>

lemma (in mult_subset) fraction_eq_witness:
  assumes "r1\<in>R" "s1\<in>S" "r2\<in>R" "s2\<in>S" "t\<in>S" "t\<cdot>(r1\<cdot>s2) = t\<cdot>(r2\<cdot>s1)"
  shows "Fraction(R,M,S,r1,s1) = Fraction(R,M,S,r2,s2)"
proof -
  from assms have "\<langle>\<langle>r1,s1\<rangle>,\<langle>r2,s2\<rangle>\<rangle> \<in> LocRel(R,M,S)"
    using loc_rel_iff by auto
  with loc_rel_equiv show ?thesis unfolding Fraction_def by (rule equiv_class_eq)
qed

text\<open>The sum of two fractions is the fraction given by the usual formula.\<close>

lemma (in mult_subset) loc_add_frac:
  assumes "r1\<in>R" "s1\<in>S" "r2\<in>R" "s2\<in>S"
  shows "LocalizedAdd(R,A,M,S)`\<langle>Fraction(R,M,S,r1,s1),Fraction(R,M,S,r2,s2)\<rangle> =
  Fraction(R,M,S,r1\<cdot>s2 \<ra> r2\<cdot>s1,s1\<cdot>s2)"
proof -
  from assms have "\<langle>r1,s1\<rangle> \<in> R\<times>S" "\<langle>r2,s2\<rangle> \<in> R\<times>S" by auto
  with loc_rel_equiv loc_add_congruent have
    "ProjFun2(R\<times>S,LocRel(R,M,S),LocAdd(R,A,M,S))`
    \<langle>LocRel(R,M,S)``{\<langle>r1,s1\<rangle>},LocRel(R,M,S)``{\<langle>r2,s2\<rangle>}\<rangle> =
    LocRel(R,M,S)``{LocAdd(R,A,M,S)`\<langle>\<langle>r1,s1\<rangle>,\<langle>r2,s2\<rangle>\<rangle>}"
    using EquivClass_1_L10 by simp
  with assms show ?thesis
    unfolding LocalizedAdd_def Fraction_def using loc_add_val by simp
qed

text\<open>The product of two fractions is the fraction given by the usual formula.\<close>

lemma (in mult_subset) loc_mul_frac:
  assumes "r1\<in>R" "s1\<in>S" "r2\<in>R" "s2\<in>S"
  shows "LocalizedMul(R,M,S)`\<langle>Fraction(R,M,S,r1,s1),Fraction(R,M,S,r2,s2)\<rangle> =
  Fraction(R,M,S,r1\<cdot>r2,s1\<cdot>s2)"
proof -
  from assms have "\<langle>r1,s1\<rangle> \<in> R\<times>S" "\<langle>r2,s2\<rangle> \<in> R\<times>S" by auto
  with loc_rel_equiv loc_mul_congruent have
    "ProjFun2(R\<times>S,LocRel(R,M,S),LocMul(R,M,S))`
    \<langle>LocRel(R,M,S)``{\<langle>r1,s1\<rangle>},LocRel(R,M,S)``{\<langle>r2,s2\<rangle>}\<rangle> =
    LocRel(R,M,S)``{LocMul(R,M,S)`\<langle>\<langle>r1,s1\<rangle>,\<langle>r2,s2\<rangle>\<rangle>}"
    using EquivClass_1_L10 by simp
  with assms show ?thesis
    unfolding LocalizedMul_def Fraction_def using loc_mul_val by simp
qed

text\<open>The projected operations are functions on the localization.\<close>

lemma (in mult_subset) loc_oper_fun:
  shows "LocalizedAdd(R,A,M,S) : Localization(R,M,S)\<times>Localization(R,M,S) \<rightarrow> Localization(R,M,S)"
  and "LocalizedMul(R,M,S) : Localization(R,M,S)\<times>Localization(R,M,S) \<rightarrow> Localization(R,M,S)"
  using loc_rel_equiv loc_add_congruent loc_mul_congruent EquivClass_1_T1
  unfolding LocalizedAdd_def LocalizedMul_def Localization_def by auto

subsection\<open>The localization is a commutative ring\<close>

text\<open>Addition of pairs is commutative (not just up to the fraction relation).\<close>

lemma (in mult_subset) loc_add_commutes:
  shows "LocAdd(R,A,M,S) {is commutative on} (R\<times>S)"
  unfolding IsCommutative_def
proof (intro ballI)
  fix x y assume "x\<in>R\<times>S" "y\<in>R\<times>S"
  then obtain r1 s1 r2 s2 where d: "x=\<langle>r1,s1\<rangle>" "y=\<langle>r2,s2\<rangle>" "r1\<in>R" "s1\<in>S" "r2\<in>R" "s2\<in>S"
    by auto
  then have rs: "r1\<cdot>s2 \<in> R" "r2\<cdot>s1 \<in> R" "s1\<in>R" "s2\<in>R"
    using S_in_R Ring_ZF_1_L4(3) by auto
  from rs(1,2) have "r1\<cdot>s2 \<ra> r2\<cdot>s1 = r2\<cdot>s1 \<ra> r1\<cdot>s2" by (rule Ring_ZF_1_L4(4))
  moreover from rs(3,4) have "s1\<cdot>s2 = s2\<cdot>s1" using mult_ac(1) by auto
  ultimately show "LocAdd(R,A,M,S)`\<langle>x,y\<rangle> = LocAdd(R,A,M,S)`\<langle>y,x\<rangle>"
    using d loc_add_val by simp
qed

text\<open>Multiplication of pairs is commutative.\<close>

lemma (in mult_subset) loc_mul_commutes:
  shows "LocMul(R,M,S) {is commutative on} (R\<times>S)"
  unfolding IsCommutative_def
proof (intro ballI)
  fix x y assume "x\<in>R\<times>S" "y\<in>R\<times>S"
  then obtain r1 s1 r2 s2 where d: "x=\<langle>r1,s1\<rangle>" "y=\<langle>r2,s2\<rangle>" "r1\<in>R" "s1\<in>S" "r2\<in>R" "s2\<in>S"
    by auto
  then have rs: "r1\<in>R" "r2\<in>R" "s1\<in>R" "s2\<in>R" using S_in_R by auto
  from rs(1,2) have "r1\<cdot>r2 = r2\<cdot>r1" using mult_ac(1) by auto
  moreover from rs(3,4) have "s1\<cdot>s2 = s2\<cdot>s1" using mult_ac(1) by auto
  ultimately show "LocMul(R,M,S)`\<langle>x,y\<rangle> = LocMul(R,M,S)`\<langle>y,x\<rangle>"
    using d loc_mul_val by simp
qed

text\<open>The algebraic identity behind associativity of addition of fractions.\<close>

lemma (in mult_subset) loc_add_assoc_alg:
  assumes "r1\<in>R" "r2\<in>R" "r3\<in>R" "s1\<in>R" "s2\<in>R" "s3\<in>R"
  shows "(r1\<cdot>s2 \<ra> r2\<cdot>s1)\<cdot>s3 \<ra> r3\<cdot>(s1\<cdot>s2) = r1\<cdot>(s2\<cdot>s3) \<ra> (r2\<cdot>s3 \<ra> r3\<cdot>s2)\<cdot>s1"
  using assms ring_oper_distr Ring_ZF_1_L11(1) mult_ac Ring_ZF_1_L4(1,3) by auto

text\<open>Addition of pairs is associative.\<close>

lemma (in mult_subset) loc_add_assoc:
  shows "LocAdd(R,A,M,S) {is associative on} (R\<times>S)"
  unfolding IsAssociative_def
proof
  show "LocAdd(R,A,M,S) : (R\<times>S)\<times>(R\<times>S) \<rightarrow> R\<times>S" using loc_add_fun by simp
  show "\<forall>x\<in>R\<times>S. \<forall>y\<in>R\<times>S. \<forall>z\<in>R\<times>S.
    LocAdd(R,A,M,S)`\<langle>LocAdd(R,A,M,S)`\<langle>x,y\<rangle>,z\<rangle> = LocAdd(R,A,M,S)`\<langle>x,LocAdd(R,A,M,S)`\<langle>y,z\<rangle>\<rangle>"
  proof (intro ballI)
    fix x y z assume "x\<in>R\<times>S" "y\<in>R\<times>S" "z\<in>R\<times>S"
    then obtain r1 s1 r2 s2 r3 s3 where d: "x=\<langle>r1,s1\<rangle>" "y=\<langle>r2,s2\<rangle>" "z=\<langle>r3,s3\<rangle>"
      "r1\<in>R" "s1\<in>S" "r2\<in>R" "s2\<in>S" "r3\<in>R" "s3\<in>S" by auto
    then have rs: "s1\<in>R" "s2\<in>R" "s3\<in>R" using S_in_R by auto
    from d S_closed have c: "s1\<cdot>s2 \<in> S" "s2\<cdot>s3 \<in> S" by auto
    from d rs have n: "r1\<cdot>s2 \<ra> r2\<cdot>s1 \<in> R" "r2\<cdot>s3 \<ra> r3\<cdot>s2 \<in> R"
      using Ring_ZF_1_L4(1,3) by auto
    from d(4-9) rs have
      "LocAdd(R,A,M,S)`\<langle>LocAdd(R,A,M,S)`\<langle>x,y\<rangle>,z\<rangle> =
      \<langle>(r1\<cdot>s2 \<ra> r2\<cdot>s1)\<cdot>s3 \<ra> r3\<cdot>(s1\<cdot>s2), (s1\<cdot>s2)\<cdot>s3\<rangle>"
      using d(1-3) loc_add_val c n by simp
    moreover from d(4-9) rs have
      "LocAdd(R,A,M,S)`\<langle>x,LocAdd(R,A,M,S)`\<langle>y,z\<rangle>\<rangle> =
      \<langle>r1\<cdot>(s2\<cdot>s3) \<ra> (r2\<cdot>s3 \<ra> r3\<cdot>s2)\<cdot>s1, s1\<cdot>(s2\<cdot>s3)\<rangle>"
      using d(1-3) loc_add_val c n by simp
    moreover from d(4,6,8) rs have
      "(r1\<cdot>s2 \<ra> r2\<cdot>s1)\<cdot>s3 \<ra> r3\<cdot>(s1\<cdot>s2) = r1\<cdot>(s2\<cdot>s3) \<ra> (r2\<cdot>s3 \<ra> r3\<cdot>s2)\<cdot>s1"
      using loc_add_assoc_alg by simp
    moreover from rs have "(s1\<cdot>s2)\<cdot>s3 = s1\<cdot>(s2\<cdot>s3)" by (rule Ring_ZF_1_L11(2))
    ultimately show "LocAdd(R,A,M,S)`\<langle>LocAdd(R,A,M,S)`\<langle>x,y\<rangle>,z\<rangle> =
      LocAdd(R,A,M,S)`\<langle>x,LocAdd(R,A,M,S)`\<langle>y,z\<rangle>\<rangle>" by simp
  qed
qed

text\<open>Multiplication of pairs is associative.\<close>

lemma (in mult_subset) loc_mul_assoc:
  shows "LocMul(R,M,S) {is associative on} (R\<times>S)"
  unfolding IsAssociative_def
proof
  show "LocMul(R,M,S) : (R\<times>S)\<times>(R\<times>S) \<rightarrow> R\<times>S" using loc_mul_fun by simp
  show "\<forall>x\<in>R\<times>S. \<forall>y\<in>R\<times>S. \<forall>z\<in>R\<times>S.
    LocMul(R,M,S)`\<langle>LocMul(R,M,S)`\<langle>x,y\<rangle>,z\<rangle> = LocMul(R,M,S)`\<langle>x,LocMul(R,M,S)`\<langle>y,z\<rangle>\<rangle>"
  proof (intro ballI)
    fix x y z assume "x\<in>R\<times>S" "y\<in>R\<times>S" "z\<in>R\<times>S"
    then obtain r1 s1 r2 s2 r3 s3 where d: "x=\<langle>r1,s1\<rangle>" "y=\<langle>r2,s2\<rangle>" "z=\<langle>r3,s3\<rangle>"
      "r1\<in>R" "s1\<in>S" "r2\<in>R" "s2\<in>S" "r3\<in>R" "s3\<in>S" by auto
    then have rs: "s1\<in>R" "s2\<in>R" "s3\<in>R" using S_in_R by auto
    from d S_closed have c: "s1\<cdot>s2 \<in> S" "s2\<cdot>s3 \<in> S" by auto
    from d Ring_ZF_1_L4(3) have n: "r1\<cdot>r2 \<in> R" "r2\<cdot>r3 \<in> R" by auto
    from d rs have "LocMul(R,M,S)`\<langle>LocMul(R,M,S)`\<langle>x,y\<rangle>,z\<rangle> = \<langle>(r1\<cdot>r2)\<cdot>r3, (s1\<cdot>s2)\<cdot>s3\<rangle>"
      using loc_mul_val c n by simp
    moreover from d rs have
      "LocMul(R,M,S)`\<langle>x,LocMul(R,M,S)`\<langle>y,z\<rangle>\<rangle> = \<langle>r1\<cdot>(r2\<cdot>r3), s1\<cdot>(s2\<cdot>s3)\<rangle>"
      using loc_mul_val c n by simp
    moreover from d(4,6,8) have "(r1\<cdot>r2)\<cdot>r3 = r1\<cdot>(r2\<cdot>r3)" by (rule Ring_ZF_1_L11(2))
    moreover from rs have "(s1\<cdot>s2)\<cdot>s3 = s1\<cdot>(s2\<cdot>s3)" by (rule Ring_ZF_1_L11(2))
    ultimately show "LocMul(R,M,S)`\<langle>LocMul(R,M,S)`\<langle>x,y\<rangle>,z\<rangle> =
      LocMul(R,M,S)`\<langle>x,LocMul(R,M,S)`\<langle>y,z\<rangle>\<rangle>" by simp
  qed
qed

text\<open>The projected addition is commutative and associative.\<close>

lemma (in mult_subset) loc_add_comm_assoc:
  shows "LocalizedAdd(R,A,M,S) {is commutative on} Localization(R,M,S)"
  and "LocalizedAdd(R,A,M,S) {is associative on} Localization(R,M,S)"
  using loc_rel_equiv loc_add_congruent loc_add_commutes loc_add_assoc
    EquivClass_2_T1 EquivClass_2_T2
  unfolding LocalizedAdd_def Localization_def by auto

text\<open>The projected multiplication is commutative and associative.\<close>

lemma (in mult_subset) loc_mul_comm_assoc:
  shows "LocalizedMul(R,M,S) {is commutative on} Localization(R,M,S)"
  and "LocalizedMul(R,M,S) {is associative on} Localization(R,M,S)"
  using loc_rel_equiv loc_mul_congruent loc_mul_commutes loc_mul_assoc
    EquivClass_2_T1 EquivClass_2_T2
  unfolding LocalizedMul_def Localization_def by auto

text\<open>The class of $0/1$ is the neutral element of the projected addition.\<close>

lemma (in mult_subset) loc_zero_neutral:
  assumes "c \<in> Localization(R,M,S)"
  shows "LocalizedAdd(R,A,M,S)`\<langle>Fraction(R,M,S,\<zero>,\<one>),c\<rangle> = c"
  "LocalizedAdd(R,A,M,S)`\<langle>c,Fraction(R,M,S,\<zero>,\<one>)\<rangle> = c"
proof -
  from assms obtain r s where d: "r\<in>R" "s\<in>S" "c = Fraction(R,M,S,r,s)"
    using fraction_cases by blast
  with S_one S_subset show "LocalizedAdd(R,A,M,S)`\<langle>Fraction(R,M,S,\<zero>,\<one>),c\<rangle> = c"
    "LocalizedAdd(R,A,M,S)`\<langle>c,Fraction(R,M,S,\<zero>,\<one>)\<rangle> = c"
    using loc_add_frac Ring_ZF_1_L2 Ring_ZF_1_L3 Ring_ZF_1_L6 by auto
qed

text\<open>The class of $1/1$ is the neutral element of the projected multiplication.\<close>

lemma (in mult_subset) loc_one_neutral:
  assumes "c \<in> Localization(R,M,S)"
  shows "LocalizedMul(R,M,S)`\<langle>Fraction(R,M,S,\<one>,\<one>),c\<rangle> = c"
  "LocalizedMul(R,M,S)`\<langle>c,Fraction(R,M,S,\<one>,\<one>)\<rangle> = c"
proof -
  from assms obtain r s where d: "r\<in>R" "s\<in>S" "c = Fraction(R,M,S,r,s)"
    using fraction_cases by blast
  with S_one S_subset show "LocalizedMul(R,M,S)`\<langle>Fraction(R,M,S,\<one>,\<one>),c\<rangle> = c"
    "LocalizedMul(R,M,S)`\<langle>c,Fraction(R,M,S,\<one>,\<one>)\<rangle> = c"
    using loc_mul_frac Ring_ZF_1_L2 Ring_ZF_1_L3 by auto
qed

text\<open>The localization with the projected addition is a monoid.\<close>

lemma (in mult_subset) loc_add_monoid:
  shows "IsAmonoid(Localization(R,M,S),LocalizedAdd(R,A,M,S))"
proof -
  have "Fraction(R,M,S,\<zero>,\<one>) \<in> Localization(R,M,S)"
    using fraction_in_localization Ring_ZF_1_L2(1) S_one by simp
  with loc_add_comm_assoc(2) loc_zero_neutral show ?thesis unfolding IsAmonoid_def by auto
qed

text\<open>The localization with the projected multiplication is a monoid.\<close>

lemma (in mult_subset) loc_mul_monoid:
  shows "IsAmonoid(Localization(R,M,S),LocalizedMul(R,M,S))"
proof -
  have "Fraction(R,M,S,\<one>,\<one>) \<in> Localization(R,M,S)"
    using fraction_in_localization Ring_ZF_1_L2(2) S_one by simp
  with loc_mul_comm_assoc(2) loc_one_neutral show ?thesis unfolding IsAmonoid_def by auto
qed

text\<open>The neutral element of the localization with the projected addition is the class of $0/1$.\<close>

lemma (in mult_subset) loc_zero_is_neutral:
  shows "Fraction(R,M,S,\<zero>,\<one>) = TheNeutralElement(Localization(R,M,S),LocalizedAdd(R,A,M,S))"
proof -
  have m: "monoid0(Localization(R,M,S),LocalizedAdd(R,A,M,S))"
    using loc_add_monoid unfolding monoid0_def by simp
  have "Fraction(R,M,S,\<zero>,\<one>) \<in> Localization(R,M,S)"
    using fraction_in_localization Ring_ZF_1_L2(1) S_one by simp
  with loc_zero_neutral have
    "Fraction(R,M,S,\<zero>,\<one>) \<in> Localization(R,M,S) \<and> (\<forall>g\<in>Localization(R,M,S).
    LocalizedAdd(R,A,M,S)`\<langle>Fraction(R,M,S,\<zero>,\<one>),g\<rangle> = g \<and>
    LocalizedAdd(R,A,M,S)`\<langle>g,Fraction(R,M,S,\<zero>,\<one>)\<rangle> = g)" by auto
  with m show ?thesis by (rule monoid0.group0_1_L4)
qed

text\<open>Fractions with zero numerator are all equal to the zero fraction.\<close>

lemma (in mult_subset) fraction_zero:
  assumes "s\<in>S"
  shows "Fraction(R,M,S,\<zero>,s) = Fraction(R,M,S,\<zero>,\<one>)"
proof -
  from assms S_one S_subset have "\<one>\<cdot>(\<zero>\<cdot>\<one>) = \<one>\<cdot>(\<zero>\<cdot>s)"
    using Ring_ZF_1_L2 Ring_ZF_1_L6 S_in_R by simp
  with assms S_one show ?thesis using fraction_eq_witness Ring_ZF_1_L2(1) by blast
qed

text\<open>Every element of the localization has an additive inverse.\<close>

lemma (in mult_subset) loc_add_inverse:
  assumes "c \<in> Localization(R,M,S)"
  shows "\<exists>d\<in>Localization(R,M,S).
  LocalizedAdd(R,A,M,S)`\<langle>c,d\<rangle> = TheNeutralElement(Localization(R,M,S),LocalizedAdd(R,A,M,S))"
proof -
  from assms obtain r s where d: "r\<in>R" "s\<in>S" "c = Fraction(R,M,S,r,s)"
    using fraction_cases by blast
  then have rs: "s\<in>R" "(\<rm>r)\<in>R" using S_in_R Ring_ZF_1_L3(1) by auto
  let ?d = "Fraction(R,M,S,\<rm>r,s)"
  from d(2) rs(2) have dd: "?d \<in> Localization(R,M,S)" using fraction_in_localization by simp
  from d rs have "(r \<ra> (\<rm>r))\<cdot>s = r\<cdot>s \<ra> (\<rm>r)\<cdot>s" using ring_oper_distr(2) by simp
  moreover from d rs have "r \<ra> (\<rm>r) = \<zero>" using Ring_ZF_1_L3(7) by simp
  moreover from rs(1) have "\<zero>\<cdot>s = \<zero>" using Ring_ZF_1_L6(1) by simp
  ultimately have "r\<cdot>s \<ra> (\<rm>r)\<cdot>s = \<zero>" by simp
  with d rs have "LocalizedAdd(R,A,M,S)`\<langle>c,?d\<rangle> = Fraction(R,M,S,\<zero>,s\<cdot>s)"
    using loc_add_frac by simp
  also from d(2) S_closed have "\<dots> = Fraction(R,M,S,\<zero>,\<one>)" using fraction_zero by simp
  finally have "LocalizedAdd(R,A,M,S)`\<langle>c,?d\<rangle> = Fraction(R,M,S,\<zero>,\<one>)" .
  with dd loc_zero_is_neutral show ?thesis by auto
qed

text\<open>The localization with the projected addition is an abelian group.\<close>

lemma (in mult_subset) loc_add_group:
  shows "IsAgroup(Localization(R,M,S),LocalizedAdd(R,A,M,S))"
  using loc_add_monoid loc_add_inverse unfolding IsAgroup_def by simp

text\<open>The algebraic identity behind distributivity of fractions.\<close>

lemma (in mult_subset) loc_distr_alg:
  assumes "a1\<in>R" "b1\<in>R" "c1\<in>R" "d1\<in>R" "e1\<in>R" "f1\<in>R"
  shows "(a1\<cdot>(c1\<cdot>f1 \<ra> e1\<cdot>d1))\<cdot>((b1\<cdot>d1)\<cdot>(b1\<cdot>f1)) =
  ((a1\<cdot>c1)\<cdot>(b1\<cdot>f1) \<ra> (a1\<cdot>e1)\<cdot>(b1\<cdot>d1))\<cdot>(b1\<cdot>(d1\<cdot>f1))"
  using assms ring_oper_distr mult_ac Ring_ZF_1_L4(1,3) by auto

text\<open>Multiplication of fractions distributes over addition.\<close>

lemma (in mult_subset) loc_distr_left:
  assumes "c1 \<in> Localization(R,M,S)" "c2 \<in> Localization(R,M,S)" "c3 \<in> Localization(R,M,S)"
  shows "LocalizedMul(R,M,S)`\<langle>c1,LocalizedAdd(R,A,M,S)`\<langle>c2,c3\<rangle>\<rangle> =
  LocalizedAdd(R,A,M,S)`\<langle>LocalizedMul(R,M,S)`\<langle>c1,c2\<rangle>,LocalizedMul(R,M,S)`\<langle>c1,c3\<rangle>\<rangle>"
proof -
  from assms(1) obtain a1 b1 where x: "a1\<in>R" "b1\<in>S" "c1 = Fraction(R,M,S,a1,b1)"
    using fraction_cases by blast
  from assms(2) obtain c d where y: "c\<in>R" "d\<in>S" "c2 = Fraction(R,M,S,c,d)"
    using fraction_cases by blast
  from assms(3) obtain e f where z: "e\<in>R" "f\<in>S" "c3 = Fraction(R,M,S,e,f)"
    using fraction_cases by blast
  from x y z have rr: "b1\<in>R" "d\<in>R" "f\<in>R" using S_in_R by auto
  from x(2) y(2) z(2) S_closed have ss: "d\<cdot>f \<in> S" "b1\<cdot>d \<in> S" "b1\<cdot>f \<in> S" by auto
  from ss(2,3) S_closed have s2: "(b1\<cdot>d)\<cdot>(b1\<cdot>f) \<in> S" by auto
  from x y z rr have n: "c\<cdot>f \<ra> e\<cdot>d \<in> R" "a1\<cdot>c \<in> R" "a1\<cdot>e \<in> R"
    using Ring_ZF_1_L4(1,3) by auto
  from x y z rr n have
    "LocalizedMul(R,M,S)`\<langle>c1,LocalizedAdd(R,A,M,S)`\<langle>c2,c3\<rangle>\<rangle> =
    Fraction(R,M,S,a1\<cdot>(c\<cdot>f \<ra> e\<cdot>d),b1\<cdot>(d\<cdot>f))"
    using loc_add_frac loc_mul_frac ss by simp
  moreover from x y z rr n ss have
    "LocalizedAdd(R,A,M,S)`\<langle>LocalizedMul(R,M,S)`\<langle>c1,c2\<rangle>,LocalizedMul(R,M,S)`\<langle>c1,c3\<rangle>\<rangle> =
    Fraction(R,M,S,(a1\<cdot>c)\<cdot>(b1\<cdot>f) \<ra> (a1\<cdot>e)\<cdot>(b1\<cdot>d),(b1\<cdot>d)\<cdot>(b1\<cdot>f))"
    using loc_mul_frac loc_add_frac by simp
  moreover from x y z rr have
    "\<one>\<cdot>((a1\<cdot>(c\<cdot>f \<ra> e\<cdot>d))\<cdot>((b1\<cdot>d)\<cdot>(b1\<cdot>f))) =
    \<one>\<cdot>(((a1\<cdot>c)\<cdot>(b1\<cdot>f) \<ra> (a1\<cdot>e)\<cdot>(b1\<cdot>d))\<cdot>(b1\<cdot>(d\<cdot>f)))"
    using loc_distr_alg by simp
  moreover
  from this x y z rr n ss s2 S_one have "a1 \<cdot> (c \<cdot> f \<ra> e \<cdot> d) \<in> R" 
    "b1 \<cdot> (d \<cdot> f) \<in> S"
    "a1 \<cdot> c \<cdot> (b1 \<cdot> f) \<ra> a1 \<cdot> e \<cdot> (b1 \<cdot> d) \<in> R"
    "b1 \<cdot> d \<cdot> (b1 \<cdot> f) \<in> S" 
    "\<one> \<in> S" "\<one>\<cdot> (a1 \<cdot> (c \<cdot> f \<ra> e \<cdot> d) \<cdot> (b1 \<cdot> d \<cdot> (b1 \<cdot> f))) =
    \<one>\<cdot> ((a1 \<cdot> c \<cdot> (b1 \<cdot> f) \<ra> a1 \<cdot> e \<cdot> (b1 \<cdot> d)) \<cdot>  (b1 \<cdot> (d \<cdot> f)))"
    using Ring_ZF_1_L4(1,3) S_subset S_closed by auto
  then have
    "Fraction(R,M,S,a1\<cdot>(c\<cdot>f \<ra> e\<cdot>d),b1\<cdot>(d\<cdot>f)) =
    Fraction(R,M,S,(a1\<cdot>c)\<cdot>(b1\<cdot>f) \<ra> (a1\<cdot>e)\<cdot>(b1\<cdot>d),(b1\<cdot>d)\<cdot>(b1\<cdot>f))"
    using fraction_eq_witness
      [of "a1\<cdot>(c\<cdot>f \<ra> e\<cdot>d)" "b1\<cdot>(d\<cdot>f)" "(a1 \<cdot> c \<cdot> (b1 \<cdot> f) \<ra> a1 \<cdot> e \<cdot> (b1 \<cdot> d))" "(b1\<cdot>d)\<cdot>(b1\<cdot>f)"
        _] by auto
  ultimately show ?thesis by simp
qed

text\<open>The projected multiplication is distributive over the projected addition.\<close>

lemma (in mult_subset) loc_distributive:
  shows "IsDistributive(Localization(R,M,S),LocalizedAdd(R,A,M,S),LocalizedMul(R,M,S))"
  unfolding IsDistributive_def
proof (intro ballI)
  fix c1 c2 c3 assume h: "c1 \<in> Localization(R,M,S)" "c2 \<in> Localization(R,M,S)"
    "c3 \<in> Localization(R,M,S)"
  from h(2,3) loc_oper_fun(1) have sum: "LocalizedAdd(R,A,M,S)`\<langle>c2,c3\<rangle> \<in> Localization(R,M,S)"
    using apply_funtype by simp
  from h loc_oper_fun(2) have p: "LocalizedMul(R,M,S)`\<langle>c2,c1\<rangle> \<in> Localization(R,M,S)"
    "LocalizedMul(R,M,S)`\<langle>c3,c1\<rangle> \<in> Localization(R,M,S)"
    by (auto intro: apply_funtype)
  from h sum loc_mul_comm_assoc(1) have
    "LocalizedMul(R,M,S)`\<langle>LocalizedAdd(R,A,M,S)`\<langle>c2,c3\<rangle>,c1\<rangle> =
    LocalizedMul(R,M,S)`\<langle>c1,LocalizedAdd(R,A,M,S)`\<langle>c2,c3\<rangle>\<rangle>"
    unfolding IsCommutative_def by simp
  moreover from h loc_mul_comm_assoc(1) have
    "LocalizedMul(R,M,S)`\<langle>c2,c1\<rangle> = LocalizedMul(R,M,S)`\<langle>c1,c2\<rangle>"
    "LocalizedMul(R,M,S)`\<langle>c3,c1\<rangle> = LocalizedMul(R,M,S)`\<langle>c1,c3\<rangle>"
    unfolding IsCommutative_def by auto
  ultimately show
    "LocalizedMul(R,M,S)`\<langle>c1,LocalizedAdd(R,A,M,S)`\<langle>c2,c3\<rangle>\<rangle> =
    LocalizedAdd(R,A,M,S)`\<langle>LocalizedMul(R,M,S)`\<langle>c1,c2\<rangle>,LocalizedMul(R,M,S)`\<langle>c1,c3\<rangle>\<rangle> \<and>
    LocalizedMul(R,M,S)`\<langle>LocalizedAdd(R,A,M,S)`\<langle>c2,c3\<rangle>,c1\<rangle> =
    LocalizedAdd(R,A,M,S)`\<langle>LocalizedMul(R,M,S)`\<langle>c2,c1\<rangle>,LocalizedMul(R,M,S)`\<langle>c3,c1\<rangle>\<rangle>"
    using h loc_distr_left by simp
qed

text\<open>The localization of a commutative ring at a multiplicative subset is a ring.\<close>

theorem (in mult_subset) localization_is_ring:
  shows "IsAring(Localization(R,M,S),LocalizedAdd(R,A,M,S),LocalizedMul(R,M,S))"
  using loc_add_group loc_add_comm_assoc(1) loc_mul_monoid loc_distributive
  unfolding IsAring_def by simp

subsection\<open>The canonical homomorphism\<close>

text\<open>The canonical map from $R$ to its localization sends $r$ to the fraction $r/1$.\<close>

definition
  "LocalizationMap(R,M,S) \<equiv> {\<langle>r,Fraction(R,M,S,r,TheNeutralElement(R,M))\<rangle>. r\<in>R}"

text\<open>The canonical map is a function from $R$ to the localization.\<close>

lemma (in mult_subset) loc_map_fun:
  shows "LocalizationMap(R,M,S) : R \<rightarrow> Localization(R,M,S)"
proof -
  have "\<forall>r\<in>R. Fraction(R,M,S,r,TheNeutralElement(R,M)) \<in> Localization(R,M,S)"
    using fraction_in_localization S_one by simp
  then show ?thesis unfolding LocalizationMap_def by (rule ZF_fun_from_total)
qed

text\<open>The value of the canonical map at $r$ is the fraction $r/1$.\<close>

lemma (in mult_subset) loc_map_val:
  assumes "r\<in>R"
  shows "LocalizationMap(R,M,S)`(r) = Fraction(R,M,S,r,\<one>)"
proof -
  from assms have "\<langle>r,Fraction(R,M,S,r,\<one>)\<rangle> \<in> LocalizationMap(R,M,S)"
    unfolding LocalizationMap_def by auto
  with loc_map_fun show ?thesis using apply_equality by auto
qed

text\<open>The neutral element of the localization with the projected multiplication
  is the class of $1/1$.\<close>

lemma (in mult_subset) loc_one_is_neutral:
  shows "Fraction(R,M,S,\<one>,\<one>) = TheNeutralElement(Localization(R,M,S),LocalizedMul(R,M,S))"
proof -
  have m: "monoid0(Localization(R,M,S),LocalizedMul(R,M,S))"
    using loc_mul_monoid unfolding monoid0_def by simp
  have "Fraction(R,M,S,\<one>,\<one>) \<in> Localization(R,M,S)"
    using fraction_in_localization Ring_ZF_1_L2(2) S_one by simp
  with loc_one_neutral have
    "Fraction(R,M,S,\<one>,\<one>) \<in> Localization(R,M,S) \<and> (\<forall>g\<in>Localization(R,M,S).
    LocalizedMul(R,M,S)`\<langle>Fraction(R,M,S,\<one>,\<one>),g\<rangle> = g \<and>
    LocalizedMul(R,M,S)`\<langle>g,Fraction(R,M,S,\<one>,\<one>)\<rangle> = g)" by auto
  with m show ?thesis by (rule monoid0.group0_1_L4)
qed

text\<open>The canonical map $r\mapsto r/1$ is a ring homomorphism from $R$ to the localization.\<close>

theorem (in mult_subset) loc_map_homomor:
  shows "IsRingHomomor(LocalizationMap(R,M,S),R,A,M,
  Localization(R,M,S),LocalizedAdd(R,A,M,S),LocalizedMul(R,M,S))"
  unfolding IsRingHomomor_def
proof (intro conjI)
  show "LocalizationMap(R,M,S) : R \<rightarrow> Localization(R,M,S)" using loc_map_fun by simp
  show "IsMorphism(R,A,LocalizedAdd(R,A,M,S),LocalizationMap(R,M,S))"
    unfolding IsMorphism_def
  proof (intro ballI)
    fix g1 g2 assume g: "g1\<in>R" "g2\<in>R"
    then have "g1\<ra>g2 \<in> R" using Ring_ZF_1_L4(1) by simp
    with g S_one show "LocalizationMap(R,M,S)`(A`\<langle>g1,g2\<rangle>) =
      LocalizedAdd(R,A,M,S)`\<langle>LocalizationMap(R,M,S)`(g1),LocalizationMap(R,M,S)`(g2)\<rangle>"
      using loc_map_val loc_add_frac Ring_ZF_1_L2(2) Ring_ZF_1_L3 by simp
  qed
  show "IsMorphism(R,M,LocalizedMul(R,M,S),LocalizationMap(R,M,S))"
    unfolding IsMorphism_def
  proof (intro ballI)
    fix g1 g2 assume g: "g1\<in>R" "g2\<in>R"
    then have "g1\<cdot>g2 \<in> R" using Ring_ZF_1_L4(3) by simp
    with g S_one show "LocalizationMap(R,M,S)`(M`\<langle>g1,g2\<rangle>) =
      LocalizedMul(R,M,S)`\<langle>LocalizationMap(R,M,S)`(g1),LocalizationMap(R,M,S)`(g2)\<rangle>"
      using loc_map_val loc_mul_frac Ring_ZF_1_L2(2) Ring_ZF_1_L3 by simp
  qed
  show "LocalizationMap(R,M,S)`(TheNeutralElement(R,M)) =
    TheNeutralElement(Localization(R,M,S),LocalizedMul(R,M,S))"
    using loc_map_val loc_one_is_neutral Ring_ZF_1_L2(2) by simp
qed

subsection\<open>The localization as a commutative ring\<close>

text\<open>The theorems proven in the \<open>commutative_ring\<close> context are valid for the
  localization with the projected operations.\<close>

sublocale mult_subset < loc_ring: commutative_ring
  "Localization(R,M,S)" "LocalizedAdd(R,A,M,S)" "LocalizedMul(R,M,S)"
  "\<lambda>x y. LocalizedAdd(R,A,M,S)`\<langle>x,y\<rangle>"
  "\<lambda>x. GroupInv(Localization(R,M,S),LocalizedAdd(R,A,M,S))`x"
  "\<lambda>x y. LocalizedAdd(R,A,M,S)`\<langle>x,GroupInv(Localization(R,M,S),LocalizedAdd(R,A,M,S))`y\<rangle>"
  "\<lambda>x y. LocalizedMul(R,M,S)`\<langle>x,y\<rangle>"
  "TheNeutralElement(Localization(R,M,S),LocalizedAdd(R,A,M,S))"
  "TheNeutralElement(Localization(R,M,S),LocalizedMul(R,M,S))"
  "LocalizedAdd(R,A,M,S)`\<langle>TheNeutralElement(Localization(R,M,S),LocalizedMul(R,M,S)),
    TheNeutralElement(Localization(R,M,S),LocalizedMul(R,M,S))\<rangle>"
  "\<lambda>x. LocalizedMul(R,M,S)`\<langle>x,x\<rangle>"
  "\<lambda>s. Fold(LocalizedAdd(R,A,M,S),TheNeutralElement(Localization(R,M,S),LocalizedAdd(R,A,M,S)),s)"
  "\<lambda>n x. Fold(LocalizedAdd(R,A,M,S),TheNeutralElement(Localization(R,M,S),LocalizedAdd(R,A,M,S)),
    {\<langle>k,x\<rangle>. k\<in>n})"
  "\<lambda>s. Fold(LocalizedMul(R,M,S),TheNeutralElement(Localization(R,M,S),LocalizedMul(R,M,S)),s)"
  "\<lambda>n x. Fold(LocalizedMul(R,M,S),TheNeutralElement(Localization(R,M,S),LocalizedMul(R,M,S)),
    {\<langle>k,x\<rangle>. k\<in>n})"
  using localization_is_ring loc_mul_comm_assoc(1)
  unfolding commutative_ring_def commutative_ring_axioms_def ring0_def by auto

text\<open>The canonical map is a ring homomorphism from $R$ to the localization, in the sense of
  the \<open>ring_homo\<close> locale. This makes the theorems about ring homomorphisms available.\<close>

sublocale mult_subset < loc_homomorphism: ring_homo R A M
  "Localization(R,M,S)" "LocalizedAdd(R,A,M,S)" "LocalizedMul(R,M,S)" "LocalizationMap(R,M,S)"
  _ _ _ _ _ _ _ _
  "\<lambda>x y. LocalizedAdd(R,A,M,S)`\<langle>x,y\<rangle>"
  "\<lambda>x. GroupInv(Localization(R,M,S),LocalizedAdd(R,A,M,S))`x"
  "\<lambda>x y. LocalizedAdd(R,A,M,S)`\<langle>x,GroupInv(Localization(R,M,S),LocalizedAdd(R,A,M,S))`y\<rangle>"
  "\<lambda>x y. LocalizedMul(R,M,S)`\<langle>x,y\<rangle>"
  "TheNeutralElement(Localization(R,M,S),LocalizedAdd(R,A,M,S))"
  "TheNeutralElement(Localization(R,M,S),LocalizedMul(R,M,S))"
  "LocalizedAdd(R,A,M,S)`\<langle>TheNeutralElement(Localization(R,M,S),LocalizedMul(R,M,S)),
    TheNeutralElement(Localization(R,M,S),LocalizedMul(R,M,S))\<rangle>"
  "\<lambda>x. LocalizedMul(R,M,S)`\<langle>x,x\<rangle>"
  using ringAssum localization_is_ring loc_map_homomor
  unfolding ring_homo_def apply simp using ringa_def apply simp
  using ringminus_def apply simp using ringsub_def apply simp
  using ringm_def apply simp using ringzero_def apply simp
  using ringone_def apply simp using ringtwo_def apply simp
  using ringsq_def apply simp prefer 9 using rlistsum_def apply simp
          prefer 9 using nat_mult_def apply simp 
          prefer 9 using listprod_def apply simp 
           prefer 9 using pow_def apply simp .

subsection\<open>Ideals of a localization\<close>

text\<open>In this section we show that every ideal of the localization is extended along the canonical
  map, i.e. it is generated by the image of its preimage.\<close>

text\<open>In the localization, $r/s\cdot s/1 = r/1$ and $r/1\cdot 1/s = r/s$.\<close>

lemma (in mult_subset) localization_fraction_decomp:
  assumes "r\<in>R" "s\<in>S"
  shows "LocalizedMul(R,M,S)`\<langle>Fraction(R,M,S,r,s),Fraction(R,M,S,s,\<one>)\<rangle> = Fraction(R,M,S,r,\<one>)"
    "LocalizedMul(R,M,S)`\<langle>Fraction(R,M,S,r,\<one>),Fraction(R,M,S,\<one>,s)\<rangle> = Fraction(R,M,S,r,s)"
proof-
  from assms(2) have sR:"s\<in>R" using S_in_R by simp
  have o:"\<one>\<in>S" "\<one>\<in>R" using S_one S_subset by auto
  from assms(1) sR have rs:"r\<cdot>s\<in>R" using Ring_ZF_1_L4(3) by simp
  from assms sR o have "LocalizedMul(R,M,S)`\<langle>Fraction(R,M,S,r,s),Fraction(R,M,S,s,\<one>)\<rangle> =
    Fraction(R,M,S,r\<cdot>s,s\<cdot>\<one>)" using loc_mul_frac[of r s s \<one>] by blast
  also from sR have "\<dots> = Fraction(R,M,S,r\<cdot>s,s)" using Ring_ZF_1_L3(5) by simp
  also have "\<dots> = Fraction(R,M,S,r,\<one>)"
  proof-
    from rs have "\<one>\<cdot>((r\<cdot>s)\<cdot>\<one>) = \<one>\<cdot>(r\<cdot>s)" using Ring_ZF_1_L3(5) by simp
    then show ?thesis using fraction_eq_witness rs assms o by blast
  qed
  finally show "LocalizedMul(R,M,S)`\<langle>Fraction(R,M,S,r,s),Fraction(R,M,S,s,\<one>)\<rangle> =
    Fraction(R,M,S,r,\<one>)" .
  from assms(1) sR o have "LocalizedMul(R,M,S)`\<langle>Fraction(R,M,S,r,\<one>),Fraction(R,M,S,\<one>,s)\<rangle> =
    Fraction(R,M,S,r\<cdot>\<one>,\<one>\<cdot>s)" using loc_mul_frac assms(2) by blast
  then have "LocalizedMul(R,M,S)`\<langle>Fraction(R,M,S,r,\<one>),Fraction(R,M,S,\<one>,s)\<rangle> =
    Fraction(R,M,S,r, \<one> \<cdot> s)" by (rule subst[OF Ring_ZF_1_L3(5)[OF assms(1)],
    of "\<lambda>t. LocalizedMul(R,M,S)`\<langle>Fraction(R,M,S,r,\<one>),Fraction(R,M,S,\<one>,s)\<rangle> =
    Fraction(R,M,S,t, \<one> \<cdot> s)"])
  then show "LocalizedMul(R,M,S)`\<langle>Fraction(R,M,S,r,\<one>),Fraction(R,M,S,\<one>,s)\<rangle> =
    Fraction(R,M,S,r,s)" by (rule subst[OF Ring_ZF_1_L3(6)[OF sR],
    of "\<lambda>t. LocalizedMul(R,M,S)`\<langle>Fraction(R,M,S,r,\<one>),Fraction(R,M,S,\<one>,s)\<rangle> =
    Fraction(R,M,S,r, t)"])
qed

text\<open>The ideals of the localization are extended along the canonical map.\<close>

theorem (in mult_subset) localization_ideals_extended:
  shows "IdealsExtended(Localization(R,M,S),LocalizedAdd(R,A,M,S),LocalizedMul(R,M,S),
    LocalizationMap(R,M,S))"
proof-
  have crit:"\<forall>x\<in>Localization(R,M,S). \<exists>r\<in>R. \<exists>c\<in>Localization(R,M,S).
    \<exists>b\<in>Localization(R,M,S).
    LocalizationMap(R,M,S)`r = LocalizedMul(R,M,S)`\<langle>x,c\<rangle> \<and>
    x = LocalizedMul(R,M,S)`\<langle>LocalizationMap(R,M,S)`r,b\<rangle>"
  proof
    fix x assume "x\<in>Localization(R,M,S)"
    then obtain r s where d:"r\<in>R" "s\<in>S" "x = Fraction(R,M,S,r,s)"
      using fraction_cases by blast
    from d(2) have sR:"s\<in>R" using S_in_R by simp
    have o:"\<one>\<in>S" "\<one>\<in>R" using S_one S_subset by auto
    have a:"Fraction(R,M,S,s,\<one>) \<in> Localization(R,M,S)"
      using fraction_in_localization sR o by simp
    have b:"Fraction(R,M,S,\<one>,s) \<in> Localization(R,M,S)"
      using fraction_in_localization o d(2) by simp
    have m:"LocalizationMap(R,M,S)`r = Fraction(R,M,S,r,\<one>)" using loc_map_val d(1) by simp
    have e1:"LocalizationMap(R,M,S)`r = LocalizedMul(R,M,S)`\<langle>x,Fraction(R,M,S,s,\<one>)\<rangle>"
      using d(3)[THEN sym] 
      trans[OF m localization_fraction_decomp(1)[OF d(1,2), THEN sym]] by blast
    have e2:"x = LocalizedMul(R,M,S)`\<langle>LocalizationMap(R,M,S)`r,Fraction(R,M,S,\<one>,s)\<rangle>"
      using m[THEN sym] trans[OF d(3) localization_fraction_decomp(2)[OF d(1,2), THEN sym]]
      subst[OF m[THEN sym], of "\<lambda>t. x = LocalizedMul(R,M,S)`\<langle>t,Fraction(R,M,S,\<one>,s)\<rangle>"]
      by blast
    from d(1) a b e1 e2 show "\<exists>r\<in>R. \<exists>c\<in>Localization(R,M,S). \<exists>b\<in>Localization(R,M,S).
      LocalizationMap(R,M,S)`r = LocalizedMul(R,M,S)`\<langle>x,c\<rangle> \<and>
      x = LocalizedMul(R,M,S)`\<langle>LocalizationMap(R,M,S)`r,b\<rangle>" by blast
  qed
  show ?thesis using loc_homomorphism.ideals_extended_criterion[OF crit] by auto 
qed

subsection\<open>Prime ideals of a localization\<close>

text\<open>In this section we show that the prime ideals of $S^{-1}R$ correspond to the prime ideals
  of $R$ that do not meet $S$: the preimages of the prime ideals of the localization under
  the canonical map are exactly the prime ideals of $R$ disjoint from $S$.\<close>

text\<open>The extension of an ideal $p$ of $R$ to the localization is the set of fractions
  $r/s$ with $r\in p$ and $s\in S$.\<close>

definition
  "ExtendedIdeal(R,M,S,p) \<equiv> {Fraction(R,M,S,fst(x),snd(x)). x\<in>p\<times>S}"

text\<open>An element belongs to the extension of $p$ iff it is a fraction with numerator in $p$.\<close>

lemma (in mult_subset) ext_ideal_iff:
  shows "c \<in> ExtendedIdeal(R,M,S,p) \<longleftrightarrow> (\<exists>r\<in>p. \<exists>s\<in>S. c = Fraction(R,M,S,r,s))"
proof
  assume "c \<in> ExtendedIdeal(R,M,S,p)"
  then obtain x where x:"x\<in>p\<times>S" "c = Fraction(R,M,S,fst(x),snd(x))"
    unfolding ExtendedIdeal_def by blast
  from x(1) obtain r s where "x = \<langle>r,s\<rangle>" "r\<in>p" "s\<in>S" by auto
  with x(2) show "\<exists>r\<in>p. \<exists>s\<in>S. c = Fraction(R,M,S,r,s)" by auto
next
  assume "\<exists>r\<in>p. \<exists>s\<in>S. c = Fraction(R,M,S,r,s)"
  then obtain r s where rs:"r\<in>p" "s\<in>S" "c = Fraction(R,M,S,r,s)" by auto
  from rs have "\<langle>r,s\<rangle> \<in> p\<times>S \<and> c = Fraction(R,M,S,fst(\<langle>r,s\<rangle>),snd(\<langle>r,s\<rangle>))"
    by simp
  then show "c \<in> ExtendedIdeal(R,M,S,p)" unfolding ExtendedIdeal_def by auto
qed

text\<open>A fraction with numerator in $p$ belongs to the extension of $p$.\<close>

lemma (in mult_subset) ext_ideal_mem:
  assumes "r\<in>p" "s\<in>S"
  shows "Fraction(R,M,S,r,s) \<in> ExtendedIdeal(R,M,S,p)"
  using assms ext_ideal_iff by auto

text\<open>The extension of a subset of $R$ is a subset of the localization.\<close>

lemma (in mult_subset) ext_ideal_sub:
  assumes "p\<subseteq>R"
  shows "ExtendedIdeal(R,M,S,p) \<subseteq> Localization(R,M,S)"
proof
  fix c assume "c \<in> ExtendedIdeal(R,M,S,p)"
  then obtain r s where "r\<in>p" "s\<in>S" "c = Fraction(R,M,S,r,s)" using ext_ideal_iff by auto
  with assms show "c \<in> Localization(R,M,S)" using fraction_in_localization by auto
qed

text\<open>Equal fractions have numerators and denominators related by the defining condition.\<close>

lemma (in mult_subset) fraction_eq_dest:
  assumes "r1\<in>R" "s1\<in>S" "r2\<in>R" "s2\<in>S" "Fraction(R,M,S,r1,s1) = Fraction(R,M,S,r2,s2)"
  shows "\<exists>t\<in>S. t\<cdot>(r1\<cdot>s2) = t\<cdot>(r2\<cdot>s1)"
proof-
  from assms(3,4) have pair:"\<langle>r2,s2\<rangle> \<in> R\<times>S" by simp
  from assms(5) have "LocRel(R,M,S)``{\<langle>r1,s1\<rangle>} = LocRel(R,M,S)``{\<langle>r2,s2\<rangle>}"
    unfolding Fraction_def by simp
  with loc_rel_equiv pair have "\<langle>\<langle>r1,s1\<rangle>,\<langle>r2,s2\<rangle>\<rangle> \<in> LocRel(R,M,S)"
    by (rule same_image_equiv)
  with assms(1,2,3,4) show ?thesis using loc_rel_iff by simp
qed

text\<open>In a commutative ring membership of factors in a prime ideal can be detected on products.\<close>

lemma (in commutative_ring) comm_prime_dest:
  assumes "P\<triangleleft>\<^sub>pR" "x\<in>R" "y\<in>R" "x\<cdot>y \<in> P"
  shows "x\<in>P \<or> y\<in>P"
proof-
  have oneR:"\<one>\<in>R" using Ring_ZF_1_L2(2) by simp
  from assms(1) have PI:"P\<triangleleft>R" unfolding primeIdeal_def by simp
  have "\<forall>z\<in>R. x\<cdot>z\<cdot>y \<in> P"
  proof
    fix z assume z:"z\<in>R"
    from assms(2) z assms(3) have e1:"x\<cdot>z\<cdot>y = x\<cdot>(z\<cdot>y)" by (rule mult_ac(2))
    from z assms(3) oneR have e2:"z\<cdot>y = y\<cdot>z" by (rule mult_ac(1))
    from assms(2,3) z have e3:"x\<cdot>y\<cdot>z = x\<cdot>(y\<cdot>z)" by (rule mult_ac(2))
    from PI assms(4) z have "x\<cdot>y\<cdot>z \<in> P" using ideal_dest_mult(1) by simp
    with e1 e2 e3 show "x\<cdot>z\<cdot>y \<in> P" by simp
  qed
  with assms(1,2,3) show ?thesis using equivalent_prime_ideal by blast
qed

text\<open>The extension of an ideal of $R$ is an ideal of the localization.\<close>

lemma (in mult_subset) ext_ideal_is_ideal:
  assumes "p\<triangleleft>R"
  shows "loc_ring.Ideal(ExtendedIdeal(R,M,S,p))"
proof-
  have pR:"p\<subseteq>R" using assms ideal_dest_subset by simp
  have o:"\<one>\<in>S" "\<one>\<in>R" using S_one S_subset by auto
  have sub:"ExtendedIdeal(R,M,S,p) \<subseteq> Localization(R,M,S)" using ext_ideal_sub pR by simp
  have ab:"\<forall>x\<in>ExtendedIdeal(R,M,S,p). \<forall>y\<in>Localization(R,M,S).
    LocalizedMul(R,M,S)`\<langle>y,x\<rangle> \<in> ExtendedIdeal(R,M,S,p) \<and>
    LocalizedMul(R,M,S)`\<langle>x,y\<rangle> \<in> ExtendedIdeal(R,M,S,p)"
  proof(intro ballI)
    fix x y assume x:"x\<in>ExtendedIdeal(R,M,S,p)" and y:"y\<in>Localization(R,M,S)"
    from x obtain r s where xd:"r\<in>p" "s\<in>S" "x = Fraction(R,M,S,r,s)"
      using ext_ideal_iff by auto
    from y obtain n d where yd:"n\<in>R" "d\<in>S" "y = Fraction(R,M,S,n,d)"
      using fraction_cases by blast
    from xd(1) pR have rR:"r\<in>R" by auto
    from assms xd(1) yd(1) have nr:"n\<cdot>r \<in> p" "r\<cdot>n \<in> p" using ideal_dest_mult by auto
    from xd(2) yd(2) have ds:"d\<cdot>s \<in> S" "s\<cdot>d \<in> S" using S_closed by auto
    from xd yd rR have A:"LocalizedMul(R,M,S)`\<langle>y,x\<rangle> = Fraction(R,M,S,n\<cdot>r,d\<cdot>s)"
      using loc_mul_frac by blast
    from nr(1) ds(1) have "Fraction(R,M,S,n\<cdot>r,d\<cdot>s) \<in> ExtendedIdeal(R,M,S,p)"
      using ext_ideal_mem by simp
    moreover from xd yd rR have B:"LocalizedMul(R,M,S)`\<langle>x,y\<rangle> = Fraction(R,M,S,r\<cdot>n,s\<cdot>d)"
      using loc_mul_frac by blast
    from nr(2) ds(2) have "Fraction(R,M,S,r\<cdot>n,s\<cdot>d) \<in> ExtendedIdeal(R,M,S,p)"
      using ext_ideal_mem by simp
    ultimately show "LocalizedMul(R,M,S)`\<langle>y,x\<rangle> \<in> ExtendedIdeal(R,M,S,p) \<and>
      LocalizedMul(R,M,S)`\<langle>x,y\<rangle> \<in> ExtendedIdeal(R,M,S,p)" 
      using subst[OF A[THEN sym], of "\<lambda>t. t\<in>ExtendedIdeal(R,M,S,p)"] 
        subst[OF B[THEN sym], of "\<lambda>t. t\<in>ExtendedIdeal(R,M,S,p)"] by blast
  qed
  have ne:"ExtendedIdeal(R,M,S,p) \<noteq> 0"
  proof-
    from assms have "\<zero>\<in>p" using ideal_dest_zero by simp
    with o(1) have "Fraction(R,M,S,\<zero>,\<one>) \<in> ExtendedIdeal(R,M,S,p)"
      using ext_ideal_mem by simp
    then show ?thesis by auto
  qed
  have cl:"ExtendedIdeal(R,M,S,p) {is closed under} LocalizedAdd(R,A,M,S)"
    unfolding IsOpClosed_def
  proof(intro ballI)
    fix x y assume as:"x\<in>ExtendedIdeal(R,M,S,p)" "y\<in>ExtendedIdeal(R,M,S,p)"
    from as(1) obtain r1 s1 where d1:"r1\<in>p" "s1\<in>S" "x = Fraction(R,M,S,r1,s1)"
      using ext_ideal_iff by auto
    from as(2) obtain r2 s2 where d2:"r2\<in>p" "s2\<in>S" "y = Fraction(R,M,S,r2,s2)"
      using ext_ideal_iff by auto
    from d1(1) d2(1) pR have r12:"r1\<in>R" "r2\<in>R" by auto
    from d1(2) d2(2) have s12:"s1\<in>R" "s2\<in>R" "s1\<cdot>s2 \<in> S" using S_in_R S_closed by auto
    from assms d1(1) d2(1) s12(1,2) have "r1\<cdot>s2 \<in> p" "r2\<cdot>s1 \<in> p"
      using ideal_dest_mult by auto
    with assms have "r1\<cdot>s2 \<ra> r2\<cdot>s1 \<in> p" using ideal_dest_sum by simp
    with s12(3) have A:"Fraction(R,M,S,r1\<cdot>s2 \<ra> r2\<cdot>s1,s1\<cdot>s2) \<in> ExtendedIdeal(R,M,S,p)"
      using ext_ideal_mem by simp
    from d1 d2 r12 have B:"LocalizedAdd(R,A,M,S)`\<langle>x,y\<rangle> =
      Fraction(R,M,S,r1\<cdot>s2 \<ra> r2\<cdot>s1,s1\<cdot>s2)" using loc_add_frac by blast
    show "LocalizedAdd(R,A,M,S)`\<langle>x,y\<rangle> \<in> ExtendedIdeal(R,M,S,p)"
      using subst[OF B[THEN sym], of "%t. t\<in>ExtendedIdeal(R,M,S,p)"] A by blast
  qed
  have inv:"\<forall>x\<in>ExtendedIdeal(R,M,S,p).
    GroupInv(Localization(R,M,S),LocalizedAdd(R,A,M,S))`x \<in> ExtendedIdeal(R,M,S,p)"
  proof
    fix x assume x:"x\<in>ExtendedIdeal(R,M,S,p)"
    with sub have xL:"x\<in>Localization(R,M,S)" by auto
    let ?one = "TheNeutralElement(Localization(R,M,S),LocalizedMul(R,M,S))"
    let ?mo = "GroupInv(Localization(R,M,S),LocalizedAdd(R,A,M,S))`(?one)"
    have oneL:"?one\<in>Localization(R,M,S)" using loc_ring.Ring_ZF_1_L2(2) by blast
    then have moL:"?mo\<in>Localization(R,M,S)" using loc_ring.Ring_ZF_1_L3(1) by blast
    from oneL xL have e1:"LocalizedMul(R,M,S)`\<langle>?mo,x\<rangle> =
      GroupInv(Localization(R,M,S),LocalizedAdd(R,A,M,S))`(LocalizedMul(R,M,S)`\<langle>?one,x\<rangle>)"
      using loc_ring.Ring_ZF_1_L7(1) by blast
    from xL have e2:"LocalizedMul(R,M,S)`\<langle>?one,x\<rangle> = x" using loc_ring.Ring_ZF_1_L3(6) by blast
    from e1 have e3:"LocalizedMul(R,M,S)`\<langle>?mo,x\<rangle> =
      GroupInv(Localization(R,M,S),LocalizedAdd(R,A,M,S))`(x)" using subst[OF e2,
      of "\<lambda>t. LocalizedMul(R,M,S)`\<langle>?mo,x\<rangle> =
      GroupInv(Localization(R,M,S),LocalizedAdd(R,A,M,S))`t"] by blast
    from ab x moL have e4:"LocalizedMul(R,M,S)`\<langle>?mo,x\<rangle> \<in> ExtendedIdeal(R,M,S,p)" by blast
    show "GroupInv(Localization(R,M,S),LocalizedAdd(R,A,M,S))`x \<in>
      ExtendedIdeal(R,M,S,p)" using subst[OF e3, of "\<lambda>t. t\<in> ExtendedIdeal(R,M,S,p)"] e4 by blast
  qed
  have sg:"IsAsubgroup(ExtendedIdeal(R,M,S,p),LocalizedAdd(R,A,M,S))"
    using ne sub cl inv by (rule loc_ring.add_group.group0_3_T3)
  from ab sg show ?thesis unfolding loc_ring.Ideal_def by blast
qed

text\<open>The preimage of the extension of $p$ under the canonical map is the set of elements
  $r$ of $R$ such that $r s\in p$ for some $s\in S$.\<close>

lemma (in mult_subset) ext_ideal_preimage:
  assumes "p\<triangleleft>R"
  shows "LocalizationMap(R,M,S)-``(ExtendedIdeal(R,M,S,p)) = {r\<in>R. \<exists>s\<in>S. r\<cdot>s \<in> p}"
proof
  have pR:"p\<subseteq>R" using assms ideal_dest_subset by simp
  have o:"\<one>\<in>S" "\<one>\<in>R" using S_one S_subset by auto
  show "LocalizationMap(R,M,S)-``(ExtendedIdeal(R,M,S,p)) \<subseteq> {r\<in>R. \<exists>s\<in>S. r\<cdot>s \<in> p}"
  proof
    fix r assume "r \<in> LocalizationMap(R,M,S)-``(ExtendedIdeal(R,M,S,p))"
    then have r:"r\<in>R" "LocalizationMap(R,M,S)`r \<in> ExtendedIdeal(R,M,S,p)"
      using func1_1_L15 loc_map_fun by auto
    then obtain r1 s1 where d:"r1\<in>p" "s1\<in>S" "LocalizationMap(R,M,S)`r = Fraction(R,M,S,r1,s1)"
      using ext_ideal_iff by auto
    from d(1) pR have r1R:"r1\<in>R" by auto
    from d(2) have s1R:"s1\<in>R" using S_in_R by simp
    from r(1) have "LocalizationMap(R,M,S)`r = Fraction(R,M,S,r,\<one>)" using loc_map_val by simp
    with d(3) have "Fraction(R,M,S,r,\<one>) = Fraction(R,M,S,r1,s1)" by simp
    with r(1) o(1) r1R d(2) have "\<exists>t\<in>S. t\<cdot>(r\<cdot>s1) = t\<cdot>(r1\<cdot>\<one>)"
      using fraction_eq_dest by simp
    then obtain t where t:"t\<in>S" "t\<cdot>(r\<cdot>s1) = t\<cdot>(r1\<cdot>\<one>)" by auto
    from t(1) have tR:"t\<in>R" using S_in_R by simp
    from tR r(1) s1R have sw:"t\<cdot>(r\<cdot>s1) = r\<cdot>(t\<cdot>s1)" by (rule mult_ac(3))
    from r1R have "r1\<cdot>\<one> = r1" using Ring_ZF_1_L3(5) by simp
    with assms d(1) tR have "t\<cdot>(r1\<cdot>\<one>) \<in> p" using ideal_dest_mult(2) by simp
    with t(2) sw have "r\<cdot>(t\<cdot>s1) \<in> p" by simp
    moreover from t(1) d(2) have "t\<cdot>s1 \<in> S" using S_closed by simp
    ultimately show "r \<in> {r\<in>R. \<exists>s\<in>S. r\<cdot>s \<in> p}" using r(1) by auto
  qed
  show "{r\<in>R. \<exists>s\<in>S. r\<cdot>s \<in> p} \<subseteq> LocalizationMap(R,M,S)-``(ExtendedIdeal(R,M,S,p))"
  proof
    fix r assume "r \<in> {r\<in>R. \<exists>s\<in>S. r\<cdot>s \<in> p}"
    then obtain s where rs:"r\<in>R" "s\<in>S" "r\<cdot>s \<in> p" by auto
    from rs(2) have sR:"s\<in>R" using S_in_R by simp
    from rs(1) sR have rsR:"r\<cdot>s \<in> R" using Ring_ZF_1_L4(3) by simp
    from rsR have "\<one>\<cdot>(r\<cdot>s) = \<one>\<cdot>((r\<cdot>s)\<cdot>\<one>)" using Ring_ZF_1_L3(5) by simp
    with rs(1,2) o rsR have "Fraction(R,M,S,r,\<one>) = Fraction(R,M,S,r\<cdot>s,s)"
      using fraction_eq_witness[of r \<one> "r\<cdot>s" s ] by simp
    with rs(1,2,3) have "LocalizationMap(R,M,S)`r \<in> ExtendedIdeal(R,M,S,p)"
      using loc_map_val ext_ideal_mem by simp
    with rs(1) show "r \<in> LocalizationMap(R,M,S)-``(ExtendedIdeal(R,M,S,p))"
      using func1_1_L15 loc_map_fun by auto
  qed
qed

text\<open>If $p$ does not meet $S$ then the extension of $p$ does not contain $1/1$,
  hence it is a proper subset of the localization.\<close>

lemma (in mult_subset) ext_ideal_proper:
  assumes "p\<triangleleft>R" "p\<inter>S = 0"
  shows "ExtendedIdeal(R,M,S,p) \<noteq> Localization(R,M,S)"
proof
  have o:"\<one>\<in>S" "\<one>\<in>R" using S_one S_subset by auto
  assume eq:"ExtendedIdeal(R,M,S,p) = Localization(R,M,S)"
  from o have "Fraction(R,M,S,\<one>,\<one>) \<in> Localization(R,M,S)"
    using fraction_in_localization by simp
  with eq have "LocalizationMap(R,M,S)`\<one> \<in> ExtendedIdeal(R,M,S,p)"
    using loc_map_val o(2) by simp
  with o(2) have "\<one> \<in> LocalizationMap(R,M,S)-``(ExtendedIdeal(R,M,S,p))"
    using func1_1_L15 loc_map_fun by auto
  with assms(1) have "\<exists>s\<in>S. \<one>\<cdot>s \<in> p" using ext_ideal_preimage by simp
  then obtain s where s:"s\<in>S" "\<one>\<cdot>s \<in> p" by auto
  from s(1) have "\<one>\<cdot>s = s" using S_in_R Ring_ZF_1_L3(6) by simp
  with s have "s \<in> p\<inter>S" by auto
  with assms(2) show False by auto
qed

text\<open>The extension of a prime ideal disjoint from $S$ is a prime ideal of the localization.\<close>

lemma (in mult_subset) ext_ideal_prime:
  assumes "p\<triangleleft>\<^sub>pR" "p\<inter>S = 0"
  shows "loc_ring.primeIdeal(ExtendedIdeal(R,M,S,p))"
proof-
  have o:"\<one>\<in>S" "\<one>\<in>R" using S_one S_subset by auto
  from assms(1) have pI:"p\<triangleleft>R" unfolding primeIdeal_def by simp
  then have pR:"p\<subseteq>R" using ideal_dest_subset by simp
  have key:"\<forall>x\<in>Localization(R,M,S). \<forall>y\<in>Localization(R,M,S).
    (\<forall>z\<in>Localization(R,M,S). LocalizedMul(R,M,S)`\<langle>LocalizedMul(R,M,S)`\<langle>x,z\<rangle>,y\<rangle>
    \<in> ExtendedIdeal(R,M,S,p)) \<longrightarrow> x \<in> ExtendedIdeal(R,M,S,p) \<or> y \<in> ExtendedIdeal(R,M,S,p)"
  proof(intro ballI impI)
    fix x y assume xy:"x\<in>Localization(R,M,S)" "y\<in>Localization(R,M,S)"
      and h:"\<forall>z\<in>Localization(R,M,S). LocalizedMul(R,M,S)`\<langle>LocalizedMul(R,M,S)`\<langle>x,z\<rangle>,y\<rangle>
      \<in> ExtendedIdeal(R,M,S,p)"
    from xy(1) obtain n1 d1 where xd:"n1\<in>R" "d1\<in>S" "x = Fraction(R,M,S,n1,d1)"
      using fraction_cases by blast
    from xy(2) obtain n2 d2 where yd:"n2\<in>R" "d2\<in>S" "y = Fraction(R,M,S,n2,d2)"
      using fraction_cases by blast
    from xd(2) yd(2) have d12:"d1\<in>R" "d2\<in>R" "d1\<cdot>d2 \<in> S" using S_in_R S_closed by auto
    from o have one:"Fraction(R,M,S,\<one>,\<one>) \<in> Localization(R,M,S)"
      using fraction_in_localization by simp
    from xd d12(1) o have "LocalizedMul(R,M,S)`\<langle>x,Fraction(R,M,S,\<one>,\<one>)\<rangle> =
      Fraction(R,M,S,n1\<cdot>\<one>,d1\<cdot>\<one>)" using loc_mul_frac by blast
    with xd(3) have xone:"LocalizedMul(R,M,S)`\<langle>x,Fraction(R,M,S,\<one>,\<one>)\<rangle> = x"
      using subst[OF Ring_ZF_1_L3(5)[OF d12(1)], of "\<lambda>t.  LocalizedMul(R, M, S) `
    \<langle>x, Fraction(R, M, S, \<one>, \<one>)\<rangle> =
    Fraction(R, M, S, n1 \<cdot> \<one>,t)"] subst[OF Ring_ZF_1_L3(5)[OF xd(1)], 
          of "\<lambda>t.  LocalizedMul(R, M, S) `
    \<langle>x, Fraction(R, M, S, \<one>, \<one>)\<rangle> =
    Fraction(R, M, S, t,d1)"]
      by blast
    from h one have "LocalizedMul(R, M, S) `
       \<langle>LocalizedMul(R, M, S) ` \<langle>x, Fraction(R,M,S,\<one>,\<one>)\<rangle>, y\<rangle> \<in>
       ExtendedIdeal(R, M, S, p)" by blast
    with subst[OF xone, of "\<lambda>t. LocalizedMul(R,M,S)`\<langle>t,y\<rangle> \<in> ExtendedIdeal(R,M,S,p)"]
      have A:"LocalizedMul(R,M,S)`\<langle>x,y\<rangle> \<in> ExtendedIdeal(R,M,S,p)" by blast
    from xd yd have B:"LocalizedMul(R,M,S)`\<langle>x,y\<rangle> = Fraction(R,M,S,n1\<cdot>n2,d1\<cdot>d2)"
      using loc_mul_frac by blast
    from A have "\<exists>r\<in>p. \<exists>s\<in>S. LocalizedMul(R, M, S) ` \<langle>x, y\<rangle> = Fraction(R, M, S, r, s)"
      using ext_ideal_iff by blast
    then have "\<exists>r\<in>p. \<exists>s\<in>S. Fraction(R,M,S,n1\<cdot>n2,d1\<cdot>d2) = Fraction(R, M, S, r, s)" 
      using subst[OF B, of "\<lambda>t. \<exists>r\<in>p. \<exists>s\<in>S. t = Fraction(R, M, S, r, s)"] by blast
    then obtain r s where rs:"r\<in>p" "s\<in>S" "Fraction(R,M,S,n1\<cdot>n2,d1\<cdot>d2) = Fraction(R,M,S,r,s)"
      by auto
    from rs(1) pR have rR:"r\<in>R" by auto
    from xd(1) yd(1) have n12:"n1\<cdot>n2 \<in> R" using Ring_ZF_1_L4(3) by simp
    from n12 d12(3) rR rs(2) rs(3) have "\<exists>t\<in>S. t\<cdot>((n1\<cdot>n2)\<cdot>s) = t\<cdot>(r\<cdot>(d1\<cdot>d2))"
      using fraction_eq_dest by simp
    then obtain t where t:"t\<in>S" "t\<cdot>((n1\<cdot>n2)\<cdot>s) = t\<cdot>(r\<cdot>(d1\<cdot>d2))" by auto
    from t(1) rs(2) have tR:"t\<in>R" "s\<in>R" "t\<cdot>s \<in> S" using S_in_R S_closed by auto
    from tR(1) n12 tR(2) have sw:"t\<cdot>((n1\<cdot>n2)\<cdot>s) = (n1\<cdot>n2)\<cdot>(t\<cdot>s)" by (rule mult_ac(3))
    from pI rs(1) d12(1,2) have "r\<cdot>(d1\<cdot>d2) \<in> p"
      using ideal_dest_mult(1) Ring_ZF_1_L4(3) by simp
    with pI tR(1) have "t\<cdot>(r\<cdot>(d1\<cdot>d2)) \<in> p" using ideal_dest_mult(2) by simp
    with t(2) sw have "(n1\<cdot>n2)\<cdot>(t\<cdot>s) \<in> p" by simp
    moreover from tR(3) assms(2) have "t\<cdot>s \<notin> p" by auto
    moreover from tR(1,2) have "t\<cdot>s \<in> R" using Ring_ZF_1_L4(3) by simp
    ultimately have "n1\<cdot>n2 \<in> p" using comm_prime_dest assms(1) n12 by blast
    then have "n1\<in>p \<or> n2\<in>p" using comm_prime_dest assms(1) xd(1) yd(1) by simp
    then show "x \<in> ExtendedIdeal(R,M,S,p) \<or> y \<in> ExtendedIdeal(R,M,S,p)"
      using ext_ideal_mem xd yd by auto
  qed
  have "loc_ring.Ideal(ExtendedIdeal(R,M,S,p))" using ext_ideal_is_ideal pI by simp
  moreover have "ExtendedIdeal(R,M,S,p) \<noteq> Localization(R,M,S)"
    using ext_ideal_proper pI assms(2) by simp
  ultimately show ?thesis using key loc_ring.equivalent_prime_ideal_2 by blast
qed

text\<open>A prime ideal of $R$ disjoint from $S$ is the preimage of its extension.\<close>

lemma (in mult_subset) ext_ideal_contract:
  assumes "p\<triangleleft>\<^sub>pR" "p\<inter>S = 0"
  shows "LocalizationMap(R,M,S)-``(ExtendedIdeal(R,M,S,p)) = p"
proof-
  from assms(1) have pI:"p\<triangleleft>R" unfolding primeIdeal_def by simp
  then have pR:"p\<subseteq>R" using ideal_dest_subset by simp
  have o:"\<one>\<in>S" "\<one>\<in>R" using S_one S_subset by auto
  have "{r\<in>R. \<exists>s\<in>S. r\<cdot>s \<in> p} = p"
  proof
    show "{r\<in>R. \<exists>s\<in>S. r\<cdot>s \<in> p} \<subseteq> p"
    proof
      fix r assume "r \<in> {r\<in>R. \<exists>s\<in>S. r\<cdot>s \<in> p}"
      then obtain s where rs:"r\<in>R" "s\<in>S" "r\<cdot>s \<in> p" by auto
      from rs(2) have "s\<in>R" using S_in_R by simp
      with assms(1) rs(1,3) have "r\<in>p \<or> s\<in>p" using comm_prime_dest by simp
      with rs(2) assms(2) show "r\<in>p" by auto
    qed
    show "p \<subseteq> {r\<in>R. \<exists>s\<in>S. r\<cdot>s \<in> p}"
    proof
      fix r assume r:"r\<in>p"
      with pR have rR:"r\<in>R" by auto
      then have "r\<cdot>\<one> = r" using Ring_ZF_1_L3(5) by simp
      with r have "r\<cdot>\<one>\<in>p" by auto
      with o(1) show "r \<in> {r\<in>R. \<exists>s\<in>S. r\<cdot>s \<in> p}" using rR by auto
    qed
  qed
  then show ?thesis using ext_ideal_preimage pI by simp
qed

text\<open>An ideal of the localization that contains $s/1$ for some $s\in S$ is the whole localization,
  since $s/1$ is invertible.\<close>

lemma (in mult_subset) loc_ideal_meets_S:
  assumes "loc_ring.Ideal(u)" "s\<in>S" "s \<in> LocalizationMap(R,M,S)-``u"
  shows "u = Localization(R,M,S)"
proof-
  have o:"\<one>\<in>S" "\<one>\<in>R" using S_one S_subset by auto
  from assms(2) have sR:"s\<in>R" using S_in_R by simp
  from assms(3) have fs:"LocalizationMap(R,M,S)`s \<in> u"
    using func1_1_L15 loc_map_fun by auto
  with sR have fsu:"Fraction(R,M,S,s,\<one>) \<in> u" using loc_map_val by simp
  from assms(2) o(2) have fr:"Fraction(R,M,S,\<one>,s) \<in> Localization(R,M,S)"
    using fraction_in_localization by simp
  have A:"LocalizedMul(R,M,S)`\<langle>Fraction(R,M,S,s,\<one>),Fraction(R,M,S,\<one>,s)\<rangle> \<in> u"
    using loc_ring.ideal_dest_mult(1)[OF assms(1) fsu fr] by blast
  moreover from sR o assms(2) have B:"LocalizedMul(R,M,S)`\<langle>Fraction(R,M,S,s,\<one>),Fraction(R,M,S,\<one>,s)\<rangle> =
    Fraction(R,M,S,s\<cdot>\<one>,\<one>\<cdot>s)" using loc_mul_frac[of s \<one> \<one> s] by blast
  moreover have C:"Fraction(R,M,S,s\<cdot>\<one>,\<one>\<cdot>s) = Fraction(R,M,S,\<one>,\<one>)"
  proof-
    from sR o(2) have "\<one>\<cdot>((s\<cdot>\<one>)\<cdot>\<one>) = \<one>\<cdot>(\<one>\<cdot>(\<one>\<cdot>s))"
      using Ring_ZF_1_L3(5,6) Ring_ZF_1_L4(3) by simp
    with sR o assms(2) show ?thesis using fraction_eq_witness[of "s\<cdot>\<one>" "\<one>\<cdot>s" \<one> \<one> \<one>]
        S_closed Ring_ZF_1_L4(3) by simp
  qed
  from A have "Fraction(R, M, S, s \<cdot> \<one>, \<one> \<cdot> s)\<in>u" using subst[OF B, of "\<lambda>t. t\<in>u"]
    by blast
  then have "Fraction(R,M,S,\<one>,\<one>) \<in> u" using subst[OF C, of "\<lambda>t. t\<in>u"] by blast
  then have "TheNeutralElement(Localization(R,M,S),LocalizedMul(R,M,S)) \<in> u"
    using subst[OF loc_one_is_neutral, of "\<lambda>t. t\<in>u"] by blast
  with assms(1) show ?thesis using loc_ring.ideal_with_one by blast
qed

text\<open>The prime ideals of the localization correspond to the prime ideals of $R$ disjoint from $S$:
  the image of the set of prime ideals of the localization under the preimage along the canonical
  map is exactly the set of prime ideals of $R$ that do not meet $S$.\<close>

theorem (in mult_subset) localization_prime_image:
  shows "{LocalizationMap(R,M,S)-``u. u\<in>{I\<in>loc_ring.ideals. loc_ring.primeIdeal(I)}} =
    {p\<in>\<I>. p\<triangleleft>\<^sub>pR \<and> p\<inter>S = 0}"
proof
  show "{LocalizationMap(R,M,S)-``u. u\<in>{I\<in>loc_ring.ideals. loc_ring.primeIdeal(I)}} \<subseteq>
    {p\<in>\<I>. p\<triangleleft>\<^sub>pR \<and> p\<inter>S = 0}"
  proof
    fix q assume "q \<in> {LocalizationMap(R,M,S)-``u. u\<in>{I\<in>loc_ring.ideals. loc_ring.primeIdeal(I)}}"
    then obtain u where u:"u\<in>loc_ring.ideals" "loc_ring.primeIdeal(u)"
      "q = LocalizationMap(R,M,S)-``u" by auto
    have o:"\<one>\<in>S" "\<one>\<in>R" using S_one S_subset by auto
    from u(1,2) have pp:"(LocalizationMap(R,M,S)-``u) \<triangleleft>\<^sub>pR"
      using loc_homomorphism.preimage_prime_ideal_comm loc_mul_comm_assoc(1) by simp
    then have pI:"(LocalizationMap(R,M,S)-``u) \<triangleleft>R" unfolding primeIdeal_def by simp
    then have "(LocalizationMap(R,M,S)-``u) \<in> \<I>" using ideal_dest_subset by simp
    moreover have "(LocalizationMap(R,M,S)-``u) \<inter> S = 0"
    proof(rule ccontr)
      assume "(LocalizationMap(R,M,S)-``u) \<inter> S \<noteq> 0"
      then obtain s where s:"s\<in>S" "s \<in> LocalizationMap(R,M,S)-``u" by blast
      from u(1) have uI:"loc_ring.Ideal(u)" by simp
      from uI s(1,2) have "u = Localization(R,M,S)" using loc_ideal_meets_S by blast
      with u(2) show False unfolding loc_ring.primeIdeal_def by simp
    qed
    ultimately show "q \<in> {p\<in>\<I>. p\<triangleleft>\<^sub>pR \<and> p\<inter>S = 0}" using pp u(3) by auto
  qed
  show "{p\<in>\<I>. p\<triangleleft>\<^sub>pR \<and> p\<inter>S = 0} \<subseteq>
    {LocalizationMap(R,M,S)-``u. u\<in>{I\<in>loc_ring.ideals. loc_ring.primeIdeal(I)}}"
  proof
    fix p assume p:"p \<in> {p\<in>\<I>. p\<triangleleft>\<^sub>pR \<and> p\<inter>S = 0}"
    then have pp:"p\<triangleleft>\<^sub>pR" "p\<inter>S = 0" "p\<triangleleft>R" "p\<subseteq>R" by auto
    let ?u = "ExtendedIdeal(R,M,S,p)"
    have "?u \<subseteq> Localization(R,M,S)" using ext_ideal_sub pp(4) by simp
    moreover have "loc_ring.Ideal(?u)" using ext_ideal_is_ideal pp(3) by simp
    ultimately have "?u \<in> {I\<in>loc_ring.ideals. loc_ring.primeIdeal(I)}"
      using ext_ideal_prime pp(1,2) by auto
    moreover have "p = LocalizationMap(R,M,S)-``?u" using ext_ideal_contract pp(1,2) by simp
    ultimately show "p \<in> {LocalizationMap(R,M,S)-``u. u\<in>{I\<in>loc_ring.ideals. loc_ring.primeIdeal(I)}}"
      by auto
  qed
qed

end
