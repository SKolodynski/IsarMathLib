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

section \<open>Rings - important localizations\<close>

theory Ring_ZF_7 imports Ring_ZF_6

begin

text\<open>This theory specializes the localization $S^{-1}R$ of a commutative ring $R$ to two
  important families of multiplicative subsets: the complement $R\setminus P$ of a prime ideal $P$
  (giving the localization $R_P$ at $P$) and the set of powers $\{1,a,a^2,\ldots\}$
  of a single element $a$ (giving the localization $R_a$).\<close>

subsection\<open>Localization at a prime ideal\<close>

text\<open>The locale \<open>prime_ideal\<close> is a commutative ring together with a prime ideal $P$.\<close>

locale prime_ideal = commutative_ring +
  fixes P
  assumes P_prime: "P\<triangleleft>\<^sub>pR"

text\<open>The complement of a prime ideal is a subset of the ring.\<close>

lemma (in prime_ideal) complement_subset:
  shows "R - P \<subseteq> R"
  by auto

text\<open>The complement of a prime ideal contains the unit, because a prime ideal is not the
  whole ring.\<close>

lemma (in prime_ideal) complement_one:
  shows "\<one> \<in> R - P"
proof-
  from P_prime have PI:"P\<triangleleft>R" "P \<noteq> R" unfolding primeIdeal_def by auto
  have "\<one>\<in>R" using Ring_ZF_1_L2(2) by simp
  moreover have "\<one> \<notin> P"
  proof
    assume "\<one> \<in> P"
    with PI(1) have "P = R" using ideal_with_one by simp
    with PI(2) show False by simp
  qed
  ultimately show ?thesis by simp
qed

text\<open>The complement of a prime ideal is closed under multiplication.\<close>

lemma (in prime_ideal) complement_closed:
  shows "(R - P) {is closed under} M"
  unfolding IsOpClosed_def
proof(intro ballI)
  fix x y assume as:"x \<in> R - P" "y \<in> R - P"
  then have "x\<in>R" "y\<in>R" by auto
  then have xy:"x\<cdot>y \<in> R" using Ring_ZF_1_L4(3) by simp
  { assume "x\<cdot>y \<in> P"
    with P_prime \<open>x\<in>R\<close> \<open>y\<in>R\<close> have "x\<in>P \<or> y\<in>P" using comm_prime_dest by simp
    with as have False by auto
  }
  with xy show "M`\<langle>x,y\<rangle> \<in> R - P" by auto
qed

text\<open>The complement of a prime ideal is a multiplicative subset, so the results about
  localizations apply to it.\<close>

sublocale prime_ideal < prime_loc: mult_subset R A M ringa ringminus ringsub ringm
  ringzero ringone ringtwo ringsq rlistsum rnat_mult listprod pow "R - P"
  using ringAssum commutative complement_subset complement_one complement_closed
  unfolding mult_subset_def mult_subset_axioms_def commutative_ring_def
    commutative_ring_axioms_def ring0_def by auto

text\<open>The extension of $P$ is a proper ideal of the localization at $P$.\<close>

theorem (in prime_ideal) prime_loc_extension_proper:
  shows "prime_loc.loc_ring.Ideal(ExtendedIdeal(R,M,R - P,P))"
  and "ExtendedIdeal(R,M,R - P,P) \<noteq> Localization(R,M,R - P)"
proof-
  from P_prime have PI:"P\<triangleleft>R" unfolding primeIdeal_def by simp
  from PI show "prime_loc.loc_ring.Ideal(ExtendedIdeal(R,M,R - P,P))"
    using prime_loc.ext_ideal_is_ideal by simp
  have "P \<inter> (R - P) = 0" by auto
  with PI show "ExtendedIdeal(R,M,R - P,P) \<noteq> Localization(R,M,R - P)"
    using prime_loc.ext_ideal_proper by simp
qed

text\<open>Every proper ideal of the localization at $P$ is contained in the extension of $P$.
  Together with the previous theorem this shows that the localization at a prime ideal is a
  local ring, whose unique maximal ideal is the extension of $P$.\<close>

theorem (in prime_ideal) prime_loc_local:
  assumes "prime_loc.loc_ring.Ideal(J)" "J \<noteq> Localization(R,M,R - P)"
  shows "J \<subseteq> ExtendedIdeal(R,M,R - P,P)"
proof-
  from P_prime have PI:"P\<triangleleft>R" unfolding primeIdeal_def by simp
  have onein:"\<one> \<in> R - P" using complement_one by simp
  have vsub:"LocalizationMap(R,M,R - P)-``J \<subseteq> P"
  proof
    fix r assume r:"r \<in> LocalizationMap(R,M,R - P)-``J"
    then have rR:"r\<in>R" using func1_1_L15 prime_loc.loc_map_fun by auto
    show "r\<in>P"
    proof(rule ccontr)
      assume "r\<notin>P"
      with rR have "r \<in> R - P" by simp
      with assms(1) r have "J = Localization(R,M,R - P)" using prime_loc.loc_ideal_meets_S by simp
      with assms(2) show False by simp
    qed
  qed
  have ext:"prime_loc.loc_ring.Ideal(ExtendedIdeal(R,M,R - P,P))"
    using prime_loc_extension_proper(1) by simp
  have img:"LocalizationMap(R,M,R - P)``(LocalizationMap(R,M,R - P)-``J) =
    {LocalizationMap(R,M,R - P)`r. r \<in> LocalizationMap(R,M,R - P)-``J}"
    using func_imagedef prime_loc.loc_map_fun func1_1_L3 by auto
  have sub:"LocalizationMap(R,M,R - P)``(LocalizationMap(R,M,R - P)-``J) \<subseteq>
    ExtendedIdeal(R,M,R - P,P)"
  proof
    fix x assume "x \<in> LocalizationMap(R,M,R - P)``(LocalizationMap(R,M,R - P)-``J)"
    with img obtain r where r:"r \<in> LocalizationMap(R,M,R - P)-``J"
      "x = LocalizationMap(R,M,R - P)`r" by auto
    from r(1) vsub have rP:"r\<in>P" by auto
    from rP PI have rR:"r\<in>R" using ideal_dest_subset by auto
    from rR r(2) have "x = Fraction(R,M,R - P,r,\<one>)" using prime_loc.loc_map_val by simp
    with rP onein show "x \<in> ExtendedIdeal(R,M,R - P,P)" using prime_loc.ext_ideal_mem by simp
  qed
  show ?thesis using prime_loc.loc_homomorphism.ideals_extended_dest
    prime_loc.localization_ideals_extended assms(1) ext sub by simp
qed

text\<open>The prime ideals of the localization at $P$ correspond to the prime ideals of $R$ contained
  in $P$.\<close>

theorem (in prime_ideal) prime_loc_prime_image:
  shows "{LocalizationMap(R,M,R - P)-``u. u\<in>{I\<in>prime_loc.loc_ring.ideals.
    prime_loc.loc_ring.primeIdeal(I)}} = {q\<in>\<I>. q\<triangleleft>\<^sub>pR \<and> q \<subseteq> P}"
proof-
  have "{q\<in>\<I>. q\<triangleleft>\<^sub>pR \<and> q \<inter> (R - P) = 0} = {q\<in>\<I>. q\<triangleleft>\<^sub>pR \<and> q \<subseteq> P}"
    by blast
  then show ?thesis using prime_loc.localization_prime_image by simp
qed

subsection\<open>Localization at the powers of an element\<close>

text\<open>The powers of an element $a$ of a ring $R$ are the elements $a^n$ for natural numbers $n$,
  where $a^0=1$.\<close>

definition
  "ElementPowers(R,M,c) \<equiv> {Fold(M,TheNeutralElement(R,M),{\<langle>k,c\<rangle>. k\<in>n}). n\<in>nat}"

text\<open>The locale \<open>ring_element\<close> is a commutative ring together with an element $a$.\<close>

locale ring_element = commutative_ring +
  fixes c
  assumes a_in: "c\<in>R"

text\<open>The set of powers of $a$ in terms of the power function of the ring context.\<close>

lemma (in ring_element) powers_eq:
  shows "ElementPowers(R,M,c) = {pow(n,c). n\<in>nat}"
  unfolding ElementPowers_def by simp

text\<open>Natural powers of an element are elements of the ring.\<close>

lemma (in ring_element) pow_in_ring:
  assumes "n\<in>nat"
  shows "pow(n,c) \<in> R"
  using assms a_in mult_monoid.nat_mult_type by simp

text\<open>The set of powers of $a$ is a subset of the ring.\<close>

lemma (in ring_element) powers_subset:
  shows "ElementPowers(R,M,c) \<subseteq> R"
  using powers_eq pow_in_ring by auto

text\<open>The unit is the zeroth power of $a$.\<close>

lemma (in ring_element) powers_one:
  shows "\<one> \<in> ElementPowers(R,M,c)"
proof-
  have "pow(0,c) = \<one>" using a_in mult_monoid.nat_mult_zero by simp
  moreover have "pow(0,c)\<in>{pow(n,c). n\<in>nat}" by blast
  then have "pow(0,c)\<in>ElementPowers(R,M,c)" 
    using subst[OF powers_eq[THEN sym], of "\<lambda>t. pow(0,c)\<in>t"] by auto
  ultimately show ?thesis by auto
qed

text\<open>The set of powers of $a$ is closed under multiplication.\<close>

lemma (in ring_element) powers_closed:
  shows "ElementPowers(R,M,c) {is closed under} M"
  unfolding IsOpClosed_def
proof(intro ballI)
  fix x y assume as:"x \<in> ElementPowers(R,M,c)" "y \<in> ElementPowers(R,M,c)"
  from as(1) obtain n where n:"n\<in>nat" "x = pow(n,c)" using powers_eq by auto
  from as(2) obtain m where m:"m\<in>nat" "y = pow(m,c)" using powers_eq by auto
  from n(1) m(1) have nm:"n #+ m \<in> nat" by simp
  from n(1) m(1) a_in have A:"pow(n #+ m,c) = pow(n,c)\<cdot>pow(m,c)"
    using mult_monoid.nat_mult_add by simp
  from nm a_in have "pow(n#+m,c)\<in>{pow(r,c). r\<in>nat}" by auto
  then have "pow(n#+m,c)\<in>ElementPowers(R,M,c)" using subst[OF powers_eq[THEN sym],
        of "\<lambda>t. pow(n#+m,c)\<in>t"] by auto
  then have "pow(n,c)\<cdot>pow(m,c) \<in> ElementPowers(R,M,c)"
    using subst[OF A, of "\<lambda>q. q\<in>ElementPowers(R,M,c)"] by auto
  then show "M`\<langle>x,y\<rangle> \<in> ElementPowers(R,M,c)" using n(2) m(2) by force
qed

text\<open>The set of powers of $a$ is a multiplicative subset, so the results about
  localizations apply to it.\<close>

sublocale ring_element < element_loc: mult_subset R A M ringa ringminus ringsub ringm
  ringzero ringone ringtwo ringsq rlistsum rnat_mult listprod pow "ElementPowers(R,M,c)"
  using ringAssum commutative powers_subset powers_one powers_closed
  unfolding mult_subset_def mult_subset_axioms_def commutative_ring_def
    commutative_ring_axioms_def ring0_def by auto

text\<open>If a prime ideal contains a power of $a$ then it contains $a$.\<close>

lemma (in ring_element) prime_contains_power:
  assumes "q\<triangleleft>\<^sub>pR"
  shows "\<forall>n\<in>nat. pow(n,c) \<in> q \<longrightarrow> c \<in> q"
proof-
  from assms have qI:"q\<triangleleft>R" "q \<noteq> R" unfolding primeIdeal_def by auto
  { fix n assume n:"n\<in>nat"
    have base:"pow(0,c) \<in> q \<longrightarrow> c \<in> q"
    proof
      assume "pow(0,c) \<in> q"
      with a_in have "\<one> \<in> q" using mult_monoid.nat_mult_zero by simp
      with qI(1) have "q = R" using ideal_with_one by simp
      with qI(2) show "c\<in>q" by simp
    qed
    have step:"\<forall>k\<in>nat. (pow(k,c) \<in> q \<longrightarrow> c \<in> q) \<longrightarrow> (pow(k #+ 1,c) \<in> q \<longrightarrow> c \<in> q)"
    proof(intro ballI impI)
      fix k assume k:"k\<in>nat" and ih:"pow(k,c) \<in> q \<longrightarrow> c \<in> q" and pq:"pow(k #+ 1,c) \<in> q"
      from k a_in have "pow(k #+ 1,c) = pow(k,c)\<cdot>c"
        using mult_monoid.nat_mult_add_one(1) by simp
      with pq have "pow(k,c)\<cdot>c \<in> q" by simp
      with assms k a_in have "pow(k,c) \<in> q \<or> c \<in> q" using comm_prime_dest pow_in_ring by simp
      with ih show "c\<in>q" by auto
    qed
    from n base step have "pow(n,c) \<in> q \<longrightarrow> c \<in> q" by (rule ind_on_nat1)
  }
  then show ?thesis by simp
qed

text\<open>A prime ideal is disjoint from the powers of $a$ if and only if it does not contain $a$.\<close>

lemma (in ring_element) prime_disjoint_powers:
  assumes "q\<triangleleft>\<^sub>pR"
  shows "q \<inter> ElementPowers(R,M,c) = 0 \<longleftrightarrow> c \<notin> q"
proof
  assume dis:"q \<inter> ElementPowers(R,M,c) = 0"
  show "c \<notin> q"
  proof
    assume aq:"c\<in>q"
    have "pow(1,c) = c" using a_in mult_monoid.nat_mult_one by simp
    then have "c\<in>{pow(n,c). n\<in>nat}" by force
    then have "c \<in> ElementPowers(R,M,c)" 
      using subst[OF powers_eq[THEN sym], of "\<lambda>q. c:q"] by blast
    with aq dis show False by auto
  qed
next
  assume na:"c \<notin> q"
  { fix x assume x:"x \<in> q \<inter> ElementPowers(R,M,c)"
    then obtain n where n:"n\<in>nat" "x = pow(n,c)" using powers_eq by auto
    with x assms have "c\<in>q" using prime_contains_power by auto
    with na have False by simp
  }
  then show "q \<inter> ElementPowers(R,M,c) = 0" by auto
qed

text\<open>The prime ideals of the localization at the powers of $a$ correspond to the prime ideals
  of $R$ that do not contain $a$.\<close>

theorem (in ring_element) element_loc_prime_image:
  shows "{LocalizationMap(R,M,ElementPowers(R,M,c))-``u.
    u\<in>{I\<in>element_loc.loc_ring.ideals. element_loc.loc_ring.primeIdeal(I)}} =
    {q\<in>\<I>. q\<triangleleft>\<^sub>pR \<and> c \<notin> q}"
proof-
  have "{q\<in>\<I>. q\<triangleleft>\<^sub>pR \<and> q \<inter> ElementPowers(R,M,c) = 0} = {q\<in>\<I>. q\<triangleleft>\<^sub>pR \<and> c \<notin> q}"
    using prime_disjoint_powers by auto
  then show ?thesis using element_loc.localization_prime_image by simp
qed

end
