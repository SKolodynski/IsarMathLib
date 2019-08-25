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

section \<open>Fields - introduction\<close>

theory Field_ZF imports Ring_ZF

begin

text\<open>This theory covers basic facts about fields.\<close>

subsection\<open>Definition and basic properties\<close>

text\<open>In this section we define what is a field and list the basic properties
  of fields.\<close>

text\<open>Field is a notrivial commutative ring such that all 
  non-zero elements have an inverse. We define the notion of being a field as
  a statement about three sets. The first set, denoted \<open>K\<close> is the 
  carrier of the field. The second set, denoted \<open>A\<close> represents the 
  additive operation on \<open>K\<close> (recall that in ZF set theory functions 
  are sets). The third set \<open>M\<close> represents the multiplicative operation 
  on \<open>K\<close>.\<close>

definition
  "IsAfield(K,A,M) \<equiv> 
  (IsAring(K,A,M) \<and> (M {is commutative on} K) \<and>
  TheNeutralElement(K,A) \<noteq> TheNeutralElement(K,M) \<and> 
  (\<forall>a\<in>K. a\<noteq>TheNeutralElement(K,A)\<longrightarrow>
  (\<exists>b\<in>K. M`\<langle>a,b\<rangle> = TheNeutralElement(K,M))))"

text\<open>The \<open>field0\<close> context extends the \<open>ring0\<close>
  context adding field-related assumptions and notation related to the 
  multiplicative inverse.\<close>

locale field0 = ring0 K A M for K A M +
  assumes mult_commute: "M {is commutative on} K"
  
  assumes not_triv: "\<zero> \<noteq> \<one>"

  assumes inv_exists: "\<forall>a\<in>K. a\<noteq>\<zero> \<longrightarrow> (\<exists>b\<in>K. a\<cdot>b = \<one>)"

  fixes non_zero ("K\<^sub>0")
  defines non_zero_def[simp]: "K\<^sub>0 \<equiv> K-{\<zero>}"

  fixes inv ("_\<inverse> " [96] 97)
  defines inv_def[simp]: "a\<inverse> \<equiv> GroupInv(K\<^sub>0,restrict(M,K\<^sub>0\<times>K\<^sub>0))`(a)"

text\<open>The next lemma assures us that we are talking fields 
  in the \<open>field0\<close> context.\<close>

lemma (in field0) Field_ZF_1_L1: shows "IsAfield(K,A,M)"
  using ringAssum mult_commute not_triv inv_exists IsAfield_def
  by simp

text\<open>We can use theorems proven in the \<open>field0\<close> context whenever we
  talk about a field.\<close>

lemma field_field0: assumes "IsAfield(K,A,M)"
  shows "field0(K,A,M)"
  using assms IsAfield_def field0_axioms.intro ring0_def field0_def 
  by simp

text\<open>Let's have an explicit statement that the multiplication
  in fields is commutative.\<close>

lemma (in field0) field_mult_comm: assumes "a\<in>K"  "b\<in>K"
  shows "a\<cdot>b = b\<cdot>a"
  using mult_commute assms IsCommutative_def by simp

text\<open>Fields do not have zero divisors.\<close>

lemma (in field0) field_has_no_zero_divs: shows "HasNoZeroDivs(K,A,M)"
proof -
  { fix a b assume A1: "a\<in>K"  "b\<in>K" and A2: "a\<cdot>b = \<zero>"  and A3: "b\<noteq>\<zero>"
    from inv_exists A1 A3 obtain c where I: "c\<in>K" and II: "b\<cdot>c = \<one>"
      by auto
    from A2 have "a\<cdot>b\<cdot>c = \<zero>\<cdot>c" by simp
    with A1 I have "a\<cdot>(b\<cdot>c) = \<zero>" 
      using Ring_ZF_1_L11 Ring_ZF_1_L6 by simp
    with A1 II have "a=\<zero> "using Ring_ZF_1_L3 by simp } 
  then have "\<forall>a\<in>K.\<forall>b\<in>K. a\<cdot>b = \<zero> \<longrightarrow> a=\<zero> \<or> b=\<zero>" by auto
    then show ?thesis using HasNoZeroDivs_def by auto
qed

text\<open>$K_0$ (the set of nonzero field elements is closed with respect
  to multiplication.\<close>

lemma (in field0) Field_ZF_1_L2: 
  shows "K\<^sub>0 {is closed under} M"
  using Ring_ZF_1_L4 field_has_no_zero_divs Ring_ZF_1_L12
    IsOpClosed_def by auto

text\<open>Any nonzero element has a right inverse that is nonzero.\<close>

lemma (in field0) Field_ZF_1_L3: assumes A1: "a\<in>K\<^sub>0"
  shows "\<exists>b\<in>K\<^sub>0. a\<cdot>b = \<one>"
proof -
  from inv_exists A1 obtain b where "b\<in>K" and "a\<cdot>b = \<one>"
    by auto
  with not_triv A1 show "\<exists>b\<in>K\<^sub>0. a\<cdot>b = \<one>"
    using Ring_ZF_1_L6 by auto
qed

text\<open>If we remove zero, the field with multiplication
  becomes a group and we can use all theorems proven in 
  \<open>group0\<close> context.\<close>

theorem (in field0) Field_ZF_1_L4: shows 
  "IsAgroup(K\<^sub>0,restrict(M,K\<^sub>0\<times>K\<^sub>0))"
  "group0(K\<^sub>0,restrict(M,K\<^sub>0\<times>K\<^sub>0))"
  "\<one> = TheNeutralElement(K\<^sub>0,restrict(M,K\<^sub>0\<times>K\<^sub>0))"
proof-
  let ?f = "restrict(M,K\<^sub>0\<times>K\<^sub>0)"
  have 
    "M {is associative on} K"
    "K\<^sub>0 \<subseteq> K"  "K\<^sub>0 {is closed under} M"
    using Field_ZF_1_L1 IsAfield_def IsAring_def IsAgroup_def 
      IsAmonoid_def Field_ZF_1_L2 by auto
  then have "?f {is associative on} K\<^sub>0"
    using func_ZF_4_L3 by simp
  moreover
  from not_triv have 
    I: "\<one>\<in>K\<^sub>0 \<and> (\<forall>a\<in>K\<^sub>0. ?f`\<langle>\<one>,a\<rangle> = a \<and>  ?f`\<langle>a,\<one>\<rangle> = a)"
    using Ring_ZF_1_L2 Ring_ZF_1_L3 by auto
  then have "\<exists>n\<in>K\<^sub>0. \<forall>a\<in>K\<^sub>0. ?f`\<langle>n,a\<rangle> = a \<and>  ?f`\<langle>a,n\<rangle> = a"
    by blast
  ultimately have II: "IsAmonoid(K\<^sub>0,?f)" using IsAmonoid_def
    by simp
  then have "monoid0(K\<^sub>0,?f)" using monoid0_def by simp
  moreover note I
  ultimately show "\<one> = TheNeutralElement(K\<^sub>0,?f)"
    by (rule monoid0.group0_1_L4)
  then have "\<forall>a\<in>K\<^sub>0.\<exists>b\<in>K\<^sub>0. ?f`\<langle>a,b\<rangle> =  TheNeutralElement(K\<^sub>0,?f)"
    using Field_ZF_1_L3 by auto
  with II show "IsAgroup(K\<^sub>0,?f)" by (rule definition_of_group)
  then show "group0(K\<^sub>0,?f)" using group0_def by simp
qed

text\<open>The inverse of a nonzero field element is nonzero.\<close>

lemma (in field0) Field_ZF_1_L5: assumes A1: "a\<in>K"  "a\<noteq>\<zero>"
  shows "a\<inverse> \<in> K\<^sub>0"  "(a\<inverse>)\<^sup>2 \<in> K\<^sub>0"   "a\<inverse> \<in> K"  "a\<inverse> \<noteq> \<zero>"
proof -
  from A1 have "a \<in> K\<^sub>0" by simp
  then show "a\<inverse> \<in> K\<^sub>0" using Field_ZF_1_L4 group0.inverse_in_group
    by auto
  then show  "(a\<inverse>)\<^sup>2 \<in> K\<^sub>0"  "a\<inverse> \<in> K"  "a\<inverse> \<noteq> \<zero>" 
    using Field_ZF_1_L2 IsOpClosed_def by auto
qed

text\<open>The inverse is really the inverse.\<close>

lemma (in field0) Field_ZF_1_L6: assumes A1: "a\<in>K"  "a\<noteq>\<zero>"
  shows "a\<cdot>a\<inverse> = \<one>"  "a\<inverse>\<cdot>a = \<one>"
proof -
  let ?f = "restrict(M,K\<^sub>0\<times>K\<^sub>0)"
  from A1 have 
    "group0(K\<^sub>0,?f)"
    "a \<in> K\<^sub>0"
    using Field_ZF_1_L4 by auto
  then have 
    "?f`\<langle>a,GroupInv(K\<^sub>0, ?f)`(a)\<rangle> = TheNeutralElement(K\<^sub>0,?f) \<and>
    ?f`\<langle>GroupInv(K\<^sub>0,?f)`(a),a\<rangle> = TheNeutralElement(K\<^sub>0, ?f)"
    by (rule group0.group0_2_L6)
  with A1 show "a\<cdot>a\<inverse> = \<one>"  "a\<inverse>\<cdot>a = \<one>"
    using Field_ZF_1_L5 Field_ZF_1_L4 by auto
qed

text\<open>A lemma with two field elements and cancelling.\<close>

lemma (in field0) Field_ZF_1_L7: assumes "a\<in>K" "b\<in>K" "b\<noteq>\<zero>"
  shows 
  "a\<cdot>b\<cdot>b\<inverse> = a"
  "a\<cdot>b\<inverse>\<cdot>b = a"
  using assms Field_ZF_1_L5 Ring_ZF_1_L11 Field_ZF_1_L6 Ring_ZF_1_L3
  by auto

subsection\<open>Equations and identities\<close>

text\<open>This section deals with more specialized identities that are true in 
  fields.\<close>

text\<open>$a/(a^2) = 1/a$.\<close>

lemma (in field0) Field_ZF_2_L1: assumes A1: "a\<in>K"  "a\<noteq>\<zero>"
  shows "a\<cdot>(a\<inverse>)\<^sup>2 = a\<inverse>"
proof -
  have "a\<cdot>(a\<inverse>)\<^sup>2 = a\<cdot>(a\<inverse>\<cdot>a\<inverse>)" by simp
  also from A1 have "\<dots> =  (a\<cdot>a\<inverse>)\<cdot>a\<inverse>" 
    using Field_ZF_1_L5 Ring_ZF_1_L11 
    by simp
  also from A1 have "\<dots> = a\<inverse>" 
    using Field_ZF_1_L6 Field_ZF_1_L5 Ring_ZF_1_L3
    by simp
  finally show "a\<cdot>(a\<inverse>)\<^sup>2 = a\<inverse>" by simp
qed

text\<open>If we multiply two different numbers by a nonzero number, the results 
  will be different.\<close>

lemma (in field0) Field_ZF_2_L2: 
  assumes "a\<in>K"  "b\<in>K"  "c\<in>K"  "a\<noteq>b"  "c\<noteq>\<zero>"
  shows "a\<cdot>c\<inverse> \<noteq> b\<cdot>c\<inverse>"
  using assms field_has_no_zero_divs Field_ZF_1_L5 Ring_ZF_1_L12B
  by simp

text\<open>We can put a nonzero factor on the other side of non-identity 
  (is this the best way to call it?) changing it to the inverse.\<close>

lemma (in field0) Field_ZF_2_L3:
  assumes A1: "a\<in>K"  "b\<in>K"  "b\<noteq>\<zero>"  "c\<in>K"   and A2: "a\<cdot>b \<noteq> c"
  shows "a \<noteq> c\<cdot>b\<inverse>"
proof -
  from A1 A2 have "a\<cdot>b\<cdot>b\<inverse> \<noteq> c\<cdot>b\<inverse>" 
    using  Ring_ZF_1_L4 Field_ZF_2_L2 by simp
  with A1 show "a \<noteq> c\<cdot>b\<inverse>" using Field_ZF_1_L7
    by simp
qed

text\<open>If if the inverse of $b$ is different than $a$, then the
  inverse of $a$ is different than $b$.\<close>

lemma (in field0) Field_ZF_2_L4:
  assumes "a\<in>K"  "a\<noteq>\<zero>" and "b\<inverse> \<noteq> a"
  shows "a\<inverse> \<noteq> b"
  using assms Field_ZF_1_L4 group0.group0_2_L11B
  by simp

text\<open>An identity with two field elements, one and an inverse.\<close>

lemma (in field0) Field_ZF_2_L5:
  assumes "a\<in>K"  "b\<in>K" "b\<noteq>\<zero>"
  shows "(\<one> \<ra> a\<cdot>b)\<cdot>b\<inverse> = a \<ra> b\<inverse>"
  using assms Ring_ZF_1_L4 Field_ZF_1_L5 Ring_ZF_1_L2 ring_oper_distr 
    Field_ZF_1_L7 Ring_ZF_1_L3 by simp

text\<open>An identity with three field elements, inverse and cancelling.\<close>

lemma (in field0) Field_ZF_2_L6: assumes A1: "a\<in>K"  "b\<in>K"  "b\<noteq>\<zero>"  "c\<in>K"
  shows "a\<cdot>b\<cdot>(c\<cdot>b\<inverse>) = a\<cdot>c"
proof -
  from A1 have T: "a\<cdot>b \<in> K"  "b\<inverse> \<in> K"
    using Ring_ZF_1_L4 Field_ZF_1_L5 by auto
  with mult_commute A1 have "a\<cdot>b\<cdot>(c\<cdot>b\<inverse>) = a\<cdot>b\<cdot>(b\<inverse>\<cdot>c)"
    using IsCommutative_def by simp
  moreover
  from A1 T have "a\<cdot>b \<in> K"  "b\<inverse> \<in> K"  "c\<in>K"
    by auto
  then have "a\<cdot>b\<cdot>b\<inverse>\<cdot>c = a\<cdot>b\<cdot>(b\<inverse>\<cdot>c)"
    by (rule Ring_ZF_1_L11)
  ultimately have "a\<cdot>b\<cdot>(c\<cdot>b\<inverse>) = a\<cdot>b\<cdot>b\<inverse>\<cdot>c" by simp
  with A1 show "a\<cdot>b\<cdot>(c\<cdot>b\<inverse>) = a\<cdot>c" 
    using Field_ZF_1_L7 by simp
qed

subsection\<open>1/0=0\<close>

text\<open>In ZF if $f: X\rightarrow Y$ and $x\notin X$ we have $f(x)=\emptyset$.
  Since $\emptyset$ (the empty set) in ZF is the same as zero of natural numbers we
  can claim that $1/0=0$ in certain sense. In this section we prove a theorem that
  makes makes it explicit.\<close>

text\<open>The next locale extends the \<open>field0\<close> locale to introduce notation
  for division operation.\<close>

locale fieldd = field0 +
  fixes division
  defines division_def[simp]: "division \<equiv> {\<langle>p,fst(p)\<cdot>snd(p)\<inverse>\<rangle>. p\<in>K\<times>K\<^sub>0}"

  fixes fdiv (infixl "\<fd>" 95)
  defines fdiv_def[simp]: "x\<fd>y \<equiv> division`\<langle>x,y\<rangle>"


text\<open>Division is a function on $K\times K_0$ with values in $K$.\<close>

lemma (in fieldd) div_fun: shows "division: K\<times>K\<^sub>0 \<rightarrow> K"
proof -
  have "\<forall>p \<in> K\<times>K\<^sub>0. fst(p)\<cdot>snd(p)\<inverse> \<in> K"
  proof
    fix p assume "p \<in> K\<times>K\<^sub>0"
    hence "fst(p) \<in> K" and "snd(p) \<in> K\<^sub>0" by auto
    then show  "fst(p)\<cdot>snd(p)\<inverse> \<in> K" using Ring_ZF_1_L4 Field_ZF_1_L5 by auto
  qed
  then have "{\<langle>p,fst(p)\<cdot>snd(p)\<inverse>\<rangle>. p\<in>K\<times>K\<^sub>0}: K\<times>K\<^sub>0 \<rightarrow> K"
    by (rule ZF_fun_from_total)
  thus ?thesis by simp
qed

text\<open>So, really $1/0=0$. The essential lemma is \<open>apply_0\<close> from standard
  Isabelle's \<open>func.thy\<close>.\<close>

theorem (in fieldd) one_over_zero: shows "\<one>\<fd>\<zero> = 0"
proof-
  have "domain(division) = K\<times>K\<^sub>0" using div_fun func1_1_L1
    by simp
  hence "\<langle>\<one>,\<zero>\<rangle> \<notin> domain(division)" by auto
  then show ?thesis using apply_0 by simp
qed

end
