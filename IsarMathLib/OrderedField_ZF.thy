(*   This file is a part of IsarMathLib - 
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

section \<open>Ordered fields\<close>

theory OrderedField_ZF imports OrderedRing_ZF Field_ZF

begin

text\<open>This theory covers basic facts about ordered fiels.\<close>

subsection\<open>Definition and basic properties\<close>

text\<open>Here we define ordered fields and proove their basic properties.\<close>

text\<open>Ordered field is a notrivial ordered ring such that all 
  non-zero elements have an inverse. We define the notion of being a ordered 
  field as
  a statement about four sets. The first set, denoted \<open>K\<close> is the 
  carrier of the field. The second set, denoted \<open>A\<close> represents the 
  additive operation on \<open>K\<close> (recall that in ZF set theory functions 
  are sets). The third set \<open>M\<close> represents the multiplicative operation 
  on \<open>K\<close>. The fourth set \<open>r\<close> is the order 
  relation on \<open>K\<close>.\<close>

definition
  "IsAnOrdField(K,A,M,r) \<equiv> (IsAnOrdRing(K,A,M,r) \<and>
  (M {is commutative on} K) \<and>
  TheNeutralElement(K,A) \<noteq> TheNeutralElement(K,M) \<and>
  (\<forall>a\<in>K. a\<noteq>TheNeutralElement(K,A)\<longrightarrow>
  (\<exists>b\<in>K. M`\<langle>a,b\<rangle> = TheNeutralElement(K,M))))"

text\<open>The next context (locale) defines notation used for ordered fields. 
  We do that by extending the notation defined in the 
  \<open>ring1\<close> context that is used for oredered rings and 
  adding some assumptions to make sure we are 
  talking about ordered fields in this context. 
  We should rename the carrier from $R$ used in the \<open>ring1\<close> 
  context to $K$, more appriopriate for fields. Theoretically the Isar locale
  facility supports such renaming, but we experienced diffculties using
  some lemmas from \<open>ring1\<close> locale after renaming. 
\<close>

locale field1 = ring1 +

  assumes mult_commute: "M {is commutative on} R"
  
  assumes not_triv: "\<zero> \<noteq> \<one>"

  assumes inv_exists: "\<forall>a\<in>R. a\<noteq>\<zero> \<longrightarrow> (\<exists>b\<in>R. a\<cdot>b = \<one>)"

  fixes non_zero ("R\<^sub>0")
  defines non_zero_def[simp]: "R\<^sub>0 \<equiv> R-{\<zero>}"

  fixes inv ("_\<inverse> " [96] 97)
  defines inv_def[simp]: "a\<inverse> \<equiv> GroupInv(R\<^sub>0,restrict(M,R\<^sub>0\<times>R\<^sub>0))`(a)"

text\<open>The next lemma assures us that we are talking fields 
  in the \<open>field1\<close> context.\<close>

lemma (in field1) OrdField_ZF_1_L1: shows "IsAnOrdField(R,A,M,r)"
  using OrdRing_ZF_1_L1 mult_commute not_triv inv_exists IsAnOrdField_def
  by simp

text\<open>Ordered field is a field, of course.\<close>

lemma OrdField_ZF_1_L1A: assumes "IsAnOrdField(K,A,M,r)"
  shows "IsAfield(K,A,M)"
  using assms IsAnOrdField_def IsAnOrdRing_def IsAfield_def
  by simp

text\<open>Theorems proven in \<open>field0\<close> (about fields) context are valid
  in the \<open>field1\<close> context (about ordered fields).\<close>

lemma (in field1) OrdField_ZF_1_L1B: shows "field0(R,A,M)"
  using OrdField_ZF_1_L1 OrdField_ZF_1_L1A field_field0
  by simp

text\<open>We can use theorems proven in the \<open>field1\<close> context whenever we
  talk about an ordered field.\<close>

lemma OrdField_ZF_1_L2: assumes "IsAnOrdField(K,A,M,r)"
  shows "field1(K,A,M,r)"
  using assms IsAnOrdField_def OrdRing_ZF_1_L2 ring1_def
    IsAnOrdField_def field1_axioms_def field1_def
  by auto

text\<open>In ordered rings the existence of a right inverse for all positive
  elements implies the existence of an inverse for all non zero elements.\<close>

lemma (in ring1) OrdField_ZF_1_L3: 
  assumes A1: "\<forall>a\<in>R\<^sub>+. \<exists>b\<in>R. a\<cdot>b = \<one>" and A2: "c\<in>R"  "c\<noteq>\<zero>"
  shows "\<exists>b\<in>R. c\<cdot>b = \<one>"
proof -
  { assume "c\<in>R\<^sub>+"
    with A1 have "\<exists>b\<in>R. c\<cdot>b = \<one>" by simp }
  moreover
  { assume "c\<notin>R\<^sub>+"
    with A2 have "(\<rm>c) \<in> R\<^sub>+"
      using OrdRing_ZF_3_L2A by simp
    with A1 obtain b where "b\<in>R" and "(\<rm>c)\<cdot>b = \<one>"
      by auto
    with A2 have "(\<rm>b) \<in> R"  "c\<cdot>(\<rm>b) = \<one>"
      using Ring_ZF_1_L3 Ring_ZF_1_L7 by auto
    then have "\<exists>b\<in>R. c\<cdot>b = \<one>" by auto }
  ultimately show ?thesis by blast
qed
  
text\<open>Ordered fields are easier to deal with, because it is sufficient 
  to show the existence of an inverse for the set of positive elements.\<close>

lemma (in ring1) OrdField_ZF_1_L4: 
  assumes "\<zero> \<noteq> \<one>" and "M {is commutative on} R" 
  and "\<forall>a\<in>R\<^sub>+. \<exists>b\<in>R. a\<cdot>b = \<one>"
  shows "IsAnOrdField(R,A,M,r)"
  using assms OrdRing_ZF_1_L1 OrdField_ZF_1_L3 IsAnOrdField_def
  by simp

text\<open>The set of positive field elements is closed under multiplication.\<close>

lemma (in field1) OrdField_ZF_1_L5: shows "R\<^sub>+ {is closed under} M"
  using OrdField_ZF_1_L1B field0.field_has_no_zero_divs OrdRing_ZF_3_L3
  by simp

text\<open>The set of positive field elements is closed under multiplication:
  the explicit version.\<close>

lemma (in field1) pos_mul_closed: 
  assumes A1: "\<zero> \<ls> a"  "\<zero> \<ls> b"
  shows "\<zero> \<ls> a\<cdot>b"
proof -
  from A1 have "a \<in> R\<^sub>+" and  "b \<in> R\<^sub>+"
    using OrdRing_ZF_3_L14 by auto
  then show "\<zero> \<ls> a\<cdot>b" 
    using OrdField_ZF_1_L5 IsOpClosed_def PositiveSet_def
    by simp
qed


text\<open>In fields square of a nonzero element is positive.\<close>

lemma (in field1) OrdField_ZF_1_L6: assumes "a\<in>R"  "a\<noteq>\<zero>"
  shows "a\<^sup>2 \<in> R\<^sub>+"
  using assms OrdField_ZF_1_L1B field0.field_has_no_zero_divs
    OrdRing_ZF_3_L15 by simp

text\<open>The next lemma restates the fact \<open>Field_ZF\<close> that out notation
  for the field inverse means what it is supposed to mean.\<close>

lemma (in field1) OrdField_ZF_1_L7: assumes "a\<in>R"  "a\<noteq>\<zero>"
  shows "a\<cdot>(a\<inverse>) = \<one>"  "(a\<inverse>)\<cdot>a = \<one>"
  using assms OrdField_ZF_1_L1B field0.Field_ZF_1_L6
  by auto

text\<open>A simple lemma about multiplication and cancelling of a positive field
   element.\<close>

lemma (in field1) OrdField_ZF_1_L7A: 
  assumes A1: "a\<in>R"  "b \<in> R\<^sub>+"
  shows 
  "a\<cdot>b\<cdot>b\<inverse> = a"
  "a\<cdot>b\<inverse>\<cdot>b = a"
proof -
  from A1 have "b\<in>R"  "b\<noteq>\<zero>" using PositiveSet_def
    by auto
  with A1 show  "a\<cdot>b\<cdot>b\<inverse> = a" and "a\<cdot>b\<inverse>\<cdot>b = a"
    using OrdField_ZF_1_L1B field0.Field_ZF_1_L7
    by auto
qed
    
text\<open>Some properties of the inverse of a positive element.\<close>

lemma (in field1) OrdField_ZF_1_L8: assumes A1: "a \<in> R\<^sub>+"
  shows "a\<inverse> \<in> R\<^sub>+"  "a\<cdot>(a\<inverse>) = \<one>"  "(a\<inverse>)\<cdot>a = \<one>"
proof -
  from A1 have I: "a\<in>R"  "a\<noteq>\<zero>" using PositiveSet_def 
    by auto
  with A1 have "a\<cdot>(a\<inverse>)\<^sup>2 \<in> R\<^sub>+" 
    using OrdField_ZF_1_L1B field0.Field_ZF_1_L5 OrdField_ZF_1_L6
      OrdField_ZF_1_L5 IsOpClosed_def by simp
  with I show "a\<inverse> \<in> R\<^sub>+"
    using OrdField_ZF_1_L1B field0.Field_ZF_2_L1
    by simp
  from I show  "a\<cdot>(a\<inverse>) = \<one>"  "(a\<inverse>)\<cdot>a = \<one>"
    using OrdField_ZF_1_L7 by auto
qed

text\<open>If $a$ is smaller than $b$, then $(b-a)^{-1}$ is positive.\<close>

lemma (in field1) OrdField_ZF_1_L9: assumes "a\<ls>b"
  shows  "(b\<rs>a)\<inverse> \<in> R\<^sub>+"  
  using assms OrdRing_ZF_1_L14 OrdField_ZF_1_L8
  by simp

text\<open>In ordered fields if at least one of $a,b$ is not zero, then
  $a^2+b^2 > 0$, in particular $a^2+b^2\neq 0$ and exists the 
  (multiplicative) inverse of $a^2+b^2$.\<close>

lemma (in field1) OrdField_ZF_1_L10: 
  assumes A1: "a\<in>R"  "b\<in>R" and A2: "a \<noteq> \<zero> \<or> b \<noteq> \<zero>"
  shows "\<zero> \<ls> a\<^sup>2 \<ra> b\<^sup>2"  and "\<exists>c\<in>R. (a\<^sup>2 \<ra> b\<^sup>2)\<cdot>c = \<one>"
proof -
  from A1 A2 show "\<zero> \<ls> a\<^sup>2 \<ra> b\<^sup>2"
    using OrdField_ZF_1_L1B field0.field_has_no_zero_divs 
      OrdRing_ZF_3_L19 by simp
  then have 
    "(a\<^sup>2 \<ra> b\<^sup>2)\<inverse> \<in> R" and "(a\<^sup>2 \<ra> b\<^sup>2)\<cdot>(a\<^sup>2 \<ra> b\<^sup>2)\<inverse> = \<one>"
    using OrdRing_ZF_1_L3 PositiveSet_def OrdField_ZF_1_L8
    by auto
  then show "\<exists>c\<in>R. (a\<^sup>2 \<ra> b\<^sup>2)\<cdot>c = \<one>" by auto
qed
  
subsection\<open>Inequalities\<close>

text\<open>In this section we develop tools to deal inequalities in fields.\<close>

text\<open>We can multiply strict inequality by a positive element.\<close>

lemma (in field1) OrdField_ZF_2_L1: 
  assumes "a\<ls>b" and "c\<in>R\<^sub>+"
  shows "a\<cdot>c \<ls> b\<cdot>c"
  using assms OrdField_ZF_1_L1B field0.field_has_no_zero_divs
    OrdRing_ZF_3_L13
  by simp

text\<open>A special case of \<open>OrdField_ZF_2_L1\<close> when we multiply
  an inverse by an element.\<close>

lemma (in field1) OrdField_ZF_2_L2: 
  assumes A1: "a\<in>R\<^sub>+" and A2: "a\<inverse> \<ls> b"
  shows "\<one> \<ls> b\<cdot>a"
proof -
  from A1 A2 have "(a\<inverse>)\<cdot>a \<ls> b\<cdot>a"
    using OrdField_ZF_2_L1 by simp
  with A1 show "\<one> \<ls> b\<cdot>a"
    using OrdField_ZF_1_L8 by simp
qed

text\<open>We can multiply an inequality by the inverse of a positive element.\<close>

lemma (in field1) OrdField_ZF_2_L3:
  assumes "a\<lsq>b"  and "c\<in>R\<^sub>+" shows "a\<cdot>(c\<inverse>) \<lsq> b\<cdot>(c\<inverse>)"
  using assms OrdField_ZF_1_L8 OrdRing_ZF_1_L9A
  by simp

text\<open>We can multiply a strict inequality by a  positive element
  or its inverse.\<close>

lemma (in field1) OrdField_ZF_2_L4:
  assumes "a\<ls>b" and "c\<in>R\<^sub>+"
  shows 
  "a\<cdot>c \<ls> b\<cdot>c"
  "c\<cdot>a \<ls> c\<cdot>b"
  "a\<cdot>c\<inverse> \<ls> b\<cdot>c\<inverse>"
   using assms OrdField_ZF_1_L1B field0.field_has_no_zero_divs
    OrdField_ZF_1_L8 OrdRing_ZF_3_L13 by auto

text\<open>We can put a positive factor on the other side of an inequality,
  changing it to its inverse.\<close>

lemma (in field1) OrdField_ZF_2_L5:
  assumes A1: "a\<in>R"  "b\<in>R\<^sub>+" and A2: "a\<cdot>b \<lsq> c"
  shows "a \<lsq> c\<cdot>b\<inverse>"
proof -
  from A1 A2 have "a\<cdot>b\<cdot>b\<inverse> \<lsq> c\<cdot>b\<inverse>"
    using OrdField_ZF_2_L3 by simp
  with A1 show "a \<lsq> c\<cdot>b\<inverse>" using OrdField_ZF_1_L7A
    by simp
qed

text\<open>We can put a positive factor on the other side of an inequality,
  changing it to its inverse, version with a product initially on the 
  right hand side.\<close>

lemma (in field1) OrdField_ZF_2_L5A:
  assumes A1: "b\<in>R"  "c\<in>R\<^sub>+" and A2: "a \<lsq> b\<cdot>c"
  shows "a\<cdot>c\<inverse> \<lsq> b"
proof -
  from A1 A2 have "a\<cdot>c\<inverse> \<lsq> b\<cdot>c\<cdot>c\<inverse>"
    using OrdField_ZF_2_L3 by simp
  with A1 show "a\<cdot>c\<inverse> \<lsq> b" using OrdField_ZF_1_L7A
    by simp
qed

text\<open>We can put a positive factor on the other side of a strict
  inequality, changing it to its inverse, version with a product
  initially on the left hand side.\<close>

lemma (in field1) OrdField_ZF_2_L6:
  assumes A1: "a\<in>R"  "b\<in>R\<^sub>+" and A2: "a\<cdot>b \<ls> c"
  shows "a \<ls> c\<cdot>b\<inverse>"
proof -
  from A1 A2 have "a\<cdot>b\<cdot>b\<inverse> \<ls> c\<cdot>b\<inverse>"
    using OrdField_ZF_2_L4 by simp
  with A1 show "a \<ls> c\<cdot>b\<inverse>" using OrdField_ZF_1_L7A
    by simp
qed

text\<open>We can put a positive factor on the other side of a strict
  inequality, changing it to its inverse, version with a product
  initially on the right hand side.\<close>

lemma (in field1) OrdField_ZF_2_L6A:
  assumes A1: "b\<in>R"  "c\<in>R\<^sub>+" and A2: "a \<ls> b\<cdot>c"
  shows "a\<cdot>c\<inverse> \<ls> b"
proof -
  from A1 A2 have "a\<cdot>c\<inverse> \<ls> b\<cdot>c\<cdot>c\<inverse>"
    using OrdField_ZF_2_L4 by simp
  with A1 show "a\<cdot>c\<inverse> \<ls> b" using OrdField_ZF_1_L7A
    by simp
qed

text\<open>Sometimes we can reverse an inequality by taking inverse
  on both sides.\<close>

lemma (in field1) OrdField_ZF_2_L7: 
  assumes A1: "a\<in>R\<^sub>+" and A2: "a\<inverse> \<lsq> b"
  shows "b\<inverse> \<lsq> a"
proof -
  from A1 have "a\<inverse> \<in> R\<^sub>+" using OrdField_ZF_1_L8
    by simp
  with A2 have "b \<in> R\<^sub>+" using  OrdRing_ZF_3_L7
    by blast
  then have T: "b \<in> R\<^sub>+"  "b\<inverse> \<in> R\<^sub>+" using OrdField_ZF_1_L8
    by auto
  with A1 A2 have "b\<inverse>\<cdot>a\<inverse>\<cdot>a \<lsq> b\<inverse>\<cdot>b\<cdot>a"
    using OrdRing_ZF_1_L9A by simp
  moreover 
  from A1 A2 T have
    "b\<inverse> \<in> R"  "a\<in>R" "a\<noteq>\<zero>"  "b\<in>R"  "b\<noteq>\<zero>"
    using PositiveSet_def OrdRing_ZF_1_L3 by auto
  then have "b\<inverse>\<cdot>a\<inverse>\<cdot>a = b\<inverse>" and  "b\<inverse>\<cdot>b\<cdot>a = a"
    using OrdField_ZF_1_L1B field0.Field_ZF_1_L7 
      field0.Field_ZF_1_L6 Ring_ZF_1_L3
    by auto
  ultimately show "b\<inverse> \<lsq> a" by simp
qed

text\<open>Sometimes we can reverse a strict inequality by taking inverse
  on both sides.\<close>

lemma (in field1) OrdField_ZF_2_L8: 
  assumes A1: "a\<in>R\<^sub>+" and A2: "a\<inverse> \<ls> b"
  shows "b\<inverse> \<ls> a"
proof -
  from A1 A2 have "a\<inverse> \<in> R\<^sub>+"  "a\<inverse> \<lsq>b"
    using OrdField_ZF_1_L8 by auto
  then have "b \<in> R\<^sub>+" using OrdRing_ZF_3_L7
    by blast
  then have "b\<in>R"  "b\<noteq>\<zero>" using PositiveSet_def by auto
  with A2 have "b\<inverse> \<noteq> a"
    using OrdField_ZF_1_L1B field0.Field_ZF_2_L4
    by simp
  with A1 A2 show "b\<inverse> \<ls> a"
    using OrdField_ZF_2_L7 by simp
qed
    
text\<open>A technical lemma about solving a strict inequality with three
  field elements and inverse of a difference.\<close>

lemma (in field1) OrdField_ZF_2_L9: 
  assumes A1: "a\<ls>b" and A2: "(b\<rs>a)\<inverse> \<ls> c"
  shows "\<one> \<ra> a\<cdot>c \<ls> b\<cdot>c"
proof -
  from A1 A2 have "(b\<rs>a)\<inverse> \<in> R\<^sub>+"  "(b\<rs>a)\<inverse> \<lsq> c" 
    using OrdField_ZF_1_L9 by auto
  then have T1: "c \<in> R\<^sub>+" using OrdRing_ZF_3_L7 by blast
  with A1 A2 have T2: 
    "a\<in>R"  "b\<in>R"  "c\<in>R"  "c\<noteq>\<zero>"   "c\<inverse> \<in> R"
    using OrdRing_ZF_1_L3 OrdField_ZF_1_L8 PositiveSet_def 
    by auto
  with A1 A2  have "c\<inverse> \<ra> a \<ls> b\<rs>a \<ra> a"
    using OrdRing_ZF_1_L14 OrdField_ZF_2_L8 ring_strict_ord_trans_inv
    by simp
  with T1 T2 have "(c\<inverse> \<ra> a)\<cdot>c \<ls> b\<cdot>c"
    using Ring_ZF_2_L1A OrdField_ZF_2_L1 by simp
  with T1 T2 show "\<one> \<ra> a\<cdot>c \<ls> b\<cdot>c"
    using ring_oper_distr OrdField_ZF_1_L8
    by simp
qed

subsection\<open>Definition of real numbers\<close>

text\<open>The only purpose of this section is to define what does it mean
  to be a model of real numbers.\<close>

text\<open>We define model of real numbers as any quadruple of sets $(K,A,M,r)$ 
  such that $(K,A,M,r)$ is an ordered field and the order relation $r$
  is complete, that is every set that is nonempty and bounded above in this 
  relation has a supremum.\<close>

definition
  "IsAmodelOfReals(K,A,M,r) \<equiv> IsAnOrdField(K,A,M,r) \<and> (r {is complete})"

end