(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2024 Slawomir Kolodynski

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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. *)

section \<open>Integer powers of group elements\<close>

theory IntGroup_ZF imports Int_ZF_1

begin

text\<open>In the \<open>Monoid_ZF_1\<close> theory we consider multiplicities of $n\cdot x$ of monoid elements, i.e.
  special cases of expressions of the form $x_1\oplus x_2\oplus\dots\oplus x_n$ where $x_i=x$ 
  for $i=1..n$.
  In the group context where we usually use multiplicative notation this translates to the "power"
  $x^n$ where $n\in \mathbb{N}$, see also section "Product of a list of group elements" in 
  the \<open>Group_ZF\<close> theory. In the group setting the notion of raising an element to natural power can
  be naturally generalized to the notion of raising an element to an integer power. \<close>

subsection\<open>Properties of natural powers of an element and its inverse\<close>

text\<open>The integer power is defined in terms of natural powers of an element and its inverse. 
  In this section we study properties of expressions $(x^n)\cdot(x^{-1})^k$, where $x$ is a group
  element and $n,k$ are natural numbers. \<close>

text\<open>The natural power of $x$ multiplied by the same power of $x^{-1}$ cancel out to give
  the neutral element of the group.\<close>

lemma (in group0) nat_pow_inv_cancel: assumes "n\<in>nat" "x\<in>G"
  shows "pow(n,x)\<cdot>pow(n,x\<inverse>) = \<one>"
proof -
  from assms(1) have "n\<in>nat" and "pow(0,x)\<cdot>pow(0,x\<inverse>) = \<one>"
    using monoid.nat_mult_zero group0_2_L2 by simp_all
  moreover have "\<forall>k\<in>nat. pow(k,x)\<cdot>pow(k,x\<inverse>) = \<one> \<longrightarrow> pow(k #+ 1,x)\<cdot>pow(k #+ 1,x\<inverse>) = \<one>"
  proof -
    { fix k assume "k\<in>nat" and "pow(k,x)\<cdot>pow(k,x\<inverse>) = \<one>"
      from assms(2) \<open>k\<in>nat\<close> have 
        "pow(k #+ 1,x)\<cdot>pow(k #+ 1,x\<inverse>) = pow(k,x)\<cdot>x\<cdot>(x\<inverse>\<cdot>pow(k,x\<inverse>))"
      using inverse_in_group nat_pow_add_one by simp
      with assms(2) \<open>k\<in>nat\<close> \<open>pow(k,x)\<cdot>pow(k,x\<inverse>) = \<one>\<close> have
        "pow(k #+ 1,x)\<cdot>pow(k #+ 1,x\<inverse>) = \<one>"
        using monoid.nat_mult_type inverse_in_group monoid.rearr4elem_monoid
          group0_2_L6(1) group0_2_L2 by simp        
    } thus ?thesis by simp
  qed
  ultimately show ?thesis by (rule ind_on_nat1)
qed

text\<open>The natural power of $x^{-1}$ multiplied by the same power of $x$ cancel out to give
  the neutral element of the group. Same as \<open>nat_pow_inv_cancel\<close> written with $x^{-1}$
  instead of $x$. \<close>

lemma (in group0) nat_pow_inv_cancel1: assumes "n\<in>nat" "x\<in>G"
  shows "pow(n,x\<inverse>)\<cdot>pow(n,x) = \<one>"
proof -
  from assms have "pow(n,x\<inverse>)\<cdot>pow(n,(x\<inverse>)\<inverse>) = \<one>"
    using inverse_in_group nat_pow_inv_cancel by simp
  with assms(2) show "pow(n,x\<inverse>)\<cdot>pow(n,x) = \<one>"
    using group_inv_of_inv by simp
qed

text\<open>If $k\leq n$ are natural numbers and $x$ an element of the group, then
  $x^n\cdot (x^{-1})^k = x^(k-n)$. \<close>

lemma (in group0) nat_pow_cancel_less: assumes "n\<in>nat" "k\<le>n" "x\<in>G"
  shows "pow(n,x)\<cdot>pow(k,x\<inverse>) = pow(n #- k,x)"
proof -
  from assms have 
    "k\<in>nat" "n #- k \<in> nat" "pow((n #- k),x) \<in> G" "pow(k,x) \<in> G" "pow(k,x\<inverse>) \<in> G"
    using leq_nat_is_nat diff_type monoid.nat_mult_type inverse_in_group 
    by simp_all
  from assms(3) \<open>k\<in>nat\<close> \<open>n #- k \<in> nat\<close> have 
    "pow((n #- k) #+ k,x) = pow((n #- k),x)\<cdot>pow(k,x)"
    using monoid.nat_mult_add by simp
  with assms(1,2) \<open>pow((n #- k),x) \<in> G\<close> \<open>pow(k,x) \<in> G\<close> \<open>pow(k,x\<inverse>) \<in> G\<close> 
    have "pow(n,x)\<cdot>pow(k,x\<inverse>) = pow(n #- k,x)\<cdot>(pow(k,x)\<cdot>pow(k,x\<inverse>))"
      using add_diff_inverse2 group_oper_assoc by simp
  with assms(3) \<open>k\<in>nat\<close> \<open>pow((n #- k),x) \<in> G\<close> show ?thesis
    using nat_pow_inv_cancel group0_2_L2 by simp 
qed

text\<open>If $k\leq n$ are natural numbers and $x$ an element of the group, then
  $(x^{-1})^n\cdot x^k = (x^{-1})^(k-n)$. \<close>

lemma (in group0) nat_pow_cancel_less1: assumes "n\<in>nat" "k\<le>n" "x\<in>G"
  shows "pow(n,x\<inverse>)\<cdot>pow(k,x) = pow(n #- k,x\<inverse>)"
proof -
  from assms have "pow(n,x\<inverse>)\<cdot>pow(k,(x\<inverse>)\<inverse>) = pow(n #- k,x\<inverse>)"
    using inverse_in_group nat_pow_cancel_less by simp
  with assms(3) show ?thesis using group_inv_of_inv by simp
qed

text\<open>If $k\leq n$ are natural numbers and $x$ an element of the group, then
  $x^k\cdot (x^{-1})^n = (x^{-1})^(k-n)$. \<close>

lemma (in group0) nat_pow_cancel_more: assumes "n\<in>nat" "k\<le>n" "x\<in>G"
  shows "pow(k,x\<inverse>)\<cdot>pow(n,x) = pow(n #- k,x)"
proof -
  from assms have
    "k\<in>nat" "n #- k \<in> nat" "pow((n #- k),x) \<in> G" "pow(k,x) \<in> G" "pow(k,x\<inverse>) \<in> G"
    using leq_nat_is_nat diff_type monoid.nat_mult_type inverse_in_group 
      by simp_all
  from assms(3) \<open>k\<in>nat\<close> \<open>n #- k \<in> nat\<close> have 
    "pow(k #+ (n #- k),x) = pow(k,x)\<cdot>pow((n #- k),x)"
    using monoid.nat_mult_add by simp
  with assms(1,2) \<open>pow((n #- k),x) \<in> G\<close> \<open>pow(k,x) \<in> G\<close> \<open>pow(k,x\<inverse>) \<in> G\<close> 
  have "pow(k,x\<inverse>)\<cdot>pow(n,x) = (pow(k,x\<inverse>)\<cdot>pow(k,x))\<cdot>pow(n #- k,x)"
    using add_diff_inverse group_oper_assoc by simp
  with assms(3) \<open>k\<in>nat\<close> \<open>pow((n #- k),x) \<in> G\<close> show ?thesis
    using nat_pow_inv_cancel1 group0_2_L2 by simp  
qed

text\<open>If $k\leq n$ are natural numbers and $x$ an element of the group, then
  $(x^{-1})^k\cdot x^n = x^(k-n)$. \<close>

lemma (in group0) nat_pow_cancel_more1: assumes "n\<in>nat" "k\<le>n" "x\<in>G"
  shows "pow(k,x)\<cdot>pow(n,x\<inverse>) = pow(n #- k,x\<inverse>)"
proof -
  from assms have "pow(k,(x\<inverse>)\<inverse>)\<cdot>pow(n,x\<inverse>) = pow(n #- k,x\<inverse>)"
    using inverse_in_group nat_pow_cancel_more by simp
  with assms(3) show ?thesis using group_inv_of_inv by simp
qed

subsection\<open>Integer powers\<close>

text\<open>In this section we introduce notation basic properties of integer power in group context.
  The goal is to show that the power homomorphism property: if $x$ is an element of the group
  and $n,m$ are integers then $x^{n+m}=x^n\cdot x^m$. \<close>

text\<open>We extend the \<open>group0\<close> context with some notation from \<open>int0\<close> context.
  We also define notation for the integer power \<open>powz(z,x)\<close>. 
  The difficulty there is that in ZF set theory nonnegative integers and natural numbers are 
  different things. However, standard Isabelle/ZF defines a meta-function \<open>nat_of\<close> 
  that we can use to convert one into the other. 
  Hence, we define the integer power \<open>powz(z,x)\<close> as $x$ raised to the corresponding
  natural power if $z$ is a nonnegative and  $x^{-1}$ raised to natural power corresponding
  to $-z$ otherwise. Since we inherit the multiplicative notation from the \<open>group0\<close> context
  the integer "one" is denoted \<open>\<one>\<^sub>Z\<close> rather than just \<open>\<one>\<close> (which is the group's neutral element). \<close>

locale group_int0 = group0 +

  fixes ints ("\<int>")
  defines ints_def [simp]: "\<int> \<equiv> int"

  fixes ia (infixl "\<ra>" 69)
  defines ia_def [simp]: "a\<ra>b \<equiv> IntegerAddition`\<langle> a,b\<rangle>"

  fixes iminus ("\<rm> _" 72)
  defines rminus_def [simp]: "\<rm>a \<equiv> GroupInv(\<int>,IntegerAddition)`(a)"

  fixes isub (infixl "\<rs>" 69)
  defines isub_def [simp]: "a\<rs>b \<equiv> a\<ra> (\<rm> b)"

  fixes izero ("\<zero>")
  defines izero_def [simp]: "\<zero> \<equiv> TheNeutralElement(\<int>,IntegerAddition)"

  fixes ione ("\<one>\<^sub>Z")
  defines ione_def [simp]: "\<one>\<^sub>Z \<equiv> TheNeutralElement(\<int>,IntegerMultiplication)"

  fixes nonnegative ("\<int>\<^sup>+")
  defines nonnegative_def [simp]: 
    "\<int>\<^sup>+ \<equiv> Nonnegative(\<int>,IntegerAddition,IntegerOrder)"

  fixes lesseq (infix "\<lsq>" 60)
  defines lesseq_def [simp]: "m \<lsq> n \<equiv> \<langle>m,n\<rangle> \<in> IntegerOrder"

  fixes sless (infix "\<ls>" 68)
  defines sless_def [simp]: "a \<ls> b \<equiv> a\<lsq>b \<and> a\<noteq>b"

  fixes powz
  defines powz_def [simp]: 
    "powz(z,x) \<equiv> pow(zmagnitude(z),if \<zero>\<lsq>z then x else x\<inverse>)"

text\<open>An integer power of a group element is in the group.\<close>

lemma (in group_int0) powz_type: assumes "z\<in>\<int>" "x\<in>G" shows "powz(z,x) \<in> G"
  using assms zmagnitude_type monoid.nat_mult_type inverse_in_group by simp

text\<open>A group element raised to (integer) zero'th power is equal to the group's neutral element. 
  An element raised to (integer) power one is the same element. \<close>

lemma (in group_int0) int_power_zero_one: assumes "x\<in>G"
  shows "powz(\<zero>,x) = \<one>" and "powz(\<one>\<^sub>Z,x) = x"
  using assms int0.Int_ZF_1_L8A(1) int0.int_ord_is_refl1 int0.zmag_zero_one 
    monoid.nat_mult_zero int0.Int_ZF_2_L16A(1) monoid.nat_mult_one by auto

text\<open>If $x$ is an element of the group and $z_1,z_2$ are nonnegative integers then
  $x^{z_1+z_2}=x^{z_1}\cdot x^{z_2}$, i.e. the power homomorphism property holds.\<close>

lemma (in group_int0) powz_hom_nneg_nneg: assumes "\<zero>\<lsq>z\<^sub>1" "\<zero>\<lsq>z\<^sub>2" "x\<in>G"
  shows "powz(z\<^sub>1\<ra>z\<^sub>2,x) = powz(z\<^sub>1,x)\<cdot>powz(z\<^sub>2,x)"
  using assms int0.add_nonneg_ints(1,2) monoid.nat_mult_add by simp

text\<open>If $x$ is an element of the group and $z_1,z_2$ are negative integers then
  the power homomorphism property holds.\<close>

lemma (in group_int0) powz_hom_neg_neg: 
  assumes "z\<^sub>1\<ls>\<zero>" "z\<^sub>2\<ls>\<zero>" "x\<in>G"
  shows "powz(z\<^sub>1\<ra>z\<^sub>2,x) = powz(z\<^sub>1,x)\<cdot>powz(z\<^sub>2,x)"
  using assms int0.neg_not_nonneg int0.add_neg_ints(1,2) 
    inverse_in_group monoid.nat_mult_add by simp

text\<open>When the integers are of different signs we further split into cases depending on
  which magnitude is greater. If $x$ is an element of the group and $z_1$ is nonnegative, 
  $z_2$ is negative and $|z_2|\leq |z_1|$ then the power homomorphism property holds.
  The proof of this lemma is presented with more detail than necessary, 
  to show the schema of the proofs of the remaining lemmas that we let Isabelle prove 
  automatically.\<close>

lemma (in group_int0) powz_hom_nneg_neg1: 
  assumes "\<zero>\<lsq>z\<^sub>1"  "z\<^sub>2\<ls>\<zero>" "zmagnitude(z\<^sub>2) \<le> zmagnitude(z\<^sub>1)" "x\<in>G"
  shows "powz(z\<^sub>1\<ra>z\<^sub>2,x) = powz(z\<^sub>1,x)\<cdot>powz(z\<^sub>2,x)"
proof -
  let ?m\<^sub>1 = "zmagnitude(z\<^sub>1)" 
  let ?m\<^sub>2 = "zmagnitude(z\<^sub>2)"
  from assms(1,2,3) have "powz(z\<^sub>1\<ra>z\<^sub>2,x) = pow(zmagnitude(z\<^sub>1\<ra>z\<^sub>2),x)"
    using int0.add_nonneg_neg1(1) by simp
  also from assms(1,2,3) have "... =  pow(?m\<^sub>1 #- ?m\<^sub>2,x)" 
    using int0.add_nonneg_neg1(2) by simp
  also from assms(3,4) have "... = pow(?m\<^sub>1,x)\<cdot>pow(?m\<^sub>2,x\<inverse>)"
    using nat_pow_cancel_less by simp
  also from assms(1,2) have "... = powz(z\<^sub>1,x)\<cdot>powz(z\<^sub>2,x)" 
    using int0.neg_not_nonneg by simp
  finally show ?thesis by simp
qed

text\<open>If $x$ is an element of the group and $z_1$ is nonnegative, 
  $z_2$ is negative and $|z_1|<|z_2|$ then the power homomorphism property holds.\<close>

lemma (in group_int0) powz_hom_nneg_neg2:
  assumes "\<zero>\<lsq>z\<^sub>1"  "z\<^sub>2\<ls>\<zero>"  "zmagnitude(z\<^sub>1) < zmagnitude(z\<^sub>2)" "x\<in>G"
  shows "powz(z\<^sub>1\<ra>z\<^sub>2,x) = powz(z\<^sub>1,x)\<cdot>powz(z\<^sub>2,x)"
  using assms int0.add_nonneg_neg2 int0.neg_not_nonneg leI nat_pow_cancel_more1
  by simp

text\<open>If $x$ is an element of the group and $z_1$ is negative, 
  $z_2$ is nonnegative and $|z_1|\leq |z_2|$ then the power homomorphism property holds.\<close>

lemma (in group_int0) powz_hom_neg_nneg1:
  assumes "z\<^sub>1\<ls>\<zero>" "\<zero>\<lsq>z\<^sub>2" "zmagnitude(z\<^sub>1) \<le> zmagnitude(z\<^sub>2)" "x\<in>G"
  shows "powz(z\<^sub>1\<ra>z\<^sub>2,x) = powz(z\<^sub>1,x)\<cdot>powz(z\<^sub>2,x)"
  using assms int0.add_neg_nonneg1 nat_pow_cancel_more int0.neg_not_nonneg
  by simp

text\<open>If $x$ is an element of the group and $z_1$ is negative, 
  $z_2$ is nonnegative and $|z_2| < |z_1|$ then the power homomorphism property holds.\<close>

lemma (in group_int0) powz_hom_neg_nneg2:
  assumes "z\<^sub>1\<ls>\<zero>" "\<zero>\<lsq>z\<^sub>2" "zmagnitude(z\<^sub>2) < zmagnitude(z\<^sub>1)" "x\<in>G"
  shows "powz(z\<^sub>1\<ra>z\<^sub>2,x) = powz(z\<^sub>1,x)\<cdot>powz(z\<^sub>2,x)"
  using assms int0.add_neg_nonneg2 int0.neg_not_nonneg leI nat_pow_cancel_less1
  by simp

text\<open>The next theorem collects the results from the above lemmas to show
  the power homomorphism property holds for any pair of integer numbers
  and any group element. \<close>

theorem (in group_int0) powz_hom_prop: assumes "z\<^sub>1\<in>\<int>" "z\<^sub>2\<in>\<int>" "x\<in>G"
  shows "powz(z\<^sub>1\<ra>z\<^sub>2,x) = powz(z\<^sub>1,x)\<cdot>powz(z\<^sub>2,x)"
proof -
  from assms(1,2) have 
   "(\<zero>\<lsq>z\<^sub>1 \<and> \<zero>\<lsq>z\<^sub>2) \<or> (z\<^sub>1\<ls>\<zero> \<and> z\<^sub>2\<ls>\<zero>) \<or>
    (\<zero>\<lsq>z\<^sub>1 \<and> z\<^sub>2\<ls>\<zero> \<and> zmagnitude(z\<^sub>2) \<le> zmagnitude(z\<^sub>1)) \<or>
    (\<zero>\<lsq>z\<^sub>1 \<and> z\<^sub>2\<ls>\<zero> \<and> zmagnitude(z\<^sub>1) < zmagnitude(z\<^sub>2)) \<or>
    (z\<^sub>1\<ls>\<zero> \<and> \<zero>\<lsq>z\<^sub>2 \<and> zmagnitude(z\<^sub>1) \<le> zmagnitude(z\<^sub>2)) \<or>
    (z\<^sub>1\<ls>\<zero> \<and> \<zero>\<lsq>z\<^sub>2 \<and> zmagnitude(z\<^sub>2) < zmagnitude(z\<^sub>1))"
    using int0.int_pair_6cases by simp
  with assms(3) show ?thesis 
    using powz_hom_nneg_nneg powz_hom_neg_neg 
    powz_hom_nneg_neg1 powz_hom_nneg_neg2 
    powz_hom_neg_nneg1 powz_hom_neg_nneg2
    by blast
qed

text\<open>A group element raised to power $-1$ is the inverse of that group element.\<close>

lemma (in group_int0) inpt_power_neg_one: assumes "x\<in>G"
  shows "powz(\<rm>\<one>\<^sub>Z,x) = x\<inverse>"
  using assms int0.neg_not_nonneg int0.neg_one_less_zero int0.zmag_opposite_same(2) 
    int0.Int_ZF_1_L8A(2) int0.zmag_zero_one(2) inverse_in_group monoid.nat_mult_one 
  by simp

text\<open>Increasing the (integer) power by one is the same as multiplying by the group element.\<close>

lemma (in group_int0) int_power_add_one: assumes "z\<in>\<int>" "x\<in>G"
  shows "powz(z\<ra>\<one>\<^sub>Z,x) = powz(z,x)\<cdot>x"
  using assms int0.Int_ZF_1_L8A(2) powz_hom_prop int_power_zero_one(2)
  by simp

text\<open>For integer power taking a negative of the exponent is the same as taking inverse of the 
  group element. \<close>

lemma (in group_int0) minus_exp_inv_base: assumes "z\<in>\<int>" "x\<in>G"
  shows "powz(\<rm>z,x) = powz(z,x\<inverse>)"
proof -
  from assms(1) have "\<zero>\<ls>z \<or> z=\<zero> \<or> z\<ls>\<zero>"
    using int0.int_neg_zero_pos by simp
  moreover from assms(1) have "\<zero>\<ls>z \<longrightarrow> powz(\<rm>z,x) = powz(z,x\<inverse>)"
    using int0.neg_pos_int_neg int0.neg_not_nonneg int0.zmag_opposite_same(2) 
    by simp
  moreover from assms(2) have "z=\<zero> \<longrightarrow> powz(\<rm>z,x) = powz(z,x\<inverse>)"
    using int0.Int_ZF_1_L11 int_power_zero_one(1) inverse_in_group by simp
  moreover from assms have "z\<ls>\<zero> \<longrightarrow> powz(\<rm>z,x) = powz(z,x\<inverse>)"
    using int0.neg_not_nonneg int0.neg_neg_int_pos group_inv_of_inv 
        int0.zmag_opposite_same(2) by simp
  ultimately show "powz(\<rm>z,x) = powz(z,x\<inverse>)" by auto
qed

text\<open>Integer power of a group element is the same as the inverse of the element
  raised to negative of the exponent. \<close>

lemma (in group_int0) minus_exp_inv_base1: assumes "z\<in>\<int>" "x\<in>G"
  shows "powz(z,x) = powz(\<rm>z,x\<inverse>)"
proof -
  from assms(1) have "(\<rm>z)\<in>\<int>" using int0.int_neg_type by simp
  with assms show ?thesis using minus_exp_inv_base int0.neg_neg_noop
    by force
qed

text\<open>The next context is like \<open>group_int0\<close> but adds the assumption that the group 
  operation is commutative (i.e. the group is abelian). \<close>

locale abgroup_int0 = group_int0 +
  assumes isAbelian: "P {is commutative on} G"

text\<open>In abelian groups taking a nonnegative integer power commutes with the group operation.
  Unfortunately we have to drop to raw set theory notation in the proof to be able to use 
  \<open>int0.Induction_on_int\<close> from the \<open>abgroup_int0\<close> context.\<close>

lemma (in abgroup_int0) powz_groupop_commute0: assumes "\<zero>\<lsq>k" "x\<in>G" "y\<in>G"
  shows "powz(k,x\<cdot>y) = powz(k,x)\<cdot>powz(k,y)"
proof -
  from assms(1) have "\<langle>\<zero>,k\<rangle> \<in> IntegerOrder" by simp
  moreover 
  from assms(2,3) have "powz(\<zero>,x\<cdot>y) = powz(\<zero>,x)\<cdot>powz(\<zero>,y)"
    using group_op_closed int_power_zero_one(1) group0_2_L2
    by simp
  moreover
  { fix m assume "\<zero>\<lsq>m" and I: "powz(m,x\<cdot>y) = powz(m,x)\<cdot>powz(m,y)"
    from assms(2,3) \<open>\<zero>\<lsq>m\<close> have  "m\<in>\<int>" and "x\<cdot>y \<in> G"  
      using int0.Int_ZF_2_L1A(3) group_op_closed by simp_all
    with isAbelian assms(2,3) I have "powz(m\<ra>\<one>\<^sub>Z,x\<cdot>y) = powz(m\<ra>\<one>\<^sub>Z,x)\<cdot>powz(m\<ra>\<one>\<^sub>Z,y)"
      using int_power_add_one group0_4_L8(3) powz_type by simp
  } hence "\<forall>m. \<zero>\<lsq>m \<and> powz(m,x\<cdot>y) = powz(m,x)\<cdot>powz(m,y) \<longrightarrow>
     powz(m\<ra>\<one>\<^sub>Z,x\<cdot>y) = powz(m\<ra>\<one>\<^sub>Z,x)\<cdot>powz(m\<ra>\<one>\<^sub>Z,y)" by simp
  hence "\<forall>m. \<langle>\<zero>, m\<rangle> \<in> IntegerOrder \<and> powz(m,x\<cdot>y) = powz(m,x)\<cdot>powz(m,y) \<longrightarrow> 
    powz(IntegerAddition`\<langle>m,TheNeutralElement(int,IntegerMultiplication)\<rangle>,x\<cdot>y) = 
    powz(IntegerAddition`\<langle>m,TheNeutralElement(int,IntegerMultiplication)\<rangle>,x)\<cdot>
    powz(IntegerAddition`\<langle>m,TheNeutralElement(int,IntegerMultiplication)\<rangle>,y)"
    by simp
  ultimately show "powz(k,x\<cdot>y) = powz(k,x)\<cdot>powz(k,y)" by (rule int0.Induction_on_int)
qed

text\<open>In abelian groups taking a nonpositive integer power commutes with the group operation.
  We could use backwards induction in the proof but it is shorter to use the nonnegative 
  case from \<open>powz_groupop_commute0\<close>. \<close>

lemma (in abgroup_int0) powz_groupop_commute1: assumes "k\<lsq>\<zero>" "x\<in>G" "y\<in>G"
  shows "powz(k,x\<cdot>y) = powz(k,x)\<cdot>powz(k,y)"
proof -
  from isAbelian assms have "powz(k,x\<cdot>y) = powz(\<rm>k,x\<inverse>\<cdot>y\<inverse>)"
    using int0.Int_ZF_2_L1A(2) group_op_closed minus_exp_inv_base1 group_inv_of_two
    unfolding IsCommutative_def by simp
  with assms show ?thesis
    using int0.Int_ZF_2_L10A inverse_in_group powz_groupop_commute0 
      int0.Int_ZF_2_L1A(2) minus_exp_inv_base1 by simp
qed

text\<open>In abelian groups taking an integer power commutes with the group operation.\<close>

theorem (in abgroup_int0) powz_groupop_commute: assumes "z\<in>\<int>" "x\<in>G" "y\<in>G"
  shows "powz(z,x\<cdot>y) = powz(z,x)\<cdot>powz(z,y)"
proof -
  from assms(1) have "\<zero>\<lsq>z \<or> z\<lsq>\<zero>" using int0.int_nonneg_or_nonpos
    by auto
  with assms(2,3) show ?thesis using powz_groupop_commute0 powz_groupop_commute1
    by blast
qed

end