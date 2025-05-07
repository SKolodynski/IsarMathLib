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

theory IntGroup_ZF imports Group_ZF_2 Int_ZF_1

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

text\<open>The natural power of an element's inverse is the inverse of the power of the element.\<close>

lemma (in group0) nat_pow_inverse: assumes "n\<in>nat" "x\<in>G"
  shows "pow(n,x\<inverse>) = pow(n,x)\<inverse>"
proof -
  from assms(1) have "n\<in>nat" and "pow(0,x\<inverse>) = pow(0,x)\<inverse>"
    using monoid.nat_mult_zero group_inv_of_one by auto
  moreover
  {
    fix k assume hyp:"k\<in>nat" "pow(k,x\<inverse>) = pow(k,x)\<inverse>"
    have "pow(k#+1,x\<inverse>) = pow(k,x\<inverse>)\<cdot>x\<inverse>" using nat_pow_add_one(1) hyp(1)
      inverse_in_group assms(2) by auto
    then have "pow(k#+1,x\<inverse>) = pow(k,x)\<inverse>\<cdot>x\<inverse>" using hyp(2) by auto
    then have "pow(k#+1,x\<inverse>) = (x\<cdot>pow(k,x))\<inverse>" using group_inv_of_two
      assms(2) monoid.nat_mult_type hyp(1) by auto
    then have "pow(k#+1,x\<inverse>) = pow(k#+1,x)\<inverse>" using nat_pow_add_one(2)
      hyp(1) assms(2) by auto
  }
  then have "\<forall>k\<in>nat. pow(k,x\<inverse>) = pow(k,x)\<inverse> \<longrightarrow> pow(k#+1,x\<inverse>) = pow(k#+1,x)\<inverse>" by auto
  ultimately show ?thesis by (rule ind_on_nat1)
qed

text\<open>The natural power of $x$ multiplied by the same power of $x^{-1}$ cancel out to give
  the neutral element of the group.\<close>

corollary (in group0) nat_pow_inv_cancel: assumes "n\<in>nat" "x\<in>G"
  shows "pow(n,x)\<cdot>pow(n,x\<inverse>) = \<one>" "pow(n,x\<inverse>)\<cdot>pow(n,x) = \<one>"
  using nat_pow_inverse assms group0_2_L6 monoid.nat_mult_type assms by auto


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
    using nat_pow_inv_cancel(1) group0_2_L2 by simp 
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
    using nat_pow_inv_cancel(2) group0_2_L2 by simp  
qed

text\<open>If $k\leq n$ are natural numbers and $x$ an element of the group, then
  $(x^{-1})^k\cdot x^n = x^{(k-n)}$. \<close>

lemma (in group0) nat_pow_cancel_more1: assumes "n\<in>nat" "k\<le>n" "x\<in>G"
  shows "pow(k,x)\<cdot>pow(n,x\<inverse>) = pow(n #- k,x\<inverse>)"
proof -
  from assms have "pow(k,(x\<inverse>)\<inverse>)\<cdot>pow(n,x\<inverse>) = pow(n #- k,x\<inverse>)"
    using inverse_in_group nat_pow_cancel_more by simp
  with assms(3) show ?thesis using group_inv_of_inv by simp
qed

text\<open>The power to a product is the power of the power.\<close>

lemma (in group0) nat_pow_mult:
  assumes "z1\<in>nat" "z2\<in>nat" "g\<in>G"
  shows "pow(z1#*z2,g) = pow(z2,pow(z1,g))"
proof -
  have "z1#*0 = 0" by auto
  then have "pow(z1 #* 0,g) = pow(0,g)" by auto
  then have B:"pow(z1 #* 0,g) = pow(0,pow(z1,g))" by auto
  {
    fix x assume x:"x\<in>nat" "pow(z1 #* x,g) = pow(x,pow(z1,g))"
    have "z1 #* succ(x) = z1#+ (z1#*x)" using mult_succ_right by auto
    then have "pow(z1 #* succ(x),g) = pow(z1#+ (z1#*x),g)" by auto
    then have "pow(z1 #* succ(x),g) = pow(z1,g)\<cdot>pow(z1#*x,g)"
      using monoid.nat_mult_add assms(1) assms(3) by auto
    with x(2) have "pow(z1 #* succ(x),g) = pow(z1,g)\<cdot>pow(x,pow(z1,g))"
      by auto
    moreover have "domain(x \<times> {pow(z1,g)}) = x" by auto
    then have "Append(x \<times> {pow(z1,g)}, pow(z1,g)) = succ(x) \<times> {pow(z1,g)}"
      unfolding Append_def by auto
    then have "Fold(P,\<one>,Append(x \<times> {pow(z1,g)}, pow(z1,g))) = Fold(P,\<one>,succ(x) \<times> {pow(z1,g)})"
      by auto moreover
    have "pow(succ(x),pow(z1,g)) = Fold(P,\<one>,succ(x) \<times> {pow(z1,g)})" using
      group_nat_pow_def_alt(2) by blast
    ultimately have A:"Fold(P,\<one>,Append(x \<times> {pow(z1,g)}, pow(z1,g))) = pow(succ(x),pow(z1,g))"
        by auto
    have zg:"pow(z1,g)\<in>G" using assms(1,3) monoid.nat_mult_type by auto 
    then have f:"x\<times>{pow(z1,g)}:x\<rightarrow>G" unfolding Pi_def function_def by auto
    from fold_append(2) x(1) group_oper_fun f zg
    have "Fold(P,\<one>,Append(x \<times> {pow(z1,g)}, pow(z1,g))) = 
      pow(x,pow(z1,g))\<cdot>pow(z1,g)" using group0_2_L2 group_nat_pow_def_alt(2) groper_def by simp
    with A have "pow(succ(x),pow(z1,g)) = pow(x,pow(z1,g))\<cdot>pow(z1,g)" by auto
    with x(2) have "pow(succ(x),pow(z1,g)) = pow(z1 #* x,g)\<cdot>pow(z1,g)" by auto
    then have "pow(succ(x),pow(z1,g)) = pow((z1 #* x) #+ z1,g)"
      using monoid.nat_mult_add assms(1,3) by auto
    then have "pow(succ(x),pow(z1,g)) = pow(z1 #+(z1 #* x),g)" 
      using add_commute by auto
    then have "pow(z1#* succ(x), g) = pow(succ(x),pow(z1,g))"
      using mult_succ_right by auto
  }
  then have "\<And>x. x\<in>nat \<Longrightarrow> pow(z1 #* x, g) = pow(x,pow(z1,g)) \<Longrightarrow> pow(z1 #* succ(x), g) = pow(succ(x),pow(z1,g))"
    by auto
  with assms(2) B show ?thesis by (rule nat_induct)
qed

subsection\<open>Integer powers\<close>

text\<open>In this section we introduce notation basic properties of integer power in group context.
  The goal is to show that the power homomorphism property: if $x$ is an element of the group
  and $n,m$ are integers then $x^{n+m}=x^n\cdot x^m$. \<close>

text\<open>We extend the \<open>group0\<close> context with some notation from \<open>int0\<close> context.
  Since we inherit the multiplicative notation from the \<open>group0\<close> context
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
  
  fixes imul (infixl "\<cdot>\<^sub>Z" 69)
  defines imul_def [simp]: "a\<cdot>\<^sub>Zb \<equiv> IntegerMultiplication`\<langle>a,b\<rangle>"

  fixes setneg ("\<sm> _" 72)
  defines setneg_def [simp]: "\<sm>A \<equiv> GroupInv(\<int>,IntegerAddition)``(A)"

  fixes izero ("\<zero>")
  defines izero_def [simp]: "\<zero> \<equiv> TheNeutralElement(\<int>,IntegerAddition)"

  fixes ione ("\<one>\<^sub>Z")
  defines ione_def [simp]: "\<one>\<^sub>Z \<equiv> TheNeutralElement(\<int>,IntegerMultiplication)"
  
  fixes itwo ("\<two>")
  defines itwo_def [simp]: "\<two> \<equiv> \<one>\<^sub>Z\<ra>\<one>\<^sub>Z"
 
  fixes ithree ("\<three>")
  defines ithree_def [simp]: "\<three> \<equiv> \<two>\<ra>\<one>\<^sub>Z"
  
  fixes nonnegative ("\<int>\<^sup>+")
  defines nonnegative_def [simp]: 
  "\<int>\<^sup>+ \<equiv> Nonnegative(\<int>,IntegerAddition,IntegerOrder)"

  fixes positive ("\<int>\<^sub>+")
  defines positive_def [simp]: 
  "\<int>\<^sub>+ \<equiv> PositiveSet(\<int>,IntegerAddition,IntegerOrder)"

  fixes abs 
  defines abs_def [simp]: 
  "abs(m) \<equiv> AbsoluteValue(\<int>,IntegerAddition,IntegerOrder)`(m)"

  fixes lesseq (infix "\<lsq>" 60)
  defines lesseq_def [simp]: "m \<lsq> n \<equiv> \<langle>m,n\<rangle> \<in> IntegerOrder"

  fixes sless (infix "\<ls>" 68)
  defines sless_def [simp]: "a \<ls> b \<equiv> a\<lsq>b \<and> a\<noteq>b"

  fixes interval (infix ".." 70)
  defines interval_def [simp]: "m..n \<equiv> Interval(IntegerOrder,m,n)"

  fixes maxf
  defines maxf_def [simp]: "maxf(f,A) \<equiv> Maximum(IntegerOrder,f``(A))"

  fixes minf
  defines minf_def [simp]: "minf(f,A) \<equiv> Minimum(IntegerOrder,f``(A))"

  fixes oddext ("_ \<degree>")
  defines oddext_def [simp]: "f\<degree> \<equiv> OddExtension(\<int>,IntegerAddition,IntegerOrder,f)"


text\<open>Next define notation for the integer power \<open>powz(z,x)\<close>. 
  The difficulty here is that in ZF set theory nonnegative integers and natural numbers are 
  different things. So, we use the notion of \<open>zmagnitude\<close> defined in the standard Isabelle/ZF 
  \<open>Int\<close> theory. For an integer number $z$, \<open>zmagnitude(z)\<close> is like absolute value of $z$ 
  but interpreted as a natural number. 
  Hence, we define the integer power \<open>powz(z,x)\<close> as $x$ raised to the magnitude of $z$ if $z$ is 
  nonnegative or $x^{-1}$ raised to the same natural power otherwise.\<close>

definition (in group_int0) powz where
  "powz(z,x) \<equiv> pow(zmagnitude(z),if \<zero>\<lsq>z then x else x\<inverse>)"

text\<open>We bring in all the results about integers in \<open>int0\<close> with the notation included in \<open>group_int0\<close>.\<close>

sublocale group_int0 < ints:int0 "\<int>" ia iminus isub imul setneg izero ione itwo 
  ithree nonnegative positive abs lesseq sless interval maxf minf oddext
by auto

text\<open>An integer power of a group element is in the group.\<close>

lemma (in group_int0) powz_type: assumes "z\<in>\<int>" "x\<in>G" shows "powz(z,x) \<in> G"
  using assms zmagnitude_type monoid.nat_mult_type inverse_in_group 
  unfolding powz_def by simp

text\<open>A group element raised to (integer) zero'th power is equal to the group's neutral element. 
  An element raised to (integer) power one is the same element. \<close>

lemma (in group_int0) int_power_zero_one: assumes "x\<in>G"
  shows "powz(\<zero>,x) = \<one>" and "powz(\<one>\<^sub>Z,x) = x"
  using assms ints.Int_ZF_1_L8A(1) ints.int_ord_is_refl1 ints.zmag_zero_one 
    monoid.nat_mult_zero ints.Int_ZF_2_L16A(1) monoid.nat_mult_one 
    unfolding powz_def by auto

text\<open>The neutral raised to any (integer) power is equal to the group's neutral element.\<close>

lemma (in group_int0) int_power_neutral: assumes "z\<in>\<int>"
  shows "powz(z,\<one>) = \<one>"
  using monoid.nat_mult_neutral group_inv_of_one zmagnitude_type
    unfolding powz_def by auto

text\<open>If $x$ is an element of the group and $z_1,z_2$ are nonnegative integers then
  $x^{z_1+z_2}=x^{z_1}\cdot x^{z_2}$, i.e. the power homomorphism property holds.\<close>

lemma (in group_int0) powz_hom_nneg_nneg: assumes "\<zero>\<lsq>z\<^sub>1" "\<zero>\<lsq>z\<^sub>2" "x\<in>G"
  shows "powz(z\<^sub>1\<ra>z\<^sub>2,x) = powz(z\<^sub>1,x)\<cdot>powz(z\<^sub>2,x)"
  using assms ints.add_nonneg_ints(1,2) monoid.nat_mult_add 
  unfolding powz_def by simp

text\<open>If $x$ is an element of the group and $z_1,z_2$ are negative integers then
  the power homomorphism property holds.\<close>

lemma (in group_int0) powz_hom_neg_neg: 
  assumes "z\<^sub>1\<ls>\<zero>" "z\<^sub>2\<ls>\<zero>" "x\<in>G"
  shows "powz(z\<^sub>1\<ra>z\<^sub>2,x) = powz(z\<^sub>1,x)\<cdot>powz(z\<^sub>2,x)"
  using assms ints.neg_not_nonneg ints.add_neg_ints(1,2) 
    inverse_in_group monoid.nat_mult_add 
  unfolding powz_def by simp

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
    using ints.add_nonneg_neg1(1) unfolding powz_def by simp
  also from assms(1,2,3) have "... =  pow(?m\<^sub>1 #- ?m\<^sub>2,x)" 
    using ints.add_nonneg_neg1(2) by simp
  also from assms(3,4) have "... = pow(?m\<^sub>1,x)\<cdot>pow(?m\<^sub>2,x\<inverse>)"
    using nat_pow_cancel_less by simp
  also from assms(1,2) have "... = powz(z\<^sub>1,x)\<cdot>powz(z\<^sub>2,x)" 
    using ints.neg_not_nonneg unfolding powz_def by simp
  finally show ?thesis by simp
qed

text\<open>If $x$ is an element of the group and $z_1$ is nonnegative, 
  $z_2$ is negative and $|z_1|<|z_2|$ then the power homomorphism property holds.\<close>

lemma (in group_int0) powz_hom_nneg_neg2:
  assumes "\<zero>\<lsq>z\<^sub>1"  "z\<^sub>2\<ls>\<zero>"  "zmagnitude(z\<^sub>1) < zmagnitude(z\<^sub>2)" "x\<in>G"
  shows "powz(z\<^sub>1\<ra>z\<^sub>2,x) = powz(z\<^sub>1,x)\<cdot>powz(z\<^sub>2,x)"
  using assms ints.add_nonneg_neg2 ints.neg_not_nonneg leI nat_pow_cancel_more1
  unfolding powz_def by simp

text\<open>If $x$ is an element of the group and $z_1$ is negative, 
  $z_2$ is nonnegative and $|z_1|\leq |z_2|$ then the power homomorphism property holds.\<close>

lemma (in group_int0) powz_hom_neg_nneg1:
  assumes "z\<^sub>1\<ls>\<zero>" "\<zero>\<lsq>z\<^sub>2" "zmagnitude(z\<^sub>1) \<le> zmagnitude(z\<^sub>2)" "x\<in>G"
  shows "powz(z\<^sub>1\<ra>z\<^sub>2,x) = powz(z\<^sub>1,x)\<cdot>powz(z\<^sub>2,x)"
  using assms ints.add_neg_nonneg1 nat_pow_cancel_more ints.neg_not_nonneg
  unfolding powz_def by simp

text\<open>If $x$ is an element of the group and $z_1$ is negative, 
  $z_2$ is nonnegative and $|z_2| < |z_1|$ then the power homomorphism property holds.\<close>

lemma (in group_int0) powz_hom_neg_nneg2:
  assumes "z\<^sub>1\<ls>\<zero>" "\<zero>\<lsq>z\<^sub>2" "zmagnitude(z\<^sub>2) < zmagnitude(z\<^sub>1)" "x\<in>G"
  shows "powz(z\<^sub>1\<ra>z\<^sub>2,x) = powz(z\<^sub>1,x)\<cdot>powz(z\<^sub>2,x)"
  using assms ints.add_neg_nonneg2 ints.neg_not_nonneg leI nat_pow_cancel_less1
  unfolding powz_def by simp

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
    using ints.int_pair_6cases by simp
  with assms(3) show ?thesis 
    using powz_hom_nneg_nneg powz_hom_neg_neg 
    powz_hom_nneg_neg1 powz_hom_nneg_neg2 
    powz_hom_neg_nneg1 powz_hom_neg_nneg2
    by blast
qed

text\<open>If $x$ is an element of the group and $z_1,z_2$ are nonnegative integers then
  $x^{z_1 z_2}=(x^{z_2})^{z_2}$.\<close>

lemma (in group_int0) powz_mult: assumes "z\<^sub>1\<in>\<int>" "z\<^sub>2\<in>\<int>" "x\<in>G"
  shows "powz(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2,x) = powz(z\<^sub>2,powz(z\<^sub>1,x))"
proof -
  from assms have
    A: "powz(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2,x) = pow(zmagnitude(z\<^sub>2),pow(zmagnitude(z\<^sub>1),if \<zero>\<lsq>(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2) then x else x\<inverse>))"
    using ints.zmagnitud_mult nat_pow_mult zmagnitude_type inverse_in_group
    unfolding powz_def by auto
  { assume C: "\<zero>\<lsq>z\<^sub>1"
    with assms(1,2) have L: "\<zero>\<lsq>z\<^sub>2 \<longrightarrow> \<zero>\<lsq>(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2)" using ints.Int_ZF_1_3_L2
      by auto
    { assume P: "\<not>(\<zero>\<lsq>z\<^sub>2)"  
      with assms(2) have Q: "z\<^sub>2\<ls>\<zero>" using ints.Int_ZF_2_L19(4) ints.int_zero_one_are_int(1) 
        by auto
      with assms(1,2) C have U: "(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2)\<lsq>\<zero>"
        using ints.Int_ZF_1_3_L12 ints.Int_ZF_1_1_L5(5) by force
      { assume D: "(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2) = \<zero>"
        with assms(1,2) Q have "z\<^sub>1 = \<zero>" using ints.int_has_no_zero_divs
          unfolding HasNoZeroDivs_def ints_def sless_def by auto
        with assms D have "powz(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2,x) = powz(z\<^sub>2,powz(z\<^sub>1,x))"
          using int_power_zero_one(1) int_power_neutral by simp
      } moreover
      { assume D: "z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2 \<noteq> \<zero>"
        with assms(3) A C P U have "powz(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2,x) = powz(z\<^sub>2,powz(z\<^sub>1,x))"
          unfolding powz_def using ints.neg_not_nonneg nat_pow_inverse zmagnitude_type 
          by auto
      }
      ultimately have "powz(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2,x) = powz(z\<^sub>2,powz(z\<^sub>1,x))" by blast
    } moreover
    { assume P: "\<zero>\<lsq>z\<^sub>2"
      with A C L P have "powz(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2,x) = powz(z\<^sub>2,powz(z\<^sub>1,x))"
        unfolding powz_def by auto
    } ultimately have "powz(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2,x) = powz(z\<^sub>2,powz(z\<^sub>1,x))" by auto
  } moreover
  { assume C: "\<not>(\<zero>\<lsq>z\<^sub>1)"
    with assms(1) have Q: "z\<^sub>1\<ls>\<zero>" 
      using ints.Int_ZF_2_L19(4) ints.int_zero_one_are_int(1)
        by auto
    then have L: "\<zero>\<lsq>z\<^sub>2 \<longrightarrow> (z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2)\<lsq>\<zero>" using ints.Int_ZF_1_3_L12
      by auto
    { assume D: "(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2) = \<zero>"
      with assms(1,2) Q have Z: "z\<^sub>2 = \<zero>" using ints.int_has_no_zero_divs 
        unfolding HasNoZeroDivs_def ints_def by auto 
      with assms(3) D have "powz(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2,x) = \<one>" using int_power_zero_one(1) by auto
      with assms(1,3) Z have "powz(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2,x) = powz(z\<^sub>2,powz(z\<^sub>1,x))"
        using int_power_zero_one(1) powz_type by simp  
    } moreover
    { assume D: "(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2) \<noteq> \<zero>"
      with L have L1: "\<zero>\<lsq>z\<^sub>2 \<longrightarrow> \<not>(\<zero>\<lsq>(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2))" using ints.ls_not_leq by auto
      from Q have "\<not>(\<zero>\<lsq>z\<^sub>1)" using ints.ls_not_leq by auto
      then have S: "powz(z\<^sub>1,x) = pow(zmagnitude(z\<^sub>1),x\<inverse>)" unfolding powz_def by auto
      { assume "\<zero>\<lsq>z\<^sub>2"
        with A L1 S have "powz(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2,x) = powz(z\<^sub>2,powz(z\<^sub>1,x))" unfolding powz_def 
          by auto
      } moreover
      { assume E: "\<not>(\<zero>\<lsq>z\<^sub>2)"
        with assms S have 
          B: "powz(z\<^sub>2, powz(z\<^sub>1,x)) = pow(zmagnitude(z\<^sub>2), pow(zmagnitude(z\<^sub>1),x))"
          unfolding powz_def
          using nat_pow_inverse zmagnitude_type group_inv_of_inv 
            zmagnitude_type monoid.nat_mult_type by simp
        from assms(1,2) C E have "\<zero>\<lsq>((\<rm>z\<^sub>1)\<cdot>\<^sub>Z(\<rm>z\<^sub>2))"
          using ints.Int_ZF_2_L19A(2) ints.Int_ZF_1_3_L2 ints.Int_ZF_1_1_L4(7)
          by simp
        with assms(1,2) A B have "powz(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2,x) = powz(z\<^sub>2, powz(z\<^sub>1,x))"
          using ints.Int_ZF_1_1_L5(11) by simp
      }
      ultimately have "powz(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2,x) = powz(z\<^sub>2, powz(z\<^sub>1,x))" by auto
    }
    ultimately have "powz(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2,x) = powz(z\<^sub>2, powz(z\<^sub>1,x))" by blast
  } 
  ultimately show "powz(z\<^sub>1\<cdot>\<^sub>Zz\<^sub>2,x) = powz(z\<^sub>2, powz(z\<^sub>1,x))" by auto
qed


text\<open>A group element raised to power $-1$ is the inverse of that group element.\<close>

lemma (in group_int0) inpt_power_neg_one: assumes "x\<in>G"
  shows "powz(\<rm>\<one>\<^sub>Z,x) = x\<inverse>"
  using assms ints.neg_not_nonneg ints.neg_one_less_zero ints.zmag_opposite_same(2) 
    ints.Int_ZF_1_L8A(2) ints.zmag_zero_one(2) inverse_in_group monoid.nat_mult_one 
  unfolding powz_def by simp

text\<open>Increasing the (integer) power by one is the same as multiplying by the group element.\<close>

lemma (in group_int0) int_power_add_one: assumes "z\<in>\<int>" "x\<in>G"
  shows "powz(z\<ra>\<one>\<^sub>Z,x) = powz(z,x)\<cdot>x"
  using assms ints.Int_ZF_1_L8A(2) powz_hom_prop int_power_zero_one(2)
  by simp

text\<open>For integer power taking a negative of the exponent is the same as taking inverse of the 
  group element. \<close>

lemma (in group_int0) minus_exp_inv_base: assumes "z\<in>\<int>" "x\<in>G"
  shows "powz(\<rm>z,x) = powz(z,x\<inverse>)"
proof -
  from assms(1) have "\<zero>\<ls>z \<or> z=\<zero> \<or> z\<ls>\<zero>"
    using ints.int_neg_zero_pos by simp
  moreover from assms(1) have "\<zero>\<ls>z \<longrightarrow> powz(\<rm>z,x) = powz(z,x\<inverse>)"
    using ints.neg_pos_int_neg ints.neg_not_nonneg ints.zmag_opposite_same(2) 
    unfolding powz_def by simp
  moreover from assms(2) have "z=\<zero> \<longrightarrow> powz(\<rm>z,x) = powz(z,x\<inverse>)"
    using ints.Int_ZF_1_L11 int_power_zero_one(1) inverse_in_group by simp
  moreover from assms have "z\<ls>\<zero> \<longrightarrow> powz(\<rm>z,x) = powz(z,x\<inverse>)"
    using ints.neg_not_nonneg ints.neg_neg_int_pos group_inv_of_inv 
    ints.zmag_opposite_same(2) unfolding powz_def by simp
  ultimately show "powz(\<rm>z,x) = powz(z,x\<inverse>)" by auto
qed

text\<open>Integer power of a group element is the same as the inverse of the element
  raised to negative of the exponent. \<close>

lemma (in group_int0) minus_exp_inv_base1: assumes "z\<in>\<int>" "x\<in>G"
  shows "powz(z,x) = powz(\<rm>z,x\<inverse>)"
proof -
  from assms(1) have "(\<rm>z)\<in>\<int>" using ints.int_neg_type by simp
  with assms show ?thesis using minus_exp_inv_base ints.neg_neg_noop
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
  let ?A\<^sub>Z = "IntegerAddition"
  let ?M\<^sub>Z = "IntegerMultiplication"
  let ?O\<^sub>Z = "IntegerOrder"
  from assms have "\<langle>\<zero>,k\<rangle> \<in> ?O\<^sub>Z" and "powz(\<zero>,x\<cdot>y) = powz(\<zero>,x)\<cdot>powz(\<zero>,y)"
    using group_op_closed int_power_zero_one(1) group0_2_L2 by simp_all
  moreover
  { fix m assume "\<zero>\<lsq>m" and I: "powz(m,x\<cdot>y) = powz(m,x)\<cdot>powz(m,y)"
    from assms(2,3) \<open>\<zero>\<lsq>m\<close> have  "m\<in>\<int>" and "x\<cdot>y \<in> G"  
      using ints.Int_ZF_2_L1A(3) group_op_closed by simp_all
    with isAbelian assms(2,3) I have "powz(m\<ra>\<one>\<^sub>Z,x\<cdot>y) = powz(m\<ra>\<one>\<^sub>Z,x)\<cdot>powz(m\<ra>\<one>\<^sub>Z,y)"
      using int_power_add_one group0_4_L8(3) powz_type by simp
  } hence "\<forall>m. \<zero>\<lsq>m \<and> powz(m,x\<cdot>y) = powz(m,x)\<cdot>powz(m,y) \<longrightarrow>
     powz(m\<ra>\<one>\<^sub>Z,x\<cdot>y) = powz(m\<ra>\<one>\<^sub>Z,x)\<cdot>powz(m\<ra>\<one>\<^sub>Z,y)" by simp
  hence "\<forall>m. \<langle>\<zero>, m\<rangle> \<in> ?O\<^sub>Z \<and> powz(m,x\<cdot>y) = powz(m,x)\<cdot>powz(m,y) \<longrightarrow> 
    powz(?A\<^sub>Z`(\<langle>m,TheNeutralElement(int,?M\<^sub>Z)\<rangle>),x\<cdot>y) = 
    powz(?A\<^sub>Z`(\<langle>m,TheNeutralElement(int,?M\<^sub>Z)\<rangle>),x)\<cdot>powz(?A\<^sub>Z`(\<langle>m,TheNeutralElement(int,?M\<^sub>Z)\<rangle>),y)"
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
    using ints.Int_ZF_2_L1A(2) group_op_closed minus_exp_inv_base1 group_inv_of_two
    unfolding IsCommutative_def by simp
  with assms show ?thesis
    using ints.Int_ZF_2_L10A inverse_in_group powz_groupop_commute0 
      ints.Int_ZF_2_L1A(2) minus_exp_inv_base1 by simp
qed

text\<open>In abelian groups taking an integer power commutes with the group operation.\<close>

theorem (in abgroup_int0) powz_groupop_commute: assumes "z\<in>\<int>" "x\<in>G" "y\<in>G"
  shows "powz(z,x\<cdot>y) = powz(z,x)\<cdot>powz(z,y)"
proof -
  from assms(1) have "\<zero>\<lsq>z \<or> z\<lsq>\<zero>" using ints.int_nonneg_or_nonpos
    by auto
  with assms(2,3) show ?thesis using powz_groupop_commute0 powz_groupop_commute1
    by blast
qed

text\<open>For any integer $n$ the mapping $x\mapsto x^n$ maps $G$ into $G$ and is a homomorphism  
  hence an endomorphism of $(G,P)$.\<close>

theorem (in abgroup_int0) powz_end: assumes "n\<in>\<int>"
  defines "h \<equiv> {\<langle>x,powz(n,x)\<rangle>. x\<in>G}"
  shows "h:G\<rightarrow>G" "Homomor(h,G,P,G,P)" "h \<in> End(G,P)"
proof -
  from assms show "h:G\<rightarrow>G" using powz_type ZF_fun_from_total by simp 
  with assms have "IsMorphism(G,P,P,h)"
    using ZF_fun_from_tot_val(1) group_op_closed powz_groupop_commute
    unfolding IsMorphism_def by simp
  with \<open>h:G\<rightarrow>G\<close> show "Homomor(h,G,P,G,P)" and "h \<in> End(G,P)"
    unfolding Homomor_def End_def by simp_all
qed

text\<open>The mapping $\mathbb{Z}\ni n\mapsto (x\mapsto x^n\in G)$ maps integers
  to endomorphisms of $(G,P)$.\<close>

theorem (in abgroup_int0) powz_maps_int_End: 
  shows "{\<langle>n,{\<langle>x,powz(n,x)\<rangle>. x\<in>G}\<rangle>. n\<in>\<int>} : \<int>\<rightarrow>End(G,P)"
  using powz_end(3) ZF_fun_from_total by simp

end