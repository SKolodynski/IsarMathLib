(*
This file is a part of IsarMathLib - 
a library of formalized mathematics for Isabelle/Isar.

Copyright (C) 2008  Slawomir Kolodynski

This program is free software; Redistribution and use in source and binary forms, 
with or without modification, are permitted provided that the 
following conditions are met:

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

section \<open>Functions with finite support\<close>

theory FinSupp_ZF imports Finite_ZF Group_ZF_2

begin

text\<open>Functions with finite support are those functions 
  valued in a monoid that are equal to the neutral element everywhere except
  a finite number of points. They form a submonoid of the space of all
  functions valued in the monoid with the natural pointwise operation 
  (or a subgroup if functions are valued in a group).
  Polynomials can be viewed as ring valued sequences that have
  finite support.\<close>

subsection\<open>Functions with finite support\<close>

text\<open>In this section we provide the definition and set up notation for 
  formalizing the notion of finitely supported functions.\<close>

text\<open>Support of a function is the subset of its domain where the values 
  are not zero.\<close>

definition
  "Supp(f,G,A) \<equiv> {x \<in> domain(f). f`(x) \<noteq> TheNeutralElement(G,A)}"

text\<open>A finitely supported function is such that its support 
  is in the finite powerset of its domain.\<close>

definition
  "FinSupp(X,G,A) \<equiv> {f \<in> X\<rightarrow>G. Supp(f,G,A) \<in> FinPow(X)}"

text\<open>We will use the additive notation writing about finitely 
  supported functions. In the \<open>finsupp\<close> context defined below 
  we assume that $(M,A)$ is a monoid and $X$ is some arbitrary
  set. We denote \<open>\<A>\<close> to be the pointwise operation
  on $M$-valued functions on $X$ corresponding to the monoid 
  operation $A$, (denoted as \<open>\<ra>\<close>). \<open>\<zero>\<close>
  is the neutral element of the monoid.\<close>

locale finsupp =
  fixes M A
  assumes monoidAsssum: "IsAmonoid(M,A)"

  fixes monoper (infixl "\<ra>" 70)
  defines monoper_def[simp]: "a \<ra> b \<equiv> A`\<langle>a,b\<rangle>"

  fixes X

  fixes finsupp ("\<M>")
  defines finsupp_def[simp]: "\<M> \<equiv> FinSupp(X,M,A)"

  fixes pointewiseoper ("\<A>")
  defines pointewiseoper_def[simp]: 
  "\<A> \<equiv> A {lifted to function space over} X"

  fixes funoper (infixl "\<oplus>" 70)
  defines funoper_def[simp]: "a \<oplus> b \<equiv> \<A>`\<langle>a,b\<rangle>"

  fixes neut ("\<zero>")
  defines neut_def[simp]: "\<zero> \<equiv> TheNeutralElement(M,A)"

  fixes supp
  defines supp_def[simp]: "supp(f) \<equiv> Supp(f,M,A)"

text\<open>We can use theorems proven in the \<open>monoid0\<close> context.\<close>

lemma (in finsupp) monoid0_valid: shows "monoid0(M,A)"
  using monoidAsssum monoid0_def by simp

subsection\<open>Finitely supported functions valued in a monoid\<close>

text\<open>We show in \<open>Group_ZF_2\<close> that if 
  $(M,A)$ is a monoid, and $X$ is
  an arbitrary set, then the space of functions 
  $X\rightarrow M$ with the natural pointwise
  operation is also a monoid.
  In this section we show that the set of
  finitely supported funtions is a a sub-monoid of that monoid.
\<close>

text\<open>The sum of monoid valued functions is a monoid valued function.\<close>

lemma (in finsupp) lifted_op_closed: 
  assumes "f:X \<rightarrow>M"  "g:X \<rightarrow>M" 
  shows "f\<oplus>g : X\<rightarrow>M"
proof -
  have "\<A> : (X\<rightarrow>M)\<times>(X\<rightarrow>M)\<rightarrow>(X\<rightarrow>M)"
    using monoid0_valid monoid0.Group_ZF_2_1_L0A
    by simp
  with assms show "f\<oplus>g : X\<rightarrow>M" by simp
qed

text\<open>What is the value of a sum of monoid-valued functions?\<close>

lemma (in finsupp) finsupp_sum_val: 
  assumes "f:X \<rightarrow>M"  "g:X \<rightarrow>M" and "x \<in> X"
  shows "(f\<oplus>g)`(x) = f`(x) \<ra> g`(x)"
  using assms monoid0_valid monoid0.lifted_val
  by simp  

text\<open>The support of the sum of functions is contained in the union of
  supports.\<close>

lemma (in finsupp) supp_sum_union: assumes "f:X \<rightarrow>M"  "g:X \<rightarrow>M"
  shows "supp(f\<oplus>g) \<subseteq> supp(f) \<union> supp(g)"
proof -
  { fix x assume "x \<in> supp(f\<oplus>g)"
    from assms have  "f\<oplus>g : X\<rightarrow>M" using lifted_op_closed
      by simp
    with assms \<open>x \<in> supp(f\<oplus>g)\<close> have  
      "x\<in>X" and "f`(x) \<ra> g`(x) \<noteq> \<zero>"
      using func1_1_L1 Supp_def finsupp_sum_val by auto
    with assms have "x \<in> (supp(f) \<union> supp(g))"
      using monoid0_valid monoid0.sum_nonzero_elmnt_nonzero
	func1_1_L1 Supp_def by simp
  } thus ?thesis by auto
qed

text\<open>The sum of finitely supported functions is 
  finitely supported.\<close>

lemma (in finsupp) sum_finsupp: 
  assumes "f \<in> \<M>"  "g \<in> \<M>"
  shows "f\<oplus>g \<in>\<M> "
proof -
  from assms have 
    I: "f: X\<rightarrow>M"  "g: X\<rightarrow>M" and
    "supp(f) \<in> FinPow(X)" "supp(g) \<in> FinPow(X)"
    using FinSupp_def by auto
  then have
    "supp(f) \<union> supp(g) \<in>  FinPow(X)" and
    "supp(f\<oplus>g) \<subseteq> supp(f) \<union> supp(g)"
    using union_finpow supp_sum_union by auto
  then have "supp(f\<oplus>g) \<in>  FinPow(X)"
    by (rule subset_finpow)
  with I show "f\<oplus>g \<in> \<M>" 
    using lifted_op_closed FinSupp_def by simp
qed

text\<open>The neutral element of the lifted (pointwise) 
  operation is the function equal zero everywhere.
  In the next lemma we show that this is a finitely
  supported function.\<close>

lemma (in finsupp) const_zero_fin_supp:
  shows "TheNeutralElement(X\<rightarrow>M, \<A>) \<in> \<M>"
  using  monoidAsssum Group_ZF_2_1_L2 
    monoid0_valid monoid0.unit_is_neutral 
    func1_3_L1 func1_3_L2 func1_1_L1 
    Supp_def empty_in_finpow FinSupp_def
  by simp

text\<open>Finitely supported functions form a submonoid
  of all functions with pointwise operation.\<close>

theorem (in finsupp) fin_supp_monoid:
  shows "IsAmonoid(\<M>,restrict(\<A>,\<M>\<times>\<M>))"
proof -
  have "monoid0(X\<rightarrow>M,\<A>)"
    using monoid0_valid monoid0.Group_ZF_2_1_T1
      monoid0_def by simp
  moreover have 
    "\<M> {is closed under} \<A>"
    "\<M> \<subseteq> (X\<rightarrow>M)"
    "TheNeutralElement(X\<rightarrow>M, \<A>) \<in> \<M>"
    using sum_finsupp IsOpClosed_def FinSupp_def
      const_zero_fin_supp by auto
  ultimately show ?thesis
    using monoid0.group0_1_T1 by simp
qed
  
subsection\<open>Group valued finitely supported functions\<close>

text\<open>Similarly as in the monoid case the group valued
  finitely supported functions form a subgroup
  of all functions valued in that group.\<close>

text\<open>We will reuse the notation defined in the 
  \<open>finsupp\<close> context, just adding an assumption
  about that the existence of the right inverse with
  a notation for it.\<close>

locale finsupp1 = finsupp + 
  assumes rinverse: "\<forall>x\<in>M. \<exists>y\<in>M. x \<ra> y = \<zero>"

  fixes inv ("\<rm> _" 89)
  defines inv_def[simp]: "(\<rm>a) \<equiv> GroupInv(M,A)`(a)"

text\<open>With this additional assumption $(M,A)$ becomes a group
  and we can use theorems proven in ine \<open>group0\<close> context.\<close>

lemma (in finsupp1) group0_valid: shows 
  "IsAgroup(M,A)" and "group0(M,A)"
  using monoidAsssum rinverse  
    IsAgroup_def group0_def by auto

text\<open>Recall from \<open>Group_ZF_2\<close> that the function space 
  of $G$ valued functions is also a group.\<close>

lemma (in finsupp1) fungroup0_valid: shows
  "IsAgroup(X\<rightarrow>M,\<A>)" and "group0(X\<rightarrow>M,\<A>)"
  using group0_valid group0.Group_ZF_2_1_T2
    group0_def by auto

text\<open>A function has the same support as its negative.\<close>

lemma (in finsupp1) finsupp_neg: assumes A1: "f: X\<rightarrow>M"
  shows "supp(f) = supp(GroupInv(X\<rightarrow>M,\<A>)`(f))"
proof -
  let ?g = "GroupInv(X\<rightarrow>M,\<A>)`(f)"
  from A1 have I: "?g : X\<rightarrow>M" 
    using fungroup0_valid group0.inverse_in_group 
    by simp
  have "supp(?g) \<subseteq> supp(f)"
  proof -
    { fix x assume "x \<in> supp(?g)"
      with I have "x\<in>X" and "?g`(x) \<noteq> \<zero>"
	using func1_1_L1 Supp_def by auto
      with A1 have "x \<in> supp(f)"
	using group0_valid group0.lift_gr_inv_val
	  group0.group0_2_L8C func1_1_L1 Supp_def
	by simp 
    } thus "supp(?g) \<subseteq> supp(f)" by auto
  qed
  moreover from A1 I have "supp(f) \<subseteq> supp(?g)"
    using func1_1_L1 Supp_def group0_valid 
      group0.group0_2_L8B group0.lift_gr_inv_val
    by auto 
  ultimately show ?thesis by auto
qed
	
text\<open>The negative of a function with a finite support
  is a function with a finite support.\<close>

lemma (in finsupp1) finsupp_neg_finsupp: assumes A1: "f \<in> \<M>"
  shows "GroupInv(X\<rightarrow>M,\<A>)`(f) \<in> \<M>"
proof -
  let ?g = "GroupInv(X\<rightarrow>M,\<A>)`(f)"
  from A1 have I: "f: X\<rightarrow>M"  "supp(f) \<in> FinPow(X)"
    using FinSupp_def func1_1_L1 by auto
  then have "?g \<in> X\<rightarrow>M" using 
    fungroup0_valid group0.inverse_in_group by simp
  moreover from I have "supp(?g) \<in> FinPow(X)"
    using finsupp_neg by simp
  ultimately show ?thesis using FinSupp_def
    by simp
qed

text\<open>Finitely supported functions form a subgroup
  with pointwise addition of group-valued functions.
\<close>

theorem (in finsupp1) fin_sup_group:
  shows "IsAsubgroup(\<M>,\<A>)"
proof -
  have 
    "\<M> \<noteq> 0" and
    "\<M> \<subseteq> X\<rightarrow>M" and
    "\<M> {is closed under} \<A>" and
    "\<forall>f\<in>\<M>. GroupInv(X\<rightarrow>M,\<A>)`(f) \<in> \<M>"
    using const_zero_fin_supp FinSupp_def
      sum_finsupp IsOpClosed_def finsupp_neg_finsupp
    by auto
  then show "IsAsubgroup(\<M>,\<A>)"
    using fungroup0_valid group0.group0_3_T3 
    by simp
qed

  
end

    
 
    
  
  
    

      









