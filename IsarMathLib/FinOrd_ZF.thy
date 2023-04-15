(*
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2008-2023  Slawomir Kolodynski

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

section \<open>Finite sets and order relations\<close>

theory FinOrd_ZF imports Finite_ZF func_ZF_1 NatOrder_ZF

begin

text\<open>This theory file contains properties of finite sets related to order 
  relations. Part of this is similar to what is done in \<open>Finite_ZF_1\<close>
  except that the development is based on the notion of finite powerset
  defined in \<open>Finite_ZF\<close> rather the one defined in standard
  Isabelle \<open>Finite\<close> theory.\<close>

subsection\<open>Finite vs. bounded sets\<close>

text\<open>The goal of this section is to show that finite sets are bounded and 
  have maxima and minima.\<close>

text\<open>For total and transitive relations 
  nonempty finite set has a maximum.\<close>

theorem fin_has_max: 
  assumes A1: "r {is total on} X" and A2: "trans(r)"
  and A3: "B \<in> FinPow(X)" and A4: "B \<noteq> 0"
  shows "HasAmaximum(r,B)"
proof -
  have "0=0 \<or> HasAmaximum(r,0)" by simp
  moreover have 
    "\<forall>A \<in> FinPow(X). A=0 \<or> HasAmaximum(r,A) \<longrightarrow>
    (\<forall>x\<in>X. (A \<union> {x}) = 0 \<or> HasAmaximum(r,A \<union> {x}))"
  proof -
    { fix A 
      assume "A \<in> FinPow(X)"  "A = 0 \<or> HasAmaximum(r,A)"
      have "\<forall>x\<in>X. (A \<union> {x}) = 0 \<or> HasAmaximum(r,A \<union> {x})"
      proof -
	{ fix x assume "x\<in>X"
	  note \<open>A = 0 \<or> HasAmaximum(r,A)\<close>
	  moreover
	  { assume "A = 0"
	    then have "A\<union>{x} = {x}" by simp
	    from A1 have "refl(X,r)" using total_is_refl 
	      by simp
	    with \<open>x\<in>X\<close> \<open>A\<union>{x} = {x}\<close> have "HasAmaximum(r,A\<union>{x})"
	      using Order_ZF_4_L8 by simp }
	  moreover
	  { assume "HasAmaximum(r,A)"
	    with A1 A2 \<open>A \<in> FinPow(X)\<close>  \<open>x\<in>X\<close> 
	    have "HasAmaximum(r,A\<union>{x})" 
	      using FinPow_def Order_ZF_4_L9 by simp }
	  ultimately  have "A \<union> {x} = 0 \<or> HasAmaximum(r,A \<union> {x})"
	    by auto
	} thus "\<forall>x\<in>X. (A \<union> {x}) = 0 \<or> HasAmaximum(r,A \<union> {x})"
	  by simp
      qed
    } thus ?thesis by simp
  qed
  moreover note A3
  ultimately have "B = 0 \<or>  HasAmaximum(r,B)"
    by (rule FinPow_induct)
  with A4 show "HasAmaximum(r,B)" by simp
qed

text\<open>For linearly ordered nonempty finite sets the 
  maximum is in the set and indeed it is the greatest
  element of the set.\<close>

lemma linord_max_props: assumes A1: "IsLinOrder(X,r)" and
  A2: "A \<in> FinPow(X)" "A \<noteq> 0"
  shows
  "Maximum(r,A) \<in> A"
  "Maximum(r,A) \<in> X"
  "\<forall>a\<in>A. \<langle>a,Maximum(r,A)\<rangle> \<in> r"
proof -
  from A1 A2 show 
    "Maximum(r,A) \<in> A" and "\<forall>a\<in>A. \<langle>a,Maximum(r,A)\<rangle> \<in> r"
    using IsLinOrder_def fin_has_max Order_ZF_4_L3
    by auto
  with A2 show "Maximum(r,A) \<in> X" using FinPow_def
    by auto
qed

text\<open>Every nonempty subset of a natural number has a maximum with expected properties.\<close>

lemma nat_max_props: assumes "n\<in>nat" "A\<subseteq>n" "A\<noteq>0"
  shows
  "Maximum(Le,A) \<in> A"
  "Maximum(Le,A) \<in> nat"
  "\<forall>k\<in>A. k \<le> Maximum(Le,A)"
proof -
  from assms(1,2) have "A \<in> FinPow(nat)" 
    using nat_finpow_nat subset_finpow by blast
  with assms(3) show 
    "Maximum(Le,A) \<in> A"
    "Maximum(Le,A) \<in> nat"
    using NatOrder_ZF_1_L2(4) linord_max_props(1,2) by simp_all
  from assms(3) \<open>A \<in> FinPow(nat)\<close> have "\<forall>k\<in>A. \<langle>k,Maximum(Le,A)\<rangle> \<in> Le"
    using linord_max_props NatOrder_ZF_1_L2(4) by blast
  then show  "\<forall>k\<in>A. k \<le> Maximum(Le,A)" by simp
qed

text\<open>Yet another version of induction where the induction step is valid only up to $n\in \mathbb{N}$
  rather than for all natural numbers.
  This lemma is redundant as it is easier to prove this assertion using lemma \<open>fin_nat_ind\<close> 
  from \<open>Nat_ZF_IML\<close> which was done in lemma \<open>fin_nat_ind1\<close> there. 
  It is left here for now as an alternative proof based on properties of the 
  maximum of a finite set. \<close>

lemma ind_on_nat2: 
  assumes "n\<in>nat" and "P(0)" and "\<forall>j\<in>n. P(j)\<longrightarrow>P(j #+ 1)"
  shows "\<forall>j\<in>n #+ 1. P(j)" and "P(n)"
proof -
  let ?A = "{k\<in>succ(n). \<forall>j\<in>succ(k). P(j)}"
  let ?M = "Maximum(Le,?A)" 
  from assms(1,2) have I: "succ(n) \<in> nat" "?A\<subseteq>succ(n)" "?A\<noteq>0" 
    using empty_in_every_succ by auto 
  then have "?M \<in> ?A" by (rule nat_max_props)
  have "n=?M"
  proof -
    from \<open>?M \<in> ?A\<close> have "?M \<in> succ(n)" by blast
    with assms(1) have "?M\<in>n \<or> ?M=n" by auto
    moreover
    { assume "?M \<in> n"
      from I have "?M \<in> nat" by (rule nat_max_props)
      from assms(3) \<open>?M\<in>?A\<close> \<open>?M\<in>n\<close> have "P(?M #+ 1)" by blast
      with \<open>?M \<in> nat\<close> have "P(succ(?M))" using succ_add_one(1) by simp
      with \<open>?M\<in>?A\<close> have "\<forall>j\<in>succ(succ(?M)). P(j)" by blast
      moreover from assms(1) \<open>?M \<in> n\<close> have "succ(?M) \<in> succ(n)"
        using succ_ineq1 by simp
      moreover from I have "\<forall>k\<in>?A. k \<le> ?M"
        by (rule nat_max_props)
      ultimately have False by blast
    }
    ultimately show "n=?M" by auto
  qed
  with \<open>?M \<in> ?A\<close> have "n\<in>?A" by (rule eq_mem)
  with assms(1) show "\<forall>j\<in>n #+ 1. P(j)" and "P(n)" 
    using succ_add_one(1) by simp_all
qed
  
subsection\<open>Order isomorphisms of finite sets\<close>

text\<open>In this section we establish that if two linearly 
  ordered finite sets have the same number of elements,
  then they are order-isomorphic and the isomorphism
  is unique. This allows us to talk about ''enumeration''
  of a linearly ordered finite set. We define the enumeration as 
  the order isomorphism between the number of elements
  of the set (which is a natural number $n = \{0,1,..,n-1\}$)
  and the set.\<close>

text\<open>A really weird corner case - empty set is order isomorphic with itself. \<close>

lemma empty_ord_iso: shows "ord_iso(0,r,0,R) \<noteq> 0"
proof -
  have "0 \<approx> 0" using eqpoll_refl by simp
  then obtain f where "f \<in> bij(0,0)"
    using eqpoll_def by blast
  then show ?thesis using ord_iso_def by auto
qed

text\<open>Even weirder than \<open>empty_ord_iso\<close>
  The order automorphism of the empty set is unique.\<close>

lemma empty_ord_iso_uniq: 
  assumes "f \<in> ord_iso(0,r,0,R)"  "g \<in> ord_iso(0,r,0,R)"
  shows "f = g"
proof -
  from assms have "f : 0 \<rightarrow> 0" and "g: 0 \<rightarrow> 0"
    using ord_iso_def bij_def surj_def by auto
    moreover have "\<forall>x\<in>0. f`(x) = g`(x)" by simp
    ultimately show "f = g" by (rule func_eq)
qed

text\<open>The empty set is the only order automorphism of itself.\<close>

lemma empty_ord_iso_empty: shows "ord_iso(0,r,0,R) = {0}"
proof -
  have "0 \<in> ord_iso(0,r,0,R)"
  proof -
    have "ord_iso(0,r,0,R) \<noteq> 0" by (rule empty_ord_iso)
    then obtain f where "f \<in> ord_iso(0,r,0,R)" by auto
    then show "0 \<in> ord_iso(0,r,0,R)" 
      using ord_iso_def bij_def surj_def fun_subset_prod
      by auto
  qed
  then show "ord_iso(0,r,0,R) = {0}" using empty_ord_iso_uniq
    by blast
qed

text\<open>An induction (or maybe recursion?) scheme for linearly ordered sets.
  The induction step is that we show that if the property holds
  when the set is a singleton or for a set with the maximum removed, 
  then it holds for the set. The idea is that since we can build
  any finite set by adding elements on the right, then if the property
  holds for the empty set and is invariant with respect to this operation, then
  it must hold for all finite sets.\<close>

lemma fin_ord_induction:  
  assumes A1: "IsLinOrder(X,r)" and A2: "P(0)" and
  A3: "\<forall>A \<in> FinPow(X). A \<noteq> 0 \<longrightarrow> (P(A - {Maximum(r,A)}) \<longrightarrow> P(A))"
  and A4: "B \<in> FinPow(X)" shows "P(B)"
proof -
  note A2
  moreover have "\<forall> A \<in> FinPow(X). A \<noteq> 0 \<longrightarrow> (\<exists>a\<in>A. P(A-{a}) \<longrightarrow> P(A))"
  proof -
    { fix A assume "A \<in>  FinPow(X)" and "A \<noteq> 0"
      with A1 A3 have "\<exists>a\<in>A. P(A-{a}) \<longrightarrow> P(A)"
	using IsLinOrder_def fin_has_max
	  IsLinOrder_def Order_ZF_4_L3
	by blast
    } thus ?thesis by simp
  qed
  moreover note A4
  ultimately show "P(B)" by (rule FinPow_ind_rem_one)
qed

text\<open>A sligltly more complicated version of \<open>fin_ord_induction\<close>
  that allows to prove properties that are not true for the empty set.\<close>

lemma fin_ord_ind:  
  assumes A1: "IsLinOrder(X,r)" and A2: "\<forall>A \<in> FinPow(X). 
  A = 0 \<or> (A = {Maximum(r,A)} \<or> P(A - {Maximum(r,A)}) \<longrightarrow> P(A))"
  and A3: "B \<in>  FinPow(X)" and A4: "B\<noteq>0"
  shows "P(B)"
proof -
  { fix A assume "A \<in>  FinPow(X)" and "A \<noteq> 0"
    with A1 A2 have
      "\<exists>a\<in>A. A = {a} \<or> P(A-{a}) \<longrightarrow> P(A)"
      using IsLinOrder_def fin_has_max
	IsLinOrder_def Order_ZF_4_L3
      by blast
  } then have "\<forall>A \<in> FinPow(X). 
      A = 0 \<or> (\<exists>a\<in>A. A = {a} \<or> P(A-{a}) \<longrightarrow> P(A))"
    by auto
  with A3 A4 show "P(B)" using  FinPow_rem_ind
    by simp
qed

text\<open>Yet another induction scheme. We build a linearly ordered
  set by adding elements that are greater than all elements in the
  set.\<close>

lemma fin_ind_add_max: 
  assumes A1: "IsLinOrder(X,r)" and A2: "P(0)" and A3: "\<forall> A \<in> FinPow(X). 
  ( \<forall> x \<in> X-A. P(A) \<and> (\<forall>a\<in>A. \<langle>a,x\<rangle> \<in> r ) \<longrightarrow> P(A \<union> {x}))"
  and A4: "B \<in> FinPow(X)"
  shows "P(B)"
proof -
  note A1 A2
  moreover have
    "\<forall>C \<in> FinPow(X). C \<noteq> 0 \<longrightarrow> (P(C - {Maximum(r,C)}) \<longrightarrow> P(C))"
    proof -
      { fix C assume "C \<in> FinPow(X)" and "C \<noteq> 0"
	let ?x = "Maximum(r,C)"
	let ?A = "C - {?x}"
	assume "P(?A)"
	moreover from \<open>C \<in> FinPow(X)\<close> have "?A \<in> FinPow(X)"
	  using fin_rem_point_fin by simp
	moreover from A1 \<open>C \<in> FinPow(X)\<close> \<open>C \<noteq> 0\<close> have 
	  "?x \<in> C" and "?x \<in> X - ?A" and "\<forall>a\<in>?A. \<langle>a,?x\<rangle> \<in> r"
	  using linord_max_props by auto
	moreover note A3
	ultimately have "P(?A \<union> {?x})" by auto
	moreover from \<open>?x \<in> C\<close> have "?A \<union> {?x} = C"
	  by auto
	ultimately have "P(C)" by simp
      } thus ?thesis by simp
    qed
    moreover note A4
  ultimately show "P(B)" by (rule fin_ord_induction)
qed

text\<open>The only order automorphism of a linearly ordered
  finite set is the identity.\<close>

theorem fin_ord_auto_id: assumes A1: "IsLinOrder(X,r)"
  and A2: "B \<in>  FinPow(X)" and A3: "B\<noteq>0"
  shows "ord_iso(B,r,B,r) = {id(B)}"
proof -
  note A1
  moreover
  { fix A assume "A \<in>  FinPow(X)" "A\<noteq>0"
    let ?M = "Maximum(r,A)"
    let ?A\<^sub>0 = "A - {?M}"
    assume "A = {?M} \<or> ord_iso(?A\<^sub>0,r,?A\<^sub>0,r) = {id(?A\<^sub>0)}"
    moreover
    { assume "A = {?M}"
      have "ord_iso({?M},r,{?M},r) = {id({?M})}"
	using id_ord_auto_singleton by simp
      with \<open>A = {?M}\<close> have "ord_iso(A,r,A,r) = {id(A)}"
	by simp }
    moreover
    { assume "ord_iso(?A\<^sub>0,r,?A\<^sub>0,r) = {id(?A\<^sub>0)}"
      have "ord_iso(A,r,A,r) = {id(A)}"
      proof
	show "{id(A)} \<subseteq> ord_iso(A,r,A,r)"
	  using id_ord_iso by simp
	{ fix f assume "f \<in> ord_iso(A,r,A,r)"
	  with A1 \<open>A \<in>  FinPow(X)\<close> \<open>A\<noteq>0\<close> have 
	    "restrict(f,?A\<^sub>0) \<in> ord_iso(?A\<^sub>0, r, A-{f`(?M)},r)"
	    using IsLinOrder_def fin_has_max ord_iso_rem_max 
	    by auto
	  with A1 \<open>A \<in>  FinPow(X)\<close> \<open>A\<noteq>0\<close> \<open>f \<in> ord_iso(A,r,A,r)\<close>
	    \<open>ord_iso(?A\<^sub>0,r,?A\<^sub>0,r) = {id(?A\<^sub>0)}\<close>
	  have "restrict(f,?A\<^sub>0) = id(?A\<^sub>0)"
	    using IsLinOrder_def fin_has_max max_auto_fixpoint 
	    by auto
	  moreover from A1 \<open>f \<in> ord_iso(A,r,A,r)\<close> 
	    \<open>A \<in>  FinPow(X)\<close> \<open>A\<noteq>0\<close> have
	    "f : A \<rightarrow> A" and "?M \<in> A" and "f`(?M) = ?M"
	    using ord_iso_def bij_is_fun IsLinOrder_def 
	      fin_has_max Order_ZF_4_L3 max_auto_fixpoint
	    by auto
	  ultimately have "f = id(A)" using id_fixpoint_rem
	    by simp 
	} then show "ord_iso(A,r,A,r) \<subseteq> {id(A)}"
	  by auto
      qed
    }
    ultimately have "ord_iso(A,r,A,r) = {id(A)}"
      by auto
  } then have "\<forall>A \<in>  FinPow(X). A = 0 \<or> 
      (A = {Maximum(r,A)} \<or> 
      ord_iso(A-{Maximum(r,A)},r,A-{Maximum(r,A)},r) = 
      {id(A-{Maximum(r,A)})} \<longrightarrow>  ord_iso(A,r,A,r) = {id(A)})"
    by auto
  moreover note A2 A3
  ultimately show "ord_iso(B,r,B,r) = {id(B)}"
    by (rule fin_ord_ind)
qed

text\<open>Every two finite linearly ordered sets are order 
  isomorphic. The statement is formulated to make the 
  proof by induction on the size of the set easier, 
  see \<open>fin_ord_iso_ex\<close> for an alternative formulation.
\<close>

lemma fin_order_iso: 
  assumes A1: "IsLinOrder(X,r)"  "IsLinOrder(Y,R)" and
  A2: "n \<in> nat" 
  shows "\<forall>A \<in> FinPow(X). \<forall>B \<in> FinPow(Y).
  A \<approx> n \<and> B \<approx> n \<longrightarrow> ord_iso(A,r,B,R) \<noteq> 0"
proof -
  note A2
  moreover have "\<forall>A \<in> FinPow(X). \<forall>B \<in> FinPow(Y).
    A \<approx> 0 \<and> B \<approx> 0 \<longrightarrow> ord_iso(A,r,B,R) \<noteq> 0"
    using eqpoll_0_is_0 empty_ord_iso by blast
  moreover have "\<forall>k \<in> nat.
    (\<forall>A \<in> FinPow(X). \<forall>B \<in> FinPow(Y). 
    A \<approx> k \<and> B \<approx> k \<longrightarrow> ord_iso(A,r,B,R) \<noteq> 0) \<longrightarrow>
    (\<forall>C \<in> FinPow(X). \<forall>D \<in> FinPow(Y). 
    C \<approx> succ(k) \<and> D \<approx> succ(k) \<longrightarrow> ord_iso(C,r,D,R) \<noteq> 0)"
  proof -
    { fix k assume "k \<in> nat"
      assume A3: "\<forall>A \<in> FinPow(X). \<forall>B \<in> FinPow(Y). 
	A \<approx> k \<and> B \<approx> k \<longrightarrow> ord_iso(A,r,B,R) \<noteq> 0"
      have "\<forall>C \<in> FinPow(X). \<forall>D \<in> FinPow(Y). 
	C \<approx> succ(k) \<and> D \<approx> succ(k) \<longrightarrow> ord_iso(C,r,D,R) \<noteq> 0"
      proof -
	{ fix C assume "C \<in> FinPow(X)"
	  fix D assume "D \<in> FinPow(Y)"
	  assume "C \<approx> succ(k)"  "D \<approx> succ(k)"
	  then have "C \<noteq> 0" and "D\<noteq> 0"
	    using eqpoll_succ_imp_not_empty by auto
	  let ?M\<^sub>C = "Maximum(r,C)"
	  let ?M\<^sub>D = "Maximum(R,D)"
	  let ?C\<^sub>0 = "C - {?M\<^sub>C}"
	  let ?D\<^sub>0 = "D - {?M\<^sub>D}"
	  from \<open>C \<in> FinPow(X)\<close> have "C \<subseteq> X"
	    using FinPow_def by simp
	  with A1 have "IsLinOrder(C,r)"
	    using ord_linear_subset by blast
	  from \<open>D \<in> FinPow(Y)\<close> have "D \<subseteq> Y"
	    using FinPow_def by simp
	  with A1 have "IsLinOrder(D,R)"
	    using ord_linear_subset by blast 
	  from A1 \<open>C \<in> FinPow(X)\<close> \<open>D \<in> FinPow(Y)\<close>  
	    \<open>C \<noteq> 0\<close> \<open>D\<noteq> 0\<close> have 
	    "HasAmaximum(r,C)" and "HasAmaximum(R,D)"
	    using IsLinOrder_def fin_has_max 
	    by auto
	  with A1 have "?M\<^sub>C \<in> C" and "?M\<^sub>D \<in> D"
	    using IsLinOrder_def Order_ZF_4_L3 by auto
	  with \<open>C \<approx> succ(k)\<close>  \<open>D \<approx> succ(k)\<close> have 
	    "?C\<^sub>0  \<approx> k" and "?D\<^sub>0 \<approx> k" using Diff_sing_eqpoll by auto
	  from \<open>C \<in> FinPow(X)\<close> \<open>D \<in> FinPow(Y)\<close>
	  have "?C\<^sub>0 \<in>  FinPow(X)" and "?D\<^sub>0 \<in>  FinPow(Y)"
	    using fin_rem_point_fin by auto
	  with A3 \<open>?C\<^sub>0  \<approx> k\<close> \<open>?D\<^sub>0 \<approx> k\<close> have
	    "ord_iso(?C\<^sub>0,r,?D\<^sub>0,R) \<noteq> 0" by simp
	  with \<open>IsLinOrder(C,r)\<close>  \<open>IsLinOrder(D,R)\<close> 
	    \<open>HasAmaximum(r,C)\<close> \<open>HasAmaximum(R,D)\<close>
	  have "ord_iso(C,r,D,R) \<noteq> 0"
	    by (rule rem_max_ord_iso)
	} thus ?thesis by simp
      qed
    } thus ?thesis by blast
  qed
  ultimately show ?thesis by (rule ind_on_nat)
qed

text\<open>Every two finite linearly ordered sets are order 
  isomorphic.\<close>

lemma fin_ord_iso_ex: 
  assumes A1: "IsLinOrder(X,r)"  "IsLinOrder(Y,R)" and
  A2: "A \<in> FinPow(X)" "B \<in> FinPow(Y)" and A3: "B \<approx> A"
  shows "ord_iso(A,r,B,R) \<noteq> 0"
proof -
  from A2 obtain n where "n \<in> nat" and "A \<approx> n"
    using finpow_decomp by auto
  from  A3 \<open>A \<approx> n\<close> have "B \<approx> n" by (rule eqpoll_trans)
  with A1 A2 \<open>A \<approx> n\<close> \<open>n \<in> nat\<close> show "ord_iso(A,r,B,R) \<noteq> 0"
    using fin_order_iso by simp
qed

text\<open>Existence and uniqueness of order isomorphism for two
  linearly ordered sets with the same number of elements.\<close>

theorem fin_ord_iso_ex_uniq: 
  assumes A1: "IsLinOrder(X,r)"  "IsLinOrder(Y,R)" and
  A2: "A \<in> FinPow(X)" "B \<in> FinPow(Y)" and A3: "B \<approx> A"
  shows "\<exists>!f. f \<in> ord_iso(A,r,B,R)"
proof
  from assms show "\<exists>f. f \<in> ord_iso(A,r,B,R)"
    using fin_ord_iso_ex by blast
  fix f g 
  assume A4: "f \<in> ord_iso(A,r,B,R)"  "g \<in> ord_iso(A,r,B,R)"
  then have "converse(g) \<in> ord_iso(B,R,A,r)"
    using ord_iso_sym by simp
  with \<open>f \<in> ord_iso(A,r,B,R)\<close> have 
    I: "converse(g) O f \<in>  ord_iso(A,r,A,r)"
    by (rule ord_iso_trans)
  { assume "A \<noteq> 0"
    with A1 A2 I have "converse(g) O f = id(A)"
      using fin_ord_auto_id by auto
    with A4 have "f = g" 
      using ord_iso_def comp_inv_id_eq_bij by auto }
  moreover
  { assume "A = 0"
    then have "A \<approx> 0" using eqpoll_0_iff
      by simp
    with A3 have "B \<approx> 0" by (rule eqpoll_trans)
    with A4 \<open>A = 0\<close> have
      "f \<in> ord_iso(0,r,0,R)" and  "g \<in> ord_iso(0,r,0,R)"
      using eqpoll_0_iff by auto
    then have "f = g" by (rule empty_ord_iso_uniq) }
  ultimately show "f = g" 
    using ord_iso_def comp_inv_id_eq_bij
    by auto
qed



end
