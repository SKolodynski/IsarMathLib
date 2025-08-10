(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2008 - 2025 Slawomir Kolodynski

    This program is free software Redistribution and use in source and binary forms, 
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

section \<open>Finite sets - introduction\<close>

theory Finite_ZF imports ZF1 Nat_ZF_IML ZF.Cardinal func1

begin

text\<open>Standard Isabelle Finite.thy contains a very useful 
  notion of finite powerset: the set of finite subsets of a given set.
  The definition, however, is specific to Isabelle and based on the notion
  of "datatype", obviously not something that belongs to ZF set theory.
  This theory file devolops the notion of finite powerset similarly as
  in Finite.thy, but based on standard library's 
  Cardinal.thy. This theory file is intended to 
  replace IsarMathLib's \<open>Finite1\<close> and \<open>Finite_ZF_1\<close> theories
  that are currently derived from the "datatype" approach.
\<close>

subsection\<open>Definition and basic properties of finite powerset\<close>

text\<open>The goal of this section is to prove an induction theorem about
  finite powersets: if the empty set has some property and this property is 
  preserved by adding a single element of a set, 
  then this property is true for all finite subsets of this set.\<close>


text\<open>We defined the finite powerset \<open>FinPow(X)\<close> as those elements 
  of the powerset that are finite.\<close>

definition
  "FinPow(X) \<equiv> {A \<in> Pow(X). Finite(A)}"

text\<open>The cardinality of an element of finite powerset is a natural number.\<close>

lemma card_fin_is_nat: assumes "A \<in> FinPow(X)" 
  shows "|A| \<in> nat" and "A \<approx> |A|"
  using assms FinPow_def Finite_def cardinal_cong nat_into_Card 
    Card_cardinal_eq by auto

text\<open>The cardinality of a finite set is a natural number.\<close>

lemma card_fin_is_nat1: assumes "Finite(A)" shows "|A| \<in> nat"
  using assms card_fin_is_nat(1) unfolding FinPow_def by auto

text\<open>A reformulation of \<open>card_fin_is_nat\<close>: for a finit
  set $A$ there is a bijection between $|A|$ and $A$.\<close>

lemma fin_bij_card: assumes A1: "A \<in> FinPow(X)"
  shows "\<exists>b. b \<in> bij(|A|, A)"
proof -
  from A1 have "|A| \<approx> A" using card_fin_is_nat eqpoll_sym
    by blast
  then show ?thesis using eqpoll_def by auto
qed

text\<open>If a set has the same number of elements as $n \in \mathbb{N}$, 
  then its cardinality is $n$. Recall that in set theory a natural number
  $n$ is a set that has $n$ elements.\<close>

lemma card_card: assumes "A \<approx> n" and "n \<in> nat"
  shows "|A| = n"
  using assms cardinal_cong nat_into_Card Card_cardinal_eq
  by auto

text\<open>If we add a point to a finite set, the cardinality 
  increases by one. To understand the second assertion
  $| A \cup \{ a\}| = |A| \cup \{ |A|\} $ recall that
  the cardinality $|A|$ of $A$ is a natural number
  and for natural numbers we have $n+1 = n \cup \{ n\}$. 
\<close>

lemma card_fin_add_one: assumes A1: "A \<in> FinPow(X)" and A2: "a \<in> X-A"
  shows 
  "|A \<union> {a}| = succ( |A| )"
  "|A \<union> {a}| = |A| \<union> {|A|}"
proof -
  from A1 A2 have "cons(a,A) \<approx> cons( |A|, |A| )"
    using card_fin_is_nat mem_not_refl cons_eqpoll_cong
    by auto
  moreover have  "cons(a,A) = A \<union> {a}" by (rule consdef) 
  moreover have "cons( |A|, |A| ) = |A| \<union> {|A|}"
    by (rule consdef)
  ultimately have "A\<union>{a} \<approx> succ( |A| )" using succ_explained
    by simp
  with A1 show 
    "|A \<union> {a}| = succ( |A| )" and "|A \<union> {a}| = |A| \<union> {|A|}"
    using card_fin_is_nat card_card by auto
qed
  
text\<open>We can decompose the finite powerset into collection of
  sets of the same natural cardinalities.\<close>

lemma finpow_decomp: 
  shows "FinPow(X) = (\<Union>n \<in> nat. {A \<in> Pow(X). A \<approx> n})"
  using Finite_def FinPow_def by auto

text\<open>Finite powerset is the union of sets of cardinality
  bounded by natural numbers.\<close>

lemma finpow_union_card_nat: 
  shows "FinPow(X) = (\<Union>n \<in> nat. {A \<in> Pow(X). A \<lesssim> n})"
proof -
  have "FinPow(X) \<subseteq> (\<Union>n \<in> nat. {A \<in> Pow(X). A \<lesssim> n})"
    using finpow_decomp FinPow_def eqpoll_imp_lepoll
    by auto
  moreover have 
    "(\<Union>n \<in> nat. {A \<in> Pow(X). A \<lesssim> n}) \<subseteq> FinPow(X)"
    using lepoll_nat_imp_Finite FinPow_def by auto
  ultimately show ?thesis by auto
qed

text\<open>A different form of \<open>finpow_union_card_nat\<close> (see above) -
  a subset that has not more elements than a given natural number 
  is in the finite powerset.\<close>

lemma lepoll_nat_in_finpow: 
  assumes "n \<in> nat"   "A \<subseteq> X"  "A \<lesssim> n"
  shows "A \<in> FinPow(X)"
  using assms finpow_union_card_nat by auto

text\<open>Natural numbers are finite subsets of the set of natural numbers.\<close>

lemma nat_finpow_nat: assumes "n \<in> nat" shows "n \<in> FinPow(nat)"
  using assms nat_into_Finite nat_subset_nat FinPow_def
  by simp
  
text\<open>A finite subset is a finite subset of itself.\<close>

lemma fin_finpow_self: assumes "A \<in> FinPow(X)" shows "A \<in> FinPow(A)"
  using assms FinPow_def by auto

text\<open>A set is finite iff it is in its finite powerset.\<close>

lemma fin_finpow_iff: shows "Finite(A) \<longleftrightarrow> A \<in> FinPow(A)"
  unfolding FinPow_def by simp

text\<open>Induction for finite powerset. This is smilar to the
  standard Isabelle's \<open>Fin_induct\<close>.\<close>

theorem FinPow_induct: assumes A1: "P(0)" and
  A2: "\<forall>A \<in> FinPow(X). P(A) \<longrightarrow> (\<forall>a\<in>X. P(A \<union> {a}))" and
  A3: "B \<in> FinPow(X)"
  shows "P(B)"
proof -
  { fix n assume "n \<in> nat"
    moreover from A1 have I: "\<forall>B\<in>Pow(X). B \<lesssim> 0 \<longrightarrow> P(B)"
      using lepoll_0_is_0 by auto
    moreover have "\<forall> k \<in> nat. 
      (\<forall>B \<in> Pow(X). (B \<lesssim> k \<longrightarrow> P(B))) \<longrightarrow> 
      (\<forall>B \<in> Pow(X). (B \<lesssim> succ(k) \<longrightarrow> P(B)))"
    proof -
      { fix k assume A4: "k \<in> nat"
	assume A5: "\<forall> B \<in> Pow(X). (B \<lesssim> k \<longrightarrow> P(B))"
	fix B assume A6: "B \<in> Pow(X)"  "B \<lesssim> succ(k)"
	have "P(B)"
	proof -
	  have "B = 0 \<longrightarrow> P(B)"
	  proof -
	    { assume "B = 0"
	      then have "B \<lesssim> 0" using lepoll_0_iff
		by simp
	      with I A6 have "P(B)" by simp 
	    } thus "B = 0 \<longrightarrow> P(B)" by simp
	  qed
	  moreover have "B\<noteq>0 \<longrightarrow> P(B)"
	  proof -
	    { assume "B \<noteq> 0"
	      then obtain a where II: "a\<in>B" by auto
	      let ?A = "B - {a}"
	      from A6 II have "?A \<subseteq> X" and "?A \<lesssim> k" 
		using Diff_sing_lepoll by auto
	      with A4 A5 have "?A \<in> FinPow(X)" and "P(?A)" 
		using lepoll_nat_in_finpow finpow_decomp 
		by auto
	      with A2 A6 II have " P(?A \<union> {a})"
		by auto
	      moreover from II have "?A \<union> {a} = B"
		by auto
	      ultimately have "P(B)" by simp 
	    } thus "B\<noteq>0 \<longrightarrow> P(B)" by simp
	  qed
	  ultimately show "P(B)" by auto
	qed
      } thus ?thesis by blast
    qed
    ultimately have "\<forall>B \<in> Pow(X). (B \<lesssim> n \<longrightarrow> P(B))"
      by (rule ind_on_nat)
  } then have "\<forall>n \<in> nat. \<forall>B \<in> Pow(X). (B \<lesssim> n \<longrightarrow> P(B))"
    by auto
  with A3 show "P(B)" using finpow_union_card_nat
    by auto
qed

text\<open>A subset of a finite subset is a finite subset.\<close>

lemma subset_finpow: assumes "A \<in> FinPow(X)" and "B \<subseteq> A"
  shows "B \<in> FinPow(X)"
  using assms FinPow_def subset_Finite by auto

text\<open>If we subtract anything from a finite set, 
  the resulting set is finite.\<close>

lemma diff_finpow: 
  assumes "A \<in> FinPow(X)" shows "A-B \<in> FinPow(X)"
  using assms subset_finpow by blast

text\<open>If we remove a point from a finites subset,
  we get a finite subset.\<close>

corollary fin_rem_point_fin: assumes "A \<in> FinPow(X)"
  shows "A - {a} \<in> FinPow(X)"
  using assms diff_finpow by simp

text\<open>Cardinality of a nonempty finite set is a successsor
  of some natural number.\<close>

lemma card_non_empty_succ: 
  assumes A1: "A \<in> FinPow(X)" and A2: "A \<noteq> 0"
  shows "\<exists>n \<in> nat. |A| = succ(n)"
proof -
  from A2 obtain a where "a \<in> A" by auto
  let ?B = "A - {a}"
  from A1 \<open>a \<in> A\<close> have 
    "?B \<in> FinPow(X)" and "a \<in> X - ?B"
    using FinPow_def fin_rem_point_fin by auto
  then have "|?B \<union> {a}| = succ( |?B| )"
    using card_fin_add_one by auto
  moreover from \<open>a \<in> A\<close> \<open>?B \<in> FinPow(X)\<close> have 
    "A = ?B \<union> {a}" and "|?B| \<in> nat"
    using card_fin_is_nat by auto
  ultimately show "\<exists>n \<in> nat. |A| = succ(n)" by auto
qed

text\<open>Nonempty set has non-zero cardinality. This is probably
  true without the assumption that the set is finite, but
  I couldn't derive it from standard Isabelle theorems.
\<close>

lemma card_non_empty_non_zero:
  assumes "A \<in> FinPow(X)" and "A \<noteq> 0"
  shows "|A| \<noteq> 0"
proof -
  from assms obtain n where "|A| = succ(n)"
    using card_non_empty_succ by auto
  then show "|A| \<noteq> 0" using succ_not_0
    by simp
qed

text\<open>Another variation on the induction theme:
  If we can show something holds for the empty set and
  if it holds for all finite sets with 
  at most $k$ elements then it holds for all 
  finite sets with at most $k+1$
  elements, the it holds for all finite sets.\<close>

theorem FinPow_card_ind: assumes A1: "P(0)" and
  A2: "\<forall>k\<in>nat.
  (\<forall>A \<in> FinPow(X). A \<lesssim> k \<longrightarrow> P(A)) \<longrightarrow>
  (\<forall>A \<in> FinPow(X). A \<lesssim> succ(k) \<longrightarrow> P(A))"
  and A3: "A \<in>  FinPow(X)" shows "P(A)"
proof -
  from A3 have "|A| \<in> nat" and "A \<in>  FinPow(X)" and "A \<lesssim> |A|"
    using card_fin_is_nat eqpoll_imp_lepoll by auto
  moreover have "\<forall>n \<in> nat. (\<forall>A \<in> FinPow(X).
    A \<lesssim> n \<longrightarrow> P(A))"
  proof
    fix n assume "n \<in> nat"
    moreover from A1 have "\<forall>A \<in> FinPow(X). A \<lesssim> 0 \<longrightarrow> P(A)"
      using lepoll_0_is_0 by auto
    moreover note A2
    ultimately show
      "\<forall>A \<in> FinPow(X). A \<lesssim> n \<longrightarrow> P(A)"
      by (rule ind_on_nat)
  qed
  ultimately show "P(A)" by simp
qed  

text\<open>Another type of induction (or, maybe recursion).
  In the induction step  we try to find a point in the set that
  if we remove it, the fact that the property holds for the 
  smaller set implies that the property holds for the whole set. 
\<close>

lemma FinPow_ind_rem_one: assumes A1: "P(0)" and 
  A2: "\<forall> A \<in> FinPow(X). A \<noteq> 0 \<longrightarrow> (\<exists>a\<in>A. P(A-{a}) \<longrightarrow> P(A))"
  and A3: "B \<in>  FinPow(X)"
  shows "P(B)"
proof -
  note A1
  moreover have "\<forall>k\<in>nat.
  (\<forall>B \<in> FinPow(X). B \<lesssim> k \<longrightarrow> P(B)) \<longrightarrow>
  (\<forall>C \<in> FinPow(X). C \<lesssim> succ(k) \<longrightarrow> P(C))"
  proof -
    { fix k assume "k \<in> nat"
      assume A4: "\<forall>B \<in> FinPow(X). B \<lesssim> k \<longrightarrow> P(B)"
      have "\<forall>C \<in> FinPow(X). C \<lesssim> succ(k) \<longrightarrow> P(C)"
      proof -
	{ fix C assume "C \<in> FinPow(X)"
	  assume "C \<lesssim> succ(k)"
	  note A1
	  moreover
	  { assume "C \<noteq> 0"
	    with A2 \<open>C \<in> FinPow(X)\<close> obtain a where
	      "a\<in>C" and "P(C-{a}) \<longrightarrow> P(C)"
	      by auto
	    with A4 \<open>C \<in> FinPow(X)\<close> \<open>C \<lesssim> succ(k)\<close>
	    have "P(C)" using Diff_sing_lepoll fin_rem_point_fin
	      by simp }
	  ultimately have "P(C)" by auto
	} thus ?thesis by simp
      qed
    } thus ?thesis by blast
  qed
  moreover note A3
  ultimately show "P(B)" by (rule FinPow_card_ind)
qed

text\<open>Yet another induction theorem. This is similar, but 
  slightly more complicated than \<open>FinPow_ind_rem_one\<close>.
  The difference is in the treatment of the empty set to allow 
  to show properties that are not true for empty set.
\<close>

lemma FinPow_rem_ind: assumes A1: "\<forall>A \<in> FinPow(X). 
  A = 0 \<or> (\<exists>a\<in>A. A = {a} \<or> P(A-{a}) \<longrightarrow> P(A))"
  and A2: "A \<in>  FinPow(X)" and A3: "A\<noteq>0"
  shows "P(A)"
proof -
  have "0 = 0 \<or> P(0)" by simp
  moreover have
    "\<forall>k\<in>nat.
    (\<forall>B \<in> FinPow(X). B \<lesssim> k \<longrightarrow> (B=0 \<or> P(B))) \<longrightarrow>
    (\<forall>A \<in> FinPow(X). A \<lesssim> succ(k) \<longrightarrow> (A=0 \<or> P(A)))"
  proof -
    { fix k assume "k \<in> nat"
      assume A4: "\<forall>B \<in> FinPow(X). B \<lesssim> k \<longrightarrow> (B=0 \<or> P(B))"
      have "\<forall>A \<in> FinPow(X). A \<lesssim> succ(k) \<longrightarrow> (A=0 \<or> P(A))"
      proof -
	{ fix A assume "A \<in> FinPow(X)"
	  assume "A \<lesssim> succ(k)"  "A\<noteq>0"
	  from A1 \<open>A \<in> FinPow(X)\<close> \<open>A\<noteq>0\<close> obtain a 
	    where "a\<in>A" and "A = {a} \<or> P(A-{a}) \<longrightarrow> P(A)"
	    by auto
	  let ?B = "A-{a}"
	  from A4 \<open>A \<in> FinPow(X)\<close> \<open>A \<lesssim> succ(k)\<close> \<open>a\<in>A\<close>
	  have "?B = 0 \<or> P(?B)" 
	    using Diff_sing_lepoll fin_rem_point_fin
	    by simp
	  with \<open>a\<in>A\<close> \<open>A = {a} \<or> P(A-{a}) \<longrightarrow> P(A)\<close>
	  have "P(A)" by auto
	} thus  ?thesis by auto
      qed	  
    } thus ?thesis by blast
  qed
  moreover note A2
  ultimately have "A=0 \<or> P(A)" by (rule FinPow_card_ind)
  with A3 show "P(A)" by simp
qed

text\<open>If a family of sets is closed with respect to taking intersections
  of two sets then it is closed with respect to taking intersections 
  of any nonempty finite collection.\<close>

lemma inter_two_inter_fin: 
  assumes A1: "\<forall>V\<in>T. \<forall>W\<in>T. V \<inter> W \<in> T" and
  A2: "N \<noteq> 0" and A3: "N \<in> FinPow(T)"
  shows "\<Inter>N \<in> T"
proof -
  have "0 = 0 \<or> (\<Inter>0 \<in> T)" by simp
  moreover have "\<forall>M \<in> FinPow(T). (M = 0 \<or> \<Inter>M \<in> T) \<longrightarrow> 
    (\<forall>W \<in> T. M\<union>{W} = 0 \<or> \<Inter>(M \<union> {W}) \<in> T)"
  proof -
    { fix M assume "M \<in> FinPow(T)"
      assume A4: "M = 0 \<or> \<Inter>M \<in> T"
      { assume "M = 0"
	hence "\<forall>W \<in> T. M\<union>{W} = 0 \<or> \<Inter>(M \<union> {W}) \<in> T"
	  by auto }
      moreover
      { assume "M \<noteq> 0" 
	with A4 have "\<Inter>M \<in> T" by simp
	{ fix W assume "W \<in> T"
	  from \<open>M \<noteq> 0\<close> have "\<Inter>(M \<union> {W}) = (\<Inter>M) \<inter> W" 
	    by auto
	  with A1 \<open>\<Inter>M \<in> T\<close> \<open>W \<in> T\<close> have "\<Inter>(M \<union> {W}) \<in> T"
	    by simp
	} hence "\<forall>W \<in> T. M\<union>{W} = 0 \<or> \<Inter>(M \<union> {W}) \<in> T"
	  by simp }
      ultimately have "\<forall>W \<in> T. M\<union>{W} = 0 \<or> \<Inter>(M \<union> {W}) \<in> T"
	by blast
    } thus ?thesis by simp
  qed
  moreover note \<open>N \<in> FinPow(T)\<close>
  ultimately have "N = 0 \<or> (\<Inter>N \<in> T)"
    by (rule FinPow_induct)
  with A2 show "(\<Inter>N \<in> T)" by simp
qed

text\<open>If a family of sets contains the empty set and
  is closed with respect to taking unions
  of two sets then it is closed with respect to taking unions 
  of any finite collection.\<close>

lemma union_two_union_fin:
  assumes A1: "\<emptyset>\<in>C" and A2: "\<forall>A\<in>C. \<forall>B\<in>C. A\<union>B \<in> C" and 
  A3: "N \<in> FinPow(C)"
  shows "\<Union>N \<in> C"
proof -
  from \<open>\<emptyset>\<in>C\<close> have "\<Union>0 \<in> C" by simp
  moreover have "\<forall>M \<in> FinPow(C). \<Union>M \<in> C \<longrightarrow> (\<forall>A\<in>C. \<Union>(M \<union> {A}) \<in> C)"
  proof -
    { fix M assume "M \<in> FinPow(C)"
      assume "\<Union>M \<in> C"
      fix A assume "A\<in>C"
      have "\<Union>(M \<union> {A}) = (\<Union>M) \<union> A" by auto
      with A2 \<open>\<Union>M \<in> C\<close>  \<open>A\<in>C\<close> have  "\<Union>(M \<union> {A}) \<in> C"
	by simp
    } thus ?thesis by simp
  qed
  moreover note \<open>N \<in> FinPow(C)\<close>
  ultimately show "\<Union>N \<in> C" by (rule FinPow_induct)
qed

text\<open>Empty set is in finite power set, hence finite power set is never empty.\<close>

lemma empty_in_finpow: shows "\<emptyset> \<in> FinPow(X)" and "FinPow(X)\<noteq>\<emptyset>"
  using FinPow_def by auto

text\<open>Singleton is in the finite powerset.\<close>

lemma singleton_in_finpow: assumes "x \<in> X"
  shows "{x} \<in> FinPow(X)" using assms FinPow_def by simp

text\<open>If a set is nonempty then its finite power set contains a nonempty set.\<close>

lemma finpow_nempty_nempty: assumes "X\<noteq>\<emptyset>" shows "FinPow(X)\<setminus>{\<emptyset>} \<noteq> \<emptyset>"
  using assms singleton_in_finpow by blast

text\<open>Union of two finite subsets is a finite subset.\<close>

lemma union_finpow: assumes "A \<in> FinPow(X)" and "B \<in> FinPow(X)"
  shows "A \<union> B \<in> FinPow(X)"
  using assms unfolding FinPow_def by auto

text\<open>The finite power set of a larger set is larger.\<close>

lemma finpow_mono: assumes "A\<subseteq>B" shows "FinPow(A) \<subseteq> FinPow(B)"
  using assms unfolding FinPow_def by auto

text\<open>Union of finite number of finite sets is finite.\<close>

lemma fin_union_finpow: assumes "M \<in> FinPow(FinPow(X))"
  shows "\<Union>M \<in> FinPow(X)"
  using assms empty_in_finpow union_finpow union_two_union_fin
  by simp

text\<open>If a set is finite after removing one element, then it is finite.\<close>

lemma rem_point_fin_fin: 
  assumes A1: "x \<in> X" and A2: "A - {x} \<in> FinPow(X)"
  shows "A \<in> FinPow(X)"
proof -
  from assms have "(A - {x}) \<union> {x} \<in> FinPow(X)"
    using singleton_in_finpow union_finpow by simp
  moreover have "A \<subseteq> (A - {x}) \<union> {x}" by auto
  ultimately show "A \<in> FinPow(X)" 
    using FinPow_def subset_Finite by auto
qed
 
text\<open>An image of a finite set is finite.\<close>
  
lemma fin_image_fin: assumes "\<forall>V\<in>B. K(V)\<in>C" and "N \<in> FinPow(B)"
  shows "{K(V). V\<in>N} \<in> FinPow(C)"
proof -
  have "{K(V). V\<in>0} \<in> FinPow(C)" using FinPow_def
    by auto
  moreover have "\<forall>A \<in> FinPow(B). 
    {K(V). V\<in>A} \<in> FinPow(C) \<longrightarrow> (\<forall>a\<in>B. {K(V). V \<in> (A \<union> {a})} \<in> FinPow(C))"
  proof -
    { fix A assume "A \<in> FinPow(B)"
      assume  "{K(V). V\<in>A} \<in> FinPow(C)"
      fix a assume "a\<in>B"
      have  "{K(V). V \<in> (A \<union> {a})} \<in> FinPow(C)"
      proof -
	have "{K(V). V \<in> (A \<union> {a})} = {K(V). V\<in>A} \<union> {K(a)}"
	  by auto
	moreover note \<open>{K(V). V\<in>A} \<in> FinPow(C)\<close>
	moreover from \<open>\<forall>V\<in>B. K(V) \<in> C\<close>  \<open>a\<in>B\<close> have "{K(a)} \<in>  FinPow(C)"
	  using singleton_in_finpow by simp
	ultimately show ?thesis using union_finpow by simp
      qed
    } thus ?thesis by simp
  qed
  moreover note \<open>N \<in> FinPow(B)\<close>
  ultimately show "{K(V). V\<in>N} \<in> FinPow(C)"
    by (rule FinPow_induct)
qed

text\<open>A variant of \<open>fin_image_fin\<close> with a bit weaker first assumption:\<close>

lemma fin_image_fin1: assumes "\<forall>V\<in>N. K(V)\<in>C" and "N \<in> FinPow(B)"
  shows "{K(V). V\<in>N} \<in> FinPow(C)"
proof -
  from assms(2) have "N \<in> FinPow(N)"
    using fin_finpow_self by simp
  with assms(1) show ?thesis by (rule fin_image_fin)
qed

text\<open>An image of a nonempty finite set is a nonempty finite set.\<close>

lemma fin_image_fin0: assumes "N \<in> FinPow(B)\<setminus>{\<emptyset>}" and "\<forall>V\<in>N. K(V)\<in>C" 
  shows  "{K(V). V\<in>N} \<in> FinPow(C)\<setminus>{\<emptyset>}"
  using assms fin_image_fin1 by auto

text\<open>A version of \<open>union_two_union_fin\<close> for nonempty finite subsets of some set $X$: 
  if a family of sets contains all singletons from a finite subset $N$ of $X$ 
  and is closed with respect to taking unions of two sets then it contains $N$.\<close>

lemma union_two_union_fin_nempty: 
  assumes "N\<in>FinPow(X)" "N\<noteq>\<emptyset>" "\<forall>x\<in>N. {x} \<in> C" "\<forall>A\<in>C. \<forall>B\<in>C. A\<union>B \<in> C" 
  shows "N\<in>C"
proof -
  let ?C\<^sub>0 = "{\<emptyset>} \<union> C"
  let ?N\<^sub>0 = "{{x}. x \<in> N}"
  have "\<Union>?N\<^sub>0 = N" by auto
  from assms(1,3,4) have 
    "\<emptyset>\<in>?C\<^sub>0" "\<forall>A\<in>?C\<^sub>0. \<forall>B\<in>?C\<^sub>0. A\<union>B \<in> ?C\<^sub>0" "?N\<^sub>0\<in>FinPow(?C\<^sub>0)"
    using fin_image_fin1 finpow_mono by auto
  then have "\<Union>?N\<^sub>0 \<in> ?C\<^sub>0" by (rule union_two_union_fin)
  with assms(2) \<open>\<Union>?N\<^sub>0 = N\<close> show "N\<in>C" by simp
qed

text\<open>If a set $X$ is finite then the set $\{ K(x). x\in X\}$ is also finite.
  It's basically standard Isalelle/ZF \<open>Finite_RepFun\<close> in nicer notation.\<close>

lemma fin_rep_fin: assumes "Finite(X)" shows "Finite({K(x). x\<in>X})"
  using assms Finite_RepFun by simp

text\<open>The image of a singleton by any function is finite. It's of course either
  empty or has exactly one element, but showing that it's a finite subset of the codomain
  is good enough for us. \<close>

lemma image_singleton_fin: assumes "f:X\<rightarrow>Y" shows "f``{x} \<in> FinPow(Y)"
proof -
  { assume "x\<in>X"
    with assms have "f``{x} \<in> FinPow(Y)"
      using singleton_image singleton_in_finpow by simp
  }
  moreover
  { assume "x\<notin>X"
    with assms have "f``{x} \<in> FinPow(Y)"
      using arg_not_in_domain(1) empty_in_finpow by simp
  }
  ultimately show ?thesis by auto
qed
    
text\<open>Union of a finite indexed family of finite sets is finite.\<close>

lemma union_fin_list_fin: 
  assumes A1: "n \<in> nat" and A2: "\<forall>k \<in> n. N(k) \<in> FinPow(X)"
  shows 
  "{N(k). k \<in> n} \<in>  FinPow(FinPow(X))" and "(\<Union>k \<in> n. N(k)) \<in> FinPow(X)"
proof -
  from A1 have "n \<in> FinPow(n)" 
    using nat_finpow_nat fin_finpow_self by auto
  with A2 show "{N(k). k \<in> n} \<in>  FinPow(FinPow(X))"
    by (rule fin_image_fin)
  then show "(\<Union>k \<in> n. N(k)) \<in> FinPow(X)"
    using fin_union_finpow by simp
qed
  
end
