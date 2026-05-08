(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2008-2026  Slawomir Kolodynski

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

section \<open>Partitions of sets\<close>

theory Partitions_ZF imports Finite_ZF InductiveSeq_ZF

begin

text\<open>It is a common trick in proofs that we divide a set into non-overlapping
  subsets. The first case is when we split the set into 
  two nonempty disjoint sets. Here this is modeled as an ordered pair of sets
  and the set of such divisions of set $X$ is called \<open>Bisections(X)\<close>.
  The second variation on this theme is a set-valued function (aren't they all
  in ZF?) whose values are nonempty and mutually disjoint.
\<close>

subsection\<open>Bisections\<close>

text\<open>This section is about dividing sets into two non-overlapping subsets.
\<close>

text\<open>The set of bisections of a given set $A$ is a set of pairs of nonempty
  subsets of $A$ that do not overlap and their union is equal to $A$.\<close>

definition
  "Bisections(X) = {p \<in> Pow(X)\<times>Pow(X). 
  fst(p)\<noteq>0 \<and> snd(p)\<noteq>0 \<and> fst(p)\<inter>snd(p) = 0 \<and> fst(p)\<union>snd(p) = X}"

text\<open>Properties of bisections.\<close>

lemma bisec_props: assumes "\<langle>A,B\<rangle> \<in> Bisections(X)" shows
  "A\<noteq>0"  "B\<noteq>0" "A \<subseteq> X"  "B \<subseteq> X"  "A \<inter> B = 0"  "A \<union> B = X"  "X \<noteq> 0"
  using assms Bisections_def by auto

text\<open>Kind of inverse of \<open>bisec_props\<close>: a pair of nonempty
  disjoint sets form a bisection of their union.\<close>

lemma is_bisec: 
  assumes "A\<noteq>0"  "B\<noteq>0"  "A \<inter> B = 0" 
  shows "\<langle>A,B\<rangle> \<in> Bisections(A\<union>B)" using assms Bisections_def
  by auto


text\<open>Bisection of $X$ is a pair of subsets of $X$.\<close>

lemma bisec_is_pair: assumes "Q \<in> Bisections(X)"
  shows "Q = \<langle>fst(Q), snd(Q)\<rangle>"
  using assms Bisections_def by auto

text\<open>The set of bisections of the empty set is empty.\<close>

lemma bisec_empty: shows "Bisections(0) = 0"
  using Bisections_def by auto

text\<open>The next lemma shows what can we say about bisections of a set
  with another element added.\<close>

lemma bisec_add_point: 
  assumes A1: "x \<notin> X" and A2: "\<langle>A,B\<rangle> \<in> Bisections(X \<union> {x})"
  shows "(A = {x} \<or> B = {x}) \<or> (\<langle>A - {x}, B - {x}\<rangle> \<in> Bisections(X))"
  proof -
    { assume "A \<noteq> {x}" and "B \<noteq> {x}"
      with A2 have "A - {x} \<noteq> 0" and "B - {x} \<noteq> 0"
	using singl_diff_empty Bisections_def
	by auto
      moreover have "(A - {x}) \<union> (B - {x}) = X"
      proof -
	have "(A - {x}) \<union> (B - {x}) = (A \<union> B) - {x}"
	  by auto
	also from assms have "(A \<union> B) - {x} = X"
	  using Bisections_def by auto
	finally show ?thesis by simp
      qed
      moreover from A2 have "(A - {x}) \<inter> (B - {x}) = 0"
	using Bisections_def by auto
      ultimately have "\<langle>A - {x}, B - {x}\<rangle> \<in> Bisections(X)"
	using Bisections_def by auto
    } thus ?thesis by auto
qed

text\<open>A continuation of the lemma \<open>bisec_add_point\<close>
  that refines the case when the pair with removed point bisects
  the original set.\<close>

lemma bisec_add_point_case3: 
  assumes A1: "\<langle>A,B\<rangle> \<in> Bisections(X \<union> {x})"
  and A2: "\<langle>A - {x}, B - {x}\<rangle> \<in> Bisections(X)"
  shows 
  "(\<langle>A, B - {x}\<rangle> \<in> Bisections(X) \<and> x \<in> B) \<or> 
  (\<langle>A - {x}, B\<rangle> \<in> Bisections(X) \<and> x \<in> A)"
proof -
  from A1 have "x \<in> A \<union> B"
    using Bisections_def by auto
  hence "x\<in>A \<or> x\<in>B" by simp
  from A1 have "A - {x} = A \<or> B - {x} = B"
    using Bisections_def by auto
  moreover
  { assume "A - {x} = A"
    with A2 \<open>x \<in> A \<union> B\<close> have 
      "\<langle>A, B - {x}\<rangle> \<in> Bisections(X) \<and> x \<in> B" 
      using singl_diff_eq by simp }
  moreover
  { assume "B - {x} = B"
    with A2 \<open>x \<in> A \<union> B\<close> have 
      "\<langle>A - {x}, B\<rangle> \<in> Bisections(X) \<and> x \<in> A"
      using singl_diff_eq by simp }
  ultimately show ?thesis by auto
qed

text\<open>Another lemma about bisecting a set with an added point.\<close>

lemma point_set_bisec: 
  assumes A1: "x \<notin> X" and A2: "\<langle>{x}, A\<rangle> \<in> Bisections(X \<union> {x})"
  shows "A = X" and "X \<noteq> 0"
proof -
  from A2 have "A \<subseteq> X" using Bisections_def by auto
  moreover
  { fix a assume "a\<in>X"
    with A2 have "a \<in> {x} \<union> A" using Bisections_def by simp
    with A1 \<open>a\<in>X\<close> have "a \<in> A" by auto }
  ultimately show "A = X" by auto
  with A2 show "X \<noteq> 0" using Bisections_def by simp
qed

text\<open>Yet another lemma about bisecting a set with an added point,
  very similar to \<open> point_set_bisec\<close> with almost the same proof.\<close>

lemma set_point_bisec: 
  assumes A1: "x \<notin> X" and A2: "\<langle>A, {x}\<rangle> \<in> Bisections(X \<union> {x})"
  shows "A = X" and "X \<noteq> 0"
proof -
  from A2 have "A \<subseteq> X" using Bisections_def by auto
  moreover
  { fix a assume "a\<in>X"
    with A2 have "a \<in> A \<union> {x}" using Bisections_def by simp
    with A1 \<open>a\<in>X\<close> have "a \<in> A" by auto }
  ultimately show "A = X" by auto
  with A2 show "X \<noteq> 0" using Bisections_def by simp
qed

text\<open>If a pair of sets bisects a finite set, then both 
  elements of the pair are finite.\<close>

lemma bisect_fin: 
  assumes A1: "A \<in> FinPow(X)" and A2: "Q \<in> Bisections(A)"
  shows "fst(Q) \<in> FinPow(X)" and "snd(Q) \<in> FinPow(X)"
proof -
  from A2 have "\<langle>fst(Q), snd(Q)\<rangle> \<in> Bisections(A)"
    using bisec_is_pair by simp
  then have "fst(Q) \<subseteq> A" and "snd(Q) \<subseteq> A"
    using bisec_props by auto
  with A1 show "fst(Q) \<in> FinPow(X)" and "snd(Q) \<in> FinPow(X)"
    using FinPow_def subset_Finite by auto
qed

subsection\<open>Partitions\<close>

text\<open>This sections covers the situation when we have an arbitrary number
  of sets we want to partition into.\<close>

text\<open>We define a notion of a partition as a set valued function 
  such that the values for different arguments are nonempty and disjoint.
  The name is derived from the fact that such 
  function "partitions" the union of its arguments. 
  Please let me know if you have 
  a better idea for a name for such notion. We would prefer to say
 ''is a partition'', but that reserves the letter ''a'' as a keyword(?)
  which causes problems.\<close>

definition
  Partition ("_ {is partition}" [90] 91) where
  "P {is partition} \<equiv>  \<forall>x \<in> domain(P). 
  P`(x) \<noteq> 0 \<and> (\<forall>y \<in> domain(P). x\<noteq>y \<longrightarrow> P`(x) \<inter> P`(y) = 0)"

text\<open>A fact about lists of mutually disjoint sets.\<close>

lemma list_partition: assumes A1: "n \<in> nat" and 
  A2: "a : succ(n) \<rightarrow> X"   "a {is partition}"
  shows "(\<Union>i\<in>n. a`(i)) \<inter> a`(n) = 0"
proof -
  { assume "(\<Union>i\<in>n. a`(i)) \<inter> a`(n) \<noteq> 0"
    then have "\<exists>x. x \<in> (\<Union>i\<in>n. a`(i)) \<inter> a`(n)"
      by (rule nonempty_has_element)
    then obtain x where "x \<in> (\<Union>i\<in>n. a`(i))" and  I: "x \<in> a`(n)"
      by auto
    then obtain i where "i \<in> n" and "x \<in> a`(i)" by auto
    with A2 I have False 
      using mem_imp_not_eq func1_1_L1 Partition_def
      by auto
  } thus ?thesis by auto
qed

text\<open>We can turn every injection into a partition.\<close>

lemma inj_partition: 
  assumes A1: "b \<in> inj(X,Y)" 
  shows 
  "\<forall>x \<in> X. {\<langle>x, {b`(x)}\<rangle>. x \<in> X}`(x) = {b`(x)}" and
  "{\<langle>x, {b`(x)}\<rangle>. x \<in> X} {is partition}"
proof -
  let ?p = "{\<langle>x, {b`(x)}\<rangle>. x \<in> X}"
  { fix x assume "x \<in> X"
    from A1 have "b : X \<rightarrow> Y" using inj_def
      by simp
    with \<open>x \<in> X\<close> have "{b`(x)} \<in> Pow(Y)"
       using apply_funtype by simp
  } hence "\<forall>x \<in> X. {b`(x)} \<in> Pow(Y)" by simp
  then have "?p : X \<rightarrow> Pow(Y)" using ZF_fun_from_total 
    by simp
  then have "domain(?p) = X" using func1_1_L1
    by simp
  from \<open>?p : X \<rightarrow> Pow(Y)\<close> show I: "\<forall>x \<in> X. ?p`(x) = {b`(x)}"
    using ZF_fun_from_tot_val0 by simp
  { fix x assume "x \<in> X"
    with I have "?p`(x) = {b`(x)}" by simp
    hence "?p`(x) \<noteq> 0" by simp
    moreover
    { fix t assume "t \<in> X" and "x \<noteq> t"
      with A1 \<open>x \<in> X\<close> have "b`(x) \<noteq> b`(t)" using inj_def 
	by auto
      with I \<open>x\<in>X\<close> \<open>t \<in> X\<close> have "?p`(x) \<inter> ?p`(t) = 0"
	by auto }
    ultimately have 
      "?p`(x) \<noteq> 0 \<and> (\<forall>t \<in> X. x\<noteq>t \<longrightarrow> ?p`(x) \<inter> ?p`(t) = 0)"
      by simp
  } with \<open>domain(?p) = X\<close> show "{\<langle>x, {b`(x)}\<rangle>. x \<in> X} {is partition}"
    using Partition_def by simp
qed

subsection\<open>Collections of pairwise disjoint sets\<close>

text\<open>The notion of collection of pairwise disjoint sets is similar to a partition 
  except that we don't require the members to be nonempty.\<close>

text\<open>A set valued function $X$ is pairwise disjoint if for any two different indices 
  the corresponding sets have empty intersection.\<close>

definition 
  IsPairwiseDisjoint ("_ {is pairwise disjoint}" [60] 61) where
  "X {is pairwise disjoint} \<equiv> \<forall>i\<in>domain(X). \<forall>j\<in>domain(X). i\<noteq>j \<longrightarrow> X`(i)\<inter>X`(j)=\<emptyset>" 

text\<open>Suppose that $X:I\rightarrow Y$ is pairwise disjoint collection of sets and 
  we know that $x$ is a member of a set in the collection. Then the index of
  that set can be expressed as $\bigcup\{ j in I: x\in X(j)\}$.\<close>

lemma get_the_one: 
  assumes "X:I\<rightarrow>Y" "X {is pairwise disjoint}" "i\<in>I" "x\<in>X`(i)"
  shows "i = \<Union>{j\<in>I. x\<in>X`(j)}"
proof -
  from assms have U: "\<exists>!i. i\<in>I \<and> x\<in>X`(i)"
    using func1_1_L1 unfolding IsPairwiseDisjoint_def by auto
  with assms(3,4) show ?thesis using ZF1_1_L9(2,3) by force
qed 

text\<open>A kind of inverse of \<open>get_the_one\<close>: if $X:I\rightarrow Y$ is pairwise disjoint 
  collection of sets and $x\in\bigcup_{i\in I} X(i)$ 
  then $i:=\bigcup\{ j\in I: x\in X(j)\}$ is an index and $x\in X(i)$.\<close>

lemma one_is_the_one: 
  assumes "X:I\<rightarrow>Y" "X {is pairwise disjoint}" "x\<in>(\<Union>j\<in>I. X`(j))"
  defines "i \<equiv> \<Union>{j\<in>I. x\<in>X`(j)}"
  shows "i\<in>I" "x\<in>X`(i)" using assms get_the_one by auto  

text\<open>A special case of pairwise disjoint collection is the sequence of set differences
  of consecutive elements of sequence of sets that is monotonic in the inclusion order.
  The next lemma shows that if a sequence $\{\mathcal{U}_i\}_{i\in\mathbb{N}}$ of subsets of $X$ 
  is decreasing in the inclusion order on the powerset of $X$ then the sequence 
  $\{\mathcal{U}_i\setminus \mathcal{U}_{i+1}\}_{i\in\mathbb{N}}$ is pairwise disjoint.
  In addition, the union $\bigcup_{n\in\mathbb{N}}\mathcal{U}_{n}\setminus \mathcal{U}_{n+1}$ 
  is the same as $\mathcal{U}_0\setminus \bigcap_{n\in\mathbb{N}} \mathcal{U}_n$.\<close>

lemma decr_pair_disj: 
  assumes "IsDecreasingSeq(Pow(X),InclusionOn(Pow(X)),\<U>)"
  shows 
    "{\<langle>n,\<U>`(n)\<setminus>\<U>`(n #+ 1)\<rangle>. n\<in>nat} {is pairwise disjoint}"
    "(\<Union>n\<in>nat. \<U>`(n)\<setminus>\<U>`(n #+ 1)) = \<U>`(0)\<setminus>(\<Inter>n\<in>nat. \<U>`(n))"
proof -
  let ?r = "InclusionOn(Pow(X))"
  let ?F = "{\<langle>n,\<U>`(n)\<setminus>\<U>`(n #+ 1)\<rangle>. n\<in>nat}"
  have "domain(?F) = nat" and "IsPreorder(Pow(X),?r)"
    using incl_is_partorder(2) by auto
  { fix i j assume "i\<in>nat" "j\<in>nat" "i\<noteq>j"
    then have "i < j \<or> j < i" using nat_mem_total by simp
    moreover
    { assume "i < j"
      with assms \<open>j\<in>nat\<close> have "\<langle>\<U>`(j), \<U>`(i #+ 1)\<rangle> \<in> ?r"
        using nat_less_succ_leq incl_is_partorder(2) 
          decreasing_seq_mono1 by blast
      then have "(\<U>`(i)\<setminus>\<U>`(i #+ 1)) \<inter> (\<U>`(j)\<setminus>\<U>`(j #+ 1)) = \<emptyset>"
        unfolding InclusionOn_def by auto
    }
    moreover
    { assume "j < i"
      with assms \<open>i\<in>nat\<close> have "\<langle>\<U>`(i), \<U>`(j #+ 1)\<rangle> \<in> ?r"
        using nat_less_succ_leq incl_is_partorder(2) 
          decreasing_seq_mono1 by blast
      then have "(\<U>`(i)\<setminus>\<U>`(i #+ 1)) \<inter> (\<U>`(j)\<setminus>\<U>`(j #+ 1)) = \<emptyset>"
        unfolding InclusionOn_def by auto
    }
    ultimately have "(\<U>`(i)\<setminus>\<U>`(i #+ 1)) \<inter> (\<U>`(j)\<setminus>\<U>`(j #+ 1)) = \<emptyset>"
      by auto
    with \<open>i\<in>nat\<close> \<open>j\<in>nat\<close> have "?F`(i) \<inter> ?F`(j) = \<emptyset>" 
      using  ZF_fun_from_tot_val2 by simp_all
  } hence "\<forall>i\<in>nat. \<forall>j\<in>nat. i\<noteq>j \<longrightarrow> ?F`(i) \<inter> ?F`(j) = \<emptyset>"
    by simp
  with \<open>domain(?F) = nat\<close> show 
    "{\<langle>n,\<U>`(n)\<setminus>\<U>`(n #+ 1)\<rangle>. n\<in>nat} {is pairwise disjoint}" 
    unfolding IsPairwiseDisjoint_def by simp
  show "(\<Union>n\<in>nat. \<U>`(n)\<setminus>\<U>`(n #+ 1)) = \<U>`(0)\<setminus>(\<Inter>n\<in>nat. \<U>`(n))"
  proof
    let ?L = "\<Union>n\<in>nat. \<U>`(n)\<setminus>\<U>`(n #+ 1)"
    let ?R = "\<U>`(0)\<setminus>(\<Inter>n\<in>nat. \<U>`(n))"
    { fix x assume "x\<in>?L"
      then obtain n where "n\<in>nat" and "x\<in>\<U>`(n)\<setminus>\<U>`(n #+ 1)"
        by auto
      then have "x\<in>\<U>`(n)" and "0\<le>n" by auto
      with assms \<open>IsPreorder(Pow(X),?r)\<close> \<open>n\<in>nat\<close> have "\<langle>\<U>`(n),\<U>`(0)\<rangle> \<in> ?r"
        using decreasing_seq_mono1 by simp
      with \<open>x\<in>\<U>`(n)\<close> have "x\<in>\<U>`(0)"
        unfolding InclusionOn_def by auto
      with \<open>n\<in>nat\<close> \<open>x\<in>\<U>`(n)\<setminus>\<U>`(n #+ 1)\<close> have "x\<in>?R" by auto
    } thus "?L\<subseteq>?R" by auto
    { fix x assume "x\<in>?R"
      then have "x\<in>\<U>`(0)" and "x\<notin>(\<Inter>n\<in>nat. \<U>`(n))" by auto
      let ?B = "{k\<in>nat. x\<notin>\<U>`(k)}"
      let ?m = "Minimum(Le,?B)"
      from \<open>x\<notin>(\<Inter>n\<in>nat. \<U>`(n))\<close> have "?B\<subseteq>nat" and "?B\<noteq>\<emptyset>" by auto
      then have "?m\<in>nat" "?m\<in>?B" and "\<forall>n\<in>?B. ?m \<le> n"
        using subset_nat_has_min(2,3) by auto
      from \<open>x\<in>\<U>`(0)\<close> \<open>?m\<in>?B\<close> have "?m\<noteq>0" by auto
      with \<open>?m\<in>nat\<close> obtain n where "n\<in>nat" and "?m = n #+ 1"
        using nat_not0_succ by auto
      with \<open>\<forall>n\<in>?B. ?m\<le>n\<close> \<open>?m\<in>?B\<close> have "\<exists>n\<in>nat. x \<in> \<U>`(n)\<setminus>\<U>`(n #+ 1)"
        using nat_less_add_one by auto
    } thus "?R\<subseteq>?L" by auto
  qed
qed

text\<open>Essentially the same assertions as \<open>decr_pair_disj\<close> but with more explicit assumptions:
  if $\mathcal{U}$ is a sequence valued in the power set of $X$ and 
  $\mathcal{U}_{n+1}\subseteq \mathcal{U}_{n+1}$ for all natural numbers $n$, then
  the assumption and hence the assertions of \<open>decr_pair_disj\<close> hold.\<close>

lemma decr_pair_disj1: 
  assumes "\<U>:nat\<rightarrow>Pow(X)" "\<forall>n\<in>nat. \<U>`(n #+ 1)\<subseteq>\<U>`(n)"
  defines "\<V> \<equiv> {\<langle>i,\<U>`(i)\<setminus>\<U>`(i #+ 1)\<rangle>. i\<in>nat}"
  shows
  "\<V>:nat\<rightarrow>Pow(X)"
  "IsDecreasingSeq(Pow(X),InclusionOn(Pow(X)),\<U>)"
  "\<V> {is pairwise disjoint}"
  "(\<Union>n\<in>nat. \<U>`(n)\<setminus>\<U>`(n #+ 1)) = \<U>`(0)\<setminus>(\<Inter>n\<in>nat. \<U>`(n))"
proof -
  have "\<forall>i\<in>nat. 
  \<langle>\<U>`(i #+ 1),\<U>`(i)\<rangle> \<in> InclusionOn(Pow(X)) \<and> \<U>`(i)\<setminus>\<U>`(i #+ 1) \<in> Pow(X)"
  proof 
    fix i assume "i\<in>nat"
    with assms(2) have "\<U>`(i #+ 1) \<subseteq> \<U>`(i)" and "i #+ 1 \<in> nat"
      by simp_all
    from assms(1) \<open>i\<in>nat\<close> have "\<U>`(i) \<in> Pow(X)" 
        using apply_funtype by blast
    from assms(1) \<open>i #+ 1 \<in> nat\<close> have "\<U>`(i #+ 1) \<in> Pow(X)" 
      using apply_funtype by blast
    with \<open>\<U>`(i #+ 1) \<subseteq> \<U>`(i)\<close> \<open>\<U>`(i) \<in> Pow(X)\<close> show
      "\<langle>\<U>`(i #+ 1),\<U>`(i)\<rangle> \<in> InclusionOn(Pow(X)) \<and> \<U>`(i)\<setminus>\<U>`(i #+ 1) \<in> Pow(X)"
      unfolding InclusionOn_def by auto
  qed
  with assms(1,3) show "\<V>:nat\<rightarrow>Pow(X)" and 
    "IsDecreasingSeq(Pow(X),InclusionOn(Pow(X)),\<U>)"
    using ZF_fun_from_total unfolding IsDecreasingSeq_def by simp_all
  with assms(3) show 
    "\<V> {is pairwise disjoint}" and 
    "(\<Union>n\<in>nat. \<U>`(n)\<setminus>\<U>`(n #+ 1)) = \<U>`(0)\<setminus>(\<Inter>n\<in>nat. \<U>`(n))"
    using decr_pair_disj by simp_all
qed

text\<open>If a sequence $\{\mathcal{U}_i\}_{i\in\mathbb{N}}$ of subsets of $X$ 
  is increasing in the inclusion order on the powerset of $X$ then the sequence 
  $\{\mathcal{U}_{i+1}\setminus \mathcal{U}_{i}\}_{i\in\mathbb{N}}$ is pairwise disjoint. \<close>

lemma incr_pair_disj:   assumes "IsIncreasingSeq(Pow(X),InclusionOn(Pow(X)),\<U>)"
  shows "{\<langle>n,\<U>`(n #+ 1)\<setminus>\<U>`(n)\<rangle>. n\<in>nat} {is pairwise disjoint}"
proof -
  let ?r = "InclusionOn(Pow(X))"
  let ?F = "{\<langle>n,\<U>`(n #+ 1)\<setminus>\<U>`(n)\<rangle>. n\<in>nat}"
  have "domain(?F) = nat" and "IsPreorder(Pow(X),?r)"
    using incl_is_partorder(2) by auto
  { fix i j assume "i\<in>nat" "j\<in>nat" "i\<noteq>j"
    then have "i < j \<or> j < i" using nat_mem_total by simp
    moreover
    { assume "i < j"
      with assms \<open>j\<in>nat\<close> have "\<langle>\<U>`(i #+ 1), \<U>`(j)\<rangle> \<in> ?r"
        using incl_is_partorder(2) increasing_seq_mono1 
          nat_less_succ_leq by blast
      then have "(\<U>`(i #+ 1)\<setminus>\<U>`(i)) \<inter> (\<U>`(j #+ 1)\<setminus>\<U>`(j)) = \<emptyset>"
        unfolding InclusionOn_def by auto
    }
    moreover
    { assume "j < i"
      with assms \<open>i\<in>nat\<close> have "\<langle>\<U>`(j #+ 1), \<U>`(i)\<rangle> \<in> ?r"
        using incl_is_partorder(2) increasing_seq_mono1 
          nat_less_succ_leq by blast
      then have "(\<U>`(i #+ 1)\<setminus>\<U>`(i)) \<inter> (\<U>`(j #+ 1)\<setminus>\<U>`(j)) = \<emptyset>"
        unfolding InclusionOn_def by auto
    }
    ultimately have "(\<U>`(i #+ 1)\<setminus>\<U>`(i)) \<inter> (\<U>`(j #+ 1)\<setminus>\<U>`(j)) = \<emptyset>"
      by auto
    with \<open>i\<in>nat\<close> \<open>j\<in>nat\<close> have "?F`(i) \<inter> ?F`(j) = \<emptyset>" 
      using  ZF_fun_from_tot_val2 by simp_all
  } hence "\<forall>i\<in>nat. \<forall>j\<in>nat. i\<noteq>j \<longrightarrow> ?F`(i) \<inter> ?F`(j) = \<emptyset>"
    by simp
  with \<open>domain(?F) = nat\<close> show ?thesis 
    unfolding IsPairwiseDisjoint_def by simp
qed


end
