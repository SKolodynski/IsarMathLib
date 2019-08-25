(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2008  Slawomir Kolodynski

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

theory Partitions_ZF imports Finite_ZF FiniteSeq_ZF

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
  such that the values for different arguments are disjoint.
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
      
  
    

end
