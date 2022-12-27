(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2005-2012  Slawomir Kolodynski

    This program is free software; Redistribution and use in source and binary forms, 
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

section \<open>Topology - introduction\<close>

theory Topology_ZF imports ZF1 Finite_ZF Fol1

begin

text\<open>This theory file provides basic definitions and properties of topology,
  open and closed sets, closure and boundary.\<close> 

subsection\<open>Basic definitions and properties\<close>

text\<open>A typical textbook defines a topology on a set $X$ as a 
  collection $T$ of subsets 
  of $X$ such that $X\in T$, $\emptyset \in T$ and $T$ is closed 
  with respect to arbitrary unions and  intersection of two sets. One can
  notice here that since we always have $\bigcup T = X$, the set 
  on which the topology
  is defined (the "carrier" of the topology) can always be constructed 
  from the topology itself and is 
  superfluous in the definition. Moreover, as Marnix Klooster pointed out to me,
  the fact that the empty set is open can also be proven from other axioms.
  Hence, we define a topology as 
  a collection of sets that is closed under 
  arbitrary unions and intersections of two sets, without any mention of the
  set on which the topology is defined. Recall that \<open>Pow(T)\<close> 
  is the powerset of $T$, so that if $M\in$ \<open> Pow(T)\<close> then $M$ 
  is a subset of $T$. The sets that belong to a topology $T$ will be sometimes called
  ''open in'' $T$ or just ''open'' if the topology is clear from the context.  
\<close>

text\<open>Topology is a collection of sets that is closed under arbitrary unions and intersections 
  of two sets.\<close>

definition
  IsATopology ("_ {is a topology}" [90] 91) where
  "T {is a topology} \<equiv> ( \<forall>M \<in> Pow(T). \<Union>M \<in> T ) \<and> 
  ( \<forall>U\<in>T. \<forall> V\<in>T. U\<inter>V \<in> T)"


text\<open>We define interior of a set $A$ as the union of all open sets 
  contained in $A$. We use \<open>Interior(A,T)\<close> to denote the 
  interior of A.\<close>

definition
  "Interior(A,T) \<equiv> \<Union> {U\<in>T. U \<subseteq> A}"

text\<open>A set is closed if it is contained in the carrier of topology
  and its complement is open.\<close>

definition
  IsClosed (infixl "{is closed in}" 90) where
  "D {is closed in} T \<equiv> (D \<subseteq> \<Union>T \<and> \<Union>T - D \<in> T)"

text\<open>To prove various properties of closure we will often use 
  the collection of  closed sets that contain a given set $A$. 
  Such collection does not have a separate
  name in informal math. We will call it \<open>ClosedCovers(A,T)\<close>. 
\<close>

definition
  "ClosedCovers(A,T) \<equiv> {D \<in> Pow(\<Union>T). D {is closed in} T \<and> A\<subseteq>D}"

text\<open>The closure of a set $A$ is defined as the intersection of the collection
  of closed sets that contain $A$.\<close>

definition
  "Closure(A,T) \<equiv> \<Inter> ClosedCovers(A,T)"

text\<open>We also define boundary  of a set as the intersection of 
  its closure with the closure of the complement (with respect to the 
  carrier).\<close>

definition
  "Boundary(A,T) \<equiv> Closure(A,T) \<inter> Closure(\<Union>T - A,T)"

text\<open>A set $K$ is compact if for every collection of open 
  sets that covers $K$ we can choose a finite one that still covers the set. 
  Recall that \<open>FinPow(M)\<close> is the collection of finite subsets of $M$ 
  (finite powerset of $M$), defined in IsarMathLib's \<open>Finite_ZF\<close>
  theory.\<close>

definition
  IsCompact (infixl "{is compact in}" 90) where
  "K {is compact in} T \<equiv> (K \<subseteq> \<Union>T \<and> 
  (\<forall> M\<in>Pow(T). K \<subseteq> \<Union>M \<longrightarrow> (\<exists> N \<in> FinPow(M). K \<subseteq> \<Union>N)))"

text\<open>A basic example of a topology: the powerset of any set is a topology.\<close>

lemma Pow_is_top: shows "Pow(X) {is a topology}"
proof -
  have "\<forall>A\<in>Pow(Pow(X)). \<Union>A \<in> Pow(X)" by fast
  moreover have "\<forall>U\<in>Pow(X). \<forall>V\<in>Pow(X). U\<inter>V \<in> Pow(X)" by fast
  ultimately show "Pow(X) {is a topology}" using IsATopology_def
    by auto
qed

text\<open>Empty set is open.\<close>

lemma empty_open: 
  assumes "T {is a topology}" shows "0 \<in> T"
proof -
  have "0 \<in> Pow(T)" by simp
  with assms have "\<Union>0 \<in> T" using IsATopology_def by blast
  thus "0 \<in> T" by simp
qed

text\<open>The carrier is open.\<close>
lemma carr_open: assumes "T {is a topology}" shows "(\<Union>T) \<in> T"
  using assms IsATopology_def by auto

text\<open>Union of a collection of open sets is open.\<close>
lemma union_open: assumes "T {is a topology}" and "\<forall>A\<in>\<A>. A \<in> T"
  shows "(\<Union>\<A>) \<in> T" using assms IsATopology_def by auto 

text\<open>Union of a indexed family of open sets is open.\<close>
lemma union_indexed_open: assumes A1: "T {is a topology}" and A2: "\<forall>i\<in>I. P(i) \<in> T"
  shows "(\<Union>i\<in>I. P(i)) \<in> T"  using assms union_open by simp

text\<open>The intersection of any nonempty collection of topologies on a set $X$ is a topology.\<close>
lemma Inter_tops_is_top: 
  assumes A1: "\<M> \<noteq> 0" and A2: "\<forall>T\<in>\<M>. T {is a topology}"
  shows "(\<Inter>\<M>) {is a topology}"
proof -
  { fix A assume "A\<in>Pow(\<Inter>\<M>)"
    with A1 have "\<forall>T\<in>\<M>. A\<in>Pow(T)" by auto
    with A1 A2 have "\<Union>A \<in> \<Inter>\<M>" using IsATopology_def
      by auto
  } then have "\<forall>A. A\<in>Pow(\<Inter>\<M>) \<longrightarrow> \<Union>A \<in> \<Inter>\<M>" by simp
  hence "\<forall>A\<in>Pow(\<Inter>\<M>). \<Union>A \<in> \<Inter>\<M>" by auto
  moreover
  { fix U V assume "U \<in> \<Inter>\<M>" and "V \<in> \<Inter>\<M>"
    then have "\<forall>T\<in>\<M>. U \<in> T \<and> V \<in> T" by auto
    with A1 A2 have "\<forall>T\<in>\<M>. U\<inter>V \<in> T" using IsATopology_def
      by simp
  } then have "\<forall> U \<in> \<Inter>\<M>. \<forall> V \<in> \<Inter>\<M>. U\<inter>V \<in> \<Inter>\<M>"
    by auto
  ultimately show "(\<Inter>\<M>) {is a topology}"
    using IsATopology_def by simp
qed

text\<open>We will now introduce some notation. In Isar, this is done by definining
  a "locale". Locale is kind of a context that holds some assumptions and 
  notation used in all theorems proven in it. In the locale (context)
  below called \<open>topology0\<close> we assume that $T$ is a topology.
  The interior of the set $A$ (with respect to the topology in the context)
  is denoted \<open>int(A)\<close>. The closure of a set $A\subseteq \bigcup T$ is 
  denoted \<open>cl(A)\<close> and the boundary is \<open>\<partial>A\<close>.\<close>

locale topology0 =
  fixes T
  assumes topSpaceAssum: "T {is a topology}"
  
  fixes int
  defines int_def [simp]: "int(A) \<equiv> Interior(A,T)"

  fixes cl
  defines cl_def [simp]: "cl(A) \<equiv> Closure(A,T)"

  fixes boundary ("\<partial>_" [91] 92)  
  defines boundary_def [simp]: "\<partial>A \<equiv> Boundary(A,T)"

text\<open>Intersection of a finite nonempty collection of open sets is open.\<close>

lemma (in topology0) fin_inter_open_open: assumes "N\<noteq>0" "N \<in> FinPow(T)"
  shows "\<Inter>N \<in> T"
  using topSpaceAssum assms IsATopology_def inter_two_inter_fin 
  by simp

text\<open>Having a topology $T$ and a set $X$ we can 
  define the induced topology 
  as the one consisting of the intersections of $X$ with sets from $T$.
  The notion of a collection restricted to a set is defined in ZF1.thy.\<close>

lemma (in topology0) Top_1_L4: 
  shows "(T {restricted to} X) {is a topology}"
proof -
  let ?S = "T {restricted to} X"
  have "\<forall>A\<in>Pow(?S). \<Union>A \<in> ?S"
  proof
    fix A assume A1: "A\<in>Pow(?S)"
    have "\<forall>V\<in>A. \<Union> {U \<in> T. V = U\<inter>X} \<in> T"
    proof -
      { fix V
	let ?M = "{U \<in> T. V = U\<inter>X}"
	have "?M \<in> Pow(T)" by auto
	with topSpaceAssum have "\<Union>?M \<in> T" using IsATopology_def by simp
      } thus ?thesis by simp
    qed
    hence "{\<Union>{U\<in>T. V = U\<inter>X}.V\<in> A} \<subseteq> T" by auto
    with topSpaceAssum have "(\<Union>V\<in>A. \<Union>{U\<in>T. V = U\<inter>X}) \<in> T"
      using IsATopology_def by auto
    then have "(\<Union>V\<in>A. \<Union>{U\<in>T. V = U\<inter>X})\<inter> X \<in> ?S"
      using RestrictedTo_def by auto
    moreover
    from A1 have "\<forall>V\<in>A. \<exists>U\<in>T. V = U\<inter>X"
      using RestrictedTo_def by auto
    hence "(\<Union>V\<in>A. \<Union>{U\<in>T. V = U\<inter>X})\<inter>X = \<Union>A" by blast
    ultimately show "\<Union>A \<in> ?S" by simp
  qed
  moreover have  "\<forall>U\<in>?S. \<forall>V\<in>?S. U\<inter>V \<in> ?S"
  proof -
    { fix U V assume "U\<in>?S"  "V\<in>?S"
      then obtain U\<^sub>1 V\<^sub>1 where 
	"U\<^sub>1 \<in> T \<and> U = U\<^sub>1\<inter>X" and "V\<^sub>1 \<in> T \<and> V = V\<^sub>1\<inter>X"
	using RestrictedTo_def by auto
      with topSpaceAssum have "U\<^sub>1\<inter>V\<^sub>1 \<in> T" and "U\<inter>V = (U\<^sub>1\<inter>V\<^sub>1)\<inter>X"
	using IsATopology_def by auto
      then have " U\<inter>V \<in> ?S" using RestrictedTo_def by auto
    } thus "\<forall>U\<in>?S. \<forall> V\<in>?S. U\<inter>V \<in> ?S"
      by simp
  qed
  ultimately show "?S {is a topology}" using IsATopology_def
    by simp
qed


subsection\<open>Interior of a set\<close>

text\<open>In this section we show basic properties of the interior of a set.\<close>

text\<open>Interior of a set $A$ is contained in $A$.\<close>

lemma (in topology0) Top_2_L1: shows "int(A) \<subseteq> A"
  using Interior_def by auto

text\<open>Interior is open.\<close>

lemma (in topology0) Top_2_L2: shows "int(A) \<in> T"
proof -
  have "{U\<in>T. U\<subseteq>A} \<in> Pow(T)" by auto
  with topSpaceAssum show "int(A) \<in> T" 
    using IsATopology_def Interior_def by auto
qed

text\<open>A set is open iff it is equal to its interior.\<close>

lemma (in topology0) Top_2_L3: shows "U\<in>T \<longleftrightarrow> int(U) = U"
proof
  assume "U\<in>T" then show "int(U) = U"
    using Interior_def by auto
next assume A1: "int(U) = U"
  have "int(U) \<in> T" using Top_2_L2 by simp
  with A1 show "U\<in>T" by simp
qed
  
text\<open>Interior of the interior is the interior.\<close>

lemma (in topology0) Top_2_L4: shows "int(int(A)) = int(A)"
proof -
  let ?U = "int(A)"
  from topSpaceAssum have "?U\<in>T" using Top_2_L2 by simp
  then show "int(int(A)) = int(A)" using Top_2_L3 by simp
qed

text\<open>Interior of a bigger set is bigger.\<close>

lemma (in topology0) interior_mono: 
  assumes A1: "A\<subseteq>B" shows "int(A) \<subseteq> int(B)"
proof -
  from A1 have "\<forall> U\<in>T. (U\<subseteq>A \<longrightarrow> U\<subseteq>B)" by auto
  then show "int(A) \<subseteq> int(B)" using Interior_def by auto
qed

text\<open>An open subset of any set is a subset of the interior of that set.\<close>

lemma (in topology0) Top_2_L5: assumes "U\<subseteq>A" and "U\<in>T"
  shows "U \<subseteq> int(A)"
  using assms Interior_def by auto

text\<open>If a point of a set has an open neighboorhood contained in the set,
  then the point belongs to the interior of the set.\<close>

lemma (in topology0) Top_2_L6:  assumes "\<exists>U\<in>T. (x\<in>U \<and> U\<subseteq>A)"
  shows "x \<in> int(A)"
  using assms Interior_def by auto

text\<open>A set is open iff its every point has a an open neighbourhood 
  contained in the set. We will formulate this statement as two lemmas
  (implication one way and the other way).
  The lemma below shows that if a set is open then every point has a 
  an open neighbourhood contained in the set.\<close>

lemma (in topology0) open_open_neigh: 
  assumes A1: "V\<in>T" 
  shows "\<forall>x\<in>V. \<exists>U\<in>T. (x\<in>U \<and> U\<subseteq>V)"
proof -
  from A1 have "\<forall>x\<in>V. V\<in>T \<and> x \<in> V \<and> V \<subseteq> V" by simp
  thus ?thesis by auto
qed

text\<open>If every point of a set has a an open neighbourhood 
  contained in the set then the set is open.\<close>

lemma (in topology0) open_neigh_open: 
  assumes A1: "\<forall>x\<in>V. \<exists>U\<in>T. (x\<in>U \<and> U\<subseteq>V)" 
  shows "V\<in>T"
proof -
  from A1 have "V = int(V)" using Top_2_L1 Top_2_L6 
    by blast
  then show "V\<in>T" using Top_2_L3 by simp
qed

text\<open>The intersection of interiors is a equal to the interior of intersections.\<close>

lemma (in topology0) int_inter_int: shows "int(A) \<inter> int(B) = int(A\<inter>B)"
proof
  have "int(A) \<inter> int(B) \<subseteq> A\<inter>B" using Top_2_L1 by auto  
  moreover have "int(A) \<inter> int(B) \<in> T" using Top_2_L2 IsATopology_def topSpaceAssum 
    by auto
  ultimately show "int(A) \<inter> int(B) \<subseteq> int(A\<inter>B)" using Top_2_L5 by simp
  have "A\<inter>B \<subseteq> A" and "A\<inter>B \<subseteq> B" by auto 
  then have "int(A\<inter>B) \<subseteq> int(A)" and "int(A\<inter>B) \<subseteq> int(B)" using interior_mono by auto
  thus "int(A\<inter>B) \<subseteq> int(A) \<inter> int(B)" by auto
qed 

subsection\<open>Closed sets, closure, boundary.\<close>

text\<open>This section is devoted to closed sets and properties 
  of the closure and boundary operators.\<close>


text\<open>The carrier of the space is closed.\<close>

lemma (in topology0) Top_3_L1: shows "(\<Union>T) {is closed in} T"
proof -
  have "\<Union>T - \<Union>T = 0" by auto
  with topSpaceAssum have "\<Union>T - \<Union>T \<in> T" using IsATopology_def by auto
  then show ?thesis using IsClosed_def by simp
qed

text\<open>Empty set is closed.\<close>

lemma (in topology0) Top_3_L2: shows "0 {is closed in} T"
  using topSpaceAssum  IsATopology_def IsClosed_def by simp

text\<open>The collection of closed covers of a subset of the carrier of topology
  is never empty. This is good to know, as we want to intersect this collection
  to get the closure.\<close>

lemma (in topology0) Top_3_L3: 
  assumes A1: "A \<subseteq> \<Union>T" shows "ClosedCovers(A,T) \<noteq> 0"
proof -
  from A1 have "\<Union>T \<in> ClosedCovers(A,T)" using ClosedCovers_def Top_3_L1
    by auto
  thus ?thesis by auto
qed

text\<open>Intersection of a nonempty family of closed sets is closed.\<close>

lemma (in topology0) Top_3_L4: assumes A1: "K\<noteq>0" and
  A2: "\<forall>D\<in>K. D {is closed in} T"
  shows "(\<Inter>K) {is closed in} T"
proof -
  from A2 have I: "\<forall>D\<in>K. (D \<subseteq> \<Union>T \<and> (\<Union>T - D)\<in> T)"
    using IsClosed_def by simp
  then have "{\<Union>T - D. D\<in> K} \<subseteq> T" by auto
  with topSpaceAssum have "(\<Union> {\<Union>T - D. D\<in> K}) \<in> T" 
    using IsATopology_def by auto
  moreover from A1 have "\<Union> {\<Union>T - D. D\<in> K} = \<Union>T - \<Inter>K" by fast
  moreover from A1 I have "\<Inter>K \<subseteq> \<Union>T" by blast
  ultimately show "(\<Inter>K) {is closed in} T" using  IsClosed_def 
    by simp
qed

text\<open>The union and intersection of two closed sets are closed.\<close>

lemma (in topology0) Top_3_L5:
  assumes A1: "D\<^sub>1 {is closed in} T"   "D\<^sub>2 {is closed in} T"
  shows 
  "(D\<^sub>1\<inter>D\<^sub>2) {is closed in} T"
  "(D\<^sub>1\<union>D\<^sub>2) {is closed in} T"
proof -
  have "{D\<^sub>1,D\<^sub>2} \<noteq> 0" by simp
  with A1 have "(\<Inter> {D\<^sub>1,D\<^sub>2}) {is closed in} T" using Top_3_L4
    by fast
  thus "(D\<^sub>1\<inter>D\<^sub>2) {is closed in} T" by simp
  from topSpaceAssum A1 have "(\<Union>T - D\<^sub>1) \<inter> (\<Union>T - D\<^sub>2) \<in> T"
    using IsClosed_def IsATopology_def by simp
  moreover have "(\<Union>T - D\<^sub>1) \<inter> (\<Union>T - D\<^sub>2) = \<Union>T - (D\<^sub>1 \<union> D\<^sub>2)" 
    by auto
  moreover from A1 have "D\<^sub>1 \<union> D\<^sub>2 \<subseteq> \<Union>T" using IsClosed_def
    by auto
  ultimately show "(D\<^sub>1\<union>D\<^sub>2) {is closed in} T" using IsClosed_def
    by simp
qed

text\<open>Finite union of closed sets is closed. To understand the proof 
  recall that $D\in$\<open>Pow(\<Union>T)\<close> means
  that $D$ is a subset of the carrier of the topology.\<close> 

lemma (in topology0) fin_union_cl_is_cl: 
  assumes 
  A1: "N \<in> FinPow({D\<in>Pow(\<Union>T). D {is closed in} T})"
  shows "(\<Union>N) {is closed in} T"
proof -
  let ?C = "{D\<in>Pow(\<Union>T). D {is closed in} T}"
  have "0\<in>?C" using Top_3_L2 by simp
  moreover have "\<forall>A\<in>?C. \<forall>B\<in>?C. A\<union>B \<in> ?C"
    using Top_3_L5 by auto
  moreover note A1
  ultimately have "\<Union>N \<in> ?C" by (rule union_two_union_fin)
  thus "(\<Union>N) {is closed in} T" by simp
qed

text\<open>Closure of a set is closed, hence the complement of the closure is open.\<close>

lemma (in topology0) cl_is_closed: assumes "A \<subseteq> \<Union>T"
  shows "cl(A) {is closed in} T" and "\<Union>T - cl(A) \<in> T"
  using assms Top_3_L3 Top_3_L4 Closure_def ClosedCovers_def IsClosed_def
  by auto

text\<open>Closure of a bigger sets is bigger.\<close>

lemma (in topology0) top_closure_mono: 
  assumes A1: "B \<subseteq> \<Union>T"  and A2:"A\<subseteq>B"
  shows "cl(A) \<subseteq> cl(B)"
proof -
  from A2 have "ClosedCovers(B,T)\<subseteq> ClosedCovers(A,T)" 
    using ClosedCovers_def by auto
  with A1 show ?thesis using Top_3_L3 Closure_def by auto
qed

text\<open>Boundary of a set is closed.\<close>

lemma (in topology0) boundary_closed: 
  assumes A1: "A \<subseteq> \<Union>T" shows "\<partial>A {is closed in} T"
proof -
  from A1 have "\<Union>T - A \<subseteq> \<Union>T" by fast
  with A1 show "\<partial>A {is closed in} T"
    using cl_is_closed Top_3_L5 Boundary_def by auto
qed

text\<open>A set is closed iff it is equal to its closure.\<close>

lemma (in topology0) Top_3_L8: assumes A1: "A \<subseteq> \<Union>T"
  shows "A {is closed in} T \<longleftrightarrow> cl(A) = A"
proof
  assume "A {is closed in} T"
  with A1 show "cl(A) = A"
    using Closure_def ClosedCovers_def by auto
next assume "cl(A) = A"
  then have "\<Union>T - A = \<Union>T - cl(A)" by simp
  with A1 show "A {is closed in} T" using cl_is_closed IsClosed_def
    by simp
qed

text\<open>Complement of an open set is closed.\<close>

lemma (in topology0) Top_3_L9: assumes A1: "A\<in>T" 
  shows "(\<Union>T - A) {is closed in} T"
proof -
  from topSpaceAssum A1 have "\<Union>T - (\<Union>T - A) = A" and "\<Union>T - A \<subseteq> \<Union>T"
    using IsATopology_def by auto
  with A1 show "(\<Union>T - A) {is closed in} T" using IsClosed_def by simp
qed

text\<open>A set is contained in its closure.\<close>

lemma (in topology0) cl_contains_set: assumes "A \<subseteq> \<Union>T" shows "A \<subseteq> cl(A)"
  using assms Top_3_L1 ClosedCovers_def Top_3_L3 Closure_def by auto

text\<open>Closure of a subset of the carrier is a subset of the carrier and closure
  of the complement is the complement of the interior.\<close>

lemma (in topology0) Top_3_L11: assumes A1: "A \<subseteq> \<Union>T" 
  shows 
  "cl(A) \<subseteq> \<Union>T"
  "cl(\<Union>T - A) = \<Union>T - int(A)"
proof -
  from A1 show "cl(A) \<subseteq> \<Union>T" using Top_3_L1 Closure_def ClosedCovers_def
    by auto
  from A1 have "\<Union>T - A \<subseteq> \<Union>T - int(A)" using Top_2_L1
    by auto
  moreover have I: "\<Union>T - int(A) \<subseteq> \<Union>T"   "\<Union>T - A \<subseteq> \<Union>T" by auto
  ultimately have "cl(\<Union>T - A) \<subseteq> cl(\<Union>T - int(A))"
    using top_closure_mono by simp
  moreover
  from I have "(\<Union>T - int(A)) {is closed in} T"
    using Top_2_L2 Top_3_L9 by simp
  with I have "cl((\<Union>T) - int(A)) = \<Union>T - int(A)"
    using Top_3_L8 by simp
  ultimately have "cl(\<Union>T - A) \<subseteq> \<Union>T - int(A)" by simp
  moreover
  from I have "\<Union>T - A \<subseteq> cl(\<Union>T - A)" using cl_contains_set by simp
  hence "\<Union>T - cl(\<Union>T - A) \<subseteq> A" and "\<Union>T - A \<subseteq> \<Union>T"  by auto
  then have "\<Union>T - cl(\<Union>T - A) \<subseteq> int(A)"
    using cl_is_closed IsClosed_def Top_2_L5 by simp
  hence "\<Union>T - int(A) \<subseteq>  cl(\<Union>T - A)" by auto
  ultimately show "cl(\<Union>T - A) = \<Union>T - int(A)" by auto
qed
 
text\<open>Boundary of a set is the closure of the set 
  minus the interior of the set.\<close>

lemma (in topology0) Top_3_L12: assumes A1: "A \<subseteq> \<Union>T"
  shows "\<partial>A = cl(A) - int(A)"
proof -
  from A1 have "\<partial>A = cl(A) \<inter> (\<Union>T - int(A))" 
    using Boundary_def Top_3_L11 by simp
  moreover from A1 have 
    "cl(A) \<inter> (\<Union>T - int(A)) = cl(A) - int(A)" 
    using Top_3_L11 by blast
  ultimately show "\<partial>A = cl(A) - int(A)" by simp
qed

text\<open>If a set $A$ is contained in a closed set $B$, then the closure of $A$ 
  is contained in $B$.\<close>

lemma (in topology0) Top_3_L13: 
  assumes A1: "B {is closed in} T"   "A\<subseteq>B"
  shows "cl(A) \<subseteq> B"
proof -
  from A1 have "B \<subseteq> \<Union>T" using IsClosed_def by simp 
  with A1 show "cl(A) \<subseteq> B" using ClosedCovers_def Closure_def by auto
qed

(*text{*If two open sets are disjoint, then we can close one of them
  and they will still be disjoint.*}

lemma (in topology0) open_disj_cl_disj:
  assumes A1: "U\<in>T"  "V\<in>T" and  A2: "U\<inter>V = 0"
  shows "cl(U) \<inter> V = 0"
proof -
  from topSpaceAssum A1 have I: "U \<subseteq> \<Union>T" using IsATopology_def
    by auto
  with A2 have  "U \<subseteq> \<Union>T - V" by auto
  moreover from A1 have "(\<Union>T - V) {is closed in} T" using Top_3_L9 
    by simp
  ultimately have "cl(U) - (\<Union>T - V) = 0" 
    using Top_3_L13 by blast
  moreover 
  from I have "cl(U) \<subseteq> \<Union>T" using cl_is_closed IsClosed_def by simp
  then have "cl(U) -(\<Union>T - V) = cl(U) \<inter> V" by auto
  ultimately show "cl(U) \<inter> V = 0" by simp
qed;*)

text\<open>If a set is disjoint with an open set, then we can close it
  and it will still be disjoint.\<close>

lemma (in topology0) disj_open_cl_disj:
  assumes A1: "A \<subseteq> \<Union>T"  "V\<in>T" and  A2: "A\<inter>V = 0"
  shows "cl(A) \<inter> V = 0"
proof -
  from assms have "A \<subseteq> \<Union>T - V" by auto
  moreover from A1 have "(\<Union>T - V) {is closed in} T" using Top_3_L9 by simp
  ultimately have "cl(A) - (\<Union>T - V) = 0" 
    using Top_3_L13 by blast
  moreover from A1 have "cl(A) \<subseteq> \<Union>T" using cl_is_closed IsClosed_def by simp
  then have "cl(A) -(\<Union>T - V) = cl(A) \<inter> V" by auto
  ultimately show ?thesis by simp
qed

text\<open>A reformulation of \<open>disj_open_cl_disj\<close>:
  If a point belongs to the closure of a set, then we can find a point
  from the set in any open neighboorhood of the point.\<close>

lemma (in topology0) cl_inter_neigh:
  assumes "A \<subseteq> \<Union>T" and "U\<in>T" and "x \<in> cl(A) \<inter> U"
  shows "A\<inter>U \<noteq> 0" using assms disj_open_cl_disj by auto

text\<open>A reverse of  \<open>cl_inter_neigh\<close>: if every open neiboorhood of a point
  has a nonempty intersection with a set, then that point belongs to the closure
  of the set.\<close>

lemma (in topology0) inter_neigh_cl:
  assumes A1: "A \<subseteq> \<Union>T" and A2: "x\<in>\<Union>T" and A3: "\<forall>U\<in>T. x\<in>U \<longrightarrow> U\<inter>A \<noteq> 0"
  shows "x \<in> cl(A)"
proof -
  { assume "x \<notin> cl(A)"
    with A1 obtain D where "D {is closed in} T" and "A\<subseteq>D" and "x\<notin>D"
      using Top_3_L3 Closure_def ClosedCovers_def by auto
    let ?U = "(\<Union>T) - D"
    from A2 \<open>D {is closed in} T\<close> \<open>x\<notin>D\<close> \<open>A\<subseteq>D\<close> have "?U\<in>T" "x\<in>?U" and "?U\<inter>A = 0"
      unfolding IsClosed_def by auto
    with A3 have False by auto
  } thus ?thesis by auto
qed

end
