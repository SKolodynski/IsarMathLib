(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2005 - 2008  Slawomir Kolodynski

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
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open>Topology 1\<close>

theory Topology_ZF_1 imports Topology_ZF

begin

text\<open>In this theory file we study separation axioms and the notion of base and
  subbase. Using the products of open sets as a subbase we define a natural
  topology on a product of two topological spaces.\<close>

subsection\<open>Separation axioms.\<close>

text\<open>Topological spaces cas be classified according to certain properties
  called "separation axioms". In this section we define what it means that a 
  topological space is $T_0$, $T_1$ or $T_2$.\<close>

text\<open>A topology on $X$ is $T_0$ if for every pair of distinct points of $X$
  there is an open set that contains only one of them.\<close>

definition
  isT0 ("_ {is T\<^sub>0}" [90] 91) where
  "T {is T\<^sub>0} \<equiv> \<forall> x y. ((x \<in> \<Union>T \<and> y \<in> \<Union>T \<and>  x\<noteq>y) \<longrightarrow> 
  (\<exists>U\<in>T. (x\<in>U \<and> y\<notin>U) \<or> (y\<in>U \<and> x\<notin>U)))"

text\<open>A topology is $T_1$ if for every such pair there exist an open set that 
  contains the first point but not the second.\<close>

definition
  isT1 ("_ {is T\<^sub>1}" [90] 91) where
  "T {is T\<^sub>1} \<equiv> \<forall> x y. ((x \<in> \<Union>T \<and> y \<in> \<Union>T \<and>  x\<noteq>y) \<longrightarrow> 
  (\<exists>U\<in>T. (x\<in>U \<and> y\<notin>U)))"

text\<open>A topology is $T_2$ (Hausdorff) if for every pair of points there exist a 
  pair of disjoint open sets each containing one of the points. 
  This is an important class of topological spaces. In particular, metric 
  spaces are Hausdorff.\<close>

definition
  isT2 ("_ {is T\<^sub>2}" [90] 91) where
  "T {is T\<^sub>2} \<equiv> \<forall> x y. ((x \<in> \<Union>T \<and> y \<in> \<Union>T \<and>  x\<noteq>y) \<longrightarrow>
  (\<exists>U\<in>T. \<exists>V\<in>T. x\<in>U \<and> y\<in>V \<and> U\<inter>V=0))"

text\<open>If a topology is $T_1$ then it is $T_0$. 
  We don't really assume here that $T$ is a topology on $X$. 
  Instead, we prove the relation between isT0 condition and isT1.\<close>

lemma T1_is_T0: assumes A1: "T {is T\<^sub>1}" shows "T {is T\<^sub>0}"
proof -
  from A1 have "\<forall> x y. x \<in> \<Union>T \<and> y \<in> \<Union>T \<and> x\<noteq>y \<longrightarrow> 
    (\<exists>U\<in>T. x\<in>U \<and> y\<notin>U)"
    using isT1_def by simp
  then have "\<forall> x y. x \<in> \<Union>T \<and> y \<in> \<Union>T \<and> x\<noteq>y \<longrightarrow> 
    (\<exists>U\<in>T. x\<in>U \<and> y\<notin>U \<or> y\<in>U \<and> x\<notin>U)"
    by auto
  then show "T {is T\<^sub>0}" using isT0_def by simp
qed

text\<open>If a topology is $T_2$ then it is $T_1$.\<close>

lemma T2_is_T1: assumes A1: "T {is T\<^sub>2}" shows "T {is T\<^sub>1}"
proof -
  { fix x y assume "x \<in> \<Union>T"  "y \<in> \<Union>T"  "x\<noteq>y"
    with A1 have "\<exists>U\<in>T. \<exists>V\<in>T. x\<in>U \<and> y\<in>V \<and> U\<inter>V=0"
      using isT2_def by auto
    then have "\<exists>U\<in>T. x\<in>U \<and> y\<notin>U" by auto
  } then have "\<forall> x y. x \<in> \<Union>T \<and> y \<in> \<Union>T \<and>  x\<noteq>y \<longrightarrow> 
      (\<exists>U\<in>T. x\<in>U \<and> y\<notin>U)" by simp
  then show "T {is T\<^sub>1}" using isT1_def by simp
qed

text\<open>In a $T_0$ space two points that can not be separated 
  by an open set are equal. Proof by contradiction.\<close>

lemma Top_1_1_L1: assumes A1: "T {is T\<^sub>0}" and A2: "x \<in> \<Union>T"  "y \<in> \<Union>T"
  and A3: "\<forall>U\<in>T. (x\<in>U \<longleftrightarrow> y\<in>U)" 
  shows "x=y"
proof -
  { assume "x\<noteq>y"
    with A1 A2 have "\<exists>U\<in>T. x\<in>U \<and> y\<notin>U \<or> y\<in>U \<and> x\<notin>U"
      using isT0_def by simp
    with A3 have False by auto
  } then show "x=y" by auto
qed

subsection\<open>Bases and subbases.\<close>

text\<open>Sometimes it is convenient to talk about topologies in terms of their bases
  and subbases. These are certain collections of open sets that define
  the whole topology.\<close>

text\<open>A base of topology is a collection of open sets such that every 
  open set is a union of the sets from the base.\<close>

definition
  IsAbaseFor (infixl "{is a base for}" 65) where 
  "B {is a base for} T \<equiv> B\<subseteq>T \<and> T = {\<Union>A. A\<in>Pow(B)}"

text\<open>A subbase is a collection 
  of open sets such that finite intersection of those sets form a base.\<close>

definition
  IsAsubBaseFor (infixl "{is a subbase for}" 65) where
  "B {is a subbase for} T \<equiv> 
  B \<subseteq> T \<and> {\<Inter>A. A \<in> FinPow(B)} {is a base for} T"

text\<open>Below we formulate a condition that we will prove to be necessary and 
  sufficient for a collection $B$ of open sets to form a base. 
  It says that for any two sets $U,V$ from the collection $B$ we can
  find a point $x\in U\cap V$ with a neighboorhod 
  from $B$ contained in $U\cap V$.\<close>

definition
  SatisfiesBaseCondition ("_ {satisfies the base condition}" [50] 50)
  where
  "B {satisfies the base condition} \<equiv> 
  \<forall>U V. ((U\<in>B \<and> V\<in>B) \<longrightarrow> (\<forall>x \<in> U\<inter>V. \<exists>W\<in>B. x\<in>W \<and> W \<subseteq> U\<inter>V))"

text\<open>A collection that is closed with respect to intersection
  satisfies the base condition.\<close>

lemma inter_closed_base: assumes "\<forall>U\<in>B.(\<forall>V\<in>B. U\<inter>V \<in> B)"
  shows  "B {satisfies the base condition}" 
proof -
    { fix U V x assume "U\<in>B" and "V\<in>B" and "x \<in> U\<inter>V"
      with assms have "\<exists>W\<in>B. x\<in>W \<and> W \<subseteq> U\<inter>V" by blast
    } then show ?thesis using SatisfiesBaseCondition_def by simp
qed

text\<open>Each open set is a union of some sets from the base.\<close>

lemma Top_1_2_L1: assumes "B {is a base for} T"  and "U\<in>T" 
  shows "\<exists>A\<in>Pow(B). U = \<Union>A"
  using assms IsAbaseFor_def by simp

text\<open>Elements of base are open.\<close>

lemma base_sets_open: 
  assumes "B {is a base for} T" and "U \<in> B"
  shows "U \<in> T"
  using assms IsAbaseFor_def by auto

text\<open>A base defines topology uniquely.\<close>

lemma same_base_same_top: 
  assumes "B {is a base for} T" and "B {is a base for} S" 
  shows "T = S"
  using assms IsAbaseFor_def by simp

text\<open>Every point from an open set has a neighboorhood from the base
  that is contained in the set.\<close>

lemma point_open_base_neigh: 
  assumes A1: "B {is a base for} T" and A2: "U\<in>T" and A3: "x\<in>U"
  shows "\<exists>V\<in>B. V\<subseteq>U \<and> x\<in>V"
proof -
  from A1 A2 obtain A where "A \<in> Pow(B)" and "U = \<Union>A"
    using Top_1_2_L1 by blast
  with A3 obtain V where "V\<in>A" and "x\<in>V" by auto
  with \<open>A \<in> Pow(B)\<close> \<open>U = \<Union>A\<close> show ?thesis by auto
qed

text\<open>A criterion for a collection to be a base for a topology
  that is a slight reformulation of the definition. The only thing
  different that in the definition is that we assume only that
  every open set is a union of some sets from the base. The definition
  requires also the opposite inclusion that every union of the 
  sets from the base is open, but that we can prove if we assume that
  $T$ is a topology.\<close>

lemma is_a_base_criterion: assumes A1: "T {is a topology}"
  and A2: "B \<subseteq> T" and A3: "\<forall>V \<in> T. \<exists>A \<in> Pow(B). V = \<Union>A"
  shows "B {is a base for} T"
proof -
  from A3 have "T \<subseteq> {\<Union>A. A\<in>Pow(B)}" by auto
  moreover have "{\<Union>A. A\<in>Pow(B)} \<subseteq> T"
  proof
    fix U assume "U \<in> {\<Union>A. A\<in>Pow(B)}"
    then obtain A where "A \<in> Pow(B)" and "U = \<Union>A"
      by auto
    with \<open>B \<subseteq> T\<close> have "A \<in> Pow(T)" by auto
    with A1 \<open>U = \<Union>A\<close> show "U \<in> T"
      unfolding IsATopology_def by simp
  qed
  ultimately have "T = {\<Union>A. A\<in>Pow(B)}" by auto
  with A2 show "B {is a base for} T" 
    unfolding IsAbaseFor_def by simp
qed
    
text\<open>A necessary condition for a collection of sets to be a base for some 
  topology : every point in the intersection
  of two sets in the base has a neighboorhood from the base contained
  in the intersection.\<close>

lemma Top_1_2_L2: 
  assumes A1:"\<exists>T. T {is a topology} \<and> B {is a base for} T"
  and A2: "V\<in>B"  "W\<in>B"
  shows "\<forall> x \<in> V\<inter>W. \<exists>U\<in>B. x\<in>U \<and> U \<subseteq> V \<inter> W"
proof -
  from A1 obtain T where 
    D1: "T {is a topology}"   "B {is a base for} T"
    by auto
  then have "B \<subseteq> T" using IsAbaseFor_def by auto
  with A2 have "V\<in>T" and "W\<in>T" using IsAbaseFor_def by auto
  with D1 have "\<exists>A\<in>Pow(B). V\<inter>W = \<Union>A" using IsATopology_def Top_1_2_L1
    by auto
  then obtain A where "A \<subseteq> B" and "V \<inter> W = \<Union>A" by auto
  then show "\<forall> x \<in> V\<inter>W. \<exists>U\<in>B. (x\<in>U \<and> U \<subseteq> V \<inter> W)" by auto
qed

text\<open>We will construct a topology as the collection of unions of (would-be)
  base. First we prove that if the collection of sets satisfies the 
  condition we want to show to be sufficient, the the intersection belongs
  to what we will define as topology (am I clear here?). Having this fact 
  ready simplifies the proof of the next lemma. There is not much topology
  here, just some set theory.\<close>

lemma Top_1_2_L3:
  assumes A1: "\<forall>x\<in> V\<inter>W . \<exists>U\<in>B. x\<in>U \<and> U \<subseteq> V\<inter>W"
  shows "V\<inter>W \<in> {\<Union>A. A\<in>Pow(B)}"
proof
  let ?A = "\<Union>x\<in>V\<inter>W. {U\<in>B. x\<in>U \<and> U \<subseteq> V\<inter>W}"
  show "?A\<in>Pow(B)" by auto
  from A1 show "V\<inter>W = \<Union>?A" by blast
qed

text\<open>The next lemma is needed when proving that the would-be topology is
  closed with respect to taking intersections. We show here that intersection
  of two sets from this (would-be) topology can be written as union of sets 
  from the topology.\<close>

lemma Top_1_2_L4:
  assumes A1:  "U\<^sub>1 \<in> {\<Union>A. A\<in>Pow(B)}"   "U\<^sub>2 \<in> {\<Union>A. A\<in>Pow(B)}"
  and A2: "B {satisfies the base condition}"
  shows "\<exists>C. C \<subseteq> {\<Union>A. A\<in>Pow(B)} \<and> U\<^sub>1\<inter>U\<^sub>2 = \<Union>C"
proof -
  from A1 A2 obtain A\<^sub>1 A\<^sub>2 where 
    D1: "A\<^sub>1\<in> Pow(B)"  "U\<^sub>1 = \<Union>A\<^sub>1"  "A\<^sub>2 \<in> Pow(B)"  "U\<^sub>2 = \<Union>A\<^sub>2" 
    by auto
  let ?C = "\<Union>U\<in>A\<^sub>1.{U\<inter>V. V\<in>A\<^sub>2}"
  from D1 have "(\<forall>U\<in>A\<^sub>1. U\<in>B) \<and> (\<forall>V\<in>A\<^sub>2. V\<in>B)" by auto
  with A2 have "?C \<subseteq> {\<Union>A . A \<in> Pow(B)}"
    using Top_1_2_L3 SatisfiesBaseCondition_def by auto
  moreover from D1 have "U\<^sub>1 \<inter> U\<^sub>2 = \<Union>?C" by auto
  ultimately show ?thesis by auto
qed

text\<open>If $B$ satisfies the base condition, then the collection of unions
  of sets from $B$ is a topology and $B$ is a base for this topology.\<close>

theorem Top_1_2_T1:
  assumes A1: "B {satisfies the base condition}"
  and A2: "T = {\<Union>A. A\<in>Pow(B)}"
  shows "T {is a topology}" and "B {is a base for} T"
proof -
  show "T {is a topology}"
  proof -
    have I: "\<forall>C\<in>Pow(T). \<Union>C \<in> T"
    proof -
      { fix C assume A3: "C \<in> Pow(T)"
        let ?Q = "\<Union> {\<Union>{A\<in>Pow(B). U = \<Union>A}. U\<in>C}"
        from A2 A3 have "\<forall>U\<in>C. \<exists>A\<in>Pow(B). U = \<Union>A" by auto
        then have "\<Union>?Q = \<Union>C" using ZF1_1_L10 by simp
        moreover from A2 have "\<Union>?Q \<in> T" by auto
        ultimately have "\<Union>C \<in> T" by simp
      } thus "\<forall>C\<in>Pow(T). \<Union>C \<in> T" by auto
    qed
    moreover have "\<forall>U\<in>T. \<forall> V\<in>T. U\<inter>V \<in> T"
    proof -
      { fix U V assume  "U \<in> T"  "V \<in> T"
        with A1 A2 have "\<exists>C.(C \<subseteq> T \<and> U\<inter>V = \<Union>C)"
        using Top_1_2_L4 by simp
        then obtain C where "C \<subseteq> T" and  "U\<inter>V = \<Union>C"
          by auto
          with I have "U\<inter>V \<in> T" by simp
      } then show "\<forall>U\<in>T. \<forall> V\<in>T. U\<inter>V \<in> T" by simp
    qed
    ultimately show "T {is a topology}" using IsATopology_def
      by simp
  qed
  from A2 have "B\<subseteq>T" by auto
  with A2 show "B {is a base for} T" using IsAbaseFor_def 
    by simp
qed

text\<open>The carrier of the base and topology are the same.\<close>

lemma Top_1_2_L5: assumes "B {is a base for} T"
  shows "\<Union>T = \<Union>B"
  using assms IsAbaseFor_def by auto

text\<open>If $B$ is a base for $T$, then $T$ is the smallest topology containing $B$.
\<close>

lemma base_smallest_top: 
  assumes A1: "B {is a base for} T" and  A2: "S {is a topology}" and A3: "B\<subseteq>S"
  shows "T\<subseteq>S"
proof
  fix U assume "U\<in>T"
  with A1 obtain B\<^sub>U where "B\<^sub>U \<subseteq> B" and "U = \<Union>B\<^sub>U" using IsAbaseFor_def by auto
  with A3 have "B\<^sub>U \<subseteq> S" by auto 
  with A2 \<open>U = \<Union>B\<^sub>U\<close> show "U\<in>S" using IsATopology_def by simp
qed

text\<open>If $B$ is a base for $T$ and $B$ is a topology, then $B=T$.\<close>

lemma base_topology: assumes "B {is a topology}" and "B {is a base for} T"
  shows "B=T" using assms base_sets_open base_smallest_top by blast 

subsection\<open>Product topology\<close>

text\<open>In this section we consider a topology defined on a product of two sets.\<close>

text\<open>Given two topological spaces we can define a topology on the product of 
  the carriers such that the cartesian products of the sets of the topologies 
  are a base for the product topology. Recall that for two collections $S,T$ 
  of sets the product collection
  is defined (in \<open>ZF1.thy\<close>) as the collections of cartesian 
  products $A\times B$, where $A\in S, B\in T$.\<close>

definition
  "ProductTopology(T,S) \<equiv> {\<Union>W. W \<in> Pow(ProductCollection(T,S))}"

text\<open>The product collection satisfies the base condition.\<close>

lemma Top_1_4_L1: 
  assumes A1: "T {is a topology}"   "S {is a topology}"
  and A2: "A \<in> ProductCollection(T,S)"  "B \<in> ProductCollection(T,S)"
  shows "\<forall>x\<in>(A\<inter>B). \<exists>W\<in>ProductCollection(T,S). (x\<in>W \<and> W \<subseteq> A \<inter> B)"
proof
  fix x assume A3: "x \<in> A\<inter>B"
  from A2 obtain U\<^sub>1 V\<^sub>1 U\<^sub>2 V\<^sub>2 where 
    D1: "U\<^sub>1\<in>T"  "V\<^sub>1\<in>S"   "A=U\<^sub>1\<times>V\<^sub>1"  "U\<^sub>2\<in>T"  "V\<^sub>2\<in>S"   "B=U\<^sub>2\<times>V\<^sub>2"
    using ProductCollection_def by auto
  let ?W = "(U\<^sub>1\<inter>U\<^sub>2) \<times> (V\<^sub>1\<inter>V\<^sub>2)"
  from A1 D1 have "U\<^sub>1\<inter>U\<^sub>2 \<in> T" and "V\<^sub>1\<inter>V\<^sub>2 \<in> S"
    using IsATopology_def by auto
  then have "?W \<in> ProductCollection(T,S)" using ProductCollection_def 
    by auto
  moreover from A3 D1 have "x\<in>?W" and "?W \<subseteq> A\<inter>B" by auto
  ultimately have "\<exists>W. (W \<in> ProductCollection(T,S) \<and> x\<in>W \<and> W \<subseteq> A\<inter>B)"
    by auto
  thus "\<exists>W\<in>ProductCollection(T,S). (x\<in>W \<and> W \<subseteq> A \<inter> B)" by auto
qed

text\<open>The product topology is indeed a topology on the product.\<close>

theorem Top_1_4_T1: assumes A1: "T {is a topology}"  "S {is a topology}"
  shows 
  "ProductTopology(T,S) {is a topology}"
  "ProductCollection(T,S) {is a base for} ProductTopology(T,S)"
  "\<Union> ProductTopology(T,S) = \<Union>T \<times> \<Union>S"
proof -
  from A1 show 
    "ProductTopology(T,S) {is a topology}"
    "ProductCollection(T,S) {is a base for} ProductTopology(T,S)"
    using Top_1_4_L1 ProductCollection_def 
      SatisfiesBaseCondition_def ProductTopology_def Top_1_2_T1 
    by auto
  then show "\<Union> ProductTopology(T,S) = \<Union>T \<times> \<Union>S"
    using Top_1_2_L5 ZF1_1_L6 by simp
qed

text\<open>Each point of a set open in the product topology has a neighborhood
  which is a cartesian product of open sets.\<close>

lemma prod_top_point_neighb: 
  assumes A1: "T {is a topology}"  "S {is a topology}" and 
  A2: "U \<in> ProductTopology(T,S)" and A3: "x \<in> U"
  shows "\<exists>V W. V\<in>T \<and> W\<in>S \<and> V\<times>W \<subseteq> U \<and> x \<in> V\<times>W"
proof -
  from A1 have 
    "ProductCollection(T,S) {is a base for} ProductTopology(T,S)"
    using Top_1_4_T1 by simp
  with A2 A3 obtain Z where 
    "Z \<in> ProductCollection(T,S)" and "Z \<subseteq> U \<and> x\<in>Z"
    using point_open_base_neigh by blast
  then obtain V W where "V \<in> T" and "W\<in>S" and" V\<times>W \<subseteq> U \<and> x \<in> V\<times>W"
    using ProductCollection_def by auto
  thus ?thesis by auto
qed

text\<open>Products of open sets are open in the product topology.\<close>

lemma prod_open_open_prod: 
  assumes A1: "T {is a topology}"  "S {is a topology}" and
  A2: "U\<in>T" "V\<in>S"
  shows "U\<times>V \<in> ProductTopology(T,S)"
proof -
  from A1 have 
    "ProductCollection(T,S) {is a base for} ProductTopology(T,S)"
    using Top_1_4_T1 by simp
  moreover from A2 have "U\<times>V \<in> ProductCollection(T,S)"
    unfolding ProductCollection_def by auto
  ultimately show "U\<times>V \<in> ProductTopology(T,S)"
    using base_sets_open by simp
qed

text\<open>Sets that are open in th product topology are contained in the product
  of the carrier.\<close>

lemma prod_open_type: assumes A1: "T {is a topology}"  "S {is a topology}" and
  A2: "V \<in> ProductTopology(T,S)"
  shows "V \<subseteq> \<Union>T \<times> \<Union>S"
proof -
  from A2 have "V \<subseteq> \<Union> ProductTopology(T,S)" by auto
  with A1 show ?thesis using Top_1_4_T1 by simp
qed

text\<open>Suppose we have subsets $A\subseteq X, B\subseteq Y$, where
  $X,Y$ are topological spaces with topologies $T,S$. We can the consider
  relative topologies on $T_A, S_B$ on sets $A,B$ and the collection
  of cartesian products of sets open in $T_A, S_B$, (namely 
  $\{U\times V: U\in T_A, V\in S_B\}$. The next lemma states that
  this collection is a base of the product topology on $X\times Y$
  restricted to the product $A\times B$.
\<close>

lemma prod_restr_base_restr:
  assumes A1: "T {is a topology}"  "S {is a topology}"
  shows 
  "ProductCollection(T {restricted to} A, S {restricted to} B)
  {is a base for} (ProductTopology(T,S) {restricted to} A\<times>B)"
proof -
  let ?\<B> = "ProductCollection(T {restricted to} A, S {restricted to} B)"
  let ?\<tau> = "ProductTopology(T,S)"
  from A1 have "(?\<tau> {restricted to} A\<times>B) {is a topology}"
    using Top_1_4_T1 topology0_def topology0.Top_1_L4
    by simp
  moreover have "?\<B> \<subseteq> (?\<tau> {restricted to} A\<times>B)"
  proof
    fix U assume "U \<in> ?\<B>"
    then obtain U\<^sub>A U\<^sub>B where "U = U\<^sub>A \<times> U\<^sub>B" and
      "U\<^sub>A \<in> (T {restricted to} A)" and "U\<^sub>B \<in> (S {restricted to} B)"
      using ProductCollection_def by auto
    then obtain W\<^sub>A W\<^sub>B where 
      "W\<^sub>A \<in> T"  "U\<^sub>A = W\<^sub>A \<inter> A" and "W\<^sub>B \<in> S"  "U\<^sub>B = W\<^sub>B \<inter> B"
      using RestrictedTo_def by auto
    with \<open>U = U\<^sub>A \<times> U\<^sub>B\<close> have "U = W\<^sub>A\<times>W\<^sub>B \<inter> (A\<times>B)" by auto
    moreover from A1 \<open>W\<^sub>A \<in> T\<close> and \<open>W\<^sub>B \<in> S\<close> have "W\<^sub>A\<times>W\<^sub>B \<in> ?\<tau>"
      using prod_open_open_prod by simp
    ultimately show "U \<in> ?\<tau> {restricted to} A\<times>B"
      using RestrictedTo_def by auto
  qed
  moreover have "\<forall>U \<in> ?\<tau> {restricted to} A\<times>B.
    \<exists>C \<in> Pow(?\<B>). U = \<Union>C"
  proof
    fix U assume "U \<in> ?\<tau> {restricted to} A\<times>B"
    then obtain W where "W \<in> ?\<tau>" and "U = W \<inter> (A\<times>B)"
      using RestrictedTo_def by auto
    from A1 \<open>W \<in> ?\<tau>\<close> obtain A\<^sub>W  where 
      "A\<^sub>W \<in> Pow(ProductCollection(T,S))" and "W = \<Union>A\<^sub>W"
       using Top_1_4_T1 IsAbaseFor_def by auto
    let ?C = "{V \<inter> A\<times>B. V \<in> A\<^sub>W}" 
    have "?C \<in> Pow(?\<B>)" and "U = \<Union>?C"
    proof -
      { fix R assume "R \<in> ?C"
	then obtain V where "V \<in> A\<^sub>W" and "R = V \<inter> A\<times>B"
	  by auto
	with \<open>A\<^sub>W \<in> Pow(ProductCollection(T,S))\<close> obtain V\<^sub>T V\<^sub>S where 
	  "V\<^sub>T \<in> T" and "V\<^sub>S \<in> S" and "V = V\<^sub>T \<times> V\<^sub>S"
	  using ProductCollection_def by auto
	with \<open>R = V \<inter> A\<times>B\<close> have "R \<in> ?\<B>"
	  using ProductCollection_def RestrictedTo_def
	  by auto
      } then show "?C \<in> Pow(?\<B>)" by auto
      from \<open>U = W \<inter> (A\<times>B)\<close> and \<open>W = \<Union>A\<^sub>W\<close>
      show "U = \<Union>?C" by auto
    qed
    thus "\<exists>C \<in> Pow(?\<B>). U = \<Union>C" by blast
  qed
  ultimately show ?thesis by (rule is_a_base_criterion)
qed
    
text\<open>We can commute taking restriction (relative topology) and
  product topology. The reason the two topologies are the same is
  that they have the same base.\<close>

lemma prod_top_restr_comm: 
  assumes A1: "T {is a topology}"  "S {is a topology}"
  shows
  "ProductTopology(T {restricted to} A,S {restricted to} B) =
  ProductTopology(T,S) {restricted to} (A\<times>B)"
proof -
  let ?\<B> = "ProductCollection(T {restricted to} A, S {restricted to} B)"
  from A1 have
    "?\<B> {is a base for} ProductTopology(T {restricted to} A,S {restricted to} B)"
    using topology0_def topology0.Top_1_L4 Top_1_4_T1 by simp
  moreover from A1 have 
    "?\<B> {is a base for} ProductTopology(T,S) {restricted to} (A\<times>B)"
    using prod_restr_base_restr by simp
  ultimately show ?thesis by (rule same_base_same_top)
qed

text\<open>Projection of a section of an open set is open.\<close>

lemma prod_sec_open1: assumes A1: "T {is a topology}"  "S {is a topology}" and
  A2: "V \<in> ProductTopology(T,S)" and A3: "x \<in> \<Union>T"
  shows "{y \<in> \<Union>S. \<langle>x,y\<rangle> \<in> V} \<in> S"
proof -
  let ?A = "{y \<in> \<Union>S. \<langle>x,y\<rangle> \<in> V}"
  from A1 have "topology0(S)" using topology0_def by simp
  moreover have "\<forall>y\<in>?A.\<exists>W\<in>S. (y\<in>W \<and> W\<subseteq>?A)"
    proof
      fix y assume "y \<in> ?A"
      then have "\<langle>x,y\<rangle> \<in> V" by simp
      with A1 A2 have "\<langle>x,y\<rangle> \<in> \<Union>T \<times> \<Union>S" using prod_open_type by blast
      hence "x \<in> \<Union>T" and "y \<in> \<Union>S" by auto
      from A1 A2 \<open>\<langle>x,y\<rangle> \<in> V\<close> have "\<exists>U W. U\<in>T \<and> W\<in>S \<and> U\<times>W \<subseteq> V \<and> \<langle>x,y\<rangle> \<in> U\<times>W"
        by (rule prod_top_point_neighb)
      then obtain U W where  "U\<in>T" "W\<in>S" "U\<times>W \<subseteq> V" "\<langle>x,y\<rangle> \<in> U\<times>W"
        by auto
      with A1 A2 show "\<exists>W\<in>S. (y\<in>W \<and> W\<subseteq>?A)" using prod_open_type section_proj
        by auto
    qed
  ultimately show ?thesis by (rule topology0.open_neigh_open)
qed

text\<open>Projection of a section of an open set is open. This is dual of 
\<open>prod_sec_open1\<close> with a very similar proof.\<close>

lemma prod_sec_open2: assumes A1: "T {is a topology}"  "S {is a topology}" and
  A2: "V \<in> ProductTopology(T,S)" and A3: "y \<in> \<Union>S"
  shows "{x \<in> \<Union>T. \<langle>x,y\<rangle> \<in> V} \<in> T"
proof -
  let ?A = "{x \<in> \<Union>T. \<langle>x,y\<rangle> \<in> V}"
  from A1 have "topology0(T)" using topology0_def by simp
  moreover have "\<forall>x\<in>?A.\<exists>W\<in>T. (x\<in>W \<and> W\<subseteq>?A)"
    proof
      fix x assume "x \<in> ?A"
      then have "\<langle>x,y\<rangle> \<in> V" by simp
      with A1 A2 have "\<langle>x,y\<rangle> \<in> \<Union>T \<times> \<Union>S" using prod_open_type by blast
      hence "x \<in> \<Union>T" and "y \<in> \<Union>S" by auto
      from A1 A2 \<open>\<langle>x,y\<rangle> \<in> V\<close> have "\<exists>U W. U\<in>T \<and> W\<in>S \<and> U\<times>W \<subseteq> V \<and> \<langle>x,y\<rangle> \<in> U\<times>W"
        by (rule prod_top_point_neighb)
      then obtain U W where  "U\<in>T" "W\<in>S" "U\<times>W \<subseteq> V" "\<langle>x,y\<rangle> \<in> U\<times>W"
        by auto
      with A1 A2 show "\<exists>W\<in>T. (x\<in>W \<and> W\<subseteq>?A)" using prod_open_type section_proj
        by auto
    qed
  ultimately show ?thesis by (rule topology0.open_neigh_open)
qed


end
