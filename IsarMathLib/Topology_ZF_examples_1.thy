(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2012 Daniel de la Concepcion

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

section \<open>More examples in topology\<close>

theory Topology_ZF_examples_1
imports Topology_ZF_1 Order_ZF
begin

text\<open>In this theory file we reformulate the concepts related to a topology
in relation with a base of the topology and we give examples of topologies defined by
bases or subbases.\<close>

subsection\<open>New ideas using a base for a topology\<close>

subsection\<open>The topology of a base\<close>

text\<open>Given a family of subsets satisfying the base condition,
  it is possible to construct a topology where that family is a base of. Even more,
  it is the only topology with such characteristics.\<close>

definition 
  TopologyWithBase ("TopologyBase _ " 50) where
  "U {satisfies the base condition} \<Longrightarrow> TopologyBase U \<equiv> THE T. U {is a base for} T"

text\<open> If a collection $U$ of sets satisfies the base condition then the topology
  constructed from it is indeed a topology and $U$ is a base for this topology. \<close>

theorem Base_topology_is_a_topology:
  assumes "U {satisfies the base condition}"
  shows "(TopologyBase U) {is a topology}" and "U {is a base for} (TopologyBase U)"
proof-
  from assms obtain T where "U {is a base for} T" using
    Top_1_2_T1(2) by blast
  then have "\<exists>!T. U {is a base for} T" using same_base_same_top ex1I[where P=
    "\<lambda>T. U {is a base for} T"] by blast
  with assms show "U {is a base for} (TopologyBase U) " using theI[where P=
    "\<lambda>T. U {is a base for} T"] TopologyWithBase_def by auto
  with assms  show "(TopologyBase U) {is a topology}" using Top_1_2_T1(1)
    IsAbaseFor_def by auto
qed

text\<open>A base doesn't need the empty set.\<close>

lemma base_no_0:
  shows "B{is a base for}T \<longleftrightarrow> (B-{0}){is a base for}T"
proof-
  {
    fix M
    assume "M\<in>{\<Union>A . A \<in> Pow(B)}"
    then obtain Q where "M=\<Union>Q""Q\<in>Pow(B)" by auto
    hence "M=\<Union>(Q-{0})""Q-{0}\<in>Pow(B-{0})" by auto
    hence "M\<in>{\<Union>A . A \<in> Pow(B - {0})}" by auto
  }
  hence "{\<Union>A . A \<in> Pow(B)} \<subseteq> {\<Union>A . A \<in> Pow(B - {0})}" by blast
  moreover
  {
    fix M
    assume "M\<in>{\<Union>A . A \<in> Pow(B-{0})}"
    then obtain Q where "M=\<Union>Q""Q\<in>Pow(B-{0})" by auto
    hence "M=\<Union>(Q)""Q\<in>Pow(B)" by auto
    hence "M\<in>{\<Union>A . A \<in> Pow(B)}" by auto
  }
  hence " {\<Union>A . A \<in> Pow(B - {0})} \<subseteq> {\<Union>A . A \<in> Pow(B)} "
    by auto
  ultimately have "{\<Union>A . A \<in> Pow(B - {0})} = {\<Union>A . A \<in> Pow(B)} " by auto
  then show "B{is a base for}T \<longleftrightarrow> (B-{0}){is a base for}T" using IsAbaseFor_def by auto
qed

text\<open>The interior of a set is the union of all the sets of the base which are fully
  contained by it.\<close>

lemma interior_set_base_topology:
  assumes "U {is a base for} T" "T{is a topology}"
  shows "Interior(A,T) = \<Union>{T\<in>U. T\<subseteq>A}"
proof
  have "{T\<in>U. T\<subseteq>A}\<subseteq>U" by auto
  with assms(1) have "\<Union>{T\<in>U. T\<subseteq>A}\<in>T"
    using IsAbaseFor_def by auto
  moreover have "\<Union>{T\<in>U. T\<subseteq>A} \<subseteq> A" by blast
  ultimately show  "\<Union>{T\<in>U. T\<subseteq>A} \<subseteq> Interior(A,T)"
    using assms(2) topology0.Top_2_L5 topology0_def by auto
  {
    fix x
    assume "x \<in> Interior(A,T)"
    with assms obtain V where "V\<in>U" "V \<subseteq> Interior(A,T)" "x\<in>V"
      using point_open_base_neigh topology0.Top_2_L2 topology0_def 
      by blast
    with assms have "V\<in>U" "x\<in>V" "V\<subseteq>A" using topology0.Top_2_L1 topology0_def
      by auto  
    hence "x \<in> \<Union>{T\<in>U. T\<subseteq>A}" by auto
  }
  thus "Interior(A, T) \<subseteq> \<Union>{T \<in> U . T \<subseteq> A} " by auto
qed

text\<open>In the following, we offer another lemma about the closure of a set 
  given a basis for a topology. This lemma is based on \<open>cl_inter_neigh\<close> and \<open>inter_neigh_cl\<close>. 
  It states that it is only necessary to check the sets of the base, not all the open sets.\<close>

lemma closure_set_base_topology:
  assumes "U {is a base for} Q" "Q{is a topology}" "A\<subseteq>\<Union>Q"
  shows "Closure(A,Q) = {x\<in>\<Union>Q. \<forall>T\<in>U. x\<in>T\<longrightarrow>A\<inter>T\<noteq>0}"
proof
  {
    fix x
    assume A:"x\<in>Closure(A,Q)"
    with assms(2,3) have B:"x\<in>\<Union>Q" using topology0_def topology0.Top_3_L11(1)
      by blast
    moreover
    {
      fix T
      assume "T\<in>U" "x\<in>T"
      with assms(1) have "T\<in>Q""x\<in>T" using base_sets_open by auto
      with assms(2,3) A have "A\<inter>T \<noteq> 0" using topology0_def topology0.cl_inter_neigh
        by auto
    }
    hence "\<forall>T\<in>U. x\<in>T\<longrightarrow>A\<inter>T\<noteq>0" by auto
    ultimately have "x\<in>{x\<in>\<Union>Q. \<forall>T\<in>U. x\<in>T\<longrightarrow>A\<inter>T\<noteq>0}" by auto
  }
  thus "Closure(A, Q) \<subseteq>{x\<in>\<Union>Q. \<forall>T\<in>U. x\<in>T\<longrightarrow>A\<inter>T\<noteq>0}"
    by auto
  {                     
    fix x
    assume AS:"x\<in>{x \<in> \<Union>Q . \<forall>T\<in>U. x \<in> T \<longrightarrow> A \<inter> T \<noteq> 0}"
    hence "x\<in>\<Union>Q" by blast
    moreover
    {
      fix R
      assume "R\<in>Q"                     
      with assms(1) obtain W where RR:"W\<subseteq>U" "R=\<Union>W" using
        IsAbaseFor_def by auto
      {
        assume "x\<in>R"
        with RR(2) obtain WW where TT:"WW\<in>W""x\<in>WW" by auto
        {
          assume "R\<inter>A=0"
          with RR(2) TT(1) have "WW\<inter>A=0"  by auto
           with TT(1) RR(1) have "WW\<in>U" "WW\<inter>A=0" by auto
          with AS have "x\<in>\<Union>Q-WW" by auto
          with TT(2) have "False" by auto
        }
        hence "R\<inter>A\<noteq>0" by auto
      }
    }
    hence "\<forall>U\<in>Q. x\<in>U \<longrightarrow> U\<inter>A\<noteq>0" by auto
    ultimately have "x\<in>Closure(A,Q)" using assms(2,3) topology0_def topology0.inter_neigh_cl 
      by auto
  }
  then show "{x \<in> \<Union>Q . \<forall>T\<in>U. x \<in> T \<longrightarrow> A \<inter> T \<noteq> 0} \<subseteq> Closure(A,Q)"
    by auto
qed

text\<open>The restriction of a base is a base for the restriction.\<close>

lemma subspace_base_topology:
  assumes "B {is a base for} T"
  shows "(B {restricted to} Y) {is a base for} (T {restricted to} Y)"
proof -
  from assms have "(B {restricted to} Y) \<subseteq> (T {restricted to} Y)"
    unfolding IsAbaseFor_def RestrictedTo_def by auto 
  moreover have "(T {restricted to} Y) = {\<Union>A. A \<in> Pow(B {restricted to} Y)}"
  proof
    { fix U assume "U \<in> (T {restricted to} Y)"
      then obtain W where "W\<in>T" and "U = W\<inter>Y" unfolding RestrictedTo_def by blast
      with assms obtain C where "C\<in>Pow(B)" and "W=\<Union>C" unfolding IsAbaseFor_def
        by blast
      let ?A="{V\<inter>Y. V\<in>C}"
      from \<open>C\<in>Pow(B)\<close> \<open>U = W\<inter>Y\<close> \<open>W=\<Union>C\<close> have 
        "?A \<in> Pow(B {restricted to} Y)" and "U=(\<Union>?A)" 
        unfolding RestrictedTo_def by auto 
      hence "U \<in> {\<Union>A. A \<in> Pow(B {restricted to} Y)}" by blast 
    } thus "(T {restricted to} Y) \<subseteq> {\<Union>A. A \<in> Pow(B {restricted to} Y)}"
      by auto
    { fix U assume "U \<in> {\<Union>A. A \<in> Pow(B {restricted to} Y)}"
      then obtain A where A: "A \<subseteq> (B {restricted to} Y)" and "U = (\<Union>A)" by auto
      let ?A\<^sub>0="{C\<in>B. Y\<inter>C\<in>A}"
      from A have "?A\<^sub>0 \<subseteq> B" and "A = ?A\<^sub>0 {restricted to} Y" unfolding RestrictedTo_def
        by auto 
      with \<open>U = (\<Union>A)\<close> have "?A\<^sub>0 \<subseteq> B" and "U = \<Union>(?A\<^sub>0 {restricted to} Y)" 
        by auto
      with assms have "U \<in> (T {restricted to} Y)" unfolding RestrictedTo_def IsAbaseFor_def
        by auto
    } thus "{\<Union>A. A \<in> Pow(B {restricted to} Y)} \<subseteq> (T {restricted to} Y)" by blast 
  qed
  ultimately show ?thesis unfolding IsAbaseFor_def by simp 
qed

text\<open>If the base of a topology is contained in the base of another
topology, then the topologies maintain the same relation.\<close>

theorem base_subset:
  assumes "B{is a base for}T""B2{is a base for}T2""B\<subseteq>B2"
  shows "T\<subseteq>T2"
proof
  {
    fix x
    assume "x\<in>T"
    with assms(1) obtain M where "M\<subseteq>B""x=\<Union>M" using IsAbaseFor_def by auto
    with assms(3) have "M\<subseteq>B2""x=\<Union>M" by auto
    with assms(2) show "x\<in>T2" using IsAbaseFor_def by auto
  }
qed

subsection\<open>Dual Base for Closed Sets\<close>

text\<open>A dual base for closed sets is the collection of complements
of sets of a base for the topology.\<close>

definition
  DualBase ("DualBase _ _" 80) where
  "B{is a base for}T \<Longrightarrow> DualBase B T\<equiv>{\<Union>T-U. U\<in>B}\<union>{\<Union>T}"


lemma closed_inter_dual_base:
  assumes "D{is closed in}T""B{is a base for}T"
  obtains M where "M\<subseteq>DualBase B T""D=\<Inter>M"
proof-
  assume K:"\<And>M. M \<subseteq> DualBase B T \<Longrightarrow> D = \<Inter>M \<Longrightarrow> thesis"
  {
    assume AS:"D\<noteq>\<Union>T"
    from assms(1) have D:"D\<in>Pow(\<Union>T)""\<Union>T-D\<in>T" using IsClosed_def by auto
    hence A:"\<Union>T-(\<Union>T-D)=D""\<Union>T-D\<in>T" by auto
    with assms(2) obtain Q where QQ:"Q\<in>Pow(B)""\<Union>T-D=\<Union>Q" using IsAbaseFor_def by auto
    {
      assume "Q=0"
      then have "\<Union>Q=0" by auto
      with QQ(2) have "\<Union>T-D=0" by auto
      with D(1) have "D=\<Union>T" by auto 
      with AS have "False" by auto
    }
    hence QNN:"Q\<noteq>0" by auto
    from QQ(2) A(1) have "D=\<Union>T-\<Union>Q" by auto
    with QNN have "D=\<Inter>{\<Union>T-R. R\<in>Q}" by auto
    moreover
    with assms(2) QQ(1) have "{\<Union>T-R. R\<in>Q}\<subseteq>DualBase B T" using DualBase_def
      by auto
    with calculation K have "thesis" by auto
  }
  moreover
  {
    assume AS:"D=\<Union>T"
    with assms(2) have "{\<Union>T}\<subseteq>DualBase B T" using DualBase_def by auto
    moreover
    have "\<Union>T = \<Inter>{\<Union>T}" by auto
    with calculation K AS have thesis by auto
  }
  ultimately show thesis by auto
qed

text\<open>We have already seen for a base that whenever
there is a union of open sets, we can consider only basic open sets
due to the fact that any open set is a union of basic open sets.
What we should expect now is that when there is an intersection
of closed sets, we can consider only dual basic closed sets.\<close>

lemma closure_dual_base:
  assumes "U {is a base for} Q""Q{is a topology}""A\<subseteq>\<Union>Q"
  shows "Closure(A,Q)=\<Inter>{T\<in>DualBase U Q. A\<subseteq>T}"
proof
  from assms(1) have T:"\<Union>Q\<in>DualBase U Q" using DualBase_def by auto
  moreover
  {
    fix T
    assume A:"T\<in>DualBase U Q" "A\<subseteq>T"
    with assms(1) obtain R where "(T=\<Union>Q-R\<and>R\<in>U)\<or>T=\<Union>Q" using DualBase_def
      by auto
    with A(2) assms(1,2) have  "(T{is closed in}Q)""A\<subseteq>T""T\<in>Pow(\<Union>Q)" using topology0.Top_3_L1 topology0_def
      topology0.Top_3_L9 base_sets_open by auto
  }
  then have SUB:"{T\<in>DualBase U Q. A\<subseteq>T}\<subseteq>{T\<in>Pow(\<Union>Q). (T{is closed in}Q)\<and>A\<subseteq>T}"
    by blast
  with calculation assms(3) have "\<Inter>{T\<in>Pow(\<Union>Q). (T{is closed in}Q)\<and>A\<subseteq>T}\<subseteq>\<Inter>{T\<in>DualBase U Q. A\<subseteq>T}"
    by auto
  then show "Closure(A,Q)\<subseteq>\<Inter>{T\<in>DualBase U Q. A\<subseteq>T}" using Closure_def ClosedCovers_def
    by auto
  {
    fix x
    assume A:"x\<in>\<Inter>{T\<in>DualBase U Q. A\<subseteq>T}"
    {
      fix T
      assume B:"x\<in>T""T\<in>U"
      {
        assume C:"A\<inter>T=0"
        from B(2) assms(1) have "\<Union>Q-T\<in>DualBase U Q" using DualBase_def
          by auto
        moreover
        from C assms(3) have "A\<subseteq>\<Union>Q-T" by auto
        moreover
        from B(1) have "x\<notin>\<Union>Q-T" by auto
        ultimately have "x\<notin>\<Inter>{T\<in>DualBase U Q. A\<subseteq>T}" by auto
        with A have "False" by auto
      }
      hence "A\<inter>T\<noteq>0" by auto
    }
    hence "\<forall>T\<in>U. x\<in>T\<longrightarrow>A\<inter>T\<noteq>0" by auto
    moreover
    from T A assms(3) have "x\<in>\<Union>Q" by auto
    with calculation assms have "x\<in>Closure(A,Q)" using closure_set_base_topology
     by auto
  }
  thus "\<Inter>{T \<in> DualBase U Q . A \<subseteq> T} \<subseteq> Closure(A, Q)" by auto
qed

subsection\<open>Partition topology\<close>

text\<open>In the theory file Partitions\_ZF.thy; there is
a definition to work with partitions. In this setting
is much easier to work with a family of subsets.\<close>

definition
  IsAPartition ("_{is a partition of}_" 90) where
  "(U {is a partition of} X) \<equiv> (\<Union>U=X \<and> (\<forall>A\<in>U. \<forall>B\<in>U. A=B\<or> A\<inter>B=0)\<and> 0\<notin>U)"

text\<open>A subcollection of a partition is a partition
of its union.\<close>

lemma subpartition:
  assumes "U {is a partition of} X" "V\<subseteq>U"
  shows "V{is a partition of}\<Union>V" 
  using assms unfolding IsAPartition_def by auto

text\<open>A restriction of a partition is a partition. If the empty set appears
it has to be removed.\<close>

lemma restriction_partition:
  assumes "U {is a partition of}X"
  shows "((U {restricted to} Y)-{0}) {is a partition of} (X\<inter>Y)"
  using assms unfolding IsAPartition_def RestrictedTo_def
  by fast

text\<open>Given a partition, 
the complement of a union of a subfamily
is a union of a subfamily.\<close>

lemma diff_union_is_union_diff:
  assumes "R\<subseteq>P" "P {is a partition of} X"
  shows "X - \<Union>R=\<Union>(P-R)"
proof
  {
    fix x
    assume "x\<in>X - \<Union>R"
    hence P:"x\<in>X""x\<notin>\<Union>R" by auto
    {
      fix T
      assume "T\<in>R"
      with P(2) have "x\<notin>T" by auto
    }
    with P(1) assms(2) obtain Q where "Q\<in>(P-R)""x\<in>Q" using IsAPartition_def by auto
    hence "x\<in>\<Union>(P-R)" by auto
  }
  thus "X - \<Union>R\<subseteq>\<Union>(P-R)" by auto
  {
    fix x
    assume "x\<in>\<Union>(P-R)"
    then obtain Q where "Q\<in>P-R""x\<in>Q" by auto
    hence C: "Q\<in>P""Q\<notin>R""x\<in>Q" by auto
    then have "x\<in>\<Union>P" by auto
    with assms(2) have "x\<in>X" using IsAPartition_def by auto
    moreover
    {
      assume "x\<in>\<Union>R"
      then obtain t where G:"t\<in>R" "x\<in>t" by auto
      with C(3) assms(1) have "t\<inter>Q\<noteq>0""t\<in>P" by auto
      with assms(2) C(1,3) have "t=Q" using IsAPartition_def
        by blast
      with C(2) G(1) have "False" by auto
    }
    hence "x\<notin>\<Union>R" by auto
    ultimately have "x\<in>X-\<Union>R" by auto
  }
  thus "\<Union>(P-R)\<subseteq>X - \<Union>R" by auto
qed

subsection\<open>Partition topology is a topology.\<close>

text\<open>A partition satisfies the base condition.\<close>

lemma partition_base_condition:
  assumes "P {is a partition of} X"
  shows "P {satisfies the base condition}"
proof-
  {
    fix U V
    assume AS:"U\<in>P\<and>V\<in>P"
    with assms have A:"U=V\<or> U\<inter>V=0" using IsAPartition_def by auto
    {
      fix x
      assume ASS:"x\<in>U\<inter>V"
      with A have "U=V" by auto
      with AS ASS have "U\<in>P""x\<in>U\<and> U\<subseteq>U\<inter>V" by auto
      hence "\<exists>W\<in>P. x\<in>W\<and> W\<subseteq>U\<inter>V" by auto
    }
    hence "(\<forall>x \<in> U\<inter>V. \<exists>W\<in>P. x\<in>W \<and> W \<subseteq> U\<inter>V)" by auto
  }
  then show ?thesis using SatisfiesBaseCondition_def by auto
qed

text\<open>Since a partition is a base of a topology, and this topology
is uniquely determined; we can built it. In the definition
we have to make sure that we have a partition.\<close>

definition 
  PartitionTopology ("PTopology _ _" 50) where
  "(U {is a partition of} X) \<Longrightarrow> PTopology X U \<equiv> TopologyBase U"

theorem Ptopology_is_a_topology:
  assumes "U {is a partition of} X"
  shows "(PTopology X U) {is a topology}" and "U {is a base for} (PTopology X U)"
  using assms Base_topology_is_a_topology partition_base_condition 
    PartitionTopology_def by auto

lemma topology0_ptopology:
  assumes "U {is a partition of} X"
  shows "topology0(PTopology X U)"
  using Ptopology_is_a_topology topology0_def assms by auto

subsection\<open>Total set, Closed sets, Interior, Closure and Boundary\<close>

text\<open>The topology is defined in the set $X$\<close>

lemma union_ptopology:
  assumes "U {is a partition of} X"
  shows "\<Union>(PTopology X U)=X"
  using assms Ptopology_is_a_topology(2) Top_1_2_L5
    IsAPartition_def by auto

text\<open>The closed sets are the open sets.\<close>

lemma closed_sets_ptopology:
  assumes "T {is a partition of} X"
  shows"D {is closed in} (PTopology X T) \<longleftrightarrow> D\<in>(PTopology X T)"
proof
  from assms
  have B:"T{is a base for}(PTopology X T)" using Ptopology_is_a_topology(2) by auto
  {
    fix D
    assume "D {is closed in} (PTopology X T)"
    with assms have A:"D\<in>Pow(X)""X-D\<in>(PTopology X T)"
      using IsClosed_def union_ptopology by auto
    from A(2) B obtain R where Q:"R\<subseteq>T" "X-D=\<Union>R" using Top_1_2_L1[where B="T" and U="X-D"]
      by auto
    from A(1) have "X-(X-D)=D" by blast 
    with Q(2) have "D=X-\<Union>R" by auto
    with Q(1) assms have "D=\<Union>(T-R)" using diff_union_is_union_diff
      by auto
    with B show "D\<in>(PTopology X T)" using IsAbaseFor_def by auto
  }
  {
    fix D
    assume "D\<in>(PTopology X T)"
    with B obtain R where Q:"R\<subseteq>T""D=\<Union>R" using IsAbaseFor_def by auto
    hence "X-D=X-\<Union>R" by auto
    with Q(1) assms have "X-D=\<Union>(T-R)" using diff_union_is_union_diff
      by auto
    with B have "X-D\<in>(PTopology X T)" using IsAbaseFor_def by auto
    moreover
    from Q have "D\<subseteq>\<Union>T" by auto
    with assms have "D\<subseteq>X" using IsAPartition_def by auto
    with calculation assms show "D{is closed in} (PTopology X T)"
      using IsClosed_def union_ptopology by auto
  }
qed

text\<open>There is a formula for the interior
given by an intersection of sets of the dual base.
Is the intersection of all the closed sets of the dual basis
such that they do not complement $A$ to $X$.
Since the interior of $X$ must be inside $X$, we have to 
enter $X$ as one of the sets to be intersected.\<close>

lemma interior_set_ptopology:
  assumes "U {is a partition of} X""A\<subseteq>X"
  shows "Interior(A,(PTopology X U))=\<Inter>{T\<in>DualBase U (PTopology X U). T=X\<or>T\<union>A\<noteq>X}"
proof
  {
    fix x
    assume "x\<in>Interior(A,(PTopology X U))"
    with assms obtain R where A:"x\<in>R""R\<in>(PTopology X U)""R\<subseteq>A"
      using topology0.open_open_neigh topology0_ptopology
      topology0.Top_2_L2 topology0.Top_2_L1
      by auto
    with assms obtain B where B:"B\<subseteq>U""R=\<Union>B" using Ptopology_is_a_topology(2)
      IsAbaseFor_def by auto
    from A(1,3) assms have XX:"x\<in>X""X\<in>{T\<in>DualBase U (PTopology X U). T=X\<or>T\<union>A\<noteq>X}"
      using union_ptopology[of "U""X"] DualBase_def[of"U"] Ptopology_is_a_topology(2)[of "U""X"] by (safe,blast,auto)
    moreover
    from B(2) A(1) obtain S where C:"S\<in>B""x\<in>S" by auto
    {
      fix T
      assume AS:"T\<in>DualBase U (PTopology X U)""T \<union>A\<noteq>X"
      from AS(1) assms obtain w where "(T=X-w\<and>w\<in>U)\<or>(T=X)"
        using DualBase_def union_ptopology Ptopology_is_a_topology(2)
        by auto
      with assms(2) AS(2) have D:"T=X-w""w\<in>U" by auto
      from D(2) have "w\<subseteq>\<Union>U" by auto
      with assms(1) have "w\<subseteq>\<Union>(PTopology X U)" using Ptopology_is_a_topology(2) Top_1_2_L5[of "U""PTopology X U"]
        by auto
      with assms(1) have "w\<subseteq>X" using union_ptopology by auto
      with D(1) have "X-T=w" by auto
      with D(2) have "X-T\<in>U" by auto
      { 
        assume "x\<in>X-T"
        with C B(1) have "S\<in>U""S\<inter>(X-T)\<noteq>0" by auto
        with \<open>X-T\<in>U\<close> assms(1) have "X-T=S" using IsAPartition_def by auto
        with \<open>X-T=w\<close>\<open>T=X-w\<close> have "X-S=T" by auto
        with AS(2) have "X-S\<union>A\<noteq>X" by auto
        from A(3) B(2) C(1) have "S\<subseteq>A" by auto
        hence "X-A\<subseteq>X-S" by auto
        with assms(2) have "X-S\<union>A=X"  by auto
        with \<open>X-S\<union>A\<noteq>X\<close> have "False" by auto
        }
      then have "x\<in>T" using XX by auto
      }
    ultimately have "x\<in>\<Inter>{T\<in>DualBase U (PTopology X U). T=X\<or>T\<union>A\<noteq>X}"
      by auto
  }
  thus "Interior(A,(PTopology X U))\<subseteq>\<Inter>{T\<in>DualBase U (PTopology X U). T=X\<or>T\<union>A\<noteq>X}" by auto
  {
    fix x
    assume p:"x\<in>\<Inter>{T\<in>DualBase U (PTopology X U). T=X\<or>T\<union>A\<noteq>X}"
    hence noE:"\<Inter>{T\<in>DualBase U (PTopology X U). T=X\<or>T\<union>A\<noteq>X}\<noteq>0" by auto
    {
      fix T
      assume "T\<in>DualBase U (PTopology X U)"
      with assms(1) obtain w where "T=X\<or>(w\<in>U\<and>T=X-w)" using DualBase_def
        Ptopology_is_a_topology(2) union_ptopology by auto
      with assms(1) have "T=X\<or>(w\<in>(PTopology X U)\<and>T=X-w)" using base_sets_open
        Ptopology_is_a_topology(2) by blast
      with assms(1) have "T{is closed in}(PTopology X U)" using topology0.Top_3_L1[where T="PTopology X U"]
        topology0_ptopology topology0.Top_3_L9[where T="PTopology X U"] union_ptopology
        by auto
    }
    moreover
    from assms(1) p have "X\<in>{T\<in>DualBase U (PTopology X U). T=X\<or>T\<union>A\<noteq>X}"and X:"x\<in>X" using Ptopology_is_a_topology(2) 
      DualBase_def union_ptopology by auto
    with calculation assms(1) have "(\<Inter>{T\<in>DualBase U (PTopology X U). T=X\<or>T\<union>A\<noteq>X}) {is closed in}(PTopology X U)"
      using topology0.Top_3_L4[where K="{T\<in>DualBase U (PTopology X U). T=X\<or>T\<union>A\<noteq>X}"] topology0_ptopology[where U="U" and X="X"]
      by auto
    with assms(1) have ab:"(\<Inter>{T\<in>DualBase U (PTopology X U). T=X\<or>T\<union>A\<noteq>X})\<in>(PTopology X U)"
      using closed_sets_ptopology by auto
    with assms(1) obtain B where "B\<in>Pow(U)""(\<Inter>{T\<in>DualBase U (PTopology X U). T=X\<or>T\<union>A\<noteq>X})=\<Union>B"
      using Ptopology_is_a_topology(2) IsAbaseFor_def by auto
    with p obtain R where "x\<in>R""R\<in>U""R\<subseteq>(\<Inter>{T\<in>DualBase U (PTopology X U). T=X\<or>T\<union>A\<noteq>X})"
      by auto
    with assms(1) have R:"x\<in>R""R\<in>(PTopology X U)""R\<subseteq>(\<Inter>{T\<in>DualBase U (PTopology X U). T=X\<or>T\<union>A\<noteq>X})""X-R\<in>DualBase U (PTopology X U)"
      using base_sets_open Ptopology_is_a_topology(2) DualBase_def union_ptopology
      by (safe,blast,simp,blast)
    {
      assume "(X-R) \<union>A\<noteq>X"
      with R(4) have "X-R\<in>{T\<in>DualBase U (PTopology X U). T=X\<or>T\<union>A\<noteq>X}" by auto
      hence "\<Inter>{T\<in>DualBase U (PTopology X U). T=X\<or>T\<union>A\<noteq>X}\<subseteq>X-R" by auto
      with R(3) have "R\<subseteq>X-R" using subset_trans[where A="R" and C="X-R"] by auto
      hence "R=0" by blast
      with R(1) have "False" by auto
    }
    hence I:"(X-R) \<union>A=X" by auto
    {
      fix y
      assume ASR:"y\<in>R"
      with R(2) have "y\<in>\<Union>(PTopology X U)" by auto
      with assms(1) have XX:"y\<in>X" using union_ptopology by auto
      with I have "y\<in>(X-R) \<union>A" by auto
      with XX have "y\<notin>R\<or>y\<in>A" by auto
      with ASR have "y\<in>A" by auto
    }
    hence "R\<subseteq>A" by auto
    with R(1,2) have "\<exists>R\<in>(PTopology X U). (x\<in>R\<and>R\<subseteq>A)" by auto
    with assms(1) have "x\<in>Interior(A,(PTopology X U))" using topology0.Top_2_L6
      topology0_ptopology by auto
  }
  thus "\<Inter>{T \<in> DualBase U PTopology X U . T = X \<or> T \<union> A \<noteq> X} \<subseteq> Interior(A, PTopology X U)"
    by auto
qed


text\<open>The closure of a set is the union of
all the sets of the partition which intersect
with \<open>A\<close>.\<close>

lemma closure_set_ptopology:
  assumes "U {is a partition of} X""A\<subseteq>X"
  shows "Closure(A,(PTopology X U))=\<Union>{T\<in>U. T\<inter>A\<noteq>0}"
proof
  {
    fix x
    assume A:"x\<in>Closure(A,(PTopology X U))"
    with assms have "x\<in>\<Union>(PTopology X U)" using topology0.Top_3_L11(1)[where T="PTopology X U"
      and A="A"] topology0_ptopology union_ptopology by auto
    with assms(1) have "x\<in>\<Union>U" using Top_1_2_L5[where B="U" and T="PTopology X U"] Ptopology_is_a_topology(2) by auto
    then obtain W where B:"x\<in>W""W\<in>U" by auto
    with A have "x\<in>Closure(A,(PTopology X U))\<inter>W" by auto
    moreover
    from assms B(2) have "W\<in>(PTopology X U)""A\<subseteq>X" using base_sets_open Ptopology_is_a_topology(2)
      by (safe,blast)
    with calculation assms(1) have "A\<inter>W\<noteq>0" using topology0_ptopology[where U="U" and X="X"]
      topology0.cl_inter_neigh union_ptopology by auto
    with B have "x\<in>\<Union>{T\<in>U. T\<inter>A\<noteq>0}" by blast
  }
  thus "Closure(A, PTopology X U) \<subseteq> \<Union>{T \<in> U . T \<inter> A \<noteq> 0}" by auto
  {
    fix x
    assume "x\<in>\<Union>{T \<in> U . T \<inter> A \<noteq> 0}"
    then obtain T where A:"x\<in>T""T\<in>U""T\<inter>A\<noteq>0" by auto
    from assms have "A\<subseteq>\<Union>(PTopology X U)" using union_ptopology by auto
    moreover
    from A(1,2) assms(1) have "x\<in>\<Union>(PTopology X U)" using Top_1_2_L5[where B="U" and T="PTopology X U"]
      Ptopology_is_a_topology(2) by auto
    moreover
    {
      fix Q
      assume B:"Q\<in>(PTopology X U)""x\<in>Q"
      with assms(1) obtain M where C:"Q=\<Union>M""M\<subseteq>U" using 
        Ptopology_is_a_topology(2)
        IsAbaseFor_def by auto
      from B(2) C(1) obtain R where D:"R\<in>M""x\<in>R" by auto
      with C(2) A(1,2) have "R\<inter>T\<noteq>0""R\<in>U""T\<in>U" by auto
      with assms(1) have "R=T" using IsAPartition_def by auto
      with C(1) D(1) have "T\<subseteq>Q" by auto
      with A(3) have "Q\<inter>A\<noteq>0" by auto
    }
    then have "\<forall>Q\<in>(PTopology X U). x\<in>Q \<longrightarrow> Q\<inter>A\<noteq>0" by auto
    with calculation assms(1) have "x\<in>Closure(A,(PTopology X U))" using topology0.inter_neigh_cl
      topology0_ptopology by auto
  }
  then show "\<Union>{T \<in> U . T \<inter> A \<noteq> 0} \<subseteq> Closure(A, PTopology X U) " by auto
qed

text\<open>The boundary of a set is given by the union of the sets
of the partition which have non empty intersection with the set
but that are not fully contained in it. Another equivalent
statement would be: the union of the sets
of the partition which have non empty intersection with the set
and its complement.\<close>

lemma boundary_set_ptopology:
  assumes "U {is a partition of} X""A\<subseteq>X"
  shows "Boundary(A,(PTopology X U))=\<Union>{T\<in>U. T\<inter>A\<noteq>0 \<and> ~(T\<subseteq>A)}"
proof-
  from assms have "Closure(A,(PTopology X U))=\<Union>{T \<in> U . T \<inter> A \<noteq> 0}" using
    closure_set_ptopology by auto
  moreover
  from assms(1) have "Interior(A,(PTopology X U))=\<Union>{T \<in> U . T \<subseteq> A}" using
    interior_set_base_topology Ptopology_is_a_topology[where U="U" and X="X"] by auto
  with calculation assms have A:"Boundary(A,(PTopology X U))=\<Union>{T \<in> U . T \<inter> A \<noteq> 0} - \<Union>{T \<in> U . T \<subseteq> A}"
    using topology0.Top_3_L12 topology0_ptopology union_ptopology
    by auto
  from assms(1) have "({T \<in> U . T \<inter> A \<noteq> 0}) {is a partition of} \<Union>({T \<in> U . T \<inter> A \<noteq> 0})"
    using subpartition by blast
  moreover
  {
    fix T
    assume "T\<in>U""T\<subseteq>A"
    with assms(1) have "T\<inter>A=T""T\<noteq>0" using IsAPartition_def by auto
    with \<open>T\<in>U\<close> have "T\<inter>A\<noteq>0""T\<in>U" by auto
  }
  then have "{T \<in> U . T \<subseteq> A}\<subseteq>{T \<in> U . T \<inter> A \<noteq> 0}"  by auto
  ultimately have "\<Union>{T \<in> U . T \<inter> A \<noteq> 0} - \<Union>{T \<in> U . T \<subseteq> A}=\<Union>(({T \<in> U . T \<inter> A \<noteq> 0})-({T \<in> U . T \<subseteq> A}))"
  using diff_union_is_union_diff by auto
  also have "\<dots>=\<Union>({T \<in> U . T \<inter> A \<noteq> 0 \<and> ~(T\<subseteq>A)})" by blast
  with calculation A show ?thesis by auto
qed

subsection\<open>Special cases and subspaces\<close>

text\<open>The discrete and the indiscrete topologies appear as special
cases of this partition topologies.\<close>

lemma discrete_partition:
  shows "{{x}.x\<in>X} {is a partition of}X"
  using IsAPartition_def by auto

lemma indiscrete_partition:
  assumes "X\<noteq>0"
  shows "{X} {is a partition of} X"
  using assms IsAPartition_def by auto

theorem discrete_ptopology:
  shows "(PTopology X {{x}.x\<in>X})=Pow(X)"
proof
  {
    fix t
    assume "t\<in>(PTopology X {{x}.x\<in>X})"
    hence "t\<subseteq>\<Union>(PTopology X {{x}.x\<in>X})" by auto
    then have "t\<in>Pow(X)" using union_ptopology 
      discrete_partition by auto
  }
  thus "(PTopology X {{x}.x\<in>X})\<subseteq>Pow(X)" by auto
  {
    fix t
    assume A:"t\<in>Pow(X)"
    have "\<Union>({{x}. x\<in>t})=t" by auto
    moreover
    from A have "{{x}. x\<in>t}\<in>Pow({{x}.x\<in>X})" by auto
    hence "\<Union>({{x}. x\<in>t})\<in>{\<Union>A . A \<in> Pow({{x} . x \<in> X})}" by auto
    ultimately
    have "t\<in>(PTopology X {{x} . x \<in> X})" using Ptopology_is_a_topology(2)
      discrete_partition IsAbaseFor_def by auto
  }
  thus "Pow(X) \<subseteq> (PTopology X {{x} . x \<in> X}) " by auto
qed

theorem indiscrete_ptopology:
  assumes "X\<noteq>0"
  shows "(PTopology X {X})={0,X}"
proof
  {
    fix T
    assume "T\<in>(PTopology X {X})"
    with assms obtain M where "M\<subseteq>{X}""\<Union>M=T" using Ptopology_is_a_topology(2)
      indiscrete_partition IsAbaseFor_def by auto
    then have "T=0\<or>T=X" by auto
  }
  then show "(PTopology X {X})\<subseteq>{0,X}" by auto
  from assms have "0\<in>(PTopology X {X})" using Ptopology_is_a_topology(1) empty_open
    indiscrete_partition by auto
  moreover
  from assms have "\<Union>(PTopology X {X})\<in>(PTopology X {X})" using union_open Ptopology_is_a_topology(1)
    indiscrete_partition by auto
  with assms have "X\<in>(PTopology X {X})" using union_ptopology indiscrete_partition
    by auto
  ultimately show "{0,X}\<subseteq>(PTopology X {X})" by auto
qed

text\<open>The topological subspaces of the \<open>(PTopology X U)\<close>
are partition topologies.\<close>

lemma subspace_ptopology:
  assumes "U{is a partition of}X"
  shows "(PTopology X U) {restricted to} Y=(PTopology (X\<inter>Y) ((U {restricted to} Y)-{0}))"
proof-
  from assms have "U{is a base for}(PTopology X U)" using Ptopology_is_a_topology(2)
    by auto
  then have "(U{restricted to} Y){is a base for}(PTopology X U){restricted to} Y"
    using subspace_base_topology by auto
  then have "((U{restricted to} Y)-{0}){is a base for}(PTopology X U){restricted to} Y" using base_no_0
    by auto
  moreover
  from assms have "((U{restricted to} Y)-{0}) {is a partition of} (X\<inter>Y)"
    using restriction_partition by auto
  then have "((U{restricted to} Y)-{0}){is a base for}(PTopology (X\<inter>Y) ((U {restricted to} Y)-{0}))"
    using Ptopology_is_a_topology(2) by auto
  ultimately show ?thesis using same_base_same_top by auto
qed

subsection\<open>Order topologies\<close>

subsection\<open>Order topology is a topology\<close>

text\<open>Given a totally ordered set, several topologies can be defined
using the order relation. First we define an open interval, notice that
the set defined as \<open>Interval\<close> is a closed interval; and open rays.\<close>

definition
  IntervalX where
  "IntervalX(X,r,b,c)\<equiv>(Interval(r,b,c)\<inter>X)-{b,c}"
definition
  LeftRayX where
  "LeftRayX(X,r,b)\<equiv>{c\<in>X. \<langle>c,b\<rangle>\<in>r}-{b}"
definition
  RightRayX where
  "RightRayX(X,r,b)\<equiv>{c\<in>X. \<langle>b,c\<rangle>\<in>r}-{b}"

text\<open>Intersections of intervals and rays.\<close>

lemma inter_two_intervals:
  assumes "bu\<in>X""bv\<in>X""cu\<in>X""cv\<in>X""IsLinOrder(X,r)"
  shows "IntervalX(X,r,bu,cu)\<inter>IntervalX(X,r,bv,cv)=IntervalX(X,r,GreaterOf(r,bu,bv),SmallerOf(r,cu,cv))"
proof
  have T:"GreaterOf(r,bu,bv)\<in>X""SmallerOf(r,cu,cv)\<in>X" using assms 
    GreaterOf_def SmallerOf_def by (cases "\<langle>bu,bv\<rangle>\<in>r",simp,simp,cases "\<langle>cu,cv\<rangle>\<in>r",simp,simp)
  {
    fix x
    assume ASS:"x\<in>IntervalX(X,r,bu,cu)\<inter>IntervalX(X,r,bv,cv)"
    then have "x\<in>IntervalX(X,r,bu,cu)""x\<in>IntervalX(X,r,bv,cv)" by auto
    then have BB:"x\<in>X""x\<in>Interval(r,bu,cu)""x\<noteq>bu""x\<noteq>cu""x\<in>Interval(r,bv,cv)""x\<noteq>bv""x\<noteq>cv"
    using IntervalX_def assms by auto
    then have "x\<in>X" by auto
    moreover
    have "x\<noteq>GreaterOf(r,bu,bv)""x\<noteq>SmallerOf(r,cu,cv)"
    proof-
      show "x\<noteq>GreaterOf(r,bu,bv)" using GreaterOf_def BB(6,3) by (cases "\<langle>bu,bv\<rangle>\<in>r",simp+)
      show "x\<noteq>SmallerOf(r,cu,cv)" using SmallerOf_def BB(7,4) by (cases "\<langle>cu,cv\<rangle>\<in>r",simp+)
    qed
    moreover
    have "\<langle>bu,x\<rangle>\<in>r""\<langle>x,cu\<rangle>\<in>r""\<langle>bv,x\<rangle>\<in>r""\<langle>x,cv\<rangle>\<in>r" using BB(2,5) Order_ZF_2_L1A by auto
    then have "\<langle>GreaterOf(r,bu,bv),x\<rangle>\<in>r""\<langle>x,SmallerOf(r,cu,cv)\<rangle>\<in>r" using GreaterOf_def SmallerOf_def 
      by (cases "\<langle>bu,bv\<rangle>\<in>r",simp,simp,cases "\<langle>cu,cv\<rangle>\<in>r",simp,simp)
    then have "x\<in>Interval(r,GreaterOf(r,bu,bv),SmallerOf(r,cu,cv))" using Order_ZF_2_L1 by auto
    ultimately
    have "x\<in>IntervalX(X,r,GreaterOf(r,bu,bv),SmallerOf(r,cu,cv))" using IntervalX_def T by auto
  }
  then show "IntervalX(X, r, bu, cu) \<inter> IntervalX(X, r, bv, cv) \<subseteq> IntervalX(X, r, GreaterOf(r, bu, bv), SmallerOf(r, cu, cv))"
    by auto
  {
    fix x
    assume "x\<in>IntervalX(X,r,GreaterOf(r,bu,bv),SmallerOf(r,cu,cv))"
    then have BB:"x\<in>X""x\<in>Interval(r,GreaterOf(r,bu,bv),SmallerOf(r,cu,cv))""x\<noteq>GreaterOf(r,bu,bv)""x\<noteq>SmallerOf(r,cu,cv)"
    using IntervalX_def T by auto
    then have "x\<in>X" by auto
    moreover
    from BB(2) have CC:"\<langle>GreaterOf(r,bu,bv),x\<rangle>\<in>r""\<langle>x,SmallerOf(r,cu,cv)\<rangle>\<in>r" using Order_ZF_2_L1A by auto
    {
      {
        assume AS:"\<langle>bu,bv\<rangle>\<in>r"
        then have "GreaterOf(r,bu,bv)=bv" using GreaterOf_def by auto
        then have "\<langle>bv,x\<rangle>\<in>r" using CC(1) by auto
        with AS have "\<langle>bu,x\<rangle>\<in>r" "\<langle>bv,x\<rangle>\<in>r" using assms IsLinOrder_def trans_def by (safe, blast)
      }
      moreover
      {
        assume AS:"\<langle>bu,bv\<rangle>\<notin>r"
        then have "GreaterOf(r,bu,bv)=bu" using GreaterOf_def by auto
        then have "\<langle>bu,x\<rangle>\<in>r" using CC(1) by auto
        from AS have "\<langle>bv,bu\<rangle>\<in>r" using assms IsLinOrder_def IsTotal_def assms by auto
        with \<open>\<langle>bu,x\<rangle>\<in>r\<close> have "\<langle>bu,x\<rangle>\<in>r" "\<langle>bv,x\<rangle>\<in>r" using assms IsLinOrder_def trans_def by (safe, blast)
      }
      ultimately have R:"\<langle>bu,x\<rangle>\<in>r" "\<langle>bv,x\<rangle>\<in>r" by auto
      moreover
      {
        assume AS:"x=bu"
        then have "\<langle>bv,bu\<rangle>\<in>r" using R(2) by auto
        then have "GreaterOf(r,bu,bv)=bu" using GreaterOf_def assms IsLinOrder_def
        antisym_def by auto
        then have "False" using AS BB(3) by auto
      }
      moreover
      {
        assume AS:"x=bv"
        then have "\<langle>bu,bv\<rangle>\<in>r" using R(1) by auto
        then have "GreaterOf(r,bu,bv)=bv" using GreaterOf_def by auto
        then have "False" using AS BB(3) by auto
      }
      ultimately have "\<langle>bu,x\<rangle>\<in>r" "\<langle>bv,x\<rangle>\<in>r""x\<noteq>bu""x\<noteq>bv" by auto
    }
    moreover
    {
      {
        assume AS:"\<langle>cu,cv\<rangle>\<in>r"
        then have "SmallerOf(r,cu,cv)=cu" using SmallerOf_def by auto
        then have "\<langle>x,cu\<rangle>\<in>r" using CC(2) by auto
        with AS have "\<langle>x,cu\<rangle>\<in>r" "\<langle>x,cv\<rangle>\<in>r" using assms IsLinOrder_def trans_def by(safe ,blast)
      }
      moreover
      {
        assume AS:"\<langle>cu,cv\<rangle>\<notin>r"
        then have "SmallerOf(r,cu,cv)=cv" using SmallerOf_def by auto
        then have "\<langle>x,cv\<rangle>\<in>r" using CC(2) by auto
        from AS have "\<langle>cv,cu\<rangle>\<in>r" using assms IsLinOrder_def IsTotal_def by auto
        with \<open>\<langle>x,cv\<rangle>\<in>r\<close> have "\<langle>x,cv\<rangle>\<in>r" "\<langle>x,cu\<rangle>\<in>r" using assms IsLinOrder_def trans_def by(safe ,blast)
      }
      ultimately have R:"\<langle>x,cv\<rangle>\<in>r" "\<langle>x,cu\<rangle>\<in>r" by auto
      moreover
      {
        assume AS:"x=cv"
        then have "\<langle>cv,cu\<rangle>\<in>r" using R(2) by auto
        then have "SmallerOf(r,cu,cv)=cv" using SmallerOf_def assms IsLinOrder_def
        antisym_def by auto
        then have "False" using AS BB(4) by auto
      }
      moreover
      {
        assume AS:"x=cu"
        then have "\<langle>cu,cv\<rangle>\<in>r" using R(1) by auto
        then have "SmallerOf(r,cu,cv)=cu" using SmallerOf_def by auto
        then have "False" using AS BB(4) by auto
      }
      ultimately have "\<langle>x,cu\<rangle>\<in>r" "\<langle>x,cv\<rangle>\<in>r""x\<noteq>cu""x\<noteq>cv" by auto
    }
    ultimately
    have "x\<in>IntervalX(X,r,bu,cu)" "x\<in>IntervalX(X,r,bv,cv)" using Order_ZF_2_L1 IntervalX_def
      assms by auto
    then have "x\<in>IntervalX(X, r, bu, cu) \<inter> IntervalX(X, r, bv, cv) " by auto
  }
  then show "IntervalX(X,r,GreaterOf(r,bu,bv),SmallerOf(r,cu,cv)) \<subseteq> IntervalX(X, r, bu, cu) \<inter> IntervalX(X, r, bv, cv)"
    by auto
qed

lemma inter_rray_interval:
  assumes "bv\<in>X""bu\<in>X""cv\<in>X""IsLinOrder(X,r)"
  shows "RightRayX(X,r,bu)\<inter>IntervalX(X,r,bv,cv)=IntervalX(X,r,GreaterOf(r,bu,bv),cv)"
proof
  {
    fix x
    assume "x\<in>RightRayX(X,r,bu)\<inter>IntervalX(X,r,bv,cv)"
    then have "x\<in>RightRayX(X,r,bu)""x\<in>IntervalX(X,r,bv,cv)" by auto
    then have BB:"x\<in>X""x\<noteq>bu""x\<noteq>bv""x\<noteq>cv""\<langle>bu,x\<rangle>\<in>r""x\<in>Interval(r,bv,cv)" using RightRayX_def IntervalX_def
      by auto
    then have "\<langle>bv,x\<rangle>\<in>r""\<langle>x,cv\<rangle>\<in>r" using Order_ZF_2_L1A by auto
    with \<open>\<langle>bu,x\<rangle>\<in>r\<close> have "\<langle>GreaterOf(r,bu,bv),x\<rangle>\<in>r" using GreaterOf_def by (cases "\<langle>bu,bv\<rangle>\<in>r",simp+)
    with \<open>\<langle>x,cv\<rangle>\<in>r\<close> have "x\<in>Interval(r,GreaterOf(r,bu,bv),cv)" using Order_ZF_2_L1 by auto
    then have "x\<in>IntervalX(X,r,GreaterOf(r,bu,bv),cv)" using BB(1-4) IntervalX_def GreaterOf_def
      by (simp)
  }
  then show "RightRayX(X, r, bu) \<inter> IntervalX(X, r, bv, cv) \<subseteq> IntervalX(X, r, GreaterOf(r, bu, bv), cv)" by auto
  {
    fix x
    assume "x\<in>IntervalX(X, r, GreaterOf(r, bu, bv), cv)"
    then have "x\<in>X""x\<in>Interval(r,GreaterOf(r, bu, bv), cv)""x\<noteq>cv""x\<noteq>GreaterOf(r, bu, bv)" using IntervalX_def by auto
    then have R:"\<langle>GreaterOf(r, bu, bv),x\<rangle>\<in>r""\<langle>x,cv\<rangle>\<in>r" using Order_ZF_2_L1A by auto
    with \<open>x\<noteq>cv\<close> have "\<langle>x,cv\<rangle>\<in>r""x\<noteq>cv" by auto
    moreover
    {
      {
        assume AS:"\<langle>bu,bv\<rangle>\<in>r"
        then have "GreaterOf(r,bu,bv)=bv" using GreaterOf_def by auto
        then have "\<langle>bv,x\<rangle>\<in>r" using R(1) by auto
        with AS have "\<langle>bu,x\<rangle>\<in>r" "\<langle>bv,x\<rangle>\<in>r" using assms unfolding IsLinOrder_def trans_def by (safe,blast)
      }
      moreover
      {
        assume AS:"\<langle>bu,bv\<rangle>\<notin>r"
        then have "GreaterOf(r,bu,bv)=bu" using GreaterOf_def by auto
        then have "\<langle>bu,x\<rangle>\<in>r" using R(1) by auto
        from AS have "\<langle>bv,bu\<rangle>\<in>r" using assms unfolding IsLinOrder_def IsTotal_def using assms by auto
        with \<open>\<langle>bu,x\<rangle>\<in>r\<close> have "\<langle>bu,x\<rangle>\<in>r" "\<langle>bv,x\<rangle>\<in>r" using assms unfolding IsLinOrder_def trans_def  by (safe,blast)
      }
      ultimately have T:"\<langle>bu,x\<rangle>\<in>r" "\<langle>bv,x\<rangle>\<in>r" by auto
      moreover
      {
        assume AS:"x=bu"
        then have "\<langle>bv,bu\<rangle>\<in>r" using T(2) by auto
        then have "GreaterOf(r,bu,bv)=bu" unfolding GreaterOf_def using assms unfolding IsLinOrder_def
        antisym_def by auto
        with \<open>x\<noteq>GreaterOf(r,bu,bv)\<close> have "False" using AS by auto
      }
      moreover
      {
        assume AS:"x=bv"
        then have "\<langle>bu,bv\<rangle>\<in>r" using T(1) by auto
        then have "GreaterOf(r,bu,bv)=bv" unfolding GreaterOf_def by auto
        with \<open>x\<noteq>GreaterOf(r,bu,bv)\<close> have "False" using AS by auto
      }
      ultimately have "\<langle>bu,x\<rangle>\<in>r" "\<langle>bv,x\<rangle>\<in>r""x\<noteq>bu""x\<noteq>bv" by auto
    }
    with calculation \<open>x\<in>X\<close> have "x\<in>RightRayX(X, r, bu)""x\<in>IntervalX(X, r, bv, cv)" unfolding RightRayX_def IntervalX_def
      using Order_ZF_2_L1 by auto
    then have "x\<in>RightRayX(X, r, bu) \<inter> IntervalX(X, r, bv, cv) " by auto
  }
  then show "IntervalX(X, r, GreaterOf(r, bu, bv), cv) \<subseteq> RightRayX(X, r, bu) \<inter> IntervalX(X, r, bv, cv) " by auto
qed


lemma inter_lray_interval:
  assumes "bv\<in>X""cu\<in>X""cv\<in>X""IsLinOrder(X,r)"
  shows "LeftRayX(X,r,cu)\<inter>IntervalX(X,r,bv,cv)=IntervalX(X,r,bv,SmallerOf(r,cu,cv))"
proof
  {
    fix x assume "x\<in>LeftRayX(X,r,cu)\<inter>IntervalX(X,r,bv,cv)"
    then have B:"x\<noteq>cu""x\<in>X""\<langle>x,cu\<rangle>\<in>r""\<langle>bv,x\<rangle>\<in>r""\<langle>x,cv\<rangle>\<in>r""x\<noteq>bv""x\<noteq>cv" unfolding LeftRayX_def IntervalX_def Interval_def
      by auto
    from \<open>\<langle>x,cu\<rangle>\<in>r\<close> \<open>\<langle>x,cv\<rangle>\<in>r\<close> have C:"\<langle>x,SmallerOf(r, cu, cv)\<rangle>\<in>r" using SmallerOf_def by (cases "\<langle>cu,cv\<rangle>\<in>r",simp+)
    from B(7,1) have "x\<noteq>SmallerOf(r,cu,cv)" using SmallerOf_def by (cases "\<langle>cu,cv\<rangle>\<in>r",simp+)
    then have "x\<in>IntervalX(X,r,bv,SmallerOf(r,cu,cv))" using B C IntervalX_def Order_ZF_2_L1 by auto
  }
  then show "LeftRayX(X, r, cu) \<inter> IntervalX(X, r, bv, cv) \<subseteq> IntervalX(X, r, bv, SmallerOf(r, cu, cv))" by auto
  {
    fix x assume "x\<in>IntervalX(X,r,bv,SmallerOf(r,cu,cv))"
    then have R:"x\<in>X""\<langle>bv,x\<rangle>\<in>r""\<langle>x,SmallerOf(r,cu,cv)\<rangle>\<in>r""x\<noteq>bv""x\<noteq>SmallerOf(r,cu,cv)" using IntervalX_def Interval_def
      by auto
    then have "\<langle>bv,x\<rangle>\<in>r""x\<noteq>bv" by auto
    moreover
    {
      {
        assume AS:"\<langle>cu,cv\<rangle>\<in>r"
        then have "SmallerOf(r,cu,cv)=cu" using SmallerOf_def by auto
        then have "\<langle>x,cu\<rangle>\<in>r" using R(3) by auto
        with AS have "\<langle>x,cu\<rangle>\<in>r" "\<langle>x,cv\<rangle>\<in>r" using assms unfolding IsLinOrder_def trans_def by (safe, blast)
      }
      moreover
      {
        assume AS:"\<langle>cu,cv\<rangle>\<notin>r"
        then have "SmallerOf(r,cu,cv)=cv" using SmallerOf_def by auto
        then have "\<langle>x,cv\<rangle>\<in>r" using R(3) by auto
        from AS have "\<langle>cv,cu\<rangle>\<in>r" using assms IsLinOrder_def IsTotal_def assms by auto
        with \<open>\<langle>x,cv\<rangle>\<in>r\<close> have "\<langle>x,cv\<rangle>\<in>r" "\<langle>x,cu\<rangle>\<in>r" using assms IsLinOrder_def trans_def by (safe, blast)
      }
      ultimately have T:"\<langle>x,cv\<rangle>\<in>r" "\<langle>x,cu\<rangle>\<in>r" by auto
      moreover
      {
        assume AS:"x=cu"
        then have "\<langle>cu,cv\<rangle>\<in>r" using T(1) by auto
        then have "SmallerOf(r,cu,cv)=cu" using SmallerOf_def assms IsLinOrder_def
          antisym_def by auto
        with \<open>x\<noteq>SmallerOf(r,cu,cv)\<close> have "False" using AS by auto
      }
      moreover
      {
        assume AS:"x=cv"
        then have "\<langle>cv,cu\<rangle>\<in>r" using T(2) by auto
        then have "SmallerOf(r,cu,cv)=cv" using SmallerOf_def assms IsLinOrder_def
        antisym_def by auto
        with \<open>x\<noteq>SmallerOf(r,cu,cv)\<close> have "False" using AS by auto
      }
      ultimately have "\<langle>x,cu\<rangle>\<in>r" "\<langle>x,cv\<rangle>\<in>r""x\<noteq>cu""x\<noteq>cv" by auto
    }
    with calculation \<open>x\<in>X\<close> have "x\<in>LeftRayX(X,r,cu)""x\<in>IntervalX(X, r, bv, cv)" using LeftRayX_def IntervalX_def Interval_def
      by auto
    then have "x\<in>LeftRayX(X, r, cu) \<inter> IntervalX(X, r, bv, cv)" by auto
  }
  then show "IntervalX(X, r, bv, SmallerOf(r, cu, cv)) \<subseteq> LeftRayX(X, r, cu) \<inter> IntervalX(X, r, bv, cv) " by auto
qed

lemma inter_lray_rray:
  assumes "bu\<in>X""cv\<in>X""IsLinOrder(X,r)"
  shows "LeftRayX(X,r,bu)\<inter>RightRayX(X,r,cv)=IntervalX(X,r,cv,bu)"
  unfolding LeftRayX_def RightRayX_def IntervalX_def Interval_def by auto

lemma inter_lray_lray:
  assumes "bu\<in>X""cv\<in>X""IsLinOrder(X,r)"
  shows "LeftRayX(X,r,bu)\<inter>LeftRayX(X,r,cv)=LeftRayX(X,r,SmallerOf(r,bu,cv))"
proof
  {
    fix x
    assume "x\<in>LeftRayX(X,r,bu)\<inter>LeftRayX(X,r,cv)"
    then have B:"x\<in>X""\<langle>x,bu\<rangle>\<in>r""\<langle>x,cv\<rangle>\<in>r""x\<noteq>bu""x\<noteq>cv" using LeftRayX_def by auto
    then have C:"\<langle>x,SmallerOf(r,bu,cv)\<rangle>\<in>r" using SmallerOf_def by (cases "\<langle>bu,cv\<rangle>\<in>r", auto)
    from B have D:"x\<noteq>SmallerOf(r,bu,cv)" using SmallerOf_def by (cases "\<langle>bu,cv\<rangle>\<in>r", auto)
    from B C D have "x\<in>LeftRayX(X,r,SmallerOf(r,bu,cv))" using LeftRayX_def by auto
  }
  then show "LeftRayX(X, r, bu) \<inter> LeftRayX(X, r, cv) \<subseteq> LeftRayX(X, r, SmallerOf(r, bu, cv))" by auto
  {
    fix x
    assume "x\<in>LeftRayX(X, r, SmallerOf(r, bu, cv))"
    then have R:"x\<in>X""\<langle>x,SmallerOf(r,bu,cv)\<rangle>\<in>r""x\<noteq>SmallerOf(r,bu,cv)" using LeftRayX_def by auto
    {
      {
        assume AS:"\<langle>bu,cv\<rangle>\<in>r"
        then have "SmallerOf(r,bu,cv)=bu" using SmallerOf_def by auto
        then have "\<langle>x,bu\<rangle>\<in>r" using R(2) by auto
        with AS have "\<langle>x,bu\<rangle>\<in>r" "\<langle>x,cv\<rangle>\<in>r" using assms IsLinOrder_def trans_def by(safe, blast)
      }
      moreover
      {
        assume AS:"\<langle>bu,cv\<rangle>\<notin>r"
        then have "SmallerOf(r,bu,cv)=cv" using SmallerOf_def by auto
        then have "\<langle>x,cv\<rangle>\<in>r" using R(2) by auto
        from AS have "\<langle>cv,bu\<rangle>\<in>r" using assms IsLinOrder_def IsTotal_def assms by auto
        with \<open>\<langle>x,cv\<rangle>\<in>r\<close> have "\<langle>x,cv\<rangle>\<in>r" "\<langle>x,bu\<rangle>\<in>r" using assms IsLinOrder_def trans_def by(safe, blast)
      }
      ultimately have T:"\<langle>x,cv\<rangle>\<in>r" "\<langle>x,bu\<rangle>\<in>r" by auto
      moreover
      {
        assume AS:"x=bu"
        then have "\<langle>bu,cv\<rangle>\<in>r" using T(1) by auto
        then have "SmallerOf(r,bu,cv)=bu" using SmallerOf_def assms IsLinOrder_def
          antisym_def by auto
        with \<open>x\<noteq>SmallerOf(r,bu,cv)\<close> have "False" using AS by auto
      }
      moreover
      {
        assume AS:"x=cv"
        then have "\<langle>cv,bu\<rangle>\<in>r" using T(2) by auto
        then have "SmallerOf(r,bu,cv)=cv" using SmallerOf_def assms IsLinOrder_def
          antisym_def by auto
        with \<open>x\<noteq>SmallerOf(r,bu,cv)\<close> have "False" using AS by auto
      }
      ultimately have "\<langle>x,bu\<rangle>\<in>r" "\<langle>x,cv\<rangle>\<in>r""x\<noteq>bu""x\<noteq>cv" by auto
    }
    with \<open>x\<in>X\<close> have "x\<in> LeftRayX(X, r, bu) \<inter> LeftRayX(X, r, cv)" using LeftRayX_def by auto
  }
  then show "LeftRayX(X, r, SmallerOf(r, bu, cv)) \<subseteq> LeftRayX(X, r, bu) \<inter> LeftRayX(X, r, cv) " by auto
qed

lemma inter_rray_rray:
  assumes "bu\<in>X""cv\<in>X""IsLinOrder(X,r)"
  shows "RightRayX(X,r,bu)\<inter>RightRayX(X,r,cv)=RightRayX(X,r,GreaterOf(r,bu,cv))"
proof
  {
    fix x
    assume "x\<in>RightRayX(X,r,bu)\<inter>RightRayX(X,r,cv)"
    then have B:"x\<in>X""\<langle>bu,x\<rangle>\<in>r""\<langle>cv,x\<rangle>\<in>r""x\<noteq>bu""x\<noteq>cv" using RightRayX_def by auto
    then have C:"\<langle>GreaterOf(r,bu,cv),x\<rangle>\<in>r" using GreaterOf_def by (cases "\<langle>bu,cv\<rangle>\<in>r",auto)
    from B have D:"x\<noteq>GreaterOf(r,bu,cv)" using GreaterOf_def by (cases "\<langle>bu,cv\<rangle>\<in>r",auto)
    from B C D have "x\<in>RightRayX(X,r,GreaterOf(r,bu,cv))" using RightRayX_def by auto
  }
  then show " RightRayX(X, r, bu) \<inter> RightRayX(X, r, cv) \<subseteq> RightRayX(X, r, GreaterOf(r, bu, cv))" by auto
  {
    fix x
    assume "x\<in>RightRayX(X, r, GreaterOf(r, bu, cv))"
    then have R:"x\<in>X""\<langle>GreaterOf(r,bu,cv),x\<rangle>\<in>r""x\<noteq>GreaterOf(r,bu,cv)" using RightRayX_def by auto
    {
      {
        assume AS:"\<langle>bu,cv\<rangle>\<in>r"
        then have "GreaterOf(r,bu,cv)=cv" using GreaterOf_def by auto
        then have "\<langle>cv,x\<rangle>\<in>r" using R(2) by auto
        with AS have "\<langle>bu,x\<rangle>\<in>r" "\<langle>cv,x\<rangle>\<in>r" using assms IsLinOrder_def trans_def by(safe, blast)
      }
      moreover
      {
        assume AS:"\<langle>bu,cv\<rangle>\<notin>r"
        then have "GreaterOf(r,bu,cv)=bu" using GreaterOf_def by auto
        then have "\<langle>bu,x\<rangle>\<in>r" using R(2) by auto
        from AS have "\<langle>cv,bu\<rangle>\<in>r" using assms IsLinOrder_def IsTotal_def assms by auto
        with \<open>\<langle>bu,x\<rangle>\<in>r\<close> have "\<langle>cv,x\<rangle>\<in>r" "\<langle>bu,x\<rangle>\<in>r" using assms IsLinOrder_def trans_def by(safe, blast)
      }
      ultimately have T:"\<langle>cv,x\<rangle>\<in>r" "\<langle>bu,x\<rangle>\<in>r" by auto
      moreover
      {
        assume AS:"x=bu"
        then have "\<langle>cv,bu\<rangle>\<in>r" using T(1) by auto
        then have "GreaterOf(r,bu,cv)=bu" using GreaterOf_def assms IsLinOrder_def
          antisym_def by auto
        with \<open>x\<noteq>GreaterOf(r,bu,cv)\<close> have "False" using AS by auto
      }
      moreover
      {
        assume AS:"x=cv"
        then have "\<langle>bu,cv\<rangle>\<in>r" using T(2) by auto
        then have "GreaterOf(r,bu,cv)=cv" using GreaterOf_def assms IsLinOrder_def
          antisym_def by auto
        with \<open>x\<noteq>GreaterOf(r,bu,cv)\<close> have "False" using AS by auto
      }
      ultimately have "\<langle>bu,x\<rangle>\<in>r" "\<langle>cv,x\<rangle>\<in>r""x\<noteq>bu""x\<noteq>cv" by auto
    }
    with \<open>x\<in>X\<close> have "x\<in> RightRayX(X, r, bu) \<inter> RightRayX(X, r, cv) " using RightRayX_def by auto
  }
  then show "RightRayX(X, r, GreaterOf(r, bu, cv)) \<subseteq> RightRayX(X, r, bu) \<inter> RightRayX(X, r, cv)" by auto
qed

text\<open>The open intervals and rays satisfy the base condition.\<close>

lemma intervals_rays_base_condition:
  assumes "IsLinOrder(X,r)"
  shows "{IntervalX(X,r,b,c). \<langle>b,c\<rangle>\<in>X\<times>X}\<union>{LeftRayX(X,r,b). b\<in>X}\<union>{RightRayX(X,r,b). b\<in>X} {satisfies the base condition}"
proof-
  let ?I="{IntervalX(X,r,b,c). \<langle>b,c\<rangle>\<in>X\<times>X}"
  let ?R="{RightRayX(X,r,b). b\<in>X}"
  let ?L="{LeftRayX(X,r,b). b\<in>X}"
  let ?B="{IntervalX(X,r,b,c). \<langle>b,c\<rangle>\<in>X\<times>X}\<union>{LeftRayX(X,r,b). b\<in>X}\<union>{RightRayX(X,r,b). b\<in>X}"
  {
    fix U V
    assume A:"U\<in>?B""V\<in>?B"
    then have dU:"U\<in>?I\<or>U\<in>?L\<or>U\<in>?R"and dV:"V\<in>?I\<or>V\<in>?L\<or>V\<in>?R" by auto
    {
      assume S:"V\<in>?I"
      {
        assume "U\<in>?I"
        with S obtain bu cu bv cv where A:"U=IntervalX(X,r,bu,cu)""V=IntervalX(X,r,bv,cv)""bu\<in>X""cu\<in>X""bv\<in>X""cv\<in>X"
          by auto
        then have "SmallerOf(r,cu,cv)\<in>X""GreaterOf(r,bu,bv)\<in>X" by (cases "\<langle>cu,cv\<rangle>\<in>r",simp add:SmallerOf_def A,simp add:SmallerOf_def A,
          cases "\<langle>bu,bv\<rangle>\<in>r",simp add:GreaterOf_def A,simp add:GreaterOf_def A)
        with A have "U\<inter>V\<in>?B" using inter_two_intervals assms by auto
      }
      moreover
      {
        assume "U\<in>?L"
        with S obtain bu bv cv where A:"U=LeftRayX(X, r,bu)""V=IntervalX(X,r,bv,cv)""bu\<in>X""bv\<in>X""cv\<in>X"
        by auto
        then have "SmallerOf(r,bu,cv)\<in>X" using SmallerOf_def by (cases "\<langle>bu,cv\<rangle>\<in>r",auto)
        with A have "U\<inter>V\<in>?B" using inter_lray_interval assms by auto
      }
      moreover
      {
        assume "U\<in>?R" 
        with S obtain cu bv cv where A:"U=RightRayX(X,r,cu)""V=IntervalX(X,r,bv,cv)""cu\<in>X""bv\<in>X""cv\<in>X"
        by auto
        then have "GreaterOf(r,cu,bv)\<in>X" using GreaterOf_def by (cases "\<langle>cu,bv\<rangle>\<in>r",auto)
        with A have "U\<inter>V\<in>?B" using inter_rray_interval assms by auto
      }
      ultimately have "U\<inter>V\<in>?B" using dU by auto
    }
    moreover
    {
      assume S:"V\<in>?L" 
      {
        assume "U\<in>?I"
        with S obtain bu bv cv where A:"V=LeftRayX(X, r,bu)""U=IntervalX(X,r,bv,cv)""bu\<in>X""bv\<in>X""cv\<in>X"
          by auto
        then have "SmallerOf(r,bu,cv)\<in>X" using SmallerOf_def by (cases "\<langle>bu,cv\<rangle>\<in>r", auto)
        have "U\<inter>V=V\<inter>U" by auto
        with A \<open>SmallerOf(r,bu,cv)\<in>X\<close> have "U\<inter>V\<in>?B" using inter_lray_interval assms by auto
      }
      moreover
      {
        assume "U\<in>?R"
        with S obtain bu cv where A:"V=LeftRayX(X,r,bu)""U=RightRayX(X,r,cv)""bu\<in>X""cv\<in>X"
        by auto
        have "U\<inter>V=V\<inter>U" by auto
        with A have "U\<inter>V\<in>?B" using inter_lray_rray assms by auto
      }
      moreover
      {
        assume "U\<in>?L"
        with S obtain bu bv where A:"U=LeftRayX(X,r,bu)""V=LeftRayX(X,r,bv)""bu\<in>X""bv\<in>X"
        by auto
        then have "SmallerOf(r,bu,bv)\<in>X" using SmallerOf_def by (cases "\<langle>bu,bv\<rangle>\<in>r", auto)
        with A have "U\<inter>V\<in>?B" using inter_lray_lray assms by auto
      }
      ultimately have "U\<inter>V\<in>?B" using dU by auto
    }
    moreover
    {
      assume S:"V\<in>?R"
      {
        assume "U\<in>?I"
        with S obtain cu bv cv where A:"V=RightRayX(X,r,cu)""U=IntervalX(X,r,bv,cv)""cu\<in>X""bv\<in>X""cv\<in>X"
        by auto
        then have "GreaterOf(r,cu,bv)\<in>X" using GreaterOf_def by (cases "\<langle>cu,bv\<rangle>\<in>r",auto)
        have "U\<inter>V=V\<inter>U" by auto
        with A \<open>GreaterOf(r,cu,bv)\<in>X\<close> have "U\<inter>V\<in>?B" using inter_rray_interval assms by auto
      }
      moreover
      {
        assume "U\<in>?L" 
        with S obtain bu cv where A:"U=LeftRayX(X,r,bu)""V=RightRayX(X,r,cv)""bu\<in>X""cv\<in>X"
        by auto
        then have "U\<inter>V\<in>?B" using inter_lray_rray assms by auto
      }
      moreover
      {
        assume "U\<in>?R" 
        with S obtain cu cv where A:"U=RightRayX(X,r,cu)""V=RightRayX(X,r,cv)""cu\<in>X""cv\<in>X"
        by auto
        then have "GreaterOf(r,cu,cv)\<in>X" using GreaterOf_def by (cases "\<langle>cu,cv\<rangle>\<in>r",auto)
        with A have "U\<inter>V\<in>?B" using inter_rray_rray assms by auto
      }
      ultimately have "U\<inter>V\<in>?B" using dU by auto
    }
    ultimately have  S:"U\<inter>V\<in>?B" using dV by auto
    {
      fix x
      assume "x\<in>U\<inter>V"
      then have "x\<in>U\<inter>V\<and>U\<inter>V\<subseteq>U\<inter>V" by auto
      then have "\<exists>W. W\<in>(?B)\<and> x\<in>W \<and> W \<subseteq> U\<inter>V" using S by blast
      then have "\<exists>W\<in>(?B). x\<in>W \<and> W \<subseteq> U\<inter>V" by blast
    }
    hence "(\<forall>x \<in> U\<inter>V. \<exists>W\<in>(?B). x\<in>W \<and> W \<subseteq> U\<inter>V)" by auto
  }
  then show ?thesis using SatisfiesBaseCondition_def by auto
qed

text\<open>Since the intervals and rays form a base of a topology, and this topology
is uniquely determined; we can built it. In the definition
we have to make sure that we have a totally ordered set.\<close>

definition 
  OrderTopology ("OrdTopology _ _" 50) where
  "IsLinOrder(X,r) \<Longrightarrow> OrdTopology X r \<equiv> TopologyBase {IntervalX(X,r,b,c). \<langle>b,c\<rangle>\<in>X\<times>X}\<union>{LeftRayX(X,r,b). b\<in>X}\<union>{RightRayX(X,r,b). b\<in>X}"

theorem Ordtopology_is_a_topology:
  assumes "IsLinOrder(X,r)"
  shows "(OrdTopology X r) {is a topology}" and "{IntervalX(X,r,b,c). \<langle>b,c\<rangle>\<in>X\<times>X}\<union>{LeftRayX(X,r,b). b\<in>X}\<union>{RightRayX(X,r,b). b\<in>X} {is a base for} (OrdTopology X r)"
  using assms Base_topology_is_a_topology intervals_rays_base_condition 
    OrderTopology_def by auto

lemma topology0_ordtopology:
  assumes "IsLinOrder(X,r)"
  shows "topology0(OrdTopology X r)"
  using Ordtopology_is_a_topology topology0_def assms by auto

subsection\<open>Total set\<close>

text\<open>The topology is defined in the set $X$, when $X$ has more than 
one point\<close>

lemma union_ordtopology:
  assumes "IsLinOrder(X,r)""\<exists>x y. x\<noteq>y \<and> x\<in>X\<and> y\<in>X"
  shows "\<Union>(OrdTopology X r)=X"
proof
  let ?B="{IntervalX(X,r,b,c). \<langle>b,c\<rangle>\<in>X\<times>X}\<union>{LeftRayX(X,r,b). b\<in>X}\<union>{RightRayX(X,r,b). b\<in>X}"
  have base:"?B {is a base for} (OrdTopology X r)" using Ordtopology_is_a_topology(2) assms(1)
    by auto
  from assms(2) obtain x y where T:"x\<noteq>y \<and> x\<in>X\<and> y\<in>X" by auto
  then have B:"x\<in>LeftRayX(X,r,y)\<or>x\<in>RightRayX(X,r,y)" using LeftRayX_def RightRayX_def
    assms(1) IsLinOrder_def IsTotal_def by auto
  then have "x\<in>\<Union>?B" using T by auto
  then have x:"x\<in>\<Union>(OrdTopology X r)" using Top_1_2_L5 base by auto
  {
    fix z
    assume z:"z\<in>X"
    {
      assume "x=z"
      then have "z\<in>\<Union>(OrdTopology X r)" using x by auto
    }
    moreover
    {
      assume "x\<noteq>z"
      with z T have "z\<in>LeftRayX(X,r,x)\<or>z\<in>RightRayX(X,r,x)""x\<in>X" using LeftRayX_def RightRayX_def
        assms(1) IsLinOrder_def IsTotal_def by auto
      then have "z\<in>\<Union>?B" by auto
      then have "z\<in>\<Union>(OrdTopology X r)" using Top_1_2_L5 base by auto
    }
    ultimately have "z\<in>\<Union>(OrdTopology X r)" by auto
  }
  then show "X\<subseteq>\<Union>(OrdTopology X r)" by auto
  have "\<Union>?B\<subseteq>X" using IntervalX_def LeftRayX_def RightRayX_def by auto
  then show "\<Union>(OrdTopology X r)\<subseteq>X" using Top_1_2_L5 base by auto
qed

text\<open>The interior, closure and boundary can be calculated using the formulas
proved in the section that deals with the base.\<close>

text\<open>The subspace of an order topology doesn't have to be an
order topology.\<close>

(*Note: Build a counter-example using the real numbers.*)

subsection\<open>Right order and Left order topologies.\<close>

text\<open>Notice that the left and right rays are closed under
intersection, hence they form a base of a topology.
They are called right order topology and left order topology
respectively.\<close>

text\<open>If the order in $X$ has a minimal or a maximal element,
is necessary to consider $X$ as an element of the base
or that limit point wouldn't be in any basic open set.\<close>

subsubsection\<open>Right and Left Order topologies are topologies\<close>

lemma leftrays_base_condition:
assumes "IsLinOrder(X,r)"
shows "{LeftRayX(X,r,b). b\<in>X}\<union>{X} {satisfies the base condition}"
proof-
  {
    fix U V
    assume "U\<in>{LeftRayX(X,r,b). b\<in>X}\<union>{X}""V\<in>{LeftRayX(X,r,b). b\<in>X}\<union>{X}"
    then obtain b c where A:"(b\<in>X\<and>U=LeftRayX(X,r,b))\<or>U=X""(c\<in>X\<and>V=LeftRayX(X,r,c))\<or>V=X""U\<subseteq>X""V\<subseteq>X"
    unfolding LeftRayX_def by auto
    then have "(U\<inter>V=LeftRayX(X,r,SmallerOf(r,b,c))\<and>b\<in>X\<and>c\<in>X)\<or>U\<inter>V=X\<or>(U\<inter>V=LeftRayX(X,r,c)\<and>c\<in>X)\<or>(U\<inter>V=LeftRayX(X,r,b)\<and>b\<in>X)"
      using inter_lray_lray assms by auto
    moreover
    have "b\<in>X\<and>c\<in>X \<longrightarrow> SmallerOf(r,b,c)\<in>X" unfolding SmallerOf_def by (cases "\<langle>b,c\<rangle>\<in>r",auto)
    ultimately have "U\<inter>V\<in>{LeftRayX(X,r,b). b\<in>X}\<union>{X}" by auto
    hence "\<forall>x\<in>U\<inter>V. \<exists>W\<in>{LeftRayX(X,r,b). b\<in>X}\<union>{X}. x\<in>W\<and>W\<subseteq>U\<inter>V" by blast
  }
  moreover
  then show ?thesis using SatisfiesBaseCondition_def by auto
qed

lemma rightrays_base_condition:
assumes "IsLinOrder(X,r)"
shows "{RightRayX(X,r,b). b\<in>X}\<union>{X} {satisfies the base condition}"
proof-
  {
    fix U V
    assume "U\<in>{RightRayX(X,r,b). b\<in>X}\<union>{X}""V\<in>{RightRayX(X,r,b). b\<in>X}\<union>{X}"
    then obtain b c where A:"(b\<in>X\<and>U=RightRayX(X,r,b))\<or>U=X""(c\<in>X\<and>V=RightRayX(X,r,c))\<or>V=X""U\<subseteq>X""V\<subseteq>X"
    unfolding RightRayX_def by auto
    then have "(U\<inter>V=RightRayX(X,r,GreaterOf(r,b,c))\<and>b\<in>X\<and>c\<in>X)\<or>U\<inter>V=X\<or>(U\<inter>V=RightRayX(X,r,c)\<and>c\<in>X)\<or>(U\<inter>V=RightRayX(X,r,b)\<and>b\<in>X)" 
      using inter_rray_rray assms by auto
    moreover
    have "b\<in>X\<and>c\<in>X \<longrightarrow> GreaterOf(r,b,c)\<in>X" using GreaterOf_def by (cases "\<langle>b,c\<rangle>\<in>r",auto)
    ultimately have "U\<inter>V\<in>{RightRayX(X,r,b). b\<in>X}\<union>{X}" by auto
    hence "\<forall>x\<in>U\<inter>V. \<exists>W\<in>{RightRayX(X,r,b). b\<in>X}\<union>{X}. x\<in>W\<and>W\<subseteq>U\<inter>V" by blast
  }
  then show ?thesis using SatisfiesBaseCondition_def by auto
qed

definition 
  LeftOrderTopology ("LOrdTopology _ _" 50) where
  "IsLinOrder(X,r) \<Longrightarrow> LOrdTopology X r \<equiv> TopologyBase {LeftRayX(X,r,b). b\<in>X}\<union>{X}"

definition 
  RightOrderTopology ("ROrdTopology _ _" 50) where
  "IsLinOrder(X,r) \<Longrightarrow> ROrdTopology X r \<equiv> TopologyBase {RightRayX(X,r,b). b\<in>X}\<union>{X}"

theorem LOrdtopology_ROrdtopology_are_topologies:
  assumes "IsLinOrder(X,r)"
  shows "(LOrdTopology X r) {is a topology}" and "{LeftRayX(X,r,b). b\<in>X}\<union>{X} {is a base for} (LOrdTopology X r)"
  and "(ROrdTopology X r) {is a topology}" and "{RightRayX(X,r,b). b\<in>X}\<union>{X} {is a base for} (ROrdTopology X r)"
  using Base_topology_is_a_topology leftrays_base_condition assms rightrays_base_condition
     LeftOrderTopology_def RightOrderTopology_def by auto

lemma topology0_lordtopology_rordtopology:
  assumes "IsLinOrder(X,r)"
  shows  "topology0(LOrdTopology X r)" and "topology0(ROrdTopology X r)"
  using LOrdtopology_ROrdtopology_are_topologies topology0_def assms by auto

subsubsection\<open>Total set\<close>

text\<open>The topology is defined on the set $X$\<close>

lemma union_lordtopology_rordtopology:
  assumes "IsLinOrder(X,r)"
  shows "\<Union>(LOrdTopology X r)=X" and "\<Union>(ROrdTopology X r)=X" 
  using Top_1_2_L5[OF LOrdtopology_ROrdtopology_are_topologies(2)[OF assms]]
    Top_1_2_L5[OF LOrdtopology_ROrdtopology_are_topologies(4)[OF assms]]
  unfolding LeftRayX_def RightRayX_def by auto

subsection\<open>Union of Topologies\<close>

text\<open>The union of two topologies is not a topology. A way to 
overcome this fact is to define the following topology:\<close>

definition
  joinT ("joinT _" 90) where
  "(\<forall>T\<in>M. T{is a topology} \<and> (\<forall>Q\<in>M. \<Union>Q=\<Union>T)) \<Longrightarrow> (joinT M \<equiv> THE T. (\<Union>M){is a subbase for} T)"

text\<open>First let's proof that given a family of sets, then it is a subbase
for a topology.\<close>

text\<open>The first result states that from any family of sets
we get a base using finite intersections of them.
The second one states that any family of sets is a subbase
of some topology.\<close>

theorem subset_as_subbase:
  shows "{\<Inter>A. A \<in> FinPow(B)} {satisfies the base condition}"
proof-
  {
    fix U V
    assume A:"U\<in>{\<Inter>A. A \<in> FinPow(B)} \<and> V\<in>{\<Inter>A. A \<in> FinPow(B)}"
    then obtain M R where MR:"Finite(M)""Finite(R)""M\<subseteq>B""R\<subseteq>B"
    "U=\<Inter>M""V=\<Inter>R"
    using FinPow_def by auto
    {
      fix x
      assume AS:"x\<in>U\<inter>V"
      then have N:"M\<noteq>0""R\<noteq>0" using MR(5,6) by auto
      have "Finite(M \<union>R)" using MR(1,2) by auto
      moreover
      have "M \<union> R\<in>Pow(B)" using MR(3,4) by auto
      ultimately have "M\<union>R\<in>FinPow(B)" using FinPow_def by auto
      then have "\<Inter>(M\<union>R)\<in>{\<Inter>A. A \<in> FinPow(B)}" by auto
      moreover
      from N have "\<Inter>(M\<union>R)\<subseteq>\<Inter>M""\<Inter>(M\<union>R)\<subseteq>\<Inter>R" by auto
      then have "\<Inter>(M\<union>R)\<subseteq>U\<inter>V" using MR(5,6) by auto
      moreover
      {
        fix S
        assume "S\<in>M \<union> R"
        then have "S\<in>M\<or>S\<in>R" by auto
        then have "x\<in>S" using AS MR(5,6) by auto
      }
      then have "x\<in>\<Inter>(M \<union> R)" using N by auto
      ultimately have "\<exists>W\<in>{\<Inter>A. A \<in> FinPow(B)}. x\<in>W\<and>W\<subseteq>U\<inter>V" by blast
    }
    then have "(\<forall>x \<in> U\<inter>V. \<exists>W\<in>{\<Inter>A. A \<in> FinPow(B)}. x\<in>W \<and> W \<subseteq> U\<inter>V)" by auto
  }
  then have "\<forall>U V. ((U\<in>{\<Inter>A. A \<in> FinPow(B)} \<and> V\<in>{\<Inter>A. A \<in> FinPow(B)}) \<longrightarrow> 
    (\<forall>x \<in> U\<inter>V. \<exists>W\<in>{\<Inter>A. A \<in> FinPow(B)}. x\<in>W \<and> W \<subseteq> U\<inter>V))" by auto
  then show "{\<Inter>A. A \<in> FinPow(B)} {satisfies the base condition}"
    using SatisfiesBaseCondition_def by auto
qed

theorem Top_subbase:
  assumes "T = {\<Union>A. A\<in>Pow({\<Inter>A. A \<in> FinPow(B)})}"
  shows "T {is a topology}" and "B {is a subbase for} T"
proof-
  {
    fix S
    assume "S\<in>B"
    then have "{S}\<in>FinPow(B)""\<Inter>{S}=S" using FinPow_def by auto
    then have "{S}\<in>Pow({\<Inter>A. A \<in> FinPow(B)})" by (blast+)
    then have "\<Union>{S}\<in>{\<Union>A. A\<in>Pow({\<Inter>A. A \<in> FinPow(B)})}" by blast
    then have "S\<in>{\<Union>A. A\<in>Pow({\<Inter>A. A \<in> FinPow(B)})}" by auto
    then have "S\<in>T" using assms by auto
  }
  then have "B\<subseteq>T" by auto
  moreover
  have "{\<Inter>A. A \<in> FinPow(B)} {satisfies the base condition}"
    using subset_as_subbase by auto
  then have "T {is a topology}" and "{\<Inter>A. A \<in> FinPow(B)} {is a base for} T"
    using Top_1_2_T1 assms by auto
  ultimately show "T {is a topology}" and "B{is a subbase for}T"
    using IsAsubBaseFor_def by auto
qed

text\<open>A subbase defines a unique topology.\<close>

theorem same_subbase_same_top:
  assumes "B {is a subbase for} T" and "B {is a subbase for} S" 
  shows "T = S"
  using IsAsubBaseFor_def assms same_base_same_top
  by auto

end
