(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2019-2022 Slawomir Kolodynski

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

section \<open> Topology and neighborhoods \<close>

theory Topology_ZF_4a imports Topology_ZF_4
begin

text\<open> This theory considers the relations between topology and systems of neighborhood filters. \<close>

subsection\<open> Neighborhood systems \<close>

text\<open> The standard way of defining a topological space is by specifying a collection
of sets that we consider "open" (see the \<open>Topology_ZF\<close> theory). 
An alternative of this approach is to define a collection of neighborhoods for each point of 
the space.  \<close>

text\<open> We define a neighborhood system as a function that takes each point $x\in X$ and assigns it 
  a collection of subsets of $X$ which is called the neighborhoods of $x$. 
  The neighborhoods of a point $x$ form a filter that satisfies an additional
  axiom that for every neighborhood $N$ of $x$ we can find another one $U$ such that $N$ 
  is a neighborhood of every point of $U$. \<close>

definition
  IsNeighSystem ("_ {is a neighborhood system on} _" 90)
  where "\<M> {is a neighborhood system on} X \<equiv> (\<M> : X\<rightarrow>Pow(Pow(X))) \<and>
  (\<forall>x\<in>X. (\<M>`(x) {is a filter on} X) \<and> (\<forall>N\<in>\<M>`(x). x\<in>N \<and> (\<exists>U\<in>\<M>`(x).\<forall>y\<in>U.(N\<in>\<M>`(y)) ) ))"

text\<open> A neighborhood system on $X$ consists of collections of subsets of $X$. \<close>

lemma neighborhood_subset:
  assumes "\<M> {is a neighborhood system on} X" and "x\<in>X" and "N\<in>\<M>`(x)"
  shows "N\<subseteq>X" and "x\<in>N"
proof -
  from \<open>\<M> {is a neighborhood system on} X\<close> have "\<M> : X\<rightarrow>Pow(Pow(X))"
    unfolding IsNeighSystem_def by simp
  with \<open>x\<in>X\<close> have "\<M>`(x) \<in> Pow(Pow(X))" using apply_funtype by blast
  with \<open>N\<in>\<M>`(x)\<close> show "N\<subseteq>X" by blast
  from assms show "x\<in>N" using IsNeighSystem_def by simp
qed

text\<open>Some sources (like Wikipedia) use a bit different definition of neighborhood systems
where the $U$ is required to be contained in $N$. The next lemma shows that this stronger version 
can be recovered from our definition. \<close>

lemma neigh_def_stronger:
  assumes "\<M> {is a neighborhood system on} X" and "x\<in>X" and "N\<in>\<M>`(x)"
  shows "\<exists>U\<in>\<M>`(x).U\<subseteq>N \<and> (\<forall>y\<in>U.(N\<in>\<M>`(y)))" 
proof -
  from assms obtain W where "W\<in>\<M>`(x)" and areNeigh:"\<forall>y\<in>W.(N\<in>\<M>`(y))"
    using  IsNeighSystem_def by blast
  let ?U = "N\<inter>W"
  from assms \<open>W\<in>\<M>`(x)\<close> have "?U \<in> \<M>`(x)" 
    unfolding IsNeighSystem_def IsFilter_def by blast 
  moreover have "?U\<subseteq>N" by blast
  moreover from areNeigh have "\<forall>y\<in>?U.(N\<in>\<M>`(y))" by auto 
  ultimately show ?thesis by auto 
qed

subsection\<open> From a neighborhood system to topology \<close>

text\<open>Given a neighborhood system $\{\mathcal{M}_x\}_{x\in X}$ we can define a topology on $X$.
Namely, we consider a subset of $X$ open if $U \in \mathcal{M}_x$ for every element $x$ of $U$. \<close>

text\<open>The collection of sets defined as above is indeed a topology. \<close>

theorem topology_from_neighs: 
  assumes "\<M> {is a neighborhood system on} X"
  defines Tdef: "T \<equiv> {U\<in>Pow(X). \<forall>x\<in>U. U \<in> \<M>`(x)}"
  shows "T {is a topology}" and "\<Union>T = X"
proof -
  { fix \<UU> assume "\<UU> \<in> Pow(T)"
    have "\<Union>\<UU> \<in> T"
    proof -
      from \<open>\<UU> \<in> Pow(T)\<close> Tdef have "\<Union>\<UU> \<in> Pow(X)" by blast
      moreover
      { fix x assume "x \<in> \<Union>\<UU>"
        then obtain U where "U\<in>\<UU>" and "x\<in>U" by blast
        with assms \<open>\<UU> \<in> Pow(T)\<close> 
        have "U \<in> \<M>`(x)" and "U \<subseteq> \<Union>\<UU>" and  "\<M>`(x) {is a filter on} X"
          unfolding IsNeighSystem_def by auto
        with \<open>\<Union>\<UU> \<in> Pow(X)\<close> have "\<Union>\<UU> \<in> \<M>`(x)" unfolding IsFilter_def
          by simp
      } 
      ultimately show "\<Union>\<UU> \<in> T" using Tdef by blast
    qed 
  }        
  moreover
  { fix U V assume "U\<in>T" and "V\<in>T"
    have "U\<inter>V \<in> T"
    proof -
      from Tdef \<open>U\<in>T\<close>  \<open>U\<in>T\<close> have "U\<inter>V \<in> Pow(X)" by auto 
      moreover
      { fix x assume "x \<in> U\<inter>V"
        with assms \<open>U\<in>T\<close> \<open>V\<in>T\<close> Tdef have "U \<in> \<M>`(x)" "V \<in> \<M>`(x)" and  "\<M>`(x) {is a filter on} X"
          unfolding IsNeighSystem_def by auto 
        then have "U\<inter>V \<in> \<M>`(x)" unfolding IsFilter_def by simp
      }
      ultimately show "U\<inter>V \<in>T" using Tdef by simp
    qed
  }
  ultimately show "T {is a topology}" unfolding IsATopology_def by blast 
  from assms show "\<Union>T = X" unfolding IsNeighSystem_def IsFilter_def by blast
qed

text\<open> Some sources (like Wikipedia) define the open sets generated by a neighborhood system
  "as those sets containing a neighborhood of each of their points". The next lemma shows that
  this definition is equivalent to the one we are using.\<close>

lemma topology_from_neighs1:
  assumes "\<M> {is a neighborhood system on} X"
  shows "{U\<in>Pow(X). \<forall>x\<in>U. U \<in> \<M>`(x)} = {U\<in>Pow(X). \<forall>x\<in>U. \<exists>V \<in> \<M>`(x). V\<subseteq>U}"
proof
  let ?T = "{U\<in>Pow(X). \<forall>x\<in>U. U \<in> \<M>`(x)}"
  let ?S = "{U\<in>Pow(X). \<forall>x\<in>U. \<exists>V \<in> \<M>`(x). V\<subseteq>U}"
  show "?S\<subseteq>?T"
  proof -
    { fix U assume "U\<in>?S"
      then have "U\<in>Pow(X)" by simp
      moreover
      from assms \<open>U\<in>?S\<close> \<open>U\<in>Pow(X)\<close> have "\<forall>x\<in>U. U \<in> \<M>`(x)"
        unfolding IsNeighSystem_def IsFilter_def by blast 
      ultimately have "U\<in>?T" by auto
    } thus ?thesis by auto
  qed
  show "?T\<subseteq>?S" by auto
qed

subsection\<open>From a topology to a neighborhood system\<close>

text\<open> Once we have a topology $T$ we can define a natural neighborhood system on $X=\bigcup T$. 
  In this section we define such neighborhood system and prove its basic properties.  \<close>

text\<open>For a topology $T$ we define a neighborhood system of $T$ as a function that takes an $x\in X=\bigcup T$ 
and assigns it the collection of supersets of open sets containing $x$. 
We call that the "neighborhood system of $T$"\<close>

definition
  NeighSystem ("{neighborhood system of} _" 91)
  where "{neighborhood system of} T \<equiv> { \<langle>x,{N\<in>Pow(\<Union>T).\<exists>U\<in>T.(x\<in>U \<and> U\<subseteq>N)}\<rangle>. x \<in> \<Union>T }" 

text\<open>The way we defined the neighborhood system of $T$ means that
  it is a function on $\bigcup T$. \<close>

lemma neigh_fun: shows "({neighborhood system of} T): \<Union>T \<rightarrow> Pow(Pow(\<Union>T))"
proof -
  let ?X = "\<Union>T"
  have "\<forall>x\<in>?X. {N\<in>Pow(?X).\<exists>U\<in>T.(x\<in>U \<and> U\<subseteq>N)} \<in> Pow(Pow(?X))"
    by blast
  then show ?thesis unfolding NeighSystem_def using ZF_fun_from_total
    by simp
qed 

text\<open>The value of the neighborhood system of $T$ at $x\in \bigcup T$ 
  is the collection of supersets of open sets containing $x$.\<close>

lemma neigh_val: assumes "x\<in>\<Union>T"
  shows "({neighborhood system of} T)`(x) = {N\<in>Pow(\<Union>T).\<exists>U\<in>T.(x\<in>U \<and> U\<subseteq>N)}"
  using assms ZF_fun_from_tot_val1 unfolding NeighSystem_def
  by simp
  
text\<open> The next lemma shows that open sets are members of (what we will prove later to be)
   the natural neighborhood system on $X=\bigcup T$. \<close>

lemma open_are_neighs:
  assumes "U\<in>T" "x\<in>U"
  shows "x \<in> \<Union>T" and "U \<in> {V\<in>Pow(\<Union>T).\<exists>U\<in>T.(x\<in>U \<and> U\<subseteq>V)}"
  using assms by auto
  
text\<open> Another fact we will need is that for every $x\in X=\bigcup T$ the neighborhoods of $x$
  form a filter \<close>

lemma neighs_is_filter:
  assumes "T {is a topology}" and "x \<in> \<Union>T" 
  defines Mdef: "\<M> \<equiv> {neighborhood system of} T"
  shows "\<M>`(x) {is a filter on} (\<Union>T)"
proof -
  let ?X = "\<Union>T"
  let ?\<FF> = "{V\<in>Pow(?X).\<exists>U\<in>T.(x\<in>U \<and> U\<subseteq>V)}"
  have "0\<notin>?\<FF>" by blast 
  moreover have "?X\<in>?\<FF>"
  proof -
    from assms \<open>x\<in>?X\<close> have "?X \<in> Pow(?X)" "?X\<in>T" and "x\<in>?X \<and> ?X\<subseteq>?X" using carr_open 
      by auto
    hence "\<exists>U\<in>T.(x\<in>U \<and> U\<subseteq>?X)" by auto
    thus ?thesis by auto
  qed
  moreover have "\<forall>A\<in>?\<FF>. \<forall>B\<in>?\<FF>. A\<inter>B \<in> ?\<FF>"
  proof -
    { fix A B assume "A\<in>?\<FF>" "B\<in>?\<FF>"
      then obtain U\<^sub>A U\<^sub>B where "U\<^sub>A\<in>T" "x\<in>U\<^sub>A" "U\<^sub>A\<subseteq>A" "U\<^sub>B\<in>T" "x\<in>U\<^sub>B" "U\<^sub>B\<subseteq>B" 
        by auto
      with \<open>T {is a topology}\<close> \<open>A\<in>?\<FF>\<close> \<open>B\<in>?\<FF>\<close> have "A\<inter>B \<in> Pow(?X)" and 
        "U\<^sub>A\<inter>U\<^sub>B \<in> T" "x \<in> U\<^sub>A\<inter>U\<^sub>B" "U\<^sub>A\<inter>U\<^sub>B \<subseteq> A\<inter>B" using IsATopology_def 
        by auto
      hence "A\<inter>B \<in> ?\<FF>" by blast
    } thus ?thesis by blast
  qed
  moreover have "\<forall>B\<in>?\<FF>. \<forall>C\<in>Pow(?X). B\<subseteq>C \<longrightarrow> C\<in>?\<FF>"
  proof -
    { fix B C assume "B\<in>?\<FF>" "C \<in> Pow(?X)" "B\<subseteq>C"
      then obtain U where "U\<in>T" and "x\<in>U" "U\<subseteq>B" by blast
      with \<open>C \<in> Pow(?X)\<close> \<open>B\<subseteq>C\<close> have "C\<in>?\<FF>" by blast
    } thus ?thesis by auto
  qed
  ultimately have "?\<FF> {is a filter on} ?X" unfolding IsFilter_def by blast
  with Mdef \<open>x\<in>?X\<close> show "\<M>`(x) {is a filter on} ?X" using ZF_fun_from_tot_val1 NeighSystem_def
    by simp
qed

text\<open>The next theorem states that the the natural 
  neighborhood system on $X=\bigcup T$ indeed is a neighborhood system. \<close>

theorem neigh_from_topology:
  assumes "T {is a topology}"
  shows "({neighborhood system of} T) {is a neighborhood system on} (\<Union>T)"
proof -
  let ?X = "\<Union>T"
  let ?\<M> = "{neighborhood system of} T" 
  have "?\<M> : ?X\<rightarrow>Pow(Pow(?X))"
  proof -
    { fix x assume "x\<in>?X"
      hence "{V\<in>Pow(\<Union>T).\<exists>U\<in>T.(x\<in>U \<and> U\<subseteq>V)} \<in> Pow(Pow(?X))" by auto
    } hence "\<forall>x\<in>?X. {V\<in>Pow(\<Union>T).\<exists>U\<in>T.(x\<in>U \<and> U\<subseteq>V)} \<in> Pow(Pow(?X))" by auto
    then show ?thesis using ZF_fun_from_total NeighSystem_def by simp
  qed
  moreover from assms have "\<forall>x\<in>?X. (?\<M>`(x) {is a filter on} ?X)"
    using neighs_is_filter NeighSystem_def by auto 
  moreover have "\<forall>x\<in>?X. \<forall>N\<in>?\<M>`(x). x\<in>N \<and> (\<exists>U\<in>?\<M>`(x).\<forall>y\<in>U.(N\<in>?\<M>`(y)))"
  proof -
    { fix x N assume "x\<in>?X" "N \<in> ?\<M>`(x)"
      let ?\<FF> = "{V\<in>Pow(?X).\<exists>U\<in>T.(x\<in>U \<and> U\<subseteq>V)}"
      from \<open>x\<in>?X\<close> have "?\<M>`(x) = ?\<FF>" using ZF_fun_from_tot_val1 NeighSystem_def 
        by simp
      with \<open>N \<in> ?\<M>`(x)\<close> have "N\<in>?\<FF>" by simp
      hence "x\<in>N" by blast
      from \<open>N\<in>?\<FF>\<close> obtain U where "U\<in>T" "x\<in>U" and "U\<subseteq>N" by blast 
      with \<open>N\<in>?\<FF>\<close> \<open>?\<M>`(x) = ?\<FF>\<close> have "U \<in> ?\<M>`(x)" by auto 
      moreover from assms \<open>U\<in>T\<close>  \<open>U\<subseteq>N\<close> \<open>N\<in>?\<FF>\<close> have  "\<forall>y\<in>U.(N \<in> ?\<M>`(y))"
        using ZF_fun_from_tot_val1 open_are_neighs neighs_is_filter 
                NeighSystem_def IsFilter_def by auto
      ultimately have "\<exists>U\<in>?\<M>`(x).\<forall>y\<in>U.(N\<in>?\<M>`(y))" by blast
      with \<open>x\<in>N\<close> have "x\<in>N \<and> (\<exists>U\<in>?\<M>`(x).\<forall>y\<in>U.(N\<in>?\<M>`(y)))" by simp      
    } thus ?thesis by auto 
  qed
  ultimately show ?thesis unfolding IsNeighSystem_def by blast
qed

text\<open>Any neighborhood of an element of the closure of a subset intersects the subset.\<close>

lemma neigh_inter_nempty: 
  assumes "T {is a topology}" "A\<subseteq>\<Union>T" "x \<in> Closure(A,T)" and
  "N \<in> ({neighborhood system of} T)`(x)"
  shows "N\<inter>A \<noteq> 0"
proof -
  let ?X = "\<Union>T"
  from assms(1) have cntx: "topology0(T)" 
    unfolding topology0_def by simp
  with assms(2,3) have "x\<in>?X"
    using topology0.Top_3_L11(1) by blast
  with assms(4) obtain U where "U\<in>T" "x\<in>U" and "U\<subseteq>N"
    using neigh_val by auto
  from assms(2,3) cntx \<open>U\<in>T\<close> \<open>x\<in>U\<close> have "A\<inter>U \<noteq> 0"
    using topology0.cl_inter_neigh by simp
  with \<open>U\<subseteq>N\<close> show "N\<inter>A \<noteq> 0" by blast
qed

subsection\<open> Neighborhood systems are 1:1 with topologies \<close>

text\<open>We can create a topology from a neighborhood system and neighborhood system from topology.
  The question is then if we start from a neighborhood system, create a topology from it 
  then create the topology's natural neighborhood system, do we get back the neighborhood system 
  we started from? Similarly, if we start from a topology, create its neighborhood system and then
  create a topology from that, do we get the original topology? This section provides 
  the affirmative answer (for now only for the first question). 
  This means that there is a one-to-one correspondence between the set of topologies on a set 
  and the set of abstract neighborhood systems on the set. \<close>

text\<open>Each abstract neighborhood of $x$ contains an open neighborhood of $x$.\<close>

lemma open_nei_in_nei: 
  assumes "\<M> {is a neighborhood system on} X" "x\<in>X" "N\<in>\<M>`(x)"
  defines Tdef: "T \<equiv> {U\<in>Pow(X). \<forall>x\<in>U. U \<in> \<M>`(x)}"
  shows "N\<in>Pow(X)" and "\<exists>U\<in>T. (x\<in>U \<and> U\<subseteq>N)"
proof -
  from assms(1) have "\<M>:X\<rightarrow>Pow(Pow(X))" unfolding IsNeighSystem_def 
    by simp
  with assms(2,3) show "N\<in>Pow(X)"using apply_funtype by blast
  let ?U = "{y\<in>X. N \<in> \<M>`(y)}"
  have "?U\<in>T"
  proof -
    have "?U \<in> Pow(X)" by auto
    moreover have "\<forall>y\<in>?U. ?U\<in>\<M>`(y)"
    proof -
      { fix y assume "y\<in>?U"
        then have "y\<in>X" and "N\<in>\<M>`(y)" by auto
        with assms(1) obtain V where "V\<in>\<M>`(y)" and "\<forall>z\<in>V. N \<in> \<M>`(z)"
          unfolding IsNeighSystem_def by blast
        with assms(1) \<open>y\<in>X\<close> \<open>V\<in>\<M>`(y)\<close> have "V\<subseteq>?U"
          using neighborhood_subset(1) by blast
        with assms(1) \<open>y\<in>X\<close> \<open>V\<in>\<M>`(y)\<close> \<open>?U \<in> Pow(X)\<close> have "?U\<in>\<M>`(y)"
          unfolding IsNeighSystem_def using is_filter_def_split(5) by blast
      } thus ?thesis by simp
    qed
    ultimately have "?U \<in> {U\<in>Pow(X). \<forall>x\<in>U. U \<in> \<M>`(x)}" by simp
    with assms(4) show "?U\<in>T" by simp
  qed
  moreover from assms(1,2) \<open>N\<in>\<M>`(x)\<close> have "x\<in>?U \<and> ?U \<subseteq> N"
    using neighborhood_subset(2) by auto
  ultimately show "\<exists>U\<in>T. (x\<in>U \<and> U\<subseteq>N)" by (rule witness_exists)
qed

text\<open>In the the next theorem we show that if we start from 
  a neighborhood system, create a topology from it, then create it's natural neighborhood system,
  we get back the original neighborhood system.\<close>

theorem nei_top_nei_round_trip: 
  assumes "\<M> {is a neighborhood system on} X"
  defines Tdef: "T \<equiv> {U\<in>Pow(X). \<forall>x\<in>U. U \<in> \<M>`(x)}"
  shows "({neighborhood system of} T) = \<M>"
proof -
  let ?M = "{neighborhood system of} T"
  from assms have "T {is a topology}" and "\<Union>T = X" using topology_from_neighs 
    by auto
  then have "?M {is a neighborhood system on} X" using neigh_from_topology 
    by blast
  with assms(1) have "?M:X\<rightarrow>Pow(Pow(X))" and "\<M>:X\<rightarrow>Pow(Pow(X))"
    unfolding IsNeighSystem_def by auto
  moreover
  { fix x assume "x\<in>X"
    from \<open>\<Union>T = X\<close> \<open>x\<in>X\<close> have I: "?M`(x) = {V\<in>Pow(X).\<exists>U\<in>T.(x\<in>U \<and> U\<subseteq>V)}"
      unfolding NeighSystem_def using ZF_fun_from_tot_val1 by simp
    have "?M`(x) = \<M>`(x)"
    proof
      { fix V assume "V\<in>?M`(x)"
        with I obtain U where "U\<in>T" "x\<in>U" "U\<subseteq>V" by auto
        from assms(2) \<open>U\<in>T\<close> \<open>x\<in>U\<close> have "U \<in> \<M>`(x)" by simp
        from assms(1) \<open>x\<in>X\<close> have "\<M>`(x) {is a filter on} X"
          unfolding IsNeighSystem_def by simp
        with \<open>U \<in> \<M>`(x)\<close> \<open>V\<in>?M`(x)\<close> I \<open>U\<subseteq>V\<close>  have "V \<in> \<M>`(x)"
          unfolding IsFilter_def by simp
      } thus "?M`(x) \<subseteq> \<M>`(x)" by auto
      { fix N assume "N\<in>\<M>`(x)"
        with assms \<open>x\<in>X\<close> \<open>\<Union>T = X\<close> I have "N\<in>?M`(x)" using open_nei_in_nei 
          by auto
      } thus "\<M>`(x) \<subseteq> ?M`(x)" by auto
    qed
  } hence "\<forall>x\<in>X. ?M`(x) = \<M>`(x)" by simp
  ultimately show ?thesis by (rule func_eq)
qed

subsection\<open>Set neighborhoods\<close>

text\<open>Some sources (like Metamath) take a somewhat different approach where instead of defining
  the collection of neighborhoods of a point $x\in X$ they define a collection of neighborhoods
  of a subset of $X$ (where $X$ is the carrier of a topology  $T$ (i.e. $X=\bigcup T$).
  In this approach a neighborhood system is a function whose domain is the powerset of $X$, i.e.
  the set of subsets of $X$. The two approaches are equivalent in a sense as
  having a neighborhood system we can create a set neighborhood system and vice versa. \<close>

text\<open>We define a set neighborhood system as a function that takes a subset $A$ of the carrier of the
  topology and assigns it the collection of supersets of all open sets that contain $A$. \<close>

definition
  SetNeighSystem ( "{set neighborhood system of} _" 91)
  where "{set neighborhood system of} T 
          \<equiv> {\<langle>A,{N\<in>Pow(\<Union>T). \<exists>U\<in>T. (A\<subseteq>U \<and> U\<subseteq>N)}\<rangle>. A\<in>Pow(\<Union>T)}" 

text\<open>Given a set neighborhood system we can recover the (standard)
  neighborhood system by taking the values of the set neighborhood system
  at singletons ${x}$ where $x\in X=\bigcup T$.\<close>

lemma neigh_from_nei: assumes "x\<in>\<Union>T"
  shows "({neighborhood system of} T)`(x) = ({set neighborhood system of} T)`{x}"
  using assms ZF_fun_from_tot_val1
  unfolding NeighSystem_def SetNeighSystem_def
  by simp

text\<open>The set neighborhood system of $T$ is a function mapping subsets of $\bigcup T$
  to collections of subsets of $\bigcup T$. \<close>

lemma nei_fun: 
  shows "({set neighborhood system of} T):Pow(\<Union>T) \<rightarrow>Pow(Pow(\<Union>T))"
proof -
  let ?X = "\<Union>T"
  have "\<forall>A\<in>Pow(?X). {N\<in>Pow(?X). \<exists>U\<in>T. (A\<subseteq>U \<and> U\<subseteq>N)} \<in> Pow(Pow(?X))"
    by blast
  then have 
    "{\<langle>A,{N\<in>Pow(?X). \<exists>U\<in>T. (A\<subseteq>U \<and> U\<subseteq>N)}\<rangle>. A\<in>Pow(?X)}:Pow(?X)\<rightarrow>Pow(Pow(?X))"
    by (rule ZF_fun_from_total)
  then show ?thesis unfolding SetNeighSystem_def by simp
qed

text\<open>The value of the set neighborhood system of $T$ at subset $A$ of $\bigcup T$
  is the collection of subsets $N$ of $\bigcup T$ for which exists an open subset
  $U\subseteq N$ that contains $A$. \<close>

lemma nei_val: assumes "A \<subseteq> \<Union>T"
  shows
  "({set neighborhood system of} T)`(A) = {N\<in>Pow(\<Union>T). \<exists>U\<in>T. (A\<subseteq>U \<and> U\<subseteq>N)}"
  using assms ZF_fun_from_tot_val1 unfolding SetNeighSystem_def by simp

text\<open>A member of the value of the set neighborhood system of $T$ at $A$ is
  a subset of $\bigcup T$. The interesting part is that we can show it without any
  assumption on $A$. \<close>

lemma nei_val_subset: 
  assumes "N \<in> ({set neighborhood system of} T)`(A)"
  shows "A \<subseteq> \<Union>T" and "N \<subseteq> \<Union>T"
proof -
  let ?f = "{set neighborhood system of} T"
  have "?f:Pow(\<Union>T) \<rightarrow>Pow(Pow(\<Union>T))" using nei_fun by simp
  with assms show "A \<subseteq> \<Union>T" using arg_in_domain by blast
  with assms show "N \<subseteq> \<Union>T" using nei_val by simp
qed

text\<open>If $T$ is a topology, then every subset of its carrier (i.e. $\bigcup T$) 
  is a (set) neighborhood of the empty set. \<close>

lemma nei_empty: assumes "T {is a topology}" "N \<subseteq> \<Union>T"
  shows "N \<in> ({set neighborhood system of} T)`(0)"
  using assms empty_open nei_val by auto

text\<open>If $T$ is a topology, then the (set) neighborhoods of a nonempty subset of 
  $\bigcup T$ form a filter on $X=\bigcup T$.\<close>

theorem nei_filter: assumes "T {is a topology}" "D \<subseteq> (\<Union>T)" "D\<noteq>0"
  shows "({set neighborhood system of} T)`(D) {is a filter on} (\<Union>T)"
proof -
  let ?X = "\<Union>T"
  let ?\<F> = "({set neighborhood system of} T)`(D)"
  from assms(2) have I: "?\<F> = {N\<in>Pow(?X). \<exists>U\<in>T. (D\<subseteq>U \<and> U\<subseteq>N)}"
    using nei_val by simp
  with assms(3) have "0 \<notin> ?\<F>" by auto
  moreover from assms(1,2) I have "?X\<in>?\<F>"
    using carr_open by auto
  moreover from I have "?\<F> \<subseteq> Pow(?X)" by auto
  moreover have "\<forall>A\<in>?\<F>. \<forall>B\<in>?\<F>. A\<inter>B \<in> ?\<F>"
  proof -
    { fix A B assume "A\<in>?\<F>" "B\<in>?\<F>"
      with I obtain U\<^sub>A U\<^sub>B where 
        "U\<^sub>A\<in>T" "D\<subseteq>U\<^sub>A" "U\<^sub>A\<subseteq>A" and "U\<^sub>B\<in>T" "D\<subseteq>U\<^sub>B" "U\<^sub>B\<subseteq>B"
        by auto
      let ?U = "U\<^sub>A\<inter>U\<^sub>B"
      from assms(1) \<open>U\<^sub>A\<in>T\<close> \<open>U\<^sub>B\<in>T\<close> \<open>D\<subseteq>U\<^sub>A\<close> \<open>D\<subseteq>U\<^sub>B\<close> \<open>U\<^sub>A\<subseteq>A\<close> \<open>U\<^sub>B\<subseteq>B\<close>
      have "?U \<in> T" "D\<subseteq>?U" "?U \<subseteq> A\<inter>B"
        unfolding IsATopology_def by auto
      with I \<open>A\<in>?\<F>\<close> \<open>B\<in>?\<F>\<close> have "A\<inter>B \<in> ?\<F>" by auto
    } thus ?thesis by simp
  qed
  moreover have "\<forall>B\<in>?\<F>. \<forall>C\<in>Pow(?X). B\<subseteq>C \<longrightarrow> C\<in>?\<F>"
  proof -
    { fix B C assume "B\<in>?\<F>" "C\<in>Pow(?X)" "B\<subseteq>C"
      from I \<open>B\<in>?\<F>\<close> obtain U where "U\<in>T" "D\<subseteq>U" and "U\<subseteq>B"
        by auto
      with \<open>B\<subseteq>C\<close> have "\<exists>U\<in>T. (D\<subseteq>U \<and> U\<subseteq>C)" by blast
      with I \<open>C\<in>Pow(?X)\<close> have "C\<in>?\<F>" by simp
    } thus ?thesis by blast
  qed
  ultimately show "?\<F> {is a filter on} ?X"
    unfolding IsFilter_def by simp
qed  
    
text\<open>If $N$ is a (set) neighborhood of $A$ in $T$, then exist an open set $U$ such that
  $N$ contains $U$ which contains $A$. This is similar to the Metamath's theorem
  with the same name, except that here we do not need assume that $T$ is a topology
  (which is a bit worrying).\<close>

lemma neii2: assumes "N \<in> ({set neighborhood system of} T)`(A)"
  shows "\<exists>U\<in>T. (A\<subseteq>U \<and> U\<subseteq>N)"
proof -
  from assms have "A\<in>Pow(\<Union>T)" using nei_fun arg_in_domain
    by blast
  with assms show ?thesis
    unfolding SetNeighSystem_def using ZF_fun_from_tot_val1
    by simp
qed

text\<open>An open set $U$ covering a set $A$ is a set neighborhood of $A$. \<close>

lemma open_superset_nei: assumes "V\<in>T" "A\<subseteq>V"
  shows "V \<in> ({set neighborhood system of} T)`(A)"
proof -
  from assms have 
    "({set neighborhood system of} T)`(A) = {N\<in>Pow(\<Union>T). \<exists>U\<in>T. (A\<subseteq>U \<and> U\<subseteq>N)}"
    using nei_val by blast
  with assms show ?thesis by auto
qed

text\<open>An open set is a set neighborhood of itself.\<close>

corollary open_is_nei: assumes "V\<in>T"
  shows "V \<in> ({set neighborhood system of} T)`(V)"
  using assms open_superset_nei by simp

text\<open>An open neighborhood of $x$ is a set neighborhood of $\{ x\}$. \<close>

corollary open_nei_singl: assumes "V\<in>T" "x\<in>V"
  shows  "V \<in> ({set neighborhood system of} T)`{x}"
  using assms open_superset_nei by simp

text\<open>The Cartesian product of two neighborhoods is a neighborhood in the 
  product topology. Similar to the Metamath's theorem with the same name. \<close>

lemma neitx: 
  assumes "T {is a topology}" "S {is a topology}" and
  "A \<in> ({set neighborhood system of} T)`(C)" and
  "B \<in> ({set neighborhood system of} S)`(D)"
  shows "A\<times>B \<in> ({set neighborhood system of} (T\<times>\<^sub>tS))`(C\<times>D)"
proof -
  have "A\<times>B \<subseteq> \<Union>(T\<times>\<^sub>tS)"
  proof -
    from assms(3,4) have "A\<times>B \<subseteq> (\<Union>T)\<times>(\<Union>S)"
      using nei_val_subset(2) by blast
    with assms(1,2) show ?thesis using Top_1_4_T1 by simp
  qed
  let ?\<F> = "({set neighborhood system of} (T\<times>\<^sub>tS))`(C\<times>D)"
  { assume "C=0 \<or> D=0"
    with assms(1,2) \<open>A\<times>B \<subseteq> \<Union>(T\<times>\<^sub>tS)\<close> have "A\<times>B \<in> ?\<F>"
      using Top_1_4_T1(1) nei_empty by auto
  }
  moreover
  { assume "C\<noteq>0" "D\<noteq>0"
    from assms(3) obtain U\<^sub>A where 
      "U\<^sub>A\<in>T" "C\<subseteq>U\<^sub>A" "U\<^sub>A\<subseteq>A" using neii2 by blast
    from assms(4) obtain U\<^sub>B where 
      "U\<^sub>B\<in>S" "D\<subseteq>U\<^sub>B" "U\<^sub>B\<subseteq>B" using neii2 by blast
    from assms(1,2) \<open>U\<^sub>A\<in>T\<close> \<open>U\<^sub>B\<in>S\<close> \<open>C\<subseteq>U\<^sub>A\<close> \<open>D\<subseteq>U\<^sub>B\<close>
    have "U\<^sub>A\<times>U\<^sub>B \<in> T\<times>\<^sub>tS" and "C\<times>D \<subseteq> U\<^sub>A\<times>U\<^sub>B"
      using prod_open_open_prod by auto
    then have "U\<^sub>A\<times>U\<^sub>B \<in> ?\<F>" using open_superset_nei 
      by simp
    from \<open>U\<^sub>A\<subseteq>A\<close> \<open>U\<^sub>B\<subseteq>B\<close> have "U\<^sub>A\<times>U\<^sub>B \<subseteq> A\<times>B" by auto
    have "?\<F> {is a filter on} (\<Union>(T\<times>\<^sub>tS))"
    proof -
      from assms(1,2) have "(T\<times>\<^sub>tS) {is a topology}"
        using Top_1_4_T1(1) by simp
      moreover have "C\<times>D \<subseteq> \<Union>(T\<times>\<^sub>tS)"
      proof -
        from assms(3,4) have "C\<times>D \<subseteq> (\<Union>T)\<times>(\<Union>S)"
          using nei_val_subset(1) by blast
        with assms(1,2) show ?thesis using Top_1_4_T1(3) by simp
      qed 
      moreover from \<open>C\<noteq>0\<close> \<open>D\<noteq>0\<close> have "C\<times>D \<noteq> 0" by auto
      ultimately show "?\<F> {is a filter on} (\<Union>(T\<times>\<^sub>tS))"
        using nei_filter by simp
    qed
    with \<open>U\<^sub>A\<times>U\<^sub>B \<in> ?\<F>\<close> \<open>A\<times>B \<subseteq> \<Union>(T\<times>\<^sub>tS)\<close> \<open>U\<^sub>A\<times>U\<^sub>B \<subseteq> A\<times>B\<close> 
    have "A\<times>B \<in> ?\<F>" using is_filter_def_split(5) by simp
  }
  ultimately show ?thesis by auto
qed

text\<open>Any neighborhood of an element of the closure of a subset intersects the subset.
  This is practically the same as \<open>neigh_inter_nempty\<close>, just formulated in terms 
  of set neighborhoods of singletons. 
  Compare with Metamath's theorem with the same name.\<close>

lemma neindisj: assumes "T {is a topology}" "A\<subseteq>\<Union>T" "x \<in> Closure(A,T)" and
  "N \<in> ({set neighborhood system of} T)`{x}"
  shows "N\<inter>A \<noteq> 0"
proof -
  let ?X = "\<Union>T"
  from assms(1) have cntx: "topology0(T)" 
    unfolding topology0_def by simp
  with assms(2,3) have "x\<in>?X"
    using topology0.Top_3_L11(1) by blast
  with assms show ?thesis using neigh_from_nei neigh_inter_nempty
    by simp
qed

end
