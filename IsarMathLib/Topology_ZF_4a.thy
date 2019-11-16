(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2019 Slawomir Kolodynski

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

subsection\<open> Topology from neighborhood systems \<close>

text\<open>Given a neighborhood system $\{\mathcal{M}_x\}_{x\in X}$ we can define a topology on $X$.
Namely, we consider a subset of $X$ open if $U \in \mathcal{M}_x$ for every element $x$ of $U$. \<close>

text\<open> The collection of sets defined as above is indeed a topology. \<close>

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

subsection\<open> Neighborhood system from topology \<close>

text\<open> Once we have a topology $T$ we can define a natural neighborhood system on $X=\bigcup T$. 
  In this section we define such neighborhood system and prove its basic properties.  \<close>

text\<open>For a topology $T$ we define a neighborhood system of $T$ as a function that takes an $x\in X=\bigcup T$ 
and assigns it a collection supersets of open sets containing $x$. 
We call that the "neighborhood system of $T$"\<close>

definition
  NeighSystem ("{neighborhood system of} _" 91)
  where "{neighborhood system of} T \<equiv> { \<langle>x,{V\<in>Pow(\<Union>T).\<exists>U\<in>T.(x\<in>U \<and> U\<subseteq>V)}\<rangle>. x \<in> \<Union>T }" 

text\<open> The next lemma shows that open sets are members of (what we will prove later to be) the natural 
  neighborhood system on $X=\bigcup T$. \<close>

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

text\<open> The next theorem states that the the natural 
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

end
