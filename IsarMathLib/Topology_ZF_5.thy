(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2012-2013 Daniel de la Concepcion

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

section \<open>Topology 5\<close>

theory Topology_ZF_5 imports Topology_ZF_properties Topology_ZF_examples_1 Topology_ZF_4
begin

subsection\<open>Some results for separation axioms\<close>

text\<open>First we will give a global characterization of $T_1$-spaces; which is interesting
because it involves the cardinal $\mathbb{N}$.\<close>

lemma (in topology0)  T1_cocardinal_coarser:
  shows "(T {is T\<^sub>1}) \<longleftrightarrow> (CoFinite (\<Union>T))\<subseteq>T"
proof
  {
    assume AS:"T {is T\<^sub>1}"
    {
      fix x assume p:"x\<in>\<Union>T"
      {
        fix y assume "y\<in>(\<Union>T)-{x}"
        with AS p obtain U where "U\<in>T" "y\<in>U" "x\<notin>U" using isT1_def by blast
        then have "U\<in>T" "y\<in>U" "U\<subseteq>(\<Union>T)-{x}" by auto
        then have "\<exists>U\<in>T. y\<in>U \<and> U\<subseteq>(\<Union>T)-{x}" by auto
      }
      then have "\<forall>y\<in>(\<Union>T)-{x}. \<exists>U\<in>T. y\<in>U \<and> U\<subseteq>(\<Union>T)-{x}" by auto
      then have "\<Union>T-{x}\<in>T" using open_neigh_open by auto
      with p have "{x} {is closed in}T" using IsClosed_def by auto
    }
    then have pointCl:"\<forall>x\<in>\<Union>T. {x} {is closed in} T" by auto
    {
      fix A
      assume AS2:"A\<in>FinPow(\<Union>T)"
      let ?p="{\<langle>x,{x}\<rangle>. x\<in>A}"
      have "?p\<in>A\<rightarrow>{{x}. x\<in>A}" using Pi_def unfolding function_def by auto
      then have "?p:bij(A,{{x}. x\<in>A})" unfolding bij_def inj_def surj_def using apply_equality
        by auto
      then have "A\<approx>{{x}. x\<in>A}" unfolding eqpoll_def by auto
      with AS2 have "Finite({{x}. x\<in>A})" unfolding FinPow_def using eqpoll_imp_Finite_iff by auto
      then have "{{x}. x\<in>A}\<in>FinPow({D \<in> Pow(\<Union>T) . D {is closed in} T})" using AS2 pointCl unfolding FinPow_def
      by (safe, blast+) 
      then have "(\<Union>{{x}. x\<in>A}) {is closed in} T" using fin_union_cl_is_cl by auto
      moreover
      have "\<Union>{{x}. x\<in>A}=A" by auto
      ultimately have "A {is closed in} T" by simp
    }
    then have reg:"\<forall>A\<in>FinPow(\<Union>T). A {is closed in} T" by auto
    {
      fix U
      assume AS2:"U \<in> CoCardinal(\<Union>T,nat)"
      then have "U\<in>Pow(\<Union>T)" "U=0 \<or> ((\<Union>T)-U)\<prec>nat" using CoCardinal_def by auto
      then have "U\<in>Pow(\<Union>T)" "U=0 \<or> Finite(\<Union>T-U)" using lesspoll_nat_is_Finite by auto
      then have "U\<in>Pow(\<Union>T)" "U\<in>T\<or>(\<Union>T-U) {is closed in} T" using empty_open topSpaceAssum
        reg unfolding FinPow_def by auto
      then have "U\<in>Pow(\<Union>T)" "U\<in>T\<or>(\<Union>T-(\<Union>T-U))\<in>T" using IsClosed_def by auto
      moreover
      then have "(\<Union>T-(\<Union>T-U))=U" by blast
      ultimately have "U\<in>T" by auto
    }
    then show "(CoFinite (\<Union>T))\<subseteq>T" using Cofinite_def by auto
  }
  {
    assume "(CoFinite (\<Union>T))\<subseteq>T"
    then have AS:"CoCardinal(\<Union>T,nat) \<subseteq> T" using Cofinite_def by auto
    {
      fix x y
      assume AS2:"x\<in>\<Union>T" "y\<in>\<Union>T""x\<noteq>y"
      have "Finite({y})" by auto
      then obtain n where "{y}\<approx>n" "n\<in>nat" using Finite_def by auto
      then have "{y}\<prec>nat" using n_lesspoll_nat eq_lesspoll_trans by auto
      then have "{y} {is closed in} CoCardinal(\<Union>T,nat)" using closed_sets_cocardinal
        AS2(2) by auto
      then have "(\<Union>T)-{y}\<in>CoCardinal(\<Union>T,nat)" using union_cocardinal IsClosed_def by auto
      with AS have "(\<Union>T)-{y}\<in>T" by auto
      moreover
      with AS2(1,3) have "x\<in>((\<Union>T)-{y}) \<and> y\<notin>((\<Union>T)-{y})" by auto
      ultimately have "\<exists>V\<in>T. x\<in>V\<and>y\<notin>V" by(safe,auto)
    }
    then show "T {is T\<^sub>1}" using isT1_def by auto
  }
qed

text\<open>In the previous proof, it is obvious that we don't need to check
if ever cofinite set is open. It is enough to check if every singleton is closed.\<close>

corollary(in topology0) T1_iff_singleton_closed:
  shows "(T {is T\<^sub>1}) \<longleftrightarrow> (\<forall>x\<in>\<Union>T. {x}{is closed in}T)"
proof
  assume AS:"T {is T\<^sub>1}"
  {
    fix x assume p:"x\<in>\<Union>T"
    {
      fix y assume "y\<in>(\<Union>T)-{x}"
      with AS p obtain U where "U\<in>T" "y\<in>U" "x\<notin>U" using isT1_def by blast
      then have "U\<in>T" "y\<in>U" "U\<subseteq>(\<Union>T)-{x}" by auto
      then have "\<exists>U\<in>T. y\<in>U \<and> U\<subseteq>(\<Union>T)-{x}" by auto
    }
    then have "\<forall>y\<in>(\<Union>T)-{x}. \<exists>U\<in>T. y\<in>U \<and> U\<subseteq>(\<Union>T)-{x}" by auto
    then have "\<Union>T-{x}\<in>T" using open_neigh_open by auto
    with p have "{x} {is closed in}T" using IsClosed_def by auto
  }
  then show pointCl:"\<forall>x\<in>\<Union>T. {x} {is closed in} T" by auto
next
  assume pointCl:"\<forall>x\<in>\<Union>T. {x} {is closed in} T"
  {
    fix A
    assume AS2:"A\<in>FinPow(\<Union>T)"
    let ?p="{\<langle>x,{x}\<rangle>. x\<in>A}"
    have "?p\<in>A\<rightarrow>{{x}. x\<in>A}" using Pi_def unfolding function_def by auto
    then have "?p:bij(A,{{x}. x\<in>A})" unfolding bij_def inj_def surj_def using apply_equality
      by auto
    then have "A\<approx>{{x}. x\<in>A}" unfolding eqpoll_def by auto
    with AS2 have "Finite({{x}. x\<in>A})" unfolding FinPow_def using eqpoll_imp_Finite_iff by auto
    then have "{{x}. x\<in>A}\<in>FinPow({D \<in> Pow(\<Union>T) . D {is closed in} T})" using AS2 pointCl unfolding FinPow_def
    by (safe, blast+) 
    then have "(\<Union>{{x}. x\<in>A}) {is closed in} T" using fin_union_cl_is_cl by auto
    moreover
    have "\<Union>{{x}. x\<in>A}=A" by auto
    ultimately have "A {is closed in} T" by simp
  }
  then have reg:"\<forall>A\<in>FinPow(\<Union>T). A {is closed in} T" by auto
  {
    fix U
    assume AS2:"U\<in>CoCardinal(\<Union>T,nat)"
    then have "U\<in>Pow(\<Union>T)" "U=0 \<or> ((\<Union>T)-U)\<prec>nat" using CoCardinal_def by auto
    then have "U\<in>Pow(\<Union>T)" "U=0 \<or> Finite(\<Union>T-U)" using lesspoll_nat_is_Finite by auto
    then have "U\<in>Pow(\<Union>T)" "U\<in>T\<or>(\<Union>T-U) {is closed in} T" using empty_open topSpaceAssum
      reg unfolding FinPow_def by auto
    then have "U\<in>Pow(\<Union>T)" "U\<in>T\<or>(\<Union>T-(\<Union>T-U))\<in>T" using IsClosed_def by auto
    moreover
    then have "(\<Union>T-(\<Union>T-U))=U" by blast
    ultimately have "U\<in>T" by auto
  }
  then have "(CoFinite (\<Union>T))\<subseteq>T" using Cofinite_def by auto
  then show "T {is T\<^sub>1}" using T1_cocardinal_coarser by auto
qed

text\<open>Secondly, let's show that the \<open>CoCardinal X Q\<close>
topologies for different sets $Q$ are all ordered
as the partial order of sets. (The order is linear when considering only cardinals)\<close>

lemma order_cocardinal_top:
  fixes X
  assumes "Q1\<lesssim>Q2"
  shows "CoCardinal(X,Q1) \<subseteq> CoCardinal(X,Q2)"
proof
  fix x
  assume "x \<in> CoCardinal(X,Q1)"
  then have "x\<in>Pow(X)" "x=0\<or>(X-x)\<prec>Q1" using CoCardinal_def by auto
  with assms have "x\<in>Pow(X)" "x=0\<or>(X-x)\<prec>Q2" using lesspoll_trans2 by auto
  then show "x\<in>CoCardinal(X,Q2)" using CoCardinal_def by auto
qed

corollary cocardinal_is_T1:
  fixes X K
  assumes "InfCard(K)"
  shows "CoCardinal(X,K) {is T\<^sub>1}"
proof-
  have "nat\<le>K" using InfCard_def assms by auto
  then have "nat\<subseteq>K" using le_imp_subset by auto
  then have "nat\<lesssim>K" "K\<noteq>0"using subset_imp_lepoll by auto
  then have "CoCardinal(X,nat) \<subseteq> CoCardinal(X,K)" "\<Union>CoCardinal(X,K)=X" using order_cocardinal_top 
    union_cocardinal by auto
  then show ?thesis using topology0.T1_cocardinal_coarser topology0_CoCardinal assms Cofinite_def
    by auto
qed

text\<open>In $T_2$-spaces, filters and nets have at most one limit point.\<close>

lemma (in topology0) T2_imp_unique_limit_filter:
  assumes "T {is T\<^sub>2}" "\<FF> {is a filter on}\<Union>T" "\<FF> \<rightarrow>\<^sub>F x" "\<FF> \<rightarrow>\<^sub>F y"
  shows "x=y"
proof-
  {
    assume "x\<noteq>y"
    from assms(3,4) have "x\<in>\<Union>T" "y\<in>\<Union>T" using FilterConverges_def assms(2)
      by auto
    with \<open>x\<noteq>y\<close> have "\<exists>U\<in>T. \<exists>V\<in>T. x\<in>U \<and> y\<in>V \<and> U\<inter>V=0" using assms(1) isT2_def by auto
    then obtain U V where "x\<in>U" "y\<in>V" "U\<inter>V=0" "U\<in>T" "V\<in>T" by auto
    then have "U\<in>{A\<in>Pow(\<Union>T). x\<in>Interior(A,T)}" "V\<in>{A\<in>Pow(\<Union>T). y\<in>Interior(A,T)}" using Top_2_L3 by auto
    then have "U\<in>\<FF>" "V\<in>\<FF>" using FilterConverges_def assms(2) assms(3,4)
      by auto
    then have "U\<inter>V\<in>\<FF>" using IsFilter_def assms(2) by auto
    with \<open>U\<inter>V=0\<close> have "0\<in>\<FF>" by auto
    then have "False" using IsFilter_def assms(2) by auto
  }
  then show ?thesis by auto
qed

lemma (in topology0) T2_imp_unique_limit_net:
  assumes "T {is T\<^sub>2}" "N {is a net on}\<Union>T" "N \<rightarrow>\<^sub>N x" "N \<rightarrow>\<^sub>N y"
  shows "x=y"
proof-
  have "(Filter N..(\<Union>T)) {is a filter on} (\<Union>T)" "(Filter N..(\<Union>T)) \<rightarrow>\<^sub>F x" "(Filter N..(\<Union>T)) \<rightarrow>\<^sub>F y"
    using filter_of_net_is_filter(1) net_conver_filter_of_net_conver assms(2)
    assms(3,4) by auto
  with assms(1) show ?thesis using T2_imp_unique_limit_filter by auto
qed
    
text\<open>In fact, $T_2$-spaces are characterized by this property. For this proof we build
a filter containing the union of two filters.\<close>

lemma (in topology0) unique_limit_filter_imp_T2:
  assumes "\<forall>x\<in>\<Union>T. \<forall>y\<in>\<Union>T. \<forall>\<FF>. ((\<FF> {is a filter on}\<Union>T) \<and> (\<FF> \<rightarrow>\<^sub>F x) \<and> (\<FF> \<rightarrow>\<^sub>F y)) \<longrightarrow> x=y"
  shows "T {is T\<^sub>2}"
proof-
  {
    fix x y
    assume "x\<in>\<Union>T" "y\<in>\<Union>T" "x\<noteq>y"
    {
      assume "\<forall>U\<in>T. \<forall>V\<in>T. (x\<in>U \<and> y\<in>V) \<longrightarrow> U\<inter>V\<noteq>0"
      let ?Ux="{A\<in>Pow(\<Union>T). x\<in>int(A)}"
      let ?Uy="{A\<in>Pow(\<Union>T). y\<in>int(A)}"
      let ?FF="?Ux \<union> ?Uy \<union> {A\<inter>B. \<langle>A,B\<rangle>\<in>?Ux \<times> ?Uy}"
      have sat:"?FF {satisfies the filter base condition}"
      proof-
        {
          fix A B
          assume "A\<in>?FF" "B\<in>?FF"
          {
            assume "A\<in>?Ux" 
            {
              assume "B\<in>?Ux"
              with \<open>x\<in>\<Union>T\<close> \<open>A\<in>?Ux\<close> have "A\<inter>B\<in>?Ux" using neigh_filter(1) IsFilter_def by auto
              then have "A\<inter>B\<in>?FF" by auto
            }
            moreover
            {
              assume "B\<in>?Uy"
              with \<open>A\<in>?Ux\<close> have "A\<inter>B\<in>?FF" by auto
            }
            moreover
            {
              assume "B\<in>{A\<inter>B. \<langle>A,B\<rangle>\<in>?Ux \<times> ?Uy}"
              then obtain AA BB where "B=AA\<inter>BB" "AA\<in>?Ux" "BB\<in>?Uy" by auto
              with \<open>x\<in>\<Union>T\<close> \<open>A\<in>?Ux\<close> have "A\<inter>B=(A\<inter>AA)\<inter>BB" "A\<inter>AA\<in>?Ux" using neigh_filter(1) IsFilter_def by auto
              with \<open>BB\<in>?Uy\<close> have "A\<inter>B\<in>{A\<inter>B. \<langle>A,B\<rangle>\<in>?Ux \<times> ?Uy}" by auto
              then have "A\<inter>B\<in>?FF" by auto
            }
            ultimately have "A\<inter>B\<in>?FF" using \<open>B\<in>?FF\<close> by auto
          }
          moreover
          {
            assume "A\<in>?Uy" 
            {
              assume "B\<in>?Uy"
              with \<open>y\<in>\<Union>T\<close> \<open>A\<in>?Uy\<close> have "A\<inter>B\<in>?Uy" using neigh_filter(1) IsFilter_def by auto
              then have "A\<inter>B\<in>?FF" by auto
            }
            moreover
            {
              assume "B\<in>?Ux"
              with \<open>A\<in>?Uy\<close> have "B\<inter>A\<in>?FF" by auto
              moreover have "A\<inter>B=B\<inter>A" by auto
              ultimately have "A\<inter>B\<in>?FF" by auto
            }
            moreover
            {
              assume "B\<in>{A\<inter>B. \<langle>A,B\<rangle>\<in>?Ux \<times> ?Uy}"
              then obtain AA BB where "B=AA\<inter>BB" "AA\<in>?Ux" "BB\<in>?Uy" by auto
              with \<open>y\<in>\<Union>T\<close> \<open>A\<in>?Uy\<close> have "A\<inter>B=AA\<inter>(A\<inter>BB)" "A\<inter>BB\<in>?Uy" using neigh_filter(1) IsFilter_def by auto
              with \<open>AA\<in>?Ux\<close> have "A\<inter>B\<in>{A\<inter>B. \<langle>A,B\<rangle>\<in>?Ux \<times> ?Uy}" by auto
              then have "A\<inter>B\<in>?FF" by auto
            }
            ultimately have "A\<inter>B\<in>?FF" using \<open>B\<in>?FF\<close> by auto
          }
          moreover
          {
            assume "A\<in>{A\<inter>B. \<langle>A,B\<rangle>\<in>?Ux \<times> ?Uy}"
            then obtain AA BB where "A=AA\<inter>BB" "AA\<in>?Ux" "BB\<in>?Uy" by auto
            {
              assume "B\<in>?Uy"
              with \<open>BB\<in>?Uy\<close> \<open>y\<in>\<Union>T\<close> have "B\<inter>BB\<in>?Uy" using neigh_filter(1) IsFilter_def by auto
              moreover from \<open>A=AA\<inter>BB\<close> have "A\<inter>B=AA\<inter>(B\<inter>BB)" by auto
              ultimately have "A\<inter>B\<in>?FF" using \<open>AA\<in>?Ux\<close> \<open>B\<inter>BB\<in>?Uy\<close> by auto
            }
            moreover
            {
              assume "B\<in>?Ux"
              with \<open>AA\<in>?Ux\<close> \<open>x\<in>\<Union>T\<close> have "B\<inter>AA\<in>?Ux" using neigh_filter(1) IsFilter_def by auto
              moreover from \<open>A=AA\<inter>BB\<close> have "A\<inter>B=(B\<inter>AA)\<inter>BB" by auto
              ultimately have "A\<inter>B\<in>?FF" using \<open>B\<inter>AA\<in>?Ux\<close> \<open>BB\<in>?Uy\<close> by auto
            }
            moreover
            {
              assume "B\<in>{A\<inter>B. \<langle>A,B\<rangle>\<in>?Ux \<times> ?Uy}"
              then obtain AA2 BB2 where "B=AA2\<inter>BB2" "AA2\<in>?Ux" "BB2\<in>?Uy" by auto
              from \<open>B=AA2\<inter>BB2\<close> \<open>A=AA\<inter>BB\<close> have "A\<inter>B=(AA\<inter>AA2)\<inter>(BB\<inter>BB2)" by auto
              moreover
              from \<open>AA\<in>?Ux\<close>\<open>AA2\<in>?Ux\<close>\<open>x\<in>\<Union>T\<close> have "AA\<inter>AA2\<in>?Ux" using neigh_filter(1) IsFilter_def by auto
              moreover
              from \<open>BB\<in>?Uy\<close>\<open>BB2\<in>?Uy\<close>\<open>y\<in>\<Union>T\<close> have "BB\<inter>BB2\<in>?Uy" using neigh_filter(1) IsFilter_def by auto
              ultimately have "A\<inter>B\<in>?FF" by auto
            }
            ultimately have "A\<inter>B\<in>?FF" using \<open>B\<in>?FF\<close> by auto
          }
          ultimately have "A\<inter>B\<in>?FF" using \<open>A\<in>?FF\<close> by auto
          then have "\<exists>D\<in>?FF. D\<subseteq>A\<inter>B" unfolding Bex_def by auto
        }
        then have "\<forall>A\<in>?FF. \<forall>B\<in>?FF. \<exists>D\<in>?FF. D\<subseteq>A\<inter>B" by force
        moreover
        have "\<Union>T\<in>?Ux" using \<open>x\<in>\<Union>T\<close> neigh_filter(1) IsFilter_def by auto
        then have "?FF\<noteq>0" by auto
        moreover
        {
          assume "0\<in>?FF"
          moreover
          have "0\<notin>?Ux" using \<open>x\<in>\<Union>T\<close> neigh_filter(1) IsFilter_def by auto
          moreover
          have "0\<notin>?Uy" using \<open>y\<in>\<Union>T\<close> neigh_filter(1) IsFilter_def by auto
          ultimately have "0\<in>{A\<inter>B. \<langle>A,B\<rangle>\<in>?Ux \<times> ?Uy}" by auto
          then obtain A B where "0=A\<inter>B" "A\<in>?Ux""B\<in>?Uy" by auto
          then have "x\<in>int(A)""y\<in>int(B)" by auto
          moreover
          with \<open>0=A\<inter>B\<close> have "int(A)\<inter>int(B)=0" using Top_2_L1 by auto
          moreover
          have "int(A)\<in>T""int(B)\<in>T" using Top_2_L2 by auto
          ultimately have "False" using \<open>\<forall>U\<in>T. \<forall>V\<in>T. x\<in>U\<and>y\<in>V \<longrightarrow> U\<inter>V\<noteq>0\<close> by auto
        }
        then have "0\<notin>?FF" by auto
        ultimately show ?thesis using SatisfiesFilterBase_def by auto
      qed
      moreover
      have "?FF\<subseteq>Pow(\<Union>T)" by auto
      ultimately have bas:"?FF {is a base filter} {A\<in>Pow(\<Union>T). \<exists>D\<in>?FF. D\<subseteq>A}" "\<Union>{A\<in>Pow(\<Union>T). \<exists>D\<in>?FF. D\<subseteq>A}=\<Union>T" 
        using base_unique_filter_set2[of "?FF"] by auto
      then have fil:"{A\<in>Pow(\<Union>T). \<exists>D\<in>?FF. D\<subseteq>A} {is a filter on} \<Union>T" using basic_filter sat by auto
      have "\<forall>U\<in>Pow(\<Union>T). x\<in>int(U) \<longrightarrow> (\<exists>D\<in>?FF. D\<subseteq>U)" by auto
      then have "{A\<in>Pow(\<Union>T). \<exists>D\<in>?FF. D\<subseteq>A} \<rightarrow>\<^sub>F x" using convergence_filter_base2[OF fil bas(1) _ \<open>x\<in>\<Union>T\<close>] by auto
      moreover
      then have "\<forall>U\<in>Pow(\<Union>T). y\<in>int(U) \<longrightarrow> (\<exists>D\<in>?FF. D\<subseteq>U)" by auto
      then have "{A\<in>Pow(\<Union>T). \<exists>D\<in>?FF. D\<subseteq>A} \<rightarrow>\<^sub>F y" using convergence_filter_base2[OF fil bas(1) _ \<open>y\<in>\<Union>T\<close>] by auto
      ultimately have "x=y" using assms fil \<open>x\<in>\<Union>T\<close>\<open>y\<in>\<Union>T\<close> by blast
      with \<open>x\<noteq>y\<close> have "False" by auto
    }
    then have "\<exists>U\<in>T. \<exists>V\<in>T. x\<in>U \<and> y\<in>V \<and> U\<inter>V=0" by blast
  }
  then show ?thesis using isT2_def by auto
qed

lemma (in topology0) unique_limit_net_imp_T2:
  assumes "\<forall>x\<in>\<Union>T. \<forall>y\<in>\<Union>T. \<forall>N. ((N {is a net on}\<Union>T) \<and> (N \<rightarrow>\<^sub>N x) \<and> (N \<rightarrow>\<^sub>N y)) \<longrightarrow> x=y"
  shows "T {is T\<^sub>2}"
proof-
  {
    fix x y \<FF>
    assume "x\<in>\<Union>T" "y\<in>\<Union>T""\<FF> {is a filter on}\<Union>T""\<FF> \<rightarrow>\<^sub>F x""\<FF> \<rightarrow>\<^sub>F y"
    then have "(Net(\<FF>)) {is a net on} \<Union>T""(Net \<FF>) \<rightarrow>\<^sub>N x""(Net \<FF>) \<rightarrow>\<^sub>N y"
      using filter_conver_net_of_filter_conver net_of_filter_is_net by auto
    with  \<open>x\<in>\<Union>T\<close> \<open>y\<in>\<Union>T\<close> have "x=y" using assms by blast
  }
  then have "\<forall>x\<in>\<Union>T. \<forall>y\<in>\<Union>T. \<forall>\<FF>. ((\<FF> {is a filter on}\<Union>T) \<and> (\<FF> \<rightarrow>\<^sub>F x) \<and> (\<FF> \<rightarrow>\<^sub>F y)) \<longrightarrow> x=y" by auto
  then show ?thesis using unique_limit_filter_imp_T2 by auto
qed

text\<open>This results make easy to check if a space is $T_2$.\<close>

text\<open>The topology
which comes from a filter as in @{thm "top_of_filter"} is not $T_2$ generally.
  We will see in this file later on, that the exceptions are a consequence of the spectrum.\<close>

corollary filter_T2_imp_card1:
  assumes "(\<FF>\<union>{0}) {is T\<^sub>2}" "\<FF> {is a filter on} \<Union>\<FF>" "x\<in>\<Union>\<FF>"
  shows "\<Union>\<FF>={x}"
proof-
  {
    fix y assume "y\<in>\<Union>\<FF>"
    then have "\<FF> \<rightarrow>\<^sub>F y {in} (\<FF>\<union>{0})" using lim_filter_top_of_filter assms(2) by auto
    moreover
    have "\<FF> \<rightarrow>\<^sub>F x {in} (\<FF>\<union>{0})" using lim_filter_top_of_filter assms(2,3) by auto
    moreover
    have "\<Union>\<FF>=\<Union>(\<FF>\<union>{0})" by auto
    ultimately
    have "y=x" using topology0.T2_imp_unique_limit_filter[OF topology0_filter[OF assms(2)] assms(1)] assms(2)
      by auto
  }
  then have "\<Union>\<FF>\<subseteq>{x}" by auto
  with assms(3) show ?thesis by auto
qed

text\<open>There are more separation axioms that just $T_0$, $T_1$ or $T_2$\<close>

definition
  isT3 ("_{is T\<^sub>3}" 90)
  where "T{is T\<^sub>3} \<equiv> (T{is T\<^sub>1}) \<and> (T{is regular})"

definition
  IsNormal ("_{is normal}" 90)
  where "T{is normal} \<equiv> \<forall>A. A{is closed in}T \<longrightarrow> (\<forall>B. B{is closed in}T \<and> A\<inter>B=0 \<longrightarrow>
  (\<exists>U\<in>T. \<exists>V\<in>T. A\<subseteq>U\<and>B\<subseteq>V\<and>U\<inter>V=0))"

definition
  isT4 ("_{is T\<^sub>4}" 90)
  where "T{is T\<^sub>4} \<equiv> (T{is T\<^sub>1}) \<and> (T{is normal})"

lemma (in topology0) T4_is_T3:
  assumes "T{is T\<^sub>4}" shows "T{is T\<^sub>3}"
proof-
  from assms have nor:"T{is normal}" using isT4_def by auto
  from assms have "T{is T\<^sub>1}" using isT4_def by auto
  then have "Cofinite (\<Union>T)\<subseteq>T" using T1_cocardinal_coarser by auto
  {
    fix A
    assume AS:"A{is closed in}T"
    {
      fix x
      assume "x\<in>\<Union>T-A"
      have "Finite({x})" by auto
      then obtain n where "{x}\<approx>n" "n\<in>nat" unfolding Finite_def by auto
      then have "{x}\<lesssim>n" "n\<in>nat" using eqpoll_imp_lepoll by auto
      then have "{x}\<prec>nat" using n_lesspoll_nat lesspoll_trans1 by auto
      with \<open>x\<in>\<Union>T-A\<close> have "{x} {is closed in} (Cofinite (\<Union>T))" using Cofinite_def 
        closed_sets_cocardinal by auto
      then have "\<Union>T-{x}\<in>Cofinite(\<Union>T)" unfolding IsClosed_def using union_cocardinal Cofinite_def
        by auto
      with \<open>Cofinite (\<Union>T)\<subseteq>T\<close> have "\<Union>T-{x}\<in>T" by auto
      with \<open>x\<in>\<Union>T-A\<close> have "{x}{is closed in}T" "A\<inter>{x}=0" using IsClosed_def by auto
      with nor AS have "\<exists>U\<in>T. \<exists>V\<in>T. A\<subseteq>U\<and>{x}\<subseteq>V\<and>U\<inter>V=0" unfolding IsNormal_def by blast
      then have "\<exists>U\<in>T. \<exists>V\<in>T. A\<subseteq>U\<and> x\<in>V\<and>U\<inter>V=0" by auto
    }
    then have "\<forall>x\<in>\<Union>T-A. \<exists>U\<in>T. \<exists>V\<in>T. A\<subseteq>U\<and> x\<in>V\<and>U\<inter>V=0" by auto
  }
  then have "T{is regular}" using IsRegular_def by blast
  with \<open>T{is T\<^sub>1}\<close> show ?thesis using isT3_def by auto
qed

lemma (in topology0) T3_is_T2:
  assumes "T{is T\<^sub>3}" shows "T{is T\<^sub>2}"
proof-
  from assms have "T{is regular}" using isT3_def by auto
  from assms have "T{is T\<^sub>1}" using isT3_def by auto
  then have "Cofinite (\<Union>T)\<subseteq>T" using T1_cocardinal_coarser by auto
  {
    fix x y
    assume "x\<in>\<Union>T""y\<in>\<Union>T""x\<noteq>y"
    have "Finite({x})" by auto
    then obtain n where "{x}\<approx>n" "n\<in>nat" unfolding Finite_def by auto
    then have "{x}\<lesssim>n" "n\<in>nat" using eqpoll_imp_lepoll by auto
    then have "{x}\<prec>nat" using n_lesspoll_nat lesspoll_trans1 by auto
    with \<open>x\<in>\<Union>T\<close> have "{x} {is closed in} (Cofinite (\<Union>T))" using Cofinite_def 
      closed_sets_cocardinal by auto
    then have "\<Union>T-{x}\<in>Cofinite(\<Union>T)" unfolding IsClosed_def using union_cocardinal Cofinite_def
       by auto
    with \<open>Cofinite (\<Union>T)\<subseteq>T\<close> have "\<Union>T-{x}\<in>T" by auto
    with \<open>x\<in>\<Union>T\<close>\<open>y\<in>\<Union>T\<close>\<open>x\<noteq>y\<close> have "{x}{is closed in}T" "y\<in>\<Union>T-{x}" using IsClosed_def by auto
    with \<open>T{is regular}\<close> have "\<exists>U\<in>T. \<exists>V\<in>T. {x}\<subseteq>U\<and>y\<in>V\<and>U\<inter>V=0" unfolding IsRegular_def by force
    then have "\<exists>U\<in>T. \<exists>V\<in>T. x\<in>U\<and>y\<in>V\<and>U\<inter>V=0" by auto
  }
  then show ?thesis using isT2_def by auto
qed

text\<open>Regularity can be rewritten in terms of existence of certain neighboorhoods.\<close>

lemma (in topology0) regular_imp_exist_clos_neig:
  assumes "T{is regular}" and "U\<in>T" and "x\<in>U"
  shows "\<exists>V\<in>T. x\<in>V \<and> cl(V)\<subseteq>U"
proof-
  from assms(2) have "(\<Union>T-U){is closed in}T" using Top_3_L9 by auto moreover
  from assms(2,3) have "x\<in>\<Union>T" by auto moreover
  note assms(1,3) ultimately obtain A B where "A\<in>T" and "B\<in>T" and "A\<inter>B=0" and "(\<Union>T-U)\<subseteq>A" and "x\<in>B"
    unfolding IsRegular_def by blast
  from \<open>A\<inter>B=0\<close> \<open>B\<in>T\<close> have "B\<subseteq>\<Union>T-A" by auto
  with \<open>A\<in>T\<close> have "cl(B)\<subseteq>\<Union>T-A" using Top_3_L9 Top_3_L13 by auto
  moreover from \<open>(\<Union>T-U)\<subseteq>A\<close> assms(3) have "\<Union>T-A\<subseteq>U" by auto
  moreover note \<open>x\<in>B\<close> \<open>B\<in>T\<close>
  ultimately have "B\<in>T \<and> x\<in>B \<and> cl(B)\<subseteq>U" by auto
  then show ?thesis by auto
qed

lemma (in topology0) exist_clos_neig_imp_regular:
  assumes "\<forall>x\<in>\<Union>T. \<forall>U\<in>T. x\<in>U \<longrightarrow> (\<exists>V\<in>T. x\<in>V\<and> cl(V)\<subseteq>U)"
  shows "T{is regular}"
proof-
  {
    fix F
    assume "F{is closed in}T" 
    {
      fix x assume "x\<in>\<Union>T-F"
      with \<open>F{is closed in}T\<close> have "x\<in>\<Union>T" "\<Union>T-F\<in>T" "F\<subseteq>\<Union>T" unfolding IsClosed_def by auto
      with assms \<open>x\<in>\<Union>T-F\<close> have "\<exists>V\<in>T. x\<in>V \<and> cl(V)\<subseteq>\<Union>T-F" by auto
      then obtain V where "V\<in>T" "x\<in>V" "cl(V)\<subseteq>\<Union>T-F" by auto
      from \<open>cl(V)\<subseteq>\<Union>T-F\<close> \<open>F\<subseteq>\<Union>T\<close> have "F\<subseteq>\<Union>T-cl(V)" by auto
      moreover from \<open>V\<in>T\<close> have "\<Union>T-(\<Union>T-V)=V" by auto
      then have "cl(V)=\<Union>T-int(\<Union>T-V)" using Top_3_L11(2)[of "\<Union>T-V"] by auto
      ultimately have "F\<subseteq>int(\<Union>T-V)" by auto moreover
      have "int(\<Union>T-V)\<subseteq>\<Union>T-V" using Top_2_L1 by auto
      then have "V\<inter>(int(\<Union>T-V))=0" by auto moreover
      note \<open>x\<in>V\<close>\<open>V\<in>T\<close> ultimately
      have "V\<in>T" "int(\<Union>T-V)\<in>T" "F\<subseteq>int(\<Union>T-V) \<and> x\<in>V \<and> (int(\<Union>T-V))\<inter>V=0" using Top_2_L2
        by auto
      then have "\<exists>U\<in>T. \<exists>V\<in>T. F\<subseteq>U \<and> x\<in>V \<and> U\<inter>V=0" by auto
    }
    then have "\<forall>x\<in>\<Union>T-F. \<exists>U\<in>T. \<exists>V\<in>T. F\<subseteq>U \<and> x\<in>V \<and> U\<inter>V=0" by auto
  }
  then show ?thesis using IsRegular_def by blast
qed

lemma (in topology0) regular_eq:
  shows "T{is regular} \<longleftrightarrow> (\<forall>x\<in>\<Union>T. \<forall>U\<in>T. x\<in>U \<longrightarrow> (\<exists>V\<in>T. x\<in>V\<and> cl(V)\<subseteq>U))"
  using regular_imp_exist_clos_neig exist_clos_neig_imp_regular by force

text\<open>A Hausdorff space separates compact spaces from points.\<close>

theorem (in topology0) T2_compact_point:
  assumes "T{is T\<^sub>2}" "A{is compact in}T" "x\<in>\<Union>T" "x\<notin>A"
  shows "\<exists>U\<in>T. \<exists>V\<in>T. A\<subseteq>U \<and> x\<in>V \<and> U\<inter>V=0"
proof-
  {
    assume "A=0"
    then have "A\<subseteq>0\<and>x\<in>\<Union>T\<and>(0\<inter>(\<Union>T)=0)" using assms(3) by auto 
    then have ?thesis using empty_open topSpaceAssum unfolding IsATopology_def by auto
  }
  moreover
  {
    assume noEmpty:"A\<noteq>0"
    let ?U="{\<langle>U,V\<rangle>\<in>T\<times>T. x\<in>U\<and>U\<inter>V=0}"
    {
      fix y assume "y\<in>A"
      with \<open>x\<notin>A\<close> assms(4) have "x\<noteq>y" by auto
      moreover from \<open>y\<in>A\<close> have "x\<in>\<Union>T""y\<in>\<Union>T" using assms(2,3) unfolding IsCompact_def by auto
      ultimately obtain U V where "U\<in>T""V\<in>T""U\<inter>V=0""x\<in>U""y\<in>V" using assms(1) unfolding isT2_def by blast
      then have "\<exists>\<langle>U,V\<rangle>\<in>?U. y\<in>V" by auto
    }
    then have "\<forall>y\<in>A. \<exists>\<langle>U,V\<rangle>\<in>?U. y\<in>V" by auto
    then have "A\<subseteq>\<Union>{snd(B). B\<in>?U}" by auto
    moreover have "{snd(B). B\<in>?U}\<in>Pow(T)" by auto
    ultimately have "\<exists>N\<in>FinPow({snd(B). B\<in>?U}). A\<subseteq>\<Union>N" using assms(2) unfolding IsCompact_def by auto
    then obtain N where ss:"N\<in>FinPow({snd(B). B\<in>?U})" "A\<subseteq>\<Union>N" by auto
    with \<open>{snd(B). B\<in>?U}\<in>Pow(T)\<close> have "A\<subseteq>\<Union>N" "N\<in>Pow(T)" unfolding FinPow_def by auto
    then have NN:"A\<subseteq>\<Union>N" "\<Union>N\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
    from ss have "Finite(N)""N\<subseteq>{snd(B). B\<in>?U}" unfolding FinPow_def by auto
    then obtain n where "n\<in>nat" "N\<approx>n" unfolding Finite_def by auto
    then have "N\<lesssim>n" using eqpoll_imp_lepoll by auto
    from noEmpty \<open>A\<subseteq>\<Union>N\<close> have NnoEmpty:"N\<noteq>0" by auto
    let ?QQ="{\<langle>n,{fst(B). B\<in>{A\<in>?U. snd(A)=n}}\<rangle>. n\<in>N}"
    have QQPi:"?QQ:N\<rightarrow>{{fst(B). B\<in>{A\<in>?U. snd(A)=n}}. n\<in>N}" unfolding Pi_def function_def domain_def by auto
    {
      fix n assume "n\<in>N"
      with \<open>N\<subseteq>{snd(B). B\<in>?U}\<close> obtain B where "n=snd(B)" "B\<in>?U" by auto
      then have "fst(B)\<in>{fst(B). B\<in>{A\<in>?U. snd(A)=n}}" by auto
      then have "{fst(B). B\<in>{A\<in>?U. snd(A)=n}}\<noteq>0" by auto moreover
      from \<open>n\<in>N\<close> have "\<langle>n,{fst(B). B\<in>{A\<in>?U. snd(A)=n}}\<rangle>\<in>?QQ" by auto
      with QQPi have "?QQ`n={fst(B). B\<in>{A\<in>?U. snd(A)=n}}" using apply_equality by auto
      ultimately have "?QQ`n\<noteq>0" by auto
    }
    then have "\<forall>n\<in>N. ?QQ`n\<noteq>0" by auto
    with \<open>n\<in>nat\<close> \<open>N\<lesssim>n\<close> have "\<exists>f. f\<in>Pi(N,\<lambda>t. ?QQ`t) \<and> (\<forall>t\<in>N. f`t\<in>?QQ`t)" using finite_choice unfolding AxiomCardinalChoiceGen_def
      by auto
    then obtain f where fPI:"f\<in>Pi(N,\<lambda>t. ?QQ`t)" "(\<forall>t\<in>N. f`t\<in>?QQ`t)" by auto
    from fPI(1) NnoEmpty have "range(f)\<noteq>0" unfolding Pi_def range_def domain_def converse_def by (safe,blast)
    {
      fix t assume "t\<in>N"
      then have "f`t\<in>?QQ`t" using fPI(2) by auto
      with \<open>t\<in>N\<close> have "f`t\<in>\<Union>(?QQ``N)" "?QQ`t\<subseteq>\<Union>(?QQ``N)" using func_imagedef QQPi by auto
    }
    then have reg:"\<forall>t\<in>N. f`t\<in>\<Union>(?QQ``N)"  "\<forall>t\<in>N. ?QQ`t\<subseteq>\<Union>(?QQ``N)" by auto
    {
      fix tt assume "tt\<in>f"
      with fPI(1) have "tt\<in>Sigma(N, (`)(?QQ))" unfolding Pi_def by auto
      then have "tt\<in>(\<Union>xa\<in>N. \<Union>y\<in>?QQ`xa. {\<langle>xa,y\<rangle>})" unfolding Sigma_def by auto
      then obtain xa y where "xa\<in>N" "y\<in>?QQ`xa" "tt=\<langle>xa,y\<rangle>" by auto
      with reg(2) have "y\<in>\<Union>(?QQ``N)" by blast
      with \<open>tt=\<langle>xa,y\<rangle>\<close> \<open>xa\<in>N\<close> have "tt\<in>(\<Union>xa\<in>N. \<Union>y\<in>\<Union>(?QQ``N). {\<langle>xa,y\<rangle>})" by auto
      then have "tt\<in>N\<times>(\<Union>(?QQ``N))" unfolding Sigma_def by auto
    }
    then have ffun:"f:N\<rightarrow>\<Union>(?QQ``N)"  using fPI(1) unfolding Pi_def by auto
    then have "f\<in>surj(N,range(f))" using fun_is_surj by auto
    with \<open>N\<lesssim>n\<close> \<open>n\<in>nat\<close> have "range(f)\<lesssim>N" using surj_fun_inv_2 nat_into_Ord by auto
    with \<open>N\<lesssim>n\<close> have "range(f)\<lesssim>n" using lepoll_trans by blast
    with \<open>n\<in>nat\<close> have "Finite(range(f))" using n_lesspoll_nat lesspoll_nat_is_Finite lesspoll_trans1 by auto
    moreover from ffun have rr:"range(f)\<subseteq>\<Union>(?QQ``N)" unfolding Pi_def by auto
    then have "range(f)\<subseteq>T" by auto
    ultimately have "range(f)\<in>FinPow(T)" unfolding FinPow_def by auto
    then have "\<Inter>range(f)\<in>T" using fin_inter_open_open \<open>range(f)\<noteq>0\<close> by auto moreover
    {
      fix S assume "S\<in>range(f)"
      with rr have "S\<in>\<Union>(?QQ``N)" by blast
      then have "\<exists>B\<in>(?QQ``N). S \<in> B" using Union_iff by auto
      then obtain B where "B\<in>(?QQ``N)" "S\<in>B" by auto
      then have "\<exists>rr\<in>N. \<langle>rr,B\<rangle>\<in>?QQ" unfolding image_def by auto
      then have "\<exists>rr\<in>N. B={fst(B). B\<in>{A\<in>?U. snd(A)=rr}}" by auto
      with \<open>S\<in>B\<close> obtain rr where "\<langle>S,rr\<rangle>\<in>?U" by auto
      then have "x\<in>S" by auto
    }
    then have "x\<in>\<Inter>range(f)" using \<open>range(f)\<noteq>0\<close> by auto moreover
    {
      fix y assume "y\<in>(\<Union>N)\<inter>(\<Inter>range(f))"
      then have reg:"(\<forall>S\<in>range(f). y\<in>S)\<and>(\<exists>t\<in>N. y\<in>t)" by auto
      then obtain t where "t\<in>N" "y\<in>t" by auto
      then have "\<langle>t, {fst(B). B\<in>{A\<in>?U. snd(A)=t}}\<rangle>\<in>?QQ" by auto
      then have "f`t\<in>range(f)" using apply_rangeI ffun by auto
      with reg have yft:"y\<in>f`t" by auto
      with \<open>t\<in>N\<close> fPI(2) have "f`t\<in>?QQ`t" by auto
      with \<open>t\<in>N\<close> have "f`t\<in>{fst(B). B\<in>{A\<in>?U. snd(A)=t}}" using apply_equality QQPi by auto
      then have "\<langle>f`t,t\<rangle>\<in>?U" by auto
      then have "f`t\<inter>t=0" by auto
      with \<open>y\<in>t\<close> yft have "False" by auto
    }
    then have "(\<Union>N)\<inter>(\<Inter>range(f))=0" by blast moreover
    note NN
    ultimately have ?thesis by auto
  }
  ultimately show ?thesis by auto
qed

text\<open>A Hausdorff space separates compact spaces from other compact spaces.\<close>

theorem (in topology0) T2_compact_compact:
  assumes "T{is T\<^sub>2}" "A{is compact in}T" "B{is compact in}T" "A\<inter>B=0"
  shows "\<exists>U\<in>T. \<exists>V\<in>T. A\<subseteq>U \<and> B\<subseteq>V \<and> U\<inter>V=0"
proof-
 {
    assume "B=0"
    then have "A\<subseteq>\<Union>T\<and>B\<subseteq>0\<and>((\<Union>T)\<inter>0=0)" using assms(2) unfolding IsCompact_def by auto moreover
    have "0\<in>T" using empty_open topSpaceAssum by auto moreover
    have "\<Union>T\<in>T" using topSpaceAssum unfolding IsATopology_def by auto ultimately
    have ?thesis by auto
  }
  moreover
  {
    assume noEmpty:"B\<noteq>0"
    let ?U="{\<langle>U,V\<rangle>\<in>T\<times>T. A\<subseteq>U \<and> U\<inter>V=0}"
    {
      fix y assume "y\<in>B"
      then have "y\<in>\<Union>T" using assms(3) unfolding IsCompact_def by auto
      with \<open>y\<in>B\<close> have "\<exists>U\<in>T. \<exists>V\<in>T. A\<subseteq>U \<and> y\<in>V \<and> U\<inter>V=0" using T2_compact_point assms(1,2,4) by auto
      then have "\<exists>\<langle>U,V\<rangle>\<in>?U. y\<in>V" by auto
    }
    then have "\<forall>y\<in>B. \<exists>\<langle>U,V\<rangle>\<in>?U. y\<in>V" by auto
    then have "B\<subseteq>\<Union>{snd(B). B\<in>?U}" by auto
    moreover have "{snd(B). B\<in>?U}\<in>Pow(T)" by auto
    ultimately have "\<exists>N\<in>FinPow({snd(B). B\<in>?U}). B\<subseteq>\<Union>N" using assms(3) unfolding IsCompact_def by auto
    then obtain N where ss:"N\<in>FinPow({snd(B). B\<in>?U})" "B\<subseteq>\<Union>N" by auto
    with \<open>{snd(B). B\<in>?U}\<in>Pow(T)\<close> have "B\<subseteq>\<Union>N" "N\<in>Pow(T)" unfolding FinPow_def by auto
    then have NN:"B\<subseteq>\<Union>N" "\<Union>N\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
    from ss have "Finite(N)""N\<subseteq>{snd(B). B\<in>?U}" unfolding FinPow_def by auto
    then obtain n where "n\<in>nat" "N\<approx>n" unfolding Finite_def by auto
    then have "N\<lesssim>n" using eqpoll_imp_lepoll by auto
    from noEmpty \<open>B\<subseteq>\<Union>N\<close> have NnoEmpty:"N\<noteq>0" by auto
    let ?QQ="{\<langle>n,{fst(B). B\<in>{A\<in>?U. snd(A)=n}}\<rangle>. n\<in>N}"
    have QQPi:"?QQ:N\<rightarrow>{{fst(B). B\<in>{A\<in>?U. snd(A)=n}}. n\<in>N}" unfolding Pi_def function_def domain_def by auto
    {
      fix n assume "n\<in>N"
      with \<open>N\<subseteq>{snd(B). B\<in>?U}\<close> obtain B where "n=snd(B)" "B\<in>?U" by auto
      then have "fst(B)\<in>{fst(B). B\<in>{A\<in>?U. snd(A)=n}}" by auto
      then have "{fst(B). B\<in>{A\<in>?U. snd(A)=n}}\<noteq>0" by auto moreover
      from \<open>n\<in>N\<close> have "\<langle>n,{fst(B). B\<in>{A\<in>?U. snd(A)=n}}\<rangle>\<in>?QQ" by auto
      with QQPi have "?QQ`n={fst(B). B\<in>{A\<in>?U. snd(A)=n}}" using apply_equality by auto
      ultimately have "?QQ`n\<noteq>0" by auto
    }
    then have "\<forall>n\<in>N. ?QQ`n\<noteq>0" by auto
    with \<open>n\<in>nat\<close> \<open>N\<lesssim>n\<close> have "\<exists>f. f\<in>Pi(N,\<lambda>t. ?QQ`t) \<and> (\<forall>t\<in>N. f`t\<in>?QQ`t)" using finite_choice unfolding AxiomCardinalChoiceGen_def
      by auto
    then obtain f where fPI:"f\<in>Pi(N,\<lambda>t. ?QQ`t)" "(\<forall>t\<in>N. f`t\<in>?QQ`t)" by auto
    from fPI(1) NnoEmpty have "range(f)\<noteq>0" unfolding Pi_def range_def domain_def converse_def by (safe,blast)
    {
      fix t assume "t\<in>N"
      then have "f`t\<in>?QQ`t" using fPI(2) by auto
      with \<open>t\<in>N\<close> have "f`t\<in>\<Union>(?QQ``N)" "?QQ`t\<subseteq>\<Union>(?QQ``N)" using func_imagedef QQPi by auto
    }
    then have reg:"\<forall>t\<in>N. f`t\<in>\<Union>(?QQ``N)"  "\<forall>t\<in>N. ?QQ`t\<subseteq>\<Union>(?QQ``N)" by auto
    {
      fix tt assume "tt\<in>f"
      with fPI(1) have "tt\<in>Sigma(N, (`)(?QQ))" unfolding Pi_def by auto
      then have "tt\<in>(\<Union>xa\<in>N. \<Union>y\<in>?QQ`xa. {\<langle>xa,y\<rangle>})" unfolding Sigma_def by auto
      then obtain xa y where "xa\<in>N" "y\<in>?QQ`xa" "tt=\<langle>xa,y\<rangle>" by auto
      with reg(2) have "y\<in>\<Union>(?QQ``N)" by blast
      with \<open>tt=\<langle>xa,y\<rangle>\<close> \<open>xa\<in>N\<close> have "tt\<in>(\<Union>xa\<in>N. \<Union>y\<in>\<Union>(?QQ``N). {\<langle>xa,y\<rangle>})" by auto
      then have "tt\<in>N\<times>(\<Union>(?QQ``N))" unfolding Sigma_def by auto
    }
    then have ffun:"f:N\<rightarrow>\<Union>(?QQ``N)"  using fPI(1) unfolding Pi_def by auto
    then have "f\<in>surj(N,range(f))" using fun_is_surj by auto
    with \<open>N\<lesssim>n\<close> \<open>n\<in>nat\<close> have "range(f)\<lesssim>N" using surj_fun_inv_2 nat_into_Ord by auto
    with \<open>N\<lesssim>n\<close> have "range(f)\<lesssim>n" using lepoll_trans by blast
    with \<open>n\<in>nat\<close> have "Finite(range(f))" using n_lesspoll_nat lesspoll_nat_is_Finite lesspoll_trans1 by auto
    moreover from ffun have rr:"range(f)\<subseteq>\<Union>(?QQ``N)" unfolding Pi_def by auto
    then have "range(f)\<subseteq>T" by auto
    ultimately have "range(f)\<in>FinPow(T)" unfolding FinPow_def by auto
    then have "\<Inter>range(f)\<in>T" using fin_inter_open_open \<open>range(f)\<noteq>0\<close> by auto moreover
    {
      fix S assume "S\<in>range(f)"
      with rr have "S\<in>\<Union>(?QQ``N)" by blast
      then have "\<exists>B\<in>(?QQ``N). S \<in> B" using Union_iff by auto
      then obtain B where "B\<in>(?QQ``N)" "S\<in>B" by auto
      then have "\<exists>rr\<in>N. \<langle>rr,B\<rangle>\<in>?QQ" unfolding image_def by auto
      then have "\<exists>rr\<in>N. B={fst(B). B\<in>{A\<in>?U. snd(A)=rr}}" by auto
      with \<open>S\<in>B\<close> obtain rr where "\<langle>S,rr\<rangle>\<in>?U" by auto
      then have "A\<subseteq>S" by auto
    }
    then have "A\<subseteq>\<Inter>range(f)" using \<open>range(f)\<noteq>0\<close> by auto moreover
    {
      fix y assume "y\<in>(\<Union>N)\<inter>(\<Inter>range(f))"
      then have reg:"(\<forall>S\<in>range(f). y\<in>S)\<and>(\<exists>t\<in>N. y\<in>t)" by auto
      then obtain t where "t\<in>N" "y\<in>t" by auto
      then have "\<langle>t, {fst(B). B\<in>{A\<in>?U. snd(A)=t}}\<rangle>\<in>?QQ" by auto
      then have "f`t\<in>range(f)" using apply_rangeI ffun by auto
      with reg have yft:"y\<in>f`t" by auto
      with \<open>t\<in>N\<close> fPI(2) have "f`t\<in>?QQ`t" by auto
      with \<open>t\<in>N\<close> have "f`t\<in>{fst(B). B\<in>{A\<in>?U. snd(A)=t}}" using apply_equality QQPi by auto
      then have "\<langle>f`t,t\<rangle>\<in>?U" by auto
      then have "f`t\<inter>t=0" by auto
      with \<open>y\<in>t\<close> yft have "False" by auto
    }
    then have "(\<Inter>range(f))\<inter>(\<Union>N)=0" by blast moreover
    note NN
    ultimately have ?thesis by auto
  }
  ultimately show ?thesis by auto
qed

text\<open>A compact Hausdorff space is normal.\<close>

corollary (in topology0) T2_compact_is_normal:
  assumes "T{is T\<^sub>2}" "(\<Union>T){is compact in}T"
  shows "T{is normal}" unfolding IsNormal_def
proof-
  from assms(2) have car_nat:"(\<Union>T){is compact of cardinal}nat{in}T" using Compact_is_card_nat by auto
  {
    fix A B assume "A{is closed in}T" "B{is closed in}T""A\<inter>B=0"
    then have com:"((\<Union>T)\<inter>A){is compact of cardinal}nat{in}T" "((\<Union>T)\<inter>B){is compact of cardinal}nat{in}T" using compact_closed[OF car_nat] 
      by auto
    from \<open>A{is closed in}T\<close>\<open>B{is closed in}T\<close> have "(\<Union>T)\<inter>A=A""(\<Union>T)\<inter>B=B" unfolding IsClosed_def by auto
    with com have "A{is compact of cardinal}nat{in}T" "B{is compact of cardinal}nat{in}T" by auto
    then have "A{is compact in}T""B{is compact in}T" using Compact_is_card_nat by auto
    with \<open>A\<inter>B=0\<close> have "\<exists>U\<in>T. \<exists>V\<in>T. A\<subseteq>U \<and> B\<subseteq>V \<and> U\<inter>V=0" using T2_compact_compact assms(1) by auto
  }
  then show " \<forall>A. A {is closed in} T \<longrightarrow> (\<forall>B. B {is closed in} T \<and> A \<inter> B = 0 \<longrightarrow> (\<exists>U\<in>T. \<exists>V\<in>T. A \<subseteq> U \<and> B \<subseteq> V \<and> U \<inter> V = 0))"
    by auto
qed

subsection\<open>Hereditability\<close>

text\<open>A topological property is hereditary if whenever a space has it, 
every subspace also has it.\<close>

definition IsHer ("_{is hereditary}" 90)
  where "P {is hereditary} \<equiv> \<forall>T. T{is a topology} \<and> P(T) \<longrightarrow> (\<forall>A\<in>Pow(\<Union>T). P(T{restricted to}A))"

lemma subspace_of_subspace:
  assumes "A\<subseteq>B""B\<subseteq>\<Union>T"
  shows "T{restricted to}A=(T{restricted to}B){restricted to}A"
proof
  from assms have S:"\<forall>S\<in>T. A\<inter>(B\<inter>S)=A\<inter>S" by auto
  then show "T {restricted to} A \<subseteq> T {restricted to} B {restricted to} A" unfolding RestrictedTo_def
    by auto
  from S show "T {restricted to} B {restricted to} A \<subseteq> T {restricted to} A" unfolding RestrictedTo_def
    by auto
qed
 
text\<open>The separation properties $T_0$, $T_1$, $T_2$ y $T_3$ are hereditary.\<close>

theorem regular_here:
  assumes "T{is regular}" "A\<in>Pow(\<Union>T)" shows "(T{restricted to}A){is regular}"
proof-
  {
    fix C
    assume A:"C{is closed in}(T{restricted to}A)"
    {fix y assume "y\<in>\<Union>(T{restricted to}A)""y\<notin>C"
    with A have "(\<Union>(T{restricted to}A))-C\<in>(T{restricted to}A)""C\<subseteq>\<Union>(T{restricted to}A)" "y\<in>\<Union>(T{restricted to}A)""y\<notin>C" unfolding IsClosed_def
      by auto
    moreover
    with assms(2) have "\<Union>(T{restricted to}A)=A" unfolding RestrictedTo_def by auto
    ultimately have "A-C\<in>T{restricted to}A" "y\<in>A""y\<notin>C""C\<in>Pow(A)" by auto
    then obtain S where "S\<in>T" "A\<inter>S=A-C" "y\<in>A""y\<notin>C" unfolding RestrictedTo_def by auto
    then have "y\<in>A-C""A\<inter>S=A-C" by auto
    with \<open>C\<in>Pow(A)\<close> have "y\<in>A\<inter>S""C=A-A\<inter>S" by auto
    then have "y\<in>S" "C=A-S" by auto
    with assms(2) have "y\<in>S" "C\<subseteq>\<Union>T-S" by auto
    moreover
    from \<open>S\<in>T\<close> have "\<Union>T-(\<Union>T-S)=S" by auto
    moreover
    with \<open>S\<in>T\<close> have "(\<Union>T-S) {is closed in}T" using IsClosed_def by auto
    ultimately have "y\<in>\<Union>T-(\<Union>T-S)" "(\<Union>T-S) {is closed in}T" by auto
    with assms(1) have "\<forall>y\<in>\<Union>T-(\<Union>T-S). \<exists>U\<in>T. \<exists>V\<in>T. (\<Union>T-S)\<subseteq>U\<and>y\<in>V\<and>U\<inter>V=0" unfolding IsRegular_def by auto
    with \<open>y\<in>\<Union>T-(\<Union>T-S)\<close> have "\<exists>U\<in>T. \<exists>V\<in>T. (\<Union>T-S)\<subseteq>U\<and>y\<in>V\<and>U\<inter>V=0" by auto
    then obtain U V where "U\<in>T""V\<in>T" "\<Union>T-S\<subseteq>U""y\<in>V""U\<inter>V=0" by auto
    then have "A\<inter>U\<in>(T{restricted to}A)""A\<inter>V\<in>(T{restricted to}A)" "C\<subseteq>U""y\<in>V""(A\<inter>U)\<inter>(A\<inter>V)=0"
      unfolding RestrictedTo_def  using \<open>C\<subseteq>\<Union>T-S\<close> by auto
    moreover
    with \<open>C\<in>Pow(A)\<close>\<open>y\<in>A\<close> have "C\<subseteq>A\<inter>U""y\<in>A\<inter>V" by auto
    ultimately have "\<exists>U\<in>(T{restricted to}A). \<exists>V\<in>(T{restricted to}A). C\<subseteq>U\<and>y\<in>V\<and>U\<inter>V=0" by auto
  }
    then have "\<forall>x\<in>\<Union>(T{restricted to}A)-C. \<exists>U\<in>(T{restricted to}A). \<exists>V\<in>(T{restricted to}A). C\<subseteq>U\<and>x\<in>V\<and>U\<inter>V=0" by auto
  }
  then have "\<forall>C. C{is closed in}(T{restricted to}A) \<longrightarrow> (\<forall>x\<in>\<Union>(T{restricted to}A)-C. \<exists>U\<in>(T{restricted to}A). \<exists>V\<in>(T{restricted to}A). C\<subseteq>U\<and>x\<in>V\<and>U\<inter>V=0)"
   by blast
  then show ?thesis using IsRegular_def by auto
qed

corollary here_regular:
  shows "IsRegular {is hereditary}" using regular_here IsHer_def by auto

theorem T1_here:
  assumes "T{is T\<^sub>1}" "A\<in>Pow(\<Union>T)" shows "(T{restricted to}A){is T\<^sub>1}"
proof-
  from assms(2) have un:"\<Union>(T{restricted to}A)=A" unfolding RestrictedTo_def by auto
  {
    fix x y
    assume "x\<in>A""y\<in>A""x\<noteq>y"
    with \<open>A\<in>Pow(\<Union>T)\<close> have "x\<in>\<Union>T""y\<in>\<Union>T""x\<noteq>y" by auto
    then have "\<exists>U\<in>T. x\<in>U\<and>y\<notin>U" using assms(1) isT1_def by auto
    then obtain U where "U\<in>T""x\<in>U""y\<notin>U" by auto
    with \<open>x\<in>A\<close> have "A\<inter>U\<in>(T{restricted to}A)" "x\<in>A\<inter>U" "y\<notin>A\<inter>U" unfolding RestrictedTo_def by auto
    then have "\<exists>U\<in>(T{restricted to}A). x\<in>U\<and>y\<notin>U" by blast
  }
  with un have "\<forall>x y. x\<in>\<Union>(T{restricted to}A) \<and> y\<in>\<Union>(T{restricted to}A) \<and> x\<noteq>y \<longrightarrow> (\<exists>U\<in>(T{restricted to}A). x\<in>U\<and>y\<notin>U)"
    by auto
  then show ?thesis using isT1_def by auto
qed

corollary here_T1:
  shows "isT1 {is hereditary}" using T1_here IsHer_def by auto

lemma here_and:
  assumes "P {is hereditary}" "Q {is hereditary}"
  shows "(\<lambda>T. P(T) \<and> Q(T)) {is hereditary}" using assms unfolding IsHer_def by auto

corollary here_T3:
  shows "isT3 {is hereditary}" using here_and[OF here_T1 here_regular] unfolding IsHer_def isT3_def.

lemma T2_here:
  assumes "T{is T\<^sub>2}" "A\<in>Pow(\<Union>T)" shows "(T{restricted to}A){is T\<^sub>2}"
proof-
  from assms(2) have un:"\<Union>(T{restricted to}A)=A" unfolding RestrictedTo_def by auto
  {
    fix x y
    assume "x\<in>A""y\<in>A""x\<noteq>y"
    with \<open>A\<in>Pow(\<Union>T)\<close> have "x\<in>\<Union>T""y\<in>\<Union>T""x\<noteq>y" by auto
    then have "\<exists>U\<in>T. \<exists>V\<in>T. x\<in>U\<and>y\<in>V\<and>U\<inter>V=0" using assms(1) isT2_def by auto
    then obtain U V where "U\<in>T" "V\<in>T""x\<in>U""y\<in>V""U\<inter>V=0" by auto
    with \<open>x\<in>A\<close>\<open>y\<in>A\<close> have "A\<inter>U\<in>(T{restricted to}A)""A\<inter>V\<in>(T{restricted to}A)" "x\<in>A\<inter>U" "y\<in>A\<inter>V" "(A\<inter>U)\<inter>(A\<inter>V)=0"unfolding RestrictedTo_def by auto
    then have "\<exists>U\<in>(T{restricted to}A). \<exists>V\<in>(T{restricted to}A). x\<in>U\<and>y\<in>V\<and>U\<inter>V=0" unfolding Bex_def by auto
  }
  with un have "\<forall>x y. x\<in>\<Union>(T{restricted to}A) \<and> y\<in>\<Union>(T{restricted to}A) \<and> x\<noteq>y \<longrightarrow> (\<exists>U\<in>(T{restricted to}A). \<exists>V\<in>(T{restricted to}A). x\<in>U\<and>y\<in>V\<and>U\<inter>V=0)"
    by auto
  then show ?thesis using isT2_def by auto
qed

corollary here_T2:
  shows "isT2 {is hereditary}" using T2_here IsHer_def by auto

lemma T0_here:
  assumes "T{is T\<^sub>0}" "A\<in>Pow(\<Union>T)" shows "(T{restricted to}A){is T\<^sub>0}"
proof-
  from assms(2) have un:"\<Union>(T{restricted to}A)=A" unfolding RestrictedTo_def by auto
  {
    fix x y
    assume "x\<in>A""y\<in>A""x\<noteq>y"
    with \<open>A\<in>Pow(\<Union>T)\<close> have "x\<in>\<Union>T""y\<in>\<Union>T""x\<noteq>y" by auto
    then have "\<exists>U\<in>T. (x\<in>U\<and>y\<notin>U)\<or>(y\<in>U\<and>x\<notin>U)" using assms(1) isT0_def by auto
    then obtain U where "U\<in>T" "(x\<in>U\<and>y\<notin>U)\<or>(y\<in>U\<and>x\<notin>U)" by auto
    with \<open>x\<in>A\<close>\<open>y\<in>A\<close> have "A\<inter>U\<in>(T{restricted to}A)" "(x\<in>A\<inter>U\<and>y\<notin>A\<inter>U)\<or>(y\<in>A\<inter>U\<and>x\<notin>A\<inter>U)" unfolding RestrictedTo_def by auto
    then have "\<exists>U\<in>(T{restricted to}A). (x\<in>U\<and>y\<notin>U)\<or>(y\<in>U\<and>x\<notin>U)" unfolding Bex_def by auto
  }
  with un have "\<forall>x y. x\<in>\<Union>(T{restricted to}A) \<and> y\<in>\<Union>(T{restricted to}A) \<and> x\<noteq>y \<longrightarrow> (\<exists>U\<in>(T{restricted to}A). (x\<in>U\<and>y\<notin>U)\<or>(y\<in>U\<and>x\<notin>U))"
    by auto
  then show ?thesis using isT0_def by auto
qed

corollary here_T0:
  shows "isT0 {is hereditary}" using T0_here IsHer_def by auto

subsection\<open>Spectrum and anti-properties\<close>

text\<open>The spectrum of a topological property is a class of
sets such that all topologies defined over that set have that property.\<close>

text\<open>The spectrum of a property gives us the list of sets for which the property doesn't give
any topological information. Being in the spectrum of a topological property is an invariant
in the category of sets and function; mening that equipollent sets are in the same
spectra.\<close>
      
definition Spec ("_ {is in the spectrum of} _" 99)
  where "Spec(K,P) \<equiv> \<forall>T. ((T{is a topology} \<and> \<Union>T\<approx>K) \<longrightarrow> P(T))"

lemma equipollent_spect:
  assumes "A\<approx>B" "B {is in the spectrum of} P"
  shows  "A {is in the spectrum of} P"
proof-
  from assms(2) have "\<forall>T. ((T{is a topology} \<and> \<Union>T\<approx>B) \<longrightarrow> P(T))" using Spec_def by auto
  then have "\<forall>T. ((T{is a topology} \<and> \<Union>T\<approx>A) \<longrightarrow> P(T))" using eqpoll_trans[OF _ assms(1)] by auto
  then show ?thesis using Spec_def by auto
qed

theorem eqpoll_iff_spec:
  assumes "A\<approx>B"
  shows "(B {is in the spectrum of} P) \<longleftrightarrow> (A {is in the spectrum of} P)"
proof
  assume "B {is in the spectrum of} P"
  with assms equipollent_spect show "A {is in the spectrum of} P" by auto
next
  assume "A {is in the spectrum of} P"
  moreover
  from assms have "B\<approx>A" using eqpoll_sym by auto
  ultimately show "B {is in the spectrum of} P" using equipollent_spect by auto
qed

text\<open>From the previous statement, we see that the spectrum could be formed only by
representative of clases of sets. If \emph{AC} holds, this means that the spectrum
can be taken as a set or class of cardinal numbers.\<close>

text\<open>Here is an example of the spectrum. The proof lies in the indiscrite filter \<open>{A}\<close>
that can be build for any set. In this proof, we see that without choice,
there is no way to define the sepctrum of a property with cardinals because if a set is not 
comparable with any ordinal, its cardinal is defined as \<open>0\<close> without the set being
empty.\<close>

theorem T4_spectrum:
  shows "(A {is in the spectrum of} isT4) \<longleftrightarrow> A \<lesssim> 1"
proof
  assume "A {is in the spectrum of} isT4"
  then have reg:"\<forall>T. ((T{is a topology} \<and> \<Union>T\<approx>A) \<longrightarrow> (T {is T\<^sub>4}))" using Spec_def by auto
  {
    assume "A\<noteq>0"
    then obtain x where "x\<in>A" by auto
    then have "x\<in>\<Union>{A}" by auto
    moreover
    then have "{A} {is a filter on}\<Union>{A}" using IsFilter_def by auto
    moreover
    then have "({A}\<union>{0}) {is a topology} \<and> \<Union>({A}\<union>{0})=A" using top_of_filter by auto
    then have top:"({A}\<union>{0}) {is a topology}" "\<Union>({A}\<union>{0})\<approx>A" using eqpoll_refl by auto
    then have "({A}\<union>{0}) {is T\<^sub>4}" using reg by auto
    then have "({A}\<union>{0}) {is T\<^sub>2}" using topology0.T3_is_T2 topology0.T4_is_T3 topology0_def top by auto
    ultimately have "\<Union>{A}={x}" using filter_T2_imp_card1[of "{A}""x"] by auto
    then have "A={x}" by auto
    then have "A\<approx>1" using singleton_eqpoll_1 by auto
  }
  moreover
  have "A=0 \<longrightarrow> A\<approx>0" by auto
  ultimately have "A\<approx>1\<or>A\<approx>0" by blast
  then show "A\<lesssim>1" using empty_lepollI eqpoll_imp_lepoll eq_lepoll_trans by auto
next
  assume "A\<lesssim>1"
  have "A=0\<or>A\<noteq>0" by auto
  then obtain E where "A=0\<or>E\<in>A" by auto
  then have "A\<approx>0\<or>E\<in>A" by auto
  with \<open>A\<lesssim>1\<close> have "A\<approx>0\<or>A={E}" using lepoll_1_is_sing by auto
  then have "A\<approx>0\<or>A\<approx>1" using singleton_eqpoll_1 by auto
  {
    fix T
    assume AS:"T{is a topology}""\<Union>T\<approx>A"
    {
      assume "A\<approx>0"
      with AS have "T{is a topology}" and empty:"\<Union>T=0" using eqpoll_trans eqpoll_0_is_0 by auto
      then have "T{is T\<^sub>2}" using isT2_def by auto
      then have "T{is T\<^sub>1}" using T2_is_T1 by auto
      moreover
      from empty have "T\<subseteq>{0}" by auto
      with AS(1) have "T={0}" using empty_open by auto
      from empty have rr:"\<forall>A. A{is closed in}T \<longrightarrow> A=0" using IsClosed_def by auto
      have "\<exists>U\<in>T. \<exists>V\<in>T. 0\<subseteq>U\<and>0\<subseteq>V\<and>U\<inter>V=0" using empty_open AS(1) by auto
      with rr have "\<forall>A. A{is closed in}T \<longrightarrow> (\<forall>B. B{is closed in}T \<and> A\<inter>B=0 \<longrightarrow> (\<exists>U\<in>T. \<exists>V\<in>T. A\<subseteq>U\<and>B\<subseteq>V\<and>U\<inter>V=0))"
        by blast
      then have "T{is normal}" using IsNormal_def by auto
      with \<open>T{is T\<^sub>1}\<close> have "T{is T\<^sub>4}" using isT4_def by auto
    }
    moreover
    {
      assume "A\<approx>1"
      with AS have "T{is a topology}" and NONempty:"\<Union>T\<approx>1" using eqpoll_trans[of "\<Union>T""A""1"] by auto
      then have "\<Union>T\<lesssim>1" using eqpoll_imp_lepoll by auto
      moreover
      {
        assume "\<Union>T=0"
        then have "0\<approx>\<Union>T" by auto
        with NONempty have "0\<approx>1" using eqpoll_trans by blast
        then have "0=1" using eqpoll_0_is_0 eqpoll_sym by auto
        then have "False" by auto
      }
      then have "\<Union>T\<noteq>0" by auto
      then obtain R where "R\<in>\<Union>T" by blast
      ultimately have "\<Union>T={R}" using lepoll_1_is_sing by auto
      {
        fix x y
        assume "x{is closed in}T""y{is closed in}T" "x\<inter>y=0"
        then have "x\<subseteq>\<Union>T""y\<subseteq>\<Union>T" using IsClosed_def by auto
        then have "x=0\<or>y=0" using \<open>x\<inter>y=0\<close> \<open>\<Union>T={R}\<close> by force
        {
          assume "x=0"
          then have "x\<subseteq>0""y\<subseteq>\<Union>T" using \<open>y\<subseteq>\<Union>T\<close> by auto
          moreover
          have "0\<in>T""\<Union>T\<in>T" using AS(1) IsATopology_def empty_open by auto
          ultimately have "\<exists>U\<in>T. \<exists>V\<in>T. x\<subseteq>U\<and>y\<subseteq>V\<and>U\<inter>V=0" by auto
        }
        moreover
        {
          assume "x\<noteq>0"
          with \<open>x=0\<or>y=0\<close> have "y=0" by auto
          then have "x\<subseteq>\<Union>T""y\<subseteq>0" using \<open>x\<subseteq>\<Union>T\<close> by auto
          moreover
          have "0\<in>T""\<Union>T\<in>T" using AS(1) IsATopology_def empty_open by auto
          ultimately have "\<exists>U\<in>T. \<exists>V\<in>T. x\<subseteq>U\<and>y\<subseteq>V\<and>U\<inter>V=0" by auto
        }
        ultimately
        have "(\<exists>U\<in>T. \<exists>V\<in>T. x \<subseteq> U \<and> y \<subseteq> V \<and> U \<inter> V = 0)" by blast
      }
      then have "T{is normal}" using IsNormal_def by auto
      moreover
      {
        fix x y
        assume "x\<in>\<Union>T""y\<in>\<Union>T""x\<noteq>y"
        with \<open>\<Union>T={R}\<close> have "False" by auto
        then have "\<exists>U\<in>T. x\<in>U\<and>y\<notin>U" by auto
      }
      then have "T{is T\<^sub>1}" using isT1_def by auto
      ultimately have "T{is T\<^sub>4}" using isT4_def by auto
    }
    ultimately have "T{is T\<^sub>4}" using \<open>A\<approx>0\<or>A\<approx>1\<close> by auto
  }
  then have "\<forall>T. (T{is a topology} \<and> \<Union>T \<approx> A) \<longrightarrow> (T{is T\<^sub>4})" by auto
  then show "A {is in the spectrum of} isT4" using Spec_def by auto
qed

text\<open>If the topological properties are related, then so are the spectra.\<close>
    
lemma P_imp_Q_spec_inv:
  assumes "\<forall>T. T{is a topology} \<longrightarrow> (Q(T) \<longrightarrow> P(T))"  "A {is in the spectrum of} Q"
  shows "A {is in the spectrum of} P"
proof-
  from assms(2) have "\<forall>T. T{is a topology} \<and> \<Union>T \<approx> A \<longrightarrow> Q(T)" using Spec_def by auto
  with assms(1) have "\<forall>T. T{is a topology} \<and> \<Union>T \<approx> A \<longrightarrow> P(T)" by auto
  then show ?thesis using Spec_def by auto
qed

text\<open>Since we already now the spectrum of $T_4$; if we now the spectrum of $T_0$,
it should be easier to compute the spectrum of $T_1$, $T_2$ and $T_3$.\<close>

theorem T0_spectrum:
  shows "(A {is in the spectrum of} isT0) \<longleftrightarrow> A \<lesssim> 1"
proof
  assume "A {is in the spectrum of} isT0"
  then have reg:"\<forall>T. ((T{is a topology} \<and> \<Union>T\<approx>A) \<longrightarrow> (T {is T\<^sub>0}))" using Spec_def by auto
  {
    assume "A\<noteq>0"
    then obtain x where "x\<in>A" by auto
    then have "x\<in>\<Union>{A}" by auto
    moreover
    then have "{A} {is a filter on}\<Union>{A}" using IsFilter_def by auto
    moreover
    then have "({A}\<union>{0}) {is a topology} \<and> \<Union>({A}\<union>{0})=A" using top_of_filter by auto
    then have "({A}\<union>{0}) {is a topology} \<and> \<Union>({A}\<union>{0})\<approx>A" using eqpoll_refl by auto
    then have "({A}\<union>{0}) {is T\<^sub>0}" using reg by auto
    {
      fix y
      assume "y\<in>A""x\<noteq>y"
      with \<open>({A}\<union>{0}) {is T\<^sub>0}\<close> obtain U where "U\<in>({A}\<union>{0})" and dis:"(x \<in> U \<and> y \<notin> U) \<or> (y \<in> U \<and> x \<notin> U)" using isT0_def by auto
      then have "U=A" by auto
      with dis \<open>y\<in>A\<close> \<open>x\<in>\<Union>{A}\<close> have "False" by auto
    }
    then have "\<forall>y\<in>A. y=x" by auto
    with \<open>x\<in>\<Union>{A}\<close> have "A={x}" by blast
    then have "A\<approx>1" using singleton_eqpoll_1 by auto
  }
  moreover
  have "A=0 \<longrightarrow> A\<approx>0" by auto
  ultimately have "A\<approx>1\<or>A\<approx>0" by blast
  then show "A\<lesssim>1" using empty_lepollI eqpoll_imp_lepoll eq_lepoll_trans by auto
next
  assume "A\<lesssim>1"
  {
    fix T
    assume "T{is a topology}"
    then have "(T{is T\<^sub>4})\<longrightarrow>(T{is T\<^sub>0})" using topology0.T4_is_T3 topology0.T3_is_T2 T2_is_T1 T1_is_T0 
      topology0_def by auto
  }
  then have "\<forall>T. T{is a topology} \<longrightarrow> ((T{is T\<^sub>4})\<longrightarrow>(T{is T\<^sub>0}))" by auto
  then have "(A {is in the spectrum of} isT4) \<longrightarrow> (A {is in the spectrum of} isT0)"
    using P_imp_Q_spec_inv[of "\<lambda>T. (T{is T\<^sub>4})""\<lambda>T. T{is T\<^sub>0}"] by auto
  then show "(A {is in the spectrum of} isT0)" using T4_spectrum \<open>A\<lesssim>1\<close> by auto
qed

theorem T1_spectrum:
  shows "(A {is in the spectrum of} isT1) \<longleftrightarrow> A \<lesssim> 1"
proof-
  note T2_is_T1 topology0.T3_is_T2 topology0.T4_is_T3
  then have "(A {is in the spectrum of} isT4) \<longrightarrow> (A {is in the spectrum of} isT1)"
    using P_imp_Q_spec_inv[of "isT4""isT1"] topology0_def by auto
  moreover
  note T1_is_T0
  then have "(A {is in the spectrum of} isT1) \<longrightarrow> (A {is in the spectrum of}isT0)"
    using P_imp_Q_spec_inv[of "isT1""isT0"] by auto
  moreover
  note T0_spectrum T4_spectrum
  ultimately show ?thesis by blast
qed

theorem T2_spectrum:
  shows "(A {is in the spectrum of} isT2) \<longleftrightarrow> A \<lesssim> 1"
proof-
  note topology0.T3_is_T2 topology0.T4_is_T3
  then have "(A {is in the spectrum of} isT4) \<longrightarrow> (A {is in the spectrum of} isT2)"
    using P_imp_Q_spec_inv[of "isT4""isT2"] topology0_def by auto
  moreover
  note T2_is_T1
  then have "(A {is in the spectrum of} isT2) \<longrightarrow> (A {is in the spectrum of}isT1)"
    using P_imp_Q_spec_inv[of "isT2""isT1"] by auto
  moreover
  note T1_spectrum T4_spectrum
  ultimately show ?thesis by blast
qed

theorem T3_spectrum:
  shows "(A {is in the spectrum of} isT3) \<longleftrightarrow> A \<lesssim> 1"
proof-
  note topology0.T4_is_T3
  then have "(A {is in the spectrum of} isT4) \<longrightarrow> (A {is in the spectrum of} isT3)"
    using P_imp_Q_spec_inv[of "isT4""isT3"] topology0_def by auto
  moreover
  note topology0.T3_is_T2
  then have "(A {is in the spectrum of} isT3) \<longrightarrow> (A {is in the spectrum of}isT2)"
    using P_imp_Q_spec_inv[of "isT3""isT2"] topology0_def by auto
  moreover
  note T2_spectrum T4_spectrum
  ultimately show ?thesis by blast
qed

theorem compact_spectrum:
  shows "(A {is in the spectrum of} (\<lambda>T. (\<Union>T) {is compact in}T)) \<longleftrightarrow> Finite(A)"
proof
  assume "A {is in the spectrum of} (\<lambda>T. (\<Union>T) {is compact in}T)"
  then have reg:"\<forall>T. T{is a topology} \<and> \<Union>T\<approx>A \<longrightarrow> ((\<Union>T) {is compact in}T)" using Spec_def by auto
  have "Pow(A){is a topology} \<and> \<Union>Pow(A)=A" using Pow_is_top by auto
  then have "Pow(A){is a topology} \<and> \<Union>Pow(A)\<approx>A" using eqpoll_refl by auto
  with reg have "A{is compact in}Pow(A)" by auto
  moreover
  have "{{x}. x\<in>A}\<in>Pow(Pow(A))" by auto
  moreover
  have "\<Union>{{x}. x\<in>A}=A" by auto
  ultimately have "\<exists>N\<in>FinPow({{x}. x\<in>A}). A\<subseteq>\<Union>N" using IsCompact_def by auto
  then obtain N where "N\<in>FinPow({{x}. x\<in>A})" "A\<subseteq>\<Union>N" by auto
  then have "N\<subseteq>{{x}. x\<in>A}" "Finite(N)" "A\<subseteq>\<Union>N" using FinPow_def by auto
  {
    fix t
    assume "t\<in>{{x}. x\<in>A}"
    then obtain x where "x\<in>A""t={x}" by auto
    with \<open>A\<subseteq>\<Union>N\<close> have "x\<in>\<Union>N" by auto
    then obtain B where "B\<in>N""x\<in>B" by auto
    with \<open>N\<subseteq>{{x}. x\<in>A}\<close> have "B={x}" by auto
    with \<open>t={x}\<close>\<open>B\<in>N\<close> have "t\<in>N" by auto 
  }
  with \<open>N\<subseteq>{{x}. x\<in>A}\<close> have "N={{x}. x\<in>A}" by auto
  with \<open>Finite(N)\<close> have "Finite({{x}. x\<in>A})" by auto
  let ?B="{\<langle>x,{x}\<rangle>. x\<in>A}"
  have "?B:A\<rightarrow>{{x}. x\<in>A}" unfolding Pi_def function_def by auto
  then have "?B:bij(A,{{x}. x\<in>A})" unfolding bij_def inj_def surj_def using apply_equality by auto
  then have "A\<approx>{{x}. x\<in>A}" using eqpoll_def by auto
  with \<open>Finite({{x}. x\<in>A})\<close> show "Finite(A)" using eqpoll_imp_Finite_iff by auto
next
  assume "Finite(A)"
  {
    fix T assume "T{is a topology}" "\<Union>T\<approx>A"
    with \<open>Finite(A)\<close> have "Finite(\<Union>T)" using eqpoll_imp_Finite_iff by auto
    then have "Finite(Pow(\<Union>T))" using Finite_Pow by auto
    moreover
    have "T\<subseteq>Pow(\<Union>T)" by auto
    ultimately have "Finite(T)" using subset_Finite by auto
    {
      fix M
      assume "M\<in>Pow(T)""\<Union>T\<subseteq>\<Union>M"
      with \<open>Finite(T)\<close> have "Finite(M)" using subset_Finite by auto
      with \<open>\<Union>T\<subseteq>\<Union>M\<close> have "\<exists>N\<in>FinPow(M). \<Union>T\<subseteq>\<Union>N" using FinPow_def by auto
    }
    then have "(\<Union>T){is compact in}T" unfolding IsCompact_def by auto
  }
  then show "A {is in the spectrum of} (\<lambda>T. (\<Union>T) {is compact in}T)" using Spec_def by auto
qed

text\<open>It is, at least for some people, surprising that the spectrum of some properties cannot be completely
determined in \emph{ZF}.\<close>

theorem compactK_spectrum:
  assumes "{the axiom of}K{choice holds for subsets}(Pow(K))" "Card(K)"
  shows "(A {is in the spectrum of} (\<lambda>T. ((\<Union>T){is compact of cardinal} csucc(K){in}T))) \<longleftrightarrow> (A\<lesssim>K)"
proof
  assume "A {is in the spectrum of} (\<lambda>T. ((\<Union>T){is compact of cardinal} csucc(K){in}T))"
  then have reg:"\<forall>T. T{is a topology}\<and>\<Union>T\<approx>A \<longrightarrow> ((\<Union>T){is compact of cardinal} csucc(K){in}T)" using Spec_def by auto
  then have "A{is compact of cardinal} csucc(K) {in} Pow(A)" using Pow_is_top[of "A"] by auto
  then have "\<forall>M\<in>Pow(Pow(A)). A\<subseteq>\<Union>M \<longrightarrow> (\<exists>N\<in>Pow(M). A\<subseteq>\<Union>N \<and> N\<prec>csucc(K))" unfolding IsCompactOfCard_def by auto
  moreover
  have "{{x}. x\<in>A}\<in>Pow(Pow(A))" by auto
  moreover
  have "A=\<Union>{{x}. x\<in>A}" by auto
  ultimately have "\<exists>N\<in>Pow({{x}. x\<in>A}). A\<subseteq>\<Union>N \<and> N\<prec>csucc(K)" by auto
  then obtain N where "N\<in>Pow({{x}. x\<in>A})" "A\<subseteq>\<Union>N" "N\<prec>csucc(K)" by auto
  then have "N\<subseteq>{{x}. x\<in>A}" "N\<prec>csucc(K)" "A\<subseteq>\<Union>N" using FinPow_def by auto
  {
    fix t
    assume "t\<in>{{x}. x\<in>A}"
    then obtain x where "x\<in>A""t={x}" by auto
    with \<open>A\<subseteq>\<Union>N\<close> have "x\<in>\<Union>N" by auto
    then obtain B where "B\<in>N""x\<in>B" by auto
    with \<open>N\<subseteq>{{x}. x\<in>A}\<close> have "B={x}" by auto
    with \<open>t={x}\<close>\<open>B\<in>N\<close> have "t\<in>N" by auto 
  }
  with \<open>N\<subseteq>{{x}. x\<in>A}\<close> have "N={{x}. x\<in>A}" by auto
  let ?B="{\<langle>x,{x}\<rangle>. x\<in>A}"
  from \<open>N={{x}. x\<in>A}\<close> have "?B:A\<rightarrow> N" unfolding Pi_def function_def by auto
  with \<open>N={{x}. x\<in>A}\<close> have "?B:inj(A,N)" unfolding inj_def using apply_equality by auto
  then have "A\<lesssim>N" using lepoll_def by auto
  with \<open>N\<prec>csucc(K)\<close> have "A\<prec>csucc(K)" using lesspoll_trans1 by auto
  then show "A\<lesssim>K" using Card_less_csucc_eq_le assms(2) by auto
next
  assume "A\<lesssim>K"
  {
    fix T
    assume "T{is a topology}""\<Union>T\<approx>A"
    have "Pow(\<Union>T){is a topology}" using Pow_is_top by auto
    {
      fix B
      assume AS:"B\<in>Pow(\<Union>T)"
      then have "{{i}. i\<in>B}\<subseteq>{{i} .i\<in>\<Union>T}" by auto
      moreover
      have "B=\<Union>{{i}. i\<in>B}" by auto
      ultimately have "\<exists>S\<in>Pow({{i}. i\<in>\<Union>T}). B=\<Union>S" by auto
      then have "B\<in>{\<Union>U. U\<in>Pow({{i}. i\<in>\<Union>T})}" by auto
    }
    moreover
    {
      fix B
      assume AS:"B\<in>{\<Union>U. U\<in>Pow({{i}. i\<in>\<Union>T})}"
      then have "B\<in>Pow(\<Union>T)" by auto
    }
    ultimately
    have base:"{{x}. x\<in>\<Union>T} {is a base for}Pow(\<Union>T)" unfolding IsAbaseFor_def by auto
    let ?f="{\<langle>i,{i}\<rangle>. i\<in>\<Union>T}"
    have f:"?f:\<Union>T\<rightarrow> {{x}. x\<in>\<Union>T}" using Pi_def function_def by auto
    moreover
    {
      fix w x
      assume as:"w\<in>\<Union>T""x\<in>\<Union>T""?f`w=?f`x"
      with f have "?f`w={w}" "?f`x={x}" using apply_equality by auto
      with as(3) have "w=x" by auto
    }
    with f have "?f:inj(\<Union>T,{{x}. x\<in>\<Union>T})" unfolding inj_def by auto
    moreover
    {
      fix xa
      assume "xa\<in>{{x}. x\<in>\<Union>T}"
      then obtain x where "x\<in>\<Union>T""xa={x}" by auto
      with f have "?f`x=xa" using apply_equality by auto
      with \<open>x\<in>\<Union>T\<close> have "\<exists>x\<in>\<Union>T. ?f`x=xa" by auto
    }
    then have "\<forall>xa\<in>{{x}. x\<in>\<Union>T}. \<exists>x\<in>\<Union>T. ?f`x=xa" by blast
    ultimately have "?f:bij(\<Union>T,{{x}. x\<in>\<Union>T})" unfolding bij_def surj_def by auto
    then have "\<Union>T\<approx>{{x}. x\<in>\<Union>T}" using eqpoll_def by auto
    then have "{{x}. x\<in>\<Union>T}\<approx>\<Union>T" using eqpoll_sym by auto
    with \<open>\<Union>T\<approx>A\<close> have "{{x}. x\<in>\<Union>T}\<approx>A" using eqpoll_trans by blast
    then have "{{x}. x\<in>\<Union>T}\<lesssim>A" using eqpoll_imp_lepoll by auto
    with \<open>A\<lesssim>K\<close> have "{{x}. x\<in>\<Union>T}\<lesssim>K" using lepoll_trans by blast
    then have "{{x}. x\<in>\<Union>T}\<prec>csucc(K)" using assms(2) Card_less_csucc_eq_le by auto
    with base have "Pow(\<Union>T) {is of second type of cardinal}csucc(K)" unfolding IsSecondOfCard_def by auto
    moreover
    have "\<Union>Pow(\<Union>T)=\<Union>T" by auto
    with calculation assms(1) \<open>Pow(\<Union>T){is a topology}\<close> have "(\<Union>T) {is compact of cardinal}csucc(K){in}Pow(\<Union>T)" 
      using compact_of_cardinal_Q[of "K""Pow(\<Union>T)"] by auto
    moreover
    have "T\<subseteq>Pow(\<Union>T)" by auto
    ultimately have "(\<Union>T) {is compact of cardinal}csucc(K){in}T" using compact_coarser by auto
  }
  then show "A {is in the spectrum of} (\<lambda>T. ((\<Union>T){is compact of cardinal}csucc(K) {in}T))" using Spec_def by auto
qed

theorem compactK_spectrum_reverse:
  assumes "\<forall>A. (A {is in the spectrum of} (\<lambda>T. ((\<Union>T){is compact of cardinal} csucc(K){in}T))) \<longleftrightarrow> (A\<lesssim>K)" "InfCard(K)"
  shows "{the axiom of}K{choice holds for subsets}(Pow(K))"
proof-
  have "K\<lesssim>K" using lepoll_refl by auto
  then have "K {is in the spectrum of} (\<lambda>T. ((\<Union>T){is compact of cardinal} csucc(K){in}T))" using assms(1) by auto
  moreover
  have "Pow(K){is a topology}" using Pow_is_top by auto
  moreover
  have "\<Union>Pow(K)=K" by auto
  then have "\<Union>Pow(K)\<approx>K" using eqpoll_refl by auto
  ultimately
  have "K {is compact of cardinal} csucc(K){in}Pow(K)" using Spec_def by auto
  then show ?thesis using Q_disc_comp_csuccQ_eq_Q_choice_csuccQ assms(2) by auto
qed

text\<open>This last theorem states that if one of the forms of the axiom of choice related to this
compactness property fails, then the spectrum will be different. Notice that even for Lindelöf
spaces that will happend.\<close>

text\<open>The spectrum gives us the posibility to define what an anti-property means.
A space is anti-\<open>P\<close> if the only subspaces which have the property
are the ones in the spectrum of \<open>P\<close>. This concept tries to put together
spaces that are completely opposite to spaces where \<open>P(T)\<close>.\<close>

definition
  antiProperty ("_{is anti-}_" 50)
  where "T{is anti-}P \<equiv> \<forall>A\<in>Pow(\<Union>T). P(T{restricted to}A) \<longrightarrow> (A {is in the spectrum of} P)"

abbreviation
  "ANTI(P) \<equiv> \<lambda>T. (T{is anti-}P)"

text\<open>A first, very simple, but very useful result is the following: when the properties
are related and the spectra are equal, then the anti-properties are related in the oposite direction.\<close>

theorem (in topology0) eq_spect_rev_imp_anti:
  assumes "\<forall>T. T{is a topology} \<longrightarrow> P(T) \<longrightarrow> Q(T)" "\<forall>A. (A{is in the spectrum of}Q) \<longrightarrow> (A{is in the spectrum of}P)"
    and "T{is anti-}Q"
  shows "T{is anti-}P"
proof-
  {
    fix A
    assume "A\<in>Pow(\<Union>T)""P(T{restricted to}A)"
    with assms(1) have "Q(T{restricted to}A)" using Top_1_L4 by auto
    with assms(3) \<open>A\<in>Pow(\<Union>T)\<close> have "A{is in the spectrum of}Q" using antiProperty_def by auto
    with assms(2) have "A{is in the spectrum of}P" by auto
  }
  then show ?thesis using antiProperty_def by auto
qed

text\<open>If a space can be \<open>P(T)\<and>Q(T)\<close> only in case the underlying set is in the
spectrum of \<open>P\<close>; then \<open>Q(T)\<longrightarrow>ANTI(P,T)\<close> when \<open>Q\<close> is hereditary.\<close>

theorem Q_P_imp_Spec:
  assumes "\<forall>T. ((T{is a topology}\<and>P(T)\<and>Q(T))\<longrightarrow> ((\<Union>T){is in the spectrum of}P))"
    and "Q{is hereditary}"
  shows "\<forall>T. T{is a topology} \<longrightarrow> (Q(T)\<longrightarrow>(T{is anti-}P))"
proof
  fix T
  {
    assume "T{is a topology}"
    {
      assume "Q(T)"
      {
        assume "\<not>(T{is anti-}P)"
        then obtain A where "A\<in>Pow(\<Union>T)" "P(T{restricted to}A)""\<not>(A{is in the spectrum of}P)"
          unfolding antiProperty_def by auto
        from \<open>Q(T)\<close>\<open>T{is a topology}\<close>\<open>A\<in>Pow(\<Union>T)\<close> assms(2) have "Q(T{restricted to}A)" 
          unfolding IsHer_def by auto
        moreover
        note \<open>P(T{restricted to}A)\<close> assms(1)
        moreover
        from \<open>T{is a topology}\<close> have "(T{restricted to}A){is a topology}" using topology0.Top_1_L4
          topology0_def by auto
        moreover
        from \<open>A\<in>Pow(\<Union>T)\<close> have "\<Union>(T{restricted to}A)=A" unfolding RestrictedTo_def by auto
        ultimately have "A{is in the spectrum of}P" by auto
        with \<open>\<not>(A{is in the spectrum of}P)\<close> have "False" by auto
      }
      then have "T{is anti-}P" by auto
    }
    then have "Q(T)\<longrightarrow>(T{is anti-}P)" by auto
  }
  then show "(T {is a topology}) \<longrightarrow> (Q(T) \<longrightarrow> (T{is anti-}P))" by auto
qed

text\<open>If a topologycal space has an hereditary property, then it has its double-anti property.\<close>  

theorem (in topology0)her_P_imp_anti2P:
  assumes "P{is hereditary}" "P(T)"
  shows "T{is anti-}ANTI(P)"
proof-
  {
    assume "\<not>(T{is anti-}ANTI(P))"
    then have "\<exists>A\<in>Pow(\<Union>T). ((T{restricted to}A){is anti-}P)\<and>\<not>(A{is in the spectrum of}ANTI(P))"
      unfolding antiProperty_def[of _ "ANTI(P)"] by auto
    then obtain A where A_def:"A\<in>Pow(\<Union>T)""\<not>(A{is in the spectrum of}ANTI(P))""(T{restricted to}A){is anti-}P"
      by auto
    from \<open>A\<in>Pow(\<Union>T)\<close> have tot:"\<Union>(T{restricted to}A)=A" unfolding RestrictedTo_def by auto
    from A_def have reg:"\<forall>B\<in>Pow(\<Union>(T{restricted to}A)). P((T{restricted to}A){restricted to}B) \<longrightarrow> (B{is in the spectrum of}P)"
      unfolding antiProperty_def by auto
    have "\<forall>B\<in>Pow(A). (T{restricted to}A){restricted to}B=T{restricted to}B" using subspace_of_subspace \<open>A\<in>Pow(\<Union>T)\<close> by auto
    then have "\<forall>B\<in>Pow(A). P(T{restricted to}B) \<longrightarrow> (B{is in the spectrum of}P)" using reg tot
      by force
    moreover
    have "\<forall>B\<in>Pow(A). P(T{restricted to}B)" using assms \<open>A\<in>Pow(\<Union>T)\<close> unfolding IsHer_def using topSpaceAssum by blast
    ultimately have reg2:"\<forall>B\<in>Pow(A). (B{is in the spectrum of}P)" by auto
    from \<open>\<not>(A{is in the spectrum of}ANTI(P))\<close> have "\<exists>T. T{is a topology} \<and> \<Union>T\<approx>A \<and> \<not>(T{is anti-}P)"
      unfolding Spec_def by auto
    then obtain S where "S{is a topology}" "\<Union>S\<approx>A" "\<not>(S{is anti-}P)" by auto
    from \<open>\<not>(S{is anti-}P)\<close> have "\<exists>B\<in>Pow(\<Union>S). P(S{restricted to}B) \<and> \<not>(B{is in the spectrum of}P)" unfolding antiProperty_def by auto
    then obtain B where B_def:"\<not>(B{is in the spectrum of}P)" "B\<in>Pow(\<Union>S)" by auto
    then have "B\<lesssim>\<Union>S" using subset_imp_lepoll by auto
    with \<open>\<Union>S\<approx>A\<close> have "B\<lesssim>A" using lepoll_eq_trans by auto
    then obtain f where "f\<in>inj(B,A)" unfolding lepoll_def by auto
    then have "f\<in>bij(B,range(f))" using inj_bij_range by auto
    then have "B\<approx>range(f)" unfolding eqpoll_def by auto
    with B_def(1) have "\<not>(range(f){is in the spectrum of}P)" using eqpoll_iff_spec by auto
    moreover
    with \<open>f\<in>inj(B,A)\<close> have "range(f)\<subseteq>A" unfolding inj_def Pi_def by auto
    with reg2 have "range(f){is in the spectrum of}P" by auto
    ultimately have "False" by auto
  }
  then show ?thesis by auto
qed
  
text\<open>The anti-properties are always hereditary\<close>

theorem anti_here:
  shows "ANTI(P){is hereditary}"
proof-
  {
    fix T
    assume "T {is a topology}""ANTI(P,T)"
    {
      fix A
      assume "A\<in>Pow(\<Union>T)"
      then have "\<Union>(T{restricted to}A)=A" unfolding RestrictedTo_def by auto
      moreover
      {
        fix B
        assume "B\<in>Pow(A)""P((T{restricted to}A){restricted to}B)"
        with \<open>A\<in>Pow(\<Union>T)\<close> have "B\<in>Pow(\<Union>T)""P(T{restricted to}B)" using subspace_of_subspace by auto
        with \<open>ANTI(P,T)\<close> have "B{is in the spectrum of}P" unfolding antiProperty_def by auto
      }
      ultimately have "\<forall>B\<in>Pow(\<Union>(T{restricted to}A)). (P((T{restricted to}A){restricted to}B)) \<longrightarrow> (B{is in the spectrum of}P)"
        by auto
      then have "ANTI(P,(T{restricted to}A))" unfolding antiProperty_def by auto
    }
    then have "\<forall>A\<in>Pow(\<Union>T). ANTI(P,(T{restricted to}A))" by auto
  }
  then show ?thesis using IsHer_def by auto
qed

corollary (in topology0) anti_imp_anti3:
  assumes "T{is anti-}P"
  shows "T{is anti-}ANTI(ANTI(P))"
  using anti_here her_P_imp_anti2P assms by auto

text\<open>In the article \cite{ReVa80}, we can find some results on anti-properties.\<close>

theorem (in topology0) anti_T0:
  shows "(T{is anti-}isT0) \<longleftrightarrow> T={0,\<Union>T}"
proof
  assume "T={0,\<Union>T}"
  {
    fix A
    assume "A\<in>Pow(\<Union>T)""(T{restricted to}A) {is T\<^sub>0}"
    {
      fix B
      assume "B\<in>T{restricted to}A"
      then obtain S where "S\<in>T" and "B=A\<inter>S" unfolding RestrictedTo_def by auto
      with \<open>T={0,\<Union>T}\<close> have "S\<in>{0,\<Union>T}" by auto
      then have "S=0\<or>S=\<Union>T" by auto
      with \<open>B=A\<inter>S\<close>\<open>A\<in>Pow(\<Union>T)\<close> have "B=0\<or>B=A" by auto
    }
    moreover
    {
      have "0\<in>{0,\<Union>T}" "\<Union>T\<in>{0,\<Union>T}" by auto
      with \<open>T={0,\<Union>T}\<close> have "0\<in>T""(\<Union>T)\<in>T" by auto
      then have "A\<inter>0\<in>(T{restricted to}A)" "A\<inter>(\<Union>T)\<in>(T{restricted to}A)" using RestrictedTo_def by auto
      moreover
      from \<open>A\<in>Pow(\<Union>T)\<close> have "A\<inter>(\<Union>T)=A" by auto
      ultimately have "0\<in>(T{restricted to}A)" "A\<in>(T{restricted to}A)" by auto
    }
    ultimately have "(T{restricted to}A)={0,A}" by auto
    with \<open>(T{restricted to}A) {is T\<^sub>0}\<close> have "{0,A} {is T\<^sub>0}" by auto
    {
      assume "A\<noteq>0"
      then obtain x where "x\<in>A" by blast
      {
        fix y
        assume "y\<in>A""x\<noteq>y"
        with \<open>{0,A} {is T\<^sub>0}\<close> obtain U where "U\<in>{0,A}" and dis:"(x \<in> U \<and> y \<notin> U) \<or> (y \<in> U \<and> x \<notin> U)" using isT0_def by auto
        then have "U=A" by auto
        with dis \<open>y\<in>A\<close> \<open>x\<in>A\<close> have "False" by auto
      }
      then have "\<forall>y\<in>A. y=x" by auto
      with \<open>x\<in>A\<close> have "A={x}" by blast
      then have "A\<approx>1" using singleton_eqpoll_1 by auto
      then have "A\<lesssim>1" using eqpoll_imp_lepoll by auto
      then have "A{is in the spectrum of}isT0" using T0_spectrum by auto   
    }
    moreover
    {
      assume "A=0"
      then have "A\<approx>0" by auto
      then have "A\<lesssim>1" using empty_lepollI eq_lepoll_trans by auto
      then have "A{is in the spectrum of}isT0" using T0_spectrum by auto
    }
    ultimately have "A{is in the spectrum of}isT0" by auto
  }
  then show "T{is anti-}isT0" using antiProperty_def by auto
next
  assume "T{is anti-}isT0"
  then have "\<forall>A\<in>Pow(\<Union>T). (T{restricted to}A){is T\<^sub>0} \<longrightarrow> (A{is in the spectrum of}isT0)" using antiProperty_def by auto
  then have reg:"\<forall>A\<in>Pow(\<Union>T). (T{restricted to}A){is T\<^sub>0} \<longrightarrow> (A\<lesssim>1)" using T0_spectrum by auto
  {
    assume "\<exists>A\<in>T. A\<noteq>0\<and> A\<noteq>\<Union>T"
    then obtain A where "A\<in>T""A\<noteq>0""A\<noteq>\<Union>T" by auto
    then obtain x y where "x\<in>A" "y\<in>\<Union>T-A" by blast
    with \<open>A\<in>T\<close> have s:"{x,y}\<in>Pow(\<Union>T)" "x\<noteq>y" by auto
    note s
    moreover
    {
      fix b1 b2
      assume "b1\<in>\<Union>(T{restricted to}{x,y})""b2\<in>\<Union>(T{restricted to}{x,y})""b1\<noteq>b2"
      moreover
      from s have "\<Union>(T{restricted to}{x,y})={x,y}" unfolding RestrictedTo_def by auto
      ultimately have "(b1=x\<and>b2=y)\<or>(b1=y\<and>b2=x)" by auto
      with \<open>x\<noteq>y\<close> have "(b1\<in>{x}\<and>b2\<notin>{x}) \<or> (b2\<in>{x}\<and>b1\<notin>{x})" by auto
      moreover
      from \<open>y\<in>\<Union>T-A\<close>\<open>x\<in>A\<close> have "{x}={x,y}\<inter>A" by auto
      with \<open>A\<in>T\<close> have "{x}\<in>(T{restricted to}{x,y})" unfolding RestrictedTo_def by auto
      ultimately have "\<exists>U\<in>(T{restricted to}{x,y}). (b1\<in>U\<and>b2\<notin>U) \<or> (b2\<in>U\<and>b1\<notin>U)" by auto
    }
    then have "(T{restricted to}{x,y}){is T\<^sub>0}" using isT0_def by auto
    ultimately have "{x,y}\<lesssim>1" using reg by auto
    moreover
    have "x\<in>{x,y}" by auto
    ultimately have "{x,y}={x}" using lepoll_1_is_sing[of "{x,y}""x"] by auto
    moreover
    have "y\<in>{x,y}" by auto
    ultimately have "y\<in>{x}" by auto
    then have "y=x" by auto
    with \<open>x\<noteq>y\<close> have "False" by auto
  }
  then have "T\<subseteq>{0,\<Union>T}" by auto
  moreover
  from topSpaceAssum have "0\<in>T""\<Union>T\<in>T" using IsATopology_def empty_open by auto
  ultimately show "T={0,\<Union>T}" by auto
qed

lemma indiscrete_spectrum:
  shows "(A {is in the spectrum of}(\<lambda>T. T={0,\<Union>T})) \<longleftrightarrow> A\<lesssim>1"
proof
  assume "(A {is in the spectrum of}(\<lambda>T. T={0,\<Union>T}))"
  then have reg:"\<forall>T. ((T{is a topology} \<and> \<Union>T\<approx>A) \<longrightarrow> T ={0,\<Union>T})" using Spec_def by auto
  moreover
  have "\<Union>Pow(A)=A" by auto
  then have "\<Union>Pow(A)\<approx>A" by auto
  moreover
  have "Pow(A) {is a topology}" using Pow_is_top by auto
  ultimately have P:"Pow(A)={0,A}" by auto
  {
    assume "A\<noteq>0"
    then obtain x where "x\<in>A" by blast
    then have "{x}\<in>Pow(A)" by auto
    with P have "{x}=A" by auto
    then have "A\<approx>1" using singleton_eqpoll_1 by auto
    then have "A\<lesssim>1" using eqpoll_imp_lepoll by auto
  }
  moreover
  {
    assume "A=0"
    then have "A\<approx>0" by auto
    then have "A\<lesssim>1" using empty_lepollI eq_lepoll_trans by auto
  }
  ultimately show "A\<lesssim>1" by auto
next
  assume "A\<lesssim>1"
  {
    fix T
    assume "T{is a topology}""\<Union>T\<approx>A"
    {
      assume "A=0"
      with \<open>\<Union>T\<approx>A\<close> have "\<Union>T\<approx>0" by auto
      then have "\<Union>T=0" using eqpoll_0_is_0 by auto
      then have "T\<subseteq>{0}" by auto
      with \<open>T{is a topology}\<close> have "T={0}" using empty_open by auto
      then have "T={0,\<Union>T}" by auto
    }
    moreover
    {
      assume "A\<noteq>0"
      then obtain E where "E\<in>A" by blast
      with \<open>A\<lesssim>1\<close> have "A={E}" using lepoll_1_is_sing by auto
      then have "A\<approx>1" using singleton_eqpoll_1 by auto
      with \<open>\<Union>T\<approx>A\<close> have NONempty:"\<Union>T\<approx>1" using eqpoll_trans by blast
      then have "\<Union>T\<lesssim>1" using eqpoll_imp_lepoll by auto
      moreover
      {
        assume "\<Union>T=0"
        then have "0\<approx>\<Union>T" by auto
        with NONempty have "0\<approx>1" using eqpoll_trans by blast
        then have "0=1" using eqpoll_0_is_0 eqpoll_sym by auto
        then have "False" by auto
      }
      then have "\<Union>T\<noteq>0" by auto
      then obtain R where "R\<in>\<Union>T" by blast
      ultimately have "\<Union>T={R}" using lepoll_1_is_sing by auto
      moreover
      have "T\<subseteq>Pow(\<Union>T)" by auto
      ultimately have "T\<subseteq>Pow({R})" by auto
      then have "T\<subseteq>{0,{R}}" by blast
      moreover
      with \<open>T{is a topology}\<close> have "0\<in>T""\<Union>T\<in>T" using IsATopology_def by auto
      moreover
      note \<open>\<Union>T={R}\<close>
      ultimately have "T={0,\<Union>T}" by auto
    }
    ultimately have "T={0,\<Union>T}" by auto
  }
  then show "A {is in the spectrum of}(\<lambda>T. T={0,\<Union>T})" using Spec_def by auto
qed

theorem (in topology0) anti_indiscrete:
  shows "(T{is anti-}(\<lambda>T. T={0,\<Union>T})) \<longleftrightarrow> T{is T\<^sub>0}"
proof
  assume "T{is T\<^sub>0}"
  {
    fix A
    assume "A\<in>Pow(\<Union>T)""T{restricted to}A={0,\<Union>(T{restricted to}A)}"
    then have un:"\<Union>(T{restricted to}A)=A" "T{restricted to}A={0,A}" using RestrictedTo_def by auto
    from \<open>T{is T\<^sub>0}\<close>\<open>A\<in>Pow(\<Union>T)\<close> have "(T{restricted to}A){is T\<^sub>0}" using T0_here by auto
    {
      assume "A=0"
      then have "A\<approx>0" by auto
      then have "A\<lesssim>1" using empty_lepollI eq_lepoll_trans by auto
    }
    moreover
    {
      assume "A\<noteq>0"
      then obtain E where "E\<in>A" by blast
      {
        fix y
        assume "y\<in>A""y\<noteq>E"
        with \<open>E\<in>A\<close> un have "y\<in>\<Union>(T{restricted to}A)""E\<in>\<Union>(T{restricted to}A)" by auto
        with \<open>(T{restricted to}A){is T\<^sub>0}\<close>\<open>y\<noteq>E\<close> have "\<exists>U\<in>(T{restricted to}A). (E\<in>U\<and>y\<notin>U)\<or>(E\<notin>U\<and>y\<in>U)"
          unfolding isT0_def by blast
        then obtain U where "U\<in>(T{restricted to}A)" "(E\<in>U\<and>y\<notin>U)\<or>(E\<notin>U\<and>y\<in>U)" by auto
        with \<open>T{restricted to}A={0,A}\<close> have "U=0\<or>U=A" by auto
        with \<open>(E\<in>U\<and>y\<notin>U)\<or>(E\<notin>U\<and>y\<in>U)\<close>\<open>y\<in>A\<close>\<open>E\<in>A\<close> have "False" by auto
      }
      then have "\<forall>y\<in>A. y=E" by auto
      with \<open>E\<in>A\<close> have "A={E}" by blast
      then have "A\<approx>1" using singleton_eqpoll_1 by auto
      then have "A\<lesssim>1" using eqpoll_imp_lepoll by auto
    }
    ultimately have "A\<lesssim>1" by auto
    then have "A{is in the spectrum of}(\<lambda>T. T={0,\<Union>T})" using indiscrete_spectrum by auto
  }
  then show "T{is anti-}(\<lambda>T. T={0,\<Union>T})" unfolding antiProperty_def by auto
next
  assume "T{is anti-}(\<lambda>T. T={0,\<Union>T})"
  then have "\<forall>A\<in>Pow(\<Union>T). (T{restricted to}A)={0,\<Union>(T{restricted to}A)} \<longrightarrow> (A {is in the spectrum of} (\<lambda>T. T={0,\<Union>T}))" using antiProperty_def by auto
  then have "\<forall>A\<in>Pow(\<Union>T). (T{restricted to}A)={0,\<Union>(T{restricted to}A)} \<longrightarrow> A\<lesssim>1" using indiscrete_spectrum by auto
  moreover
  have "\<forall>A\<in>Pow(\<Union>T). \<Union>(T{restricted to}A)=A" unfolding RestrictedTo_def by auto
  ultimately have reg:"\<forall>A\<in>Pow(\<Union>T). (T{restricted to}A)={0,A} \<longrightarrow> A\<lesssim>1" by auto
  {
    fix x y
    assume "x\<in>\<Union>T""y\<in>\<Union>T""x\<noteq>y"
    {
      assume "\<forall>U\<in>T. (x\<in>U\<and>y\<in>U)\<or>(x\<notin>U\<and>y\<notin>U)"
      then have "T{restricted to}{x,y}\<subseteq>{0,{x,y}}" unfolding RestrictedTo_def by auto
      moreover
      from \<open>x\<in>\<Union>T\<close>\<open>y\<in>\<Union>T\<close> have emp:"0\<in>T""{x,y}\<inter>0=0" and tot: "{x,y}={x,y}\<inter>\<Union>T" "\<Union>T\<in>T" using topSpaceAssum empty_open IsATopology_def by auto
      from emp have "0\<in>T{restricted to}{x,y}" unfolding RestrictedTo_def by auto
      moreover
      from tot have "{x,y}\<in>T{restricted to}{x,y}" unfolding RestrictedTo_def by auto
      ultimately have "T{restricted to}{x,y}={0,{x,y}}" by auto
      with reg \<open>x\<in>\<Union>T\<close>\<open>y\<in>\<Union>T\<close> have "{x,y}\<lesssim>1" by auto
      moreover
      have "x\<in>{x,y}" by auto
      ultimately have "{x,y}={x}" using lepoll_1_is_sing[of "{x,y}""x"] by auto
      moreover
      have "y\<in>{x,y}" by auto
      ultimately have "y\<in>{x}" by auto
      then have "y=x" by auto
      then have "False" using \<open>x\<noteq>y\<close> by auto
    }
    then have "\<exists>U\<in>T. (x\<notin>U\<or>y\<notin>U)\<and>(x\<in>U\<or>y\<in>U)" by auto
    then have "\<exists>U\<in>T. (x\<in>U\<and>y\<notin>U)\<or>(x\<notin>U\<and>y\<in>U)" by auto
  }
  then have "\<forall>x y. x\<in>\<Union>T\<and>y\<in>\<Union>T\<and> x\<noteq>y \<longrightarrow> (\<exists>U\<in>T. (x\<in>U\<and>y\<notin>U)\<or>(y\<in>U\<and>x\<notin>U))" by auto
  then show "T {is T\<^sub>0}" using isT0_def by auto
qed

text\<open>The conclusion is that being $T_0$ is just the opposite to being indiscrete.\<close>

text\<open>Next, let's compute the anti-$T_i$ for $i=1,\ 2,\ 3$ or $4$. Surprisingly, 
they are all the same. Meaning, that the total negation of $T_1$ is enough
to negate all of these axioms.\<close>

theorem anti_T1:
  shows "(T{is anti-}isT1) \<longleftrightarrow> (IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V}))"
proof
  assume "T{is anti-}isT1"
  let ?r="{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V}"
  have "antisym(?r)" unfolding antisym_def by auto
  moreover
  have "trans(?r)" unfolding trans_def by auto
  moreover
  {
    fix A B
    assume "A\<in>T""B\<in>T"
    {
      assume "\<not>(A\<subseteq>B\<or>B\<subseteq>A)"
      then have "A-B\<noteq>0""B-A\<noteq>0" by auto
      then obtain x y where "x\<in>A""x\<notin>B""y\<in>B""y\<notin>A" "x\<noteq>y" by blast
      then have "{x,y}\<inter>A={x}""{x,y}\<inter>B={y}" by auto
      moreover
      from \<open>A\<in>T\<close>\<open>B\<in>T\<close> have "{x,y}\<inter>A\<in>T{restricted to}{x,y}""{x,y}\<inter>B\<in>T{restricted to}{x,y}" unfolding
        RestrictedTo_def by auto
      ultimately have open_set:"{x}\<in>T{restricted to}{x,y}""{y}\<in>T{restricted to}{x,y}" by auto
      have "x\<in>\<Union>T""y\<in>\<Union>T" using \<open>A\<in>T\<close>\<open>B\<in>T\<close>\<open>x\<in>A\<close>\<open>y\<in>B\<close> by auto
      then have sub:"{x,y}\<in>Pow(\<Union>T)" by auto
      then have tot:"\<Union>(T{restricted to}{x,y})={x,y}" unfolding RestrictedTo_def by auto
      {
        fix s t
        assume "s\<in>\<Union>(T{restricted to}{x,y})""t\<in>\<Union>(T{restricted to}{x,y})""s\<noteq>t"
        with tot have "s\<in>{x,y}""t\<in>{x,y}""s\<noteq>t" by auto
        then have "(s=x\<and>t=y)\<or>(s=y\<and>t=x)" by auto
        with open_set have "\<exists>U\<in>(T{restricted to}{x,y}). s\<in>U\<and>t\<notin>U" using \<open>x\<noteq>y\<close> by auto
      }
      then have "(T{restricted to}{x,y}){is T\<^sub>1}" unfolding isT1_def by auto
      with sub \<open>T{is anti-}isT1\<close> tot have "{x,y} {is in the spectrum of}isT1" using antiProperty_def
        by auto
      then have "{x,y}\<lesssim>1" using T1_spectrum by auto
      moreover
      have "x\<in>{x,y}" by auto
      ultimately have "{x}={x,y}" using lepoll_1_is_sing[of "{x,y}""x"] by auto
      moreover
      have "y\<in>{x,y}" by auto
      ultimately
      have "y\<in>{x}" by auto
      then have "x=y" by auto
      then have "False" using \<open>x\<in>A\<close>\<open>y\<notin>A\<close> by auto
    }
    then have "A\<subseteq>B\<or>B\<subseteq>A" by auto
  }
  then have "?r {is total on}T" using IsTotal_def by auto
  ultimately
  show "IsLinOrder(T,?r)" using IsLinOrder_def by auto
next
  assume "IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V})"
  then have ordTot:"\<forall>S\<in>T. \<forall>B\<in>T. S\<subseteq>B\<or>B\<subseteq>S" unfolding IsLinOrder_def IsTotal_def by auto
  {
    fix A
    assume "A\<in>Pow(\<Union>T)" and T1:"(T{restricted to}A) {is T\<^sub>1}"
    then have tot:"\<Union>(T{restricted to}A)=A" unfolding RestrictedTo_def by auto
    {
      fix U V
      assume "U\<in>T{restricted to}A""V\<in>T{restricted to}A"
      then obtain AU AV where "AU\<in>T""AV\<in>T""U=A\<inter>AU""V=A\<inter>AV" unfolding RestrictedTo_def by auto
      with ordTot have "U\<subseteq>V\<or>V\<subseteq>U" by auto
    }
    then have ordTotSub:"\<forall>S\<in>T{restricted to}A. \<forall>B\<in>T{restricted to}A. S\<subseteq>B\<or>B\<subseteq>S" by auto
    {
      assume "A=0"
      then have "A\<approx>0" by auto
      moreover
      have "0\<lesssim>1" using empty_lepollI by auto
      ultimately have "A\<lesssim>1" using eq_lepoll_trans by auto
      then have "A{is in the spectrum of}isT1" using T1_spectrum by auto
    }
    moreover
    {
      assume "A\<noteq>0"
      then obtain t where "t\<in>A" by blast
      {
        fix y
        assume "y\<in>A""y\<noteq>t"
        with \<open>t\<in>A\<close> tot T1 obtain U where "U\<in>(T{restricted to}A)""y\<in>U""t\<notin>U" unfolding isT1_def
          by auto
        from \<open>y\<noteq>t\<close> have "t\<noteq>y" by auto
        with \<open>y\<in>A\<close>\<open>t\<in>A\<close> tot T1 obtain V where "V\<in>(T{restricted to}A)""t\<in>V""y\<notin>V" unfolding isT1_def
          by auto
        with \<open>y\<in>U\<close>\<open>t\<notin>U\<close> have "\<not>(U\<subseteq>V\<or>V\<subseteq>U)" by auto
        with ordTotSub \<open>U\<in>(T{restricted to}A)\<close>\<open>V\<in>(T{restricted to}A)\<close> have "False" by auto
      }
      then have "\<forall>y\<in>A. y=t" by auto
      with \<open>t\<in>A\<close> have "A={t}" by blast
      then have "A\<approx>1" using singleton_eqpoll_1 by auto
      then have "A\<lesssim>1" using eqpoll_imp_lepoll by auto
      then have "A{is in the spectrum of}isT1" using T1_spectrum by auto
    }
    ultimately
    have "A{is in the spectrum of}isT1" by auto
  }
  then show "T{is anti-}isT1" using antiProperty_def by auto
qed

corollary linordtop_here:
  shows "(\<lambda>T. IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V})){is hereditary}"
  using anti_T1 anti_here[of "isT1"] by auto

theorem (in topology0) anti_T4:
  shows "(T{is anti-}isT4) \<longleftrightarrow> (IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V}))"
proof
  assume "T{is anti-}isT4"
  let ?r="{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V}"
  have "antisym(?r)" unfolding antisym_def by auto
  moreover
  have "trans(?r)" unfolding trans_def by auto
  moreover
  {
    fix A B
    assume "A\<in>T""B\<in>T"
    {
      assume "\<not>(A\<subseteq>B\<or>B\<subseteq>A)"
      then have "A-B\<noteq>0""B-A\<noteq>0" by auto
      then obtain x y where "x\<in>A""x\<notin>B""y\<in>B""y\<notin>A" "x\<noteq>y" by blast
      then have "{x,y}\<inter>A={x}""{x,y}\<inter>B={y}" by auto
      moreover
      from \<open>A\<in>T\<close>\<open>B\<in>T\<close> have "{x,y}\<inter>A\<in>T{restricted to}{x,y}""{x,y}\<inter>B\<in>T{restricted to}{x,y}" unfolding
        RestrictedTo_def by auto
      ultimately have open_set:"{x}\<in>T{restricted to}{x,y}""{y}\<in>T{restricted to}{x,y}" by auto
      have "x\<in>\<Union>T""y\<in>\<Union>T" using \<open>A\<in>T\<close>\<open>B\<in>T\<close>\<open>x\<in>A\<close>\<open>y\<in>B\<close> by auto
      then have sub:"{x,y}\<in>Pow(\<Union>T)" by auto
      then have tot:"\<Union>(T{restricted to}{x,y})={x,y}" unfolding RestrictedTo_def by auto
      {
        fix s t
        assume "s\<in>\<Union>(T{restricted to}{x,y})""t\<in>\<Union>(T{restricted to}{x,y})""s\<noteq>t"
        with tot have "s\<in>{x,y}""t\<in>{x,y}""s\<noteq>t" by auto
        then have "(s=x\<and>t=y)\<or>(s=y\<and>t=x)" by auto
        with open_set have "\<exists>U\<in>(T{restricted to}{x,y}). s\<in>U\<and>t\<notin>U" using \<open>x\<noteq>y\<close> by auto
      }
      then have "(T{restricted to}{x,y}){is T\<^sub>1}" unfolding isT1_def by auto
      moreover
      {
        fix s
        assume AS:"s{is closed in}(T{restricted to}{x,y})"
        {
          fix t
          assume AS2:"t{is closed in}(T{restricted to}{x,y})""s\<inter>t=0"
          have "(T{restricted to}{x,y}){is a topology}" using Top_1_L4 by auto
          with tot have "0\<in>(T{restricted to}{x,y})""{x,y}\<in>(T{restricted to}{x,y})" using empty_open
            union_open[where \<A>="T{restricted to}{x,y}"] by auto
          moreover
          note open_set
          moreover
          have "T{restricted to}{x,y}\<subseteq>Pow(\<Union>(T{restricted to}{x,y}))" by blast
          with tot have "T{restricted to}{x,y}\<subseteq>Pow({x,y})" by auto
          ultimately have "T{restricted to}{x,y}={0,{x},{y},{x,y}}" by blast
          moreover have "{0,{x},{y},{x,y}}=Pow({x,y})" by blast
          ultimately have P:"T{restricted to}{x,y}=Pow({x,y})" by simp
          with tot have "{A\<in>Pow({x,y}). A{is closed in}(T{restricted to}{x,y})}={A \<in> Pow({x, y}) . A \<subseteq> {x, y} \<and> {x, y} - A \<in> Pow({x, y})}" using IsClosed_def by simp
          with P have S:"{A\<in>Pow({x,y}). A{is closed in}(T{restricted to}{x,y})}=T{restricted to}{x,y}" by auto
          from AS AS2(1) have "s\<in>Pow({x,y})" "t\<in>Pow({x,y})" using IsClosed_def tot by auto
          moreover
          note AS2(1) AS
          ultimately have "s\<in>{A\<in>Pow({x,y}). A{is closed in}(T{restricted to}{x,y})}""t\<in>{A\<in>Pow({x,y}). A{is closed in}(T{restricted to}{x,y})}"
            by auto
          with S AS2(2) have "s\<in>T{restricted to}{x,y}" "t\<in>T{restricted to}{x,y}""s\<inter>t=0" by auto
          then have "\<exists>U\<in>(T{restricted to}{x,y}). \<exists>V\<in>(T{restricted to}{x,y}). s\<subseteq>U\<and>t\<subseteq>V\<and>U\<inter>V=0" by auto
        }
        then have "\<forall>t. t{is closed in}(T{restricted to}{x,y})\<and>s\<inter>t=0 \<longrightarrow> (\<exists>U\<in>(T{restricted to}{x,y}). \<exists>V\<in>(T{restricted to}{x,y}). s\<subseteq>U\<and>t\<subseteq>V\<and>U\<inter>V=0)"
          by auto
      }
      then have "\<forall>s. s{is closed in}(T{restricted to}{x,y}) \<longrightarrow> (\<forall>t. t{is closed in}(T{restricted to}{x,y})\<and>s\<inter>t=0 \<longrightarrow> (\<exists>U\<in>(T{restricted to}{x,y}). \<exists>V\<in>(T{restricted to}{x,y}). s\<subseteq>U\<and>t\<subseteq>V\<and>U\<inter>V=0))"
        by auto
      then have "(T{restricted to}{x,y}){is normal}" using IsNormal_def by auto
      ultimately have "(T{restricted to}{x,y}){is T\<^sub>4}" using isT4_def by auto
      with sub \<open>T{is anti-}isT4\<close> tot have "{x,y} {is in the spectrum of}isT4" using antiProperty_def
        by auto
      then have "{x,y}\<lesssim>1" using T4_spectrum by auto
      moreover
      have "x\<in>{x,y}" by auto
      ultimately have "{x}={x,y}" using lepoll_1_is_sing[of "{x,y}""x"] by auto
      moreover
      have "y\<in>{x,y}" by auto
      ultimately
      have "y\<in>{x}" by auto
      then have "x=y" by auto
      then have "False" using \<open>x\<in>A\<close>\<open>y\<notin>A\<close> by auto
    }
    then have "A\<subseteq>B\<or>B\<subseteq>A" by auto
  }
  then have "?r {is total on}T" using IsTotal_def by auto
  ultimately
  show "IsLinOrder(T,?r)" using IsLinOrder_def by auto
next
  assume "IsLinOrder(T, {\<langle>U,V\<rangle> \<in> Pow(\<Union>T) \<times> Pow(\<Union>T) . U \<subseteq> V})"
  then have "T{is anti-}isT1" using anti_T1 by auto
  moreover
  have "\<forall>T. T{is a topology} \<longrightarrow> (T{is T\<^sub>4}) \<longrightarrow> (T{is T\<^sub>1})" using topology0.T4_is_T3 
    topology0.T3_is_T2 T2_is_T1 topology0_def by auto
  moreover
  have " \<forall>A. (A {is in the spectrum of} isT1) \<longrightarrow> (A {is in the spectrum of} isT4)" using T1_spectrum T4_spectrum
    by auto
  ultimately show "T{is anti-}isT4" using eq_spect_rev_imp_anti[of "isT4""isT1"] by auto
qed

theorem (in topology0) anti_T3:
  shows "(T{is anti-}isT3) \<longleftrightarrow> (IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V}))"
proof
  assume "T{is anti-}isT3"
  moreover
  have "\<forall>T. T{is a topology} \<longrightarrow> (T{is T\<^sub>4}) \<longrightarrow> (T{is T\<^sub>3})" using topology0.T4_is_T3 
    topology0_def by auto
  moreover
  have " \<forall>A. (A {is in the spectrum of} isT3) \<longrightarrow> (A {is in the spectrum of} isT4)" using T3_spectrum T4_spectrum
    by auto
  ultimately have "T{is anti-}isT4" using eq_spect_rev_imp_anti[of "isT4""isT3"] by auto
  then show "IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V})" using anti_T4 by auto
next
  assume "IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V})"
  then have "T{is anti-}isT1" using anti_T1 by auto
  moreover
  have "\<forall>T. T{is a topology} \<longrightarrow> (T{is T\<^sub>3}) \<longrightarrow> (T{is T\<^sub>1})" using
    topology0.T3_is_T2 T2_is_T1 topology0_def by auto
  moreover
  have " \<forall>A. (A {is in the spectrum of} isT1) \<longrightarrow> (A {is in the spectrum of} isT3)" using T1_spectrum T3_spectrum
    by auto
  ultimately show "T{is anti-}isT3" using eq_spect_rev_imp_anti[of "isT3""isT1"] by auto
qed

theorem (in topology0) anti_T2:
  shows "(T{is anti-}isT2) \<longleftrightarrow> (IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V}))"
proof
  assume "T{is anti-}isT2"
  moreover
  have "\<forall>T. T{is a topology} \<longrightarrow> (T{is T\<^sub>4}) \<longrightarrow> (T{is T\<^sub>2})" using topology0.T4_is_T3 
    topology0.T3_is_T2 topology0_def by auto
  moreover
  have " \<forall>A. (A {is in the spectrum of} isT2) \<longrightarrow> (A {is in the spectrum of} isT4)" using T2_spectrum T4_spectrum
    by auto
  ultimately have "T{is anti-}isT4" using eq_spect_rev_imp_anti[of "isT4""isT2"] by auto
  then show "IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V})" using anti_T4 by auto
next
  assume "IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V})"
  then have "T{is anti-}isT1" using anti_T1 by auto
  moreover
  have "\<forall>T. T{is a topology} \<longrightarrow> (T{is T\<^sub>2}) \<longrightarrow> (T{is T\<^sub>1})" using T2_is_T1 by auto
  moreover
  have " \<forall>A. (A {is in the spectrum of} isT1) \<longrightarrow> (A {is in the spectrum of} isT2)" using T1_spectrum T2_spectrum
    by auto
  ultimately show "T{is anti-}isT2" using eq_spect_rev_imp_anti[of "isT2""isT1"] by auto
qed

lemma linord_spectrum:
  shows "(A{is in the spectrum of}(\<lambda>T. IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V}))) \<longleftrightarrow> A\<lesssim>1"
proof
  assume "A{is in the spectrum of}(\<lambda>T. IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V}))"
  then have reg:"\<forall>T. T{is a topology}\<and> \<Union>T\<approx>A \<longrightarrow> IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V})"
    using Spec_def by auto
  {
    assume "A=0"
    moreover
    have "0\<lesssim>1" using empty_lepollI by auto
    ultimately have "A\<lesssim>1" using eq_lepoll_trans by auto
  }
  moreover
  { 
    assume "A\<noteq>0"
    then obtain x where "x\<in>A" by blast
    moreover
    {
      fix y
      assume "y\<in>A"
      have "Pow(A) {is a topology}" using Pow_is_top by auto
      moreover
      have "\<Union>Pow(A)=A" by auto
      then have "\<Union>Pow(A)\<approx>A" by auto
      note reg
      ultimately have "IsLinOrder(Pow(A),{\<langle>U,V\<rangle>\<in>Pow(\<Union>Pow(A))\<times>Pow(\<Union>Pow(A)). U\<subseteq>V})" by auto
      then have "IsLinOrder(Pow(A),{\<langle>U,V\<rangle>\<in>Pow(A)\<times>Pow(A). U\<subseteq>V})" by auto
      with \<open>x\<in>A\<close>\<open>y\<in>A\<close> have "{x}\<subseteq>{y}\<or>{y}\<subseteq>{x}" unfolding IsLinOrder_def IsTotal_def by auto
      then have "x=y" by auto
    }
    ultimately have "A={x}" by blast
    then have "A\<approx>1" using singleton_eqpoll_1 by auto
    then have "A\<lesssim>1" using eqpoll_imp_lepoll by auto
  }
  ultimately show "A\<lesssim>1" by auto
next
  assume "A\<lesssim>1"
  then have ind:"A{is in the spectrum of}(\<lambda>T. T={0,\<Union>T})" using indiscrete_spectrum by auto
  {
    fix T
    assume AS:"T{is a topology}" "T={0,\<Union>T}"
    have "trans({\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V})" unfolding trans_def by auto
    moreover
    have "antisym({\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V})" unfolding antisym_def by auto
    moreover
    have "{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V}{is total on}T"
    proof-
      {
        fix aa b
        assume "aa\<in>T""b\<in>T"
        with AS(2) have "aa\<in>{0,\<Union>T}""b\<in>{0,\<Union>T}" by auto
        then have "aa=0\<or>aa=\<Union>T""b=0\<or>b=\<Union>T" by auto
        then have "aa\<subseteq>b\<or>b\<subseteq>aa" by auto
        then have "\<langle>aa, b\<rangle> \<in> Collect(Pow(\<Union>T) \<times> Pow(\<Union>T), split((\<subseteq>))) \<or> \<langle>b, aa\<rangle> \<in> Collect(Pow(\<Union>T) \<times> Pow(\<Union>T), split((\<subseteq>)))"
        using \<open>aa\<in>T\<close>\<open>b\<in>T\<close> by auto
      }
      then show ?thesis using IsTotal_def by auto
    qed
    ultimately have "IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V})" unfolding IsLinOrder_def by auto
  }
  then have " \<forall>T. T {is a topology} \<longrightarrow> T = {0, \<Union>T} \<longrightarrow> IsLinOrder(T, {\<langle>U,V\<rangle> \<in> Pow(\<Union>T) \<times> Pow(\<Union>T) . U \<subseteq> V})" by auto
  then show "A{is in the spectrum of}(\<lambda>T. IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V}))"
    using P_imp_Q_spec_inv[of "\<lambda>T. T={0,\<Union>T}""\<lambda>T. IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V})"]
    ind by auto
qed

theorem (in topology0) anti_linord:
  shows "(T{is anti-}(\<lambda>T. IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V}))) \<longleftrightarrow> T{is T\<^sub>1}"
proof
  assume AS:"T{is anti-}(\<lambda>T. IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V}))"
  {
    assume "\<not>(T{is T\<^sub>1})"
    then obtain x y where "x\<in>\<Union>T""y\<in>\<Union>T""x\<noteq>y""\<forall>U\<in>T. x\<notin>U\<or>y\<in>U" unfolding isT1_def by auto
    {
      assume "{x}\<in>T{restricted to}{x,y}"
      then obtain U where "U\<in>T" "{x}={x,y}\<inter>U" unfolding RestrictedTo_def by auto
      moreover
      have "x\<in>{x}" by auto
      ultimately have "U\<in>T""x\<in>U" by auto
      moreover
      {
        assume "y\<in>U"
        then have "y\<in>{x,y}\<inter>U" by auto
        with \<open>{x}={x,y}\<inter>U\<close> have "y\<in>{x}" by auto
        with \<open>x\<noteq>y\<close> have "False" by auto
      }
      then have "y\<notin>U" by auto
      moreover
      note \<open>\<forall>U\<in>T. x\<notin>U\<or>y\<in>U\<close>
      ultimately have "False" by auto
    }
    then have "{x}\<notin>T{restricted to}{x,y}" by auto
    moreover
    have tot:"\<Union>(T{restricted to}{x,y})={x,y}" using \<open>x\<in>\<Union>T\<close>\<open>y\<in>\<Union>T\<close> unfolding RestrictedTo_def by auto
    moreover
    have "T{restricted to}{x,y}\<subseteq>Pow(\<Union>(T{restricted to}{x,y}))" by auto
    ultimately have "T{restricted to}{x,y}\<subseteq>Pow({x,y})-{{x}}" by auto
    moreover
    have "Pow({x,y})={0,{x,y},{x},{y}}" by blast
    ultimately have "T{restricted to}{x,y}\<subseteq>{0,{x,y},{y}}" by auto
    moreover
    have "IsLinOrder({0,{x,y},{y}},{\<langle>U,V\<rangle>\<in>Pow({x,y})\<times>Pow({x,y}). U\<subseteq>V})"
    proof-
      have "antisym(Collect(Pow({x, y}) \<times> Pow({x, y}), split((\<subseteq>))))" using antisym_def by auto
      moreover
      have "trans(Collect(Pow({x, y}) \<times> Pow({x, y}), split((\<subseteq>))))" using trans_def by auto
      moreover
      have "Collect(Pow({x, y}) \<times> Pow({x, y}), split((\<subseteq>))) {is total on} {0, {x, y}, {y}}" using IsTotal_def by auto
      ultimately show "IsLinOrder({0,{x,y},{y}},{\<langle>U,V\<rangle>\<in>Pow({x,y})\<times>Pow({x,y}). U\<subseteq>V})" using IsLinOrder_def by auto
    qed
    ultimately have "IsLinOrder(T{restricted to}{x,y},{\<langle>U,V\<rangle>\<in>Pow({x,y})\<times>Pow({x,y}). U\<subseteq>V})" using ord_linear_subset
      by auto
    with tot have "IsLinOrder(T{restricted to}{x,y},{\<langle>U,V\<rangle>\<in>Pow(\<Union>(T{restricted to}{x,y}))\<times>Pow(\<Union>(T{restricted to}{x,y})). U\<subseteq>V})"
      by auto
    then have "IsLinOrder(T{restricted to}{x,y},Collect(Pow(\<Union>(T {restricted to} {x,y})) \<times> Pow(\<Union>(T {restricted to} {x,y})), split((\<subseteq>))))" by auto
    moreover
    from \<open>x\<in>\<Union>T\<close>\<open>y\<in>\<Union>T\<close> have "{x,y}\<in>Pow(\<Union>T)" by auto
    moreover
    note AS
    ultimately have "{x,y}{is in the spectrum of}(\<lambda>T. IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V}))" unfolding antiProperty_def
      by simp
    then have "{x,y}\<lesssim>1" using linord_spectrum by auto
    moreover
    have "x\<in>{x,y}" by auto
    ultimately have "{x}={x,y}" using lepoll_1_is_sing[of "{x,y}""x"] by auto
    moreover
    have "y\<in>{x,y}" by auto
    ultimately
    have "y\<in>{x}" by auto
    then have "x=y" by auto
    then have "False" using \<open>x\<noteq>y\<close> by auto
  }
  then show "T {is T\<^sub>1}" by auto
next
  assume T1:"T {is T\<^sub>1}"
  {
    fix A
    assume A_def:"A\<in>Pow(\<Union>T)""IsLinOrder((T{restricted to}A) ,{\<langle>U,V\<rangle>\<in>Pow(\<Union>(T{restricted to}A))\<times>Pow(\<Union>(T{restricted to}A)). U\<subseteq>V})"
    {
      fix x 
      assume AS1:"x\<in>A"
      {
        fix y
        assume AS:"y\<in>A""x\<noteq>y"
        with AS1 have "{x,y}\<in>Pow(\<Union>T)" using \<open>A\<in>Pow(\<Union>T)\<close> by auto
        from \<open>x\<in>A\<close>\<open>y\<in>A\<close> have "{x,y}\<in>Pow(A)" by auto
        from \<open>{x,y}\<in>Pow(\<Union>T)\<close> have T11:"(T{restricted to}{x,y}){is T\<^sub>1}" using T1_here T1 by auto
        moreover
        have tot:"\<Union>(T{restricted to}{x,y})={x,y}" unfolding RestrictedTo_def using \<open>{x,y}\<in>Pow(\<Union>T)\<close> by auto
        moreover
        note AS(2) 
        ultimately obtain U where "x\<in>U""y\<notin>U""U\<in>(T{restricted to}{x,y})" unfolding isT1_def by auto
        moreover
        from AS(2) tot T11 obtain V where "y\<in>V""x\<notin>V""V\<in>(T{restricted to}{x,y})" unfolding isT1_def by auto
        ultimately have "x\<in>U-V""y\<in>V-U""U\<in>(T{restricted to}{x,y})""V\<in>(T{restricted to}{x,y})" by auto
        then have "\<not>(U\<subseteq>V\<or>V\<subseteq>U)""U\<in>(T{restricted to}{x,y})""V\<in>(T{restricted to}{x,y})" by auto
        then have "\<not>({\<langle>U,V\<rangle>\<in>Pow(\<Union>(T{restricted to}{x,y}))\<times>Pow(\<Union>(T{restricted to}{x,y})). U\<subseteq>V} {is total on} (T{restricted to}{x,y}))"
          unfolding IsTotal_def by auto
        then have "\<not>(IsLinOrder((T{restricted to}{x,y}),{\<langle>U,V\<rangle>\<in>Pow(\<Union>(T{restricted to}{x,y}))\<times>Pow(\<Union>(T{restricted to}{x,y})). U\<subseteq>V}))"
          unfolding IsLinOrder_def by auto
        moreover
        {
          have "(T{restricted to}A) {is a topology}" using Top_1_L4 by auto
          moreover
          note A_def(2) linordtop_here
          ultimately have "\<forall>B\<in>Pow(\<Union>(T{restricted to}A)). IsLinOrder((T{restricted to}A){restricted to}B ,{\<langle>U,V\<rangle>\<in>Pow(\<Union>((T{restricted to}A){restricted to}B))\<times>Pow(\<Union>((T{restricted to}A){restricted to}B)). U\<subseteq>V})"
            unfolding IsHer_def by auto
          moreover
          have tot:"\<Union>(T{restricted to}A)=A" unfolding RestrictedTo_def using \<open>A\<in>Pow(\<Union>T)\<close> by auto
          ultimately have  "\<forall>B\<in>Pow(A). IsLinOrder((T{restricted to}A){restricted to}B ,{\<langle>U,V\<rangle>\<in>Pow(\<Union>((T{restricted to}A){restricted to}B))\<times>Pow(\<Union>((T{restricted to}A){restricted to}B)). U\<subseteq>V})" by auto
          moreover
          have "\<forall>B\<in>Pow(A). (T{restricted to}A){restricted to}B=T{restricted to}B" using subspace_of_subspace \<open>A\<in>Pow(\<Union>T)\<close> by auto
          ultimately
          have "\<forall>B\<in>Pow(A). IsLinOrder((T{restricted to}B) ,{\<langle>U,V\<rangle>\<in>Pow(\<Union>((T{restricted to}A){restricted to}B))\<times>Pow(\<Union>((T{restricted to}A){restricted to}B)). U\<subseteq>V})" by auto
          moreover
          have "\<forall>B\<in>Pow(A). \<Union>((T{restricted to}A){restricted to}B)=B" using \<open>A\<in>Pow(\<Union>T)\<close> unfolding RestrictedTo_def by auto
          ultimately have "\<forall>B\<in>Pow(A). IsLinOrder((T{restricted to}B) ,{\<langle>U,V\<rangle>\<in>Pow(B)\<times>Pow(B). U\<subseteq>V})" by auto
          with \<open>{x,y}\<in>Pow(A)\<close> have "IsLinOrder((T{restricted to}{x,y}) ,{\<langle>U,V\<rangle>\<in>Pow({x,y})\<times>Pow({x,y}). U\<subseteq>V})" by auto
        }
        ultimately have "False" using tot by auto
      }
      then have "A={x}" using AS1 by auto
      then have "A\<approx>1" using singleton_eqpoll_1 by auto
      then have "A\<lesssim>1" using eqpoll_imp_lepoll by auto
      then have "A{is in the spectrum of}(\<lambda>T. IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V}))" using linord_spectrum
        by auto
    }
    moreover
    {
      assume "A=0"
      then have "A\<approx>0" by auto
      moreover
      have "0\<lesssim>1" using empty_lepollI by auto
      ultimately have "A\<lesssim>1" using eq_lepoll_trans by auto
      then have "A{is in the spectrum of}(\<lambda>T. IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V}))" using linord_spectrum
        by auto
    }
    ultimately have "A{is in the spectrum of}(\<lambda>T. IsLinOrder(T,{\<langle>U,V\<rangle>\<in>Pow(\<Union>T)\<times>Pow(\<Union>T). U\<subseteq>V}))" by blast
  }
  then show "T{is anti-}(\<lambda>T. IsLinOrder(T, {\<langle>U,V\<rangle> \<in> Pow(\<Union>T) \<times> Pow(\<Union>T) . U \<subseteq> V}))" unfolding antiProperty_def
    by auto
qed

text\<open>In conclusion, $T_1$ is also an anti-property.\<close>

text\<open>Let's define some anti-properties that we'll use in the future.\<close>

definition
  IsAntiComp ("_{is anti-compact}")
  where "T{is anti-compact} \<equiv> T{is anti-}(\<lambda>T. (\<Union>T){is compact in}T)"

definition
  IsAntiLin ("_{is anti-lindeloef}")
  where "T{is anti-lindeloef} \<equiv> T{is anti-}(\<lambda>T. ((\<Union>T){is lindeloef in}T))"

text\<open>Anti-compact spaces are also called pseudo-finite spaces in literature
before the concept of anti-property was defined.\<close>

end

