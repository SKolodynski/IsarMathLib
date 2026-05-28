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

section \<open>Topology 4\<close>

theory Topology_ZF_4 imports Topology_ZF_1 Order_ZF func1 NatOrder_ZF
begin

text\<open>This theory deals with convergence in topological spaces.
  Contributed by Daniel de la Concepcion.\<close>

subsection\<open>Nets\<close>

text\<open>Nets are a generalization of sequences. It is known that sequences do not
determine the behavior of the topological spaces that are not first countable; i.e.,
have a countable neighborhood base for each point. To solve this problem,
nets were defined so that the behavior of any topological space can be
thought in terms of convergence of nets.\<close>

text\<open>We say that a relation $r$ \<open>directs\<close> a set $X$ if the relation is reflexive, transitive
  on $X$ and for every two elements $x,y$ of $X$ there is some element $z$ such that both
  $x$ and $y$ are in the relation with $z$. Note that this naming is a bit inconsistent with what
  is defined in \<open>Order_ZF\<close> where we define what it means that $r$ \<open>up-directs\<close> $X$ 
  (the third condition in the definition below) or $r$ \<open>down-directs\<close> $X$. This naming inconsistency
   will be fixed in the future (maybe).\<close>

definition
  IsDirectedSet ("_ directs _" 90)
  where "r directs X \<equiv> refl(X,r) \<and> trans(r) \<and> (\<forall>x\<in>X. \<forall>y\<in>X. \<exists>z\<in>X. \<langle>x,z\<rangle>\<in>r \<and> \<langle>y,z\<rangle>\<in>r)"

text\<open>Any linear order is a directed set; in particular $(\mathbb{N},\leq)$.\<close>

lemma linorder_imp_directed:
  assumes "IsLinOrder(X,r)"
  shows "r directs X"
proof-
  from assms have "trans(r)" using IsLinOrder_def by auto
  moreover
  from assms have r:"refl(X,r)" using IsLinOrder_def total_is_refl by auto
  moreover
  {
    fix x y
    assume R: "x\<in>X" "y\<in>X"
    with assms have "\<langle>x,y\<rangle>\<in>r \<or> \<langle>y,x\<rangle>\<in>r" using IsLinOrder_def IsTotal_def by auto
    with r have "(\<langle>x,y\<rangle>\<in>r \<and> \<langle>y,y\<rangle>\<in>r)\<or>(\<langle>y,x\<rangle>\<in>r \<and> \<langle>x,x\<rangle>\<in>r)" using R refl_def by auto
    then have "\<exists>z\<in>X. \<langle>x,z\<rangle>\<in>r \<and> \<langle>y,z\<rangle>\<in>r" using R by auto
  }
  ultimately show ?thesis using IsDirectedSet_def function_def by auto
qed

text\<open> Natural numbers are a directed set.\<close>

corollary Le_directs_nat:
  shows "IsLinOrder(nat,Le)" "Le directs nat"
proof -
  show "IsLinOrder(nat,Le)"  by (rule NatOrder_ZF_1_L2) 
  then show "Le directs nat" using linorder_imp_directed by auto
qed

text\<open>We are able to define the concept of net, now that we now what a directed set is.\<close>

definition
  IsNet ("_ {is a net on} _" 90)
  where "N {is a net on} X \<equiv> fst(N):domain(fst(N))\<rightarrow>X \<and> (snd(N) directs domain(fst(N))) \<and> domain(fst(N))\<noteq>0"

text\<open>Provided a topology and a net directed on its underlying set,
we can talk about convergence of the net in the topology.\<close>

definition (in topology0)
  NetConverges ("_ \<rightarrow>\<^sub>N _" 90)
  where "N {is a net on} \<Union>T \<Longrightarrow> N \<rightarrow>\<^sub>N x \<equiv> 
  (x\<in>\<Union>T) \<and> (\<forall>U\<in>Pow(\<Union>T). (x\<in>int(U) \<longrightarrow> (\<exists>t\<in>domain(fst(N)). \<forall>m\<in>domain(fst(N)). 
    (\<langle>t,m\<rangle>\<in>snd(N) \<longrightarrow> fst(N)`m\<in>U))))"

text\<open>One of the most important directed sets, is the neighborhoods of a point.\<close>

theorem (in topology0) directedset_neighborhoods:
  assumes "x\<in>\<Union>T"
  defines "Neigh\<equiv>{U\<in>Pow(\<Union>T). x\<in>int(U)}"
  defines "r\<equiv>{\<langle>U,V\<rangle>\<in>(Neigh \<times> Neigh). V\<subseteq>U}"
  shows "r directs Neigh"
proof-
  {
    fix U
    assume "U \<in> Neigh"
    then have "\<langle>U,U\<rangle> \<in> r" using r_def by auto
  }
  then have "refl(Neigh,r)" using refl_def by auto
  moreover
  {
    fix U V W
    assume "\<langle>U,V\<rangle> \<in> r" "\<langle>V,W\<rangle> \<in> r"
    then have "U \<in> Neigh" "W \<in> Neigh" "W\<subseteq>U" using r_def by auto
    then have "\<langle>U,W\<rangle>\<in>r" using r_def by auto
  }
  then have "trans(r)" using trans_def by blast
  moreover
  {
    fix A B
    assume p: "A\<in>Neigh" "B\<in>Neigh"
    have "A\<inter>B \<in> Neigh"
    proof-
      from p have "A\<inter>B \<in> Pow(\<Union>T)" using Neigh_def by auto
      moreover
      { from p have "x\<in>int(A)""x\<in>int(B)" using Neigh_def by auto
        then have "x\<in>int(A)\<inter>int(B)" by auto
        moreover
        { have "int(A)\<inter>int(B)\<subseteq>A\<inter>B" using Top_2_L1  by auto
          moreover have "int(A)\<inter>int(B)\<in>T" 
            using Top_2_L2 Top_2_L2 topSpaceAssum IsATopology_def by blast
          ultimately have "int(A)\<inter>int(B)\<subseteq>int(A\<inter>B)" 
          using Top_2_L5 by auto 
        }
        ultimately have "x \<in> int(A\<inter>B)" by auto 
      }
      ultimately show ?thesis using Neigh_def by auto
    qed
    moreover from \<open>A\<inter>B \<in> Neigh\<close> have "\<langle>A,A\<inter>B\<rangle>\<in>r \<and> \<langle>B,A\<inter>B\<rangle>\<in>r" 
      using r_def p by auto
    ultimately
    have "\<exists>z\<in>Neigh. \<langle>A,z\<rangle>\<in>r \<and> \<langle>B,z\<rangle>\<in>r" by auto
  }
  ultimately show ?thesis using IsDirectedSet_def by auto
qed

text\<open>There can be nets directed by the neighborhoods that converge to the point;
if there is a choice function.\<close>

theorem (in topology0) net_direct_neigh_converg:
  assumes "x\<in>\<Union>T"
  defines "Neigh\<equiv>{U\<in>Pow(\<Union>T). x\<in>int(U)}"
  defines "r\<equiv>{\<langle>U,V\<rangle>\<in>(Neigh \<times> Neigh). V\<subseteq>U}"
  assumes "f:Neigh\<rightarrow>\<Union>T" "\<forall>U\<in>Neigh. f`(U) \<in> U"
  shows "\<langle>f,r\<rangle> \<rightarrow>\<^sub>N x"
proof -
  from assms(4) have dom_def: "Neigh = domain(f)" using Pi_def by auto
  moreover
    have "\<Union>T\<in>T" using topSpaceAssum IsATopology_def by auto
    then have "int(\<Union>T)=\<Union>T" using Top_2_L3 by auto
    with assms(1) have "\<Union>T\<in>Neigh" using Neigh_def by auto
    then have "\<Union>T\<in>domain(fst(\<langle>f,r\<rangle>))" using dom_def by auto
  moreover from assms(4) dom_def have "fst(\<langle>f,r\<rangle>):domain(fst(\<langle>f,r\<rangle>))\<rightarrow>\<Union>T" 
    by auto
  moreover from assms(1,2,3) dom_def have "snd(\<langle>f,r\<rangle>) directs domain(fst(\<langle>f,r\<rangle>))" 
      using directedset_neighborhoods by simp
  ultimately have Net: "\<langle>f,r\<rangle> {is a net on} \<Union>T" unfolding IsNet_def by auto
  {
    fix U
    assume "U \<in> Pow(\<Union>T)" "x \<in> int(U)"
    then have "U \<in> Neigh" using Neigh_def by auto
    then have t: "U \<in> domain(f)" using dom_def by auto
    {
      fix W
      assume A: "W\<in>domain(f)" "\<langle>U,W\<rangle>\<in>r"
      then have "W\<in>Neigh" using dom_def by auto
      with assms(5) have "f`W\<in>W" by auto
      with A(2) r_def have "f`W\<in>U" by auto
    }
    then have "\<forall>W\<in>domain(f). (\<langle>U,W\<rangle>\<in>r \<longrightarrow> f`W\<in>U)" by auto
    with t have "\<exists>V\<in>domain(f). \<forall>W\<in>domain(f). (\<langle>V,W\<rangle>\<in>r \<longrightarrow> f`W\<in>U)" by auto
  }
  then have "\<forall>U\<in>Pow(\<Union>T). (x\<in>int(U) \<longrightarrow> (\<exists>V\<in>domain(f). \<forall>W\<in>domain(f). (\<langle>V,W\<rangle>\<in>r \<longrightarrow> f`(W) \<in> U)))"
    by auto
  with assms(1) Net show ?thesis using NetConverges_def by auto
qed

subsection\<open>Filters\<close>

text\<open>Nets are a generalization of sequences that can make us see that not all
topological spaces can be described by sequences. Nevertheless, nets are not
always the tool used to deal with convergence. The reason is that they make
use of directed sets which are completely unrelated with the topology.\<close>

text\<open>The topological tools to deal with convergence are what is called filters.\<close>

definition
  IsFilter ("_ {is a filter on} _" 90)
  where "\<FF> {is a filter on} X \<equiv> (\<emptyset>\<notin>\<FF>) \<and> (X\<in>\<FF>) \<and> \<FF>\<subseteq>Pow(X) \<and> 
  (\<forall>A\<in>\<FF>. \<forall>B\<in>\<FF>. A\<inter>B\<in>\<FF>) \<and> (\<forall>B\<in>\<FF>. \<forall>C\<in>Pow(X). B\<subseteq>C \<longrightarrow> C\<in>\<FF>)"

text\<open>The next lemma splits the the definition of a filter into four conditions
 to make it easier to reference each one separately in proofs.\<close>

lemma is_filter_def_split: assumes "\<FF> {is a filter on} X"
  shows "\<emptyset>\<notin>\<FF>" "X\<in>\<FF>" "\<FF>\<subseteq>Pow(X)" 
    "\<forall>A\<in>\<FF>. \<forall>B\<in>\<FF>. A\<inter>B\<in>\<FF>" and "\<forall>B\<in>\<FF>. \<forall>C\<in>Pow(X). B\<subseteq>C \<longrightarrow> C\<in>\<FF>"
  using assms unfolding IsFilter_def by auto

text\<open>Filters are closed with respect to taking finite intersections.\<close>

lemma filter_fin_inter_closed: 
  assumes "\<FF> {is a filter on} X" "M\<in>FinPow(\<FF>)\<setminus>{\<emptyset>}"
  shows "\<Inter>M \<in> \<FF>"
  using assms is_filter_def_split(4) inter_two_inter_fin by simp

text\<open>Filters are closed with respect to taking supersets.\<close>

lemma filter_superset_closed: 
  assumes "\<FF> {is a filter on} X" "\<A>\<subseteq>\<FF>"
  shows "Supersets(X,\<A>) \<subseteq> \<FF>"
  using assms is_filter_def_split(5) unfolding Supersets_def
  by auto
 
text\<open>Not all the sets of a filter are needed to be consider at all times; as it happens
  with a topology we can consider bases.\<close>

definition
  IsBaseFilter ("_ {is a base filter} _" 90)
  where "C {is a base filter} \<FF> \<equiv> C\<subseteq>\<FF> \<and> \<FF>={A\<in>Pow(\<Union>\<FF>). (\<exists>D\<in>C. D\<subseteq>A)}"

text\<open>Not every set is a base for a filter, as it happens with topologies, there
is a condition to be satisfied.\<close>

definition
  SatisfiesFilterBase ("_ {satisfies the filter base condition}" 90)
  where "C {satisfies the filter base condition} \<equiv> (\<forall>A\<in>C. \<forall>B\<in>C. \<exists>D\<in>C. D\<subseteq>A\<inter>B) \<and> C\<noteq>0 \<and> 0\<notin>C"

text\<open>Every set of a filter contains a set from the filter's base.\<close>

lemma basic_element_filter:
  assumes "A\<in>\<FF>" and "C {is a base filter} \<FF>"
  shows "\<exists>D\<in>C. D\<subseteq>A"
proof-
  from assms(2) have t:"\<FF>={A\<in>Pow(\<Union>\<FF>). (\<exists>D\<in>C. D\<subseteq>A)}" using IsBaseFilter_def by auto
  with assms(1) have "A\<in>{A\<in>Pow(\<Union>\<FF>). (\<exists>D\<in>C. D\<subseteq>A)}" by auto
  then have "A\<in>Pow(\<Union>\<FF>)" "\<exists>D\<in>C. D\<subseteq>A" by auto
  then show ?thesis by auto
qed

text\<open>The following two results state that the filter base condition is necessary
and sufficient for the filter generated by a base, to be an actual filter.
The third result, rewrites the previous two.\<close>

theorem basic_filter_1:
  assumes "C {is a base filter} \<FF>" and "C {satisfies the filter base condition}"
  shows "\<FF> {is a filter on} \<Union>\<FF>"
proof-
  {
    fix A B
    assume AF: "A\<in>\<FF>" and BF: "B\<in>\<FF>"
    with assms(1) have "\<exists>DA\<in>C. DA\<subseteq>A" using  basic_element_filter by simp
    then obtain DA where perA: "DA\<in>C" and subA: "DA\<subseteq>A" by auto
    from BF assms have "\<exists>DB\<in>C. DB\<subseteq>B" using  basic_element_filter by simp
    then obtain DB where perB: "DB\<in>C" and subB: "DB\<subseteq>B" by auto
    from assms(2) perA perB have "\<exists>D\<in>C. D\<subseteq>DA\<inter>DB" 
      unfolding SatisfiesFilterBase_def by auto
    then obtain D where "D\<in>C" "D\<subseteq>DA\<inter>DB" by auto
    with subA subB AF BF have "A\<inter>B\<in>{A \<in> Pow(\<Union>\<FF>) . \<exists>D\<in>C. D \<subseteq> A}" by auto
    with assms(1) have "A\<inter>B\<in>\<FF>" unfolding IsBaseFilter_def by auto    
  }
  moreover
  {
    fix A B
    assume AF: "A\<in>\<FF>" and BS: "B\<in>Pow(\<Union>\<FF>)" and sub: "A\<subseteq>B"
    from assms(1) AF have "\<exists>D\<in>C. D\<subseteq>A" using basic_element_filter by auto
    then obtain D where "D\<subseteq>A" "D\<in>C" by auto
    with sub BS have "B\<in>{A\<in>Pow(\<Union>\<FF>). \<exists>D\<in>C. D\<subseteq>A}" by auto
    with assms(1) have "B\<in>\<FF>" unfolding IsBaseFilter_def by auto
    }
  moreover
  from assms(2) have "C\<noteq>0" using SatisfiesFilterBase_def by auto
  then obtain D where "D\<in>C" by auto
  with assms(1) have "D\<subseteq>\<Union>\<FF>" using IsBaseFilter_def by auto
  with \<open>D\<in>C\<close> have "\<Union>\<FF>\<in>{A\<in>Pow(\<Union>\<FF>). \<exists>D\<in>C. D\<subseteq>A}" by auto
  with assms(1) have "\<Union>\<FF>\<in>\<FF>" unfolding IsBaseFilter_def by auto
  moreover
  {
    assume "0\<in>\<FF>" 
    with assms(1) have "\<exists>D\<in>C. D\<subseteq>0" using basic_element_filter by simp 
    then obtain D where "D\<in>C""D\<subseteq>0" by auto
    then have "D\<in>C" "D=0" by auto
    with assms(2) have "False" using SatisfiesFilterBase_def by auto 
  }
  then have "0\<notin>\<FF>" by auto
  ultimately show ?thesis using IsFilter_def by auto
qed

text\<open>A base filter satisfies the filter base condition.\<close>

theorem basic_filter_2:
  assumes "C {is a base filter} \<FF>" and "\<FF> {is a filter on} \<Union>\<FF>"
  shows "C {satisfies the filter base condition}"
proof-
  {
    fix A B
    assume AF: "A\<in>C" and BF: "B\<in>C"
    then have "A\<in>\<FF>" and "B\<in>\<FF>" using assms(1) IsBaseFilter_def by auto
    then have "A\<inter>B\<in>\<FF>" using assms(2) IsFilter_def by auto
    then have "\<exists>D\<in>C. D\<subseteq>A\<inter>B" using assms(1) basic_element_filter by blast
  }
  then have "\<forall>A\<in>C. \<forall>B\<in>C. \<exists>D\<in>C. D\<subseteq>A\<inter>B" by auto
  moreover
  {
    assume "0\<in>C"
    then have "0\<in>\<FF>" using assms(1) IsBaseFilter_def by auto
    then have "False" using assms(2) IsFilter_def by auto
  } 
  then have "0\<notin>C" by auto
  moreover
  {
    assume "C=0"
    then have "\<FF>=0" using assms(1) IsBaseFilter_def by auto
    then have "False" using assms(2) IsFilter_def by auto
  }
  then have "C\<noteq>0" by auto
  ultimately show ?thesis using SatisfiesFilterBase_def by auto
qed

text\<open>A base filter for a collection satisfies the filter base condition iff that collection
  is in fact a filter.\<close>

theorem basic_filter:
  assumes "C {is a base filter} \<FF>"
  shows "(C {satisfies the filter base condition}) \<longleftrightarrow> (\<FF> {is a filter on} \<Union>\<FF>)"
using assms basic_filter_1 basic_filter_2 by auto

text\<open>A base for a filter determines a filter up to the underlying set.\<close>

theorem base_unique_filter:
  assumes "C {is a base filter} \<FF>\<^sub>1"and "C {is a base filter} \<FF>\<^sub>2"
  shows "\<FF>\<^sub>1=\<FF>\<^sub>2 \<longleftrightarrow> \<Union>\<FF>\<^sub>1=\<Union>\<FF>\<^sub>2"
using assms unfolding IsBaseFilter_def by auto

text\<open>Suppose that we take any nonempty collection $C$ of subsets of some set $X$. 
Then this collection is a base filter for the collection of all supersets (in $X$) of sets from $C$.
\<close>

theorem base_unique_filter_set1:
  assumes "C \<subseteq> Pow(X)" and "C\<noteq>0"
  shows "C {is a base filter} {A\<in>Pow(X). \<exists>D\<in>C. D\<subseteq>A}" and "\<Union>{A\<in>Pow(X). \<exists>D\<in>C. D\<subseteq>A}=X"
proof-
  from assms(1) have "C\<subseteq>{A\<in>Pow(X). \<exists>D\<in>C. D\<subseteq>A}" by auto
  moreover
  from assms(2) obtain D where "D\<in>C" by auto
  then have "D\<subseteq>X" using assms(1) by auto
  with \<open>D\<in>C\<close> have "X\<in>{A\<in>Pow(X). \<exists>D\<in>C. D\<subseteq>A}" by auto
  then show "\<Union>{A\<in>Pow(X). \<exists>D\<in>C. D\<subseteq>A}=X" by auto
  ultimately
  show "C {is a base filter} {A\<in>Pow(X). \<exists>D\<in>C. D\<subseteq>A}" using IsBaseFilter_def by auto
qed

text\<open>A collection $C$ that satisfies the filter base condition is a base filter for some other
collection $\frak F$ iff $\frak F$ is the collection of supersets of $C$.\<close>

theorem base_unique_filter_set2:
  assumes "C\<subseteq>Pow(X)" and "C {satisfies the filter base condition}"
  shows "((C {is a base filter} \<FF>) \<and> \<Union>\<FF>=X) \<longleftrightarrow> \<FF>={A\<in>Pow(X). \<exists>D\<in>C. D\<subseteq>A}"
  using assms IsBaseFilter_def SatisfiesFilterBase_def base_unique_filter_set1
   by auto

text\<open>A simple corollary from the previous lemma.\<close>

corollary base_unique_filter_set3:
  assumes "C\<subseteq>Pow(X)" and "C {satisfies the filter base condition}"
  shows "C {is a base filter} {A\<in>Pow(X). \<exists>D\<in>C. D\<subseteq>A}" and "\<Union>{A\<in>Pow(X). \<exists>D\<in>C. D\<subseteq>A} = X"
proof -
  let ?\<FF> = "{A\<in>Pow(X). \<exists>D\<in>C. D\<subseteq>A}"
  from assms have "(C {is a base filter} ?\<FF>) \<and> \<Union>?\<FF>=X"
    using base_unique_filter_set2 by simp
  thus "C {is a base filter} ?\<FF>" and "\<Union>?\<FF> = X"
    by auto
qed  

text\<open>Every filter can be expanded by a set\<close>

lemma extend_filter:
  assumes "A\<in>Pow(X)" "\<FF> {is a filter on} X" "A\<noteq>0" "A\<notin>\<FF>" "X\<setminus>A\<notin>\<FF>"
  shows "\<exists>\<GG>. (\<GG> {is a filter on} X) \<and> A\<in>\<GG> \<and> \<FF>\<subseteq>\<GG>"
proof
  from assms(2,3) have ne: "{F\<inter>A. F\<in>\<FF>}\<noteq>\<emptyset>" unfolding IsFilter_def 
    by auto 
  moreover
  { assume "\<emptyset> \<in> {F\<inter>A. F\<in>\<FF>}"
    then obtain F where F: "F\<in>\<FF>" "F\<inter>A = \<emptyset>" by auto
    with assms(2) have f: "F \<subseteq> X\<setminus>A" unfolding IsFilter_def by auto
    from assms(2) F(1) have "\<forall>C\<in>Pow(X). F \<subseteq> C \<longrightarrow> C \<in> \<FF>"
      unfolding IsFilter_def by auto
    with assms(5) \<open>F \<subseteq> X\<setminus>A\<close> have False by auto
  } hence "\<emptyset> \<notin> {F\<inter>A. F\<in>\<FF>}" by auto 
  moreover
  { fix x y assume as: "x \<in> {F\<inter>A. F\<in>\<FF>}" "y \<in> {F\<inter>A. F\<in>\<FF>}"
    then obtain f\<^sub>x f\<^sub>y where ff: "x=f\<^sub>x\<inter>A" "y=f\<^sub>y\<inter>A" "f\<^sub>x\<in>\<FF>" "f\<^sub>y\<in>\<FF>" 
      by auto
    hence "x\<inter>y = f\<^sub>x\<inter>f\<^sub>y\<inter>A" by auto
    with assms(2) ff have "\<exists>D\<in>{F\<inter>A. F\<in>\<FF>}. D\<subseteq>x\<inter>y" 
      unfolding IsFilter_def by blast
  } hence "\<forall>A\<^sub>a\<in>{F\<inter>A. F\<in>\<FF>}. \<forall>B\<in>{F\<inter>A. F\<in>\<FF>}. \<exists>D\<in>{F\<inter>A. F\<in>\<FF>}. D\<subseteq>A\<^sub>a\<inter>B" 
    by auto
  ultimately have 
    baseCond: "{F\<inter>A. F\<in>\<FF>} {satisfies the filter base condition}"
    unfolding SatisfiesFilterBase_def by blast
  let ?F = "{A\<^sub>A\<in>Pow(X). (\<exists>D\<in>{F\<inter>A. F\<in>\<FF>}. D\<subseteq>A\<^sub>A)}"
  have rule: "{F\<inter>A. F\<in>\<FF>} \<subseteq> Pow(X) \<and>  {F\<inter>A. F\<in>\<FF>} \<noteq> \<emptyset> \<longrightarrow>
    ({F\<inter>A. F\<in>\<FF>} {is a base filter} {A\<^sub>A\<in>Pow(X). (\<exists>D\<in>{F\<inter>A. F\<in>\<FF>}. D\<subseteq>A\<^sub>A)})"
    using base_unique_filter_set1(1) by blast
  from assms(2) have p: "{F\<inter>A. F\<in>\<FF>} \<subseteq> Pow(X)" unfolding IsFilter_def 
    by auto
  with ne rule have base: "{F\<inter>A. F\<in>\<FF>} {is a base filter} ?F" by auto
  have "{F\<inter>A. F\<in>\<FF>}\<subseteq>Pow(X) \<and> ({F\<inter>A. F\<in>\<FF>} {satisfies the filter base condition})
      \<longrightarrow> \<Union>?F = X"
    using base_unique_filter_set3(2) by blast
  with p base baseCond have "?F {is a filter on} X" using basic_filter by auto
  moreover from assms(1,2) have "A\<in>?F" and "\<FF>\<subseteq>?F" unfolding IsFilter_def 
    by auto
  ultimately show "(?F {is a filter on} X) \<and> A \<in> ?F \<and> \<FF> \<subseteq> ?F" by auto
qed

text\<open>The convergence for filters is much easier concept to write. Given a topology
and a filter on the same underlying set, we can define convergence as containing
all the neighborhoods of the point.\<close>

definition (in topology0)
  FilterConverges ("_ \<rightarrow>\<^sub>F _" 50) where
  "\<FF>{is a filter on}\<Union>T  \<Longrightarrow> \<FF>\<rightarrow>\<^sub>Fx \<equiv>
  x\<in>\<Union>T \<and> ({U\<in>Pow(\<Union>T). x\<in>int(U)} \<subseteq> \<FF>)"
 
text\<open>The neighborhoods of a point form a filter that converges to that point.\<close>

lemma (in topology0) neigh_filter:
  assumes "x\<in>\<Union>T"
  defines "Neigh\<equiv>{U\<in>Pow(\<Union>T). x\<in>int(U)}"
  shows "Neigh {is a filter on}\<Union>T" and "Neigh \<rightarrow>\<^sub>F x"
proof-
  {
    fix A B
    assume p:"A\<in>Neigh" "B\<in>Neigh"
    have "A\<inter>B\<in>Neigh"
    proof-
      from p have "A\<inter>B\<in>Pow(\<Union>T)" using Neigh_def by auto
      moreover
      {from p have "x\<in>int(A)" "x\<in>int(B)" using Neigh_def by auto
      then have "x\<in>int(A)\<inter>int(B)" by auto
      moreover
      { have "int(A)\<inter>int(B)\<subseteq>A\<inter>B" using Top_2_L1 by auto
        moreover have "int(A)\<inter>int(B)\<in>T" 
          using Top_2_L2 topSpaceAssum IsATopology_def by blast
        ultimately have "int(A)\<inter>int(B)\<subseteq>int(A\<inter>B)" using Top_2_L5 by auto}
        ultimately have "x\<in>int(A\<inter>B)" by auto
      }
      ultimately show ?thesis using Neigh_def by auto
    qed
    }
  moreover
  {
    fix A B
    assume A: "A\<in>Neigh" and B: "B\<in>Pow(\<Union>T)" and sub: "A\<subseteq>B"
    from sub have "int(A)\<in>T" "int(A)\<subseteq>B" using Top_2_L2 Top_2_L1 
      by auto 
    then have "int(A)\<subseteq>int(B)" using Top_2_L5  by auto
    with A have "x\<in>int(B)" using Neigh_def by auto
    with B have "B\<in>Neigh" using Neigh_def by auto
    }
  moreover
  {
    assume "0\<in>Neigh"
    then have "x\<in>Interior(0,T)" using Neigh_def by auto
    then have "x\<in>0" using Top_2_L1 by auto
    then have "False" by auto
    }
  then have "0\<notin>Neigh" by auto
  moreover
  have "\<Union>T\<in>T" using topSpaceAssum IsATopology_def by auto
  then have "Interior(\<Union>T,T)=\<Union>T" using Top_2_L3 by auto
  with assms(1) have ab: "\<Union>T\<in>Neigh" unfolding Neigh_def by auto
  moreover have "Neigh\<subseteq>Pow(\<Union>T)" using Neigh_def by auto
  ultimately show "Neigh {is a filter on} \<Union>T" using IsFilter_def 
    by auto
  moreover from ab have "\<Union>Neigh=\<Union>T" unfolding Neigh_def by auto
  ultimately show "Neigh \<rightarrow>\<^sub>F x" using FilterConverges_def assms(1) Neigh_def by auto
qed

text\<open>Note that with the net we built in a previous result, it wasn't clear that
we could construct an actual net that converged to the given point without the
axiom of choice. With filters, there is no problem.

Another positive point of filters is due to the existence of filter basis.
If we have a basis for a filter, then the filter converges to a point iff
every neighborhood of that point contains a basic filter element.\<close>

theorem (in topology0) convergence_filter_base1:
  assumes "\<FF> {is a filter on} \<Union>T" and "C {is a base filter} \<FF>" and "\<FF> \<rightarrow>\<^sub>F x"
  shows "\<forall>U\<in>Pow(\<Union>T). x\<in>int(U) \<longrightarrow> (\<exists>D\<in>C. D\<subseteq>U)" and "x\<in>\<Union>T"
proof -
  { fix U
    assume "U\<subseteq>(\<Union>T)" and "x\<in>int(U)"
    with assms(1,3) have "U\<in>\<FF>" using FilterConverges_def by auto
    with assms(2) have "\<exists>D\<in>C. D\<subseteq>U" using basic_element_filter by blast
  } thus "\<forall>U\<in>Pow(\<Union>T). x\<in>int(U) \<longrightarrow> (\<exists>D\<in>C. D\<subseteq>U)" by auto
  from assms(1,3) show "x\<in>\<Union>T" using  FilterConverges_def by auto
qed

text\<open>A sufficient condition for a filter to converge to a point.\<close>

theorem (in topology0) convergence_filter_base2:
  assumes "\<FF> {is a filter on} \<Union>T" and "C {is a base filter} \<FF>"
    and "\<forall>U\<in>Pow(\<Union>T). x\<in>int(U) \<longrightarrow> (\<exists>D\<in>C. D\<subseteq>U)" and "x\<in>\<Union>T"
  shows "\<FF> \<rightarrow>\<^sub>F x"
proof-
  {
    fix U
    assume AS: "U\<in>Pow(\<Union>T)" "x\<in>int(U)"
    then obtain D where pD:"D\<in>C" and s:"D\<subseteq>U" using assms(3) by blast
    with assms(2) AS have "D\<in>\<FF>" and "D\<subseteq>U" and "U\<in>Pow(\<Union>T)" 
      using IsBaseFilter_def by auto
    with assms(1) have "U\<in>\<FF>" using IsFilter_def by auto
  }
  with assms(1,4) show ?thesis using FilterConverges_def by auto
qed

text\<open>A necessary and sufficient condition for a filter to converge to a point.\<close>

theorem (in topology0) convergence_filter_base_eq:
  assumes "\<FF> {is a filter on} \<Union>T" and "C {is a base filter} \<FF>"
  shows "(\<FF> \<rightarrow>\<^sub>F x) \<longleftrightarrow> ((\<forall>U\<in>Pow(\<Union>T). x\<in>int(U) \<longrightarrow> (\<exists>D\<in>C. D\<subseteq>U)) \<and> x\<in>\<Union>T)"
proof
  assume "\<FF> \<rightarrow>\<^sub>F x"
  with assms show "((\<forall>U\<in>Pow(\<Union>T). x\<in>int(U) \<longrightarrow> (\<exists>D\<in>C. D\<subseteq>U)) \<and> x\<in>\<Union>T)"
    using convergence_filter_base1 by simp  
  next 
  assume "(\<forall>U\<in>Pow(\<Union>T). x\<in>int(U) \<longrightarrow> (\<exists>D\<in>C. D\<subseteq>U)) \<and> x\<in>\<Union>T"
  with assms show "\<FF> \<rightarrow>\<^sub>F x" using convergence_filter_base2
    by auto
qed

end
