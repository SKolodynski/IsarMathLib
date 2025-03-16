(*
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2025  Slawomir Kolodynski

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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section\<open>Uniformity defined by a a collection of pseudometrics\<close>

theory MetricUniform_ZF imports FinOrd_ZF_1 MetricSpace_ZF

begin

text\<open>Note: this theory is a work in progress. The approach taken is probably not the
  right one. The right approach is through the notion of least upper bound of a collection
  of uniformities.

  In the \<open>MetricSpace_ZF\<close> we show how a single (ordered loop valued) pseudometric
  defines a uniformity. In this theory we extend this to the situation where we have
  an arbitrary collection of pseudometrics, all defined on the the same set $X$ and valued
  in an ordered loop $L$. Since real numbers form an ordered loop all results proven in
  this theory are true for the standard real-valued pseudometrics. \<close>

subsection\<open>From collection of pseudometrics to fundamental system of entourages\<close>

text\<open>Suppose $\mathcal{M}$ is a collection of (an ordered loop valued) pseudometrics on $X$,
  i.e. $d:X\times X\rightarrow L^+$ is a pseudometric for every $d\in \mathcal{M}$.
  Then, for each $d\in \mathcal{M}$ the sets $\{ d^{-1}(\{c\in L^+: c\leq b\}): b \in L_+ \}$
  form a fundamental system of entourages (see \<open>MetricSpace_ZF\<close>). \<close>

text\<open>The next two definitions describe the way a common fundamental system of entourages 
  for $\mathcal{M}$ is constructed. First we take finite subset $M$ of $\mathcal{M}$.
  Then we choose $f:M\rightarrow L_+$. This way for each $d\in M$
  the value $f(d)$ is a positive element of $L$ and 
  $\{d^{-1}(\{c\in L^+: c\leq f(d)\}): d\in M\}$ is a finite collection of 
  subsets of $X\times X$. Then we take intersections of such finite
  collections as $M$ varies over $\mathcal{M}$ and $f$ varies over all possible functions mapping
  $M$ to $L_+$. To simplify notation for this construction we split it into two steps. 
  In the first step we define a collection of finite intersections resulting from 
  choosing a finite set of pseudometrics $M$, $f:M\rightarrow L_+$ and varying 
  the selector function $f$ over the space of functions mapping $M$ to the set of 
  positive elements of $L$. \<close>

definition
  "UniformGaugeSets(X,L,A,r,M) \<equiv> 
  {(\<Inter>d\<in>M. d-``({c\<in>Nonnegative(L,A,r). \<langle>c,f`(d)\<rangle> \<in> r})). f\<in>M\<rightarrow>PositiveSet(L,A,r)}"
  
text\<open>In the second step we collect all uniform gauge sets defined above 
  as parameter $M$ vary over all nonempty finite subsets of $\mathcal{M}$. 
  This is the collection of sets that we will show forms a fundamental system of entourages.\<close>

definition
  "UniformGauges(X,L,A,r,\<M>) \<equiv> \<Union>M\<in>FinPow(\<M>)\<setminus>{\<emptyset>}. UniformGaugeSets(X,L,A,r,M)"

text\<open>The context \<open>muliple_pmetric\<close> is very similar to the \<open>pmetric_space\<close> context
  except that rather than fixing a single pseudometric $d$ we fix a 
  collection of pseudometrics $\mathcal{M}$. That forces the notation for
  \<open>disk\<close>, topology, interior and closure to depend on the pseudometric $d$. \<close>

locale muliple_pmetric = loop1 +
  fixes \<M> and X
  assumes mpmetricAssm: "\<forall>d\<in>\<M>. IsApseudoMetric(d,X,L,A,r)"
  fixes disk
  defines disk_def [simp]: "disk(d,c,R) \<equiv> Disk(X,d,r,c,R)"
  fixes pmettop ("\<tau>") 
  defines pmettop [simp]: "\<tau>(d) \<equiv> MetricTopology(X,L,A,r,d)"
  fixes interior ("int")
  defines interior_def [simp]: "int(d,D) \<equiv> Interior(D,\<tau>(d))"
  fixes cl
  defines cl_def [simp]: "cl(d,D) \<equiv> Closure(D,\<tau>(d))"

text\<open>Analogously what is done in the \<open>pmetric_space\<close> context 
  we will write \<open>UniformGauges(X,L,A,r,\<M>)\<close> as \<open>\<BB>\<close> in the \<open>muliple_pmetric\<close> context.\<close>

abbreviation (in muliple_pmetric) mgauge ("\<BB>") where "\<BB> \<equiv> UniformGauges(X,L,A,r,\<M>)"

text\<open>The next lemma just shows the definition of $\mathfrak{B}$ in notation 
  used in the \<open>muliple_pmetric\<close>. \<close>

lemma (in muliple_pmetric) mgauge_def_alt: shows 
  "\<BB> = (\<Union>M\<in>FinPow(\<M>)\<setminus>{\<emptyset>}. {(\<Inter>d\<in>M. d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)})). f\<in>M\<rightarrow>L\<^sub>+})"
  unfolding UniformGaugeSets_def UniformGauges_def by simp

text\<open>$\mathfrak{B}$ consists of (finite) intersections of sets of the
  form $d^{-1}(\{c\in L^+:c\leq f(d)\})$ where $f:M\rightarrow L_+$
  some finite subset $M\subseteq \mathcal{M}$.
  More precisely, if $M$ is a nonempty finite subset of $\mathcal{M}$ and $f$ maps 
  $M$ to the positive set of the loop $L$, then the set 
  $\bigcap_{d\in M} d^{-1}(\{c\in L^+:c\leq f(d)\}$ is in $\mathfrak{B}$.\<close>

lemma (in muliple_pmetric) mgauge_finset_fun:
  assumes "M\<in>FinPow(\<M>)" "M\<noteq>\<emptyset>" "f:M\<rightarrow>L\<^sub>+"
  shows "(\<Inter>d\<in>M. d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)})) \<in> \<BB>"
  using assms mgauge_def_alt by auto

text\<open>If $d$ is one of the pseudometrics from $\mathcal{M}$ then theorems
  proven in \<open>pmetric_space\<close> can are valid. \<close>

lemma (in muliple_pmetric) pmetric_space_valid_in_mpm: 
  assumes "d\<in>\<M>" shows "pmetric_space(L,A,r,d,X)" 
proof
  from assms mpmetricAssm show "IsApseudoMetric(d,X,L,A,r)" by simp
qed

text\<open>If $d$ is member of any finite subset of $\mathcal{M}$ then 
  $d$ maps $X\times X$ to the nonnegative set of the ordered loop $L$.\<close>

lemma (in muliple_pmetric) each_pmetric_map:
  assumes "M\<in>FinPow(\<M>)" and "d\<in>M" shows "d: X\<times>X \<rightarrow> L\<^sup>+"
    using assms pmetric_space_valid_in_mpm pmetric_space.pmetric_properties(1)
    unfolding FinPow_def by auto

text\<open>Members of the uniform gauge defined by multiple pseudometrics 
  are subsets of $X\times X$ i.e. relations on $X$. \<close>

lemma (in muliple_pmetric) muniform_gauge_relations:
  assumes "B\<in>\<BB>" shows "B\<subseteq>X\<times>X"
proof -
  from assms obtain M f where "M\<in>FinPow(\<M>)" and
    I: "B = (\<Inter>d\<in>M. d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)}))"
    using mgauge_def_alt by auto
  { fix d assume "d\<in>M"
    with \<open>M\<in>FinPow(\<M>)\<close> have "d: X\<times>X \<rightarrow> L\<^sup>+"
      using each_pmetric_map by simp
    then have "d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)}) \<subseteq> X\<times>X" using func1_1_L15 by auto
  } with I show ?thesis using inter_subsets_subset by simp
qed

text\<open>Suppose $M_1$ is a subset of $M$ and $\mathcal{M}$.
  $f_1,f$ map $M_1$ and $M$, resp. to $L_+$ and $f\leq f_1$ on $M_1$.
  Then the set $\bigcap_{d\in M} d^{-1}(\{y \in L_+: y\leq f(d)\})$
  is included in the set $\bigcap_{d\in M_1} d^{-1}(\{y \in L_+: y\leq f_1(d)\})$. \<close>

lemma (in muliple_pmetric) fun_inter_vimage_mono:
  assumes "M\<^sub>1\<subseteq>\<M>" "M\<^sub>1\<subseteq>M" "M\<^sub>1\<noteq>\<emptyset>" "f\<^sub>1:M\<^sub>1\<rightarrow>L\<^sub>+" "f:M\<rightarrow>L\<^sub>+" and 
    "\<forall>d\<in>M\<^sub>1. f`(d)\<lsq>f\<^sub>1`(d)"
  shows
     "(\<Inter>d\<in>M. d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)})) \<subseteq> (\<Inter>d\<in>M\<^sub>1. d-``({c\<in>L\<^sup>+. c\<lsq>f\<^sub>1`(d)}))"
proof -
  let ?L = "(\<Inter>d\<in>M. d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)}))"
  let ?R = "(\<Inter>d\<in>M\<^sub>1. d-``({c\<in>L\<^sup>+. c\<lsq>f\<^sub>1`(d)}))"
  from assms(2,3) have I: "?L \<subseteq> (\<Inter>d\<in>M\<^sub>1. d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)}))"
    using inter_index_mono by simp
  from assms(1,6) have 
    "\<forall>d\<in>M\<^sub>1. (d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)})) \<subseteq> d-``({c\<in>L\<^sup>+. c\<lsq>f\<^sub>1`(d)})" 
    using pmetric_space_valid_in_mpm pmetric_space.uniform_gauge_mono
      by force
  with assms(2) have  "(\<Inter>d\<in>M\<^sub>1. d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)})) \<subseteq> ?R" by force
  with I show "?L\<subseteq>?R" by (rule subset_trans)
qed

text\<open>For any two sets $B_1,B_2$ in $\mathfrak{B}$ there exist a third one
  that is contained in both. \<close>

lemma (in muliple_pmetric) mgauge_1st_cond:
  assumes "r {down-directs} L\<^sub>+" "B\<^sub>1\<in>\<BB>" "B\<^sub>2\<in>\<BB>"
  shows "\<exists>B\<in>\<BB>. B\<subseteq>B\<^sub>1\<inter>B\<^sub>2" 
proof -
  from assms(2,3) obtain M\<^sub>1 f\<^sub>1 M\<^sub>2 f\<^sub>2 where "M\<^sub>1\<noteq>\<emptyset>" "M\<^sub>2\<noteq>\<emptyset>" and
  I: "M\<^sub>1\<in>FinPow(\<M>)" "M\<^sub>2\<in>FinPow(\<M>)" "f\<^sub>1:M\<^sub>1\<rightarrow>L\<^sub>+" "f\<^sub>2:M\<^sub>2\<rightarrow>L\<^sub>+" and  
  II: "B\<^sub>1 = (\<Inter>d\<in>M\<^sub>1. d-``({c\<in>L\<^sup>+. c\<lsq>f\<^sub>1`(d)}))" "B\<^sub>2 = (\<Inter>d\<in>M\<^sub>2. d-``({c\<in>L\<^sup>+. c\<lsq>f\<^sub>2`(d)}))"
    using mgauge_def_alt by auto
  let ?M\<^sub>3 = "M\<^sub>1\<union>M\<^sub>2"  
  from assms(1) have "IsDownDirectedSet(L\<^sub>+,r)" 
    using down_directs_directed by simp
  with I have 
    "\<exists>f\<^sub>3\<in>?M\<^sub>3\<rightarrow>L\<^sub>+. (\<forall>d\<in>M\<^sub>1. \<langle>f\<^sub>3`(d),f\<^sub>1`(d)\<rangle>\<in>r) \<and> (\<forall>d\<in>M\<^sub>2. \<langle>f\<^sub>3`(d),f\<^sub>2`(d)\<rangle>\<in>r)"
    using two_fun_low_bound by simp
  then obtain f\<^sub>3 where "f\<^sub>3:?M\<^sub>3\<rightarrow>L\<^sub>+" and
    III: "\<forall>d\<in>M\<^sub>1. f\<^sub>3`(d)\<lsq>f\<^sub>1`(d)" "\<forall>d\<in>M\<^sub>2. f\<^sub>3`(d)\<lsq>f\<^sub>2`(d)"
      by auto
  let ?B\<^sub>3 = "\<Inter>d\<in>?M\<^sub>3. d-``({c\<in>L\<^sup>+. c\<lsq>f\<^sub>3`(d)})"
  from I(1,2) \<open>M\<^sub>1\<noteq>\<emptyset>\<close> \<open>f\<^sub>3:?M\<^sub>3\<rightarrow>L\<^sub>+\<close> have "?B\<^sub>3\<in>\<BB>"
    using union_finpow mgauge_def_alt by auto
  moreover have "?B\<^sub>3\<subseteq>B\<^sub>1\<inter>B\<^sub>2"
  proof - 
    from I(1,2) have "M\<^sub>1\<subseteq>\<M>" "M\<^sub>1\<subseteq>?M\<^sub>3" "M\<^sub>2\<subseteq>\<M>" "M\<^sub>2\<subseteq>?M\<^sub>3"
      unfolding FinPow_def by auto
    with \<open>M\<^sub>1\<noteq>\<emptyset>\<close> \<open>M\<^sub>2\<noteq>\<emptyset>\<close> I(3,4) II \<open>f\<^sub>3:?M\<^sub>3\<rightarrow>L\<^sub>+\<close> III  
    have "?B\<^sub>3\<subseteq>B\<^sub>1" and "?B\<^sub>3\<subseteq>B\<^sub>2" using fun_inter_vimage_mono by simp_all
    thus "?B\<^sub>3\<subseteq>B\<^sub>1\<inter>B\<^sub>2" by auto
  qed
  ultimately show "\<exists>B\<in>\<BB>. B\<subseteq>B\<^sub>1\<inter>B\<^sub>2" by (rule witness_exists)
qed

text\<open>Sets in $\mathfrak{B}$ contain the diagonal and are symmetric,
  hence contain a symmetric subset from $\mathfrak{B}$.\<close>

lemma (in muliple_pmetric) mgauge_2nd_and_3rd_cond: assumes "B\<in>\<BB>" 
  shows "id(X)\<subseteq>B" "B = converse(B)" "\<exists>B\<^sub>2\<in>\<BB>. B\<^sub>2 \<subseteq> converse(B)" 
proof -
  from assms obtain M f where "M\<in>FinPow(\<M>)" "M\<noteq>\<emptyset>" "f:M\<rightarrow>L\<^sub>+" and
    I: "B = (\<Inter>d\<in>M. d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)}))"
    using mgauge_def_alt by auto
  { fix d assume "d\<in>M"
    let ?B\<^sub>d = "d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)})"
    from \<open>d\<in>M\<close> \<open>f:M\<rightarrow>L\<^sub>+\<close> \<open>M\<in>FinPow(\<M>)\<close> have
      "pmetric_space(L,A,r,d,X)" and "?B\<^sub>d \<in> UniformGauge(X,L,A,r,d)"
      unfolding FinPow_def UniformGauge_def 
      using apply_funtype pmetric_space_valid_in_mpm by auto
    then have "id(X)\<subseteq>?B\<^sub>d" and "?B\<^sub>d = converse(?B\<^sub>d)" 
      using pmetric_space.gauge_2nd_cond pmetric_space.gauge_symmetric 
      by simp_all
  } with I \<open>M\<noteq>\<emptyset>\<close> show "id(X)\<subseteq>B" and "B = converse(B)" by auto
  from assms \<open>B = converse(B)\<close> show "\<exists>B\<^sub>2\<in>\<BB>. B\<^sub>2 \<subseteq> converse(B)"
    by auto
qed

text\<open>$\mathfrak{B}$ is a subset of the power set of $X\times X$.\<close>

lemma (in muliple_pmetric) mgauge_5thCond: shows "\<BB>\<subseteq>Pow(X\<times>X)"
  using muniform_gauge_relations by auto

text\<open>If $\mathcal{M}$ and $L_+$ are nonempty then $\mathfrak{B}$ is also nonempty.\<close>

lemma (in muliple_pmetric) mgauge_6thCond:
  assumes "\<M>\<noteq>\<emptyset>" and "L\<^sub>+\<noteq>\<emptyset>" shows "\<BB>\<noteq>\<emptyset>" 
proof -
  from assms obtain M y where "M\<in>FinPow(\<M>)" "M\<noteq>\<emptyset>" and "y\<in>L\<^sub>+"
    using finpow_nempty_nempty by blast
  from \<open>y\<in>L\<^sub>+\<close> have "ConstantFunction(M,y):M\<rightarrow>L\<^sub>+" using func1_3_L1 by simp
  with \<open>M\<in>FinPow(\<M>)\<close> \<open>M\<noteq>\<emptyset>\<close> show "\<BB>\<noteq>\<emptyset>" using mgauge_finset_fun by auto
qed

text\<open>If the loop order is halfable then for every set $B_1\in \mathfrak{B}$
  there is another set $B_2\in \mathfrak{B}$ such that $B_2\circ B_2 \subseteq B_1$.\<close>

lemma (in muliple_pmetric) mgauge_4thCond: 
  assumes "IsHalfable(L,A,r)" "B\<^sub>1\<in>\<BB>" shows "\<exists>B\<^sub>2\<in>\<BB>. B\<^sub>2 O B\<^sub>2 \<subseteq> B\<^sub>1"
proof -
  from assms(2) obtain M f\<^sub>1 where "M\<in>FinPow(\<M>)" "M\<noteq>\<emptyset>" "f\<^sub>1:M\<rightarrow>L\<^sub>+" and
    I: "B\<^sub>1 = (\<Inter>d\<in>M. d-``({c\<in>L\<^sup>+. c\<lsq>f\<^sub>1`(d)}))"
    using mgauge_def_alt by auto
  from assms(1) \<open>f\<^sub>1:M\<rightarrow>L\<^sub>+\<close> have "\<forall>d\<in>M. \<exists>b\<^sub>2\<in>L\<^sub>+. b\<^sub>2\<ra>b\<^sub>2 \<lsq> f\<^sub>1`(d)"
    using apply_funtype unfolding IsHalfable_def by simp
  with \<open>M\<in>FinPow(\<M>)\<close> have "\<exists>f\<^sub>2\<in>M\<rightarrow>L\<^sub>+. \<forall>d\<in>M. f\<^sub>2`(d) \<ra> f\<^sub>2`(d) \<lsq> f\<^sub>1`(d)"
    unfolding FinPow_def using finite_choice_fun by auto
  then obtain f\<^sub>2 where "f\<^sub>2\<in>M\<rightarrow>L\<^sub>+" and II: "\<forall>d\<in>M. f\<^sub>2`(d) \<ra> f\<^sub>2`(d) \<lsq> f\<^sub>1`(d)"
    by auto
  let ?B\<^sub>2 = "\<Inter>d\<in>M. d-``({c\<in>L\<^sup>+. c\<lsq>f\<^sub>2`(d)})" 
  { fix d assume "d\<in>M"
    let ?A\<^sub>2 = "d-``({c\<in>L\<^sup>+. c\<lsq>f\<^sub>2`(d)})"
    from \<open>d\<in>M\<close> \<open>M\<in>FinPow(\<M>)\<close> have "pmetric_space(L,A,r,d,X)"
      unfolding FinPow_def using pmetric_space_valid_in_mpm by auto 
    with \<open>f\<^sub>2\<in>M\<rightarrow>L\<^sub>+\<close> \<open>d\<in>M\<close> II have "?A\<^sub>2 O ?A\<^sub>2 \<subseteq> d-``({c\<in>L\<^sup>+. c\<lsq>f\<^sub>1`(d)})"
      using apply_funtype pmetric_space.half_vimage_square by simp
  } 
  with \<open>M\<noteq>\<emptyset>\<close> I have "?B\<^sub>2 O ?B\<^sub>2 \<subseteq> B\<^sub>1" using square_incl_product by simp
  with \<open>M\<in>FinPow(\<M>)\<close> \<open>M\<noteq>\<emptyset>\<close> \<open>f\<^sub>2\<in>M\<rightarrow>L\<^sub>+\<close> show ?thesis
    using mgauge_finset_fun by auto
qed

text\<open>If $\mathcal{M}$ is a nonempty collection of pseudometrics on a nonempty set $X$
   valued in loop $L$ partially ordered by relation $r$ such that the set of positive elements 
   $L_+$ is nonempty, $r$ down directs $L_+$ and $r$ is halfable on $L$,then
   $\mathfrak{B}$ is a fundamental system of entourages in $X$ hence its supersets 
  form a uniformity on $X$ and hence those supersets define a topology on $X$ \<close>

lemma (in muliple_pmetric) mmetric_gauge_base:
  assumes "X\<noteq>\<emptyset>" "\<M>\<noteq>\<emptyset>" "L\<^sub>+\<noteq>\<emptyset>" "r {down-directs} L\<^sub>+" "IsHalfable(L,A,r)" 
  shows
    "\<BB> {is a uniform base on} X"
    "Supersets(X\<times>X,\<BB>) {is a uniformity on} X"
    "UniformTopology(Supersets(X\<times>X,\<BB>),X) {is a topology}"
    "\<Union>UniformTopology(Supersets(X\<times>X,\<BB>),X) = X"
  using assms mgauge_1st_cond mgauge_2nd_and_3rd_cond mgauge_4thCond 
    mgauge_5thCond mgauge_6thCond uniformity_base_is_base uniform_top_is_top
  unfolding IsUniformityBaseOn_def by simp_all

subsection\<open>An alternative approach\<close>

text\<open>The formula for defining the fundamental system of entourages from a collection
  of pseudometrics given in lemma \<open>mgauge_def_alt\<close> is a bit different than the standard one
  found in the literature on real-valued pseudometrics. In this section we explore another
  alternative to defining fundamental system of entourages common to a collection of pseudometrics.\<close>

text\<open>Any pseudometrics $d:X\times X\rightarrow L^+$ defines a fundamental system of entourages
  on $X$ by the formula $\mathcal{B}(d) = \{ d^{-1}(\{c\in L^+: c\leq b\}): b \in L_+ \}$
  (see theorem \<open>metric_gauge_base\<close> in \<open>Metric_Space_ZF\<close> theory. \<close>

definition (in muliple_pmetric) gauge ("\<B>") where 
  "\<B>(d) \<equiv> {d-``({c\<in>L\<^sup>+. c\<lsq>b}). b\<in>L\<^sub>+}"

text\<open>Every subset $M$ of $\mathcal{M}$ defines a collection of fundamental systems
  of entourages $\mathfrak{M}(M) = \{\mathcal{B}(d): d\in M\}$. \<close>

definition (in muliple_pmetric) gauge_set ("\<MM>") where
  "\<MM>(M) = {\<B>(d). d\<in>M}" 

text\<open> To get a fundamental system of entourages common to all pseudometrics
  $d\in \mathcal{M}$ we take intersections of sets selected from finite nonempty 
  subcollections of the collection of all fundamental systems of entourages defined by pseudometrics 
  $d\in \mathcal{M}$. To distinguish it from the common fundamental system of entourages
  defined in the previous section we denote that $\mathfrak{B}_1$. \<close>

definition (in muliple_pmetric) mgauge_alt ("\<BB>\<^sub>1") where
  "\<BB>\<^sub>1 \<equiv> \<Union>M\<in>FinPow(\<M>)\<setminus>{\<emptyset>}. {(\<Inter>B\<in>\<MM>(M). g`(B)). g\<in>ChoiceFunctions(\<MM>(M))}"

text\<open>If $M$ is a nonempty finite subset of $mathcal{M}$ then we have
  inclusion $\{\bigcap_{B\in \mathfrak{M}(M)} g(B) : g \in \mathcal(C)(\mathfrak{M}(M)\} \subseteq
  \{\bigcap_{d\in M} d^{-1}(\{c\in L^+: c\leq f(d)\}:\  f:M\rightarrow L_+\})$.
  where $\mathcal{C}(\mathcal{A})$ is the set of choice functions for a collection $\mathcal{A}$
  (see theory \<open>Cardinal_ZF\<close> for definition of choice function for a collection. \<close>

lemma (in muliple_pmetric) mgauge_alt_mgauge1:
  assumes "M\<in>FinPow(\<M>)" "M\<noteq>\<emptyset>"
  defines "\<C> \<equiv> ChoiceFunctions(\<MM>(M))"
  shows "{(\<Inter>B\<in>\<MM>(M). g`(B)). g\<in>\<C>} \<subseteq> {(\<Inter>d\<in>M. d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)})). f\<in>M\<rightarrow>L\<^sub>+}"
proof -
  let ?L = "{(\<Inter>B\<in>\<MM>(M). g`(B)). g\<in>\<C>}" 
  let ?R = "{(\<Inter>d\<in>M. d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)})). f\<in>M\<rightarrow>L\<^sub>+}"
  from assms(1,2) have "Finite(\<MM>(M))" and "\<MM>(M)\<noteq>\<emptyset>" 
    unfolding gauge_set_def FinPow_def using fin_rep_fin by simp_all
  { fix U assume "U \<in> ?L"
    then obtain g where "g\<in>\<C>" and "U=(\<Inter>B\<in>\<MM>(M). g`(B))" by auto
    from assms(3) \<open>g\<in>\<C>\<close> have "g:(\<MM>(M))\<rightarrow>(\<Union>\<MM>(M))" and 
      I: "\<forall>B\<in>\<MM>(M). g`(B) \<in> B"
      unfolding ChoiceFunctions_def by auto
    { fix d assume "d\<in>M"
      then have "\<B>(d) \<in> \<MM>(M)" and II: "\<B>(d) = {d-``({c\<in>L\<^sup>+. c\<lsq>b}). b\<in>L\<^sub>+}"
        unfolding gauge_set_def gauge_def by auto
      from I \<open>\<B>(d) \<in> \<MM>(M)\<close> have "g`(\<B>(d)) \<in> \<B>(d)" by simp
      with II obtain b where 
        "b\<in>L\<^sub>+" and "g`(\<B>(d)) = d-``({c\<in>L\<^sup>+. c\<lsq>b})"
        by auto
      hence "\<exists>b\<in>L\<^sub>+. g`(\<B>(d)) = d-``({c\<in>L\<^sup>+. c\<lsq>b})" by auto
    } hence "\<forall>d\<in>M. \<exists>b\<in>L\<^sub>+. g`(\<B>(d)) = d-``({c\<in>L\<^sup>+. c\<lsq>b})"
        by auto
    with assms(1) have 
      "\<exists>f\<in>M\<rightarrow>L\<^sub>+. \<forall>d\<in>M. g`(\<B>(d)) = d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)})"
      unfolding FinPow_def using finite_choice_fun by auto
    then obtain f where 
      "f:M\<rightarrow>L\<^sub>+" and II: "\<forall>d\<in>M. g`(\<B>(d)) = d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)})"
      by auto
    have "U = (\<Inter>d\<in>M. d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)}))"
    proof 
      { fix p assume "p\<in>U"
        with \<open>U=(\<Inter>B\<in>\<MM>(M). g`(B))\<close> have "\<forall>B\<in>\<MM>(M). p\<in>g`(B)" by auto
        { fix d assume "d\<in>M"
          then have "\<B>(d) \<in> \<MM>(M)" unfolding gauge_set_def by auto
          with \<open>\<forall>B\<in>\<MM>(M). p\<in>g`(B)\<close> have "p\<in>g`(\<B>(d))" by simp
          with II \<open>d\<in>M\<close> have "p \<in> d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)})"
            by simp
        } hence "\<forall>d\<in>M. p \<in> d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)})" by simp
        with assms(2) have "p\<in>(\<Inter>d\<in>M. d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)}))" 
            by auto
      } thus "U \<subseteq> (\<Inter>d\<in>M. d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)}))" by auto
      { fix p assume "p \<in> (\<Inter>d\<in>M. d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)}))"
        hence III: "\<forall>d\<in>M. p \<in> d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)})" by auto
        { fix B assume "B\<in>\<MM>(M)"
          then have "B \<in> {\<B>(d). d\<in>M}" unfolding gauge_set_def 
            by simp
          then obtain d where "d\<in>M" and "B=\<B>(d)"
            unfolding gauge_def by auto
          from \<open>d\<in>M\<close> II have "g`(\<B>(d)) = d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)})"
            by simp
          with III \<open>d\<in>M\<close> have "p \<in> g`(\<B>(d))" by simp
          with \<open>B=\<B>(d)\<close> have "p\<in>g`(B)" by simp 
        } hence "\<forall>B\<in>\<MM>(M). p\<in>g`(B)" by simp
        with \<open>\<MM>(M)\<noteq>\<emptyset>\<close> \<open>U=(\<Inter>B\<in>\<MM>(M). g`(B))\<close> have "p\<in>U" by auto
      } thus "(\<Inter>d\<in>M. d-``({c\<in>L\<^sup>+. c\<lsq>f`(d)})) \<subseteq> U" by auto
    qed
    with \<open>f:M\<rightarrow>L\<^sub>+\<close> have "U\<in>?R" by auto
  } thus "?L\<subseteq>?R" by auto      
qed  
end