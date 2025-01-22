(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2020 - 2024 Slawomir Kolodynski

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

section \<open>Metric spaces\<close>

theory MetricSpace_ZF imports Topology_ZF_1 OrderedLoop_ZF Lattice_ZF UniformSpace_ZF
begin

text\<open>A metric space is a set on which a distance between points is defined as a function
  $d:X \times X \to [0,\infty)$. With this definition each metric space is a topological space 
  which is paracompact and Hausdorff ($T_2$), hence normal (in fact even perfectly normal).\<close>

subsection\<open> Pseudometric - definition and basic properties \<close>

text\<open>A metric on $X$ is usually defined as a function $d:X \times X \to [0,\infty)$ that satisfies
  the conditions $d(x,x) = 0$, $d(x, y) = 0 \Rightarrow  x = y$ (identity of indiscernibles), 
  $d(x, y)  = d(y, x)$ (symmetry) and $d(x, y) \le d(x, z) + d(z, y)$ (triangle inequality) 
  for all $x,y \in X$.  Here we are going to be a bit more general and define metric and 
  pseudo-metric as a function valued in an ordered loop. \<close>

text\<open> First we define a pseudo-metric, which has the axioms of a metric, but without the second part
  of the identity of indiscernibles. In our definition \<open>IsApseudoMetric\<close> is a predicate on five sets: the function $d$, 
  the set $X$ on which the metric is defined, the loop carrier $G$, the loop operation $A$ 
  and the order $r$ on $G$.\<close>

definition 
  "IsApseudoMetric(d,X,G,A,r) \<equiv> d:X\<times>X \<rightarrow> Nonnegative(G,A,r) 
    \<and> (\<forall>x\<in>X. d`\<langle>x,x\<rangle> = TheNeutralElement(G,A))
    \<and> (\<forall>x\<in>X.\<forall>y\<in>X. d`\<langle>x,y\<rangle> = d`\<langle>y,x\<rangle>)
    \<and> (\<forall>x\<in>X.\<forall>y\<in>X.\<forall>z\<in>X. \<langle>d`\<langle>x,z\<rangle>, A`\<langle>d`\<langle>x,y\<rangle>,d`\<langle>y,z\<rangle>\<rangle>\<rangle> \<in> r)"

text\<open>We add the full axiom of identity of indiscernibles to the definition of a pseudometric
  to get the definition of metric.\<close>

definition 
  "IsAmetric(d,X,G,A,r) \<equiv> 
    IsApseudoMetric(d,X,G,A,r) \<and> (\<forall>x\<in>X.\<forall>y\<in>X. d`\<langle>x,y\<rangle> = TheNeutralElement(G,A) \<longrightarrow> x=y)"

text\<open>A disk is defined as set of points located less than the radius from the center.\<close>

definition "Disk(X,d,r,c,R) \<equiv> {x\<in>X. \<langle>d`\<langle>c,x\<rangle>,R\<rangle> \<in> StrictVersion(r)}"

text\<open>We define \<open>metric topology\<close> as consisting of unions of open disks.\<close>

definition
  "MetricTopology(X,L,A,r,d) \<equiv> {\<Union>\<A>. \<A> \<in> Pow(\<Union>c\<in>X. {Disk(X,d,r,c,R). R\<in>PositiveSet(L,A,r)})}"

text\<open>Next we define notation for metric spaces. We will reuse the additive notation defined in 
  the \<open>loop1\<close> locale adding only the assumption about $d$ being a pseudometric and notation
  for a disk centered at $c$ with radius $R$.
  Since for many theorems it is sufficient to assume the pseudometric axioms we will
  assume in this context that the sets $d,X,L,A,r$ form a pseudometric raher than a metric.
  In the \<open>pmetric_space\<close> context $\tau$ denotes the topology defined by the metric $d$. 
  Analogously to the notation defined in the \<open>topology0\<close> context \<open>int(A)\<close>,
  \<open>cl(A)\<close>, \<open>\<partial>A\<close> will denote the interior, closure and boundary of the set $A$
  with respect to the metric topology. \<close>

locale pmetric_space =  loop1 +
  fixes d and X 
  assumes pmetricAssum: "IsApseudoMetric(d,X,L,A,r)"
  fixes disk
  defines disk_def [simp]: "disk(c,R) \<equiv> Disk(X,d,r,c,R)"
  fixes pmettop ("\<tau>") 
  defines pmettop [simp]: "\<tau> \<equiv> MetricTopology(X,L,A,r,d)"
  fixes interior ("int")
  defines interior_def [simp]: "int(D) \<equiv> Interior(D,\<tau>)"
  fixes cl
  defines cl_def [simp]: "cl(D) \<equiv> Closure(D,\<tau>)"
 

text\<open> The next lemma shows the definition of the pseudometric in the notation used in the 
  \<open>pmetric_space\<close> context.\<close>

lemma (in pmetric_space) pmetric_properties: shows 
  "d: X\<times>X \<rightarrow> L\<^sup>+"
  "\<forall>x\<in>X. d`\<langle>x,x\<rangle> = \<zero>"
  "\<forall>x\<in>X.\<forall>y\<in>X. d`\<langle>x,y\<rangle> = d`\<langle>y,x\<rangle>"
  "\<forall>x\<in>X.\<forall>y\<in>X.\<forall>z\<in>X. d`\<langle>x,z\<rangle> \<lsq> d`\<langle>x,y\<rangle> \<ra> d`\<langle>y,z\<rangle>"
  using pmetricAssum unfolding IsApseudoMetric_def by auto

text\<open>The values of the metric are in the in the nonnegative set of the loop, 
  hence in the loop.\<close>

lemma (in pmetric_space) pmetric_loop_valued: assumes "x\<in>X" "y\<in>X"
  shows "d`\<langle>x,y\<rangle> \<in> L\<^sup>+" "d`\<langle>x,y\<rangle> \<in> L"
proof -
  from assms show "d`\<langle>x,y\<rangle> \<in> L\<^sup>+" using pmetric_properties(1) apply_funtype
    by simp
  then show "d`\<langle>x,y\<rangle> \<in> L" using Nonnegative_def by auto
qed
  
text\<open>The definition of the disk in the notation used in the \<open>pmetric_space\<close> context:\<close>

lemma (in pmetric_space) disk_definition: shows "disk(c,R) = {x\<in>X. d`\<langle>c,x\<rangle> \<ls> R}"
proof -
  have "disk(c,R) = Disk(X,d,r,c,R)" by simp
  then have "disk(c,R) = {x\<in>X. \<langle>d`\<langle>c,x\<rangle>,R\<rangle> \<in> StrictVersion(r)}" 
    unfolding Disk_def by simp
  moreover have "\<forall>x\<in>X. \<langle>d`\<langle>c,x\<rangle>,R\<rangle> \<in> StrictVersion(r) \<longleftrightarrow> d`\<langle>c,x\<rangle> \<ls> R"
    using def_of_strict_ver by simp
  ultimately show ?thesis by auto
qed

text\<open>If the radius is positive then the center is in disk.\<close>

lemma (in pmetric_space) center_in_disk: assumes "c\<in>X" and "R\<in>L\<^sub>+" shows "c \<in> disk(c,R)"
  using pmetricAssum assms IsApseudoMetric_def PositiveSet_def disk_definition by simp
  
text\<open>A technical lemma that allows us to shorten some proofs: if $c$ is an element
  of $X$ and $x$ is in disk with center $c$ and radius $R$ then $R$ is a positive element of 
  $L$ and $-d(x,y)+R$ is in the set of positive elements of the loop. \<close>

lemma (in pmetric_space) radius_in_loop: assumes "c\<in>X" and "x \<in> disk(c,R)"
  shows "R\<in>L" "\<zero>\<ls>R" "R\<in>L\<^sub>+" "(\<rm>d`\<langle>c,x\<rangle> \<ad> R) \<in> L\<^sub>+"
proof -
  from assms(2) have "x\<in>X" and "d`\<langle>c,x\<rangle> \<ls> R" using disk_definition by auto
  with assms(1) show "\<zero>\<ls>R" using pmetric_properties(1) apply_funtype 
      nonneg_definition loop_strict_ord_trans by blast
  then show "R\<in>L" and "R\<in>L\<^sub>+" using posset_definition PositiveSet_def by auto
  from \<open>d`\<langle>c,x\<rangle> \<ls> R\<close> show "(\<rm>d`\<langle>c,x\<rangle> \<ad> R) \<in> L\<^sub>+"
    using ls_other_side(2) by simp
qed

text\<open>If a point $x$ is inside a disk $B$ and $m\leq -d\langle c,x\rangle + R$ then the disk centered 
  at the point $x$ and with radius $m$ is contained in the disk $B$. \<close>

lemma (in pmetric_space) disk_in_disk: 
  assumes "c\<in>X"  and "x \<in> disk(c,R)" and "m \<lsq> (\<rm>d`\<langle>c,x\<rangle> \<ad> R)"
  shows "disk(x,m) \<subseteq> disk(c,R)"
proof
  fix y assume "y \<in> disk(x,m)"
  then have "d`\<langle>x,y\<rangle> \<ls> m" using disk_definition by simp
  from assms(1,2) \<open>y \<in> disk(x,m)\<close> have "R\<in>L" "x\<in>X" "y\<in>X" 
    using radius_in_loop(1) disk_definition by auto
  with assms(1) have "d`\<langle>c,y\<rangle> \<lsq> d`\<langle>c,x\<rangle> \<ra> d`\<langle>x,y\<rangle>" using pmetric_properties(4) by simp
  from assms(1) \<open>x\<in>X\<close> have "d`\<langle>c,x\<rangle> \<in> L" 
    using pmetric_properties(1) apply_funtype nonneg_subset by auto
  with \<open>d`\<langle>x,y\<rangle> \<ls> m\<close> assms(3) have "d`\<langle>c,x\<rangle> \<ra> d`\<langle>x,y\<rangle> \<ls> d`\<langle>c,x\<rangle> \<ra> (\<rm>d`\<langle>c,x\<rangle> \<ad> R)"
    using loop_strict_ord_trans1 strict_ord_trans_inv(2) by blast
  with \<open>d`\<langle>c,x\<rangle> \<in> L\<close> \<open>R\<in>L\<close> \<open>d`\<langle>c,y\<rangle> \<lsq> d`\<langle>c,x\<rangle> \<ra> d`\<langle>x,y\<rangle>\<close> \<open>y\<in>X\<close> show "y \<in> disk(c,R)"
    using lrdiv_props(6) loop_strict_ord_trans disk_definition by simp
qed

text\<open>A special case of \<open>disk_in_disk\<close> where we set $m = -d\langle c,x\rangle + R$: 
  if $x$ is an element of a disk with center $c\in X$
  and radius $R$ then this disk contains the disk centered at $x$ and with radius 
  $-d\langle c,x\rangle + R$. \<close>

lemma (in pmetric_space) disk_in_disk1: 
  assumes "c\<in>X"  and "x \<in> disk(c,R)"
  shows "disk(x,\<rm>d`\<langle>c,x\<rangle> \<ad> R) \<subseteq> disk(c,R)"
proof -
  from assms(2) have "R\<in>L" and "d`\<langle>c,x\<rangle> \<in> L"
    using disk_definition less_members by auto
  with assms show ?thesis using left_right_sub_closed(1) loop_ord_refl disk_in_disk
    by simp
qed

text\<open>Assuming that two disks have the same center, closed disk with smaller radius
  in contained in the (open) disk with a larger radius. \<close>

lemma (in pmetric_space) disk_radius_strict_mono:
  assumes "r\<^sub>1 \<ls> r\<^sub>2" 
  shows "{y\<in>X. d`\<langle>x,y\<rangle> \<lsq> r\<^sub>1} \<subseteq> disk(x,r\<^sub>2)"
  using assms loop_strict_ord_trans disk_definition by auto

text\<open> If we assume that the loop's order relation down-directs $L_+$ then
  the collection of disks centered at points of the space and with radii in the positive set 
  of the loop satisfies the base condition. The property that an order relation "down-directs"
  a set is defined in \<open>Order_ZF\<close> and means that every two-element subset of the set 
  has a lower bound in that set. \<close>

lemma (in pmetric_space) disks_form_base: 
  assumes "r {down-directs} L\<^sub>+"
  defines "B \<equiv> \<Union>c\<in>X. {disk(c,R). R\<in>L\<^sub>+}"
  shows "B {satisfies the base condition}"
proof -
  { fix U V assume "U\<in>B" "V\<in>B"
    fix x assume "x\<in>U\<inter>V"
    have "\<exists>W\<in>B. x\<in>W \<and> W\<subseteq>U\<inter>V"
    proof -
      from assms(2) \<open>U\<in>B\<close> \<open>V\<in>B\<close> obtain c\<^sub>U  c\<^sub>V R\<^sub>U  R\<^sub>V 
        where "c\<^sub>U \<in> X" "R\<^sub>U \<in> L\<^sub>+" "c\<^sub>V \<in> X" "R\<^sub>V \<in> L\<^sub>+" "U = disk(c\<^sub>U,R\<^sub>U)" "V = disk(c\<^sub>V,R\<^sub>V)"
        by auto
      with \<open>x\<in>U\<inter>V\<close> have "x \<in> disk(c\<^sub>U,R\<^sub>U)" and "x \<in> disk(c\<^sub>V,R\<^sub>V)" by auto
      then have "x\<in>X" "d`\<langle>c\<^sub>U,x\<rangle> \<ls> R\<^sub>U" "d`\<langle>c\<^sub>V,x\<rangle> \<ls> R\<^sub>V" using disk_definition by auto
      let ?m\<^sub>U = "\<rm> d`\<langle>c\<^sub>U,x\<rangle> \<ad> R\<^sub>U"
      let ?m\<^sub>V = "\<rm> d`\<langle>c\<^sub>V,x\<rangle> \<ad> R\<^sub>V"
      from \<open>c\<^sub>U\<in>X\<close> \<open>x\<in>disk(c\<^sub>U,R\<^sub>U)\<close> \<open>c\<^sub>V\<in>X\<close> \<open>x\<in>disk(c\<^sub>V,R\<^sub>V)\<close> have "?m\<^sub>U\<in>L\<^sub>+" and "?m\<^sub>V\<in>L\<^sub>+" 
        using radius_in_loop(4) by auto
      with assms(1) obtain m where "m \<in> L\<^sub>+" "m \<lsq> ?m\<^sub>U" "m \<lsq> ?m\<^sub>V"
        unfolding DownDirects_def by auto
      let ?W = "disk(x,m)"
      from \<open>m \<in> L\<^sub>+\<close> \<open>m \<lsq> ?m\<^sub>U\<close> \<open>m \<lsq> ?m\<^sub>V\<close> 
        \<open>c\<^sub>U \<in> X\<close> \<open>x \<in> disk(c\<^sub>U,R\<^sub>U)\<close> \<open>c\<^sub>V \<in> X\<close> \<open>x \<in> disk(c\<^sub>V,R\<^sub>V)\<close> 
        \<open>U = disk(c\<^sub>U,R\<^sub>U)\<close> \<open>V = disk(c\<^sub>V,R\<^sub>V)\<close>
        have "?W \<subseteq> U\<inter>V" using disk_in_disk by blast
      moreover from assms(2) \<open>x\<in>X\<close> \<open>m \<in> L\<^sub>+\<close> have "?W \<in> B" and "x\<in>?W" using center_in_disk
        by auto
      ultimately show ?thesis by auto
    qed      
  } then show ?thesis unfolding SatisfiesBaseCondition_def by auto
qed

text\<open>Disks centered at points farther away than the sum of radii do not overlap. \<close>

lemma (in pmetric_space) far_disks:
  assumes "x\<in>X" "y\<in>X"  "r\<^sub>x\<ra>r\<^sub>y \<lsq> d`\<langle>x,y\<rangle>"
  shows "disk(x,r\<^sub>x)\<inter>disk(y,r\<^sub>y) = \<emptyset>"
proof -
  { assume "disk(x,r\<^sub>x)\<inter>disk(y,r\<^sub>y) \<noteq> \<emptyset>"
    then obtain z where "z \<in> disk(x,r\<^sub>x)\<inter>disk(y,r\<^sub>y)" by auto
    then have "z\<in>X" and "d`\<langle>x,z\<rangle> \<ra> d`\<langle>y,z\<rangle> \<ls> r\<^sub>x\<ra>r\<^sub>y"
      using disk_definition add_ineq_strict by auto
    moreover from assms(1,2) \<open>z\<in>X\<close> have "d`\<langle>x,y\<rangle> \<lsq> d`\<langle>x,z\<rangle> \<ra> d`\<langle>y,z\<rangle>"
      using pmetric_properties(3,4) by auto
    ultimately have "d`\<langle>x,y\<rangle> \<ls> r\<^sub>x\<ra>r\<^sub>y" using loop_strict_ord_trans 
      by simp
    with assms(3) have False using loop_strict_ord_trans by auto
  } thus ?thesis by auto
qed

text\<open> If we have a loop element that is smaller than the distance between two points, then
  we can separate these points with disks.\<close>

lemma (in pmetric_space) disjoint_disks:
  assumes "x\<in>X" "y\<in>X" "r\<^sub>x\<ls>d`\<langle>x,y\<rangle>"
  shows "(\<rm>r\<^sub>x\<ad>(d`\<langle>x,y\<rangle>)) \<in> L\<^sub>+" and "disk(x,r\<^sub>x)\<inter>disk(y,\<rm>r\<^sub>x\<ad>(d`\<langle>x,y\<rangle>)) = 0"
proof -
  from assms(3) show "(\<rm>r\<^sub>x\<ad>(d`\<langle>x,y\<rangle>)) \<in> L\<^sub>+"
    using ls_other_side posset_definition1 by simp
  from assms(1,2,3) have "r\<^sub>x\<in>L" and "d`\<langle>x,y\<rangle> \<in> L" 
    using less_members(1) pmetric_loop_valued(2) by auto
  then have "r\<^sub>x\<ra>(\<rm>r\<^sub>x\<ad>(d`\<langle>x,y\<rangle>)) = d`\<langle>x,y\<rangle>" using lrdiv_props(6) by simp
  with assms(1,2) \<open>d`\<langle>x,y\<rangle> \<in> L\<close> show "disk(x,r\<^sub>x)\<inter>disk(y,\<rm>r\<^sub>x\<ad>(d`\<langle>x,y\<rangle>)) = 0"
    using loop_ord_refl far_disks by simp
qed

text\<open>The definition of metric topology written in notation of \<open>pmetric_space\<close> context:\<close>

lemma (in pmetric_space) metric_top_def_alt:
  defines "B \<equiv> \<Union>c\<in>X. {disk(c,R). R\<in>L\<^sub>+}"
  shows "\<tau> = {\<Union>A. A \<in> Pow(B)}"
proof -
  from assms have "MetricTopology(X,L,A,r,d) =  {\<Union>A. A \<in> Pow(B)}"
    unfolding MetricTopology_def by simp
  thus ?thesis by simp
qed

text\<open>If the order of the loop down-directs its set of positive elements 
  then the metric topology defined as collection of unions of (open) disks is indeed a topology.
  Recall that in the \<open>pmetric_space\<close> context $\tau$ denotes the metric topology. \<close>

theorem (in pmetric_space) pmetric_is_top: 
  assumes  "r {down-directs} L\<^sub>+"  
  shows "\<tau> {is a topology}"
  using assms disks_form_base Top_1_2_T1 metric_top_def_alt by simp

text\<open>If $r$ down-directs $L_+$ then the collection of open disks is a base for
  the metric topology.\<close>

theorem (in pmetric_space) disks_are_base:
  assumes  "r {down-directs} L\<^sub>+" 
  defines "B \<equiv> \<Union>c\<in>X. {disk(c,R). R\<in>L\<^sub>+}"
  shows "B {is a base for} \<tau>"
  using assms disks_form_base Top_1_2_T1 metric_top_def_alt by simp

text\<open>If $r$ down-directs $L_+$ then $X$ is the carrier of metric topology.\<close>

theorem (in pmetric_space) metric_top_carrier: 
  assumes  "r {down-directs} L\<^sub>+" shows "\<Union>\<tau> = X"
proof -
  let ?B = "\<Union>c\<in>X. {disk(c,R). R\<in>L\<^sub>+}"
  from assms have "\<Union>\<tau> = \<Union>?B"
    using disks_are_base Top_1_2_L5 by simp
  moreover have "\<Union>?B = X"
  proof
    show "\<Union>?B \<subseteq> X" using disk_definition by auto
    from assms show "X \<subseteq> \<Union>?B" unfolding DownDirects_def using center_in_disk 
      by blast
  qed 
  ultimately show "\<Union>\<tau> = X" by simp
qed

text\<open>Under the assumption that $r$ down-directs $L_+$ the propositions proven
  in the \<open>topology0\<close> context can be used in the \<open>pmetric_space\<close> context.\<close>

lemma (in pmetric_space) topology0_valid_in_pmetric_space:
  assumes  "r {down-directs} L\<^sub>+" 
  shows "topology0(\<tau>)" 
  using assms pmetric_is_top unfolding topology0_def by simp

text\<open>If $r$ down-directs $L_+$ then disks are open in the metric topology.\<close>

lemma (in pmetric_space) disks_open: 
  assumes "c\<in>X" "R\<in>L\<^sub>+" "r {down-directs} L\<^sub>+"
  shows "disk(c,R) \<in> \<tau>"
  using assms base_sets_open disks_are_base(1) pmetric_is_top 
  by blast

text\<open>If $r$ down-directs $L_+$ and $x$ is an element of an open set $U$ then
  there exist radius $R\in L_+$ such that the disk with center $x$ and radius $R$
  is contained in $U$. \<close>

lemma (in pmetric_space) point_open_disk: 
  assumes "r {down-directs} L\<^sub>+" "U\<in>\<tau>" "x\<in>U"
  shows "\<exists>R\<in>L\<^sub>+. disk(x,R) \<subseteq> U"
proof -
  let ?B = "\<Union>c\<in>X. {disk(c,R). R\<in>L\<^sub>+}"
  from assms have "\<exists>V\<in>?B. V\<subseteq>U \<and> x\<in>V"
    using disks_are_base point_open_base_neigh by force
  then obtain c R where "c\<in>X" "R\<in>L\<^sub>+" "x\<in>disk(c,R)" "disk(c,R)\<subseteq>U"
    by auto
  then show ?thesis using radius_in_loop(4) disk_in_disk1
    by blast
qed

text\<open>If $r$ down-directs $L_+$ then the generated topology cannot distinguish
  two points if their distance is zero. "Cannot distinguish" here means that if one is 
  in an open set then the second one is in that set too. \<close>

lemma (in pmetric_space) zero_dist_same_open:
  assumes "r {down-directs} L\<^sub>+" "U\<in>\<tau>" "x\<in>U" "y\<in>X" "d`\<langle>x,y\<rangle>=\<zero>"
  shows "y\<in>U"
  using assms point_open_disk posset_definition1 disk_definition
    by force

text\<open>A pseudometric that induces a $T_0$ topology is a metric.\<close>

theorem (in pmetric_space) pmetric_t0_metric:
  assumes "r {down-directs} L\<^sub>+" "\<tau> {is T\<^sub>0}"
  shows "IsAmetric(d,X,L,A,r)"
proof -
  { fix x y
    assume "x\<in>X" "y\<in>X" "d`\<langle>x,y\<rangle>=\<zero>"
    with assms(1) have "\<forall>U\<in>\<tau>. (x\<in>U \<longleftrightarrow> y\<in>U)"
      using zero_dist_same_open pmetric_properties(3) by auto
    with assms \<open>x\<in>X\<close> \<open>y\<in>X\<close> have "x=y" using metric_top_carrier Top_1_1_L1
      by blast
  } then show "IsAmetric(d,X,L,A,r)"
    using pmetricAssum unfolding IsAmetric_def by auto
qed

text\<open>To define the \<open>metric_space\<close> locale we take the \<open>pmetric_space\<close> and add 
  the assumption of identity of indiscernibles.\<close>

locale metric_space =  pmetric_space +
  assumes ident_indisc: "\<forall>x\<in>X. \<forall>y\<in>X. d`\<langle>x,y\<rangle>=\<zero> \<longrightarrow> x=y"

text\<open>In the \<open>metric_space\<close> locale $d$ is a metric.\<close>

lemma (in metric_space) d_metric: shows "IsAmetric(d,X,L,A,r)"
  using pmetricAssum ident_indisc unfolding IsAmetric_def by simp

text\<open>Distance of different points is greater than zero. \<close>

lemma (in metric_space) dist_pos: assumes "x\<in>X" "y\<in>X" "x\<noteq>y"
  shows "\<zero>\<ls>d`\<langle>x,y\<rangle>" "d`\<langle>x,y\<rangle> \<in> L\<^sub>+"
proof -
  from assms(1,2) have "d`\<langle>x,y\<rangle> \<in> L\<^sup>+" 
    using pmetric_properties(1) apply_funtype by simp  
  then have "\<zero> \<lsq> d`\<langle>x,y\<rangle>" using Nonnegative_def by auto
  with assms show "d`\<langle>x,y\<rangle> \<in> L\<^sub>+" and "\<zero>\<ls>d`\<langle>x,y\<rangle>" 
    using ident_indisc posset_definition posset_definition1 by auto
qed

text\<open>If $r$ down-directs $L_+$ then the ordered loop valued metric space is $T_2$ (i.e. Hausdorff).\<close>

theorem (in metric_space) metric_space_T2:
    assumes "r {down-directs} L\<^sub>+" 
    shows "\<tau> {is T\<^sub>2}"
proof -
  let ?B = "\<Union>c\<in>X. {disk(c,R). R\<in>L\<^sub>+}"
  { fix x y assume "x\<in>\<Union>\<tau>" "y\<in>\<Union>\<tau>" "x\<noteq>y"
    from assms have "?B\<subseteq>\<tau>" using metric_top_def_alt by auto
    have "\<exists>U\<in>?B. \<exists>V\<in>?B. x\<in>U \<and> y\<in>V \<and> U\<inter>V = \<emptyset>"
    proof -
      let ?R = "d`\<langle>x,y\<rangle>" 
      from assms have "\<Union>\<tau> = X" using metric_top_carrier by simp
      with \<open>x\<in>\<Union>\<tau>\<close> have "x\<in>X" by blast
      from \<open>\<Union>\<tau> = X\<close> \<open>y\<in>\<Union>\<tau>\<close> have "y\<in>X" by blast
      with \<open>x\<noteq>y\<close> \<open>x\<in>X\<close> have "?R\<in>L\<^sub>+" using dist_pos by simp
      with \<open>x\<in>X\<close> \<open>y\<in>X\<close> have "disk(x,?R) \<in> ?B" and "disk(y,?R) \<in> ?B"
        by auto
      { assume "disk(x,?R) \<inter> disk(y,?R) = \<emptyset>"
        moreover from \<open>x\<in>X\<close> \<open>y\<in>X\<close> \<open>?R\<in>L\<^sub>+\<close> have 
            "disk(x,?R)\<in>?B" "disk(y,?R)\<in>?B" "x\<in>disk(x,?R)" "y\<in>disk(y,?R)"
          using center_in_disk by auto
        ultimately have "\<exists>U\<in>?B. \<exists>V\<in>?B. x\<in>U \<and> y\<in>V \<and> U\<inter>V = 0" by blast
      }
      moreover
      { assume "disk(x,?R) \<inter> disk(y,?R) \<noteq> 0"
        then obtain z where "z \<in> disk(x,?R)" and "z \<in> disk(y,?R)" 
          by auto
        then have "d`\<langle>x,z\<rangle> \<ls> ?R" using disk_definition by simp
        then have "\<zero> \<ls> \<rm>d`\<langle>x,z\<rangle>\<ad>?R" using ls_other_side(1) by simp
        let ?r = "\<rm>d`\<langle>x,z\<rangle>\<ad>?R"
        have "?r\<ls>?R"
        proof -
          from \<open>z \<in> disk(y,?R)\<close> \<open>x\<in>X\<close> \<open>y\<in>X\<close> have "z\<in>X" "x\<noteq>z"
            using disk_definition pmetric_properties(3) by auto
          with \<open>x\<in>X\<close> \<open>y\<in>X\<close> \<open>z\<in>X\<close> show ?thesis
            using pmetric_loop_valued dist_pos(1) add_subtract_pos(2) by simp 
        qed
        with \<open>x\<in>X\<close> \<open>y\<in>X\<close> have "disk(x,?r)\<inter>disk(y,\<rm>?r\<ad>?R) = 0"
          by (rule disjoint_disks)
        moreover 
        from \<open>\<zero>\<ls>?r\<close> \<open>?r\<ls>?R\<close> have "?r\<in>L\<^sub>+" "(\<rm>?r\<ad>?R) \<in> L\<^sub>+"
          using ls_other_side posset_definition1 by auto
        with \<open>x\<in>X\<close> \<open>y\<in>X\<close> have 
            "disk(x,?r)\<in>?B" "disk(y,\<rm>?r\<ad>(d`\<langle>x,y\<rangle>))\<in>?B" and
            "x\<in>disk(x,?r)" "y\<in>disk(y,\<rm>?r\<ad>(d`\<langle>x,y\<rangle>))"
          using center_in_disk by auto
        ultimately have "\<exists>U\<in>?B. \<exists>V\<in>?B. x\<in>U \<and> y\<in>V \<and> U\<inter>V = 0" by blast
      }
      ultimately show ?thesis by auto
    qed
    with \<open>?B\<subseteq>\<tau>\<close> have "\<exists>U\<in>\<tau>. \<exists>V\<in>\<tau>. x\<in>U \<and> y\<in>V \<and> U\<inter>V = \<emptyset>" by (rule exist2_subset)
  } then show ?thesis unfolding isT2_def by simp
qed

subsection\<open>Uniform structures on (pseudo-)metric spaces\<close>

text\<open>Each pseudometric space with pseudometric $d:X\times X\rightarrow L^+$ 
  supports a natural uniform structure, defined as supersets of the collection
  of inverse images $U_c = d^{-1}([0,c])$, where $c>0$.  \<close>

text\<open>In the following definition $X$ is the underlying space, $L$ is the loop (carrier),
  $A$ is the loop operation, $r$ is an order relation compatible with $A$,
  and $d$ is a pseudometric on $X$, valued in the ordered loop $L$.
  With this we define the uniform gauge as the collection of inverse images
  of the closed intervals $[0,c]$ as $c$ varies of the set of positive elements of $L$.\<close>

definition
  "UniformGauge(X,L,A,r,d) \<equiv> {d-``({c\<in>Nonnegative(L,A,r). \<langle>c,b\<rangle> \<in> r}). b\<in>PositiveSet(L,A,r)}"

text\<open>In the \<open>pmetric_space\<close> context we will write \<open>UniformGauge(X,L,A,r,d)\<close> as \<open>\<BB>\<close>. \<close>

abbreviation (in pmetric_space) gauge ("\<BB>") where "\<BB> \<equiv> UniformGauge(X,L,A,r,d)"

text\<open>In notation defined in the \<open>pmetric_space\<close> context we can write the uniform gauge
  as $\{ d^{-1}(\{c\in L^+: c\leq b\}: b \in L_+ \}$.  \<close>

lemma (in pmetric_space) uniform_gauge_def_alt: 
  shows "\<BB> = {d-``({c\<in>L\<^sup>+. c\<lsq>b}). b\<in>L\<^sub>+}"
  unfolding UniformGauge_def by simp

text\<open>Members of the uniform gauge are subsets of $X\times X$ i.e. relations on $X$. \<close>

lemma (in pmetric_space) uniform_gauge_relations: 
  assumes "B\<in>\<BB>" shows "B\<subseteq>X\<times>X"
  using assms uniform_gauge_def_alt pmetric_properties(1) func1_1_L3
  by force

text\<open>If the distance between two points of $X$ is less or equal $b$, then
  this pair of points is in $d^{-1}([0,b])$. \<close>

lemma (in pmetric_space) gauge_members: 
  assumes "x\<in>X" "y\<in>X" "d`\<langle>x,y\<rangle> \<lsq> b"
  shows "\<langle>x,y\<rangle> \<in> d-``({c\<in>L\<^sup>+. c\<lsq>b})"
  using assms pmetric_properties(1) apply_funtype func1_1_L15
  by simp

text\<open>Suppose $b\in L_+$ (i.e. b is an element of the loop that is greater than the neutral element)
  and $x\in X$. Then the image of the singleton set $\{ x\}$ by the relation 
  $B=\{ d^{-1}(\{c\in L^+: c\leq b\}$ is the set $\{ y\in X:d\langle x,y\rangle  \leq b\}$,
  i.e. the closed disk with center $x$ and radius $b$. Hence the the image $B\{ x\}$ contains
  the open disk with center $x$ and radius $b$. \<close>

lemma (in pmetric_space) disk_in_gauge: 
  assumes "b\<in>L\<^sub>+" "x\<in>X" 
  defines "B \<equiv> d-``({c\<in>L\<^sup>+. c\<lsq>b})"
  shows "B``{x} = {y\<in>X. d`\<langle>x,y\<rangle> \<lsq> b}" and "disk(x,b) \<subseteq> B``{x}"
proof -
  from assms(1,3) have "B\<subseteq>X\<times>X" 
    using uniform_gauge_def_alt uniform_gauge_relations by auto
  with assms(2,3) show "B``{x} = {y\<in>X. d`\<langle>x,y\<rangle> \<lsq> b}"
    using pmetric_properties(1) func1_1_L15 by force
  then show "disk(x,b) \<subseteq> B``{x}" using disk_definition by auto
qed

text\<open>Gauges corresponding to larger elements of the loop are larger. \<close>

lemma (in pmetric_space) uniform_gauge_mono: 
  assumes "b\<^sub>1\<lsq>b\<^sub>2" shows "d-``({c\<in>L\<^sup>+. c\<lsq>b\<^sub>1}) \<subseteq> d-``({c\<in>L\<^sup>+. c\<lsq>b\<^sub>2})" 
  using ordLoopAssum assms vimage_mono1 
  unfolding IsAnOrdLoop_def IsPartOrder_def trans_def by auto

text\<open>For any two sets of the form $d^{-1}([0,b])$ we can find a third one that is contained
  in both. \<close>

lemma (in pmetric_space) gauge_1st_cond: 
  assumes "r {down-directs} L\<^sub>+" "B\<^sub>1\<in>\<BB>" "B\<^sub>2\<in>\<BB>"
  shows "\<exists>B\<^sub>3\<in>\<BB>. B\<^sub>3\<subseteq>B\<^sub>1\<inter>B\<^sub>2" 
proof -
  from assms(2,3) obtain b\<^sub>1 b\<^sub>2 where "b\<^sub>1\<in>L\<^sub>+" "b\<^sub>2\<in>L\<^sub>+" and 
    I: "B\<^sub>1 = d-``({c\<in>L\<^sup>+. c\<lsq>b\<^sub>1})" "B\<^sub>2 = d-``({c\<in>L\<^sup>+. c\<lsq>b\<^sub>2})"
    using uniform_gauge_def_alt by auto
  from assms(1) \<open>b\<^sub>1\<in>L\<^sub>+\<close> \<open>b\<^sub>2\<in>L\<^sub>+\<close> obtain b\<^sub>3 where "b\<^sub>3\<in>L\<^sub>+" "b\<^sub>3\<lsq>b\<^sub>1" "b\<^sub>3\<lsq>b\<^sub>2"
    unfolding DownDirects_def by auto
  from I \<open>b\<^sub>3\<lsq>b\<^sub>1\<close> \<open>b\<^sub>3\<lsq>b\<^sub>2\<close> have "d-``({c\<in>L\<^sup>+. c\<lsq>b\<^sub>3}) \<subseteq> B\<^sub>1\<inter>B\<^sub>2"
    using uniform_gauge_mono by blast
  with \<open>b\<^sub>3\<in>L\<^sub>+\<close> show ?thesis using uniform_gauge_def_alt 
    by auto
qed

text\<open>Sets of the form $d^{-1}([0,b])$ contain the diagonal. \<close>

lemma (in pmetric_space) gauge_2nd_cond: assumes "B\<in>\<BB>" shows "id(X)\<subseteq>B"
proof
  fix p assume "p\<in>id(X)"
  then obtain x where "x\<in>X" and "p=\<langle>x,x\<rangle>" by auto
  then have "p\<in>X\<times>X" and "d`(p) = \<zero>" using pmetric_properties(2) by simp_all
  from assms obtain b where "b\<in>L\<^sub>+" and "B = d-``({c\<in>L\<^sup>+. c\<lsq>b})"
    using uniform_gauge_def_alt by auto
  with \<open>p\<in>X\<times>X\<close> \<open>d`(p) = \<zero>\<close> show "p\<in>B"
    using posset_definition1 loop_zero_nonneg pmetric_properties(1) func1_1_L15
    by simp
qed

text\<open>Sets of the form $d^{-1}([0,b])$ are symmetric.\<close>

lemma (in pmetric_space) gauge_symmetric: 
  assumes "B\<in>\<BB>" shows "B = converse(B)"
proof -
  from assms obtain b where "B = d-``({c\<in>L\<^sup>+. c\<lsq>b})"
    using uniform_gauge_def_alt by auto
  with pmetricAssum show ?thesis unfolding IsApseudoMetric_def
    using symm_vimage_symm by auto
qed

text\<open>A set of the form $d^{-1}([0,b])$ contains a symmetric set of this form.\<close>

corollary (in pmetric_space) gauge_3rd_cond: 
  assumes "B\<^sub>1\<in>\<BB>" shows "\<exists>B\<^sub>2\<in>\<BB>. B\<^sub>2 \<subseteq> converse(B\<^sub>1)"
  using assms gauge_symmetric by auto

text\<open>The collection of sets of the form $d^{-1}([0,b])$ for $b\in L_+$ 
  is contained of the powerset of $X\times X$.\<close>

lemma (in pmetric_space) gauge_5thCond: shows "\<BB>\<subseteq>Pow(X\<times>X)"
  using uniform_gauge_def_alt pmetric_properties(1) func1_1_L3 by force

text\<open>If the set of positive values is non-empty, then there are sets
  of the form $d^{-1}([0,b])$ for $b>0$.\<close>

lemma (in pmetric_space) gauge_6thCond: 
  assumes "L\<^sub>+\<noteq>\<emptyset>" shows "\<BB>\<noteq>\<emptyset>"  using assms uniform_gauge_def_alt by simp

text\<open>The remaining 4th condition for the sets of the form $d^{-1}([0,b])$
  to be a uniform base (or a fundamental system of entourages) cannot be proven
  without additional assumptions in the context of ordered loop valued metrics. 
  To see that consider the example
  of natural numbers with the metric $d\langle x,y \rangle = |x-y|$, where we think
  of $d$ as valued in the nonnegative set of ordered group of integers.
  Now take the set $B_1 = d^{-1}([0,1]) = d^{-1}(\{ 0,1\} )$. Then the set $B_1 \circ B_1$ 
  is strictly larger than $B_1$, but there is no smaller set $B_2$ we can take so that
  $B_2 \circ B_2 \subseteq B_1$. 
  One condition that is sufficient is that for every $b_1 >0$ there is a $b_2 >0$
  such that $b_2 + b_2 \leq b_1 $. I have not found a standard name for this property, for now
  we will use the name \<open>IsHalfable\<close>. \<close>

definition
  "IsHalfable(L,A,r) \<equiv> \<forall>b\<^sub>1\<in>PositiveSet(L,A,r). \<exists>b\<^sub>2\<in>PositiveSet(L,A,r). \<langle>A`\<langle>b\<^sub>2,b\<^sub>2\<rangle>,b\<^sub>1\<rangle> \<in> r"

text\<open>The property of halfability written in the notation used in the \<open>pmetric_space\<close> context.\<close>

lemma (in pmetric_space) is_halfable_def_alt: 
  assumes "IsHalfable(L,A,r)" "b\<^sub>1\<in>L\<^sub>+"
  shows "\<exists>b\<^sub>2\<in>L\<^sub>+. b\<^sub>2\<ra>b\<^sub>2 \<lsq> b\<^sub>1"
  using assms unfolding IsHalfable_def by simp

text\<open>If the loop order is halfable then for every set $B_1$ of the form $d^{-1}([0,b_1])$ 
  for some $b_1>0$ we can find another one $B_2 = d^{-1}([0,b_2])$ such that $B_2$ 
  composed with itself is contained in $B_1$.\<close>

lemma (in pmetric_space) gauge_4thCond: 
  assumes "IsHalfable(L,A,r)" "B\<^sub>1\<in>\<BB>" shows "\<exists>B\<^sub>2\<in>\<BB>.\<exists>B\<^sub>2\<in>\<BB>. B\<^sub>2 O B\<^sub>2 \<subseteq> B\<^sub>1"
proof -
  from assms(2) obtain b\<^sub>1 where "b\<^sub>1\<in>L\<^sub>+" and "B\<^sub>1 = d-``({c\<in>L\<^sup>+. c\<lsq>b\<^sub>1})"
    using uniform_gauge_def_alt by auto
  from assms(1) \<open>b\<^sub>1\<in>L\<^sub>+\<close> obtain b\<^sub>2 where "b\<^sub>2\<in>L\<^sub>+" and "b\<^sub>2\<ra>b\<^sub>2 \<lsq> b\<^sub>1"
    using is_halfable_def_alt by auto
  let ?B\<^sub>2 = "d-``({c\<in>L\<^sup>+. c\<lsq>b\<^sub>2})"
  from \<open>b\<^sub>2\<in>L\<^sub>+\<close> have "?B\<^sub>2\<in>\<BB>" unfolding UniformGauge_def by auto
  { fix p assume "p \<in> ?B\<^sub>2 O ?B\<^sub>2" 
    with \<open>?B\<^sub>2\<in>\<BB>\<close> obtain x y where "x\<in>X" "y\<in>X" and "p=\<langle>x,y\<rangle>"
      using gauge_5thCond by blast
    from \<open>p \<in> ?B\<^sub>2 O ?B\<^sub>2\<close> \<open>p=\<langle>x,y\<rangle>\<close> obtain z where 
      "\<langle>x,z\<rangle> \<in> ?B\<^sub>2" and "\<langle>z,y\<rangle> \<in> ?B\<^sub>2"
      using rel_compdef by auto
    with \<open>?B\<^sub>2\<in>\<BB>\<close> have "z\<in>X" using gauge_5thCond by auto
    from \<open>\<langle>x,z\<rangle> \<in> ?B\<^sub>2\<close> \<open>\<langle>z,y\<rangle> \<in> ?B\<^sub>2\<close> have "d`\<langle>x,z\<rangle> \<ra> d`\<langle>z,y\<rangle> \<lsq> b\<^sub>2\<ra> b\<^sub>2"
      using pmetric_properties(1) func1_1_L15 add_ineq by simp
    with \<open>b\<^sub>2\<ra>b\<^sub>2 \<lsq> b\<^sub>1\<close> have "d`\<langle>x,z\<rangle> \<ra> d`\<langle>z,y\<rangle> \<lsq> b\<^sub>1"
      using loop_ord_trans by simp
    with \<open>x\<in>X\<close> \<open>y\<in>X\<close> \<open>z\<in>X\<close> \<open>p=\<langle>x,y\<rangle>\<close> \<open>B\<^sub>1 = d-``({c\<in>L\<^sup>+. c\<lsq>b\<^sub>1})\<close> have "p\<in>B\<^sub>1"
      using pmetric_properties(4) loop_ord_trans gauge_members by blast      
  } hence "?B\<^sub>2 O ?B\<^sub>2 \<subseteq> B\<^sub>1" by auto
  with \<open>?B\<^sub>2\<in>\<BB>\<close> show ?thesis by auto
qed

text\<open>If $X$ and $L_+$ are not empty, the order relation $r$
  down-directs $L_+$, and the loop order is halfable, then $\mathfrak{B}$
  (which in the \<open>pmetric_space\<close> context is an abbreviation for 
  $\{ d^{-1}(\{c\in L^+: c\leq b\}: b \in L_+ \}$)
  is a fundamental system of entourages, hence its supersets 
  form a uniformity on $X$ and hence those supersets define a topology on $X$.\<close>

theorem (in pmetric_space) metric_gauge_base: 
  assumes "X\<noteq>\<emptyset>" "L\<^sub>+\<noteq>\<emptyset>" "r {down-directs} L\<^sub>+" "IsHalfable(L,A,r)"
  shows 
    "\<BB> {is a uniform base on} X"
    "Supersets(X\<times>X,\<BB>) {is a uniformity on} X"
    "UniformTopology(Supersets(X\<times>X,\<BB>),X) {is a topology}"
    "\<Union>UniformTopology(Supersets(X\<times>X,\<BB>),X) = X"
  using assms gauge_1st_cond gauge_2nd_cond gauge_3rd_cond 
    gauge_4thCond gauge_5thCond gauge_6thCond uniformity_base_is_base
    uniform_top_is_top
  unfolding IsUniformityBaseOn_def by simp_all

text\<open>At this point we know that a pseudometric induces two topologies: one consisting of unions
  of open disks (the metric topology) and second one being the uniform topology derived 
  from the uniformity generated the fundamental system of entourages (the base uniformity) 
  of the sets of the form $d^{-1}([0,b])$ for $b>0$.  
  The next theorem states that if $X$ and $L_+$ are not empty, $r$ down-directs $L_+$,
  and the loop order is halfable, then these two topologies are in fact the same. 
  Recall that in the \<open>pmetric_space\<close> context $\tau$ denotes the metric topology. \<close>

theorem (in pmetric_space) metric_top_is_uniform_top:
  assumes "X\<noteq>\<emptyset>" "L\<^sub>+\<noteq>\<emptyset>" "r {down-directs} L\<^sub>+" "IsHalfable(L,A,r)"
  shows "\<tau> = UniformTopology(Supersets(X\<times>X,\<BB>),X)"
proof
  let ?\<Phi> = "Supersets(X\<times>X,\<BB>)"
  from assms have "?\<Phi> {is a uniformity on} X" using metric_gauge_base
    by simp
  let ?T = "UniformTopology(?\<Phi>,X)"
  { fix U assume "U\<in>?T"
    then have "U\<in>Pow(X)" and I: "\<forall>x\<in>U. U\<in>{V``{x}. V\<in>?\<Phi>}"
      unfolding UniformTopology_def by auto
    { fix x assume "x\<in>U"
      with I obtain A where "A\<in>?\<Phi>" and "U = A``{x}"
        by auto
      from \<open>x\<in>U\<close> \<open>U\<in>?T\<close> have "x\<in>\<Union>?T" by auto
      with assms have "x\<in>X" using metric_gauge_base(4) by simp
      from \<open>A\<in>?\<Phi>\<close> obtain B where "B\<in>\<BB>" and "B\<subseteq>A"
        unfolding Supersets_def by auto
      from \<open>B\<in>\<BB>\<close> obtain b where "b\<in>L\<^sub>+" and "B = d-``({c\<in>L\<^sup>+. c\<lsq>b})"
        using uniform_gauge_def_alt by auto
      with \<open>x\<in>X\<close> \<open>B\<subseteq>A\<close> \<open>U = A``{x}\<close> have "disk(x,b) \<subseteq> U"
        using disk_in_gauge(2) by blast
      with assms(3) \<open>x\<in>X\<close> \<open>b\<in>L\<^sub>+\<close> have "\<exists>V\<in>\<tau>. x\<in>V \<and> V\<subseteq>U"
        using disks_open center_in_disk by force
    } with assms(3) have "U\<in>\<tau>"
      using topology0_valid_in_pmetric_space topology0.open_neigh_open
        by simp
  } thus "?T \<subseteq> \<tau>" by auto
  let ?\<D> = "\<Union>c\<in>X. {disk(c,R). R\<in>L\<^sub>+}"
  { fix U assume "U \<in> ?\<D>"
    then obtain c b where "c\<in>X" "b\<in>L\<^sub>+" "U = disk(c,b)"
      by blast
    { fix x assume "x\<in>U"
      let ?b\<^sub>1 = "\<rm>d`\<langle>c,x\<rangle> \<ad> b"
      from \<open>x\<in>U\<close> \<open>c\<in>X\<close> \<open>U = disk(c,b)\<close> have 
        "x\<in>X" "x\<in>disk(c,b)" "disk(x,?b\<^sub>1) \<subseteq> U" "?b\<^sub>1 \<in> L\<^sub>+"
        using disk_in_disk1 disk_definition radius_in_loop(4) by simp_all
      with assms(4) obtain b\<^sub>2 where "b\<^sub>2\<in>L\<^sub>+" and "b\<^sub>2\<ra>b\<^sub>2 \<lsq> ?b\<^sub>1"
        using is_halfable_def_alt by auto
      let ?D = "{y\<in>X. d`\<langle>x,y\<rangle> \<lsq> b\<^sub>2}"
      from \<open>b\<^sub>2\<in>L\<^sub>+\<close> \<open>b\<^sub>2\<ra>b\<^sub>2 \<lsq> ?b\<^sub>1\<close> have "?D \<subseteq> disk(x,?b\<^sub>1)"
        using posset_definition1 positive_subset add_subtract_pos(3) 
          loop_strict_ord_trans1 disk_radius_strict_mono by blast 
      let ?B = "d-``({c\<in>L\<^sup>+. c\<lsq>b\<^sub>2})"
      from \<open>b\<^sub>2\<in>L\<^sub>+\<close> have "?B\<in>\<BB>" using uniform_gauge_def_alt by auto
      then have "?B\<in>?\<Phi>" using uniform_gauge_relations superset_gen 
        by simp
      from \<open>b\<^sub>2\<in>L\<^sub>+\<close> \<open>x\<in>X\<close> \<open>?D \<subseteq> disk(x,?b\<^sub>1)\<close> \<open>disk(x,?b\<^sub>1) \<subseteq> U\<close> have "?B``{x} \<subseteq> U"
        using disk_in_gauge(1) by auto
      with \<open>?B\<in>?\<Phi>\<close> have "\<exists>W\<in>?\<Phi>. W``{x} \<subseteq> U" by auto
    } with \<open>U = disk(c,b)\<close> \<open>?\<Phi> {is a uniformity on} X\<close> have "U \<in> ?T"
      using disk_definition uniftop_def_alt1 by auto
  } hence "?\<D> \<subseteq> ?T" by auto
  with assms show "\<tau>\<subseteq>?T"
    using disks_are_base(1) metric_gauge_base(3) base_smallest_top
    by simp
qed

end
