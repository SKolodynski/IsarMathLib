(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2020,2021 Slawomir Kolodynski

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

section \<open> Metric spaces \<close>

theory MetricSpace_ZF imports Topology_ZF_1 OrderedLoop_ZF Lattice_ZF
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


text\<open>Next we define notation for metric spaces. We will reuse the additive notation defined in 
  the \<open>loop1\<close> locale adding only the assumption about $d$ being a pseudometric and notation
  for a disk centered at $c$ with radius $R$.
  Since for many theorems it is sufficient to assume the pseudometric axioms we will
  assume in this context that the sets $d,X,L,A,r$ form a pseudometric raher than a metric.\<close>

locale pmetric_space =  loop1 +
  fixes d and X 

  assumes pmetricAssum: "IsApseudoMetric(d,X,L,A,r)"
  
  fixes disk
  defines disk_def [simp]: "disk(c,R) \<equiv> Disk(X,d,r,c,R)"


text\<open> The next lemma shows the definition of the pseudometric in the notation used in the 
  \<open>metric_space\<close> context.\<close>

lemma (in pmetric_space) pmetric_properties: shows 
  "d: X\<times>X \<rightarrow> L\<^sup>+"
  "\<forall>x\<in>X. d`\<langle>x,x\<rangle> = \<zero>"
  "\<forall>x\<in>X.\<forall>y\<in>X. d`\<langle>x,y\<rangle> = d`\<langle>y,x\<rangle>"
  "\<forall>x\<in>X.\<forall>y\<in>X.\<forall>z\<in>X. d`\<langle>x,z\<rangle> \<lsq> d`\<langle>x,y\<rangle> \<ra> d`\<langle>y,z\<rangle>"
  using pmetricAssum unfolding IsApseudoMetric_def by auto

text\<open>The values of the metric are in the loop.\<close>

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
  then have "disk(c,R) = {x\<in>X. \<langle>d`\<langle>c,x\<rangle>,R\<rangle> \<in> StrictVersion(r)}" unfolding Disk_def by simp
  moreover have "\<forall>x\<in>X. \<langle>d`\<langle>c,x\<rangle>,R\<rangle> \<in> StrictVersion(r) \<longleftrightarrow> d`\<langle>c,x\<rangle> \<ls> R"
    using def_of_strict_ver by simp
  ultimately show ?thesis by auto
qed

text\<open>If the radius is positive then the center is in disk.\<close>

lemma (in pmetric_space) center_in_disk: assumes "c\<in>X" and "R\<in>L\<^sub>+" shows "c \<in> disk(c,R)"
  using pmetricAssum assms IsApseudoMetric_def PositiveSet_def disk_definition by simp
  
text\<open>A technical lemma that allows us to shorten some proofs: \<close>

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

text\<open>If a point $x$ is inside a disk $B$ and $m\leq R-d(c,x)$ then the disk centered 
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

text\<open> If we assume that the order on the group makes the positive set a meet semi-lattice (i.e.
  every two-element subset of $G_+$ has a greatest lower bound) then 
  the collection of disks centered at points of the space and with radii in the positive set 
  of the group satisfies the base condition. The meet semi-lattice assumption can be weakened 
  to "each two-element subset of $G_+$ has a lower bound in $G_+$", but we don't do that here. \<close>

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
  shows "disk(x,r\<^sub>x)\<inter>disk(y,r\<^sub>y) = 0"
proof -
  { assume "disk(x,r\<^sub>x)\<inter>disk(y,r\<^sub>y) \<noteq> 0"
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

text\<open>Unions of disks form a topology, hence (pseudo)metric spaces are topological spaces. \<close>

theorem (in pmetric_space) pmetric_is_top: 
  assumes  "r {down-directs} L\<^sub>+" 
  defines "B \<equiv> \<Union>c\<in>X. {disk(c,R). R\<in>L\<^sub>+}" 
  defines "T \<equiv> {\<Union>A. A \<in> Pow(B)}"
  shows "T {is a topology}"  "B {is a base for} T"  "\<Union>T = X"
proof -
  from assms  show  "T {is a topology}"  "B {is a base for} T" 
    using disks_form_base Top_1_2_T1 by auto
  then have "\<Union>T = \<Union>B" using Top_1_2_L5 by simp
  moreover have "\<Union>B = X"
  proof
    from assms(2) show "\<Union>B \<subseteq> X" using disk_definition by auto
    { fix x assume "x\<in>X"
      from assms(1) obtain R where "R\<in>L\<^sub>+" unfolding DownDirects_def by blast
      with assms(2) \<open>x\<in>X\<close> have "x \<in> \<Union>B" using center_in_disk by auto
    } thus "X \<subseteq> \<Union>B" by auto
  qed 
  ultimately show "\<Union>T = X" by simp
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

text\<open>An ordered loop valued metric space is $T_2$ (i.e. Hausdorff).\<close>

theorem (in metric_space) metric_space_T2:
    assumes "r {down-directs} L\<^sub>+"
    defines "B \<equiv> \<Union>c\<in>X. {disk(c,R). R\<in>L\<^sub>+}" 
    defines "T \<equiv> {\<Union>A. A \<in> Pow(B)}"
    shows "T {is T\<^sub>2}"
proof -
  { fix x y assume "x\<in>\<Union>T" "y\<in>\<Union>T" "x\<noteq>y"
    from assms have "B\<subseteq>T" using pmetric_is_top(2) base_sets_open by auto
    moreover have "\<exists>U\<in>B. \<exists>V\<in>B. x\<in>U \<and> y\<in>V \<and> U\<inter>V = 0"
    proof -
      let ?R = "d`\<langle>x,y\<rangle>"
      from assms have "\<Union>T = X" using pmetric_is_top(3) by simp
      with \<open>x\<in>\<Union>T\<close> \<open>y\<in>\<Union>T\<close> have "x\<in>X" "y\<in>X" by auto
      with \<open>x\<noteq>y\<close> have "?R\<in>L\<^sub>+" using dist_pos by simp
      with assms(2) \<open>x\<in>X\<close> \<open>y\<in>X\<close> have "disk(x,?R) \<in> B" and "disk(y,?R) \<in> B"
        by auto
      { assume "disk(x,?R) \<inter> disk(y,?R) = 0"
        moreover from assms(2) \<open>x\<in>X\<close> \<open>y\<in>X\<close> \<open>?R\<in>L\<^sub>+\<close> have 
            "disk(x,?R)\<in>B" "disk(y,?R)\<in>B" "x\<in>disk(x,?R)" "y\<in>disk(y,?R)"
          using center_in_disk by auto
        ultimately have "\<exists>U\<in>B. \<exists>V\<in>B. x\<in>U \<and> y\<in>V \<and> U\<inter>V = 0" by auto
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
            using pmetric_loop_valued dist_pos(1) subtract_pos(2) by simp 
        qed
        with \<open>x\<in>X\<close> \<open>y\<in>X\<close> have "disk(x,?r)\<inter>disk(y,\<rm>?r\<ad>?R) = 0"
          by (rule disjoint_disks)
        moreover 
        from \<open>\<zero>\<ls>?r\<close> \<open>?r\<ls>?R\<close> have "?r\<in>L\<^sub>+" "(\<rm>?r\<ad>?R) \<in> L\<^sub>+"
          using ls_other_side posset_definition1 by auto
        with assms(2) \<open>x\<in>X\<close> \<open>y\<in>X\<close> have 
            "disk(x,?r)\<in>B" "disk(y,\<rm>?r\<ad>(d`\<langle>x,y\<rangle>))\<in>B" and
            "x\<in>disk(x,?r)" "y\<in>disk(y,\<rm>?r\<ad>(d`\<langle>x,y\<rangle>))"
          using center_in_disk by auto
        ultimately have "\<exists>U\<in>B. \<exists>V\<in>B. x\<in>U \<and> y\<in>V \<and> U\<inter>V = 0" by auto
      }
      ultimately show ?thesis by auto
    qed
    ultimately have "\<exists>U\<in>T. \<exists>V\<in>T. x\<in>U \<and> y\<in>V \<and> U\<inter>V = 0" by auto
  } then show ?thesis unfolding isT2_def by simp
qed

end
