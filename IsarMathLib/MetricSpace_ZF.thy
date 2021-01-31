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

section \<open> Metric spaces - definitions and basic properties \<close>

theory MetricSpace_ZF imports Topology_ZF_1 OrderedGroup_ZF Lattice_ZF
begin

text\<open>A metric space is a set on which a distance between points is defined as a function
  $d:X \times X \to [0,\infty)$. Each metric space is a topological space which is paracompact 
  and Hausdorff ($T_2$), hence normal (in fact even perfectly normal).\<close>

text\<open>A metric on $X$ is usually defined as a function $d:X \times X \to [0,\infty)$ that satisfies
  the conditions $d(x,x) = 0", $d(x, y) = 0 \Rightarrow  x = y$ (identity of indiscernibles), 
  $d(x, y)  = d(y, x)$ (symmetry) and  $d(x, y) \le d(x, z) + d(z, y)$ (triangle inequality) for all $x,y \in X$. 
  Here we are going to be a bit more general and define metric as a function valued in a 
  linearly ordered group. 
  First we define a preudo-metric, which has the axioms of a metric, but without the second part
  of the identity of indiscernibles.
  In our definition \<IsApseudoMetric> is a predicate on five sets: the function $d$, 
  the set $X$ on which the metric is defined, the group carrier $G$, the group operation $A$ 
  and the order $r$ on $G$.\<close>


definition 
  "IsApseudoMetric(d,X,G,A,r) \<equiv> d:X\<times>X \<rightarrow> Nonnegative(G,A,r) 
    \<and> (\<forall>x\<in>X. d`\<langle>x,x\<rangle> = TheNeutralElement(G,A))
    \<and> (\<forall>x\<in>X.\<forall>y\<in>X. d`\<langle>x,y\<rangle> = d`\<langle>y,x\<rangle>)
    \<and> (\<forall>x\<in>X.\<forall>y\<in>X.\<forall>z\<in>X. \<langle>d`\<langle>x,z\<rangle>, A`\<langle>d`\<langle>x,y\<rangle>,d`\<langle>y,z\<rangle>\<rangle>\<rangle> \<in> r)"

text\<open>We add the full axiom of identity of indiscernibles to the definition of a pseudometric
  to get the definition of metric.\<close>

definition 
  "IsAmetric(d,X,G,A,r) \<equiv> IsApseudoMetric(d,X,G,A,r) \<and> (\<forall>x\<in>X.\<forall>y\<in>X. d`\<langle>x,y\<rangle> = 0 \<longrightarrow> x=y)"

text\<open>A disk is defined as set of points located less than the radius from the center\<close>

definition "Disk(X,d,r,c,R) \<equiv> {x\<in>X. \<langle>d`\<langle>c,x\<rangle>,R\<rangle> \<in> StrictVersion(r)}"


text\<open>Next we define notation for metric spaces. We will use additive notation for the group 
  operation but we do not  assume that the group is abelian. 
  Since for many theorems it is sufficient to assume the pseudometric axioms we will
  assume in this context that the sets $d,X,G,A,r$ form a pseudometric raher than a metric.\<close>

locale pmetric_space = 
  fixes d and X and G and A and r
  
  assumes ordGroupAssum: "IsAnOrdGroup(G,A,r)"

  assumes pmetricAssum: "IsApseudoMetric(d,X,G,A,r)"
  
  fixes zero ("\<zero>")
  defines zero_def [simp]: "\<zero> \<equiv> TheNeutralElement(G,A)"

  fixes grop (infixl "\<ra>" 80)
  defines grop_def [simp]: "x\<ra>y \<equiv> A`\<langle>x,y\<rangle>"

  fixes grinv ("\<rm> _" 89)
  defines grinv_def [simp]: "(\<rm>x) \<equiv> GroupInv(G,A)`(x)"

  fixes lesseq (infix "\<lsq>" 68)
  defines lesseq_def [simp]: "x \<lsq> y \<equiv> \<langle> x,y\<rangle> \<in> r"

  fixes sless (infix "\<ls>" 68)
  defines sless_def [simp]: "x \<ls> y \<equiv> x\<lsq>y \<and> x\<noteq>y"

  fixes nonnegative ("G\<^sup>+")
  defines nonnegative_def [simp]: "G\<^sup>+ \<equiv> Nonnegative(G,A,r)"

  fixes positive ("G\<^sub>+")
  defines positive_def [simp]: "G\<^sub>+ \<equiv> PositiveSet(G,A,r)"

  fixes setinv ("\<sm> _" 72)
  defines setninv_def [simp]: "\<sm>C \<equiv> GroupInv(G,A)``(C)"

  fixes abs 
  defines abs_def [simp]: "abs(x) \<equiv> AbsoluteValue(G,A,r)`(x)"

  fixes oddext ("_ \<degree>")
  defines oddext_def [simp]: "f\<degree> \<equiv> OddExtension(G,A,r,f)"

  fixes disk
  defines disk_def [simp]: "disk(c,R) \<equiv> Disk(X,d,r,c,R)"

text\<open> The theorems proven the in the \<open>group3\<close> locale are valid in the \<open>pmetric_space\<close> locale. \<close>

sublocale 
  pmetric_space < group3 G A r zero grop grinv lesseq sless nonnegative positive setinv abs oddext 
  using ordGroupAssum unfolding group3_def by auto

text\<open> The theorems proven the in the \<open>group0\<close> locale are valid in the \<open>pmetric_space\<close> locale. \<close>

sublocale pmetric_space < group0 G A zero grop grinv
   using ordGroupAssum unfolding group0_def IsAnOrdGroup_def by auto

text\<open> The next lemma shows the definition of the pseudometric in the notation used in the 
  \<open>metric_space\<close> context.\<close>

lemma (in pmetric_space) pmetric_properties: shows 
  "d: X\<times>X \<rightarrow> G\<^sup>+"
  "\<forall>x\<in>X. d`\<langle>x,x\<rangle> = \<zero>"
  "\<forall>x\<in>X.\<forall>y\<in>X. d`\<langle>x,y\<rangle> = d`\<langle>y,x\<rangle>"
  "\<forall>x\<in>X.\<forall>y\<in>X.\<forall>z\<in>X. d`\<langle>x,z\<rangle> \<lsq> d`\<langle>x,y\<rangle> \<ra> d`\<langle>y,z\<rangle>"
  using pmetricAssum unfolding IsApseudoMetric_def by auto

text\<open>The definition of the disk in the notation used in the \<open>pmetric_space\<close> context:\<close>

lemma (in pmetric_space) disk_definition: shows "disk(c,R) = {x\<in>X. d`\<langle>c,x\<rangle> \<ls> R}"
proof -
  have "disk(c,R) = Disk(X,d,r,c,R)" by simp
  then have "disk(c,R) = {x\<in>X. \<langle>d`\<langle>c,x\<rangle>,R\<rangle> \<in> StrictVersion(r)}" unfolding Disk_def by simp
  moreover have "\<forall>x\<in>X. \<langle>d`\<langle>c,x\<rangle>,R\<rangle> \<in> StrictVersion(r) \<longleftrightarrow> d`\<langle>c,x\<rangle> \<ls> R"
    using def_of_strict_ver by simp
  ultimately show ?thesis by auto
qed

text\<open>If the radius is positive then center is in disk.\<close>

lemma (in pmetric_space) center_in_disk: assumes "c\<in>X" and "R\<in>G\<^sub>+" shows "c \<in> disk(c,R)"
  using pmetricAssum assms IsApseudoMetric_def PositiveSet_def disk_definition by simp
  
text\<open>A technical lemma that allows us to shorten some proofs: \<close>

lemma (in pmetric_space) radius_in_group: assumes "c\<in>X" and "x \<in> disk(c,R)"
  shows "R\<in>G" "\<zero>\<ls>R" "R\<in>G\<^sub>+" "((\<rm>d`\<langle>c,x\<rangle>) \<ra> R) \<in> G\<^sub>+"
proof -
  from assms(2) have "x\<in>X" and "d`\<langle>c,x\<rangle> \<ls> R" using disk_definition by auto
  with assms(1) show "\<zero>\<ls>R" using pmetric_properties(1) apply_funtype 
      OrderedGroup_ZF_1_L2 group_strict_ord_transit by blast
  then show "R\<in>G" and "R\<in>G\<^sub>+" using OrderedGroup_ZF_1_L2A less_are_members by auto
  from assms(1) \<open>x\<in>X\<close> have "d`\<langle>c,x\<rangle> \<in> G" 
    using pmetric_properties(1) apply_funtype OrderedGroup_ZF_1_L4E by auto
  then have "(\<rm>d`\<langle>c,x\<rangle>) \<in> G" using inverse_in_group by simp
  with \<open>R\<in>G\<close> \<open>d`\<langle>c,x\<rangle> \<ls> R\<close> have "(\<rm>d`\<langle>c,x\<rangle>) \<ra> d`\<langle>c,x\<rangle> \<ls> (\<rm>d`\<langle>c,x\<rangle>) \<ra> R"
    using group_strict_ord_transl_inv(2) by simp
  with \<open>d`\<langle>c,x\<rangle> \<in> G\<close> show "((\<rm>d`\<langle>c,x\<rangle>) \<ra> R) \<in> G\<^sub>+" 
    using group0_2_L6 OrderedGroup_ZF_1_L2A less_are_members by auto
qed

text\<open>If a point $x$ is inside a disk $B$ and $m\leq R-d(c,x)$ then the disk centered 
  at the point $x$ and with radius $m$ is contained in the disk $B$. \<close>

lemma (in pmetric_space) disk_in_disk: 
  assumes "c\<in>X"  and "x \<in> disk(c,R)" and "m \<lsq> (\<rm>d`\<langle>c,x\<rangle>) \<ra> R"
  shows "disk(x,m) \<subseteq> disk(c,R)"
proof
  fix y assume "y \<in> disk(x,m)"
  then have "d`\<langle>x,y\<rangle> \<ls> m" using disk_definition by simp
  from assms(1,2) \<open>y \<in> disk(x,m)\<close> have "R\<in>G" "x\<in>X" "y\<in>X" using radius_in_group(1) disk_definition
    by auto
  with assms(1) have "d`\<langle>c,y\<rangle> \<lsq> d`\<langle>c,x\<rangle> \<ra> d`\<langle>x,y\<rangle>" using pmetric_properties(4) by simp
  from assms(1) \<open>x\<in>X\<close> have "d`\<langle>c,x\<rangle> \<in> G" 
    using pmetric_properties(1) apply_funtype OrderedGroup_ZF_1_L4E by auto
  with \<open>d`\<langle>x,y\<rangle> \<ls> m\<close> assms(3) have "d`\<langle>c,x\<rangle> \<ra> d`\<langle>x,y\<rangle> \<ls> d`\<langle>c,x\<rangle> \<ra> ((\<rm>d`\<langle>c,x\<rangle>) \<ra> R)"
    using OrderedGroup_ZF_1_L4A group_strict_ord_transl_inv(2) by blast
  with \<open>d`\<langle>c,x\<rangle> \<in> G\<close> \<open>R\<in>G\<close> \<open>d`\<langle>c,y\<rangle> \<lsq> d`\<langle>c,x\<rangle> \<ra> d`\<langle>x,y\<rangle>\<close> \<open>y\<in>X\<close> show "y \<in> disk(c,R)"
    using inv_cancel_two(4) group_strict_ord_transit disk_definition by simp
qed

text\<open> If we assume that the order on the group makes the positive set a meet semi-lattice (i.e.
  every two-element subset of $G_+$ has a greatest lower bound) then 
  the collection of disks centered at points of the space and with radii in the positive set 
  of the group satisfies the base condition. The meet semi-lattice assumption can be weakened 
  to "each two-element subset of $G_+$ has a lower bound in $G_+$", but we don't do that here. \<close>

lemma (in pmetric_space) disks_form_base: 
  assumes "IsMeetSemilattice(G\<^sub>+,r \<inter> G\<^sub>+\<times>G\<^sub>+)"
  defines "B \<equiv> \<Union>c\<in>X. {disk(c,R). R\<in>G\<^sub>+}"
  shows "B {satisfies the base condition}"
proof -
  { fix U V assume "U\<in>B" "V\<in>B"
    fix x assume "x\<in>U\<inter>V"
    have "\<exists>W\<in>B. x\<in>W \<and> W\<subseteq>U\<inter>V"
    proof -
      from assms(2) \<open>U\<in>B\<close> \<open>V\<in>B\<close> obtain "c\<^sub>U"  "c\<^sub>V" "R\<^sub>U"  "R\<^sub>V" 
        where "c\<^sub>U \<in> X" "R\<^sub>U \<in> G\<^sub>+" "c\<^sub>V \<in> X" "R\<^sub>V \<in> G\<^sub>+" "U = disk(c\<^sub>U,R\<^sub>U)" "V = disk(c\<^sub>V,R\<^sub>V)"
        by auto
      with \<open>x\<in>U\<inter>V\<close> have "x \<in> disk(c\<^sub>U,R\<^sub>U)" and "x \<in> disk(c\<^sub>V,R\<^sub>V)" by auto
      then have "x\<in>X" "d`\<langle>c\<^sub>U,x\<rangle> \<ls> R\<^sub>U" "d`\<langle>c\<^sub>V,x\<rangle> \<ls> R\<^sub>V" using disk_definition by auto
      let ?m\<^sub>U = "(\<rm> d`\<langle>c\<^sub>U,x\<rangle>) \<ra> R\<^sub>U"
      let ?m\<^sub>V = "(\<rm> d`\<langle>c\<^sub>V,x\<rangle>) \<ra> R\<^sub>V"
      from \<open>c\<^sub>U\<in>X\<close> \<open>x\<in>disk(c\<^sub>U,R\<^sub>U)\<close> \<open>c\<^sub>V\<in>X\<close> \<open>x\<in>disk(c\<^sub>V,R\<^sub>V)\<close> have "?m\<^sub>U\<in>G\<^sub>+" and "?m\<^sub>V\<in>G\<^sub>+" 
        using radius_in_group(4) by auto
      let ?m = "Meet(G\<^sub>+,r \<inter> G\<^sub>+\<times>G\<^sub>+)`\<langle>?m\<^sub>U,?m\<^sub>V\<rangle>"
      let ?W = "disk(x,?m)"
      from assms(1) \<open>?m\<^sub>U \<in> G\<^sub>+\<close> \<open>?m\<^sub>V \<in> G\<^sub>+\<close> have  "\<langle>?m,?m\<^sub>U\<rangle> \<in> r \<inter> G\<^sub>+\<times>G\<^sub>+" 
        using meet_val(3) by blast
      moreover from assms(1) \<open>?m\<^sub>U \<in> G\<^sub>+\<close> \<open>?m\<^sub>V \<in> G\<^sub>+\<close> have  "\<langle>?m,?m\<^sub>V\<rangle> \<in> r \<inter> G\<^sub>+\<times>G\<^sub>+" 
        using meet_val(4) by blast
      moreover from assms(1) \<open>?m\<^sub>U \<in> G\<^sub>+\<close> \<open>?m\<^sub>V \<in> G\<^sub>+\<close> have "?m \<in> G\<^sub>+"
        using meet_val(1) by simp
      ultimately have "?m \<in> G\<^sub>+" "?m \<lsq> ?m\<^sub>U" "?m \<lsq> ?m\<^sub>V" by auto
      with \<open>c\<^sub>U \<in> X\<close> \<open>x \<in> disk(c\<^sub>U,R\<^sub>U)\<close> \<open>c\<^sub>V \<in> X\<close> \<open>x \<in> disk(c\<^sub>V,R\<^sub>V)\<close> \<open>U = disk(c\<^sub>U,R\<^sub>U)\<close> \<open>V = disk(c\<^sub>V,R\<^sub>V)\<close>
      have "?W \<subseteq> U\<inter>V" using disk_in_disk by blast
      moreover from assms(2) \<open>x\<in>X\<close> \<open>?m \<in> G\<^sub>+\<close> have "?W \<in> B" and "x\<in>?W" using center_in_disk
        by auto
      ultimately show ?thesis by auto
    qed      
  } then show ?thesis unfolding SatisfiesBaseCondition_def by auto
qed

text\<open>Unions of disks form a topology, hence (pseudo)metric spaces are topological spaces. We have
  to add the assumption that the positive set is not empty. This is necessary to show that we can
  cover the space with disks and it does not look like it follows from anything we have assumed 
  so far. \<close>

theorem (in pmetric_space) pmetric_is_top: 
  assumes "IsMeetSemilattice(G\<^sub>+,r \<inter> G\<^sub>+\<times>G\<^sub>+)" "G\<^sub>+\<noteq>0"
  defines "B \<equiv> \<Union>c\<in>X. {disk(c,R). R\<in>G\<^sub>+}" 
  defines "T \<equiv> {\<Union>A. A \<in> Pow(B)}"
  shows "T {is a topology}"  "B {is a base for} T"  "\<Union>T = X"
proof -
  from assms(1,3,4) show  "T {is a topology}"  "B {is a base for} T" 
    using disks_form_base Top_1_2_T1 by auto
  then have "\<Union>T = \<Union>B" using Top_1_2_L5 by simp
  moreover have "\<Union>B = X"
  proof
    from assms(3) show "\<Union>B \<subseteq> X" using disk_definition by auto
    { fix x assume "x\<in>X" 
      from assms(2) obtain R where "R\<in>G\<^sub>+" by auto
      with assms(3) \<open>x\<in>X\<close> have "x \<in> \<Union>B" using center_in_disk by auto
    } thus "X \<subseteq> \<Union>B" by auto
  qed 
  ultimately show "\<Union>T = X" by simp
qed

end
