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

section \<open> Basic properties of real numbers \<close>

theory Real_ZF_2 imports OrderedField_ZF MetricSpace_ZF
begin

text\<open> Isabelle/ZF and IsarMathLib do not have a set of real numbers built-in. 
  The \<open>Real_ZF\<close> and \<open>Real_ZF_1\<close> theories provide a construction but here we do not use it in any way
  and we just assume that we have a model of real numbers (i.e. a completely ordered field) 
  as defined in the \<open>Ordered_Field\<close> theory. The construction only assures us that objects with 
  the desired properties exist in the ZF world. \<close>

subsection\<open>Basic notation for real numbers\<close>

text\<open> In this section we define notation that we will use whenever real numbers play a role, i.e. 
  most of mathematics.\<close>

text\<open> The next locale sets up notation for contexts where real numbers are used. \<close>

locale reals =
  fixes Reals("\<real>") and Add and Mul and ROrd
  assumes R_are_reals: "IsAmodelOfReals(\<real>,Add,Mul, ROrd)"

  fixes zero ("\<zero>")
  defines zero_def[simp]: "\<zero> \<equiv> TheNeutralElement(\<real>,Add)"

  fixes one ("\<one>")
  defines one_def[simp]: "\<one> \<equiv> TheNeutralElement(\<real>,Mul)"

  fixes realmul (infixl "\<rmu>" 71)
  defines realmul_def[simp]: "x \<rmu> y \<equiv> Mul`\<langle>x,y\<rangle>"

  fixes realadd (infixl "\<ra>" 69)
  defines realadd_def[simp]: "x \<ra> y \<equiv> Add`\<langle>x,y\<rangle>"

  fixes realminus("\<rm> _" 89)
  defines realminus_def[simp]: "(\<rm>x) \<equiv> GroupInv(\<real>,Add)`(x)"

  fixes realsub (infixl "\<rs>" 90)
  defines realsub_def [simp]: "x\<rs>y \<equiv> x\<ra>(\<rm>y)"

  fixes lesseq (infix "\<lsq>" 68)
  defines lesseq_def [simp]: "x \<lsq> y \<equiv> \<langle>x,y\<rangle> \<in>  ROrd"

  fixes sless (infix "\<ls>" 68)
  defines sless_def [simp]: "x \<ls> y \<equiv> x\<lsq>y \<and> x\<noteq>y"

  fixes nonnegative ("\<real>\<^sup>+")
  defines nonnegative_def[simp]: "\<real>\<^sup>+ \<equiv> Nonnegative(\<real>,Add, ROrd)"

  fixes positiveset ("\<real>\<^sub>+")
  defines positiveset_def[simp]: "\<real>\<^sub>+ \<equiv> PositiveSet(\<real>,Add, ROrd)"

  fixes setinv ("\<sm> _" 72)
  defines setninv_def [simp]: "\<sm>A \<equiv> GroupInv(\<real>,Add)``(A)"

  fixes non_zero ("\<real>\<^sub>0")
  defines non_zero_def[simp]: "\<real>\<^sub>0 \<equiv> \<real>-{\<zero>}"

  fixes abs ("\<bar> _ \<bar>")
  defines abs_def [simp]: "\<bar>x\<bar> \<equiv> AbsoluteValue(\<real>,Add,ROrd)`(x)"

  fixes dist
  defines dist_def[simp]: "dist \<equiv> {\<langle>p,\<bar>fst(p) \<rs> snd(p)\<bar>\<rangle> . p \<in> \<real>\<times>\<real>}" 

  fixes two ("\<two>")
  defines two_def[simp]: "\<two> \<equiv> \<one> \<ra> \<one>"

  fixes inv ("_\<inverse> " [96] 97)
  defines inv_def[simp]: 
    "x\<inverse> \<equiv> GroupInv(\<real>\<^sub>0,restrict(Mul,\<real>\<^sub>0\<times>\<real>\<^sub>0))`(x)"

  fixes realsq ("_\<^sup>2" [96] 97)
  defines realsq_def [simp]: "x\<^sup>2 \<equiv> x\<rmu>x"

  fixes oddext ("_ \<degree>")
  defines oddext_def [simp]: "f\<degree> \<equiv> OddExtension(\<real>,Add,ROrd,f)"

  fixes disk
  defines disk_def [simp]: "disk(c,r) \<equiv> Disk(\<real>,dist,ROrd,c,r)"

text\<open> The assumtions of the \<open>field1\<close> locale (that sets the context for ordered fields) 
  hold in the \<open>reals\<close> locale \<close>

lemma (in reals) field1_is_valid: shows "field1(\<real>, Add, Mul,ROrd)"
proof
  from R_are_reals show "IsAring(\<real>, Add, Mul)" and "Mul {is commutative on} \<real>"
    and "ROrd \<subseteq> \<real> \<times> \<real>" and "IsLinOrder(\<real>,  ROrd)" 
    and "\<forall>x y. \<forall>z\<in>\<real>. \<langle>x, y\<rangle> \<in> ROrd \<longrightarrow> \<langle>Add`\<langle>x, z\<rangle>, Add`\<langle>y, z\<rangle>\<rangle> \<in> ROrd"
    and "Nonnegative(\<real>, Add, ROrd) {is closed under} Mul"
    and "TheNeutralElement(\<real>, Add) \<noteq> TheNeutralElement(\<real>, Mul)"
    and "\<forall>x\<in>\<real>. x \<noteq> TheNeutralElement(\<real>,Add) \<longrightarrow> (\<exists>y\<in>\<real>. Mul`\<langle>x, y\<rangle> = TheNeutralElement(\<real>,Mul))"
    using IsAmodelOfReals_def IsAnOrdField_def IsAnOrdRing_def by auto
qed
  
text\<open> We can use theorems proven in the  \<open>field1\<close> locale in the \<open>reals\<close> locale. 
  Note that since the the \<open>field1\<close> locale is an extension of the \<open>ring1\<close> locale, which is an 
  extension of \<open>ring0\<close> locale , this makes available also the theorems proven in 
  the \<open>ring1\<close> and \<open>ring0\<close> locales. \<close>

sublocale reals < field1 Reals Add Mul realadd realminus realsub realmul zero one two realsq ROrd
  using field1_is_valid by auto

text\<open> The \<open>group3\<close> locale from the \<open>OrderedGroup_ZF\<close> theory defines context for theorems about 
  ordered groups. We can use theorems proven in there in the \<open>reals\<close> locale as real numbers 
  with addition form an ordered group. \<close>

sublocale reals < group3 Reals Add ROrd zero realadd realminus lesseq sless nonnegative positiveset
  unfolding group3_def using OrdRing_ZF_1_L4 by auto

text\<open>Since real numbers with addition form a group we can use the theorems proven in the  \<open>group0\<close> 
  locale defined in the \<open>Group_ZF\<close> theory in the \<open>reals\<close> locale. \<close>

sublocale reals < group0 Reals Add zero realadd realminus 
  unfolding group3_def using OrderedGroup_ZF_1_L1 by auto

text\<open>Let's recall basic properties of the real line. \<close>

lemma (in reals) basic_props: shows  "ROrd {is total on} \<real>" and "Add {is commutative on} \<real>"
  using OrdRing_ZF_1_L4(2,3) by auto 

text\<open> The distance function \<open>dist\<close> defined in the \<open>reals\<close> locale is a metric. \<close>

lemma (in reals) dist_is_metric: shows 
  "dist : \<real>\<times>\<real> \<rightarrow> \<real>\<^sup>+" 
  "\<forall>x\<in>\<real>.\<forall>y\<in>\<real>. dist`\<langle>x,y\<rangle> = \<bar>x \<rs> y\<bar>"
  "\<forall>x\<in>\<real>.dist`\<langle>x,x\<rangle> = \<zero>"
  "\<forall>x\<in>\<real>.\<forall>y\<in>\<real>. dist`\<langle>x,y\<rangle> = dist`\<langle>y,x\<rangle>"
  "\<forall>x\<in>\<real>.\<forall>y\<in>\<real>.\<forall>z\<in>\<real>. \<bar>x \<rs> z\<bar> \<lsq> \<bar>x \<rs> y\<bar> \<ra> \<bar>y \<rs> z\<bar>"
  "\<forall>x\<in>\<real>.\<forall>y\<in>\<real>.\<forall>z\<in>\<real>. dist`\<langle>x,z\<rangle> \<lsq> dist`\<langle>x, y\<rangle> \<ra> dist`\<langle>y,z\<rangle>"
  "\<forall>x\<in>\<real>.\<forall>y\<in>\<real>. dist`\<langle>x,y\<rangle> = \<zero> \<longrightarrow> x=y" 
  "IsApseudoMetric(dist,\<real>,\<real>,Add,ROrd)"
  "IsAmetric(dist,\<real>,\<real>,Add,ROrd)"
proof -
  show I: "dist : \<real>\<times>\<real> \<rightarrow> \<real>\<^sup>+" using group_op_closed inverse_in_group OrdRing_ZF_1_L4 
      OrderedGroup_ZF_3_L3B  ZF_fun_from_total by simp
  then show II:"\<forall>x\<in>\<real>.\<forall>y\<in>\<real>. dist`\<langle>x,y\<rangle> = \<bar>x\<rs>y\<bar>" using ZF_fun_from_tot_val0 by auto
  then show III: "\<forall>x\<in>\<real>.dist`\<langle>x,x\<rangle> = \<zero>" using group0_2_L6 OrderedGroup_ZF_3_L2A by simp
  { fix x y
    assume "x\<in>\<real>" "y\<in>\<real>"
    then have "(\<rm>(x\<rs>y)) = y\<rs>x" using group0_2_L12 by simp
    moreover from \<open>x\<in>\<real>\<close> \<open>y\<in>\<real>\<close> have "\<bar>\<rm>(x\<rs>y)\<bar> =\<bar>x\<rs>y\<bar>"
      using group_op_closed inverse_in_group basic_props(1) OrderedGroup_ZF_3_L7A
      by simp
    ultimately have "\<bar>y\<rs>x\<bar> = \<bar>x\<rs>y\<bar>" by simp
    with \<open>x\<in>\<real>\<close> \<open>y\<in>\<real>\<close> II have "dist`\<langle>x,y\<rangle> = dist`\<langle>y,x\<rangle>" by simp
  } thus IV: "\<forall>x\<in>\<real>.\<forall>y\<in>\<real>. dist`\<langle>x,y\<rangle> = dist`\<langle>y,x\<rangle>" by simp
  { fix x y
    assume "x\<in>\<real>" "y\<in>\<real>" "dist`\<langle>x,y\<rangle> = \<zero>"  
    with II have "\<bar>x\<rs>y\<bar> = \<zero>" by simp
    with \<open>x\<in>\<real>\<close> \<open>y\<in>\<real>\<close> have "x\<rs>y = \<zero>" 
      using group_op_closed inverse_in_group OrderedGroup_ZF_3_L3D by auto
    with \<open>x\<in>\<real>\<close> \<open>y\<in>\<real>\<close> have"x=y" using group0_2_L11A by simp
  } thus V: "\<forall>x\<in>\<real>.\<forall>y\<in>\<real>. dist`\<langle>x,y\<rangle> = \<zero> \<longrightarrow> x=y" by auto
  { fix x y z
    assume "x\<in>\<real>" "y\<in>\<real>" "z\<in>\<real>"
    then have "\<bar>x\<rs>z\<bar> = \<bar>(x\<rs>y)\<ra>(y \<rs> z)\<bar>" using cancel_middle(5) by simp
    with \<open>x\<in>\<real>\<close> \<open>y\<in>\<real>\<close> \<open>z\<in>\<real>\<close> have "\<bar>x\<rs>z\<bar>  \<lsq> \<bar>x\<rs>y\<bar> \<ra> \<bar>y \<rs> z\<bar>"
      using group_op_closed inverse_in_group OrdRing_ZF_1_L4(2,3) OrdGroup_triangle_ineq
      by simp
  } thus  "\<forall>x\<in>\<real>.\<forall>y\<in>\<real>.\<forall>z\<in>\<real>. \<bar>x \<rs> z\<bar> \<lsq> \<bar>x \<rs> y\<bar> \<ra> \<bar>y \<rs> z\<bar>" by simp
  with II show "\<forall>x\<in>\<real>.\<forall>y\<in>\<real>.\<forall>z\<in>\<real>. dist`\<langle>x,z\<rangle> \<lsq> dist`\<langle>x, y\<rangle> \<ra> dist`\<langle>y,z\<rangle>" by auto
  with I III IV V show "IsApseudoMetric(dist,\<real>,\<real>,Add,ROrd)" and "IsAmetric(dist,\<real>,\<real>,Add,ROrd)"
    unfolding IsApseudoMetric_def IsAmetric_def by auto
qed

text\<open>Real numbers form an ordered loop.\<close>

lemma (in reals) reals_loop: shows "IsAnOrdLoop(\<real>,Add,ROrd)"
proof -
  have "IsAloop(\<real>,Add)" using group_is_loop by simp
  moreover from R_are_reals have "ROrd \<subseteq> \<real> \<times> \<real>" and "IsPartOrder(\<real>,ROrd)"
    using IsAmodelOfReals_def IsAnOrdField_def IsAnOrdRing_def Order_ZF_1_L2 
    by auto
  moreover 
  { fix x y z assume A: "x\<in>\<real>" "y\<in>\<real>"  "z\<in>\<real>"
    then have "x\<lsq>y \<longleftrightarrow> x\<ra>z \<lsq> y\<ra>z" 
      using ord_transl_inv ineq_cancel_right by blast
    moreover from A have "x\<lsq>y \<longleftrightarrow> z\<ra>x \<lsq> z\<ra>y"
      using ord_transl_inv OrderedGroup_ZF_1_L5AE by blast
    ultimately have "(x\<lsq>y \<longleftrightarrow> x\<ra>z \<lsq> y\<ra>z) \<and> (x\<lsq>y \<longleftrightarrow> z\<ra>x \<lsq> z\<ra>y)"
      by simp
  }
  ultimately show "IsAnOrdLoop(\<real>,Add,ROrd)" unfolding IsAnOrdLoop_def by auto
qed

text\<open> The assumptions of the  \<open>pmetric_space\<close> locale hold in the \<open>reals\<close> locale. \<close>

lemma (in reals) pmetric_space_valid: shows "pmetric_space(\<real>,Add, ROrd,dist,\<real>)" 
  unfolding pmetric_space_def pmetric_space_axioms_def loop1_def
  using reals_loop dist_is_metric(8) 
  by blast 

text\<open> The assumptions of the  \<open>metric_space\<close> locale hold in the \<open>reals\<close> locale. \<close>

lemma (in reals) metric_space_valid: shows "metric_space(\<real>,Add, ROrd,dist,\<real>)"
proof -
  have "\<forall>x\<in>\<real>. \<forall>y\<in>\<real>. dist`\<langle>x,y\<rangle>=\<zero> \<longrightarrow> x=y"
    using dist_is_metric(9) unfolding IsAmetric_def by auto
  then show ?thesis unfolding metric_space_def metric_space_axioms_def 
    using pmetric_space_valid by simp
qed

text\<open>Some properties of the order relation on reals: \<close>

lemma (in reals) pos_is_lattice: shows 
  "IsLinOrder(\<real>,ROrd)"
  "IsLinOrder(\<real>\<^sub>+,ROrd \<inter> \<real>\<^sub>+\<times>\<real>\<^sub>+)"
  "(ROrd \<inter> \<real>\<^sub>+\<times>\<real>\<^sub>+) {is a lattice on} \<real>\<^sub>+"
proof -
  show "IsLinOrder(\<real>,ROrd)" using OrdRing_ZF_1_L1 unfolding IsAnOrdRing_def by simp
  moreover have "\<real>\<^sub>+ \<subseteq> \<real>" using pos_set_in_gr by simp 
  ultimately show "IsLinOrder(\<real>\<^sub>+,ROrd \<inter> \<real>\<^sub>+\<times>\<real>\<^sub>+)" using ord_linear_subset(2) by simp
  moreover have "(ROrd \<inter> \<real>\<^sub>+\<times>\<real>\<^sub>+) \<subseteq> \<real>\<^sub>+\<times>\<real>\<^sub>+" by auto
  ultimately show "(ROrd \<inter> \<real>\<^sub>+\<times>\<real>\<^sub>+) {is a lattice on} \<real>\<^sub>+" using lin_is_latt by simp
qed

text\<open>Of course the set of positive real numbers is nonempty as one is there.\<close>

lemma (in reals) pos_non_empty: shows "\<real>\<^sub>+\<noteq>0"
  using R_are_reals ordring_one_is_pos 
  unfolding IsAmodelOfReals_def IsAnOrdField_def by auto

text\<open> We define the topology on reals as one consisting of the unions of open disks. \<close>

definition (in reals) RealTopology ("\<tau>\<^sub>\<real>") 
  where "\<tau>\<^sub>\<real> \<equiv> {\<Union>A. A \<in> Pow(\<Union>c\<in>\<real>.{disk(c,r). r \<in> \<real>\<^sub>+})}"
  
text\<open>Real numbers form a Hausdorff topological space with topology generated by open disks. \<close>

theorem (in reals) reals_is_top: 
  shows "\<tau>\<^sub>\<real> {is a topology}" "\<Union>\<tau>\<^sub>\<real> = \<real>" "\<tau>\<^sub>\<real> {is T\<^sub>2}"
proof -
  let ?B = "\<Union>c\<in>\<real>.{disk(c,r). r \<in> \<real>\<^sub>+}"
  have "pmetric_space(\<real>,Add, ROrd,dist,\<real>)" using pmetric_space_valid by simp
  moreover have "metric_space(\<real>,Add, ROrd,dist,\<real>)" using metric_space_valid by simp
  moreover have "ROrd {down-directs} \<real>\<^sub>+"
    using pos_is_lattice(3) pos_non_empty meet_down_directs down_dir_mono
    unfolding IsAlattice_def by blast
  moreover have "?B = (\<Union>c\<in>\<real>.{disk(c,r). r \<in> \<real>\<^sub>+})" by simp
  moreover have "\<tau>\<^sub>\<real> =  {\<Union>A. A \<in> Pow(?B)}" unfolding RealTopology_def by simp
  ultimately show "\<tau>\<^sub>\<real> {is a topology}"  "\<Union>\<tau>\<^sub>\<real> = \<real>"  "\<tau>\<^sub>\<real> {is T\<^sub>2}"
    using pmetric_space.pmetric_is_top metric_space.metric_space_T2
    by auto
qed

end
