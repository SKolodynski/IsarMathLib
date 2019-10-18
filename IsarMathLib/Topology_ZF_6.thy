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

section \<open>Topology 6\<close>

theory Topology_ZF_6 imports Topology_ZF_4 Topology_ZF_2 Topology_ZF_1

begin

text\<open>
  This theory deals with the relations between continuous functions and convergence
  of filters. At the end of the file there some results about the building of functions
  in cartesian products.
\<close>

subsection\<open>Image filter\<close>

text\<open>First of all, we will define the appropriate tools to work with functions
and filters together.\<close>

text\<open>We define the image filter as the collections of supersets of of images of sets from a filter.
\<close>

definition
  ImageFilter ("_[_].._" 98)
  where "\<FF> {is a filter on} X \<Longrightarrow> f:X\<rightarrow>Y \<Longrightarrow> f[\<FF>]..Y \<equiv> {A\<in>Pow(Y). \<exists>D\<in>{f``(B) .B\<in>\<FF>}. D\<subseteq>A}"

text\<open>Note that in the previous definition, it is necessary to state
 $Y$ as the final set because $f$ is also a function to every superset of its range.
$X$ can be changed by \<open>domain(f)\<close> without any change in the definition.\<close>

lemma base_image_filter:
  assumes "\<FF> {is a filter on} X" "f:X\<rightarrow>Y"
  shows "{f``B .B\<in>\<FF>} {is a base filter} (f[\<FF>]..Y)" and "(f[\<FF>]..Y) {is a filter on} Y"
proof-
  {
    assume "0 \<in> {f``B .B\<in>\<FF>}"
    then obtain B where "B\<in>\<FF>" and f_B:"f``B=0" by auto
    then have "B\<in>Pow(X)" using assms(1) IsFilter_def by auto
    then have "f``B={f`b. b\<in>B}" using image_fun assms(2) by auto
    with f_B have "{f`b. b\<in>B}=0" by auto
    then have "B=0" by auto
    with \<open>B\<in>\<FF>\<close> have "False" using IsFilter_def assms(1) by auto
  }
  then have "0\<notin>{f``B .B\<in>\<FF>}" by auto
  moreover
  from assms(1) obtain S where "S\<in>\<FF>" using IsFilter_def by auto
  then have "f``S\<in>{f``B .B\<in>\<FF>}" by auto
  then have nA:"{f``B .B\<in>\<FF>}\<noteq>0" by auto
  moreover
  {
    fix A B
    assume "A\<in>{f``B .B\<in>\<FF>}" and "B\<in>{f``B .B\<in>\<FF>}"
    then obtain AB BB where "A=f``AB" "B=f``BB" "AB\<in>\<FF>" "BB\<in>\<FF>" by auto
    then have "A\<inter>B=(f``AB)\<inter>(f``BB)" by auto
    then have I: "f``(AB\<inter>BB)\<subseteq>A\<inter>B" by auto
    moreover
    from assms(1) I \<open>AB\<in>\<FF>\<close>\<open>BB\<in>\<FF>\<close> have "AB\<inter>BB\<in>\<FF>" using IsFilter_def by auto
    ultimately have "\<exists>D\<in>{f``B .B\<in>\<FF>}. D\<subseteq>A\<inter>B" by auto
  }
  then have "\<forall>A\<in>{f``B .B\<in>\<FF>}. \<forall>B\<in>{f``B .B\<in>\<FF>}. \<exists>D\<in>{f``B .B\<in>\<FF>}. D\<subseteq>A\<inter>B" by auto
  ultimately have sbc:"{f``B .B\<in>\<FF>} {satisfies the filter base condition}" 
    using SatisfiesFilterBase_def by auto
  moreover
  {
    fix t
    assume "t\<in>{f``B . B\<in>\<FF>}"
    then obtain B where "B\<in>\<FF>" and im_def:"f``B=t" by auto
    with assms(1) have "B\<in>Pow(X)" unfolding IsFilter_def by auto
    with im_def assms(2) have "t={f`x. x\<in>B}" using image_fun by auto
    with assms(2) \<open>B\<in>Pow(X)\<close> have "t\<subseteq>Y" using apply_funtype by auto
    }
  then have nB:"{f``B . B\<in>\<FF>}\<subseteq>Pow(Y)" by auto
  ultimately
  have "(({f``B .B\<in>\<FF>} {is a base filter} {A \<in> Pow(Y) . \<exists>D\<in>{f``B .B\<in>\<FF>}. D \<subseteq> A}) \<and> (\<Union>{A \<in> Pow(Y) . \<exists>D\<in>{f``B .B\<in>\<FF>}. D \<subseteq> A}=Y))" using base_unique_filter_set2 
    by force
  then have "{f``B .B\<in>\<FF>} {is a base filter} {A \<in> Pow(Y) . \<exists>D\<in>{f``B .B\<in>\<FF>}. D \<subseteq> A}" by auto
  with assms show "{f``B .B\<in>\<FF>} {is a base filter} (f[\<FF>]..Y)" using ImageFilter_def  by auto
  moreover
  note sbc
  moreover
  {
    from nA obtain D where I: "D\<in>{f``B .B\<in>\<FF>}" by blast
    moreover from I nB have "D\<subseteq>Y" by auto
    ultimately have "Y\<in>{A\<in>Pow(Y). \<exists>D\<in>{f``B .B\<in>\<FF>}. D\<subseteq>A}" by auto
  }
  then have "\<Union>{A\<in>Pow(Y). \<exists>D\<in>{f``B .B\<in>\<FF>}. D\<subseteq>A}=Y" by auto
  ultimately show "(f[\<FF>]..Y) {is a filter on} Y" using basic_filter
    ImageFilter_def assms by auto 
qed

subsection\<open>Continuous at a point vs. globally continuous\<close>

text\<open>In this section we show that continuity of a function implies local continuity (at a point)
  and that local continuity at all points implies (global) continuity.\<close>

text\<open>If a function is continuous, then it is continuous at every point.\<close>

lemma cont_global_imp_continuous_x:
  assumes "x\<in>\<Union>\<tau>\<^sub>1" "IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2,f)" "f:(\<Union>\<tau>\<^sub>1)\<rightarrow>(\<Union>\<tau>\<^sub>2)" "x\<in>\<Union>\<tau>\<^sub>1"
  shows "\<forall>U\<in>\<tau>\<^sub>2. f`(x)\<in>U \<longrightarrow> (\<exists>V\<in>\<tau>\<^sub>1. x\<in>V \<and> f``(V)\<subseteq>U)"
proof-
  {
    fix U
    assume AS:"U\<in>\<tau>\<^sub>2" "f`(x)\<in>U"
    then have "f-``(U)\<in>\<tau>\<^sub>1" using assms(2) IsContinuous_def by auto
    moreover
    from assms(3) have "f``(f-``(U))\<subseteq>U" using function_image_vimage fun_is_fun 
      by auto
    moreover
    from assms(3) assms(4) AS(2) have "x\<in>f-``(U)" using func1_1_L15 by auto
    ultimately have "\<exists>V\<in>\<tau>\<^sub>1. x\<in>V \<and> f``V\<subseteq>U" by auto
  }
  then show "\<forall>U\<in>\<tau>\<^sub>2. f`(x)\<in>U \<longrightarrow> (\<exists>V\<in>\<tau>\<^sub>1. x\<in>V \<and> f``(V)\<subseteq>U)" by auto
qed

text\<open>A function that is continuous at every point of its domain is continuous.\<close>

lemma ccontinuous_all_x_imp_cont_global:
  assumes "\<forall>x\<in>\<Union>\<tau>\<^sub>1. \<forall>U\<in>\<tau>\<^sub>2. f`x\<in>U \<longrightarrow> (\<exists>V\<in>\<tau>\<^sub>1. x\<in>V \<and> f``V\<subseteq>U)" "f\<in>(\<Union>\<tau>\<^sub>1)\<rightarrow>(\<Union>\<tau>\<^sub>2)"  and 
    "\<tau>\<^sub>1 {is a topology}"
  shows "IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2,f)"
proof-
  {
    fix U
    assume "U\<in>\<tau>\<^sub>2"
    {
      fix x
      assume AS: "x\<in>f-``U"
      note \<open>U\<in>\<tau>\<^sub>2\<close>
      moreover
      from assms(2) have "f -`` U \<subseteq> \<Union>\<tau>\<^sub>1" using func1_1_L6A by auto
      with AS have "x\<in>\<Union>\<tau>\<^sub>1" by auto
      with assms(1) have "\<forall>U\<in>\<tau>\<^sub>2. f`x\<in>U \<longrightarrow> (\<exists>V\<in>\<tau>\<^sub>1. x\<in>V \<and> f``V\<subseteq>U)" by auto
      moreover
      from AS assms(2) have "f`x\<in>U" using func1_1_L15 by auto
      ultimately have "\<exists>V\<in>\<tau>\<^sub>1. x\<in>V \<and> f``V\<subseteq>U" by auto
      then obtain V where I: "V\<in>\<tau>\<^sub>1" "x\<in>V" "f``(V)\<subseteq>U" by auto
      moreover
      from I have "V\<subseteq>\<Union>\<tau>\<^sub>1" by auto
      moreover
      from assms(2) \<open>V\<subseteq>\<Union>\<tau>\<^sub>1\<close> have "V\<subseteq>f-``(f``V)" using func1_1_L9 by auto
      ultimately have "V \<subseteq> f-``(U)" by blast
      with \<open>V\<in>\<tau>\<^sub>1\<close> \<open>x\<in>V\<close> have "\<exists>V\<in>\<tau>\<^sub>1. x\<in>V \<and> V \<subseteq> f-``(U)" by auto
    } hence "\<forall>x\<in>f-``(U). \<exists>V\<in>\<tau>\<^sub>1. x\<in>V \<and> V\<subseteq>f-``(U)" by auto
    with assms(3) have "f-``(U) \<in> \<tau>\<^sub>1" using topology0.open_neigh_open topology0_def 
      by auto
  }
  hence "\<forall>U\<in>\<tau>\<^sub>2. f-``U\<in>\<tau>\<^sub>1" by auto
  then show ?thesis using IsContinuous_def by auto
qed

subsection\<open>Continuous functions and filters\<close>

text\<open>In this section we consider the relations between filters and continuity.\<close> 

text\<open>If the function is continuous then 
  if the filter converges to a point the image filter converges to the image point.\<close>

lemma (in two_top_spaces0) cont_imp_filter_conver_preserved:
  assumes "\<FF> {is a filter on} X\<^sub>1" "f {is continuous}" "\<FF> \<rightarrow>\<^sub>F x {in} \<tau>\<^sub>1"
  shows "(f[\<FF>]..X\<^sub>2) \<rightarrow>\<^sub>F (f`(x)) {in} \<tau>\<^sub>2"
proof -
  from assms(1) assms(3) have "x\<in>X\<^sub>1" 
    using topology0.FilterConverges_def topol_cntxs_valid(1) X1_def by auto
  have "topology0(\<tau>\<^sub>2)" using topol_cntxs_valid(2) by simp 
  moreover from assms(1) have "(f[\<FF>]..X\<^sub>2) {is a filter on} (\<Union>\<tau>\<^sub>2)" and "{f``B .B\<in>\<FF>} {is a base filter} (f[\<FF>]..X\<^sub>2)" 
    using base_image_filter fmapAssum X1_def X2_def by auto
  moreover have "\<forall>U\<in>Pow(\<Union>\<tau>\<^sub>2). (f`x)\<in>Interior(U,\<tau>\<^sub>2) \<longrightarrow> (\<exists>D\<in>{f``B .B\<in>\<FF>}. D\<subseteq>U)"
  proof - 
    { fix U
    assume "U\<in>Pow(X\<^sub>2)" "(f`x)\<in>Interior(U,\<tau>\<^sub>2)"
    with \<open>x\<in>X\<^sub>1\<close> have xim: "x\<in>f-``(Interior(U,\<tau>\<^sub>2))" and sub: "f-``(Interior(U,\<tau>\<^sub>2))\<in>Pow(X\<^sub>1)" 
      using func1_1_L6A fmapAssum func1_1_L15 fmapAssum by auto
    note sub 
    moreover
    have "Interior(U,\<tau>\<^sub>2)\<in>\<tau>\<^sub>2" using topology0.Top_2_L2 topol_cntxs_valid(2) by auto
    with assms(2) have "f-``(Interior(U,\<tau>\<^sub>2))\<in>\<tau>\<^sub>1" unfolding isContinuous_def IsContinuous_def
      by auto
    with xim have "x\<in>Interior(f-``(Interior(U,\<tau>\<^sub>2)),\<tau>\<^sub>1)" 
      using topology0.Top_2_L3 topol_cntxs_valid(1) by auto
    moreover from assms(1) assms(3) have "{U\<in>Pow(X\<^sub>1). x\<in>Interior(U,\<tau>\<^sub>1)}\<subseteq>\<FF>" 
        using topology0.FilterConverges_def topol_cntxs_valid(1) X1_def by auto
    ultimately have "f-``(Interior(U,\<tau>\<^sub>2))\<in>\<FF>" by auto
    moreover have "f``(f-``(Interior(U,\<tau>\<^sub>2)))\<subseteq>Interior(U,\<tau>\<^sub>2)" 
      using function_image_vimage fun_is_fun fmapAssum by auto
    then have "f``(f-``(Interior(U,\<tau>\<^sub>2)))\<subseteq>U" 
      using topology0.Top_2_L1 topol_cntxs_valid(2) by auto
    ultimately have "\<exists>D\<in>{f``(B) .B\<in>\<FF>}. D\<subseteq>U" by auto
    } thus ?thesis by auto 
  qed
  moreover from fmapAssum \<open>x\<in>X\<^sub>1\<close>  have "f`(x) \<in> X\<^sub>2"
    by (rule apply_funtype) 
  hence "f`(x) \<in> \<Union>\<tau>\<^sub>2" by simp 
  ultimately show ?thesis by (rule topology0.convergence_filter_base2) 
qed

text\<open>Continuity in filter at every point of the domain implies global continuity.\<close>

lemma (in two_top_spaces0) filter_conver_preserved_imp_cont:
  assumes "\<forall>x\<in>\<Union>\<tau>\<^sub>1. \<forall>\<FF>. ((\<FF> {is a filter on} X\<^sub>1) \<and> (\<FF> \<rightarrow>\<^sub>F x {in} \<tau>\<^sub>1)) \<longrightarrow> ((f[\<FF>]..X\<^sub>2) \<rightarrow>\<^sub>F (f`x) {in} \<tau>\<^sub>2)"
  shows "f{is continuous}"
proof-
  {
    fix x
    assume as2: "x\<in>\<Union>\<tau>\<^sub>1"
    with assms have reg: 
      "\<forall>\<FF>. ((\<FF> {is a filter on} X\<^sub>1) \<and> (\<FF> \<rightarrow>\<^sub>F x {in} \<tau>\<^sub>1)) \<longrightarrow> ((f[\<FF>]..X\<^sub>2) \<rightarrow>\<^sub>F (f`x) {in} \<tau>\<^sub>2)" 
      by auto
    let ?Neig = "{U \<in> Pow(\<Union>\<tau>\<^sub>1) . x \<in> Interior(U, \<tau>\<^sub>1)}"
    from as2 have NFil: "?Neig{is a filter on}X\<^sub>1" and NCon: "?Neig \<rightarrow>\<^sub>F x {in} \<tau>\<^sub>1"
      using topol_cntxs_valid(1) topology0.neigh_filter by auto
    {
      fix U
      assume "U\<in>\<tau>\<^sub>2" "f`x\<in>U"
      then have "U\<in>Pow(\<Union>\<tau>\<^sub>2)" "f`x\<in>Interior(U,\<tau>\<^sub>2)" using topol_cntxs_valid(2) topology0.Top_2_L3 by auto
      moreover
      from NCon NFil reg have "(f[?Neig]..X\<^sub>2) \<rightarrow>\<^sub>F (f`x) {in} \<tau>\<^sub>2" by auto 
      moreover have "(f[?Neig]..X\<^sub>2) {is a filter on} X\<^sub>2" 
        using base_image_filter(2) NFil fmapAssum by auto
      ultimately have "U\<in>(f[?Neig]..X\<^sub>2)" 
        using topology0.FilterConverges_def topol_cntxs_valid(2) unfolding X1_def X2_def 
        by auto
      moreover
      from fmapAssum NFil have "{f``B .B\<in>?Neig} {is a base filter} (f[?Neig]..X\<^sub>2)" 
        using base_image_filter(1) X1_def X2_def by auto
      ultimately have "\<exists>V\<in>{f``B .B\<in>?Neig}. V\<subseteq>U" using basic_element_filter by blast
      then obtain B where "B\<in>?Neig" "f``B\<subseteq>U" by auto
      moreover
      have "Interior(B,\<tau>\<^sub>1)\<subseteq>B" using topology0.Top_2_L1 topol_cntxs_valid(1) by auto
      hence "f``Interior(B,\<tau>\<^sub>1) \<subseteq> f``(B)" by auto
      moreover have "Interior(B,\<tau>\<^sub>1)\<in>\<tau>\<^sub>1" 
        using topology0.Top_2_L2 topol_cntxs_valid(1) by auto
      ultimately have "\<exists>V\<in>\<tau>\<^sub>1. x\<in>V \<and> f``V\<subseteq>U" by force
    }
    hence "\<forall>U\<in>\<tau>\<^sub>2. f`x\<in>U \<longrightarrow> (\<exists>V\<in>\<tau>\<^sub>1. x\<in>V \<and> f``V\<subseteq>U)" by auto
  }
  hence "\<forall>x\<in>\<Union>\<tau>\<^sub>1. \<forall>U\<in>\<tau>\<^sub>2. f`x\<in>U \<longrightarrow> (\<exists>V\<in>\<tau>\<^sub>1. x\<in>V \<and> f``V\<subseteq>U)" by auto
  then show ?thesis 
    using ccontinuous_all_x_imp_cont_global fmapAssum X1_def X2_def isContinuous_def tau1_is_top 
    by auto
qed

end

