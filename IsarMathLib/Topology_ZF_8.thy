(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2013 Daniel de la Concepcion

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

section \<open>Topology 8\<close>

theory Topology_ZF_8 imports Topology_ZF_6 EquivClass1
begin

text\<open>This theory deals with quotient topologies.\<close>

subsection\<open>Definition of quotient topology\<close>

text\<open>Given a surjective function $f:X\to Y$ and a topology $\tau$ in $X$, it is
posible to consider a special topology in $Y$. $f$ is called quotient function.\<close>

definition(in topology0)
  QuotientTop ("{quotient topology in}_{by}_" 80)
  where "f\<in>surj(\<Union>T,Y) \<Longrightarrow>{quotient topology in}Y{by}f\<equiv>
    {U\<in>Pow(Y). f-``U\<in>T}"

abbreviation QuotientTopTop ("{quotient topology in}_{by}_{from}_")
  where "QuotientTopTop(Y,f,T) \<equiv> topology0.QuotientTop(T,Y,f)"

text\<open>The quotient topology is indeed a topology.\<close>

theorem(in topology0) quotientTop_is_top:
  assumes "f\<in>surj(\<Union>T,Y)"
  shows "({quotient topology in} Y {by} f) {is a topology}"
proof-
  have "({quotient topology in} Y {by} f)={U \<in> Pow(Y) . f -`` U \<in> T}" using QuotientTop_def assms
    by auto moreover
  {
    fix M x B assume M:"M \<subseteq> {U \<in> Pow(Y) . f -`` U \<in> T}"
    then have "\<Union>M\<subseteq>Y" by blast moreover
    have A1:"f -`` (\<Union>M)=(\<Union>y\<in>(\<Union>M). f-``{y})" using vimage_eq_UN by blast
    {
      fix A assume "A\<in>M"
      with M have "A\<in>Pow(Y)" "f -`` A\<in>T" by auto
      have "f -`` A=(\<Union>y\<in>A. f-``{y})" using vimage_eq_UN by blast
    }
    then have "(\<Union>A\<in>M. f-`` A)=(\<Union>A\<in>M. (\<Union>y\<in>A. f-``{y}))" by auto
    then have "(\<Union>A\<in>M. f-`` A)=(\<Union>y\<in>\<Union>M. f-``{y})" by auto
    with A1 have A2:"f -`` (\<Union>M)=\<Union>{f-`` A. A\<in>M}" by auto
    {
      fix A assume "A\<in>M"
      with M have "f -`` A\<in>T" by auto
    }
    then have "\<forall>A\<in>M. f -`` A\<in>T" by auto
    then have "{f-`` A. A\<in>M}\<subseteq>T" by auto
    then have "(\<Union>{f-`` A. A\<in>M})\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
    with A2 have "(f -`` (\<Union>M))\<in>T" by auto
    ultimately have "\<Union>M\<in>{U\<in>Pow(Y). f-``U\<in>T}" by auto
  }
  moreover
  {
    fix U V assume "U\<in>{U\<in>Pow(Y). f-``U\<in>T}""V\<in>{U\<in>Pow(Y). f-``U\<in>T}"
    then have "U\<in>Pow(Y)""V\<in>Pow(Y)""f-``U\<in>T""f-``V\<in>T" by auto
    then have "(f-``U)\<inter>(f-``V)\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
    then have "f-`` (U\<inter>V)\<in>T" using invim_inter_inter_invim assms unfolding surj_def
      by auto
    with \<open>U\<in>Pow(Y)\<close>\<open>V\<in>Pow(Y)\<close> have "U\<inter>V\<in>{U\<in>Pow(Y). f-``U\<in>T}" by auto
  }
  ultimately show ?thesis using IsATopology_def by auto
qed

text\<open>The quotient function is continuous.\<close>

lemma (in topology0) quotient_func_cont:
  assumes "f\<in>surj(\<Union>T,Y)"
  shows "IsContinuous(T,({quotient topology in} Y {by} f),f)"
    unfolding IsContinuous_def using QuotientTop_def assms by auto

text\<open>One of the important properties of this topology, is that a function
from the quotient space is continuous iff the composition with the quotient
function is continuous.\<close>

theorem(in two_top_spaces0) cont_quotient_top:
  assumes "h\<in>surj(\<Union>\<tau>\<^sub>1,Y)" "g:Y\<rightarrow>\<Union>\<tau>\<^sub>2" "IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2,g O h)"
  shows "IsContinuous(({quotient topology in} Y {by} h {from} \<tau>\<^sub>1),\<tau>\<^sub>2,g)"
proof-
  {
    fix U assume "U\<in>\<tau>\<^sub>2"
    with assms(3) have "(g O h)-``(U)\<in>\<tau>\<^sub>1" unfolding IsContinuous_def by auto
    then have "h-``(g-``(U))\<in>\<tau>\<^sub>1" using vimage_comp by auto
    then have "g-``(U)\<in>({quotient topology in} Y {by} h {from} \<tau>\<^sub>1)" using topology0.QuotientTop_def
      tau1_is_top assms(1) using func1_1_L3 assms(2) unfolding topology0_def by auto
  }
  then show ?thesis unfolding IsContinuous_def by auto
qed

text\<open>The underlying set of the quotient topology is $Y$.\<close>

lemma(in topology0) total_quo_func:
  assumes "f\<in>surj(\<Union>T,Y)"
  shows "(\<Union>({quotient topology in}Y{by}f))=Y"
proof-
  from assms have "f-``Y=\<Union>T" using func1_1_L4 unfolding surj_def by auto moreover
  have "\<Union>T\<in>T" using topSpaceAssum unfolding IsATopology_def by auto ultimately
  have "Y\<in>({quotient topology in}Y{by}f{from}T)" using QuotientTop_def assms by auto
  then show ?thesis using QuotientTop_def assms by auto
qed

subsection\<open>Quotient topologies from equivalence relations\<close>
text\<open>In this section we will show that the quotient topologies come from
an equivalence relation.\<close>

text\<open>First, some lemmas for relations.\<close>

lemma quotient_proj_fun:
  shows "{\<langle>b,r``{b}\<rangle>. b\<in>A}:A\<rightarrow>A//r" unfolding Pi_def function_def domain_def
    unfolding quotient_def by auto

lemma quotient_proj_surj:
  shows "{\<langle>b,r``{b}\<rangle>. b\<in>A}\<in>surj(A,A//r)"
proof-
  {
    fix y assume "y\<in>A//r"
    then obtain yy where A:"yy\<in>A" "y=r``{yy}" unfolding quotient_def by auto
    then have "\<langle>yy,y\<rangle>\<in>{\<langle>b,r``{b}\<rangle>. b\<in>A}" by auto
    then have "{\<langle>b,r``{b}\<rangle>. b\<in>A}`yy=y" using apply_equality[OF _ quotient_proj_fun] by auto
    with A(1) have "\<exists>yy\<in>A. {\<langle>b,r``{b}\<rangle>. b\<in>A}`yy=y" by auto
  }
  with quotient_proj_fun show ?thesis unfolding surj_def by auto
qed 

lemma preim_equi_proj:
  assumes "U\<subseteq>A//r" "equiv(A,r)"
  shows "{\<langle>b,r``{b}\<rangle>. b\<in>A}-``U=\<Union>U"
proof
  {
    fix y assume "y\<in>\<Union>U"
    then obtain V where V:"y\<in>V""V\<in>U" by auto
    with \<open>U\<subseteq>(A//r)\<close> have "y\<in>A" using EquivClass_1_L1 assms(2) by auto moreover
    from \<open>U\<subseteq>(A//r)\<close> V have "r``{y}=V" using EquivClass_1_L2 assms(2) by auto
    moreover note V(2) ultimately have "y\<in>{x\<in>A. r``{x}\<in>U}" by auto
    then have "y\<in>{\<langle>b,r``{b}\<rangle>. b\<in>A}-``U" by auto
  }
  then show "\<Union>U\<subseteq>{\<langle>b,r``{b}\<rangle>. b\<in>A}-``U" by blast moreover
  {
    fix y assume "y\<in>{\<langle>b,r``{b}\<rangle>. b\<in>A}-``U"
    then have yy:"y\<in>{x\<in>A. r``{x}\<in>U}" by auto
    then have "r``{y}\<in>U" by auto moreover
    from yy have "y\<in>r``{y}" using assms equiv_class_self by auto ultimately
    have "y\<in>\<Union>U" by auto
  }
  then show "{\<langle>b,r``{b}\<rangle>. b\<in>A}-``U\<subseteq>\<Union>U" by blast
qed

text\<open>Now we define what a quotient topology from an equivalence relation is:\<close>

definition(in topology0)
  EquivQuo ("{quotient by}_" 70)
  where "equiv(\<Union>T,r)\<Longrightarrow>({quotient by}r)\<equiv>{quotient topology in}(\<Union>T)//r{by}{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}"

abbreviation
  EquivQuoTop ("_{quotient by}_" 60)
  where "EquivQuoTop(T,r)\<equiv>topology0.EquivQuo(T,r)"

text\<open>First, another description of the topology (more intuitive):\<close>

theorem (in topology0) quotient_equiv_rel:
  assumes "equiv(\<Union>T,r)"
  shows "({quotient by}r)={U\<in>Pow((\<Union>T)//r). \<Union>U\<in>T}"
proof-
  have "({quotient topology in}(\<Union>T)//r{by}{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T})={U\<in>Pow((\<Union>T)//r). {\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}-``U\<in>T}"
    using QuotientTop_def quotient_proj_surj by auto moreover
  have "{U\<in>Pow((\<Union>T)//r). {\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}-``U\<in>T}={U\<in>Pow((\<Union>T)//r). \<Union>U\<in>T}"
    proof
     {
       fix U assume "U\<in>{U\<in>Pow((\<Union>T)//r). {\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}-``U\<in>T}"
       then have "U\<in>{U\<in>Pow((\<Union>T)//r). \<Union>U\<in>T}" using preim_equi_proj assms by auto
     }
     then show "{U\<in>Pow((\<Union>T)//r). {\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}-``U\<in>T}\<subseteq>{U\<in>Pow((\<Union>T)//r). \<Union>U\<in>T}" by auto
     {
       fix U assume "U\<in>{U\<in>Pow((\<Union>T)//r). \<Union>U\<in>T}"
       then have "U\<in>{U\<in>Pow((\<Union>T)//r). {\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}-``U\<in>T}" using preim_equi_proj assms by auto
     }
     then show "{U\<in>Pow((\<Union>T)//r). \<Union>U\<in>T}\<subseteq>{U\<in>Pow((\<Union>T)//r). {\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}-``U\<in>T}" by auto
   qed
  ultimately show ?thesis using EquivQuo_def assms by auto
qed

text\<open>We apply previous results to this topology.\<close>

theorem(in topology0) total_quo_equi:
  assumes "equiv(\<Union>T,r)"
  shows "\<Union>({quotient by}r)=(\<Union>T)//r"
  using total_quo_func quotient_proj_surj EquivQuo_def assms by auto

theorem(in topology0) equiv_quo_is_top:
  assumes "equiv(\<Union>T,r)"
  shows "({quotient by}r){is a topology}"
  using quotientTop_is_top quotient_proj_surj EquivQuo_def assms by auto

text\<open>MAIN RESULT: All quotient topologies arise from an equivalence relation given by the quotient 
function $f:X\to Y$. This means that any quotient topology is homeomorphic to a topology
given by an equivalence relation quotient.\<close>

theorem(in topology0) equiv_quotient_top:
  assumes "f\<in>surj(\<Union>T,Y)"
  defines "r\<equiv>{\<langle>x,y\<rangle>\<in>\<Union>T\<times>\<Union>T. f`(x)=f`(y)}"
  defines "g\<equiv>{\<langle>y,f-``{y}\<rangle>. y\<in>Y}"
  shows "equiv(\<Union>T,r)" and "IsAhomeomorphism(({quotient topology in}Y{by}f),({quotient by}r),g)"
proof-
  have ff:"f:\<Union>T\<rightarrow>Y" using assms(1) unfolding surj_def by auto
  show B:"equiv(\<Union>T,r)" unfolding equiv_def refl_def sym_def trans_def unfolding r_def by auto
  have gg:"g:Y\<rightarrow>((\<Union>T)//r)"
    proof-
      {
        fix B assume "B\<in>g"
        then obtain y where Y:"y\<in>Y" "B=\<langle>y,f-``{y}\<rangle>" unfolding g_def by auto
        then have "f-``{y}\<subseteq>\<Union>T" using func1_1_L3 ff by blast
        then have eq:"f-``{y}={x\<in>\<Union>T. \<langle>x,y\<rangle>\<in>f}" using vimage_iff by auto
        from Y obtain A where A1:"A\<in>\<Union>T""f`A=y" using assms(1) unfolding surj_def by blast
        with eq have A:"A\<in>f-``{y}" using apply_Pair[OF ff] by auto
        {
          fix t assume "t\<in>f-``{y}"
          with A have "t\<in>\<Union>T""A\<in>\<Union>T""\<langle>t,y\<rangle>\<in>f""\<langle>A,y\<rangle>\<in>f" using eq by auto
          then have "f`t=f`A" using apply_equality assms(1) unfolding surj_def by auto
          with \<open>t\<in>\<Union>T\<close>\<open>A\<in>\<Union>T\<close> have "\<langle>A,t\<rangle>\<in>r" using r_def by auto
          then have "t\<in>r``{A}" using image_iff by auto
        }
        then have "f-``{y}\<subseteq>r``{A}" by auto moreover
        {
          fix t assume "t\<in>r``{A}"
          then have "\<langle>A,t\<rangle>\<in>r" using image_iff by auto
          then have un:"t\<in>\<Union>T""A\<in>\<Union>T" and eq2:"f`t=f`A" unfolding r_def by auto moreover
          from un have "\<langle>t,f`t\<rangle>\<in>f" using apply_Pair[OF ff] by auto
          with eq2 A1 have "\<langle>t,y\<rangle>\<in>f" by auto
          with un have "t\<in>f-``{y}" using eq by auto
        }
        then have "r``{A}\<subseteq>f-``{y}" by auto ultimately
        have "f-``{y}=r``{A}" by auto
        then have "f-``{y}\<in> (\<Union>T)//r" using A1(1) unfolding quotient_def by auto
        with Y have "B\<in>Y\<times>(\<Union>T)//r" by auto
      }
      then have "\<forall>A\<in>g. A\<in> Y\<times>(\<Union>T)//r" by auto
      then have "g\<subseteq>(Y\<times>(\<Union>T)//r)" by auto moreover
      then show ?thesis unfolding Pi_def function_def domain_def g_def by auto
    qed
  then have gg2:"g:Y\<rightarrow>(\<Union>({quotient by}r))" using total_quo_equi B by auto
  {
    fix s assume S:"s\<in>({quotient topology in}Y{by}f)"
    then have "s\<in>Pow(Y)"and P:"f-``s\<in>T" using QuotientTop_def topSpaceAssum assms(1)
      by auto
    have "f-``s=(\<Union>y\<in>s. f-``{y})" using vimage_eq_UN by blast moreover
    from \<open>s\<in>Pow(Y)\<close> have "\<forall>y\<in>s. \<langle>y,f-``{y}\<rangle>\<in>g" unfolding g_def by auto
    then have "\<forall>y\<in>s. g`y=f-``{y}" using apply_equality gg by auto ultimately
    have "f-``s=(\<Union>y\<in>s. g`y)" by auto
    with P have "(\<Union>y\<in>s. g`y)\<in>T" by auto moreover
    from \<open>s\<in>Pow(Y)\<close> have "\<forall>y\<in>s. g`y\<in>(\<Union>T)//r" using apply_type gg by auto
    ultimately have "{g`y. y\<in>s}\<in>({quotient by}r)" using quotient_equiv_rel B by auto
    with \<open>s\<in>Pow(Y)\<close> have "g``s\<in>({quotient by}r)" using func_imagedef gg by auto
  }
  then have gopen:"\<forall>s\<in>({quotient topology in}Y{by}f). g``s\<in>(T{quotient by}r)" by auto
  have pr_fun:"{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}:\<Union>T\<rightarrow>(\<Union>T)//r" using quotient_proj_fun by auto
  {
    fix b assume b:"b\<in>\<Union>T"
    have bY:"f`b\<in>Y" using apply_funtype ff b by auto
    with b have com:"(g O f)`b=g`(f`b)" using comp_fun_apply ff by auto
    from bY have pg:"\<langle>f`b,f-``({f`b})\<rangle>\<in>g" unfolding g_def by auto
    then have "g`(f`b)=f-``({f`b})" using apply_equality gg by auto
    with com have comeq:"(g O f)`b=f-``({f`b})" by auto
    from b have A:"f``{b}={f`b}" "{b}\<subseteq>\<Union>T" using func_imagedef ff by auto
    from A(2) have "b\<in>f -`` (f `` {b})" using func1_1_L9 ff by blast
    then have "b\<in>f-``({f`b})" using A(1) by auto moreover
    from pg have "f-``({f`b})\<in>(\<Union>T)//r" using gg unfolding Pi_def by auto
    ultimately have "r``{b}=f-``({f`b})" using EquivClass_1_L2 B by auto
    then have "(g O f)`b=r``{b}" using comeq by auto moreover
    from b have "\<langle>b,r``{b}\<rangle>\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}" by auto
    with pr_fun have "{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}`b=r``{b}" using apply_equality by auto ultimately
    have "(g O f)`b={\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}`b" by auto
  } 
  then have reg:"\<forall>b\<in>\<Union>T. (g O f)`b={\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}`b" by auto moreover
  have compp:"g O f\<in>\<Union>T\<rightarrow>(\<Union>T)//r" using comp_fun ff gg by auto
  have feq:"(g O f)={\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}" using fun_extension[OF compp pr_fun] reg by auto
  then have "IsContinuous(T,{quotient by}r,(g O f))" using quotient_func_cont quotient_proj_surj
    EquivQuo_def topSpaceAssum B by auto moreover
  have "(g O f):\<Union>T\<rightarrow>\<Union>({quotient by}r)" using comp_fun ff gg2 by auto
  ultimately have gcont:"IsContinuous({quotient topology in}Y{by}f,{quotient by}r,g)"
    using two_top_spaces0.cont_quotient_top assms(1) gg2 unfolding two_top_spaces0_def
    using topSpaceAssum equiv_quo_is_top B by auto
  {
    fix x y assume T:"x\<in>Y""y\<in>Y""g`x=g`y"
      then have "f-``{x}=f-``{y}" using apply_equality gg unfolding g_def by auto
      then have "f``(f-``{x})=f``(f-``{y})" by auto
      with T(1,2) have "{x}={y}" using surj_image_vimage assms(1) by auto
      then have "x=y" by auto
  }
  with gg2 have "g\<in>inj(Y,\<Union>({quotient by}r))" unfolding inj_def by auto moreover
  have "g O f\<in>surj(\<Union>T, (\<Union>T)//r)" using feq quotient_proj_surj by auto
  then have "g\<in>surj(Y,(\<Union>T)//r)" using comp_mem_surjD1 ff gg by auto
  then have "g\<in>surj(Y,\<Union>(T{quotient by}r))" using total_quo_equi B by auto
  ultimately have "g\<in>bij(\<Union>({quotient topology in}Y{by}f),\<Union>({quotient by}r))" unfolding bij_def using total_quo_func assms(1) by auto
  with gcont gopen show "IsAhomeomorphism(({quotient topology in}Y{by}f),({quotient by}r),g)"
    using bij_cont_open_homeo by auto
qed

lemma product_equiv_rel_fun:
  shows "{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}:(\<Union>T\<times>\<Union>T)\<rightarrow>((\<Union>T)//r\<times>(\<Union>T)//r)"
proof-
  have " {\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}\<in>\<Union>T\<rightarrow>(\<Union>T)//r" using quotient_proj_fun by auto moreover
  have "\<forall>A\<in>\<Union>T. \<langle>A,r``{A}\<rangle>\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}" by auto
  ultimately have "\<forall>A\<in>\<Union>T. {\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}`A=r``{A}" using apply_equality by auto
  then have IN:" {\<langle>\<langle>b, c\<rangle>, r `` {b}, r `` {c}\<rangle> . \<langle>b,c\<rangle> \<in> \<Union>T \<times> \<Union>T}= {\<langle>\<langle>x, y\<rangle>, {\<langle>b, r `` {b}\<rangle> . b \<in> \<Union>T} ` x, {\<langle>b, r `` {b}\<rangle> . b \<in> \<Union>T} ` y\<rangle> . \<langle>x,y\<rangle> \<in> \<Union>T \<times> \<Union>T}"
    by force
  then show ?thesis using prod_fun quotient_proj_fun by auto
qed

lemma(in topology0) prod_equiv_rel_surj:
  shows "{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}:surj(\<Union>(ProductTopology(T,T)),((\<Union>T)//r\<times>(\<Union>T)//r))"
proof-
  have fun:"{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}:(\<Union>T\<times>\<Union>T)\<rightarrow>((\<Union>T)//r\<times>(\<Union>T)//r)" using
    product_equiv_rel_fun by auto moreover
  {
    fix M assume "M\<in>((\<Union>T)//r\<times>(\<Union>T)//r)"
    then obtain M1 M2 where M:"M=\<langle>M1,M2\<rangle>" "M1\<in>(\<Union>T)//r""M2\<in>(\<Union>T)//r" by auto
    then obtain m1 m2 where m:"m1\<in>\<Union>T""m2\<in>\<Union>T""M1=r``{m1}""M2=r``{m2}" unfolding quotient_def
      by auto
    then have mm:"\<langle>m1,m2\<rangle>\<in>(\<Union>T\<times>\<Union>T)" by auto
    then have "\<langle>\<langle>m1,m2\<rangle>,\<langle>r``{m1},r``{m2}\<rangle>\<rangle>\<in>{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}" by auto
    then have "{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}`\<langle>m1,m2\<rangle>=\<langle>r``{m1},r``{m2}\<rangle>"
      using apply_equality fun by auto
    then have "{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}`\<langle>m1,m2\<rangle>=M" using M(1) m(3,4) by auto
    then have "\<exists>R\<in>(\<Union>T\<times>\<Union>T). {\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}`R=M" using mm by auto
  }
  ultimately show ?thesis unfolding surj_def using Top_1_4_T1(3) topSpaceAssum by auto
qed

lemma(in topology0) product_quo_fun:
  assumes "equiv(\<Union>T,r)"
  shows "IsContinuous(ProductTopology(T,T),ProductTopology({quotient by}r,({quotient by}r)),{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T})"
proof-
  have "{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}:\<Union>T\<rightarrow>(\<Union>T)//r" using quotient_proj_fun by auto moreover
  have "\<forall>A\<in>\<Union>T. \<langle>A,r``{A}\<rangle>\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}" by auto ultimately
  have "\<forall>A\<in>\<Union>T. {\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}`A=r``{A}" using apply_equality by auto
  then have IN:" {\<langle>\<langle>b, c\<rangle>, r `` {b}, r `` {c}\<rangle> . \<langle>b,c\<rangle> \<in> \<Union>T \<times> \<Union>T}= {\<langle>\<langle>x, y\<rangle>, {\<langle>b, r `` {b}\<rangle> . b \<in> \<Union>T} ` x, {\<langle>b, r `` {b}\<rangle> . b \<in> \<Union>T} ` y\<rangle> . \<langle>x,y\<rangle> \<in> \<Union>T \<times> \<Union>T}"
    by force
  have cont:"IsContinuous(T,{quotient by}r,{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T})" using quotient_func_cont quotient_proj_surj
    EquivQuo_def assms by auto
  have tot:"\<Union>(T{quotient by}r) = (\<Union>T) // r" and top:"({quotient by}r) {is a topology}" using total_quo_equi equiv_quo_is_top assms by auto 
  then have fun:"{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}:\<Union>T\<rightarrow>\<Union>({quotient by}r)" using quotient_proj_fun by auto
  then have two:"two_top_spaces0(T,{quotient by}r,{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T})" unfolding two_top_spaces0_def using topSpaceAssum top by auto
  show ?thesis using two_top_spaces0.product_cont_functions two fun fun cont cont top topSpaceAssum IN by auto
qed

text\<open>The product of quotient topologies is a quotient topology given that the
quotient map is open. This isn't true in general.\<close>

theorem(in topology0) prod_quotient:
  assumes "equiv(\<Union>T,r)" "\<forall>A\<in>T. {\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``A\<in>({quotient by}r)"
  shows "(ProductTopology({quotient by}r,{quotient by}r)) = ({quotient topology in}(((\<Union>T)//r)\<times>((\<Union>T)//r)){by}({\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}){from}(ProductTopology(T,T)))"
proof
  {
    fix A assume A:"A\<in>ProductTopology({quotient by}r,{quotient by}r)"
    from assms have "IsContinuous(ProductTopology(T,T),ProductTopology({quotient by}r,({quotient by}r)),{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T})" using product_quo_fun
      by auto
    with A have "{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}-``A\<in>ProductTopology(T,T)"
      unfolding IsContinuous_def by auto moreover
    from A have "A\<subseteq>\<Union>ProductTopology(T{quotient by}r,T{quotient by}r)" by auto
    then have "A\<subseteq>\<Union>(T{quotient by}r)\<times>\<Union>(T{quotient by}r)" using Top_1_4_T1(3) equiv_quo_is_top equiv_quo_is_top
      using assms by auto
    then have "A\<in>Pow(((\<Union>T)//r)\<times>((\<Union>T)//r))" using total_quo_equi assms by auto
    ultimately have "A\<in>({quotient topology in}(((\<Union>T)//r)\<times>((\<Union>T)//r)){by}{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}{from}(ProductTopology(T,T)))"
      using topology0.QuotientTop_def Top_1_4_T1(1) topSpaceAssum prod_equiv_rel_surj assms(1) unfolding topology0_def by auto
  }
  then show "ProductTopology(T{quotient by}r,T{quotient by}r)\<subseteq>({quotient topology in}(((\<Union>T)//r)\<times>((\<Union>T)//r)){by}{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}{from}(ProductTopology(T,T)))"
    by auto
  {
    fix A assume "A\<in>({quotient topology in}(((\<Union>T)//r)\<times>((\<Union>T)//r)){by}{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}{from}(ProductTopology(T,T)))"
    then have A:"A\<subseteq>((\<Union>T)//r)\<times>((\<Union>T)//r)" "{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}-``A\<in>ProductTopology(T,T)"
      using topology0.QuotientTop_def Top_1_4_T1(1) topSpaceAssum prod_equiv_rel_surj assms(1) unfolding topology0_def by auto
    {
      fix CC assume "CC\<in>A"
      with A(1) obtain C1 C2 where CC:"CC=\<langle>C1,C2\<rangle>" "C1\<in>((\<Union>T)//r)""C2\<in>((\<Union>T)//r)" by auto
      then obtain c1 c2 where CC1:"c1\<in>\<Union>T""c2\<in>\<Union>T" and CC2:"C1=r``{c1}""C2=r``{c2}" unfolding quotient_def
        by auto
      then have "\<langle>c1,c2\<rangle>\<in>\<Union>T\<times>\<Union>T" by auto
      then have "\<langle>\<langle>c1,c2\<rangle>,\<langle>r``{c1},r``{c2}\<rangle>\<rangle>\<in>{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}" by auto
      with CC2 CC have "\<langle>\<langle>c1,c2\<rangle>,CC\<rangle>\<in>{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}" by auto
      with \<open>CC\<in>A\<close> have "\<langle>c1,c2\<rangle>\<in>{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}-``A"
        using vimage_iff by auto
      with A(2) have " \<exists>V W. V \<in> T \<and> W \<in> T \<and> V \<times> W \<subseteq> {\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}-``A \<and> \<langle>c1,c2\<rangle> \<in> V \<times> W"
         using prod_top_point_neighb topSpaceAssum by blast
      then obtain V W where VW:"V\<in>T""W\<in>T""V \<times> W \<subseteq> {\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}-``A""c1\<in>V""c2\<in>W" by auto
      with assms(2) have "{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``V\<in>(T{quotient by}r)""{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``W\<in>(T{quotient by}r)" by auto
      then have P:"{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``V\<times>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``W\<in>ProductTopology(T{quotient by}r,T{quotient by}r)" using prod_open_open_prod equiv_quo_is_top
        assms(1) by auto
      {
        fix S assume "S\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``V\<times>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``W"
        then obtain s1 s2 where S:"S=\<langle>s1,s2\<rangle>""s1\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``V""s2\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``W" by blast
        then obtain t1 t2 where T:"\<langle>t1,s1\<rangle>\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}""\<langle>t2,s2\<rangle>\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}""t1\<in>V""t2\<in>W" using image_iff by auto
        then have "\<langle>t1,t2\<rangle>\<in>V\<times>W" by auto
        with VW(3) have "\<langle>t1,t2\<rangle>\<in>{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}-``A" by auto
        then have "\<exists>SS\<in>A. \<langle>\<langle>t1,t2\<rangle>,SS\<rangle>\<in>{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}" using vimage_iff by auto
        then obtain SS where "SS\<in>A""\<langle>\<langle>t1,t2\<rangle>,SS\<rangle>\<in>{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}" by auto moreover       
        from T VW(1,2) have "\<langle>t1,t2\<rangle>\<in>\<Union>T\<times>\<Union>T""\<langle>s1,s2\<rangle>=\<langle>r``{t1},r``{t2}\<rangle>" by auto
        with S(1) have "\<langle>\<langle>t1,t2\<rangle>,S\<rangle>\<in>{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}" by auto
        ultimately have "S\<in>A" using product_equiv_rel_fun unfolding Pi_def function_def
          by auto
      }
      then have sub:"{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``V\<times>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``W\<subseteq>A" by blast
      have "\<langle>c1,C1\<rangle>\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}""\<langle>c2,C2\<rangle>\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}" using CC2 CC1
        by auto
      with \<open>c1\<in>V\<close>\<open>c2\<in>W\<close> have "C1\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``V""C2\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``W"
        using image_iff by auto
      then have "CC\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``V\<times>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``W" using CC by auto
      with sub P have "\<exists>OO\<in>ProductTopology(T{quotient by}r,T{quotient by}r). CC\<in>OO\<and> OO\<subseteq>A"
        using exI[where x="{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``V\<times>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``W" and P="\<lambda>OO. OO\<in>ProductTopology(T{quotient by}r,T{quotient by}r)\<and> CC\<in>OO\<and> OO\<subseteq>A"]
        by auto
    }
    then have "\<forall>C\<in>A. \<exists>OO\<in>ProductTopology(T{quotient by}r,T{quotient by}r). C\<in>OO\<and> OO\<subseteq>A" by auto
    then have "A\<in>ProductTopology(T{quotient by}r,T{quotient by}r)" using topology0.open_neigh_open
      unfolding topology0_def using Top_1_4_T1 equiv_quo_is_top assms by auto
  }
  then show "({quotient topology in}(((\<Union>T)//r)\<times>((\<Union>T)//r)){by}{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}{from}(ProductTopology(T,T)))\<subseteq>ProductTopology(T{quotient by}r,T{quotient by}r)"
    by auto
qed

end
