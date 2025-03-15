(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2023 Slawomir Kolodynski

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

section \<open> Real valued metric spaces \<close>

theory MetricSpace_ZF_1 imports Real_ZF_2
begin

text\<open>The development of metric spaces in IsarMathLib is different from the usual treatment
  of the subject because the notion of a metric (or a pseudometric) is defined in the 
  \<open>MetricSpace_ZF\<close> theory a more generally as a function valued in an ordered loop. 
  This theory file brings the subject closer to the standard way by specializing that general
  definition to the usual special case where the value of the metric are nonnegative real numbers. \<close>

subsection\<open>Real valued metric scapes: context and notation\<close>

text\<open> The \<open>reals\<close> context (locale) defined in the \<open>Real_ZF_2\<close> theory fixes a model of reals 
  (i.e. a complete ordered field) and defines notation for things like zero, one, the set of 
  positive numbers, absolute value etc. For metric spaces we reuse the notation defined there.\<close>

text\<open>The \<open>rpmetric_space\<close> locale extends the \<open>reals\<close> locale, adding the carrier $X$ 
  of the metric space and the metric $\mathcal{d}$ to the context, together with the assumption
  that $\mathcal{d}:X\times X \rightarrow \mathbb{R}^+$ is a pseudo metric.
  We choose to denote the disk in $X$ with center $c$ and radius $r$ as \<open>ball(c,r)\<close> 
  As in the \<open>pmetric_space\<close> locale we define the $\tau$ to be the metric topology, i.e.
  the topology induced by the (real valued) pseudometric $\mathcal{d}$.
  An alternative would be to define the \<open>rpmetric_space\<close> as an extension of the \<open>rpmetric_space\<close>
  context, but that is in turn an extension of the \<open>loop1\<close> locale that defines notation
  for left and right division which which do not want in the context of real numbers. \<close>

locale rpmetric_space = reals +
  fixes X and \<d>
  assumes pmetricAssum: "IsApseudoMetric(\<d>,X,\<real>,Add,ROrd)"
  fixes ball
  defines ball_def [simp]: "ball(c,r) \<equiv> Disk(X,\<d>,ROrd,c,r)"
  fixes pmettop ("\<tau>") 
  defines pmettop [simp]: "\<tau> \<equiv> MetricTopology(X,\<real>,Add,ROrd,\<d>)"
  fixes interior ("int")
  defines interior_def [simp]: "int(D) \<equiv> Interior(D,\<tau>)"
  fixes cl
  defines cl_def [simp]: "cl(D) \<equiv> Closure(D,\<tau>)"

text\<open>The propositions proven in the \<open>pmetric_space\<close> context defined in \<open>Metric_Space_ZF\<close> theory 
  are valid in the \<open>rpmetric_space\<close> context. \<close>

lemma (in rpmetric_space) pmetric_space_rpmetric_space_valid: 
  shows "pmetric_space(\<real>,Add,ROrd,\<d>,X)"
  unfolding pmetric_space_def pmetric_space_axioms_def loop1_def
  using pmetricAssum reals_loop by simp

text\<open>The context \<open>rpmetric_space\<close> is a special case of context \<open>pmetric_space\<close> 
  where the fixed objects in \<open>pmetric_space\<close> map to (in the order defined in \<open>pmetric_space\<close>) 
  the set of real numbers, real addition, the order relation on reals, 
  the strict order relation on reals, the set of non-negative reals and 
  the set of positive reals. The metrics $d$ maps to the real metrics 
  \<open>\<d>\<close>, the carrier of the metric space $X$ is still $X$, and the \<open>disk\<close>s from \<open>pmetric_space\<close>
  are now called \<open>ball\<close>s in \<open>rpmetric_space\<close>. The notation for right and left division from 
  \<open>rpmetric_space\<close> is not used in \<open>pmetric_space\<close>. \<close>

sublocale rpmetric_space < pmetric_space 
  "\<real>" Add ROrd "\<zero>" realadd lesseq sless nonnegative positiveset
  "\<lambda>x y. LeftDiv(\<real>,Add)`\<langle>x,y\<rangle>"
  "\<lambda>x y. RightDiv(\<real>,Add)`\<langle>y,x\<rangle>"
  "\<d>" X ball
  using pmetric_space_rpmetric_space_valid by simp_all

text\<open>The \<open>rmetric_space\<close> locale (context) specializes the the \<open>rpmetric_space\<close> context
  by adding the assumption of identity of indiscernibles. \<close>

locale rmetric_space = rpmetric_space +
  assumes ident_indisc: "\<forall>x\<in>X. \<forall>y\<in>Y. \<d>`\<langle>x,y\<rangle> = \<zero> \<longrightarrow> x=y"

text\<open>The propositions proven in the \<open>metric_space\<close> context defined in \<open>Metric_Space_ZF\<close> theory 
  are valid in the \<open>rmetric_space\<close> context. \<close>

lemma (in rmetric_space) metric_space_rmetric_space_valid: 
  shows "metric_space(\<real>,Add,ROrd,\<d>,X)"
  unfolding metric_space_def metric_space_axioms_def
  using pmetric_space_rpmetric_space_valid ident_indisc
  by simp

text\<open>The \<open>rmetric_space\<close> context is a special case of the \<open>metric_space\<close> context,
  with fixed objects mapping the same as in the mapping between \<open>rpmetric_space\<close>
  and \<open>pmetric_space\<close> above. \<close>

sublocale rmetric_space < metric_space 
   "\<real>" Add ROrd "\<zero>" realadd lesseq sless nonnegative positiveset
  "\<lambda>x y. LeftDiv(\<real>,Add)`\<langle>x,y\<rangle>"
  "\<lambda>x y. RightDiv(\<real>,Add)`\<langle>y,x\<rangle>"
  "\<d>" X ball
proof
  from ident_indisc show "\<forall>x\<in>X. \<forall>y\<in>X. \<d> ` \<langle>x, y\<rangle> = TheNeutralElement(\<real>, Add) \<longrightarrow> x = y"
    by simp
qed

subsection\<open>Real valued metric spaces are Hausdorff as topological spaces\<close>

text\<open>The usual (real-valued) metric spaces are a special case of ordered loop valued
  metric spaces defined in the \<open>MetricSpace_ZF\<close> theory, hence they are $T_2$ 
  as topological spaces. Below we repeat the major theorems of \<open>MetricSpace_ZF\<close> theory
  specialized the standard setting of real valued metrics. \<close>

text\<open>Since in the \<open>rpmetric_space\<close> context $\mathfrak{d}$ is a pseudometrics
  the (real valued) metric topology indeed a topology. \<close>

theorem (in rpmetric_space) rpmetric_is_top:
  shows  "\<tau> {is a topology}"
  using rord_down_directs pmetric_is_top by simp

text\<open>The collection of open disks (caled \<open>ball\<close>s in the \<open>rpmetric_space\<close> context
  is a base for the (real valued) metric topology.\<close>

theorem (in rpmetric_space) rdisks_are_base:
  shows "(\<Union>c\<in>X. {ball(c,R). R\<in>\<real>\<^sub>+}) {is a base for} \<tau>"
  using rord_down_directs disks_are_base by simp

text\<open>$X$ is the carrier of the (real valued) metric topology.\<close>

theorem (in rpmetric_space) rmetric_top_carrier: shows  "\<Union>\<tau> = X"
  using rord_down_directs metric_top_carrier by simp

text\<open>The topology generated by a (real valued) metric is Hausdorff (i.e. $T_2$). \<close>

theorem (in rmetric_space) rmetric_space_T2: shows "\<tau> {is T\<^sub>2}"
  using rord_down_directs metric_space_T2 by simp

subsection\<open>Real valued (pseudo)metric spaces as uniform spaces\<close>

text\<open>The ordered loop valued pseudometric spaces are uniform spaces. In this 
  section we specialize major propositions from that context to the real valued pseudometric. \<close>

text\<open>In the \<open>MetricSpace_ZF\<close> theory we define a property \<open>IsHalfable\<close> of an ordered loop
  that states that for every positive element $b_1$ of the loop there is another (positive) 
  one $b_2$ such that $b_2+b_2 \leq b_1$. This property is needed for the ordered loop valued 
  pseudometric space to be a uniform space. In the next lemma we show that real numbers satisfy 
  this property. \<close>

lemma (in reals) pos_reals_halfable: shows "IsHalfable(\<real>,Add,ROrd)"
proof -
  { fix x assume "x\<in>\<real>\<^sub>+"
    let ?y = "(\<two>\<inverse>)\<cdot>x"
    from \<open>x\<in>\<real>\<^sub>+\<close> have "x\<in>\<real>" and "?y\<in>\<real>\<^sub>+"
      using element_pos pos_mul_closed ord_ring_less_members one_half_pos(2)
      by simp_all
    from \<open>x\<in>\<real>\<close> have "(\<two>\<inverse>\<ra>\<two>\<inverse>)\<cdot>x = x" using half_half_one(2) Ring_ZF_1_L3(6) by simp
    with \<open>x\<in>\<real>\<close> have "?y\<ra>?y \<lsq> x"
      using ord_ring_less_members ring_oper_distr(2) one_half_pos(2) ring_ord_refl
      by auto
    with \<open>?y\<in>\<real>\<^sub>+\<close> have "\<exists>y\<in>\<real>\<^sub>+. y \<ra> y \<lsq> x" by auto
  } then show ?thesis unfolding IsHalfable_def by simp
qed

text\<open>In the \<open>rpmetric_space\<close> we will write \<open>UniformGauge(X,\<real>,Add,ROrd,\<d>)\<close> i.e.
  $\{\mathcal{d}^{-1}([0,b]: b \in \mathbb{R}_+ \}$ as $\mathfrak{U}$. \<close>

abbreviation (in rpmetric_space) rgauge ("\<UU>") where "\<UU> \<equiv> UniformGauge(X,\<real>,Add,ROrd,\<d>)"

text\<open>$\mathfrak{U}$ is a fundamental system of entourages, hence its supersets 
  form a uniformity on $X$ and hence those supersets define a topology on $X$.
  This is a special case of the theorem \<open>metric_gauge_base\<close> from the \<open>Metric_Space_ZF\<close> 
  theory but instead an ordered loop we have real numbers, so all the premises are automatically
  satisfied, except for the one of $X$ being nonempty.\<close>

theorem (in rpmetric_space) metric_gauge_base: assumes "X\<noteq>\<emptyset>"
  shows
    "\<UU> {is a uniform base on} X"
    "Supersets(X\<times>X,\<UU>) {is a uniformity on} X"
    "UniformTopology(Supersets(X\<times>X,\<UU>),X) {is a topology}"
    "\<Union>UniformTopology(Supersets(X\<times>X,\<UU>),X) = X"
  using assms rord_down_directs pos_non_empty pos_reals_halfable metric_gauge_base
  by simp_all

text\<open>The topology generated by open disks is the same as the one 
  coming from the the unifomity consisting of supersets of sets in $\mathfrak{U}$. \<close>

theorem (in rpmetric_space) rmetric_top_is_uniform_top: assumes "X\<noteq>\<emptyset>"
  shows "\<tau> = UniformTopology(Supersets(X\<times>X,\<UU>),X)"
  using assms rord_down_directs pos_non_empty pos_reals_halfable metric_top_is_uniform_top
  by simp

end
