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

subsection\<open>Context and notation\<close>

text\<open> The \<open>reals\<close> context (locale) defined in the \<open>Real_ZF_2\<close> theory fixes a model of reals 
  (i.e. a complete ordered field) and defines notation for things like zero, one, the set of 
  positive numbers, absolute value etc. For metric spaces we reuse the notation defined there.\<close>

text\<open>The \<open>pmetric_space1\<close> locale extends the \<open>reals\<close> locale, adding the carrier $X$ 
  of the metric space and the metric $\mathcal{d}$ to the context, together with the assumption
  that $\mathcal{d}:X\times X \rightarrow \mathbb{R}^+$ is a pseudo metric.
  We choose to denote the disk in $X$ with center $c$ and radius $r$ as \<open>ball(c,r)\<close> 
  As in the \<open>pmetric_space\<close> locale we define the $\tau$ to be the metric topology, i.e.
  the topology induced by the (real valued) pseudometric $\mathcal{d}$.
  An alternative would be to define the \<open>pmetric_space1\<close> as an extension of the \<open>pmetric_space1\<close>
  context, but that is in turn an extension of the \<open>loop1\<close> locale that defines notation
  for left and right division which which do not want in the context of real numbers. \<close>

locale pmetric_space1 = reals +
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
  are valid in the \<open>pmetric_space1\<close> context. \<close>

lemma (in pmetric_space1) pmetric_space_pmetric_space1_valid: 
  shows "pmetric_space(\<real>,Add,ROrd,\<d>,X)"
  unfolding pmetric_space_def pmetric_space_axioms_def loop1_def
  using pmetricAssum reals_loop by simp

text\<open>The context \<open>pmetric_space1\<close> is a special case of context \<open>pmetric_space\<close> 
  where the fixed objects in \<open>pmetric_space\<close> map to (in the order defined in \<open>pmetric_space\<close>) 
  the set of real numbers, real addition, the order relation on reals, 
  the strict order relation on reals, the set of non-negative reals and 
  the set of positive reals. The metrics $d$ maps to the real metrics 
  \<open>\<d>\<close>, the carrier of the metric space $X$ is still $X$, and the \<open>disk\<close>s from \<open>pmetric_space\<close>
  are now called \<open>ball\<close>s in \<open>pmetric_space1\<close>. The notation for right and left division from 
  \<open>pmetric_space1\<close> is not used in \<open>pmetric_space\<close>. \<close>

sublocale pmetric_space1 < pmetric_space 
  "\<real>" Add ROrd "\<zero>" realadd lesseq sless nonnegative positiveset
  "\<lambda>x y. LeftDiv(\<real>,Add)`\<langle>x,y\<rangle>"
  "\<lambda>x y. RightDiv(\<real>,Add)`\<langle>y,x\<rangle>"
  "\<d>" X ball
  using pmetric_space_pmetric_space1_valid by simp_all

text\<open>The \<open>metric_space1\<close> locale (context) specializes the the \<open>pmetric_space1\<close> context
  by adding the assumption of identity of indiscernibles. \<close>

locale metric_space1 = pmetric_space1 +
  assumes ident_indisc: "\<forall>x\<in>X. \<forall>y\<in>Y. \<d>`\<langle>x,y\<rangle> = \<zero> \<longrightarrow> x=y"

text\<open>The propositions proven in the \<open>metric_space\<close> context defined in \<open>Metric_Space_ZF\<close> theory 
  are valid in the \<open>metric_space1\<close> context. \<close>

lemma (in metric_space1) metric_space_metric_space1_valid: 
  shows "metric_space(\<real>,Add,ROrd,\<d>,X)"
  unfolding metric_space_def metric_space_axioms_def
  using pmetric_space_pmetric_space1_valid ident_indisc
  by simp

text\<open>The \<open>metric_space1\<close> context is a special case of the \<open>metric_space\<close> context,
  with fixed objects mapping the same as in the mapping between \<open>pmetric_space1\<close>
  and \<open>pmetric_space\<close> above. \<close>

sublocale metric_space1 < metric_space 
   "\<real>" Add ROrd "\<zero>" realadd lesseq sless nonnegative positiveset
  "\<lambda>x y. LeftDiv(\<real>,Add)`\<langle>x,y\<rangle>"
  "\<lambda>x y. RightDiv(\<real>,Add)`\<langle>y,x\<rangle>"
  "\<d>" X ball
proof
  from ident_indisc show "\<forall>x\<in>X. \<forall>y\<in>X. \<d> ` \<langle>x, y\<rangle> = TheNeutralElement(\<real>, Add) \<longrightarrow> x = y"
    by simp
qed

subsection\<open>Metric spaces are Hausdorff as topological spaces\<close>

text\<open>The usual (real-valued) metric spaces are a special case of ordered loop valued
  metric spaces defined in the \<open>MetricSpace_ZF\<close> theory, hence they are $T_2$ 
  as topological spaces. Below we repeat the major theorems of \<open>MetricSpace_ZF\<close> theory
  specialized the standard setting of real valued metrics. \<close>

text\<open>Since in the \<open>pmetric_space1\<close> context $\mathfrak{d}$ is a pseudometrics
  the (real valued) metric topology indeed a topology. \<close>

theorem (in pmetric_space1) rpmetric_is_top:
  shows  "\<tau> {is a topology}"
  using rord_down_directs pmetric_is_top by simp

text\<open>The collection of open disks (caled \<open>ball\<close>s in the \<open>pmetric_space1\<close> context
  is a base for the (real valued) metric topology.\<close>

theorem (in pmetric_space1) rdisks_are_base:
  shows "(\<Union>c\<in>X. {ball(c,R). R\<in>\<real>\<^sub>+}) {is a base for} \<tau>"
  using rord_down_directs disks_are_base by simp

text\<open>$X$ is the carrier of the (real valued) metric topology.\<close>

theorem (in pmetric_space1) rmetric_top_carrier: shows  "\<Union>\<tau> = X"
  using rord_down_directs metric_top_carrier by simp

text\<open>The topology generated by a (real valued) metric is Hausdorff (i.e. $T_2$). \<close>

theorem (in metric_space1) rmetric_space_T2: shows "\<tau> {is T\<^sub>2}"
  using rord_down_directs metric_space_T2 by simp

end