(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2019 Slawomir Kolodynski

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

section \<open> Uniform spaces \<close>

theory UniformSpace_ZF imports Topology_ZF_4a
begin

text\<open> This theory defines uniform spaces and proves their basic properties. \<close>

subsection\<open> Definition and motivation \<close>

text\<open> Just like a topological space constitutes the minimal setting 
  in which one can speak of continuous functions, the notion of uniform spaces 
  (commonly attributed to André Weil) captures the minimal setting in which one can speak 
  of uniformly continuous functions. 
  In some sense this is a generalization of the notion of metric (or metrizable) 
  spaces and topological groups. \<close>

text\<open> There are several definitions of uniform spaces. 
  The fact that these definitions are equivalent is far from obvious
  (some people call such phenomenon cryptomorphism). 
  We will use the definition of the uniform structure (or ''uniformity'') 
  based on entourages. This was the original definition by Weil and it seems 
  to be the most commonly used.
  A uniformity consists of entourages that are binary relations between points of space $X$ 
  that satisfy a certain collection of conditions, specified below. \<close>

definition
  IsUniformity ("_ {is a uniformity on} _" 90) where
    "\<Phi> {is a uniformity on} X \<equiv>(\<Phi> {is a filter on} (X\<times>X))
    \<and> (\<forall>U\<in>\<Phi>. id(X) \<subseteq> U \<and> (\<exists>V\<in>\<Phi>. V O V \<subseteq> U) \<and> converse(U) \<in> \<Phi>)"

text\<open> If $\Phi$ is a uniformity on $X$, then the every element $V$ of $\Phi$ is a certain relation on $X$ (a subset of $X\times X$ and is called 
  an ''entourage''. For an $x\in X$ we call $V\{ x\}$ a neighborhood of $x$. 
  The first useful fact we will show is that neighborhoods are non-empty. \<close>

lemma neigh_not_empty: 
  assumes "\<Phi> {is a uniformity on} X" "V\<in>\<Phi>" and "x\<in>X"
  shows "V``{x} \<noteq> 0" and "x \<in> V``{x}"
proof -
  from assms(1,2) have "id(X) \<subseteq> V" using IsUniformity_def IsFilter_def 
    by auto
  with \<open>x\<in>X\<close> show" x\<in>V``{x}" and "V``{x} \<noteq> 0" by auto
qed

text\<open> Uniformity \<open>\<Phi>\<close>  defines a natural topology on its space $X$ via the neighborhood system 
  that assigns the collection $\{V(\{x\}):V\in \Phi\}$ to every point $x\in X$. 
  In the next lemma we show that if we define a function
  this way the values of that function are what they should be. This is only a technical
  fact which is useful to shorten the remaining proofs, usually treated as obvious in standard
  mathematics. \<close>

lemma neigh_filt_fun: 
  assumes "\<Phi> {is a uniformity on} X"
  defines "\<M> \<equiv> {\<langle>x,{V``{x}.V\<in>\<Phi>}\<rangle>.x\<in>X}"
  shows "\<M>:X\<rightarrow>Pow(Pow(X))" and "\<forall>x\<in>X. \<M>`(x) = {V``{x}.V\<in>\<Phi>}"
proof -
  from assms have "\<forall>x\<in>X. {V``{x}.V\<in>\<Phi>} \<in> Pow(Pow(X))" 
    using IsUniformity_def IsFilter_def image_subset by auto
  with assms show "\<M>:X\<rightarrow>Pow(Pow(X))" using ZF_fun_from_total by simp
  with assms show "\<forall>x\<in>X. \<M>`(x) = {V``{x}.V\<in>\<Phi>}" using ZF_fun_from_tot_val
    by simp
qed

text\<open> In the next lemma we show that the collection defined in lemma \<open>neigh_filt_fun\<close> is a filter on $X$.
   The proof is kind of long, but it just checks that all filter conditions hold.\<close>

lemma filter_from_uniformity: 
  assumes "\<Phi> {is a uniformity on} X" and "x\<in>X"
  defines "\<M> \<equiv> {\<langle>x,{V``{x}.V\<in>\<Phi>}\<rangle>.x\<in>X}" 
  shows "\<M>`(x) {is a filter on} X"
proof -
  from assms have PhiFilter: "\<Phi> {is a filter on} (X\<times>X)" and 
    "\<M>:X\<rightarrow>Pow(Pow(X))" and "\<M>`(x) = {V``{x}.V\<in>\<Phi>}"
    using IsUniformity_def neigh_filt_fun by auto
  have "0 \<notin> \<M>`(x)"
  proof -
    from assms \<open>x\<in>X\<close> have "0 \<notin> {V``{x}.V\<in>\<Phi>}" using neigh_not_empty by blast  
    with \<open>\<M>`(x) = {V``{x}.V\<in>\<Phi>}\<close> show "0 \<notin> \<M>`(x)" by simp 
  qed
  moreover have "X \<in> \<M>`(x)"
  proof -
    note \<open>\<M>`(x) = {V``{x}.V\<in>\<Phi>}\<close> 
    moreover from assms have "X\<times>X \<in> \<Phi>" unfolding IsUniformity_def IsFilter_def 
      by blast
    hence "(X\<times>X)``{x} \<in> {V``{x}.V\<in>\<Phi>}" by auto
    moreover from \<open>x\<in>X\<close> have "(X\<times>X)``{x} = X" by auto
    ultimately show "X \<in> \<M>`(x)" by simp 
  qed
  moreover from \<open>\<M>:X\<rightarrow>Pow(Pow(X))\<close> \<open>x\<in>X\<close> have "\<M>`(x) \<subseteq> Pow(X)" using apply_funtype
    by blast
  moreover have LargerIn: "\<forall>B \<in> \<M>`(x). \<forall>C \<in> Pow(X). B\<subseteq>C \<longrightarrow> C \<in> \<M>`(x)"
  proof -
  { fix B assume "B \<in> \<M>`(x)"
    fix C assume "C \<in> Pow(X)" and "B\<subseteq>C"
    from \<open>\<M>`(x) = {V``{x}.V\<in>\<Phi>}\<close> \<open>B \<in> \<M>`(x)\<close> obtain U where
         "U\<in>\<Phi>" and "B = U``{x}" by auto 
    let ?V = "U \<union> C\<times>C"
    from assms \<open>U\<in>\<Phi>\<close> \<open>C \<in> Pow(X)\<close> have "?V \<in> Pow(X\<times>X)" and "U\<subseteq>?V" 
      using IsUniformity_def IsFilter_def by auto
    with \<open>U\<in>\<Phi>\<close> PhiFilter have "?V\<in>\<Phi>" using IsFilter_def by simp
    moreover from assms \<open>U\<in>\<Phi>\<close> \<open>x\<in>X\<close> \<open>B = U``{x}\<close> \<open>B\<subseteq>C\<close> have "C = ?V``{x}"
      using neigh_not_empty image_greater_rel by simp  
    ultimately have "C \<in> {V``{x}.V\<in>\<Phi>}" by auto 
    with \<open>\<M>`(x) = {V``{x}.V\<in>\<Phi>}\<close> have "C \<in> \<M>`(x)" by simp
  } thus ?thesis by blast
  qed
  moreover have "\<forall>A \<in> \<M>`(x).\<forall>B \<in> \<M>`(x). A\<inter>B \<in> \<M>`(x)"
  proof -
  { fix A B assume "A \<in> \<M>`(x)" and "B \<in> \<M>`(x)"
    with \<open>\<M>`(x) = {V``{x}.V\<in>\<Phi>}\<close> obtain V\<^sub>A V\<^sub>B where
      "A = V\<^sub>A``{x}" "B = V\<^sub>B``{x}" and  "V\<^sub>A \<in> \<Phi>" "V\<^sub>B \<in> \<Phi>"
      by auto 
    let ?C = "V\<^sub>A``{x} \<inter> V\<^sub>B``{x}"
    from assms \<open>V\<^sub>A \<in> \<Phi>\<close> \<open>V\<^sub>B \<in> \<Phi>\<close> have "V\<^sub>A\<inter>V\<^sub>B \<in> \<Phi>" using IsUniformity_def IsFilter_def 
      by simp
    with \<open>\<M>`(x) = {V``{x}.V\<in>\<Phi>}\<close> have "(V\<^sub>A\<inter>V\<^sub>B)``{x} \<in> \<M>`(x)" by auto
    moreover from PhiFilter \<open>V\<^sub>A \<in> \<Phi>\<close> \<open>V\<^sub>B \<in> \<Phi>\<close> have "?C \<in> Pow(X)" unfolding IsFilter_def
            by auto 
    moreover have "(V\<^sub>A\<inter>V\<^sub>B)``{x} \<subseteq> ?C" using image_Int_subset_left by simp
    moreover note LargerIn
    ultimately have "?C \<in> \<M>`(x)" by simp
    with \<open>A = V\<^sub>A``{x}\<close> \<open>B = V\<^sub>B``{x}\<close> have "A\<inter>B \<in> \<M>`(x)" by blast
  } thus ?thesis by simp
  qed
  ultimately show ?thesis unfolding IsFilter_def by simp
qed
 
text\<open> The function defined in the premises of lemma \<open>neigh_filt_fun\<close>
  (or \<open>filter_from_uniformity\<close>) is a neighborhood system. The proof uses the existence
  of the "half-the-size" neighborhood condition (\<open>\<exists>V\<in>\<Phi>. V O V \<subseteq> U\<close>) of the uniformity definition, 
  but not the \<open>converse(U) \<in> \<Phi>\<close> part. \<close>

theorem neigh_from_uniformity: 
  assumes "\<Phi> {is a uniformity on} X"
  shows "{\<langle>x,{V``{x}.V\<in>\<Phi>}\<rangle>.x\<in>X} {is a neighborhood system on} X"
proof -
  let ?\<M> = "{\<langle>x,{V``{x}.V\<in>\<Phi>}\<rangle>.x\<in>X}"
  from assms have "?\<M>:X\<rightarrow>Pow(Pow(X))" and Mval: "\<forall>x\<in>X. ?\<M>`(x) = {V``{x}.V\<in>\<Phi>}"
    using IsUniformity_def neigh_filt_fun by auto 
  moreover from assms have "\<forall>x\<in>X. (?\<M>`(x) {is a filter on} X)" using filter_from_uniformity
    by simp
  moreover 
  { fix x assume "x\<in>X"
    have "\<forall>N\<in>?\<M>`(x). x\<in>N \<and> (\<exists>U\<in>?\<M>`(x).\<forall>y\<in>U.(N\<in>?\<M>`(y)))"
    proof -
      { fix N assume "N\<in>?\<M>`(x)"
        have "x\<in>N" and "\<exists>U\<in>?\<M>`(x).\<forall>y\<in>U.(N \<in> ?\<M>`(y))"
        proof -
          from \<open>?\<M>:X\<rightarrow>Pow(Pow(X))\<close> Mval \<open>x\<in>X\<close> \<open>N\<in>?\<M>`(x)\<close> 
          obtain U where "U\<in>\<Phi>" and "N = U``{x}" by auto 
          with assms \<open>x\<in>X\<close> show "x\<in>N" using neigh_not_empty by simp
          from assms \<open>U\<in>\<Phi>\<close> obtain V where "V\<in>\<Phi>"  and  "V O V \<subseteq> U" 
            unfolding IsUniformity_def by auto
          let ?W = "V``{x}"
          from \<open>V\<in>\<Phi>\<close> Mval \<open>x\<in>X\<close> have "?W \<in> ?\<M>`(x)" by auto
          moreover have "\<forall>y\<in>?W. N \<in> ?\<M>`(y)"
          proof -
            { fix y assume "y\<in>?W"
              with \<open>?\<M>:X\<rightarrow>Pow(Pow(X))\<close> \<open>x\<in>X\<close> \<open>?W \<in> ?\<M>`(x)\<close> have "y\<in>X" 
                using apply_funtype by blast
              with assms have "?\<M>`(y) {is a filter on} X" using filter_from_uniformity
                by simp
              moreover from assms \<open>y\<in>X\<close> \<open>V\<in>\<Phi>\<close> have "V``{y} \<in> ?\<M>`(y)" 
                using neigh_filt_fun by auto      
              moreover from \<open>?\<M>:X\<rightarrow>Pow(Pow(X))\<close> \<open>x\<in>X\<close> \<open>N \<in> ?\<M>`(x)\<close> have "N \<in> Pow(X)" 
                using apply_funtype by blast 
              moreover from \<open>V O V \<subseteq> U\<close> \<open>y\<in>?W\<close> have 
                "V``{y} \<subseteq> (V O V)``{x}" and "(V O V)``{x} \<subseteq> U``{x}"
                by auto 
              with \<open>N = U``{x}\<close>  have "V``{y} \<subseteq> N" by blast
              ultimately have "N \<in> ?\<M>`(y)" unfolding IsFilter_def by simp
            } thus ?thesis by simp 
          qed
          ultimately show "\<exists>U\<in>?\<M>`(x).\<forall>y\<in>U.(N \<in> ?\<M>`(y))" by auto
        qed
      } thus ?thesis by simp
    qed 
  }   
  ultimately show ?thesis unfolding IsNeighSystem_def by simp
qed

text\<open> When we have a uniformity $\Phi$ on $X$ we can define a topology on $X$ in a (relatively)
  natural way. We will call that topology the \<open> UniformTopology(\<Phi>)\<close>. The definition may be a bit 
  cryptic but it just combines the construction of a neighborhood system from uniformity as in 
  the assumptions of lemma \<open>filter_from_uniformity\<close> and the construction of topology from 
  a neighborhood system from theorem \<open>topology_from_neighs\<close>. 
  We could probably reformulate the definition to skip 
  the $X$ parameter because if $\Phi$ is a uniformity on $X$ then $X$ can be recovered 
  from (is determined by) $\Phi$. \<close>

definition
   "UniformTopology(\<Phi>,X) \<equiv> {U \<in> Pow(X). \<forall>x\<in>U. U \<in> {\<langle>t,{V``{t}.V\<in>\<Phi>}\<rangle>.t\<in>X}`(x)}"

text\<open> The collection of sets constructed in the \<open> UniformTopology \<close> definition
  is indeed a topology on $X$. \<close>

theorem uniform_top_is_top:
  assumes "\<Phi> {is a uniformity on} X"
  shows 
  "UniformTopology(\<Phi>,X) {is a topology}" and "\<Union> UniformTopology(\<Phi>,X) = X"
  using assms  neigh_from_uniformity UniformTopology_def topology_from_neighs
  by auto 

end
