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

theory UniformSpace_ZF imports Topology_ZF_2 Topology_ZF_4a
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

text\<open> If $\Phi$ is a uniformity on $X$, then the every element $V$ of $\Phi$ 
  is a certain relation on $X$ (a subset of $X\times X$) and is called 
  an ''entourage''. For an $x\in X$ we call $V\{ x\}$ a neighborhood of $x$. 
  The first useful fact we will show is that neighborhoods are non-empty. \<close>

lemma neigh_not_empty: 
  assumes "\<Phi> {is a uniformity on} X" "W\<in>\<Phi>" and "x\<in>X"
  shows "W``{x} \<noteq> 0" and "x \<in> W``{x}"
proof -
  from assms(1,2) have "id(X) \<subseteq> W" 
    unfolding IsUniformity_def IsFilter_def by auto
  with \<open>x\<in>X\<close> show" x\<in>W``{x}" and "W``{x} \<noteq> 0" by auto
qed

text\<open>The filter part of the definition of uniformity for easier reference:\<close>

lemma unif_filter: assumes "\<Phi> {is a uniformity on} X"
  shows "\<Phi> {is a filter on} (X\<times>X)"
  using assms unfolding IsUniformity_def by simp

text\<open>The second part of the definition of uniformity for easy reference:\<close>

lemma entourage_props: 
  assumes "\<Phi> {is a uniformity on} X" and "A\<in>\<Phi>"
  shows
    "A \<subseteq> X\<times>X"
    "id(X) \<subseteq> A"
    "\<exists>V\<in>\<Phi>. V O V \<subseteq> A"
    "converse(A) \<in> \<Phi>"
proof -
  from assms show "id(X) \<subseteq> A" "\<exists>V\<in>\<Phi>. V O V \<subseteq> A" "converse(A) \<in> \<Phi>"
    unfolding IsUniformity_def by auto
  from assms show "A \<subseteq> X\<times>X"
    using unif_filter unfolding IsFilter_def by blast
qed

text\<open>The definition of uniformity states (among other things) that for every member $U$
  of uniformity $\Phi$ there is another one, say $V$ such that $V\circ V\subseteq U$. Sometimes such $V$
  is said to be half the size of $U$. The next lemma states that $V$ can be taken to be symmetric. \<close>

lemma half_size_symm: assumes "\<Phi> {is a uniformity on} X" "W\<in>\<Phi>" 
  shows "\<exists>V\<in>\<Phi>. V O V \<subseteq> W \<and> V=converse(V)"
proof -
  from assms obtain U where "U\<in>\<Phi>" and "U O U \<subseteq> W"
    unfolding IsUniformity_def by auto
  let ?V = "U \<inter> converse(U)"
  from assms(1) \<open>U\<in>\<Phi>\<close> have "?V \<in> \<Phi>" and "?V = converse(?V)" 
    unfolding IsUniformity_def IsFilter_def by auto
  moreover from \<open>U O U \<subseteq> W\<close> have "?V O ?V \<subseteq> W" by auto
  ultimately show ?thesis by blast
qed

text\<open>Inside every member $W$ of the uniformity $\Phi$ we can find one that is symmetric and 
  smaller than a third of size $W$. Compare with the Metamath's theorem with the same name.\<close>

lemma ustex3sym: assumes "\<Phi> {is a uniformity on} X" "A\<in>\<Phi>"
  shows "\<exists>B\<in>\<Phi>. B O (B O B) \<subseteq> A \<and> B=converse(B)"
proof -
  from assms obtain C where "C\<in>\<Phi>" and "C O C \<subseteq> A"
    unfolding IsUniformity_def by auto
  from assms(1) \<open>C\<in>\<Phi>\<close> obtain B where 
    "B\<in>\<Phi>" "B O B \<subseteq> C" and "B=converse(B)"
    using half_size_symm by blast
  with \<open>C O C \<subseteq> A\<close> have "(B O B) O (B O B) \<subseteq> A" by blast
  with assms(1) \<open>B\<in>\<Phi>\<close> have "B O (B O B) \<subseteq> A"
    using entourage_props(1,2) by blast
  with \<open>B\<in>\<Phi>\<close> \<open>B=converse(B)\<close> show ?thesis by blast
qed

text\<open>If $\Phi$ is a uniformity on $X$ then every element of $\Phi$ is a subset of $X\times X$ 
  whose domain is $X$. \<close>

lemma uni_domain: 
  assumes "\<Phi> {is a uniformity on} X" "W\<in>\<Phi>" 
  shows "W \<subseteq> X\<times>X" and "domain(W) = X" 
proof -
  from assms show "W \<subseteq> X\<times>X" unfolding IsUniformity_def IsFilter_def 
    by blast
  show "domain(W) = X"
  proof 
    from assms show "domain(W) \<subseteq> X" unfolding IsUniformity_def IsFilter_def 
      by auto
    from assms show "X \<subseteq> domain(W)" unfolding IsUniformity_def by blast
  qed
qed

text\<open>If $\Phi$ is a uniformity on $X$ and $W\in \Phi$ the for every $x\in X$ 
  the image of the singleton $\{ x\}$ by $W$ is contained in $X$. Compare
  the Metamath's theorem with the same name. \<close>

lemma ustimasn: 
  assumes "\<Phi> {is a uniformity on} X" "W\<in>\<Phi>" and "x\<in>X"
  shows "W``{x} \<subseteq> X"
  using assms uni_domain(1) by auto

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

text\<open>A rephrasing of \<open>filter_from_uniformity\<close>: if $\Phi$ is a uniformity on $X$, 
  then $\{V(\{ x\}) | V\in \Phi\}$ is a filter on $X$ for every $x\in X$.\<close>

lemma unif_filter_at_point: 
  assumes "\<Phi> {is a uniformity on} X" and "x\<in>X"
  shows "{V``{x}.V\<in>\<Phi>} {is a filter on} X"
  using assms filter_from_uniformity ZF_fun_from_tot_val1 
  by simp

text\<open>A frequently used property of filters is that they are "upward closed" i.e.  supersets 
  of a filter element are also in the filter. The next lemma makes this explicit
  for easy reference as applied to the natural filter created from a uniformity.\<close>

corollary unif_filter_up_closed: 
  assumes "\<Phi> {is a uniformity on} X" "x\<in>X" "U \<in> {V``{x}. V\<in>\<Phi>}" "W\<subseteq>X" "U\<subseteq>W"
  shows "W \<in> {V``{x}.V\<in>\<Phi>}"
  using assms filter_from_uniformity ZF_fun_from_tot_val1
  unfolding IsFilter_def by auto
 
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
  natural way. We will call that topology the \<open> UniformTopology(\<Phi>)\<close>.
  We could probably reformulate the definition to skip 
  the $X$ parameter because if $\Phi$ is a uniformity on $X$ then $X$ can be recovered 
  from (is determined by) $\Phi$. \<close>

definition
  "UniformTopology(\<Phi>,X) \<equiv> {U\<in>Pow(X). \<forall>x\<in>U. U\<in>{V``{x}. V\<in>\<Phi>}}"

text\<open>An identity showing how the definition of uniform topology is constructed.
  Here, the $M = \{\langle t,\{ V\{ t\} : V\in \Phi\}\rangle : t\in X\}$ is the neighborhood system
  (a function on $X$) created from uniformity $\Phi$. 
  Then for each $x\in X$, $M(x) = \{ V\{ t\} : V\in \Phi\}$ is the set of neighborhoods of $x$. \<close>

lemma uniftop_def_alt: 
  shows "UniformTopology(\<Phi>,X) = {U \<in> Pow(X). \<forall>x\<in>U. U \<in> {\<langle>t,{V``{t}.V\<in>\<Phi>}\<rangle>.t\<in>X}`(x)}"
proof -
  let ?\<M> = "{\<langle>x,{V``{x}. V\<in>\<Phi>}\<rangle>. x\<in>X}"
  have "\<forall>U\<in>Pow(X).\<forall>x\<in>U. ?\<M>`(x) = {V``{x}. V\<in>\<Phi>}"
    using ZF_fun_from_tot_val1 by auto
  then show ?thesis unfolding UniformTopology_def by auto
qed

text\<open> The collection of sets constructed in the \<open> UniformTopology \<close> definition
  is indeed a topology on $X$. \<close>

theorem uniform_top_is_top:
  assumes "\<Phi> {is a uniformity on} X"
  shows 
  "UniformTopology(\<Phi>,X) {is a topology}" and "\<Union> UniformTopology(\<Phi>,X) = X"
  using assms neigh_from_uniformity uniftop_def_alt topology_from_neighs
  by auto 

text\<open>If we have a uniformity $\Phi$ we can create a neighborhood system from it in two ways.
  We can create a a neighborhood system directly from $\Phi$ using the formula 
  $X \ni x \mapsto \{V\{x\} | x\in X\}$ (see theorem \<open>neigh_from_uniformity\<close>).
  Alternatively we can construct a topology from $\Phi$ as in theorem 
  \<open>uniform_top_is_top\<close> and then create a neighborhood system from this topology
  as in theorem \<open>neigh_from_topology\<close>. The next theorem states that these two ways give the same 
  result. \<close>

theorem neigh_unif_same: assumes "\<Phi> {is a uniformity on} X"
  shows 
    "{\<langle>x,{V``{x}.V\<in>\<Phi>}\<rangle>. x\<in>X} = {neighborhood system of} UniformTopology(\<Phi>,X)"
  using assms neigh_from_uniformity nei_top_nei_round_trip uniftop_def_alt
  by simp

text\<open>Another form of the definition of topology generated from a uniformity.\<close>

lemma uniftop_def_alt1: assumes "\<Phi> {is a uniformity on} X"
  shows "UniformTopology(\<Phi>,X) = {U\<in>Pow(X).  \<forall>x\<in>U. \<exists>W\<in>\<Phi>. W``{x} \<subseteq> U}"
proof
  let ?T = "UniformTopology(\<Phi>,X)"
  show "?T \<subseteq> {U\<in>Pow(X).  \<forall>x\<in>U. \<exists>W\<in>\<Phi>. W``{x} \<subseteq> U}"
    unfolding UniformTopology_def by auto
  { fix U assume "U\<in>{U\<in>Pow(X).  \<forall>x\<in>U. \<exists>W\<in>\<Phi>. W``{x} \<subseteq> U}"
    then have "U\<in>Pow(X)" and I: "\<forall>x\<in>U. \<exists>W\<in>\<Phi>. W``{x} \<subseteq> U" by auto
    { fix x assume "x\<in>U"
      with I obtain W where "W\<in>\<Phi>" and "W``{x} \<subseteq> U"
        by auto
      let ?\<FF> = "{V``{x}.V\<in>\<Phi>}"
      from assms(1) \<open>U\<in>Pow(X)\<close> \<open>x\<in>U\<close> \<open>W\<in>\<Phi>\<close> have 
        "?\<FF> {is a filter on} X" and "W``{x} \<in> ?\<FF>"
        using unif_filter_at_point by auto
      with \<open>U\<in>Pow(X)\<close> \<open>W``{x} \<subseteq> U\<close> have "U\<in>?\<FF>"
        using is_filter_def_split(5) by blast
    } hence "\<forall>x\<in>U. U \<in> {V``{x}.V\<in>\<Phi>}" by simp
    with \<open>U\<in>Pow(X)\<close> have "U\<in>?T"
      unfolding UniformTopology_def by simp
  } thus "{U\<in>Pow(X).  \<forall>x\<in>U. \<exists>W\<in>\<Phi>. W``{x} \<subseteq> U} \<subseteq> ?T"
    by blast
qed

text\<open>Images of singletons by entourages are neighborhoods of those singletons.\<close>

lemma image_singleton_ent_nei: 
  assumes "\<Phi> {is a uniformity on} X" "V\<in>\<Phi>" "x\<in>X"
  defines "\<M> \<equiv> {neighborhood system of} UniformTopology(\<Phi>,X)"
  shows "V``{x} \<in> \<M>`(x)"
proof -
  from assms(1,4) have "\<M> = {\<langle>x,{V``{x}.V\<in>\<Phi>}\<rangle>. x\<in>X}"
    using neigh_unif_same by simp
  with assms(2,3) show ?thesis
    using ZF_fun_from_tot_val1 by auto
qed

text\<open>The set neighborhoods of a singleton $\{ x\}$ where $x\in X$ consist
  of images of the singleton by the entourages $W\in \Phi$. 
  See also the Metamath's theorem with the same name. \<close>

lemma utopsnneip: assumes "\<Phi> {is a uniformity on} X" "x\<in>X"
  defines "\<S> \<equiv> {set neighborhood system of} UniformTopology(\<Phi>,X)"
  shows "\<S>`{x} = {W``{x}. W\<in>\<Phi>}"
proof -
  let ?T = "UniformTopology(\<Phi>,X)"
  let ?\<M> = "{neighborhood system of} ?T"
  from assms(1,2) have "x \<in> \<Union>?T"
    using uniform_top_is_top(2) by simp
  with assms(3) have "?\<M>`(x) = \<S>`{x}"
    using neigh_from_nei by simp
  moreover 
  from assms(1) have "?\<M> = {\<langle>x,{W``{x}.W\<in>\<Phi>}\<rangle>. x\<in>X}"
    using neigh_unif_same by simp
  with assms(2) have "?\<M>`(x) =  {W``{x}.W\<in>\<Phi>}"
    using ZF_fun_from_tot_val1 by simp
  ultimately show ?thesis by simp
qed

text\<open>Images of singletons by entourages are set neighborhoods of those singletons.
  See also the Metamath theorem with the same name.\<close>

corollary utopsnnei: assumes "\<Phi> {is a uniformity on} X" "W\<in>\<Phi>" "x\<in>X"
  defines "\<S> \<equiv> {set neighborhood system of} UniformTopology(\<Phi>,X)"
  shows "W``{x} \<in> \<S>`{x}" using assms utopsnneip by auto
  
text\<open>If $\Phi$ is a uniformity on $X$ that generates a topology $T$, $R$ is any relation
  on $X$ (i.e. $R\subseteq X\times X$), $W$ is a symmetric entourage (i.e. $W\in \Phi$,
  and $W$ is symmetric (i.e. equal to its converse)), then the closure of $R$ in the product topology
  is contained the the composition $V\circ (M \circ V)$. 
  Metamath has a similar theorem with the same name.  \<close>

lemma utop3cls: 
  assumes "\<Phi> {is a uniformity on} X" "R\<subseteq>X\<times>X" "W\<in>\<Phi>" "W=converse(W)"
  defines "J \<equiv> UniformTopology(\<Phi>,X)"
  shows "Closure(R,J\<times>\<^sub>tJ) \<subseteq> W O (R O W)"
proof
  let ?M = "{set neighborhood system of} (J\<times>\<^sub>tJ)"
  fix z assume zMem: "z \<in> Closure(R,J\<times>\<^sub>tJ)"
  from assms(1,5) have Jtop: "J {is a topology}" and "\<Union>J = X"
    using uniform_top_is_top by auto
  then have JJtop: "(J\<times>\<^sub>tJ) {is a topology}" and JxJ: "\<Union>(J\<times>\<^sub>tJ) = X\<times>X"
    using Top_1_4_T1(1,3) by auto
  with assms(2) have "topology0(J\<times>\<^sub>tJ)" and "R \<subseteq> \<Union>(J\<times>\<^sub>tJ)"
    unfolding topology0_def by auto
  then have "Closure(R,J\<times>\<^sub>tJ) \<subseteq> \<Union>(J\<times>\<^sub>tJ)"
    using topology0.Top_3_L11(1) by simp
  with \<open>z \<in> Closure(R,J\<times>\<^sub>tJ)\<close> JxJ have "z\<in>X\<times>X" by auto
  let ?x = "fst(z)"
  let ?y = "snd(z)"
  from \<open>z\<in>X\<times>X\<close> have "?x\<in>X" "?y\<in>X" "z = \<langle>?x,?y\<rangle>" by auto
  with assms(1,3,5) Jtop have "(W``{?x})\<times>(W``{?y}) \<in> ?M`({?x}\<times>{?y})"
    using utopsnnei neitx by simp
  moreover from \<open>z = \<langle>?x,?y\<rangle>\<close> have "{?x}\<times>{?y} = {z}" 
    by (rule pair_prod)
  ultimately have "(W``{?x})\<times>(W``{?y}) \<in> ?M`{z}" by simp
  with zMem JJtop \<open>R \<subseteq> \<Union>(J\<times>\<^sub>tJ)\<close> have "(W``{?x})\<times>(W``{?y}) \<inter> R \<noteq> 0" 
    using neindisj by blast
  with assms(4) have "\<langle>?x,?y\<rangle> \<in> W O (R O W)" 
    using sym_rel_comp by simp
  with \<open>z = \<langle>?x,?y\<rangle>\<close> show "z \<in> W O (R O W)"
    by simp
qed

text\<open>Uniform spaces are regular ($T_3$). \<close>

theorem utopreg: 
  assumes "\<Phi> {is a uniformity on} X"
  shows "UniformTopology(\<Phi>,X) {is regular}"
proof -
  let ?J = "UniformTopology(\<Phi>,X)"
  let ?\<S> = "{set neighborhood system of} ?J"
  from assms have "\<Union>?J = X"
    and Jtop: "?J {is a topology}" and cntx: "topology0(?J)"
    using uniform_top_is_top unfolding topology0_def by auto 
  have "\<forall>U\<in>?J. \<forall>x\<in>U. \<exists>V\<in>?J. x\<in>V \<and> Closure(V,?J)\<subseteq>U"
  proof -
    { fix U x assume "U\<in>?J" "x\<in>U"
      then have "U \<in> ?\<S>`{x}" using open_nei_singl by simp
      from \<open>U\<in>?J\<close> have "U\<subseteq>\<Union>?J" by auto
      with \<open>x\<in>U\<close> \<open>\<Union>?J = X\<close> have "x\<in>X" by auto
      from assms(1) \<open>x\<in>X\<close> \<open>U \<in> ?\<S>`{x}\<close> obtain A 
        where "U=A``{x}" and "A\<in>\<Phi>"
        using utopsnneip by auto
      from assms(1) \<open>A\<in>\<Phi>\<close> obtain W where 
        "W\<in>\<Phi>" "W O (W O W) \<subseteq> A" and Wsymm: "W=converse(W)"
        using ustex3sym by blast
      with assms(1) \<open>x\<in>X\<close> have "W``{x} \<in> ?\<S>`{x}" and "W``{x} \<subseteq> X"
        using utopsnnei ustimasn by auto
      from \<open>W``{x} \<in> ?\<S>`{x}\<close> have "\<exists>V\<in>?J. {x}\<subseteq>V \<and> V\<subseteq>W``{x}"
        by (rule neii2)
      then obtain V where "V\<in>?J" "x\<in>V" "V\<subseteq>W``{x}"
        by blast
      have "Closure(V,?J) \<subseteq> U"
      proof -
        from assms(1) \<open>W\<in>\<Phi>\<close> \<open>\<Union>?J = X\<close> have "W \<subseteq> X\<times>X"
          using entourage_props(1) by simp
        from cntx \<open>W``{x} \<subseteq> X\<close> \<open>\<Union>?J = X\<close> \<open>V\<subseteq>W``{x}\<close>
          have "Closure(V,?J) \<subseteq> Closure(W``{x},?J)"
            using topology0.top_closure_mono by simp
        also have "Closure(W``{x},?J) \<subseteq> Closure(W,?J\<times>\<^sub>t?J)``{x}"
        proof -
          from \<open>W\<subseteq>X\<times>X\<close> \<open>x\<in>X\<close> \<open>\<Union>?J = X\<close> 
            have "W\<subseteq>(\<Union>?J)\<times>(\<Union>?J)" "x\<in>\<Union>?J" by auto
          with \<open>?J {is a topology}\<close> show ?thesis 
            using imasncls by simp
        qed
        also from assms(1) \<open>W\<subseteq>X\<times>X\<close> \<open>W\<in>\<Phi>\<close> Wsymm \<open>W O (W O W) \<subseteq> A\<close>
          have "Closure(W,?J\<times>\<^sub>t?J)``{x} \<subseteq> A``{x}"
            using utop3cls by blast
        finally have "Closure(V,?J) \<subseteq> A``{x}"
          by simp
        with \<open>U=A``{x}\<close> show ?thesis by auto
      qed
      with \<open>V\<in>?J\<close> \<open>x\<in>V\<close> have "\<exists>V\<in>?J. x\<in>V \<and> Closure(V,?J)\<subseteq>U" 
        by blast
    } thus ?thesis by simp
  qed
  with Jtop show "?J {is regular}" using is_regular_def_alt
    by simp
qed

end
