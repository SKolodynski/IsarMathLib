(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2019-2025 Slawomir Kolodynski

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

section \<open>Uniform spaces\<close>

theory UniformSpace_ZF imports Cardinal_ZF Order_ZF_1a Topology_ZF_2 Topology_ZF_4a
begin

text\<open> This theory defines uniform spaces and proves their basic properties. \<close>

subsection\<open> Entourages and neighborhoods \<close>

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

text\<open>Since the whole $XUniformities\times X$ is in a uniformity, a uniformity is never empty.\<close>

lemma uniformity_non_empty: assumes "\<Phi> {is a uniformity on} X"
    shows "\<Phi>\<noteq>\<emptyset>"
  using assms unfolding IsUniformity_def IsFilter_def by auto

text\<open> If $\Phi$ is a uniformity on $X$, then the every element $V$ of $\Phi$ 
  is a certain relation on $X$ (a subset of $X\times X$) and is called 
  an ''entourage''. For an $x\in X$ we call $V\{ x\}$ a neighborhood of $x$. 
  The first useful fact we will show is that neighborhoods are non-empty. \<close>

lemma neigh_not_empty: 
  assumes "\<Phi> {is a uniformity on} X" "W\<in>\<Phi>" and "x\<in>X"
  shows "W``{x} \<noteq> \<emptyset>" and "x \<in> W``{x}"
proof -
  from assms(1,2) have "id(X) \<subseteq> W" 
    unfolding IsUniformity_def IsFilter_def by auto
  with \<open>x\<in>X\<close> show" x\<in>W``{x}" and "W``{x} \<noteq> \<emptyset>" by auto
qed

text\<open>The filter part of the definition of uniformity for easier reference:\<close>

lemma unif_filter: assumes "\<Phi> {is a uniformity on} X"
  shows "\<Phi> {is a filter on} (X\<times>X)"
  using assms unfolding IsUniformity_def by simp

text\<open>If $X$ is not empty then the singleton $\{ X\times X\}$ is a (trivial) 
  example of a uniformity on $X$. \<close>

lemma min_uniformity: assumes "X\<noteq>\<emptyset>" shows "{X\<times>X} {is a uniformity on} X"
  using assms unfolding IsFilter_def IsUniformity_def by auto

text\<open>On the other side of the spectrum is the collection of sets containing the
  diagonal, that is also a uniformity.\<close>

lemma max_uniformity: assumes "X\<noteq>\<emptyset>" 
  shows "{U\<in>Pow(X\<times>X). id(X)\<subseteq>U} {is a uniformity on} X"
  using assms unfolding IsFilter_def IsUniformity_def by auto

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
  have "\<emptyset> \<notin> \<M>`(x)"
  proof -
    from assms \<open>x\<in>X\<close> have "\<emptyset> \<notin> {V``{x}.V\<in>\<Phi>}" using neigh_not_empty by blast  
    with \<open>\<M>`(x) = {V``{x}.V\<in>\<Phi>}\<close> show "\<emptyset> \<notin> \<M>`(x)" by simp 
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
  $X \ni x \mapsto \{V\{x\} | V\in \Phi\}$ (see theorem \<open>neigh_from_uniformity\<close>).
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
  with zMem JJtop \<open>R \<subseteq> \<Union>(J\<times>\<^sub>tJ)\<close> have "(W``{?x})\<times>(W``{?y}) \<inter> R \<noteq> \<emptyset>" 
    using neindisj by blast
  with assms(4) have "\<langle>?x,?y\<rangle> \<in> W O (R O W)" 
    using sym_rel_comp by simp
  with \<open>z = \<langle>?x,?y\<rangle>\<close> show "z \<in> W O (R O W)"
    by simp
qed

text\<open>Uniform spaces are regular. Note that is not the same as $T_3$, see \<open>Topology_ZF_1\<close> 
  for separation axioms definitions. In some sources the definitions of "regular" and $T_3$
  are swapped. In IsarMathLib we adopt the terminology as on the "Separation axiom" 
  page on Wikipedia.\<close>

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

text\<open>If the topological space generated by a uniformity $\Phi$ on $X$ is $T_1$ 
  then the intersection $\bigcup \Phi$ is contained in the diagonal 
  $\{\langle x,x\rangle : x\in X\}$. Note the opposite inclusion is true for every uniformity.\<close>

lemma unif_t1_inter_diag: 
  assumes "\<Phi> {is a uniformity on} X" and "UniformTopology(\<Phi>,X) {is T\<^sub>1}"
  shows "\<Inter>\<Phi> \<subseteq> {\<langle>x,x\<rangle>. x\<in>X}"
proof -
  let ?T = "UniformTopology(\<Phi>,X)"
  from assms(1) have "\<Inter>\<Phi> \<subseteq> X\<times>X" using uniformity_non_empty entourage_props(1) 
    by blast
  { fix p assume "p \<in> \<Inter>\<Phi>" and "p \<notin> {\<langle>x,x\<rangle>. x\<in>X}"
    from \<open>\<Inter>\<Phi> \<subseteq> X\<times>X\<close> \<open>p \<in> \<Inter>\<Phi>\<close> obtain x y where "x\<in>X" "y\<in>X" "p = \<langle>x,y\<rangle>" by auto
    with assms \<open>p \<notin> {\<langle>x,x\<rangle>. x\<in>X}\<close> obtain U where "U \<in> ?T" "x\<in>U" "y\<notin>U"
      using uniform_top_is_top(2) unfolding isT1_def by force 
    with assms(1) \<open>p = \<langle>x,y\<rangle>\<close> \<open>p \<in> \<Inter>\<Phi>\<close> have False 
      using uniftop_def_alt1 by force
  } with \<open>\<Inter>\<Phi> \<subseteq> X\<times>X\<close> show ?thesis by blast
qed

text\<open>If the intersection of a uniformity is contained in the the diagonal 
  $\{\langle x,x\rangle : x\in X\}$ then the topological space generated by this uniformity 
  is $T_1$.\<close>

lemma unif_inter_diag_t1: 
  assumes "\<Phi> {is a uniformity on} X" and "\<Inter>\<Phi> \<subseteq> {\<langle>x,x\<rangle>. x\<in>X}"
  shows "UniformTopology(\<Phi>,X) {is T\<^sub>1}"
proof -
  let ?T = "UniformTopology(\<Phi>,X)" 
  let ?\<M> = "{neighborhood system of} ?T"
  from assms(1) have "\<Union>?T = X" using uniform_top_is_top(2) by simp
  { fix x y assume "x\<in>X" "y\<in>X" "x\<noteq>y"
    with assms obtain W where "W\<in>\<Phi>" and "y\<notin>W``{x}" 
      using uniformity_non_empty by blast
    from assms(1) \<open>x\<in>X\<close> \<open>W\<in>\<Phi>\<close> have "W``{x} \<in> ?\<M>`(x)"
      using image_singleton_ent_nei by simp
    with \<open>x\<in>X\<close> \<open>\<Union>?T = X\<close> \<open>y\<notin>W``{x}\<close> have "\<exists>U\<in>?T. x\<in>U \<and> y\<notin>U"
      using neigh_val by auto
  } with \<open>\<Union>?T = X\<close> show ?thesis unfolding isT1_def by simp
qed

text\<open>If $\Phi$ is a uniformity on $X$ then the intersection of $\Phi$ is contained in 
  diagonal of $X$ if and only if $\bigcup \Phi$ is equal to that diagonal. Some people call
  such uniform space "separating".\<close>

theorem unif_inter_diag: assumes "\<Phi> {is a uniformity on} X"
  shows "\<Inter>\<Phi> \<subseteq> {\<langle>x,x\<rangle>. x\<in>X} \<longleftrightarrow> \<Inter>\<Phi> = {\<langle>x,x\<rangle>. x\<in>X}"
  using assms entourage_props(2) uniformity_non_empty by force


text\<open>The next theorem collects the information we have to show that
  if $\Phi$ is a uniformity on $X$, with the induced topology $T$ then
  conditions $T$ is $T_0$, $T$ is $T_1$, $T$ is $T_2$ $T$ is $T_3$ are all equivalent to
  the intersection of $\Phi$ being contained in the diagonal 
  (which is equivalent to the intersection of $\Phi$ being equal to the diagonal, see 
  \<open>unif_inter_diag\<close> above.\<close>

theorem unif_sep_axioms_diag: assumes "\<Phi> {is a uniformity on} X"
  defines "T \<equiv> UniformTopology(\<Phi>,X)"
  shows 
    "\<Inter>\<Phi> \<subseteq> {\<langle>x,x\<rangle>. x\<in>X} \<longleftrightarrow> T {is T\<^sub>0}"
    "\<Inter>\<Phi> \<subseteq> {\<langle>x,x\<rangle>. x\<in>X} \<longleftrightarrow> T {is T\<^sub>1}"
    "\<Inter>\<Phi> \<subseteq> {\<langle>x,x\<rangle>. x\<in>X} \<longleftrightarrow> T {is T\<^sub>2}"
    "\<Inter>\<Phi> \<subseteq> {\<langle>x,x\<rangle>. x\<in>X} \<longleftrightarrow> T {is T\<^sub>3}"
proof -
  from assms show "\<Inter>\<Phi> \<subseteq> {\<langle>x,x\<rangle>. x\<in>X} \<longleftrightarrow> T {is T\<^sub>1}"
    using unif_t1_inter_diag unif_inter_diag_t1 by auto
  with assms show 
    "\<Inter>\<Phi> \<subseteq> {\<langle>x,x\<rangle>. x\<in>X} \<longleftrightarrow> T {is T\<^sub>0}"
    "\<Inter>\<Phi> \<subseteq> {\<langle>x,x\<rangle>. x\<in>X} \<longleftrightarrow> T {is T\<^sub>2}"
    "\<Inter>\<Phi> \<subseteq> {\<langle>x,x\<rangle>. x\<in>X} \<longleftrightarrow> T {is T\<^sub>3}"
    using utopreg T1_is_T0 T3_is_T2 T2_is_T1
    unfolding isT3_def by auto
qed

subsection\<open> Base of a uniformity \<close>

text\<open>A \<open>base\<close> or a \<open>fundamental system of entourages\<close> of a uniformity $\Phi$ is 
  a subset of $\Phi$ that is sufficient to uniquely determine it. This is 
  analogous to the notion of a base of a topology (see \<open>Topology_ZF_1\<close> or a base of a filter
  (see \<open>Topology_ZF_4\<close>). \<close>

text\<open>A base of a uniformity $\Phi$ is any subset $\mathfrak{B}\subseteq \Phi$ such that
  every entourage in $\Phi$ contains (at least) one from $\mathfrak{B}$. 
  The phrase \<open>is a base for\<close> is already defined to mean a base for a topology, 
  so we use the phrase \<open>is a uniform base of\<close> here. \<close>

definition
  IsUniformityBase ("_ {is a uniform base of} _" 90) where
    "\<BB> {is a uniform base of} \<Phi> \<equiv> \<BB> \<subseteq> \<Phi> \<and> (\<forall>U\<in>\<Phi>. \<exists>B\<in>\<BB>. B\<subseteq>U)"

text\<open>Symmetric entourages form a base of the uniformity.\<close>

lemma symm_are_base: assumes "\<Phi> {is a uniformity on} X"
  shows "{V\<in>\<Phi>. V = converse(V)} {is a uniform base of} \<Phi>"
proof -
  let ?\<BB> = "{V\<in>\<Phi>. V = converse(V)}"
  { fix W assume "W\<in>\<Phi>"
    with assms obtain V where "V\<in>\<Phi>" "V O V \<subseteq> W"  "V=converse(V)"
      using half_size_symm by blast
    from assms \<open>V\<in>\<Phi>\<close> have "V \<subseteq> V O V"
      using entourage_props(1,2) refl_square_greater by blast
    with \<open>V O V \<subseteq> W\<close> \<open>V\<in>\<Phi>\<close> \<open>V=converse(V)\<close> have "\<exists>V\<in>?\<BB>. V\<subseteq>W" by auto
  } hence "\<forall>W\<in>\<Phi>. \<exists>V\<in>?\<BB>. V \<subseteq> W" by auto
  then show ?thesis unfolding IsUniformityBase_def by auto
qed

text\<open>Given a base of a uniformity we can recover the uniformity taking the supersets.
  The \<open>Supersets\<close> constructor is defined in \<open>ZF1\<close>.\<close>

lemma uniformity_from_base: 
  assumes "\<Phi> {is a uniformity on} X" "\<BB> {is a uniform base of} \<Phi>"
  shows "\<Phi> = Supersets(X\<times>X,\<BB>)"
proof
  from assms show "\<Phi> \<subseteq> Supersets(X\<times>X,\<BB>)"
    unfolding IsUniformityBase_def Supersets_def
    using entourage_props(1) by auto
  from assms show "Supersets(X\<times>X,\<BB>) \<subseteq> \<Phi>"
    unfolding Supersets_def IsUniformityBase_def IsUniformity_def IsFilter_def
    by auto
qed

text\<open>Analogous to the predicate "satisfies base condition" (defined in \<open>Topology_ZF_1\<close>)
  and "is a base filter" (defined in \<open>Topology_ZF_4\<close>) we can specify conditions 
  for a collection $\mathfrak{B}$ of subsets of $X\times X$ to be a base of some
  uniformity on $X$. Namely, the following conditions are necessary and sufficient:

  1. Intersection of two sets of $\mathfrak{B}$ contains a set of $\mathfrak{B}$.

  2. Every set of $\mathfrak{B}$ contains the diagonal of $X\times X$.

  3. For each set $B_1\in \mathfrak{B}$ we can find a set $B_2\in \mathfrak{B}$ 
  such that $B_2\subseteq B_1^{-1}$.

  4. For each set $B_1\in \mathfrak{B}$ we can find a set $B_2\in \mathfrak{B}$
  such that $B_2\circ B_2 \subseteq B_1$.

  The conditions in the definition below are taken from 
  N. Bourbaki "Elements of Mathematics, General Topology", Chapter II.1., 
  except for the last two that are missing there.\<close>

definition
  IsUniformityBaseOn ("_ {is a uniform base on} _" 90) where
    "\<BB> {is a uniform base on} X \<equiv> 
      (\<forall>B\<^sub>1\<in>\<BB>. \<forall>B\<^sub>2\<in>\<BB>. \<exists>B\<^sub>3\<in>\<BB>. B\<^sub>3\<subseteq>B\<^sub>1\<inter>B\<^sub>2) \<and> (\<forall>B\<in>\<BB>. id(X)\<subseteq>B) \<and>
      (\<forall>B\<^sub>1\<in>\<BB>. \<exists>B\<^sub>2\<in>\<BB>. B\<^sub>2 \<subseteq> converse(B\<^sub>1)) \<and> (\<forall>B\<^sub>1\<in>\<BB>. \<exists>B\<^sub>2\<in>\<BB>. B\<^sub>2 O B\<^sub>2 \<subseteq> B\<^sub>1) \<and>
      \<BB>\<subseteq>Pow(X\<times>X) \<and> \<BB>\<noteq>\<emptyset>"

text\<open>The next lemma splits the definition of \<open>IsUniformityBaseOn\<close> into four conditions
  to enable more precise references in proofs.\<close>

lemma uniformity_base_props: assumes "\<BB> {is a uniform base on} X"
  shows
  "\<forall>B\<^sub>1\<in>\<BB>. \<forall>B\<^sub>2\<in>\<BB>. \<exists>B\<^sub>3\<in>\<BB>. B\<^sub>3\<subseteq>B\<^sub>1\<inter>B\<^sub>2"
  "\<forall>B\<in>\<BB>. id(X)\<subseteq>B"
  "\<forall>B\<^sub>1\<in>\<BB>. \<exists>B\<^sub>2\<in>\<BB>. B\<^sub>2 \<subseteq> converse(B\<^sub>1)"
  "\<forall>B\<^sub>1\<in>\<BB>. \<exists>B\<^sub>2\<in>\<BB>. B\<^sub>2 O B\<^sub>2 \<subseteq> B\<^sub>1"
  "\<BB>\<subseteq>Pow(X\<times>X)" and "\<BB>\<noteq>\<emptyset>"
  using assms unfolding IsUniformityBaseOn_def by simp_all

text\<open>If supersets of some collection of subsets of $X\times X$ form a uniformity,
  then this collection satisfies the conditions in the definition of \<open>IsUniformityBaseOn\<close>. \<close>

theorem base_is_uniform_base: 
  assumes "\<BB>\<subseteq>Pow(X\<times>X)" and "Supersets(X\<times>X,\<BB>) {is a uniformity on} X"
  shows "\<BB> {is a uniform base on} X"
proof -
  let ?\<Phi> = "Supersets(X\<times>X,\<BB>)"
  have "\<forall>B\<^sub>1\<in>\<BB>. \<forall>B\<^sub>2\<in>\<BB>. \<exists>B\<^sub>3\<in>\<BB>. B\<^sub>3\<subseteq>B\<^sub>1\<inter>B\<^sub>2"
  proof -
    { fix B\<^sub>1 B\<^sub>2 assume "B\<^sub>1\<in>\<BB>" "B\<^sub>2\<in>\<BB>"
      with assms(1) have "B\<^sub>1\<in>?\<Phi>" and "B\<^sub>2\<in>?\<Phi>" unfolding Supersets_def by auto
      with assms(2) have "\<exists>B\<^sub>3\<in>\<BB>. B\<^sub>3 \<subseteq> B\<^sub>1\<inter>B\<^sub>2"
        unfolding IsUniformity_def IsFilter_def Supersets_def by simp
    } thus ?thesis by simp
  qed
  moreover have "\<forall>B\<in>\<BB>. id(X)\<subseteq>B"
  proof -
    { fix B assume "B\<in>\<BB>"
      with assms(1) have "B\<in>?\<Phi>" unfolding Supersets_def by auto
      with assms(2) have "id(X)\<subseteq>B" unfolding IsUniformity_def by simp
    } thus ?thesis by simp
  qed
  moreover have "\<forall>B\<^sub>1\<in>\<BB>. \<exists>B\<^sub>2\<in>\<BB>. B\<^sub>2 \<subseteq> converse(B\<^sub>1)"
  proof -
    { fix B\<^sub>1 assume "B\<^sub>1\<in>\<BB>"
      with assms(1) have "B\<^sub>1\<in>?\<Phi>" unfolding Supersets_def by auto
      with assms have "\<exists>B\<^sub>2\<in>\<BB>. B\<^sub>2 \<subseteq> converse(B\<^sub>1)" 
        unfolding IsUniformity_def Supersets_def by auto
    } thus ?thesis by simp
  qed
  moreover have "\<forall>B\<^sub>1\<in>\<BB>. \<exists>B\<^sub>2\<in>\<BB>. B\<^sub>2 O B\<^sub>2 \<subseteq> B\<^sub>1"
  proof -
    { fix B\<^sub>1 assume "B\<^sub>1\<in>\<BB>"
      with assms(1) have "B\<^sub>1\<in>?\<Phi>" unfolding Supersets_def by auto 
      with assms(2) obtain V where "V\<in>?\<Phi>" and "V O V \<subseteq> B\<^sub>1"
        unfolding IsUniformity_def by blast
      from assms(2) \<open>V\<in>?\<Phi>\<close> obtain B\<^sub>2 where "B\<^sub>2\<in>\<BB>" and "B\<^sub>2\<subseteq>V"
        unfolding Supersets_def by auto
      from \<open>V O V \<subseteq> B\<^sub>1\<close> \<open>B\<^sub>2\<subseteq>V\<close> have "B\<^sub>2 O B\<^sub>2 \<subseteq> B\<^sub>1" by auto
      with \<open>B\<^sub>2\<in>\<BB>\<close> have "\<exists>B\<^sub>2\<in>\<BB>. B\<^sub>2 O B\<^sub>2 \<subseteq> B\<^sub>1" by auto
    } thus ?thesis by simp
  qed
  moreover from assms(2) have "\<BB>\<noteq>\<emptyset>"
    using supersets_of_empty uniformity_non_empty by blast
  ultimately show "\<BB> {is a uniform base on} X"
    unfolding IsUniformityBaseOn_def using assms(1) by simp
qed

text\<open>if a nonempty collection of subsets of $X\times X$ satisfies conditions in the definition 
  of \<open>IsUniformityBaseOn\<close> then the supersets of that collection form a uniformity on $X$.\<close>

theorem uniformity_base_is_base: 
  assumes "X\<noteq>\<emptyset>" and "\<BB> {is a uniform base on} X"
  shows "Supersets(X\<times>X,\<BB>) {is a uniformity on} X"
proof -
  let ?\<Phi> = "Supersets(X\<times>X,\<BB>)"
  from assms(2) have "\<BB>\<subseteq>Pow(X\<times>X)" using uniformity_base_props(5)
    by simp
  have "?\<Phi> {is a filter on} (X\<times>X)"
  proof -
    from assms have "\<emptyset>\<notin>?\<Phi>"
      unfolding Supersets_def using uniformity_base_props(2) 
      by blast
    moreover have "X\<times>X \<in> ?\<Phi>"
    proof -
      from assms(2) obtain B where "B\<in>\<BB>"
        using uniformity_base_props(6) by blast
      with \<open>\<BB>\<subseteq>Pow(X\<times>X)\<close> show "X\<times>X \<in> ?\<Phi>" unfolding Supersets_def 
        by blast
    qed
    moreover have "?\<Phi> \<subseteq> Pow(X\<times>X)" unfolding Supersets_def by auto
    moreover have "\<forall>U\<in>?\<Phi>. \<forall>V\<in>?\<Phi>. U\<inter>V \<in> ?\<Phi>"
    proof -
      { fix U V assume "U\<in>?\<Phi>" "V\<in>?\<Phi>"
        then obtain B\<^sub>1 B\<^sub>2 where "B\<^sub>1\<in>\<BB>" "B\<^sub>2\<in>\<BB>" "B\<^sub>1\<subseteq>U" "B\<^sub>2\<subseteq>V"
          unfolding Supersets_def by auto
        from assms(2) \<open>B\<^sub>1\<in>\<BB>\<close> \<open>B\<^sub>2\<in>\<BB>\<close> obtain B\<^sub>3 where "B\<^sub>3\<in>\<BB>" and "B\<^sub>3\<subseteq>B\<^sub>1\<inter>B\<^sub>2"
          using uniformity_base_props(1) by blast
        from \<open>B\<^sub>1\<subseteq>U\<close> \<open>B\<^sub>2\<subseteq>V\<close> \<open>B\<^sub>3\<subseteq>B\<^sub>1\<inter>B\<^sub>2\<close> have "B\<^sub>3\<subseteq>U\<inter>V" by auto
        with \<open>U\<in>?\<Phi>\<close> \<open>V\<in>?\<Phi>\<close> \<open>B\<^sub>3\<in>\<BB>\<close> have "U\<inter>V \<in> ?\<Phi>"
          unfolding Supersets_def by auto
      } thus ?thesis by simp
    qed
    moreover have "\<forall>U\<in>?\<Phi>. \<forall>C\<in>Pow(X\<times>X). U\<subseteq>C \<longrightarrow> C\<in>?\<Phi>"
    proof -
      { fix U C assume "U\<in>?\<Phi>" "C\<in>Pow(X\<times>X)" "U\<subseteq>C"
        from \<open>U\<in>?\<Phi>\<close> obtain B where "B\<in>\<BB>" and "B\<subseteq>U"
          unfolding Supersets_def by auto
        with \<open>U\<subseteq>C\<close> \<open>C\<in>Pow(X\<times>X)\<close> have "C\<in>?\<Phi>"
          unfolding Supersets_def by auto
      } thus ?thesis by auto
    qed
    ultimately show "?\<Phi> {is a filter on} (X\<times>X)"
      unfolding IsFilter_def by simp
  qed
  moreover have "\<forall>U\<in>?\<Phi>. id(X) \<subseteq> U \<and> (\<exists>V\<in>?\<Phi>. V O V \<subseteq> U) \<and> converse(U) \<in> ?\<Phi>"
  proof -
    { fix U assume "U\<in>?\<Phi>"
      then obtain B where "B\<in>\<BB>" and "B\<subseteq>U"
        unfolding Supersets_def by auto
      with assms(2) have "id(X) \<subseteq> U"
        using uniformity_base_props(2) by blast
      moreover
      from assms(2) \<open>B\<in>\<BB>\<close> obtain V where "V\<in>\<BB>" and "V O V \<subseteq> B"
        using uniformity_base_props(4) by blast
      with \<open>\<BB>\<subseteq>Pow(X\<times>X)\<close> have "V\<in>?\<Phi>" using superset_gen by auto
      with \<open>V O V \<subseteq> B\<close> \<open>B\<subseteq>U\<close> have "\<exists>V\<in>?\<Phi>. V O V \<subseteq> U" by blast
      moreover 
      from assms(2) \<open>B\<in>\<BB>\<close> \<open>B\<subseteq>U\<close> obtain W where "W\<in>\<BB>" and "W \<subseteq> converse(U)"
        using uniformity_base_props(3) by blast
      with \<open>U\<in>?\<Phi>\<close> have "converse(U) \<in> ?\<Phi>" unfolding Supersets_def 
        by auto
      ultimately have "id(X) \<subseteq> U \<and> (\<exists>V\<in>?\<Phi>. V O V \<subseteq> U) \<and> converse(U) \<in> ?\<Phi>"
        by simp
    } thus ?thesis by simp
  qed
  ultimately show ?thesis unfolding IsUniformity_def by simp
qed

text\<open>The assumption that $X$ is not empty in \<open>uniformity_base_is_base\<close> above is neccessary
  as the assertion is false if $X$ is empty.\<close>

lemma uniform_space_empty: assumes "\<BB> {is a uniform base on} \<emptyset>"
  shows "\<not>(Supersets(\<emptyset>\<times>\<emptyset>,\<BB>) {is a uniformity on} \<emptyset>)"
proof -
  { let ?\<Phi> = "Supersets(\<emptyset>\<times>\<emptyset>,\<BB>)"
    assume "?\<Phi> {is a uniformity on} \<emptyset>"
    from assms have "\<BB>={\<emptyset>}" using uniformity_base_props(5,6) by force
    with \<open>?\<Phi> {is a uniformity on} \<emptyset>\<close> have False
      using supersets_in_empty unif_filter unfolding IsFilter_def by auto
  } thus ?thesis by auto
qed

subsection\<open>Least upper bound of a set of uniformities\<close>

text\<open>Uniformities on a set $X$ are naturally ordered by the inclusion relation.
  Specifically, for two uniformities $\mathcal{U}_1$ and $\mathcal{U}_2$​ on a set $X$ 
  if $\mathcal{U}_1 \subseteq \mathcal{U}_2$ we say that $\mathcal{U}_2$ is finer than 
  $\mathcal{U}_1$ or that $\mathcal{U}_1$ is coarser than $\mathcal{U}_2$. 
  Turns out this order is complete: every nonempty set of uniformities has
  a least upper bound, i.e. a supremum. \<close>

text\<open>We define \<open>UniformitiesOn(X)\<close> as the set of all uniformities on $X$. \<close>

definition 
  "Uniformities(X) \<equiv> {\<Phi> \<in> Pow(Pow(X\<times>X)). \<Phi> {is a uniformity on} X}"

text\<open>If $Phi$ is a uniformity on $X$, then $Phi$ is a collection of subsets of $X\times X$,
  hence it's a member of \<open>Uniformities(X)\<close>.\<close>

lemma unif_in_unifs: assumes "\<Phi> {is a uniformity on} X"
  shows "\<Phi> \<in> Uniformities(X)"
  using assms unfolding Uniformities_def IsUniformity_def IsFilter_def
  by auto

text\<open>For nonempty sets the set of uniformities is not empty as well.\<close>

lemma unifomities_exist: assumes "X\<noteq>\<emptyset>" shows "Uniformities(X)\<noteq>\<emptyset>"
  unfolding Uniformities_def using assms min_uniformity by auto

text\<open>Uniformities on a set $X$ are naturally ordered by inclusion, we call
  the resulting order relation \<open>OrderOnUniformities\<close>.\<close>

definition
  "OrderOnUniformities(X) \<equiv> InclusionOn(Uniformities(X))"

text\<open>The order defined by inclusion on uniformities is a partial order.\<close>

lemma ord_unif_partial_ord: 
  shows "IsPartOrder(Uniformities(X),OrderOnUniformities(X))"
  unfolding OrderOnUniformities_def using incl_is_partorder by simp

text\<open>In particular, the order defined by inclusion on uniformities is antisymmetric.
  Having this as a separate fact is handy as we reference some lemmas 
  proven for antisymmetric (not necessarily partial order) relations.\<close>

lemma ord_unif_antisymm: shows "antisym(OrderOnUniformities(X))"
  using ord_unif_partial_ord unfolding IsPartOrder_def by simp

text\<open>If $X$ is not empty then the singleton $\{ X\times X\}$ is the minimal
  element of the set of uniformities on $X$ ordered by inclusion 
  and the collection of subsets of $X\times X$ that contain the diagonal
  is the maximal element.\<close>

theorem uniformities_min_max: assumes "X\<noteq>\<emptyset>" shows 
  "HasAminimum(OrderOnUniformities(X),Uniformities(X))"
  "Minimum(OrderOnUniformities(X),Uniformities(X)) = {X\<times>X}"
  "HasAmaximum(OrderOnUniformities(X),Uniformities(X))"
  "Maximum(OrderOnUniformities(X),Uniformities(X)) = {U\<in>Pow(X\<times>X). id(X)\<subseteq>U}"
proof -
  let ?\<UU> = "Uniformities(X)"
  let ?r = "OrderOnUniformities(X)"
  let ?M = "{U\<in>Pow(X\<times>X). id(X)\<subseteq>U}"
  from assms have "{X\<times>X} \<in> ?\<UU>" and "?M\<in>?\<UU>"
    unfolding Uniformities_def using min_uniformity max_uniformity 
    by auto
  { fix \<Phi> assume "\<Phi> \<in> ?\<UU>"
    then have "\<Phi> {is a filter on} (X\<times>X)"
      unfolding Uniformities_def using unif_filter by simp
    with \<open>{X\<times>X}\<in>?\<UU>\<close> \<open>\<Phi>\<in>?\<UU>\<close> have "\<langle>{X\<times>X},\<Phi>\<rangle> \<in> ?r"
      unfolding IsFilter_def OrderOnUniformities_def InclusionOn_def
      by simp
  } with  \<open>{X\<times>X} \<in> ?\<UU>\<close> show "HasAminimum(?r,?\<UU>)" and "Minimum(?r,?\<UU>) = {X\<times>X}"
    unfolding HasAminimum_def using Order_ZF_4_L15 ord_unif_antisymm by auto
  { fix \<Phi> assume "\<Phi> \<in> ?\<UU>"
    then have "\<Phi> \<subseteq> ?M" unfolding IsUniformity_def Uniformities_def 
      by auto
    with \<open>?M\<in>?\<UU>\<close> \<open>\<Phi>\<in>?\<UU>\<close>  have "\<langle>\<Phi>,?M\<rangle> \<in> ?r"
      unfolding OrderOnUniformities_def InclusionOn_def by simp
  } with  \<open>?M\<in>?\<UU>\<close> show "HasAmaximum(?r,?\<UU>)" and "Maximum(?r,?\<UU>) = ?M"
    unfolding HasAmaximum_def using Order_ZF_4_L14 ord_unif_antisymm by auto
qed

text\<open>Given a set of uniformities $\mathcal{U}$ on $X$ we define a collection of subsets of $X$ 
  called \<open>LUB_UnifBase\<close> (the least upper bound base in comments) 
  as the set of all products of nonempty finite subsets of $\bigcup\mathcal{U}$. 
  The "least upper bound base" term is not justified at this point, but we will show later 
  that this set is actually a uniform base (i.e. a fundamental system of entourages) 
  on $X$ and hence the supersets of it form a uniformity on $X$, which is the supremum 
  (i.e. the least upper bound) of $\mathcal{U}$.\<close>

definition "LUB_UnifBase(\<U>) = {\<Inter>M. M \<in> FinPow(\<Union>\<U>)\<setminus>{\<emptyset>}}"

text\<open>For any two sets in the least upper bound base there is a third one contained in both.\<close>

lemma lub_unif_base_1st_cond: 
  assumes "\<U>\<subseteq>Uniformities(X)" "U\<^sub>1 \<in> LUB_UnifBase(\<U>)" "U\<^sub>2 \<in> LUB_UnifBase(\<U>)"
  shows "\<exists>U\<^sub>3\<in>LUB_UnifBase(\<U>). U\<^sub>3\<subseteq>U\<^sub>1\<inter>U\<^sub>2"
proof -
  let ?\<F> = "FinPow(\<Union>\<U>)\<setminus>{\<emptyset>}"
  from assms(2,3) obtain M\<^sub>1 M\<^sub>2 where 
    "M\<^sub>1\<in>?\<F>" "M\<^sub>1\<noteq>\<emptyset>" "U\<^sub>1=\<Inter>M\<^sub>1" "M\<^sub>2\<in>?\<F>" "M\<^sub>2\<noteq>\<emptyset>" "U\<^sub>2=\<Inter>M\<^sub>2"
    unfolding LUB_UnifBase_def by auto
  let ?M\<^sub>3 = "M\<^sub>1\<union>M\<^sub>2"  
  from \<open>M\<^sub>1\<noteq>\<emptyset>\<close> \<open>M\<^sub>2\<noteq>\<emptyset>\<close> \<open>U\<^sub>1=\<Inter>M\<^sub>1\<close> \<open>U\<^sub>2=\<Inter>M\<^sub>2\<close> have "\<Inter>?M\<^sub>3 \<subseteq> U\<^sub>1\<inter>U\<^sub>2"
    by auto
  with \<open>M\<^sub>1 \<in> ?\<F>\<close> \<open>M\<^sub>2 \<in> ?\<F>\<close> \<open>U\<^sub>2=\<Inter>M\<^sub>2\<close> show ?thesis
    using union_finpow unfolding LUB_UnifBase_def by auto
qed

text\<open>Each set in the least upper bound base contains the diagonal of $X\times X$.\<close>

lemma lub_unif_base_2nd_cond:
  assumes "\<U>\<subseteq>Uniformities(X)" "U \<in> LUB_UnifBase(\<U>)"
  shows "id(X)\<subseteq>U"
  using assms 
  unfolding LUB_UnifBase_def FinPow_def Uniformities_def IsUniformity_def
  by blast

text\<open>The converse of each set from the least upper bound base contains a
  set from it.\<close>

lemma lub_unif_base_3rd_cond:
  assumes "\<U>\<subseteq>Uniformities(X)" "U\<^sub>1 \<in> LUB_UnifBase(\<U>)"
  shows "\<exists>U\<^sub>2 \<in> LUB_UnifBase(\<U>). U\<^sub>2 \<subseteq> converse(U\<^sub>1)"
proof -
  let ?\<F> = "FinPow(\<Union>\<U>)\<setminus>{\<emptyset>}"
  from assms(2) obtain M\<^sub>1 where  "M\<^sub>1\<in>?\<F>" "M\<^sub>1\<noteq>\<emptyset>" "U\<^sub>1=\<Inter>M\<^sub>1"
    unfolding LUB_UnifBase_def by auto
  let ?M\<^sub>2 = "{converse(V). V\<in>M\<^sub>1}"
  from assms(1) \<open>M\<^sub>1\<in>?\<F>\<close> have "\<forall>V\<in>M\<^sub>1. converse(V) \<in> \<Union>\<U>"
    unfolding FinPow_def Uniformities_def using entourage_props(4)
    by blast
  with \<open>M\<^sub>1\<in>?\<F>\<close> have "\<Inter>?M\<^sub>2 \<in> LUB_UnifBase(\<U>)"
    using fin_image_fin0 unfolding LUB_UnifBase_def by auto
  from assms(1) \<open>M\<^sub>1\<in>?\<F>\<close> \<open>U\<^sub>1=\<Inter>M\<^sub>1\<close> have "\<Inter>?M\<^sub>2 \<subseteq> converse(U\<^sub>1)"
    unfolding Uniformities_def FinPow_def using prod_converse
    by blast
  with \<open>\<Inter>?M\<^sub>2 \<in> LUB_UnifBase(\<U>)\<close> show ?thesis by auto
qed

text\<open>For each set (relation) $U_1$ from the least upper bound base there is another one $U_2$
  such that $U_2$ composed with itself is contained in $U_1$.\<close>

lemma lub_unif_base_4th_cond: 
  assumes "\<U>\<subseteq>Uniformities(X)" "U\<^sub>1 \<in> LUB_UnifBase(\<U>)"
  shows "\<exists>U\<^sub>2 \<in> LUB_UnifBase(\<U>). U\<^sub>2 O U\<^sub>2 \<subseteq> U\<^sub>1"
proof -
  let ?\<F> = "FinPow(\<Union>\<U>)\<setminus>{\<emptyset>}"
  from assms(2) obtain M\<^sub>1 where  "M\<^sub>1\<in>?\<F>" "M\<^sub>1\<noteq>\<emptyset>" "U\<^sub>1=\<Inter>M\<^sub>1"
    unfolding LUB_UnifBase_def by auto
  from \<open>M\<^sub>1\<in>?\<F>\<close> have "Finite(M\<^sub>1)" unfolding FinPow_def by simp
  { fix V assume "V\<in>M\<^sub>1"
    with assms(1) \<open>M\<^sub>1\<in>?\<F>\<close> obtain \<Phi> where "\<Phi>\<in>\<U>" and "V\<in>\<Phi>"
      unfolding FinPow_def by auto
    with assms(1) \<open>V\<in>\<Phi>\<close> obtain W where "W\<in>\<Phi>" and "W O W \<subseteq> V"
      unfolding Uniformities_def using entourage_props(3) by blast
    with \<open>\<Phi>\<in>\<U>\<close> have "\<exists>W\<in>\<Union>\<U>. W O W \<subseteq> V" by auto
  } hence "\<forall>V\<in>M\<^sub>1. \<exists>W\<in>\<Union>\<U>. W O W \<subseteq> V" by simp
  with \<open>Finite(M\<^sub>1)\<close> have "\<exists>f\<in>M\<^sub>1\<rightarrow>\<Union>\<U>. \<forall>V\<in>M\<^sub>1. f`(V) O f`(V) \<subseteq> V"
    by (rule finite_choice_fun)
  then obtain f where "f:M\<^sub>1\<rightarrow>\<Union>\<U>" and "\<forall>V\<in>M\<^sub>1. f`(V) O f`(V) \<subseteq> V"
    by auto
  let ?M\<^sub>2 = "{f`(V). V\<in>M\<^sub>1}"
  from \<open>f:M\<^sub>1\<rightarrow>\<Union>\<U>\<close> have "\<forall>V\<in>M\<^sub>1. f`(V) \<in> \<Union>\<U>" using apply_funtype by blast
  with \<open>M\<^sub>1\<in>?\<F>\<close> have "\<Inter>?M\<^sub>2 \<in> LUB_UnifBase(\<U>)"
    using fin_image_fin0 unfolding LUB_UnifBase_def by auto
  from \<open>M\<^sub>1\<noteq>\<emptyset>\<close> \<open>\<forall>V\<in>M\<^sub>1. f`(V) O f`(V) \<subseteq> V\<close> have 
    "(\<Inter>V\<in>M\<^sub>1. f`(V)) O (\<Inter>V\<in>M\<^sub>1. f`(V)) \<subseteq> (\<Inter>V\<in>M\<^sub>1. V)"
    by (rule square_incl_product)
  with \<open>U\<^sub>1=\<Inter>M\<^sub>1\<close> \<open>\<Inter>?M\<^sub>2 \<in> LUB_UnifBase(\<U>)\<close> show ?thesis by auto
qed

text\<open>The least upper bound base is a collection of relations on $X$.\<close>

lemma lub_unif_base_5th_cond:
  assumes "\<U>\<subseteq>Uniformities(X)" shows "LUB_UnifBase(\<U>) \<subseteq> Pow(X\<times>X)"
  using assms unfolding Uniformities_def FinPow_def LUB_UnifBase_def
  by blast

text\<open>If a collection of uniformities is nonempty, then the least upper bound base 
  is non-empty as well.\<close>

lemma lub_unif_base_6th_cond: assumes "\<U>\<subseteq>Uniformities(X)" "\<U>\<noteq>\<emptyset>"
  shows "LUB_UnifBase(\<U>) \<noteq> \<emptyset>"
proof - 
  from assms(2) obtain \<Phi> where "\<Phi>\<in>\<U>" by auto
  with assms(1) have "\<Union>\<U> \<noteq> \<emptyset>" unfolding Uniformities_def 
    using uniformity_non_empty by blast
  then show "LUB_UnifBase(\<U>) \<noteq> \<emptyset>" using finpow_nempty_nempty 
    unfolding LUB_UnifBase_def by simp
qed

text\<open>If a collection of uniformities $\mathcal{U}$ is nonempty, $\mathcal{B}$
  denotes the least upper bound base for $\mathcal{U}$, then $\mathcal{B}$ 
  is a uniform base on $X$, hence its supersets form a uniformity on $X$ and 
  the uniform topology generated by that uniformity is indeed a topology on $X$. \<close>

theorem lub_unif_base_base: 
  assumes "X\<noteq>\<emptyset>" "\<U>\<subseteq>Uniformities(X)" "\<U>\<noteq>\<emptyset>"
  defines "\<BB> \<equiv> LUB_UnifBase(\<U>)"
  shows
    "\<BB> {is a uniform base on} X"
    "Supersets(X\<times>X,\<BB>) {is a uniformity on} X"
    "UniformTopology(Supersets(X\<times>X,\<BB>),X) {is a topology}"
    "\<Union>UniformTopology(Supersets(X\<times>X,\<BB>),X) = X"
  using assms lub_unif_base_1st_cond lub_unif_base_2nd_cond 
    lub_unif_base_3rd_cond lub_unif_base_4th_cond lub_unif_base_5th_cond 
    lub_unif_base_6th_cond uniformity_base_is_base uniform_top_is_top
  unfolding IsUniformityBaseOn_def by simp_all

text\<open>At this point we know that supersets with respect to $X\times X$ 
  of the least upper bound base for a collection of uniformities $\mathcal{U}$ form a uniformity.
  To shorten the notation we will call this uniformity \<open>LUB_Unif(X,\<U>)\<close>.\<close>

definition
  "LUB_Unif(X,\<U>) \<equiv> Supersets(X\<times>X,LUB_UnifBase(\<U>))"

text\<open>For any collection of uniformities $\mathcal{U}$ on a nonempty set $X$ 
  the \<open>LUB_Unif(X,\<U>)\<close> collection defined above is indeed an upper bound of $\mathcal{U}$
  in the order defined by the inclusion relation.\<close>

lemma lub_unif_upper_bound: 
  assumes "X\<noteq>\<emptyset>" "\<U>\<subseteq>Uniformities(X)" "\<Phi>\<in>\<U>"
  shows "\<langle>\<Phi>,LUB_Unif(X,\<U>)\<rangle> \<in> OrderOnUniformities(X)"
proof -
  let ?\<Psi> = "LUB_Unif(X,\<U>)"
  from assms have "?\<Psi> \<in> Uniformities(X)"
    unfolding LUB_Unif_def using lub_unif_base_base(2) unif_in_unifs
    by blast
  from assms(2,3) have "\<Phi> \<in> Uniformities(X)" and "\<Phi> {is a uniformity on} X"
    unfolding Uniformities_def by auto
  { fix E assume "E\<in>\<Phi>"
    with assms(3) have "E \<in> LUB_UnifBase(\<U>)"
      using singleton_in_finpow unfolding LUB_UnifBase_def
      by blast
    with \<open>\<Phi> {is a uniformity on} X\<close> \<open>E\<in>\<Phi>\<close> have "E \<in> ?\<Psi>"
      using entourage_props(1) superset_gen unfolding LUB_Unif_def
      by simp
  } hence "\<Phi> \<subseteq> ?\<Psi>" by auto
  with \<open>\<Phi> \<in> Uniformities(X)\<close> \<open>?\<Psi> \<in> Uniformities(X)\<close> show ?thesis
    unfolding OrderOnUniformities_def InclusionOn_def by simp
qed

text\<open>An upper bound (in the order defined by inclusion relation) of a nonempty collection of 
  uniformities $\mathcal{U}$ on a nonempty set $X$ is greater or equal (in that order) 
  than \<open>LUB_Unif(X,\<U>)\<close>. Together with \<open>lub_unif_upper_bound\<close> it means that \<open>LUB_Unif(X,\<U>)\<close>
  is indeed the least upper bound of $\mathcal{U}$.\<close>

lemma lub_unif_lub: 
  assumes "X\<noteq>\<emptyset>" "\<U>\<subseteq>Uniformities(X)" "\<U>\<noteq>\<emptyset>"  "\<forall>\<Phi>\<in>\<U>. \<langle>\<Phi>,\<Psi>\<rangle> \<in> OrderOnUniformities(X)"
  shows "\<langle>LUB_Unif(X,\<U>),\<Psi>\<rangle> \<in> OrderOnUniformities(X)"
proof -
  from assms(3,4) have "\<Psi> \<in> Uniformities(X)" 
    unfolding OrderOnUniformities_def InclusionOn_def by auto
  then have "\<Psi> {is a filter on} (X\<times>X)" 
    unfolding Uniformities_def IsUniformity_def by simp
  from assms(4) have "FinPow(\<Union>\<U>)\<setminus>{\<emptyset>} \<subseteq> FinPow(\<Psi>)\<setminus>{\<emptyset>}"
    unfolding OrderOnUniformities_def InclusionOn_def FinPow_def by auto 
  with \<open>\<Psi> {is a filter on} (X\<times>X)\<close> have "LUB_UnifBase(\<U>) \<subseteq> \<Psi>"
    using filter_fin_inter_closed unfolding LUB_UnifBase_def by auto
  with \<open>\<Psi> {is a filter on} (X\<times>X)\<close> have "LUB_Unif(X,\<U>) \<subseteq> \<Psi>"
    using filter_superset_closed unfolding LUB_Unif_def by simp
  with assms(1,2,3) \<open>\<Psi> \<in> Uniformities(X)\<close> show ?thesis
    using lub_unif_base_base(2) unif_in_unifs 
    unfolding LUB_Unif_def OrderOnUniformities_def InclusionOn_def 
    by simp
qed

text\<open>A nonempty collection $\mathcal{U}$  of uniformities on $X$ has a supremum 
  (i.e. the least upper bound).\<close>

lemma lub_unif_sup: assumes "X\<noteq>\<emptyset>" "\<U>\<subseteq>Uniformities(X)" "\<U>\<noteq>\<emptyset>"
  shows "HasAsupremum(OrderOnUniformities(X),\<U>)" and
    "LUB_Unif(X,\<U>) = Supremum(OrderOnUniformities(X),\<U>)"
proof -
  let ?r = "OrderOnUniformities(X)"
  let ?S = "LUB_Unif(X,\<U>)"
  from assms(1,2) have "antisym(?r)" and "\<forall>\<Phi>\<in>\<U>. \<langle>\<Phi>,?S\<rangle> \<in> ?r"
    using ord_unif_antisymm lub_unif_upper_bound by simp_all
  from assms have I: "\<forall>\<Psi>. (\<forall>\<Phi>\<in>\<U>. \<langle>\<Phi>,\<Psi>\<rangle> \<in> ?r) \<longrightarrow> \<langle>?S,\<Psi>\<rangle> \<in> ?r"
    using lub_unif_lub by simp
  with assms(3) \<open>antisym(?r)\<close>  \<open>\<forall>\<Phi>\<in>\<U>. \<langle>\<Phi>,?S\<rangle> \<in> ?r\<close> show "HasAsupremum(?r,\<U>)" 
    unfolding HasAsupremum_def using Order_ZF_5_L5(1) by blast
  from assms(3) \<open>antisym(?r)\<close>  \<open>\<forall>\<Phi>\<in>\<U>. \<langle>\<Phi>,?S\<rangle> \<in> ?r\<close> I
  show "?S = Supremum(?r,\<U>)" using Order_ZF_5_L5(2) by blast
qed

text\<open>The order on uniformities derived from inclusion is complete.\<close>

theorem uniformities_complete: assumes "X\<noteq>\<emptyset>"
  shows "OrderOnUniformities(X) {is complete}"
proof -
  let ?r = "OrderOnUniformities(X)"
  { fix \<U> assume "\<U>\<noteq>\<emptyset>" and "IsBoundedAbove(\<U>,?r)"
    then obtain \<Psi> where "\<forall>\<Phi>\<in>\<U>. \<langle>\<Phi>,\<Psi>\<rangle> \<in> ?r"
      unfolding IsBoundedAbove_def by auto
    then have "\<U>\<subseteq>Uniformities(X)" 
      unfolding OrderOnUniformities_def InclusionOn_def by auto
    with assms \<open>\<U>\<noteq>\<emptyset>\<close> have "HasAsupremum(?r,\<U>)"
      using lub_unif_sup by simp
  } 
  then show "?r {is complete}" unfolding HasAsupremum_def IsComplete_def
    by simp
qed

end
