(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2021-2022 Slawomir Kolodynski

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

section \<open> Alternative definitions of uniformity \<close>

theory UniformSpace_ZF_2 imports UniformSpace_ZF
begin

text\<open> The \<open>UniformSpace_ZF\<close> theory defines uniform spaces based on entourages (also called surroundings 
  sometimes). In this theory we consider an alternative definition based of the 
  notion of uniform covers.
  \<close>

subsection\<open> Uniform covers \<close>

text\<open> Given a set $X$ we can consider collections of subsets of $X$ whose unions are equal to $X$. 
  Any such collection is called a cover of $X$. We can define relation on the set of covers
  of $X$, called "star refinement" (definition below). A collection of covers is a 
  "family of uniform covers" if it is a filter with respect to the start refinement ordering. 
  A member of such family is called a "uniform cover", but one has to remember that this notion 
  has meaning only in the contexts a the whole family of uniform covers. Looking at a specific cover
  in isolation we can not say whether it is a uniform cover or not.  \<close>

text\<open> The set of all covers of $X$ is called \<open>Covers(X)\<close>. \<close>

definition 
  "Covers(X) \<equiv> {P \<in> Pow(Pow(X)). \<Union>P = X}" 

text\<open>A cover of a nonempty set must have a nonempty member.\<close>

lemma cover_nonempty: assumes "X\<noteq>0" "P \<in> Covers(X)"
  shows "\<exists>U\<in>P. U\<noteq>0"
  using assms unfolding Covers_def by blast  

text\<open> A "star" of $R$ with respect to $\mathcal{R}$ is the union of all $S\in \mathcal{R}$ that
  intersect $R$. \<close>

definition
  "Star(R,\<R>) \<equiv> \<Union>{S\<in>\<R>. S\<inter>R \<noteq> 0}"

text\<open>An element of $\mathcal{R}$ is a subset of its star with respect to $\mathcal{R}$. \<close>

lemma element_subset_star: assumes "U\<in>P" shows "U \<subseteq> Star(U,P)"
  using assms unfolding Star_def by auto

text\<open>An alternative formula for star of a singleton.\<close>

lemma star_singleton: shows "(\<Union>{V\<times>V. V\<in>P})``{x} = Star({x},P)"
  unfolding Star_def by blast

text\<open>Star of a larger set is larger.\<close>

lemma star_mono: assumes "U\<subseteq>V" shows "Star(U,P) \<subseteq> Star(V,P)"
  using assms unfolding Star_def by blast

text\<open>In particular, star of a set is larger than star of any singleton in that set.\<close>

corollary star_single_mono: assumes "x\<in>U" shows "Star({x},P) \<subseteq> Star(U,P)"
  using assms star_mono by auto

text\<open>A cover $\mathcal{R}$ (of $X$) is said to be a "barycentric refinement" of a cover $\mathcal{C}$ 
  iff for every $x\in X$ the star of $\{x\}$ in $\mathcal{R}$ is contained 
  in some $C\in \mathcal{C}$. \<close>

definition
  IsBarycentricRefinement ("_ <\<^sup>B _" 90) 
  where "P <\<^sup>B Q \<equiv> \<forall>x\<in>\<Union>P.\<exists>U\<in>Q.  Star({x},P) \<subseteq> U"

text\<open>A cover is a barycentric refinement of the collection of stars of the singletons
  $\{x \}$ as $x$ ranges over $X$.\<close>

lemma singl_star_bary: 
  assumes "P \<in> Covers(X)" shows "P <\<^sup>B {Star({x},P). x\<in>X}"
  using assms unfolding Covers_def IsBarycentricRefinement_def by blast    

text\<open> A cover $\mathcal{R}$ is a "star refinement" of a cover $\mathcal{C}$  iff 
  for each $R\in \mathcal{R}$ there is a $C\in \mathcal{C}$ such that the star of $R$ with 
  respect to $\mathcal{R}$ is contained in $C$. \<close>

definition
  IsStarRefinement ("_ <\<^sup>* _" 90)
  where "P <\<^sup>* Q \<equiv> \<forall>U\<in>P.\<exists>V\<in>Q. Star(U,P) \<subseteq> V"

text\<open>Every cover star-refines the trivial cover $\{ X\}$. \<close>

lemma cover_stref_triv: assumes "P \<in> Covers(X)" shows "P <\<^sup>* {X}"
  using assms unfolding Star_def IsStarRefinement_def Covers_def by auto

text\<open>Star refinement implies barycentric refinement. \<close>

lemma star_is_bary: assumes "Q\<in>Covers(X)" and "Q <\<^sup>* P"
  shows "Q <\<^sup>B P"
proof -
  from assms(1) have "\<Union>Q = X" unfolding Covers_def by simp
  { fix x assume "x\<in>X"
    with \<open>\<Union>Q = X\<close> obtain R where "R\<in>Q" and "x\<in>R" by auto
    with assms(2) obtain U where "U\<in>P" and "Star(R,Q) \<subseteq> U"
      unfolding IsStarRefinement_def by auto
    from \<open>x\<in>R\<close> \<open>Star(R,Q) \<subseteq> U\<close> have "Star({x},Q) \<subseteq> U"
      using star_single_mono by blast
    with \<open>U\<in>P\<close> have "\<exists>U\<in>P. Star({x},Q) \<subseteq> U" by auto
 } with \<open>\<Union>Q = X\<close> show ?thesis unfolding IsBarycentricRefinement_def
    by simp
qed

text\<open> Barycentric refinement of a barycentric refinement is a star refinement. \<close>

lemma bary_bary_star: 
  assumes "P\<in>Covers(X)" "Q\<in>Covers(X)" "R\<in>Covers(X)" "P <\<^sup>B Q" "Q <\<^sup>B R" "X\<noteq>0" 
  shows "P <\<^sup>* R"
proof -
  { fix U assume "U\<in>P" 
    { assume "U = 0"
      then have "Star(U,P) = 0" unfolding Star_def by simp
      from assms(6,3) obtain V where "V\<in>R" using cover_nonempty by auto
      with \<open>Star(U,P) = 0\<close> have "\<exists>V\<in>R. Star(U,P) \<subseteq> V" by auto
    }
    moreover 
    { assume "U\<noteq>0"
      then obtain x\<^sub>0 where "x\<^sub>0\<in>U" by auto
      with assms(1,2,5) \<open>U\<in>P\<close> obtain V where "V\<in>R" and "Star({x\<^sub>0},Q) \<subseteq> V"
        unfolding Covers_def IsBarycentricRefinement_def by auto
      have "Star(U,P) \<subseteq> V"
      proof -
        { fix W assume "W\<in>P" and "W\<inter>U \<noteq> 0"
          from \<open>W\<inter>U \<noteq> 0\<close> obtain x where "x\<in>W\<inter>U" by auto
          with assms(2) \<open>U\<in>P\<close> have  "x\<in>\<Union>P" by auto
          with assms(4) obtain C where "C\<in>Q" and "Star({x},P) \<subseteq> C"
            unfolding IsBarycentricRefinement_def by blast
          with \<open>U\<in>P\<close> \<open>W\<in>P\<close> \<open>x\<in>W\<inter>U\<close> \<open>x\<^sub>0\<in>U\<close> \<open>Star({x\<^sub>0},Q) \<subseteq> V\<close> have "W\<subseteq>V" 
            unfolding Star_def by blast
        } then show "Star(U,P) \<subseteq> V" unfolding Star_def by auto        
      qed
      with \<open>V\<in>R\<close> have "\<exists>V\<in>R. Star(U,P) \<subseteq> V" by auto
    }
    ultimately have "\<exists>V\<in>R. Star(U,P) \<subseteq> V" by auto
  } then show "P <\<^sup>* R" unfolding IsStarRefinement_def by simp
qed

text\<open>The notion of a filter defined in \<open>Topology_ZF_4\<close> is not sufficiently general to use it to 
  define uniform covers, so we write the conditions directly. A nonempty 
  collection $\Theta$ of covers of $X$ is a family of uniform covers if  
  
  a) if $\mathcal{R} \in \Theta$ and $\mathcal{C}$ is any cover of $X$ such that $\mathcal{R}$ is 
  a star refinement of $\mathcal{C}$, then $\mathcal{C} \in \Theta$.
  
  b) For any $\mathcal{C},\mathcal{D} \in \Theta$ there is some $\mathcal{R}\in\Theta$ 
  such that $\mathcal{R}$ is a star refinement of both $\mathcal{C}$ and $\mathcal{R}$.

  This departs slightly from the definition in Wikipedia that requires that $\Theta$ contains the
  trivial cover $\{ X\}$. As we show in lemma \<open>unicov_contains_trivial\<close> below we don't loose 
  anything by weakening the definition this way.
  \<close>

definition
  AreUniformCovers ("_ {are uniform covers of} _" 90)
  where "\<Theta> {are uniform covers of} X \<equiv>  \<Theta> \<subseteq> Covers(X) \<and> \<Theta>\<noteq>0 \<and> 
  (\<forall>\<R>\<in>\<Theta>.\<forall>\<C>\<in>Covers(X). ((\<R> <\<^sup>* \<C>) \<longrightarrow> \<C>\<in>\<Theta>)) \<and>
  (\<forall>\<C>\<in>\<Theta>.\<forall>\<D>\<in>\<Theta>.\<exists>\<R>\<in>\<Theta>.(\<R> <\<^sup>* \<C>) \<and> (\<R> <\<^sup>* \<D>))"

text\<open>A family of uniform covers contain the trivial cover $\{ X\}$.\<close>

lemma unicov_contains_triv: assumes "\<Theta> {are uniform covers of} X" 
  shows "{X} \<in> \<Theta>"
proof -
  from assms obtain \<R> where "\<R>\<in>\<Theta>" unfolding AreUniformCovers_def by blast
  with assms show ?thesis using cover_stref_triv 
    unfolding AreUniformCovers_def Covers_def by auto
qed

text\<open>If $\Theta$ are uniform covers of $X$ then we can recover $X$ from $\Theta$ by taking 
  $\bigcup\bigcup \Theta$. \<close>

lemma space_from_unicov: assumes "\<Theta> {are uniform covers of} X" shows "X = \<Union>\<Union>\<Theta>"
proof
  from assms show "X \<subseteq> \<Union>\<Union>\<Theta>" using unicov_contains_triv 
    unfolding AreUniformCovers_def by auto
  from assms show "\<Union>\<Union>\<Theta> \<subseteq> X" unfolding AreUniformCovers_def Covers_def 
    by auto
qed

text\<open> Every uniform cover has a star refinement. \<close>

lemma unicov_has_star_ref: 
  assumes "\<Theta> {are uniform covers of} X" and "P\<in>\<Theta>"
  shows "\<exists>Q\<in>\<Theta>. (Q <\<^sup>* P)"
  using assms unfolding AreUniformCovers_def by blast

text\<open> In particular, every uniform cover has a barycentric refinement. \<close>

corollary unicov_has_bar_ref:
  assumes "\<Theta> {are uniform covers of} X" and "P\<in>\<Theta>"
  shows "\<exists>Q\<in>\<Theta>. (Q <\<^sup>B P)"
proof - 
  from assms obtain Q where "Q\<in>\<Theta>" and "Q <\<^sup>* P" 
    using unicov_has_star_ref by blast
  with assms show ?thesis 
    unfolding AreUniformCovers_def using star_is_bary by blast
qed

text\<open> From the definition of uniform covers we know that if a uniform cover $P$ 
  is a star-refinement of a cover $Q$ then $Q$ is in a uniform cover. The next lemma
  shows that in order for $Q$ to be a uniform cover it is sufficient that $P$ is a 
  barycentric refinement of $Q$. \<close>

lemma unicov_bary_cov: 
  assumes "\<Theta> {are uniform covers of} X" "P\<in>\<Theta>" "Q \<in> Covers(X)" "P <\<^sup>B Q" and "X\<noteq>0" 
  shows "Q\<in>\<Theta>"
proof -
  from assms(1,2) obtain R where "R\<in>\<Theta>" and "R <\<^sup>B P"
    using unicov_has_bar_ref by blast
  from assms(1,2,3) \<open>R\<in>\<Theta>\<close> have 
    "P \<in> Covers(X)" "Q \<in> Covers(X)" "R \<in> Covers(X)"
    unfolding AreUniformCovers_def by auto
  with assms(1,3,4,5) \<open>R\<in>\<Theta>\<close> \<open>R <\<^sup>B P\<close> show ?thesis 
    using bary_bary_star unfolding AreUniformCovers_def by auto
qed

text\<open> A technical lemma to simplify proof of the \<open>uniformity_from_unicov\<close> theorem. \<close>

lemma star_ref_mem: assumes "U\<in>P" "P<\<^sup>*Q" and "\<Union>{W\<times>W. W\<in>Q} \<subseteq> A"
  shows "U\<times>U \<subseteq> A"
proof -
  from assms(1,2) obtain W where "W\<in>Q" and "\<Union>{S\<in>P. S\<inter>U \<noteq> 0} \<subseteq> W"
    unfolding IsStarRefinement_def Star_def by auto
  with assms(1,3) show "U\<times>U \<subseteq> A" by blast
qed

text\<open>An identity related to square (in the sense of composition) of a relation of the 
  form $\bigcup \{U\times U : U\in P\}$. 
  I am amazed that Isabelle can see that this is true without an explicit proof, I can't. \<close>

lemma rel_square_starr: shows 
  "(\<Union>{U\<times>U. U\<in>P}) O (\<Union>{U\<times>U. U\<in>P}) = \<Union>{U\<times>Star(U,P). U\<in>P}"
  unfolding Star_def by blast

text\<open> An identity similar to \<open>rel_square_starr\<close> but with \<open>Star\<close> on the left side of the Cartesian 
  product: \<close>

lemma rel_square_starl: shows 
  "(\<Union>{U\<times>U. U\<in>P}) O (\<Union>{U\<times>U. U\<in>P}) = \<Union>{Star(U,P)\<times>U. U\<in>P}"
  unfolding Star_def by blast


text\<open>A somewhat technical identity about the square of a symmetric relation: \<close>

lemma rel_sq_image: 
  assumes "W = converse(W)"  "domain(W) \<subseteq> X" 
  shows "Star({x},{W``{t}. t\<in>X}) = (W O W)``{x}"
proof
  have I: "Star({x},{W``{t}. t\<in>X}) = \<Union>{S\<in>{W``{t}. t\<in>X}. x\<in>S}" 
    unfolding Star_def by auto
  { fix y assume "y \<in> Star({x},{W``{t}. t\<in>X})"
    with I obtain S where "y\<in>S" "x\<in>S" "S \<in> {W``{t}. t\<in>X}" by auto
    from \<open>S \<in> {W``{t}. t\<in>X}\<close> obtain t where "t\<in>X" and "S = W``{t}" 
      by auto
    with \<open>x\<in>S\<close> \<open>y\<in>S\<close> have "\<langle>t,x\<rangle> \<in> W" and "\<langle>t,y\<rangle> \<in> W" 
      by auto
    from \<open>\<langle>t,x\<rangle> \<in> W\<close> have "\<langle>x,t\<rangle> \<in> converse(W)" by auto
    with assms(1) \<open>\<langle>t,y\<rangle> \<in> W\<close> have "y \<in> (W O W)``{x}" 
      using rel_compdef by auto
  } then show "Star({x},{W``{t}. t\<in>X}) \<subseteq> (W O W)``{x}" 
    by blast
  { fix y assume "y\<in>(W O W)``{x}"
    then obtain t where "\<langle>x,t\<rangle> \<in> W" and "\<langle>t,y\<rangle> \<in> W"
      using rel_compdef by auto
    from assms(2) \<open>\<langle>t,y\<rangle> \<in> W\<close> have "t\<in>X" by auto
    from \<open>\<langle>x,t\<rangle> \<in> W\<close> have "\<langle>t,x\<rangle> \<in> converse(W)" by auto
    with assms(1) I \<open>\<langle>t,y\<rangle> \<in> W\<close> \<open>t\<in>X\<close> have "y \<in> Star({x},{W``{t}. t\<in>X})"
      by auto
  } then show "(W O W)``{x} \<subseteq> Star({x},{W``{t}. t\<in>X})"
    by blast
qed

text\<open> Given a family of uniform covers of $X$ we can create a uniformity on $X$ by taking the supersets
  of $\bigcup \{A\times A: A\in P \}$ as $P$ ranges over the uniform covers. The next definition
  specifies the operation creating entourages from uniform covers. \<close>

definition
  "UniformityFromUniCov(X,\<Theta>) \<equiv> Supersets(X\<times>X,{\<Union>{U\<times>U. U\<in>P}. P\<in>\<Theta>})"

text\<open>For any member $P$ of a cover $\Theta$ the set $\bigcup \{U\times U : U\in P\}$ 
  is a member of \<open>UniformityFromUniCov(X,\<Theta>)\<close>. \<close>

lemma basic_unif: assumes "\<Theta> \<subseteq> Covers(X)" "P\<in>\<Theta>"
  shows "\<Union>{U\<times>U. U\<in>P} \<in> UniformityFromUniCov(X,\<Theta>)"
  using assms unfolding UniformityFromUniCov_def Supersets_def Covers_def
  by blast

text\<open>If $\Theta$ is a family of uniform covers of $X$ then 
  \<open>UniformityFromUniCov(X,\<Theta>)\<close> is a uniformity on $X$ \<close> 

theorem uniformity_from_unicov: 
  assumes "\<Theta> {are uniform covers of} X" "X\<noteq>0"
  shows "UniformityFromUniCov(X,\<Theta>) {is a uniformity on} X"
proof -
  let ?\<Phi> = "UniformityFromUniCov(X,\<Theta>)"
  have "?\<Phi> {is a filter on} (X\<times>X)"
  proof -
    have "0 \<notin> ?\<Phi>"
    proof -
      { assume "0 \<in> ?\<Phi>"
        then obtain P where "P\<in>\<Theta>" and "0 = \<Union>{U\<times>U. U\<in>P}"
          unfolding UniformityFromUniCov_def Supersets_def by auto
        hence "\<Union>P = 0" by auto
        with assms \<open>P\<in>\<Theta>\<close> have False unfolding AreUniformCovers_def Covers_def
          by auto
      } thus ?thesis by auto
    qed
    moreover have "X\<times>X \<in> ?\<Phi>"
    proof -
      from assms have "X\<times>X \<in> {\<Union>{U\<times>U. U\<in>P}. P\<in>\<Theta>}" 
        using unicov_contains_triv unfolding AreUniformCovers_def 
        by auto
      then show ?thesis unfolding Supersets_def UniformityFromUniCov_def 
        by blast
    qed
    moreover have "?\<Phi> \<subseteq> Pow(X\<times>X)" 
      unfolding UniformityFromUniCov_def Supersets_def by auto
    moreover have "\<forall>A\<in>?\<Phi>.\<forall>B\<in>?\<Phi>. A\<inter>B \<in> ?\<Phi>"
    proof -
      { fix A B assume "A\<in>?\<Phi>" "B\<in>?\<Phi>"
        then have "A\<inter>B \<subseteq> X\<times>X" unfolding UniformityFromUniCov_def Supersets_def
          by auto
        from \<open>A\<in>?\<Phi>\<close> \<open>B\<in>?\<Phi>\<close> obtain P\<^sub>A P\<^sub>B where 
          "P\<^sub>A\<in>\<Theta>" "P\<^sub>B\<in>\<Theta>" and I:"\<Union>{U\<times>U. U\<in>P\<^sub>A} \<subseteq> A"  "\<Union>{U\<times>U. U\<in>P\<^sub>B} \<subseteq> B" 
          unfolding UniformityFromUniCov_def Supersets_def by auto
        from assms(1) \<open>P\<^sub>A\<in>\<Theta>\<close> \<open>P\<^sub>B\<in>\<Theta>\<close> obtain P 
          where "P\<in>\<Theta>" and "P<\<^sup>*P\<^sub>A" and "P<\<^sup>*P\<^sub>B"
          unfolding AreUniformCovers_def by blast
        have "\<Union>{U\<times>U. U\<in>P} \<subseteq> A\<inter>B"
        proof -
          { fix U assume "U\<in>P" 
            with \<open>P<\<^sup>*P\<^sub>A\<close>  \<open>P<\<^sup>*P\<^sub>B\<close> I have "U\<times>U \<subseteq> A" and "U\<times>U \<subseteq> B" 
              using star_ref_mem by auto
          } thus ?thesis by blast
        qed
        with \<open>A\<inter>B \<subseteq> X\<times>X\<close> \<open>P\<in>\<Theta>\<close> have "A\<inter>B \<in> ?\<Phi>" 
          unfolding Supersets_def UniformityFromUniCov_def by auto
      } thus ?thesis by auto
    qed
    moreover have 
      "\<forall>B\<in>?\<Phi>.\<forall>C\<in>Pow(X\<times>X). B\<subseteq>C \<longrightarrow> C\<in>?\<Phi>"
    proof -
      { fix B C assume "B\<in>?\<Phi>" "C\<in>Pow(X\<times>X)" "B\<subseteq>C"
        from \<open>B\<in>?\<Phi>\<close> obtain P\<^sub>B where  "\<Union>{U\<times>U. U\<in>P\<^sub>B} \<subseteq> B" "P\<^sub>B\<in>\<Theta>"
          unfolding UniformityFromUniCov_def Supersets_def by auto
        with \<open>C\<in>Pow(X\<times>X)\<close> \<open>B\<subseteq>C\<close> have "C\<in>?\<Phi>"
          unfolding UniformityFromUniCov_def Supersets_def by blast
      } thus ?thesis by auto
    qed
    ultimately show ?thesis unfolding IsFilter_def by simp
  qed
  moreover have "\<forall>A\<in>?\<Phi>. id(X) \<subseteq> A \<and> (\<exists>B\<in>?\<Phi>. B O B \<subseteq> A) \<and> converse(A) \<in> ?\<Phi>"
  proof
    fix A assume "A\<in>?\<Phi>"
    then obtain P where "\<Union>{U\<times>U. U\<in>P} \<subseteq> A" "P\<in>\<Theta>" 
      unfolding UniformityFromUniCov_def Supersets_def by auto
    have "id(X)\<subseteq>A"
    proof -
      from assms(1) \<open>P\<in>\<Theta>\<close> have "\<Union>P = X" unfolding AreUniformCovers_def Covers_def
        by auto
      with \<open>\<Union>{U\<times>U. U\<in>P} \<subseteq> A\<close> show ?thesis by auto
    qed
    moreover have "\<exists>B\<in>?\<Phi>. B O B \<subseteq> A"
    proof -
      from assms(1) \<open>P\<in>\<Theta>\<close> have "\<Union>{U\<times>U. U\<in>P} \<in> ?\<Phi>" 
        unfolding AreUniformCovers_def Covers_def UniformityFromUniCov_def Supersets_def
        by auto
      from assms(1) \<open>P\<in>\<Theta>\<close> obtain Q where "Q\<in>\<Theta>" and  "Q <\<^sup>* P" using unicov_has_star_ref
        by blast
      let ?B = "\<Union>{U\<times>U. U\<in>Q}"
      from assms(1) \<open>Q\<in>\<Theta>\<close> have "?B \<in> ?\<Phi>" 
        unfolding AreUniformCovers_def Covers_def UniformityFromUniCov_def Supersets_def
        by auto
      moreover have "?B O ?B \<subseteq> A"
      proof -
        have II: "?B O ?B = \<Union>{U\<times>Star(U,Q). U\<in>Q}" using rel_square_starr 
          by simp
        have "\<forall>U\<in>Q. \<exists>V\<in>P. U\<times>Star(U,Q) \<subseteq> V\<times>V"
        proof
          fix U assume "U\<in>Q"
          with \<open>Q <\<^sup>* P\<close> obtain V where "V\<in>P" and "Star(U,Q) \<subseteq> V"
            unfolding IsStarRefinement_def by blast
          with \<open>U\<in>Q\<close> have "V\<in>P" and "U\<times>Star(U,Q) \<subseteq> V\<times>V" using element_subset_star
            by auto
          thus "\<exists>V\<in>P. U\<times>Star(U,Q) \<subseteq> V\<times>V" by auto
        qed
        hence "\<Union>{U\<times>Star(U,Q). U\<in>Q} \<subseteq> \<Union>{V\<times>V. V\<in>P}" by blast 
        with \<open>\<Union>{V\<times>V. V\<in>P} \<subseteq> A\<close> have "\<Union>{U\<times>Star(U,Q). U\<in>Q} \<subseteq> A" by blast
        with II show ?thesis by simp
      qed
      ultimately show ?thesis by auto
    qed
    moreover from \<open>A\<in>?\<Phi>\<close> \<open>P\<in>\<Theta>\<close> \<open>\<Union>{U\<times>U. U\<in>P} \<subseteq> A\<close> have "converse(A) \<in> ?\<Phi>"
      unfolding AreUniformCovers_def UniformityFromUniCov_def Supersets_def 
      by auto
    ultimately show "id(X) \<subseteq> A \<and> (\<exists>B\<in>?\<Phi>. B O B \<subseteq> A) \<and> converse(A) \<in> ?\<Phi>" 
      by simp
  qed
  ultimately show "?\<Phi>  {is a uniformity on} X" unfolding IsUniformity_def 
    by simp
qed

text\<open>Given a uniformity $\Phi$ on $X$ we can create a family of uniform covers by taking the 
  collection of covers $P$ for which there exist an entourage $U\in \Phi$ such that 
  for each $x\in X$, there is an $A\in P$ such that $U(\{ x\}) \subseteq A$. The next definition
  specifies the operation of creating a family of uniform covers from a uniformity. \<close>

definition
  "UniCovFromUniformity(X,\<Phi>) \<equiv> {P\<in>Covers(X). \<exists>U\<in>\<Phi>.\<forall>x\<in>X.\<exists>A\<in>P. U``({x}) \<subseteq> A}"

text\<open>When we convert the quantifiers into unions and intersections in the definition
  of \<open>UniCovFromUniformity\<close> we get an alternative definition of the operation
  that creates a family of uniform covers from a uniformity. Just a curiosity, not used anywhere.\<close>

lemma UniCovFromUniformityDef: assumes "X\<noteq>0"
  shows "UniCovFromUniformity(X,\<Phi>) = (\<Union>U\<in>\<Phi>.\<Inter>x\<in>X. {P\<in>Covers(X). \<exists>A\<in>P. U``({x}) \<subseteq> A})"
proof -
  have "{P\<in>Covers(X). \<exists>U\<in>\<Phi>.\<forall>x\<in>X.\<exists>A\<in>P. U``({x}) \<subseteq> A} = 
  (\<Union>U\<in>\<Phi>.\<Inter>x\<in>X. {P\<in>Covers(X). \<exists>A\<in>P. U``({x}) \<subseteq> A})"
  proof
  { fix P assume "P\<in>{P\<in>Covers(X). \<exists>U\<in>\<Phi>.\<forall>x\<in>X.\<exists>A\<in>P. U``({x}) \<subseteq> A}"
    then have "P\<in>Covers(X)" and "\<exists>U\<in>\<Phi>.\<forall>x\<in>X.\<exists>A\<in>P. U``({x}) \<subseteq> A" by auto
    then obtain U where "U\<in>\<Phi>" and "\<forall>x\<in>X.\<exists>A\<in>P. U``({x}) \<subseteq> A" by auto
    with assms \<open>P\<in>Covers(X)\<close> have "P \<in> (\<Inter>x\<in>X. {P\<in>Covers(X). \<exists>A\<in>P. U``({x}) \<subseteq> A})" 
      by auto
    with \<open>U\<in>\<Phi>\<close>  have "P\<in>(\<Union>U\<in>\<Phi>.\<Inter>x\<in>X. {P\<in>Covers(X). \<exists>A\<in>P. U``({x}) \<subseteq> A})" 
      by blast
  } then show 
    "{P\<in>Covers(X). \<exists>U\<in>\<Phi>.\<forall>x\<in>X.\<exists>A\<in>P. U``({x}) \<subseteq> A} \<subseteq> 
    (\<Union>U\<in>\<Phi>.\<Inter>x\<in>X. {P\<in>Covers(X). \<exists>A\<in>P. U``({x}) \<subseteq> A})"
    using subset_iff by simp
  { fix P assume "P\<in>(\<Union>U\<in>\<Phi>.\<Inter>x\<in>X. {P\<in>Covers(X). \<exists>A\<in>P. U``({x}) \<subseteq> A})"
    then obtain U where "U\<in>\<Phi>" "P \<in> (\<Inter>x\<in>X. {P\<in>Covers(X). \<exists>A\<in>P. U``({x}) \<subseteq> A})" 
      by auto
    with assms have "P\<in>Covers(X)" and "\<forall>x\<in>X.\<exists>A\<in>P. U``({x}) \<subseteq> A" by auto
    with \<open>U\<in>\<Phi>\<close> have "P\<in>{P\<in>Covers(X). \<exists>U\<in>\<Phi>.\<forall>x\<in>X.\<exists>A\<in>P. U``({x}) \<subseteq> A}"
      by auto
  } then show "(\<Union>U\<in>\<Phi>.\<Inter>x\<in>X. {P\<in>Covers(X). \<exists>A\<in>P. U``({x}) \<subseteq> A}) \<subseteq> 
    {P\<in>Covers(X). \<exists>U\<in>\<Phi>.\<forall>x\<in>X.\<exists>A\<in>P. U``({x}) \<subseteq> A}" by auto
  qed
  then show ?thesis unfolding UniCovFromUniformity_def by simp
qed

text\<open>If $\Phi$ is a (diagonal) uniformity on $X$, then covers of the form 
  $\{ W\{ x\} : x\in X\}$ are members of \<open>UniCovFromUniformity(X,\<Phi>)\<close>. \<close>

lemma cover_image: 
  assumes "\<Phi> {is a uniformity on} X" "W\<in>\<Phi>" 
  shows "{W``{x}. x\<in>X} \<in> UniCovFromUniformity(X,\<Phi>)"
proof -
  let ?P = "{W``{x}. x\<in>X}"
  have "?P \<in> Covers(X)"
  proof -
    from assms have "W \<subseteq> X\<times>X" and "?P \<in> Pow(Pow(X))" 
      using entourage_props(1) by auto
    moreover have "\<Union>?P = X"
    proof
      from \<open>W \<subseteq> X\<times>X\<close> show "\<Union>?P \<subseteq> X" by auto
      from assms show "X \<subseteq> \<Union>?P" using neigh_not_empty(2) by auto
    qed
    ultimately show ?thesis unfolding Covers_def by simp
  qed
  moreover from assms(2) have "\<exists>W\<in>\<Phi>. \<forall>x\<in>X. \<exists>A\<in>?P. W``{x} \<subseteq> A" 
    by auto
  ultimately show ?thesis unfolding UniCovFromUniformity_def
    by simp
qed

text\<open>If $\Phi$ is a (diagonal) uniformity on $X$, then every two elements 
  of  \<open>UniCovFromUniformity(X,\<Phi>)\<close> have a common barycentric refinement.\<close>

lemma common_bar_refinemnt: 
  assumes 
    "\<Phi> {is a uniformity on} X" 
    "\<Theta> = UniCovFromUniformity(X,\<Phi>)"
    "\<C>\<in>\<Theta>" "\<D>\<in>\<Theta>"
  shows "\<exists>\<R>\<in>\<Theta>.(\<R> <\<^sup>B \<C>) \<and> (\<R> <\<^sup>B \<D>)"
proof -
  from assms(2,3) obtain U where "U\<in>\<Phi>" and I: "\<forall>x\<in>X.\<exists>C\<in>\<C>. U``{x} \<subseteq> C"
    unfolding UniCovFromUniformity_def by auto
  from assms(2,4) obtain V where "V\<in>\<Phi>" and II: "\<forall>x\<in>X.\<exists>D\<in>\<D>. V``{x} \<subseteq> D"
    unfolding UniCovFromUniformity_def by auto    
  from assms(1) \<open>U\<in>\<Phi>\<close> \<open>V\<in>\<Phi>\<close> have "U\<inter>V \<in> \<Phi>"  
    unfolding IsUniformity_def IsFilter_def by auto
  with assms(1) obtain W where "W\<in>\<Phi>" and "W O W \<subseteq> U\<inter>V" and "W=converse(W)"
    using half_size_symm by blast
  from assms(1) \<open>W\<in>\<Phi>\<close> have "domain(W) \<subseteq> X" 
    unfolding IsUniformity_def IsFilter_def by auto
  let ?P = "{W``{t}. t\<in>X}"
  have "?P\<in>\<Theta>" "?P <\<^sup>B \<C>" "?P <\<^sup>B \<D>"
  proof -
    from assms(1,2) \<open>W\<in>\<Phi>\<close> show "?P\<in>\<Theta>" using cover_image by simp
    with assms(2) have "\<Union>?P = X" unfolding UniCovFromUniformity_def Covers_def
      by simp
    { fix x assume "x\<in>X"
      from \<open>W=converse(W)\<close> \<open>domain(W) \<subseteq> X\<close> \<open>W O W \<subseteq> U\<inter>V\<close> 
      have "Star({x},?P) \<subseteq> U``{x}" and "Star({x},?P) \<subseteq> V``{x}"
        using rel_sq_image by auto
      from \<open>x\<in>X\<close> I obtain C where "C\<in>\<C>" and "U``{x} \<subseteq> C"
        by auto
      with \<open>Star({x},?P) \<subseteq> U``{x}\<close> \<open>C\<in>\<C>\<close> have "\<exists>C\<in>\<C>. Star({x},?P) \<subseteq> C"
        by auto
      moreover 
      from \<open>x\<in>X\<close> II obtain D where "D\<in>\<D>" and "V``{x} \<subseteq> D"
        by auto
      with \<open>Star({x},?P) \<subseteq> V``{x}\<close> \<open>D\<in>\<D>\<close> have "\<exists>D\<in>\<D>. Star({x},?P) \<subseteq> D"
        by auto
      ultimately have "\<exists>C\<in>\<C>. Star({x},?P) \<subseteq> C" and "\<exists>D\<in>\<D>. Star({x},?P) \<subseteq> D"
        by auto
    } hence "\<forall>x\<in>X. \<exists>C\<in>\<C>. Star({x},?P) \<subseteq> C" and "\<forall>x\<in>X.\<exists>D\<in>\<D>. Star({x},?P) \<subseteq> D"
      by auto 
    with \<open>\<Union>?P = X\<close> show "?P <\<^sup>B \<C>" and "?P <\<^sup>B \<D>"
      unfolding IsBarycentricRefinement_def by auto
  qed
  thus ?thesis by auto
qed

text\<open>If $\Phi$ is a (diagonal) uniformity on $X$, then every element
  of  \<open>UniCovFromUniformity(X,\<Phi>)\<close> has a barycentric refinement there.\<close>

corollary bar_refinement_ex:
  assumes "\<Phi> {is a uniformity on} X" "\<Theta> = UniCovFromUniformity(X,\<Phi>)" "\<C> \<in> \<Theta>"
  shows "\<exists>\<R>\<in>\<Theta>. (\<R> <\<^sup>B \<C>)"
  using assms common_bar_refinemnt by blast


text\<open> If $\Phi$ is a (diagonal) uniformity on $X$, then \<open>UniCovFromUniformity(X,\<Phi>)\<close> is 
  a family of uniform covers.\<close>

theorem unicov_from_uniformity: assumes "\<Phi> {is a uniformity on} X" and "X\<noteq>0" 
  shows "UniCovFromUniformity(X,\<Phi>) {are uniform covers of} X"
proof -
  let ?\<Theta> = "UniCovFromUniformity(X,\<Phi>)"
  from assms(1) have "?\<Theta> \<subseteq> Covers(X)" unfolding UniCovFromUniformity_def 
    by auto
  moreover 
  from assms(1) have "{X} \<in> ?\<Theta>"
    unfolding Covers_def IsUniformity_def IsFilter_def UniCovFromUniformity_def
    by auto
  hence "?\<Theta> \<noteq> 0" by auto
  moreover have "\<forall>\<R>\<in>?\<Theta>.\<forall>\<C>\<in>Covers(X). ((\<R> <\<^sup>* \<C>) \<longrightarrow> \<C>\<in>?\<Theta>)"
  proof -
    { fix \<R> \<C> assume "\<R>\<in>?\<Theta>" "\<C>\<in>Covers(X)" "\<R> <\<^sup>* \<C>"
      have "\<C>\<in>?\<Theta>"
      proof -
        from \<open>\<R>\<in>?\<Theta>\<close> obtain U where "U\<in>\<Phi>" and I: "\<forall>x\<in>X.\<exists>R\<in>\<R>. U``({x}) \<subseteq> R"
          unfolding UniCovFromUniformity_def by auto
        { fix x assume "x\<in>X" 
          with I obtain R where "R\<in>\<R>" and "U``({x}) \<subseteq> R" by auto
          from \<open>R\<in>\<R>\<close> \<open>\<R> <\<^sup>* \<C>\<close> obtain C where "C\<in>\<C>" and "Star(R,\<R>) \<subseteq> C"
            unfolding IsStarRefinement_def by auto
          with \<open>U``({x}) \<subseteq> R\<close> \<open>R\<in>\<R>\<close> have "U``({x}) \<subseteq> C" 
            using element_subset_star by blast
          with \<open>C\<in>\<C>\<close> have "\<exists>C\<in>\<C>. U``({x}) \<subseteq> C" by auto
        } hence "\<forall>x\<in>X.\<exists>C\<in>\<C>. U``({x}) \<subseteq> C" by auto
        with \<open>U\<in>\<Phi>\<close> \<open>\<C>\<in>Covers(X)\<close> show ?thesis unfolding UniCovFromUniformity_def
          by auto
      qed
    } thus ?thesis by auto
  qed
  moreover have "\<forall>\<C>\<in>?\<Theta>.\<forall>\<D>\<in>?\<Theta>.\<exists>\<R>\<in>?\<Theta>.(\<R> <\<^sup>* \<C>) \<and> (\<R> <\<^sup>* \<D>)"
  proof -
    { fix \<C> \<D> assume "\<C>\<in>?\<Theta>" "\<D>\<in>?\<Theta>" 
      with assms(1) obtain P where "P\<in>?\<Theta>" and "P <\<^sup>B \<C>" "P <\<^sup>B \<D>"
        using common_bar_refinemnt by blast
      from assms(1) \<open>P\<in>?\<Theta>\<close> obtain \<R> where "\<R>\<in>?\<Theta>" and "\<R> <\<^sup>B P"
        using bar_refinement_ex by blast
      from \<open>\<R>\<in>?\<Theta>\<close> \<open>P\<in>?\<Theta>\<close> \<open>\<C>\<in>?\<Theta>\<close> \<open>\<D>\<in>?\<Theta>\<close> have 
        "P \<in> Covers(X)" "\<R> \<in> Covers(X)" "\<C> \<in> Covers(X)" "\<D> \<in> Covers(X)"
        unfolding UniCovFromUniformity_def by auto
      with assms(2) \<open>\<R> <\<^sup>B P\<close> \<open>P <\<^sup>B \<C>\<close> \<open>P <\<^sup>B \<D>\<close> have "\<R> <\<^sup>* \<C>" and "\<R> <\<^sup>* \<D>" 
        using bary_bary_star by auto
      with \<open>\<R>\<in>?\<Theta>\<close> have "\<exists>\<R>\<in>?\<Theta>.(\<R> <\<^sup>* \<C>) \<and> (\<R> <\<^sup>* \<D>)" by auto
    } thus ?thesis by simp
  qed
  ultimately show ?thesis unfolding AreUniformCovers_def by simp
qed

text\<open> The \<open>UniCovFromUniformity\<close> operation is the inverse of \<open>UniformityFromUniCov\<close>. \<close>

theorem unicov_from_unif_inv: assumes "\<Theta> {are uniform covers of} X" "X\<noteq>0"
  shows "UniCovFromUniformity(X,UniformityFromUniCov(X,\<Theta>)) = \<Theta>"
proof
  let ?\<Phi> = "UniformityFromUniCov(X,\<Theta>)"
  let ?L = "UniCovFromUniformity(X,?\<Phi>)"
  from assms have I: "?\<Phi> {is a uniformity on} X" 
    using uniformity_from_unicov by simp
  with assms(2) have II: "?L {are uniform covers of} X" 
    using unicov_from_uniformity by simp
  { fix P assume "P\<in>?L"
    with I obtain Q where "Q\<in>?L" and "Q <\<^sup>B P" 
      using bar_refinement_ex by blast
    from \<open>Q\<in>?L\<close> obtain U where "U\<in>?\<Phi>" and III:"\<forall>x\<in>X.\<exists>A\<in>Q. U``{x} \<subseteq> A"
      unfolding UniCovFromUniformity_def by auto
    from \<open>U\<in>?\<Phi>\<close> have "U \<in> Supersets(X\<times>X,{\<Union>{U\<times>U. U\<in>P}. P\<in>\<Theta>})"
      unfolding UniformityFromUniCov_def by simp
    then obtain B where "B\<subseteq>X\<times>X" "B\<subseteq>U" and "\<exists>C\<in>{\<Union>{U\<times>U. U\<in>P}. P\<in>\<Theta>}. C\<subseteq>B" 
      unfolding Supersets_def by auto
    then obtain C where "C \<in> {\<Union>{U\<times>U. U\<in>P}. P\<in>\<Theta>}" and "C\<subseteq>B" by auto
    then obtain R where "R\<in>\<Theta>" and "C = \<Union>{V\<times>V. V\<in>R}" by auto
    with \<open>C\<subseteq>B\<close> \<open>B\<subseteq>U\<close> have "\<Union>{V\<times>V. V\<in>R} \<subseteq> U" by auto
    from assms(1) II \<open>P\<in>?L\<close> \<open>Q\<in>?L\<close> \<open>R\<in>\<Theta>\<close> have
      IV: "P\<in>Covers(X)" "Q\<in>Covers(X)" "R\<in>Covers(X)"
      unfolding AreUniformCovers_def by auto
    have "R <\<^sup>B Q"
    proof -
      { fix x assume "x\<in>X"
        with III obtain A where "A\<in>Q" and "U``{x} \<subseteq> A" by auto
        with \<open>\<Union>{V\<times>V. V\<in>R} \<subseteq> U\<close> have "(\<Union>{V\<times>V. V\<in>R})``{x} \<subseteq> A"
          by auto
        with \<open>A\<in>Q\<close> have "\<exists>A\<in>Q. Star({x},R) \<subseteq> A" using star_singleton by auto
      } then have "\<forall>x\<in>X. \<exists>A\<in>Q. Star({x},R) \<subseteq> A" by simp
      moreover from \<open>R\<in>Covers(X)\<close> have "\<Union>R = X" unfolding Covers_def
        by simp
      ultimately show ?thesis unfolding IsBarycentricRefinement_def
        by simp
    qed
    with assms(2) \<open>Q <\<^sup>B P\<close> IV have "R <\<^sup>* P" using bary_bary_star by simp
    with assms(1) \<open>R\<in>\<Theta>\<close> \<open>P\<in>Covers(X)\<close> have "P\<in>\<Theta>" 
      unfolding AreUniformCovers_def by simp
  } thus "?L\<subseteq>\<Theta>" by auto
  { fix P assume "P\<in>\<Theta>"
    with assms(1) have "P \<in> Covers(X)" 
      unfolding AreUniformCovers_def by auto
    from assms(1) \<open>P\<in>\<Theta>\<close> obtain Q where "Q \<in> \<Theta>" and "Q <\<^sup>B P" 
      using unicov_has_bar_ref by blast
    let ?A = "\<Union>{V\<times>V. V\<in>Q}"
    have "?A \<in> ?\<Phi>" 
    proof -
      from assms(1) \<open>Q\<in>\<Theta>\<close> have "?A \<subseteq> X\<times>X" and "?A \<in> {\<Union>{V\<times>V. V\<in>Q}. Q\<in>\<Theta>}"
        unfolding AreUniformCovers_def Covers_def by auto 
      then show ?thesis 
        using superset_gen unfolding UniformityFromUniCov_def 
        by auto
    qed
    with I obtain B where "B\<in>?\<Phi>" "B O B \<subseteq> ?A" and "B=converse(B)"
      using half_size_symm by blast
    let ?R = "{B``{x}. x\<in>X}"
    from I II \<open>B\<in>?\<Phi>\<close> have "?R\<in>?L" and "\<Union>?R =X"
      using cover_image unfolding UniCovFromUniformity_def Covers_def
      by auto
    have "?R <\<^sup>B P"
    proof -
      { fix x assume "x\<in>X"
        from assms(1) \<open>Q \<in> \<Theta>\<close> have "\<Union>Q = X" 
          unfolding AreUniformCovers_def Covers_def by auto
        with \<open>Q <\<^sup>B P\<close> \<open>x\<in>X\<close> obtain C where "C\<in>P" and "Star({x},Q) \<subseteq> C"
          unfolding IsBarycentricRefinement_def by auto
        from \<open>B=converse(B)\<close> I \<open>B\<in>?\<Phi>\<close> have "Star({x},?R) = (B O B)``{x}"
          using  uni_domain rel_sq_image by auto
        moreover from  \<open>(B O B) \<subseteq> ?A\<close> have "(B O B)``{x} \<subseteq> ?A``{x}" by blast
        moreover have "?A``{x} = Star({x},Q)" using star_singleton by simp
        ultimately have "Star({x},?R) \<subseteq> Star({x},Q)" by auto
        with \<open>Star({x},Q) \<subseteq> C\<close> \<open>C\<in>P\<close> have "\<exists>C\<in>P. Star({x},?R) \<subseteq> C"
          by auto
      } with \<open>\<Union>?R = X\<close> show ?thesis unfolding IsBarycentricRefinement_def
        by auto
    qed
    with assms(2) II \<open>P \<in> Covers(X)\<close> \<open>?R\<in>?L\<close> \<open>?R <\<^sup>B P\<close> have "P\<in>?L" 
       using unicov_bary_cov by simp
  } thus "\<Theta>\<subseteq>?L" by auto
qed

text\<open>The \<open>UniformityFromUniCov\<close> operation is the inverse of \<open>UniCovFromUniformity\<close>. \<close>

theorem unif_from_unicov_inv: assumes "\<Phi> {is a uniformity on} X" "X\<noteq>0"
  shows "UniformityFromUniCov(X,UniCovFromUniformity(X,\<Phi>)) = \<Phi>"
proof 
  let ?\<Theta> = "UniCovFromUniformity(X,\<Phi>)"
  let ?L = "UniformityFromUniCov(X,?\<Theta>)"
  from assms have I: "?\<Theta> {are uniform covers of} X"
    using unicov_from_uniformity by simp
  with assms have II: "?L {is a uniformity on} X" 
    using uniformity_from_unicov by simp
  { fix A assume "A\<in>\<Phi>"
    with assms(1) obtain B where "B\<in>\<Phi>" "B O B \<subseteq> A" and "B = converse(B)"
      using half_size_symm by blast
    from assms(1) \<open>A\<in>\<Phi>\<close> have "A \<subseteq> X\<times>X" using uni_domain(1)
      by simp
    let ?P = "{B``{x}. x\<in>X}"
    from assms(1) \<open>B\<in>\<Phi>\<close> have "?P\<in>?\<Theta>" using cover_image
      by simp
    let ?C = "\<Union>{U\<times>U. U\<in>?P}"
    from I \<open>?P\<in>?\<Theta>\<close> have "?C\<in>?L" 
      unfolding AreUniformCovers_def using basic_unif by blast  
    from assms(1) \<open>B\<in>\<Phi>\<close> \<open>B = converse(B)\<close> \<open>B O B \<subseteq> A\<close> have "?C \<subseteq> A" 
      using uni_domain(2) symm_sq_prod_image by simp
    with II \<open>A \<subseteq> X\<times>X\<close> \<open>?C\<in>?L\<close> have "A\<in>?L"
      unfolding IsUniformity_def IsFilter_def by simp
  } thus "\<Phi>\<subseteq>?L" by auto
  { fix A assume "A\<in>?L" 
    with II have "A \<subseteq> X\<times>X" using entourage_props(1) by simp
    from \<open>A\<in>?L\<close> obtain P where "P\<in>?\<Theta>" and "\<Union>{U\<times>U. U\<in>P} \<subseteq> A"
      unfolding UniformityFromUniCov_def Supersets_def by blast
    from \<open>P\<in>?\<Theta>\<close> obtain B where "B\<in>\<Phi>" and III: "\<forall>x\<in>X. \<exists>V\<in>P. B``{x} \<subseteq> V"
      unfolding UniCovFromUniformity_def by auto
    have "B\<subseteq>A"
    proof -
      from assms(1) \<open>B\<in>\<Phi>\<close> have "B \<subseteq> \<Union>{B``{x}\<times>B``{x}. x\<in>X}"
        using entourage_props(1,2) refl_union_singl_image by simp
      moreover have "\<Union>{B``{x}\<times>B``{x}. x\<in>X} \<subseteq> A"
      proof -
        { fix x assume "x\<in>X"
          with III obtain V where "V\<in>P" and "B``{x} \<subseteq> V" by auto
          hence "B``{x}\<times>B``{x} \<subseteq> \<Union>{U\<times>U. U\<in>P}" by auto
        } hence "\<Union>{B``{x}\<times>B``{x}. x\<in>X} \<subseteq> \<Union>{U\<times>U. U\<in>P}" by blast
        with \<open>\<Union>{U\<times>U. U\<in>P} \<subseteq> A\<close> show ?thesis by blast
      qed
      ultimately show ?thesis by auto
    qed
    with assms(1) \<open>B\<in>\<Phi>\<close> \<open>A \<subseteq> X\<times>X\<close> have "A\<in>\<Phi>"
      unfolding IsUniformity_def IsFilter_def by simp
  } thus "?L\<subseteq>\<Phi>" by auto
qed

end

 
