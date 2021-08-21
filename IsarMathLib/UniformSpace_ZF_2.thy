section \<open> Uniformizability \<close>

theory UniformSpace_ZF_2 imports UniformSpace_ZF_1 Real_ZF_2
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
  The members of such family are called a "uniform cover", but one has to remember that this notion 
  has meaning only in the contexts a the whole family of uniform covers. Looking at a specific cover
  in isolation we can not say whether it is a uniform cover or not.  \<close>

text\<open>A cover of a set $X$ is a collection subsets of $X$ whose union is equal to $X$. 
  The set of all covers of $X$ is called \<open>Covers(X)\<close>. \<close>

definition 
  "Covers(X) \<equiv> {A \<in> Pow(Pow(X)). \<Union>A = X}" 

text\<open> A "star" of $R$ with respect to $\mathcal{R}$ is the union of all $S\in \mathcal{R}$ that
  intersect $R$. \<close>

definition
  "Star(R,\<R>) \<equiv> \<Union>{S\<in>\<R>. S\<inter>R \<noteq> 0}"

text\<open>An element of $\mathcal{R}$ is a subset of its star with respect to $\mathcal{R}$. \<close>

lemma element_subset_star: assumes "R\<in>\<R>" shows "R \<subseteq> Star(R,\<R>)"
  using assms unfolding Star_def by auto

text\<open> A cover $\mathcal{R}$ is a "star refinement" of a cover $\mathcal{C}$  iff 
  for each $R\in \mathcal{R}$ there is a $C\in \mathcal{C}$ such that the star of $R$ with 
  respect to $\mathcal{R}$ is contained in $C$. \<close>

definition
  IsStarRefinement ("_ <\<^sup>* _" 90)
  where "\<R> <\<^sup>* \<C> \<equiv> \<forall>R\<in>\<R>.\<exists>C\<in>\<C>. Star(R,\<R>) \<subseteq> C"
  
text\<open>The notion of filter defined in \<open>Topology_ZF_4\<close> is not sufficiently general to use it to 
  define uniform covers, so we write the conditions directly. In this case a collection $\Theta$ of
  covers of $X$ is a family of uniform covers if 
  
  a) the trivial cover $\{ X\}$ belongs to $\Theta$, 
  
  b) if $\mathcal{R} \in \Theta$ and $\mathcal{C}$ is any cover of $X$ such that $\mathcal{R}$ is 
  a star refinement of $\mathcal{C}$, then $\mathcal{C} \in \Theta$.
  
  c) For any $\mathcal{C},\mathcal{D} \in \Theta$ there is some $\mathcal{R}\in\Theta$ 
  such that $\mathcal{R}$ is a star refinement of $\mathcal{C}$ and $\mathcal{R}$ is a 
  star refinement of $\mathcal{D}$. 
  
  The first condition can be (probably) replaced by the requirement that $\Theta$ is not empty.\<close>

definition
  AreUniformCovers ("_ {are uniform covers of} _" 90)
  where "\<Theta> {are uniform covers of} X \<equiv>  (\<Theta> \<subseteq> Covers(X)) \<and> ({X}\<in>\<Theta>) \<and> 
  (\<forall>\<R>\<in>\<Theta>.\<forall>\<C>\<in>Covers(X). ((\<R> <\<^sup>* \<C>) \<longrightarrow> \<C>\<in>\<Theta>)) \<and>
  (\<forall>\<C>\<in>\<Theta>.\<forall>\<D>\<in>\<Theta>.\<exists>\<R>\<in>\<Theta>.(\<R> <\<^sup>* \<C>) \<and> (\<R> <\<^sup>* \<D>))"

text\<open>If $\Theta$ are uniform covers of $X$ then we can recover $X$ from $\Theta$ by taking 
  $\bigcup\bigcup \Theta$. \<close>

lemma space_from_unicov: assumes "\<Theta> {are uniform covers of} X" shows "X = \<Union>\<Union>\<Theta>"
proof
  from assms show "X \<subseteq> \<Union>\<Union>\<Theta>" unfolding AreUniformCovers_def by auto
  from assms show "\<Union>\<Union>\<Theta> \<subseteq> X" unfolding AreUniformCovers_def Covers_def by auto
qed

text\<open> Every uniform cover has a star refinement. \<close>

lemma unicov_has_star_ref: assumes "\<Theta> {are uniform covers of} X" and "P\<in>\<Theta>"
  shows "\<exists>Q\<in>\<Theta>. (Q <\<^sup>* P)"
  using assms unfolding AreUniformCovers_def by blast

text\<open> A technical lemma to simplify proof of the \<open> uniformity_from_unicov \<close> theorem. \<close>

lemma star_ref_mem: assumes "U\<in>P" "P<\<^sup>*Q" "\<Union>{W\<times>W. W\<in>Q} \<subseteq> A"
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

text\<open> A formula similar to \<open>rel_square_starr\<close> but with \<open>Star\<close> on the left side of the Cartesian 
  product: \<close>

lemma rel_square_starl: shows 
  "(\<Union>{U\<times>U. U\<in>P}) O (\<Union>{U\<times>U. U\<in>P}) = \<Union>{Star(U,P)\<times>U. U\<in>P}"
  unfolding Star_def by blast

text\<open> Given a family of uniform covers of $X$ we can create a uniformity on $X$ by taking the supersets
  of $\bigcup \{A\times A: A\in P \}$ as $P$ ranges over the uniform covers. The next definition
  specifies the operation creating entourages from unform covers. \<close>

definition
  "UniformityFromUniCov(X,\<Theta>) \<equiv> Supersets(X\<times>X,{\<Union>{U\<times>U. U\<in>P}. P\<in>\<Theta>})"

text\<open>If $\Theta$ is a family of uniform covers of $X$ then 
  \<open>UniformityFromUniCov(X,\<Theta>)\<close> is a unformity on $X$ \<close> 

theorem uniformity_from_unicov: assumes "X\<noteq>0" "\<Theta> {are uniform covers of} X"
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
      from assms have "X\<times>X \<in> {\<Union>{U\<times>U. U\<in>P}. P\<in>\<Theta>}" unfolding AreUniformCovers_def 
        by auto
      then show ?thesis unfolding Supersets_def UniformityFromUniCov_def by blast
    qed
    moreover have "?\<Phi> \<subseteq> Pow(X\<times>X)" unfolding UniformityFromUniCov_def Supersets_def 
      by auto
    moreover have "\<forall>A\<in>?\<Phi>.\<forall>B\<in>?\<Phi>. A\<inter>B \<in> ?\<Phi>"
    proof -
      { fix A B assume "A\<in>?\<Phi>" "B\<in>?\<Phi>"
        then have "A\<inter>B \<subseteq> X\<times>X" unfolding UniformityFromUniCov_def Supersets_def
          by auto
        from \<open>A\<in>?\<Phi>\<close> \<open>B\<in>?\<Phi>\<close> obtain P\<^sub>A P\<^sub>B where 
          "\<Union>{U\<times>U. U\<in>P\<^sub>A} \<subseteq> A" "P\<^sub>A\<in>\<Theta>" "\<Union>{U\<times>U. U\<in>P\<^sub>B} \<subseteq> B" "P\<^sub>B\<in>\<Theta>"
          unfolding UniformityFromUniCov_def Supersets_def by auto
        from assms(2) \<open>P\<^sub>A\<in>\<Theta>\<close> \<open>P\<^sub>B\<in>\<Theta>\<close> obtain P where "P\<in>\<Theta>" and "P<\<^sup>*P\<^sub>A" and "P<\<^sup>*P\<^sub>B"
          unfolding AreUniformCovers_def by blast
        have "\<Union>{U\<times>U. U\<in>P} \<subseteq> A\<inter>B"
        proof -
          { fix U assume "U\<in>P" 
            with \<open>P<\<^sup>*P\<^sub>A\<close>  \<open>P<\<^sup>*P\<^sub>B\<close> \<open>\<Union>{W\<times>W. W\<in>P\<^sub>A} \<subseteq> A\<close> \<open>\<Union>{W\<times>W. W\<in>P\<^sub>B} \<subseteq> B\<close> 
            have "U\<times>U \<subseteq> A" and "U\<times>U \<subseteq> B" using star_ref_mem by auto
          } thus ?thesis by blast
        qed
        with \<open>A\<inter>B \<subseteq> X\<times>X\<close> \<open>P\<in>\<Theta>\<close> have "A\<inter>B \<in> ?\<Phi>" 
          unfolding Supersets_def UniformityFromUniCov_def by auto
      } thus ?thesis by auto
    qed
    moreover have "\<forall>B\<in>?\<Phi>.\<forall>C\<in>Pow(X\<times>X). B\<subseteq>C \<longrightarrow> C\<in>?\<Phi>"
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
      from assms(2) \<open>P\<in>\<Theta>\<close> have "\<Union>P = X" unfolding AreUniformCovers_def Covers_def
        by auto
      with \<open>\<Union>{U\<times>U. U\<in>P} \<subseteq> A\<close> show ?thesis by auto
    qed
    moreover have "\<exists>B\<in>?\<Phi>. B O B \<subseteq> A"
    proof -
      from assms(2) \<open>P\<in>\<Theta>\<close> have "\<Union>{U\<times>U. U\<in>P} \<in> ?\<Phi>" 
        unfolding AreUniformCovers_def Covers_def UniformityFromUniCov_def Supersets_def
        by auto
      from assms(2) \<open>P\<in>\<Theta>\<close> obtain Q where "Q\<in>\<Theta>" and  "Q <\<^sup>* P" using unicov_has_star_ref
        by blast
      let ?B = "\<Union>{U\<times>U. U\<in>Q}"
      from assms(2) \<open>Q\<in>\<Theta>\<close> have "?B \<in> ?\<Phi>" 
        unfolding AreUniformCovers_def Covers_def UniformityFromUniCov_def Supersets_def
        by auto
      moreover have "?B O ?B \<subseteq> A"
      proof -
        have I: "?B O ?B = \<Union>{U\<times>Star(U,Q). U\<in>Q}" using rel_square_starr by simp
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
        with I show ?thesis by simp
      qed
      ultimately show ?thesis by auto
    qed
    moreover from assms(2) \<open>A\<in>?\<Phi>\<close> \<open>P\<in>\<Theta>\<close> \<open>\<Union>{U\<times>U. U\<in>P} \<subseteq> A\<close> have "converse(A) \<in> ?\<Phi>"
      unfolding AreUniformCovers_def UniformityFromUniCov_def Supersets_def by auto
    ultimately show "id(X) \<subseteq> A \<and> (\<exists>B\<in>?\<Phi>. B O B \<subseteq> A) \<and> converse(A) \<in> ?\<Phi>" by simp
  qed
  ultimately show "?\<Phi>  {is a uniformity on} X" unfolding IsUniformity_def by simp
qed

end
