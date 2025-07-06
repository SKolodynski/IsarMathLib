(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2024  Slawomir Kolodynski

    This program is free software; Redistribution and use in source and binary forms, 
    with or without modification, are permitted provided that the following conditions are met:

   1. Redistributions of source code must retain the above copyright notice, 
   this list of conditions and the following disclaimer.
   2. Redistributions in binary form must reproduce the above copyright notice, 
   this list of conditions and the following disclaimer in the documentation and/or 
   other materials provided with the distribution.
   3. The name of the author may not be used to endorse or promote products 
   derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES,
INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT,
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES LOSS OF USE, DATA, OR PROFITS OR
BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open>Set of uniformities as a complete lattice \<close>

theory UniformityLattice_ZF imports Cardinal_ZF Order_ZF_1a UniformSpace_ZF

begin

text\<open>In this theory we consider the collection of all uniformities on a arbitrary set $X$.
  Since unformities are sets of subsets of $X\times X$ such set of uniformities 
  is naturally ordered by the inclusion relation.
  Specifically, for two uniformities $\mathcal{U}_1$ and $\mathcal{U}_2$​ on a set $X$ 
  if $\mathcal{U}_1 \subseteq \mathcal{U}_2$ we say that $\mathcal{U}_2$ is finer than 
  $\mathcal{U}_1$ or that $\mathcal{U}_1$ is coarser than $\mathcal{U}_2$. 
  In this theory we show that with this order the collection of uniformities 
  forms a complete lattice. \<close>

subsection\<open>Uniformities on a fixed set as a partially ordered set\<close>

text\<open>In this section we introduce the definitions of the set of uniformities on $X$ and
  show that the inclusion relation is on this set makes it a partially ordered set (a poset)
  with a maximum and minimum.\<close>

text\<open>We define \<open>Uniformities(X)\<close> as the set of all uniformities on $X$. \<close>

definition 
  "Uniformities(X) \<equiv> {\<Phi> \<in> Pow(Pow(X\<times>X)). \<Phi> {is a uniformity on} X}"

text\<open>If $\Phi$ is a uniformity on $X$, then $\Phi$ is a collection of subsets of $X\times X$,
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
    unfolding HasAminimum_def using Order_ZF_4_L15 ord_unif_antisymm 
    by auto
  { fix \<Phi> assume "\<Phi> \<in> ?\<UU>"
    then have "\<Phi> \<subseteq> ?M" unfolding IsUniformity_def Uniformities_def 
      by auto
    with \<open>?M\<in>?\<UU>\<close> \<open>\<Phi>\<in>?\<UU>\<close>  have "\<langle>\<Phi>,?M\<rangle> \<in> ?r"
      unfolding OrderOnUniformities_def InclusionOn_def by simp
  } with  \<open>?M\<in>?\<UU>\<close> show "HasAmaximum(?r,?\<UU>)" and "Maximum(?r,?\<UU>) = ?M"
    unfolding HasAmaximum_def using Order_ZF_4_L14 ord_unif_antisymm 
    by auto
qed

subsection\<open>Least upper bound of a set of uniformities\<close>

text\<open>In this section we show that inclusion order on the collection of unformities on a fixed
  set is (Dedekind) complete i.e. every nonempty set of uniformities has
  a least upper bound. \<close>


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
  assumes "\<U>\<subseteq>Uniformities(X)"  "U\<^sub>1 \<in> LUB_UnifBase(\<U>)"  "U\<^sub>2 \<in> LUB_UnifBase(\<U>)"
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
  from assms(2,3) have 
    "\<Phi> \<in> Uniformities(X)" and "\<Phi> {is a uniformity on} X"
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

text\<open>Any upper bound (in the order defined by inclusion relation) of a nonempty collection of 
  uniformities $\mathcal{U}$ on a nonempty set $X$ is greater or equal (in that order) 
  than \<open>LUB_Unif(X,\<U>)\<close>. Together with \<open>lub_unif_upper_bound\<close> it means that \<open>LUB_Unif(X,\<U>)\<close>
  is indeed the least upper bound of $\mathcal{U}$.\<close>

lemma lub_unif_lub: 
  assumes "X\<noteq>\<emptyset>"  "\<U>\<subseteq>Uniformities(X)"  "\<U>\<noteq>\<emptyset>"  and 
    "\<forall>\<Phi>\<in>\<U>. \<langle>\<Phi>,\<Psi>\<rangle> \<in> OrderOnUniformities(X)"
  shows "\<langle>LUB_Unif(X,\<U>),\<Psi>\<rangle> \<in> OrderOnUniformities(X)"
proof -
  from assms(3,4) have "\<Psi> \<in> Uniformities(X)" 
    unfolding OrderOnUniformities_def InclusionOn_def by auto
  then have "\<Psi> {is a filter on} (X\<times>X)" 
    unfolding Uniformities_def IsUniformity_def by simp
  from assms(4) have "FinPow(\<Union>\<U>)\<setminus>{\<emptyset>} \<subseteq> FinPow(\<Psi>)\<setminus>{\<emptyset>}"
    unfolding OrderOnUniformities_def InclusionOn_def FinPow_def 
    by auto 
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
  with assms(3) \<open>antisym(?r)\<close> \<open>\<forall>\<Phi>\<in>\<U>. \<langle>\<Phi>,?S\<rangle> \<in> ?r\<close> show "HasAsupremum(?r,\<U>)" 
    unfolding HasAsupremum_def using Order_ZF_5_L5(1) by blast
  from assms(3) \<open>antisym(?r)\<close> \<open>\<forall>\<Phi>\<in>\<U>. \<langle>\<Phi>,?S\<rangle> \<in> ?r\<close> I
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
