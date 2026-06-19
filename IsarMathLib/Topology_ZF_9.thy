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

section \<open>Homeomorphisms as a group — connecting topology and group theory\<close>

theory Topology_ZF_9
imports Topology_ZF_2 Group_ZF_2 Topology_ZF_7 Topology_ZF_8
begin

text\<open>The collection of all homeomorphisms of a topological space onto itself forms a group
  under composition. This file develops that group structure, connecting the theory of
  topological spaces with the algebraic theory of groups.\<close>

subsection\<open>Group of homeomorphisms\<close>

text\<open>We show that the homeomorphisms of a topological space onto itself form a group
under composition, and compute this group for several concrete topologies.\<close>

text\<open>First, we define the set of homeomorphisms.\<close>

definition
  "HomeoG(T) \<equiv> {f:\<Union>T\<rightarrow>\<Union>T. IsAhomeomorphism(T,T,f)}"

text\<open>The homeomorphisms are closed by composition.\<close>

lemma (in topology0) homeo_composition:
  assumes "f\<in>HomeoG(T)""g\<in>HomeoG(T)"
  shows "Composition(\<Union>T)`\<langle>f, g\<rangle>\<in>HomeoG(T)"
proof-
  from assms have fun:"f\<in>\<Union>T\<rightarrow>\<Union>T""g\<in>\<Union>T\<rightarrow>\<Union>T" and homeo:"IsAhomeomorphism(T,T,f)""IsAhomeomorphism(T,T,g)" 
    unfolding HomeoG_def by auto
  from homeo have bij:"f\<in>bij(\<Union>T,\<Union>T)""g\<in>bij(\<Union>T,\<Union>T)" and cont:"IsContinuous(T,T,f)""IsContinuous(T,T,g)" 
    and contconv:"IsContinuous(T,T,converse(f))""IsContinuous(T,T,converse(g))" 
    unfolding IsAhomeomorphism_def by auto
  from fun have "f O g\<in>\<Union>T\<rightarrow>\<Union>T" using comp_fun by auto moreover
  from bij have "f O g\<in>bij(\<Union>T,\<Union>T)" using comp_bij by auto moreover
  from cont have "IsContinuous(T,T,f O g)" using comp_cont by auto moreover
  have "converse(f O g)=converse(g) O converse(f)" using converse_comp by auto
  with contconv have "IsContinuous(T,T,converse(f O g))" using comp_cont by auto ultimately
  have "f O g\<in>HomeoG(T)" unfolding HomeoG_def IsAhomeomorphism_def by auto
  then show ?thesis using func_ZF_5_L2 fun by auto
qed

text\<open>The identity function is a homeomorphism.\<close>

lemma (in topology0) homeo_id:
  shows "id(\<Union>T)\<in>HomeoG(T)"
proof-
  have "converse(id(\<Union>T)) O id(\<Union>T)=id(\<Union>T)" using left_comp_inverse id_bij by auto
  then have "converse(id(\<Union>T))=id(\<Union>T)" using right_comp_id by auto
  then show ?thesis unfolding HomeoG_def IsAhomeomorphism_def using id_cont id_type id_bij
    by auto
qed

text\<open>The homeomorphisms form a monoid and its neutral element is the identity.\<close>

theorem (in topology0) homeo_submonoid:
  shows "IsAmonoid(HomeoG(T),restrict(Composition(\<Union>T),HomeoG(T)\<times>HomeoG(T)))" 
  "TheNeutralElement(HomeoG(T),restrict(Composition(\<Union>T),HomeoG(T)\<times>HomeoG(T)))=id(\<Union>T)"
proof-
  have cl:"HomeoG(T) {is closed under} Composition(\<Union>T)" unfolding IsOpClosed_def using homeo_composition by auto
  moreover have sub:"HomeoG(T)\<subseteq>\<Union>T\<rightarrow>\<Union>T" unfolding HomeoG_def by auto moreover
  have ne:"TheNeutralElement(\<Union>T\<rightarrow>\<Union>T, Composition(\<Union>T))\<in>HomeoG(T)" using homeo_id Group_ZF_2_5_L2(2) by auto
  ultimately show "IsAmonoid(HomeoG(T),restrict(Composition(\<Union>T),HomeoG(T)\<times>HomeoG(T)))" using Group_ZF_2_5_L2(1)
    monoid0.group0_1_T1 unfolding monoid0_def by force
  from cl sub ne have "TheNeutralElement(HomeoG(T),restrict(Composition(\<Union>T),HomeoG(T)\<times>HomeoG(T)))=TheNeutralElement(\<Union>T\<rightarrow>\<Union>T, Composition(\<Union>T))" 
    using Group_ZF_2_5_L2(1) group0_1_L6 by blast moreover
  have "id(\<Union>T)=TheNeutralElement(\<Union>T\<rightarrow>\<Union>T, Composition(\<Union>T))" using Group_ZF_2_5_L2(2) by auto
  ultimately show "TheNeutralElement(HomeoG(T),restrict(Composition(\<Union>T),HomeoG(T)\<times>HomeoG(T)))=id(\<Union>T)" by auto
qed

text\<open>The homeomorphisms form a group, with the composition.\<close>

theorem (in topology0) homeo_group:
  shows "IsAgroup(HomeoG(T),restrict(Composition(\<Union>T),HomeoG(T)\<times>HomeoG(T)))"
proof-
  {
    fix x assume AS:"x\<in>HomeoG(T)"
    then have surj:"x\<in>surj(\<Union>T,\<Union>T)" and bij:"x\<in>bij(\<Union>T,\<Union>T)" unfolding HomeoG_def IsAhomeomorphism_def bij_def by auto
    from bij have "converse(x)\<in>bij(\<Union>T,\<Union>T)" using bij_converse_bij by auto
    with bij have conx_fun:"converse(x)\<in>\<Union>T\<rightarrow>\<Union>T""x\<in>\<Union>T\<rightarrow>\<Union>T" unfolding bij_def inj_def by auto
    from surj have id:"x O converse(x)=id(\<Union>T)" using right_comp_inverse by auto
    from conx_fun have "Composition(\<Union>T)`\<langle>x,converse(x)\<rangle>=x O converse(x)" using func_ZF_5_L2 by auto
    with id have "Composition(\<Union>T)`\<langle>x,converse(x)\<rangle>=id(\<Union>T)" by auto
    moreover have "converse(x)\<in>HomeoG(T)" using conx_fun(1) homeo_inv AS unfolding HomeoG_def
      by auto
    ultimately have "\<exists>M\<in>HomeoG(T). Composition(\<Union>T)`\<langle>x,M\<rangle>=id(\<Union>T)" by auto
  }
  then have "\<forall>x\<in>HomeoG(T). \<exists>M\<in>HomeoG(T). Composition(\<Union>T)`\<langle>x,M\<rangle>=id(\<Union>T)" by auto
  then show ?thesis using homeo_submonoid definition_of_group by auto
qed

subsection\<open>Examples computed\<close>

text\<open>We compute $\text{HomeoG}$ for several concrete topologies: the cocardinal topology,
the excluded set topology, the included set topology, and the order topology.\<close>

text\<open>For the cocardinal topology every bijection is a homeomorphism, so $\text{HomeoG}$
equals $\text{bij}(X,X)$.\<close>

theorem homeo_cocardinal:
  assumes "InfCard(Q)"
  shows "HomeoG(CoCardinal(X,Q))=bij(X,X)"
proof
  from assms have n:"Q\<noteq>0" unfolding InfCard_def by auto
  then show "HomeoG(CoCardinal(X,Q)) \<subseteq> bij(X, X)" unfolding HomeoG_def IsAhomeomorphism_def
    using union_cocardinal by auto
  {
    fix f assume a:"f\<in>bij(X,X)"
    then have "converse(f)\<in>bij(X,X)" using bij_converse_bij by auto
    then have cinj:"converse(f)\<in>inj(X,X)" unfolding bij_def by auto
    from a have fun:"f\<in>X\<rightarrow>X" unfolding bij_def inj_def by auto
    then have two:"two_top_spaces0((CoCardinal(X,Q)),(CoCardinal(X,Q)),f)" unfolding two_top_spaces0_def
      using union_cocardinal assms n CoCar_is_topology by auto
    {
      fix N assume "N{is closed in}(CoCardinal(X,Q))"
      then have N_def:"N=X \<or> (N\<in>Pow(X) \<and> N\<prec>Q)" using closed_sets_cocardinal n by auto
      then have "restrict(converse(f),N)\<in>bij(N,converse(f)``N)" using cinj restrict_bij by auto
      then have "N\<approx>f-``N" unfolding vimage_def eqpoll_def by auto
      then have "f-``N\<approx>N" using eqpoll_sym by auto
      with N_def have "N=X \<or> (f-``N\<prec>Q \<and> N\<in>Pow(X))" using eq_lesspoll_trans by auto
      with fun have "f-``N=X \<or> (f-``N\<prec>Q \<and> (f-``N)\<in>Pow(X))" using func1_1_L3 func1_1_L4 by auto
      then have "f-``N {is closed in}(CoCardinal(X,Q))" using closed_sets_cocardinal n by auto
    }
    then have "\<forall>N. N{is closed in}(CoCardinal(X,Q)) \<longrightarrow> f-``N {is closed in}(CoCardinal(X,Q))" by auto
    then have "IsContinuous((CoCardinal(X,Q)),(CoCardinal(X,Q)),f)" using two_top_spaces0.Top_ZF_2_1_L4 
      two_top_spaces0.Top_ZF_2_1_L3 two_top_spaces0.Top_ZF_2_1_L2 two by auto
  }
  then have "\<forall>f\<in>bij(X,X). IsContinuous((CoCardinal(X,Q)),(CoCardinal(X,Q)),f)" by auto
  then have "\<forall>f\<in>bij(X,X). IsContinuous((CoCardinal(X,Q)),(CoCardinal(X,Q)),f) \<and> IsContinuous((CoCardinal(X,Q)),(CoCardinal(X,Q)),converse(f))"
    using bij_converse_bij by auto
  then have "\<forall>f\<in>bij(X,X). IsAhomeomorphism((CoCardinal(X,Q)),(CoCardinal(X,Q)),f)" unfolding IsAhomeomorphism_def
    using n union_cocardinal by auto
  then show "bij(X,X)\<subseteq>HomeoG((CoCardinal(X,Q)))" unfolding HomeoG_def bij_def inj_def using n union_cocardinal
    by auto
qed

text\<open>The homeomorphisms of the excluded set topology are exactly the bijections of $X$
that map $X\setminus T$ to itself.\<close>

theorem homeo_excluded:
  assumes "T \<subseteq> X"
  shows "HomeoG(ExcludedSet(X,T))={f\<in>bij(X,X). f``(X-T)=(X-T)}"
proof
  have sub1:"X-T\<subseteq>X" by auto
  {
    fix g assume "g\<in>HomeoG(ExcludedSet(X,T))"
    then have fun:"g:X\<rightarrow>X" and bij:"g\<in>bij(X,X)" and hom:"IsAhomeomorphism((ExcludedSet(X,T)),(ExcludedSet(X,T)),g)" 
      using union_excludedset unfolding IsAhomeomorphism_def HomeoG_def by auto
    have op:"X-T\<in>ExcludedSet(X,T)" unfolding ExcludedSet_def by auto
    with hom have "converse(g)-``(X-T)\<in>ExcludedSet(X,T)" unfolding IsAhomeomorphism_def IsContinuous_def by auto
    then have "converse(converse(g))``(X-T)\<in>ExcludedSet(X,T)" using vimage_def by auto
    with bij have D1:"g``(X-T)\<in>ExcludedSet(X,T)" using converse_converse unfolding bij_def inj_def Pi_def Sigma_def by auto
    from op hom have D2:"g-``(X-T)\<in>ExcludedSet(X,T)" unfolding IsAhomeomorphism_def IsContinuous_def by auto
    {
      assume as:"g``(X-T) = X"
      then have "g-``(g``(X-T)) = g-``X" by auto
      then have "converse(g)``(g``(X-T)) = g-``X" using vimage_def by auto
      then have "(converse(g) O g)``(X-T) = g-``X" using image_comp by auto
      then have "id(X)``(X-T) = g-``X" using left_comp_inverse bij unfolding bij_def by auto moreover
      have "X-T \<subseteq> X \<Longrightarrow> id(X)``(X-T) = X-T" by auto
      ultimately have "X-T = g-``X" using sub1 by auto
      moreover
      have "converse(g):bij(X,X)" using bij_converse_bij bij by auto
      then have "converse(g):surj(X,X)" unfolding bij_def by auto
      then have "converse(g)``X = X" using surj_range_image_domain by auto
      then have "g-``X =X" using vimage_def by auto
      ultimately have "X-T =X" by auto
      with as have "g``(X-T) = X-T" by auto
    } moreover
    {
      assume A:"g``(X-T)\<in>{F \<in> Pow(X) . T \<inter> F = \<emptyset>}"
      then have "T\<inter>g``(X-T) =0" by auto
      then have "g``(X-T) \<subseteq> X -T" using A by auto
      then have "g-``(g``(X-T)) \<subseteq> g-``(X-T)" by auto
      then have "converse(g)``(g``(X-T)) \<subseteq> g-``(X-T)" using vimage_def by auto
      then have "(converse(g) O g)``(X-T) \<subseteq> g-``(X-T)" using image_comp by auto
      then have "id(X)``(X-T) \<subseteq> g-``(X-T)" using left_comp_inverse bij 
        unfolding bij_def by force moreover
      have "X-T \<subseteq> X \<Longrightarrow> id(X)``(X-T) = X-T" by auto
      ultimately have C:"X-T \<subseteq> g-``(X-T)" using sub1 by auto
      {
        assume as:"g-``(X-T) = X"
        then have "g``(g-``(X-T)) = g``X" by auto
        then have "g``(converse(g)``(X-T)) = g``X" using vimage_def by auto
        then have "(g O converse(g))``(X-T) = g``X" using image_comp by auto
        then have "id(X)``(X-T) = g``X" using right_comp_inverse bij unfolding bij_def by auto moreover
        have "X-T \<subseteq> X \<Longrightarrow> id(X)``(X-T) = X-T" by auto
        ultimately have B:"X-T = g``X" using sub1 by auto
        moreover
        from bij have "g``X = X" using surj_range_image_domain unfolding bij_def by auto
        ultimately have "X-T =X" by auto
        with B have "g``(X-T) = X-T" by auto
      } moreover
      {
        assume as:"g-``(X-T)\<in>{F \<in> Pow(X) . T \<inter> F = \<emptyset>}"
        then have "T\<inter>g-``(X-T) =0" by auto
        then have "g-``(X-T) \<subseteq> X -T" using as by auto
        with C have "g-``(X-T) = X-T" by auto
        then have "g``(g-``(X-T)) = g``(X-T)" by auto
        then have "g``(converse(g)``(X-T)) = g``(X-T)" using vimage_def by auto
        then have "(g O converse(g))``(X-T) = g``(X-T)" using image_comp by auto
        then have "id(X)``(X-T) = g``(X-T)" using right_comp_inverse bij unfolding bij_def by auto moreover
        have "X-T \<subseteq> X \<Longrightarrow> id(X)``(X-T) = X-T" by auto
        ultimately have B:"X-T = g``(X-T)" using sub1 by auto
        then have "g``(X-T) = X-T" by auto
      } moreover
      note D2 ultimately have "g``(X-T) = X-T" unfolding ExcludedSet_def by blast
    }
    moreover note D1
    ultimately have "g``(X-T) = X-T" unfolding ExcludedSet_def by blast
    with bij have "g\<in>{f\<in>bij(X,X). f``(X-T)=(X-T)}" by auto
  }
  then show "HomeoG(ExcludedSet(X,T))\<subseteq>{f\<in>bij(X,X). f``(X-T)=(X-T)}" by auto
  {
    fix g assume as:"g\<in>bij(X,X)""g``(X-T)=X-T"
    then have inj:"g\<in>inj(X,X)" and im:"g-``(g``(X-T))=g-``(X-T)" unfolding bij_def by auto
    from inj have "g-``(g``(X-T))=X-T" using inj_vimage_image sub1 by force
    with im have as_3:"g-``(X-T)=X-T" by auto
    {
      fix A
      assume "A\<in>(ExcludedSet(X,T))"
      then have "A=X\<or>A\<inter>T=0" "A\<subseteq>X" unfolding ExcludedSet_def by auto
      then have "A\<subseteq>X-T\<or>A=X" by auto moreover
      {
        assume "A=X"
        with as(1) have "g``A=X" using surj_range_image_domain unfolding bij_def by auto
      }
      moreover
      {
        assume "A\<subseteq>X-T"
        then have "g``A\<subseteq>g``(X-T)" using func1_1_L8 by auto
        then have "g``A\<subseteq>(X-T)" using as(2)  by auto
      }
      ultimately have "g``A\<subseteq>(X-T) \<or> g``A=X" by auto
      then have "g``A\<in>(ExcludedSet(X,T))" unfolding ExcludedSet_def by auto
    }
    then have "\<forall>A\<in>(ExcludedSet(X,T)). g``A\<in>(ExcludedSet(X,T))" by auto moreover
    {
      fix A assume "A\<in>(ExcludedSet(X,T))"
      then have "A=X\<or>A\<inter>T=0" "A\<subseteq>X" unfolding ExcludedSet_def by auto
      then have "A\<subseteq>X-T\<or>A=X" by auto moreover
      {
        assume "A=X"
        with as(1) have "g-``A=X" using func1_1_L4 unfolding bij_def inj_def by auto
      }
      moreover
      {
        assume "A\<subseteq>X-T"
        then have "g-``A\<subseteq>g-``(X-T)" using func1_1_L8 by auto
        then have "g-``A\<subseteq>(X-T)" using as_3 by auto
      }
      ultimately have "g-``A\<subseteq>(X-T) \<or> g-``A=X" by auto
      then have "g-``A\<in>(ExcludedSet(X,T))" unfolding ExcludedSet_def by auto
    }
    then have "IsContinuous(ExcludedSet(X,T),ExcludedSet(X,T),g)" unfolding IsContinuous_def by auto moreover
    note as(1) ultimately have "IsAhomeomorphism(ExcludedSet(X,T),ExcludedSet(X,T),g)" 
      using union_excludedset bij_cont_open_homeo by auto
    with as(1) have "g\<in>HomeoG(ExcludedSet(X,T))" unfolding bij_def inj_def HomeoG_def using union_excludedset by auto
  }
  then show "{f \<in> bij(X, X) . f `` (X - T) = X - T} \<subseteq> HomeoG(ExcludedSet(X,T))" by auto
qed

text\<open>Continuity in the included set topology implies continuity in the excluded set topology.\<close>

lemma cont_in_cont_ex:
  assumes "IsContinuous(IncludedSet(X,T),IncludedSet(X,T),f)" "f:X\<rightarrow>X" "T\<subseteq>X"
  shows "IsContinuous(ExcludedSet(X,T),ExcludedSet(X,T),f)"
proof-
  from assms(2,3) have two:"two_top_spaces0(IncludedSet(X,T),IncludedSet(X,T),f)" using union_includedset includedset_is_topology 
    unfolding two_top_spaces0_def by auto
  {
    fix A assume "A\<in>(ExcludedSet(X,T))"
    then have "A\<inter>T=0 \<or> A=X""A\<subseteq>X" unfolding ExcludedSet_def by auto
    then have "A{is closed in}(IncludedSet(X,T))" using closed_sets_includedset assms by auto
    then have "f-``A{is closed in}(IncludedSet(X,T))" using two_top_spaces0.TopZF_2_1_L1 assms(1)
      two assms includedset_is_topology by auto
    then have "(f-``A)\<inter>T=0 \<or> f-``A=X""f-``A\<subseteq>X" using closed_sets_includedset assms(1,3) by auto
    then have "f-``A\<in>(ExcludedSet(X,T))" unfolding ExcludedSet_def by auto
  }
  then show "IsContinuous(ExcludedSet(X,T),ExcludedSet(X,T),f)" unfolding IsContinuous_def by auto
qed

text\<open>Continuity in the excluded set topology implies continuity in the included set topology.\<close>

lemma cont_ex_cont_in:
  assumes "IsContinuous(ExcludedSet(X,T),ExcludedSet(X,T),f)" "f:X\<rightarrow>X" "T\<subseteq>X"
  shows "IsContinuous(IncludedSet(X,T),IncludedSet(X,T),f)"
proof-
  from assms(2) have two:"two_top_spaces0(ExcludedSet(X,T),ExcludedSet(X,T),f)" using union_excludedset excludedset_is_topology 
    unfolding two_top_spaces0_def by auto
  {
    fix A assume "A\<in>(IncludedSet(X,T))"
    then have "T\<subseteq>A \<or> A=0""A\<subseteq>X" unfolding IncludedSet_def by auto
    then have "A{is closed in}(ExcludedSet(X,T))" using closed_sets_excludedset assms by auto
    then have "f-``A{is closed in}(ExcludedSet(X,T))" using two_top_spaces0.TopZF_2_1_L1 assms(1)
      two assms excludedset_is_topology by auto
    then have "T\<subseteq>(f-``A) \<or> f-``A=0""f-``A\<subseteq>X" using closed_sets_excludedset assms(1,3) by auto
    then have "f-``A\<in>(IncludedSet(X,T))" unfolding IncludedSet_def by auto
  }
  then show "IsContinuous(IncludedSet(X,T),IncludedSet(X,T),f)" unfolding IsContinuous_def by auto
qed

text\<open>By the previous two lemmas, the homeomorphism groups of the included and excluded
set topologies on $X$ coincide.\<close>

lemma homeo_included:
  assumes "T\<subseteq>X"
  shows "HomeoG(IncludedSet(X,T))={f \<in> bij(X, X) . f `` (X - T) = X - T}"
proof-
  {
    fix f assume "f\<in>HomeoG(IncludedSet(X,T))"
    then have hom:"IsAhomeomorphism(IncludedSet(X,T),IncludedSet(X,T),f)" and fun:"f\<in>X\<rightarrow>X" and
      bij:"f\<in>bij(X,X)" unfolding HomeoG_def IsAhomeomorphism_def using union_includedset assms by auto
    then have cont:"IsContinuous(IncludedSet(X,T),IncludedSet(X,T),f)" unfolding IsAhomeomorphism_def by auto
    then have "IsContinuous(ExcludedSet(X,T),ExcludedSet(X,T),f)" using cont_in_cont_ex fun assms by auto moreover
    {
      from hom have cont1:"IsContinuous(IncludedSet(X,T),IncludedSet(X,T),converse(f))" unfolding IsAhomeomorphism_def by auto moreover
      have "converse(f):X\<rightarrow>X" using bij_converse_bij bij unfolding bij_def inj_def by auto moreover
      note assms ultimately 
      have "IsContinuous(ExcludedSet(X,T),ExcludedSet(X,T),converse(f))" using cont_in_cont_ex assms by auto
    }
    then have "IsContinuous(ExcludedSet(X,T),ExcludedSet(X,T),converse(f))" by auto
    moreover note bij ultimately
    have "IsAhomeomorphism(ExcludedSet(X,T),ExcludedSet(X,T),f)" unfolding IsAhomeomorphism_def
      using union_excludedset by auto
    with fun have "f\<in>HomeoG(ExcludedSet(X,T))" unfolding HomeoG_def using union_excludedset by auto
  }
  then have "HomeoG(IncludedSet(X,T))\<subseteq>HomeoG(ExcludedSet(X,T))" by auto moreover
  {
    fix f assume "f\<in>HomeoG(ExcludedSet(X,T))"
    then have hom:"IsAhomeomorphism(ExcludedSet(X,T),ExcludedSet(X,T),f)" and fun:"f\<in>X\<rightarrow>X" and
      bij:"f\<in>bij(X,X)" unfolding HomeoG_def IsAhomeomorphism_def using union_excludedset assms by auto
    then have cont:"IsContinuous(ExcludedSet(X,T),ExcludedSet(X,T),f)" unfolding IsAhomeomorphism_def by auto
    then have "IsContinuous(IncludedSet(X,T),IncludedSet(X,T),f)" using cont_ex_cont_in fun assms by auto moreover
    {
      from hom have cont1:"IsContinuous(ExcludedSet(X,T),ExcludedSet(X,T),converse(f))" unfolding IsAhomeomorphism_def by auto moreover
      have "converse(f):X\<rightarrow>X" using bij_converse_bij bij unfolding bij_def inj_def by auto moreover
      note assms ultimately 
      have "IsContinuous(IncludedSet(X,T),IncludedSet(X,T),converse(f))" using cont_ex_cont_in assms by auto
    }
    then have "IsContinuous(IncludedSet(X,T),IncludedSet(X,T),converse(f))" by auto
    moreover note bij ultimately
    have "IsAhomeomorphism(IncludedSet(X,T),IncludedSet(X,T),f)" unfolding IsAhomeomorphism_def
      using union_includedset assms by auto
    with fun have "f\<in>HomeoG(IncludedSet(X,T))" unfolding HomeoG_def using union_includedset assms by auto
  }
  then have "HomeoG(ExcludedSet(X,T))\<subseteq>HomeoG(IncludedSet(X,T))" by auto ultimately
  show ?thesis using homeo_excluded assms by auto
qed

text\<open>Every order isomorphism of a linearly ordered set is a homeomorphism of
the induced order topology.\<close>

lemma homeo_order:
  assumes "IsLinOrder(X,r)""\<exists>x y. x\<noteq>y\<and>x\<in>X\<and>y\<in>X"
  shows "ord_iso(X,r,X,r)\<subseteq>HomeoG(OrdTopology X r)"
proof
  let ?\<BB> = "{IntervalX(X, r, b, c) . \<langle>b,c\<rangle> \<in> X \<times> X} \<union> {LeftRayX(X, r, b) . b \<in> X} \<union>
    {RightRayX(X, r, b) . b \<in> X}"
  fix f assume "f\<in>ord_iso(X,r,X,r)"
  then have bij:"f\<in>bij(X,X)" and ord:"\<forall>x\<in>X. \<forall>y\<in>X. \<langle>x, y\<rangle> \<in> r \<longleftrightarrow> \<langle>f ` x, f ` y\<rangle> \<in> r"
    unfolding ord_iso_def by auto
  have top:"(OrdTopology X r){is a topology}" using Ordtopology_is_a_topology(1) assms(1) by auto
  have union:"\<Union>(OrdTopology X r) = X" using union_ordtopology assms by auto
  have twoSpac:"two_top_spaces0(OrdTopology X r,OrdTopology X r,f)" using bij top union unfolding two_top_spaces0_def
    bij_def inj_def
    by auto
  {
    fix c d assume A:"c\<in>X""d\<in>X"
    {
      fix x assume AA:"x\<in>X""x\<noteq>c""x\<noteq>d""\<langle>c,x\<rangle>\<in>r""\<langle>x,d\<rangle>\<in>r"
      then have "\<langle>f`c,f`x\<rangle>\<in>r""\<langle>f`x,f`d\<rangle>\<in>r" using A(2,1) ord by auto moreover
      {
        assume "f`x=f`c \<or> f`x=f`d"
        with A(2,1) AA(1) have "x=c\<or>x=d" using bij unfolding bij_def inj_def by auto
        then have "False" using AA(2,3) by auto
      }
      then have "f`x\<noteq>f`c""f`x\<noteq>f`d" by auto moreover
      have "f`x\<in>X" using bij apply_type AA(1) unfolding bij_def inj_def by auto
      ultimately have "f`x\<in>IntervalX(X,r,f`c,f`d)" unfolding IntervalX_def Interval_def by auto
    }
    then have "{f`x. x\<in>IntervalX(X,r,c,d)}\<subseteq>IntervalX(X,r,f`c,f`d)" unfolding IntervalX_def Interval_def by auto
    moreover
    {
      fix y assume "y\<in>IntervalX(X,r,f`c,f`d)"
      then have y:"y\<in>X""y\<noteq>f`c""y\<noteq>f`d""\<langle>f`c,y\<rangle>\<in>r""\<langle>y,f`d\<rangle>\<in>r" unfolding IntervalX_def Interval_def by auto
      then obtain s where s:"s\<in>X""y=f`s" using bij unfolding bij_def surj_def by auto
      {
        assume "s=c\<or>s=d"
        then have "f`s=f`c\<or>f`s=f`d" by auto
        then have "False" using s(2) y(2,3) by auto
      }
      then have "s\<noteq>c""s\<noteq>d" by auto moreover
      have "\<langle>c,s\<rangle>\<in>r""\<langle>s,d\<rangle>\<in>r" using y(4,5) s ord A(2,1) by auto moreover
      note s(1) ultimately have "s\<in>IntervalX(X,r,c,d)" unfolding IntervalX_def Interval_def by auto
      then have "y\<in>{f`x. x\<in>IntervalX(X,r,c,d)}" using s(2) by auto
    }
    ultimately have "{f`x. x\<in>IntervalX(X,r,c,d)}=IntervalX(X,r,f`c,f`d)" by auto moreover
    have "IntervalX(X,r,c,d)\<subseteq>X" unfolding IntervalX_def by auto moreover
    have "f:X\<rightarrow>X" using bij unfolding bij_def surj_def by auto ultimately
    have "f``IntervalX(X,r,c,d)=IntervalX(X,r,f`c,f`d)" using func_imagedef by auto
  }
  then have inter:"\<forall>c\<in>X. \<forall>d\<in>X. f``IntervalX(X,r,c,d)=IntervalX(X,r,f`c,f`d) \<and> f`c\<in>X \<and> f`d\<in>X" using bij 
    unfolding bij_def inj_def by auto
  {
    fix c assume A:"c\<in>X"
    {
      fix x assume AA:"x\<in>X""x\<noteq>c""\<langle>c,x\<rangle>\<in>r"
      then have "\<langle>f`c,f`x\<rangle>\<in>r" using A ord by auto moreover
      {
        assume "f`x=f`c"
        with A AA(1) have "x=c" using bij unfolding bij_def inj_def by auto
        then have "False" using AA(2) by auto
      }
      then have "f`x\<noteq>f`c" by auto moreover
      have "f`x\<in>X" using bij apply_type AA(1) unfolding bij_def inj_def by auto
      ultimately have "f`x\<in>RightRayX(X,r,f`c)" unfolding RightRayX_def by auto
    }
    then have "{f`x. x\<in>RightRayX(X,r,c)}\<subseteq>RightRayX(X,r,f`c)" unfolding RightRayX_def by auto
    moreover
    {
      fix y assume "y\<in>RightRayX(X,r,f`c)"
      then have y:"y\<in>X""y\<noteq>f`c""\<langle>f`c,y\<rangle>\<in>r" unfolding RightRayX_def by auto
      then obtain s where s:"s\<in>X""y=f`s" using bij unfolding bij_def surj_def by auto
      {
        assume "s=c"
        then have "f`s=f`c" by auto
        then have "False" using s(2) y(2) by auto
      }
      then have "s\<noteq>c" by auto moreover
      have "\<langle>c,s\<rangle>\<in>r" using y(3) s ord A by auto moreover
      note s(1) ultimately have "s\<in>RightRayX(X,r,c)" unfolding RightRayX_def by auto
      then have "y\<in>{f`x. x\<in>RightRayX(X,r,c)}" using s(2) by auto
    }
    ultimately have "{f`x. x\<in>RightRayX(X,r,c)}=RightRayX(X,r,f`c)" by auto moreover
    have "RightRayX(X,r,c)\<subseteq>X" unfolding RightRayX_def by auto moreover
    have "f:X\<rightarrow>X" using bij unfolding bij_def surj_def by auto ultimately
    have "f``RightRayX(X,r,c)=RightRayX(X,r,f`c)" using func_imagedef by auto
  }
  then have rray:"\<forall>c\<in>X. f``RightRayX(X,r,c)=RightRayX(X,r,f`c) \<and> f`c\<in>X" using bij 
    unfolding bij_def inj_def by auto
  {
    fix c assume A:"c\<in>X"
    {
      fix x assume AA:"x\<in>X""x\<noteq>c""\<langle>x,c\<rangle>\<in>r"
      then have "\<langle>f`x,f`c\<rangle>\<in>r" using A ord by auto moreover
      {
        assume "f`x=f`c"
        with A AA(1) have "x=c" using bij unfolding bij_def inj_def by auto
        then have "False" using AA(2) by auto
      }
      then have "f`x\<noteq>f`c" by auto moreover
      from AA(1) have "f`x\<in>X" using bij apply_type unfolding bij_def inj_def by auto
      ultimately have "f`x\<in>LeftRayX(X,r,f`c)" unfolding LeftRayX_def by auto
    }
    then have "{f`x. x\<in>LeftRayX(X,r,c)}\<subseteq>LeftRayX(X,r,f`c)" unfolding LeftRayX_def by auto
    moreover
    {
      fix y assume "y\<in>LeftRayX(X,r,f`c)"
      then have y:"y\<in>X""y\<noteq>f`c""\<langle>y,f`c\<rangle>\<in>r" unfolding LeftRayX_def by auto
      then obtain s where s:"s\<in>X""y=f`s" using bij unfolding bij_def surj_def by auto
      {
        assume "s=c"
        then have "f`s=f`c" by auto
        then have "False" using s(2) y(2) by auto
      }
      then have "s\<noteq>c" by auto moreover
      have "\<langle>s,c\<rangle>\<in>r" using y(3) s ord A by auto moreover
      note s(1) ultimately have "s\<in>LeftRayX(X,r,c)" unfolding LeftRayX_def by auto
      then have "y\<in>{f`x. x\<in>LeftRayX(X,r,c)}" using s(2) by auto
    }
    ultimately have "{f`x. x\<in>LeftRayX(X,r,c)}=LeftRayX(X,r,f`c)" by auto moreover
    have "LeftRayX(X,r,c)\<subseteq>X" unfolding LeftRayX_def by auto moreover
    have "f:X\<rightarrow>X" using bij unfolding bij_def surj_def by auto ultimately
    have "f``LeftRayX(X,r,c)=LeftRayX(X,r,f`c)" using func_imagedef by auto
  }
  then have lray:"\<forall>c\<in>X. f``LeftRayX(X,r,c)=LeftRayX(X,r,f`c)\<and>f`c\<in>X" using bij 
    unfolding bij_def inj_def by auto
  have r1:"\<forall>U\<in>?\<BB>. f``U\<in>?\<BB>" 
  proof
    fix U assume A:"U\<in>?\<BB>"
    {
      assume "U\<in>{IntervalX(X, r, b, c) . \<langle>b,c\<rangle> \<in> X \<times> X}"
      with inter have "f``U\<in>{IntervalX(X, r, b, c) . \<langle>b,c\<rangle> \<in> X \<times> X}" by auto
      then have "f``U\<in>?\<BB>" by auto
    } moreover
    {
      assume "U\<in>{LeftRayX(X, r, b) . b \<in> X}"
      with lray have "f``U\<in>{LeftRayX(X, r, b) . b \<in> X}" by auto
      then have "f``U\<in>?\<BB>" by auto
    } moreover
    {
      assume "U\<in>{RightRayX(X,r,b). b\<in>X}"
      with rray have "f``U\<in>{RightRayX(X,r,b). b\<in>X}" by auto
      then have "f``U\<in>?\<BB>" by auto
    }
    moreover note A ultimately
    show "f``U\<in>?\<BB>" by auto
  qed
  from Ordtopology_is_a_topology(2) assms(1) have
    base:"?\<BB>{is a base for}(OrdTopology X r)" by auto
  then have r2:"?\<BB>\<subseteq>(OrdTopology X r)"
    using base_sets_open by blast
  {
    fix U assume "U\<in>?\<BB>"
    with r1 have "f``U\<in>?\<BB>"
      by auto
    with r2 have "f``U\<in>(OrdTopology X r)" by blast
  }
  then have "\<forall>U\<in>?\<BB>. f``U\<in>(OrdTopology X r)" by blast moreover
  from twoSpac have "\<And>U. ?\<BB> {is a base for} (OrdTopology X r) \<Longrightarrow>
    \<forall>B\<in>?\<BB>. f `` B \<in> (OrdTopology X r) \<Longrightarrow>
    U \<in> (OrdTopology X r) \<Longrightarrow> f `` U \<in> (OrdTopology X r)" using two_top_spaces0.base_image_open
    by auto
  ultimately have f_open:"\<forall>U\<in>(OrdTopology X r). f``U\<in>(OrdTopology X r)" using Ordtopology_is_a_topology(2) assms(1)
    by auto
  {
    fix c d assume A:"c\<in>X""d\<in>X"
    then obtain cc dd where pre:"f`cc=c""f`dd=d""cc\<in>X""dd\<in>X" using bij unfolding bij_def surj_def by blast
    with inter have "f `` IntervalX(X, r, cc, dd) = IntervalX(X, r,  c,  d)" by auto
    then have "f-``(f``IntervalX(X, r, cc, dd)) = f-``(IntervalX(X, r,  c,  d))" by auto 
    moreover
    have "IntervalX(X, r, cc, dd)\<subseteq>X" unfolding IntervalX_def by auto moreover
    have "f\<in>inj(X,X)" using bij unfolding bij_def by auto ultimately
    have "IntervalX(X, r, cc, dd)=f-``IntervalX(X, r,  c,  d)" using inj_vimage_image by auto
    moreover
    from pre(3,4) have "IntervalX(X, r, cc, dd)\<in>{IntervalX(X,r,e1,e2). \<langle>e1,e2\<rangle>\<in>X\<times>X}" by auto
    then have "IntervalX(X, r, cc, dd)\<in>?\<BB>" by auto
    with r2 have "IntervalX(X, r, cc, dd)\<in>(OrdTopology X r)" by blast
    ultimately have "f-``IntervalX(X, r,  c,  d)\<in>(OrdTopology X r)" by auto
  }
  then have inter:"\<forall>c\<in>X. \<forall>d\<in>X. f-``IntervalX(X, r,  c,  d)\<in>(OrdTopology X r)" by auto
  {
    fix c assume A:"c\<in>X"
    then obtain cc where pre:"f`cc=c""cc\<in>X" using bij unfolding bij_def surj_def by blast
    with rray have "f `` RightRayX(X, r, cc) = RightRayX(X, r,  c)" by auto
    then have "f-``(f``RightRayX(X, r, cc)) = f-``(RightRayX(X, r,  c))" by auto 
    moreover
    have "RightRayX(X, r, cc)\<subseteq>X" unfolding RightRayX_def by auto moreover
    have "f\<in>inj(X,X)" using bij unfolding bij_def by auto ultimately
    have "RightRayX(X, r, cc)=f-``RightRayX(X, r,  c)" using inj_vimage_image by auto
    moreover
    from pre(2) have "RightRayX(X, r, cc)\<in>{RightRayX(X,r,e2). e2\<in>X}" by auto
    ultimately have "f-``RightRayX(X, r,  c)\<in>(OrdTopology X r)" using
      r2 by auto
  }
  then have rray:"\<forall>c\<in>X. f-``RightRayX(X, r,  c)\<in>(OrdTopology X r)" by auto
  {
    fix c assume A:"c\<in>X"
    then obtain cc where pre:"f`cc=c""cc\<in>X" using bij unfolding bij_def surj_def by blast
    with lray have "f `` LeftRayX(X, r, cc) = LeftRayX(X, r,  c)" by auto
    then have "f-``(f``LeftRayX(X, r, cc)) = f-``(LeftRayX(X, r,  c))" by auto 
    moreover
    have "LeftRayX(X, r, cc)\<subseteq>X" unfolding LeftRayX_def by auto moreover
    have "f\<in>inj(X,X)" using bij unfolding bij_def by auto ultimately
    have "LeftRayX(X, r, cc)=f-``LeftRayX(X, r,  c)" using inj_vimage_image by auto
    moreover
    from pre(2) have "LeftRayX(X, r, cc)\<in>{LeftRayX(X,r,e2). e2\<in>X}" by auto
    ultimately have "f-``LeftRayX(X, r,  c)\<in>(OrdTopology X r)" using
     r2 by auto
  }
  then have lray:"\<forall>c\<in>X. f-``LeftRayX(X, r,  c)\<in>(OrdTopology X r)" by auto
  {
    fix U assume "U\<in>{IntervalX(X, r, b, c) . \<langle>b,c\<rangle> \<in> X \<times> X} \<union> {LeftRayX(X, r, b) . b \<in> X} \<union> {RightRayX(X, r, b) . b \<in> X}"
    with lray inter rray have "f-``U\<in>(OrdTopology X r)" by auto
  }
  then have "\<forall>U\<in>{IntervalX(X, r, b, c) . \<langle>b,c\<rangle> \<in> X \<times> X} \<union> {LeftRayX(X, r, b) . b \<in> X} \<union> {RightRayX(X, r, b) . b \<in> X}.
    f-``U\<in>(OrdTopology X r)" by blast
  from twoSpac base this have fcont:"IsContinuous(OrdTopology X r,OrdTopology X r,f)" 
    by (rule two_top_spaces0.Top_ZF_2_1_L5)
  from assms have "\<Union>(OrdTopology X r) = X" using union_ordtopology by auto
  with bij have b:"f\<in>bij(\<Union>(OrdTopology X r),\<Union>(OrdTopology X r))" by auto
  from this fcont f_open have "IsAhomeomorphism(OrdTopology X r,OrdTopology X r,f)" by (rule bij_cont_open_homeo)
  then show "f\<in>HomeoG(OrdTopology X r)" using b
    unfolding bij_def inj_def HomeoG_def by auto
qed
      
subsection\<open>Properties preserved by functions\<close>

text\<open>Continuous surjections preserve connectedness and compactness. As consequences,
quotient spaces of connected or compact spaces inherit those properties.\<close>

text\<open>The continuous surjective image of a connected space is connected.\<close>

theorem (in two_top_spaces0) cont_image_conn:
  assumes "IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2,f)" "f\<in>surj(X\<^sub>1,X\<^sub>2)" "\<tau>\<^sub>1{is connected}"
  shows "\<tau>\<^sub>2{is connected}"
proof-
  {
    fix U
    assume Uop:"U\<in>\<tau>\<^sub>2" and Ucl:"U{is closed in}\<tau>\<^sub>2"
    from Uop assms(1) have "f-``U\<in>\<tau>\<^sub>1" unfolding IsContinuous_def by auto moreover
    from Ucl assms(1) have  "f-``U{is closed in}\<tau>\<^sub>1" using TopZF_2_1_L1 by auto ultimately
    have disj:"f-``U=0 \<or> f-``U=\<Union>\<tau>\<^sub>1" using assms(3) unfolding IsConnected_def by auto moreover
    {
      assume as:"f-``U\<noteq>0"
      then have "U\<noteq>0" using func1_1_L13 by auto
      from as disj have "f-``U=\<Union>\<tau>\<^sub>1" by auto
      then have "f``(f-``U)=f``(\<Union>\<tau>\<^sub>1)" by auto moreover
      have "U\<subseteq>\<Union>\<tau>\<^sub>2" using Uop by blast ultimately
      have "U=f``(\<Union>\<tau>\<^sub>1)" using surj_image_vimage assms(2) Uop by force
      then have "\<Union>\<tau>\<^sub>2=U" using surj_range_image_domain assms(2) by auto
    }
    moreover
    {
      assume as:"U\<noteq>0"
      from Uop have s:"U\<subseteq>\<Union>\<tau>\<^sub>2" by auto
      with as obtain u where uU:"u\<in>U" by auto
      with s have "u\<in>\<Union>\<tau>\<^sub>2" by auto
      with assms(2) obtain w where "f`w=u""w\<in>\<Union>\<tau>\<^sub>1" unfolding surj_def X1_def X2_def by blast
      with uU have "w\<in>f-``U" using func1_1_L15 assms(2) unfolding surj_def by auto
      then have "f-``U\<noteq>0" by auto
    }
    ultimately have "U=0\<or>U=\<Union>\<tau>\<^sub>2" by auto
  }
  then show ?thesis unfolding IsConnected_def by auto
qed

text\<open>A continuous function from a connected space to a totally-disconnected space
must be constant.\<close>

corollary (in two_top_spaces0) cont_conn_tot_disc:
  assumes "IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2,f)" "\<tau>\<^sub>1{is connected}" "\<tau>\<^sub>2{is totally-disconnected}" "f:X\<^sub>1\<rightarrow>X\<^sub>2" "X\<^sub>1\<noteq>0"
  shows "\<exists>q\<in>X\<^sub>2. \<forall>w\<in>X\<^sub>1. f`(w)=q"
proof-
  from assms(4) have surj:"f\<in>surj(X\<^sub>1,range(f))" using fun_is_surj by auto
  have sub:"range(f)\<subseteq>X\<^sub>2" using func1_1_L5B assms(4) by auto
  from assms(1) have cont:"IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2{restricted to}range(f),f)" using restr_image_cont range_image_domain
    assms(4) by auto
  have union:"\<Union>(\<tau>\<^sub>2{restricted to}range(f))=range(f)" unfolding RestrictedTo_def using sub by auto
  then have "two_top_spaces0(\<tau>\<^sub>1,\<tau>\<^sub>2{restricted to}range(f),f)" 
    using surj  tau1_is_top topology0.Top_1_L4 tau2_is_top
    unfolding two_top_spaces0_def surj_def topology0_def
    by auto
  then have conn:"(\<tau>\<^sub>2{restricted to}range(f)){is connected}" using two_top_spaces0.cont_image_conn surj assms(2) cont
    union by auto
  then have "range(f){is in the spectrum of}IsConnected" using assms(3) sub union unfolding IsTotDis_def antiProperty_def
    by auto
  then have "range(f)\<lesssim>1" using conn_spectrum by auto moreover
  from assms(5) have "f``X\<^sub>1\<noteq>0" using func1_1_L15A assms(4) by auto
  then have "range(f)\<noteq>0" using range_image_domain assms(4) by auto
  ultimately obtain q where uniq:"range(f)={q}" using lepoll_1_is_sing by blast
  {
    fix w assume "w\<in>X\<^sub>1"
    then have "f`w\<in>range(f)" using func1_1_L5A(2) assms(4) by auto
    with uniq have "f`w=q" by auto
  }
  then have "\<forall>w\<in>X\<^sub>1. f`w=q" by auto
  then show ?thesis using uniq sub by auto
qed

text\<open>The continuous image of a compact space is compact.\<close>

theorem (in two_top_spaces0) cont_image_com:
  assumes "IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2,f)" "f\<in>surj(X\<^sub>1,X\<^sub>2)" "X\<^sub>1{is compact of cardinal}K{in}\<tau>\<^sub>1"
  shows "X\<^sub>2{is compact of cardinal}K{in}\<tau>\<^sub>2"
proof-
  have "X\<^sub>2\<subseteq>\<Union>\<tau>\<^sub>2" by auto moreover
  {
    fix U assume as:"X\<^sub>2\<subseteq>\<Union>U" "U\<subseteq>\<tau>\<^sub>2"
    then have P:"{f-``V. V\<in>U}\<subseteq>\<tau>\<^sub>1" using assms(1) unfolding IsContinuous_def by auto
    from as(1) have "f-``X\<^sub>2 \<subseteq> f-``(\<Union>U)" by blast
    then have "f-``X\<^sub>2 \<subseteq> converse(f)``(\<Union>U)" unfolding vimage_def by auto moreover
    have "converse(f)``(\<Union>U)=(\<Union>V\<in>U. converse(f)``V)" using image_UN by force ultimately
    have "f-``X\<^sub>2 \<subseteq> (\<Union>V\<in>U. converse(f)``V)" by auto
    then have "f-``X\<^sub>2 \<subseteq> (\<Union>V\<in>U. f-``V)" unfolding vimage_def by auto
    then have "X\<^sub>1 \<subseteq> (\<Union>V\<in>U. f-``V)" using func1_1_L4 assms(2) unfolding surj_def by force
    then have "X\<^sub>1 \<subseteq> \<Union>{f-``V. V\<in>U}" by auto
    with P assms(3) have "\<exists>N\<in>Pow({f-``V. V\<in>U}). X\<^sub>1 \<subseteq> \<Union>N \<and> N\<prec>K" unfolding IsCompactOfCard_def by auto
    then obtain N where N:"N\<in>Pow({f-``V. V\<in>U})" "X\<^sub>1 \<subseteq> \<Union>N" "N\<prec>K" by auto
    let ?FN = "{\<langle>R,f``R\<rangle>. R\<in>N}"
    have FN:"?FN:N\<rightarrow>{f``R. R\<in>N}" unfolding Pi_def function_def domain_def by auto
    {
      fix S assume "S\<in>{f``R. R\<in>N}"
      then obtain R where R_def:"R\<in>N""f``R=S" by auto
      then have "\<langle>R,f``R\<rangle>\<in>?FN" by auto
      then have "?FN`R=f``R" using FN apply_equality by auto
      then have "\<exists>R\<in>N. ?FN`R=S" using R_def by auto
    }
    then have surj:"?FN\<in>surj(N,{f``R. R\<in>N})" unfolding surj_def using FN by force
    from N have fin:"N\<prec>K" and sub:"N\<subseteq>{f-``V. V\<in>U}" and cov:"X\<^sub>1 \<subseteq> \<Union>N" unfolding FinPow_def by auto
    from sub have "{f``R. R\<in>N}\<subseteq>{f``(f-``V). V\<in>U}" by auto moreover
    have "\<forall>V\<in>U. V\<subseteq>\<Union>\<tau>\<^sub>2" using as(2) by auto ultimately
    have "{f``R. R\<in>N}\<subseteq>U" using surj_image_vimage assms(2) by auto moreover
    from fin have N:"N\<lesssim>K" "Ord(K)" using assms(3) lesspoll_imp_lepoll
      Card_is_Ord unfolding IsCompactOfCard_def by auto
    then have "{f``R. R\<in>N}\<lesssim>N" using surj_fun_inv_2 surj by auto
    then have "{f``R. R\<in>N}\<prec>K" using fin lesspoll_trans1 by blast
    moreover
    have "\<Union>{f``R. R\<in>N}=f``(\<Union>N)" using image_UN by auto
    then have "f``X\<^sub>1 \<subseteq> \<Union>{f``R. R\<in>N}" using cov by blast
    then have "X\<^sub>2 \<subseteq> \<Union>{f``R. R\<in>N}" using assms(2) surj_range_image_domain by auto
    ultimately have "\<exists>NN\<in>Pow(U). X\<^sub>2 \<subseteq> \<Union>NN \<and> NN\<prec>K" by auto
  }
  then have "\<forall>U\<in>Pow(\<tau>\<^sub>2). X\<^sub>2 \<subseteq> \<Union>U \<longrightarrow> (\<exists>NN\<in>Pow(U). X\<^sub>2 \<subseteq> \<Union>NN \<and> NN\<prec>K)" by auto
  ultimately show ?thesis using assms(3) unfolding IsCompactOfCard_def by auto
qed

text\<open>Analogously to the connected case, the continuous image of a compact space
in an anti-compact space is finite.\<close>

corollary (in two_top_spaces0) cont_comp_anti_comp:
  assumes "IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2,f)" "X\<^sub>1{is compact in}\<tau>\<^sub>1" "\<tau>\<^sub>2{is anti-compact}" "f:X\<^sub>1\<rightarrow>X\<^sub>2" "X\<^sub>1\<noteq>0"
  shows "Finite(range(f))" and "range(f)\<noteq>0"
proof-
  from assms(4) have surj:"f\<in>surj(X\<^sub>1,range(f))" using fun_is_surj by auto
  have sub:"range(f)\<subseteq>X\<^sub>2" using func1_1_L5B assms(4) by auto
  from assms(1) have cont:"IsContinuous(\<tau>\<^sub>1,\<tau>\<^sub>2{restricted to}range(f),f)"
    using restr_image_cont range_image_domain
    assms(4) by auto
  have union:"\<Union>(\<tau>\<^sub>2{restricted to}range(f))=range(f)" unfolding RestrictedTo_def using sub by auto
  then have "two_top_spaces0(\<tau>\<^sub>1,\<tau>\<^sub>2{restricted to}range(f),f)" 
    using surj tau1_is_top topology0.Top_1_L4 tau2_is_top
    unfolding surj_def topology0_def two_top_spaces0_def
    by auto
  then have "range(f){is compact in}(\<tau>\<^sub>2{restricted to}range(f))" using surj two_top_spaces0.cont_image_com cont union 
    assms(2) Compact_is_card_nat by force
  then have "range(f){is in the spectrum of}(\<lambda>T. (\<Union>T) {is compact in}T)" using assms(3) sub union
    unfolding IsAntiComp_def antiProperty_def
    by auto
  then show "Finite(range(f))" using compact_spectrum by auto
  from assms(5) have "f``X\<^sub>1\<noteq>0" using func1_1_L15A assms(4) by auto
  then show "range(f)\<noteq>0" using range_image_domain assms(4) by auto
qed

text\<open>A quotient of a compact space is compact.\<close>

corollary (in topology0) compQuot:
  assumes "(\<Union>T){is compact in}T" "equiv(\<Union>T,r)"
  shows "(\<Union>T)//r{is compact in}({quotient by}r)"
proof-
  have surj:"{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}\<in>surj(\<Union>T,(\<Union>T)//r)" using quotient_proj_surj by auto
  moreover have tot:"\<Union>({quotient by}r)=(\<Union>T)//r" using total_quo_equi assms(2) by auto
  ultimately have cont:"IsContinuous(T,{quotient by}r,{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T})" using quotient_func_cont
    EquivQuo_def assms(2) by auto
  from surj tot have "two_top_spaces0(T,{quotient by}r,{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T})" 
    using topSpaceAssum equiv_quo_is_top assms(2) unfolding surj_def two_top_spaces0_def by auto
  with surj cont tot assms(1) show ?thesis using two_top_spaces0.cont_image_com Compact_is_card_nat by force
qed

text\<open>A quotient of a connected space is connected.\<close>

corollary (in topology0) ConnQuot:
  assumes "T{is connected}" "equiv(\<Union>T,r)"
  shows "({quotient by}r){is connected}"
proof-
  have surj:"{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}\<in>surj(\<Union>T,(\<Union>T)//r)" using quotient_proj_surj by auto
  moreover have tot:"\<Union>({quotient by}r)=(\<Union>T)//r" using total_quo_equi assms(2) by auto
  ultimately have cont:"IsContinuous(T,{quotient by}r,{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T})" using quotient_func_cont
    EquivQuo_def assms(2) by auto
  from surj tot have "two_top_spaces0(T,{quotient by}r,{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T})"
    using topSpaceAssum equiv_quo_is_top assms(2) unfolding two_top_spaces0_def surj_def by auto
  with surj cont tot assms(1) show ?thesis using two_top_spaces0.cont_image_conn by force
qed

end
