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

section \<open>Properties in topology 2\<close>

theory Topology_ZF_properties_2 imports Topology_ZF_7 Topology_ZF_1b
  Finite_ZF_1 Topology_ZF_11

begin

subsection\<open>Local properties.\<close>
text\<open>This theory file deals with local topological properties; and applies local compactness
to the one point compactification.\<close>

text\<open>We will say that a topological space is locally @term{"P"} iff every point has a neighbourhood basis
of subsets that have the property @term{"P"} as subspaces.\<close>

definition
  IsLocally ("_{is locally}_" 90)
  where "T{is a topology} \<Longrightarrow> T{is locally}P \<equiv> (\<forall>x\<in>\<Union>T. \<forall>b\<in>T. x\<in>b \<longrightarrow> (\<exists>c\<in>Pow(b). x\<in>Interior(c,T) \<and> P(c,T)))"

subsection\<open>First examples\<close>
text\<open>Our first examples deal with the locally finite property. Finiteness is a property of sets,
and hence it is preserved by homeomorphisms; which are in particular bijective.\<close>

text\<open>The discrete topology is locally finite.\<close>

lemma discrete_locally_finite:
  shows "Pow(A){is locally}(\<lambda>A.(\<lambda>B. Finite(A)))"
proof-
  have "\<forall>b\<in>Pow(A). \<Union>(Pow(A){restricted to}b)=b" unfolding RestrictedTo_def by blast
  then have "\<forall>b\<in>{{x}. x\<in>A}. Finite(b)" by auto moreover
  have reg:"\<forall>S\<in>Pow(A). Interior(S,Pow(A))=S" unfolding Interior_def by auto
  {
    fix x b assume "x\<in>\<Union>Pow(A)" "b\<in>Pow(A)" "x\<in>b"
    then have "{x}\<subseteq>b" "x\<in>Interior({x},Pow(A))" "Finite({x})" using reg by auto
    then have "\<exists>c\<in>Pow(b). x\<in>Interior(c,Pow(A))\<and>Finite(c)" by blast
  }
  then have "\<forall>x\<in>\<Union>Pow(A). \<forall>b\<in>Pow(A). x\<in>b \<longrightarrow> (\<exists>c\<in>Pow(b). x\<in>Interior(c,Pow(A)) \<and> Finite(c))" by auto
  then show ?thesis using IsLocally_def[OF Pow_is_top] by auto
qed

text\<open>The included set topology is locally finite when the set is finite.\<close>

lemma included_finite_locally_finite:
  assumes "Finite(A)" and "A\<subseteq>X"
  shows "(IncludedSet(X,A)){is locally}(\<lambda>A.(\<lambda>B. Finite(A)))"
proof-
  have "\<forall>b\<in>Pow(X). b\<inter>A\<subseteq>b" by auto moreover
  note assms(1)
  ultimately have rr:"\<forall>b\<in>{A\<union>{x}. x\<in>X}. Finite(b)" by force
  {
    fix x b assume "x\<in>\<Union>(IncludedSet(X,A))" "b\<in>(IncludedSet(X,A))" "x\<in>b"
    then have "A\<union>{x}\<subseteq>b" "A\<union>{x}\<in>{A\<union>{x}. x\<in>X}" and sub: "b\<subseteq>X" unfolding IncludedSet_def by auto
    moreover have "A \<union> {x} \<subseteq> X" using assms(2) sub \<open>x\<in>b\<close> by auto
    then have "x\<in>Interior(A\<union>{x},IncludedSet(X,A))" using interior_set_includedset[of "A\<union>{x}""X""A"] by auto
    ultimately have "\<exists>c\<in>Pow(b). x\<in>Interior(c,IncludedSet(X,A))\<and> Finite(c)" using rr by blast
  }
  then have "\<forall>x\<in>\<Union>(IncludedSet(X,A)). \<forall>b\<in>(IncludedSet(X,A)). x\<in>b \<longrightarrow> (\<exists>c\<in>Pow(b). x\<in>Interior(c,IncludedSet(X,A))\<and> Finite(c))" by auto
  then show ?thesis using IsLocally_def includedset_is_topology by auto
qed

subsection\<open>Local compactness\<close>

definition
  IsLocallyComp ("_{is locally-compact}" 70)
  where "T{is locally-compact}\<equiv>T{is locally}(\<lambda>B. \<lambda>T. B{is compact in}T)"

text\<open>We center ourselves in local compactness, because it is a very important tool in topological groups
and compactifications.\<close>

text\<open>If a subset is compact of some cardinal for a topological space, it is compact of the same cardinal
in the subspace topology.\<close>

lemma compact_imp_compact_subspace:
  assumes "A{is compact of cardinal}K{in}T" "A\<subseteq>B"
  shows "A{is compact of cardinal}K{in}(T{restricted to}B)" unfolding IsCompactOfCard_def
proof
  from assms show C:"Card(K)" unfolding IsCompactOfCard_def by auto
  from assms have "A\<subseteq>\<Union>T" unfolding IsCompactOfCard_def by auto
  then have AA:"A\<subseteq>\<Union>(T{restricted to}B)" using assms(2) unfolding RestrictedTo_def by auto moreover
  {
    fix M assume "M\<in>Pow(T{restricted to}B)" "A\<subseteq>\<Union>M"
    let ?M="{S\<in>T. B\<inter>S\<in>M}"
    from \<open>M\<in>Pow(T{restricted to}B)\<close> have "\<Union>M\<subseteq>\<Union>?M" unfolding RestrictedTo_def by auto
    with \<open>A\<subseteq>\<Union>M\<close> have "A\<subseteq>\<Union>?M""?M\<in>Pow(T)" by auto
    with assms have "\<exists>N\<in>Pow(?M). A\<subseteq>\<Union>N\<and>N\<prec>K" unfolding IsCompactOfCard_def by auto
    then obtain N where "N\<in>Pow(?M)" "A\<subseteq>\<Union>N" "N\<prec>K" by auto
    then have "N{restricted to}B\<subseteq>M" unfolding RestrictedTo_def FinPow_def by auto
    moreover
    let ?f="{\<langle>\<BB>,B\<inter>\<BB>\<rangle>. \<BB>\<in>N}"
    have "?f:N\<rightarrow>(N{restricted to}B)" unfolding Pi_def function_def domain_def RestrictedTo_def by auto
    then have "?f\<in>surj(N,N{restricted to}B)" unfolding surj_def RestrictedTo_def using apply_equality
      by auto
    from \<open>N\<prec>K\<close> have "N\<lesssim>K" unfolding lesspoll_def by auto
    with \<open>?f\<in>surj(N,N{restricted to}B)\<close> have "N{restricted to}B\<lesssim>N" using surj_fun_inv_2 Card_is_Ord C by auto
    with \<open>N\<prec>K\<close> have "N{restricted to}B\<prec>K" using lesspoll_trans1 by auto
    moreover from \<open>A\<subseteq>\<Union>N\<close> have "A\<subseteq>\<Union>(N{restricted to}B)" using assms(2) unfolding RestrictedTo_def by auto
    ultimately have "\<exists>N\<in>Pow(M). A\<subseteq>\<Union>N \<and> N\<prec>K" by auto
  }
  with AA show "A \<subseteq> \<Union>(T {restricted to} B) \<and> (\<forall>M\<in>Pow(T {restricted to} B). A \<subseteq> \<Union>M \<longrightarrow> (\<exists>N\<in>Pow(M). A \<subseteq> \<Union>N \<and> N\<prec>K))" by auto
qed

text\<open>The converse of the previous result is not always true. For compactness, it holds because the axiom of finite choice
always holds.\<close>

lemma compact_subspace_imp_compact:
  assumes "A{is compact in}(T{restricted to}B)" "A\<subseteq>B"
  shows "A{is compact in}T" unfolding IsCompact_def
proof
  from assms show "A\<subseteq>\<Union>T" unfolding IsCompact_def RestrictedTo_def by auto
next
  {
    fix M assume "M\<in>Pow(T)" "A\<subseteq>\<Union>M"
    let ?M="M{restricted to}B"
    from \<open>M\<in>Pow(T)\<close> have "?M\<in>Pow(T{restricted to}B)" unfolding RestrictedTo_def by auto
    from \<open>A\<subseteq>\<Union>M\<close> have "A\<subseteq>\<Union>?M" unfolding RestrictedTo_def using assms(2) by auto
    with assms \<open>?M\<in>Pow(T{restricted to}B)\<close> obtain N where "N\<in>FinPow(?M)" "A\<subseteq>\<Union>N" unfolding IsCompact_def by blast
    from \<open>N\<in>FinPow(?M)\<close> have "N\<prec>nat" unfolding FinPow_def Finite_def using n_lesspoll_nat eq_lesspoll_trans
      by auto
    then have "Finite(N)" using lesspoll_nat_is_Finite by auto
    then obtain n where "n\<in>nat" "N\<approx>n" unfolding Finite_def by auto
    then have "N\<lesssim>n" using eqpoll_imp_lepoll by auto
    moreover 
    {
      fix BB assume "BB\<in>N"
      with \<open>N\<in>FinPow(?M)\<close> have "BB\<in>?M" unfolding FinPow_def by auto
      then obtain S where "S\<in>M" and "BB=B\<inter>S" unfolding RestrictedTo_def by auto
      then have "S\<in>{S\<in>M. B\<inter>S=BB}" by auto
      then obtain "{S\<in>M. B\<inter>S=BB}\<noteq>0" by auto
    }
    then have "\<forall>BB\<in>N. ((\<lambda>W\<in>N. {S\<in>M. B\<inter>S=W})`BB)\<noteq>0" by auto moreover
    from \<open>n\<in>nat\<close> have " (N \<lesssim> n \<and> (\<forall>t\<in>N. (\<lambda>W\<in>N. {S\<in>M. B\<inter>S=W}) ` t \<noteq> 0) \<longrightarrow> (\<exists>f. f \<in> Pi(N,\<lambda>t. (\<lambda>W\<in>N. {S\<in>M. B\<inter>S=W}) ` t) \<and> (\<forall>t\<in>N. f ` t \<in> (\<lambda>W\<in>N. {S\<in>M. B\<inter>S=W}) ` t)))" using finite_choice unfolding AxiomCardinalChoiceGen_def by blast
    ultimately
    obtain f where AA:"f\<in>Pi(N,\<lambda>t. (\<lambda>W\<in>N. {S\<in>M. B\<inter>S=W}) ` t)" "\<forall>t\<in>N. f`t\<in>(\<lambda>W\<in>N. {S\<in>M. B\<inter>S=W}) ` t" by blast
    from AA(2) have ss:"\<forall>t\<in>N. f`t\<in>{S\<in>M. B\<inter>S=t}" using beta_if by auto
    then have "{f`t. t\<in>N}\<subseteq>M" by auto
    {
      fix t assume "t\<in>N"
      with ss have "f`t\<in>{S\<in>M. B\<inter>S\<in>N}" by auto
    }
    with AA(1) have FF:"f:N\<rightarrow>{S\<in>M. B\<inter>S\<in>N}" unfolding Pi_def Sigma_def using beta_if by auto moreover
    {
      fix aa bb assume AAA:"aa\<in>N" "bb\<in>N" "f`aa=f`bb"
      from AAA(1) ss have "B\<inter> (f`aa) =aa" by auto
      with AAA(3) have "B\<inter>(f`bb)=aa" by auto
      with ss AAA(2) have "aa=bb" by auto
    }
    ultimately have "f\<in>inj(N,{S\<in>M. B\<inter>S\<in>N})" unfolding inj_def by auto
    then have "f\<in>bij(N,range(f))" using inj_bij_range by auto
    then have "f\<in>bij(N,f``N)" using range_image_domain FF by auto
    then have "f\<in>bij(N,{f`t. t\<in>N})" using func_imagedef FF by auto
    then have "N\<approx>{f`t. t\<in>N}" unfolding eqpoll_def by auto
    with \<open>N\<approx>n\<close> have "{f`t. t\<in>N}\<approx>n" using eqpoll_sym eqpoll_trans by blast
    with \<open>n\<in>nat\<close> have "Finite({f`t. t\<in>N})" unfolding Finite_def by auto
    with ss have "{f`t. t\<in>N}\<in>FinPow(M)" unfolding FinPow_def by auto moreover
    {
      fix aa assume "aa\<in>A"
      with \<open>A\<subseteq>\<Union>N\<close> obtain b where "b\<in>N" and "aa\<in>b" by auto
      with ss have "B\<inter>(f`b)=b" by auto
      with \<open>aa\<in>b\<close> have "aa\<in>B\<inter>(f`b)" by auto
      then have "aa\<in> f`b" by auto
      with \<open>b\<in>N\<close> have "aa\<in>\<Union>{f`t. t\<in>N}" by auto
    }
    then have "A\<subseteq>\<Union>{f`t. t\<in>N}" by auto ultimately
    have "\<exists>R\<in>FinPow(M). A\<subseteq>\<Union>R" by auto
  }
  then show "\<forall>M\<in>Pow(T). A \<subseteq> \<Union>M \<longrightarrow> (\<exists>N\<in>FinPow(M). A \<subseteq> \<Union>N)" by auto
qed

text\<open>If the axiom of choice holds for some cardinal,
then we can drop the compact sets of that cardial are compact of the same cardinal
as subspaces of every superspace.\<close>

lemma Kcompact_subspace_imp_Kcompact:
  assumes "A{is compact of cardinal}Q{in}(T{restricted to}B)" "A\<subseteq>B" "({the axiom of} Q {choice holds})"
  shows "A{is compact of cardinal}Q{in}T"
proof -
  from assms(1) have a1:"Card(Q)" unfolding IsCompactOfCard_def RestrictedTo_def by auto
  from assms(1) have a2:"A\<subseteq>\<Union>T" unfolding IsCompactOfCard_def RestrictedTo_def by auto
  {
    fix M assume "M\<in>Pow(T)" "A\<subseteq>\<Union>M"
    let ?M="M{restricted to}B"
    from \<open>M\<in>Pow(T)\<close> have "?M\<in>Pow(T{restricted to}B)" unfolding RestrictedTo_def by auto
    from \<open>A\<subseteq>\<Union>M\<close> have "A\<subseteq>\<Union>?M" unfolding RestrictedTo_def using assms(2) by auto
    with assms \<open>?M\<in>Pow(T{restricted to}B)\<close> obtain N where N:"N\<in>Pow(?M)" "A\<subseteq>\<Union>N" "N \<prec> Q" unfolding IsCompactOfCard_def by blast
    from N(3) have "N\<lesssim>Q" using lesspoll_imp_lepoll by auto moreover 
    {
      fix BB assume "BB\<in>N"
      with \<open>N\<in>Pow(?M)\<close> have "BB\<in>?M" unfolding FinPow_def by auto
      then obtain S where "S\<in>M" and "BB=B\<inter>S" unfolding RestrictedTo_def by auto
      then have "S\<in>{S\<in>M. B\<inter>S=BB}" by auto
      then obtain "{S\<in>M. B\<inter>S=BB}\<noteq>0" by auto
    }
    then have "\<forall>BB\<in>N. ((\<lambda>W\<in>N. {S\<in>M. B\<inter>S=W})`BB)\<noteq>0" by auto moreover
    have " (N \<lesssim> Q \<and> (\<forall>t\<in>N. (\<lambda>W\<in>N. {S\<in>M. B\<inter>S=W}) ` t \<noteq> 0) \<longrightarrow> (\<exists>f. f \<in> Pi(N,\<lambda>t. (\<lambda>W\<in>N. {S\<in>M. B\<inter>S=W}) ` t) \<and> (\<forall>t\<in>N. f ` t \<in> (\<lambda>W\<in>N. {S\<in>M. B\<inter>S=W}) ` t)))" 
      using assms(3) unfolding AxiomCardinalChoiceGen_def by blast
    ultimately
    obtain f where AA:"f\<in>Pi(N,\<lambda>t. (\<lambda>W\<in>N. {S\<in>M. B\<inter>S=W}) ` t)" "\<forall>t\<in>N. f`t\<in>(\<lambda>W\<in>N. {S\<in>M. B\<inter>S=W}) ` t" by blast
    from AA(2) have ss:"\<forall>t\<in>N. f`t\<in>{S\<in>M. B\<inter>S=t}" using beta_if by auto
    then have "{f`t. t\<in>N}\<subseteq>M" by auto
    {
      fix t assume "t\<in>N"
      with ss have "f`t\<in>{S\<in>M. B\<inter>S\<in>N}" by auto
    }
    with AA(1) have FF:"f:N\<rightarrow>{S\<in>M. B\<inter>S\<in>N}" unfolding Pi_def Sigma_def using beta_if by auto moreover
    {
      fix aa bb assume AAA:"aa\<in>N" "bb\<in>N" "f`aa=f`bb"
      from AAA(1) ss have "B\<inter> (f`aa) =aa" by auto
      with AAA(3) have "B\<inter>(f`bb)=aa" by auto
      with ss AAA(2) have "aa=bb" by auto
    }
    ultimately have "f\<in>inj(N,{S\<in>M. B\<inter>S\<in>N})" unfolding inj_def by auto
    then have "f\<in>bij(N,range(f))" using inj_bij_range by auto
    then have "f\<in>bij(N,f``N)" using range_image_domain FF by auto
    then have "f\<in>bij(N,{f`t. t\<in>N})" using func_imagedef FF by auto
    then have "N\<approx>{f`t. t\<in>N}" unfolding eqpoll_def by auto
    with \<open>N\<prec>Q\<close> have "{f`t. t\<in>N}\<prec>Q" using eqpoll_sym eq_lesspoll_trans by blast moreover
    with ss have "{f`t. t\<in>N}\<in>Pow(M)" unfolding FinPow_def by auto moreover
    {
      fix aa assume "aa\<in>A"
      with \<open>A\<subseteq>\<Union>N\<close> obtain b where "b\<in>N" and "aa\<in>b" by auto
      with ss have "B\<inter>(f`b)=b" by auto
      with \<open>aa\<in>b\<close> have "aa\<in>B\<inter>(f`b)" by auto
      then have "aa\<in> f`b" by auto
      with \<open>b\<in>N\<close> have "aa\<in>\<Union>{f`t. t\<in>N}" by auto
    }
    then have "A\<subseteq>\<Union>{f`t. t\<in>N}" by auto ultimately
    have "\<exists>R\<in>Pow(M). A\<subseteq>\<Union>R \<and> R\<prec>Q" by auto
  }
  then show ?thesis using a1 a2 unfolding IsCompactOfCard_def by auto
qed

text\<open>Every set, with the cofinite topology is compact.\<close>

lemma cofinite_compact:
  shows "X {is compact in}(CoFinite X)" unfolding IsCompact_def
proof
  show "X\<subseteq>\<Union>(CoFinite X)" using union_cocardinal unfolding Cofinite_def by auto
next
  {
    fix M assume "M\<in>Pow(CoFinite X)" "X\<subseteq>\<Union>M"
    {
      assume "M=0\<or>M={0}"
      then have "M\<in>FinPow(M)" unfolding FinPow_def by auto
      with \<open>X\<subseteq>\<Union>M\<close> have "\<exists>N\<in>FinPow(M). X\<subseteq>\<Union>N" by auto
    }
    moreover
    {
      assume "M\<noteq>0""M\<noteq>{0}"
      then obtain U where "U\<in>M""U\<noteq>0" by auto
      with \<open>M\<in>Pow(CoFinite X)\<close> have "U\<in>CoFinite X" by auto
      with \<open>U\<noteq>0\<close> have "U\<subseteq>X" "(X-U)\<prec>nat" unfolding Cofinite_def CoCardinal_def by auto
      then have "Finite(X-U)" using lesspoll_nat_is_Finite by auto
      then have "(X-U){is in the spectrum of}(\<lambda>T. (\<Union>T){is compact in}T)" using compact_spectrum
        by auto
      then have "((\<Union>(CoFinite (X-U)))\<approx>X-U) \<longrightarrow> ((\<Union>(CoFinite (X-U))){is compact in}(CoFinite (X-U)))" unfolding Spec_def
        using InfCard_nat CoCar_is_topology unfolding Cofinite_def by auto
      then have com:"(X-U){is compact in}(CoFinite (X-U))" using union_cocardinal unfolding Cofinite_def by auto
      have "(X-U)\<inter>X=X-U" by auto
      then have "(CoFinite X){restricted to}(X-U)=(CoFinite (X-U))" using subspace_cocardinal unfolding Cofinite_def by auto
      with com have "(X-U){is compact in}(CoFinite X)" using compact_subspace_imp_compact[of "X-U""CoFinite X""X-U"] by auto
      moreover have "X-U\<subseteq>\<Union>M" using \<open>X\<subseteq>\<Union>M\<close> by auto
      moreover note \<open>M\<in>Pow(CoFinite X)\<close>
      ultimately have "\<exists>N\<in>FinPow(M). X-U\<subseteq>\<Union>N" unfolding IsCompact_def by auto
      then obtain N where "N\<subseteq>M" "Finite(N)" "X-U\<subseteq>\<Union>N" unfolding FinPow_def by auto
      with \<open>U\<in>M\<close> have "N \<union>{U}\<subseteq>M" "Finite(N \<union>{U})" "X\<subseteq>\<Union>(N \<union>{U})" by auto
      then have "\<exists>N\<in>FinPow(M). X\<subseteq>\<Union>N" unfolding FinPow_def by blast
    }
    ultimately
    have "\<exists>N\<in>FinPow(M). X\<subseteq>\<Union>N" by auto
  }
  then show "\<forall>M\<in>Pow(CoFinite X). X \<subseteq> \<Union>M \<longrightarrow> (\<exists>N\<in>FinPow(M). X \<subseteq> \<Union>N)" by auto
qed

text\<open>A corollary is then that the cofinite topology is locally compact; since every subspace
of a cofinite space is cofinite.\<close>

corollary cofinite_locally_compact:
  shows "(CoFinite X){is locally-compact}"
proof-
  have cof:"topology0(CoFinite X)" and cof1:"(CoFinite X){is a topology}" 
    using CoCar_is_topology InfCard_nat Cofinite_def unfolding topology0_def by auto
  {
    fix x B assume "x\<in>\<Union>(CoFinite X)" "B\<in>(CoFinite X)" "x\<in>B"
    then have "x\<in>Interior(B,CoFinite X)" using topology0.Top_2_L3[OF cof] by auto moreover
    from \<open>B\<in>(CoFinite X)\<close> have "B\<subseteq>X" unfolding Cofinite_def CoCardinal_def by auto
    then have "B\<inter>X=B" by auto
    then have "(CoFinite X){restricted to}B=CoFinite B" using subspace_cocardinal unfolding Cofinite_def by auto
    then have "B{is compact in}((CoFinite X){restricted to}B)" using cofinite_compact
      union_cocardinal unfolding Cofinite_def by auto
    then have "B{is compact in}(CoFinite X)" using compact_subspace_imp_compact by auto
    ultimately have "\<exists>c\<in>Pow(B). x\<in>Interior(c,CoFinite X)\<and> c{is compact in}(CoFinite X)" by auto
  }
  then have "(\<forall>x\<in>\<Union>(CoFinite X). \<forall>b\<in>(CoFinite X). x\<in>b \<longrightarrow> (\<exists>c\<in>Pow(b). x\<in>Interior(c,CoFinite X) \<and> c{is compact in}(CoFinite X)))"
    by auto
  then show ?thesis unfolding IsLocallyComp_def IsLocally_def[OF cof1] by auto
qed

text\<open>In every locally compact space, by definition, every point has a compact neighbourhood.\<close>

theorem (in topology0) locally_compact_exist_compact_neig:
  assumes "T{is locally-compact}"
  shows "\<forall>x\<in>\<Union>T. \<exists>A\<in>Pow(\<Union>T). A{is compact in}T \<and> x\<in>int(A)"
proof-
  {
    fix x assume "x\<in>\<Union>T" moreover
    then have "\<Union>T\<noteq>0" by auto
    have "\<Union>T\<in>T" using union_open topSpaceAssum by auto
    ultimately have "\<exists>c\<in>Pow(\<Union>T). x\<in>int(c)\<and> c{is compact in}T" using assms 
      IsLocally_def topSpaceAssum unfolding IsLocallyComp_def by auto
    then have "\<exists>c\<in>Pow(\<Union>T). c{is compact in}T \<and> x\<in>int(c)" by auto
  }
  then show ?thesis by auto
qed

text\<open>In Hausdorff spaces, the previous result is an equivalence.\<close>

theorem (in topology0) exist_compact_neig_T2_imp_locally_compact:
  assumes "\<forall>x\<in>\<Union>T. \<exists>A\<in>Pow(\<Union>T). x\<in>int(A) \<and> A{is compact in}T" "T{is T\<^sub>2}"
  shows "T{is locally-compact}"
proof-
  {
    fix x assume "x\<in>\<Union>T"
    with assms(1) obtain A where "A\<in>Pow(\<Union>T)" "x\<in>int(A)" and Acom:"A{is compact in}T" by blast
    then have Acl:"A{is closed in}T" using in_t2_compact_is_cl assms(2) by auto
    then have sub:"A\<subseteq>\<Union>T" unfolding IsClosed_def by auto
    {
      fix U assume "U\<in>T" "x\<in>U"
      let ?V="int(A\<inter>U)"
      from \<open>x\<in>U\<close> \<open>x\<in>int(A)\<close> have "x\<in>U\<inter>(int (A))" by auto
      moreover from \<open>U\<in>T\<close> have "U\<inter>(int(A))\<in>T" using Top_2_L2 topSpaceAssum unfolding IsATopology_def
        by auto moreover
      have "U\<inter>(int(A))\<subseteq>A\<inter>U" using Top_2_L1 by auto
      ultimately have "x\<in>?V" using Top_2_L5 by blast
      have "?V\<subseteq>A" using Top_2_L1 by auto
      then have "cl(?V)\<subseteq>A" using Acl Top_3_L13 by auto
      then have "A\<inter>cl(?V)=cl(?V)" by auto moreover
      have clcl:"cl(?V){is closed in}T" using cl_is_closed \<open>?V\<subseteq>A\<close> \<open>A\<subseteq>\<Union>T\<close> by auto
      ultimately have comp:"cl(?V){is compact in}T" using Acom compact_closed[of "A""nat""T""cl(?V)"] Compact_is_card_nat
        by auto
      {
        then have "cl(?V){is compact in}(T{restricted to}cl(?V))" using compact_imp_compact_subspace[of "cl(?V)""nat""T"] Compact_is_card_nat
          by auto moreover
        have "\<Union>(T{restricted to}cl(?V))=cl(?V)" unfolding RestrictedTo_def using clcl unfolding IsClosed_def by auto moreover
        ultimately have "(\<Union>(T{restricted to}cl(?V))){is compact in}(T{restricted to}cl(?V))" by auto
      }
      then have "(\<Union>(T{restricted to}cl(?V))){is compact in}(T{restricted to}cl(?V))" by auto moreover
      have "(T{restricted to}cl(?V)){is T\<^sub>2}" using assms(2) T2_here clcl unfolding IsClosed_def by auto
      ultimately have "(T{restricted to}cl(?V)){is T\<^sub>4}" using topology0.T2_compact_is_normal unfolding topology0_def
        using Top_1_L4 unfolding isT4_def using T2_is_T1 by auto
      then have clvreg:"(T{restricted to}cl(?V)){is regular}" using topology0.T4_is_T3 unfolding topology0_def isT3_def using Top_1_L4
        by auto 
      have "?V\<subseteq>cl(?V)" using cl_contains_set \<open>?V\<subseteq>A\<close> \<open>A\<subseteq>\<Union>T\<close> by auto
      then have "?V\<in>(T{restricted to}cl(?V))" unfolding RestrictedTo_def using Top_2_L2 by auto
      with \<open>x\<in>?V\<close> obtain W where Wop:"W\<in>(T{restricted to}cl(?V))" and clcont:"Closure(W,(T{restricted to}cl(?V)))\<subseteq>?V" and cinW:"x\<in>W"
      using topology0.regular_imp_exist_clos_neig unfolding topology0_def using Top_1_L4 clvreg
        by blast
      from clcont Wop have "W\<subseteq>?V" using topology0.cl_contains_set unfolding topology0_def using Top_1_L4 by auto
      with Wop have "W\<in>(T{restricted to}cl(?V)){restricted to}?V" unfolding RestrictedTo_def by auto
      moreover from \<open>?V\<subseteq>A\<close> \<open>A\<subseteq>\<Union>T\<close> have "?V\<subseteq>\<Union>T" by auto
      then have "?V\<subseteq>cl(?V)""cl(?V)\<subseteq>\<Union>T" using \<open>?V\<subseteq>cl(?V)\<close> Top_3_L11(1) by auto
      then have "(T{restricted to}cl(?V)){restricted to}?V=(T{restricted to}?V)" using subspace_of_subspace by auto
      ultimately have "W\<in>(T{restricted to}?V)" by auto
      then obtain UU where "UU\<in>T" "W=UU\<inter>?V" unfolding RestrictedTo_def by auto
      then have "W\<in>T" using Top_2_L2 topSpaceAssum unfolding IsATopology_def by auto moreover
      have "W\<subseteq>Closure(W,(T{restricted to}cl(?V)))" using topology0.cl_contains_set unfolding topology0_def
        using Top_1_L4 Wop by auto
      ultimately have A1:"x\<in>int(Closure(W,(T{restricted to}cl(?V))))" using Top_2_L6 cinW by auto
      from clcont have A2:"Closure(W,(T{restricted to}cl(?V)))\<subseteq>U" using Top_2_L1 by auto
      have clwcl:"Closure(W,(T{restricted to}cl(?V))) {is closed in}(T{restricted to}cl(?V))"
        using topology0.cl_is_closed Top_1_L4 Wop unfolding topology0_def by auto
      from comp have "cl(?V){is compact in}(T{restricted to}cl(?V))" using compact_imp_compact_subspace[of "cl(?V)""nat""T"] Compact_is_card_nat
          by auto
      with clwcl have "((cl(?V)\<inter>(Closure(W,(T{restricted to}cl(?V)))))){is compact in}(T{restricted to}cl(?V))"
        using compact_closed Compact_is_card_nat by auto moreover
      from clcont have cont:"(Closure(W,(T{restricted to}cl(?V))))\<subseteq>cl(?V)" using cl_contains_set \<open>?V\<subseteq>A\<close>\<open>A\<subseteq>\<Union>T\<close>
        by blast
      then have "((cl(?V)\<inter>(Closure(W,(T{restricted to}cl(?V))))))=Closure(W,(T{restricted to}cl(?V)))" by auto
      ultimately have "Closure(W,(T{restricted to}cl(?V))){is compact in}(T{restricted to}cl(?V))" by auto
      then have "Closure(W,(T{restricted to}cl(?V))){is compact in}T" using compact_subspace_imp_compact[of "Closure(W,T{restricted to}cl(?V))"]
        cont by auto
      with A1 A2 have "\<exists>c\<in>Pow(U). x\<in>int(c)\<and>c{is compact in}T" by auto
    }
    then have "\<forall>U\<in>T. x\<in>U \<longrightarrow> (\<exists>c\<in>Pow(U). x\<in>int(c)\<and>c{is compact in}T)" by auto
  }
  then show ?thesis unfolding IsLocally_def[OF topSpaceAssum] IsLocallyComp_def by auto
qed

subsection\<open>Compactification by one point\<close>

text\<open>Given a topological space, we can always add one point to the space and get a new compact topology; as we
will check in this section.\<close>

definition 
  OPCompactification ("{one-point compactification of}_" 90)
  where "{one-point compactification of}T\<equiv>T\<union>{{\<Union>T}\<union>((\<Union>T)-K). K\<in>{B\<in>Pow(\<Union>T). B{is compact in}T \<and> B{is closed in}T}}"

text\<open>Firstly, we check that what we defined is indeed a topology.\<close>

theorem (in topology0) op_comp_is_top:
  shows "({one-point compactification of}T){is a topology}" unfolding IsATopology_def
proof(safe)
  fix M assume "M\<subseteq>{one-point compactification of}T"
  then have disj:"M\<subseteq>T\<union>{{\<Union>T}\<union>((\<Union>T)-K). K\<in>{B\<in>Pow(\<Union>T). B{is compact in}T \<and> B{is closed in}T}}" unfolding OPCompactification_def by auto
  let ?MT="{A\<in>M. A\<in>T}"
  have "?MT\<subseteq>T" by auto
  then have c1:"\<Union>?MT\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
  let ?MK="{A\<in>M. A\<notin>T}"
  have "\<Union>M=\<Union>?MK \<union> \<Union>?MT" by auto
  from disj have "?MK\<subseteq>{A\<in>M. A\<in>{{\<Union>T}\<union>((\<Union>T)-K). K\<in>{B\<in>Pow(\<Union>T). B{is compact in}T \<and> B{is closed in}T}}}" by auto
  moreover have N:"\<Union>T\<notin>(\<Union>T)" using mem_not_refl by auto
  {
    fix B assume "B\<in>M" "B\<in>{{\<Union>T}\<union>((\<Union>T)-K). K\<in>{B\<in>Pow(\<Union>T). B{is compact in}T \<and> B{is closed in}T}}"
    then obtain K where "K\<in>Pow(\<Union>T)" "B={\<Union>T}\<union>((\<Union>T)-K)" by auto
    with N have "\<Union>T\<in>B" by auto
    with N have "B\<notin>T" by auto
    with \<open>B\<in>M\<close> have "B\<in>?MK" by auto
  }
  then have "{A\<in>M. A\<in>{{\<Union>T}\<union>((\<Union>T)-K). K\<in>{B\<in>Pow(\<Union>T). B{is compact in}T \<and> B{is closed in}T}}}\<subseteq>?MK" by auto
  ultimately have MK_def:"?MK={A\<in>M. A\<in>{{\<Union>T}\<union>((\<Union>T)-K). K\<in>{B\<in>Pow(\<Union>T). B{is compact in}T \<and> B{is closed in}T}}}" by auto
  let ?KK="{K\<in>Pow(\<Union>T). {\<Union>T}\<union>((\<Union>T)-K)\<in>?MK}"
  {
    assume "?MK=0"
    then have "\<Union>M=\<Union>?MT" by auto
    then have "\<Union>M\<in>T" using c1 by auto
    then have "\<Union>M\<in>{one-point compactification of}T" unfolding OPCompactification_def by auto
  }
  moreover
  {
    assume "?MK\<noteq>0"
    then obtain A where "A\<in>?MK" by auto
    then obtain K1 where "A={\<Union>T}\<union>((\<Union>T)-K1)" "K1\<in>Pow(\<Union>T)" "K1{is closed in}T" "K1{is compact in}T" using MK_def by auto
    with \<open>A\<in>?MK\<close> have "\<Inter>?KK\<subseteq>K1" by auto
    from \<open>A\<in>?MK\<close> \<open>A={\<Union>T}\<union>((\<Union>T)-K1)\<close> \<open>K1\<in>Pow(\<Union>T)\<close> have "?KK\<noteq>0" by blast
    {
      fix K assume "K\<in>?KK"
      then have "{\<Union>T}\<union>((\<Union>T)-K)\<in>?MK" "K\<subseteq>\<Union>T" by auto
      then obtain KK where A:"{\<Union>T}\<union>((\<Union>T)-K)={\<Union>T}\<union>((\<Union>T)-KK)" "KK\<subseteq>\<Union>T" "KK{is compact in}T" "KK{is closed in}T" using MK_def by auto
      note A(1) moreover
      have "(\<Union>T)-K\<subseteq>{\<Union>T}\<union>((\<Union>T)-K)" "(\<Union>T)-KK\<subseteq>{\<Union>T}\<union>((\<Union>T)-KK)" by auto
      ultimately have "(\<Union>T)-K\<subseteq>{\<Union>T}\<union>((\<Union>T)-KK)" "(\<Union>T)-KK\<subseteq>{\<Union>T}\<union>((\<Union>T)-K)" by auto moreover
      from N have "\<Union>T\<notin>(\<Union>T)-K" "\<Union>T\<notin>(\<Union>T)-KK" by auto ultimately
      have "(\<Union>T)-K\<subseteq>((\<Union>T)-KK)" "(\<Union>T)-KK\<subseteq>((\<Union>T)-K)" by auto
      then have "(\<Union>T)-K=(\<Union>T)-KK" by auto moreover
      from \<open>K\<subseteq>\<Union>T\<close> have "K=(\<Union>T)-((\<Union>T)-K)" by auto ultimately
      have "K=(\<Union>T)-((\<Union>T)-KK)" by auto
      with \<open>KK\<subseteq>\<Union>T\<close> have "K=KK" by auto
      with A(4) have "K{is closed in}T" by auto
    }
    then have "\<forall>K\<in>?KK. K{is closed in}T" by auto
    with \<open>?KK\<noteq>0\<close> have "(\<Inter>?KK){is closed in}T" using Top_3_L4 by auto
    with \<open>K1{is compact in}T\<close> have "(K1\<inter>(\<Inter>?KK)){is compact in}T" using Compact_is_card_nat
      compact_closed[of "K1""nat""T""\<Inter>?KK"] by auto moreover
    from \<open>\<Inter>?KK\<subseteq>K1\<close> have "K1\<inter>(\<Inter>?KK)=(\<Inter>?KK)" by auto ultimately
    have "(\<Inter>?KK){is compact in}T" by auto
    with \<open>(\<Inter>?KK){is closed in}T\<close> \<open>\<Inter>?KK\<subseteq>K1\<close> \<open>K1\<in>Pow(\<Union>T)\<close> have "({\<Union>T}\<union>((\<Union>T)-(\<Inter>?KK)))\<in>({one-point compactification of}T)"
      unfolding OPCompactification_def by blast
    have t:"\<Union>?MK=\<Union>{A\<in>M. A\<in>{{\<Union>T}\<union>((\<Union>T)-K). K\<in>{B\<in>Pow(\<Union>T). B{is compact in}T \<and> B{is closed in}T}}}"
      using MK_def by auto
    {
      fix x assume "x\<in>\<Union>?MK"
      with t have "x\<in>\<Union>{A\<in>M. A\<in>{{\<Union>T}\<union>((\<Union>T)-K). K\<in>{B\<in>Pow(\<Union>T). B{is compact in}T \<and> B{is closed in}T}}}" by auto 
      then have "\<exists>AA\<in>{A\<in>M. A\<in>{{\<Union>T}\<union>((\<Union>T)-K). K\<in>{B\<in>Pow(\<Union>T). B{is compact in}T \<and> B{is closed in}T}}}. x\<in>AA"
        using Union_iff by auto
      then obtain AA where AAp:"AA\<in>{A\<in>M. A\<in>{{\<Union>T}\<union>((\<Union>T)-K). K\<in>{B\<in>Pow(\<Union>T). B{is compact in}T \<and> B{is closed in}T}}}" "x\<in>AA" by auto
      then obtain K2 where "AA={\<Union>T}\<union>((\<Union>T)-K2)" "K2\<in>Pow(\<Union>T)""K2{is compact in}T" "K2{is closed in}T" by auto
      with \<open>x\<in>AA\<close> have "x=\<Union>T \<or> (x\<in>(\<Union>T) \<and> x\<notin>K2)" by auto
      from \<open>K2\<in>Pow(\<Union>T)\<close> \<open>AA={\<Union>T}\<union>((\<Union>T)-K2)\<close> AAp(1) MK_def have "K2\<in>?KK" by auto
      then have "\<Inter>?KK\<subseteq>K2" by auto
      with \<open>x=\<Union>T \<or> (x\<in>(\<Union>T) \<and> x\<notin>K2)\<close> have "x=\<Union>T\<or>(x\<in>\<Union>T \<and> x\<notin>\<Inter>?KK)" by auto
     then have "x\<in>{\<Union>T}\<union>((\<Union>T)-(\<Inter>?KK))" by auto
    }
    then have "\<Union>?MK\<subseteq>{\<Union>T}\<union>((\<Union>T)-(\<Inter>?KK))" by auto
    moreover
    {
      fix x assume "x\<in>{\<Union>T}\<union>((\<Union>T)-(\<Inter>?KK))"
      then have "x=\<Union>T\<or>(x\<in>(\<Union>T)\<and> x\<notin>\<Inter>?KK)" by auto
      with \<open>?KK\<noteq>0\<close> obtain K2 where "K2\<in>?KK" "x=\<Union>T\<or>(x\<in>\<Union>T\<and> x\<notin>K2)" by auto
      then have "{\<Union>T}\<union>((\<Union>T)-K2)\<in>?MK" by auto
      with \<open>x=\<Union>T\<or>(x\<in>\<Union>T\<and> x\<notin>K2)\<close> have "x\<in>\<Union>?MK" by auto
    }
    then have "{\<Union>T}\<union>((\<Union>T)-(\<Inter>?KK))\<subseteq>\<Union>?MK" by (safe,auto)
    ultimately have "\<Union>?MK={\<Union>T}\<union>((\<Union>T)-(\<Inter>?KK))" by blast
    from \<open>\<Union>?MT\<in>T\<close> have "\<Union>T-(\<Union>T-\<Union>?MT)=\<Union>?MT" by auto
    with \<open>\<Union>?MT\<in>T\<close> have "(\<Union>T-\<Union>?MT){is closed in}T" unfolding IsClosed_def by auto
    have "((\<Union>T)-(\<Inter>?KK))\<union>(\<Union>T-(\<Union>T-\<Union>?MT))=(\<Union>T)-((\<Inter>?KK)\<inter>(\<Union>T-\<Union>?MT))" by auto
    then have "({\<Union>T}\<union>((\<Union>T)-(\<Inter>?KK)))\<union>(\<Union>T-(\<Union>T-\<Union>?MT))={\<Union>T}\<union>((\<Union>T)-((\<Inter>?KK)\<inter>(\<Union>T-\<Union>?MT)))" by auto
    with \<open>\<Union>?MK={\<Union>T}\<union>((\<Union>T)-(\<Inter>?KK))\<close>\<open>\<Union>T-(\<Union>T-\<Union>?MT)=\<Union>?MT\<close> have "\<Union>?MK\<union>\<Union>?MT={\<Union>T}\<union>((\<Union>T)-((\<Inter>?KK)\<inter>(\<Union>T-\<Union>?MT)))"
    by auto
    with \<open>\<Union>M=\<Union>?MK \<union>\<Union>?MT\<close> have unM:"\<Union>M={\<Union>T}\<union>((\<Union>T)-((\<Inter>?KK)\<inter>(\<Union>T-\<Union>?MT)))" by auto
    have "((\<Inter>?KK)\<inter>(\<Union>T-\<Union>?MT)) {is closed in}T" using \<open>(\<Inter>?KK){is closed in}T\<close>\<open>(\<Union>T-(\<Union>?MT)){is closed in}T\<close>
      Top_3_L5 by auto
    moreover  
    note \<open>(\<Union>T-(\<Union>?MT)){is closed in}T\<close> \<open>(\<Inter>?KK){is compact in}T\<close>
    then have "((\<Inter>?KK)\<inter>(\<Union>T-\<Union>?MT)){is compact of cardinal}nat{in}T" using compact_closed[of "\<Inter>?KK""nat""T""(\<Union>T-\<Union>?MT)"] Compact_is_card_nat
      by auto
    then have "((\<Inter>?KK)\<inter>(\<Union>T-\<Union>?MT)){is compact in}T" using Compact_is_card_nat by auto
    ultimately have "{\<Union>T}\<union>(\<Union>T-((\<Inter>?KK)\<inter>(\<Union>T-\<Union>?MT)))\<in>{one-point compactification of}T"
      unfolding OPCompactification_def IsClosed_def by auto
    with unM have "\<Union>M\<in>{one-point compactification of}T" by auto
  }
  ultimately show "\<Union>M\<in>{one-point compactification of}T" by auto
next
  fix U V assume "U\<in>{one-point compactification of}T" and "V\<in>{one-point compactification of}T"
  then have A:"U\<in>T\<or>(\<exists>KU\<in>Pow(\<Union>T). U={\<Union>T}\<union>(\<Union>T-KU)\<and>KU{is closed in}T\<and>KU{is compact in}T)"
    "V\<in>T\<or>(\<exists>KV\<in>Pow(\<Union>T). V={\<Union>T}\<union>(\<Union>T-KV)\<and>KV{is closed in}T\<and>KV{is compact in}T)" unfolding OPCompactification_def
    by auto
 have N:"\<Union>T\<notin>(\<Union>T)" using mem_not_refl by auto
  {
    assume "U\<in>T""V\<in>T"
    then have "U\<inter>V\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
    then have "U\<inter>V\<in>{one-point compactification of}T" unfolding OPCompactification_def
    by auto
  }
  moreover
  {
    assume "U\<in>T""V\<notin>T"
    then obtain KV where V:"KV{is closed in}T""KV{is compact in}T""V={\<Union>T}\<union>(\<Union>T-KV)"
    using A(2) by auto
    with N \<open>U\<in>T\<close> have "\<Union>T\<notin>U" by auto
    then have "\<Union>T\<notin>U\<inter>V" by auto
    then have "U\<inter>V=U\<inter>(\<Union>T-KV)" using V(3) by auto
    moreover have "\<Union>T-KV\<in>T" using V(1) unfolding IsClosed_def by auto
    with \<open>U\<in>T\<close> have "U\<inter>(\<Union>T-KV)\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
    with \<open>U\<inter>V=U\<inter>(\<Union>T-KV)\<close> have "U\<inter>V\<in>T" by auto
    then have "U\<inter>V\<in>{one-point compactification of}T" unfolding OPCompactification_def by auto
    }
  moreover
  {
    assume "U\<notin>T""V\<in>T"
    then obtain KV where V:"KV{is closed in}T""KV{is compact in}T""U={\<Union>T}\<union>(\<Union>T-KV)"
    using A(1) by auto
    with N \<open>V\<in>T\<close> have "\<Union>T\<notin>V" by auto
    then have "\<Union>T\<notin>U\<inter>V" by auto
    then have "U\<inter>V=(\<Union>T-KV)\<inter>V" using V(3) by auto
    moreover have "\<Union>T-KV\<in>T" using V(1) unfolding IsClosed_def by auto
    with \<open>V\<in>T\<close> have "(\<Union>T-KV)\<inter>V\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
    with \<open>U\<inter>V=(\<Union>T-KV)\<inter>V\<close> have "U\<inter>V\<in>T" by auto
    then have "U\<inter>V\<in>{one-point compactification of}T" unfolding OPCompactification_def by auto
  }
  moreover
  {
    assume "U\<notin>T""V\<notin>T"
    then obtain KV KU where V:"KV{is closed in}T""KV{is compact in}T""V={\<Union>T}\<union>(\<Union>T-KV)"
     and U:"KU{is closed in}T""KU{is compact in}T""U={\<Union>T}\<union>(\<Union>T-KU)"
    using A by auto
    with V(3) U(3) have "\<Union>T\<in>U\<inter>V" by auto
    then have "U\<inter>V={\<Union>T}\<union>((\<Union>T-KV)\<inter>(\<Union>T-KU))" using V(3) U(3) by auto
    moreover have "\<Union>T-KV\<in>T""\<Union>T-KU\<in>T" using V(1) U(1) unfolding IsClosed_def by auto
    then have "(\<Union>T-KV)\<inter>(\<Union>T-KU)\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
    then have "(\<Union>T-KV)\<inter>(\<Union>T-KU)=\<Union>T-(\<Union>T-((\<Union>T-KV)\<inter>(\<Union>T-KU)))" by auto moreover
    with \<open>(\<Union>T-KV)\<inter>(\<Union>T-KU)\<in>T\<close> have "(\<Union>T-(\<Union>T-KV)\<inter>(\<Union>T-KU)){is closed in}T" unfolding IsClosed_def
      by auto moreover
    from V(1) U(1) have "(\<Union>T-(\<Union>T-KV)\<inter>(\<Union>T-KU))=KV\<union>KU" unfolding IsClosed_def by auto
    with V(2) U(2) have "(\<Union>T-(\<Union>T-KV)\<inter>(\<Union>T-KU)){is compact in}T" using union_compact[of "KV""nat""T""KU"] Compact_is_card_nat
      InfCard_nat by auto ultimately
    have "U\<inter>V\<in>{one-point compactification of}T" unfolding OPCompactification_def by auto
  }
  ultimately show "U\<inter>V\<in>{one-point compactification of}T" by auto
qed

text\<open>The original topology is an open subspace of the new topology.\<close>

theorem (in topology0) open_subspace:
  shows "\<Union>T\<in>{one-point compactification of}T" and "({one-point compactification of}T){restricted to}\<Union>T=T"
proof-
  show "\<Union>T\<in>{one-point compactification of}T"
  unfolding OPCompactification_def using topSpaceAssum unfolding IsATopology_def by auto
  have "T\<subseteq>({one-point compactification of}T){restricted to}\<Union>T" unfolding OPCompactification_def RestrictedTo_def by auto
  moreover
  {
    fix A assume "A\<in>({one-point compactification of}T){restricted to}\<Union>T"
    then obtain R where "R\<in>({one-point compactification of}T)" "A=\<Union>T\<inter>R" unfolding RestrictedTo_def by auto
    then obtain K where K:"R\<in>T \<or> (R={\<Union>T}\<union>(\<Union>T-K) \<and> K{is closed in}T)" unfolding OPCompactification_def by auto
    with \<open>A=\<Union>T\<inter>R\<close> have "(A=R\<and>R\<in>T)\<or>(A=\<Union>T-K \<and> K{is closed in}T)" using mem_not_refl unfolding IsClosed_def by auto
    with K have "A\<in>T" unfolding IsClosed_def by auto
  }
  ultimately
  show "({one-point compactification of}T){restricted to}\<Union>T=T" by auto
qed

text\<open>We added only one new point to the space.\<close>

lemma (in topology0) op_compact_total:
  shows "\<Union>({one-point compactification of}T)={\<Union>T}\<union>(\<Union>T)"
proof-
  have "0{is compact in}T" unfolding IsCompact_def FinPow_def by auto
  moreover note Top_3_L2 ultimately have TT:"0\<in>{A\<in>Pow(\<Union>T). A{is compact in}T \<and>A{is closed in}T}" by auto
  have "\<Union>({one-point compactification of}T)=(\<Union>T)\<union>(\<Union>{{\<Union>T}\<union>(\<Union>T-K). K\<in>{B\<in>Pow(\<Union>T). B{is compact in}T\<and>B{is closed in}T}})" unfolding OPCompactification_def
    by blast
  also have "\<dots>=(\<Union>T)\<union>{\<Union>T}\<union>(\<Union>{(\<Union>T-K). K\<in>{B\<in>Pow(\<Union>T). B{is compact in}T\<and>B{is closed in}T}})" using TT by auto
  ultimately show "\<Union>({one-point compactification of}T)={\<Union>T}\<union>(\<Union>T)" by auto
qed

text\<open>The one point compactification, gives indeed a compact topological space.\<close>

theorem (in topology0) compact_op:
  shows "({\<Union>T}\<union>(\<Union>T)){is compact in}({one-point compactification of}T)" unfolding IsCompact_def
proof(safe)
  have "0{is compact in}T" unfolding IsCompact_def FinPow_def by auto
  moreover note Top_3_L2 ultimately have "0\<in>{A\<in>Pow(\<Union>T). A{is compact in}T \<and>A{is closed in}T}" by auto
  then have "{\<Union>T}\<union>(\<Union>T)\<in>{one-point compactification of}T" unfolding OPCompactification_def by auto
  then show "\<Union>T \<in> \<Union>{one-point compactification of}T" by auto
next
  fix x B assume "x\<in>B""B\<in>T"
  then show "x\<in>\<Union>({one-point compactification of}T)" using open_subspace by auto
next
  fix M assume A:"M\<subseteq>({one-point compactification of}T)" "{\<Union>T} \<union> \<Union>T \<subseteq> \<Union>M"
  then obtain R where "R\<in>M""\<Union>T\<in>R" by auto
  have "\<Union>T\<notin>\<Union>T" using mem_not_refl by auto
  with \<open>R\<in>M\<close> \<open>\<Union>T\<in>R\<close> A(1) obtain K where K:"R={\<Union>T}\<union>(\<Union>T-K)" "K{is compact in}T""K{is closed in}T"
    unfolding OPCompactification_def by auto
  from K(1,2) have B:"{\<Union>T} \<union> (\<Union>T) = R \<union> K" unfolding IsCompact_def by auto
  with A(2) have "K\<subseteq>\<Union>M" by auto
  from K(2) have "K{is compact in}(({one-point compactification of}T){restricted to}\<Union>T)" using open_subspace(2)
    by auto
  then have "K{is compact in}({one-point compactification of}T)" using compact_subspace_imp_compact
    \<open>K{is closed in}T\<close> unfolding IsClosed_def by auto
  with \<open>K\<subseteq>\<Union>M\<close> A(1) have "(\<exists>N\<in>FinPow(M). K \<subseteq> \<Union>N)" unfolding IsCompact_def by auto
  then obtain N where "N\<in>FinPow(M)" "K\<subseteq>\<Union>N" by auto
  with \<open>R\<in>M\<close> have "(N \<union>{R})\<in>FinPow(M)""R\<union>K\<subseteq>\<Union>(N\<union>{R})" unfolding FinPow_def by auto
  with B show "\<exists>N\<in>FinPow(M). {\<Union>T} \<union> (\<Union>T)\<subseteq>\<Union>N" by auto
qed

text\<open>The one point compactification is Hausdorff iff the original space is also
Hausdorff and locally compact.\<close>

lemma (in topology0) op_compact_T2_1:
  assumes "({one-point compactification of}T){is T\<^sub>2}"
  shows "T{is T\<^sub>2}"
  using T2_here[OF assms, of "\<Union>T"] open_subspace by auto

lemma (in topology0) op_compact_T2_2:
  assumes "({one-point compactification of}T){is T\<^sub>2}"
  shows "T{is locally-compact}"
proof-
  {
    fix x assume "x\<in>\<Union>T"
    then have "x\<in>{\<Union>T}\<union>(\<Union>T)" by auto
    moreover have "\<Union>T\<in>{\<Union>T}\<union>(\<Union>T)" by auto moreover
    from \<open>x\<in>\<Union>T\<close> have "x\<noteq>\<Union>T" using mem_not_refl by auto
    ultimately have "\<exists>U\<in>{one-point compactification of}T. \<exists>V\<in>{one-point compactification of}T. x \<in> U \<and> (\<Union>T) \<in> V \<and> U \<inter> V = 0"
      using assms op_compact_total unfolding isT2_def by auto
    then obtain U V where UV:"U\<in>{one-point compactification of}T""V\<in>{one-point compactification of}T"
      "x\<in>U""\<Union>T\<in>V""U\<inter>V=0" by auto
    from \<open>V\<in>{one-point compactification of}T\<close> \<open>\<Union>T\<in>V\<close> mem_not_refl obtain K where K:"V={\<Union>T}\<union>(\<Union>T-K)""K{is closed in}T""K{is compact in}T"
      unfolding OPCompactification_def by auto
    from \<open>U\<in>{one-point compactification of}T\<close> have "U\<subseteq>{\<Union>T}\<union>(\<Union>T)" unfolding OPCompactification_def 
      using op_compact_total by auto
    with \<open>U\<inter>V=0\<close> K have "U\<subseteq>K""K\<subseteq>\<Union>T" unfolding IsClosed_def by auto
    then have "(\<Union>T)\<inter>U=U" by auto moreover
    from UV(1) have "((\<Union>T)\<inter>U)\<in>({one-point compactification of}T){restricted to}\<Union>T" 
      unfolding RestrictedTo_def by auto
    ultimately have "U\<in>T" using open_subspace(2) by auto
    with \<open>x\<in>U\<close>\<open>U\<subseteq>K\<close> have "x\<in>int(K)" using Top_2_L6 by auto
    with \<open>K\<subseteq>\<Union>T\<close> \<open>K{is compact in}T\<close> have "\<exists>A\<in>Pow(\<Union>T). x\<in>int(A)\<and> A{is compact in}T" by auto
  }
  then have "\<forall>x\<in>\<Union>T. \<exists>A\<in>Pow(\<Union>T). x\<in>int(A)\<and> A{is compact in}T" by auto
  then show ?thesis using op_compact_T2_1[OF assms] exist_compact_neig_T2_imp_locally_compact
    by auto
qed

lemma (in topology0) op_compact_T2_3:
  assumes "T{is locally-compact}" "T{is T\<^sub>2}"
  shows "({one-point compactification of}T){is T\<^sub>2}"
proof-
  {
    fix x y assume "x\<noteq>y""x\<in>\<Union>({one-point compactification of}T)""y\<in>\<Union>({one-point compactification of}T)"
    then have S:"x\<in>{\<Union>T}\<union>(\<Union>T)""y\<in>{\<Union>T}\<union>(\<Union>T)" using op_compact_total by auto
    {
      assume "x\<in>\<Union>T""y\<in>\<Union>T"
      with \<open>x\<noteq>y\<close> have "\<exists>U\<in>T. \<exists>V\<in>T. x\<in>U\<and>y\<in>V\<and>U\<inter>V=0" using assms(2) unfolding isT2_def by auto
      then have "\<exists>U\<in>({one-point compactification of}T). \<exists>V\<in>({one-point compactification of}T). x\<in>U\<and>y\<in>V\<and>U\<inter>V=0"
        unfolding OPCompactification_def by auto
    }
    moreover
    {
      assume "x\<notin>\<Union>T\<or>y\<notin>\<Union>T"
      with S have "x=\<Union>T\<or>y=\<Union>T" by auto
      with \<open>x\<noteq>y\<close> have "(x=\<Union>T\<and>y\<noteq>\<Union>T)\<or>(y=\<Union>T\<and>x\<noteq>\<Union>T)" by auto
      with S have "(x=\<Union>T\<and>y\<in>\<Union>T)\<or>(y=\<Union>T\<and>x\<in>\<Union>T)" by auto
      then obtain Ky Kx where "(x=\<Union>T\<and> Ky{is compact in}T\<and>y\<in>int(Ky))\<or>(y=\<Union>T\<and> Kx{is compact in}T\<and>x\<in>int(Kx))"
        using assms(1) locally_compact_exist_compact_neig by blast
      then have "(x=\<Union>T\<and> Ky{is compact in}T\<and> Ky{is closed in}T\<and>y\<in>int(Ky))\<or>(y=\<Union>T\<and> Kx{is compact in}T\<and> Kx{is closed in}T\<and>x\<in>int(Kx))"
        using in_t2_compact_is_cl assms(2) by auto
      then have "(x\<in>{\<Union>T}\<union>(\<Union>T-Ky)\<and>y\<in>int(Ky)\<and> Ky{is compact in}T\<and> Ky{is closed in}T)\<or>(y\<in>{\<Union>T}\<union>(\<Union>T-Kx)\<and>x\<in>int(Kx)\<and> Kx{is compact in}T\<and> Kx{is closed in}T)"
        by auto moreover
      {
        fix K
        assume A:"K{is closed in}T""K{is compact in}T"
        then have "K\<subseteq>\<Union>T" unfolding IsClosed_def by auto
        moreover have "\<Union>T\<notin>\<Union>T" using mem_not_refl by auto
        ultimately have "({\<Union>T}\<union>(\<Union>T-K))\<inter>K=0" by auto
        then have "({\<Union>T}\<union>(\<Union>T-K))\<inter>int(K)=0" using Top_2_L1 by auto moreover
        from A have "{\<Union>T}\<union>(\<Union>T-K)\<in>({one-point compactification of}T)" unfolding OPCompactification_def
          IsClosed_def by auto moreover
        have "int(K)\<in>({one-point compactification of}T)" using Top_2_L2 unfolding OPCompactification_def
          by auto ultimately
        have "int(K)\<in>({one-point compactification of}T)\<and>{\<Union>T}\<union>(\<Union>T-K)\<in>({one-point compactification of}T)\<and>({\<Union>T}\<union>(\<Union>T-K))\<inter>int(K)=0"
          by auto
      }
      ultimately have "({\<Union>T} \<union> (\<Union>T - Ky)\<in>({one-point compactification of}T)\<and>int(Ky)\<in>({one-point compactification of}T)\<and>x \<in> {\<Union>T} \<union> (\<Union>T - Ky) \<and> y \<in> int(Ky) \<and> ({\<Union>T}\<union>(\<Union>T-Ky))\<inter>int(Ky)=0) \<or>
        ({\<Union>T} \<union> (\<Union>T - Kx)\<in>({one-point compactification of}T)\<and>int(Kx)\<in>({one-point compactification of}T)\<and>y \<in> {\<Union>T} \<union> (\<Union>T - Kx) \<and> x \<in> int(Kx) \<and> ({\<Union>T}\<union>(\<Union>T-Kx))\<inter>int(Kx)=0)" by auto
      moreover
      {
        assume "({\<Union>T} \<union> (\<Union>T - Ky)\<in>({one-point compactification of}T)\<and>int(Ky)\<in>({one-point compactification of}T)\<and>x \<in> {\<Union>T} \<union> (\<Union>T - Ky) \<and> y \<in> int(Ky) \<and> ({\<Union>T}\<union>(\<Union>T-Ky))\<inter>int(Ky)=0)"
        then have "\<exists>U\<in>({one-point compactification of}T). \<exists>V\<in>({one-point compactification of}T). x\<in>U\<and>y\<in>V\<and>U\<inter>V=0" using exI[OF exI[of _ "int(Ky)"],of "\<lambda>U V. U\<in>({one-point compactification of}T)\<and>V\<in>({one-point compactification of}T) \<and> x\<in>U\<and>y\<in>V\<and>U\<inter>V=0" "{\<Union>T}\<union>(\<Union>T-Ky)"]
          by auto          
      } moreover
      {
        assume "({\<Union>T} \<union> (\<Union>T - Kx)\<in>({one-point compactification of}T)\<and>int(Kx)\<in>({one-point compactification of}T)\<and>y \<in> {\<Union>T} \<union> (\<Union>T - Kx) \<and> x \<in> int(Kx) \<and> ({\<Union>T}\<union>(\<Union>T-Kx))\<inter>int(Kx)=0)"
        then have "\<exists>U\<in>({one-point compactification of}T). \<exists>V\<in>({one-point compactification of}T). x\<in>U\<and>y\<in>V\<and>U\<inter>V=0" using exI[OF exI[of _ "{\<Union>T}\<union>(\<Union>T-Kx)"],of "\<lambda>U V. U\<in>({one-point compactification of}T)\<and>V\<in>({one-point compactification of}T) \<and> x\<in>U\<and>y\<in>V\<and>U\<inter>V=0""int(Kx)" ]
          by blast
      }
      ultimately have "\<exists>U\<in>({one-point compactification of}T). \<exists>V\<in>({one-point compactification of}T). x\<in>U\<and>y\<in>V\<and>U\<inter>V=0" by auto
    }
    ultimately have "\<exists>U\<in>({one-point compactification of}T). \<exists>V\<in>({one-point compactification of}T). x\<in>U\<and>y\<in>V\<and>U\<inter>V=0" by auto
  }
  then show ?thesis unfolding isT2_def by auto
qed

text\<open>In conclusion, every locally compact Hausdorff topological space is regular; since this property is hereditary.\<close>

corollary (in topology0) locally_compact_T2_imp_regular:
  assumes "T{is locally-compact}" "T{is T\<^sub>2}"
  shows "T{is regular}"
proof-
  from assms have "( {one-point compactification of}T) {is T\<^sub>2}" using op_compact_T2_3 by auto
  then have "({one-point compactification of}T) {is T\<^sub>4}" unfolding isT4_def using T2_is_T1 topology0.T2_compact_is_normal
    op_comp_is_top unfolding topology0_def using op_compact_total compact_op by auto
  then have "({one-point compactification of}T) {is T\<^sub>3}" using topology0.T4_is_T3 op_comp_is_top unfolding topology0_def
    by auto
  then have "({one-point compactification of}T) {is regular}" using isT3_def by auto moreover
  have "\<Union>T\<subseteq>\<Union>({one-point compactification of}T)" using op_compact_total by auto
  ultimately have "(({one-point compactification of}T){restricted to}\<Union>T) {is regular}" using regular_here by auto
  then show "T{is regular}" using open_subspace(2) by auto
qed

text\<open>This last corollary has an explanation: In Hausdorff spaces, compact sets are closed
and regular spaces are exactly the "locally closed spaces"(those which have a neighbourhood basis of closed sets).
So the neighbourhood basis of compact sets also works as the neighbourhood basis of closed sets we needed to find.\<close>

definition
  IsLocallyClosed ("_{is locally-closed}")
  where "T{is locally-closed} \<equiv> T{is locally}(\<lambda>B TT. B{is closed in}TT)"

lemma (in topology0) regular_locally_closed:
  shows "T{is regular} \<longleftrightarrow> (T{is locally-closed})"
proof
  assume "T{is regular}"
  then have a:"\<forall>x\<in>\<Union>T. \<forall>U\<in>T. (x\<in>U) \<longrightarrow> (\<exists>V\<in>T. x \<in> V \<and> cl(V) \<subseteq> U)"  using regular_imp_exist_clos_neig by auto
  {
    fix x b assume "x\<in>\<Union>T""b\<in>T""x\<in>b"
    with a obtain V where "V\<in>T""x\<in>V""cl(V)\<subseteq>b" by blast
    note \<open>cl(V)\<subseteq>b\<close> moreover
    from \<open>V\<in>T\<close> have "V\<subseteq>\<Union>T" by auto
    then have "V\<subseteq>cl(V)" using cl_contains_set by auto
    with \<open>x\<in>V\<close>\<open>V\<in>T\<close> have "x\<in>int(cl(V))" using Top_2_L6 by auto moreover
    from \<open>V\<subseteq>\<Union>T\<close> have "cl(V){is closed in}T" using cl_is_closed by auto
    ultimately have "x\<in>int(cl(V))""cl(V)\<subseteq>b""cl(V){is closed in}T" by auto
    then have "\<exists>K\<in>Pow(b). x\<in>int(K)\<and>K{is closed in}T" by auto
  }
  then show "T{is locally-closed}" unfolding IsLocally_def[OF topSpaceAssum] IsLocallyClosed_def
    by auto
next
  assume "T{is locally-closed}"
  then have a:"\<forall>x\<in>\<Union>T. \<forall>b\<in>T. x\<in>b \<longrightarrow> (\<exists>K\<in>Pow(b). x\<in>int(K)\<and>K{is closed in}T)" unfolding IsLocally_def[OF topSpaceAssum]
    IsLocallyClosed_def by auto
  {
    fix x b assume "x\<in>\<Union>T""b\<in>T""x\<in>b"
    with a obtain K where K:"K\<subseteq>b""x\<in>int(K)""K{is closed in}T" by blast
    have "int(K)\<subseteq>K" using Top_2_L1 by auto
    with K(3) have "cl(int(K))\<subseteq>K" using Top_3_L13 by auto
    with K(1) have "cl(int(K))\<subseteq>b" by auto moreover
    have "int(K)\<in>T" using Top_2_L2 by auto moreover
    note \<open>x\<in>int(K)\<close> ultimately have "\<exists>V\<in>T. x\<in>V\<and> cl(V)\<subseteq>b" by auto
  }
  then have "\<forall>x\<in>\<Union>T. \<forall>b\<in>T. x\<in>b \<longrightarrow> (\<exists>V\<in>T. x\<in>V\<and> cl(V)\<subseteq>b)" by auto
  then show "T{is regular}" using exist_clos_neig_imp_regular by auto
qed

subsection\<open>Hereditary properties and local properties\<close>

text\<open>In this section, we prove a relation between a property and its local property
for hereditary properties. Then we apply it to locally-Hausdorff or locally-$T_2$.
We also prove the relation between locally-$T_2$ and
another property that appeared when considering anti-properties, the
anti-hyperconnectness.\<close>

text\<open>If a property is hereditary in open sets, then local properties are equivalent
to find just one open neighbourhood with that property instead of a whole local basis.\<close>

lemma (in topology0) her_P_is_loc_P:
  assumes "\<forall>TT. \<forall>B\<in>Pow(\<Union>TT). \<forall>A\<in>TT. TT{is a topology}\<and>P(B,TT) \<longrightarrow> P(B\<inter>A,TT)"
  shows "(T{is locally}P) \<longleftrightarrow> (\<forall>x\<in>\<Union>T. \<exists>A\<in>T. x\<in>A\<and>P(A,T))"
proof
  assume A:"T{is locally}P"
  {
    fix x assume x:"x\<in>\<Union>T"
    with A have "\<forall>b\<in>T. x\<in>b \<longrightarrow> (\<exists>c\<in>Pow(b). x\<in>int(c)\<and>P(c,T))" unfolding IsLocally_def[OF topSpaceAssum]
      by auto moreover
    note x moreover
    have "\<Union>T\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
    ultimately have "\<exists>c\<in>Pow(\<Union>T). x\<in>int(c)\<and> P(c,T)" by auto
    then obtain c where c:"c\<subseteq>\<Union>T""x\<in>int(c)""P(c,T)" by auto
    have P:"int(c)\<in>T" using Top_2_L2 by auto moreover
    from c(1,3) topSpaceAssum assms have "\<forall>A\<in>T. P(c\<inter>A,T)" by auto
    ultimately have "P(c\<inter>int(c),T)" by auto moreover
    from Top_2_L1[of "c"] have "int(c)\<subseteq>c" by auto
    then have "c\<inter>int(c)=int(c)" by auto
    ultimately have "P(int(c),T)" by auto
    with P c(2) have "\<exists>V\<in>T. x\<in>V\<and>P(V,T)" by auto
  }
  then show "\<forall>x\<in>\<Union>T. \<exists>V\<in>T. x\<in>V\<and>P(V,T)" by auto
  next
  assume A:"\<forall>x\<in>\<Union>T. \<exists>A\<in>T. x \<in> A \<and> P(A, T)"
  {
    fix x assume x:"x\<in>\<Union>T"
    {
      fix b assume b:"x\<in>b""b\<in>T"
      from x A obtain A where A_def:"A\<in>T""x\<in>A""P(A,T)" by auto
      from A_def(1,3) assms topSpaceAssum have "\<forall>G\<in>T. P(A\<inter>G,T)" by auto
      with b(2) have "P(A\<inter>b,T)" by auto
      moreover from b(1) A_def(2) have "x\<in>A\<inter>b" by auto moreover
      have "A\<inter>b\<in>T" using b(2) A_def(1) topSpaceAssum IsATopology_def by auto
      then have "int(A\<inter>b)=A\<inter>b" using Top_2_L3 by auto
      ultimately have "x\<in>int(A\<inter>b)\<and>P(A\<inter>b,T)" by auto
      then have "\<exists>c\<in>Pow(b). x\<in>int(c)\<and>P(c,T)" by auto
    }
    then have "\<forall>b\<in>T. x\<in>b\<longrightarrow>(\<exists>c\<in>Pow(b). x\<in>int(c)\<and>P(c,T))" by auto
  }
  then show "T{is locally}P" unfolding IsLocally_def[OF topSpaceAssum] by auto
qed


definition
  IsLocallyT2 ("_{is locally-T\<^sub>2}" 70)
  where "T{is locally-T\<^sub>2}\<equiv>T{is locally}(\<lambda>B. \<lambda>T. (T{restricted to}B){is T\<^sub>2})"

text\<open>Since $T_2$ is an hereditary property, we can apply the previous lemma.\<close>

corollary (in topology0) loc_T2:
  shows "(T{is locally-T\<^sub>2}) \<longleftrightarrow> (\<forall>x\<in>\<Union>T. \<exists>A\<in>T. x\<in>A\<and>(T{restricted to}A){is T\<^sub>2})"
proof-
  {
    fix TT B A assume TT:"TT{is a topology}" "(TT{restricted to}B){is T\<^sub>2}" "A\<in>TT""B\<in>Pow(\<Union>TT)"
    then have s:"B\<inter>A\<subseteq>B""B\<subseteq>\<Union>TT" by auto
    then have "(TT{restricted to}(B\<inter>A))=(TT{restricted to}B){restricted to}(B\<inter>A)" using subspace_of_subspace
      by auto moreover
    have "\<Union>(TT{restricted to}B)=B" unfolding RestrictedTo_def using s(2) by auto
    then have "B\<inter>A\<subseteq>\<Union>(TT{restricted to}B)" using s(1) by auto moreover
    note TT(2) ultimately have "(TT{restricted to}(B\<inter>A)){is T\<^sub>2}" using T2_here
      by auto
  }
  then have "\<forall>TT. \<forall>B\<in>Pow(\<Union>TT). \<forall>A\<in>TT. TT{is a topology}\<and>(TT{restricted to}B){is T\<^sub>2} \<longrightarrow> (TT{restricted to}(B\<inter>A)){is T\<^sub>2}"
    by auto
  with her_P_is_loc_P[where P="\<lambda>A. \<lambda>TT. (TT{restricted to}A){is T\<^sub>2}"] show ?thesis unfolding IsLocallyT2_def by auto
qed


text\<open>First, we prove that a locally-$T_2$ space is anti-hyperconnected.\<close>

text\<open>Before starting, let's prove that an open subspace of an hyperconnected
space is hyperconnected.\<close>

lemma(in topology0) open_subspace_hyperconn:
  assumes "T{is hyperconnected}" "U\<in>T"
  shows "(T{restricted to}U){is hyperconnected}"
proof-
  {
    fix A B assume "A\<in>(T{restricted to}U)""B\<in>(T{restricted to}U)""A\<inter>B=0"
    then obtain AU BU where "A=U\<inter>AU""B=U\<inter>BU" "AU\<in>T""BU\<in>T" unfolding RestrictedTo_def by auto
    then have "A\<in>T""B\<in>T" using topSpaceAssum assms(2) unfolding IsATopology_def by auto
    with \<open>A\<inter>B=0\<close> have "A=0\<or>B=0" using assms(1) unfolding IsHConnected_def by auto
  }
  then show ?thesis unfolding IsHConnected_def by auto
qed

lemma(in topology0) locally_T2_is_antiHConn:
  assumes "T{is locally-T\<^sub>2}"
  shows "T{is anti-}IsHConnected"
proof-
  {
    fix A assume A:"A\<in>Pow(\<Union>T)""(T{restricted to}A){is hyperconnected}"
    {
      fix x assume "x\<in>A"
      with A(1) have "x\<in>\<Union>T" by auto moreover
      have "\<Union>T\<in>T" using topSpaceAssum unfolding IsATopology_def by auto ultimately
      have "\<exists>c\<in>Pow(\<Union>T). x \<in> int(c) \<and> (T {restricted to} c) {is T\<^sub>2}" using assms
        unfolding IsLocallyT2_def IsLocally_def[OF topSpaceAssum] by auto
      then obtain c where c:"c\<in>Pow(\<Union>T)""x\<in>int(c)""(T {restricted to} c) {is T\<^sub>2}" by auto
      have "\<Union>(T {restricted to} c)=(\<Union>T)\<inter>c" unfolding RestrictedTo_def by auto
      with \<open>c\<in>Pow(\<Union>T)\<close>\<open>\<Union>T\<in>T\<close> have tot:"\<Union>(T {restricted to} c)=c" by auto
      have "int(c)\<in>T" using Top_2_L2 by auto
      then have "A\<inter>(int(c))\<in>(T{restricted to}A)" unfolding RestrictedTo_def by auto
      with A(2) have "((T{restricted to}A){restricted to}(A\<inter>(int(c)))){is hyperconnected}"
        using topology0.open_subspace_hyperconn unfolding topology0_def using Top_1_L4
        by auto
      then have "(T{restricted to}(A\<inter>(int(c)))){is hyperconnected}" using subspace_of_subspace[of "A\<inter>(int(c))"
        "A""T"] A(1) by force moreover
      have "int(c)\<subseteq>c" using Top_2_L1 by auto
      then have sub:"A\<inter>(int(c))\<subseteq>c" by auto
      then have "A\<inter>(int(c))\<subseteq>\<Union>(T {restricted to} c)" using tot by auto
      then have "((T {restricted to} c){restricted to}(A\<inter>(int(c)))) {is T\<^sub>2}" using
        T2_here[OF c(3)] by auto
      with sub have "(T {restricted to}(A\<inter>(int(c)))){is T\<^sub>2}" using subspace_of_subspace[of "A\<inter>(int(c))"
        "c""T"] \<open>c\<in>Pow(\<Union>T)\<close> by auto
      ultimately have "(T{restricted to}(A\<inter>(int(c)))){is hyperconnected}""(T {restricted to}(A\<inter>(int(c)))){is T\<^sub>2}"
        by auto
      then have "(T{restricted to}(A\<inter>(int(c)))){is hyperconnected}""(T {restricted to}(A\<inter>(int(c)))){is anti-}IsHConnected"
        using topology0.T2_imp_anti_HConn unfolding topology0_def using Top_1_L4 by auto
      moreover
      have "\<Union>(T{restricted to}(A\<inter>(int(c))))=(\<Union>T)\<inter>A\<inter>(int(c))" unfolding RestrictedTo_def by auto
      with A(1) Top_2_L2 have "\<Union>(T{restricted to}(A\<inter>(int(c))))=A\<inter>(int(c))" by auto
      then have "A\<inter>(int(c))\<subseteq>\<Union>(T{restricted to}(A\<inter>(int(c))))" by auto moreover
      have "A\<inter>(int(c))\<subseteq>\<Union>T" using A(1) Top_2_L2 by auto
      then have "(T{restricted to}(A\<inter>(int(c)))){restricted to}(A\<inter>(int(c)))=(T{restricted to}(A\<inter>(int(c))))"
        using subspace_of_subspace[of "A\<inter>(int(c))""A\<inter>(int(c))""T"] by auto
      ultimately have "(A\<inter>(int(c))){is in the spectrum of}IsHConnected" unfolding antiProperty_def
        by auto
      then have "A\<inter>(int(c))\<lesssim>1" using HConn_spectrum by auto
      then have "(A\<inter>(int(c))={x})" using lepoll_1_is_sing \<open>x\<in>A\<close>\<open>x\<in>int(c)\<close> by auto
      then have "{x}\<in>(T{restricted to}A)" using \<open>(A\<inter>(int(c))\<in>(T{restricted to}A))\<close> by auto 
    }
    then have pointOpen:"\<forall>x\<in>A. {x}\<in>(T{restricted to}A)" by auto
    {
      fix x y assume "x\<noteq>y""x\<in>A""y\<in>A"
      with pointOpen have "{x}\<in>(T{restricted to}A)""{y}\<in>(T{restricted to}A)""{x}\<inter>{y}=0"
        by auto
      with A(2) have "{x}=0\<or>{y}=0" unfolding IsHConnected_def by auto
      then have "False" by auto
    }
    then have uni:"\<forall>x\<in>A. \<forall>y\<in>A. x=y" by auto
    {
      assume "A\<noteq>0"
      then obtain x where "x\<in>A" by auto
      with uni have "A={x}" by auto
      then have "A\<approx>1" using singleton_eqpoll_1 by auto
      then have "A\<lesssim>1" using eqpoll_imp_lepoll by auto
    }
    moreover
    {
      assume "A=0"
      then have "A\<approx>0" by auto
      then have "A\<lesssim>1" using empty_lepollI eq_lepoll_trans by auto
    }
    ultimately have "A\<lesssim>1" by auto
    then have "A{is in the spectrum of}IsHConnected" using HConn_spectrum by auto
  }
  then show ?thesis unfolding antiProperty_def by auto
qed  

text\<open>Now we find a counter-example for: Every anti-hyperconnected space is locally-Hausdorff.\<close>

text\<open>The example we are going to consider is the following. Put
in $X$ an anti-hyperconnected topology, where an infinite number of points don't
have finite sets as neighbourhoods. Then add a new point to the set, $p\notin X$.
Consider the open sets on $X\cup {p}$ as the anti-hyperconnected topology and
the open sets that contain $p$ are $p\cup A$ where $X\setminus A$ is finite.\<close>

text\<open>This construction equals the one-point compactification iff
$X$ is anti-compact; i.e., the only compact sets are the finite ones.
In general this topology is contained in the one-point compactification topology,
making it compact too.\<close>

text\<open>It is easy to check that any open set containing $p$ meets infinite other non-empty
open set. The question is if such a topology exists.\<close>

theorem (in topology0) COF_comp_is_top:
  assumes "T{is T\<^sub>1}""\<not>(\<Union>T\<prec>nat)"
  shows "((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T) {is a topology}"
proof-
  have N:"\<Union>T\<notin>(\<Union>T)" using mem_not_refl by auto    
  {
    fix M assume M:"M\<subseteq>((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T)"
    let ?MT="{A\<in>M. A\<in>T}"
    let ?MK="{A\<in>M. A\<notin>T}"
    have MM:"(\<Union>?MT)\<union>(\<Union>?MK)=\<Union>M" by auto
    have MN:"\<Union>?MT\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
    then have sub:"?MK\<subseteq>({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}"
      using M by auto
    then have "?MK\<subseteq>({one-point compactification of}(CoFinite (\<Union>T)))" by auto
    then have CO:"\<Union>?MK\<in>({one-point compactification of}(CoFinite (\<Union>T)))" using 
      topology0.op_comp_is_top[OF topology0_CoCardinal[OF InfCard_nat]] unfolding Cofinite_def
      IsATopology_def by auto
    {
      assume AS:"\<Union>?MK={\<Union>T}"
      moreover have "\<forall>R\<in>?MK. R\<subseteq>\<Union>?MK" by auto
      ultimately have "\<forall>R\<in>?MK. R\<subseteq>{\<Union>T}" by auto
      then have "\<forall>R\<in>?MK. R={\<Union>T}\<or>R=0" by force moreover
      with sub have "\<forall>R\<in>?MK. R=0" by auto
      then have "\<Union>?MK=0" by auto
      with AS have "False" by auto
    }
    with CO have CO2:"\<Union>?MK\<in>({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}" by auto
    {
      assume "\<Union>?MK\<in>(CoFinite (\<Union>T))"
      then have "\<Union>?MK\<in>T" using assms(1) T1_cocardinal_coarser by auto
      with MN have "{\<Union>?MT,\<Union>?MK}\<subseteq>(T)" by auto
      then have "(\<Union>?MT)\<union>(\<Union>?MK)\<in>T" using union_open[OF topSpaceAssum, of "{\<Union>?MT,\<Union>?MK}"] by auto
      then have "\<Union>M\<in>T" using MM by auto
    }
    moreover
    {
      assume "\<Union>?MK\<notin>(CoFinite (\<Union>T))"
      with CO obtain B where "B{is compact in}(CoFinite (\<Union>T))""B{is closed in}(CoFinite (\<Union>T))"
        "\<Union>?MK={\<Union>CoFinite \<Union>T}\<union>(\<Union>(CoFinite \<Union>T)-B)" unfolding OPCompactification_def by auto
      then have MK:"\<Union>?MK={\<Union>T}\<union>(\<Union>T-B)""B{is closed in}(CoFinite (\<Union>T))"
        using union_cocardinal unfolding Cofinite_def by auto
      then have B:"B\<subseteq>\<Union>T" "B\<prec>nat\<or>B=\<Union>T" using closed_sets_cocardinal unfolding Cofinite_def by auto
      {
        assume "B=\<Union>T"
        with MK have "\<Union>?MK={\<Union>T}" by auto
        then have "False" using CO2 by auto
      }
      with B have "B\<subseteq>\<Union>T" and natB:"B\<prec>nat" by auto
      have "(\<Union>T-(\<Union>?MT))\<inter>B\<subseteq>B" by auto
      then have "(\<Union>T-(\<Union>?MT))\<inter>B\<lesssim>B" using subset_imp_lepoll by auto
      then have "(\<Union>T-(\<Union>?MT))\<inter>B\<prec>nat" using natB lesspoll_trans1 by auto
      then have "((\<Union>T-(\<Union>?MT))\<inter>B){is closed in}(CoFinite (\<Union>T))" using closed_sets_cocardinal
        B(1) unfolding Cofinite_def by auto
      then have "\<Union>T-((\<Union>T-(\<Union>?MT))\<inter>B)\<in>(CoFinite (\<Union>T))" unfolding IsClosed_def using union_cocardinal unfolding Cofinite_def by auto
      also have "\<Union>T-((\<Union>T-(\<Union>?MT))\<inter>B)=(\<Union>T-(\<Union>T-(\<Union>?MT)))\<union>(\<Union>T-B)" by auto
      also have "\<dots>=(\<Union>?MT)\<union>(\<Union>T-B)" by auto
      ultimately have P:"(\<Union>?MT)\<union>(\<Union>T-B)\<in>(CoFinite (\<Union>T))" by auto
      then have eq:"\<Union>T-(\<Union>T-((\<Union>?MT)\<union>(\<Union>T-B)))=(\<Union>?MT)\<union>(\<Union>T-B)" by auto
      from P eq have "(\<Union>T-((\<Union>?MT)\<union>(\<Union>T-B))){is closed in}(CoFinite (\<Union>T))" unfolding IsClosed_def
        using union_cocardinal[of "nat""\<Union>T"] unfolding Cofinite_def by auto moreover
      have "(\<Union>T-((\<Union>?MT)\<union>(\<Union>T-B)))\<inter>\<Union>T=(\<Union>T-((\<Union>?MT)\<union>(\<Union>T-B)))" by auto
      then have "(CoFinite \<Union>T){restricted to}(\<Union>T-((\<Union>?MT)\<union>(\<Union>T-B)))=CoFinite (\<Union>T-((\<Union>?MT)\<union>(\<Union>T-B)))" using subspace_cocardinal unfolding Cofinite_def by auto
      then have "(\<Union>T-((\<Union>?MT)\<union>(\<Union>T-B))){is compact in}((CoFinite \<Union>T){restricted to}(\<Union>T-((\<Union>?MT)\<union>(\<Union>T-B))))" using cofinite_compact
        union_cocardinal unfolding Cofinite_def by auto
      then have "(\<Union>T-((\<Union>?MT)\<union>(\<Union>T-B))){is compact in}(CoFinite \<Union>T)" using compact_subspace_imp_compact by auto ultimately
      have "{\<Union>T}\<union>(\<Union>T-(\<Union>T-((\<Union>?MT)\<union>(\<Union>T-B))))\<in>({one-point compactification of}(CoFinite (\<Union>T)))"
        unfolding OPCompactification_def using union_cocardinal unfolding Cofinite_def by auto
      with eq have "{\<Union>T}\<union>((\<Union>?MT)\<union>(\<Union>T-B))\<in>({one-point compactification of}(CoFinite (\<Union>T)))" by auto
      moreover have AA:"{\<Union>T}\<union>((\<Union>?MT)\<union>(\<Union>T-B))=((\<Union>?MT)\<union>(\<Union>?MK))" using MK(1) by auto
      ultimately have AA2:"((\<Union>?MT)\<union>(\<Union>?MK))\<in>({one-point compactification of}(CoFinite (\<Union>T)))" by auto
      {
        assume AS:"(\<Union>?MT)\<union>(\<Union>?MK)={\<Union>T}"
        from MN have T:"\<Union>T\<notin>\<Union>?MT" using N by auto
        {
          fix x assume G:"x\<in>\<Union>?MT"
          then have "x\<in>(\<Union>?MT)\<union>(\<Union>?MK)" by auto
          with AS have "x\<in>{\<Union>T}" by auto
          then have "x=\<Union>T" by auto
          with T have "False" using G by auto
        }
        then have "\<Union>?MT=0" by auto
        with AS have "(\<Union>?MK)={\<Union>T}" by auto
        then have "False" using CO2 by auto
      }
      with AA2 have "((\<Union>?MT)\<union>(\<Union>?MK))\<in>({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}" by auto
      with MM have "\<Union>M\<in>({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}" by auto
    }
    ultimately
    have "\<Union>M\<in>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T" by auto
  }
  then have "\<forall>M\<in>Pow((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T). \<Union>M\<in>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T"
    by auto moreover
  {
    fix U V assume "U\<in>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T""V\<in>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T" moreover
    {
      assume "U\<in>T""V\<in>T"
      then have "U\<inter>V\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
      then have "U\<inter>V\<in>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T" by auto
    }
    moreover
    {
      assume UV:"U\<in>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})""V\<in>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})"
      then have O:"U\<inter>V\<in>({one-point compactification of}(CoFinite (\<Union>T)))" using topology0.op_comp_is_top[OF topology0_CoCardinal[OF InfCard_nat]] unfolding Cofinite_def
        IsATopology_def by auto
      then have "\<Union>T\<inter>(U\<inter>V)\<in>({one-point compactification of}(CoFinite (\<Union>T))){restricted to}\<Union>T"
        unfolding RestrictedTo_def by auto
      then have "\<Union>T\<inter>(U\<inter>V)\<in>CoFinite \<Union>T" using topology0.open_subspace(2)[OF topology0_CoCardinal[OF InfCard_nat]]
        union_cocardinal unfolding Cofinite_def by auto
      from UV have "U\<noteq>{\<Union>T}""V\<noteq>{\<Union>T}""\<Union>T\<inter>U\<in>({one-point compactification of}(CoFinite (\<Union>T))){restricted to}\<Union>T""\<Union>T\<inter>V\<in>({one-point compactification of}(CoFinite (\<Union>T))){restricted to}\<Union>T"
        unfolding RestrictedTo_def by auto
      then have R:"U\<noteq>{\<Union>T}""V\<noteq>{\<Union>T}""\<Union>T\<inter>U\<in>CoFinite \<Union>T""\<Union>T\<inter>V\<in>CoFinite \<Union>T" using topology0.open_subspace(2)[OF topology0_CoCardinal[OF InfCard_nat]]
        union_cocardinal unfolding Cofinite_def by auto
      from UV have "U\<subseteq>\<Union>({one-point compactification of}(CoFinite (\<Union>T)))""V\<subseteq>\<Union>({one-point compactification of}(CoFinite (\<Union>T)))" by auto
      then have "U\<subseteq>{\<Union>T}\<union>\<Union>T""V\<subseteq>{\<Union>T}\<union>\<Union>T" using topology0.op_compact_total[OF topology0_CoCardinal[OF InfCard_nat]]
        union_cocardinal unfolding Cofinite_def by auto
      then have E:"U=(\<Union>T\<inter>U)\<union>({\<Union>T}\<inter>U)""V=(\<Union>T\<inter>V)\<union>({\<Union>T}\<inter>V)""U\<inter>V=(\<Union>T\<inter>U\<inter>V)\<union>({\<Union>T}\<inter>U\<inter>V)" by auto
      {
        assume Q:"U\<inter>V={\<Union>T}"
        then have RR:"\<Union>T\<inter>(U\<inter>V)=0" using N by auto
        {
          assume "\<Union>T\<inter>U=0"
          with E(1) have "U={\<Union>T}\<inter>U" by auto
          also have "\<dots>\<subseteq>{\<Union>T}" by auto
          ultimately have "U\<subseteq>{\<Union>T}" by auto
          then have "U=0\<or>U={\<Union>T}" by auto
          with R(1) have "U=0" by auto
          then have "U\<inter>V=0" by auto
          then have "False" using Q by auto
        }
        moreover
        {
          assume "\<Union>T\<inter>V=0"
          with E(2) have "V={\<Union>T}\<inter>V" by auto
          also have "\<dots>\<subseteq>{\<Union>T}" by auto
          ultimately have "V\<subseteq>{\<Union>T}" by auto
          then have "V=0\<or>V={\<Union>T}" by auto
          with R(2) have "V=0" by auto
          then have "U\<inter>V=0" by auto
          then have "False" using Q by auto
        }
        moreover
        {
          assume "\<Union>T\<inter>U\<noteq>0""\<Union>T\<inter>V\<noteq>0"
          with R(3,4) have "(\<Union>T\<inter>U)\<inter>(\<Union>T\<inter>V)\<noteq>0" using Cofinite_nat_HConn[OF assms(2)]
            unfolding IsHConnected_def by auto
          then have "\<Union>T\<inter>(U\<inter>V)\<noteq>0" by auto
          then have "False" using RR by auto
        }
        ultimately have "False" by auto
      }
      with O have "U\<inter>V\<in>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T" by auto
    }
    moreover
    {
      assume UV:"U\<in>T""V\<in>({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}"
      from UV(2) obtain B where "V\<in>(CoFinite \<Union>T)\<or>(V={\<Union>T}\<union>(\<Union>T-B)\<and>B{is closed in}(CoFinite (\<Union>T)))" unfolding OPCompactification_def
        using union_cocardinal unfolding Cofinite_def by auto
      with assms(1) have "V\<in>T\<or>(V={\<Union>T}\<union>(\<Union>T-B)\<and>B{is closed in}(CoFinite (\<Union>T)))" using T1_cocardinal_coarser by auto
      then have "V\<in>T\<or>(U\<inter>V=U\<inter>(\<Union>T-B)\<and>B{is closed in}(CoFinite (\<Union>T)))" using UV(1) N by auto
      then have "V\<in>T\<or>(U\<inter>V=U\<inter>(\<Union>T-B)\<and>(\<Union>T-B)\<in>(CoFinite (\<Union>T)))" unfolding IsClosed_def using union_cocardinal unfolding Cofinite_def by auto
      then have "V\<in>T\<or>(U\<inter>V=U\<inter>(\<Union>T-B)\<and>(\<Union>T-B)\<in>T)" using assms(1) T1_cocardinal_coarser by auto
      with UV(1) have "U\<inter>V\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
      then have "U\<inter>V\<in>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T" by auto
    }
    moreover
    {
      assume UV:"U\<in>({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}""V\<in>T"
      from UV(1) obtain B where "U\<in>(CoFinite \<Union>T)\<or>(U={\<Union>T}\<union>(\<Union>T-B)\<and>B{is closed in}(CoFinite (\<Union>T)))" unfolding OPCompactification_def
        using union_cocardinal unfolding Cofinite_def by auto
      with assms(1) have "U\<in>T\<or>(U={\<Union>T}\<union>(\<Union>T-B)\<and>B{is closed in}(CoFinite (\<Union>T)))" using T1_cocardinal_coarser by auto
      then have "U\<in>T\<or>(U\<inter>V=(\<Union>T-B)\<inter>V\<and>B{is closed in}(CoFinite (\<Union>T)))" using UV(2) N by auto
      then have "U\<in>T\<or>(U\<inter>V=(\<Union>T-B)\<inter>V\<and>(\<Union>T-B)\<in>(CoFinite (\<Union>T)))" unfolding IsClosed_def using union_cocardinal unfolding Cofinite_def by auto
      then have "U\<in>T\<or>(U\<inter>V=(\<Union>T-B)\<inter>V\<and>(\<Union>T-B)\<in>T)" using assms(1) T1_cocardinal_coarser by auto
      with UV(2) have "U\<inter>V\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
      then have "U\<inter>V\<in>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T" by auto
    }
    ultimately
    have "U\<inter>V\<in>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T" by auto
  }
  ultimately show ?thesis unfolding IsATopology_def by auto
qed

text\<open>The previous construction preserves anti-hyperconnectedness.\<close>

theorem (in topology0) COF_comp_antiHConn:
  assumes "T{is anti-}IsHConnected" "\<not>(\<Union>T\<prec>nat)"
  shows "((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T) {is anti-}IsHConnected"
proof-
  have N:"\<Union>T\<notin>(\<Union>T)" using mem_not_refl by auto
  from assms(1) have T1:"T{is T\<^sub>1}" using anti_HConn_imp_T1 by auto
  have tot1:"\<Union>({one-point compactification of}(CoFinite (\<Union>T)))={\<Union>T}\<union>\<Union>T" using topology0.op_compact_total[OF topology0_CoCardinal[OF InfCard_nat], of "\<Union>T"]
        union_cocardinal[of "nat""\<Union>T"] unfolding Cofinite_def by auto 
  then have "(\<Union>({one-point compactification of}(CoFinite (\<Union>T))))\<union>\<Union>T={\<Union>T}\<union>\<Union>T" by auto moreover
  have "\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))\<union>T)=(\<Union>({one-point compactification of}(CoFinite (\<Union>T))))\<union>\<Union>T"
    by auto
  ultimately have tot2:"\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))\<union>T)={\<Union>T}\<union>\<Union>T" by auto
  have "{\<Union>T}\<union>\<Union>T\<in>({one-point compactification of}(CoFinite (\<Union>T)))" using union_open[OF topology0.op_comp_is_top[OF topology0_CoCardinal[OF InfCard_nat]],of "{one-point compactification of}(CoFinite (\<Union>T))"]
    tot1 unfolding Cofinite_def by auto moreover
  {
    assume "\<Union>T=0"
    with assms(2) have "\<not>(0\<prec>nat)" by auto
    then have "False" unfolding lesspoll_def using empty_lepollI eqpoll_0_is_0
      eqpoll_sym by auto
  }
  then have "\<Union>T\<noteq>0" by auto
  with N have Not:"\<not>(\<Union>T\<subseteq>{\<Union>T})" by auto
  {
    assume "{\<Union>T}\<union>\<Union>T={\<Union>T}" moreover
    have "\<Union>T\<subseteq>{\<Union>T}\<union>\<Union>T" by auto ultimately
    have "\<Union>T\<subseteq>{\<Union>T}" by auto
    with Not have "False" by auto
  }
  then have "{\<Union>T}\<union>\<Union>T\<noteq>{\<Union>T}" by auto ultimately
  have "{\<Union>T}\<union>\<Union>T\<in>({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}" by auto
  then have "{\<Union>T}\<union>\<Union>T\<in>({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T" by auto
  then have "{\<Union>T}\<union>\<Union>T\<subseteq>\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T)" by auto moreover
  have "({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T\<subseteq>({one-point compactification of}(CoFinite (\<Union>T)))\<union>T" by auto
  then have "\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T)\<subseteq>\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))\<union>T)" by auto
  with tot2 have "\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T)\<subseteq>{\<Union>T}\<union>\<Union>T" by auto
  ultimately have TOT:"\<Union>((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T)={\<Union>T}\<union>\<Union>T" by auto
  {
    fix A assume AS:"A\<subseteq>\<Union>T" "(((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T){restricted to}A) {is hyperconnected}"
    from AS(1,2) have e0:"((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T){restricted to}A=(((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T){restricted to}\<Union>T){restricted to}A"
      using subspace_of_subspace[of "A""\<Union>T""((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T)"] TOT by auto
    have e1:"(((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T){restricted to}(\<Union>T))=((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}){restricted to}\<Union>T)\<union>(T{restricted to}\<Union>T)"
      unfolding RestrictedTo_def by auto
    {
      fix A assume "A\<in>T{restricted to}\<Union>T"
      then obtain B where "B\<in>T""A=B\<inter>\<Union>T" unfolding RestrictedTo_def by auto
      then have "A=B" by auto
      with \<open>B\<in>T\<close> have "A\<in>T" by auto
    }
    then have "T{restricted to}\<Union>T\<subseteq>T" by auto moreover
      {
      fix A assume "A\<in>T"
      then have "\<Union>T\<inter>A=A" by auto
      with \<open>A\<in>T\<close> have "A\<in>T{restricted to}\<Union>T" unfolding RestrictedTo_def by auto
    }
    ultimately have "T{restricted to}\<Union>T=T" by auto moreover
    {
      fix A assume "A\<in>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}){restricted to}\<Union>T"
      then obtain B where "B\<in>({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}""\<Union>T\<inter>B=A" unfolding RestrictedTo_def by auto
      then have "B\<in>({one-point compactification of}(CoFinite (\<Union>T)))""\<Union>T\<inter>B=A" by auto
      then have "A\<in>({one-point compactification of}(CoFinite (\<Union>T))){restricted to}\<Union>T" unfolding RestrictedTo_def by auto
      then have "A\<in>(CoFinite (\<Union>T))" using topology0.open_subspace(2)[OF topology0_CoCardinal[OF InfCard_nat]]
        union_cocardinal unfolding Cofinite_def by auto
      with T1 have "A\<in>T" using T1_cocardinal_coarser by auto
    }
    then have "(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}){restricted to}\<Union>T\<subseteq>T" by auto
    moreover note e1 ultimately
    have "((({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}} \<union> T) {restricted to} (\<Union>T)) =T" by auto
    with e0 have "((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T){restricted to}A=T{restricted to}A" by auto
    with assms(1) AS have "A{is in the spectrum of}IsHConnected" unfolding antiProperty_def by auto
  }
  then have reg:"\<forall>A\<in>Pow(\<Union>T). ((((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T){restricted to}A) {is hyperconnected}) \<longrightarrow>(A{is in the spectrum of}IsHConnected)" by auto
  have "\<Union>T\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
  then have P:"\<Union>T\<in>((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T)" by auto
  {
    fix B assume sub:"B\<in>Pow(\<Union>T \<union>{\<Union>T})" and hyp:"((((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T){restricted to}B) {is hyperconnected})"
    from P have  subop:"\<Union>T\<inter>B\<in>(((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T){restricted to}B)" unfolding RestrictedTo_def by auto
    with hyp have hypSub:"((((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T){restricted to}B){restricted to}(\<Union>T\<inter>B)){is hyperconnected}" using topology0.open_subspace_hyperconn
      topology0.Top_1_L4 COF_comp_is_top[OF T1 assms(2)] unfolding topology0_def by auto
    from sub TOT have "B \<subseteq> \<Union>(({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}} \<union> T)" by auto
    then have "(((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T){restricted to}(\<Union>T\<inter>B))=(((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T){restricted to}B){restricted to}(\<Union>T\<inter>B)"
      using subspace_of_subspace[of "\<Union>T\<inter>B""B""((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T)"] by auto
    with hypSub have "((({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}} \<union> T) {restricted to} (\<Union>T \<inter> B)){is hyperconnected}" by auto
    with reg have "(\<Union>T\<inter>B){is in the spectrum of}IsHConnected" by auto
    then have le:"\<Union>T\<inter>B\<lesssim>1" using HConn_spectrum by auto
    {
      fix x assume x:"x\<in>\<Union>T\<inter>B"
      with le have sing:"\<Union>T\<inter>B={x}" using lepoll_1_is_sing by auto
      {
        fix y assume y:"y\<in>B"
        then have "y\<in>\<Union>T \<union>{\<Union>T}" using sub by auto
        with y have "y\<in>\<Union>T\<inter>B\<or>y=\<Union>T" by auto
        with sing have "y=x\<or>y=\<Union>T" by auto
      }
      then have "B\<subseteq>{x,\<Union>T}" by auto
      with x have disj:"B={x}\<or>B={x,\<Union>T}" by auto
      {
        assume "\<Union>T\<in>B"
        with disj have B:"B={x,\<Union>T}" by auto
        from sing subop have singOp:"{x}\<in>(((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T){restricted to}B)"
          by auto
        have "{x}{is closed in}(CoFinite \<Union>T)" using topology0.T1_iff_singleton_closed[OF topology0_CoCardinal[OF InfCard_nat]] cocardinal_is_T1[OF InfCard_nat]
          x union_cocardinal unfolding Cofinite_def by auto
        moreover 
        have "Finite({x})" by auto
        then have spec:"{x}{is in the spectrum of} (\<lambda>T. (\<Union>T) {is compact in}T)" using compact_spectrum by auto
        have "((CoFinite \<Union>T){restricted to}{x}){is a topology}""\<Union>((CoFinite \<Union>T){restricted to}{x})={x}"
          using topology0.Top_1_L4[OF topology0_CoCardinal[OF InfCard_nat]] unfolding RestrictedTo_def Cofinite_def
          using x union_cocardinal by auto
        with spec have "{x}{is compact in}((CoFinite \<Union>T){restricted to}{x})" unfolding Spec_def
          by auto
        then have "{x}{is compact in}(CoFinite \<Union>T)" using compact_subspace_imp_compact
          by auto moreover note x
        ultimately have "{\<Union>T}\<union>(\<Union>T-{x})\<in>{one-point compactification of}(CoFinite (\<Union>T))" unfolding OPCompactification_def
          using union_cocardinal unfolding Cofinite_def by auto moreover
        {
          assume A:"{\<Union>T}\<union>(\<Union>T-{x})={\<Union>T}"
          {
            fix y assume P:"y\<in>\<Union>T-{x}"
            then have "y\<in>{\<Union>T}\<union>(\<Union>T-{x})" by auto
            then have "y=\<Union>T" using A by auto
            with N P have "False" by auto
          }
          then have "\<Union>T-{x}=0" by auto
          with x have "\<Union>T={x}" by auto
          then have "\<Union>T\<approx>1" using singleton_eqpoll_1 by auto moreover
          have "1\<prec>nat" using n_lesspoll_nat by auto
          ultimately have "\<Union>T\<prec>nat" using eq_lesspoll_trans by auto
          then have "False" using assms(2) by auto
        }
        ultimately have "{\<Union>T}\<union>(\<Union>T-{x})\<in>({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}" by auto
        then have  "{\<Union>T}\<union>(\<Union>T-{x})\<in>(((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T))" by auto
        then have "B\<inter>({\<Union>T}\<union>(\<Union>T-{x}))\<in>(((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T){restricted to}B)" unfolding RestrictedTo_def by auto
        moreover have "B\<inter>({\<Union>T}\<union>(\<Union>T-{x}))={\<Union>T}" using B by auto
        ultimately have "{\<Union>T}\<in>(((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T){restricted to}B)" by auto
        with singOp hyp N x have "False" unfolding IsHConnected_def by auto
      }
      with disj have "B={x}" by auto
      then have "B\<approx>1" using singleton_eqpoll_1 by auto
      then have "B\<lesssim>1" using eqpoll_imp_lepoll by auto
    }
    then have "\<Union>T\<inter>B\<noteq>0\<longrightarrow>B\<lesssim>1" by blast
    moreover
    {
      assume "\<Union>T\<inter>B=0"
      with sub have "B\<subseteq>{\<Union>T}" by auto
      then have "B\<lesssim>{\<Union>T}" using subset_imp_lepoll by auto
      then have "B\<lesssim>1" using singleton_eqpoll_1 lepoll_eq_trans by auto
    }
    ultimately have "B\<lesssim>1" by auto
    then have "B{is in the spectrum of}IsHConnected" using HConn_spectrum by auto
  }
  then show ?thesis unfolding antiProperty_def using TOT by auto
qed

text\<open>The previous construction, applied to a densely ordered topology, gives the desired counterexample.
What happends is that every neighbourhood of \<open>\<Union>T\<close> is dense; because there are no finite open
sets, and hence meets every non-empty open set. In conclusion, \<open>\<Union>T\<close> cannot be separated from other points
by disjoint open sets.\<close>

text\<open>Every open set that contains \<open>\<Union>T\<close> is dense, when considering the order
topology in a densely ordered set with more than two points.\<close>

theorem neigh_infPoint_dense:
  fixes T X r
  defines T_def:"T \<equiv> (OrdTopology X r)"
  assumes "IsLinOrder(X,r)" "X{is dense with respect to}r"
    "\<exists>x y. x\<noteq>y\<and>x\<in>X\<and>y\<in>X" "U\<in>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T" "\<Union>T\<in>U"
    "V\<in>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T" "V\<noteq>0"
  shows "U\<inter>V\<noteq>0"
proof
  have N:"\<Union>T\<notin>(\<Union>T)" using mem_not_refl by auto
  have tot1:"\<Union>({one-point compactification of}(CoFinite (\<Union>T)))={\<Union>T}\<union>\<Union>T" using topology0.op_compact_total[OF topology0_CoCardinal[OF InfCard_nat], of "\<Union>T"]
        union_cocardinal[of "nat""\<Union>T"] unfolding Cofinite_def by auto 
  then have "(\<Union>({one-point compactification of}(CoFinite (\<Union>T))))\<union>\<Union>T={\<Union>T}\<union>\<Union>T" by auto moreover
  have "\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))\<union>T)=(\<Union>({one-point compactification of}(CoFinite (\<Union>T))))\<union>\<Union>T"
    by auto
  ultimately have tot2:"\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))\<union>T)={\<Union>T}\<union>\<Union>T" by auto
  have "{\<Union>T}\<union>\<Union>T\<in>({one-point compactification of}(CoFinite (\<Union>T)))" using union_open[OF topology0.op_comp_is_top[OF topology0_CoCardinal[OF InfCard_nat]],of "{one-point compactification of}(CoFinite (\<Union>T))"]
    tot1 unfolding Cofinite_def by auto moreover
  {
    assume "\<Union>T=0"
    then have "X=0" unfolding T_def using union_ordtopology[OF assms(2)] assms(4) by auto
    then have "False" using assms(4) by auto
  }
  then have "\<Union>T\<noteq>0" by auto
  with N have Not:"\<not>(\<Union>T\<subseteq>{\<Union>T})" by auto
  {
    assume "{\<Union>T}\<union>\<Union>T={\<Union>T}" moreover
    have "\<Union>T\<subseteq>{\<Union>T}\<union>\<Union>T" by auto ultimately
    have "\<Union>T\<subseteq>{\<Union>T}" by auto
    with Not have "False" by auto
  }
  then have "{\<Union>T}\<union>\<Union>T\<noteq>{\<Union>T}" by auto ultimately
  have "{\<Union>T}\<union>\<Union>T\<in>({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}" by auto
  then have "{\<Union>T}\<union>\<Union>T\<in>({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T" by auto
  then have "{\<Union>T}\<union>\<Union>T\<subseteq>\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T)" by auto moreover
  have "({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T\<subseteq>({one-point compactification of}(CoFinite (\<Union>T)))\<union>T" by auto
  then have "\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T)\<subseteq>\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))\<union>T)" by auto
  with tot2 have "\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T)\<subseteq>{\<Union>T}\<union>\<Union>T" by auto
  ultimately have TOT:"\<Union>((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T)={\<Union>T}\<union>\<Union>T" by auto
  assume A:"U\<inter>V=0"
  with assms(6) have NN:"\<Union>T\<notin>V" by auto
  with assms(7) have "V\<in>(CoFinite \<Union>T)\<union>T" unfolding OPCompactification_def using union_cocardinal
    unfolding Cofinite_def by auto
  moreover have "T{is T\<^sub>2}" unfolding T_def using order_top_T2[OF assms(2)] assms(4) by auto
  then have T1:"T{is T\<^sub>1}" using T2_is_T1 by auto
  ultimately have VopT:"V\<in>T" using topology0.T1_cocardinal_coarser[OF topology0_ordtopology(1)[OF assms(2)]]
    unfolding T_def by auto
  from A assms(7) have "V\<subseteq>\<Union>((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T)-U" by auto
  then have "V\<subseteq>({\<Union>T}\<union>\<Union>T)-U" using TOT by auto
  then have "V\<subseteq>(\<Union>T)-U" using NN by auto
  from N have "U\<notin>T" using assms(6) by auto
  then have "U\<notin>(CoFinite \<Union>T)\<union>T" using T1 topology0.T1_cocardinal_coarser[OF topology0_ordtopology(1)[OF assms(2)]]
    unfolding T_def using union_cocardinal union_ordtopology[OF assms(2)] assms(4) by auto
  with assms(5,6) obtain B where U:"U={\<Union>T}\<union>(\<Union>T-B)" "B{is closed in}(CoFinite \<Union>T)" "B\<noteq>\<Union>T"
    unfolding OPCompactification_def using union_cocardinal unfolding Cofinite_def by auto
  then have "U={\<Union>T}\<union>(\<Union>T-B)" "B=\<Union>T \<or> B\<prec>nat" "B\<noteq>\<Union>T" using closed_sets_cocardinal unfolding Cofinite_def
    by auto
  then have "U={\<Union>T}\<union>(\<Union>T-B)" "B\<prec>nat" by auto
  with N have "\<Union>T-U=\<Union>T-(\<Union>T-B)" by auto
  then have "\<Union>T-U=B" using U(2) unfolding IsClosed_def using union_cocardinal unfolding Cofinite_def
    by auto
  with \<open>B\<prec>nat\<close> have "Finite(\<Union>T-U)" using lesspoll_nat_is_Finite by auto
  with \<open>V\<subseteq>(\<Union>T)-U\<close> have "Finite(V)" using subset_Finite by auto
  from assms(8) obtain v where "v\<in>V" by auto
  with VopT have "\<exists>R\<in>{IntervalX(X, r, b, c) . \<langle>b,c\<rangle> \<in> X \<times> X} \<union> {LeftRayX(X, r, b) . b \<in> X} \<union>{RightRayX(X, r, b) . b \<in> X}. R \<subseteq> V \<and> v \<in> R" using 
    point_open_base_neigh[OF Ordtopology_is_a_topology(2)[OF assms(2)]] unfolding T_def by auto
  then obtain R where R_def:"R\<in>{IntervalX(X, r, b, c) . \<langle>b,c\<rangle> \<in> X \<times> X} \<union> {LeftRayX(X, r, b) . b \<in> X} \<union>{RightRayX(X, r, b) . b \<in> X}" "R\<subseteq>V" "v\<in>R" by blast
  moreover
  {
    assume "R\<in>{IntervalX(X, r, b, c) . \<langle>b,c\<rangle> \<in> X \<times> X}"
    then obtain b c where lim:"b\<in>X""c\<in>X""R=IntervalX(X, r, b, c)" by auto
    with \<open>v\<in>R\<close> have " \<not> Finite(R)" using dense_order_inf_intervals[OF assms(2) _ _ _ assms(3)] 
      by auto
    with \<open>R\<subseteq>V\<close> \<open>Finite(V)\<close> have "False" using subset_Finite by auto
  } moreover
  {
    assume "R\<in>{LeftRayX(X, r, b) . b \<in> X}"
    then obtain b where lim:"b\<in>X""R=LeftRayX(X, r, b)" by auto
    with \<open>v\<in>R\<close> have " \<not> Finite(R)" using dense_order_inf_lrays[OF assms(2) _ _ assms(3)] by auto 
    with \<open>R\<subseteq>V\<close> \<open>Finite(V)\<close> have "False" using subset_Finite by auto
  } moreover
  {
    assume "R\<in>{RightRayX(X, r, b) . b \<in> X}"
    then obtain b where lim:"b\<in>X""R=RightRayX(X, r, b)" by auto
    with \<open>v\<in>R\<close> have " \<not> Finite(R)" using dense_order_inf_rrays[OF assms(2)_ _ assms(3)] by auto
    with \<open>R\<subseteq>V\<close> \<open>Finite(V)\<close> have "False" using subset_Finite by auto
  } ultimately
  show "False" by auto
qed

text\<open>A densely ordered set with more than one point gives an order topology.
Applying the previous construction to this topology we get a non locally-Hausdorff space.\<close>
  
theorem OPComp_cofinite_dense_order_not_loc_T2:
  fixes T X r
  defines T_def:"T \<equiv> (OrdTopology X r)"
  assumes "IsLinOrder(X,r)" "X{is dense with respect to}r"
    "\<exists>x y. x\<noteq>y\<and>x\<in>X\<and>y\<in>X"
  shows "\<not>((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T){is locally-T\<^sub>2})"
proof
  have N:"\<Union>T\<notin>(\<Union>T)" using mem_not_refl by auto
  have tot1:"\<Union>({one-point compactification of}(CoFinite (\<Union>T)))={\<Union>T}\<union>\<Union>T" using topology0.op_compact_total[OF topology0_CoCardinal[OF InfCard_nat], of "\<Union>T"]
        union_cocardinal[of "nat""\<Union>T"] unfolding Cofinite_def by auto 
  then have "(\<Union>({one-point compactification of}(CoFinite (\<Union>T))))\<union>\<Union>T={\<Union>T}\<union>\<Union>T" by auto moreover
  have "\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))\<union>T)=(\<Union>({one-point compactification of}(CoFinite (\<Union>T))))\<union>\<Union>T"
    by auto
  ultimately have tot2:"\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))\<union>T)={\<Union>T}\<union>\<Union>T" by auto
  have "{\<Union>T}\<union>\<Union>T\<in>({one-point compactification of}(CoFinite (\<Union>T)))" using union_open[OF topology0.op_comp_is_top[OF topology0_CoCardinal[OF InfCard_nat]],of "{one-point compactification of}(CoFinite (\<Union>T))"]
    tot1 unfolding Cofinite_def by auto moreover
  {
    assume "\<Union>T=0"
    then have "X=0" unfolding T_def using union_ordtopology[OF assms(2)] assms(4) by auto
    then have "False" using assms(4) by auto
  }
  then have "\<Union>T\<noteq>0" by auto
  with N have Not:"\<not>(\<Union>T\<subseteq>{\<Union>T})" by auto
  {
    assume "{\<Union>T}\<union>\<Union>T={\<Union>T}" moreover
    have "\<Union>T\<subseteq>{\<Union>T}\<union>\<Union>T" by auto ultimately
    have "\<Union>T\<subseteq>{\<Union>T}" by auto
    with Not have "False" by auto
  }
  then have "{\<Union>T}\<union>\<Union>T\<noteq>{\<Union>T}" by auto ultimately
  have "{\<Union>T}\<union>\<Union>T\<in>({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}" by auto
  then have "{\<Union>T}\<union>\<Union>T\<in>({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T" by auto
  then have "{\<Union>T}\<union>\<Union>T\<subseteq>\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T)" by auto moreover
  have "({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T\<subseteq>({one-point compactification of}(CoFinite (\<Union>T)))\<union>T" by auto
  then have "\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T)\<subseteq>\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))\<union>T)" by auto
  with tot2 have "\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T)\<subseteq>{\<Union>T}\<union>\<Union>T" by auto
  ultimately have TOT:"\<Union>((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}})\<union>T)={\<Union>T}\<union>\<Union>T" by auto
  have T1:"T{is T\<^sub>1}" using order_top_T2[OF assms(2,4)] T2_is_T1 unfolding T_def by auto moreover
  from assms(4) obtain b c where B:"b\<in>X""c\<in>X""b\<noteq>c" by auto
  {
    assume "\<langle>b,c\<rangle>\<notin>r"
    with assms(2) have "\<langle>c,b\<rangle>\<in>r" unfolding IsLinOrder_def IsTotal_def using \<open>b\<in>X\<close>\<open>c\<in>X\<close> by auto
    with assms(3) B obtain z where "z\<in>X-{b,c}""\<langle>c,z\<rangle>\<in>r""\<langle>z,b\<rangle>\<in>r" unfolding IsDense_def by auto
    then have "IntervalX(X,r,c,b)\<noteq>0" unfolding IntervalX_def using Order_ZF_2_L1 by auto
    then have "\<not>(Finite(IntervalX(X,r,c,b)))" using dense_order_inf_intervals[OF assms(2) _ \<open>c\<in>X\<close>\<open>b\<in>X\<close> assms(3)]
      by auto moreover
    have "IntervalX(X,r,c,b)\<subseteq>X" unfolding IntervalX_def by auto
    ultimately have "\<not>(Finite(X))" using subset_Finite by auto
    then have "\<not>(X\<prec>nat)" using lesspoll_nat_is_Finite by auto
  }
  moreover
  {
    assume "\<langle>b,c\<rangle>\<in>r"
    with assms(3) B obtain z where "z\<in>X-{b,c}""\<langle>b,z\<rangle>\<in>r""\<langle>z,c\<rangle>\<in>r" unfolding IsDense_def by auto
    then have "IntervalX(X,r,b,c)\<noteq>0" unfolding IntervalX_def using Order_ZF_2_L1 by auto
    then have "\<not>(Finite(IntervalX(X,r,b,c)))" using dense_order_inf_intervals[OF assms(2) _ \<open>b\<in>X\<close>\<open>c\<in>X\<close> assms(3)]
      by auto moreover
    have "IntervalX(X,r,b,c)\<subseteq>X" unfolding IntervalX_def by auto
    ultimately have "\<not>(Finite(X))" using subset_Finite by auto
    then have "\<not>(X\<prec>nat)" using lesspoll_nat_is_Finite by auto
  }
  ultimately have "\<not>(X\<prec>nat)" by auto
  with T1 have top:"(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T){is a topology}" using topology0.COF_comp_is_top[OF topology0_ordtopology[OF assms(2)]] unfolding T_def
    using union_ordtopology[OF assms(2,4)] by auto
  assume "(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T){is locally-T\<^sub>2}" moreover
  have "\<Union>T\<in>\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T)" using TOT by auto
  moreover have "\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T)\<in>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T)"
    using top unfolding IsATopology_def by auto
  ultimately have "\<exists>c\<in>Pow(\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T)). \<Union>T \<in> Interior(c, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T) \<and>
            ((({one-point compactification of}CoFinite \<Union>T) - {{\<Union>T}} \<union> T) {restricted to} c) {is T\<^sub>2}" unfolding IsLocallyT2_def IsLocally_def[OF top] by auto
  then obtain C where C:"C\<subseteq>\<Union>(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T)" "\<Union>T \<in> Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T)" and T2:"((({one-point compactification of}CoFinite \<Union>T) - {{\<Union>T}} \<union> T) {restricted to} C) {is T\<^sub>2}"
    by auto
  have sub:"Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T)\<subseteq>C" using topology0.Top_2_L1
    top unfolding topology0_def by auto
  have "(((({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T){restricted to}C){restricted to}(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T))=((({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T){restricted to}(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T))"
    using subspace_of_subspace[OF sub C(1)] by auto moreover
  have "(\<Union>((({one-point compactification of}CoFinite \<Union>T) - {{\<Union>T}} \<union> T) {restricted to} C))\<subseteq>C" unfolding RestrictedTo_def by auto
  with C(1) have "(\<Union>((({one-point compactification of}CoFinite \<Union>T) - {{\<Union>T}} \<union> T) {restricted to} C))=C" unfolding RestrictedTo_def by auto
  with sub have pp:"Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T)\<in>Pow(\<Union>((({one-point compactification of}CoFinite \<Union>T) - {{\<Union>T}} \<union> T) {restricted to} C))" by auto
  ultimately have T2_2:"(((({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T){restricted to}(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T))){is T\<^sub>2}"
    using T2_here[OF T2 pp] by auto
  have top2:"(((({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T){restricted to}(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T))){is a topology}"
    using topology0.Top_1_L4 top unfolding topology0_def by auto
  from C(2) pp have p1:"\<Union>T\<in>\<Union>(((({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T){restricted to}(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T)))"
    unfolding RestrictedTo_def by auto
    from top topology0.Top_2_L2 have intOP:"(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T))\<in>(({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T" unfolding topology0_def by auto
  {
    fix x assume "x\<noteq>\<Union>T" "x\<in>\<Union>(((({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T){restricted to}(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T)))"
    with p1 have "\<exists>U\<in>(((({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T){restricted to}(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T))). \<exists>V\<in>(((({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T){restricted to}(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T))).
      x\<in>U\<and>\<Union>T\<in>V\<and>U\<inter>V=0" using T2_2 unfolding isT2_def by auto
    then obtain U V where UV:"U\<in>(((({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T){restricted to}(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T)))"
      "V\<in>(((({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T){restricted to}(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T)))"
      "U\<noteq>0""\<Union>T\<in>V""U\<inter>V=0" by auto
    from UV(1) obtain UC where "U=(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T))\<inter>UC""UC\<in>(((({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T))"
      unfolding RestrictedTo_def by auto
    with top intOP have Uop:"U\<in>(({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T" unfolding IsATopology_def by auto
    from UV(2) obtain VC where "V=(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T))\<inter>VC""VC\<in>(((({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T))"
      unfolding RestrictedTo_def by auto
    with top intOP have "V\<in>(({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T" unfolding IsATopology_def by auto
    with UV(3-5) Uop neigh_infPoint_dense[OF assms(2-4),of "V""U"] union_ordtopology[OF assms(2,4)]
      have "False" unfolding T_def by auto
  }
  then have "\<Union>(((({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T){restricted to}(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T)))\<subseteq>{\<Union>T}"
    by auto
  with p1 have "\<Union>(((({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T){restricted to}(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T)))={\<Union>T}"
    by auto
  with top2 have "{\<Union>T}\<in>(((({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T){restricted to}(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T)))"
    unfolding IsATopology_def by auto
  then obtain W where UT:"{\<Union>T}=(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T))\<inter>W""W\<in>(({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T"
    unfolding RestrictedTo_def by auto
  from this(2) have "(Interior(C, (({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T))\<inter>W\<in>(({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T" using intOP
    top unfolding IsATopology_def by auto
  with UT(1) have "{\<Union>T}\<in>(({one-point compactification of}(CoFinite \<Union>T)) - {{\<Union>T}}) \<union> T" by auto
  then have "{\<Union>T}\<in>T" by auto
  with N show "False" by auto
qed

text\<open>This topology, from the previous result, gives a counter-example for
anti-hyperconnected implies locally-$T_2$.\<close>
  
theorem antiHConn_not_imp_loc_T2:
  fixes T X r
  defines T_def:"T \<equiv> (OrdTopology X r)"
  assumes "IsLinOrder(X,r)" "X{is dense with respect to}r"
    "\<exists>x y. x\<noteq>y\<and>x\<in>X\<and>y\<in>X"
  shows "\<not>((({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T){is locally-T\<^sub>2})"
  and "(({one-point compactification of}(CoFinite (\<Union>T)))-{{\<Union>T}}\<union>T){is anti-}IsHConnected"
  using OPComp_cofinite_dense_order_not_loc_T2[OF assms(2-4)] dense_order_infinite[OF assms(2-4)] union_ordtopology[OF assms(2,4)]
  topology0.COF_comp_antiHConn[OF topology0_ordtopology[OF assms(2)] topology0.T2_imp_anti_HConn[OF topology0_ordtopology[OF assms(2)] order_top_T2[OF assms(2,4)]]]
  unfolding T_def by auto

text\<open>Let's prove that $T_2$ spaces are locally-$T_2$, but that there
are locally-$T_2$ spaces which aren't $T_2$. In conclusion $T_2\Rightarrow$ locally
-$T_2\Rightarrow$ anti-hyperconnected; all implications proper.\<close>

theorem(in topology0) T2_imp_loc_T2:
  assumes "T{is T\<^sub>2}"
  shows "T{is locally-T\<^sub>2}"
proof-
  {
    fix x assume "x\<in>\<Union>T"
    {
      fix b assume b:"b\<in>T""x\<in>b"
      then have "(T{restricted to}b){is T\<^sub>2}" using T2_here assms by auto moreover
      from b have "x\<in>int(b)" using Top_2_L3 by auto
      ultimately have "\<exists>c\<in>Pow(b). x\<in>int(c)\<and>(T{restricted to}c){is T\<^sub>2}" by auto
    }
    then have "\<forall>b\<in>T. x\<in>b \<longrightarrow>(\<exists>c\<in>Pow(b). x\<in>int(c)\<and>(T{restricted to}c){is T\<^sub>2})" by auto
  }
  then show ?thesis unfolding IsLocallyT2_def IsLocally_def[OF topSpaceAssum] by auto
qed

text\<open>If there is a closed singleton, then we can consider a topology that
makes this point doble.\<close>

theorem(in topology0) doble_point_top:
  assumes "{m}{is closed in}T"
  shows "(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}) {is a topology}"
proof-
  {
    fix M assume M:"M\<subseteq>T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}"
    let ?MT="{V\<in>M. V\<in>T}"
    let ?Mm="{V\<in>M. V\<notin>T}"
    have unm:"\<Union>M=(\<Union>?MT)\<union>(\<Union>?Mm)" by auto
    have tt:"\<Union>?MT\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
    {
      assume "?Mm=0"
      then have "\<Union>?Mm=0" by auto
      with unm have "\<Union>M=(\<Union>?MT)" by auto
      with tt have "\<Union>M\<in>T" by auto
      then have "\<Union>M\<in>T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
    }
    moreover
    {
      assume AS:"?Mm\<noteq>0"
      then obtain V where V:"V\<in>M""V\<notin>T" by auto
      with M have "V\<in>{(U - {m}) \<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by blast
      then obtain U W where U:"V=(U-{m})\<union>{\<Union>T}\<union>W" "U\<in>T""m\<in>U" "W\<in>T" by auto
      let ?U="{\<langle>V,W\<rangle>\<in>T\<times>T. m\<in>V\<and> (V-{m})\<union>{\<Union>T}\<union>W\<in>?Mm}"
      let ?fU="{fst(B). B\<in>?U}"
      let ?sU="{snd(B). B\<in>?U}"
      have "?fU\<subseteq>T""?sU\<subseteq>T" by auto
      then have P:"\<Union>?fU\<in>T""\<Union>?sU\<in>T" using topSpaceAssum unfolding IsATopology_def by auto moreover
      have "\<langle>U,W\<rangle>\<in>?U" using U V by auto
      then have "m\<in>\<Union>?fU" by auto
      ultimately have s:"\<langle>\<Union>?fU,\<Union>?sU\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T" by auto
      moreover have r:"\<forall>S. \<forall>R. S\<in>{V\<in>T. m\<in>V}\<longrightarrow> R\<in>T\<longrightarrow>(S-{m})\<union>{\<Union>T}\<union>R\<in>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}"
        by auto
      ultimately have "(\<Union>?fU-{m})\<union>{\<Union>T}\<union>\<Union>?sU\<in>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
      {
        fix v assume "v\<in>\<Union>?Mm"
        then obtain V where v:"v\<in>V""V\<in>?Mm" by auto
        then have V:"V\<in>M""V\<notin>T" by auto
        with M have "V\<in>{U - {m} \<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by blast
        then obtain U W where U:"V=(U-{m})\<union>{\<Union>T}\<union>W" "U\<in>T""m\<in>U" "W\<in>T" by auto
        with v(1) have "v\<in>(U-{m})\<union>{\<Union>T}\<union>W" by auto
        then have "v\<in>U-{m}\<or>v=\<Union>T\<or>v\<in>W" by auto
        then have "(v\<in>U\<and>v\<noteq>m)\<or>v=\<Union>T\<or>v\<in>W" by auto
        moreover from U V have "\<langle>U,W\<rangle>\<in>?U" by auto
        ultimately have "v\<in>((\<Union>?fU)-{m})\<union>{\<Union>T}\<union>(\<Union>?sU)" by auto
      }
      then have "\<Union>?Mm\<subseteq>((\<Union>?fU)-{m})\<union>{\<Union>T}\<union>(\<Union>?sU)" by blast moreover
      {
        fix v assume v:"v\<in>((\<Union>?fU)-{m})\<union>{\<Union>T}\<union>(\<Union>?sU)"
        {
          assume "v=\<Union>T"
          then have "v\<in>(U-{m})\<union>{\<Union>T}\<union>W" by auto
          with \<open>\<langle>U,W\<rangle>\<in>?U\<close> have "v\<in>\<Union>?Mm" by auto
        }
        moreover
        {
          assume "v\<noteq>\<Union>T""v\<notin>\<Union>?sU"
          with v have "v\<in>((\<Union>?fU)-{m})" by auto
          then have "(v\<in>\<Union>?fU\<and>v\<noteq>m)" by auto
          then obtain W where "(v\<in>W\<and>W\<in>?fU\<and>v\<noteq>m)" by auto
          then have "v\<in>(W-{m})\<union>{\<Union>T}" "W\<in>?fU" by auto
          then obtain B where "fst(B)=W" "B\<in>?U" "v\<in>(W-{m})\<union>{\<Union>T}" by blast
          then have "v\<in>\<Union>?Mm" by auto
        }
        ultimately have "v\<in>\<Union>?Mm" by auto
      }
      then have "((\<Union>?fU)-{m})\<union>{\<Union>T}\<union>(\<Union>?sU)\<subseteq>\<Union>?Mm" by auto
      ultimately have "\<Union>?Mm=((\<Union>?fU)-{m})\<union>{\<Union>T}\<union>(\<Union>?sU)" by auto
      then have "\<Union>M=((\<Union>?fU)-{m})\<union>{\<Union>T}\<union>((\<Union>?sU)\<union>(\<Union>?MT))" using unm by auto
      moreover from P tt have "(\<Union>?sU)\<union>(\<Union>?MT)\<in>T" using topSpaceAssum 
        union_open[OF topSpaceAssum, of "{\<Union>?sU,\<Union>?MT}"] by auto
      with s have "\<langle>\<Union>?fU,(\<Union>?sU)\<union>(\<Union>?MT)\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T" by auto
      then have "((\<Union>?fU)-{m})\<union>{\<Union>T}\<union>((\<Union>?sU)\<union>(\<Union>?MT))\<in>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" using r
        by auto
      ultimately have "\<Union>M\<in>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
      then have "\<Union>M\<in>T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
    }
    ultimately
    have "\<Union>M\<in>T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
  }
  then have "\<forall>M\<in>Pow(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}). \<Union>M\<in>T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
  moreover
  {
    fix A B assume ass:"A\<in>T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}""B\<in>T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}"
    {
      assume A:"A\<in>T"
      {
        assume "B\<in>T"
        with A have "A\<inter>B\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
      }
      moreover
      {
        assume "B\<notin>T"
        with ass(2) have "B\<in>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
        then obtain U W where U:"U\<in>T""m\<in>U""W\<in>T""B=(U-{m})\<union>{\<Union>T}\<union>W" by auto moreover
        from A mem_not_refl have "\<Union>T\<notin>A" by auto
        ultimately have "A\<inter>B=A\<inter>((U-{m})\<union>W)" by auto
        then have eq:"A\<inter>B=(A\<inter>(U-{m}))\<union>(A\<inter>W)" by auto
        have "\<Union>T-{m}\<in>T" using assms unfolding IsClosed_def by auto
        with U(1) have O:"U\<inter>(\<Union>T-{m})\<in>T" using topSpaceAssum unfolding IsATopology_def
          by auto
        have "U\<inter>(\<Union>T-{m})=U-{m}" using U(1) by auto
        with O have "U-{m}\<in>T" by auto
        with A have "(A\<inter>(U-{m}))\<in>T" using topSpaceAssum unfolding IsATopology_def
          by auto
        moreover
        from A U(3) have "A\<inter>W\<in>T" using topSpaceAssum unfolding IsATopology_def
          by auto
        ultimately have "(A\<inter>(U-{m}))\<union>(A\<inter>W)\<in>T" using
          union_open[OF topSpaceAssum, of "{A\<inter>(U-{m}),A\<inter>W}"] by auto
        with eq have "A\<inter>B\<in>T" by auto
      }
      ultimately have "A\<inter>B\<in>T" by auto
    }
    moreover
    {
      assume "A\<notin>T"
      with ass(1) have A:"A\<in>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto      
        {
        assume B:"B\<in>T"
        from A obtain U W where U:"U\<in>T""m\<in>U""W\<in>T""A=(U-{m})\<union>{\<Union>T}\<union>W" by auto moreover
        from B mem_not_refl have "\<Union>T\<notin>B" by auto
        ultimately have "A\<inter>B=((U-{m})\<union>W)\<inter>B" by auto
        then have eq:"A\<inter>B=((U-{m})\<inter>B)\<union>(W\<inter>B)" by auto
        have "\<Union>T-{m}\<in>T" using assms unfolding IsClosed_def by auto
        with U(1) have O:"U\<inter>(\<Union>T-{m})\<in>T" using topSpaceAssum unfolding IsATopology_def
          by auto
        have "U\<inter>(\<Union>T-{m})=U-{m}" using U(1) by auto
        with O have "U-{m}\<in>T" by auto
        with B have "((U-{m})\<inter>B)\<in>T" using topSpaceAssum unfolding IsATopology_def
          by auto
        moreover
        from B U(3) have "W\<inter>B\<in>T" using topSpaceAssum unfolding IsATopology_def
          by auto
        ultimately have "((U-{m})\<inter>B)\<union>(W\<inter>B)\<in>T" using
          union_open[OF topSpaceAssum, of "{((U-{m})\<inter>B),(W\<inter>B)}"] by auto
        with eq have "A\<inter>B\<in>T" by auto
      }
      moreover
      {
        assume "B\<notin>T"
        with ass(2) have "B\<in>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
        then obtain U W where U:"U\<in>T""m\<in>U""W\<in>T""B=(U-{m})\<union>{\<Union>T}\<union>W" by auto moreover
        from A obtain UA WA where UA:"UA\<in>T""m\<in>UA""WA\<in>T""A=(UA-{m})\<union>{\<Union>T}\<union>WA" by auto
        ultimately have "A\<inter>B=(((UA-{m})\<union>WA)\<inter>((U-{m})\<union>W))\<union>{\<Union>T}" by auto
        then have eq:"A\<inter>B=((UA-{m})\<inter>(U-{m}))\<union>(WA\<inter>(U-{m}))\<union>((UA-{m})\<inter>W)\<union>(WA\<inter>W)\<union>{\<Union>T}" by auto
        have "\<Union>T-{m}\<in>T" using assms unfolding IsClosed_def by auto
        with U(1) UA(1) have O:"U\<inter>(\<Union>T-{m})\<in>T""UA\<inter>(\<Union>T-{m})\<in>T" using topSpaceAssum unfolding IsATopology_def
          by auto
        have "U\<inter>(\<Union>T-{m})=U-{m}""UA\<inter>(\<Union>T-{m})=UA-{m}" using U(1) UA(1) by auto
        with O have OO:"U-{m}\<in>T""UA-{m}\<in>T" by auto
        then have "((UA-{m})\<inter>(U-{m}))=UA\<inter>U-{m}" by auto
        moreover
        have "UA\<inter>U\<in>T""m\<in>UA\<inter>U" using U(1,2) UA(1,2) topSpaceAssum unfolding IsATopology_def
          by auto
        moreover
        from OO U(3) UA(3) have TT:"WA\<inter>(U-{m})\<in>T""(UA-{m})\<inter>W\<in>T""WA\<inter>W\<in>T" using topSpaceAssum unfolding IsATopology_def
          by auto
        from TT(2,3) have "((UA-{m})\<inter>W)\<union>(WA\<inter>W)\<in>T" using union_open[OF topSpaceAssum,
          of "{(UA-{m})\<inter>W,WA\<inter>W}"] by auto
        with TT(1) have "(WA\<inter>(U-{m}))\<union>(((UA-{m})\<inter>W)\<union>(WA\<inter>W))\<in>T" using union_open[OF topSpaceAssum,
          of "{WA\<inter>(U-{m}),((UA-{m})\<inter>W)\<union>(WA\<inter>W)}"] by auto
        ultimately
        have "A\<inter>B=(UA\<inter>U-{m})\<union>{\<Union>T}\<union>((WA\<inter>(U-{m}))\<union>(((UA-{m})\<inter>W)\<union>(WA\<inter>W)))"
          "(WA\<inter>(U-{m}))\<union>(((UA-{m})\<inter>W)\<union>(WA\<inter>W))\<in>T" "UA\<inter>U\<in>{V\<in>T. m\<in>V}" using eq by auto
        then have "\<exists>W\<in>T. A\<inter>B=(UA\<inter>U-{m})\<union>{\<Union>T}\<union>W" "UA\<inter>U\<in>{V\<in>T. m\<in>V}" by auto
        then have "A\<inter>B\<in>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
      }
      ultimately
      have "A\<inter>B\<in>T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
    }
    ultimately have "A\<inter>B\<in>T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
  }
  then have "\<forall>A\<in>T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}. \<forall>B\<in>T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}.
    A\<inter>B\<in>T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by blast
  ultimately show ?thesis unfolding IsATopology_def by auto
qed

text\<open>The previous topology is defined over a set with one more point.\<close>

lemma(in topology0) union_doublepoint_top:
  assumes "{m}{is closed in}T"
  shows "\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})=\<Union>T \<union>{\<Union>T}"
proof
  {
    fix x assume "x\<in>\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})"
    then obtain R where x:"x\<in>R""R\<in>T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by blast
    {
      assume "R\<in>T"
      with x(1) have "x\<in>\<Union>T" by auto
    }
    moreover
    {
      assume "R\<notin>T"
      with x(2) have "R\<in>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
      then obtain U W where "R=(U-{m})\<union>{\<Union>T}\<union>W""W\<in>T""U\<in>T""m\<in>U" by auto
      with x(1) have "x=\<Union>T\<or>x\<in>\<Union>T" by auto
    }
    ultimately have "x\<in>\<Union>T \<union>{\<Union>T}" by auto
  }
  then show "\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})\<subseteq>\<Union>T \<union>{\<Union>T}" by auto
  {
    fix x assume "x\<in>\<Union>T \<union>{\<Union>T}"
    then have dis:"x\<in>\<Union>T\<or>x=\<Union>T" by auto
    {
      assume "x\<in>\<Union>T"
      then have "x\<in>\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" by auto
    }
    moreover
    {
      assume "x\<notin>\<Union>T"
      with dis have "x=\<Union>T" by auto
      moreover from assms have "\<Union>T-{m}\<in>T""m\<in>\<Union>T" unfolding IsClosed_def by auto
      moreover have "0\<in>T" using empty_open topSpaceAssum by auto
      ultimately have "x\<in>(\<Union>T-{m})\<union>{\<Union>T}\<union>0" "(\<Union>T-{m})\<union>{\<Union>T}\<union>0\<in>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}"
        using union_open[OF topSpaceAssum] by auto
      then have "x\<in>(\<Union>T-{m})\<union>{\<Union>T}\<union>0" "(\<Union>T-{m})\<union>{\<Union>T}\<union>0\<in>T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}"
        by auto
      then have "x\<in>\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" by blast
    }
    ultimately have "x\<in>\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" by auto
  }
  then show "\<Union>T \<union>{\<Union>T}\<subseteq>\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" by auto
qed

text\<open>In this topology, the previous topological space is an open subspace.\<close>

theorem(in topology0) open_subspace_double_point:
  assumes "{m}{is closed in}T"
  shows "(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}\<Union>T=T" and "\<Union>T\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})"
proof-
  have N:"\<Union>T\<notin>\<Union>T" using mem_not_refl by auto
  {
    fix x assume "x\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}\<Union>T"
    then obtain U where U:"U\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})""x=\<Union>T\<inter>U"
      unfolding RestrictedTo_def by blast
    {
      assume "U\<notin>T"
      with U(1) have  "U\<in>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
      then obtain V W where VW:"U=(V-{m})\<union>{\<Union>T}\<union>W""V\<in>T""m\<in>V""W\<in>T" by auto
      with N U(2) have x:"x=(V-{m})\<union>W" by auto
      have "\<Union>T-{m}\<in>T" using assms unfolding IsClosed_def by auto
      then have "V\<inter>(\<Union>T-{m})\<in>T" using VW(2) topSpaceAssum unfolding IsATopology_def
        by auto moreover
      have "V-{m}=V\<inter>(\<Union>T-{m})" using VW(2,3) by auto ultimately
      have "V-{m}\<in>T" by auto
      with VW(4) have "(V-{m})\<union>W\<in>T" using union_open[OF topSpaceAssum, of "{V-{m},W}"]
        by auto
      with x have "x\<in>T" by auto
    }
    moreover
    {
      assume A:"U\<in>T"
      with U(2) have "x=U" by auto
      with A have "x\<in>T" by auto
    }
    ultimately have "x\<in>T" by auto
  }
  then have "(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}\<Union>T\<subseteq>T" by auto
  moreover
  {
    fix x assume x:"x\<in>T"
    then have "x\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" by auto moreover
    from x have "\<Union>T\<inter>x=x" by auto ultimately
    have "\<exists>M\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}). \<Union>T\<inter>M=x" by blast
    then have "x\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}\<Union>T" unfolding RestrictedTo_def
      by auto
  }
  ultimately show "(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}\<Union>T=T" by auto
  have P:"\<Union>T\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
  then show "\<Union>T\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" by auto
qed
  
text\<open>The previous topology construction applied to a $T_2$ non-discrite space
topology, gives a counter-example to: Every locally-$T_2$ space
is $T_2$.\<close>

text\<open>If there is a singleton which is not open, but closed; then the construction on that point
is not $T_2$.\<close>

theorem(in topology0) loc_T2_imp_T2_counter_1:
  assumes "{m}\<notin>T" "{m}{is closed in}T"
  shows "\<not>((T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}) {is T\<^sub>2})"
proof
  assume ass:"(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}) {is T\<^sub>2}"
  then have tot1:"\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})=\<Union>T \<union>{\<Union>T}" using union_doublepoint_top
    assms(2) by auto
  have "m\<noteq>\<Union>T" using mem_not_refl assms(2) unfolding IsClosed_def by auto moreover
  from ass tot1 have "\<forall>x y. x\<in>\<Union>T \<union>{\<Union>T} \<and> y\<in>\<Union>T \<union>{\<Union>T}\<and>x\<noteq>y \<longrightarrow> (\<exists>\<UU>\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}).
    \<exists>\<VV>\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}). x\<in>\<UU>\<and>y\<in>\<VV>\<and>\<UU>\<inter>\<VV>=0)" unfolding isT2_def by auto
  moreover
  from assms(2) have "m\<in>\<Union>T \<union>{\<Union>T}" unfolding IsClosed_def by auto moreover
  have "\<Union>T\<in>\<Union>T \<union>{\<Union>T}" by auto ultimately
  have "\<exists>\<UU>\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}). \<exists>\<VV>\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}). m\<in>\<UU>\<and>\<Union>T\<in>\<VV>\<and>\<UU>\<inter>\<VV>=0"
    by auto
  then obtain \<UU> \<VV> where UV:"\<UU>\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})"
    "\<VV>\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})""m\<in>\<UU>""\<Union>T\<in>\<VV>""\<UU>\<inter>\<VV>=0" using tot1 by blast
  then have "\<Union>T\<notin>\<UU>" by auto
  with UV(1) have P:"\<UU>\<in>T" by auto
  {
    assume "\<VV>\<in>T"
    then have "\<VV>\<subseteq>\<Union>T" by auto
    with UV(4) have "\<Union>T\<in>\<Union>T" using tot1 by auto
    then have "False" using mem_not_refl by auto
  }
  with UV(2) have "\<VV>\<in>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
  then obtain U W where V:"\<VV>=(U-{m})\<union>{\<Union>T}\<union>W" "U\<in>T""m\<in>U""W\<in>T" by auto
  from V(2,3) P have int:"U\<inter>\<UU>\<in>T""m\<in>U\<inter>\<UU>" using UV(3) topSpaceAssum 
    unfolding IsATopology_def by auto
  have "(U\<inter>\<UU>-{m})\<subseteq>\<UU>" "(U\<inter>\<UU>-{m})\<subseteq>\<VV>" using V(1) by auto
  then have "(U\<inter>\<UU>-{m})=0" using UV(5) by auto
  with int(2) have "U\<inter>\<UU>={m}" by auto
  with int(1) assms(1) show "False" by auto
qed

text\<open>This topology is locally-$T_2$.\<close>

theorem(in topology0) loc_T2_imp_T2_counter_2:
  assumes "{m}\<notin>T" "m\<in>\<Union>T" "T{is T\<^sub>2}"
  shows "(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}) {is locally-T\<^sub>2}"
proof-
  from assms(3) have "T{is T\<^sub>1}" using T2_is_T1 by auto
  with assms(2) have mc:"{m}{is closed in}T" using T1_iff_singleton_closed by auto
  have N:"\<Union>T\<notin>\<Union>T" using mem_not_refl by auto
  have res:"(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}\<Union>T=T"
    and P:"\<Union>T\<in>T" and Q:"\<Union>T\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" using open_subspace_double_point mc
    topSpaceAssum unfolding IsATopology_def by auto
  {
    fix A assume ass:"A\<in>\<Union>T \<union>{\<Union>T}"
    {
      assume "A\<noteq>\<Union>T"
      with ass have "A\<in>\<Union>T" by auto
      with Q res assms(3) have "\<Union>T\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})\<and> A\<in>\<Union>T \<and> (((T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}\<Union>T){is T\<^sub>2})" by auto
      then have "\<exists>Z\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}). A\<in>Z\<and>(((T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}Z){is T\<^sub>2})"
        by blast
    }
    moreover
    {
      assume A:"A=\<Union>T"
      have "\<Union>T\<in>T""m\<in>\<Union>T""0\<in>T" using assms(2) empty_open[OF topSpaceAssum] unfolding IsClosed_def using P by auto
      then have "(\<Union>T-{m})\<union>{\<Union>T}\<union>0\<in>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
      then have opp:"(\<Union>T-{m})\<union>{\<Union>T}\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" by auto
      {
        fix A1 A2 assume points:"A1\<in>(\<Union>T-{m})\<union>{\<Union>T}""A2\<in>(\<Union>T-{m})\<union>{\<Union>T}""A1\<noteq>A2"
        from points(1,2) have notm:"A1\<noteq>m""A2\<noteq>m" using assms(2) unfolding IsClosed_def 
          using mem_not_refl by auto
        {
          assume or:"A1\<in>\<Union>T""A2\<in>\<Union>T"
          with points(3) assms(3) obtain U V where UV:"U\<in>T""V\<in>T""A1\<in>U""A2\<in>V"
            "U\<inter>V=0" unfolding isT2_def by blast
          from UV(1,2) have "U\<inter>((\<Union>T-{m})\<union>{\<Union>T})\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})"
            "V\<inter>((\<Union>T-{m})\<union>{\<Union>T})\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})"
            unfolding RestrictedTo_def by auto moreover
          then have "U\<inter>(\<Union>T-{m})=U\<inter>((\<Union>T-{m})\<union>{\<Union>T})" "V\<inter>(\<Union>T-{m})=V\<inter>((\<Union>T-{m})\<union>{\<Union>T})" using UV(1,2) mem_not_refl[of "\<Union>T"]
            by auto
          ultimately have opUV:"U\<inter>(\<Union>T-{m})\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})"
            "V\<inter>(\<Union>T-{m})\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})" by auto
          moreover have "U\<inter>(\<Union>T-{m})\<inter>(V\<inter>(\<Union>T-{m}))=0" using UV(5) by auto moreover
          from UV(3) or(1) notm(1) have "A1\<in>U\<inter>(\<Union>T-{m})" by auto moreover
          from UV(4) or(2) notm(2) have "A2\<in>V\<inter>(\<Union>T-{m})" by auto ultimately
          have "\<exists>V. V\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})\<and> A1\<in>U\<inter>(\<Union>T-{m})\<and>A2\<in>V\<and>(U\<inter>(\<Union>T-{m}))\<inter>V=0" using exI[where x="V\<inter>(\<Union>T-{m})" and P="\<lambda>W. W\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})\<and>A1\<in>(U\<inter>(\<Union>T-{m}))\<and>A2\<in>W\<and>(U\<inter>(\<Union>T-{m}))\<inter>W=0"]
            using opUV(2) by auto
          then have "\<exists>U. U\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})\<and>(\<exists>V. V\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})\<and>
            A1\<in>U\<and>A2\<in>V\<and>U\<inter>V=0)" using exI[where x="U\<inter>(\<Union>T-{m})" and P="\<lambda>W. W\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})\<and>(\<exists>V. V\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})\<and> A1\<in>W\<and>A2\<in>V\<and>W\<inter>V=0)"]
            using opUV(1) by auto
          then have "\<exists>U\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}). (\<exists>V. V\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})\<and>A1\<in>U\<and>A2\<in>V\<and>U\<inter>V=0)" by blast
          then have "\<exists>U\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}). (\<exists>V\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}). A1\<in>U\<and>A2\<in>V\<and>U\<inter>V=0)" by blast
        }
        moreover
        {
          assume "A1\<notin>\<Union>T"
          then have ig:"A1=\<Union>T" using points(1) by auto
          {
            assume "A2\<notin>\<Union>T"
            then have "A2=\<Union>T" using points(2) by auto
            with points(3) ig have "False" by auto
          }
          then have igA2:"A2\<in>\<Union>T" by auto moreover
          have "m\<in>\<Union>T" using assms(2) unfolding IsClosed_def by auto
          moreover note notm(2) assms(3) ultimately obtain U V where UV:"U\<in>T""V\<in>T"
            "m\<in>U""A2\<in>V""U\<inter>V=0" unfolding isT2_def by blast
          from UV(1,3) have "U\<in>{W\<in>T. m\<in>W}" by auto moreover
          have "0\<in>T" using empty_open topSpaceAssum by auto ultimately
          have "(U-{m})\<union>{\<Union>T}\<in>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
          then have Uop:"(U-{m})\<union>{\<Union>T}\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" by auto
          from UV(2) have Vop:"V\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" by auto
          from UV(1-3,5) have sub:"V\<subseteq>(\<Union>T-{m})\<union>{\<Union>T}" "((U-{m})\<union>{\<Union>T})\<subseteq>(\<Union>T-{m})\<union>{\<Union>T}" by auto
          from sub(1) have "V=((\<Union>T-{m})\<union>{\<Union>T})\<inter>V" by auto
          then have VV:"V\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})" unfolding RestrictedTo_def
            using Vop by blast moreover
          from sub(2) have "((U-{m})\<union>{\<Union>T})=((\<Union>T-{m})\<union>{\<Union>T})\<inter>((U-{m})\<union>{\<Union>T})" by auto
          then have UU:"((U-{m})\<union>{\<Union>T})\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})" unfolding RestrictedTo_def
            using Uop by blast moreover
          from UV(2) have "((U-{m})\<union>{\<Union>T})\<inter>V=(U-{m})\<inter>V" using mem_not_refl by auto
          then  have "((U-{m})\<union>{\<Union>T})\<inter>V=0" using UV(5) by auto
          with UV(4) VV ig igA2 have "\<exists>V\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}).
            A1\<in>(U-{m})\<union>{\<Union>T}\<and>A2\<in>V\<and>((U-{m})\<union>{\<Union>T})\<inter>V=0" by auto
          with UU ig have "\<exists>U. U\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})\<and> (\<exists>V\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}).
            A1\<in>U\<and>A2\<in>V\<and>U\<inter>V=0)" using exI[where x="((U-{m})\<union>{\<Union>T})" and P="\<lambda>U. U\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})\<and> (\<exists>V\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}).
            A1\<in>U\<and>A2\<in>V\<and>U\<inter>V=0)"] by auto
          then have "\<exists>U\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}). (\<exists>V\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}).
            A1\<in>U\<and>A2\<in>V\<and>U\<inter>V=0)" by blast
        }
        moreover
        {
          assume "A2\<notin>\<Union>T"
          then have ig:"A2=\<Union>T" using points(2) by auto
          {
            assume "A1\<notin>\<Union>T"
            then have "A1=\<Union>T" using points(1) by auto
            with points(3) ig have "False" by auto
          }
          then have igA2:"A1\<in>\<Union>T" by auto moreover
          have "m\<in>\<Union>T" using assms(2) unfolding IsClosed_def by auto
          moreover note notm(1) assms(3) ultimately obtain U V where UV:"U\<in>T""V\<in>T"
            "m\<in>U""A1\<in>V""U\<inter>V=0" unfolding isT2_def by blast
          from UV(1,3) have "U\<in>{W\<in>T. m\<in>W}" by auto moreover
          have "0\<in>T" using empty_open topSpaceAssum by auto ultimately
          have "(U-{m})\<union>{\<Union>T}\<in>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
          then have Uop:"(U-{m})\<union>{\<Union>T}\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" by auto
          from UV(2) have Vop:"V\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" by auto
          from UV(1-3,5) have sub:"V\<subseteq>(\<Union>T-{m})\<union>{\<Union>T}" "((U-{m})\<union>{\<Union>T})\<subseteq>(\<Union>T-{m})\<union>{\<Union>T}" by auto
          from sub(1) have "V=((\<Union>T-{m})\<union>{\<Union>T})\<inter>V" by auto
          then have VV:"V\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})" unfolding RestrictedTo_def
            using Vop by blast moreover
          from sub(2) have "((U-{m})\<union>{\<Union>T})=((\<Union>T-{m})\<union>{\<Union>T})\<inter>((U-{m})\<union>{\<Union>T})" by auto
          then have UU:"((U-{m})\<union>{\<Union>T})\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})" unfolding RestrictedTo_def
            using Uop by blast moreover
          from UV(2) have "V\<inter>((U-{m})\<union>{\<Union>T})=V\<inter>(U-{m})" using mem_not_refl by auto
          then have "V\<inter>((U-{m})\<union>{\<Union>T})=0" using UV(5) by auto
          with UU UV(4) ig igA2 have "\<exists>U\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}).
            A1\<in>V\<and>A2\<in>U\<and>V\<inter>U=0" by auto
          with VV igA2 have "\<exists>U. U\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})\<and> (\<exists>V\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}).
            A1\<in>U\<and>A2\<in>V\<and>U\<inter>V=0)" using exI[where x="V" and P="\<lambda>U. U\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})\<and> (\<exists>V\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}).
            A1\<in>U\<and>A2\<in>V\<and>U\<inter>V=0)"] by auto
          then have "\<exists>U\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}). (\<exists>V\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}).
            A1\<in>U\<and>A2\<in>V\<and>U\<inter>V=0)" by blast
        }
        ultimately have "\<exists>U\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}). (\<exists>V\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}).
            A1\<in>U\<and>A2\<in>V\<and>U\<inter>V=0)" by blast
      }
      then have "\<forall>A1\<in>(\<Union>T-{m})\<union>{\<Union>T}. \<forall>A2\<in>(\<Union>T-{m})\<union>{\<Union>T}. A1\<noteq>A2 \<longrightarrow> (\<exists>U\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}). (\<exists>V\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}).
            A1\<in>U\<and>A2\<in>V\<and>U\<inter>V=0))" by auto moreover
      have "\<Union>((T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}))=(\<Union>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}))\<inter>((\<Union>T-{m})\<union>{\<Union>T})"
        unfolding RestrictedTo_def by auto
      then have "\<Union>((T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}))=(\<Union>T \<union>{\<Union>T})\<inter>((\<Union>T-{m})\<union>{\<Union>T})" using 
        union_doublepoint_top mc by auto
      then have "\<Union>((T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}))=(\<Union>T-{m})\<union>{\<Union>T}" by auto
      ultimately have "\<forall>A1\<in>\<Union>((T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})). \<forall>A2\<in>\<Union>((T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})). A1\<noteq>A2 \<longrightarrow> (\<exists>U\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}). (\<exists>V\<in>(T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T}).
            A1\<in>U\<and>A2\<in>V\<and>U\<inter>V=0))" by auto
      then have "((T \<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}((\<Union>T-{m})\<union>{\<Union>T})){is T\<^sub>2}" unfolding isT2_def
        by force
      with opp A have "\<exists>Z\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}). A\<in>Z\<and>(((T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}Z){is T\<^sub>2})"
        by blast
    }
    ultimately
    have "\<exists>Z\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}). A\<in>Z\<and>(((T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}Z){is T\<^sub>2})"
        by blast
  }
  then have "\<forall>A\<in>\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}). \<exists>Z\<in>T \<union> {U - {m} \<union> {\<Union>T} \<union> W . \<langle>U,W\<rangle> \<in> {V \<in> T . m \<in> V} \<times> T}.
     A \<in> Z \<and> ((T \<union> {U - {m} \<union> {\<Union>T} \<union> W . \<langle>U,W\<rangle> \<in> {V \<in> T . m \<in> V} \<times> T}) {restricted to} Z) {is T\<^sub>2}"
     using union_doublepoint_top mc by auto
  with topology0.loc_T2 show "(T \<union> {U - {m} \<union> {\<Union>T} \<union> W . \<langle>U,W\<rangle> \<in> {V \<in> T . m \<in> V} \<times> T}){is locally-T\<^sub>2}"
    unfolding topology0_def using doble_point_top mc by auto
qed

text\<open>There can be considered many more local properties, which; as
happens with locally-$T_2$; can distinguish between spaces other properties cannot.\<close>

end
