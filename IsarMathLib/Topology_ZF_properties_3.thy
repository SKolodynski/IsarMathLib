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

section \<open>Properties in Topology 3\<close>

theory Topology_ZF_properties_3 imports Topology_ZF_7 Finite_ZF_1 Topology_ZF_1b Topology_ZF_9
  Topology_ZF_properties_2 FinOrd_ZF
begin

text\<open>This theory file deals with more topological properties and the
relation with the previous ones in other theory files.\<close>

subsection\<open>More anti-properties\<close>

text\<open>In this section we study more anti-properties.\<close>

subsection\<open>First examples\<close>

text\<open>A first example of an anti-compact space is the discrete space.\<close>

lemma pow_compact_imp_finite:
  assumes "B{is compact in}Pow(A)"
  shows "Finite(B)"
proof-
  from assms have B:"B\<subseteq>A" "\<forall>M\<in>Pow(Pow(A)). B\<subseteq>\<Union>M \<longrightarrow>(\<exists>N\<in>FinPow(M). B\<subseteq>\<Union>N)"
    unfolding IsCompact_def by auto
  from B(1) have "{{x}. x\<in>B}\<in>Pow(Pow(A))" "B\<subseteq>\<Union>{{x}. x\<in>B}" by auto
  with B(2) have "\<exists>N\<in>FinPow({{x}. x\<in>B}). B\<subseteq>\<Union>N" by auto
  then obtain N where "N\<in>FinPow({{x}. x\<in>B})" "B\<subseteq>\<Union>N" by auto
  then have "Finite(N)" "N\<subseteq>{{x}. x\<in>B}" "B\<subseteq>\<Union>N" unfolding FinPow_def by auto
  then have "Finite(N)" "\<forall>b\<in>N. Finite(b)" "B\<subseteq>\<Union>N" by auto
  then have "B\<subseteq>\<Union>N" "Finite(\<Union>N)" using Finite_Union[of "N"] by auto
  then show "Finite(B)" using subset_Finite by auto
qed
    
theorem pow_anti_compact:
  shows "Pow(A){is anti-compact}"
proof-
  {
    fix B assume as:"B\<subseteq>\<Union>Pow(A)" "(\<Union>(Pow(A){restricted to}B)){is compact in}(Pow(A){restricted to}B)"
    then have sub:"B\<subseteq>A" by auto
    then have "Pow(B)=Pow(A){restricted to}B" unfolding RestrictedTo_def by blast
    with as(2) have "(\<Union>Pow(B)){is compact in}Pow(B)" by auto
    then have "B{is compact in}Pow(B)" by auto
    then have "Finite(B)" using pow_compact_imp_finite by auto
    then have "B{is in the spectrum of}(\<lambda>T. (\<Union>T){is compact in}T)" using compact_spectrum by auto
  }
  then show ?thesis unfolding IsAntiComp_def antiProperty_def by auto
qed

text\<open>In a previous file, @{file "Topology_ZF_5.thy"}, we proved that
the spectrum of the lindelöf property depends on the axiom of countable choice
on subsets of the power set of the natural number.\<close>

text\<open>In this context, the examples depend on wether this choice principle holds or not.
This is the reason that the examples of anti-lindeloef topologies are left for the next
section.\<close>

subsection\<open>Structural results\<close>

text\<open>We first differenciate the spectrum of the lindeloef property depending
on some axiom of choice.\<close>

lemma lindeloef_spec1:
  assumes "{the axiom of} nat {choice holds for subsets}(Pow(nat))"
  shows "(A {is in the spectrum of} (\<lambda>T. ((\<Union>T){is lindeloef in}T))) \<longleftrightarrow> (A\<lesssim>nat)"
  using compactK_spectrum[OF assms Card_nat] unfolding IsLindeloef_def.

lemma lindeloef_spec2:
  assumes "\<not>({the axiom of} nat {choice holds for subsets}(Pow(nat)))"
  shows "(A {is in the spectrum of} (\<lambda>T. ((\<Union>T){is lindeloef in}T))) \<longleftrightarrow> Finite(A)"
proof
  assume "Finite(A)"
  then have A:"A{is in the spectrum of} (\<lambda>T. ((\<Union>T){is compact in}T))" using compact_spectrum by auto
  have s:"nat\<lesssim>csucc(nat)" using le_imp_lesspoll[OF Card_csucc[OF Ord_nat]] lt_csucc[OF Ord_nat] le_iff by auto
  {
    fix T assume "T{is a topology}" "(\<Union>T){is compact in}T"
    then have "(\<Union>T){is compact of cardinal}nat{in}T" using Compact_is_card_nat by auto
    then have "(\<Union>T){is compact of cardinal}csucc(nat){in}T" using s compact_greater_card Card_csucc[OF Ord_nat] by auto
    then have "(\<Union>T){is lindeloef in}T" unfolding IsLindeloef_def by auto
  }
  then have "\<forall>T. T{is a topology} \<longrightarrow> ((\<Union>T){is compact in}T) \<longrightarrow> ((\<Union>T){is lindeloef in}T)" by auto
  with A show "A {is in the spectrum of} (\<lambda>T. ((\<Union>T){is lindeloef in}T))" using P_imp_Q_spec_inv[
    where Q="\<lambda>T. ((\<Union>T){is compact in}T)" and P="\<lambda>T. ((\<Union>T){is lindeloef in}T)"] by auto
next
  assume A:"A {is in the spectrum of} (\<lambda>T. ((\<Union>T){is lindeloef in}T))"
  then have reg:"\<forall>T. T{is a topology}\<and>\<Union>T\<approx>A \<longrightarrow> ((\<Union>T){is compact of cardinal} csucc(nat){in}T)" using Spec_def
    unfolding IsLindeloef_def by auto
  then have "A{is compact of cardinal} csucc(nat) {in} Pow(A)" using Pow_is_top[of "A"] by auto
  then have "\<forall>M\<in>Pow(Pow(A)). A\<subseteq>\<Union>M \<longrightarrow> (\<exists>N\<in>Pow(M). A\<subseteq>\<Union>N \<and> N\<prec>csucc(nat))" unfolding IsCompactOfCard_def by auto
  moreover
  have "{{x}. x\<in>A}\<in>Pow(Pow(A))" by auto
  moreover
  have "A=\<Union>{{x}. x\<in>A}" by auto
  ultimately have "\<exists>N\<in>Pow({{x}. x\<in>A}). A\<subseteq>\<Union>N \<and> N\<prec>csucc(nat)" by auto
  then obtain N where "N\<in>Pow({{x}. x\<in>A})" "A\<subseteq>\<Union>N" "N\<prec>csucc(nat)" by auto
  then have "N\<subseteq>{{x}. x\<in>A}" "N\<prec>csucc(nat)" "A\<subseteq>\<Union>N" using FinPow_def by auto
  {
    fix t
    assume "t\<in>{{x}. x\<in>A}"
    then obtain x where "x\<in>A""t={x}" by auto
    with \<open>A\<subseteq>\<Union>N\<close> have "x\<in>\<Union>N" by auto
    then obtain B where "B\<in>N""x\<in>B" by auto
    with \<open>N\<subseteq>{{x}. x\<in>A}\<close> have "B={x}" by auto
    with \<open>t={x}\<close>\<open>B\<in>N\<close> have "t\<in>N" by auto 
  }
  with \<open>N\<subseteq>{{x}. x\<in>A}\<close> have "N={{x}. x\<in>A}" by auto
  let ?B="{\<langle>x,{x}\<rangle>. x\<in>A}"
  from \<open>N={{x}. x\<in>A}\<close> have "?B:A\<rightarrow> N" unfolding Pi_def function_def by auto
  with \<open>N={{x}. x\<in>A}\<close> have "?B:inj(A,N)" unfolding inj_def using apply_equality by auto
  then have "A\<lesssim>N" using lepoll_def by auto
  with \<open>N\<prec>csucc(nat)\<close> have "A\<prec>csucc(nat)" using lesspoll_trans1 by auto
  then have "A\<lesssim>nat" using Card_less_csucc_eq_le Card_nat by auto
  then have "A\<prec>nat\<or>A\<approx>nat" using lepoll_iff_leqpoll by auto moreover
  {
    assume "A\<approx>nat"
    then have "nat\<approx>A" using eqpoll_sym by auto
    with A have "nat {is in the spectrum of} (\<lambda>T. ((\<Union>T){is lindeloef in}T))" using equipollent_spect[
      where P="(\<lambda>T. ((\<Union>T){is lindeloef in}T))"] by auto
    moreover
    have "Pow(nat){is a topology}" using Pow_is_top by auto
    moreover
    have "\<Union>Pow(nat)=nat" by auto
    then have "\<Union>Pow(nat)\<approx>nat" using eqpoll_refl by auto
    ultimately
    have "nat {is compact of cardinal} csucc(nat){in}Pow(nat)" using Spec_def unfolding IsLindeloef_def by auto
    then have "False" using Q_disc_comp_csuccQ_eq_Q_choice_csuccQ[OF InfCard_nat] assms by auto
  }
  ultimately have "A\<prec>nat" by auto
  then show "Finite(A)" using lesspoll_nat_is_Finite by auto
qed

text\<open>If the axiom of countable choice on subsets of the pow of the natural numbers
doesn't hold, then anti-lindeloef spaces are anti-compact.\<close>

theorem(in topology0) no_choice_imp_anti_lindeloef_is_anti_comp:
  assumes "\<not>({the axiom of} nat {choice holds for subsets}(Pow(nat)) )" "T{is anti-lindeloef}"
  shows "T{is anti-compact}"
proof-
  have s:"nat\<lesssim>csucc(nat)" using le_imp_lesspoll[OF Card_csucc[OF Ord_nat]] lt_csucc[OF Ord_nat] le_iff by auto
  {
    fix T assume "T{is a topology}" "(\<Union>T){is compact in}T"
    then have "(\<Union>T){is compact of cardinal}nat{in}T" using Compact_is_card_nat by auto
    then have "(\<Union>T){is compact of cardinal}csucc(nat){in}T" using s compact_greater_card Card_csucc[OF Ord_nat] by auto
    then have "(\<Union>T){is lindeloef in}T" unfolding IsLindeloef_def by auto
  }
  then have "\<forall>T. T{is a topology} \<longrightarrow> ((\<Union>T){is compact in}T) \<longrightarrow> ((\<Union>T){is lindeloef in}T)" by auto
  from eq_spect_rev_imp_anti[OF this] lindeloef_spec2[OF assms(1)] compact_spectrum
    show ?thesis using assms(2) unfolding IsAntiLin_def IsAntiComp_def by auto
qed

text\<open>If the axiom of countable choice holds for subsets of the power set of the
natural numbers, then there exists a topological space that is anti-lindeloef
but no anti-compact.\<close>

theorem no_choice_imp_anti_lindeloef_is_anti_comp:
  assumes "({the axiom of} nat {choice holds for subsets}(Pow(nat)))"
  shows "({one-point compactification of}Pow(nat)){is anti-lindeloef}"
proof-
  have t:"\<Union>({one-point compactification of}Pow(nat))={nat}\<union>nat" using topology0.op_compact_total
    unfolding topology0_def using Pow_is_top by auto
  have "{nat}\<approx>1" using singleton_eqpoll_1 by auto
  then have "{nat}\<prec>nat" using n_lesspoll_nat eq_lesspoll_trans by auto moreover
  have s:"nat\<prec>csucc(nat)" using lt_Card_imp_lesspoll[OF Card_csucc] lt_csucc[OF Ord_nat] by auto
  ultimately have "{nat}\<prec>csucc(nat)" using lesspoll_trans by blast
  with s have "{nat}\<union>nat\<prec>csucc(nat)" using less_less_imp_un_less[OF _ _ InfCard_csucc[OF InfCard_nat]]
    by auto
  then have "{nat}\<union>nat\<lesssim>nat" using Card_less_csucc_eq_le[OF Card_nat] by auto
  with t have r:"\<Union>({one-point compactification of}Pow(nat))\<lesssim>nat" by auto
  {
    fix A assume A:"A\<in>Pow(\<Union>({one-point compactification of}Pow(nat)))" "(\<Union>(({one-point compactification of}Pow(nat)){restricted to}A)){is lindeloef in}(({one-point compactification of}Pow(nat)){restricted to}A)"
    from A(1) have "A\<subseteq>\<Union>({one-point compactification of}Pow(nat))" by auto
    with r have "A\<lesssim>nat" using subset_imp_lepoll lepoll_trans by blast
    then have "A{is in the spectrum of}(\<lambda>T. ((\<Union>T){is lindeloef in}T))" using assms
      lindeloef_spec1 by auto
  }
  then show ?thesis unfolding IsAntiLin_def antiProperty_def by auto
qed

theorem op_comp_pow_nat_no_anti_comp:
  shows "\<not>(({one-point compactification of}Pow(nat)){is anti-compact})"
proof
  let ?T="({one-point compactification of}Pow(nat)){restricted to}({nat} \<union> nat)"
  assume antiComp:"({one-point compactification of}Pow(nat)){is anti-compact}"
  have "({nat} \<union> nat){is compact in}({one-point compactification of}Pow(nat))"
    using topology0.compact_op[of "Pow(nat)"] Pow_is_top[of "nat"] unfolding topology0_def
    by auto
  then have "({nat} \<union> nat){is compact in}?T" using compact_imp_compact_subspace Compact_is_card_nat by auto
  moreover have "\<Union>?T=(\<Union>({one-point compactification of}Pow(nat)))\<inter>({nat} \<union> nat)" unfolding RestrictedTo_def by auto
  then have "\<Union>?T={nat} \<union> nat" using topology0.op_compact_total unfolding topology0_def
    using Pow_is_top by auto
  ultimately have "(\<Union>?T){is compact in}?T" by auto
  with antiComp have "({nat} \<union> nat){is in the spectrum of}(\<lambda>T. (\<Union>T){is compact in}T)" unfolding IsAntiComp_def
    antiProperty_def using topology0.op_compact_total unfolding topology0_def using Pow_is_top by auto
  then have "Finite({nat} \<union> nat)" using compact_spectrum by auto
  then have "Finite(nat)" using subset_Finite by auto
  then show "False" using nat_not_Finite by auto
qed

text\<open>In coclusion, we reached another equivalence of this choice principle.\<close>

text\<open>The axiom of countable choice holds for subsets of the power set of the
natural numbers if and only if there exists a topological space which is anti-lindeloef
but not anti-compact; this space can be chosen as the one-point compactification
of the discrete topology on $\mathbb{N}$.\<close>

theorem acc_pow_nat_equiv1:
  shows "({the axiom of} nat {choice holds for subsets}(Pow(nat))) \<longleftrightarrow> (({one-point compactification of}Pow(nat)){is anti-lindeloef})"
  using op_comp_pow_nat_no_anti_comp no_choice_imp_anti_lindeloef_is_anti_comp
  topology0.no_choice_imp_anti_lindeloef_is_anti_comp topology0.op_comp_is_top
  Pow_is_top[of "nat"] unfolding topology0_def by auto

theorem acc_pow_nat_equiv2:
  shows "({the axiom of} nat {choice holds for subsets}(Pow(nat))) \<longleftrightarrow> (\<exists>T. T{is a topology}
  \<and> (T{is anti-lindeloef}) \<and> \<not>(T{is anti-compact}))"
  using op_comp_pow_nat_no_anti_comp no_choice_imp_anti_lindeloef_is_anti_comp
  topology0.no_choice_imp_anti_lindeloef_is_anti_comp topology0.op_comp_is_top
  Pow_is_top[of "nat"] unfolding topology0_def by auto

text\<open>In the file @{file "Topology_ZF_properties.thy"}, it is proven that $\mathbb{N}$ is
lindeloef if and only if the axiom of countable choice holds for subsets of $Pow(\mathbb{N})$.
Now we check that, in ZF, this space is always anti-lindeloef.\<close>

theorem nat_anti_lindeloef:
  shows "Pow(nat){is anti-lindeloef}"
proof-
  {
   fix A assume A:"A\<in>Pow(\<Union>Pow(nat))" "(\<Union>(Pow(nat){restricted to}A)){is lindeloef in}(Pow(nat){restricted to}A)"
    from A(1) have "A\<subseteq>nat" by auto
    then have "Pow(nat){restricted to}A=Pow(A)" unfolding RestrictedTo_def by blast
    with A(2) have lin:"A{is lindeloef in}Pow(A)" using subset_imp_lepoll by auto
    {
      fix T assume T:"T{is a topology}" "\<Union>T\<approx>A"
      then have "A\<approx>\<Union>T" using eqpoll_sym by auto
      then obtain f where f:"f\<in>bij(A,\<Union>T)" unfolding eqpoll_def by auto
      then have "f\<in>surj(A,\<Union>T)" unfolding bij_def by auto
      moreover then have "IsContinuous(Pow(A),T,f)" unfolding IsContinuous_def
        surj_def using func1_1_L3 by blast
      moreover have "two_top_spaces0(Pow(A),T,f)" unfolding two_top_spaces0_def
        using f T(1) Pow_is_top unfolding bij_def inj_def by auto
      ultimately have "(\<Union>T){is lindeloef in}T" using two_top_spaces0.cont_image_com
        lin unfolding IsLindeloef_def by auto
    }
    then have "A{is in the spectrum of} (\<lambda>T. ((\<Union>T){is lindeloef in}T))" unfolding Spec_def by auto
  }
  then show ?thesis unfolding IsAntiLin_def antiProperty_def by auto   
qed

text\<open>This result is interesting because depending on the different axioms we add
to ZF, it means two different things: 
\begin{itemize}
\item Every subspace of $\mathbb{N}$ is Lindeloef.
\item Only the compact subspaces of $\mathbb{N}$ are Lindeloef.
\end{itemize}
\<close>

text\<open>Now, we could wonder if the class of compact spaces and the class of lindeloef spaces being equal
is consistent in ZF. Let's find a topological space which is lindeloef and no compact
without assuming any axiom of choice or any negation of one. This will prove
that the class of lindeloef spaces and the class of compact spaces cannot be equal
in any model of ZF.\<close>

theorem lord_nat:
  shows "(LOrdTopology nat Le)={LeftRayX(nat,Le,n). n\<in>nat} \<union>{nat} \<union>{0}"
proof-
  {
    fix U assume U:"U\<subseteq>{LeftRayX(nat,Le,n). n\<in>nat} \<union>{nat}" "U\<noteq>0"
    {
      assume "nat\<in>U"
      with U have "\<Union>U=nat" unfolding LeftRayX_def by auto
      then have "\<Union>U\<in>{LeftRayX(nat,Le,n). n\<in>nat} \<union>{nat}\<union>{0}" by auto
    }
    moreover
    {
      assume "nat\<notin>U"
      with U have UU:"U\<subseteq>{LeftRayX(nat,Le,n). n\<in>nat}\<union>{0}" by auto
      {
        assume A:"\<exists>i. i\<in>nat\<and> \<Union>U\<subseteq> LeftRayX(nat,Le,i)"
        let ?M="\<mu> i. i\<in>nat \<and> \<Union>U\<subseteq> LeftRayX(nat,Le,i)"
        from A have M:"?M\<in>nat" "\<Union>U\<subseteq> LeftRayX(nat,Le,?M)" using LeastI[OF _ nat_into_Ord, where P="\<lambda>i. i\<in>nat \<and> \<Union>U\<subseteq> LeftRayX(nat,Le,i)"]
          by auto
        {
          fix y assume V:"y\<in>LeftRayX(nat,Le,?M)"
          then have y:"y\<in>nat" unfolding LeftRayX_def by auto
          {
            assume "\<forall>V\<in>U. y\<notin>V"
            then have "\<forall>m\<in>{n\<in>nat. LeftRayX(nat,Le,n)\<in>U}. y\<notin>LeftRayX(nat,Le,m)" using UU by auto
            then have "\<forall>m\<in>{n\<in>nat. LeftRayX(nat,Le,n)\<in>U}. \<langle>y,m\<rangle>\<notin>Le\<or>y=m" unfolding LeftRayX_def using y
              by auto
            then have RR:"\<forall>m\<in>{n\<in>nat. LeftRayX(nat,Le,n)\<in>U}. \<langle>m,y\<rangle>\<in>Le" using Le_directs_nat(1) y unfolding IsLinOrder_def IsTotal_def by blast
            {
              fix rr V assume "rr\<in>\<Union>U"
              then obtain V where V:"V\<in>U" "rr\<in>V" by auto
              with UU obtain m where m:"V=LeftRayX(nat,Le,m)" "m\<in>nat" by auto
              with V(1) RR have a:"\<langle>m,y\<rangle>\<in>Le" by auto
              from V(2) m(1) have b:"\<langle>rr,m\<rangle>\<in>Le" "rr\<in>nat-{m}" unfolding LeftRayX_def by auto
              from a b(1) have "\<langle>rr,y\<rangle>\<in>Le" using Le_directs_nat(1) unfolding IsLinOrder_def
                trans_def by blast moreover
              {
                assume "rr=y"
                with a b have "False" using Le_directs_nat(1) unfolding IsLinOrder_def antisym_def by blast
              }
              ultimately have "rr\<in>LeftRayX(nat,Le,y)" unfolding LeftRayX_def using b(2) by auto
            }
            then have "\<Union>U\<subseteq>LeftRayX(nat,Le,y)" by auto
            with y M(1) have "\<langle>?M,y\<rangle>\<in>Le" using Least_le by auto
            with V have "False" unfolding LeftRayX_def using Le_directs_nat(1) unfolding IsLinOrder_def antisym_def by blast
          }
          then have "y\<in>\<Union>U" by auto
        }
        then have "LeftRayX(nat,Le,?M)\<subseteq>\<Union>U" by auto
        with M(2) have "\<Union>U=LeftRayX(nat,Le,?M)" by auto
        with M(1) have "\<Union>U\<in>{LeftRayX(nat,Le,n). n\<in>nat} \<union>{nat}" by auto
      }
      moreover
      {
        assume "\<not>(\<exists>i. i \<in> nat \<and> \<Union>U \<subseteq> LeftRayX(nat, Le, i))"
        then have A:"\<forall>i. i\<in>nat \<longrightarrow> \<not>(\<Union>U \<subseteq> LeftRayX(nat, Le, i))" by auto
        {
          fix i assume i:"i\<in>nat"
          with A have AA:"\<not>(\<Union>U \<subseteq> LeftRayX(nat, Le, i))" by auto
          {
            assume "i\<notin>\<Union>U"
            then have "\<forall>V\<in>U. i\<notin>V" by auto
            then have "\<forall>m\<in>{n\<in>nat. LeftRayX(nat, Le, n)\<in>U}. i\<notin>LeftRayX(nat, Le, m)" by auto
            with i have "\<forall>m\<in>{n\<in>nat. LeftRayX(nat, Le, n)\<in>U}. \<langle>i,m\<rangle>\<notin>Le\<or>i=m" unfolding LeftRayX_def by auto
            with i have "\<forall>m\<in>{n\<in>nat. LeftRayX(nat, Le, n)\<in>U}. \<not>(i\<le>m)\<or>i=m" unfolding Le_def by auto
            then have "\<forall>m\<in>{n\<in>nat. LeftRayX(nat, Le, n)\<in>U}. m<i\<or>m=i" using not_le_iff_lt[OF nat_into_Ord[OF i]
              nat_into_Ord] by auto
            then have M:"\<forall>m\<in>{n\<in>nat. LeftRayX(nat, Le, n)\<in>U}. m\<le>i" using le_iff nat_into_Ord[OF i] by auto
            {
              fix s assume "s\<in>\<Union>U"
              then obtain n where n:"n\<in>nat" "s\<in>LeftRayX(nat, Le, n)" "LeftRayX(nat, Le, n)\<in>U"
                using UU by auto
              with M have ni:"n\<le>i" by auto
              from n(2) have sn:"s\<le>n" "s\<noteq>n" unfolding LeftRayX_def by auto
              then have "s\<le>i" "s\<noteq>i" using le_trans[OF sn(1) ni] le_anti_sym[OF sn(1)] ni by auto
              then have "s\<in>LeftRayX(nat, Le, i)" using i le_in_nat unfolding LeftRayX_def by auto
            }
            with AA have "False" by auto
          }
          then have "i\<in>\<Union>U" by auto
        }
        then have "nat\<subseteq>\<Union>U" by auto
        then have "\<Union>U=nat" using UU unfolding LeftRayX_def by auto
        then have "\<Union>U\<in>{LeftRayX(nat,Le,n). n\<in>nat} \<union>{nat} \<union>{0}" by auto
      }
      ultimately have "\<Union>U\<in>{LeftRayX(nat,Le,n). n\<in>nat} \<union>{nat} \<union>{0}" by auto
    }
    ultimately have "\<Union>U\<in>{LeftRayX(nat,Le,n). n\<in>nat} \<union>{nat} \<union>{0}" by auto
  }
  moreover
  {
    fix U assume "U=0"
    then have "\<Union>U\<in>{LeftRayX(nat,Le,n). n\<in>nat} \<union>{nat} \<union>{0}" by auto
  }
  ultimately have "\<forall>U. U\<subseteq>{LeftRayX(nat,Le,n). n\<in>nat} \<union>{nat} \<longrightarrow> \<Union>U\<in>{LeftRayX(nat,Le,n). n\<in>nat} \<union>{nat} \<union>{0}"
    by auto
  then have "{LeftRayX(nat,Le,n). n\<in>nat} \<union>{nat} \<union>{0}={\<Union>U. U\<in>Pow({LeftRayX(nat,Le,n). n\<in>nat} \<union>{nat})}" by blast
  then show ?thesis using LOrdtopology_ROrdtopology_are_topologies(2)[OF Le_directs_nat(1)]
    unfolding IsAbaseFor_def by auto
qed

lemma countable_lord_nat:
  shows "{LeftRayX(nat,Le,n). n\<in>nat} \<union>{nat} \<union>{0}\<prec>csucc(nat)"
proof-
  {
    fix e
    have "{e}\<approx>1" using singleton_eqpoll_1 by auto
    then have "{e}\<prec>nat" using n_lesspoll_nat eq_lesspoll_trans by auto moreover
    have s:"nat\<prec>csucc(nat)" using lt_Card_imp_lesspoll[OF Card_csucc] lt_csucc[OF Ord_nat] by auto
    ultimately have "{e}\<prec>csucc(nat)" using lesspoll_trans by blast
  }
  then have "{nat} \<union>{0}\<prec>csucc(nat)" using less_less_imp_un_less[OF _ _ InfCard_csucc[OF InfCard_nat], of "{nat}" "{0}"]
    by auto moreover
  let ?FF="{\<langle>n,LeftRayX(nat,Le,n)\<rangle>. n\<in>nat}"
  have ff:"?FF:nat\<rightarrow>{LeftRayX(nat,Le,n). n\<in>nat}" unfolding Pi_def domain_def function_def by auto
  then have su:"?FF\<in>surj(nat,{LeftRayX(nat,Le,n). n\<in>nat})" unfolding surj_def using apply_equality[
    OF _ ff] by auto
  then have "{LeftRayX(nat,Le,n). n\<in>nat}\<lesssim>nat" using surj_fun_inv_2[OF su lepoll_refl[of "nat"]] Ord_nat 
    by auto
  then have "{LeftRayX(nat,Le,n). n\<in>nat}\<prec>csucc(nat)" using Card_less_csucc_eq_le[OF Card_nat] by auto
  ultimately have "{LeftRayX(nat, Le, n) . n \<in> nat} \<union> ({nat} \<union> {0}) \<prec> csucc(nat)" using less_less_imp_un_less[OF _ _ InfCard_csucc[OF InfCard_nat]] by auto
  moreover have "{LeftRayX(nat, Le, n) . n \<in> nat} \<union> ({nat} \<union> {0})={LeftRayX(nat, Le, n) . n \<in> nat} \<union> {nat} \<union> {0}" by auto
  ultimately show ?thesis by auto
qed

corollary lindelof_lord_nat:
  shows "nat{is lindeloef in}(LOrdTopology nat Le)"
  unfolding IsLindeloef_def using countable_lord_nat lord_nat card_top_comp[OF Card_csucc[OF Ord_nat]]
    union_lordtopology_rordtopology(1)[OF Le_directs_nat(1)] by auto
  
theorem not_comp_lord_nat:
  shows "\<not>(nat{is compact in}(LOrdTopology nat Le))"
proof
  assume "nat{is compact in}(LOrdTopology nat Le)"
  with lord_nat have "nat{is compact in}({LeftRayX(nat,Le,n). n\<in>nat} \<union>{nat} \<union>{0})" by auto
  then have "\<forall>M\<in>Pow({LeftRayX(nat,Le,n). n\<in>nat} \<union>{nat} \<union>{0}). nat\<subseteq>\<Union>M \<longrightarrow> (\<exists>N\<in>FinPow(M). nat\<subseteq>\<Union>N)"
    unfolding IsCompact_def by auto moreover
  {
    fix n assume n:"n\<in>nat"
    then have "n<succ(n)" by auto
    then have "\<langle>n,succ(n)\<rangle>\<in>Le" "n\<noteq>succ(n)" using n nat_succ_iff by auto
    then have "n\<in>LeftRayX(nat,Le,succ(n))" unfolding LeftRayX_def using n by auto
    then have "n\<in>\<Union>({LeftRayX(nat,Le,n). n\<in>nat})" using n nat_succ_iff by auto
  }
  ultimately have "\<exists>N\<in>FinPow({LeftRayX(nat,Le,n). n\<in>nat}). nat\<subseteq>\<Union>N" by blast
  then obtain N where "N\<in>FinPow({LeftRayX(nat,Le,n). n\<in>nat})" "nat\<subseteq>\<Union>N" by auto
  then have N:"N\<subseteq>{LeftRayX(nat,Le,n). n\<in>nat}" "Finite(N)" "nat\<subseteq>\<Union>N" unfolding FinPow_def by auto
  let ?F="{\<langle>n,LeftRayX(nat,Le,n)\<rangle>. n\<in>{m\<in>nat. LeftRayX(nat,Le,m)\<in>N}}"
  have ff:"?F:{m\<in>nat. LeftRayX(nat,Le,m)\<in>N} \<rightarrow> N" unfolding Pi_def function_def by auto
  then have "?F\<in>surj({m\<in>nat. LeftRayX(nat,Le,m)\<in>N}, N)" unfolding surj_def using N(1) apply_equality[
    OF _ ff] by blast moreover
  {
    fix x y assume xyF:"x\<in>{m\<in>nat. LeftRayX(nat,Le,m)\<in>N}" "y\<in>{m\<in>nat. LeftRayX(nat,Le,m)\<in>N}" "?F`x=?F`y"
    then have "?F`x=LeftRayX(nat,Le,x)" "?F`y=LeftRayX(nat,Le,y)" using apply_equality[
      OF _ ff] by auto
    with xyF(3) have lxy:"LeftRayX(nat,Le,x)=LeftRayX(nat,Le,y)" by auto
    {
      fix r assume "r<x"
      then have "r\<le>x" "r\<noteq>x" using leI by auto
      with xyF(1) have "r\<in>LeftRayX(nat,Le,x)" unfolding LeftRayX_def using le_in_nat by auto
      then have "r\<in>LeftRayX(nat,Le,y)" using lxy by auto
      then have "r\<le>y" "r\<noteq>y" unfolding LeftRayX_def by auto
      then have "r<y" using le_iff by auto
    }
    then have "\<forall>r. r<x \<longrightarrow> r<y" by auto
    then have r:"\<not>(y<x)" by auto
    {
      fix r assume "r<y"
      then have "r\<le>y" "r\<noteq>y" using leI by auto
      with xyF(2) have "r\<in>LeftRayX(nat,Le,y)" unfolding LeftRayX_def using le_in_nat by auto
      then have "r\<in>LeftRayX(nat,Le,x)" using lxy by auto
      then have "r\<le>x" "r\<noteq>x" unfolding LeftRayX_def by auto
      then have "r<x" using le_iff by auto
    }
    then have "\<not>(x<y)" by auto
    with r have "x=y" using not_lt_iff_le[OF nat_into_Ord nat_into_Ord] xyF(1,2)
      le_anti_sym by auto
  }
  then have "?F\<in>inj({m\<in>nat. LeftRayX(nat,Le,m)\<in>N}, N)" unfolding inj_def using ff by auto
  ultimately have "?F\<in>bij({m\<in>nat. LeftRayX(nat,Le,m)\<in>N}, N)" unfolding bij_def by auto
  then have "{m\<in>nat. LeftRayX(nat,Le,m)\<in>N}\<approx> N" unfolding eqpoll_def by auto
  with N(2) have fin:"Finite({m\<in>nat. LeftRayX(nat,Le,m)\<in>N})" using lepoll_Finite eqpoll_imp_lepoll
    by auto
  from N(3) have "N\<noteq>0" by auto
  then have nE:"{m\<in>nat. LeftRayX(nat,Le,m)\<in>N}\<noteq>0" using N(1) by auto
  let ?M="Maximum(Le,{m\<in>nat. LeftRayX(nat,Le,m)\<in>N})"
  have M:"?M\<in>nat" "LeftRayX(nat,Le,?M)\<in>N" "\<forall>\<xx>\<in>{m\<in>nat. LeftRayX(nat,Le,m)\<in>N}. \<langle>\<xx>,?M\<rangle>\<in>Le" using fin linord_max_props(1,3)[OF Le_directs_nat(1) _ nE]
    unfolding FinPow_def by auto
  {
    fix V \<xx> assume V:"V\<in>N" "\<xx>\<in>V"
    then obtain m where m:"V=LeftRayX(nat,Le,m)" "LeftRayX(nat,Le,m)\<in>N" "m\<in>nat" using N(1) by auto
    with V(2) have xx:"\<langle>\<xx>,m\<rangle>\<in>Le" "\<xx>\<noteq>m" unfolding LeftRayX_def by auto
    from m(2,3) have "m\<in>{m\<in>nat. LeftRayX(nat,Le,m)\<in>N}" by auto
    then have mM:"\<langle>m,?M\<rangle>\<in>Le" using M(3) by auto
    with xx(1) have "\<langle>\<xx>,?M\<rangle>\<in>Le" using le_trans unfolding Le_def by auto
    moreover
    {
      assume "\<xx>=?M"
      with xx mM have "False" using le_anti_sym by auto
    }
    ultimately have "\<xx>\<in>LeftRayX(nat,Le,?M)" unfolding LeftRayX_def by auto
  }
  then have "\<Union>N\<subseteq>LeftRayX(nat,Le,?M)" by auto
  with M(2) have "\<Union>N=LeftRayX(nat,Le,?M)" by auto
  with N(3) have "nat\<subseteq>LeftRayX(nat,Le,?M)" by auto
  moreover from M(1) have "succ(?M)\<in>nat" using nat_succI by auto
  ultimately have "succ(?M)\<in>LeftRayX(nat,Le,?M)" by auto
  then have "\<langle>succ(?M),?M\<rangle>\<in>Le" unfolding LeftRayX_def by blast
  then show "False" by auto
qed
      
subsection\<open>More Separation properties\<close>

text\<open>In this section we study more separation properties.\<close>

subsection\<open>Definitions\<close>

text\<open>We start with a property that has already appeared in
@{file "Topology_ZF_1b.thy"}. A KC-space is a space where
compact sets are closed.\<close>

definition
  IsKC ("_ {is KC}") where
  "T{is KC} \<equiv> \<forall>A\<in>Pow(\<Union>T). A{is compact in}T \<longrightarrow> A{is closed in}T"

text\<open>Another type of space is an US-space; those where sequences
have at most one limit.\<close>

definition
  IsUS ("_{is US}") where
  "T{is US} \<equiv> \<forall>N x y. (N:nat\<rightarrow>\<Union>T) \<and> NetConvTop(\<langle>N,Le\<rangle>,x,T) \<and> NetConvTop(\<langle>N,Le\<rangle>,y,T) \<longrightarrow> y=x"

subsection\<open>First results\<close>

text\<open>The proof in @{file "Topology_ZF_1b.thy"} shows that a Hausdorff space
is KC.\<close>

corollary(in topology0) T2_imp_KC:
  assumes "T{is T\<^sub>2}"
  shows "T{is KC}"
proof-
  {
    fix A assume "A{is compact in}T"
    then have "A{is closed in}T" using in_t2_compact_is_cl assms by auto
  }
  then show ?thesis unfolding IsKC_def by auto
qed

text\<open>From the spectrum of compactness, it follows that any KC-space
is $T_1$.\<close>

lemma(in topology0) KC_imp_T1:
  assumes "T{is KC}"
  shows "T{is T\<^sub>1}"
proof-
  {
    fix x assume A:"x\<in>\<Union>T"
    have "Finite({x})" by auto
    then have "{x}{is in the spectrum of}(\<lambda>T. (\<Union>T){is compact in}T)"
      using compact_spectrum by auto moreover
    have "(T{restricted to}{x}){is a topology}" using Top_1_L4 by auto
    moreover have "\<Union>(T{restricted to}{x})={x}" using A unfolding RestrictedTo_def by auto
    ultimately have com:"{x}{is compact in}(T{restricted to}{x})" unfolding Spec_def
      by auto
    then have "{x}{is compact in}T" using compact_subspace_imp_compact A by auto
    then have "{x}{is closed in}T" using assms unfolding IsKC_def using A by auto
  }
  then show ?thesis using T1_iff_singleton_closed by auto
qed

text\<open>Even more, if a space is KC, then it is US. We already know that
for $T_2$ spaces, any net or filter has at most one limit; and that
this property is equivalent with $T_2$. The US property is much weaker
because we don't know what happends with other nets that are not directed by
the order on the natural numbers.\<close>

theorem(in topology0) KC_imp_US:
  assumes "T{is KC}"
  shows "T{is US}"
proof-
  {
    fix N x y  assume A:"N:nat\<rightarrow>\<Union>T" "\<langle>N,Le\<rangle>\<rightarrow>\<^sub>N x" "\<langle>N,Le\<rangle>\<rightarrow>\<^sub>N y" "x\<noteq>y"
    have dir:"Le directs nat" using Le_directs_nat by auto moreover
    from A(1) have dom:"domain(N)=nat" using func1_1_L1 by auto
    moreover note A(1) ultimately have Net:"\<langle>N,Le\<rangle>{is a net on}\<Union>T" unfolding IsNet_def
      by auto
    from A(3) have y:"y\<in>\<Union>T" unfolding NetConverges_def[OF Net] by auto
    from A(2) have x:"x\<in>\<Union>T" unfolding NetConverges_def[OF Net] by auto
    from A(2) have o1:"\<forall>U\<in>Pow(\<Union>T). x\<in>int(U) \<longrightarrow> (\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>U)" unfolding NetConverges_def[OF Net]
       using dom by auto
    {
      assume B:"\<exists>n\<in>nat. \<forall>m\<in>nat. \<langle>n,m\<rangle>\<in>Le \<longrightarrow> N`m=y"
      have "{y}{is closed in}T" using y T1_iff_singleton_closed KC_imp_T1 assms by auto
      then have o2:"\<Union>T-{y}\<in>T" unfolding IsClosed_def by auto
      then have "int(\<Union>T-{y})=\<Union>T-{y}" using Top_2_L3 by auto
      with A(4) x have o3:"x\<in>int(\<Union>T-{y})" by auto
      from o2 have "\<Union>T-{y}\<in>Pow(\<Union>T)" by auto
      with o1 o3 obtain r where r:"r\<in>nat" "\<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>\<Union>T-{y}" by auto
      from B obtain n where n:"n\<in>nat" "\<forall>m\<in>nat. \<langle>n,m\<rangle>\<in>Le \<longrightarrow> N`m=y" by auto
      from dir r(1) n(1) obtain z where "\<langle>r,z\<rangle>\<in>Le""\<langle>n,z\<rangle>\<in>Le""z\<in>nat" unfolding IsDirectedSet_def by auto
      with r(2) n(2) have "N`z\<in>\<Union>T-{y}" "N`z=y" by auto
      then have "False" by auto
    }
    then have reg:"\<forall>n\<in>nat. \<exists>m\<in>nat. N`m\<noteq>y \<and> \<langle>n,m\<rangle>\<in>Le" by auto
    let ?NN="{\<langle>n,N`(\<mu> i. N`i\<noteq>y \<and> \<langle>n,i\<rangle>\<in>Le)\<rangle>. n\<in>nat}"
    {
      fix x z assume A1:"\<langle>x, z\<rangle> \<in> ?NN"
      {
        fix y' assume A2:"\<langle>x,y'\<rangle>\<in>?NN"
        with A1 have "z=y'" by auto
      }
      then have "\<forall>y'. \<langle>x,y'\<rangle>\<in>?NN \<longrightarrow> z=y'" by auto
    }
    then have "\<forall>x z. \<langle>x, z\<rangle> \<in> ?NN \<longrightarrow> (\<forall>y'. \<langle>x,y'\<rangle>\<in>?NN \<longrightarrow> z=y')" by auto
    moreover
    {
      fix n assume as:"n\<in>nat"
      with reg obtain m where "N`m\<noteq>y \<and> \<langle>n,m\<rangle>\<in>Le" "m\<in>nat" by auto
      then have LI:"N`(\<mu> i. N`i\<noteq>y \<and> \<langle>n,i\<rangle>\<in>Le)\<noteq>y" "\<langle>n,\<mu> i. N`i\<noteq>y \<and> \<langle>n,i\<rangle>\<in>Le\<rangle>\<in>Le" using LeastI[of "\<lambda>m. N`m\<noteq>y \<and> \<langle>n,m\<rangle>\<in>Le" "m"]
        nat_into_Ord[of "m"] by auto
      then have "(\<mu> i. N`i\<noteq>y \<and> \<langle>n,i\<rangle>\<in>Le)\<in>nat" by auto
      then have "N`(\<mu> i. N`i\<noteq>y \<and> \<langle>n,i\<rangle>\<in>Le)\<in>\<Union>T" using apply_type[OF A(1)] by auto
      with as have "\<langle>n,N`(\<mu> i. N`i\<noteq>y \<and> \<langle>n,i\<rangle>\<in>Le)\<rangle>\<in>nat\<times>\<Union>T" by auto
    }
    then have "?NN\<in>Pow(nat\<times>\<Union>T)" by auto
    ultimately have NFun:"?NN:nat\<rightarrow>\<Union>T" unfolding Pi_def function_def domain_def by auto
    {
      fix n assume as:"n\<in>nat"
      with reg obtain m where "N`m\<noteq>y \<and> \<langle>n,m\<rangle>\<in>Le" "m\<in>nat" by auto
      then have LI:"N`(\<mu> i. N`i\<noteq>y \<and> \<langle>n,i\<rangle>\<in>Le)\<noteq>y" "\<langle>n,\<mu> i. N`i\<noteq>y \<and> \<langle>n,i\<rangle>\<in>Le\<rangle>\<in>Le" using LeastI[of "\<lambda>m. N`m\<noteq>y \<and> \<langle>n,m\<rangle>\<in>Le" "m"]
        nat_into_Ord[of "m"] by auto
      then have "?NN`n\<noteq>y" using apply_equality[OF _ NFun] by auto
    }
    then have noy:"\<forall>n\<in>nat. ?NN`n\<noteq>y" by auto
    have dom2:"domain(?NN)=nat" by auto
    then have net2:"\<langle>?NN,Le\<rangle>{is a net on}\<Union>T" unfolding IsNet_def using NFun dir by auto
    {
      fix U assume "U\<in>Pow(\<Union>T)" "x\<in>int(U)"
      then have "(\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>U)" using o1 by auto
      then obtain r where r_def:"r\<in>nat" "\<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>U" by auto
      {
        fix s assume AA:"\<langle>r,s\<rangle>\<in>Le"
        with reg obtain m where "N`m\<noteq>y" "\<langle>s,m\<rangle>\<in>Le" by auto
        then have "\<langle>s,\<mu> i. N`i\<noteq>y \<and> \<langle>s,i\<rangle>\<in>Le\<rangle>\<in>Le" using LeastI[of "\<lambda>m. N`m\<noteq>y \<and> \<langle>s,m\<rangle>\<in>Le" "m"]
          nat_into_Ord by auto
        with AA have "\<langle>r,\<mu> i. N`i\<noteq>y \<and> \<langle>s,i\<rangle>\<in>Le\<rangle>\<in>Le" using le_trans by auto
        with r_def(2) have "N`(\<mu> i. N`i\<noteq>y \<and> \<langle>s,i\<rangle>\<in>Le)\<in>U" by blast
        then have "?NN`s\<in>U" using apply_equality[OF _ NFun] AA by auto
      }
      then have "\<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> ?NN`s\<in>U" by auto
      with r_def(1) have "\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> ?NN`s\<in>U" by auto
    }
    then have conv2:"\<langle>?NN,Le\<rangle>\<rightarrow>\<^sub>N x" unfolding NetConverges_def[OF net2] using x dom2 by auto
    let ?A="{x}\<union>?NN``nat"
    {
      fix M assume Acov:"?A\<subseteq>\<Union>M" "M\<subseteq>T"
      then have "x\<in>\<Union>M" by auto
      then obtain U where U:"x\<in>U" "U\<in>M" by auto
      with Acov(2) have UT:"U\<in>T" by auto
      then have "U=int(U)" using Top_2_L3 by auto
      with U(1) have "x\<in>int(U)" by auto
      with conv2 obtain r where rr:"r\<in>nat" "\<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> ?NN`s\<in>U"
        unfolding NetConverges_def[OF net2] using dom2 UT by auto
      have NresFun:"restrict(?NN,{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}):{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}\<rightarrow>\<Union>T" using restrict_fun
        [OF NFun, of "{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}"] by auto
      then have "restrict(?NN,{n\<in>nat. \<langle>n,r\<rangle>\<in>Le})\<in>surj({n\<in>nat. \<langle>n,r\<rangle>\<in>Le},range(restrict(?NN,{n\<in>nat. \<langle>n,r\<rangle>\<in>Le})))"
        using fun_is_surj by auto moreover
      have "{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}\<subseteq>nat" by auto
      then have "{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}\<lesssim>nat" using subset_imp_lepoll by auto
      ultimately have "range(restrict(?NN,{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}))\<lesssim>{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}" using surj_fun_inv_2 by auto
      moreover
      have "{n\<in>nat. \<langle>n,0\<rangle>\<in>Le}={0}" by auto
      then have "Finite({n\<in>nat. \<langle>n,0\<rangle>\<in>Le})" by auto moreover
      {
        fix j assume as:"j\<in>nat" "Finite({n\<in>nat. \<langle>n,j\<rangle>\<in>Le})"
        {
          fix t assume "t\<in>{n\<in>nat. \<langle>n,succ(j)\<rangle>\<in>Le}"
          then have "t\<in>nat" "\<langle>t,succ(j)\<rangle>\<in>Le" by auto
          then have "t\<le>succ(j)" by auto
          then have "t\<subseteq>succ(j)" using le_imp_subset by auto
          then have "t\<subseteq>j \<union>{j}" using succ_explained by auto
          then have "j\<in>t\<or>t\<subseteq>j" by auto
          then have "j\<in>t\<or>t\<le>j" using subset_imp_le \<open>t\<in>nat\<close> \<open>j\<in>nat\<close> nat_into_Ord by auto
          then have "j \<union>{j}\<subseteq>t\<or>t\<le>j" using \<open>t\<in>nat\<close> \<open>j\<in>nat\<close> nat_into_Ord unfolding Ord_def
            Transset_def by auto
          then have "succ(j)\<subseteq>t\<or>t\<le>j" using succ_explained by auto
          with \<open>t\<subseteq>succ(j)\<close> have "t=succ(j)\<or>t\<le>j" by auto
          with \<open>t\<in>nat\<close> \<open>j\<in>nat\<close> have "t\<in>{n\<in>nat. \<langle>n,j\<rangle>\<in>Le} \<union> {succ(j)}" by auto
        }
        then have "{n\<in>nat. \<langle>n,succ(j)\<rangle>\<in>Le} \<subseteq>{n\<in>nat. \<langle>n,j\<rangle>\<in>Le} \<union> {succ(j)}" by auto
        moreover have "Finite({n\<in>nat. \<langle>n,j\<rangle>\<in>Le} \<union> {succ(j)})" using as(2) Finite_cons
          by auto
        ultimately have "Finite({n\<in>nat. \<langle>n,succ(j)\<rangle>\<in>Le})" using subset_Finite by auto
      }
      then have "\<forall>j\<in>nat. Finite({n\<in>nat. \<langle>n,j\<rangle>\<in>Le}) \<longrightarrow> Finite({n\<in>nat. \<langle>n,succ(j)\<rangle>\<in>Le})"
        by auto
      ultimately have "Finite(range(restrict(?NN, {n \<in> nat . \<langle>n, r\<rangle> \<in> Le})))"
        using lepoll_Finite[of "range(restrict(?NN, {n \<in> nat . \<langle>n, r\<rangle> \<in> Le}))"
          "{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}"] ind_on_nat[OF \<open>r\<in>nat\<close>, where P="\<lambda>t. Finite({n\<in>nat. \<langle>n,t\<rangle>\<in>Le})"] by auto
      then have "Finite((restrict(?NN, {n \<in> nat . \<langle>n, r\<rangle> \<in> Le}))``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})" using range_image_domain[OF NresFun]
        by auto
      then have "Finite(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})" using restrict_image by auto
      then have "(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}){is in the spectrum of}(\<lambda>T. (\<Union>T){is compact in}T)" using compact_spectrum by auto
      moreover have "\<Union>(T{restricted to}?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})=\<Union>T\<inter>?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}"
        unfolding RestrictedTo_def by auto moreover
      have "\<Union>T\<inter>?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}=?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}"
        using func1_1_L6(2)[OF NFun] by blast
      moreover have "(T{restricted to}?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}){is a topology}"
        using Top_1_L4 by auto
      ultimately have "(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}){is compact in}(T{restricted to}?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})"
        unfolding Spec_def by force
      then have "(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}){is compact in}T" using compact_subspace_imp_compact by auto
      moreover from Acov(1) have "(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})\<subseteq>\<Union>M" by auto
      moreover note Acov(2) ultimately
      obtain \<NN> where \<NN>:"\<NN>\<in>FinPow(M)" "(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})\<subseteq>\<Union>\<NN>"
        unfolding IsCompact_def by blast
      from \<NN>(1) have "\<NN> \<union>{U}\<in>FinPow(M)" using U(2) unfolding FinPow_def by auto moreover
      {
        fix s assume s:"s\<in>?A" "s\<notin>U"
        with U(1) have "s\<in>?NN``nat" by auto
        then have "s\<in>{?NN`n. n\<in>nat}" using func_imagedef[OF NFun] by auto
        then obtain n where n:"n\<in>nat" "s=?NN`n" by auto
        {
          assume "\<langle>r,n\<rangle>\<in>Le"
          with rr have "?NN`n\<in>U" by auto
          with n(2) s(2) have "False" by auto
        }
        then have "\<langle>r,n\<rangle>\<notin>Le" by auto
        with rr(1) n(1) have "\<not>(r\<le>n)" by auto
        then have "n\<le>r" using Ord_linear_le[where thesis="\<langle>n,r\<rangle>\<in>Le"] nat_into_Ord[OF rr(1)]
          nat_into_Ord[OF n(1)] by auto
        with rr(1) n(1) have "\<langle>n,r\<rangle>\<in>Le" by auto
        with n(2) have "s\<in>{?NN`t. t\<in>{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}}" by auto moreover
        have "{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}\<subseteq>nat" by auto
        ultimately have "s\<in>?NN``{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}" using func_imagedef[OF NFun]
          by auto
        with \<NN>(2) have "s\<in>\<Union>\<NN>" by auto
      }
      then have "?A\<subseteq>\<Union>\<NN> \<union> U" by auto
      then have "?A\<subseteq>\<Union>(\<NN> \<union> {U})" by auto ultimately
      have "\<exists>\<NN>\<in>FinPow(M). ?A\<subseteq>\<Union>\<NN>" by auto
    }
    then have "\<forall>M\<in>Pow(T). ?A\<subseteq>\<Union>M \<longrightarrow> (\<exists>\<NN>\<in>FinPow(M). ?A\<subseteq>\<Union>\<NN>)" by auto moreover
    have "?A\<subseteq>\<Union>T" using func1_1_L6(2)[OF NFun] x by blast ultimately
    have "?A{is compact in}T" unfolding IsCompact_def by auto
    with assms have "?A{is closed in}T" unfolding IsKC_def IsCompact_def by auto
    then have "\<Union>T-?A\<in>T" unfolding IsClosed_def by auto
    then have "\<Union>T-?A=int(\<Union>T-?A)" using Top_2_L3 by auto moreover
    {
      assume "y\<in>?A"
      with A(4) have "y\<in>?NN``nat" by auto
      then have "y\<in>{?NN`n. n\<in>nat}" using func_imagedef[OF NFun] by auto
      then obtain n where "n\<in>nat""?NN`n=y" by auto
      with noy have "False" by auto
    }
    with y have "y\<in>\<Union>T-?A" by force ultimately
    have "y\<in>int(\<Union>T-?A)" "\<Union>T-?A\<in>Pow(\<Union>T)" by auto moreover
    have "(\<forall>U\<in>Pow(\<Union>T).  y \<in> int(U) \<longrightarrow> (\<exists>t\<in>nat. \<forall>m\<in>nat. \<langle>t, m\<rangle> \<in> Le \<longrightarrow> N ` m \<in> U))"
      using A(3) dom unfolding NetConverges_def[OF Net] by auto
    ultimately have "\<exists>t\<in>nat. \<forall>m\<in>nat. \<langle>t, m\<rangle> \<in> Le \<longrightarrow> N ` m \<in> \<Union>T-?A" by blast
    then obtain r where r_def:"r\<in>nat" "\<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>\<Union>T-?A" by auto
    {
        fix s assume AA:"\<langle>r,s\<rangle>\<in>Le"
        with reg obtain m where "N`m\<noteq>y" "\<langle>s,m\<rangle>\<in>Le" by auto
        then have "\<langle>s,\<mu> i. N`i\<noteq>y \<and> \<langle>s,i\<rangle>\<in>Le\<rangle>\<in>Le" using LeastI[of "\<lambda>m. N`m\<noteq>y \<and> \<langle>s,m\<rangle>\<in>Le" "m"]
          nat_into_Ord by auto
        with AA have "\<langle>r,\<mu> i. N`i\<noteq>y \<and> \<langle>s,i\<rangle>\<in>Le\<rangle>\<in>Le" using le_trans by auto
        with r_def(2) have "N`(\<mu> i. N`i\<noteq>y \<and> \<langle>s,i\<rangle>\<in>Le)\<in>\<Union>T-?A" by force
        then have "?NN`s\<in>\<Union>T-?A" using apply_equality[OF _ NFun] AA by auto
        moreover have "?NN`s\<in>{?NN`t. t\<in>nat}" using AA by auto
        then have "?NN`s\<in>?NN``nat" using func_imagedef[OF NFun] by auto
        then have "?NN`s\<in>?A" by auto
        ultimately have "False" by auto
      }
      moreover have "r\<subseteq>succ(r)" using succ_explained by auto
      then have "r\<le>succ(r)" using subset_imp_le nat_into_Ord \<open>r\<in>nat\<close> nat_succI
        by auto
      then have "\<langle>r,succ(r)\<rangle>\<in>Le" using \<open>r\<in>nat\<close> nat_succI by auto
      ultimately have "False" by auto
    }
    then have "\<forall>N x y. (N:nat\<rightarrow>\<Union>T) \<and> (\<langle>N, Le\<rangle> \<rightarrow>\<^sub>N x {in} T) \<and> (\<langle>N, Le\<rangle> \<rightarrow>\<^sub>N y {in} T)
      \<longrightarrow> x=y" by auto
  then show ?thesis unfolding IsUS_def by auto
qed

text\<open>US spaces are also $T_1$.\<close>

theorem (in topology0) US_imp_T1:
  assumes "T{is US}"
  shows "T{is T\<^sub>1}"
proof-
  {
    fix x assume x:"x\<in>\<Union>T"
    then have "{x}\<subseteq>\<Union>T" by auto
    {
      fix y assume y:"y\<noteq>x" "y\<in>cl({x})"
      then have r:"\<forall>U\<in>T. y\<in>U \<longrightarrow> x\<in>U" using cl_inter_neigh[OF \<open>{x}\<subseteq>\<Union>T\<close>] by auto
      let ?N="ConstantFunction(nat,x)"
      have fun:"?N:nat\<rightarrow>\<Union>T" using x func1_3_L1 by auto
      then have dom:"domain(?N)=nat" using func1_1_L1 by auto
      with fun have Net:"\<langle>?N,Le\<rangle>{is a net on}\<Union>T" using Le_directs_nat unfolding IsNet_def
        by auto
      {
        fix U assume "U\<in>Pow(\<Union>T)" "x\<in>int(U)"
        then have "x\<in>U" using Top_2_L1 by auto
        then have "\<forall>n\<in>nat. ?N`n\<in>U" using func1_3_L2 by auto
        then have "\<forall>n\<in>nat. \<langle>0,n\<rangle>\<in>Le \<longrightarrow>?N`n\<in>U" by auto
        then have "\<exists>r\<in>nat. \<forall>n\<in>nat. \<langle>r,n\<rangle>\<in>Le \<longrightarrow>?N`n\<in>U" by auto
      }
      then have "\<langle>?N,Le\<rangle> \<rightarrow>\<^sub>N x" unfolding NetConverges_def[OF Net] using x dom by auto moreover
      {
        fix U assume "U\<in>Pow(\<Union>T)" "y\<in>int(U)"
        then have "x\<in>int(U)" using r Top_2_L2 by auto
        then have "x\<in>U" using Top_2_L1 by auto
        then have "\<forall>n\<in>nat. ?N`n\<in>U" using func1_3_L2 by auto
        then have "\<forall>n\<in>nat. \<langle>0,n\<rangle>\<in>Le \<longrightarrow>?N`n\<in>U" by auto
        then have "\<exists>r\<in>nat. \<forall>n\<in>nat. \<langle>r,n\<rangle>\<in>Le \<longrightarrow>?N`n\<in>U" by auto
      }
      then have "\<langle>?N,Le\<rangle> \<rightarrow>\<^sub>N y" unfolding NetConverges_def[OF Net] using y(2) dom
        Top_3_L11(1)[OF \<open>{x}\<subseteq>\<Union>T\<close>] by auto
      ultimately have "x=y" using assms unfolding IsUS_def using fun by auto
      with y(1) have "False" by auto
    }
    then have "cl({x})\<subseteq>{x}" by auto
    then have "cl({x})={x}" using cl_contains_set[OF \<open>{x}\<subseteq>\<Union>T\<close>] by auto
    then have "{x}{is closed in}T" using Top_3_L8 x by auto
  }
  then show ?thesis using T1_iff_singleton_closed by auto
qed

subsection\<open>Counter-examples\<close>

text\<open>We need to find counter-examples that prove that this properties
are new ones.\<close>

text\<open>We know that $T_2\Rightarrow loc.T_2\Rightarrow$ anti-hyperconnected $\Rightarrow T_1$
and $T_2\Rightarrow KC\Rightarrow US\Rightarrow T_1$. The question is: What is the relation
between $KC$ or $US$ and, $loc.T_2$ or anti-hyperconnected?\<close>

text\<open>In the file @{file "Topology_ZF_properties_2.thy"} we built a topological space
which is locally-$T_2$ but no $T_2$. It happends actually that this space is not even US
given the appropiate topology \<open>T\<close>.\<close>

lemma (in topology0) locT2_not_US_1:
  assumes "{m}\<notin>T" "{m}{is closed in}T" "\<exists>N\<in>nat\<rightarrow>\<Union>T. (\<langle>N,Le\<rangle>\<rightarrow>\<^sub>N m) \<and> m\<notin>N``nat" 
  shows "\<exists>N\<in>nat\<rightarrow>\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}). (\<langle>N,Le\<rangle>\<rightarrow>\<^sub>N \<Union>T {in} (T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}))
    \<and> (\<langle>N,Le\<rangle>\<rightarrow>\<^sub>N m {in} (T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}))"
proof-
  from assms(3) obtain N where N:"N:nat\<rightarrow>\<Union>T" "\<langle>N,Le\<rangle>\<rightarrow>\<^sub>N m" "m\<notin>N``nat" by auto
  have "\<Union>T\<subseteq>\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" using assms(2) union_doublepoint_top
    by auto
  with N(1) have fun:"N:nat\<rightarrow>\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" using func1_1_L1B by auto
  then have dom:"domain(N)=nat" using func1_1_L1 by auto
  with fun have Net:"\<langle>N,Le\<rangle>{is a net on}\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" unfolding
    IsNet_def using Le_directs_nat by auto
  from N(1) dom have Net2:"\<langle>N,Le\<rangle>{is a net on}\<Union>T" unfolding IsNet_def using Le_directs_nat by auto
  from N(2) have R:"\<forall>U\<in>Pow(\<Union>T). m\<in>int(U) \<longrightarrow>(\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>U)"
    unfolding NetConverges_def[OF Net2] using dom by auto
  {
    fix U assume U:"U\<in>Pow(\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}))"  "m\<in>Interior(U,T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})"
    let ?I="Interior(U,T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})"
    have "?I\<in>T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" using topology0.Top_2_L2 assms(2) doble_point_top unfolding topology0_def by blast
    then have "(\<Union>T)\<inter>?I\<in>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){restricted to}\<Union>T" unfolding RestrictedTo_def by blast
    then have "(\<Union>T)\<inter>?I\<in>T" using open_subspace_double_point(1) assms(2) by auto moreover
    then have "int((\<Union>T)\<inter>?I)=(\<Union>T)\<inter>?I" using Top_2_L3 by auto
    with U(2) assms(2) have "m\<in>int((\<Union>T)\<inter>?I)" unfolding IsClosed_def by auto
    moreover note R ultimately have "\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>(\<Union>T)\<inter>?I" by blast
    then have "\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>?I" by blast
    then have "\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>U" using topology0.Top_2_L1[of "T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}""U"] doble_point_top assms(2)
      unfolding topology0_def by auto
  }
  then have "\<forall>U\<in>Pow(\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})). m\<in>Interior(U,T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}) \<longrightarrow>(\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>U)" by auto
  moreover have tt:"topology0(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" using doble_point_top[OF assms(2)] unfolding topology0_def. 
  have "m\<in>\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" using assms(2) union_doublepoint_top unfolding IsClosed_def by auto ultimately
  have con1:"(\<langle>N,Le\<rangle>\<rightarrow>\<^sub>N m {in} (T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}))" unfolding topology0.NetConverges_def[OF tt Net]
    using dom by auto
  {
    fix U assume U:"U\<in>Pow(\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}))"  "\<Union>T\<in>Interior(U,T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})"
    let ?I="Interior(U,T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})"
    have "?I\<in>T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" using topology0.Top_2_L2 assms(2) doble_point_top unfolding topology0_def by blast
    with U(2) mem_not_refl have "?I\<in>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}" by auto
    then obtain V W where VW:"?I=(V-{m})\<union>{\<Union>T}\<union>W" "W\<in>T" "V\<in>T" "m\<in>V" by auto
    from VW(3,4) have "m\<in>int(V)" using Top_2_L3 by auto moreover
    have "V\<in>Pow(\<Union>T)" using VW(3) by auto moreover
    note R ultimately
    have "\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>V" by blast moreover
    from N(3) have "\<forall>s\<in>nat. N`s\<noteq>m" using func_imagedef[OF N(1)] by auto ultimately
    have "\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>V-{m}" by blast
    then have "\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>?I" using VW(1) by auto
    then have "\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>U" using topology0.Top_2_L1 assms(2) doble_point_top unfolding topology0_def by blast
  }
  then have "\<forall>U\<in>Pow(\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})). \<Union>T\<in>Interior(U,T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}) \<longrightarrow> (\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>U)" by auto
  moreover have "\<Union>T\<in>\<Union>(T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T})" using assms(2) union_doublepoint_top by auto ultimately
  have "(\<langle>N,Le\<rangle>\<rightarrow>\<^sub>N \<Union>T {in} (T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}))" unfolding topology0.NetConverges_def[OF tt Net]
    using dom by auto
  with con1 fun show ?thesis by auto
qed

corollary (in topology0) locT2_not_US_2:
  assumes "{m}\<notin>T" "{m}{is closed in}T" "\<exists>N\<in>nat\<rightarrow>\<Union>T. (\<langle>N,Le\<rangle>\<rightarrow>\<^sub>N m) \<and> m\<notin>N``nat"
  shows "\<not>((T\<union>{(U-{m})\<union>{\<Union>T}\<union>W. \<langle>U,W\<rangle>\<in>{V\<in>T. m\<in>V}\<times>T}){is US})"
proof-
  have "m\<noteq>\<Union>T" using assms(2) mem_not_refl unfolding IsClosed_def by auto 
  then show ?thesis using locT2_not_US_1 assms unfolding IsUS_def by blast
qed

text\<open>In particular, we also know that a locally-$T_2$ space doesn't need to be KC;
since KC$\Rightarrow$US. Also we know that anti-hyperconnected spaces don't need to be
KC or US, since locally-$T_2\Rightarrow$anti-hyperconnected.\<close>

text\<open>Let's find a KC space that is not $T_2$, an US space which is not KC
and a $T_1$ space which is not US.\<close>

text\<open>First, let's prove some lemmas about what relation
is there between this properties under the influence of other ones. This will
help us to find counter-examples.\<close>

text\<open>Anti-compactness ereases the differences between several properties.\<close>

lemma (in topology0) anticompact_KC_equiv_T1:
  assumes "T{is anti-compact}"
  shows "T{is KC}\<longleftrightarrow>T{is T\<^sub>1}"
proof
  assume "T{is KC}"
  then show "T{is T\<^sub>1}" using KC_imp_T1 by auto
next
  assume AS:"T{is T\<^sub>1}"
  {
    fix A assume A:"A{is compact in}T" "A\<in>Pow(\<Union>T)"
    then have "A{is compact in}(T{restricted to}A)" "A\<in>Pow(\<Union>T)" using compact_imp_compact_subspace
      Compact_is_card_nat by auto
    moreover then have "\<Union>(T{restricted to}A)=A" unfolding RestrictedTo_def by auto
    ultimately have "(\<Union>(T{restricted to}A)){is compact in}(T{restricted to}A)" "A\<in>Pow(\<Union>T)" by auto
    with assms have "Finite(A)" unfolding IsAntiComp_def antiProperty_def using compact_spectrum by auto
    then obtain n where "n\<in>nat" "A\<approx>n" unfolding Finite_def by auto
    then have "A\<prec>nat" using eq_lesspoll_trans n_lesspoll_nat by auto moreover
    have "\<Union>T-(\<Union>T-A)=A" using A(2) by auto
    ultimately have "\<Union>T-(\<Union>T-A)\<prec>nat" by auto
    then have "\<Union>T-A\<in>CoFinite \<Union>T" unfolding Cofinite_def CoCardinal_def by auto
    then have "\<Union>T-A\<in>T" using AS T1_cocardinal_coarser by auto
    with A(2) have "A{is closed in}T" unfolding IsClosed_def by auto
  }
  then show "T{is KC}" unfolding IsKC_def by auto
qed

text\<open>Then if we find an anti-compact and $T_1$ but no $T_2$ space,
there is a counter-example for $KC\Rightarrow T_2$. A counter-example for US doesn't
need to be KC mustn't be anti-compact.\<close>

text\<open>The cocountable topology on \<open>csucc(nat)\<close> is such a topology.\<close>
text\<open>The cocountable topology on $\mathbb{N}^+$ is hyperconnected.\<close>

lemma cocountable_in_csucc_nat_HConn:
  shows "(CoCountable csucc(nat)){is hyperconnected}"
proof-
  {
    fix U V assume as:"U\<in>(CoCountable csucc(nat))""V\<in>(CoCountable csucc(nat))""U\<inter>V=0"
    then have "csucc(nat)-U\<prec>csucc(nat)\<or>U=0""csucc(nat)-V\<prec>csucc(nat)\<or>V=0"
      unfolding Cocountable_def CoCardinal_def by auto
    then have "(csucc(nat)-U)\<union>(csucc(nat)-V)\<prec>csucc(nat)\<or>U=0\<or>V=0" using less_less_imp_un_less[
      OF _ _ InfCard_csucc[OF InfCard_nat]] by auto moreover
    {
      assume "(csucc(nat)-U)\<union>(csucc(nat)-V)\<prec>csucc(nat)" moreover
      have "(csucc(nat)-U)\<union>(csucc(nat)-V)=csucc(nat)-U\<inter>V" by auto
      with as(3) have "(csucc(nat)-U)\<union>(csucc(nat)-V)=csucc(nat)" by auto
      ultimately have "csucc(nat)\<prec>csucc(nat)" by auto
      then have "False" by auto
    }
    ultimately have "U=0\<or>V=0" by auto
  }
  then show "(CoCountable csucc(nat)){is hyperconnected}" unfolding IsHConnected_def by auto
qed

text\<open>The cocountable topology on $\mathbb{N}^+$ is not anti-hyperconnected.\<close>

corollary cocountable_in_csucc_nat_notAntiHConn:
  shows "\<not>((CoCountable csucc(nat)){is anti-}IsHConnected)"
proof
  assume as:"(CoCountable csucc(nat)){is anti-}IsHConnected"
  have "(CoCountable csucc(nat)){is hyperconnected}" using cocountable_in_csucc_nat_HConn by auto moreover
  have "csucc(nat)\<noteq>0" using Ord_0_lt_csucc[OF Ord_nat] by auto
  then have uni:"\<Union>(CoCountable csucc(nat))=csucc(nat)" using union_cocardinal unfolding Cocountable_def by auto
  have "\<forall>A\<in>(CoCountable csucc(nat)). A\<subseteq>\<Union>(CoCountable csucc(nat))" by fast
  with uni have "\<forall>A\<in>(CoCountable csucc(nat)). A\<subseteq>csucc(nat)" by auto
  then have "\<forall>A\<in>(CoCountable csucc(nat)). csucc(nat)\<inter>A=A" by auto
  ultimately have "((CoCountable csucc(nat)){restricted to}csucc(nat)){is hyperconnected}"
    unfolding RestrictedTo_def by auto
  with as have "(csucc(nat)){is in the spectrum of}IsHConnected" unfolding antiProperty_def
    using uni by auto
  then have "csucc(nat)\<lesssim>1" using HConn_spectrum by auto
  then have "csucc(nat)\<prec>nat" using n_lesspoll_nat lesspoll_trans1 by auto
  then show "False" using lt_csucc[OF Ord_nat] lt_Card_imp_lesspoll[OF Card_csucc[OF Ord_nat]]
    lesspoll_trans by auto
qed

text\<open>The cocountable topology on $\mathbb{N}^+$ is not $T_2$.\<close>

theorem cocountable_in_csucc_nat_noT2:
  shows "\<not>(CoCountable csucc(nat)){is T\<^sub>2}"
proof
  assume "(CoCountable csucc(nat)){is T\<^sub>2}" 
  then have antiHC:"(CoCountable csucc(nat)){is anti-}IsHConnected" 
    using topology0.T2_imp_anti_HConn[OF topology0_CoCardinal[OF InfCard_csucc[OF InfCard_nat]]]
    unfolding Cocountable_def by auto
  then show "False" using cocountable_in_csucc_nat_notAntiHConn by auto
qed
    
text\<open>The cocountable topology on $\mathbb{N}^+$ is $T_1$.\<close>

theorem cocountable_in_csucc_nat_T1:
  shows "(CoCountable csucc(nat)){is T\<^sub>1}"
  using cocardinal_is_T1[OF InfCard_csucc[OF InfCard_nat]] unfolding Cocountable_def by auto
    
text\<open>The cocountable topology on $\mathbb{N}^+$ is anti-compact.\<close>

theorem cocountable_in_csucc_nat_antiCompact:
  shows "(CoCountable csucc(nat)){is anti-compact}"
proof-
  have noE:"csucc(nat)\<noteq>0" using Ord_0_lt_csucc[OF Ord_nat] by auto 
  {
    fix A assume as:"A\<subseteq>\<Union>(CoCountable csucc(nat))" "(\<Union>((CoCountable csucc(nat)){restricted to}A)){is compact in}((CoCountable csucc(nat)){restricted to}A)"
    from as(1) have ass:"A\<subseteq>csucc(nat)" using union_cocardinal[OF noE] unfolding Cocountable_def by auto
    have "((CoCountable csucc(nat)){restricted to}A)=CoCountable (A\<inter>csucc(nat))" using subspace_cocardinal
      unfolding Cocountable_def by auto moreover
    from ass have "A\<inter>csucc(nat)=A" by auto
    ultimately have "((CoCountable csucc(nat)){restricted to}A)=CoCountable A" by auto
    with as(2) have comp:"(\<Union>(CoCountable A)){is compact in}(CoCountable A)" by auto   
    {
      assume as2:"A\<prec>csucc(nat)" moreover
      {
        fix t assume t:"t\<in>A"
        have "A-{t}\<subseteq>A" by auto
        then have "A-{t}\<lesssim>A" using subset_imp_lepoll by auto
        with as2 have "A-{t}\<prec>csucc(nat)" using lesspoll_trans1 by auto moreover note noE
        ultimately have "(A-{t}){is closed in}(CoCountable A)" using closed_sets_cocardinal[of "csucc(nat)"
          "A-{t}""A"] unfolding Cocountable_def by auto
        then have "A-(A-{t})\<in>(CoCountable A)" unfolding IsClosed_def using union_cocardinal[OF noE, of "A"]
          unfolding Cocountable_def by auto moreover
        from t have "A-(A-{t})={t}" by auto ultimately
        have "{t}\<in>(CoCountable A)" by auto
      }
      then have r:"\<forall>t\<in>A. {t}\<in>(CoCountable A)" by auto
      {
        fix U assume U:"U\<in>Pow(A)"
        {
          fix t assume "t\<in>U"
          with U r have "t\<in>{t}""{t}\<subseteq>U""{t}\<in>(CoCountable A)" by auto
          then have "\<exists>V\<in>(CoCountable A). t\<in>V \<and> V\<subseteq>U" by auto
        }
        then have "U\<in>(CoCountable A)" using topology0.open_neigh_open[OF topology0_CoCardinal[
          OF InfCard_csucc[OF InfCard_nat]]] unfolding Cocountable_def by auto
      }
      then have "Pow(A)\<subseteq>(CoCountable A)" by auto moreover
      {
        fix B assume "B\<in>(CoCountable A)"
        then have "B\<in>Pow(\<Union>(CoCountable A))" by auto
        then have "B\<in>Pow(A)" using union_cocardinal[OF noE] unfolding Cocountable_def by auto
      }
      ultimately have p:"Pow(A)=(CoCountable A)" by auto
      then have "(CoCountable A){is anti-compact}" using pow_anti_compact[of "A"] by auto moreover
      from p have "\<Union>(CoCountable A)=\<Union>Pow(A)" by auto
      then have tot:"\<Union>(CoCountable A)=A" by auto
      from comp have "(\<Union>((CoCountable A){restricted to}(\<Union>(CoCountable A)))){is compact in}((CoCountable A){restricted to}(\<Union>(CoCountable A)))" using compact_imp_compact_subspace
        Compact_is_card_nat tot unfolding RestrictedTo_def by auto
      ultimately have "A{is in the spectrum of}(\<lambda>T. (\<Union>T){is compact in}T)"
        using comp tot unfolding IsAntiComp_def antiProperty_def by auto
    }
    moreover
    {
      assume as1:"\<not>(A\<prec>csucc(nat))"
      from ass have "A\<lesssim>csucc(nat)" using subset_imp_lepoll by auto
      with as1 have "A\<approx>csucc(nat)" using lepoll_iff_leqpoll by auto
      then have "csucc(nat)\<approx>A" using eqpoll_sym by auto
      then have "nat\<prec>A" using lesspoll_eq_trans lt_csucc[OF Ord_nat]
        lt_Card_imp_lesspoll[OF Card_csucc[OF Ord_nat]] by auto
      then have "nat\<lesssim>A" using lepoll_iff_leqpoll by auto
      then obtain f where "f\<in>inj(nat,A)" unfolding lepoll_def by auto moreover
      then have fun:"f:nat\<rightarrow>A" unfolding inj_def by auto
      then have "f\<in>surj(nat,range(f))" using fun_is_surj by auto
      ultimately have "f\<in>bij(nat,range(f))" unfolding bij_def inj_def surj_def by auto
      then have "nat\<approx>range(f)" unfolding eqpoll_def by auto
      then have e:"range(f)\<approx>nat" using eqpoll_sym by auto
      then have as2:"range(f)\<prec>csucc(nat)" using lt_Card_imp_lesspoll[OF Card_csucc[OF Ord_nat]]
        lt_csucc[OF Ord_nat] eq_lesspoll_trans by auto
      then have "range(f){is closed in}(CoCountable A)" using closed_sets_cocardinal[of "csucc(nat)"
          "range(f)""A"] unfolding Cocountable_def using func1_1_L5B[OF fun] noE by auto
      then have "(A\<inter>range(f)){is compact in}(CoCountable A)" using compact_closed union_cocardinal[OF noE, of "A"]
        comp Compact_is_card_nat unfolding Cocountable_def by auto
      moreover have int:"A\<inter>range(f)=range(f)""range(f)\<inter>A=range(f)" using func1_1_L5B[OF fun] by auto
      ultimately have "range(f){is compact in}(CoCountable A)" by auto
      then have "range(f){is compact in}((CoCountable A){restricted to}range(f))" using compact_imp_compact_subspace
        Compact_is_card_nat by auto
      moreover have "((CoCountable A){restricted to}range(f))=CoCountable (range(f)\<inter>A)"
        using subspace_cocardinal unfolding Cocountable_def by auto
      with int(2) have "((CoCountable A){restricted to}range(f))=CoCountable range(f)" by auto
      ultimately have comp2:"range(f){is compact in}(CoCountable range(f))" by auto
      {
        fix t assume t:"t\<in>range(f)"
        have "range(f)-{t}\<subseteq>range(f)" by auto
        then have "range(f)-{t}\<lesssim>range(f)" using subset_imp_lepoll by auto
        with as2 have "range(f)-{t}\<prec>csucc(nat)" using lesspoll_trans1 by auto moreover note noE
        ultimately have "(range(f)-{t}){is closed in}(CoCountable range(f))" using closed_sets_cocardinal[of "csucc(nat)"
          "range(f)-{t}""range(f)"] unfolding Cocountable_def by auto
        then have "range(f)-(range(f)-{t})\<in>(CoCountable range(f))" unfolding IsClosed_def using union_cocardinal[OF noE, of "range(f)"]
          unfolding Cocountable_def by auto moreover
        from t have "range(f)-(range(f)-{t})={t}" by auto ultimately
        have "{t}\<in>(CoCountable range(f))" by auto
      }
      then have r:"\<forall>t\<in>range(f). {t}\<in>(CoCountable range(f))" by auto
      {
        fix U assume U:"U\<in>Pow(range(f))"
        {
          fix t assume "t\<in>U"
          with U r have "t\<in>{t}""{t}\<subseteq>U""{t}\<in>(CoCountable range(f))" by auto
          then have "\<exists>V\<in>(CoCountable range(f)). t\<in>V \<and> V\<subseteq>U" by auto
        }
        then have "U\<in>(CoCountable range(f))" using topology0.open_neigh_open[OF topology0_CoCardinal[
          OF InfCard_csucc[OF InfCard_nat]]] unfolding Cocountable_def by auto
      }
      then have "Pow(range(f))\<subseteq>(CoCountable range(f))" by auto moreover
      {
        fix B assume "B\<in>(CoCountable range(f))"
        then have "B\<in>Pow(\<Union>(CoCountable range(f)))" by auto
        then have "B\<in>Pow(range(f))" using union_cocardinal[OF noE] unfolding Cocountable_def by auto
      }
      ultimately have p:"Pow(range(f))=(CoCountable range(f))" by blast
      then have "(CoCountable range(f)){is anti-compact}" using pow_anti_compact[of "range(f)"] by auto moreover
      from p have "\<Union>(CoCountable range(f))=\<Union>Pow(range(f))" by auto
      then have tot:"\<Union>(CoCountable range(f))=range(f)" by auto
      from comp2 have "(\<Union>((CoCountable range(f)){restricted to}(\<Union>(CoCountable range(f))))){is compact in}((CoCountable range(f)){restricted to}(\<Union>(CoCountable range(f))))" using compact_imp_compact_subspace
        Compact_is_card_nat tot unfolding RestrictedTo_def by auto
      ultimately have "range(f){is in the spectrum of}(\<lambda>T. (\<Union>T){is compact in}T)"
        using comp tot unfolding IsAntiComp_def antiProperty_def by auto
      then have "Finite(range(f))" using compact_spectrum by auto
      then have "Finite(nat)" using e eqpoll_imp_Finite_iff by auto
      then have "False" using nat_not_Finite by auto
    }
    ultimately have "A{is in the spectrum of}(\<lambda>T. (\<Union>T){is compact in}T)" by auto
  }
  then have "\<forall>A\<in>Pow(\<Union>(CoCountable csucc(nat))). ((\<Union>((CoCountable csucc(nat)) {restricted to} A)) {is compact in} ((CoCountable csucc(nat)) {restricted to} A))
    \<longrightarrow> (A{is in the spectrum of}(\<lambda>T. (\<Union>T){is compact in}T))" by auto
  then show ?thesis unfolding IsAntiComp_def antiProperty_def by auto
qed

text\<open>In conclusion, the cocountable topology defined on \<open>csucc(nat)\<close>
is KC but not $T_2$. Also note that is KC but not anti-hyperconnected, hence KC or US
spaces need not to be sober.\<close>

text\<open>The cofinite topology on the natural numbers is $T_1$, but
not US.\<close>

theorem cofinite_not_US:
  shows "\<not>((CoFinite nat){is US})"
proof
  assume A:"(CoFinite nat){is US}"
  let ?N="id(nat)"
  have f:"?N:nat\<rightarrow>nat" using id_type by auto
  then have fun:"?N:nat\<rightarrow>\<Union>(CoCardinal(nat,nat))" using union_cocardinal unfolding Cofinite_def by auto
  then have dom:"domain(?N)=nat" using func1_1_L1 by auto
  with fun have NET:"\<langle>?N,Le\<rangle>{is a net on}\<Union>(CoCardinal(nat,nat))" unfolding IsNet_def
    using Le_directs_nat by auto
  have tot:"\<Union>(CoCardinal(nat,nat))=nat" using union_cocardinal by auto
  {
    fix U n assume U:"U\<in>Pow(\<Union>(CoFinite nat))" "n\<in>Interior(U,(CoFinite nat))"
    have "Interior(U,(CoFinite nat))\<in>(CoFinite nat)" using topology0.Top_2_L2
      topology0_CoCardinal[OF InfCard_nat] unfolding Cofinite_def by auto
    then have "nat-Interior(U,(CoFinite nat))\<prec>nat" using U(2) unfolding Cofinite_def
      CoCardinal_def by auto
    then have "Finite(nat-Interior(U,(CoFinite nat)))" using lesspoll_nat_is_Finite by auto moreover
    have "nat-U\<subseteq>nat-Interior(U,(CoFinite nat))" using topology0.Top_2_L1
      topology0_CoCardinal[OF InfCard_nat] unfolding Cofinite_def by auto
    ultimately have fin:"Finite(nat-U)" using subset_Finite by auto
    moreover have lin:"IsLinOrder(nat,Le)" using Le_directs_nat(1) by auto
    then have "IsLinOrder(nat-U,Le)" using ord_linear_subset[of "nat" "Le" "nat-U"] by auto
    ultimately have r:"nat-U=0 \<or> (\<forall>r\<in>nat-U. \<langle>r,Maximum(Le,nat-U)\<rangle>\<in>Le)" using linord_max_props(3)[of "nat-U""Le""nat-U"]
      unfolding FinPow_def by auto
    {
      assume reg:"\<forall>s\<in>nat. \<exists>r\<in>nat. \<langle>s,r\<rangle>\<in>Le \<and> ?N`r\<notin>U"
      with r have s:"(\<forall>r\<in>nat-U. \<langle>r,Maximum(Le,nat-U)\<rangle>\<in>Le)" "nat-U\<noteq>0" using apply_type[OF f] by auto
      have "Maximum(Le,nat-U)\<in>nat" using linord_max_props(2)[OF lin _ s(2)] fin
        unfolding FinPow_def by auto
      then have "succ(Maximum(Le,nat-U))\<in>nat" using nat_succI by auto
      with reg have "\<exists>r\<in>nat. \<langle>succ(Maximum(Le,nat-U)),r\<rangle>\<in>Le \<and> ?N`r\<notin>U" by auto
      then obtain r where r_def:"r\<in>nat" "\<langle>succ(Maximum(Le,nat-U)),r\<rangle>\<in>Le" "?N`r\<notin>U" by auto
      from r_def(1,3) have "?N`r\<in>nat-U" using apply_type[OF f] by auto
      with s(1) have "\<langle>?N`r,Maximum(Le,nat-U)\<rangle>\<in>Le" by auto
      then have "\<langle>r,Maximum(Le,nat-U)\<rangle>\<in>Le" using id_conv r_def(1) by auto
      then have "r<succ(Maximum(Le,nat-U))" by auto
      with r_def(2) have "r<r" using lt_trans2 by auto
      then have "False" by auto
    }
    then have "\<exists>s\<in>nat. \<forall>r\<in>nat. \<langle>s,r\<rangle>\<in>Le \<longrightarrow> ?N`r\<in>U" by auto
  }
  then have "\<forall>n\<in>nat. \<forall>U\<in>Pow(\<Union>(CoFinite nat)). n\<in>Interior(U,CoFinite nat) \<longrightarrow> (\<exists>s\<in>nat. \<forall>r\<in>nat. \<langle>s,r\<rangle>\<in>Le \<longrightarrow> ?N`r\<in>U)" by auto
  with tot have "\<forall>n\<in>\<Union>(CoCardinal(nat,nat)). \<forall>U\<in>Pow(\<Union>(CoCardinal(nat,nat))). n\<in>Interior(U,CoCardinal(nat,nat)) \<longrightarrow> (\<exists>s\<in>nat. \<forall>r\<in>nat. \<langle>s,r\<rangle>\<in>Le \<longrightarrow> ?N`r\<in>U)"
    unfolding Cofinite_def by auto
  then have "\<forall>n\<in>\<Union>(CoCardinal(nat,nat)). (\<langle>?N,Le\<rangle>\<rightarrow>\<^sub>N n {in}(CoCardinal(nat,nat)))" unfolding topology0.NetConverges_def[OF topology0_CoCardinal[OF InfCard_nat] NET]
    using dom by auto
  with tot have "\<forall>n\<in>nat. (\<langle>?N,Le\<rangle>\<rightarrow>\<^sub>N n {in}(CoFinite nat))" unfolding Cofinite_def by auto
  then have "(\<langle>?N,Le\<rangle>\<rightarrow>\<^sub>N 0 {in}(CoFinite nat)) \<and> (\<langle>?N,Le\<rangle>\<rightarrow>\<^sub>N 1 {in}(CoFinite nat)) \<and> 0\<noteq>1" by auto
  then show "False" using A unfolding IsUS_def using fun unfolding Cofinite_def by auto
qed

text\<open>To end, we need a space which is US but no KC. This example
comes from the one point compactification of a $T_2$, anti-compact
and non discrete space. This $T_2$, anti-compact and non discrete space
comes from a construction over the cardinal $\mathbb{N}^+$ or \<open>csucc(nat)\<close>.\<close>

theorem extension_pow_top:
  shows "(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){is a topology}"
proof-
  have noE:"csucc(nat)\<noteq>0" using Ord_0_lt_csucc[OF Ord_nat] by auto 
  {
    fix M assume M:"M\<subseteq>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
    let ?MP="{U\<in>M. U\<in>Pow(csucc(nat))}"
    let ?MN="{U\<in>M. U\<notin>Pow(csucc(nat))}"
    have unM:"\<Union>M=(\<Union>?MP)\<union>(\<Union>?MN)" by auto
    have "csucc(nat)\<notin>csucc(nat)" using mem_not_refl by auto
    with M have MN:"?MN={U\<in>M. U\<in>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}}" by auto
    have unMP:"\<Union>?MP\<in>Pow(csucc(nat))" by auto
    then have "?MN=0\<longrightarrow>\<Union>M\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
      using unM by auto moreover
    {
      assume "?MN\<noteq>0"
      with MN have "{U\<in>M. U\<in>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}}\<noteq>0" by auto
      then obtain U where U:"U\<in>M" "U\<in>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}" by blast
      then obtain S where S:"U={csucc(nat)}\<union>S" "S\<in>(CoCountable csucc(nat))-{0}" by auto
      with U MN have "csucc(nat)\<in>U" "U\<in>?MN" by auto
      then have a1:"csucc(nat)\<in>\<Union>?MN" by auto
      let ?SC="{S\<in>(CoCountable csucc(nat)). {csucc(nat)}\<union>S\<in>M}"
      have unSC:"\<Union>?SC\<in>(CoCountable csucc(nat))" using CoCar_is_topology[OF InfCard_csucc[OF InfCard_nat]]
        unfolding IsATopology_def unfolding Cocountable_def by blast
      {
        fix s assume "s\<in>{csucc(nat)}\<union>\<Union>?SC"
        then have "s=csucc(nat)\<or>s\<in>\<Union>?SC" by auto
        then have "s\<in>\<Union>?MN\<or>(\<exists>S\<in>?SC. s\<in>S)" using a1 by auto
        then have "s\<in>\<Union>?MN\<or>(\<exists>S\<in>(CoCountable csucc(nat)). {csucc(nat)}\<union>S\<in>M \<and> s\<in>S)" by auto
        with MN have "s\<in>\<Union>?MN\<or>(\<exists>S\<in>(CoCountable csucc(nat)). {csucc(nat)}\<union>S\<in>?MN \<and> s\<in>S)" by auto
        then have "s\<in>\<Union>?MN" by blast
      }
      then have "{csucc(nat)}\<union>\<Union>?SC\<subseteq>\<Union>?MN" by blast
      moreover
      {
        fix s assume "s\<in>\<Union>?MN"
        then obtain U where U:"s\<in>U" "U\<in>M" "U\<notin>Pow(csucc(nat))" by auto
        with M have "U\<in>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))}" by auto
        then obtain S where S:"U={csucc(nat)}\<union>S" "S\<in>(CoCountable csucc(nat))" by auto
        with U(1) have "s=csucc(nat)\<or>s\<in>S" by auto
        with S U(2) have "s=csucc(nat)\<or>s\<in>\<Union>?SC" by auto
        then have "s\<in>{csucc(nat)}\<union>\<Union>?SC" by auto
      }
      then have "\<Union>?MN\<subseteq>{csucc(nat)}\<union>\<Union>?SC" by blast
      ultimately have unMN:"\<Union>?MN={csucc(nat)}\<union>\<Union>?SC" by auto
      from unSC have b1:"csucc(nat)-\<Union>?SC\<prec>csucc(nat)\<or>\<Union>?SC=0" unfolding Cocountable_def CoCardinal_def
        by auto
      {
        assume "0\<in>?SC"
        then have "{csucc(nat)}\<in>M" by auto
        then have "{csucc(nat)}\<in>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}" using mem_not_refl
          M by auto
        then obtain S where S:"S\<in>(CoCountable csucc(nat))-{0}" "{csucc(nat)}={csucc(nat)}\<union>S" by auto
        {
          fix x assume "x\<in>S"
          then have "x\<in>{csucc(nat)}\<union>S" by auto
          with S(2) have "x\<in>{csucc(nat)}" by auto
          then have "x=csucc(nat)" by auto
        }
        then have "S\<subseteq>{csucc(nat)}" by auto
        with S(1) have "S={csucc(nat)}" by auto
        with S(1) have "csucc(nat)-{csucc(nat)}\<prec>csucc(nat)" unfolding Cocountable_def CoCardinal_def
          by auto moreover
        then have "csucc(nat)-{csucc(nat)}=csucc(nat)" using mem_not_refl[of "csucc(nat)"] by force
        ultimately have "False" by auto
      }
      then have "0\<notin>?SC" by auto moreover
      from S U(1) have "S\<in>?SC" by auto
      ultimately have "S\<subseteq>\<Union>?SC" "S\<noteq>0" by auto
      then have noe:"\<Union>?SC\<noteq>0" by auto
      with b1 have "csucc(nat)-\<Union>?SC\<prec>csucc(nat)" by auto
      moreover have "csucc(nat)-(\<Union>?SC \<union> \<Union>?MP)\<subseteq>csucc(nat)-\<Union>?SC" by auto
      then have "csucc(nat)-(\<Union>?SC \<union> \<Union>?MP)\<lesssim>csucc(nat)-\<Union>?SC" using subset_imp_lepoll by auto
      ultimately have "csucc(nat)-(\<Union>?SC \<union> \<Union>?MP)\<prec>csucc(nat)" using lesspoll_trans1 by auto moreover
      have "\<Union>?SC\<subseteq>\<Union>(CoCountable csucc(nat))" using unSC by auto
      then have "\<Union>?SC\<subseteq>csucc(nat)" using union_cocardinal[OF noE] unfolding Cocountable_def by auto
      ultimately have "(\<Union>?SC \<union> \<Union>?MP)\<in>(CoCountable csucc(nat))"
        using unMP unfolding Cocountable_def CoCardinal_def by auto
      then have "{csucc(nat)}\<union>(\<Union>?SC \<union> \<Union>?MP)\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
        using noe by auto moreover
      from unM unMN have "\<Union>M=({csucc(nat)}\<union>\<Union>?SC) \<union> \<Union>?MP" by auto
      then have "\<Union>M={csucc(nat)}\<union>(\<Union>?SC \<union> \<Union>?MP)" by auto
      ultimately have "\<Union>M\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" by auto
    }
    ultimately have "\<Union>M\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" by auto
  }
  then have "\<forall>M\<in>Pow(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}). \<Union>M\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" by auto
  moreover
  {
    fix U V assume UV:"U\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" "V\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
    {
      assume "csucc(nat)\<notin>U\<or>csucc(nat)\<notin>V"
      with UV have "U\<in>Pow(csucc(nat))\<or>V\<in>Pow(csucc(nat))" by auto
      then have "U\<inter>V\<in>Pow(csucc(nat))" by auto
      then have "U\<inter>V\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" by auto
    }
    moreover
    {
      assume "csucc(nat)\<in>U\<and>csucc(nat)\<in>V"
      then obtain SU SV where S:"U={csucc(nat)}\<union>SU" "V={csucc(nat)}\<union>SV" "SU\<in>(CoCountable csucc(nat))-{0}"
        "SV\<in>(CoCountable csucc(nat))-{0}" using UV mem_not_refl by auto
      from S(1,2) have "U\<inter>V={csucc(nat)}\<union>(SU\<inter>SV)" by auto moreover
      from S(3,4) have "SU\<inter>SV\<in>(CoCountable csucc(nat))" using CoCar_is_topology[OF InfCard_csucc[OF InfCard_nat]] unfolding IsATopology_def
        unfolding Cocountable_def by blast moreover
      from S(3,4) have "SU\<inter>SV\<noteq>0" using cocountable_in_csucc_nat_HConn unfolding IsHConnected_def
        by auto ultimately
      have "U\<inter>V\<in>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}" by auto
      then have "U\<inter>V\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" by auto
    }
    ultimately have "U\<inter>V\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" by auto
  }
  then have "\<forall>U\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}). \<forall>V\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}). U\<inter>V\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" by auto
  ultimately show ?thesis unfolding IsATopology_def by auto
qed

text\<open>This topology is defined over $\mathbb{N}^+\cup\{\mathbb{N}^+\}$ or \<open>csucc(nat)\<union>{csucc(nat)}\<close>.\<close>

lemma extension_pow_union:
  shows "\<Union>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})=csucc(nat)\<union>{csucc(nat)}"
proof
  have noE:"csucc(nat)\<noteq>0" using Ord_0_lt_csucc[OF Ord_nat] by auto 
  have "\<Union>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})=\<Union>(Pow(csucc(nat))) \<union> (\<Union>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
    by blast
  also have "\<dots>=csucc(nat) \<union> (\<Union>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" by auto
  ultimately have A:"\<Union>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})=csucc(nat) \<union> (\<Union>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" by auto
  have "\<Union>(CoCountable csucc(nat))\<in>(CoCountable csucc(nat))" using CoCar_is_topology[OF InfCard_csucc[OF InfCard_nat]]
    unfolding IsATopology_def Cocountable_def by auto
  then have "csucc(nat)\<in>(CoCountable csucc(nat))" using union_cocardinal[OF noE] unfolding Cocountable_def
    by auto
  with noE have "csucc(nat)\<in>(CoCountable csucc(nat))-{0}" by auto
  then have "{csucc(nat)}\<union>csucc(nat)\<in>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}" by auto
  then have "{csucc(nat)}\<union>csucc(nat)\<subseteq>\<Union>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}" by blast
  with A show "csucc(nat)\<union>{csucc(nat)}\<subseteq>\<Union>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
    by auto
  {
    fix x assume x:"x\<in>(\<Union>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" "x\<noteq>csucc(nat)"
    then obtain U where U:"U\<in>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}" "x\<in>U" by blast
    then obtain S where S:"U={csucc(nat)}\<union>S" "S\<in>(CoCountable csucc(nat))-{0}" by auto
    with U(2) x(2) have "x\<in>S" by auto
    with S(2) have "x\<in>\<Union>(CoCountable csucc(nat))" by auto
    then have "x\<in>csucc(nat)" using union_cocardinal[OF noE] unfolding Cocountable_def by auto
  }
  then have "(\<Union>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})\<subseteq>csucc(nat) \<union>{csucc(nat)}" by blast
  with A show "\<Union>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})\<subseteq>csucc(nat)\<union>{csucc(nat)}"
    by blast
qed

text\<open>This topology has a discrete open subspace.\<close>

lemma extension_pow_subspace:
  shows "(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){restricted to}csucc(nat)=Pow(csucc(nat))"
  and "csucc(nat)\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
proof
  show "csucc(nat)\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" by auto
  {
    fix x assume "x\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){restricted to}csucc(nat)"
    then obtain R where "x=csucc(nat)\<inter>R" "R\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" unfolding RestrictedTo_def
      by auto
    then have "x\<in>Pow(csucc(nat))" by auto
  }
  then show "(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){restricted to}csucc(nat)\<subseteq>Pow(csucc(nat))" by auto
  {
    fix x assume x:"x\<in>Pow(csucc(nat))"
    then have "x=csucc(nat)\<inter>x" by auto
    with x have "x\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){restricted to}csucc(nat)"
      unfolding RestrictedTo_def by auto
  }
  then show "Pow(csucc(nat))\<subseteq>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){restricted to}csucc(nat)" by auto
qed

text\<open>This topology is Hausdorff.\<close>

theorem extension_pow_T2:
  shows "(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){is T\<^sub>2}"
proof-
  have noE:"csucc(nat)\<noteq>0" using Ord_0_lt_csucc[OF Ord_nat] by auto 
  {
    fix A B assume "A\<in>\<Union>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
      "B\<in>\<Union>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" "A\<noteq>B"
    then have AB:"A\<in>csucc(nat)\<union>{csucc(nat)}" "B\<in>csucc(nat)\<union>{csucc(nat)}" "A\<noteq>B" using extension_pow_union by auto
    {
      assume "A\<noteq>csucc(nat)" "B\<noteq>csucc(nat)"
      then have "A\<in>csucc(nat)" "B\<in>csucc(nat)" using AB by auto
      then have sub:"{A}\<in>Pow(csucc(nat))" "{B}\<in>Pow(csucc(nat))" by auto
      then have "{A}\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){restricted to}csucc(nat)" 
        "{B}\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){restricted to}csucc(nat)" using extension_pow_subspace(1)
        by auto 
      then obtain RA RB where "{A}=csucc(nat)\<inter>RA" "{B}=csucc(nat)\<inter>RB" "RA\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
        "RB\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" unfolding RestrictedTo_def by auto
      then have "{A}\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" "{B}\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
        using extension_pow_subspace(2) extension_pow_top unfolding IsATopology_def by auto
      moreover
      from AB(3) have "{A}\<inter>{B}=0" by auto ultimately
      have "\<exists>U\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}). \<exists>V\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}). A\<in>U\<and>B\<in>V\<and>U\<inter>V=0" by auto
    }
    moreover
    {
      assume "A=csucc(nat)\<or>B=csucc(nat)"
      with AB(3) have disj:"(A=csucc(nat)\<and>B\<noteq>csucc(nat))\<or>(B=csucc(nat)\<and>A\<noteq>csucc(nat))" by auto
      {
        assume ass:"A=csucc(nat)\<and>B\<noteq>csucc(nat)" 
        then have p:"B\<in>csucc(nat)" using AB(2) by auto
        have "{B}\<approx>1" using singleton_eqpoll_1 by auto
        then have "{B}\<prec>nat" using eq_lesspoll_trans n_lesspoll_nat by auto
        then have "{B}\<lesssim>nat" using lesspoll_imp_lepoll by auto
        then have "{B}\<prec>csucc(nat)" using Card_less_csucc_eq_le[OF Card_nat] by auto
        with p have "{B}{is closed in}(CoCountable csucc(nat))" unfolding Cocountable_def
          using closed_sets_cocardinal[OF noE] by auto
        then have "csucc(nat)-{B}\<in>(CoCountable csucc(nat))" unfolding IsClosed_def
          Cocountable_def using union_cocardinal[OF noE] by auto moreover
        {
          assume "csucc(nat)-{B}=0"
          with p have "csucc(nat)={B}" by auto
          then have "csucc(nat)\<approx>1" using singleton_eqpoll_1 by auto
          then have "csucc(nat)\<lesssim>nat" using eq_lesspoll_trans n_lesspoll_nat lesspoll_imp_lepoll by auto
          then have "csucc(nat)\<prec>csucc(nat)" using Card_less_csucc_eq_le[OF Card_nat] by auto
          then have "False" by auto
        }
        ultimately
        have "{csucc(nat)}\<union>(csucc(nat)-{B})\<in>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}" by auto
        then have U1:"{csucc(nat)}\<union>(csucc(nat)-{B})\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" by auto
        have "{B}\<in>Pow(csucc(nat))" using p by auto
        then have "{B}\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){restricted to}csucc(nat)"
          using extension_pow_subspace(1) by auto
        then obtain R where "R\<in>Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}" "{B}=csucc(nat)\<inter>R"
          unfolding RestrictedTo_def by auto
        then have U2:"{B}\<in>Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}" using extension_pow_subspace(2)
          extension_pow_top unfolding IsATopology_def by auto
        have "({csucc(nat)}\<union>(csucc(nat)-{B}))\<inter>{B}=0" using p mem_not_refl[of "csucc(nat)"] by auto
        with U1 U2 have "\<exists>U\<in>Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}. \<exists>V\<in>Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}.
          A\<in>U\<and>B\<in>V\<and>U\<inter>V=0" using ass(1) by auto
      }
      moreover
      {
        assume "\<not>(A=csucc(nat)\<and>B\<noteq>csucc(nat))" 
        then have ass:"B = csucc(nat) \<and> A \<noteq> csucc(nat)" using disj by auto
        then have p:"A\<in>csucc(nat)" using AB(1) by auto
        have "{A}\<approx>1" using singleton_eqpoll_1 by auto
        then have "{A}\<prec>nat" using eq_lesspoll_trans n_lesspoll_nat by auto
        then have "{A}\<lesssim>nat" using lesspoll_imp_lepoll by auto
        then have "{A}\<prec>csucc(nat)" using Card_less_csucc_eq_le[OF Card_nat] by auto
        with p have "{A}{is closed in}(CoCountable csucc(nat))" unfolding Cocountable_def
          using closed_sets_cocardinal[OF noE] by auto
        then have "csucc(nat)-{A}\<in>(CoCountable csucc(nat))" unfolding IsClosed_def
          Cocountable_def using union_cocardinal[OF noE] by auto moreover
        {
          assume "csucc(nat)-{A}=0"
          with p have "csucc(nat)={A}" by auto
          then have "csucc(nat)\<approx>1" using singleton_eqpoll_1 by auto
          then have "csucc(nat)\<lesssim>nat" using eq_lesspoll_trans n_lesspoll_nat lesspoll_imp_lepoll by auto
          then have "csucc(nat)\<prec>csucc(nat)" using Card_less_csucc_eq_le[OF Card_nat] by auto
          then have "False" by auto
        }
        ultimately
        have "{csucc(nat)}\<union>(csucc(nat)-{A})\<in>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}" by auto
        then have U1:"{csucc(nat)}\<union>(csucc(nat)-{A})\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" by auto
        have "{A}\<in>Pow(csucc(nat))" using p by auto
        then have "{A}\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){restricted to}csucc(nat)"
          using extension_pow_subspace(1) by auto
        then obtain R where "R\<in>Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}" "{A}=csucc(nat)\<inter>R"
          unfolding RestrictedTo_def by auto
        then have U2:"{A}\<in>Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}" using extension_pow_subspace(2)
          extension_pow_top unfolding IsATopology_def by auto
        have int:"{A}\<inter>({csucc(nat)}\<union>(csucc(nat)-{A}))=0" using p mem_not_refl[of "csucc(nat)"] by auto
        have "A\<in>{A}" "csucc(nat)\<in>({csucc(nat)}\<union>(csucc(nat)-{A}))" by auto
        with int U1 have "\<exists>V\<in>Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}.
          A\<in>{A}\<and>csucc(nat)\<in>V\<and>{A}\<inter>V=0" by auto
        with U2 have "\<exists>U\<in>Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}. \<exists>V\<in>Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}.
          A\<in>U\<and>csucc(nat)\<in>V\<and>U\<inter>V=0" using exI[where P="\<lambda>U. U\<in>Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}\<and>(\<exists>V\<in>Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}.
          A\<in>U\<and>csucc(nat)\<in>V\<and>U\<inter>V=0)" and x="{A}"] unfolding Bex_def by auto
        then have "\<exists>U\<in>Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}. \<exists>V\<in>Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}.
          A\<in>U\<and>B\<in>V\<and>U\<inter>V=0" using ass by auto
      } 
      ultimately have "\<exists>U\<in>Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}. \<exists>V\<in>Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}.
          A\<in>U\<and>B\<in>V\<and>U\<inter>V=0" by auto
    }
    ultimately have "\<exists>U\<in>Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}. \<exists>V\<in>Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}.
          A\<in>U\<and>B\<in>V\<and>U\<inter>V=0" by auto
  }
  then show ?thesis unfolding isT2_def by auto
qed

text\<open>The topology we built is not discrete; i.e., not every set is open.\<close>

theorem extension_pow_notDiscrete:
  shows "{csucc(nat)}\<notin>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
proof
  assume "{csucc(nat)}\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
  then have "{csucc(nat)}\<in>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}" using mem_not_refl by auto
  then obtain S where S:"S\<in>(CoCountable csucc(nat))-{0}" "{csucc(nat)}={csucc(nat)}\<union>S" by auto
  {
    fix x assume "x\<in>S"
    then have "x\<in>{csucc(nat)}\<union>S" by auto
    with S(2) have "x\<in>{csucc(nat)}" by auto
    then have "x=csucc(nat)" by auto
  }
  then have "S\<subseteq>{csucc(nat)}" by auto
  with S(1) have "S={csucc(nat)}" by auto
  with S(1) have "csucc(nat)-{csucc(nat)}\<prec>csucc(nat)" unfolding Cocountable_def CoCardinal_def
    by auto moreover
  then have "csucc(nat)-{csucc(nat)}=csucc(nat)" using mem_not_refl[of "csucc(nat)"] by force
  ultimately show "False" by auto
qed

text\<open>The topology we built is anti-compact.\<close>

theorem extension_pow_antiCompact:
  shows "(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){is anti-compact}"
proof-
  have noE:"csucc(nat)\<noteq>0" using Ord_0_lt_csucc[OF Ord_nat] by auto 
  {
    fix K assume K:"K\<subseteq>\<Union>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" 
      "(\<Union>((Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){restricted to}K)){is compact in}((Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){restricted to}K)"
    from K(1) have sub:"K\<subseteq>csucc(nat) \<union>{csucc(nat)}" using extension_pow_union by auto
    have "(\<Union>((Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){restricted to}K))=(csucc(nat) \<union>{csucc(nat)})\<inter>K"
      using extension_pow_union unfolding RestrictedTo_def by auto moreover
    from sub have "(csucc(nat) \<union>{csucc(nat)})\<inter>K=K" by auto
    ultimately have "(\<Union>((Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){restricted to}K))=K" by auto
    with K(2) have "K{is compact in}((Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){restricted to}K)" by auto
    then have comp:"K{is compact in}(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" using 
      compact_subspace_imp_compact by auto
    {
      assume ss:"K\<subseteq>csucc(nat)"
      then have "K{is compact in}((Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){restricted to}csucc(nat))"
        using compact_imp_compact_subspace comp Compact_is_card_nat by auto
      then have "K{is compact in}Pow(csucc(nat))" using extension_pow_subspace(1) by auto
      then have "K{is compact in}(Pow(csucc(nat)){restricted to}K)" using compact_imp_compact_subspace
        Compact_is_card_nat by auto moreover
      have "\<Union>(Pow(csucc(nat)){restricted to}K)=K" using ss unfolding RestrictedTo_def by auto
      ultimately have "(\<Union>(Pow(csucc(nat)){restricted to}K)){is compact in}(Pow(csucc(nat)){restricted to}K)" by auto
      then have "K{is in the spectrum of}(\<lambda>T. (\<Union>T){is compact in}T)" using pow_anti_compact 
        unfolding IsAntiComp_def antiProperty_def using ss by auto
    }
    moreover
    {
      assume "\<not>(K\<subseteq>csucc(nat))"
      with sub have "csucc(nat)\<in>K" by auto
      with sub have ss:"K-{csucc(nat)}\<subseteq>csucc(nat)" by auto
      {
        assume prec:"K-{csucc(nat)}\<prec>csucc(nat)"
        then have "(K-{csucc(nat)}){is closed in}(CoCountable csucc(nat))"
          using closed_sets_cocardinal[OF noE] ss unfolding Cocountable_def by auto
        then have "csucc(nat)-(K-{csucc(nat)})\<in>(CoCountable csucc(nat))" unfolding IsClosed_def
          Cocountable_def using union_cocardinal[OF noE] by auto moreover
        {
          assume "csucc(nat)-(K-{csucc(nat)})=0"
          with ss have "csucc(nat)=(K-{csucc(nat)})" by auto
          with prec have "False" by auto
        }
        ultimately have "{csucc(nat)} \<union>(csucc(nat)-(K-{csucc(nat)}))\<in>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}"
          by auto
        moreover have "{csucc(nat)} \<union>(csucc(nat)-(K-{csucc(nat)}))=({csucc(nat)} \<union> csucc(nat))-(K-{csucc(nat)})" by blast
        ultimately have "({csucc(nat)} \<union> csucc(nat))-(K-{csucc(nat)})\<in>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}" by auto
        then have "({csucc(nat)} \<union> csucc(nat))-(K-{csucc(nat)})\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
          by auto moreover
        have "csucc(nat) \<union> {csucc(nat)}={csucc(nat)} \<union> csucc(nat)" by auto
        ultimately have "(csucc(nat) \<union> {csucc(nat)})-(K-{csucc(nat)})\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
          by auto
        then have "(\<Union>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}))-(K-{csucc(nat)})\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
          using extension_pow_union by auto
        then have "(K-{csucc(nat)}){is closed in}(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
          unfolding IsClosed_def using ss by auto
        with comp have "(K\<inter>(K-{csucc(nat)})){is compact in}(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" using compact_closed
          Compact_is_card_nat by auto
        moreover have "K\<inter>(K-{csucc(nat)})=(K-{csucc(nat)})" by auto
        ultimately have "(K-{csucc(nat)}){is compact in}(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" by auto
        with ss have "(K-{csucc(nat)}){is compact in}((Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){restricted to}csucc(nat))"
          using compact_imp_compact_subspace comp Compact_is_card_nat by auto
        then have "(K-{csucc(nat)}){is compact in}(Pow(csucc(nat)))" using extension_pow_subspace(1) by auto
        then have "(K-{csucc(nat)}){is compact in}(Pow(csucc(nat)){restricted to}(K-{csucc(nat)}))" using compact_imp_compact_subspace
          Compact_is_card_nat by auto moreover
        have "\<Union>(Pow(csucc(nat)){restricted to}(K-{csucc(nat)}))=(K-{csucc(nat)})" using ss unfolding RestrictedTo_def by auto
        ultimately have "(\<Union>(Pow(csucc(nat)){restricted to}(K-{csucc(nat)}))){is compact in}(Pow(csucc(nat)){restricted to}(K-{csucc(nat)}))" by auto
        then have "(K-{csucc(nat)}){is in the spectrum of}(\<lambda>T. (\<Union>T){is compact in}T)" using pow_anti_compact 
          unfolding IsAntiComp_def antiProperty_def using ss by auto
        then have "Finite(K-{csucc(nat)})" using compact_spectrum by auto moreover
        have "Finite({csucc(nat)})" by auto ultimately
        have "Finite(K)" using Diff_Finite[of "{csucc(nat)}" "K"] by auto
        then have "K{is in the spectrum of}(\<lambda>T. (\<Union>T){is compact in}T)" using compact_spectrum by auto
      }
      moreover
      {
        assume "\<not>(K-{csucc(nat)}\<prec>csucc(nat))"
        with ss have "K-{csucc(nat)}\<approx>csucc(nat)" using lepoll_iff_leqpoll subset_imp_lepoll[of "K-{csucc(nat)}"
          "csucc(nat)"] by auto
        then have "csucc(nat)\<approx>K-{csucc(nat)}" using eqpoll_sym by auto
        then have "nat\<prec>K-{csucc(nat)}" using lesspoll_eq_trans lt_csucc[OF Ord_nat]
          lt_Card_imp_lesspoll[OF Card_csucc[OF Ord_nat]] by auto
        then have "nat\<lesssim>K-{csucc(nat)}" using lepoll_iff_leqpoll by auto
        then obtain f where "f\<in>inj(nat,K-{csucc(nat)})" unfolding lepoll_def by auto moreover
        then have fun:"f:nat\<rightarrow>K-{csucc(nat)}" unfolding inj_def by auto
        then have "f\<in>surj(nat,range(f))" using fun_is_surj by auto
        ultimately have "f\<in>bij(nat,range(f))" unfolding bij_def inj_def surj_def by auto
        then have "nat\<approx>range(f)" unfolding eqpoll_def by auto
        then have e:"range(f)\<approx>nat" using eqpoll_sym by auto
        then have as2:"range(f)\<prec>csucc(nat)" using lt_Card_imp_lesspoll[OF Card_csucc[OF Ord_nat]]
          lt_csucc[OF Ord_nat] eq_lesspoll_trans by auto
        then have "range(f){is closed in}(CoCountable csucc(nat))" using closed_sets_cocardinal[of "csucc(nat)"
            "range(f)""csucc(nat)"] unfolding Cocountable_def using func1_1_L5B[OF fun] ss noE by auto
        then have "csucc(nat)-(range(f))\<in>(CoCountable csucc(nat))" unfolding IsClosed_def
          Cocountable_def using union_cocardinal[OF noE] by auto moreover
        {
          assume "csucc(nat)-(range(f))=0"
          with ss func1_1_L5B[OF fun] have "csucc(nat)=(range(f))" by blast
          with as2 have "False" by auto
        }
        ultimately have "{csucc(nat)} \<union>(csucc(nat)-(range(f)))\<in>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}"
          by auto
        moreover have "{csucc(nat)} \<union>(csucc(nat)-(range(f)))=({csucc(nat)} \<union> csucc(nat))-(range(f))" using func1_1_L5B[OF fun] by blast
        ultimately have "({csucc(nat)} \<union> csucc(nat))-(range(f))\<in>{{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}" by auto
        then have "({csucc(nat)} \<union> csucc(nat))-(range(f))\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
          by auto moreover
        have "csucc(nat) \<union> {csucc(nat)}={csucc(nat)} \<union> csucc(nat)" by auto
        ultimately have "(csucc(nat) \<union> {csucc(nat)})-(range(f))\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
          by auto
        then have "(\<Union>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}))-(range(f))\<in>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
          using extension_pow_union by auto moreover
        have "range(f)\<subseteq>\<Union>(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" using ss func1_1_L5B[OF fun] by auto
        ultimately have "(range(f)){is closed in}(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
          unfolding IsClosed_def by blast
        with comp have "(K\<inter>(range(f))){is compact in}(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" using compact_closed
          Compact_is_card_nat by auto
        moreover have "K\<inter>(range(f))=(range(f))" using func1_1_L5B[OF fun] by auto
        ultimately have "(range(f)){is compact in}(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})" by auto
        with ss func1_1_L5B[OF fun] have "(range(f)){is compact in}((Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}){restricted to}csucc(nat))"
          using compact_imp_compact_subspace[of "range(f)" "nat" "Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}}" "csucc(nat)"] comp Compact_is_card_nat by auto
        then have "(range(f)){is compact in}(Pow(csucc(nat)))" using extension_pow_subspace(1) by auto
        then have "(range(f)){is compact in}(Pow(csucc(nat)){restricted to}(range(f)))" using compact_imp_compact_subspace
          Compact_is_card_nat by auto moreover
        have "\<Union>(Pow(csucc(nat)){restricted to}(range(f)))=(range(f))" using ss func1_1_L5B[OF fun] unfolding RestrictedTo_def by auto
        ultimately have "(\<Union>(Pow(csucc(nat)){restricted to}(range(f)))){is compact in}(Pow(csucc(nat)){restricted to}(range(f)))" by auto
        then have "(range(f)){is in the spectrum of}(\<lambda>T. (\<Union>T){is compact in}T)" using pow_anti_compact[of "csucc(nat)"]
          unfolding IsAntiComp_def antiProperty_def using ss func1_1_L5B[OF fun] by auto
        then have "Finite(range(f))" using compact_spectrum by auto moreover
        then have "Finite(nat)" using e eqpoll_imp_Finite_iff by auto ultimately
        have "False" using nat_not_Finite by auto
      }
      ultimately have "K {is in the spectrum of}( \<lambda>T. (\<Union>T) {is compact in} T)" by auto
    }
    ultimately have "K {is in the spectrum of}( \<lambda>T. (\<Union>T) {is compact in} T)" by auto
  }
  then show ?thesis unfolding IsAntiComp_def antiProperty_def by auto
qed

text\<open>If a topological space is KC, then its one-point compactification
is US.\<close>

theorem (in topology0) KC_imp_OP_comp_is_US:
  assumes "T{is KC}"
  shows "({one-point compactification of}T){is US}"
proof-
  {
    fix N x y assume A:"N:nat\<rightarrow>\<Union>({one-point compactification of}T)" "\<langle>N,Le\<rangle>\<rightarrow>\<^sub>N x{in}({one-point compactification of}T)" "\<langle>N,Le\<rangle>\<rightarrow>\<^sub>N y{in}({one-point compactification of}T)" "x\<noteq>y"
    have dir:"Le directs nat" using Le_directs_nat(2).
    from A(1) have dom:"domain(N)=nat" using func1_1_L1 by auto
    with dir A(1) have NET:"\<langle>N,Le\<rangle>{is a net on}\<Union>({one-point compactification of}T)" unfolding IsNet_def by auto
    have xy:"x\<in>\<Union>({one-point compactification of}T)" "y\<in>\<Union>({one-point compactification of}T)"
      using A(2,3) topology0.NetConverges_def[OF _ NET] unfolding topology0_def using op_comp_is_top dom by auto 
    then have pp:"x\<in>\<Union>T \<union>{\<Union>T}" "y\<in>\<Union>T \<union>{\<Union>T}" using op_compact_total by auto
    from A(2) have comp:"\<forall>U\<in>Pow(\<Union>{one-point compactification of}T).
        x \<in> Interior(U, {one-point compactification of}T) \<longrightarrow>
        (\<exists>t\<in>nat. \<forall>m\<in>nat. \<langle>t, m\<rangle> \<in> Le \<longrightarrow> N ` m \<in> U)" using topology0.NetConverges_def[OF _ NET, of "x"]
        unfolding topology0_def using op_comp_is_top dom op_compact_total by auto
    from A(3) have op2:"\<forall>U\<in>Pow(\<Union>{one-point compactification of}T).
        y \<in> Interior(U, {one-point compactification of}T) \<longrightarrow>
        (\<exists>t\<in>nat. \<forall>m\<in>nat. \<langle>t, m\<rangle> \<in> Le \<longrightarrow> N ` m \<in> U)" using topology0.NetConverges_def[OF _ NET, of "y"]
        unfolding topology0_def using op_comp_is_top dom op_compact_total by auto
    {
      assume p:"x\<in>\<Union>T" "y\<in>\<Union>T"
      {
        assume B:"\<exists>n\<in>nat. \<forall>m\<in>nat. \<langle>n,m\<rangle>\<in>Le \<longrightarrow> N`m=\<Union>T"
        have "\<Union>T\<in>({one-point compactification of}T)" using open_subspace by auto
        then have "\<Union>T=Interior(\<Union>T,{one-point compactification of}T)" using topology0.Top_2_L3
          unfolding topology0_def using op_comp_is_top by auto
        then have "x\<in>Interior(\<Union>T,{one-point compactification of}T)" using p(1) by auto moreover
        have "\<Union>T\<in>Pow(\<Union>({one-point compactification of}T))" using open_subspace(1) by auto
        ultimately have "\<exists>t\<in>domain(fst(\<langle>N, Le\<rangle>)). \<forall>m\<in>domain(fst(\<langle>N, Le\<rangle>)). \<langle>t, m\<rangle> \<in> snd(\<langle>N, Le\<rangle>) \<longrightarrow> fst(\<langle>N, Le\<rangle>) ` m \<in> \<Union>T" using A(2)
          using topology0.NetConverges_def[OF _ NET] op_comp_is_top unfolding topology0_def by blast
        then have "\<exists>t\<in>nat. \<forall>m\<in>nat. \<langle>t, m\<rangle> \<in> Le \<longrightarrow> N ` m \<in> \<Union>T" using dom by auto
        then obtain t where t:"t\<in>nat" "\<forall>m\<in>nat. \<langle>t, m\<rangle> \<in> Le \<longrightarrow> N ` m \<in> \<Union>T" by auto
        from B obtain n where n:"n\<in>nat" "\<forall>m\<in>nat. \<langle>n,m\<rangle>\<in>Le \<longrightarrow> N`m=\<Union>T" by auto
        from t(1) n(1) dir obtain z where z:"z\<in>nat" "\<langle>n,z\<rangle>\<in>Le" "\<langle>t,z\<rangle>\<in>Le" unfolding IsDirectedSet_def
          by auto
        from t(2) z(1,3) have "N`z\<in>\<Union>T" by auto moreover
        from n(2) z(1,2) have "N`z=\<Union>T" by auto ultimately
        have "False" using mem_not_refl by auto
      }
      then have reg:"\<forall>n\<in>nat. \<exists>m\<in>nat. N`m\<noteq>\<Union>T \<and> \<langle>n,m\<rangle>\<in>Le" by auto
      let ?NN="{\<langle>n,N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<rangle>. n\<in>nat}"
      {
        fix x z assume A1:"\<langle>x, z\<rangle> \<in> ?NN"
        {
          fix y' assume A2:"\<langle>x,y'\<rangle>\<in>?NN"
          with A1 have "z=y'" by auto
        }
        then have "\<forall>y'. \<langle>x,y'\<rangle>\<in>?NN \<longrightarrow> z=y'" by auto
      }
      then have "\<forall>x z. \<langle>x, z\<rangle> \<in> ?NN \<longrightarrow> (\<forall>y'. \<langle>x,y'\<rangle>\<in>?NN \<longrightarrow> z=y')" by auto
      moreover
      {
      fix n assume as:"n\<in>nat"
        with reg obtain m where "N`m\<noteq>\<Union>T \<and> \<langle>n,m\<rangle>\<in>Le" "m\<in>nat" by auto
        then have LI:"N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<noteq>\<Union>T" "\<langle>n,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le\<rangle>\<in>Le" using LeastI[of "\<lambda>m. N`m\<noteq>\<Union>T \<and> \<langle>n,m\<rangle>\<in>Le" "m"]
          nat_into_Ord[of "m"] by auto
        then have "(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<in>nat" by auto
        then have "N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<in>\<Union>({one-point compactification of}T)" using apply_type[OF A(1)] op_compact_total by auto
        with as have "\<langle>n,N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<rangle>\<in>nat\<times>\<Union>({one-point compactification of}T)" by auto
      }
      then have "?NN\<in>Pow(nat\<times>\<Union>({one-point compactification of}T))" by auto
      ultimately have NFun:"?NN:nat\<rightarrow>\<Union>({one-point compactification of}T)" unfolding Pi_def function_def domain_def by auto
      {
        fix n assume as:"n\<in>nat"
        with reg obtain m where "N`m\<noteq>\<Union>T \<and> \<langle>n,m\<rangle>\<in>Le" "m\<in>nat" by auto
        then have LI:"N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<noteq>\<Union>T" "\<langle>n,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le\<rangle>\<in>Le" using LeastI[of "\<lambda>m. N`m\<noteq>\<Union>T \<and> \<langle>n,m\<rangle>\<in>Le" "m"]
          nat_into_Ord[of "m"] by auto
        then have "?NN`n\<noteq>\<Union>T" using apply_equality[OF _ NFun] by auto
      }
      then have noy:"\<forall>n\<in>nat. ?NN`n\<noteq>\<Union>T" by auto
      then have "\<forall>n\<in>nat. ?NN`n\<in>\<Union>T" using apply_type[OF NFun] op_compact_total by auto
      then have R:"?NN:nat\<rightarrow>\<Union>T" using func1_1_L1A[OF NFun] by auto
      have dom2:"domain(?NN)=nat" by auto
      then have net2:"\<langle>?NN,Le\<rangle>{is a net on}\<Union>T" unfolding IsNet_def using R dir by auto
      {
        fix U assume U:"U\<subseteq>\<Union>T" "x\<in>int(U)"
        have intT:"int(U)\<in>T" using Top_2_L2 by auto
        then have "int(U)\<in>({one-point compactification of}T)" unfolding OPCompactification_def
          by auto
        then have "Interior(int(U),{one-point compactification of}T)=int(U)" using topology0.Top_2_L3
          unfolding topology0_def using op_comp_is_top by auto
        with U(2) have "x\<in>Interior(int(U),{one-point compactification of}T)" by auto
        with intT have "(\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>int(U))" using comp op_compact_total by auto
        then obtain r where r_def:"r\<in>nat" "\<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>U" using Top_2_L1 by auto
        {
          fix s assume AA:"\<langle>r,s\<rangle>\<in>Le"
          with reg obtain m where "N`m\<noteq>\<Union>T" "\<langle>s,m\<rangle>\<in>Le" by auto
          then have "\<langle>s,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le\<rangle>\<in>Le" using LeastI[of "\<lambda>m. N`m\<noteq>\<Union>T \<and> \<langle>s,m\<rangle>\<in>Le" "m"]
            nat_into_Ord by auto
          with AA have "\<langle>r,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le\<rangle>\<in>Le" using le_trans by auto
          with r_def(2) have "N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le)\<in>U" by blast
          then have "?NN`s\<in>U" using apply_equality[OF _ NFun] AA by auto
        }
        then have "\<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> ?NN`s\<in>U" by auto
        with r_def(1) have "\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> ?NN`s\<in>U" by auto
      }
      then have "\<forall>U\<in>Pow(\<Union>T). x \<in> int(U)
        \<longrightarrow> (\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r, s\<rangle> \<in> Le \<longrightarrow> ?NN ` s \<in> U)" by auto
      then have conx:"\<langle>?NN,Le\<rangle>\<rightarrow>\<^sub>N x{in}T" using NetConverges_def[OF net2] p(1) op_comp_is_top 
        unfolding topology0_def using xy(1) dom2 by auto
      {
        fix U assume U:"U\<subseteq>\<Union>T" "y\<in>int(U)"
        have intT:"int(U)\<in>T" using Top_2_L2 by auto
        then have "int(U)\<in>({one-point compactification of}T)" unfolding OPCompactification_def
          by auto
        then have "Interior(int(U),{one-point compactification of}T)=int(U)" using topology0.Top_2_L3
          unfolding topology0_def using op_comp_is_top by auto
        with U(2) have "y\<in>Interior(int(U),{one-point compactification of}T)" by auto
        with intT have "(\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>int(U))" using op2 op_compact_total by auto
        then obtain r where r_def:"r\<in>nat" "\<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>U" using Top_2_L1 by auto
        {
          fix s assume AA:"\<langle>r,s\<rangle>\<in>Le"
          with reg obtain m where "N`m\<noteq>\<Union>T" "\<langle>s,m\<rangle>\<in>Le" by auto
          then have "\<langle>s,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le\<rangle>\<in>Le" using LeastI[of "\<lambda>m. N`m\<noteq>\<Union>T \<and> \<langle>s,m\<rangle>\<in>Le" "m"]
            nat_into_Ord by auto
          with AA have "\<langle>r,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le\<rangle>\<in>Le" using le_trans by auto
          with r_def(2) have "N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le)\<in>U" by blast
          then have "?NN`s\<in>U" using apply_equality[OF _ NFun] AA by auto
        }
        then have "\<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> ?NN`s\<in>U" by auto
        with r_def(1) have "\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> ?NN`s\<in>U" by auto
      }
      then have "\<forall>U\<in>Pow(\<Union>T). y \<in> int(U)
        \<longrightarrow> (\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r, s\<rangle> \<in> Le \<longrightarrow> ?NN ` s \<in> U)" by auto
      then have cony:"\<langle>?NN,Le\<rangle>\<rightarrow>\<^sub>N y{in}T" using NetConverges_def[OF net2] p(2) op_comp_is_top 
        unfolding topology0_def using xy(2) dom2 by auto
      with conx assms have "x=y" using KC_imp_US unfolding IsUS_def using R by auto
      with A(4) have "False" by auto
    }
    moreover
    {
      assume AAA:"x\<notin>\<Union>T\<or>y\<notin>\<Union>T"
      with pp have "x=\<Union>T\<or>y=\<Union>T" by auto
      {
        assume x:"x=\<Union>T"
        with A(4) have y:"y\<in>\<Union>T" using pp(2) by auto
        {
          assume B:"\<exists>n\<in>nat. \<forall>m\<in>nat. \<langle>n,m\<rangle>\<in>Le \<longrightarrow> N`m=\<Union>T"
          have "\<Union>T\<in>({one-point compactification of}T)" using open_subspace by auto
          then have "\<Union>T=Interior(\<Union>T,{one-point compactification of}T)" using topology0.Top_2_L3
            unfolding topology0_def using op_comp_is_top by auto
          then have "y\<in>Interior(\<Union>T,{one-point compactification of}T)" using y by auto moreover
          have "\<Union>T\<in>Pow(\<Union>({one-point compactification of}T))" using open_subspace(1) by auto
          ultimately have "\<exists>t\<in>domain(fst(\<langle>N, Le\<rangle>)). \<forall>m\<in>domain(fst(\<langle>N, Le\<rangle>)). \<langle>t, m\<rangle> \<in> snd(\<langle>N, Le\<rangle>) \<longrightarrow> fst(\<langle>N, Le\<rangle>) ` m \<in> \<Union>T" using A(3)
            using topology0.NetConverges_def[OF _ NET] op_comp_is_top unfolding topology0_def by blast
          then have "\<exists>t\<in>nat. \<forall>m\<in>nat. \<langle>t, m\<rangle> \<in> Le \<longrightarrow> N ` m \<in> \<Union>T" using dom by auto
          then obtain t where t:"t\<in>nat" "\<forall>m\<in>nat. \<langle>t, m\<rangle> \<in> Le \<longrightarrow> N ` m \<in> \<Union>T" by auto
          from B obtain n where n:"n\<in>nat" "\<forall>m\<in>nat. \<langle>n,m\<rangle>\<in>Le \<longrightarrow> N`m=\<Union>T" by auto
          from t(1) n(1) dir obtain z where z:"z\<in>nat" "\<langle>n,z\<rangle>\<in>Le" "\<langle>t,z\<rangle>\<in>Le" unfolding IsDirectedSet_def
            by auto
          from t(2) z(1,3) have "N`z\<in>\<Union>T" by auto moreover
          from n(2) z(1,2) have "N`z=\<Union>T" by auto ultimately
          have "False" using mem_not_refl by auto
        }
        then have reg:"\<forall>n\<in>nat. \<exists>m\<in>nat. N`m\<noteq>\<Union>T \<and> \<langle>n,m\<rangle>\<in>Le" by auto
        let ?NN="{\<langle>n,N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<rangle>. n\<in>nat}"
        {
          fix x z assume A1:"\<langle>x, z\<rangle> \<in> ?NN"
          {
            fix y' assume A2:"\<langle>x,y'\<rangle>\<in>?NN"
            with A1 have "z=y'" by auto
          }
          then have "\<forall>y'. \<langle>x,y'\<rangle>\<in>?NN \<longrightarrow> z=y'" by auto
        }
        then have "\<forall>x z. \<langle>x, z\<rangle> \<in> ?NN \<longrightarrow> (\<forall>y'. \<langle>x,y'\<rangle>\<in>?NN \<longrightarrow> z=y')" by auto
        moreover
        {
          fix n assume as:"n\<in>nat"
          with reg obtain m where "N`m\<noteq>\<Union>T \<and> \<langle>n,m\<rangle>\<in>Le" "m\<in>nat" by auto
          then have LI:"N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<noteq>\<Union>T" "\<langle>n,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le\<rangle>\<in>Le" using LeastI[of "\<lambda>m. N`m\<noteq>\<Union>T \<and> \<langle>n,m\<rangle>\<in>Le" "m"]
            nat_into_Ord[of "m"] by auto
          then have "(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<in>nat" by auto
          then have "N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<in>\<Union>({one-point compactification of}T)" using apply_type[OF A(1)] op_compact_total by auto
          with as have "\<langle>n,N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<rangle>\<in>nat\<times>\<Union>({one-point compactification of}T)" by auto
        }
        then have "?NN\<in>Pow(nat\<times>\<Union>({one-point compactification of}T))" by auto
        ultimately have NFun:"?NN:nat\<rightarrow>\<Union>({one-point compactification of}T)" unfolding Pi_def function_def domain_def by auto
        {
          fix n assume as:"n\<in>nat"
          with reg obtain m where "N`m\<noteq>\<Union>T \<and> \<langle>n,m\<rangle>\<in>Le" "m\<in>nat" by auto
          then have LI:"N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<noteq>\<Union>T" "\<langle>n,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le\<rangle>\<in>Le" using LeastI[of "\<lambda>m. N`m\<noteq>\<Union>T \<and> \<langle>n,m\<rangle>\<in>Le" "m"]
            nat_into_Ord[of "m"] by auto
          then have "?NN`n\<noteq>\<Union>T" using apply_equality[OF _ NFun] by auto
        }
        then have noy:"\<forall>n\<in>nat. ?NN`n\<noteq>\<Union>T" by auto
        then have "\<forall>n\<in>nat. ?NN`n\<in>\<Union>T" using apply_type[OF NFun] op_compact_total by auto
        then have R:"?NN:nat\<rightarrow>\<Union>T" using func1_1_L1A[OF NFun] by auto
        have dom2:"domain(?NN)=nat" by auto
        then have net2:"\<langle>?NN,Le\<rangle>{is a net on}\<Union>T" unfolding IsNet_def using R dir by auto
        {
          fix U assume U:"U\<subseteq>\<Union>T" "y\<in>int(U)"
          have intT:"int(U)\<in>T" using Top_2_L2 by auto
          then have "int(U)\<in>({one-point compactification of}T)" unfolding OPCompactification_def
            by auto
          then have "Interior(int(U),{one-point compactification of}T)=int(U)" using topology0.Top_2_L3
            unfolding topology0_def using op_comp_is_top by auto
          with U(2) have "y\<in>Interior(int(U),{one-point compactification of}T)" by auto
          with intT have "(\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>int(U))" using op2 op_compact_total by auto
          then obtain r where r_def:"r\<in>nat" "\<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>U" using Top_2_L1 by auto
          {
            fix s assume AA:"\<langle>r,s\<rangle>\<in>Le"
            with reg obtain m where "N`m\<noteq>\<Union>T" "\<langle>s,m\<rangle>\<in>Le" by auto
            then have "\<langle>s,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le\<rangle>\<in>Le" using LeastI[of "\<lambda>m. N`m\<noteq>\<Union>T \<and> \<langle>s,m\<rangle>\<in>Le" "m"]
              nat_into_Ord by auto
            with AA have "\<langle>r,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le\<rangle>\<in>Le" using le_trans by auto
            with r_def(2) have "N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le)\<in>U" by blast
            then have "?NN`s\<in>U" using apply_equality[OF _ NFun] AA by auto
          }
          then have "\<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> ?NN`s\<in>U" by auto
          with r_def(1) have "\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> ?NN`s\<in>U" by auto
        }
        then have "\<forall>U\<in>Pow(\<Union>T). y \<in> int(U)
          \<longrightarrow> (\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r, s\<rangle> \<in> Le \<longrightarrow> ?NN ` s \<in> U)" by auto
        then have cony:"\<langle>?NN,Le\<rangle>\<rightarrow>\<^sub>N y{in}T" using NetConverges_def[OF net2] y op_comp_is_top 
          unfolding topology0_def using xy(2) dom2 by auto
        let ?A="{y}\<union>?NN``nat"
        {
          fix M assume Acov:"?A\<subseteq>\<Union>M" "M\<subseteq>T"
          then have "y\<in>\<Union>M" by auto
          then obtain V where V:"y\<in>V" "V\<in>M" by auto
          with Acov(2) have VT:"V\<in>T" by auto
          then have "V=int(V)" using Top_2_L3 by auto
          with V(1) have "y\<in>int(V)" by auto
          with cony obtain r where rr:"r\<in>nat" "\<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> ?NN`s\<in>V"
            unfolding NetConverges_def[OF net2, of "y"] using dom2 VT y by auto
          have NresFun:"restrict(?NN,{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}):{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}\<rightarrow>\<Union>T" using restrict_fun
            [OF R, of "{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}"] by auto
          then have "restrict(?NN,{n\<in>nat. \<langle>n,r\<rangle>\<in>Le})\<in>surj({n\<in>nat. \<langle>n,r\<rangle>\<in>Le},range(restrict(?NN,{n\<in>nat. \<langle>n,r\<rangle>\<in>Le})))"
            using fun_is_surj by auto moreover
          have "{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}\<subseteq>nat" by auto
          then have "{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}\<lesssim>nat" using subset_imp_lepoll by auto
          ultimately have "range(restrict(?NN,{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}))\<lesssim>{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}" using surj_fun_inv_2 by auto
          moreover
          have "{n\<in>nat. \<langle>n,0\<rangle>\<in>Le}={0}" by auto
          then have "Finite({n\<in>nat. \<langle>n,0\<rangle>\<in>Le})" by auto moreover
          {
            fix j assume as:"j\<in>nat" "Finite({n\<in>nat. \<langle>n,j\<rangle>\<in>Le})"
            {
              fix t assume "t\<in>{n\<in>nat. \<langle>n,succ(j)\<rangle>\<in>Le}"
              then have "t\<in>nat" "\<langle>t,succ(j)\<rangle>\<in>Le" by auto
              then have "t\<le>succ(j)" by auto
              then have "t\<subseteq>succ(j)" using le_imp_subset by auto
              then have "t\<subseteq>j \<union>{j}" using succ_explained by auto
              then have "j\<in>t\<or>t\<subseteq>j" by auto
              then have "j\<in>t\<or>t\<le>j" using subset_imp_le \<open>t\<in>nat\<close> \<open>j\<in>nat\<close> nat_into_Ord by auto
              then have "j \<union>{j}\<subseteq>t\<or>t\<le>j" using \<open>t\<in>nat\<close> \<open>j\<in>nat\<close> nat_into_Ord unfolding Ord_def
                Transset_def by auto
              then have "succ(j)\<subseteq>t\<or>t\<le>j" using succ_explained by auto
              with \<open>t\<subseteq>succ(j)\<close> have "t=succ(j)\<or>t\<le>j" by auto
              with \<open>t\<in>nat\<close> \<open>j\<in>nat\<close> have "t\<in>{n\<in>nat. \<langle>n,j\<rangle>\<in>Le} \<union> {succ(j)}" by auto
            }
            then have "{n\<in>nat. \<langle>n,succ(j)\<rangle>\<in>Le} \<subseteq>{n\<in>nat. \<langle>n,j\<rangle>\<in>Le} \<union> {succ(j)}" by auto
            moreover have "Finite({n\<in>nat. \<langle>n,j\<rangle>\<in>Le} \<union> {succ(j)})" using as(2) Finite_cons
              by auto
            ultimately have "Finite({n\<in>nat. \<langle>n,succ(j)\<rangle>\<in>Le})" using subset_Finite by auto
          }
          then have "\<forall>j\<in>nat. Finite({n\<in>nat. \<langle>n,j\<rangle>\<in>Le}) \<longrightarrow> Finite({n\<in>nat. \<langle>n,succ(j)\<rangle>\<in>Le})"
            by auto
          ultimately have "Finite(range(restrict(?NN, {n \<in> nat . \<langle>n, r\<rangle> \<in> Le})))"
            using lepoll_Finite[of "range(restrict(?NN, {n \<in> nat . \<langle>n, r\<rangle> \<in> Le}))"
              "{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}"] ind_on_nat[OF \<open>r\<in>nat\<close>, where P="\<lambda>t. Finite({n\<in>nat. \<langle>n,t\<rangle>\<in>Le})"] by auto
          then have "Finite((restrict(?NN, {n \<in> nat . \<langle>n, r\<rangle> \<in> Le}))``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})" using range_image_domain[OF NresFun]
            by auto
          then have "Finite(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})" using restrict_image by auto
          then have "(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}){is in the spectrum of}(\<lambda>T. (\<Union>T){is compact in}T)" using compact_spectrum by auto
          moreover have "\<Union>(T{restricted to}?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})=\<Union>T\<inter>?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}"
            unfolding RestrictedTo_def by auto moreover
          have "\<Union>T\<inter>?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}=?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}"
            using func1_1_L6(2)[OF R] by blast
          moreover have "(T{restricted to}?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}){is a topology}"
            using Top_1_L4 unfolding topology0_def by auto
          ultimately have "(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}){is compact in}(T{restricted to}?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})"
            unfolding Spec_def by force
          then have "(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}){is compact in}(T)" using compact_subspace_imp_compact by auto
          moreover from Acov(1) have "(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})\<subseteq>\<Union>M" by auto
          moreover note Acov(2) ultimately
          obtain \<NN> where \<NN>:"\<NN>\<in>FinPow(M)" "(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})\<subseteq>\<Union>\<NN>"
            unfolding IsCompact_def by blast
          from \<NN>(1) have "\<NN> \<union>{V}\<in>FinPow(M)" using V(2) unfolding FinPow_def by auto moreover
          {
            fix s assume s:"s\<in>?A" "s\<notin>V"
            with V(1) have "s\<in>?NN``nat" by auto
            then have "s\<in>{?NN`n. n\<in>nat}" using func_imagedef[OF NFun] by auto
            then obtain n where n:"n\<in>nat" "s=?NN`n" by auto
            {
              assume "\<langle>r,n\<rangle>\<in>Le"
              with rr have "?NN`n\<in>V" by auto
              with n(2) s(2) have "False" by auto
            }
            then have "\<langle>r,n\<rangle>\<notin>Le" by auto
            with rr(1) n(1) have "\<not>(r\<le>n)" by auto
            then have "n\<le>r" using Ord_linear_le[where thesis="\<langle>n,r\<rangle>\<in>Le"] nat_into_Ord[OF rr(1)]
              nat_into_Ord[OF n(1)] by auto
            with rr(1) n(1) have "\<langle>n,r\<rangle>\<in>Le" by auto
            with n(2) have "s\<in>{?NN`t. t\<in>{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}}" by auto moreover
            have "{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}\<subseteq>nat" by auto
            ultimately have "s\<in>?NN``{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}" using func_imagedef[OF NFun]
              by auto
            with \<NN>(2) have "s\<in>\<Union>\<NN>" by auto
          }
          then have "?A\<subseteq>\<Union>\<NN> \<union> V" by auto
          then have "?A\<subseteq>\<Union>(\<NN> \<union> {V})" by auto ultimately
          have "\<exists>\<NN>\<in>FinPow(M). ?A\<subseteq>\<Union>\<NN>" by auto
        }
        then have "\<forall>M\<in>Pow(T). ?A\<subseteq>\<Union>M \<longrightarrow> (\<exists>\<NN>\<in>FinPow(M). ?A\<subseteq>\<Union>\<NN>)" by auto moreover
        have ss:"?A\<subseteq>\<Union>(T)" using func1_1_L6(2)[OF R] y by blast ultimately
        have "?A{is compact in}(T)" unfolding IsCompact_def by auto moreover
        with assms have "?A{is closed in}(T)" unfolding IsKC_def IsCompact_def by auto ultimately
        have "?A\<in>{B\<in>Pow(\<Union>T). B{is compact in}(T)\<and>B{is closed in}(T)}" using ss by auto
        then have "{\<Union>T}\<union>(\<Union>T-?A)\<in>({one-point compactification of}T)" unfolding OPCompactification_def
          by auto
        then have "{\<Union>T}\<union>(\<Union>T-?A)=Interior({\<Union>T}\<union>(\<Union>T-?A),{one-point compactification of}T)" using topology0.Top_2_L3 op_comp_is_top
          unfolding topology0_def by auto moreover
        {
          assume "x\<in>?A"
          with A(4) have "x\<in>?NN``nat" by auto
          then have "x\<in>{?NN`n. n\<in>nat}" using func_imagedef[OF NFun] by auto
          then obtain n where "n\<in>nat""?NN`n=x" by auto
          with noy x have "False" by auto
        }
        with y have "x\<in>{\<Union>T}\<union>(\<Union>T-?A)" using x by force ultimately
        have "x\<in>Interior({\<Union>T}\<union>(\<Union>T-?A),{one-point compactification of}T)" "{\<Union>T}\<union>(\<Union>T-?A)\<in>Pow(\<Union>({one-point compactification of}T))"
          using op_compact_total by auto moreover
        have "(\<forall>U\<in>Pow(\<Union>({one-point compactification of}T)).  x \<in> Interior(U,{one-point compactification of}T) \<longrightarrow> (\<exists>t\<in>nat. \<forall>m\<in>nat. \<langle>t, m\<rangle> \<in> Le \<longrightarrow> N ` m \<in> U))"
          using A(2) dom topology0.NetConverges_def[OF _ NET] op_comp_is_top unfolding topology0_def by auto
        ultimately have "\<exists>t\<in>nat. \<forall>m\<in>nat. \<langle>t, m\<rangle> \<in> Le \<longrightarrow> N ` m \<in> {\<Union>T}\<union>(\<Union>T-?A)" by blast
        then obtain r where r_def:"r\<in>nat" "\<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>{\<Union>T}\<union>(\<Union>T-?A)" by auto
        {
          fix s assume AA:"\<langle>r,s\<rangle>\<in>Le"
          with reg obtain m where "N`m\<noteq>\<Union>T" "\<langle>s,m\<rangle>\<in>Le" by auto
          then have "\<langle>s,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le\<rangle>\<in>Le" using LeastI[of "\<lambda>m. N`m\<noteq>\<Union>T \<and> \<langle>s,m\<rangle>\<in>Le" "m"]
            nat_into_Ord by auto
          with AA have "\<langle>r,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le\<rangle>\<in>Le" using le_trans by auto
          with r_def(2) have "N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le)\<in>{\<Union>T}\<union>(\<Union>T-?A)" by auto
          then have "?NN`s\<in>{\<Union>T}\<union>(\<Union>T-?A)" using apply_equality[OF _ NFun] AA by auto
          with noy have "?NN`s\<in>(\<Union>T-?A)" using AA by auto
          moreover have "?NN`s\<in>{?NN`t. t\<in>nat}" using AA by auto
          then have "?NN`s\<in>?NN``nat" using func_imagedef[OF NFun] by auto
          then have "?NN`s\<in>?A" by auto
          ultimately have "False" by auto
        }
        moreover have "r\<subseteq>succ(r)" using succ_explained by auto
        then have "r\<le>succ(r)" using subset_imp_le nat_into_Ord \<open>r\<in>nat\<close> nat_succI
          by auto
        then have "\<langle>r,succ(r)\<rangle>\<in>Le" using \<open>r\<in>nat\<close> nat_succI by auto
        ultimately have "False" by auto
      }
      then have "x\<noteq>\<Union>T" by auto
      with xy(1) AAA have "y\<notin>\<Union>T" "x\<in>\<Union>T" using op_compact_total by auto
      with xy(2) have y:"y=\<Union>T" and x:"x\<in>\<Union>T" using op_compact_total by auto
      {
        assume B:"\<exists>n\<in>nat. \<forall>m\<in>nat. \<langle>n,m\<rangle>\<in>Le \<longrightarrow> N`m=\<Union>T"
        have "\<Union>T\<in>({one-point compactification of}T)" using open_subspace by auto
        then have "\<Union>T=Interior(\<Union>T,{one-point compactification of}T)" using topology0.Top_2_L3
          unfolding topology0_def using op_comp_is_top by auto
        then have "x\<in>Interior(\<Union>T,{one-point compactification of}T)" using x by auto moreover
        have "\<Union>T\<in>Pow(\<Union>({one-point compactification of}T))" using open_subspace(1) by auto
        ultimately have "\<exists>t\<in>domain(fst(\<langle>N, Le\<rangle>)). \<forall>m\<in>domain(fst(\<langle>N, Le\<rangle>)). \<langle>t, m\<rangle> \<in> snd(\<langle>N, Le\<rangle>) \<longrightarrow> fst(\<langle>N, Le\<rangle>) ` m \<in> \<Union>T" using A(2)
          using topology0.NetConverges_def[OF _ NET] op_comp_is_top unfolding topology0_def by blast
        then have "\<exists>t\<in>nat. \<forall>m\<in>nat. \<langle>t, m\<rangle> \<in> Le \<longrightarrow> N ` m \<in> \<Union>T" using dom by auto
        then obtain t where t:"t\<in>nat" "\<forall>m\<in>nat. \<langle>t, m\<rangle> \<in> Le \<longrightarrow> N ` m \<in> \<Union>T" by auto
        from B obtain n where n:"n\<in>nat" "\<forall>m\<in>nat. \<langle>n,m\<rangle>\<in>Le \<longrightarrow> N`m=\<Union>T" by auto
        from t(1) n(1) dir obtain z where z:"z\<in>nat" "\<langle>n,z\<rangle>\<in>Le" "\<langle>t,z\<rangle>\<in>Le" unfolding IsDirectedSet_def
          by auto
        from t(2) z(1,3) have "N`z\<in>\<Union>T" by auto moreover
        from n(2) z(1,2) have "N`z=\<Union>T" by auto ultimately
        have "False" using mem_not_refl by auto
      }
      then have reg:"\<forall>n\<in>nat. \<exists>m\<in>nat. N`m\<noteq>\<Union>T \<and> \<langle>n,m\<rangle>\<in>Le" by auto
      let ?NN="{\<langle>n,N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<rangle>. n\<in>nat}"
      {
        fix x z assume A1:"\<langle>x, z\<rangle> \<in> ?NN"
        {
          fix y' assume A2:"\<langle>x,y'\<rangle>\<in>?NN"
          with A1 have "z=y'" by auto
        }
        then have "\<forall>y'. \<langle>x,y'\<rangle>\<in>?NN \<longrightarrow> z=y'" by auto
      }
      then have "\<forall>x z. \<langle>x, z\<rangle> \<in> ?NN \<longrightarrow> (\<forall>y'. \<langle>x,y'\<rangle>\<in>?NN \<longrightarrow> z=y')" by auto
      moreover
      {
        fix n assume as:"n\<in>nat"
        with reg obtain m where "N`m\<noteq>\<Union>T \<and> \<langle>n,m\<rangle>\<in>Le" "m\<in>nat" by auto
        then have LI:"N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<noteq>\<Union>T" "\<langle>n,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le\<rangle>\<in>Le" using LeastI[of "\<lambda>m. N`m\<noteq>\<Union>T \<and> \<langle>n,m\<rangle>\<in>Le" "m"]
          nat_into_Ord[of "m"] by auto
        then have "(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<in>nat" by auto
        then have "N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<in>\<Union>({one-point compactification of}T)" using apply_type[OF A(1)] op_compact_total by auto
        with as have "\<langle>n,N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<rangle>\<in>nat\<times>\<Union>({one-point compactification of}T)" by auto
      }
      then have "?NN\<in>Pow(nat\<times>\<Union>({one-point compactification of}T))" by auto
      ultimately have NFun:"?NN:nat\<rightarrow>\<Union>({one-point compactification of}T)" unfolding Pi_def function_def domain_def by auto
      {
        fix n assume as:"n\<in>nat"
        with reg obtain m where "N`m\<noteq>\<Union>T \<and> \<langle>n,m\<rangle>\<in>Le" "m\<in>nat" by auto
        then have LI:"N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le)\<noteq>\<Union>T" "\<langle>n,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>n,i\<rangle>\<in>Le\<rangle>\<in>Le" using LeastI[of "\<lambda>m. N`m\<noteq>\<Union>T \<and> \<langle>n,m\<rangle>\<in>Le" "m"]
          nat_into_Ord[of "m"] by auto
        then have "?NN`n\<noteq>\<Union>T" using apply_equality[OF _ NFun] by auto
      }
      then have noy:"\<forall>n\<in>nat. ?NN`n\<noteq>\<Union>T" by auto
      then have "\<forall>n\<in>nat. ?NN`n\<in>\<Union>T" using apply_type[OF NFun] op_compact_total by auto
      then have R:"?NN:nat\<rightarrow>\<Union>T" using func1_1_L1A[OF NFun] by auto
      have dom2:"domain(?NN)=nat" by auto
      then have net2:"\<langle>?NN,Le\<rangle>{is a net on}\<Union>T" unfolding IsNet_def using R dir by auto
      {
        fix U assume U:"U\<subseteq>\<Union>T" "x\<in>int(U)"
        have intT:"int(U)\<in>T" using Top_2_L2 by auto
        then have "int(U)\<in>({one-point compactification of}T)" unfolding OPCompactification_def
          by auto
        then have "Interior(int(U),{one-point compactification of}T)=int(U)" using topology0.Top_2_L3
          unfolding topology0_def using op_comp_is_top by auto
        with U(2) have "x\<in>Interior(int(U),{one-point compactification of}T)" by auto
        with intT have "(\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>int(U))" using comp op_compact_total by auto
        then obtain r where r_def:"r\<in>nat" "\<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>U" using Top_2_L1 by auto
        {
          fix s assume AA:"\<langle>r,s\<rangle>\<in>Le"
          with reg obtain m where "N`m\<noteq>\<Union>T" "\<langle>s,m\<rangle>\<in>Le" by auto
          then have "\<langle>s,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le\<rangle>\<in>Le" using LeastI[of "\<lambda>m. N`m\<noteq>\<Union>T \<and> \<langle>s,m\<rangle>\<in>Le" "m"]
            nat_into_Ord by auto
          with AA have "\<langle>r,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le\<rangle>\<in>Le" using le_trans by auto
          with r_def(2) have "N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le)\<in>U" by blast
          then have "?NN`s\<in>U" using apply_equality[OF _ NFun] AA by auto
        }
        then have "\<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> ?NN`s\<in>U" by auto
        with r_def(1) have "\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> ?NN`s\<in>U" by auto
      }
      then have "\<forall>U\<in>Pow(\<Union>T). x \<in> int(U)
        \<longrightarrow> (\<exists>r\<in>nat. \<forall>s\<in>nat. \<langle>r, s\<rangle> \<in> Le \<longrightarrow> ?NN ` s \<in> U)" by auto
      then have cony:"\<langle>?NN,Le\<rangle>\<rightarrow>\<^sub>N x{in}T" using NetConverges_def[OF net2] x op_comp_is_top 
        unfolding topology0_def using xy(2) dom2 by auto
      let ?A="{x}\<union>?NN``nat"
      {
        fix M assume Acov:"?A\<subseteq>\<Union>M" "M\<subseteq>T"
        then have "x\<in>\<Union>M" by auto
        then obtain V where V:"x\<in>V" "V\<in>M" by auto
        with Acov(2) have VT:"V\<in>T" by auto
        then have "V=int(V)" using Top_2_L3 by auto
        with V(1) have "x\<in>int(V)" by auto
        with cony VT obtain r where rr:"r\<in>nat" "\<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> ?NN`s\<in>V"
          unfolding NetConverges_def[OF net2, of "x"] using dom2 y by auto
        have NresFun:"restrict(?NN,{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}):{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}\<rightarrow>\<Union>T" using restrict_fun
          [OF R, of "{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}"] by auto
        then have "restrict(?NN,{n\<in>nat. \<langle>n,r\<rangle>\<in>Le})\<in>surj({n\<in>nat. \<langle>n,r\<rangle>\<in>Le},range(restrict(?NN,{n\<in>nat. \<langle>n,r\<rangle>\<in>Le})))"
          using fun_is_surj by auto moreover
        have "{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}\<subseteq>nat" by auto
        then have "{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}\<lesssim>nat" using subset_imp_lepoll by auto
        ultimately have "range(restrict(?NN,{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}))\<lesssim>{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}" using surj_fun_inv_2 by auto
        moreover
        have "{n\<in>nat. \<langle>n,0\<rangle>\<in>Le}={0}" by auto
        then have "Finite({n\<in>nat. \<langle>n,0\<rangle>\<in>Le})" by auto moreover
        {
          fix j assume as:"j\<in>nat" "Finite({n\<in>nat. \<langle>n,j\<rangle>\<in>Le})"
          {
            fix t assume "t\<in>{n\<in>nat. \<langle>n,succ(j)\<rangle>\<in>Le}"
            then have "t\<in>nat" "\<langle>t,succ(j)\<rangle>\<in>Le" by auto
            then have "t\<le>succ(j)" by auto
            then have "t\<subseteq>succ(j)" using le_imp_subset by auto
            then have "t\<subseteq>j \<union>{j}" using succ_explained by auto
            then have "j\<in>t\<or>t\<subseteq>j" by auto
            then have "j\<in>t\<or>t\<le>j" using subset_imp_le \<open>t\<in>nat\<close> \<open>j\<in>nat\<close> nat_into_Ord by auto
            then have "j \<union>{j}\<subseteq>t\<or>t\<le>j" using \<open>t\<in>nat\<close> \<open>j\<in>nat\<close> nat_into_Ord unfolding Ord_def
              Transset_def by auto
            then have "succ(j)\<subseteq>t\<or>t\<le>j" using succ_explained by auto
            with \<open>t\<subseteq>succ(j)\<close> have "t=succ(j)\<or>t\<le>j" by auto
            with \<open>t\<in>nat\<close> \<open>j\<in>nat\<close> have "t\<in>{n\<in>nat. \<langle>n,j\<rangle>\<in>Le} \<union> {succ(j)}" by auto
          }
          then have "{n\<in>nat. \<langle>n,succ(j)\<rangle>\<in>Le} \<subseteq>{n\<in>nat. \<langle>n,j\<rangle>\<in>Le} \<union> {succ(j)}" by auto
          moreover have "Finite({n\<in>nat. \<langle>n,j\<rangle>\<in>Le} \<union> {succ(j)})" using as(2) Finite_cons
            by auto
          ultimately have "Finite({n\<in>nat. \<langle>n,succ(j)\<rangle>\<in>Le})" using subset_Finite by auto
        }
        then have "\<forall>j\<in>nat. Finite({n\<in>nat. \<langle>n,j\<rangle>\<in>Le}) \<longrightarrow> Finite({n\<in>nat. \<langle>n,succ(j)\<rangle>\<in>Le})"
          by auto
        ultimately have "Finite(range(restrict(?NN, {n \<in> nat . \<langle>n, r\<rangle> \<in> Le})))"
          using lepoll_Finite[of "range(restrict(?NN, {n \<in> nat . \<langle>n, r\<rangle> \<in> Le}))"
            "{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}"] ind_on_nat[OF \<open>r\<in>nat\<close>, where P="\<lambda>t. Finite({n\<in>nat. \<langle>n,t\<rangle>\<in>Le})"] by auto
        then have "Finite((restrict(?NN, {n \<in> nat . \<langle>n, r\<rangle> \<in> Le}))``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})" using range_image_domain[OF NresFun]
          by auto
        then have "Finite(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})" using restrict_image by auto
        then have "(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}){is in the spectrum of}(\<lambda>T. (\<Union>T){is compact in}T)" using compact_spectrum by auto
        moreover have "\<Union>(T{restricted to}?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})=\<Union>T\<inter>?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}"
          unfolding RestrictedTo_def by auto moreover
        have "\<Union>T\<inter>?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}=?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}"
          using func1_1_L6(2)[OF R] by blast
        moreover have "(T{restricted to}?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}){is a topology}"
          using Top_1_L4 unfolding topology0_def by auto
        ultimately have "(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}){is compact in}(T{restricted to}?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})"
          unfolding Spec_def by force
        then have "(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le}){is compact in}(T)" using compact_subspace_imp_compact by auto
        moreover from Acov(1) have "(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})\<subseteq>\<Union>M" by auto
        moreover note Acov(2) ultimately
        obtain \<NN> where \<NN>:"\<NN>\<in>FinPow(M)" "(?NN``{n \<in> nat . \<langle>n, r\<rangle> \<in> Le})\<subseteq>\<Union>\<NN>"
          unfolding IsCompact_def by blast
        from \<NN>(1) have "\<NN> \<union>{V}\<in>FinPow(M)" using V(2) unfolding FinPow_def by auto moreover
        {
          fix s assume s:"s\<in>?A" "s\<notin>V"
          with V(1) have "s\<in>?NN``nat" by auto
          then have "s\<in>{?NN`n. n\<in>nat}" using func_imagedef[OF NFun] by auto
          then obtain n where n:"n\<in>nat" "s=?NN`n" by auto
          {
            assume "\<langle>r,n\<rangle>\<in>Le"
            with rr have "?NN`n\<in>V" by auto
            with n(2) s(2) have "False" by auto
          }
          then have "\<langle>r,n\<rangle>\<notin>Le" by auto
          with rr(1) n(1) have "\<not>(r\<le>n)" by auto
          then have "n\<le>r" using Ord_linear_le[where thesis="\<langle>n,r\<rangle>\<in>Le"] nat_into_Ord[OF rr(1)]
            nat_into_Ord[OF n(1)] by auto
          with rr(1) n(1) have "\<langle>n,r\<rangle>\<in>Le" by auto
          with n(2) have "s\<in>{?NN`t. t\<in>{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}}" by auto moreover
          have "{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}\<subseteq>nat" by auto
          ultimately have "s\<in>?NN``{n\<in>nat. \<langle>n,r\<rangle>\<in>Le}" using func_imagedef[OF NFun]
            by auto
          with \<NN>(2) have "s\<in>\<Union>\<NN>" by auto
        }
        then have "?A\<subseteq>\<Union>\<NN> \<union> V" by auto
        then have "?A\<subseteq>\<Union>(\<NN> \<union> {V})" by auto ultimately
        have "\<exists>\<NN>\<in>FinPow(M). ?A\<subseteq>\<Union>\<NN>" by auto
      }
      then have "\<forall>M\<in>Pow(T). ?A\<subseteq>\<Union>M \<longrightarrow> (\<exists>\<NN>\<in>FinPow(M). ?A\<subseteq>\<Union>\<NN>)" by auto moreover
      have ss:"?A\<subseteq>\<Union>(T)" using func1_1_L6(2)[OF R] x by blast ultimately
      have "?A{is compact in}(T)" unfolding IsCompact_def by auto moreover
      with assms have "?A{is closed in}(T)" unfolding IsKC_def IsCompact_def by auto ultimately
      have "?A\<in>{B\<in>Pow(\<Union>T). B{is compact in}(T)\<and>B{is closed in}(T)}" using ss by auto
      then have "{\<Union>T}\<union>(\<Union>T-?A)\<in>({one-point compactification of}T)" unfolding OPCompactification_def
        by auto
      then have "{\<Union>T}\<union>(\<Union>T-?A)=Interior({\<Union>T}\<union>(\<Union>T-?A),{one-point compactification of}T)" using topology0.Top_2_L3 op_comp_is_top
        unfolding topology0_def by auto moreover
      {
        assume "y\<in>?A"
        with A(4) have "y\<in>?NN``nat" by auto
        then have "y\<in>{?NN`n. n\<in>nat}" using func_imagedef[OF NFun] by auto
        then obtain n where "n\<in>nat""?NN`n=y" by auto
        with noy y have "False" by auto
      }
      with y have "y\<in>{\<Union>T}\<union>(\<Union>T-?A)" by force ultimately
      have "y\<in>Interior({\<Union>T}\<union>(\<Union>T-?A),{one-point compactification of}T)" "{\<Union>T}\<union>(\<Union>T-?A)\<in>Pow(\<Union>({one-point compactification of}T))"
        using op_compact_total by auto moreover
      have "(\<forall>U\<in>Pow(\<Union>({one-point compactification of}T)). y \<in> Interior(U,{one-point compactification of}T) \<longrightarrow> (\<exists>t\<in>nat. \<forall>m\<in>nat. \<langle>t, m\<rangle> \<in> Le \<longrightarrow> N ` m \<in> U))"
        using A(3) dom topology0.NetConverges_def[OF _ NET] op_comp_is_top unfolding topology0_def by auto
      ultimately have "\<exists>t\<in>nat. \<forall>m\<in>nat. \<langle>t, m\<rangle> \<in> Le \<longrightarrow> N ` m \<in> {\<Union>T}\<union>(\<Union>T-?A)" by blast
      then obtain r where r_def:"r\<in>nat" "\<forall>s\<in>nat. \<langle>r,s\<rangle>\<in>Le \<longrightarrow> N`s\<in>{\<Union>T}\<union>(\<Union>T-?A)" by auto
      {
        fix s assume AA:"\<langle>r,s\<rangle>\<in>Le"
        with reg obtain m where "N`m\<noteq>\<Union>T" "\<langle>s,m\<rangle>\<in>Le" by auto
        then have "\<langle>s,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le\<rangle>\<in>Le" using LeastI[of "\<lambda>m. N`m\<noteq>\<Union>T \<and> \<langle>s,m\<rangle>\<in>Le" "m"]
          nat_into_Ord by auto
        with AA have "\<langle>r,\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le\<rangle>\<in>Le" using le_trans by auto
        with r_def(2) have "N`(\<mu> i. N`i\<noteq>\<Union>T \<and> \<langle>s,i\<rangle>\<in>Le)\<in>{\<Union>T}\<union>(\<Union>T-?A)" by auto
        then have "?NN`s\<in>{\<Union>T}\<union>(\<Union>T-?A)" using apply_equality[OF _ NFun] AA by auto
        with noy have "?NN`s\<in>(\<Union>T-?A)" using AA by auto
        moreover have "?NN`s\<in>{?NN`t. t\<in>nat}" using AA by auto
        then have "?NN`s\<in>?NN``nat" using func_imagedef[OF NFun] by auto
        then have "?NN`s\<in>?A" by auto
        ultimately have "False" by auto
      }
      moreover have "r\<subseteq>succ(r)" using succ_explained by auto
      then have "r\<le>succ(r)" using subset_imp_le nat_into_Ord \<open>r\<in>nat\<close> nat_succI
        by auto
      then have "\<langle>r,succ(r)\<rangle>\<in>Le" using \<open>r\<in>nat\<close> nat_succI by auto
      ultimately have "False" by auto
    }
    ultimately have "False" by auto
  }
  then have "\<forall>N x y. N:nat\<rightarrow>(\<Union>{one-point compactification of}T) \<and> (\<langle>N,Le\<rangle>\<rightarrow>\<^sub>N x{in}({one-point compactification of}T))
    \<and> (\<langle>N,Le\<rangle>\<rightarrow>\<^sub>N y{in}({one-point compactification of}T)) \<longrightarrow> x=y" by auto
  then show ?thesis unfolding IsUS_def by auto
qed

text\<open>In the one-point compactification of an anti-compact space,
ever subspace that contains the infinite point is compact.\<close>

theorem (in topology0) anti_comp_imp_OP_inf_comp:
  assumes "T{is anti-compact}" "A\<subseteq>\<Union>({one-point compactification of}T)" "\<Union>T\<in>A"
  shows "A{is compact in}({one-point compactification of}T)"
proof-
  {
    fix M assume M:"M\<subseteq>({one-point compactification of}T)" "A\<subseteq>\<Union>M"
    with assms(3) obtain U where U:"\<Union>T\<in>U" "U\<in>M" by auto
    with M(1) obtain K where K:"K{is compact in}T" "K{is closed in}T" "U={\<Union>T}\<union>(\<Union>T-K)"
      unfolding OPCompactification_def using mem_not_refl[of "\<Union>T"] by auto
    from K(1) have "K{is compact in}(T{restricted to}K)" using compact_imp_compact_subspace Compact_is_card_nat
      by auto
    moreover have "\<Union>(T{restricted to}K)=\<Union>T\<inter>K" unfolding RestrictedTo_def by auto
    with K(1) have "\<Union>(T{restricted to}K)=K" unfolding IsCompact_def by auto ultimately
    have "(\<Union>(T{restricted to}K)){is compact in}(T{restricted to}K)" by auto
    with assms(1) have "K{is in the spectrum of}(\<lambda>T. (\<Union>T){is compact in}T)" unfolding IsAntiComp_def
      antiProperty_def using K(1) unfolding IsCompact_def by auto
    then have finK:"Finite(K)" using compact_spectrum by auto
    from assms(2) have "A-U\<subseteq>(\<Union>T \<union>{\<Union>T}) -U" using op_compact_total by auto
    with K(3) have "A-U\<subseteq>K" by auto
    with finK have "Finite(A-U)" using subset_Finite by auto
    then have "(A-U){is in the spectrum of}(\<lambda>T. (\<Union>T){is compact in}T)" using compact_spectrum by auto moreover
    have "\<Union>(({one-point compactification of}T){restricted to}(A-U))=A-U" unfolding RestrictedTo_def using assms(2) K(3)
      op_compact_total by auto moreover
    have "(({one-point compactification of}T){restricted to}(A-U)){is a topology}" using topology0.Top_1_L4
      op_comp_is_top unfolding topology0_def by auto
    ultimately have "(A-U){is compact in}(({one-point compactification of}T){restricted to}(A-U))"
      unfolding Spec_def by auto
    then have "(A-U){is compact in}({one-point compactification of}T)" using compact_subspace_imp_compact by auto
    moreover have "A-U\<subseteq>\<Union>M" using M(2) by auto moreover
    note M(1) ultimately obtain N where N:"N\<in>FinPow(M)" "A-U\<subseteq>\<Union>N" unfolding IsCompact_def by blast
    from N(1) U(2) have "N \<union>{U}\<in>FinPow(M)" unfolding FinPow_def by auto moreover
    from N(2) have "A\<subseteq>\<Union>(N \<union>{U})" by auto
    ultimately have "\<exists>R\<in>FinPow(M). A\<subseteq>\<Union>R" by auto
  }
  then show ?thesis using op_compact_total assms(2) unfolding IsCompact_def by auto
qed

text\<open>As a last result in this section, the one-point compactification of our topology is not a KC space.\<close>

theorem extension_pow_OP_not_KC:
  shows "\<not>(({one-point compactification of}(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})){is KC})"
proof
  have noE:"csucc(nat)\<noteq>0" using Ord_0_lt_csucc[OF Ord_nat] by auto
  let ?T="(Pow(csucc(nat)) \<union> {{csucc(nat)}\<union>S. S\<in>(CoCountable csucc(nat))-{0}})"
  assume ass:"({one-point compactification of}?T){is KC}"
  from extension_pow_notDiscrete have "{csucc(nat)} \<notin> (Pow(csucc(nat)) \<union> {{csucc(nat)} \<union> S . S \<in> (CoCountable csucc(nat)) - {0}})"
    by auto
  {
    assume "csucc(nat)=csucc(nat)\<union>{csucc(nat)}" moreover
    have "csucc(nat)\<in>csucc(nat)\<union>{csucc(nat)}" by auto
    ultimately have "csucc(nat)\<in>csucc(nat)" by auto
    then have "False" using mem_not_refl by auto
  }
  then have dist:"csucc(nat)\<noteq>csucc(nat)\<union>{csucc(nat)}" by blast
  {
    assume "{csucc(nat)}\<in>({one-point compactification of}(Pow(csucc(nat)) \<union> {{csucc(nat)} \<union> S . S \<in> (CoCountable csucc(nat)) - {0}}))"
    then have "{csucc(nat)}\<in>{{\<Union>?T}\<union>((\<Union>?T)-K). K\<in>{B\<in>Pow(\<Union>?T). B{is compact in}?T \<and> B{is closed in}?T}}"
      unfolding OPCompactification_def using extension_pow_notDiscrete by auto
    then obtain K where "{csucc(nat)}={\<Union>?T}\<union>((\<Union>?T)-K)" by auto moreover
    have "\<Union>?T\<in>{\<Union>?T}\<union>((\<Union>?T)-K)" by auto
    ultimately have "\<Union>?T\<in>{csucc(nat)}" by auto
    with dist have "False" using extension_pow_union by auto
  }
  then have "{csucc(nat)}\<notin>({one-point compactification of}?T)" by auto moreover
  have "\<Union>({one-point compactification of}?T)-(\<Union>({one-point compactification of}?T)-{csucc(nat)})={csucc(nat)}" using extension_pow_union
    topology0.op_compact_total unfolding topology0_def using extension_pow_top by auto ultimately
  have di:"\<Union>({one-point compactification of}?T)-(\<Union>({one-point compactification of}?T)-{csucc(nat)})\<notin>({one-point compactification of}?T)" by auto
  {
    assume "(\<Union>({one-point compactification of}?T)-{csucc(nat)}){is closed in}({one-point compactification of}?T)"
    then have "\<Union>({one-point compactification of}?T)-(\<Union>({one-point compactification of}?T)-{csucc(nat)})\<in>({one-point compactification of}?T)" unfolding IsClosed_def by auto
    with di have "False" by auto
  }
  then have n:"\<not>((\<Union>({one-point compactification of}?T)-{csucc(nat)}){is closed in}({one-point compactification of}?T))" by auto moreover
  from dist have "\<Union>?T\<in>(\<Union>({one-point compactification of}?T)-{csucc(nat)})" using topology0.op_compact_total unfolding topology0_def using extension_pow_top
    extension_pow_union by auto
  then have "(\<Union>({one-point compactification of}?T)-{csucc(nat)}){is compact in}({one-point compactification of}?T)" using topology0.anti_comp_imp_OP_inf_comp[of "?T"
    "(\<Union>({one-point compactification of}?T)-{csucc(nat)})"] unfolding topology0_def using extension_pow_antiCompact extension_pow_top by auto
  with ass have "(\<Union>({one-point compactification of}?T)-{csucc(nat)}){is closed in}({one-point compactification of}?T)" unfolding IsKC_def by auto
  with n show "False" by auto
qed
    
text\<open>In conclusion, $US\not\Rightarrow KC$.\<close>

subsection\<open>Other types of properties\<close>

text\<open>In this section we will define new properties that
aren't defined as anti-properties and that are not separation axioms.
In some cases we will consider their anti-properties.\<close>

subsection\<open>Definitions\<close>

text\<open>A space is called perfect if it has no isolated points.
This definition may vary in the literature to similar, but not equivalent definitions.\<close>

definition
  IsPerf ("_ {is perfect}") where
  "T{is perfect} \<equiv> \<forall>x\<in>\<Union>T. {x}\<notin>T"

text\<open>An anti-perfect space is called scattered.\<close>

definition
  IsScatt ("_ {is scattered}") where
  "T{is scattered} \<equiv> T{is anti-}IsPerf"

text\<open>A topological space with two disjoint dense subspaces
is called resolvable.\<close>

definition
  IsRes ("_ {is resolvable}") where
  "T{is resolvable} \<equiv> \<exists>U\<in>Pow(\<Union>T). \<exists>V\<in>Pow(\<Union>T). Closure(U,T)=\<Union>T \<and> Closure(V,T)=\<Union>T \<and> U\<inter>V=0"

text\<open>A topological space where every dense subset is open
is called submaximal.\<close>

definition
  IsSubMax ("_ {is submaximal}") where
  "T{is submaximal} \<equiv> \<forall>U\<in>Pow(\<Union>T). Closure(U,T)=\<Union>T \<longrightarrow> U\<in>T"

text\<open>A subset of a topological space is nowhere-dense if
the interior of its closure is empty.\<close>

definition
  IsNowhereDense ("_ {is nowhere dense in} _") where
  "A{is nowhere dense in}T \<equiv> A\<subseteq>\<Union>T \<and> Interior(Closure(A,T),T)=0"

text\<open>A topological space is then a Luzin space if
every nowhere-dense subset is countable.\<close>

definition
  IsLuzin ("_ {is luzin}") where
  "T{is luzin} \<equiv> \<forall>A\<in>Pow(\<Union>T). (A{is nowhere dense in}T) \<longrightarrow> A\<lesssim>nat"

text\<open>An also useful property is local-connexion.\<close>

definition
  IsLocConn ("_{is locally-connected}") where
  "T{is locally-connected} \<equiv> T{is locally}(\<lambda>T. \<lambda>B. ((T{restricted to}B){is connected}))"

text\<open>An SI-space is an anti-resolvable perfect space.\<close>

definition
  IsAntiRes ("_{is anti-resolvable}") where
  "T{is anti-resolvable} \<equiv> T{is anti-}IsRes"

definition
  IsSI ("_{is Strongly Irresolvable}") where
  "T{is Strongly Irresolvable} \<equiv> (T{is anti-resolvable}) \<and> (T{is perfect})"

subsection\<open>First examples\<close>

text\<open>Firstly, we need to compute the spectrum of
the being perfect.\<close>

lemma spectrum_perfect:
  shows "(A{is in the spectrum of}IsPerf) \<longleftrightarrow> A=0"
proof
  assume "A{is in the spectrum of}IsPerf"
  then have "Pow(A){is perfect}" unfolding Spec_def using Pow_is_top by auto
  then have "\<forall>b\<in>A. {b}\<notin>Pow(A)" unfolding IsPerf_def by auto
  then show "A=0" by auto
next
  assume A:"A=0"
  {
    fix T assume T:"T{is a topology}" "\<Union>T\<approx>A"
    with T(2) A have "\<Union>T\<approx>0" by auto
    then have "\<Union>T=0" using eqpoll_0_is_0 by auto
    then have "T{is perfect}" unfolding IsPerf_def by auto
  }
  then show "A{is in the spectrum of}IsPerf" unfolding Spec_def by auto
qed

text\<open>The discrete space is clearly scattered:\<close>

lemma pow_is_scattered:
  shows "Pow(A){is scattered}"
proof-
  {
    fix B assume B:"B\<subseteq>\<Union>Pow(A)" "(Pow(A){restricted to}B){is perfect}"
    from B(1) have "Pow(A){restricted to}B=Pow(B)" unfolding RestrictedTo_def by blast
    with B(2) have "Pow(B){is perfect}" by auto
    then have "\<forall>b\<in>B. {b}\<notin>Pow(B)" unfolding IsPerf_def by auto
    then have "B=0" by auto
  }
  then show ?thesis using spectrum_perfect unfolding IsScatt_def antiProperty_def by auto
qed

text\<open>The trivial topology is perfect, if it is defined over a set with more than one point.\<close>

lemma trivial_is_perfect:
  assumes "\<exists>x y. x\<in>X \<and> y\<in>X \<and> x\<noteq>y"
  shows "{0,X}{is perfect}"
proof-
  {
    fix r assume "{r}\<in>{0,X}"
    then have "X={r}" by auto
    with assms have "False" by auto
  }
  then show ?thesis unfolding IsPerf_def by auto
qed

text\<open>The trivial topology is resolvable, if it is defined over a set with more than one point.\<close>

lemma trivial_is_resolvable:
  assumes "\<exists>x y. x\<in>X \<and> y\<in>X \<and> x\<noteq>y"
  shows "{0,X}{is resolvable}"
proof-
  from assms obtain x y where xy:"x\<in>X" "y\<in>X" "x\<noteq>y" by auto
  {
    fix A assume A:"A{is closed in}{0,X}" "A\<subseteq>X"
    then have "X-A\<in>{0,X}" unfolding IsClosed_def by auto
    then have "X-A=0\<or>X-A=X" by auto
    with A(2) have "A=X\<or>X-A=X" by auto moreover
    {
      assume "X-A=X"
      then have "X-(X-A)=0" by auto
      with A(2) have "A=0" by auto
    }
    ultimately have "A=X\<or>A=0" by auto
    then have "A=0\<or>A=X" by auto
  }
  then have cl:"\<forall>A\<in>Pow(X). A{is closed in}{0,X} \<longrightarrow> A=0\<or>A=X" by auto
  from xy(3) have "{x}\<inter>{y}=0" by auto moreover
  {
    have "{X}{is a partition of}X" using indiscrete_partition xy(1) by auto
    then have top:"topology0(PTopology X {X})" using topology0_ptopology by auto
    have "X\<noteq>0" using xy(1) by auto
    then have "(PTopology X {X})={0,X}" using indiscrete_ptopology[of "X"] by auto
    with top have top0:"topology0({0,X})" by auto
    then have "x\<in>Closure({x},{0,X})" using topology0.cl_contains_set xy(1) by auto moreover
    have "Closure({x},{0,X}) {is closed in}{0,X}" using topology0.cl_is_closed top0 xy(1) by auto
    moreover note cl
    moreover have "Closure({x},{0,X})\<subseteq>X" using topology0.Top_3_L11(1) top0 xy(1) by auto
    ultimately have "Closure({x},{0,X})=X" by auto
  }
  moreover
  {
    have "{X}{is a partition of}X" using indiscrete_partition xy(1) by auto
    then have top:"topology0(PTopology X {X})" using topology0_ptopology by auto
    have "X\<noteq>0" using xy(1) by auto
    then have "(PTopology X {X})={0,X}" using indiscrete_ptopology[of "X"] by auto
    with top have top0:"topology0({0,X})" by auto
    then have "y\<in>Closure({y},{0,X})" using topology0.cl_contains_set xy(2) by auto moreover
    have "Closure({y},{0,X}) {is closed in}{0,X}" using topology0.cl_is_closed top0 xy(2) by auto
    moreover note cl
    moreover have "Closure({y},{0,X})\<subseteq>X" using topology0.Top_3_L11(1) top0 xy(2) by auto
    ultimately have "Closure({y},{0,X})=X" by auto
  } 
  ultimately show ?thesis using xy(1,2) unfolding IsRes_def by auto
qed

text\<open>The spectrum of Luzin spaces is the class of countable sets, so there
are lots of examples of Luzin spaces.\<close>

lemma spectrum_Luzin:
  shows "(A{is in the spectrum of}IsLuzin) \<longleftrightarrow> A\<lesssim>nat"
proof
  assume A:"A{is in the spectrum of}IsLuzin"
  {
    assume "A=0"
    then have "A\<lesssim>nat" using empty_lepollI by auto
  }
  moreover
  {
    assume "A\<noteq>0"
    then obtain x where x:"x\<in>A" by auto
    {
      fix M assume "M\<subseteq>{0,{x},A}"
      then have "\<Union>M\<in>{0,{x},A}" using x by blast
    }
    moreover
    {
      fix U V assume "U\<in>{0,{x},A}" "V\<in>{0,{x},A}"
      then have "U\<inter>V\<in>{0,{x},A}" by auto
    }
    ultimately have top:"{0,{x},A}{is a topology}" unfolding IsATopology_def by auto
    moreover have tot:"\<Union>{0,{x},A}=A" using x by auto
    moreover note A ultimately have luz:"{0,{x},A}{is luzin}" unfolding Spec_def by auto
    moreover have "{x}\<in>{0,{x},A}" by auto
    then have "((\<Union>{0,{x},A})-{x}){is closed in}{0,{x},A}" using topology0.Top_3_L9
      unfolding topology0_def using top by blast
    then have "(A-{x}){is closed in}{0,{x},A}" using tot by auto
    then have "Closure(A-{x},{0,{x},A})=A-{x}" using tot top topology0.Top_3_L8[of "{0,{x},A}"]
      unfolding topology0_def by auto
    then have B:"Interior(Closure(A-{x},{0,{x},A}),{0,{x},A})=Interior(A-{x},{0,{x},A})" by auto
    then have C:"Interior(Closure(A-{x},{0,{x},A}),{0,{x},A})\<subseteq>A-{x}" using top topology0.Top_2_L1
      unfolding topology0_def by auto
    then have D:"Interior(Closure(A-{x},{0,{x},A}),{0,{x},A})\<in>{0,{x},A}" using topology0.Top_2_L2 
      unfolding topology0_def using top by auto
    from x have "\<not>(A\<subseteq>A-{x})" by auto
    with C D have "Interior(Closure(A-{x},{0,{x},A}),{0,{x},A})=0" by auto
    then have "(A-{x}){is nowhere dense in}{0,{x},A}" unfolding IsNowhereDense_def using tot
      by auto
    with luz have "A-{x}\<lesssim>nat" unfolding IsLuzin_def using tot by auto
    then have U1:"A-{x}\<prec>csucc(nat)" using Card_less_csucc_eq_le[OF Card_nat] by auto
    have "{x}\<approx>1" using singleton_eqpoll_1 by auto
    then have "{x}\<prec>nat" using n_lesspoll_nat eq_lesspoll_trans by auto
    then have "{x}\<lesssim>nat" using lesspoll_imp_lepoll by auto
    then have U2:"{x}\<prec>csucc(nat)" using Card_less_csucc_eq_le[OF Card_nat] by auto
    with U1 have U:"(A-{x})\<union>{x}\<prec>csucc(nat)" using less_less_imp_un_less[OF _ _ InfCard_csucc[OF InfCard_nat]]
      by auto
    have "(A-{x})\<union>{x}=A" using x by auto
    with U have "A\<prec>csucc(nat)" by auto
    then have "A\<lesssim>nat" using Card_less_csucc_eq_le[OF Card_nat] by auto
  }
  ultimately
  show "A\<lesssim>nat" by auto
next
  assume A:"A\<lesssim>nat"
  {
    fix T assume T:"T{is a topology}" "\<Union>T\<approx>A"
    {
      fix B assume "B\<subseteq>\<Union>T" "B{is nowhere dense in}T"
      then have "B\<lesssim>\<Union>T" using subset_imp_lepoll by auto
      with T(2) have "B\<lesssim>A" using lepoll_eq_trans by auto
      with A have "B\<lesssim>nat" using lepoll_trans by blast
    }
    then have "\<forall>B\<in>Pow(\<Union>T). (B{is nowhere dense in}T) \<longrightarrow> B\<lesssim>nat" by auto
    then have "T{is luzin}" unfolding IsLuzin_def by auto
  }
  then show "A{is in the spectrum of}IsLuzin" unfolding Spec_def by auto
qed

subsection\<open>Structural results\<close>

text\<open>Every resolvable space is also perfect.\<close>

theorem (in topology0) resolvable_imp_perfect:
  assumes "T{is resolvable}"
  shows "T{is perfect}"
proof-
  {
    assume "\<not>(T{is perfect})"
    then obtain x where x:"x\<in>\<Union>T" "{x}\<in>T" unfolding IsPerf_def by auto
    then have cl:"(\<Union>T-{x}){is closed in}T" using Top_3_L9 by auto
    from assms obtain U V where UV:"U\<subseteq>\<Union>T" "V\<subseteq>\<Union>T" "cl(U)=\<Union>T" "cl(V)=\<Union>T" "U\<inter>V=0" unfolding IsRes_def by auto
    {
      fix W assume "x\<notin>W" "W\<subseteq>\<Union>T"
      then have "W\<subseteq>\<Union>T-{x}" by auto
      then have "cl(W)\<subseteq>\<Union>T-{x}" using cl Top_3_L13 by auto
      with x(1) have "\<not>(\<Union>T\<subseteq>cl(W))" by auto
      then have "\<not>(cl(W)=\<Union>T)" by auto
    }
    with UV have "False" by auto
  }
  then show ?thesis by auto
qed
   
text\<open>The spectrum of being resolvable follows:\<close>

corollary spectrum_resolvable:
  shows "(A{is in the spectrum of}IsRes) \<longleftrightarrow> A=0"
proof
  assume A:"A{is in the spectrum of}IsRes"
  have "\<forall>T. T{is a topology} \<longrightarrow> IsRes(T) \<longrightarrow> IsPerf(T)" using topology0.resolvable_imp_perfect 
    unfolding topology0_def by auto
  with A have "A{is in the spectrum of}IsPerf" using P_imp_Q_spec_inv[of IsRes IsPerf] by auto
  then show "A=0" using spectrum_perfect by auto
next
  assume A:"A=0"
  {
    fix T assume T:"T{is a topology}" "\<Union>T\<approx>A"
    with T(2) A have "\<Union>T\<approx>0" by auto
    then have "\<Union>T=0" using eqpoll_0_is_0 by auto
    then have "Closure(0,T)=\<Union>T" using topology0.Top_3_L2 T(1)
      topology0.Top_3_L8 unfolding topology0_def by auto
    then have "T{is resolvable}" unfolding IsRes_def by auto
  }
  then show "A{is in the spectrum of}IsRes" unfolding Spec_def by auto
qed

text\<open>The cofinite space over $\mathbb{N}$ is a $T_1$, perfect and luzin space.\<close>

theorem cofinite_nat_perfect:
  shows "(CoFinite nat){is perfect}"
proof-
  {
    fix x assume x:"x\<in>\<Union>(CoFinite nat)" "{x}\<in>(CoFinite nat)"
    then have xn:"x\<in>nat" using union_cocardinal unfolding Cofinite_def by auto
    with x(2) have "nat-{x}\<prec>nat" unfolding Cofinite_def CoCardinal_def by auto
    moreover have "Finite({x})" by auto
    then have "{x}\<prec>nat" unfolding Finite_def using n_lesspoll_nat eq_lesspoll_trans by auto
    ultimately have "(nat-{x})\<union>{x}\<prec>nat" using less_less_imp_un_less[OF _ _ InfCard_nat] by auto
    moreover have "(nat-{x})\<union>{x}=nat" using xn by auto
    ultimately have "False" by auto
  }
  then show ?thesis unfolding IsPerf_def by auto
qed

theorem cofinite_nat_luzin:
  shows "(CoFinite nat){is luzin}"
proof-
  have "nat{is in the spectrum of}IsLuzin" using spectrum_Luzin by auto moreover
  have "\<Union>(CoFinite nat)=nat" using union_cocardinal unfolding Cofinite_def by auto
  moreover have "(CoFinite nat){is a topology}" unfolding Cofinite_def using CoCar_is_topology[OF InfCard_nat]
    by auto
  ultimately show ?thesis unfolding Spec_def by auto
qed

text\<open>The cocountable topology on $\mathbb{N}^+$ or \<open>csucc(nat)\<close> is also $T_1$,
perfect and luzin; but defined on a set not in the spectrum.\<close>

theorem cocountable_csucc_nat_perfect:
  shows "(CoCountable csucc(nat)){is perfect}"
proof-
  have noE:"csucc(nat)\<noteq>0" using lt_csucc[OF Ord_nat] by auto 
  {
    fix x assume x:"x\<in>\<Union>(CoCountable csucc(nat))" "{x}\<in>(CoCountable csucc(nat))"
    then have xn:"x\<in>csucc(nat)" using union_cocardinal noE unfolding Cocountable_def by auto
    with x(2) have "csucc(nat)-{x}\<prec>csucc(nat)" unfolding Cocountable_def CoCardinal_def by auto
    moreover have "Finite({x})" by auto
    then have "{x}\<prec>nat" unfolding Finite_def using n_lesspoll_nat eq_lesspoll_trans by auto
    then have "{x}\<lesssim>nat" using lesspoll_imp_lepoll by auto
    then have "{x}\<prec>csucc(nat)" using Card_less_csucc_eq_le[OF Card_nat] by auto
    ultimately have "(csucc(nat)-{x})\<union>{x}\<prec>csucc(nat)" using less_less_imp_un_less[OF _ _ InfCard_csucc[OF InfCard_nat]] by auto
    moreover have "(csucc(nat)-{x})\<union>{x}=csucc(nat)" using xn by auto
    ultimately have "False" by auto
  }
  then show ?thesis unfolding IsPerf_def by auto
qed

theorem cocountable_csucc_nat_luzin:
  shows "(CoCountable csucc(nat)){is luzin}"
proof-
  have noE:"csucc(nat)\<noteq>0" using lt_csucc[OF Ord_nat] by auto 
  {
    fix B assume B:"B\<in>Pow(\<Union>(CoCountable csucc(nat)))" "B{is nowhere dense in}(CoCountable csucc(nat))" "\<not>(B\<lesssim>nat)"
    from B(1) have "B\<subseteq>csucc(nat)" using union_cocardinal noE unfolding Cocountable_def by auto moreover
    from B(3) have "\<not>(B\<prec>csucc(nat))" using Card_less_csucc_eq_le[OF Card_nat] by auto ultimately
    have "Closure(B,CoCountable csucc(nat))=csucc(nat)" using closure_set_cocardinal noE unfolding Cocountable_def by auto
    then have "Interior(Closure(B,CoCountable csucc(nat)),CoCountable csucc(nat))=Interior(csucc(nat),CoCountable csucc(nat))" by auto
    with B(2) have "0=Interior(csucc(nat),CoCountable csucc(nat))" unfolding IsNowhereDense_def by auto moreover
    have "csucc(nat)-csucc(nat)=0" by auto
    then have "csucc(nat)-csucc(nat)\<prec>csucc(nat)" using empty_lepollI Card_less_csucc_eq_le[OF Card_nat] by auto
    then have "Interior(csucc(nat),CoCountable csucc(nat))=csucc(nat)" using interior_set_cocardinal noE unfolding Cocountable_def by auto
    ultimately have "False" using noE by auto
  }
  then have "\<forall>B\<in>Pow(\<Union>(CoCountable csucc(nat))). (B{is nowhere dense in}(CoCountable csucc(nat))) \<longrightarrow> B\<lesssim>nat" by auto
  then show ?thesis unfolding IsLuzin_def by auto
qed

text\<open>The existence of $T_2$, uncountable, perfect and luzin spaces is unprovable in \emph{ZFC}.
It is related to the \emph{CH} and Martin's axiom.\<close>

end


