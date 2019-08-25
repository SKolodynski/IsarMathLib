(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2013  Daniel de la Concepcion

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

section \<open>Groups 4\<close>

theory Group_ZF_4 imports Group_ZF_1 Group_ZF_2 Finite_ZF Ring_ZF
  Cardinal_ZF Semigroup_ZF

begin

text\<open>This theory file deals with normal subgroup test and some finite group theory.
Then we define group homomorphisms and prove that the set of endomorphisms
forms a ring with unity and we also prove the first isomorphism theorem.\<close>

subsection\<open>Conjugation of subgroups\<close>

text\<open>The conjugate of a subgroup is a subgroup.\<close>

theorem(in group0) semigr0:
  shows "semigr0(G,P)"
  unfolding semigr0_def using groupAssum IsAgroup_def IsAmonoid_def by auto

theorem (in group0) conj_group_is_group:
  assumes "IsAsubgroup(H,P)" "g\<in>G"
  shows "IsAsubgroup({g\<cdot>(h\<cdot>g\<inverse>). h\<in>H},P)"
proof-
  have sub:"H\<subseteq>G" using assms(1) group0_3_L2 by auto
  from assms(2) have "g\<inverse>\<in>G" using inverse_in_group by auto
  {
    fix r assume "r\<in>{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}"
    then  obtain h where h:"h\<in>H" "r=g\<cdot>(h\<cdot>(g\<inverse>))" by auto
    from h(1) have "h\<inverse>\<in>H" using group0_3_T3A assms(1) by auto
    from h(1) sub have "h\<in>G" by auto
    then have "h\<inverse>\<in>G" using inverse_in_group by auto
    with \<open>g\<inverse>\<in>G\<close> have "((h\<inverse>)\<cdot>(g)\<inverse>)\<in>G" using group_op_closed by auto
    from h(2) have "r\<inverse>=(g\<cdot>(h\<cdot>(g\<inverse>)))\<inverse>" by auto moreover
    from \<open>h\<in>G\<close> \<open>g\<inverse>\<in>G\<close> have s:"h\<cdot>(g\<inverse>)\<in>G" using group_op_closed by blast
    ultimately have "r\<inverse>=(h\<cdot>(g\<inverse>))\<inverse>\<cdot>(g)\<inverse>" using group_inv_of_two[OF assms(2)] by auto
    moreover
    from s assms(2) h(2) have r:"r\<in>G" using group_op_closed by auto
    have "(h\<cdot>(g\<inverse>))\<inverse>=(g\<inverse>)\<inverse>\<cdot>h\<inverse>" using group_inv_of_two[OF \<open>h\<in>G\<close>\<open>g\<inverse>\<in>G\<close>] by auto
    moreover have "(g\<inverse>)\<inverse>=g" using group_inv_of_inv[OF assms(2)] by auto
    ultimately have "r\<inverse>=(g\<cdot>(h\<inverse>))\<cdot>(g)\<inverse>" by auto
    then have "r\<inverse>=g\<cdot>((h\<inverse>)\<cdot>(g)\<inverse>)" using group_oper_assoc[OF assms(2) \<open>h\<inverse>\<in>G\<close>\<open>g\<inverse>\<in>G\<close>] by auto
    with \<open>h\<inverse>\<in>H\<close> r have "r\<inverse>\<in>{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}" "r\<in>G" by auto
  }
  then have "\<forall>r\<in>{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}. r\<inverse>\<in>{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}" and "{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}\<subseteq>G" by auto moreover
  {
    fix s t assume s:"s\<in>{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}" and t:"t\<in>{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}"
    then obtain hs ht where hs:"hs\<in>H" "s=g\<cdot>(hs\<cdot>(g\<inverse>))" and ht:"ht\<in>H" "t=g\<cdot>(ht\<cdot>(g\<inverse>))" by auto
    from hs(1) have "hs\<in>G" using sub by auto
    then have "g\<cdot>hs\<in>G" using group_op_closed assms(2) by auto
    then have "(g\<cdot>hs)\<inverse>\<in>G" using inverse_in_group by auto
    from ht(1) have "ht\<in>G" using sub by auto
    with \<open>g\<inverse>:G\<close> have "ht\<cdot>(g\<inverse>)\<in>G" using group_op_closed by auto
    from hs(2) ht(2) have "s\<cdot>t=(g\<cdot>(hs\<cdot>(g\<inverse>)))\<cdot>(g\<cdot>(ht\<cdot>(g\<inverse>)))" by auto moreover
    have "g\<cdot>(hs\<cdot>(g\<inverse>))=g\<cdot>hs\<cdot>(g\<inverse>)" using group_oper_assoc[OF assms(2) \<open>hs\<in>G\<close> \<open>g\<inverse>\<in>G\<close>] by auto
    then have "(g\<cdot>(hs\<cdot>(g\<inverse>)))\<cdot>(g\<cdot>(ht\<cdot>(g\<inverse>)))=(g\<cdot>hs\<cdot>(g\<inverse>))\<cdot>(g\<cdot>(ht\<cdot>(g\<inverse>)))" by auto
    then have "(g\<cdot>(hs\<cdot>(g\<inverse>)))\<cdot>(g\<cdot>(ht\<cdot>(g\<inverse>)))=(g\<cdot>hs\<cdot>(g\<inverse>))\<cdot>(g\<inverse>\<inverse>\<cdot>(ht\<cdot>(g\<inverse>)))" using group_inv_of_inv[OF assms(2)] by auto
    also have "\<dots>=g\<cdot>hs\<cdot>(ht\<cdot>(g\<inverse>))" using group0_2_L14A(2)[OF \<open>(g\<cdot>hs)\<inverse>\<in>G\<close> \<open>g\<inverse>\<in>G\<close>\<open>ht\<cdot>(g\<inverse>)\<in>G\<close>] group_inv_of_inv[OF \<open>(g\<cdot>hs)\<in>G\<close>]
      by auto
    ultimately have "s\<cdot>t=g\<cdot>hs\<cdot>(ht\<cdot>(g\<inverse>))" by auto moreover
    have "hs\<cdot>(ht\<cdot>(g\<inverse>))=(hs\<cdot>ht)\<cdot>(g\<inverse>)" using group_oper_assoc[OF \<open>hs\<in>G\<close>\<open>ht\<in>G\<close>\<open>g\<inverse>\<in>G\<close>] by auto moreover 
    have "g\<cdot>hs\<cdot>(ht\<cdot>(g\<inverse>))=g\<cdot>(hs\<cdot>(ht\<cdot>(g\<inverse>)))" using group_oper_assoc[OF \<open>g\<in>G\<close>\<open>hs\<in>G\<close>\<open>(ht\<cdot>g\<inverse>)\<in>G\<close>] by auto
    ultimately have "s\<cdot>t=g\<cdot>((hs\<cdot>ht)\<cdot>(g\<inverse>))" by auto moreover
    from hs(1) ht(1) have "hs\<cdot>ht\<in>H" using assms(1) group0_3_L6 by auto
    ultimately have "s\<cdot>t\<in>{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}" by auto
  }
  then have "{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H} {is closed under}P" unfolding IsOpClosed_def by auto moreover
  from assms(1) have "\<one>\<in>H" using group0_3_L5 by auto
  then have "g\<cdot>(\<one>\<cdot>g\<inverse>)\<in>{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}" by auto
  then have "{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}\<noteq>0" by auto ultimately
  show ?thesis using group0_3_T3 by auto
qed

text\<open>Every set is equipollent with its conjugates.\<close>

theorem (in group0) conj_set_is_eqpoll:
  assumes "H\<subseteq>G" "g\<in>G"
  shows "H\<approx>{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}"
proof-
  have fun:"{\<langle>h,g\<cdot>(h\<cdot>g\<inverse>)\<rangle>. h\<in>H}:H\<rightarrow>{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}" unfolding Pi_def function_def domain_def by auto
  {
    fix h1 h2 assume "h1\<in>H""h2\<in>H""{\<langle>h,g\<cdot>(h\<cdot>g\<inverse>)\<rangle>. h\<in>H}`h1={\<langle>h,g\<cdot>(h\<cdot>g\<inverse>)\<rangle>. h\<in>H}`h2"
    with fun have "g\<cdot>(h1\<cdot>g\<inverse>)=g\<cdot>(h2\<cdot>g\<inverse>)""h1\<cdot>g\<inverse>\<in>G""h2\<cdot>g\<inverse>\<in>G""h1\<in>G""h2\<in>G" using apply_equality assms(1)
      group_op_closed[OF _ inverse_in_group[OF assms(2)]] by auto
    then have "h1\<cdot>g\<inverse>=h2\<cdot>g\<inverse>" using group0_2_L19(2)[OF \<open>h1\<cdot>g\<inverse>\<in>G\<close> \<open>h2\<cdot>g\<inverse>\<in>G\<close> assms(2)] by auto
    then have "h1=h2" using group0_2_L19(1)[OF \<open>h1\<in>G\<close>\<open>h2\<in>G\<close> inverse_in_group[OF assms(2)]] by auto
  }
  then have "\<forall>h1\<in>H. \<forall>h2\<in>H. {\<langle>h,g\<cdot>(h\<cdot>g\<inverse>)\<rangle>. h\<in>H}`h1={\<langle>h,g\<cdot>(h\<cdot>g\<inverse>)\<rangle>. h\<in>H}`h2 \<longrightarrow> h1=h2" by auto
  with fun have "{\<langle>h,g\<cdot>(h\<cdot>g\<inverse>)\<rangle>. h\<in>H}\<in>inj(H,{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H})" unfolding inj_def by auto moreover
  {
    fix ghg assume "ghg\<in>{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}"
    then obtain h where "h\<in>H" "ghg=g\<cdot>(h\<cdot>g\<inverse>)" by auto
    then have "\<langle>h,ghg\<rangle>\<in>{\<langle>h,g\<cdot>(h\<cdot>g\<inverse>)\<rangle>. h\<in>H}" by auto
    then have "{\<langle>h,g\<cdot>(h\<cdot>g\<inverse>)\<rangle>. h\<in>H}`h=ghg" using apply_equality fun by auto
    with \<open>h\<in>H\<close> have "\<exists>h\<in>H. {\<langle>h,g\<cdot>(h\<cdot>g\<inverse>)\<rangle>. h\<in>H}`h=ghg" by auto
  }
  with fun have "{\<langle>h,g\<cdot>(h\<cdot>g\<inverse>)\<rangle>. h\<in>H}\<in>surj(H,{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H})" unfolding surj_def by auto
  ultimately have "{\<langle>h,g\<cdot>(h\<cdot>g\<inverse>)\<rangle>. h\<in>H}\<in>bij(H,{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H})" unfolding bij_def by auto
  then show ?thesis unfolding eqpoll_def by auto
qed

text\<open>Every normal subgroup contains its conjugate subgroups.\<close>

theorem (in group0) norm_group_cont_conj:
  assumes "IsAnormalSubgroup(G,P,H)" "g\<in>G"
  shows "{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}\<subseteq>H"
proof-
  {
    fix r assume "r\<in>{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}"
    then obtain h where "r=g\<cdot>(h\<cdot>g\<inverse>)" "h\<in>H" by auto moreover
    then have "h\<in>G" using group0_3_L2 assms(1) unfolding IsAnormalSubgroup_def by auto moreover
    from assms(2) have "g\<inverse>\<in>G" using inverse_in_group by auto
    ultimately have "r=g\<cdot>h\<cdot>g\<inverse>" "h\<in>H" using group_oper_assoc assms(2) by auto
    then have "r\<in>H" using assms unfolding IsAnormalSubgroup_def by auto
  }
  then show "{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}\<subseteq>H" by auto
qed

text\<open>If a subgroup contains all its conjugate subgroups, then it is normal.\<close>

theorem (in group0) cont_conj_is_normal:
  assumes "IsAsubgroup(H,P)" "\<forall>g\<in>G. {g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}\<subseteq>H"
  shows "IsAnormalSubgroup(G,P,H)"
proof-
  {
    fix h g assume "h\<in>H" "g\<in>G"
    with assms(2) have "g\<cdot>(h\<cdot>g\<inverse>)\<in>H" by auto
    moreover have "h\<in>G""g\<inverse>\<in>G" using group0_3_L2 assms(1) \<open>g\<in>G\<close>\<open>h\<in>H\<close> inverse_in_group by auto
    ultimately have "g\<cdot>h\<cdot>g\<inverse>\<in>H" using group_oper_assoc \<open>g\<in>G\<close> by auto
  }
  then show ?thesis using assms(1) unfolding IsAnormalSubgroup_def by auto
qed

text\<open>If a group has only one subgroup of a given order, then this subgroup is normal.\<close>

corollary(in group0) only_one_equipoll_sub:
  assumes "IsAsubgroup(H,P)" "\<forall>M. IsAsubgroup(M,P)\<and> H\<approx>M \<longrightarrow> M=H"
  shows "IsAnormalSubgroup(G,P,H)"
proof-
  {
    fix g assume g:"g\<in>G"
    with assms(1) have "IsAsubgroup({g\<cdot>(h\<cdot>g\<inverse>). h\<in>H},P)" using conj_group_is_group by auto
    moreover
    from assms(1) g have "H\<approx>{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}" using conj_set_is_eqpoll group0_3_L2 by auto
    ultimately have "{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}=H" using assms(2) by auto
    then have "{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}\<subseteq>H" by auto
  }
  then show ?thesis using cont_conj_is_normal assms(1) by auto
qed

text\<open>The trivial subgroup is then a normal subgroup.\<close>

corollary(in group0) trivial_normal_subgroup:
  shows "IsAnormalSubgroup(G,P,{\<one>})"
proof-
  have "{\<one>}\<subseteq>G" using group0_2_L2 by auto
  moreover have "{\<one>}\<noteq>0" by auto moreover
  {
    fix a b assume "a\<in>{\<one>}""b\<in>{\<one>}"
    then have "a=\<one>""b=\<one>" by auto
    then have "P`\<langle>a,b\<rangle>=\<one>\<cdot>\<one>" by auto
    then have "P`\<langle>a,b\<rangle>=\<one>" using group0_2_L2 by auto
    then have "P`\<langle>a,b\<rangle>\<in>{\<one>}" by auto
  }
  then have "{\<one>}{is closed under}P" unfolding IsOpClosed_def by auto
  moreover
  {
    fix a assume "a\<in>{\<one>}"
    then have "a=\<one>" by auto
    then have "a\<inverse>=\<one>\<inverse>" by auto
    then have "a\<inverse>=\<one>" using group_inv_of_one by auto
    then have "a\<inverse>\<in>{\<one>}" by auto
  }
  then have "\<forall>a\<in>{\<one>}. a\<inverse>\<in>{\<one>}" by auto ultimately
  have "IsAsubgroup({\<one>},P)" using group0_3_T3 by auto moreover
  {
    fix M assume M:"IsAsubgroup(M,P)" "{\<one>}\<approx>M"
    then have "\<one>\<in>M" "M\<approx>{\<one>}" using eqpoll_sym group0_3_L5 by auto
    then obtain f where "f\<in>bij(M,{\<one>})" unfolding eqpoll_def by auto
    then have inj:"f\<in>inj(M,{\<one>})" unfolding bij_def by auto
    then have fun:"f:M\<rightarrow>{\<one>}" unfolding inj_def by auto
    {
      fix b assume "b\<in>M""b\<noteq>\<one>"
      then have "f`b\<noteq>f`\<one>" using inj \<open>\<one>\<in>M\<close> unfolding inj_def by auto
      then have "False" using \<open>b\<in>M\<close> \<open>\<one>\<in>M\<close> apply_type[OF fun] by auto
    }
    then have "M={\<one>}" using \<open>\<one>\<in>M\<close> by auto
  }
  ultimately show ?thesis using only_one_equipoll_sub by auto
qed

lemma(in group0) whole_normal_subgroup:
  shows "IsAnormalSubgroup(G,P,G)"
  unfolding IsAnormalSubgroup_def
  using group_op_closed inverse_in_group
  using group0_2_L2 group0_3_T3[of "G"] unfolding IsOpClosed_def
    by auto

text\<open>Since the whole group and the trivial subgroup are normal,
it is natural to define simplicity of groups in the following way:\<close>

definition
  IsSimple ("[_,_]{is a simple group}" 89)
  where "[G,f]{is a simple group} \<equiv> IsAgroup(G,f)\<and>(\<forall>M. IsAnormalSubgroup(G,f,M) \<longrightarrow> M=G\<or>M={TheNeutralElement(G,f)})"

text\<open>From the definition follows that if a group has no subgroups,
then it is simple.\<close>

corollary (in group0) noSubgroup_imp_simple:
  assumes "\<forall>H. IsAsubgroup(H,P)\<longrightarrow> H=G\<or>H={\<one>}"
  shows "[G,P]{is a simple group}"
proof-
  have "IsAgroup(G,P)" using groupAssum. moreover
  {
    fix M assume "IsAnormalSubgroup(G,P,M)"
    then have "IsAsubgroup(M,P)" unfolding IsAnormalSubgroup_def by auto
    with assms have "M=G\<or>M={\<one>}" by auto
  }
  ultimately show ?thesis unfolding IsSimple_def by auto
qed

text\<open>Since every subgroup is normal in abelian
groups, it follows that commutative simple groups
do not have subgroups.\<close>

corollary (in group0) abelian_simple_noSubgroups:
  assumes "[G,P]{is a simple group}" "P{is commutative on}G"
  shows "\<forall>H. IsAsubgroup(H,P)\<longrightarrow> H=G\<or>H={\<one>}"
proof(safe)
  fix H assume A:"IsAsubgroup(H,P)""H \<noteq> {\<one>}"
  then have "IsAnormalSubgroup(G,P,H)" using Group_ZF_2_4_L6(1) groupAssum assms(2)
    by auto
  with assms(1) A show "H=G" unfolding IsSimple_def by auto
qed

subsection\<open>Finite groups\<close>

text\<open>The subgroup of a finite group is finite.\<close>

lemma(in group0) finite_subgroup:
  assumes "Finite(G)" "IsAsubgroup(H,P)"
  shows "Finite(H)"
  using group0_3_L2 subset_Finite assms by force

text\<open>The space of cosets is also finite. In particular, quotient groups.\<close>

lemma(in group0) finite_cosets:
  assumes "Finite(G)" "IsAsubgroup(H,P)" "r=QuotientGroupRel(G,P,H)"
  shows "Finite(G//r)"
proof- 
  have fun:"{\<langle>g,r``{g}\<rangle>. g\<in>G}:G\<rightarrow>(G//r)" unfolding Pi_def function_def domain_def by auto
  {
    fix C assume C:"C\<in>G//r"
    then obtain c where c:"c\<in>C" using EquivClass_1_L5[OF Group_ZF_2_4_L1[OF assms(2)]] assms(3) by auto
    with C have "r``{c}=C" using EquivClass_1_L2[OF Group_ZF_2_4_L3] assms(2,3) by auto
    with c C have "\<langle>c,C\<rangle>\<in>{\<langle>g,r``{g}\<rangle>. g\<in>G}" using EquivClass_1_L1[OF Group_ZF_2_4_L3] assms(2,3)
      by auto
    then have "{\<langle>g,r``{g}\<rangle>. g\<in>G}`c=C" "c\<in>G" using apply_equality fun by auto
    then have "\<exists>c\<in>G. {\<langle>g,r``{g}\<rangle>. g\<in>G}`c=C" by auto
  }
  with fun have surj:"{\<langle>g,r``{g}\<rangle>. g\<in>G}\<in>surj(G,G//r)" unfolding surj_def by auto moreover
  from assms(1) obtain n where "n\<in>nat" "G\<approx>n" unfolding Finite_def by auto
  then have G:"G\<lesssim>n" "Ord(n)" using eqpoll_imp_lepoll by auto
  then have "G//r\<lesssim>G" using surj_fun_inv_2 surj by auto
  with G(1) have "G//r\<lesssim>n" using lepoll_trans by blast
  then show "Finite(G//r)" using lepoll_nat_imp_Finite \<open>n\<in>nat\<close> by auto
qed

text\<open>All the cosets are equipollent.\<close>

lemma(in group0) cosets_equipoll:
  assumes "IsAsubgroup(H,P)" "r=QuotientGroupRel(G,P,H)" "g1\<in>G""g2\<in>G"
  shows "r``{g1}\<approx>r``{g2}"
proof-
  from assms(3,4) have GG:"(g1\<inverse>)\<cdot>g2\<in>G" using inverse_in_group group_op_closed by auto
  then have "RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)\<in>bij(G,G)" using trans_bij(1) by auto moreover
  have sub2:"r``{g2}\<subseteq>G" using EquivClass_1_L1[OF Group_ZF_2_4_L3[OF assms(1)]] assms(2,4) unfolding quotient_def by auto
  have sub:"r``{g1}\<subseteq>G" using EquivClass_1_L1[OF Group_ZF_2_4_L3[OF assms(1)]] assms(2,3) unfolding quotient_def by auto
  ultimately have "restrict(RightTranslation(G,P,(g1\<inverse>)\<cdot>g2),r``{g1})\<in>bij(r``{g1},RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)``(r``{g1}))"
    using restrict_bij unfolding bij_def by auto
  then have "r``{g1}\<approx>RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)``(r``{g1})" unfolding eqpoll_def by auto
  then have A0:"r``{g1}\<approx>{RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)`t. t\<in>r``{g1}}"
    using func_imagedef[OF group0_5_L1(1)[OF GG] sub] by auto
  {
    fix t assume "t\<in>{RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)`t. t\<in>r``{g1}}"
    then obtain q where q:"t=RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)`q" "q\<in>r``{g1}" by auto
    then have "\<langle>g1,q\<rangle>\<in>r" "q\<in>G" using image_iff sub by auto
    then have "g1\<cdot>(q\<inverse>)\<in>H" "q\<inverse>\<in>G" using assms(2) inverse_in_group unfolding QuotientGroupRel_def by auto
    from q(1) have t:"t=q\<cdot>((g1\<inverse>)\<cdot>g2)" using group0_5_L2(1)[OF GG] q(2) sub by auto
    then have "g2\<cdot>t\<inverse>=g2\<cdot>(q\<cdot>((g1\<inverse>)\<cdot>g2))\<inverse>" by auto
    then have "g2\<cdot>t\<inverse>=g2\<cdot>(((g1\<inverse>)\<cdot>g2)\<inverse>\<cdot>q\<inverse>)" using group_inv_of_two[OF \<open>q\<in>G\<close> GG] by auto
    then have "g2\<cdot>t\<inverse>=g2\<cdot>(((g2\<inverse>)\<cdot>g1\<inverse>\<inverse>)\<cdot>q\<inverse>)" using group_inv_of_two[OF inverse_in_group[OF assms(3)] 
      assms(4)] by auto
    then have "g2\<cdot>t\<inverse>=g2\<cdot>(((g2\<inverse>)\<cdot>g1)\<cdot>q\<inverse>)" using group_inv_of_inv assms(3) by auto moreover
    have "t\<in>G" using t \<open>q\<in>G\<close> \<open>g2\<in>G\<close> inverse_in_group[OF assms(3)] group_op_closed by auto
    have "(g2\<inverse>)\<cdot>g1\<in>G" using assms(3) inverse_in_group[OF assms(4)] group_op_closed by auto
    with assms(4) \<open>q\<inverse>\<in>G\<close> have "g2\<cdot>(((g2\<inverse>)\<cdot>g1)\<cdot>q\<inverse>)=g2\<cdot>((g2\<inverse>)\<cdot>g1)\<cdot>q\<inverse>" using group_oper_assoc by auto
    moreover have "g2\<cdot>((g2\<inverse>)\<cdot>g1)=g2\<cdot>(g2\<inverse>)\<cdot>g1" using assms(3) inverse_in_group[OF assms(4)] assms(4)
      group_oper_assoc by auto
    then have "g2\<cdot>((g2\<inverse>)\<cdot>g1)=g1" using group0_2_L6[OF assms(4)] group0_2_L2 assms(3) by auto ultimately
    have "g2\<cdot>t\<inverse>=g1\<cdot>q\<inverse>" by auto
    with \<open>g1\<cdot>(q\<inverse>)\<in>H\<close> have "g2\<cdot>t\<inverse>\<in>H" by auto
    then have "\<langle>g2,t\<rangle>\<in>r" using assms(2) unfolding QuotientGroupRel_def using assms(4) \<open>t\<in>G\<close> by auto
    then have "t\<in>r``{g2}" using image_iff assms(4) by auto
  }
  then have A1:"{RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)`t. t\<in>r``{g1}}\<subseteq>r``{g2}" by auto
  {
    fix t assume "t\<in>r``{g2}"
    then have "\<langle>g2,t\<rangle>\<in>r" "t\<in>G" using sub2 image_iff by auto
    then have H:"g2\<cdot>t\<inverse>\<in>H" using assms(2) unfolding QuotientGroupRel_def by auto
    then have G:"g2\<cdot>t\<inverse>\<in>G" using group0_3_L2 assms(1) by auto
    then have "g1\<cdot>(g1\<inverse>\<cdot>(g2\<cdot>t\<inverse>))=g1\<cdot>g1\<inverse>\<cdot>(g2\<cdot>t\<inverse>)" using group_oper_assoc[OF assms(3) inverse_in_group[OF assms(3)]]
      by auto
    then have "g1\<cdot>(g1\<inverse>\<cdot>(g2\<cdot>t\<inverse>))=g2\<cdot>t\<inverse>" using group0_2_L6[OF assms(3)] group0_2_L2 G by auto
    with H have HH:"g1\<cdot>(g1\<inverse>\<cdot>(g2\<cdot>t\<inverse>))\<in>H" by auto
    have GGG:"t\<cdot>g2\<inverse>\<in>G" using \<open>t\<in>G\<close> inverse_in_group[OF assms(4)] group_op_closed by auto
    have "(t\<cdot>g2\<inverse>)\<inverse>=g2\<inverse>\<inverse>\<cdot>t\<inverse>" using group_inv_of_two[OF \<open>t\<in>G\<close> inverse_in_group[OF assms(4)]] by auto
    also have "\<dots>=g2\<cdot>t\<inverse>" using group_inv_of_inv[OF assms(4)] by auto
    ultimately have "(t\<cdot>g2\<inverse>)\<inverse>=g2\<cdot>t\<inverse>" by auto
    then have "g1\<inverse>\<cdot>(t\<cdot>g2\<inverse>)\<inverse>=g1\<inverse>\<cdot>(g2\<cdot>t\<inverse>)" by auto
    then have "((t\<cdot>g2\<inverse>)\<cdot>g1)\<inverse>=g1\<inverse>\<cdot>(g2\<cdot>t\<inverse>)" using group_inv_of_two[OF GGG assms(3)] by auto
    then have HHH:"g1\<cdot>((t\<cdot>g2\<inverse>)\<cdot>g1)\<inverse>\<in>H" using HH by auto
    have "(t\<cdot>g2\<inverse>)\<cdot>g1\<in>G" using assms(3) \<open>t\<in>G\<close> inverse_in_group[OF assms(4)] group_op_closed by auto
    with HHH have "\<langle>g1,(t\<cdot>g2\<inverse>)\<cdot>g1\<rangle>\<in>r" using assms(2,3) unfolding QuotientGroupRel_def by auto
    then have rg1:"t\<cdot>g2\<inverse>\<cdot>g1\<in>r``{g1}" using image_iff by auto
    have "t\<cdot>g2\<inverse>\<cdot>g1\<cdot>((g1\<inverse>)\<cdot>g2)=t\<cdot>(g2\<inverse>\<cdot>g1)\<cdot>((g1\<inverse>)\<cdot>g2)" using group_oper_assoc[OF \<open>t\<in>G\<close> inverse_in_group[OF assms(4)] assms(3)]
      by auto
    also have "\<dots>=t\<cdot>((g2\<inverse>\<cdot>g1)\<cdot>((g1\<inverse>)\<cdot>g2))" using group_oper_assoc[OF \<open>t\<in>G\<close> group_op_closed[OF inverse_in_group[OF assms(4)] assms(3)] GG]
      by auto
    also have "\<dots>=t\<cdot>(g2\<inverse>\<cdot>(g1\<cdot>((g1\<inverse>)\<cdot>g2)))" using group_oper_assoc[OF inverse_in_group[OF assms(4)] assms(3) GG] by auto
    also have "\<dots>=t\<cdot>(g2\<inverse>\<cdot>(g1\<cdot>(g1\<inverse>)\<cdot>g2))" using group_oper_assoc[OF assms(3) inverse_in_group[OF assms(3)] assms(4)] by auto
    also have "\<dots>=t" using group0_2_L6[OF assms(3)]group0_2_L6[OF assms(4)] group0_2_L2 \<open>t\<in>G\<close> assms(4) by auto
    ultimately have "t\<cdot>g2\<inverse>\<cdot>g1\<cdot>((g1\<inverse>)\<cdot>g2)=t" by auto
    then have "RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)`(t\<cdot>g2\<inverse>\<cdot>g1)=t" using group0_5_L2(1)[OF GG] \<open>(t\<cdot>g2\<inverse>)\<cdot>g1\<in>G\<close> by auto
    then have "t\<in>{RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)`t. t\<in>r``{g1}}" using rg1 by force
  }
  then have "r``{g2}\<subseteq>{RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)`t. t\<in>r``{g1}}" by blast
  with A1 have "r``{g2}={RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)`t. t\<in>r``{g1}}" by auto
  with A0 show ?thesis by auto
qed

text\<open>The order of a subgroup multiplied by the order of the space of cosets is the order of
the group. We only prove the theorem for finite groups.\<close>

theorem(in group0) Lagrange:
  assumes "Finite(G)" "IsAsubgroup(H,P)" "r=QuotientGroupRel(G,P,H)"
  shows "|G|=|H| #* |G//r|"
proof-
  have "Finite(G//r)" using assms finite_cosets by auto moreover
  have un:"\<Union>(G//r)=G" using Union_quotient Group_ZF_2_4_L3 assms(2,3) by auto
  then have "Finite(\<Union>(G//r))" using assms(1) by auto moreover
  have "\<forall>c1\<in>(G//r). \<forall>c2\<in>(G//r). c1\<noteq>c2 \<longrightarrow> c1\<inter>c2=0" using quotient_disj[OF Group_ZF_2_4_L3[OF assms(2)]]
    assms(3) by auto moreover
  have "\<forall>aa\<in>G. aa\<in>H \<longleftrightarrow> \<langle>aa,\<one>\<rangle>\<in>r" using Group_ZF_2_4_L5C assms(3) by auto
  then have "\<forall>aa\<in>G. aa\<in>H \<longleftrightarrow> \<langle>\<one>,aa\<rangle>\<in>r" using Group_ZF_2_4_L2 assms(2,3) unfolding sym_def
    by auto
  then have "\<forall>aa\<in>G. aa\<in>H \<longleftrightarrow> aa\<in>r``{\<one>}" using image_iff by auto
  then have H:"H=r``{\<one>}" using group0_3_L2[OF assms(2)] assms(3) unfolding QuotientGroupRel_def by auto
  {
    fix c assume "c\<in>(G//r)"
    then obtain g where "g\<in>G" "c=r``{g}" unfolding quotient_def by auto
    then have "c\<approx>r``{\<one>}" using cosets_equipoll[OF assms(2,3)] group0_2_L2 by auto
    then have "|c|=|H|" using H cardinal_cong by auto
  }
  then have "\<forall>c\<in>(G//r). |c|=|H|" by auto ultimately
  show ?thesis using card_partition un by auto
qed

subsection\<open>Subgroups generated by sets\<close>

text\<open>Given a subset of a group, we can ask ourselves which is the 
  smallest group that contains that set; if it even exists.\<close>

lemma(in group0) inter_subgroups:
  assumes "\<forall>H\<in>\<HH>. IsAsubgroup(H,P)" "\<HH>\<noteq>0"
  shows "IsAsubgroup(\<Inter>\<HH>,P)"
proof-
  from assms have "\<one>\<in>\<Inter>\<HH>" using group0_3_L5 by auto
  then have "\<Inter>\<HH>\<noteq>0" by auto moreover
  {
    fix A B assume "A\<in>\<Inter>\<HH>""B\<in>\<Inter>\<HH>"
    then have "\<forall>H\<in>\<HH>. A\<in>H\<and>B\<in>H" by auto
    then have "\<forall>H\<in>\<HH>. A\<cdot>B\<in>H" using assms(1) group0_3_L6 by auto
    then have "A\<cdot>B\<in>\<Inter>\<HH>" using assms(2) by auto
  }
  then have "(\<Inter>\<HH>){is closed under}P" using IsOpClosed_def by auto moreover
  {
    fix A assume "A\<in>\<Inter>\<HH>"
    then have "\<forall>H\<in>\<HH>. A\<in>H" by auto
    then have "\<forall>H\<in>\<HH>. A\<inverse>\<in>H" using assms(1) group0_3_T3A by auto
    then have "A\<inverse>\<in>\<Inter>\<HH>" using assms(2) by auto
  }
  then have "\<forall>A\<in>\<Inter>\<HH>. A\<inverse>\<in>\<Inter>\<HH>" by auto moreover
  have "\<Inter>\<HH>\<subseteq>G" using assms(1,2) group0_3_L2 by force
  ultimately show ?thesis using group0_3_T3 by auto
qed

text\<open>As the previous lemma states, the subgroup that contains a subset
can be defined as an intersection of subgroups.\<close>

definition(in group0)
  SubgroupGenerated ("\<langle>_\<rangle>\<^sub>G" 80)
  where "\<langle>X\<rangle>\<^sub>G \<equiv> \<Inter>{H\<in>Pow(G). X\<subseteq>H \<and> IsAsubgroup(H,P)}"

theorem(in group0) subgroupGen_is_subgroup:
  assumes "X\<subseteq>G"
  shows "IsAsubgroup(\<langle>X\<rangle>\<^sub>G,P)"
proof-
  have "restrict(P,G\<times>G)=P" using group_oper_assocA restrict_idem unfolding Pi_def by auto
  then have "IsAsubgroup(G,P)" unfolding IsAsubgroup_def using groupAssum by auto
  with assms have "G\<in>{H\<in>Pow(G). X\<subseteq>H \<and> IsAsubgroup(H,P)}" by auto
  then have "{H\<in>Pow(G). X\<subseteq>H \<and> IsAsubgroup(H,P)}\<noteq>0" by auto
  then show ?thesis using inter_subgroups unfolding SubgroupGenerated_def by auto
qed

subsection\<open>Homomorphisms\<close>

text\<open>A homomorphism is a function between groups that preserves
group operations.\<close>

definition
  Homomor ("_{is a homomorphism}{_,_}\<rightarrow>{_,_}" 85)
  where "IsAgroup(G,P) \<Longrightarrow> IsAgroup(H,F) \<Longrightarrow> Homomor(f,G,P,H,F) \<equiv> \<forall>g1\<in>G. \<forall>g2\<in>G. f`(P`\<langle>g1,g2\<rangle>)=F`\<langle>f`g1,f`g2\<rangle>"

text\<open>Now a lemma about the definition:\<close>

lemma homomor_eq:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)" "g1\<in>G" "g2\<in>G"
  shows "f`(P`\<langle>g1,g2\<rangle>)=F`\<langle>f`g1,f`g2\<rangle>"
  using assms Homomor_def by auto

text\<open>An endomorphism is a homomorphism from a group to the same group. In case
the group is abelian, it has a nice structure.\<close>

definition
  End
  where "End(G,P) \<equiv> {f:G\<rightarrow>G. Homomor(f,G,P,G,P)}"

text\<open>The set of endomorphisms forms a submonoid of the monoid of function
from a set to that set under composition.\<close>

lemma(in group0) end_composition:
  assumes "f1\<in>End(G,P)""f2\<in>End(G,P)"
  shows "Composition(G)`\<langle>f1,f2\<rangle>\<in>End(G,P)"
proof-
  from assms have fun:"f1:G\<rightarrow>G""f2:G\<rightarrow>G" unfolding End_def by auto
  then have fun2:"f1 O f2:G\<rightarrow>G" using comp_fun by auto
  have comp:"Composition(G)`\<langle>f1,f2\<rangle>=f1 O f2" using func_ZF_5_L2 fun by auto
  {
    fix g1 g2 assume AS2:"g1\<in>G""g2\<in>G"
    then have g1g2:"g1\<cdot>g2\<in>G" using group_op_closed by auto
    from fun2 have "(f1 O f2)`(g1\<cdot>g2)=f1`(f2`(g1\<cdot>g2))" using comp_fun_apply fun(2) g1g2 by auto
    also have "\<dots>=f1`((f2`g1)\<cdot>(f2`g2))" using assms(2) unfolding End_def Homomor_def[OF groupAssum groupAssum]
      using AS2 by auto moreover
    have "f2`g1\<in>G""f2`g2\<in>G" using fun(2) AS2 apply_type by auto ultimately
    have "(f1 O f2)`(g1\<cdot>g2)=(f1`(f2`g1))\<cdot>(f1`(f2`g2))" using assms(1) unfolding End_def Homomor_def[OF groupAssum groupAssum]
      using AS2 by auto
    then have "(f1 O f2)`(g1\<cdot>g2)=((f1 O f2)`g1)\<cdot>((f1 O f2)`g2)" using comp_fun_apply fun(2) AS2 by auto
  }
  then have "\<forall>g1\<in>G. \<forall>g2\<in>G. (f1 O f2)`(g1\<cdot>g2)=((f1 O f2)`g1)\<cdot>((f1 O f2)`g2)" by auto
  then have "(f1 O f2)\<in>End(G,P)" unfolding End_def Homomor_def[OF groupAssum groupAssum] using fun2 by auto
  with comp show "Composition(G)`\<langle>f1,f2\<rangle>\<in>End(G,P)" by auto
qed

theorem(in group0) end_comp_monoid:
  shows "IsAmonoid(End(G,P),restrict(Composition(G),End(G,P)\<times>End(G,P)))"
  and "TheNeutralElement(End(G,P),restrict(Composition(G),End(G,P)\<times>End(G,P)))=id(G)"
proof-
  have fun:"id(G):G\<rightarrow>G" unfolding id_def by auto
  {
    fix g h assume "g\<in>G""h\<in>G"
    then have id:"g\<cdot>h\<in>G""id(G)`g=g""id(G)`h=h" using group_op_closed by auto
    then have "id(G)`(g\<cdot>h)=g\<cdot>h" unfolding id_def by auto
    with id(2,3) have "id(G)`(g\<cdot>h)=(id(G)`g)\<cdot>(id(G)`h)" by auto
  }
  with fun have "id(G)\<in>End(G,P)" unfolding End_def Homomor_def[OF groupAssum groupAssum] by auto moreover
  from Group_ZF_2_5_L2(2) have A0:"id(G)=TheNeutralElement(G \<rightarrow> G, Composition(G))" by auto ultimately
  have A1:"TheNeutralElement(G \<rightarrow> G, Composition(G))\<in>End(G,P)" by auto moreover
  have A2:"End(G,P)\<subseteq>G\<rightarrow>G" unfolding End_def by auto moreover
  from end_composition have A3:"End(G,P){is closed under}Composition(G)" unfolding IsOpClosed_def by auto
  ultimately show "IsAmonoid(End(G,P),restrict(Composition(G),End(G,P)\<times>End(G,P)))" 
    using monoid0.group0_1_T1 unfolding monoid0_def using Group_ZF_2_5_L2(1)
    by force
  have "IsAmonoid(G\<rightarrow>G,Composition(G))" using Group_ZF_2_5_L2(1) by auto
  with A0 A1 A2 A3 show "TheNeutralElement(End(G,P),restrict(Composition(G),End(G,P)\<times>End(G,P)))=id(G)"
    using group0_1_L6 by auto
qed

text\<open>The set of endomorphisms is closed under pointwise addition. This is so because the
group is abelian.\<close>
  
theorem(in group0) end_pointwise_addition:
  assumes "f\<in>End(G,P)""g\<in>End(G,P)""P{is commutative on}G""F = P {lifted to function space over} G"
  shows "F`\<langle>f,g\<rangle>\<in>End(G,P)"
proof-
  from assms(1,2) have fun:"f\<in>G\<rightarrow>G""g\<in>G\<rightarrow>G" unfolding End_def by auto
  then have fun2:"F`\<langle>f,g\<rangle>:G\<rightarrow>G" using monoid0.Group_ZF_2_1_L0 group0_2_L1 assms(4) by auto
  {
    fix g1 g2 assume AS:"g1\<in>G""g2\<in>G"
    then have "g1\<cdot>g2\<in>G" using group_op_closed by auto
    then have "(F`\<langle>f,g\<rangle>)`(g1\<cdot>g2)=(f`(g1\<cdot>g2))\<cdot>(g`(g1\<cdot>g2))" using Group_ZF_2_1_L3 fun assms(4) by auto
    also have "\<dots>=(f`(g1)\<cdot>f`(g2))\<cdot>(g`(g1)\<cdot>g`(g2))" using assms unfolding End_def Homomor_def[OF groupAssum groupAssum]
      using AS by auto ultimately
    have "(F`\<langle>f,g\<rangle>)`(g1\<cdot>g2)=(f`(g1)\<cdot>f`(g2))\<cdot>(g`(g1)\<cdot>g`(g2))" by auto moreover
    have "f`g1\<in>G""f`g2\<in>G""g`g1\<in>G""g`g2\<in>G" using fun apply_type AS by auto ultimately
    have "(F`\<langle>f,g\<rangle>)`(g1\<cdot>g2)=(f`(g1)\<cdot>g`(g1))\<cdot>(f`(g2)\<cdot>g`(g2))" using group0_4_L8(3) assms(3)
      by auto
    with AS have "(F`\<langle>f,g\<rangle>)`(g1\<cdot>g2)=((F`\<langle>f,g\<rangle>)`g1)\<cdot>((F`\<langle>f,g\<rangle>)`g2)"
      using Group_ZF_2_1_L3 fun assms(4) by auto
  }
  with fun2 show ?thesis unfolding End_def Homomor_def[OF groupAssum groupAssum] by auto
qed

text\<open>The inverse of an abelian group is an endomorphism.\<close>

lemma(in group0) end_inverse_group:
  assumes "P{is commutative on}G"
  shows "GroupInv(G,P)\<in>End(G,P)"
proof-
  {
    fix s t assume AS:"s\<in>G""t\<in>G"
    then have elinv:"s\<inverse>\<in>G""t\<inverse>\<in>G" using inverse_in_group by auto
    have "(s\<cdot>t)\<inverse>=t\<inverse>\<cdot>s\<inverse>" using group_inv_of_two AS by auto
    then have "(s\<cdot>t)\<inverse>=s\<inverse>\<cdot>t\<inverse>" using assms(1) elinv unfolding IsCommutative_def by auto
  }
  then have "\<forall>s\<in>G. \<forall>t\<in>G. GroupInv(G,P)`(s\<cdot>t)=GroupInv(G,P)`(s)\<cdot>GroupInv(G,P)`(t)" by auto
  with group0_2_T2 groupAssum show ?thesis unfolding End_def using Homomor_def by auto
qed

text\<open>The set of homomorphisms of an abelian group is an abelian subgroup of
the group of functions from a set to a group, under pointwise multiplication.\<close>

theorem(in group0) end_addition_group:
  assumes "P{is commutative on}G" "F = P {lifted to function space over} G"
  shows "IsAgroup(End(G,P),restrict(F,End(G,P)\<times>End(G,P)))" "restrict(F,End(G,P)\<times>End(G,P)){is commutative on}End(G,P)"
proof-
  from end_comp_monoid(1) monoid0.group0_1_L3A have "End(G,P)\<noteq>0" unfolding monoid0_def by auto
  moreover have "End(G,P)\<subseteq>G\<rightarrow>G" unfolding End_def by auto moreover
  have "End(G,P){is closed under}F" unfolding IsOpClosed_def using end_pointwise_addition
    assms(1,2) by auto moreover
  {
    fix ff assume AS:"ff\<in>End(G,P)"
    then have "restrict(Composition(G),End(G,P)\<times>End(G,P))`\<langle>GroupInv(G,P), ff\<rangle>\<in>End(G,P)" using monoid0.group0_1_L1
      unfolding monoid0_def using end_composition(1) end_inverse_group[OF assms(1)]
      by force
    then have "Composition(G)`\<langle>GroupInv(G,P), ff\<rangle>\<in>End(G,P)" using AS end_inverse_group[OF assms(1)]
      by auto
    then have "GroupInv(G,P) O ff\<in>End(G,P)" using func_ZF_5_L2 AS group0_2_T2 groupAssum unfolding
      End_def by auto
    then have "GroupInv(G\<rightarrow>G,F)`ff\<in>End(G,P)" using Group_ZF_2_1_L6 assms(2) AS unfolding End_def
      by auto
  }
  then have "\<forall>ff\<in>End(G,P). GroupInv(G\<rightarrow>G,F)`ff\<in>End(G,P)" by auto ultimately
  show "IsAgroup(End(G,P),restrict(F,End(G,P)\<times>End(G,P)))" using group0.group0_3_T3 Group_ZF_2_1_T2[OF assms(2)] unfolding IsAsubgroup_def group0_def
    by auto
  show "restrict(F,End(G,P)\<times>End(G,P)){is commutative on}End(G,P)" using Group_ZF_2_1_L7[OF assms(2,1)] unfolding End_def IsCommutative_def by auto
qed

lemma(in group0) distributive_comp_pointwise:
  assumes "P{is commutative on}G" "F = P {lifted to function space over} G"
  shows "IsDistributive(End(G,P),restrict(F,End(G,P)\<times>End(G,P)),restrict(Composition(G),End(G,P)\<times>End(G,P)))"
proof-
  {
    fix b c d assume AS:"b\<in>End(G,P)""c\<in>End(G,P)""d\<in>End(G,P)"
    have ig1:"Composition(G) `\<langle>b, F ` \<langle>c, d\<rangle>\<rangle> =b O (F`\<langle>c,d\<rangle>)" using monoid0.Group_ZF_2_1_L0[OF group0_2_L1 assms(2)]
      AS unfolding End_def using func_ZF_5_L2 by auto
    have ig2:"F `\<langle>Composition(G) `\<langle>b , c\<rangle>,Composition(G) `\<langle>b , d\<rangle>\<rangle>=F `\<langle>b O c,b O d\<rangle>" using AS unfolding End_def using func_ZF_5_L2 by auto
    have comp1fun:"(b O (F`\<langle>c,d\<rangle>)):G\<rightarrow>G" using monoid0.Group_ZF_2_1_L0[OF group0_2_L1 assms(2)] comp_fun AS unfolding End_def by force
    have comp2fun:"(F `\<langle>b O c,b O d\<rangle>):G\<rightarrow>G" using monoid0.Group_ZF_2_1_L0[OF group0_2_L1 assms(2)] comp_fun AS unfolding End_def by force
    {
      fix g assume gG:"g\<in>G"
      then have "(b O (F`\<langle>c,d\<rangle>))`g=b`((F`\<langle>c,d\<rangle>)`g)" using comp_fun_apply monoid0.Group_ZF_2_1_L0[OF group0_2_L1 assms(2)]
        AS(2,3) unfolding End_def by force
      also have "\<dots>=b`(c`(g)\<cdot>d`(g))" using Group_ZF_2_1_L3[OF assms(2)] AS(2,3) gG unfolding End_def by auto
      ultimately have "(b O (F`\<langle>c,d\<rangle>))`g=b`(c`(g)\<cdot>d`(g))" by auto moreover
      have "c`g\<in>G""d`g\<in>G" using AS(2,3) unfolding End_def using apply_type gG by auto
      ultimately have "(b O (F`\<langle>c,d\<rangle>))`g=(b`(c`g))\<cdot>(b`(d`g))" using AS(1) unfolding End_def
        Homomor_def[OF groupAssum groupAssum] by auto
      then have "(b O (F`\<langle>c,d\<rangle>))`g=((b O c)`g)\<cdot>((b O d)`g)" using comp_fun_apply gG AS(2,3)
        unfolding End_def by auto
      then have "(b O (F`\<langle>c,d\<rangle>))`g=(F`\<langle>b O c,b O d\<rangle>)`g" using gG Group_ZF_2_1_L3[OF assms(2) comp_fun comp_fun gG]
        AS unfolding End_def by auto
    }
    then have "\<forall>g\<in>G. (b O (F`\<langle>c,d\<rangle>))`g=(F`\<langle>b O c,b O d\<rangle>)`g" by auto
    then have "b O (F`\<langle>c,d\<rangle>)=F`\<langle>b O c,b O d\<rangle>" using fun_extension[OF comp1fun comp2fun] by auto
    with ig1 ig2 have "Composition(G) `\<langle>b, F ` \<langle>c, d\<rangle>\<rangle> =F `\<langle>Composition(G) `\<langle>b , c\<rangle>,Composition(G) `\<langle>b , d\<rangle>\<rangle>" by auto moreover
    have "F ` \<langle>c, d\<rangle>=restrict(F,End(G,P)\<times>End(G,P)) ` \<langle>c, d\<rangle>" using AS(2,3) restrict by auto moreover
    have "Composition(G) `\<langle>b , c\<rangle>=restrict(Composition(G),End(G,P)\<times>End(G,P)) `\<langle>b , c\<rangle>" "Composition(G) `\<langle>b , d\<rangle>=restrict(Composition(G),End(G,P)\<times>End(G,P)) `\<langle>b , d\<rangle>"
      using restrict AS by auto moreover
    have "Composition(G) `\<langle>b, F ` \<langle>c, d\<rangle>\<rangle> =restrict(Composition(G),End(G,P)\<times>End(G,P)) `\<langle>b, F ` \<langle>c, d\<rangle>\<rangle>" using AS(1)
      end_pointwise_addition[OF AS(2,3) assms] by auto
    moreover have "F `\<langle>Composition(G) `\<langle>b , c\<rangle>,Composition(G) `\<langle>b , d\<rangle>\<rangle>=restrict(F,End(G,P)\<times>End(G,P)) `\<langle>Composition(G) `\<langle>b , c\<rangle>,Composition(G) `\<langle>b , d\<rangle>\<rangle>"
      using end_composition[OF AS(1,2)] end_composition[OF AS(1,3)] by auto ultimately
    have eq1:"restrict(Composition(G),End(G,P)\<times>End(G,P)) `\<langle>b, restrict(F,End(G,P)\<times>End(G,P)) ` \<langle>c, d\<rangle>\<rangle> =restrict(F,End(G,P)\<times>End(G,P)) `\<langle>restrict(Composition(G),End(G,P)\<times>End(G,P)) `\<langle>b , c\<rangle>,restrict(Composition(G),End(G,P)\<times>End(G,P))`\<langle>b , d\<rangle>\<rangle>"
      by auto
    have ig1:"Composition(G) `\<langle> F ` \<langle>c, d\<rangle>,b\<rangle> = (F`\<langle>c,d\<rangle>) O b" using monoid0.Group_ZF_2_1_L0[OF group0_2_L1 assms(2)]
      AS unfolding End_def using func_ZF_5_L2 by auto
    have ig2:"F `\<langle>Composition(G) `\<langle>c , b\<rangle>,Composition(G) `\<langle>d , b\<rangle>\<rangle>=F `\<langle>c O b,d O b\<rangle>" using AS unfolding End_def using func_ZF_5_L2 by auto
    have comp1fun:"((F`\<langle>c,d\<rangle>) O b):G\<rightarrow>G" using monoid0.Group_ZF_2_1_L0[OF group0_2_L1 assms(2)] comp_fun AS unfolding End_def by force
    have comp2fun:"(F `\<langle>c O b,d O b\<rangle>):G\<rightarrow>G" using monoid0.Group_ZF_2_1_L0[OF group0_2_L1 assms(2)] comp_fun AS unfolding End_def by force
    {
      fix g assume gG:"g\<in>G"
      then have bg:"b`g\<in>G" using AS(1) unfolding End_def using apply_type by auto
      from gG have "((F`\<langle>c,d\<rangle>) O b)`g=(F`\<langle>c,d\<rangle>)`(b`g)" using comp_fun_apply AS(1) unfolding End_def by force
      also have "\<dots>=(c`(b`g))\<cdot>(d`(b`g))" using Group_ZF_2_1_L3[OF assms(2)] AS(2,3) bg unfolding End_def by auto
      also  have "\<dots>=((c O b)`g)\<cdot>((d O b)`g)" using comp_fun_apply gG AS unfolding End_def by auto
      also have "\<dots>=(F`\<langle>c O b,d O b\<rangle>)`g" using gG Group_ZF_2_1_L3[OF assms(2) comp_fun comp_fun gG]
        AS unfolding End_def by auto
      ultimately have"((F`\<langle>c,d\<rangle>) O b)`g=(F`\<langle>c O b,d O b\<rangle>)`g" by auto
    }
    then have "\<forall>g\<in>G. ((F`\<langle>c,d\<rangle>) O b)`g=(F`\<langle>c O b,d O b\<rangle>)`g" by auto
    then have "(F`\<langle>c,d\<rangle>) O b=F`\<langle>c O b,d O b\<rangle>" using fun_extension[OF comp1fun comp2fun] by auto
    with ig1 ig2 have "Composition(G) `\<langle>F ` \<langle>c, d\<rangle>,b\<rangle> =F `\<langle>Composition(G) `\<langle>c , b\<rangle>,Composition(G) `\<langle>d , b\<rangle>\<rangle>" by auto moreover
    have "F ` \<langle>c, d\<rangle>=restrict(F,End(G,P)\<times>End(G,P)) ` \<langle>c, d\<rangle>" using AS(2,3) restrict by auto moreover
    have "Composition(G) `\<langle>c , b\<rangle>=restrict(Composition(G),End(G,P)\<times>End(G,P)) `\<langle>c , b\<rangle>" "Composition(G) `\<langle>d , b\<rangle>=restrict(Composition(G),End(G,P)\<times>End(G,P)) `\<langle>d , b\<rangle>"
      using restrict AS by auto moreover
    have "Composition(G) `\<langle>F ` \<langle>c, d\<rangle>,b\<rangle> =restrict(Composition(G),End(G,P)\<times>End(G,P)) `\<langle>F ` \<langle>c, d\<rangle>,b\<rangle>" using AS(1)
      end_pointwise_addition[OF AS(2,3) assms] by auto
    moreover have "F `\<langle>Composition(G) `\<langle>c , b\<rangle>,Composition(G) `\<langle>d , b\<rangle>\<rangle>=restrict(F,End(G,P)\<times>End(G,P)) `\<langle>Composition(G) `\<langle>c , b\<rangle>,Composition(G) `\<langle>d , b\<rangle>\<rangle>"
      using end_composition[OF AS(2,1)] end_composition[OF AS(3,1)] by auto ultimately
    have eq2:"restrict(Composition(G),End(G,P)\<times>End(G,P)) `\<langle> restrict(F,End(G,P)\<times>End(G,P)) ` \<langle>c, d\<rangle>,b\<rangle> =restrict(F,End(G,P)\<times>End(G,P)) `\<langle>restrict(Composition(G),End(G,P)\<times>End(G,P)) `\<langle>c ,b\<rangle>,restrict(Composition(G),End(G,P)\<times>End(G,P))`\<langle>d , b\<rangle>\<rangle>"
      by auto
    with eq1 have "(restrict(Composition(G),End(G,P)\<times>End(G,P)) `\<langle>b, restrict(F,End(G,P)\<times>End(G,P)) ` \<langle>c, d\<rangle>\<rangle> =restrict(F,End(G,P)\<times>End(G,P)) `\<langle>restrict(Composition(G),End(G,P)\<times>End(G,P)) `\<langle>b , c\<rangle>,restrict(Composition(G),End(G,P)\<times>End(G,P))`\<langle>b , d\<rangle>\<rangle>)\<and>
      (restrict(Composition(G),End(G,P)\<times>End(G,P)) `\<langle> restrict(F,End(G,P)\<times>End(G,P)) ` \<langle>c, d\<rangle>,b\<rangle> =restrict(F,End(G,P)\<times>End(G,P)) `\<langle>restrict(Composition(G),End(G,P)\<times>End(G,P)) `\<langle>c ,b\<rangle>,restrict(Composition(G),End(G,P)\<times>End(G,P))`\<langle>d , b\<rangle>\<rangle>)"
      by auto
  }
  then show ?thesis unfolding IsDistributive_def by auto
qed

text\<open>The endomorphisms of an abelian group is in fact a ring with the previous
  operations.\<close>

theorem(in group0) end_is_ring:
  assumes "P{is commutative on}G" "F = P {lifted to function space over} G"
  shows "IsAring(End(G,P),restrict(F,End(G,P)\<times>End(G,P)),restrict(Composition(G),End(G,P)\<times>End(G,P)))"
  unfolding IsAring_def using end_addition_group[OF assms] end_comp_monoid(1) distributive_comp_pointwise[OF assms]
  by auto

subsection\<open>First isomorphism theorem\<close>

text\<open>Now we will prove that any homomorphism $f:G\to H$ defines a bijective
homomorphism between $G/H$ and $f(G)$.\<close>
  
text\<open>A group homomorphism sends the neutral element to the neutral element
and commutes with the inverse.\<close>

lemma image_neutral:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)" "f:G\<rightarrow>H"
  shows "f`TheNeutralElement(G,P)=TheNeutralElement(H,F)"
proof-
  have g:"TheNeutralElement(G,P)=P`\<langle>TheNeutralElement(G,P),TheNeutralElement(G,P)\<rangle>" "TheNeutralElement(G,P)\<in>G"
    using assms(1) group0.group0_2_L2 unfolding group0_def by auto
  from g(1) have "f`TheNeutralElement(G,P)=f`(P`\<langle>TheNeutralElement(G,P),TheNeutralElement(G,P)\<rangle>)" by auto
  also have "\<dots>=F`\<langle>f`TheNeutralElement(G,P),f`TheNeutralElement(G,P)\<rangle>"
    using assms(3) unfolding Homomor_def[OF assms(1,2)] using g(2) by auto
  ultimately have "f`TheNeutralElement(G,P)=F`\<langle>f`TheNeutralElement(G,P),f`TheNeutralElement(G,P)\<rangle>" by auto moreover
  have h:"f`TheNeutralElement(G,P)\<in>H" using g(2) apply_type[OF assms(4)] by auto
  then have "f`TheNeutralElement(G,P)=F`\<langle>f`TheNeutralElement(G,P),TheNeutralElement(H,F)\<rangle>"
    using assms(2) group0.group0_2_L2 unfolding group0_def by auto ultimately
  have "F`\<langle>f`TheNeutralElement(G,P),TheNeutralElement(H,F)\<rangle>=F`\<langle>f`TheNeutralElement(G,P),f`TheNeutralElement(G,P)\<rangle>" by auto
  with h have "LeftTranslation(H,F,f`TheNeutralElement(G,P))`TheNeutralElement(H,F)=LeftTranslation(H,F,f`TheNeutralElement(G,P))`(f`TheNeutralElement(G,P))"
    using group0.group0_5_L2(2)[OF _ h] assms(2) group0.group0_2_L2 unfolding group0_def by auto
  moreover have "LeftTranslation(H,F,f`TheNeutralElement(G,P))\<in>bij(H,H)" using group0.trans_bij(2)
    assms(2) h unfolding group0_def by auto
  then have "LeftTranslation(H,F,f`TheNeutralElement(G,P))\<in>inj(H,H)" unfolding bij_def by auto ultimately
  show "f`TheNeutralElement(G,P)=TheNeutralElement(H,F)" using h assms(2) group0.group0_2_L2 unfolding inj_def group0_def
    by force
qed

lemma image_inv:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)" "f:G\<rightarrow>H" "g\<in>G"
  shows "f`( GroupInv(G,P)`g)=GroupInv(H,F)` (f`g)"
proof-
  have im:"f`g\<in>H" using apply_type[OF assms(4,5)].
  have inv:"GroupInv(G,P)`g\<in>G" using group0.inverse_in_group[OF _ assms(5)] assms(1) unfolding group0_def by auto
  then have inv2:"f`(GroupInv(G,P)`g)\<in>H"using apply_type[OF assms(4)] by auto
  have "f`TheNeutralElement(G,P)=f`(P`\<langle>g,GroupInv(G,P)`g\<rangle>)" using assms(1,5) group0.group0_2_L6
    unfolding group0_def by auto
  also have "\<dots>=F`\<langle>f`g,f`(GroupInv(G,P)`g)\<rangle>" using assms(3) unfolding Homomor_def[OF assms(1,2)] using
    assms(5) inv by auto
  ultimately have "TheNeutralElement(H,F)=F`\<langle>f`g,f`(GroupInv(G,P)`g)\<rangle>" using image_neutral[OF assms(1-4)]
    by auto
  then show ?thesis using group0.group0_2_L9(2)[OF _ im inv2] assms(2) unfolding group0_def by auto
qed

text\<open>The kernel of an homomorphism is a normal subgroup.\<close>

theorem kerner_normal_sub:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)" "f:G\<rightarrow>H"
  shows "IsAnormalSubgroup(G,P,f-``{TheNeutralElement(H,F)})"
proof-
  have xy:"\<forall>x y. \<langle>x, y\<rangle> \<in> f \<longrightarrow> (\<forall>y'. \<langle>x, y'\<rangle> \<in> f \<longrightarrow> y = y')" using assms(4) unfolding Pi_def function_def
    by force 
  {
    fix g1 g2 assume "g1\<in>f-``{TheNeutralElement(H,F)}""g2\<in>f-``{TheNeutralElement(H,F)}"
    then have "\<langle>g1,TheNeutralElement(H,F)\<rangle>\<in>f""\<langle>g2,TheNeutralElement(H,F)\<rangle>\<in>f"
      using vimage_iff by auto moreover
    then have G:"g1\<in>G""g2\<in>G" using assms(4) unfolding Pi_def by auto
    then have "\<langle>g1,f`g1\<rangle>\<in>f""\<langle>g2,f`g2\<rangle>\<in>f" using apply_Pair[OF assms(4)] by auto moreover
    note xy ultimately
    have "f`g1=TheNeutralElement(H,F)""f`g2=TheNeutralElement(H,F)" by auto moreover
    have "f`(P`\<langle>g1,g2\<rangle>)=F`\<langle>f`g1,f`g2\<rangle>" using assms(3) G unfolding Homomor_def[OF assms(1,2)] by auto
    ultimately have "f`(P`\<langle>g1,g2\<rangle>)=F`\<langle>TheNeutralElement(H,F),TheNeutralElement(H,F)\<rangle>" by auto
    also have "\<dots>=TheNeutralElement(H,F)" using group0.group0_2_L2 assms(2) unfolding group0_def
      by auto
    ultimately have "f`(P`\<langle>g1,g2\<rangle>)=TheNeutralElement(H,F)" by auto moreover
    from G have "P`\<langle>g1,g2\<rangle>\<in>G" using group0.group_op_closed assms(1) unfolding group0_def by auto
    ultimately have "\<langle>P`\<langle>g1,g2\<rangle>,TheNeutralElement(H,F)\<rangle>\<in>f" using apply_Pair[OF assms(4)] by force
    then have "P`\<langle>g1,g2\<rangle>\<in>f-``{TheNeutralElement(H,F)}" using vimage_iff by auto
  }
  then have "f-``{TheNeutralElement(H,F)} {is closed under}P" unfolding IsOpClosed_def by auto
  moreover have A:"f-``{TheNeutralElement(H,F)} \<subseteq> G" using func1_1_L3 assms(4) by auto
  moreover have "f`TheNeutralElement(G,P)=TheNeutralElement(H,F)" using image_neutral
    assms by auto
  then have "\<langle>TheNeutralElement(G,P),TheNeutralElement(H,F)\<rangle>\<in>f" using apply_Pair[OF assms(4)]
    group0.group0_2_L2 assms(1) unfolding group0_def by force
  then have "TheNeutralElement(G,P)\<in>f-``{TheNeutralElement(H,F)}" using vimage_iff by auto
  then have "f-``{TheNeutralElement(H,F)}\<noteq>0" by auto moreover
  {
    fix x assume "x\<in>f-``{TheNeutralElement(H,F)}"
    then have "\<langle>x,TheNeutralElement(H,F)\<rangle>\<in>f" and x:"x\<in>G" using vimage_iff A by auto moreover
    from x have "\<langle>x,f`x\<rangle>\<in>f" using apply_Pair[OF assms(4)] by auto ultimately
    have "f`x=TheNeutralElement(H,F)" using xy by auto moreover
    have "f`(GroupInv(G,P)`x)=GroupInv(H,F)`(f`x)" using x image_inv assms by auto
    ultimately have "f`(GroupInv(G,P)`x)=GroupInv(H,F)`TheNeutralElement(H,F)" by auto
    then have "f`(GroupInv(G,P)`x)=TheNeutralElement(H,F)" using group0.group_inv_of_one
      assms(2) unfolding group0_def by auto moreover
    have "\<langle>GroupInv(G,P)`x,f`(GroupInv(G,P)`x)\<rangle>\<in>f" using apply_Pair[OF assms(4)]
      x group0.inverse_in_group assms(1) unfolding group0_def by auto
    ultimately have "\<langle>GroupInv(G,P)`x,TheNeutralElement(H,F)\<rangle>\<in>f" by auto
    then have "GroupInv(G,P)`x\<in>f-``{TheNeutralElement(H,F)}" using vimage_iff by auto
  }
  then have "\<forall>x\<in>f-``{TheNeutralElement(H,F)}. GroupInv(G,P)`x\<in>f-``{TheNeutralElement(H,F)}" by auto
  ultimately have SS:"IsAsubgroup(f-``{TheNeutralElement(H,F)},P)" using group0.group0_3_T3
    assms(1) unfolding group0_def by auto
  {
    fix g h assume AS:"g\<in>G""h\<in>f-``{TheNeutralElement(H,F)}"
    from AS(1) have im:"f`g\<in>H" using assms(4) apply_type by auto
    then have iminv:"GroupInv(H,F)`(f`g)\<in>H" using assms(2) group0.inverse_in_group unfolding group0_def by auto
    from AS have "h\<in>G" and inv:"GroupInv(G,P)`g\<in>G" using A group0.inverse_in_group assms(1) unfolding group0_def by auto
    then have P:"P`\<langle>h,GroupInv(G,P)`g\<rangle>\<in>G" using assms(1) group0.group_op_closed unfolding group0_def by auto
    with \<open>g\<in>G\<close> have "P`\<langle>g,P`\<langle>h,GroupInv(G,P)`g\<rangle> \<rangle>\<in>G" using assms(1) group0.group_op_closed unfolding group0_def by auto
    then have "f`(P`\<langle>g,P`\<langle>h,GroupInv(G,P)`g\<rangle> \<rangle>)=F`\<langle>f`g,f`(P`\<langle>h,GroupInv(G,P)`g\<rangle>)\<rangle>"
      using assms(3) unfolding Homomor_def[OF assms(1,2)] using \<open>g\<in>G\<close> P by auto
    also have "\<dots>=F`\<langle>f`g,F`(\<langle>f`h,f`(GroupInv(G,P)`g)\<rangle>)\<rangle>" using assms(3) unfolding Homomor_def[OF assms(1,2)]
      using \<open>h\<in>G\<close> inv by auto
    also have "\<dots>=F`\<langle>f`g,F`(\<langle>f`h,GroupInv(H,F)`(f`g)\<rangle>)\<rangle>" using image_inv[OF assms \<open>g\<in>G\<close>] by auto
    ultimately have "f`(P`\<langle>g,P`\<langle>h,GroupInv(G,P)`g\<rangle> \<rangle>)=F`\<langle>f`g,F`(\<langle>f`h,GroupInv(H,F)`(f`g)\<rangle>)\<rangle>" by auto
    moreover from AS(2) have "f`h=TheNeutralElement(H,F)" using func1_1_L15[OF assms(4)]
      by auto ultimately
    have "f`(P`\<langle>g,P`\<langle>h,GroupInv(G,P)`g\<rangle> \<rangle>)=F`\<langle>f`g,F`(\<langle>TheNeutralElement(H,F),GroupInv(H,F)`(f`g)\<rangle>)\<rangle>" by auto
    also have "\<dots>=F`\<langle>f`g,GroupInv(H,F)`(f`g)\<rangle>" using assms(2) im group0.group0_2_L2 unfolding group0_def
      using iminv by auto
    also have "\<dots>=TheNeutralElement(H,F)" using assms(2) group0.group0_2_L6 im
      unfolding group0_def by auto
    ultimately have "f`(P`\<langle>g,P`\<langle>h,GroupInv(G,P)`g\<rangle> \<rangle>)=TheNeutralElement(H,F)" by auto moreover
    from P \<open>g\<in>G\<close> have "P`\<langle>g,P`\<langle>h,GroupInv(G,P)`g\<rangle>\<rangle>\<in>G" using group0.group_op_closed assms(1) unfolding group0_def by auto
    ultimately have "P`\<langle>g,P`\<langle>h,GroupInv(G,P)`g\<rangle> \<rangle>\<in>f-``{TheNeutralElement(H,F)}" using func1_1_L15[OF assms(4)]
      by auto
  }
  then have "\<forall>g\<in>G. {P`\<langle>g,P`\<langle>h,GroupInv(G,P)`g\<rangle> \<rangle>. h\<in>f-``{TheNeutralElement(H,F)}}\<subseteq>f-``{TheNeutralElement(H,F)}"
    by auto
  then show ?thesis using group0.cont_conj_is_normal assms(1) SS unfolding group0_def by auto
qed

text\<open>The image of a homomorphism is a subgroup.\<close>

theorem image_sub:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)" "f:G\<rightarrow>H"
  shows "IsAsubgroup(f``G,F)"
proof-
  have "TheNeutralElement(G,P)\<in>G" using group0.group0_2_L2 assms(1) unfolding group0_def by auto
  then have "TheNeutralElement(H,F)\<in>f``G" using func_imagedef[OF assms(4),of "G"] image_neutral[OF assms]
    by force
  then have "f``G\<noteq>0" by auto moreover
  {
    fix h1 h2 assume "h1\<in>f``G""h2\<in>f``G"
    then obtain g1 g2 where "h1=f`g1" "h2=f`g2" and p:"g1\<in>G""g2\<in>G" using func_imagedef[OF assms(4)] by auto
    then have "F`\<langle>h1,h2\<rangle>=F`\<langle>f`g1,f`g2\<rangle>" by auto
    also have "\<dots>=f`(P`\<langle>g1,g2\<rangle>)" using assms(3) unfolding Homomor_def[OF assms(1,2)] using p by auto
    ultimately have "F`\<langle>h1,h2\<rangle>=f`(P`\<langle>g1,g2\<rangle>)" by auto
    moreover have "P`\<langle>g1,g2\<rangle>\<in>G" using p group0.group_op_closed assms(1) unfolding group0_def
      by auto ultimately
    have "F`\<langle>h1,h2\<rangle>\<in>f``G" using func_imagedef[OF assms(4)] by auto
  }
  then have "f``G {is closed under} F" unfolding IsOpClosed_def by auto
  moreover have "f``G\<subseteq>H" using func1_1_L6(2) assms(4) by auto moreover
  {
    fix h assume "h\<in>f``G"
    then obtain g where "h=f`g" and p:"g\<in>G" using func_imagedef[OF assms(4)] by auto
    then have "GroupInv(H,F)`h=GroupInv(H,F)`(f`g)" by auto
    then have "GroupInv(H,F)`h=f`(GroupInv(G,P)`g)" using p image_inv[OF assms] by auto
    then have "GroupInv(H,F)`h\<in>f``G" using p group0.inverse_in_group assms(1) unfolding group0_def
      using func_imagedef[OF assms(4)] by auto
  }
  then have "\<forall>h\<in>f``G. GroupInv(H,F)`h\<in>f``G" by auto ultimately
  show ?thesis using group0.group0_3_T3 assms(2) unfolding group0_def by auto
qed

text\<open>Now we are able to prove the first isomorphism theorem. This theorem states
that any group homomorphism $f:G\to H$ gives an isomorphism between a quotient group of $G$
and a subgroup of $H$.\<close>

theorem isomorphism_first_theorem:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)" "f:G\<rightarrow>H"
  defines "r \<equiv> QuotientGroupRel(G,P,f-``{TheNeutralElement(H,F)})" and
  "PP \<equiv> QuotientGroupOp(G,P,f-``{TheNeutralElement(H,F)})"
  shows "\<exists>ff. Homomor(ff,G//r,PP,f``G,restrict(F,(f``G)\<times>(f``G))) \<and> ff\<in>bij(G//r,f``G)"
proof-
  let ?ff="{\<langle>r``{g},f`g\<rangle>. g\<in>G}"
  {
    fix t assume "t\<in>{\<langle>r``{g},f`g\<rangle>. g\<in>G}"
    then obtain g where "t=\<langle>r``{g},f`g\<rangle>" "g\<in>G" by auto
    moreover then have "r``{g}\<in>G//r" unfolding r_def quotient_def by auto
    moreover from \<open>g\<in>G\<close> have "f`g\<in>f``G" using func_imagedef[OF assms(4)] by auto
    ultimately have "t\<in>(G//r)\<times>f``G" by auto
  }
  then have "?ff\<in>Pow((G//r)\<times>f``G)" by auto
  moreover have "(G//r)\<subseteq>domain(?ff)" unfolding domain_def quotient_def by auto moreover
  {
    fix x y t assume A:"\<langle>x,y\<rangle>\<in>?ff" "\<langle>x,t\<rangle>\<in>?ff"
    then obtain gy gr where "\<langle>x, y\<rangle>=\<langle>r``{gy},f`gy\<rangle>" "\<langle>x, t\<rangle>=\<langle>r``{gr},f`gr\<rangle>" and p:"gr\<in>G""gy\<in>G" by auto
    then have B:"r``{gy}=r``{gr}""y=f`gy""t=f`gr" by auto
    from B(2,3) have q:"y\<in>H""t\<in>H" using apply_type p assms(4) by auto
    have "\<langle>gy,gr\<rangle>\<in>r" using eq_equiv_class[OF B(1) _ p(1)] group0.Group_ZF_2_4_L3 kerner_normal_sub[OF assms(1-4)]
      assms(1) unfolding group0_def IsAnormalSubgroup_def r_def by auto
    then have "P`\<langle>gy,GroupInv(G,P)`gr\<rangle>\<in>f-``{TheNeutralElement(H,F)}" unfolding r_def QuotientGroupRel_def by auto
    then have eq:"f`(P`\<langle>gy,GroupInv(G,P)`gr\<rangle>)=TheNeutralElement(H,F)" using func1_1_L15[OF assms(4)] by auto
    from B(2,3) have "F`\<langle>y,GroupInv(H,F)`t\<rangle>=F`\<langle>f`gy,GroupInv(H,F)`(f`gr)\<rangle>" by auto
    also have "\<dots>=F`\<langle>f`gy,f`(GroupInv(G,P)`gr)\<rangle>" using image_inv[OF assms(1-4)] p(1) by auto
    also have "\<dots>=f`(P`\<langle>gy,GroupInv(G,P)`gr\<rangle>)" using assms(3) unfolding Homomor_def[OF assms(1,2)] using p(2)
      group0.inverse_in_group assms(1) p(1) unfolding group0_def by auto
    ultimately have "F`\<langle>y,GroupInv(H,F)`t\<rangle>=TheNeutralElement(H,F)" using eq by auto
    then have "y=t" using assms(2) group0.group0_2_L11A q unfolding group0_def by auto
  }
  then have "\<forall>x y. \<langle>x,y\<rangle>\<in>?ff \<longrightarrow> (\<forall>y'. \<langle>x,y'\<rangle>\<in>?ff \<longrightarrow> y=y')" by auto
  ultimately have ff_fun:"?ff:G//r\<rightarrow>f``G" unfolding Pi_def function_def by auto
  {
    fix a1 a2 assume AS:"a1\<in>G//r""a2\<in>G//r"
    then obtain g1 g2 where p:"g1\<in>G""g2\<in>G" and a:"a1=r``{g1}""a2=r``{g2}" unfolding quotient_def by auto
    have "equiv(G,r)" using group0.Group_ZF_2_4_L3 kerner_normal_sub[OF assms(1-4)]
      assms(1) unfolding group0_def IsAnormalSubgroup_def r_def by auto moreover
    have "Congruent2(r,P)" using Group_ZF_2_4_L5A[OF assms(1) kerner_normal_sub[OF assms(1-4)]]
      unfolding r_def by auto moreover
    have "PP=ProjFun2(G,r,P)" unfolding PP_def QuotientGroupOp_def r_def by auto moreover
    note a p ultimately have "PP`\<langle>a1,a2\<rangle>=r``{P`\<langle>g1,g2\<rangle>}" using group0.Group_ZF_2_2_L2 assms(1)
      unfolding group0_def by auto
    then have "\<langle>PP`\<langle>a1,a2\<rangle>,f`(P`\<langle>g1,g2\<rangle>)\<rangle>\<in>?ff" using group0.group_op_closed[OF _ p] assms(1) unfolding group0_def
      by auto
    then have eq:"?ff`(PP`\<langle>a1,a2\<rangle>)=f`(P`\<langle>g1,g2\<rangle>)" using apply_equality ff_fun by auto
    from p a have "\<langle>a1,f`g1\<rangle>\<in>?ff""\<langle>a2,f`g2\<rangle>\<in>?ff" by auto
    then have "?ff`a1=f`g1""?ff`a2=f`g2" using apply_equality ff_fun by auto
    then have "F`\<langle>?ff`a1,?ff`a2\<rangle>=F`\<langle>f`g1,f`g2\<rangle>" by auto
    also have "\<dots>=f`(P`\<langle>g1,g2\<rangle>)" using assms(3) unfolding Homomor_def[OF assms(1,2)] using p by auto
    ultimately have "F`\<langle>?ff`a1,?ff`a2\<rangle>=?ff`(PP`\<langle>a1,a2\<rangle>)" using eq by auto moreover
    have "?ff`a1\<in>f``G""?ff`a2\<in>f``G" using ff_fun apply_type AS by auto ultimately
    have "restrict(F,f``G\<times>f``G)`\<langle>?ff`a1,?ff`a2\<rangle>=?ff`(PP`\<langle>a1,a2\<rangle>)" by auto
  }
  then have r:"\<forall>a1\<in>G//r. \<forall>a2\<in>G//r. restrict(F,f``G\<times>f``G)`\<langle>?ff`a1,?ff`a2\<rangle>=?ff`(PP`\<langle>a1,a2\<rangle>)" by auto
  have G:"IsAgroup(G//r,PP)" using Group_ZF_2_4_T1[OF assms(1) kerner_normal_sub[OF assms(1-4)]] unfolding r_def PP_def by auto
  have H:"IsAgroup(f``G, restrict(F,f``G\<times>f``G))" using image_sub[OF assms(1-4)] unfolding IsAsubgroup_def .
  have HOM:"Homomor(?ff,G//r,PP,f``G,restrict(F,(f``G)\<times>(f``G)))" using r unfolding Homomor_def[OF G H] by auto
  {
    fix b1 b2 assume AS:"?ff`b1=?ff`b2""b1\<in>G//r""b2\<in>G//r"
    have invb2:"GroupInv(G//r,PP)`b2\<in>G//r" using group0.inverse_in_group[OF _ AS(3)] G unfolding group0_def
      by auto
    with AS(2) have "PP`\<langle>b1,GroupInv(G//r,PP)`b2\<rangle>\<in>G//r" using group0.group_op_closed G unfolding group0_def by auto moreover
    then obtain gg where gg:"gg\<in>G""PP`\<langle>b1,GroupInv(G//r,PP)`b2\<rangle>=r``{gg}" unfolding quotient_def by auto
    ultimately have E:"?ff`(PP`\<langle>b1,GroupInv(G//r,PP)`b2\<rangle>)=f`gg" using apply_equality[OF _ ff_fun] by auto
    from invb2 have pp:"?ff`(GroupInv(G//r,PP)`b2)\<in>f``G" using apply_type ff_fun by auto
    from AS(2,3) have fff:"?ff`b1\<in>f``G""?ff`b2\<in>f``G" using apply_type[OF ff_fun] by auto
    from fff(1) pp have EE:"F`\<langle>?ff`b1,?ff`(GroupInv(G//r,PP)`b2)\<rangle>=restrict(F,f``G\<times>f``G)`\<langle>?ff`b1,?ff`(GroupInv(G//r,PP)`b2)\<rangle>"
      by auto
    from fff have fff2:"?ff`b1\<in>H""?ff`b2\<in>H" using func1_1_L6(2)[OF assms(4)] by auto
    with AS(1) have "TheNeutralElement(H,F)=F`\<langle>?ff`b1,GroupInv(H,F)`(?ff`b2)\<rangle>" using group0.group0_2_L6(1)
      assms(2) unfolding group0_def by auto
    also have "\<dots>=F`\<langle>?ff`b1,restrict(GroupInv(H,F),f``G)`(?ff`b2)\<rangle>" using restrict fff(2) by auto
    also have "\<dots>=F`\<langle>?ff`b1,?ff`(GroupInv(G//r,PP)`b2)\<rangle>" using image_inv[OF G H HOM ff_fun AS(3)]
      group0.group0_3_T1[OF _ image_sub[OF assms(1-4)]] assms(2) unfolding group0_def by auto
    also have "\<dots>=restrict(F,f``G\<times>f``G)`\<langle>?ff`b1,?ff`(GroupInv(G//r,PP)`b2)\<rangle>" using EE by auto
    also have "\<dots>=?ff`(PP`\<langle>b1,GroupInv(G//r,PP)`b2\<rangle>)" using HOM unfolding Homomor_def[OF G H] using AS(2)
      group0.inverse_in_group[OF _ AS(3)] G unfolding group0_def by auto
    also have "\<dots>=f`gg" using E by auto
    ultimately have "f`gg=TheNeutralElement(H,F)" by auto
    then have "gg\<in>f-``{TheNeutralElement(H,F)}" using func1_1_L15[OF assms(4)] \<open>gg\<in>G\<close> by auto
    then have "r``{gg}=TheNeutralElement(G//r,PP)" using group0.Group_ZF_2_4_L5E[OF _ kerner_normal_sub[OF assms(1-4)]
      \<open>gg\<in>G\<close> ] using assms(1) unfolding group0_def r_def PP_def by auto 
    with gg(2) have "PP`\<langle>b1,GroupInv(G//r,PP)`b2\<rangle>=TheNeutralElement(G//r,PP)" by auto
    then have "b1=b2" using group0.group0_2_L11A[OF _ AS(2,3)] G unfolding group0_def by auto
  }
  then have "?ff\<in>inj(G//r,f``G)" unfolding inj_def using ff_fun by auto moreover
  {
    fix m assume "m\<in>f``G"
    then obtain g where "g\<in>G""m=f`g" using func_imagedef[OF assms(4)] by auto
    then have "\<langle>r``{g},m\<rangle>\<in>?ff" by auto
    then have "?ff`(r``{g})=m" using apply_equality ff_fun by auto
    then have "\<exists>A\<in>G//r. ?ff`A=m" unfolding quotient_def using \<open>g\<in>G\<close> by auto
  }
  ultimately have "?ff\<in>bij(G//r,f``G)" unfolding bij_def surj_def using ff_fun by auto
  with HOM show ?thesis by auto
qed

text\<open>As a last result, the inverse of a bijective homomorphism is an homomorphism.
Meaning that in the previous result, the homomorphism we found is an isomorphism.\<close>

theorem bij_homomor:
  assumes "f\<in>bij(G,H)""IsAgroup(G,P)""IsAgroup(H,F)""Homomor(f,G,P,H,F)"
  shows "Homomor(converse(f),H,F,G,P)"
proof-
  {
    fix h1 h2 assume A:"h1\<in>H" "h2\<in>H"
    from A(1) obtain g1 where g1:"g1\<in>G" "f`g1=h1" using assms(1) unfolding bij_def surj_def by auto moreover
    from A(2) obtain g2 where g2:"g2\<in>G" "f`g2=h2" using assms(1) unfolding bij_def surj_def by auto ultimately
    have "F`\<langle>f`g1,f`g2\<rangle>=F`\<langle>h1,h2\<rangle>" by auto
    then have "f`(P`\<langle>g1,g2\<rangle>)=F`\<langle>h1,h2\<rangle>" using assms(2,3,4) homomor_eq g1(1) g2(1) by auto
    then have "converse(f)`(f`(P`\<langle>g1,g2\<rangle>))=converse(f)`(F`\<langle>h1,h2\<rangle>)" by auto
    then have "P`\<langle>g1,g2\<rangle>=converse(f)`(F`\<langle>h1,h2\<rangle>)" using left_inverse assms(1) group0.group_op_closed
      assms(2) g1(1) g2(1) unfolding group0_def bij_def by auto moreover
    from g1(2) have "converse(f)`(f`g1)=converse(f)`h1" by auto
    then have "g1=converse(f)`h1" using left_inverse assms(1) unfolding bij_def using g1(1) by auto moreover
    from g2(2) have "converse(f)`(f`g2)=converse(f)`h2" by auto
    then have "g2=converse(f)`h2" using left_inverse assms(1) unfolding bij_def using g2(1) by auto ultimately
    have "P`\<langle>converse(f)`h1,converse(f)`h2\<rangle>=converse(f)`(F`\<langle>h1,h2\<rangle>)" by auto
  }
  then show ?thesis using assms(2,3) Homomor_def by auto
qed

end
