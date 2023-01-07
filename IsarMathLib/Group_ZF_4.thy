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

theory Group_ZF_4 imports Group_ZF_1 Group_ZF_2 Finite_ZF Cardinal_ZF

begin

text\<open>This theory file deals with normal subgroup test and some finite group theory.
Then we define group homomorphisms and prove that the set of endomorphisms
forms a ring with unity and we also prove the first isomorphism theorem.\<close>

subsection\<open>Conjugation of subgroups\<close>

text\<open>First we show some properties of conjugation\<close>

text\<open>The conjugate of a subgroup is a subgroup.\<close>

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
    ultimately have "r\<inverse>=(h\<cdot>(g\<inverse>))\<inverse>\<cdot>(g)\<inverse>" using group_inv_of_two assms(2) by auto
    moreover
    from \<open>h\<in>G\<close> \<open>g\<inverse>\<in>G\<close> have "(h\<cdot>(g\<inverse>))\<inverse>=(g\<inverse>)\<inverse>\<cdot>h\<inverse>" using group_inv_of_two by auto
    moreover have "(g\<inverse>)\<inverse>=g" using group_inv_of_inv assms(2) by auto
    ultimately have "r\<inverse>=(g\<cdot>(h\<inverse>))\<cdot>(g)\<inverse>" by auto
    with \<open>h\<inverse>\<in>G\<close>\<open>g\<inverse>\<in>G\<close> have "r\<inverse>=g\<cdot>((h\<inverse>)\<cdot>(g)\<inverse>)" using group_oper_assoc assms(2) by auto
    moreover from s assms(2) h(2) have "r\<in>G" using group_op_closed by auto
    moreover note \<open>h\<inverse>\<in>H\<close> ultimately have "r\<inverse>\<in>{g\<cdot>(h\<cdot>g\<inverse>). h\<in>H}" "r\<in>G" by auto
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
    from hs(2) ht(2) have "s\<cdot>t=(g\<cdot>(hs\<cdot>(g\<inverse>)))\<cdot>(g\<cdot>(ht\<cdot>(g\<inverse>)))" by auto
    moreover from \<open>hs\<in>G\<close> have "hs\<cdot>ht = hs\<cdot>\<one>\<cdot>ht" using group0_2_L2 by auto
    then have "hs\<cdot>ht = hs\<cdot>(g\<inverse>\<cdot>g)\<cdot>ht" using group0_2_L6 assms(2) by auto
    then have "g\<cdot>(hs\<cdot>ht) = g\<cdot>(hs\<cdot>(g\<inverse>\<cdot>g)\<cdot>ht)" by auto
    with \<open>hs\<in>G\<close> have "g\<cdot>(hs\<cdot>ht) = g\<cdot>((hs\<cdot>g\<inverse>\<cdot>g)\<cdot>ht)" using group_oper_assoc
      assms(2) inverse_in_group by auto
    with \<open>hs\<in>G\<close> \<open>ht\<in>G\<close> have "g\<cdot>(hs\<cdot>ht) = g\<cdot>(hs\<cdot>g\<inverse>\<cdot>(g\<cdot>ht))" using group_oper_assoc
      assms(2) inverse_in_group group_op_closed by auto
    with \<open>hs\<in>G\<close> \<open>ht\<in>G\<close> have "g\<cdot>(hs\<cdot>ht) = g\<cdot>(hs\<cdot>g\<inverse>)\<cdot>(g\<cdot>ht)" using group_oper_assoc
      assms(2) inverse_in_group group_op_closed by auto
    then have "g\<cdot>(hs\<cdot>ht)\<cdot>g\<inverse> = g\<cdot>(hs\<cdot>g\<inverse>)\<cdot>(g\<cdot>ht)\<cdot>g\<inverse>" by auto
    with \<open>hs\<in>G\<close> \<open>ht\<in>G\<close> have "g\<cdot>((hs\<cdot>ht)\<cdot>g\<inverse>) = g\<cdot>(hs\<cdot>g\<inverse>)\<cdot>(g\<cdot>ht)\<cdot>g\<inverse>" using group_oper_assoc
      inverse_in_group assms(2) group_op_closed by auto
    with \<open>hs\<in>G\<close> \<open>ht\<in>G\<close> have "g\<cdot>((hs\<cdot>ht)\<cdot>g\<inverse>) = (g\<cdot>(hs\<cdot>g\<inverse>))\<cdot>(g\<cdot>(ht\<cdot>g\<inverse>))" using group_oper_assoc
      inverse_in_group assms(2) group_op_closed by auto
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
      group_op_closed inverse_in_group assms(2) by auto
    then have "h1\<cdot>g\<inverse>=h2\<cdot>g\<inverse>" using group0_2_L19(2) assms(2) by auto
    with \<open>h1\<in>G\<close> \<open>h2\<in>G\<close> have "h1=h2" using group0_2_L19(1) inverse_in_group assms(2) by auto
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
    then obtain h where h:"r=g\<cdot>(h\<cdot>g\<inverse>)" "h\<in>H" by auto moreover
    from h(2) have "h\<in>G" using group0_3_L2 assms(1) unfolding IsAnormalSubgroup_def by auto moreover
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
    moreover from \<open>g\<in>G\<close>\<open>h\<in>H\<close> have "h\<in>G" "g\<inverse>\<in>G" "g\<in>G" using group0_3_L2 assms(1) inverse_in_group by auto
    ultimately have "g\<cdot>h\<cdot>g\<inverse>\<in>H" using group_oper_assoc by auto
  }
  then show ?thesis using assms(1) unfolding IsAnormalSubgroup_def by auto
qed

text\<open>If a group has only one subgroup of a given order, then this subgroup is normal.\<close>

corollary (in group0) only_one_equipoll_sub:
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

corollary (in group0) trivial_normal_subgroup:
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
    then have one:"\<one>\<in>M" "M\<approx>{\<one>}" using eqpoll_sym group0_3_L5 by auto
    then obtain f where "f\<in>bij(M,{\<one>})" unfolding eqpoll_def by auto
    then have inj:"f\<in>inj(M,{\<one>})" unfolding bij_def by auto
    then have fun:"f:M\<rightarrow>{\<one>}" unfolding inj_def by auto
    {
      fix b assume b:"b\<in>M" "b\<noteq>\<one>"
      with \<open>\<one>\<in>M\<close> have "f`b\<noteq>f`\<one>" using inj unfolding inj_def by auto
      moreover from fun b(1) have "f`b\<in>{\<one>}" by (rule apply_type)
      moreover from fun one(1) have "f`\<one>\<in>{\<one>}" by (rule apply_type)
      ultimately have "False" by auto
    }
    with \<open>\<one>\<in>M\<close> have "M={\<one>}" by auto
  }
  ultimately show ?thesis using only_one_equipoll_sub by auto
qed

text\<open>The whole group is normal as a subgroup\<close>

lemma (in group0) whole_normal_subgroup:
  shows "IsAnormalSubgroup(G,P,G)"
proof-
  have "G\<subseteq>G" by auto moreover
  have "\<forall>x\<in>G. x\<inverse>\<in>G" using inverse_in_group by auto moreover
  have "G\<noteq>0" using group0_2_L2 by auto moreover
  have "G{is closed under}P" using group_op_closed
    unfolding IsOpClosed_def by auto ultimately
  have "IsAsubgroup(G,P)" using group0_3_T3 by auto
  moreover
  {
    fix n g assume ng:"n\<in>G" "g\<in>G"
    then have "P ` \<langle>P ` \<langle>g, n\<rangle>, GroupInv(G, P) ` g\<rangle> \<in> G"
      using group_op_closed inverse_in_group by auto
  }
  ultimately show ?thesis unfolding IsAnormalSubgroup_def by auto
qed

subsection\<open>Simple groups\<close>

text\<open>In this subsection we study the groups that build the rest of
the groups: the simple groups.\<close>

text\<open>Since the whole group and the trivial subgroup are always normal,
it is natural to define simplicity of groups in the following way:\<close>

definition
  IsSimple ("[_,_]{is a simple group}" 89)
  where "[G,f]{is a simple group} \<equiv> IsAgroup(G,f) \<and> (\<forall>M. IsAnormalSubgroup(G,f,M) \<longrightarrow> M=G\<or>M={TheNeutralElement(G,f)})"

text\<open>From the definition follows that if a group has no subgroups,
then it is simple.\<close>

corollary (in group0) noSubgroup_imp_simple:
  assumes "\<forall>H. IsAsubgroup(H,P)\<longrightarrow> H=G\<or>H={\<one>}"
  shows "[G,P]{is a simple group}"
proof-
  have "IsAgroup(G,P)" using groupAssum by auto moreover
  {
    fix M assume "IsAnormalSubgroup(G,P,M)"
    then have "IsAsubgroup(M,P)" unfolding IsAnormalSubgroup_def by auto
    with assms have "M=G\<or>M={\<one>}" by auto
  }
  ultimately show ?thesis unfolding IsSimple_def by auto
qed

text\<open>We add a context for an abelian group\<close>

locale abelian_group = group0 +
  assumes isAbelian: "P {is commutative on} G"

text\<open>Since every subgroup is normal in abelian
groups, it follows that commutative simple groups
do not have subgroups.\<close>

corollary (in abelian_group) abelian_simple_noSubgroups:
  assumes "[G,P]{is a simple group}"
  shows "\<forall>H. IsAsubgroup(H,P)\<longrightarrow> H=G\<or>H={\<one>}"
proof-
  {
    fix H assume A:"IsAsubgroup(H,P)""H \<noteq> {\<one>}"
    then have "IsAnormalSubgroup(G,P,H)" using Group_ZF_2_4_L6(1) groupAssum isAbelian
      by auto
    with assms(1) A have "H=G" unfolding IsSimple_def by auto
  }
  then show ?thesis by auto
qed

subsection\<open>Finite groups\<close>

text\<open>This subsection deals with finite groups and their structure\<close>

text\<open>The subgroup of a finite group is finite.\<close>

lemma (in group0) finite_subgroup:
  assumes "Finite(G)" "IsAsubgroup(H,P)"
  shows "Finite(H)"
  using group0_3_L2 subset_Finite assms by force

text\<open>The space of cosets is also finite. In particular, quotient groups.\<close>

lemma (in group0) finite_cosets:
  assumes "Finite(G)" "IsAsubgroup(H,P)"
  defines "r \<equiv> QuotientGroupRel(G,P,H)"
  shows "Finite(G//r)"
proof- 
  have fun:"{\<langle>g,r``{g}\<rangle>. g\<in>G}:G\<rightarrow>(G//r)" unfolding Pi_def function_def domain_def by auto
  {
    fix C assume C:"C\<in>G//r"
    have equiv:"equiv(G,r)" using Group_ZF_2_4_L3 assms(2) unfolding r_def by auto
    then have "refl(G,r)" unfolding equiv_def by auto
    with C have "C\<noteq>0" using EquivClass_1_L5 by auto
    then obtain c where c:"c\<in>C" by auto
    with C have "r``{c}=C" using EquivClass_1_L2 equiv by auto
    with c C have "\<langle>c,C\<rangle>\<in>{\<langle>g,r``{g}\<rangle>. g\<in>G}" using EquivClass_1_L1 equiv by auto
    then have "{\<langle>g,r``{g}\<rangle>. g\<in>G}`c=C" "c\<in>G" using apply_equality fun by auto
    then have "\<exists>c\<in>G. {\<langle>g,r``{g}\<rangle>. g\<in>G}`c=C" by auto
  }
  with fun have surj:"{\<langle>g,r``{g}\<rangle>. g\<in>G}\<in>surj(G,G//r)" unfolding surj_def by auto
  from assms(1) obtain n where "n\<in>nat" "G\<approx>n" unfolding Finite_def by auto
  then have G:"G\<lesssim>n" "Ord(n)" using eqpoll_imp_lepoll by auto
  then have "G//r\<lesssim>G" using surj_fun_inv_2 surj by auto
  with G(1) have "G//r\<lesssim>n" using lepoll_trans by blast
  with \<open>n\<in>nat\<close> show "Finite(G//r)" using lepoll_nat_imp_Finite by auto
qed

text\<open>All the cosets are equipollent.\<close>

lemma (in group0) cosets_equipoll:
  assumes "IsAsubgroup(H,P)" "g1\<in>G""g2\<in>G"
  defines "r \<equiv> QuotientGroupRel(G,P,H)"
  shows "r``{g1} \<approx> r``{g2}"
proof-
  have equiv:"equiv(G,r)" using Group_ZF_2_4_L3 assms(1) unfolding r_def by auto
  from assms(3,2) have GG:"(g1\<inverse>)\<cdot>g2\<in>G" using inverse_in_group group_op_closed by auto
  then have bij:"RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)\<in>bij(G,G)" using trans_bij(1) by auto
  have "r``{g2}\<in>G//r" using assms(3) unfolding quotient_def by auto
  then have sub2:"r``{g2}\<subseteq>G" using EquivClass_1_L1 equiv
      assms(3) by blast
  have "r``{g1}\<in>G//r" using assms(2) unfolding quotient_def by auto
  then have sub:"r``{g1}\<subseteq>G" using EquivClass_1_L1 equiv assms(2) by blast
  with bij have "restrict(RightTranslation(G,P,(g1\<inverse>)\<cdot>g2),r``{g1})\<in>bij(r``{g1},RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)``(r``{g1}))"
    using restrict_bij unfolding bij_def by auto
  then have "r``{g1}\<approx>RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)``(r``{g1})" unfolding eqpoll_def by auto
  with GG sub have A0:"r``{g1}\<approx>{RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)`t. t\<in>r``{g1}}"
    using func_imagedef group0_5_L1(1) by force
  {
    fix t assume "t\<in>{RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)`t. t\<in>r``{g1}}"
    then obtain q where q:"t=RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)`q" "q\<in>r``{g1}" by auto
    then have "\<langle>g1,q\<rangle>\<in>r" "q\<in>G" using image_iff sub by auto
    then have "g1\<cdot>(q\<inverse>)\<in>H" "q\<inverse>\<in>G" using inverse_in_group unfolding r_def QuotientGroupRel_def by auto
    from GG q sub have t:"t=q\<cdot>((g1\<inverse>)\<cdot>g2)" using group0_5_L2(1) by auto
    then have "g2\<cdot>t\<inverse>=g2\<cdot>(q\<cdot>((g1\<inverse>)\<cdot>g2))\<inverse>" by auto
    with \<open>q\<in>G\<close> GG have "g2\<cdot>t\<inverse>=g2\<cdot>(((g1\<inverse>)\<cdot>g2)\<inverse>\<cdot>q\<inverse>)" using group_inv_of_two by auto
    then have "g2\<cdot>t\<inverse>=g2\<cdot>(((g2\<inverse>)\<cdot>g1\<inverse>\<inverse>)\<cdot>q\<inverse>)" using group_inv_of_two inverse_in_group assms(2)
      assms(3) by auto
    then have "g2\<cdot>t\<inverse>=g2\<cdot>(((g2\<inverse>)\<cdot>g1)\<cdot>q\<inverse>)" using group_inv_of_inv assms(2) by auto moreover
    have "(g2\<inverse>)\<cdot>g1\<in>G" using assms(2) inverse_in_group assms(3) group_op_closed by auto
    with assms(3) \<open>q\<inverse>\<in>G\<close> have "g2\<cdot>(((g2\<inverse>)\<cdot>g1)\<cdot>q\<inverse>)=g2\<cdot>((g2\<inverse>)\<cdot>g1)\<cdot>q\<inverse>" using group_oper_assoc by auto
    moreover have "g2\<cdot>((g2\<inverse>)\<cdot>g1)=g2\<cdot>(g2\<inverse>)\<cdot>g1" using assms(2) inverse_in_group assms(3)
      group_oper_assoc by auto
    then have "g2\<cdot>((g2\<inverse>)\<cdot>g1)=g1" using group0_2_L6 assms(3) group0_2_L2 assms(2) by auto ultimately
    have "g2\<cdot>t\<inverse>=g1\<cdot>q\<inverse>" by auto
    with \<open>g1\<cdot>(q\<inverse>)\<in>H\<close> have "g2\<cdot>t\<inverse>\<in>H" by auto moreover
    from t \<open>q\<in>G\<close> \<open>g2\<in>G\<close> have "t\<in>G" using inverse_in_group assms(2) group_op_closed by auto
    ultimately have "\<langle>g2,t\<rangle>\<in>r" unfolding QuotientGroupRel_def r_def using assms(3) by auto
    then have "t\<in>r``{g2}" using image_iff assms(4) by auto
  }
  then have A1:"{RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)`t. t\<in>r``{g1}}\<subseteq>r``{g2}" by auto
  {
    fix t assume "t\<in>r``{g2}"
    then have "\<langle>g2,t\<rangle>\<in>r" "t\<in>G" using sub2 image_iff by auto
    then have H:"g2\<cdot>t\<inverse>\<in>H" unfolding QuotientGroupRel_def r_def by auto
    then have G:"g2\<cdot>t\<inverse>\<in>G" using group0_3_L2 assms(1) by auto
    then have "g1\<cdot>(g1\<inverse>\<cdot>(g2\<cdot>t\<inverse>))=g1\<cdot>g1\<inverse>\<cdot>(g2\<cdot>t\<inverse>)" using group_oper_assoc
        assms(2) inverse_in_group by auto
    with G have "g1\<cdot>(g1\<inverse>\<cdot>(g2\<cdot>t\<inverse>))=g2\<cdot>t\<inverse>" using group0_2_L6 assms(2) group0_2_L2 by auto
    with H have HH:"g1\<cdot>(g1\<inverse>\<cdot>(g2\<cdot>t\<inverse>))\<in>H" by auto
    from \<open>t\<in>G\<close> have GGG:"t\<cdot>g2\<inverse>\<in>G" using inverse_in_group assms(3) group_op_closed by auto
    from \<open>t\<in>G\<close> have "(t\<cdot>g2\<inverse>)\<inverse>=g2\<inverse>\<inverse>\<cdot>t\<inverse>" using group_inv_of_two inverse_in_group assms(3) by auto
    also have "\<dots>=g2\<cdot>t\<inverse>" using group_inv_of_inv assms(3) by auto
    finally have "(t\<cdot>g2\<inverse>)\<inverse>=g2\<cdot>t\<inverse>" by auto
    then have "g1\<inverse>\<cdot>(t\<cdot>g2\<inverse>)\<inverse>=g1\<inverse>\<cdot>(g2\<cdot>t\<inverse>)" by auto
    then have "((t\<cdot>g2\<inverse>)\<cdot>g1)\<inverse>=g1\<inverse>\<cdot>(g2\<cdot>t\<inverse>)" using group_inv_of_two GGG assms(2) by auto
    then have HHH:"g1\<cdot>((t\<cdot>g2\<inverse>)\<cdot>g1)\<inverse>\<in>H" using HH by auto
    from \<open>t\<in>G\<close> have "(t\<cdot>g2\<inverse>)\<cdot>g1\<in>G" using assms(2) inverse_in_group assms(3) group_op_closed by auto
    with HHH have "\<langle>g1,(t\<cdot>g2\<inverse>)\<cdot>g1\<rangle>\<in>r" using assms(2) unfolding r_def QuotientGroupRel_def by auto
    then have rg1:"t\<cdot>g2\<inverse>\<cdot>g1\<in>r``{g1}" using image_iff by auto
    from assms(3) have "g2\<inverse>:G" using inverse_in_group by auto
    from \<open>t\<in>G\<close> have "t\<cdot>g2\<inverse>\<cdot>g1\<cdot>((g1\<inverse>)\<cdot>g2)=t\<cdot>(g2\<inverse>\<cdot>g1)\<cdot>((g1\<inverse>)\<cdot>g2)" using group_oper_assoc inverse_in_group assms(3) assms(2)
      by auto
    also from \<open>t\<in>G\<close> have "\<dots>=t\<cdot>((g2\<inverse>\<cdot>g1)\<cdot>((g1\<inverse>)\<cdot>g2))" using group_oper_assoc group_op_closed inverse_in_group assms(3) assms(2)
      by auto
    also from GG \<open>g2\<inverse>:G\<close> have "\<dots>=t\<cdot>(g2\<inverse>\<cdot>(g1\<cdot>((g1\<inverse>)\<cdot>g2)))" using group_oper_assoc
      assms(2) by auto
    also have "\<dots>=t\<cdot>(g2\<inverse>\<cdot>(g1\<cdot>(g1\<inverse>)\<cdot>g2))" using group_oper_assoc assms(2) inverse_in_group assms(3) by auto
    also from \<open>t\<in>G\<close> have "\<dots>=t" using group0_2_L6 assms(3) group0_2_L6 assms(2) group0_2_L2 assms(3) by auto
    finally have "t\<cdot>g2\<inverse>\<cdot>g1\<cdot>((g1\<inverse>)\<cdot>g2)=t" by auto
    with \<open>(t\<cdot>g2\<inverse>)\<cdot>g1\<in>G\<close> GG have "RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)`(t\<cdot>g2\<inverse>\<cdot>g1)=t" using group0_5_L2(1) by auto
    then have "t\<in>{RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)`t. t\<in>r``{g1}}" using rg1 by force
  }
  then have "r``{g2}\<subseteq>{RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)`t. t\<in>r``{g1}}" by blast
  with A1 have "r``{g2}={RightTranslation(G,P,(g1\<inverse>)\<cdot>g2)`t. t\<in>r``{g1}}" by auto
  with A0 show ?thesis by auto
qed

text\<open>The order of a subgroup multiplied by the order of the space of cosets is the order of
the group. We only prove the theorem for finite groups.\<close>

theorem (in group0) Lagrange:
  assumes "Finite(G)" "IsAsubgroup(H,P)"
  defines "r \<equiv> QuotientGroupRel(G,P,H)"
  shows "|G|=|H| #* |G//r|"
proof-
  have equiv:"equiv(G,r)" using Group_ZF_2_4_L3 assms(2) unfolding r_def by auto
  have "r``{\<one>} \<subseteq>G" unfolding r_def QuotientGroupRel_def by auto

  have "\<forall>aa\<in>G. aa\<in>H \<longleftrightarrow> \<langle>aa,\<one>\<rangle>\<in>r" using Group_ZF_2_4_L5C unfolding r_def by auto
  then have "\<forall>aa\<in>G. aa\<in>H \<longleftrightarrow> \<langle>\<one>,aa\<rangle>\<in>r" using equiv unfolding sym_def equiv_def
    by auto
  then have "\<forall>aa\<in>G. aa\<in>H \<longleftrightarrow> aa\<in>r``{\<one>}" using image_iff by auto
  with \<open>r``{\<one>} \<subseteq>G\<close> have H:"H=r``{\<one>}" using group0_3_L2 assms(2) by blast
  {
    fix c assume "c\<in>(G//r)"
    then obtain g where "g\<in>G" "c=r``{g}" unfolding quotient_def by auto
    then have "c\<approx>r``{\<one>}" using cosets_equipoll assms(2) group0_2_L2 unfolding r_def by auto
    then have "|c|=|H|" using H cardinal_cong by auto
  }
  then have "\<forall>c\<in>(G//r). |c|=|H|" by auto moreover
  have "Finite(G//r)" using assms finite_cosets by auto moreover
  have "\<Union>(G//r)=G" using Union_quotient Group_ZF_2_4_L3 assms(2,3) by auto moreover
  from \<open>\<Union>(G//r)=G\<close> have "Finite(\<Union>(G//r))" using assms(1) by auto moreover
  have "\<forall>c1\<in>(G//r). \<forall>c2\<in>(G//r). c1\<noteq>c2 \<longrightarrow> c1\<inter>c2=0" using quotient_disj
      equiv by blast ultimately
  show ?thesis using card_partition by auto
qed

subsection\<open>Subgroups generated by sets\<close>

text\<open>In this section we study the minimal subgroup containing a set\<close>

text\<open>Since \<open>G\<close> is always a group containing the set, we may take
the intersection of all subgroups bigger than the set; and hence
the result is the subgroup we searched.\<close>

definition (in group0)
  SubgroupGenerated ("\<langle>_\<rangle>\<^sub>G" 80)
  where "X\<subseteq>G \<Longrightarrow> \<langle>X\<rangle>\<^sub>G \<equiv> \<Inter>{H\<in>Pow(G). X\<subseteq>H \<and> IsAsubgroup(H,P)}"

text\<open>Every generated subgroup is a subgroup\<close>

theorem (in group0) subgroupGen_is_subgroup:
  assumes "X\<subseteq>G"
  shows "IsAsubgroup(\<langle>X\<rangle>\<^sub>G,P)"
proof-
  have "restrict(P,G\<times>G)=P" using group_oper_fun restrict_idem unfolding Pi_def by auto
  then have "IsAsubgroup(G,P)" unfolding IsAsubgroup_def using groupAssum by auto
  with assms have "G\<in>{H\<in>Pow(G). X\<subseteq>H \<and> IsAsubgroup(H,P)}" by auto
  then have "{H\<in>Pow(G). X\<subseteq>H \<and> IsAsubgroup(H,P)}\<noteq>0" by auto
  then show ?thesis using subgroup_inter SubgroupGenerated_def assms by auto
qed

text\<open>The generated subgroup contains the original set\<close>

theorem (in group0) subgroupGen_contains_set:
  assumes "X\<subseteq>G"
  shows "X \<subseteq> \<langle>X\<rangle>\<^sub>G"
proof-
  have "restrict(P,G\<times>G)=P" using group_oper_fun restrict_idem unfolding Pi_def by auto
  then have "IsAsubgroup(G,P)" unfolding IsAsubgroup_def using groupAssum by auto
  with assms have "G\<in>{H\<in>Pow(G). X\<subseteq>H \<and> IsAsubgroup(H,P)}" by auto
  then have "{H\<in>Pow(G). X\<subseteq>H \<and> IsAsubgroup(H,P)}\<noteq>0" by auto
  then show ?thesis using subgroup_inter SubgroupGenerated_def assms by auto
qed

text\<open>Given a subgroup that contains a set, the generated subgroup
from that set is smaller than this subgroup\<close>

theorem (in group0) subgroupGen_minimal:
  assumes "IsAsubgroup(H,P)" "X\<subseteq>H"
  shows "\<langle>X\<rangle>\<^sub>G \<subseteq> H"
proof-
  from assms have sub:"X\<subseteq>G" using group0_3_L2 by auto
  from assms have "H\<in>{H\<in>Pow(G). X\<subseteq>H \<and> IsAsubgroup(H,P)}" using group0_3_L2 by auto
  then show ?thesis using sub subgroup_inter SubgroupGenerated_def assms by auto
qed

end