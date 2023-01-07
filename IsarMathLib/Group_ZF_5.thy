(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2013-2022 Daniel de la Concepcion

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

section \<open>Groups 5\<close>

theory Group_ZF_5 imports Group_ZF_4 Ring_ZF Semigroup_ZF

begin

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
  
theorem(in abelian_group) end_pointwise_addition:
  assumes "f\<in>End(G,P)" "g\<in>End(G,P)" "F = P {lifted to function space over} G"
  shows "F`\<langle>f,g\<rangle>\<in>End(G,P)"
proof-
  from assms(1,2) have fun:"f\<in>G\<rightarrow>G""g\<in>G\<rightarrow>G" unfolding End_def by auto
  then have fun2:"F`\<langle>f,g\<rangle>:G\<rightarrow>G" using monoid0.Group_ZF_2_1_L0 group0_2_L1 assms(3) by auto
  {
    fix g1 g2 assume AS:"g1\<in>G""g2\<in>G"
    then have "g1\<cdot>g2\<in>G" using group_op_closed by auto
    then have "(F`\<langle>f,g\<rangle>)`(g1\<cdot>g2)=(f`(g1\<cdot>g2))\<cdot>(g`(g1\<cdot>g2))" using Group_ZF_2_1_L3 fun assms(3) by auto
    also have "\<dots>=(f`(g1)\<cdot>f`(g2))\<cdot>(g`(g1)\<cdot>g`(g2))" using assms unfolding End_def Homomor_def[OF groupAssum groupAssum]
      using AS by auto ultimately
    have "(F`\<langle>f,g\<rangle>)`(g1\<cdot>g2)=(f`(g1)\<cdot>f`(g2))\<cdot>(g`(g1)\<cdot>g`(g2))" by auto moreover
    have "f`g1\<in>G""f`g2\<in>G""g`g1\<in>G""g`g2\<in>G" using fun apply_type AS by auto ultimately
    have "(F`\<langle>f,g\<rangle>)`(g1\<cdot>g2)=(f`(g1)\<cdot>g`(g1))\<cdot>(f`(g2)\<cdot>g`(g2))" using group0_4_L8(3) assms(3) isAbelian
      by auto
    with AS have "(F`\<langle>f,g\<rangle>)`(g1\<cdot>g2)=((F`\<langle>f,g\<rangle>)`g1)\<cdot>((F`\<langle>f,g\<rangle>)`g2)"
      using Group_ZF_2_1_L3 fun assms(3) by auto
  }
  with fun2 show ?thesis unfolding End_def Homomor_def[OF groupAssum groupAssum] by auto
qed

text\<open>The inverse of an abelian group is an endomorphism.\<close>

lemma(in abelian_group) end_inverse_group:
  shows "GroupInv(G,P)\<in>End(G,P)"
proof-
  {
    fix s t assume AS:"s\<in>G""t\<in>G"
    then have elinv:"s\<inverse>\<in>G""t\<inverse>\<in>G" using inverse_in_group by auto
    have "(s\<cdot>t)\<inverse>=t\<inverse>\<cdot>s\<inverse>" using group_inv_of_two AS by auto
    then have "(s\<cdot>t)\<inverse>=s\<inverse>\<cdot>t\<inverse>" using isAbelian elinv unfolding IsCommutative_def by auto
  }
  then have "\<forall>s\<in>G. \<forall>t\<in>G. GroupInv(G,P)`(s\<cdot>t)=GroupInv(G,P)`(s)\<cdot>GroupInv(G,P)`(t)" by auto
  with group0_2_T2 groupAssum show ?thesis unfolding End_def using Homomor_def by auto
qed

text\<open>The set of homomorphisms of an abelian group is an abelian subgroup of
the group of functions from a set to a group, under pointwise multiplication.\<close>

theorem(in abelian_group) end_addition_group:
  assumes "F = P {lifted to function space over} G"
  shows "IsAgroup(End(G,P),restrict(F,End(G,P)\<times>End(G,P)))" "restrict(F,End(G,P)\<times>End(G,P)){is commutative on}End(G,P)"
proof-
  from end_comp_monoid(1) monoid0.group0_1_L3A have "End(G,P)\<noteq>0" unfolding monoid0_def by auto
  moreover have "End(G,P)\<subseteq>G\<rightarrow>G" unfolding End_def by auto moreover
  have "End(G,P){is closed under}F" unfolding IsOpClosed_def using end_pointwise_addition
    assms(1) isAbelian by auto moreover
  {
    fix ff assume AS:"ff\<in>End(G,P)"
    then have "restrict(Composition(G),End(G,P)\<times>End(G,P))`\<langle>GroupInv(G,P), ff\<rangle>\<in>End(G,P)" using monoid0.group0_1_L1
      unfolding monoid0_def using end_composition(1) end_inverse_group
      by force
    then have "Composition(G)`\<langle>GroupInv(G,P), ff\<rangle>\<in>End(G,P)" using AS end_inverse_group
      by auto
    then have "GroupInv(G,P) O ff\<in>End(G,P)" using func_ZF_5_L2 AS group0_2_T2 groupAssum unfolding
      End_def by auto
    then have "GroupInv(G\<rightarrow>G,F)`ff\<in>End(G,P)" using Group_ZF_2_1_L6 assms(1) AS unfolding End_def
      by auto
  }
  then have "\<forall>ff\<in>End(G,P). GroupInv(G\<rightarrow>G,F)`ff\<in>End(G,P)" by auto ultimately
  show "IsAgroup(End(G,P),restrict(F,End(G,P)\<times>End(G,P)))" using group0.group0_3_T3 Group_ZF_2_1_T2[OF assms(1)] unfolding IsAsubgroup_def group0_def
    by auto
  show "restrict(F,End(G,P)\<times>End(G,P)){is commutative on}End(G,P)" using Group_ZF_2_1_L7[OF assms(1)] isAbelian unfolding End_def IsCommutative_def by auto
qed

lemma(in abelian_group) distributive_comp_pointwise:
  assumes "F = P {lifted to function space over} G"
  shows "IsDistributive(End(G,P),restrict(F,End(G,P)\<times>End(G,P)),restrict(Composition(G),End(G,P)\<times>End(G,P)))"
proof-
  {
    fix b c d assume AS:"b\<in>End(G,P)""c\<in>End(G,P)""d\<in>End(G,P)"
    have ig1:"Composition(G) `\<langle>b, F ` \<langle>c, d\<rangle>\<rangle> =b O (F`\<langle>c,d\<rangle>)" using monoid.Group_ZF_2_1_L0 assms(1)
      AS unfolding End_def using func_ZF_5_L2 by auto
    have ig2:"F `\<langle>Composition(G) `\<langle>b , c\<rangle>,Composition(G) `\<langle>b , d\<rangle>\<rangle>=F `\<langle>b O c,b O d\<rangle>" using AS unfolding End_def using func_ZF_5_L2 by auto
    have comp1fun:"(b O (F`\<langle>c,d\<rangle>)):G\<rightarrow>G" using monoid.Group_ZF_2_1_L0 assms(1) comp_fun AS unfolding End_def by force
    have comp2fun:"(F `\<langle>b O c,b O d\<rangle>):G\<rightarrow>G" using monoid.Group_ZF_2_1_L0 assms(1) comp_fun AS unfolding End_def by force
    {
      fix g assume gG:"g\<in>G"
      then have "(b O (F`\<langle>c,d\<rangle>))`g=b`((F`\<langle>c,d\<rangle>)`g)" using comp_fun_apply monoid.Group_ZF_2_1_L0 assms(1)
        AS(2,3) unfolding End_def by force
      also have "\<dots>=b`(c`(g)\<cdot>d`(g))" using Group_ZF_2_1_L3[OF assms(1)] AS(2,3) gG unfolding End_def by auto
      ultimately have "(b O (F`\<langle>c,d\<rangle>))`g=b`(c`(g)\<cdot>d`(g))" by auto moreover
      have "c`g\<in>G""d`g\<in>G" using AS(2,3) unfolding End_def using apply_type gG by auto
      ultimately have "(b O (F`\<langle>c,d\<rangle>))`g=(b`(c`g))\<cdot>(b`(d`g))" using AS(1) unfolding End_def
        Homomor_def[OF groupAssum groupAssum] by auto
      then have "(b O (F`\<langle>c,d\<rangle>))`g=((b O c)`g)\<cdot>((b O d)`g)" using comp_fun_apply gG AS(2,3)
        unfolding End_def by auto
      then have "(b O (F`\<langle>c,d\<rangle>))`g=(F`\<langle>b O c,b O d\<rangle>)`g" using gG Group_ZF_2_1_L3[OF assms(1) comp_fun comp_fun gG]
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
    have ig1:"Composition(G) `\<langle> F ` \<langle>c, d\<rangle>,b\<rangle> = (F`\<langle>c,d\<rangle>) O b" using monoid.Group_ZF_2_1_L0 assms(1)
      AS unfolding End_def using func_ZF_5_L2 by auto
    have ig2:"F `\<langle>Composition(G) `\<langle>c , b\<rangle>,Composition(G) `\<langle>d , b\<rangle>\<rangle>=F `\<langle>c O b,d O b\<rangle>" using AS unfolding End_def using func_ZF_5_L2 by auto
    have comp1fun:"((F`\<langle>c,d\<rangle>) O b):G\<rightarrow>G" using monoid.Group_ZF_2_1_L0 assms(1) comp_fun AS unfolding End_def by force
    have comp2fun:"(F `\<langle>c O b,d O b\<rangle>):G\<rightarrow>G" using monoid.Group_ZF_2_1_L0 assms(1) comp_fun AS unfolding End_def by force
    {
      fix g assume gG:"g\<in>G"
      then have bg:"b`g\<in>G" using AS(1) unfolding End_def using apply_type by auto
      from gG have "((F`\<langle>c,d\<rangle>) O b)`g=(F`\<langle>c,d\<rangle>)`(b`g)" using comp_fun_apply AS(1) unfolding End_def by force
      also have "\<dots>=(c`(b`g))\<cdot>(d`(b`g))" using Group_ZF_2_1_L3[OF assms(1)] AS(2,3) bg unfolding End_def by auto
      also  have "\<dots>=((c O b)`g)\<cdot>((d O b)`g)" using comp_fun_apply gG AS unfolding End_def by auto
      also have "\<dots>=(F`\<langle>c O b,d O b\<rangle>)`g" using gG Group_ZF_2_1_L3[OF assms(1) comp_fun comp_fun gG]
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

theorem(in abelian_group) end_is_ring:
  assumes "F = P {lifted to function space over} G"
  shows "IsAring(End(G,P),restrict(F,End(G,P)\<times>End(G,P)),restrict(Composition(G),End(G,P)\<times>End(G,P)))"
  unfolding IsAring_def using end_addition_group[OF assms] end_comp_monoid(1) distributive_comp_pointwise[OF assms]
  by auto

sublocale abelian_group < endo_ring:ring0 "End(G,P)" "restrict(P {lifted to function space over} G,End(G,P)\<times>End(G,P))" "restrict(Composition(G),End(G,P)\<times>End(G,P))"
  "\<lambda>x b. restrict(P {lifted to function space over} G,End(G,P)\<times>End(G,P))`\<langle>x,b\<rangle>" "\<lambda>x. GroupInv(End(G, P), restrict(P {lifted to function space over} G, End(G, P) \<times> End(G, P))) `x" 
  "\<lambda>x b. restrict(P {lifted to function space over} G, End(G, P) \<times> End(G, P)) ` \<langle>x, GroupInv(End(G, P), restrict(P {lifted to function space over} G, End(G, P) \<times> End(G, P))) ` b\<rangle>"
  "\<lambda>x b. restrict(Composition(G), End(G, P) \<times> End(G, P)) ` \<langle>x, b\<rangle>"
  "TheNeutralElement(End(G, P), restrict(P {lifted to function space over} G, End(G, P) \<times> End(G, P)))"
  "TheNeutralElement(End(G, P), restrict(Composition(G), End(G, P) \<times> End(G, P)))"
  "restrict(P {lifted to function space over} G, End(G, P) \<times> End(G, P)) `
     \<langle>TheNeutralElement
       (End(G, P), restrict(Composition(G), End(G, P) \<times> End(G, P))),
      TheNeutralElement
       (End(G, P), restrict(Composition(G), End(G, P) \<times> End(G, P)))\<rangle>"
  "\<lambda>x. restrict(Composition(G), End(G, P) \<times> End(G, P)) ` \<langle>x, x\<rangle>"
  using end_is_ring unfolding ring0_def by auto
  

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

text\<open>The preimage of a subgroup is a subgroup\<close>

theorem preimage_sub:
  assumes "IsAgroup(G,P)" 
          "IsAgroup(H,F)" 
          "Homomor(f,G,P,H,F)" 
          "f:G\<rightarrow>H"
          "IsAsubgroup(K,F)"
        shows "IsAsubgroup(f-``K,P)"
proof(rule group0.group0_3_T3)
  show "group0(G, P)" unfolding group0_def using assms(1).
  show KG:"f-``K \<subseteq> G" using func1_1_L3 assms(4) by auto
  have "f`TheNeutralElement(G,P) = TheNeutralElement(H,F)"
    using image_neutral assms(1-4) by auto
  then have "f`TheNeutralElement(G,P) \<in> K" using group0.group0_3_L5
    assms(2,5) unfolding group0_def by auto
  then have "TheNeutralElement(G,P)\<in>f-``K"
    using func1_1_L15 assms(4) assms(1) group0.group0_2_L2[of G P] unfolding group0_def
    by auto
  then show "f-``K\<noteq>0" by auto
  {
    fix x assume "x\<in>f-``K"
    then obtain y where y:"\<langle>x,y\<rangle>\<in>f" "y \<in> K" using vimage_iff by auto
    from y(1) have x:"x:G" using assms(4) unfolding Pi_def by auto
    with y(1) have "\<langle>GroupInv(G, P)`x,GroupInv(H, F)`y\<rangle>\<in>f" using 
        image_inv[OF assms(1-4), of x]
      apply_Pair[OF assms(4), of x] assms(4)
      apply_Pair[OF assms(4) group0.inverse_in_group[of G P x]] 
      assms(1)
      unfolding Pi_def function_def group0_def by force
    moreover have "GroupInv(H, F)`y \<in> K" using group0.group0_3_T3A
      assms(2,5) y(2) unfolding group0_def by auto
    ultimately have "GroupInv(G, P)`x \<in>f-``K" using vimage_iff by auto
  }
  then show "\<forall>x\<in>f -`` K. GroupInv(G, P) ` x \<in> f -`` K" by auto
  {
    fix x y assume as:"x:f-``K" "y:f-``K"
    then obtain x1 y1 where xy1:"\<langle>x,x1\<rangle>\<in>f" "x1\<in>K" "\<langle>y,y1\<rangle>\<in>f" "y1\<in>K"
      using vimage_iff by auto
    have "f`(P`\<langle>x,y\<rangle>) = F`\<langle>f`x,f`y\<rangle>" using homomor_eq[OF assms(1-3)]
      as KG by auto moreover
    from assms(4) xy1(3) apply_Pair[OF assms(4), of y]
    have "y1=f`y" unfolding Pi_def function_def by blast moreover
    from assms(4) xy1(1) apply_Pair[OF assms(4), of x]
    have "x1=f`x" unfolding Pi_def function_def by blast ultimately
    have "f`(P`\<langle>x,y\<rangle>) = F`\<langle>x1,y1\<rangle>" by auto
    with xy1(2,4) have "f`(P`\<langle>x,y\<rangle>) \<in> K" using group0.group0_3_L6
      assms(2,5) unfolding group0_def by auto
    then have "P`\<langle>x,y\<rangle>:f-``K" using func1_1_L15[OF assms(4)]
      using group0.group_op_closed as KG unfolding group0_def
      using assms(1) by auto
  }
  then show "f -`` K {is closed under} P" unfolding IsOpClosed_def by auto
qed

text\<open>The preimage of a normal subgroup is normal\<close>

theorem preimage_normal_subgroup:
  assumes  "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)" "f:G\<rightarrow>H"
          "IsAnormalSubgroup(H,F,K)"
        shows "IsAnormalSubgroup(G,P,f-``K)"
proof (rule group0.cont_conj_is_normal)
  show "group0(G,P)" unfolding group0_def using assms(1).
  show "IsAsubgroup(f-``K,P)" using preimage_sub assms unfolding IsAnormalSubgroup_def
    by auto
  {
    fix g assume g:"g\<in>G"
    {
      fix h assume "h:{P ` \<langle>g, P ` \<langle>h, GroupInv(G, P) ` g\<rangle>\<rangle> . h \<in> f -`` K}"
      then obtain k where k:"h = P ` \<langle>g, P ` \<langle>k, GroupInv(G, P) ` g\<rangle>\<rangle>" "k\<in> f -`` K" by auto
      from k(1) have "f`h = f`(P ` \<langle>g, P ` \<langle>k, GroupInv(G, P) ` g\<rangle>\<rangle>)" by auto
      moreover have "k:G" using k(2) assms(4) vimage_iff unfolding Pi_def by auto
      moreover note g
      ultimately have f:"f`h = F`\<langle>f`g,F`\<langle>f`k,GroupInv(H,F)`(f`g)\<rangle>\<rangle>"
        using group0.group_op_closed[of G P] group0.inverse_in_group[of G P]
        image_inv[OF assms(1-4)] homomor_eq[OF assms(1-3)]
        assms(1) unfolding group0_def by auto
      from g k have hg:"h:G" using group0.group_op_closed[of G P]
        group0.inverse_in_group[of G P] func1_1_L15[OF assms(4)] assms(1)
        unfolding group0_def by auto
      from k(2) have fk:"f`k:K" using func1_1_L15[OF assms(4)] by auto
      moreover have fg:"f`g:H" using apply_type[OF assms(4)] g by auto
      ultimately have "F`\<langle>F`\<langle>f`g,f`k\<rangle>,GroupInv(H,F)`(f`g)\<rangle> \<in>K"
        using assms(5) unfolding IsAnormalSubgroup_def by auto
      then have "f`h \<in>K" using group0.group_oper_assoc[of H F "f`g" "f`k"]
        fk fg f assms(2,5) group0.group0_3_L2[of H F K]
        group0.inverse_in_group[of H F "f`g"]
        unfolding group0_def IsAnormalSubgroup_def by auto
      then have "h:f-``K" using func1_1_L15[OF assms(4)] hg by auto
    }
    then have "{P ` \<langle>g, P ` \<langle>h, GroupInv(G, P) ` g\<rangle>\<rangle> . h \<in> f -`` K} \<subseteq> f -`` K" by auto
  }
  then show "\<forall>g\<in>G. {P ` \<langle>g, P ` \<langle>h, GroupInv(G, P) ` g\<rangle>\<rangle> . h \<in> f -`` K} \<subseteq> f -`` K" by auto
qed        

text\<open>The kernel of an homomorphism is a normal subgroup.\<close>

corollary kerner_normal_sub:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)" "f:G\<rightarrow>H"
  shows "IsAnormalSubgroup(G,P,f-``{TheNeutralElement(H,F)})"
  using preimage_normal_subgroup[OF assms]
    group0.trivial_normal_subgroup[of H F] unfolding group0_def
  using assms(2) by auto

text\<open>The image of a subgroup is a subgroup\<close>

theorem image_subgroup:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" 
    "Homomor(f,G,P,H,F)" "f:G\<rightarrow>H" "IsAsubgroup(K,P)"
  shows "IsAsubgroup(f``K,F)"
proof(rule group0.group0_3_T3)
  have sub:"K\<subseteq>G" using group0.group0_3_L2[of G P K] assms(1,5) unfolding group0_def by auto
  show "group0(H,F)" using assms(2) unfolding group0_def.
  show "f``K \<subseteq> H" using func_imagedef[OF assms(4)] sub apply_type[OF assms(4)] by auto
  have "TheNeutralElement(G,P) :  K" using group0.group0_3_L5
    assms(1,5) unfolding group0_def by auto
  then have "f`TheNeutralElement(G,P) \<in>f``K" using func_imagedef[OF assms(4)]
    sub by auto
  then show "f``K \<noteq> 0" by auto
  {
    fix x assume x:"x:f``K"
    then obtain q where q:"q:K" "x=f`q" using func_imagedef[OF assms(4)] sub by auto
    then have "GroupInv(H,F)`x = f`(GroupInv(G,P)`q)" using 
      image_inv[OF assms(1-4)] sub by auto
    then have "GroupInv(H,F)`x:f``K" using group0.group0_3_T3A[of G P K q]
      assms(1,5) q(1) func_imagedef[OF assms(4)] sub unfolding group0_def by auto
  }
  then show "\<forall>x\<in>f `` K. GroupInv(H, F) ` x \<in> f `` K" by auto
  {
    fix x y assume "x:f``K" "y:f``K"
    then obtain qx qy where q:"qx:K" "x=f`qx" "qy:K" "y=f`qy" using func_imagedef[OF assms(4)] sub by auto
    then have "F`\<langle>x,y\<rangle> = f`(P`\<langle>qx,qy\<rangle>)" using homomor_eq[OF assms(1-3), of qx qy] sub by force
    moreover from q(1,3) have "P`\<langle>qx,qy\<rangle>:K" using group0.group0_3_L6
      assms(1,5) unfolding group0_def by auto
    ultimately have "F`\<langle>x,y\<rangle> \<in>f``K" using func_imagedef[OF assms(4)] sub by auto
  }
  then show "f `` K {is closed under} F" unfolding IsOpClosed_def by auto
qed

corollary image_group:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)" "f:G\<rightarrow>H"
  shows "IsAsubgroup(f``G,F)"
proof-
  have "restrict(P,G\<times>G)=P" using group0.group_oper_fun[of G P] restrict_idem assms(1)
    unfolding Pi_def group0_def by auto
  then have "IsAsubgroup(G,P)" unfolding IsAsubgroup_def using assms(1) by auto
  then show ?thesis using image_subgroup[OF assms, of G] by auto
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
  have H:"IsAgroup(f``G, restrict(F,f``G\<times>f``G))" using image_group[OF assms(1-4)] unfolding IsAsubgroup_def .
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
      group0.group0_3_T1[OF _ image_group[OF assms(1-4)]] assms(2) unfolding group0_def by auto
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

text\<open>A very important homomorphism is given by taken every element
to its class in a group quotient\<close>

lemma (in group0) quotient_map:
  assumes "IsAnormalSubgroup(G,P,H)"
  defines "r \<equiv> QuotientGroupRel(G,P,H)" and "q \<equiv> \<lambda>x\<in>G. QuotientGroupRel(G,P,H)``{x}"
  shows "Homomor(q,G,P,G//r,QuotientGroupOp(G,P,H))"
  unfolding r_def Homomor_def[OF groupAssum Group_ZF_2_4_T1[OF groupAssum assms(1)]]
proof(safe)
  fix x y assume as:"x\<in>G" "y\<in>G"
  then have "x\<cdot>y\<in>G" using group_op_closed by auto
  then have "q`(x\<cdot>y) = r``{x\<cdot>y}" unfolding q_def
    using lam_funtype lamE unfolding r_def by auto
  then have "q`(x\<cdot>y) = QuotientGroupOp(G,P,H)`\<langle>r``{x},r``{y}\<rangle>"
    using EquivClass_1_L10[OF Group_ZF_2_4_L3 _ as]
    Group_ZF_2_4_L5A[OF groupAssum assms(1)] assms(1)
    unfolding IsAnormalSubgroup_def QuotientGroupOp_def
    r_def by auto
  then show "q`(P`\<langle>x,y\<rangle>) = QuotientGroupOp(G, P, H) ` \<langle>q ` x, q ` y\<rangle>"
    unfolding q_def r_def using lam_funtype lamE as by auto
qed

text\<open>In the context of \<open>group0\<close>, we may use all results of \<open>semigr0\<close>.\<close>

sublocale group0 < semigroup:semigr0 G P groper "\<lambda>x. Fold1(P,x)" Append Concat  
  unfolding semigr0_def using groupAssum IsAgroup_def IsAmonoid_def by auto

end