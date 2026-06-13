(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2013-2026 Daniel de la Concepcion

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

section \<open>Endomorphisms of abelian groups\<close>

theory Group_ZF_5 imports Group_ZF_4 Ring_ZF Semigroup_ZF

begin

text\<open>When the operation $P$ in the group $(G,P)$ is commutative (i.e. the group the abelian)
  the space \<open>End(G,P)\<close> of homomorphisms of a group $(G,P)$ into itself has a nice structure.\<close>

subsection\<open>First ring of endomorphisms of an abelian group\<close>

text\<open>In this section we show that for an abelian group $(G,P)$ the space \<open>End(G,P)\<close> 
  (defined in the \<open>Group_ZF_2\<close> theory) forms a ring.\<close>

text\<open>The set of endomorphisms is closed under pointwise addition (derived from the group operation).
   This is so because the group is abelian.\<close>
  
theorem (in abelian_group) end_pointwise_addition:
  assumes "f\<in>End(G,P)" "g\<in>End(G,P)" 
  defines "F \<equiv> P {lifted to function space over} G"
  shows "F`\<langle>f,g\<rangle> \<in> End(G,P)"
proof-
  from assms(1,2) have fun: "f:G\<rightarrow>G" "g\<in>G\<rightarrow>G" unfolding End_def by simp_all
  with assms(3) have fun2: "F`\<langle>f,g\<rangle>:G\<rightarrow>G" 
    using monoid0.Group_ZF_2_1_L0 group0_2_L1 by simp
  { fix g\<^sub>1 g\<^sub>2 assume "g\<^sub>1\<in>G" "g\<^sub>2\<in>G"
    with isAbelian assms fun have 
      "(F`\<langle>f,g\<rangle>)`(g\<^sub>1\<cdot>g\<^sub>2) = (F`\<langle>f,g\<rangle>)`(g\<^sub>1)\<cdot>(F`\<langle>f,g\<rangle>)`(g\<^sub>2)"
      using Group_ZF_2_1_L3 group_op_closed endomor_eq
        apply_type group0_4_L8(3) Group_ZF_2_1_L3 by simp
  } with fun2 show ?thesis using eq_endomor by simp
qed

text\<open>The value of a product of endomorphisms on a group element is the product of values.\<close>

lemma (in abelian_group) end_pointwise_add_val:
  assumes "f\<in>End(G,P)" "g\<in>End(G,P)" "x\<in>G" "F = P {lifted to function space over} G"
  shows "(InEnd(F,G,P)`\<langle>f,g\<rangle>)`(x) = (f`(x))\<cdot>(g`(x))"
  using assms group_oper_fun monoid.group0_1_L3B func_ZF_1_L4 
  unfolding End_def by simp

text\<open>The operation of taking the inverse in an abelian group is an endomorphism.\<close>

lemma (in abelian_group) end_inverse_group:
  shows "GroupInv(G,P) \<in> End(G,P)"
  using inverse_in_group group_inv_of_two isAbelian IsCommutative_def 
    group0_2_T2 groupAssum Homomor_def 
  unfolding End_def IsMorphism_def by simp

text\<open>The set of homomorphisms of an abelian group is an abelian subgroup of
  the group of functions from a set to a group, under pointwise addition.\<close>

theorem (in abelian_group) end_addition_group:
  assumes "F = P {lifted to function space over} G"
  shows "IsAgroup(End(G,P),InEnd(F,G,P))" and
    "InEnd(F,G,P) {is commutative on} End(G,P)"
proof-
  have "End(G,P)\<noteq>0" using end_comp_monoid(1) monoid0.group0_1_L3A 
    unfolding monoid0_def by auto
  moreover have "End(G,P) \<subseteq> G\<rightarrow>G" unfolding End_def by auto 
  moreover from isAbelian assms(1) have "End(G,P){is closed under} F" 
    unfolding IsOpClosed_def using end_pointwise_addition by auto 
  moreover from groupAssum assms(1) have 
    "\<forall>f\<in>End(G,P). GroupInv(G\<rightarrow>G,F)`(f) \<in> End(G,P)"
    using monoid0.group0_1_L1 end_composition(1) end_inverse_group 
      func_ZF_5_L2 group0_2_T2 Group_ZF_2_1_L6 
    unfolding monoid0_def End_def by force
  ultimately show "IsAgroup(End(G,P),InEnd(F,G,P))" 
    using assms(1) group0.group0_3_T3 Group_ZF_2_1_T2 
    unfolding IsAsubgroup_def group0_def by blast
  from assms(1) isAbelian show 
    "InEnd(F,G,P) {is commutative on} End(G,P)" 
    using Group_ZF_2_1_L7 unfolding End_def IsCommutative_def by auto
qed

text\<open>Endomorphisms form a subgroup of the space of functions that map the group to itself.\<close>

lemma (in abelian_group) end_addition_subgroup:
  shows "IsAsubgroup(End(G,P),P {lifted to function space over} G)"
  using end_addition_group unfolding IsAsubgroup_def by simp

text\<open>The neutral element of the group of endomorphisms of a group is the constant function 
  with value equal to the neutral element of the group.\<close>

lemma (in abelian_group) end_add_neut_elem:
  assumes "F = P {lifted to function space over} G"
  shows "TheNeutralElement(End(G,P),InEnd(F,G,P)) = ConstantFunction(G,\<one>)"
  using assms end_addition_subgroup lift_group_subgr_neut by simp

text\<open>For the endomorphisms of a group $G$ the group operation lifted to the function space 
  over $G$ is distributive with respect to the composition operation. \<close>

lemma (in abelian_group) distributive_comp_pointwise:
  assumes "F = P {lifted to function space over} G"
  shows 
    "IsDistributive(End(G,P),InEnd(F,G,P),InEnd(Composition(G),G,P))"
proof -
  let ?C\<^sub>G = "Composition(G)"
  let ?C\<^sub>E = "InEnd(?C\<^sub>G,G,P)"
  let ?F\<^sub>E = "InEnd(F,G,P)"
  { fix b c d assume AS: "b\<in>End(G,P)" "c\<in>End(G,P)" "d\<in>End(G,P)"
    with assms(1) have ig1: "?C\<^sub>G`\<langle>b,F`\<langle>c, d\<rangle>\<rangle> = b O (F`\<langle>c,d\<rangle>)" 
      using monoid.Group_ZF_2_1_L0 func_ZF_5_L2 unfolding End_def 
      by auto
    with AS have ig2: "F`\<langle>?C\<^sub>G`\<langle>b,c\<rangle>,?C\<^sub>G `\<langle>b,d\<rangle>\<rangle> = F`\<langle>b O c,b O d\<rangle>" 
      unfolding End_def using func_ZF_5_L2 by auto
    from assms(1) AS have comp1fun: "(b O (F`\<langle>c,d\<rangle>)):G\<rightarrow>G" 
      using monoid.Group_ZF_2_1_L0 comp_fun unfolding End_def by force
    from assms(1) AS have comp2fun: "(F `\<langle>b O c,b O d\<rangle>) : G\<rightarrow>G" 
      using monoid.Group_ZF_2_1_L0 comp_fun unfolding End_def by force
    { fix g assume "g\<in>G"
      with assms(1) AS(2,3) have "(b O (F`\<langle>c,d\<rangle>))`(g) = b`((F`\<langle>c,d\<rangle>)`(g))" 
        using comp_fun_apply monoid.Group_ZF_2_1_L0 unfolding End_def 
        by force
      with groupAssum assms(1) AS \<open>g\<in>G\<close> have 
        "(b O (F`\<langle>c,d\<rangle>))`(g) = (F`\<langle>b O c,b O d\<rangle>)`(g)"
        using Group_ZF_2_1_L3 apply_type homomor_eq comp_fun 
        unfolding End_def by auto
    } hence "\<forall>g\<in>G. (b O (F`\<langle>c,d\<rangle>))`(g) = (F`\<langle>b O c,b O d\<rangle>)`(g)" by simp
    with comp1fun comp2fun ig1 ig2 have 
      "?C\<^sub>G`\<langle>b,F`\<langle>c, d\<rangle>\<rangle> = F`\<langle>?C\<^sub>G`\<langle>b , c\<rangle>,?C\<^sub>G`\<langle>b,d\<rangle>\<rangle>"
      using func_eq by simp
    moreover from AS(2,3) have "F`\<langle>c, d\<rangle> = ?F\<^sub>E`\<langle>c, d\<rangle>" 
      using restrict by simp
    moreover from AS have "?C\<^sub>G`\<langle>b,c\<rangle> = ?C\<^sub>E`\<langle>b,c\<rangle>" and "?C\<^sub>G`\<langle>b,d\<rangle> = ?C\<^sub>E`\<langle>b,d\<rangle>"
      using restrict by auto 
    moreover from assms AS have "?C\<^sub>G`\<langle>b,F `\<langle>c,d\<rangle>\<rangle> = ?C\<^sub>E`\<langle>b, F`\<langle>c, d\<rangle>\<rangle>"
      using end_pointwise_addition by simp
    moreover from AS have "F`\<langle>?C\<^sub>G`\<langle>b,c\<rangle>,?C\<^sub>G`\<langle>b,d\<rangle>\<rangle> = ?F\<^sub>E`\<langle>?C\<^sub>G `\<langle>b,c\<rangle>,?C\<^sub>G `\<langle>b,d\<rangle>\<rangle>"
      using end_composition by simp
    ultimately have eq1: "?C\<^sub>E`\<langle>b, ?F\<^sub>E`\<langle>c,d\<rangle>\<rangle> = ?F\<^sub>E `\<langle>?C\<^sub>E`\<langle>b,c\<rangle>,?C\<^sub>E`\<langle>b,d\<rangle>\<rangle>"
      by simp
    from assms(1) AS have 
      compfun: "(F`\<langle>c,d\<rangle>) O b : G\<rightarrow>G" "F`\<langle>c O b,d O b\<rangle> : G\<rightarrow>G" 
      using monoid.Group_ZF_2_1_L0 comp_fun unfolding End_def by auto
    { fix g assume "g\<in>G"
      with AS(1) have bg: "b`(g) \<in> G" unfolding End_def using apply_type 
        by auto
      from \<open>g\<in>G\<close> AS(1) have "((F`\<langle>c,d\<rangle>) O b)`g = (F`\<langle>c,d\<rangle>)`(b`(g))" 
        using comp_fun_apply  unfolding End_def by force
      also from assms(1) AS(2,3) bg have "\<dots> = (c`(b`(g)))\<cdot>(d`(b`(g)))" 
        using Group_ZF_2_1_L3 unfolding End_def by auto
      also from \<open>g\<in>G\<close> AS have "\<dots> = ((c O b)`(g))\<cdot>((d O b)`(g))" 
        using comp_fun_apply unfolding End_def by auto
      also from assms(1) \<open>g\<in>G\<close> AS have "\<dots> = (F`\<langle>c O b,d O b\<rangle>)`g" 
        using comp_fun Group_ZF_2_1_L3 unfolding End_def by auto
      finally have "((F`\<langle>c,d\<rangle>) O b)`(g) = (F`\<langle>c O b,d O b\<rangle>)`(g)" by simp
    } hence "\<forall>g\<in>G. ((F`\<langle>c,d\<rangle>) O b)`(g) = (F`\<langle>c O b,d O b\<rangle>)`(g)" by simp
    with compfun have "(F`\<langle>c,d\<rangle>) O b = F`\<langle>c O b,d O b\<rangle>" 
      using func_eq by blast
    with assms(1) AS have "?C\<^sub>G`\<langle>F`\<langle>c,d\<rangle>,b\<rangle> = F`\<langle>?C\<^sub>G`\<langle>c,b\<rangle>,?C\<^sub>G`\<langle>d , b\<rangle>\<rangle>"
      using monoid.Group_ZF_2_1_L0 func_ZF_5_L2 unfolding End_def 
      by simp
    moreover from AS(2,3) have "F`\<langle>c, d\<rangle> = ?F\<^sub>E`\<langle>c, d\<rangle>" 
      using restrict by simp 
    moreover from AS have "?C\<^sub>G`\<langle>c,b\<rangle> = ?C\<^sub>E`\<langle>c , b\<rangle>" "?C\<^sub>G`\<langle>d,b\<rangle> = ?C\<^sub>E`\<langle>d,b\<rangle>"
      using restrict by auto 
    moreover from assms AS have "?C\<^sub>G`\<langle>F`\<langle>c,d\<rangle>,b\<rangle> = ?C\<^sub>E`\<langle>F`\<langle>c,d\<rangle>,b\<rangle>" 
      using end_pointwise_addition by auto
    moreover from AS have "F`\<langle>?C\<^sub>G`\<langle>c,b\<rangle>,?C\<^sub>G`\<langle>d,b\<rangle>\<rangle> = ?F\<^sub>E`\<langle>?C\<^sub>G`\<langle>c,b\<rangle>,?C\<^sub>G`\<langle>d,b\<rangle>\<rangle>"
      using end_composition by auto 
    ultimately have "?C\<^sub>E`\<langle>?F\<^sub>E`\<langle>c,d\<rangle>,b\<rangle> = ?F\<^sub>E`\<langle>?C\<^sub>E`\<langle>c,b\<rangle>,?C\<^sub>E`\<langle>d,b\<rangle>\<rangle>"
      by auto
    with eq1 have "(?C\<^sub>E`\<langle>b, ?F\<^sub>E`\<langle>c, d\<rangle>\<rangle> = ?F\<^sub>E`\<langle>?C\<^sub>E`\<langle>b,c\<rangle>,?C\<^sub>E`\<langle>b,d\<rangle>\<rangle>) \<and>
      (?C\<^sub>E`\<langle>?F\<^sub>E`\<langle>c,d\<rangle>,b\<rangle> = ?F\<^sub>E`\<langle>?C\<^sub>E`\<langle>c,b\<rangle>,?C\<^sub>E`\<langle>d,b\<rangle>\<rangle>)"
      by auto
  } then show ?thesis unfolding IsDistributive_def by auto
qed

text\<open>The endomorphisms of an abelian group is in fact a ring with the previous operations.\<close>

theorem (in abelian_group) end_is_ring:
  assumes "F = P {lifted to function space over} G"
  shows 
    "IsAring(End(G,P),InEnd(F,G,P),InEnd(Composition(G),G,P))"
  using assms end_addition_group end_comp_monoid(1) distributive_comp_pointwise
  unfolding IsAring_def by auto

text\<open>The theorems proven in the \<open>ring0\<close> context are valid in the \<open>abelian_group\<close> context
   as applied to the endomorphisms of $G$.  \<close>

sublocale abelian_group < endo_ring: ring0 
  "End(G,P)" 
  "InEnd(P {lifted to function space over} G,G,P)" 
  "InEnd(Composition(G),G,P)"
  "\<lambda>x b. InEnd(P {lifted to function space over} G,G,P)`\<langle>x,b\<rangle>" 
  "\<lambda>x. GroupInv(End(G, P), InEnd(P {lifted to function space over} G,G,P))`(x)" 
  "\<lambda>x b. InEnd(P {lifted to function space over} G,G,P)`\<langle>x, GroupInv(End(G, P), InEnd(P {lifted to function space over} G,G,P))`(b)\<rangle>"
  "\<lambda>x b. InEnd(Composition(G),G,P)`\<langle>x, b\<rangle>"
  "TheNeutralElement(End(G, P),InEnd(P {lifted to function space over} G,G,P))"
  "TheNeutralElement(End(G, P),InEnd(Composition(G),G,P))"
  "InEnd(P {lifted to function space over} G,G,P)`
     \<langle>TheNeutralElement (End(G, P), InEnd(Composition(G),G,P)),
      TheNeutralElement (End(G, P), InEnd(Composition(G),G,P))\<rangle>"
  "\<lambda>x. InEnd(Composition(G),G,P)`\<langle>x, x\<rangle>"
  "\<lambda>s. Fold(InEnd(P {lifted to function space over} G,G,P), TheNeutralElement(End(G, P), InEnd(P {lifted to function space over} G,G,P)),s)"
  "\<lambda>n x. Fold(InEnd(P {lifted to function space over} G,G,P), TheNeutralElement(End(G, P), InEnd(P {lifted to function space over} G,G,P)),{\<langle>k,x\<rangle>. k\<in>n})"
  "\<lambda>s. Fold(InEnd(Composition(G),G,P), TheNeutralElement(End(G, P), InEnd(Composition(G),G,P)),s)"
  "\<lambda>n x. Fold(InEnd(Composition(G),G,P), TheNeutralElement(End(G, P), InEnd(Composition(G),G,P)),{\<langle>k,x\<rangle>. k\<in>n})"
  using end_is_ring unfolding ring0_def by blast

text\<open>In the context of \<open>group0\<close>, we may use all results of \<open>semigr0\<close>.\<close>

sublocale group0 < semigroup:semigr0 G P groper "\<lambda>x. Fold1(P,x)" Append Concat
  unfolding semigr0_def using groupAssum IsAgroup_def IsAmonoid_def by auto

end
