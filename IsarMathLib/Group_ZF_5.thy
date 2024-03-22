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

text\<open>In this theory we study group homomorphisms.\<close>

subsection\<open>Homomorphisms\<close>

text\<open>A homomorphism is a function between groups that preserves the group operations.\<close>

text\<open>In general we may have a homomorphism not only between groups, but also between various 
  algebraic structures with one operation like magmas, semigroups, quasigroups, loops and monoids. 
  In all cases the homomorphism is defined by using the morphism property. In the 
  multiplicative notation we we will write that $f$ has a morphism property if 
  $f(x\cdot_G y) = f(x)\cdot_H f(y)$ for all $x,y\in G$. Below we write this definition 
  in raw set theory notation and use the expression \<open>IsMorphism\<close> instead of the possible, but longer
  \<open>HasMorphismProperty\<close>. \<close>

definition 
  "IsMorphism(G,P,F,f) \<equiv> \<forall>g\<^sub>1\<in>G. \<forall>g\<^sub>2\<in>G. f`(P`\<langle>g\<^sub>1,g\<^sub>2\<rangle>) = F`\<langle>f`(g\<^sub>1),f`(g\<^sub>2)\<rangle>"

text\<open>A function $f:G\rightarrow H$ between algebraic structures 
  $(G,\cdot_G)$ and $(H,\cdot_H)$ with one operation (each) is a homomorphism is it has the morphism
  property. \<close> 

definition
  "Homomor(f,G,P,H,F) \<equiv> f:G\<rightarrow>H \<and> IsMorphism(G,P,F,f)"

text\<open>Now a lemma about the definition:\<close>

lemma homomor_eq:
  assumes "Homomor(f,G,P,H,F)" "g\<^sub>1\<in>G" "g\<^sub>2\<in>G"
  shows "f`(P`\<langle>g\<^sub>1,g\<^sub>2\<rangle>) = F`\<langle>f`(g\<^sub>1),f`(g\<^sub>2)\<rangle>"
  using assms unfolding Homomor_def IsMorphism_def by auto

text\<open>An endomorphism is a homomorphism from a group to the same group. In case
the group is abelian, it has a nice structure.\<close>

definition
  "End(G,P) \<equiv> {f\<in>G\<rightarrow>G. Homomor(f,G,P,G,P)}"

text\<open>The defining property of an endomorphism written in notation used in \<open>group0\<close> context:\<close>

lemma (in group0) endomor_eq: assumes "f \<in> End(G,P)" "g\<^sub>1\<in>G" "g\<^sub>2\<in>G"
  shows "f`(g\<^sub>1\<cdot>g\<^sub>2) = f`(g\<^sub>1)\<cdot>f`(g\<^sub>2)"
  using assms homomor_eq unfolding End_def by auto

text\<open>A function that maps a group $G$ into itself and satisfies 
  $f(g_1\cdot g2) = f(g_1)\cdot f(g_2)$ is an endomorphism.\<close>

lemma (in group0) eq_endomor: 
  assumes "f:G\<rightarrow>G" and "\<forall>g\<^sub>1\<in>G. \<forall>g\<^sub>2\<in>G. f`(g\<^sub>1\<cdot>g\<^sub>2)=f`(g\<^sub>1)\<cdot>f`(g\<^sub>2)"
  shows "f \<in> End(G,P)"
  using assms  unfolding End_def Homomor_def IsMorphism_def by simp

text\<open>The set of endomorphisms forms a submonoid of the monoid of function
from a set to that set under composition.\<close>

lemma (in group0) end_composition:
  assumes "f\<^sub>1\<in>End(G,P)" "f\<^sub>2\<in>End(G,P)"
  shows "Composition(G)`\<langle>f\<^sub>1,f\<^sub>2\<rangle> \<in> End(G,P)"
proof-
  from assms have fun: "f\<^sub>1:G\<rightarrow>G" "f\<^sub>2:G\<rightarrow>G" unfolding End_def by auto
  then have "f\<^sub>1 O f\<^sub>2:G\<rightarrow>G" using comp_fun by auto
  from assms fun(2) have 
    "\<forall>g\<^sub>1\<in>G. \<forall>g\<^sub>2\<in>G. (f\<^sub>1 O f\<^sub>2)`(g\<^sub>1\<cdot>g\<^sub>2) = ((f\<^sub>1 O f\<^sub>2)`(g\<^sub>1))\<cdot>((f\<^sub>1 O f\<^sub>2)`(g\<^sub>2))"
    using group_op_closed comp_fun_apply endomor_eq apply_type 
    by simp    
  with fun \<open>f\<^sub>1 O f\<^sub>2:G\<rightarrow>G\<close> show ?thesis using eq_endomor func_ZF_5_L2 
    by simp
qed

text\<open>We will use some binary operations that are naturally defined on the function space 
   $G\rightarrow G$, but we consider them restricted to the endomorphisms of $G$.
  To shorten the notation in such case we define an abbreviation \<open>InEnd(F,G,P)\<close> 
  which restricts a binary operation $F$ to the set of endomorphisms of $G$. \<close>

abbreviation InEnd("_ {in End} [_,_]")
  where "InEnd(F,G,P) \<equiv> restrict(F,End(G,P)\<times>End(G,P))"

text\<open>Endomoprhisms of a group form a monoid with composition as the binary operation,
  with the identity map as the neutral element.\<close>

theorem (in group0) end_comp_monoid:
  shows "IsAmonoid(End(G,P),InEnd(Composition(G),G,P))"
  and "TheNeutralElement(End(G,P),InEnd(Composition(G),G,P)) = id(G)"
proof -
  let ?C\<^sub>0 = "InEnd(Composition(G),G,P)"
  have fun: "id(G):G\<rightarrow>G" unfolding id_def by auto
  { fix g h assume "g\<in>G""h\<in>G"
    then have "id(G)`(g\<cdot>h)=(id(G)`g)\<cdot>(id(G)`h)"
      using group_op_closed by simp
  } 
  with groupAssum fun have "id(G) \<in> End(G,P)" using eq_endomor by simp 
  moreover  have A0: "id(G)=TheNeutralElement(G \<rightarrow> G, Composition(G))" 
    using Group_ZF_2_5_L2(2) by auto 
  ultimately have A1: "TheNeutralElement(G \<rightarrow> G, Composition(G)) \<in> End(G,P)" by auto 
  moreover have A2: "End(G,P) \<subseteq> G\<rightarrow>G" unfolding End_def by blast 
  moreover have A3: "End(G,P) {is closed under} Composition(G)" 
    using end_composition unfolding IsOpClosed_def by blast
  ultimately show "IsAmonoid(End(G,P),?C\<^sub>0)" 
    using monoid0.group0_1_T1 Group_ZF_2_5_L2(1) unfolding monoid0_def
    by blast
  have "IsAmonoid(G\<rightarrow>G,Composition(G))" using Group_ZF_2_5_L2(1) by auto
  with A0 A1 A2 A3 show "TheNeutralElement(End(G,P),?C\<^sub>0) = id(G)"
    using group0_1_L6 by auto
qed

text\<open>The set of endomorphisms is closed under pointwise addition (derived from the group operation).
   This is so because the group is abelian.\<close>
  
theorem (in abelian_group) end_pointwise_addition:
  assumes "f\<in>End(G,P)" "g\<in>End(G,P)" "F = P {lifted to function space over} G"
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

text\<open>The inverse of an abelian group is an endomorphism.\<close>

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
    with assms(1) have ig1: "?C\<^sub>G `\<langle>b, F ` \<langle>c, d\<rangle>\<rangle> = b O (F`\<langle>c,d\<rangle>)" 
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

text\<open>The endomorphisms of an abelian group is in fact a ring with the previous
  operations.\<close>

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
  using end_is_ring unfolding ring0_def by blast

subsection\<open>First isomorphism theorem\<close>

text\<open>Now we will prove that any homomorphism $f:G\to H$ defines a bijective
  homomorphism between $G/H$ and $f(G)$.\<close>
  
text\<open>A group homomorphism sends the neutral element to the neutral element.\<close>

lemma image_neutral:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)"
  shows "f`(TheNeutralElement(G,P)) = TheNeutralElement(H,F)"
proof -
  let ?e\<^sub>G = "TheNeutralElement(G,P)"
  let ?e\<^sub>H = "TheNeutralElement(H,F)"
  from assms(3) have ff: "f:G\<rightarrow>H"
    unfolding Homomor_def by simp
  have g: "?e\<^sub>G = P`\<langle>?e\<^sub>G,?e\<^sub>G\<rangle>" "?e\<^sub>G \<in> G"
    using assms(1) group0.group0_2_L2 unfolding group0_def by simp_all
  with assms have "f`(?e\<^sub>G) = F`\<langle>f`(?e\<^sub>G),f`(?e\<^sub>G)\<rangle>"
    unfolding Homomor_def IsMorphism_def by force
  moreover
  from ff g(2) have h: "f`(?e\<^sub>G) \<in> H" using apply_type 
    by simp
  with assms(2) have "f`(?e\<^sub>G) = F`\<langle>f`(?e\<^sub>G),?e\<^sub>H\<rangle>"
    using group0.group0_2_L2 unfolding group0_def by simp 
  ultimately have "F`\<langle>f`(?e\<^sub>G),?e\<^sub>H\<rangle> = F`\<langle>f`(?e\<^sub>G),f`(?e\<^sub>G)\<rangle>" 
    by simp
  with assms(2) h have 
    "LeftTranslation(H,F,f`(?e\<^sub>G))`(?e\<^sub>H) = LeftTranslation(H,F,f`(?e\<^sub>G))`(f`(?e\<^sub>G))"
    using group0.group0_5_L2(2) group0.group0_2_L2 unfolding group0_def 
      by simp
  moreover from assms(2) h have "LeftTranslation(H,F,f`(?e\<^sub>G))\<in>inj(H,H)"
      using group0.trans_bij(2) unfolding group0_def bij_def
      by simp
  ultimately show ?thesis using h assms(2) group0.group0_2_L2 
    unfolding inj_def group0_def by force
qed

text\<open>If $f:G\rightarrow H$ is a homomorphism, then it commutes with the inverse \<close>

lemma image_inv:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)" "g\<in>G"
  shows "f`(GroupInv(G,P)`(g)) = GroupInv(H,F)`(f`(g))"
proof -
  from assms(3) have ff: "f:G\<rightarrow>H"
    unfolding Homomor_def by simp
  with assms(4) have im: "f`(g)\<in>H" using apply_type by simp
  from assms(1,4) have inv: "GroupInv(G,P)`(g)\<in>G" 
    using group0.inverse_in_group unfolding group0_def by simp
  with ff have inv2: "f`(GroupInv(G,P)`g)\<in>H" using apply_type by simp
  from assms(1,4) have 
    "f`(TheNeutralElement(G,P)) = f`(P`\<langle>g,GroupInv(G,P)`(g)\<rangle>)" 
    using group0.group0_2_L6 unfolding group0_def by simp
  also from assms inv have "\<dots> = F`\<langle>f`(g),f`(GroupInv(G,P)`(g))\<rangle>" 
    unfolding Homomor_def IsMorphism_def by simp
  finally have "f`(TheNeutralElement(G,P)) = F`\<langle>f`(g),f`(GroupInv(G,P)`(g))\<rangle>"
    by simp
  with assms im inv2 show ?thesis 
    using group0.group0_2_L9 image_neutral unfolding group0_def by simp
qed

text\<open>The preimage of a subgroup is a subgroup\<close>

theorem preimage_sub:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)"
          "IsAsubgroup(K,F)"
  shows "IsAsubgroup(f-``(K),P)"
proof -
  from assms(3) have ff: "f:G\<rightarrow>H"
    unfolding Homomor_def by simp
  from assms(2) have Hgr: "group0(H,F)" unfolding group0_def by simp
  from assms(1) have Ggr: "group0(G,P)" unfolding group0_def by simp
  moreover 
  from assms ff Ggr Hgr have "TheNeutralElement(G,P) \<in> f-``(K)"
    using image_neutral group0.group0_3_L5 func1_1_L15 group0.group0_2_L2 
    by simp
  hence "f-``(K)\<noteq>0" by blast
  moreover from ff have "f-``(K) \<subseteq> G" using func1_1_L3 by simp
  moreover from assms ff Ggr Hgr have "f-``(K) {is closed under} P"
    using func1_1_L15 group0.group0_3_L6 group0.group_op_closed func1_1_L15
    unfolding IsOpClosed_def Homomor_def IsMorphism_def by simp
  moreover from assms ff Ggr Hgr have 
    "\<forall>x\<in>f-``(K). GroupInv(G, P)`(x) \<in> f-``(K)"
    using group0.group0_3_T3A image_inv func1_1_L15 
        group0.inverse_in_group by simp
  ultimately show ?thesis by (rule group0.group0_3_T3)
qed

text\<open>The preimage of a normal subgroup is normal\<close>

theorem preimage_normal_subgroup:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)"
          "IsAnormalSubgroup(H,F,K)"
        shows "IsAnormalSubgroup(G,P,f-``(K))"
proof -
  from assms(3) have ff: "f:G\<rightarrow>H"
    unfolding Homomor_def by simp
  from assms(2) have Hgr: "group0(H,F)" unfolding group0_def by simp
  with assms(4) have "K\<subseteq>H" using group0.group0_3_L2 
    unfolding IsAnormalSubgroup_def by simp
  from assms(1) have Ggr: "group0(G,P)" unfolding group0_def by simp
  moreover from assms have "IsAsubgroup(f-``(K),P)" 
    using preimage_sub unfolding IsAnormalSubgroup_def by simp
  moreover
  { fix g assume gG: "g\<in>G"
    { fix h assume "h \<in> {P`\<langle>g,P`\<langle>h, GroupInv(G, P)`(g)\<rangle>\<rangle>. h \<in> f-``(K)}"
      then obtain k where 
        k: "h = P`\<langle>g,P`\<langle>k,GroupInv(G, P)`(g)\<rangle>\<rangle>" "k \<in> f-``(K)" 
        by auto
      from k(1) have "f`(h) = f`(P`\<langle>g,P`\<langle>k, GroupInv(G, P)`(g)\<rangle>\<rangle>)" by simp
      moreover from ff k(2) have "k\<in>G" using vimage_iff 
        unfolding Pi_def by blast
      ultimately have f: "f`(h) = F`\<langle>f`(g),F`\<langle>f`(k),GroupInv(H,F)`(f`(g))\<rangle>\<rangle>"
        using assms(1-4) Ggr gG group0.group_op_closed 
          group0.inverse_in_group image_inv homomor_eq by simp
      from assms(1) ff Ggr \<open>g\<in>G\<close> k have "h\<in>G" using group0.group_op_closed
        group0.inverse_in_group func1_1_L15 by simp
      from assms(4) ff k(2) \<open>g\<in>G\<close> have "f`(k)\<in>K" "f`(g)\<in>H" and 
        "F`\<langle>F`\<langle>f`(g),f`(k)\<rangle>,GroupInv(H,F)`(f`(g))\<rangle> \<in> K"
        using func1_1_L15 apply_type unfolding IsAnormalSubgroup_def 
        by auto
      moreover from \<open>f`(k)\<in>K\<close> \<open>K\<subseteq>H\<close> Hgr f \<open>f`(g)\<in>H\<close> have
        "f`(h) = F`\<langle>F`\<langle>f`(g),f`(k)\<rangle>,GroupInv(H,F)`(f`(g))\<rangle>"
        using group0.group_oper_assoc group0.inverse_in_group by auto
      ultimately have "f`(h) \<in> K" by simp
      with ff \<open>h\<in>G\<close> have "h \<in> f-``(K)" using func1_1_L15 by simp
    } hence "{P`\<langle>g,P`\<langle>h,GroupInv(G,P)`(g)\<rangle>\<rangle>. h\<in>f-``(K)} \<subseteq> f-``(K)" 
      by blast
  } hence "\<forall>g\<in>G. {P`\<langle>g, P`\<langle>h, GroupInv(G, P)`(g)\<rangle>\<rangle>. h\<in>f-``(K)} \<subseteq> f-``(K)" 
    by simp
  ultimately show ?thesis using group0.cont_conj_is_normal by simp 
qed        

text\<open>The kernel of an homomorphism is a normal subgroup.\<close>

corollary kernel_normal_sub:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)"
  shows "IsAnormalSubgroup(G,P,f-``{TheNeutralElement(H,F)})"
  using assms preimage_normal_subgroup group0.trivial_normal_subgroup 
  unfolding group0_def by auto

text\<open>The image of a subgroup is a subgroup\<close>

theorem image_subgroup:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" 
    "Homomor(f,G,P,H,F)" "f:G\<rightarrow>H" "IsAsubgroup(K,P)"
  shows "IsAsubgroup(f``K,F)"
proof - 
  from assms(1,5) have sub: "K\<subseteq>G" using group0.group0_3_L2 
    unfolding group0_def by simp
  from assms(2) have "group0(H,F)" unfolding group0_def by simp
  moreover from assms(4) have "f``(K) \<subseteq> H" 
    using func_imagedef sub apply_type by auto
  moreover
  from assms(1,4,5) sub have "f`(TheNeutralElement(G,P)) \<in> f``(K)"
    using group0.group0_3_L5 func_imagedef unfolding group0_def 
    by auto
  hence "f``(K) \<noteq> 0" by blast
  moreover
  { fix x assume "x\<in>f``(K)"
    with assms(4) sub obtain q where q: "q\<in>K" "x=f`(q)" 
      using func_imagedef by auto
    with assms(1-4) sub have "GroupInv(H,F)`(x) = f`(GroupInv(G,P)`q)" 
      using image_inv by auto
    with assms(1,4,5) q(1) sub have "GroupInv(H,F)`(x) \<in> f``(K)" 
      using group0.group0_3_T3A func_imagedef unfolding group0_def 
      by auto
  } hence "\<forall>x\<in>f``(K). GroupInv(H, F)`(x) \<in> f``(K)" by auto
  moreover 
  { fix x y assume "x\<in>f``(K)" "y\<in>f``(K)"
    with assms(4) sub obtain q\<^sub>x q\<^sub>y where 
      q: "q\<^sub>x\<in>K" "x=f`(q\<^sub>x)" "q\<^sub>y\<in>K" "y=f`(q\<^sub>y)" 
      using func_imagedef by auto
    with assms(1-3) sub have "F`\<langle>x,y\<rangle> = f`(P`\<langle>q\<^sub>x,q\<^sub>y\<rangle>)" 
      using homomor_eq by force
    moreover from assms(1,5) q(1,3) have "P`\<langle>q\<^sub>x,q\<^sub>y\<rangle> \<in> K" 
      using group0.group0_3_L6 unfolding group0_def by simp
    ultimately have "F`\<langle>x,y\<rangle>  \<in> f``(K)" 
      using assms(4) sub func_imagedef by auto
  } then have  "f``(K) {is closed under} F" unfolding IsOpClosed_def 
    by simp
  ultimately show ?thesis using group0.group0_3_T3 by simp
qed

text\<open>The image of a group under a homomorphism is a subgroup of the target group.\<close>

corollary image_group:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)"
  shows "IsAsubgroup(f``(G),F)"
proof - 
  from assms(1) have "restrict(P,G\<times>G) = P" 
    using group0.group_oper_fun restrict_domain unfolding group0_def 
    by blast
  with assms show ?thesis using image_subgroup 
    unfolding Homomor_def IsAsubgroup_def by simp
qed

text\<open>Now we are able to prove the first isomorphism theorem. This theorem states
  that any group homomorphism $f:G\to H$ gives an isomorphism between a quotient group of $G$
  and a subgroup of $H$.\<close>

theorem isomorphism_first_theorem:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)" 
  defines "r \<equiv> QuotientGroupRel(G,P,f-``{TheNeutralElement(H,F)})" and
  "\<P> \<equiv> QuotientGroupOp(G,P,f-``{TheNeutralElement(H,F)})"
  shows "\<exists>\<ff>. Homomor(\<ff>,G//r,\<P>,f``(G),restrict(F,(f``(G))\<times>(f``(G)))) \<and> \<ff>\<in>bij(G//r,f``(G))"
proof-
  let ?\<ff> = "{\<langle>r``{g},f`(g)\<rangle>. g\<in>G}"
  from assms(3) have ff: "f:G\<rightarrow>H"
    unfolding Homomor_def by simp
  from assms(1-5) have "equiv(G,r)"
    using group0.Group_ZF_2_4_L3 kernel_normal_sub 
    unfolding group0_def IsAnormalSubgroup_def by simp
  from assms(4) ff have "?\<ff> \<in> Pow((G//r)\<times>f``(G))" 
    unfolding quotient_def using func_imagedef by auto
  moreover have "(G//r) \<subseteq> domain(?\<ff>)" unfolding domain_def quotient_def by auto 
  moreover
  { fix x y t assume A: "\<langle>x,y\<rangle> \<in> ?\<ff>" "\<langle>x,t\<rangle> \<in> ?\<ff>"
    then obtain g\<^sub>y g\<^sub>r where "\<langle>x, y\<rangle>=\<langle>r``{g\<^sub>y},f`(g\<^sub>y)\<rangle>" "\<langle>x, t\<rangle>=\<langle>r``{g\<^sub>r},f`(g\<^sub>r)\<rangle>" 
      and "g\<^sub>r\<in>G" "g\<^sub>y\<in>G" by auto
    hence B: "r``{g\<^sub>y}=r``{g\<^sub>r}" "y=f`(g\<^sub>y)" "t=f`(g\<^sub>r)" by auto
    from ff \<open>g\<^sub>y\<in>G\<close> \<open>g\<^sub>r\<in>G\<close> B(2,3) have "y\<in>H" "t\<in>H" 
      using apply_type by simp_all
    with \<open>equiv(G,r)\<close> \<open>g\<^sub>r\<in>G\<close> \<open>r``{g\<^sub>y}=r``{g\<^sub>r}\<close> have "\<langle>g\<^sub>y,g\<^sub>r\<rangle>\<in>r" 
      using same_image_equiv by simp
    with assms(4) ff have 
      "f`(P`\<langle>g\<^sub>y,GroupInv(G,P)`(g\<^sub>r)\<rangle>) = TheNeutralElement(H,F)"
      unfolding QuotientGroupRel_def using func1_1_L15 by simp
    with assms(1-4) B(2,3) \<open>g\<^sub>y\<in>G\<close> \<open>g\<^sub>r\<in>G\<close> \<open>y\<in>H\<close> \<open>t\<in>H\<close> have "y=t"
      using image_inv group0.inverse_in_group group0.group0_2_L11A 
      unfolding group0_def Homomor_def IsMorphism_def by auto
  } hence "\<forall>x y. \<langle>x,y\<rangle> \<in> ?\<ff> \<longrightarrow> (\<forall>z. \<langle>x,z\<rangle>\<in>?\<ff> \<longrightarrow> y=z)" by auto
  ultimately have ff_fun: "?\<ff>:G//r\<rightarrow>f``(G)" unfolding Pi_def function_def 
    by auto
  { fix a\<^sub>1 a\<^sub>2 assume AS: "a\<^sub>1\<in>G//r" "a\<^sub>2\<in>G//r"
    then obtain g\<^sub>1 g\<^sub>2  where "g\<^sub>1\<in>G" "g\<^sub>2\<in>G" and a: "a\<^sub>1=r``{g\<^sub>1}" "a\<^sub>2=r``{g\<^sub>2}" 
      unfolding quotient_def by auto
    with assms \<open>equiv(G,r)\<close> have "\<langle>\<P>`\<langle>a\<^sub>1,a\<^sub>2\<rangle>,f`(P`\<langle>g\<^sub>1,g\<^sub>2\<rangle>)\<rangle> \<in> ?\<ff>"
      using Group_ZF_2_4_L5A kernel_normal_sub group0.Group_ZF_2_2_L2 group0.group_op_closed
      unfolding QuotientGroupOp_def group0_def by auto       
    with ff_fun have eq: "?\<ff>`(\<P>`\<langle>a\<^sub>1,a\<^sub>2\<rangle>) = f`(P`\<langle>g\<^sub>1,g\<^sub>2\<rangle>)" using apply_equality  
      by simp
    from \<open>g\<^sub>1\<in>G\<close> \<open>g\<^sub>2\<in>G\<close> a have "\<langle>a\<^sub>1,f`(g\<^sub>1)\<rangle> \<in> ?\<ff>" and "\<langle>a\<^sub>2,f`(g\<^sub>2)\<rangle> \<in> ?\<ff>" by auto
    with assms(1,2,3) ff_fun \<open>g\<^sub>1\<in>G\<close> \<open>g\<^sub>2\<in>G\<close> eq have "F`\<langle>?\<ff>`(a\<^sub>1),?\<ff>`(a\<^sub>2)\<rangle> = ?\<ff>`(\<P>`\<langle>a\<^sub>1,a\<^sub>2\<rangle>)"
      using apply_equality unfolding Homomor_def IsMorphism_def by simp
    moreover from AS ff_fun have "?\<ff>`(a\<^sub>1) \<in> f``(G)" "?\<ff>`(a\<^sub>2) \<in> f``(G)" 
      using apply_type by auto 
    ultimately have "restrict(F,f``(G)\<times>f``(G))`\<langle>?\<ff>`(a\<^sub>1),?\<ff>`(a\<^sub>2)\<rangle> = ?\<ff>`(\<P>`\<langle>a\<^sub>1,a\<^sub>2\<rangle>)" 
      by simp
  } hence 
    r: "\<forall>a\<^sub>1\<in>G//r. \<forall>a\<^sub>2\<in>G//r. restrict(F,f``(G)\<times>f``(G))`\<langle>?\<ff>`(a\<^sub>1),?\<ff>`(a\<^sub>2)\<rangle> = ?\<ff>`(\<P>`\<langle>a\<^sub>1,a\<^sub>2\<rangle>)" 
    by simp
  with ff_fun have HOM: "Homomor(?\<ff>,G//r,\<P>,f``(G),restrict(F,(f``(G))\<times>(f``(G))))"
    unfolding Homomor_def IsMorphism_def by simp
  from assms have G: "IsAgroup(G//r,\<P>)" and 
      H: "IsAgroup(f``(G), restrict(F,f``(G)\<times>f``(G)))"
        using Group_ZF_2_4_T1 kernel_normal_sub image_group 
        unfolding IsAsubgroup_def by simp_all
  { fix b\<^sub>1 b\<^sub>2 assume AS: "?\<ff>`(b\<^sub>1) = ?\<ff>`(b\<^sub>2)" "b\<^sub>1\<in>G//r" "b\<^sub>2\<in>G//r"
    from G AS(3) have invb2: "GroupInv(G//r,\<P>)`(b\<^sub>2)\<in>G//r" 
      using group0.inverse_in_group unfolding group0_def by simp
    with G AS(2) have I: "\<P>`\<langle>b\<^sub>1,GroupInv(G//r,\<P>)`(b\<^sub>2)\<rangle>\<in>G//r"
      using group0.group_op_closed unfolding group0_def by auto
    then obtain g where "g\<in>G" and gg: "\<P>`\<langle>b\<^sub>1,GroupInv(G//r,\<P>)`(b\<^sub>2)\<rangle>=r``{g}" 
      unfolding quotient_def by auto
    from \<open>g\<in>G\<close> have "\<langle>r``{g},f`(g)\<rangle> \<in> ?\<ff>" by blast
    with ff_fun gg have E: "?\<ff>`(\<P>`\<langle>b\<^sub>1,GroupInv(G//r,\<P>)`(b\<^sub>2)\<rangle>) = f`(g)"
      using apply_equality by simp
    from ff_fun invb2 have pp: "?\<ff>`(GroupInv(G//r,\<P>)`(b\<^sub>2))\<in>f``(G)" 
      using apply_type by simp
    from ff_fun AS(2,3) have fff: "?\<ff>`(b\<^sub>1) \<in> f``(G)" "?\<ff>`(b\<^sub>2) \<in> f``(G)" 
      using apply_type by simp_all
    from fff(1) pp have 
      EE: "F`\<langle>?\<ff>`(b\<^sub>1),?\<ff>`(GroupInv(G//r,\<P>)`(b\<^sub>2))\<rangle>=
          restrict(F,f``(G)\<times>f``(G))`\<langle>?\<ff>`(b\<^sub>1),?\<ff>`(GroupInv(G//r,\<P>)`(b\<^sub>2))\<rangle>"
      by auto
    from ff have "f``(G) \<subseteq> H" using func1_1_L6(2) by simp
    with fff have "?\<ff>`(b\<^sub>1)\<in>H" "?\<ff>`(b\<^sub>2)\<in>H" by auto
    with assms(1-4) G H HOM ff_fun AS(1,3) fff(2) EE have
      "TheNeutralElement(H,F) = 
        restrict(F,f``(G)\<times>f``(G))`\<langle>?\<ff>`(b\<^sub>1),?\<ff>`(GroupInv(G//r,\<P>)`(b\<^sub>2))\<rangle>"
      using group0.group0_2_L6(1) restrict image_inv group0.group0_3_T1 image_group 
      unfolding group0_def by simp
    also from G H HOM AS(2,3) E have "\<dots> = f`(g)"
      using group0.inverse_in_group unfolding group0_def IsMorphism_def Homomor_def
      by simp
    finally have "TheNeutralElement(H,F) = f`(g)" by simp
    with ff \<open>g\<in>G\<close> have "g\<in>f-``{TheNeutralElement(H,F)}" using func1_1_L15 
      by simp
    with assms \<open>g\<in>G\<close> gg have 
      "\<P>`\<langle>b\<^sub>1,GroupInv(G//r,\<P>)`(b\<^sub>2)\<rangle> = TheNeutralElement(G//r,\<P>)"
      using group0.Group_ZF_2_4_L5E kernel_normal_sub unfolding group0_def 
      by simp
    with AS(2,3) G have "b\<^sub>1=b\<^sub>2" using group0.group0_2_L11A unfolding group0_def 
      by auto
  } with ff_fun have "?\<ff> \<in> inj(G//r,f``(G))" unfolding inj_def by blast 
  moreover
  { fix m assume "m \<in> f``(G)"
    with ff obtain g where "g\<in>G" "m=f`(g)" using func_imagedef by auto
    hence "\<langle>r``{g},m\<rangle> \<in> ?\<ff>" by blast
    with ff_fun have "?\<ff>`(r``{g})=m" using apply_equality by auto
    with \<open>g\<in>G\<close> have "\<exists>A\<in>G//r. ?\<ff>`(A) = m" unfolding quotient_def by auto
  }
  ultimately have "?\<ff> \<in> bij(G//r,f``G)" unfolding bij_def surj_def 
    using ff_fun by blast
  with HOM show ?thesis by blast
qed

text\<open>The inverse of a bijective homomorphism is an homomorphism.
  Meaning that in the previous result, the homomorphism we found is an isomorphism.\<close>

theorem bij_homomor:
  assumes "f\<in>bij(G,H)" "IsAgroup(G,P)" "Homomor(f,G,P,H,F)"
  shows "Homomor(converse(f),H,F,G,P)"
proof -
  { fix h\<^sub>1 h\<^sub>2 assume "h\<^sub>1\<in>H" "h\<^sub>2\<in>H"
    with assms(1) obtain g\<^sub>1 g\<^sub>2 where 
      g1: "g\<^sub>1\<in>G" "f`(g\<^sub>1)=h\<^sub>1" and g2: "g\<^sub>2\<in>G" "f`(g\<^sub>2)=h\<^sub>2"
      unfolding bij_def surj_def by blast
    with assms(2,3) have  
      "converse(f)`(f`(P`\<langle>g\<^sub>1,g\<^sub>2\<rangle>)) = converse(f)`(F`\<langle>h\<^sub>1,h\<^sub>2\<rangle>)"
      using homomor_eq by simp
    with assms(1,2) g1 g2 have
      "P`\<langle>converse(f)`(h\<^sub>1),converse(f)`(h\<^sub>2)\<rangle> = converse(f)`(F`\<langle>h\<^sub>1,h\<^sub>2\<rangle>)"
      using left_inverse group0.group_op_closed unfolding group0_def bij_def
      by auto
  } with assms(1) show ?thesis using bij_converse_bij bij_is_fun 
    unfolding Homomor_def IsMorphism_def by simp
qed

text\<open>A very important homomorphism is given by taking every element
  to its class in a group quotient. Recall that $\lambda x\in X. p(x)$
  is an alternative notation for function defined as a set of pairs,
  see lemma \<open>lambda_fun_alt\<close> in theory \<open>func1.thy\<close>.\<close>

lemma (in group0) quotient_map:
  assumes "IsAnormalSubgroup(G,P,H)"
  defines "r \<equiv> QuotientGroupRel(G,P,H)" and "q \<equiv> \<lambda>x\<in>G. QuotientGroupRel(G,P,H)``{x}"
  shows "Homomor(q,G,P,G//r,QuotientGroupOp(G,P,H))"
  using groupAssum assms group_op_closed lam_funtype lamE EquivClass_1_L10 
    Group_ZF_2_4_L3 Group_ZF_2_4_L5A  Group_ZF_2_4_T1
  unfolding IsAnormalSubgroup_def QuotientGroupOp_def Homomor_def IsMorphism_def
  by simp

text\<open>In the context of \<open>group0\<close>, we may use all results of \<open>semigr0\<close>.\<close>

sublocale group0 < semigroup:semigr0 G P groper "\<lambda>x. Fold1(P,x)" Append Concat  
  unfolding semigr0_def using groupAssum IsAgroup_def IsAmonoid_def by auto

end
