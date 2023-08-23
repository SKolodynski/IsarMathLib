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

text\<open>Suppose we have two groups $G$ and $H$ with corresponding binary operations 
  $P:G\times G \rightarrow G$ and $F:H\times H \rightarrow H$. Then $f$ is a homomorphism
  if for all $g_1,g_2\in G$ we have $f(P\langle g_1,g_2\rangle ) = F\langle f(g_1),f(g_2)\rangle$. \<close> 

definition
  Homomor ("_{is a homomorphism}{_,_}\<rightarrow>{_,_}" 85)
    where  "IsAgroup(G,P) \<Longrightarrow> IsAgroup(H,F) \<Longrightarrow> 
    Homomor(f,G,P,H,F) \<equiv> \<forall>g\<^sub>1\<in>G. \<forall>g\<^sub>2\<in>G. f`(P`\<langle>g\<^sub>1,g\<^sub>2\<rangle>)=F`\<langle>f`(g\<^sub>1),f`(g\<^sub>2)\<rangle>"

text\<open>Now a lemma about the definition:\<close>

lemma homomor_eq:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)" "g\<^sub>1\<in>G" "g\<^sub>2\<in>G"
  shows "f`(P`\<langle>g\<^sub>1,g\<^sub>2\<rangle>)=F`\<langle>f`(g\<^sub>1),f`(g\<^sub>2)\<rangle>"
  using assms Homomor_def by auto

text\<open>An endomorphism is a homomorphism from a group to the same group. In case
the group is abelian, it has a nice structure.\<close>

definition
  "End(G,P) \<equiv> {f\<in>G\<rightarrow>G. Homomor(f,G,P,G,P)}"

text\<open>The defining property of an endomorphism written in notation used in \<open>group0\<close> context:\<close>

lemma (in group0) endomor_eq: assumes "f \<in> End(G,P)" "g\<^sub>1\<in>G" "g\<^sub>2\<in>G"
  shows "f`(g\<^sub>1\<cdot>g\<^sub>2) = f`(g\<^sub>1)\<cdot>f`(g\<^sub>2)"
  using groupAssum assms homomor_eq unfolding End_def by simp

text\<open>A function that maps a group $G$ into itself and satisfies 
  $f(g_1\cdot g2) = f(g_1)\cdot f(g_2)$ is an endomorphism.\<close>

lemma (in group0) eq_endomor: 
  assumes "f:G\<rightarrow>G" and "\<forall>g\<^sub>1\<in>G. \<forall>g\<^sub>2\<in>G. f`(g\<^sub>1\<cdot>g\<^sub>2)=f`(g\<^sub>1)\<cdot>f`(g\<^sub>2)"
  shows "f \<in> End(G,P)"
  using groupAssum assms Homomor_def unfolding End_def by auto

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

text\<open>We will use some binary opetrations that are naturally defined on the function space 
   $G\rightarrow G$, but we consider them restricted to the endomorphisms of $G$.
  To shorten the notation in such case we define an abbreviation \<open>InEnd(F,G,P)\<close> 
  which restricts a binary operation $F$ to the set of endomorphisms of $G$. 
  An alterrnative notation for \<open>InEnd(F,G,P)\<close> is \<open>F {in End} [G,P]\<close>. \<close>

abbreviation InEnd("_ {in End} [_,_]")
  where "InEnd(F,G,P) \<equiv> restrict(F,End(G,P)\<times>End(G,P))"

text\<open>Endomoprhisms of a group form a monoid with composition as the binary operation,
  with the identity map as the neutral element.\<close>

theorem (in group0) end_comp_monoid:
  shows "IsAmonoid(End(G,P),InEnd(Composition(G),G,P))"
  and "TheNeutralElement(End(G,P),InEnd(Composition(G),G,P))=id(G)"
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

text\<open>The inverse of an abelian group is an endomorphism.\<close>

lemma (in abelian_group) end_inverse_group:
  shows "GroupInv(G,P) \<in> End(G,P)"
  using inverse_in_group group_inv_of_two isAbelian IsCommutative_def 
    group0_2_T2 groupAssum Homomor_def 
  unfolding End_def by simp

text\<open>The set of homomorphisms of an abelian group is an abelian subgroup of
  the group of functions from a set to a group, under pointwise multiplication.\<close>

theorem (in abelian_group) end_addition_group:
  assumes "F = P {lifted to function space over} G"
  shows "IsAgroup(End(G,P),InEnd(F,G,P))" and
    "InEnd(F,G,P) {is commutative on} End(G,P)"
proof-
  have "End(G,P)\<noteq>0" using end_comp_monoid(1) monoid0.group0_1_L3A 
    unfolding monoid0_def by auto
  moreover have "End(G,P) \<subseteq> G\<rightarrow>G" unfolding End_def by auto 
  moreover from isAbelian assms(1) have "End(G,P){is closed under}F" 
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

sublocale abelian_group < endo_ring:ring0 
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
  
text\<open>A group homomorphism sends the neutral element to the neutral element
  and commutes with the inverse.\<close>

lemma image_neutral:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)" "f:G\<rightarrow>H"
  shows "f`(TheNeutralElement(G,P)) = TheNeutralElement(H,F)"
proof -
  let ?e\<^sub>G = "TheNeutralElement(G,P)"
  let ?e\<^sub>H = "TheNeutralElement(H,F)"
  have g: "?e\<^sub>G = P`\<langle>?e\<^sub>G,?e\<^sub>G\<rangle>" "?e\<^sub>G \<in> G"
    using assms(1) group0.group0_2_L2 unfolding group0_def by simp_all
  with assms have "f`(?e\<^sub>G) = F`\<langle>f`(?e\<^sub>G),f`(?e\<^sub>G)\<rangle>"
    using Homomor_def by force 
  moreover
  from assms(4) g(2) have h: "f`(?e\<^sub>G) \<in> H" using apply_type 
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

text\<open>If $f:G\rightarrow H$ is a homomorphism, then it sends the inverse of an element in $G$
  to the inverse of the image of this element in $H$. \<close>

lemma image_inv:
  assumes "IsAgroup(G,P)" "IsAgroup(H,F)" "Homomor(f,G,P,H,F)" "f:G\<rightarrow>H" "g\<in>G"
  shows "f`( GroupInv(G,P)`(g)) = GroupInv(H,F)` (f`(g))"
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
        shows "IsAsubgroup(f-``(K),P)"
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
    then obtain g\<^sub>1 g\<^sub>2  where p:"g\<^sub>1\<in>G""g\<^sub>2\<in>G" and a:"a1=r``{g\<^sub>1}""a2=r``{g\<^sub>2}" unfolding quotient_def by auto
    have "equiv(G,r)" using group0.Group_ZF_2_4_L3 kerner_normal_sub[OF assms(1-4)]
      assms(1) unfolding group0_def IsAnormalSubgroup_def r_def by auto moreover
    have "Congruent2(r,P)" using Group_ZF_2_4_L5A[OF assms(1) kerner_normal_sub[OF assms(1-4)]]
      unfolding r_def by auto moreover
    have "PP=ProjFun2(G,r,P)" unfolding PP_def QuotientGroupOp_def r_def by auto moreover
    note a p ultimately have "PP`\<langle>a1,a2\<rangle>=r``{P`\<langle>g\<^sub>1,g\<^sub>2\<rangle>}" using group0.Group_ZF_2_2_L2 assms(1)
      unfolding group0_def by auto
    then have "\<langle>PP`\<langle>a1,a2\<rangle>,f`(P`\<langle>g\<^sub>1,g\<^sub>2\<rangle>)\<rangle>\<in>?ff" using group0.group_op_closed[OF _ p] assms(1) unfolding group0_def
      by auto
    then have eq:"?ff`(PP`\<langle>a1,a2\<rangle>)=f`(P`\<langle>g\<^sub>1,g\<^sub>2\<rangle>)" using apply_equality ff_fun by auto
    from p a have "\<langle>a1,f`g\<^sub>1\<rangle>\<in>?ff""\<langle>a2,f`g\<^sub>2\<rangle>\<in>?ff" by auto
    then have "?ff`a1=f`g\<^sub>1""?ff`a2=f`g\<^sub>2" using apply_equality ff_fun by auto
    then have "F`\<langle>?ff`a1,?ff`a2\<rangle>=F`\<langle>f`g\<^sub>1,f`g\<^sub>2\<rangle>" by auto
    also have "\<dots>=f`(P`\<langle>g\<^sub>1,g\<^sub>2\<rangle>)" using assms(3) unfolding Homomor_def[OF assms(1,2)] using p by auto
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
    fix h\<^sub>1 h\<^sub>2 assume A:"h\<^sub>1\<in>H" "h\<^sub>2\<in>H"
    from A(1) obtain g\<^sub>1 where g1:"g\<^sub>1\<in>G" "f`g\<^sub>1=h\<^sub>1" using assms(1) unfolding bij_def surj_def by auto moreover
    from A(2) obtain g\<^sub>2 where g2:"g\<^sub>2\<in>G" "f`g\<^sub>2=h\<^sub>2" using assms(1) unfolding bij_def surj_def by auto ultimately
    have "F`\<langle>f`g\<^sub>1,f`g\<^sub>2\<rangle>=F`\<langle>h\<^sub>1,h\<^sub>2\<rangle>" by auto
    then have "f`(P`\<langle>g\<^sub>1,g\<^sub>2\<rangle>)=F`\<langle>h\<^sub>1,h\<^sub>2\<rangle>" using assms(2,3,4) homomor_eq g1(1) g2(1) by auto
    then have "converse(f)`(f`(P`\<langle>g\<^sub>1,g\<^sub>2\<rangle>))=converse(f)`(F`\<langle>h\<^sub>1,h\<^sub>2\<rangle>)" by auto
    then have "P`\<langle>g\<^sub>1,g\<^sub>2\<rangle>=converse(f)`(F`\<langle>h\<^sub>1,h\<^sub>2\<rangle>)" using left_inverse assms(1) group0.group_op_closed
      assms(2) g1(1) g2(1) unfolding group0_def bij_def by auto moreover
    from g1(2) have "converse(f)`(f`g\<^sub>1)=converse(f)`h\<^sub>1" by auto
    then have "g\<^sub>1=converse(f)`h\<^sub>1" using left_inverse assms(1) unfolding bij_def using g1(1) by auto moreover
    from g2(2) have "converse(f)`(f`g\<^sub>2)=converse(f)`h\<^sub>2" by auto
    then have "g\<^sub>2=converse(f)`h\<^sub>2" using left_inverse assms(1) unfolding bij_def using g2(1) by auto ultimately
    have "P`\<langle>converse(f)`h\<^sub>1,converse(f)`h\<^sub>2\<rangle>=converse(f)`(F`\<langle>h\<^sub>1,h\<^sub>2\<rangle>)" by auto
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
