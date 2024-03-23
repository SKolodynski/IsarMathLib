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

section \<open> Modules\<close>

theory Module_ZF imports Ring_ZF_3 Field_ZF

begin

text\<open>A module is a generalization of the concept of a vector space in which scalars
  do not form a field but a ring. \<close>

subsection\<open>Definition and basic properties of modules\<close>

text\<open>Let $R$ be a ring and $M$ be an abelian group. The most common definition
  of a left $R$-module posits the existence of a scalar multiplication operation
  $R\times M\rightarrow M$ satisfying certain four properties.
  Here we take a bit more concise and abstract approach defining a module as a ring action
  on an abelian group.  \<close>

text\<open>We know that endomorphisms of an abelian group $\cal{M}$ form a ring with pointwise addition
  as the additive operation and composition as the ring multiplication. 
  This asssertion is a bit imprecise though as the domain of pointwise addition 
  is a binary operation on the space of functions $\cal{M}\rightarrow \cal{M}$ 
  (i.e. its domain is  $(\cal{M}\rightarrow \cal{M})\times \cal{M}\rightarrow \cal{M}$) 
  while we need the space of endomorphisms to be the
  domain of the ring addition and multiplication. Therefore, to get the actual additive operation
  we need to restrict the pointwise addition of functions $\cal{M}\rightarrow \cal{M}$ 
  to the set of endomorphisms of $\cal{M}$. 
  Recall from the \<open>Group_ZF_5\<close> that the \<open>InEnd\<close> operator restricts an operation to
  the set of endomorphisms and see the \<open>func_ZF\<close> theory for definitions 
  of lifting an operation on a set to a function space over that set. \<close>

definition "EndAdd(\<M>,A) \<equiv> InEnd(A {lifted to function space over} \<M>,\<M>,A)"

text\<open>Similarly we define the multiplication in the ring of endomorphisms 
  as the restriction of compositions to the endomorphisms of $\cal{M}$.
  See the \<open>func_ZF\<close> theory for the definition of the \<open>Composition\<close> operator. \<close>

definition "EndMult(\<M>,A) \<equiv> InEnd(Composition(\<M>),\<M>,A)"

text\<open>We can now reformulate the theorem \<open>end_is_ring\<close> from the \<open>Group_ZF_5\<close> theory
  in terms of the addition and multiplication of endomorphisms defined above. \<close>

lemma (in abelian_group) end_is_ring1: 
  shows "IsAring(End(G,P),EndAdd(G,P),EndMult(G,P))"
  using end_is_ring unfolding EndAdd_def EndMult_def by simp

text\<open>We define an \<open>action\<close> as a homomorphism into a space of endomorphisms (typically of some
  abelian group). In the definition below $S$ is the set of scalars, $A$ is the addition operation
  on this set, $M$ is multiplication on the set, $V$ is the group, $A_V$ is the 
  group operation, and $H$ is the ring homomorphism that of the ring of scalars 
  to the ring of endomorphisms of the group.
  On the right hand side of the definition \<open>End(V,A\<^sub>V)\<close> is the set of endomorphisms,  
  This definition is only ever used as part of the definition of a module and vector space, 
  it's just convenient to split it off to shorten the main definitions. \<close>

definition 
  "IsAction(S,A,M,\<M>,A\<^sub>M,H) \<equiv> ringHomomor(H,S,A,M,End(\<M>,A\<^sub>M),EndAdd(\<M>,A\<^sub>M),EndMult(\<M>,A\<^sub>M))"

text\<open>A module is a ring action on an abelian group.\<close>

definition "IsLeftModule(S,A,M,\<M>,A\<^sub>M,H) \<equiv>
  IsAring(S,A,M) \<and> IsAgroup(\<M>,A\<^sub>M) \<and> (A\<^sub>M {is commutative on} \<M>) \<and> IsAction(S,A,M,\<M>,A\<^sub>M,H)"


text\<open>The next locale defines context (i.e. common assumptions and notation) when considering 
  modules. We reuse notation from the \<open>ring0\<close> locale and add notation specific to
  modules. The addition and multiplication in the ring of scalars is denoted $+$ and $\cdot$,
  resp. The addition of module elements will be denoted $+_V$. 
  The multiplication (scaling) of scalars by module elemenst will be denoted $\cdot_S$. 
  $\Theta$ is the zero module element, i.e. the neutral element of the abelian group
  of the module elements. \<close>

locale module0 = ring0 +
  
  fixes \<M> A\<^sub>M H
  
  assumes mAbGr: "IsAgroup(\<M>,A\<^sub>M) \<and> (A\<^sub>M {is commutative on} \<M>)"

  assumes mAction: "IsAction(R,A,M,\<M>,A\<^sub>M,H)"

  fixes zero_vec ("\<Theta>")
  defines zero_vec_def [simp]: "\<Theta> \<equiv> TheNeutralElement(\<M>,A\<^sub>M)"

  fixes vAdd (infixl "+\<^sub>V" 80)
  defines vAdd_def [simp]: "v\<^sub>1 +\<^sub>V v\<^sub>2 \<equiv> A\<^sub>M`\<langle>v\<^sub>1,v\<^sub>2\<rangle>"

  fixes scal (infix "\<cdot>\<^sub>S" 90)
  defines scal_def [simp]: "s \<cdot>\<^sub>S v \<equiv> (H`(s))`(v)"

  fixes negV ("\<midarrow>_")
  defines negV_def [simp]: "\<midarrow>v \<equiv> GroupInv(\<M>,A\<^sub>M)`(v)"

  fixes vSub (infix "-\<^sub>V" 80)
  defines vSub_def [simp]: "v\<^sub>1 -\<^sub>V v\<^sub>2 \<equiv> v\<^sub>1 +\<^sub>V (\<midarrow>v\<^sub>2)"

text\<open>We indeed talk about modules in the \<open>module0\<close> context.\<close>

lemma (in module0) module_in_module0: shows "IsLeftModule(R,A,M,\<M>,A\<^sub>M,H)"
  using ringAssum mAbGr mAction unfolding IsLeftModule_def by simp

text\<open>Theorems proven in the \<open>abelian_group\<close> context are valid as applied to the \<open>module0\<close>
  context as applied to the abelian group of module elements. \<close>

lemma (in module0) abelian_group_valid_module0: 
  shows "abelian_group(\<M>,A\<^sub>M)"
  using mAbGr group0_def abelian_group_def abelian_group_axioms_def 
  by simp

text\<open>Another way to state that theorems proven in the \<open>abelian_group\<close> context 
  can be used in the \<open>module0\<close> context:  \<close>

sublocale module0 < mod_ab_gr: abelian_group "\<M>" "A\<^sub>M" "\<Theta>" vAdd negV
  using abelian_group_valid_module0 by auto
  
text\<open>Theorems proven in the \<open>ring_homo\<close> context are valid in the \<open>module0\<close> context, as
  applied to ring $R$ and the ring of endomorphisms of the group of module elements. \<close>
 
lemma (in module0) ring_homo_valid_module0: 
  shows "ring_homo(R,A,M,End(\<M>,A\<^sub>M),EndAdd(\<M>,A\<^sub>M),EndMult(\<M>,A\<^sub>M),H)"
  using ringAssum mAction abelian_group_valid_module0 abelian_group.end_is_ring1
  unfolding IsAction_def ring_homo_def by simp

text\<open>Another way to make theorems proven in the \<open>ring_homo\<close> context available in the 
  \<open>module0\<close> context: \<close>

sublocale module0 < vec_act_homo: ring_homo R A M 
  "End(\<M>,A\<^sub>M)" "EndAdd(\<M>,A\<^sub>M)" "EndMult(\<M>,A\<^sub>M)" H
  ringa
  ringminus
  ringsub
  ringm
  ringzero
  ringone
  ringtwo
  ringsq
  "\<lambda>x y.  EndAdd(\<M>,A\<^sub>M) ` \<langle>x, y\<rangle>"
  "\<lambda>x. GroupInv(End(\<M>,A\<^sub>M), EndAdd(\<M>, A\<^sub>M))`(x)"
  "\<lambda>x y. EndAdd(\<M>,A\<^sub>M)`\<langle>x,GroupInv(End(\<M>, A\<^sub>M), EndAdd(\<M>, A\<^sub>M))`(y)\<rangle>"
  "\<lambda>x y. EndMult(\<M>,A\<^sub>M)`\<langle>x, y\<rangle>"
  "TheNeutralElement(End(\<M>, A\<^sub>M), EndAdd(\<M>, A\<^sub>M))"
  "TheNeutralElement(End(\<M>, A\<^sub>M), EndMult(\<M>, A\<^sub>M))"
  "EndAdd(\<M>,A\<^sub>M)`\<langle>TheNeutralElement(End(\<M>, A\<^sub>M),EndMult(\<M>, A\<^sub>M)),TheNeutralElement(End(\<M>, A\<^sub>M), EndMult(\<M>,A\<^sub>M))\<rangle>"
  "\<lambda>x.  EndMult(\<M>,A\<^sub>M)`\<langle>x, x\<rangle>"
  using ring_homo_valid_module0 by auto

text\<open>In the ring of endomorphisms of the module the neutral element of the additive operation 
  is the zero valued constant function. The neutral element of the multiplicative operation is
  the identity function.\<close>

lemma (in module0) add_mult_neut_elems: shows 
  "TheNeutralElement(End(\<M>, A\<^sub>M), EndMult(\<M>,A\<^sub>M)) = id(\<M>)" and 
  "TheNeutralElement(End(\<M>,A\<^sub>M),EndAdd(\<M>,A\<^sub>M)) = ConstantFunction(\<M>,\<Theta>)"
proof -
  show "TheNeutralElement(End(\<M>, A\<^sub>M), EndMult(\<M>, A\<^sub>M)) = id(\<M>)"
    using mod_ab_gr.end_comp_monoid(2) unfolding EndMult_def
    by blast
  show "TheNeutralElement(End(\<M>, A\<^sub>M), EndAdd(\<M>, A\<^sub>M)) = ConstantFunction(\<M>,\<Theta>)"
    using mod_ab_gr.end_add_neut_elem unfolding EndAdd_def by blast
qed

text\<open>The value of the homomorphism defining the module is an endomorphism
  of the group of module elements and hence a function that maps the module into itself.\<close>

lemma (in module0) H_val_type: assumes "r\<in>R" shows 
  "H`(r) \<in> End(\<M>,A\<^sub>M)" and "H`(r):\<M>\<rightarrow>\<M>"
  using mAction assms apply_funtype unfolding IsAction_def ringHomomor_def End_def
  by auto

text\<open> In the \<open>module0\<close> context the neutral element of addition of module elements 
  is denoted $\Theta$. Of course $\Theta$ is an element of the module. \<close>

lemma (in module0) zero_in_mod: shows "\<Theta> \<in> \<M>"
  using mod_ab_gr.group0_2_L2 by simp

text\<open> $\Theta$ is indeed the neutral element of addition of module elements.\<close>

lemma (in module0) zero_neutral: assumes "x\<in>\<M>" 
  shows "x +\<^sub>V \<Theta> = x" and "\<Theta> +\<^sub>V x = x"
  using assms  mod_ab_gr.group0_2_L2 by simp_all

subsection\<open>Module axioms\<close>

text\<open>A more common definition of a module assumes that $R$ is a ring, $V$ 
  is an abelian group and lists a couple of properties that the multiplications of scalars 
  (elements of $R$) by the elements of the module $V$ should have. 
  In this section we show that the definition of a module as a ring action
  on an abelian group $V$ implies these properties.   \<close>

text\<open>The scalar multiplication is distributive with respect to the module addition.\<close>

lemma (in module0) module_ax1: assumes "r\<in>R" "x\<in>\<M>" "y\<in>\<M>"
  shows "r\<cdot>\<^sub>S(x+\<^sub>Vy) = r\<cdot>\<^sub>Sx +\<^sub>V r\<cdot>\<^sub>Sy"
  using assms H_val_type(1) mod_ab_gr.endomor_eq by simp
  
text\<open>The scalar addition is distributive with respect to scalar multiplication.\<close>

lemma (in module0) module_ax2: assumes "r\<in>R" "s\<in>R" "x\<in>\<M>"
  shows "(r\<ra>s)\<cdot>\<^sub>Sx = r\<cdot>\<^sub>Sx +\<^sub>V s\<cdot>\<^sub>Sx"
  using assms vec_act_homo.homomor_dest_add H_val_type(1) mod_ab_gr.end_pointwise_add_val
  unfolding EndAdd_def by simp

text\<open>Multiplication by scalars is associative with multiplication of scalars.\<close>

lemma (in module0) module_ax3: assumes "r\<in>R" "s\<in>R" "x\<in>\<M>"
  shows "(r\<cdot>s)\<cdot>\<^sub>Sx = r\<cdot>\<^sub>S(s\<cdot>\<^sub>Sx)"
proof -
  let ?e = "EndMult(\<M>,A\<^sub>M)`\<langle>H`(r),H`(s)\<rangle>"
  have "(r\<cdot>s)\<cdot>\<^sub>Sx = (H`(r\<cdot>s))`(x)" by simp
  also have "(H`(r\<cdot>s))`(x) = ?e`(x)"
  proof -
    from mAction assms(1,2) have "H`(r\<cdot>s) = ?e"
      using vec_act_homo.homomor_dest_mult unfolding IsAction_def
      by blast
    then show ?thesis by (rule same_constr)
  qed
  also have  "?e`(x) = r\<cdot>\<^sub>S(s\<cdot>\<^sub>Sx)"
  proof - 
    from assms(1,2) have "?e`(x) = (Composition(\<M>)`\<langle>H`(r),H`(s)\<rangle>)`(x)"
      using H_val_type(1) unfolding EndMult_def by simp
    also from assms have "... =  r\<cdot>\<^sub>S(s\<cdot>\<^sub>Sx)" using H_val_type(2) func_ZF_5_L3
      by simp
    finally show "?e`(x) = r\<cdot>\<^sub>S(s\<cdot>\<^sub>Sx)" by blast
  qed
  finally show ?thesis by simp
qed

text\<open>Scaling a module element by one gives the same module element.\<close>

lemma (in module0) module_ax4: assumes "x\<in>\<M>" shows "\<one>\<cdot>\<^sub>Sx = x"
proof -
  let ?n = "TheNeutralElement(End(\<M>,A\<^sub>M),EndMult(\<M>,A\<^sub>M))"
  from mAction have "H`(TheNeutralElement(R,M)) = ?n"
    unfolding IsAction_def ringHomomor_def by blast
  moreover have "TheNeutralElement(R,M) = \<one>" by simp
  ultimately have "H`(\<one>) = ?n" by blast
  also have "?n = id(\<M>)" by (rule add_mult_neut_elems)
  finally have "H`(\<one>) = id(\<M>)" by simp
  with assms show "\<one>\<cdot>\<^sub>Sx = x" by simp
qed

end



