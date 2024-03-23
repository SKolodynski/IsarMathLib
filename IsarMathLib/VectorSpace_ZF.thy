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

section \<open>Vector spaces\<close>

theory VectorSpace_ZF imports Module_ZF

begin

text\<open> Vector spaces have a long history of applications in mathematics and physics.
  To this collection of applications a new one has been added recently - Large Language Models.
  It turned out that representing words, phrases and documents as vectors in a high-dimensional
  vector space provides an effective way to capture semantic relationships 
  and emulate contextual understanding.
  This theory has nothing to do with LLM's however - it just defines vector space as a 
  mathematical structure as it has been understood from at least the beginning of the XXth century.  \<close>

subsection\<open>Definition and basic properties of vector spaces\<close>

text\<open> The canonical example of a vector space is $\mathbb{R}^2$ - the set of $n$-tuples
  of real numbers. We can add them adding respective coordinates and scale them by 
  multiplying all coordinates by the same number. In a more abstract approach we start
  with an abelian group (of vectors) and a field (of scalars) and define an operation
  of multiplying a vector by a scalar so that the distributive 
  properties $x(v_1 + v_2) = s v_1 + s v_2$ and $(s_1+s_2)v =s_1 v + s_2 v$ are satisfied for any
  scalars $s,s_1,s_2$ and vectors $v,v_1,v_2$. \<close>


text\<open>A vector space is a field action on an abelian group. \<close>

definition "IsVectorSpace(S,A,M,V,A\<^sub>V,H) \<equiv>
  IsAfield(S,A,M) \<and> IsAgroup(V,A\<^sub>V) \<and> (A\<^sub>V {is commutative on} V) \<and> IsAction(S,A,M,V,A\<^sub>V,H)"

text\<open>The next locale defines context (i.e. common assumptions and notation) when considering 
  vector spaces. We reuse notation from the \<open>field0\<close> locale adding more similarly to the
  \<open>module0\<close> locale. \<close>

locale vector_space0 = field0 +
  fixes V A\<^sub>V H

  assumes mAbGr: "IsAgroup(V,A\<^sub>V) \<and> (A\<^sub>V {is commutative on} V)"

  assumes mAction: "IsAction(K,A,M,V,A\<^sub>V,H)"

  fixes zero_vec ("\<Theta>")
  defines zero_vec_def [simp]: "\<Theta> \<equiv> TheNeutralElement(V,A\<^sub>V)"

  fixes vAdd (infixl "+\<^sub>V" 80)
  defines vAdd_def [simp]: "v\<^sub>1 +\<^sub>V v\<^sub>2 \<equiv> A\<^sub>V`\<langle>v\<^sub>1,v\<^sub>2\<rangle>"

  fixes scal (infix "\<cdot>\<^sub>S" 90)
  defines scal_def [simp]: "s \<cdot>\<^sub>S v \<equiv> (H`(s))`(v)"

  fixes negV ("\<midarrow>_")
  defines negV_def [simp]: "\<midarrow>v \<equiv> GroupInv(V,A\<^sub>V)`(v)"

  fixes vSub (infix "-\<^sub>V" 80)
  defines vSub_def [simp]: "v\<^sub>1 -\<^sub>V v\<^sub>2 \<equiv> v\<^sub>1 +\<^sub>V (\<midarrow>v\<^sub>2)"

text\<open>We indeed talk about vector spaces in the \<open>vector_space0\<close> context. \<close>

lemma (in vector_space0) V_vec_space: shows "IsVectorSpace(K,A,M,V,A\<^sub>V,H)"
  using mAbGr mAction Field_ZF_1_L1 unfolding IsVectorSpace_def by simp

text\<open>If a quintuple of sets forms a vector space then the assumptions of 
  the \<open>vector_spce0\<close> hold for those sets.\<close>

lemma vec_spce_vec_spce_contxt: assumes "IsVectorSpace(K,A,M,V,A\<^sub>V,H)"
  shows "vector_space0(K, A, M, V, A\<^sub>V, H)"
proof
  from assms show 
    "IsAring(K, A, M)" "M {is commutative on} K"
    "TheNeutralElement(K, A) \<noteq> TheNeutralElement(K, M)"
    "\<forall>x\<in>K. x \<noteq> TheNeutralElement(K, A) \<longrightarrow> (\<exists>y\<in>K. M`\<langle>x, y\<rangle> = TheNeutralElement(K, M))"
    "IsAgroup(V, A\<^sub>V) \<and> A\<^sub>V {is commutative on} V"
    "IsAction(K, A, M, V, A\<^sub>V, H)"
    unfolding IsAfield_def IsVectorSpace_def by simp_all
qed

text\<open>The assumptions of \<open>module0\<close> context hold in the \<open>vector_spce0\<close> context.\<close>

lemma (in vector_space0) vec_spce_mod: shows "module0(K, A, M, V, A\<^sub>V, H)" 
proof
  from mAbGr show "IsAgroup(V,A\<^sub>V) \<and> (A\<^sub>V {is commutative on} V)" by simp
  from mAction show "IsAction(K,A,M,V,A\<^sub>V,H)" by simp
qed

text\<open>Propositions proven in the \<open>module0\<close> context are valid in the \<open>vector_spce0\<close> context.\<close>

sublocale vector_space0 < vspce_mod: module0 K A M 
    ringa ringminus ringsub ringm ringzero ringone ringtwo ringsq V "A\<^sub>V"
  using vec_spce_mod by auto

subsection\<open>Vector space axioms\<close>

text\<open>In this section we show that the definition of a vector space as a field action
  on an abelian group implies the vector space axioms as listed on Wikipedia (March 2024). 
  The first four axioms just state that vectors with addition form an abelian group.
  That is fine of course, but in such case the axioms for scalars being a field should be listed
  too, and they are not. The entry on modules is more consistent, 
  it states that module elements form an abelian group, scalars form a ring and lists only
  four properties of multiplication of scalars by vectors as module axioms.
  The remaining four axioms are just restatemenst of module axioms and since
  vector spaces are modules we can prove them by refering to the module axioms 
  proven in the \<open>module0\<close> context \<close>

text\<open>Vector addition is associative.\<close>

lemma (in vector_space0) vec_spce_ax1: assumes "u\<in>V" "v\<in>V" "w\<in>V"
  shows "u +\<^sub>V (v +\<^sub>V w) = (u +\<^sub>V v) +\<^sub>V w"
  using assms vspce_mod.mod_ab_gr.group_oper_assoc by simp

text\<open>Vector addition is commutative.\<close>

lemma (in vector_space0) vec_spce_ax2: assumes "u\<in>V" "v\<in>V"
  shows "u +\<^sub>V v = v +\<^sub>V u"
  using mAbGr assms unfolding IsCommutative_def by simp
  
text\<open>The zero vector is a vector.\<close>

lemma (in vector_space0) vec_spce_ax3a: shows "\<Theta> \<in> V"
  using vspce_mod.zero_in_mod by simp

text\<open>The zero vector is the neutral element of addition of vectors.\<close>

lemma (in vector_space0) vec_spce_ax3b: assumes "v\<in>V" shows "v +\<^sub>V \<Theta> = v"
  using assms vspce_mod.zero_neutral by simp

text\<open>The additive inverse of a vector is a vector.\<close>

lemma (in vector_space0) vec_spce_ax4a: assumes "v\<in>V" shows "(\<midarrow>v) \<in> V"
  using assms vspce_mod.mod_ab_gr.inverse_in_group by simp

text\<open>Sum of of a vector and it's additive inverse is the zero vector.\<close>

lemma (in vector_space0) vec_spce_ax4b: assumes "v\<in>V"
  shows "v +\<^sub>V (\<midarrow>v) = \<Theta>"
  using assms vspce_mod.mod_ab_gr.group0_2_L6 by simp

text\<open>Scalar multiplication and field multiplication are "compatible" (as Wikipedia calls it). \<close>

lemma (in vector_space0) vec_spce_ax5: assumes "x\<in>K" "y\<in>K" "v\<in>V"
  shows "x\<cdot>\<^sub>S(y\<cdot>\<^sub>Sv) = (x\<cdot>y)\<cdot>\<^sub>Sv"
  using assms vspce_mod.module_ax3 by simp

text\<open>Multiplying the identity element of the field by a vector gives the vector.\<close>

lemma (in vector_space0) vec_spce_ax6: assumes "v\<in>V" shows "\<one>\<cdot>\<^sub>Sv = v"
  using assms vspce_mod.module_ax4 by simp

text\<open>Scalar multiplication is distributive with respect to vector addition.\<close>

lemma (in vector_space0) vec_spce_ax7: assumes "x\<in>K" "u\<in>V" "v\<in>V"
  shows "x\<cdot>\<^sub>S(u+\<^sub>Vv) = x\<cdot>\<^sub>Su +\<^sub>V x\<cdot>\<^sub>Sv"
  using assms vspce_mod.module_ax1 by simp

text\<open>Scalar multiplication is distributive with respect to field addition.\<close>

lemma (in vector_space0) vec_spce_ax8: assumes "x\<in>K" "y\<in>K" "v\<in>V"
  shows "(x\<ra>y)\<cdot>\<^sub>Sv = x\<cdot>\<^sub>Sv +\<^sub>V y\<cdot>\<^sub>Sv"
  using assms vspce_mod.module_ax2 by simp

end
