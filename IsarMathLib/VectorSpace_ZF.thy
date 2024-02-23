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

section \<open> Modules and vector spaces \<close>

theory VectorSpace_ZF imports Ring_ZF_3 Field_ZF

begin

text\<open> Vector spaces have a long history of applications in mathematics and physics.
  To this collection of applications a new one has been added recently - Large Language Models.
  It turned out that representing words, phrases and documents as vectors in a high-dimensional
  vector space provides an effective way to capture semantic relationships 
  and emulate contextual understanding.
  This theory has nothing to do with LLM's however - it just defines vector space as a 
  mathematical structure as it has been understood from at least the beginning of the XXth century.  \<close>

subsection\<open>Definition and basic properties of modules and vector spaces\<close>

text\<open> The canonical example of a vector space is $\mathbb{R}^2$ - the set of $n$-tuples
  of real numbers. We can add them adding respective coordinates and scale them by 
  multiplying all coordinates by the same number. In a more abstract approach we start
  with an abelian group (of vectors) and a field (of scalars) and define an operation
  of multiplying a vector by a scalar so that the distributive 
  properties $x(v_1 + v_2) = s v_1 + s v_2$ and $(s_1+s_2)v =s_1 v + s_2 v$ are satisfied for any
  scalars $s,s_1,s_2$ and vectors $v,v_1,v_2$. \<close>

text\<open>we know that endomorphisms of an abelian group $G$ form a ring with pointwise addition
  as the additive operation and composition as the ring multiplication. This asssertion is a bit
  imprecise though as the domain of pointwise addition is a binary operation on 
  the space of functions $G\rightarrow G$ (i.e. its domain is 
  $(G\rightarrow G)\times G\rightarrow G$) while we need the space of endomorphisms to be the
  domain of the ring addition and multiplication. Therefore, to get the actual additive operation
  we need to restrict the pointwise addition of functions $G\rightarrow G$ 
  to the set of endomorphisms of G$G$. 
  Recall from the \<open>Group_ZF_5\<close> that the \<open>InEnd\<close> operator restricts an operation to
  the set of endomorphisms and see the \<open>func_ZF\<close> theory for definitions 
  of lifting an operation on a set to a function space over that set. \<close>

definition "EndAdd(G,P) \<equiv> InEnd(P {lifted to function space over} G,G,P)"

text\<open>Similarly we define the multiplication in the ring of endomorphisms 
  as the restriction of compositions to the endomorphisms of $G$.
  See the \<open>func_ZF\<close> theory for the definition of the \<open>Composition\<close> operator. \<close>

definition "EndMult(G,P) \<equiv> InEnd(Composition(G),G,P)"

text\<open>We can now reformulate the theorem \<open>end_is_ring\<close> from the \<open>Group_ZF_5\<close> theory
  in terms of the addition and multiplication of endomorphisms defined above. \<close>

lemma (in abelian_group) end_is_ring1: 
  shows "IsAring(End(G,P),EndAdd(G,P),EndMult(G,P))"
  using end_is_ring unfolding EndAdd_def EndMult_def by simp

text\<open>We define an \<open>action\<close> as a homomorphism into a space of endomorphisms (typically of some
  abelian group). In the definition below $S$ is the set of scalars, $A$ is the addition operation
  on this set, $M$ is multiplication on the set, $V$ is the set of vectors, $A_V$ is the 
  operation of vector addition, and $H$ is the homomorphism that defines the vector space.
  On the right hand side of the definition \<open>End(V,A\<^sub>V)\<close> is the set of endomorphisms,  
  This definition is only ever used as part of the definition of a module and vector space, 
  it's just convenient to split it off to shorten the main definitions. \<close>

definition 
  "IsAction(S,A,M,V,A\<^sub>V,H) \<equiv> ringHomomor(H,S,A,M,End(V,A\<^sub>V),EndAdd(V,A\<^sub>V),EndMult(V,A\<^sub>V))"

text\<open>A module is a ring action on an abelian group.\<close>

definition "IsModule(S,A,M,V,A\<^sub>V,H) \<equiv>
  IsAring(S,A,M) \<and> IsAgroup(V,A\<^sub>V) \<and> (A\<^sub>V {is commutative on} V) \<and> IsAction(S,A,M,V,A\<^sub>V,H)"

text\<open>A vector space is a field action on an abelian group. \<close>

definition "IsVectorSpace(S,A,M,V,A\<^sub>V,H) \<equiv>
  IsAfield(S,A,M) \<and> IsAgroup(V,A\<^sub>V) \<and> (A\<^sub>V {is commutative on} V) \<and> IsAction(S,A,M,V,A\<^sub>V,H)"


text\<open>The next locale defines context (i.e. common assumptions and notation) when considering 
  modules. We reuse notation from the \<open>ring0\<close> locale and add notation specific to the
  vector spaces. We split the definition of a module into components to make the assumptions
  easier to use. The addition and multiplication in the ring of scalars is denoted $+$ and $\cdot$,
  resp. The addition of vectors will be denoted $+_V$. The multiplication (scaling) of scalars and
  by vectors will be denoted $\cdot_S$.   \<close>

locale module0 = ring0 +
  
  fixes V A\<^sub>V H
  
  assumes vAbGr: "IsAgroup(V,A\<^sub>V) \<and> (A\<^sub>V {is commutative on} V)"

  assumes vSpce: "IsAction(R,A,M,V,A\<^sub>V,H)"

  fixes vAdd (infixl "+\<^sub>V" 80)
  defines vAdd_def [simp]: "v\<^sub>1 +\<^sub>V v\<^sub>2 \<equiv> A\<^sub>V`\<langle>v\<^sub>1,v\<^sub>2\<rangle>"

  fixes scal (infix "\<cdot>\<^sub>S" 90)
  defines scal_def [simp]: "s \<cdot>\<^sub>S v \<equiv> (H`(s))`(v)"


text\<open>We indeed talk about modules in the \<open>module0\<close> context.\<close>

lemma (in module0) module_in_module0: shows "IsModule(R,A,M,V,A\<^sub>V,H)"
  using ringAssum vAbGr vSpce unfolding IsModule_def by simp

text\<open>Theorems proven in the \<open>ring_homo\<close> context are valid in the \<open>module0\<close> context, as
  applied to ring $R$ and the ring of endomorphisms of the vector group. \<close>

lemma (in module0) ring_homo_in_module0: 
  shows "ring_homo(R,A,M,End(V,A\<^sub>V),EndAdd(V,A\<^sub>V),EndMult(V,A\<^sub>V),H)"
proof 

end



