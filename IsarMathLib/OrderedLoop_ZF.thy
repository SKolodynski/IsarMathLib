(*    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2021 Slawomir Kolodynski

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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open> Ordered loops \<close>

theory OrderedLoop_ZF imports Loop_ZF Order_ZF

begin

text\<open> This theory file is about properties of loops (the algebraic structures introduced 
  in IsarMathLib in the \<open>Loop_ZF\<close> theory) with an additional order relation that is in
  a way compatible with the loop's binary operation. The oldest reference I have found on the subject is
  \cite{Zelinski1948}. \<close>

subsection\<open>Definition and notation\<close>

text\<open> An ordered loop $(G,A)$ is a loop with a partial order relation r that is 
  "translation invariant" with respect to the loop operation $A$.\<close>
  
text\<open> A triple $(G,A,r)$ is an ordered loop if $(G,A)$ is a loop and $r$ is a relation
  on $G$ (i.e. a subset of $G\times G$ with is a partial order and for all elements $z \in G$
  the condition $\langle x,y\rangle \in r$ implies 
  $\langle A\langle x,z\rangle, A\langle x,z\rangle\rangle \in r$ and 
  $\langle A\langle z,x\rangle, A\langle z,x\rangle\rangle \in r$. 
  This looks a bit awkward in the basic set theory notation, but using the additive notation 
  for the group operation and $x\leq y$ to instead of $\langle x,y \rangle \in r$ this just means that
  $x+z\leq y+z$ and $z+x\leq z+y$ whenever $x\leq y$. Note also that since $r\subseteq G\times G$
  we have $x\in G$ and $y\in G$ whenever $\langle x,y\rangle \in r$, we do not have to explicitly 
  assume that $x\in G, y\in G$ in the definition. \<close>

definition
  "IsAnOrdLoop(L,A,r) \<equiv> 
  (IsAloop(L,A) \<and> r\<subseteq>L\<times>L \<and> IsPartOrder(L,r) \<and> (\<forall>z\<in>L. \<forall>x y. 
  \<langle>x,y\<rangle> \<in> r \<longrightarrow> \<langle>A`\<langle> x,z\<rangle>,A`\<langle>y,z\<rangle> \<rangle> \<in> r \<and> \<langle> A`\<langle>z,x\<rangle>,A`\<langle>z,y\<rangle> \<rangle> \<in> r ) )"

text\<open>We define the set of nonnegative elements  in the obvious way as $L^+ =\{x\in L: 0 \leq x\}$.\<close>

definition
  "Nonnegative(L,A,r) \<equiv> {x\<in>L. \<langle> TheNeutralElement(L,A),x\<rangle> \<in> r}"

text\<open>The \<open>PositiveSet(L,A,r)\<close> is a set similar to  \<open>Nonnegative(L,A,r)\<close>, but without the neutral element.\<close>

definition
  "PositiveSet(L,A,r) \<equiv> 
  {x\<in>L. \<langle> TheNeutralElement(L,A),x\<rangle> \<in> r \<and> TheNeutralElement(L,A)\<noteq> x}"

text\<open> We will use additive notation for ordered loops.\<close>

locale loop1 =
  fixes L and A and r
  assumes ordLoopAssum: "IsAnOrdLoop(L,A,r)"
  fixes neut ("\<zero>")
  defines neut_def[simp]: "\<zero> \<equiv> TheNeutralElement(L,A)"
  fixes looper (infixl "\<ra>" 69)
  defines looper_def[simp]: "x \<ra> y \<equiv> A`\<langle> x,y\<rangle>"
  fixes lesseq (infix "\<lsq>" 68)
  defines lesseq_def [simp]: "x \<lsq> y \<equiv> \<langle> x,y\<rangle> \<in> r"
  fixes sless (infix "\<ls>" 68)
  defines sless_def[simp]: "x \<ls> y \<equiv> x\<lsq>y \<and> x\<noteq>y"
  fixes nonnegative ("L\<^sup>+")
  defines nonnegative_def [simp]: "L\<^sup>+ \<equiv> Nonnegative(L,A,r)"
  fixes positive ("L\<^sub>+")
  defines positive_def[simp]: "L\<^sub>+ \<equiv> PositiveSet(L,A,r)"
  fixes leftdiv ("\<rm> _ \<ad> _")
  defines leftdiv_def[simp]: "\<rm>x\<ad>y \<equiv> LeftDiv(L,A)`\<langle>x,y\<rangle>"
  fixes rightdiv (infixl "\<rs>" 69)
  defines rightdiv_def[simp]:"x\<rs>y \<equiv> RightDiv(L,A)`\<langle>y,x\<rangle>"
    
text\<open>Theorems proven in the \<open>loop0\<close> locale are valid in the \<open>loop1\<close> locale\<close>

sublocale loop1 < loop0 L A looper  
  using ordLoopAssum loop_loop0_valid unfolding IsAnOrdLoop_def by auto

text\<open> In an ordered loop the order is translation invariant. This is in the definition, here
  we just show it in the additive notation used in the \<open>loop1\<close> locale.\<close>

lemma (in loop1) ord_trans_inv: assumes "x\<lsq>y" "z\<in>L"
  shows "x\<ra>z \<lsq> y\<ra>z" and "z\<ra>x \<lsq> z\<ra>y"
  using assms ordLoopAssum IsAnOrdLoop_def by auto

end
