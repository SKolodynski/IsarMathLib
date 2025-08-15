(*
    This file is a part of IsarMathLib -
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2024  Daniel de la Concepcion Saez

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

theory Module_ZF_2 imports Module_ZF_1 Ring_ZF_2

begin

text\<open>The most basic examples of modules, are subsets of the ring; since a ring is an abelian group
when considering addition. \<close>

subsection\<open>Ideals as Modules\<close>

text\<open>Let's show first that the ring acting on itself is a module; and then we will show that ideals
are submodules.\<close>

text\<open>The map that takes every element to its left multiplication map, is a map to endomorphisms.\<close>

lemma (in ring0) action_regular_map:
  shows "{\<langle>r,{\<langle>s,r\<cdot>s\<rangle>. s\<in>R}\<rangle>. r\<in>R}:R\<rightarrow>End(R,A)" unfolding Pi_def
    function_def End_def Homomor_def IsMorphism_def apply auto
  using Ring_ZF_1_L4(3) apply simp using Ring_ZF_1_L4(3) apply simp
proof-
  fix x g1 g2 assume as:"x\<in>R" "g1\<in>R" "g2\<in>R"
  have f:"{\<langle>t, M ` \<langle>x, t\<rangle>\<rangle> . t \<in> R}:R\<rightarrow>R" unfolding Pi_def function_def apply auto
    using Ring_ZF_1_L4(3) as(1) by auto
  from f as(2) have g1:"{\<langle>t, M ` \<langle>x, t\<rangle>\<rangle> . t \<in> R}`g1 = x\<cdot>g1" using apply_equality by auto
  from f as(3) have g2:"{\<langle>t, M ` \<langle>x, t\<rangle>\<rangle> . t \<in> R}`g2 = x\<cdot>g2" using apply_equality by auto
  have "g1\<ra>g2 \<in>R" using Ring_ZF_1_L4(1) as(3,2) by auto
  then have "{\<langle>t, M ` \<langle>x, t\<rangle>\<rangle> . t \<in> R} `(g1\<ra>g2) = x\<cdot>(g1\<ra>g2)" using apply_equality f by auto
  with g1 g2 show "{\<langle>t, M ` \<langle>x, t\<rangle>\<rangle> . t \<in> R} ` (A ` \<langle>g1, g2\<rangle>) = A ` \<langle>{\<langle>t, M ` \<langle>x, t\<rangle>\<rangle> . t \<in> R} ` g1, {\<langle>t, M ` \<langle>x, t\<rangle>\<rangle> . t \<in> R} ` g2\<rangle>"
    using ring_oper_distr(1)[of x g1 g2] as by auto
qed

text\<open>The previous map respects addition because of distribution\<close>

lemma (in ring0) action_regular_distrib:
  assumes "g\<^sub>1 \<in> R" "g\<^sub>2 \<in> R"
  shows "{\<langle>xa, M ` \<langle>(A ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>), xa\<rangle>\<rangle> . xa \<in> R} =
       EndAdd(R, A) ` \<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R} \<rangle>"
proof(rule func_eq)
  from assms have A:"g\<^sub>1\<ra>g\<^sub>2\<in>R" using Ring_ZF_1_L4(1) by auto
  then have "{\<langle>r,{\<langle>s,r\<cdot>s\<rangle>. s\<in>R}\<rangle>. r\<in>R}`(g\<^sub>1\<ra>g\<^sub>2) = {\<langle>xa, M ` \<langle>(A ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>), xa\<rangle>\<rangle> . xa \<in> R}" using
    apply_equality action_regular_map by auto
  then show f1:" {\<langle>xa, M ` \<langle>(A ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>), xa\<rangle>\<rangle> . xa \<in> R}:R\<rightarrow>R" using 
    apply_type[OF action_regular_map A] unfolding End_def by auto
  have END:"{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}:End(R,A)" "{\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}:End(R,A)" using 
     apply_type[OF action_regular_map assms(1)] apply_type[OF action_regular_map assms(2)]
    apply_equality[OF _ action_regular_map] assms by auto
  with apply_type[OF restrict_fun[OF monoid0.Group_ZF_2_1_L0A, of R A _ R "End(R,A)\<times>End(R,A)"]] 
  show f2:"EndAdd(R, A) `
        \<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}\<rangle>:R\<rightarrow>R" 
    unfolding EndAdd_def End_def using Ring_ZF_1_L1(2) unfolding group0_def monoid0_def IsAgroup_def by blast
  {
    fix x assume x:"x\<in>R"
    then have " {\<langle>xa, M ` \<langle>A ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>, xa\<rangle>\<rangle> . xa \<in> R} ` x = (g\<^sub>1\<ra>g\<^sub>2)\<cdot>x" using apply_equality[OF _ f1] by auto
    moreover
    from END have "EndAdd(R, A) ` \<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> ` x = (A {lifted to function space over} R)`\<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> ` x" using restrict
      unfolding EndAdd_def by auto
    with END have "EndAdd(R, A) ` \<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> ` x = A`\<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}`x, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}`x\<rangle>"
      using group0.Group_ZF_2_1_L3[OF Ring_ZF_1_L1(2) _ _ _ x] unfolding EndAdd_def End_def by auto
    then have "EndAdd(R, A) ` \<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> ` x = (g\<^sub>1\<cdot>x)\<ra>(g\<^sub>2\<cdot>x)" using apply_equality x
      END unfolding End_def by auto
    moreover
    have "(g\<^sub>1\<cdot>x)\<ra>(g\<^sub>2\<cdot>x)= (g\<^sub>1\<ra>g\<^sub>2)\<cdot>x" using ring_oper_distr(2) x assms by auto
    ultimately have " {\<langle>xa, M ` \<langle>A ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>, xa\<rangle>\<rangle> . xa \<in> R} ` x = EndAdd(R, A) ` \<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> ` x" by auto
  }
  then show "\<forall>x\<in>R. {\<langle>xa, M ` \<langle>A ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>, xa\<rangle>\<rangle> . xa \<in> R} ` x = EndAdd(R, A) ` \<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> ` x" by auto
qed

text\<open>The previous map respects multiplication because of associativity\<close>

lemma (in ring0) action_regular_assoc:
  assumes "g\<^sub>1 \<in> R" "g\<^sub>2 \<in> R"
  shows "{\<langle>xa, M ` \<langle>(M ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>), xa\<rangle>\<rangle> . xa \<in> R} =
       EndMult(R, A) ` \<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R} \<rangle>"
proof(rule func_eq)
  from assms have A:"g\<^sub>1\<cdot>g\<^sub>2\<in>R" using Ring_ZF_1_L4(3) by auto
  then have "{\<langle>r,{\<langle>s,r\<cdot>s\<rangle>. s\<in>R}\<rangle>. r\<in>R}`(g\<^sub>1\<cdot>g\<^sub>2) = {\<langle>xa, M ` \<langle>(M ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>), xa\<rangle>\<rangle> . xa \<in> R}" using
    apply_equality action_regular_map by auto
  then show f1:" {\<langle>xa, M ` \<langle>(M ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>), xa\<rangle>\<rangle> . xa \<in> R}:R\<rightarrow>R" using 
    apply_type[OF action_regular_map A] unfolding End_def by auto
  have END:"{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}:End(R,A)" "{\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}:End(R,A)" using 
     apply_type[OF action_regular_map assms(1)] apply_type[OF action_regular_map assms(2)]
    apply_equality[OF _ action_regular_map] assms by auto
  with apply_type[OF restrict_fun[OF func_ZF_5_L1[of R], of "End(R,A)\<times>End(R,A)"]] 
  show f2:"EndMult(R, A) `
        \<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}\<rangle>:R\<rightarrow>R" 
    unfolding EndMult_def End_def  unfolding group0_def monoid0_def IsAgroup_def by blast
  {
    fix x assume x:"x\<in>R"
    then have " {\<langle>xa, M ` \<langle>M ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>, xa\<rangle>\<rangle> . xa \<in> R} ` x = (g\<^sub>1\<cdot>g\<^sub>2)\<cdot>x" using apply_equality[OF _ f1] by auto
    moreover
    from END have "EndMult(R, A) ` \<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> ` x = Composition(R)`\<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> ` x" using restrict
      unfolding EndMult_def by auto
    with END have "EndMult(R, A) ` \<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> ` x = ({\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R} O {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R})`x"
      unfolding End_def using  func_ZF_5_L2 by auto
    then have "EndMult(R, A) ` \<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> ` x = {\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R} `({\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}`x)" using x
      END comp_fun_apply[of "{\<langle>t,g\<^sub>2\<cdot>t\<rangle>. t\<in>R}" R R x] unfolding End_def by auto
    then have "EndMult(R, A) ` \<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> ` x = {\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R} `(g\<^sub>2\<cdot>x)"
      using apply_equality END(2) x unfolding End_def by auto
    then have "EndMult(R, A) ` \<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> ` x = g\<^sub>1\<cdot>(g\<^sub>2\<cdot>x)"
      using apply_equality END(1) Ring_ZF_1_L4(3)[OF assms(2) x] unfolding End_def by auto
    moreover
    have "g\<^sub>1\<cdot>g\<^sub>2\<cdot>x= g\<^sub>1\<cdot>(g\<^sub>2\<cdot>x)" using Ring_ZF_1_L11(2) x assms by auto
    ultimately have " {\<langle>xa, M ` \<langle>M ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>, xa\<rangle>\<rangle> . xa \<in> R} ` x = EndMult(R, A) ` \<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> ` x" by auto
  }
  then show "\<forall>x\<in>R. {\<langle>xa, M ` \<langle>M ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>, xa\<rangle>\<rangle> . xa \<in> R} ` x = EndMult(R, A) ` \<langle>{\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}, {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> ` x" by auto
qed

text\<open>The previous map takes the unit element to the identity map\<close>
  
lemma (in ring0) action_regular_neut:
  shows "{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` \<one> = id(R)"
proof (rule func_eq)
  from apply_type[OF action_regular_map] have "{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` \<one> :End(R,A)"
    using Ring_ZF_1_L2(2) by auto
  then show f1:"{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` \<one> :R\<rightarrow>R" unfolding End_def by auto
  show "id(R):R\<rightarrow>R" using id_inj unfolding inj_def by auto
  {
    fix x assume x:"x\<in>R"
    have "({\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` \<one>) = {\<langle>xa, M ` \<langle>\<one>, xa\<rangle>\<rangle> . xa \<in> R} "
      using apply_equality[OF _ action_regular_map] Ring_ZF_1_L2(2) by auto
    with x f1 have "({\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` \<one>)`x = \<one>\<cdot>x" using apply_equality
      by auto
    then have "({\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` \<one>)`x = x" using Ring_ZF_1_L3(6) x by auto
    then have "({\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` \<one>)`x = id(R)`x" using x by auto
  }
  then show " \<forall>x\<in>R. {\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` \<one> ` x = id(R) ` x" by auto
qed

text\<open>The previous map is an action\<close>

theorem(in ring0) action_regular:
  shows "IsAction(R,A,M,R,A,{\<langle>r,{\<langle>s,r\<cdot>s\<rangle>. s\<in>R}\<rangle>. r\<in>R})" unfolding IsAction_def IsRingHomomor_def
  IsMorphism_def apply auto using action_regular_map apply simp prefer 3
  using group0.end_comp_monoid(2)[OF Ring_ZF_1_L1(2)] action_regular_neut unfolding EndMult_def apply simp
proof-
  fix g\<^sub>1 g\<^sub>2 assume as: "g\<^sub>1 \<in> R" "g\<^sub>2 \<in> R"
  have "{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` (A ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>) = {\<langle>xa, M ` \<langle>A ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>, xa\<rangle>\<rangle> . xa \<in> R}"
    using apply_equality[OF _ action_regular_map] Ring_ZF_1_L4(1) as by auto moreover
  have "{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` g\<^sub>1 = {\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}"
    using apply_equality[OF _ action_regular_map] as(1) by auto moreover
  have "{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` g\<^sub>2 = {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}"
    using apply_equality[OF _ action_regular_map] as(2) by auto moreover
  note action_regular_distrib[OF as] ultimately
  show "{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` (A ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>) =
       EndAdd(R, A) ` \<langle>{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` g\<^sub>1, {\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` g\<^sub>2\<rangle>" by auto
  have "{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` (M ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>) = {\<langle>xa, M ` \<langle>M ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>, xa\<rangle>\<rangle> . xa \<in> R}"
    using apply_equality[OF _ action_regular_map] Ring_ZF_1_L4(3) as by auto moreover
  have "{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` g\<^sub>1 = {\<langle>xa, M ` \<langle>g\<^sub>1, xa\<rangle>\<rangle> . xa \<in> R}"
    using apply_equality[OF _ action_regular_map] as(1) by auto moreover
  have "{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` g\<^sub>2 = {\<langle>xa, M ` \<langle>g\<^sub>2, xa\<rangle>\<rangle> . xa \<in> R}"
    using apply_equality[OF _ action_regular_map] as(2) by auto moreover
  note action_regular_assoc[OF as] ultimately
  show "{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` (M ` \<langle>g\<^sub>1, g\<^sub>2\<rangle>) =
       (Composition(R) {in End} [R,A]) ` \<langle>{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` g\<^sub>1, {\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` g\<^sub>2\<rangle>"
    unfolding EndMult_def by auto
qed

text\<open>The action defines the Regular Module\<close>

theorem (in ring0) reg_module:
  shows "module0(R,A,M,R,A,{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R})" unfolding module0_def
  module0_axioms_def using ring0_axioms action_regular unfolding ring0_def IsAring_def by auto

text\<open>Every ideal is a submodule of this regular action.\<close>

corollary (in ring0) ideal_submodule:
  assumes "I\<triangleleft>R"
  shows "module0.IsAsubmodule(R,A,{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R},I)"
proof(rule module0.submoduleI[OF reg_module])
  from ideal_dest_subset[OF assms] show "I \<subseteq> R" by auto
  from ideal_dest_zero[OF assms] show "I\<noteq>0" by auto
  {
    fix r h assume as:"r:R" "h:I"
    then have A:"{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` r = {\<langle>xa, M ` \<langle>r, xa\<rangle>\<rangle> . xa \<in> R}"
      using apply_equality[OF _ action_regular_map] by auto
    then have "{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` r `h= {\<langle>xa, M ` \<langle>r, xa\<rangle>\<rangle> . xa \<in> R}`h" by auto
    moreover from A have "{\<langle>xa, M ` \<langle>r, xa\<rangle>\<rangle> . xa \<in> R}:R\<rightarrow>R" using apply_type[OF action_regular_map as(1)] 
      unfolding End_def by auto
    then have "{\<langle>xa, M ` \<langle>r, xa\<rangle>\<rangle> . xa \<in> R}`h = r\<cdot>h" using apply_equality as(2) ideal_dest_subset[OF assms] by auto
    ultimately have "{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` r `h=r\<cdot>h" by auto
    then have "{\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` r `h:I" using as ideal_dest_mult(2) assms by auto
  }
  then show "\<forall>r\<in>R. \<forall>h\<in>I. {\<langle>x, {\<langle>xa, M ` \<langle>x, xa\<rangle>\<rangle> . xa \<in> R}\<rangle> . x \<in> R} ` r ` h \<in> I" by auto
  show "I{is closed under}A" using assms ideal_dest_sum unfolding IsOpClosed_def by auto
qed

subsection\<open>Annihilators\<close>

text\<open>An annihilator of a module subset is the set of elements of the ring whose action
on that module subset is $0$.\<close>

definition (in module0) ann where
"N \<subseteq> \<M> \<Longrightarrow> ann(N) \<equiv> {r\<in>R. \<forall>n\<in>N. r\<cdot>\<^sub>Sn =\<Theta>}"

text\<open>If the subset is a submodule, then the annihilator is an ideal.\<close>

lemma (in module0) ann_ideal:
  assumes "IsAsubmodule(N)"
  shows "ann(N)\<triangleleft>R" unfolding Ideal_def
proof(safe)
  have sub:"N \<subseteq> \<M>" using mod_ab_gr.group0_3_L2 using assms unfolding IsAsubmodule_def by auto
  fix x y assume as:"x\<in>ann(N)" "y\<in>R"
  {
    fix n assume n:"n\<in>N"
    then have "(x\<cdot>y)\<cdot>\<^sub>Sn=x\<cdot>\<^sub>S(y\<cdot>\<^sub>Sn)" using module_ax3 as assms sub unfolding ann_def[OF sub]
      by auto
    moreover have "y\<cdot>\<^sub>Sn\<in>N" using n as(2) sumodule_is_subaction[OF assms] by auto
    with as(1) have "x\<cdot>\<^sub>S(y\<cdot>\<^sub>Sn) = \<Theta>" unfolding ann_def[OF sub] by auto
    ultimately have "(x\<cdot>y)\<cdot>\<^sub>Sn=\<Theta>" by auto
  }
  then have "\<forall>n\<in>N. (x\<cdot>y)\<cdot>\<^sub>Sn=\<Theta>" by auto
  then show "x\<cdot>y\<in>ann(N)" using as Ring_ZF_1_L4(3) unfolding ann_def[OF sub] by auto
  {
    fix n assume n:"n\<in>N"
    then have "(y\<cdot>x)\<cdot>\<^sub>Sn=y\<cdot>\<^sub>S(x\<cdot>\<^sub>Sn)" using module_ax3 as assms sub unfolding ann_def[OF sub] by auto
    moreover have "x\<cdot>\<^sub>Sn=\<Theta>" using n as(1) unfolding ann_def[OF sub] by auto
    with as(2) have "y\<cdot>\<^sub>S(x\<cdot>\<^sub>Sn) = \<Theta>" using zero_fixed by auto
    ultimately have "(y\<cdot>x)\<cdot>\<^sub>Sn=\<Theta>" by auto
  }
  then have "\<forall>n\<in>N. (y\<cdot>x)\<cdot>\<^sub>Sn=\<Theta>" by auto
  then show "y\<cdot>x\<in>ann(N)" using as Ring_ZF_1_L4(3) unfolding ann_def[OF sub] by auto
next
  have sub:"N \<subseteq> \<M>" using mod_ab_gr.group0_3_L2 using assms unfolding IsAsubmodule_def by auto
  show "IsAsubgroup(ann(N),A)"
  proof(rule add_group.group0_3_T3)
    show "ann(N) \<subseteq> R" unfolding ann_def[OF sub] by auto
    have "\<zero>\<in>R" using Ring_ZF_1_L2(1) by auto
    moreover have "\<forall>n\<in>N. \<zero>\<cdot>\<^sub>Sn=\<Theta>" using mult_zero sub by auto
    ultimately have "\<zero>\<in>ann(N)" unfolding ann_def[OF sub] by auto
    then show "ann(N)\<noteq>0" by auto
    {
      fix x assume "x\<in>ann(N)"
      then have x:"x\<in>R" "\<forall>n\<in>N. x\<cdot>\<^sub>Sn=\<Theta>" unfolding ann_def[OF sub] by auto
      {
        fix n assume n:"n\<in>N"
        have "(\<rm>x)\<cdot>\<^sub>Sn=(x\<cdot>(\<rm>\<one>))\<cdot>\<^sub>Sn" using Ring_ZF_1_L7(2)[of x \<one>] Ring_ZF_1_L2(2)
          Ring_ZF_1_L3(5)[of x] x(1) by auto
        then have "(\<rm>x)\<cdot>\<^sub>Sn=x\<cdot>\<^sub>S((\<rm>\<one>)\<cdot>\<^sub>Sn)" using module_ax3[of x "\<rm>\<one>" n]
          using n sub x(1) Ring_ZF_1_L3(1)[OF Ring_ZF_1_L2(2)] by auto
        moreover have "(\<rm>\<one>)\<cdot>\<^sub>Sn\<in>N" using sumodule_is_subaction[OF assms Ring_ZF_1_L3(1)[OF Ring_ZF_1_L2(2)] n].
        then have "x\<cdot>\<^sub>S((\<rm>\<one>)\<cdot>\<^sub>Sn) = \<Theta>" using x(2) by auto
        ultimately have "(\<rm>x)\<cdot>\<^sub>Sn=\<Theta>" by auto
      }
      then have "\<forall>n\<in>N. (\<rm>x)\<cdot>\<^sub>Sn=\<Theta>" by auto moreover
      have "(\<rm>x)\<in>R" using Ring_ZF_1_L3(1) x(1) by auto
      ultimately have "(\<rm>x) \<in> ann(N)" unfolding ann_def[OF sub] by auto
    }
    then show "\<forall>x\<in>ann(N). (\<rm>x) \<in> ann(N)" by auto
    {
      fix x y assume as:"x\<in>ann(N)" "y\<in>ann(N)"
      from as(1) have x:"x\<in>R" unfolding ann_def[OF sub] by auto
      from as(2) have y:"y\<in>R" unfolding ann_def[OF sub] by auto
      {
        fix n assume n:"n\<in>N"
        from n as(1) have x0:"x\<cdot>\<^sub>Sn=\<Theta>" unfolding ann_def[OF sub] by auto
        from n as(2) have y0:"y\<cdot>\<^sub>Sn=\<Theta>" unfolding ann_def[OF sub] by auto
        have "(x\<ra>y)\<cdot>\<^sub>Sn = (x\<cdot>\<^sub>Sn) +\<^sub>V(y\<cdot>\<^sub>Sn)" using module_ax2[of x y n] x y n sub by auto
        with x0 y0 have "(x\<ra>y)\<cdot>\<^sub>Sn =\<Theta> +\<^sub>V\<Theta>" by auto
        then have "(x\<ra>y)\<cdot>\<^sub>Sn =\<Theta>" using zero_neutral(1) zero_in_mod by auto
      }
      then have "\<forall>n\<in>N. (x\<ra>y)\<cdot>\<^sub>Sn =\<Theta>" by auto moreover
      have "x\<ra>y:R" using Ring_ZF_1_L4(1) x y by auto
      ultimately have "x\<ra>y\<in>ann(N)" unfolding ann_def[OF sub] by auto
    }
    then show "ann(N) {is closed under} A" unfolding IsOpClosed_def by auto
  qed
qed

text\<open>Annihilator is reverse monotonic\<close>

lemma (in module0) ann_mono:
  assumes "N \<subseteq> \<M>" "K \<subseteq> N"
  shows "ann(N) \<subseteq> ann(K)"
proof
  fix x assume "x\<in>ann(N)"
  then have "x\<in>R" "\<forall>n\<in>N. x\<cdot>\<^sub>Sn =\<Theta>" unfolding ann_def[OF assms(1)] by auto
  then have "x\<in>R" "\<forall>n\<in>K. x\<cdot>\<^sub>Sn =\<Theta>" using assms(2) by auto
  then have "x\<in> {r \<in> R . \<forall>n\<in>K. r \<cdot>\<^sub>S n = \<Theta>}" by auto moreover
  from assms have "K \<subseteq> \<M>" by auto
  ultimately show "x\<in>ann(K)" using ann_def[of K] by auto
qed


text\<open>If the ring is commutative, the annihilator of a subset shrinks to the annihilator
of the generated submodule\<close>

lemma (in module0) comm_ann_of_ideal:
  assumes "N \<subseteq> \<M>" "M {is commutative on} R"
  shows "ann(N) = ann({span of}N)"
proof
  have "N \<subseteq> {span of}N" using linear_ind_set_comb_submodule(2) assms(1) by auto
  moreover have "({span of}N) \<subseteq> \<M>" using trivial_submodules(1)
    minimal_submodule[OF assms(1)] by auto moreover
  note assms(1) ultimately show "ann({span of}N) \<subseteq> ann(N)" using ann_mono by auto
  {
    fix x assume "x\<in>ann(N)"
    then have x:"x\<in>R" "\<forall>n\<in>N. x\<cdot>\<^sub>Sn =\<Theta>" unfolding ann_def[OF assms(1)] by auto
    let ?Q="{m\<in>\<M>. x\<cdot>\<^sub>Sm=\<Theta>}"
    have "IsAsubmodule(?Q)"
    proof (rule submoduleI)
      show "?Q \<subseteq> \<M>" by auto
      have "\<Theta>\<in>?Q" using zero_fixed x(1) zero_in_mod by auto
      then show "?Q\<noteq>0" by auto
      {
        fix t h assume as:"t\<in>R" "h:?Q"
        from as(2) have h:"h\<in>\<M>" "x\<cdot>\<^sub>Sh=\<Theta>" by auto
        have "x\<cdot>\<^sub>S(t\<cdot>\<^sub>Sh) = (x\<cdot>t)\<cdot>\<^sub>Sh" using module_ax3 as(1) x(1) h(1) by auto
        then have "x\<cdot>\<^sub>S(t\<cdot>\<^sub>Sh) = (t\<cdot>x)\<cdot>\<^sub>Sh" using as(1) x(1) assms(2) unfolding IsCommutative_def by auto
        then have "x\<cdot>\<^sub>S(t\<cdot>\<^sub>Sh) = t\<cdot>\<^sub>S(x\<cdot>\<^sub>Sh)" using module_ax3 as(1) x(1) h(1) by auto
        with h(2) have "x\<cdot>\<^sub>S(t\<cdot>\<^sub>Sh) = t\<cdot>\<^sub>S\<Theta>" by auto
        then have "x\<cdot>\<^sub>S(t\<cdot>\<^sub>Sh) = \<Theta>" using zero_fixed as(1) by auto
        moreover have "t\<cdot>\<^sub>Sh\<in>\<M>" using as(1) h(1) apply_type[OF H_val_type(2)] by auto
        ultimately have "t\<cdot>\<^sub>Sh\<in>?Q" by auto
      }
      then show " \<forall>r\<in>R. \<forall>h\<in>{m \<in> \<M> . x \<cdot>\<^sub>S m = \<Theta>}. r \<cdot>\<^sub>S h \<in> {m \<in> \<M> . x \<cdot>\<^sub>S m = \<Theta>}" by auto
      {
        fix u v assume "u:?Q" "v:?Q"
        then have uv:"u\<in>\<M>" "v\<in>\<M>" "x \<cdot>\<^sub>S u = \<Theta>" "x \<cdot>\<^sub>S v = \<Theta>" by auto
        have "x\<cdot>\<^sub>S(u+\<^sub>Vv) = x \<cdot>\<^sub>S u +\<^sub>V x \<cdot>\<^sub>S v" using module_ax1 uv(1,2) x(1) by auto
        with uv(3,4) have "x\<cdot>\<^sub>S(u+\<^sub>Vv) = \<Theta> +\<^sub>V \<Theta>" by auto
        then have "x\<cdot>\<^sub>S(u+\<^sub>Vv) = \<Theta>" using zero_neutral(1) zero_in_mod by auto
        moreover have "u+\<^sub>Vv:\<M>" using mod_ab_gr.group_op_closed uv(1,2) by auto
        ultimately have "u+\<^sub>Vv:?Q" by auto
      }
      then show "?Q{is closed under}A\<^sub>M" unfolding IsOpClosed_def by auto
    qed
    moreover have "N \<subseteq> ?Q" using assms(1) x(2) by auto
    ultimately have "({span of}N) \<subseteq> ?Q" using minimal_submodule by auto
    then have "ann(?Q) \<subseteq> ann({span of}N)" using ann_mono[of ?Q "{span of}N"] by auto
    moreover have "ann(?Q) = {r\<in>R. \<forall>n\<in>?Q. r\<cdot>\<^sub>Sn = \<Theta>}" using ann_def[of ?Q] by auto
    then have "ann(?Q) = {r\<in>R. \<forall>n\<in>\<M>. x\<cdot>\<^sub>Sn=\<Theta> \<longrightarrow> r\<cdot>\<^sub>Sn = \<Theta>}" using ann_def[of ?Q] by auto
    with x(1) have "x\<in>ann(?Q)" by auto
    ultimately have "x\<in>ann({span of}N)" by auto
  }
  then show "ann(N) \<subseteq> ann({span of}N)" by auto
qed

text\<open>Annihilators on commutative rings are ideals\<close>

corollary (in module0) comm_ann_ideal:
  assumes "N \<subseteq> \<M>" "M {is commutative on} R"
  shows "ann(N) \<triangleleft>R" using comm_ann_of_ideal[OF assms] linear_ind_set_comb_submodule(1)[OF assms(1)]
    ann_ideal by auto

end