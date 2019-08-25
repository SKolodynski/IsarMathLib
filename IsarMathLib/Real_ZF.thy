(*
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2005 - 2009  Slawomir Kolodynski

    This program is free software; Redistribution and use in source and binary forms, 
    with or without modification, are permitted provided that the following conditions are met:

   1. Redistributions of source code must retain the above copyright notice, 
   this list of conditions and the following disclaimer.
   2. Redistributions in binary form must reproduce the above copyright notice, 
   this list of conditions and the following disclaimer in the documentation and/or 
   other materials provided with the distribution.
   3. The name of the author may not be used to endorse or promote products 
   derived from this software without specific prior written permission.

HIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES,
INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT,
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open>Construction real numbers - the generic part\<close>

theory Real_ZF imports Int_ZF_IML Ring_ZF_1

begin

text\<open>The goal of the \<open>Real_ZF\<close> series of theory files is 
  to provide a contruction of the set of 
  real numbers. There are several ways to construct real numbers. 
  Most common start from the rational numbers and use Dedekind cuts 
  or Cauchy sequences. \<open>Real_ZF_x.thy\<close> series formalizes 
  an alternative 
  approach that constructs real numbers directly from the group of integers.
  Our formalization is mostly based on \cite{Arthan2004}. 
  Different variants of this contruction are also 
  described in \cite{Campo2003} and \cite{Street2003}.
  I recommend to read these papers, but for the impatient here is a short 
  description: we take a set of maps $s : Z\rightarrow Z$ such that
   the set $\{s(m+n)-s(m)-s(n)\}_{n,m \in Z}$ is finite 
  ($Z$ means the integers here). We call these maps slopes. 
  Slopes form a group with the natural addition
  $(s+r)(n) = s(n)+r(n)$. The maps such that the set $s(Z)$ is finite 
  (finite range functions) form a subgroup of slopes. 
  The additive group of real numbers is defined as the 
  quotient group of slopes by the (sub)group of finite range functions.
  The multiplication is defined as the projection of the composition of slopes
  into the resulting quotient (coset) space.
\<close>

subsection\<open>The definition of real numbers\<close>

text\<open>This section contains the construction of the ring of real numbers
  as classes of slopes - integer almost homomorphisms. The real definitions
  are in \<open>Group_ZF_2\<close> theory, here we just specialize the definitions
  of almost homomorphisms, their equivalence and operations to the 
  additive group of integers from the general case of abelian groups considered
  in \<open>Group_ZF_2\<close>.\<close>

text\<open>The set of slopes is defined as the set of almost homomorphisms
  on the additive group of integers.\<close>

definition
  "Slopes \<equiv> AlmostHoms(int,IntegerAddition)"

text\<open>The first operation on slopes (pointwise addition) is a special case 
  of the first operation on almost homomorphisms.\<close>

definition
  "SlopeOp1 \<equiv> AlHomOp1(int,IntegerAddition)"

text\<open>The second operation on slopes (composition) is a special case 
  of the second operation on almost homomorphisms.\<close>

definition
  "SlopeOp2 \<equiv> AlHomOp2(int,IntegerAddition)"

text\<open>Bounded integer maps are functions from integers
  to integers that have finite range. They play a role of 
  zero in the set of real numbers we are constructing.\<close>

definition
  "BoundedIntMaps \<equiv> FinRangeFunctions(int,int)"

text\<open>Bounded integer maps form a normal subgroup of slopes.
  The equivalence relation on slopes is the (group) quotient 
  relation defined by this subgroup.
\<close>

definition
  "SlopeEquivalenceRel \<equiv> QuotientGroupRel(Slopes,SlopeOp1,BoundedIntMaps)"

text\<open>The set of real numbers is the set of equivalence classes of
  slopes.\<close>

definition
  "RealNumbers \<equiv> Slopes//SlopeEquivalenceRel"

text\<open>The addition on real numbers is defined as the projection of 
  pointwise addition of slopes on the quotient. This means that
  the additive group of real numbers is the quotient group: 
  the group of slopes (with pointwise addition) defined by the
  normal subgroup of bounded integer maps.\<close>

definition
  "RealAddition \<equiv> ProjFun2(Slopes,SlopeEquivalenceRel,SlopeOp1)"

text\<open>Multiplication is defined as the projection of composition
  of slopes on the quotient. The fact that it works is probably the
  most surprising part of the construction.\<close>

definition
  "RealMultiplication \<equiv> ProjFun2(Slopes,SlopeEquivalenceRel,SlopeOp2)"

text\<open>We first show that we can use theorems proven in some proof contexts
  (locales). The locale \<open>group1\<close> requires assumption that we deal with
  an abelian group. The next lemma allows to use all theorems proven 
  in the context called \<open>group1\<close>.\<close>

lemma Real_ZF_1_L1: shows "group1(int,IntegerAddition)"
  using group1_axioms.intro group1_def Int_ZF_1_T2 by simp

text\<open>Real numbers form a ring. This is a special case of the theorem
  proven in \<open>Ring_ZF_1.thy\<close>, where we show the same in general for 
  almost homomorphisms rather than slopes.\<close>

theorem Real_ZF_1_T1: shows "IsAring(RealNumbers,RealAddition,RealMultiplication)"
proof -
  let ?AH = "AlmostHoms(int,IntegerAddition)"
  let ?Op1 = "AlHomOp1(int,IntegerAddition)"
  let ?FR = "FinRangeFunctions(int,int)"
  let ?Op2 = "AlHomOp2(int,IntegerAddition)"
  let ?R = "QuotientGroupRel(?AH,?Op1,?FR)"
  let ?A = "ProjFun2(?AH,?R,?Op1)"
  let ?M = "ProjFun2(?AH,?R,?Op2)"
  have "IsAring(?AH//?R,?A,?M)" using Real_ZF_1_L1 group1.Ring_ZF_1_1_T1
    by simp
  then show ?thesis using Slopes_def SlopeOp2_def SlopeOp1_def 
    BoundedIntMaps_def SlopeEquivalenceRel_def RealNumbers_def
    RealAddition_def RealMultiplication_def by simp
qed

text\<open>We can use theorems proven in \<open>group0\<close> and \<open>group1\<close>
  contexts applied to the group of real numbers.\<close>

lemma Real_ZF_1_L2: shows
  "group0(RealNumbers,RealAddition)"
  "RealAddition {is commutative on} RealNumbers"
  "group1(RealNumbers,RealAddition)"
proof -
  have 
    "IsAgroup(RealNumbers,RealAddition)"
    "RealAddition {is commutative on} RealNumbers"
    using Real_ZF_1_T1 IsAring_def by auto
  then show 
    "group0(RealNumbers,RealAddition)"
    "RealAddition {is commutative on} RealNumbers"
    "group1(RealNumbers,RealAddition)"
    using group1_axioms.intro group0_def group1_def
    by auto
qed

text\<open>Let's define some notation.\<close>

locale real0 =

  fixes real ("\<real>")
  defines real_def [simp]: "\<real> \<equiv> RealNumbers"

  fixes ra (infixl "\<ra>" 69)
  defines ra_def [simp]: "a\<ra> b \<equiv> RealAddition`\<langle>a,b\<rangle>"

  fixes rminus ("\<rm> _" 72)
  defines rminus_def [simp]:"\<rm>a \<equiv> GroupInv(\<real>,RealAddition)`(a)"

  fixes rsub (infixl "\<rs>" 69)
  defines rsub_def [simp]: "a\<rs>b \<equiv> a\<ra>(\<rm>b)"
 
  fixes rm (infixl "\<cdot>" 70)
  defines rm_def [simp]: "a\<cdot>b \<equiv> RealMultiplication`\<langle>a,b\<rangle>"

  fixes rzero ("\<zero>")
  defines rzero_def [simp]: 
  "\<zero> \<equiv> TheNeutralElement(RealNumbers,RealAddition)"
 
  fixes rone ("\<one>")
  defines rone_def [simp]: 
  "\<one> \<equiv> TheNeutralElement(RealNumbers,RealMultiplication)"

  fixes rtwo ("\<two>")
  defines rtwo_def [simp]: "\<two>  \<equiv> \<one>\<ra>\<one>"

  fixes non_zero ("\<real>\<^sub>0")
  defines non_zero_def[simp]: "\<real>\<^sub>0 \<equiv> \<real>-{\<zero>}"

  fixes inv ("_\<inverse> " [90] 91)
  defines inv_def[simp]: 
  "a\<inverse> \<equiv> GroupInv(\<real>\<^sub>0,restrict(RealMultiplication,\<real>\<^sub>0\<times>\<real>\<^sub>0))`(a)"

text\<open>In \<open>real0\<close> context all theorems proven in the \<open>ring0\<close>,
  context are valid.\<close>

lemma (in real0) Real_ZF_1_L3: shows 
  "ring0(\<real>,RealAddition,RealMultiplication)"
  using Real_ZF_1_T1 ring0_def ring0.Ring_ZF_1_L1 
  by auto

text\<open>Lets try out our notation to see that zero and one are real numbers.\<close>

lemma (in real0) Real_ZF_1_L4: shows "\<zero>\<in>\<real>"  "\<one>\<in>\<real>"
  using Real_ZF_1_L3 ring0.Ring_ZF_1_L2 by auto

text\<open>The lemma below lists some properties that
  require one real number to state.\<close>

lemma (in real0) Real_ZF_1_L5: assumes A1: "a\<in>\<real>"
  shows 
  "(\<rm>a) \<in> \<real>"
  "(\<rm>(\<rm>a)) = a"
  "a\<ra>\<zero> = a" 
  "\<zero>\<ra>a = a" 
  "a\<cdot>\<one> = a" 
  "\<one>\<cdot>a = a" 
  "a\<rs>a = \<zero>" 
  "a\<rs>\<zero> = a"  
  using assms Real_ZF_1_L3 ring0.Ring_ZF_1_L3 by auto

text\<open>The lemma below lists some properties that
  require two real numbers to state.\<close>

lemma (in real0) Real_ZF_1_L6: assumes "a\<in>\<real>"  "b\<in>\<real>"
  shows 
  "a\<ra>b \<in> \<real>" 
  "a\<rs>b \<in> \<real>" 
  "a\<cdot>b \<in> \<real>" 
  "a\<ra>b = b\<ra>a"
  "(\<rm>a)\<cdot>b = \<rm>(a\<cdot>b)" 
  "a\<cdot>(\<rm>b) = \<rm>(a\<cdot>b)"
  using assms Real_ZF_1_L3 ring0.Ring_ZF_1_L4 ring0.Ring_ZF_1_L7
  by auto

text\<open>Multiplication of reals is associative.\<close>

lemma (in real0) Real_ZF_1_L6A: assumes "a\<in>\<real>"  "b\<in>\<real>"  "c\<in>\<real>"
  shows "a\<cdot>(b\<cdot>c) = (a\<cdot>b)\<cdot>c"
  using assms Real_ZF_1_L3 ring0.Ring_ZF_1_L11 
  by simp

text\<open>Addition is distributive with respect to multiplication.\<close>

lemma (in real0) Real_ZF_1_L7: assumes "a\<in>\<real>"  "b\<in>\<real>"  "c\<in>\<real>" 
  shows 
  "a\<cdot>(b\<ra>c) = a\<cdot>b \<ra> a\<cdot>c" 
  "(b\<ra>c)\<cdot>a = b\<cdot>a \<ra> c\<cdot>a"
  "a\<cdot>(b\<rs>c) = a\<cdot>b \<rs> a\<cdot>c"  
  "(b\<rs>c)\<cdot>a = b\<cdot>a \<rs> c\<cdot>a"
  using assms Real_ZF_1_L3 ring0.ring_oper_distr  ring0.Ring_ZF_1_L8 
  by auto

text\<open>A simple rearrangement with four real numbers.\<close>

lemma (in real0) Real_ZF_1_L7A: 
  assumes "a\<in>\<real>"  "b\<in>\<real>"  "c\<in>\<real>"  "d\<in>\<real>"
  shows "a\<rs>b \<ra> (c\<rs>d) = a\<ra>c\<rs>b\<rs>d"
  using assms Real_ZF_1_L2 group0.group0_4_L8A by simp

text\<open>\<open>RealAddition\<close> is defined as the projection of the
  first operation on slopes (that is, slope addition) on the quotient 
  (slopes divided by the "almost equal" relation. The next lemma plays with
  definitions to show that this is the same as the operation induced on the 
  appriopriate quotient group. The names \<open>AH\<close>, \<open>Op1\<close> 
  and \<open>FR\<close> are used in \<open>group1\<close> context to denote almost 
  homomorphisms, the first operation on \<open>AH\<close> and finite range 
  functions resp.\<close>

lemma Real_ZF_1_L8: assumes
  "AH = AlmostHoms(int,IntegerAddition)" and
  "Op1 = AlHomOp1(int,IntegerAddition)" and
  "FR = FinRangeFunctions(int,int)"
  shows "RealAddition = QuotientGroupOp(AH,Op1,FR)"
  using assms RealAddition_def SlopeEquivalenceRel_def
    QuotientGroupOp_def Slopes_def SlopeOp1_def BoundedIntMaps_def
  by simp

text\<open>The symbol \<open>\<zero>\<close> in the \<open>real0\<close> context is defined
  as the neutral element of real addition. The next lemma shows that this
  is the same as the neutral element of the appriopriate quotient group.\<close>

lemma (in real0) Real_ZF_1_L9: assumes
  "AH = AlmostHoms(int,IntegerAddition)" and
  "Op1 = AlHomOp1(int,IntegerAddition)" and
  "FR = FinRangeFunctions(int,int)" and 
  "r = QuotientGroupRel(AH,Op1,FR)"
  shows 
  "TheNeutralElement(AH//r,QuotientGroupOp(AH,Op1,FR)) = \<zero>"
  "SlopeEquivalenceRel = r"
  using assms Slopes_def Real_ZF_1_L8 RealNumbers_def
    SlopeEquivalenceRel_def SlopeOp1_def BoundedIntMaps_def
  by auto

text\<open>Zero is the class of any finite range function.\<close>

lemma (in real0) Real_ZF_1_L10: 
  assumes A1: "s \<in> Slopes"
  shows "SlopeEquivalenceRel``{s} = \<zero> \<longleftrightarrow> s \<in> BoundedIntMaps"
proof -
  let ?AH = "AlmostHoms(int,IntegerAddition)"
  let ?Op1 = "AlHomOp1(int,IntegerAddition)"
  let ?FR = "FinRangeFunctions(int,int)"
  let ?r = "QuotientGroupRel(?AH,?Op1,?FR)"
  let ?e = "TheNeutralElement(?AH//?r,QuotientGroupOp(?AH,?Op1,?FR))"
  from A1 have 
    "group1(int,IntegerAddition)"
    "s\<in>?AH"
    using Real_ZF_1_L1 Slopes_def
    by auto
  then have "?r``{s} = ?e \<longleftrightarrow> s \<in> ?FR"
    using group1.Group_ZF_3_3_L5 by simp
  moreover have 
    "?r = SlopeEquivalenceRel"
    "?e = \<zero>"
    "?FR = BoundedIntMaps"
    using SlopeEquivalenceRel_def Slopes_def SlopeOp1_def 
      BoundedIntMaps_def Real_ZF_1_L9 by auto
  ultimately show ?thesis by simp
qed

text\<open>We will need a couple of results from \<open>Group_ZF_3.thy\<close> 
  The first two that state that the definition
  of addition and multiplication of real numbers are consistent, 
  that is the result 
  does not depend on the choice of the slopes representing the numbers.
  The second one implies that what we call \<open>SlopeEquivalenceRel\<close> 
  is actually an equivalence relation on the set of slopes.
  We also show that the neutral element of the multiplicative operation on
  reals (in short number $1$) is the class of the identity function on 
  integers.\<close>

lemma Real_ZF_1_L11: shows
  "Congruent2(SlopeEquivalenceRel,SlopeOp1)"
  "Congruent2(SlopeEquivalenceRel,SlopeOp2)"
  "SlopeEquivalenceRel \<subseteq> Slopes \<times> Slopes"
  "equiv(Slopes, SlopeEquivalenceRel)"
  "SlopeEquivalenceRel``{id(int)} = 
  TheNeutralElement(RealNumbers,RealMultiplication)"
  "BoundedIntMaps \<subseteq> Slopes"
proof -
  let ?G = "int"
  let ?f = "IntegerAddition"
  let ?AH = "AlmostHoms(int,IntegerAddition)"
  let ?Op1 = "AlHomOp1(int,IntegerAddition)"
  let ?Op2 = "AlHomOp2(int,IntegerAddition)"
  let ?FR = "FinRangeFunctions(int,int)"
  let ?R = "QuotientGroupRel(?AH,?Op1,?FR)"
   have 
     "Congruent2(?R,?Op1)"
     "Congruent2(?R,?Op2)"
    using Real_ZF_1_L1 group1.Group_ZF_3_4_L13A group1.Group_ZF_3_3_L4
    by auto
  then show 
    "Congruent2(SlopeEquivalenceRel,SlopeOp1)"
    "Congruent2(SlopeEquivalenceRel,SlopeOp2)"
    using SlopeEquivalenceRel_def SlopeOp1_def Slopes_def 
      BoundedIntMaps_def SlopeOp2_def by auto
  have "equiv(?AH,?R)"
    using Real_ZF_1_L1 group1.Group_ZF_3_3_L3 by simp
  then show "equiv(Slopes,SlopeEquivalenceRel)"
    using BoundedIntMaps_def SlopeEquivalenceRel_def SlopeOp1_def Slopes_def
    by simp
  then show "SlopeEquivalenceRel \<subseteq> Slopes \<times> Slopes"
    using equiv_type by simp
  have "?R``{id(int)} = TheNeutralElement(?AH//?R,ProjFun2(?AH,?R,?Op2))"
    using Real_ZF_1_L1 group1.Group_ZF_3_4_T2 by simp
  then show  "SlopeEquivalenceRel``{id(int)} = 
    TheNeutralElement(RealNumbers,RealMultiplication)"
    using Slopes_def RealNumbers_def
    SlopeEquivalenceRel_def SlopeOp1_def BoundedIntMaps_def
    RealMultiplication_def SlopeOp2_def
    by simp
  have "?FR \<subseteq> ?AH" using Real_ZF_1_L1 group1.Group_ZF_3_3_L1
    by simp
  then show "BoundedIntMaps \<subseteq> Slopes"
    using BoundedIntMaps_def Slopes_def by simp
qed

text\<open>A one-side implication of the equivalence from \<open>Real_ZF_1_L10\<close>:
  the class of a bounded integer map is the real zero.\<close>

lemma (in real0) Real_ZF_1_L11A: assumes "s \<in> BoundedIntMaps"
  shows "SlopeEquivalenceRel``{s} = \<zero>"
  using assms Real_ZF_1_L11 Real_ZF_1_L10 by auto

text\<open>The next lemma is rephrases the result from \<open>Group_ZF_3.thy\<close>
  that says that the negative (the group inverse with respect to real 
  addition) of the class of a slope is the class of that slope 
  composed with the integer additive group inverse. The result and proof is not
  very readable as we use mostly generic set theory notation with long names 
  here. \<open>Real_ZF_1.thy\<close> contains the same statement written in a more
  readable notation: $[-s] = -[s]$.\<close>

lemma (in real0) Real_ZF_1_L12: assumes A1: "s \<in> Slopes" and 
  Dr: "r = QuotientGroupRel(Slopes,SlopeOp1,BoundedIntMaps)"
  shows "r``{GroupInv(int,IntegerAddition) O s} = \<rm>(r``{s})"
proof -
  let ?G = "int"
  let ?f = "IntegerAddition"
  let ?AH = "AlmostHoms(int,IntegerAddition)"
  let ?Op1 = "AlHomOp1(int,IntegerAddition)"
  let ?FR = "FinRangeFunctions(int,int)"
  let ?F = "ProjFun2(Slopes,r,SlopeOp1)"
  from A1 Dr have 
    "group1(?G, ?f)" 
    "s \<in> AlmostHoms(?G, ?f)"
    "r = QuotientGroupRel(
    AlmostHoms(?G, ?f), AlHomOp1(?G, ?f), FinRangeFunctions(?G, ?G))"
    and "?F = ProjFun2(AlmostHoms(?G, ?f), r, AlHomOp1(?G, ?f))"
    using Real_ZF_1_L1 Slopes_def SlopeOp1_def BoundedIntMaps_def
    by auto
  then have
    "r``{GroupInv(?G, ?f) O s} =
    GroupInv(AlmostHoms(?G, ?f) // r, ?F)`(r `` {s})"
    using group1.Group_ZF_3_3_L6 by simp
  with Dr show ?thesis
    using RealNumbers_def Slopes_def SlopeEquivalenceRel_def RealAddition_def
    by simp
qed

text\<open>Two classes are equal iff the slopes that represent them 
  are almost equal.\<close>

lemma Real_ZF_1_L13: assumes "s \<in> Slopes"  "p \<in> Slopes"
  and "r = SlopeEquivalenceRel"
  shows "r``{s} = r``{p} \<longleftrightarrow> \<langle>s,p\<rangle> \<in>  r"
  using assms Real_ZF_1_L11 eq_equiv_class equiv_class_eq
  by blast

text\<open>Identity function on integers is a slope.
  Thislemma  concludes the easy part of the construction that follows from
  the fact that slope equivalence classes form a ring. It is easy to see
  that multiplication of classes of almost homomorphisms is not 
  commutative in general.
  The remaining properties of real numbers, like commutativity of 
  multiplication and the existence of multiplicative inverses have to be 
  proven using properties of the group of integers, rather that in general
  setting of abelian groups.\<close>

lemma Real_ZF_1_L14: shows "id(int) \<in> Slopes"
proof -
  have "id(int) \<in> AlmostHoms(int,IntegerAddition)"
    using Real_ZF_1_L1 group1.Group_ZF_3_4_L15
    by simp
  then show ?thesis using Slopes_def by simp
qed

end
