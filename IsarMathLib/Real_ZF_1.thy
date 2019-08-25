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

section \<open>Construction of real numbers\<close>

theory Real_ZF_1 imports Real_ZF Int_ZF_3 OrderedField_ZF

begin

text\<open>In this theory file we continue the construction of real numbers started
  in \<open>Real_ZF\<close> to a succesful conclusion. 
  We put here those parts of the construction that 
  can not be done in the general settings of abelian groups and require 
  integers.\<close>

subsection\<open>Definitions and notation\<close>

text\<open>In this section we define notions and notation needed for the rest of 
  the construction.\<close>

text\<open>We define positive slopes as those that take an infinite number of 
  posititive values on the positive integers (see \<open>Int_ZF_2\<close> 
  for properties of positive slopes).\<close>

definition
  "PositiveSlopes \<equiv> {s \<in> Slopes. 
  s``(PositiveIntegers) \<inter>  PositiveIntegers \<notin> Fin(int)}"

text\<open>The order on the set of real numbers is constructed by 
  specifying the set of positive reals. This set is defined
  as  the projection of the set of positive slopes.\<close>

definition
  "PositiveReals \<equiv> {SlopeEquivalenceRel``{s}. s \<in> PositiveSlopes}"

text\<open>The order relation on real numbers is constructed from the set of 
  positive elements in a standard way (see section 
  "Alternative definitions" in \<open>OrderedGroup_ZF\<close>.)
\<close>

definition
  "OrderOnReals \<equiv> OrderFromPosSet(RealNumbers,RealAddition,PositiveReals)"

text\<open>The next locale extends the locale \<open>real0\<close> to define notation 
  specific to the construction of real numbers. The notation follows the
  one defined in \<open>Int_ZF_2.thy\<close>.
  If $m$ is an integer, then the real number which is the class of the slope
  $n\mapsto m\cdot n$ is denoted \<open>m\<^sup>R\<close>. 
  For a real number $a$ notation $\lfloor a \rfloor$ means the largest integer
  $m$ such that the real version of it (that is, $m^R$) is not greater 
  than $a$.
  For an integer $m$ and a subset 
  of reals $S$ the expression  $\Gamma(S,m)$ is defined as 
  $\max \{\lfloor p^R\cdot x\rfloor : x\in S\}$. This is plays a role in
  the proof of completeness of real numbers.  
  We also reuse some notation defined in the \<open>int0\<close> context, like
  \<open>\<int>\<^sub>+ \<close> (the set of positive integers) and abs$(m)$ ( the absolute
  value of an integer, and some defined in the \<open>int1\<close> context, like
  the addition ( \<open>\<fp>\<close>) and composition (\<open>\<circ>\<close> 
  of slopes.\<close>

locale real1 = real0 +

  fixes AlEq (infix "\<sim>" 68)
  defines AlEq_def[simp]: "s \<sim> r \<equiv> \<langle>s,r\<rangle> \<in> SlopeEquivalenceRel"

  fixes slope_add (infix "\<fp>" 70)
  defines slope_add_def[simp]: 
  "s \<fp> r \<equiv>  SlopeOp1`\<langle>s,r\<rangle>"

  fixes slope_comp (infix "\<circ>" 71)
  defines slope_comp_def[simp]: "s \<circ> r \<equiv>  SlopeOp2`\<langle>s,r\<rangle>"

  fixes slopes ("\<S>")
  defines slopes_def[simp]: "\<S> \<equiv> AlmostHoms(int,IntegerAddition)"

  fixes posslopes ("\<S>\<^sub>+")
  defines posslopes_def[simp]: "\<S>\<^sub>+ \<equiv> PositiveSlopes"

  fixes slope_class ("[ _ ]")
  defines slope_class_def[simp]: "[f] \<equiv> SlopeEquivalenceRel``{f}"


  fixes slope_neg ("\<fm>_" [90] 91)
  defines slope_neg_def[simp]: "\<fm>s \<equiv> GroupInv(int,IntegerAddition) O s"

  fixes lesseqr (infix "\<lsq>" 60)
  defines lesseqr_def[simp]: "a \<lsq> b \<equiv> \<langle>a,b\<rangle> \<in> OrderOnReals"

  fixes sless (infix "\<ls>" 60)
  defines sless_def[simp]: "a \<ls> b \<equiv> a\<lsq>b \<and> a\<noteq>b"

  fixes positivereals ("\<real>\<^sub>+")
  defines positivereals_def[simp]: "\<real>\<^sub>+ \<equiv> PositiveSet(\<real>,RealAddition,OrderOnReals)"

  fixes intembed ("_\<^sup>R" [90] 91)
  defines intembed_def[simp]: 
  "m\<^sup>R \<equiv> [{\<langle>n,IntegerMultiplication`\<langle>m,n\<rangle> \<rangle>. n \<in> int}]"

  fixes floor ("\<lfloor> _ \<rfloor>")
  defines floor_def[simp]: 
  "\<lfloor>a\<rfloor> \<equiv> Maximum(IntegerOrder,{m \<in> int. m\<^sup>R \<lsq> a})"

  fixes \<Gamma> 
  defines \<Gamma>_def[simp]: "\<Gamma>(S,p) \<equiv> Maximum(IntegerOrder,{\<lfloor>p\<^sup>R\<cdot>x\<rfloor>. x\<in>S})"

  fixes ia (infixl "\<za>" 69)
  defines ia_def[simp]: "a\<za>b \<equiv> IntegerAddition`\<langle> a,b\<rangle>"

  fixes iminus ("\<zm> _" 72)
  defines iminus_def[simp]: "\<zm>a \<equiv> GroupInv(int,IntegerAddition)`(a)"

  fixes isub (infixl "\<zs>" 69)
  defines isub_def[simp]: "a\<zs>b \<equiv> a\<za> (\<zm> b)"

  fixes intpositives ("\<int>\<^sub>+")
  defines intpositives_def[simp]: 
  "\<int>\<^sub>+ \<equiv> PositiveSet(int,IntegerAddition,IntegerOrder)"

  fixes zlesseq (infix "\<zlq>" 60)
  defines lesseq_def[simp]: "m \<zlq> n \<equiv> \<langle>m,n\<rangle> \<in> IntegerOrder"

  fixes imult (infixl "\<zmu>" 70)
  defines imult_def[simp]: "a\<zmu>b \<equiv> IntegerMultiplication`\<langle> a,b\<rangle>"

  fixes izero ("\<zero>\<^sub>Z")
  defines izero_def[simp]: "\<zero>\<^sub>Z \<equiv> TheNeutralElement(int,IntegerAddition)"

  fixes ione ("\<one>\<^sub>Z")
  defines ione_def[simp]: "\<one>\<^sub>Z \<equiv> TheNeutralElement(int,IntegerMultiplication)"

  fixes itwo ("\<two>\<^sub>Z")
  defines itwo_def[simp]: "\<two>\<^sub>Z \<equiv> \<one>\<^sub>Z\<za>\<one>\<^sub>Z"
  
  fixes abs 
  defines abs_def[simp]: 
  "abs(m) \<equiv> AbsoluteValue(int,IntegerAddition,IntegerOrder)`(m)"

  fixes \<delta> 
  defines \<delta>_def[simp]: "\<delta>(s,m,n) \<equiv> s`(m\<za>n)\<zs>s`(m)\<zs>s`(n)"


subsection\<open>Multiplication of real numbers\<close>

text\<open>Multiplication of real numbers is defined as a projection of 
  composition of slopes onto the space of equivalence classes of slopes.
  Thus, the product of the real numbers given as classes of slopes $s$ and 
  $r$ is defined as the class of $s\circ r$. The goal of this section is to 
  show that multiplication defined this way is commutative.\<close>

text\<open>Let's recall a theorem from \<open>Int_ZF_2.thy\<close> that states that 
  if $f,g$ are slopes,
  then $f\circ g$ is equivalent to $g\circ f$. 
  Here we conclude from that that
  the classes of $f\circ g$ and $g\circ f$ are the same.\<close>

lemma (in real1) Real_ZF_1_1_L2: assumes A1: "f \<in> \<S>"  "g \<in> \<S>"
  shows "[f\<circ>g] = [g\<circ>f]"
proof -
  from A1 have "f\<circ>g \<sim> g\<circ>f" 
    using Slopes_def int1.Arthan_Th_9 SlopeOp1_def BoundedIntMaps_def
      SlopeEquivalenceRel_def SlopeOp2_def by simp
  then show ?thesis using Real_ZF_1_L11 equiv_class_eq
    by simp
qed

text\<open>Classes of slopes are real numbers.\<close>

lemma (in real1) Real_ZF_1_1_L3: assumes A1: "f \<in> \<S>"
  shows "[f] \<in> \<real>"
proof -
  from A1 have "[f] \<in> Slopes//SlopeEquivalenceRel"
    using Slopes_def quotientI by simp
  then show "[f] \<in> \<real>" using RealNumbers_def by simp  
qed

text\<open>Each real number is a class of a slope.\<close>

lemma (in real1) Real_ZF_1_1_L3A: assumes A1: "a\<in>\<real>"
  shows "\<exists>f\<in>\<S> . a = [f]"
proof -
  from A1 have "a \<in> \<S>//SlopeEquivalenceRel" 
    using RealNumbers_def Slopes_def by simp
  then show ?thesis using quotient_def
    by simp
qed

text\<open>It is useful to have the definition of addition and multiplication 
  in the \<open>real1\<close> context notation.\<close>

lemma (in real1) Real_ZF_1_1_L4: 
  assumes A1: "f \<in> \<S>"  "g \<in> \<S>"
  shows
  "[f] \<ra> [g] = [f\<fp>g]"
  "[f] \<cdot> [g] = [f\<circ>g]"
proof -
  let ?r = "SlopeEquivalenceRel"
  have "[f]\<cdot>[g] = ProjFun2(\<S>,?r,SlopeOp2)`\<langle>[f],[g]\<rangle>"
    using RealMultiplication_def Slopes_def by simp
  also from A1 have "\<dots> = [f\<circ>g]"
    using Real_ZF_1_L11 EquivClass_1_L10 Slopes_def
    by simp
  finally show "[f] \<cdot> [g] = [f\<circ>g]" by simp
  have "[f] \<ra> [g] = ProjFun2(\<S>,?r,SlopeOp1)`\<langle>[f],[g]\<rangle>"
    using RealAddition_def Slopes_def by simp
  also from A1 have "\<dots> = [f\<fp>g]"
    using Real_ZF_1_L11 EquivClass_1_L10 Slopes_def
    by simp
  finally show "[f] \<ra> [g] = [f\<fp>g]" by simp
qed


text\<open>The next lemma is essentially the same as \<open> Real_ZF_1_L12\<close>, but
  written in the notation defined in the \<open>real1\<close> context. It states
  that if $f$ is a slope, then $-[f] = [-f]$.\<close>

lemma (in real1) Real_ZF_1_1_L4A: assumes "f \<in> \<S>"
  shows "[\<fm>f] = \<rm>[f]"
  using assms Slopes_def SlopeEquivalenceRel_def Real_ZF_1_L12
  by simp

text\<open>Subtracting real numbers correspods to adding the opposite slope.\<close>

lemma (in real1) Real_ZF_1_1_L4B: assumes A1: "f \<in> \<S>"  "g \<in> \<S>"
  shows "[f] \<rs> [g] = [f\<fp>(\<fm>g)]"
proof -
  from A1 have "[f\<fp>(\<fm>g)] = [f] \<ra> [\<fm>g]"
    using Slopes_def BoundedIntMaps_def int1.Int_ZF_2_1_L12
      Real_ZF_1_1_L4 by simp
  with A1 show "[f] \<rs> [g] = [f\<fp>(\<fm>g)]"
    using Real_ZF_1_1_L4A by simp
qed
  
text\<open>Multiplication of real numbers is commutative.\<close>

theorem (in real1) real_mult_commute: assumes A1: "a\<in>\<real>"  "b\<in>\<real>"
  shows "a\<cdot>b = b\<cdot>a"
proof -
  from A1 have 
    "\<exists>f\<in>\<S> . a = [f]"
    "\<exists>g\<in>\<S> . b = [g]"
    using Real_ZF_1_1_L3A by auto
  then obtain f g where 
    "f \<in> \<S>"  "g \<in> \<S>" and "a = [f]"  "b = [g]" 
    by auto
  then show "a\<cdot>b = b\<cdot>a"
    using Real_ZF_1_1_L4 Real_ZF_1_1_L2 by simp
qed

text\<open>Multiplication is commutative on reals.\<close>

lemma real_mult_commutative: shows
  "RealMultiplication {is commutative on} RealNumbers"
  using real1.real_mult_commute IsCommutative_def
  by simp

text\<open>The neutral element of multiplication of reals 
  (denoted as \<open>\<one>\<close> in the \<open>real1\<close> context) 
  is the class of identity function on integers. This is really shown
  in \<open>Real_ZF_1_L11\<close>, here we only rewrite it in the notation used
  in the \<open>real1\<close> context.\<close>

lemma (in real1) real_one_cl_identity: shows "[id(int)] = \<one>"
  using Real_ZF_1_L11 by simp

text\<open>If $f$ is bounded, then its class is the neutral element of additive 
  operation on reals (denoted as \<open>\<zero>\<close> in the \<open>real1\<close> context).\<close>

lemma (in real1) real_zero_cl_bounded_map: 
  assumes "f \<in> BoundedIntMaps" shows "[f] = \<zero>"
  using assms Real_ZF_1_L11A by simp
  

text\<open>Two real numbers are equal iff the slopes that represent them are 
  almost equal. This is proven in \<open>Real_ZF_1_L13\<close>, here we just 
  rewrite it in the notation used in the \<open>real1\<close> context.\<close>

lemma (in real1) Real_ZF_1_1_L5: 
  assumes "f \<in> \<S>"  "g \<in> \<S>"
  shows "[f] = [g] \<longleftrightarrow> f \<sim> g"
  using assms Slopes_def Real_ZF_1_L13 by simp

text\<open>If the pair of function belongs to the slope equivalence relation, then
  their classes are equal. This is convenient, because we don't need to assume
  that $f,g$ are slopes (follows from the fact that $f\sim g$).\<close>

lemma (in real1) Real_ZF_1_1_L5A: assumes "f \<sim> g"
  shows "[f] = [g]"
  using assms Real_ZF_1_L11 Slopes_def Real_ZF_1_1_L5
  by auto

text\<open>Identity function on integers is a slope. 
  This is proven in \<open>Real_ZF_1_L13\<close>, here we just 
  rewrite it in the notation used in the \<open>real1\<close> context.\<close>

lemma (in real1) id_on_int_is_slope: shows "id(int) \<in> \<S>"
  using Real_ZF_1_L14 Slopes_def by simp


text\<open>A result from \<open>Int_ZF_2.thy\<close>: the identity function on integers
  is not almost equal to any bounded function.\<close>

lemma (in real1) Real_ZF_1_1_L7:
  assumes A1: "f \<in> BoundedIntMaps"
  shows "\<not>(id(int) \<sim> f)"
  using assms Slopes_def SlopeOp1_def BoundedIntMaps_def 
    SlopeEquivalenceRel_def BoundedIntMaps_def int1.Int_ZF_2_3_L12 
  by simp

text\<open>Zero is not one.\<close>

lemma (in real1) real_zero_not_one: shows "\<one>\<noteq>\<zero>"
proof -
  { assume A1: "\<one>=\<zero>"
    have "\<exists>f \<in> \<S>. \<zero> = [f]"
      using  Real_ZF_1_L4 Real_ZF_1_1_L3A by simp
    with A1 have 
      "\<exists>f \<in> \<S>. [id(int)] = [f] \<and> [f] = \<zero>"
      using real_one_cl_identity by auto
    then have False using Real_ZF_1_1_L5 Slopes_def 
      Real_ZF_1_L10 Real_ZF_1_1_L7 id_on_int_is_slope
      by auto
  } then show "\<one>\<noteq>\<zero>" by auto
qed

text\<open>Negative of a real number is a real number. Property of groups.\<close>

lemma (in real1) Real_ZF_1_1_L8: assumes "a\<in>\<real>" shows "(\<rm>a) \<in> \<real>"
  using assms Real_ZF_1_L2 group0.inverse_in_group
  by simp

text\<open>An identity with three real numbers.\<close>

lemma (in real1) Real_ZF_1_1_L9: assumes "a\<in>\<real>"  "b\<in>\<real>"  "c\<in>\<real>"
  shows "a\<cdot>(b\<cdot>c) = a\<cdot>c\<cdot>b"
  using assms real_mult_commutative Real_ZF_1_L3 ring0.Ring_ZF_2_L4
  by simp

subsection\<open>The order on reals\<close>

text\<open>In this section we show that the order relation defined by prescribing
  the set of positive reals as the projection of the set of positive
  slopes makes the ring of real numbers into an ordered ring. We also
  collect the facts about ordered groups and rings that we use in 
  the construction.\<close>

text\<open>Positive slopes are slopes and positive reals are real.\<close>

lemma Real_ZF_1_2_L1: shows 
  "PositiveSlopes \<subseteq> Slopes"
  "PositiveReals \<subseteq> RealNumbers"
proof -
  have "PositiveSlopes = 
    {s \<in> Slopes. s``(PositiveIntegers) \<inter> PositiveIntegers \<notin> Fin(int)}"
    using PositiveSlopes_def by simp
  then show "PositiveSlopes \<subseteq> Slopes" by (rule subset_with_property)
  then have 
    "{SlopeEquivalenceRel``{s}. s \<in> PositiveSlopes } \<subseteq> 
    Slopes//SlopeEquivalenceRel"
    using EquivClass_1_L1A by simp
  then show "PositiveReals \<subseteq> RealNumbers"
    using PositiveReals_def RealNumbers_def by simp
qed
  
text\<open>Positive reals are the same as classes of a positive slopes.\<close>

lemma (in real1) Real_ZF_1_2_L2: 
  shows "a \<in> PositiveReals \<longleftrightarrow> (\<exists>f\<in>\<S>\<^sub>+. a = [f])"
proof
  assume "a \<in> PositiveReals"
  then have "a \<in> {([s]). s \<in> \<S>\<^sub>+}" using PositiveReals_def 
    by simp (* it has to be ([a]), otherwise fails*)
  then show "\<exists>f\<in>\<S>\<^sub>+. a = [f]" by auto
next assume "\<exists>f\<in>\<S>\<^sub>+. a = [f]"
  then have  "a \<in> {([s]). s \<in> \<S>\<^sub>+}" by auto
  then show "a \<in> PositiveReals" using PositiveReals_def
    by simp
qed

text\<open>Let's recall from \<open>Int_ZF_2.thy\<close> that the sum and composition 
  of positive slopes is a positive slope.\<close>

lemma (in real1) Real_ZF_1_2_L3:
  assumes "f\<in>\<S>\<^sub>+"  "g\<in>\<S>\<^sub>+"
  shows 
  "f\<fp>g \<in> \<S>\<^sub>+"
  "f\<circ>g \<in> \<S>\<^sub>+"
  using assms Slopes_def PositiveSlopes_def PositiveIntegers_def
    SlopeOp1_def int1.sum_of_pos_sls_is_pos_sl
    SlopeOp2_def int1.comp_of_pos_sls_is_pos_sl
  by auto

text\<open>Bounded integer maps are not positive slopes.\<close>

lemma (in real1) Real_ZF_1_2_L5:
  assumes "f \<in> BoundedIntMaps"
  shows "f \<notin> \<S>\<^sub>+"
  using assms BoundedIntMaps_def Slopes_def PositiveSlopes_def
    PositiveIntegers_def int1.Int_ZF_2_3_L1B by simp

 
text\<open>The set of positive reals is closed under addition and multiplication.
  Zero (the neutral element of addition) is not a positive number.\<close>

lemma (in real1) Real_ZF_1_2_L6: shows 
  "PositiveReals {is closed under} RealAddition"
  "PositiveReals {is closed under} RealMultiplication"
  "\<zero> \<notin> PositiveReals"
proof -
  { fix a fix b
    assume "a \<in> PositiveReals" and "b \<in> PositiveReals"
    then obtain f g where
      I: "f \<in> \<S>\<^sub>+"  "g \<in> \<S>\<^sub>+" and
      II: "a = [f]"  "b = [g]"
      using Real_ZF_1_2_L2 by auto
    then have "f \<in> \<S>"  "g \<in> \<S>" using Real_ZF_1_2_L1 Slopes_def 
      by auto
    with I II have 
      "a\<ra>b \<in> PositiveReals \<and> a\<cdot>b \<in> PositiveReals"
       using Real_ZF_1_1_L4 Real_ZF_1_2_L3 Real_ZF_1_2_L2
       by auto
  } then show 
      "PositiveReals {is closed under} RealAddition"
      "PositiveReals {is closed under} RealMultiplication"
    using IsOpClosed_def
    by auto
  { assume "\<zero> \<in> PositiveReals"
    then obtain f where "f \<in> \<S>\<^sub>+" and "\<zero> = [f]"
      using Real_ZF_1_2_L2 by auto
    then have False
      using Real_ZF_1_2_L1 Slopes_def Real_ZF_1_L10 Real_ZF_1_2_L5
      by auto
  } then show "\<zero> \<notin> PositiveReals" by auto
qed

text\<open>If a class of a slope $f$ is not zero, then either $f$ is 
  a positive slope or $-f$ is a positive slope. The real proof is in
  \<open>Int_ZF_2.thy.\<close>\<close>

lemma (in real1) Real_ZF_1_2_L7: 
  assumes A1: "f \<in> \<S>" and A2: "[f] \<noteq> \<zero>"
  shows "(f \<in> \<S>\<^sub>+) Xor ((\<fm>f) \<in> \<S>\<^sub>+)"
  using assms Slopes_def SlopeEquivalenceRel_def BoundedIntMaps_def
    PositiveSlopes_def PositiveIntegers_def 
    Real_ZF_1_L10 int1.Int_ZF_2_3_L8 by simp
  
text\<open>The next lemma rephrases \<open> Int_ZF_2_3_L10\<close> in the notation
  used in \<open>real1\<close> context.\<close>

lemma (in real1) Real_ZF_1_2_L8: 
  assumes A1: "f \<in> \<S>"  "g \<in> \<S>"
  and A2: "(f \<in> \<S>\<^sub>+) Xor (g \<in> \<S>\<^sub>+)"
  shows "([f] \<in> PositiveReals) Xor ([g] \<in> PositiveReals)"
  using assms PositiveReals_def SlopeEquivalenceRel_def Slopes_def 
    SlopeOp1_def BoundedIntMaps_def PositiveSlopes_def PositiveIntegers_def
    int1.Int_ZF_2_3_L10 by simp

text\<open>The trichotomy law for the (potential) order on reals: if $a\neq 0$,
  then either $a$ is positive or $-a$ is potitive.\<close>

lemma (in real1) Real_ZF_1_2_L9: 
  assumes A1: "a\<in>\<real>" and A2: "a\<noteq>\<zero>"
  shows "(a \<in> PositiveReals) Xor ((\<rm>a) \<in> PositiveReals)"
proof -
  from A1 obtain f where I: "f \<in> \<S>"  "a = [f]"
    using Real_ZF_1_1_L3A by auto
  with A2 have "([f] \<in> PositiveReals) Xor ([\<fm>f] \<in> PositiveReals)"
    using Slopes_def BoundedIntMaps_def int1.Int_ZF_2_1_L12
      Real_ZF_1_2_L7 Real_ZF_1_2_L8 by simp
  with I show "(a \<in> PositiveReals) Xor ((\<rm>a) \<in> PositiveReals)"
    using Real_ZF_1_1_L4A by simp
qed

text\<open>Finally we are ready to prove that real numbers form an ordered ring
 with no zero divisors.\<close>

theorem reals_are_ord_ring: shows
  "IsAnOrdRing(RealNumbers,RealAddition,RealMultiplication,OrderOnReals)"
  "OrderOnReals {is total on} RealNumbers"
  "PositiveSet(RealNumbers,RealAddition,OrderOnReals) = PositiveReals"
  "HasNoZeroDivs(RealNumbers,RealAddition,RealMultiplication)"
proof -
  let ?R = "RealNumbers"
  let ?A = "RealAddition"
  let ?M = "RealMultiplication"
  let ?P = "PositiveReals"
  let ?r = "OrderOnReals"
  let ?z = "TheNeutralElement(?R, ?A)"
  have I:
    "ring0(?R, ?A, ?M)" 
    "?M {is commutative on} ?R"
    "?P \<subseteq> ?R"
    "?P {is closed under} ?A"
    "TheNeutralElement(?R, ?A) \<notin> ?P"
    "\<forall>a\<in>?R. a \<noteq> ?z \<longrightarrow> (a \<in> ?P) Xor (GroupInv(?R, ?A)`(a) \<in> ?P)"
    "?P {is closed under} ?M" 
    "?r = OrderFromPosSet(?R, ?A, ?P)"
    using real0.Real_ZF_1_L3 real_mult_commutative Real_ZF_1_2_L1
      real1.Real_ZF_1_2_L6 real1.Real_ZF_1_2_L9 OrderOnReals_def
    by auto
  then show "IsAnOrdRing(?R, ?A, ?M, ?r)" 
    by (rule ring0.ring_ord_by_positive_set)
  from I show "?r {is total on} ?R"
    by (rule ring0.ring_ord_by_positive_set)
  from I show "PositiveSet(?R,?A,?r) = ?P"
    by (rule ring0.ring_ord_by_positive_set)
  from I show "HasNoZeroDivs(?R,?A,?M)"
    by (rule ring0.ring_ord_by_positive_set)
qed

text\<open>All theorems proven in the \<open>ring1\<close>
  (about ordered rings), \<open>group3\<close> (about ordered groups) and
  \<open>group1\<close> (about groups)
  contexts are valid as applied to ordered real numbers with addition 
  and (real) order.\<close>

lemma Real_ZF_1_2_L10: shows 
  "ring1(RealNumbers,RealAddition,RealMultiplication,OrderOnReals)"
  "IsAnOrdGroup(RealNumbers,RealAddition,OrderOnReals)"
  "group3(RealNumbers,RealAddition,OrderOnReals)"
  "OrderOnReals {is total on} RealNumbers"
proof -
  show "ring1(RealNumbers,RealAddition,RealMultiplication,OrderOnReals)"
    using reals_are_ord_ring OrdRing_ZF_1_L2 by simp
  then show 
    "IsAnOrdGroup(RealNumbers,RealAddition,OrderOnReals)"
    "group3(RealNumbers,RealAddition,OrderOnReals)"
    "OrderOnReals {is total on} RealNumbers"
    using ring1.OrdRing_ZF_1_L4 by auto
qed

text\<open>If $a=b$ or $b-a$ is positive, then $a$ is less or equal $b$.\<close>

lemma (in real1) Real_ZF_1_2_L11: assumes A1: "a\<in>\<real>"  "b\<in>\<real>" and
  A3: "a=b \<or> b\<rs>a \<in> PositiveReals"
  shows "a\<lsq>b"
  using assms reals_are_ord_ring Real_ZF_1_2_L10 
    group3.OrderedGroup_ZF_1_L30 by simp

text\<open>A sufficient condition for two classes to be in the real order.\<close>

lemma (in real1) Real_ZF_1_2_L12: assumes A1: "f \<in> \<S>"  "g \<in> \<S>" and
  A2: "f\<sim>g \<or> (g \<fp> (\<fm>f)) \<in> \<S>\<^sub>+"
  shows "[f] \<lsq> [g]"
proof -
  from A1 A2 have "[f] = [g] \<or> [g]\<rs>[f] \<in> PositiveReals"
    using Real_ZF_1_1_L5A Real_ZF_1_2_L2 Real_ZF_1_1_L4B
    by auto
  with A1 show "[f] \<lsq> [g]" using  Real_ZF_1_1_L3 Real_ZF_1_2_L11
    by simp
qed

text\<open>Taking negative on both sides reverses the inequality, a case with
  an inverse on one side. Property of ordered groups.\<close>

lemma (in real1) Real_ZF_1_2_L13: 
  assumes A1: "a\<in>\<real>" and A2: "(\<rm>a) \<lsq> b"
  shows "(\<rm>b) \<lsq> a"
  using assms Real_ZF_1_2_L10 group3.OrderedGroup_ZF_1_L5AG
  by simp

text\<open>Real order is antisymmetric.\<close>

lemma (in real1) real_ord_antisym: 
  assumes A1: "a\<lsq>b"  "b\<lsq>a" shows "a=b"
proof -
  from A1 have
    "group3(RealNumbers,RealAddition,OrderOnReals)"
    "\<langle>a,b\<rangle> \<in> OrderOnReals"  "\<langle>b,a\<rangle> \<in> OrderOnReals"
    using Real_ZF_1_2_L10 by auto
  then show "a=b" by (rule group3.group_order_antisym)
qed
  
text\<open>Real order is transitive.\<close>

lemma (in real1) real_ord_transitive: assumes A1: "a\<lsq>b"  "b\<lsq>c"
  shows "a\<lsq>c"
proof -
  from A1 have
    "group3(RealNumbers,RealAddition,OrderOnReals)"
    "\<langle>a,b\<rangle> \<in> OrderOnReals"  "\<langle>b,c\<rangle> \<in> OrderOnReals"
    using Real_ZF_1_2_L10 by auto
  then have "\<langle>a,c\<rangle> \<in> OrderOnReals" 
    by (rule group3.Group_order_transitive)
  then show "a\<lsq>c" by simp
qed

text\<open>We can multiply both sides of an inequality 
  by a nonnegative real number.\<close>

lemma (in real1) Real_ZF_1_2_L14:
  assumes "a\<lsq>b" and "\<zero>\<lsq>c"
  shows 
  "a\<cdot>c \<lsq> b\<cdot>c"  
  "c\<cdot>a \<lsq> c\<cdot>b"
  using assms Real_ZF_1_2_L10 ring1.OrdRing_ZF_1_L9
  by auto

text\<open>A special case of \<open>Real_ZF_1_2_L14\<close>: we can multiply
  an inequality by a real number.\<close>

lemma (in real1) Real_ZF_1_2_L14A:
  assumes A1: "a\<lsq>b" and A2: "c\<in>\<real>\<^sub>+"
  shows "c\<cdot>a \<lsq> c\<cdot>b"
  using assms Real_ZF_1_2_L10 ring1.OrdRing_ZF_1_L9A
  by simp

text\<open>In the \<open>real1\<close> context notation $a\leq b$ 
  implies that $a$ and $b$ are real numbers.\<close>

lemma (in real1) Real_ZF_1_2_L15: assumes "a\<lsq>b" shows "a\<in>\<real>"  "b\<in>\<real>"
  using assms Real_ZF_1_2_L10 group3.OrderedGroup_ZF_1_L4
  by auto

text\<open>$a\leq b$ implies that $0 \leq b -a$.\<close>

lemma (in real1) Real_ZF_1_2_L16: assumes "a\<lsq>b"
  shows "\<zero> \<lsq> b\<rs>a"
  using assms Real_ZF_1_2_L10 group3.OrderedGroup_ZF_1_L12A
  by simp

text\<open>A sum of nonnegative elements is nonnegative.\<close>

lemma (in real1) Real_ZF_1_2_L17: assumes "\<zero>\<lsq>a" "\<zero>\<lsq>b"
  shows "\<zero> \<lsq> a\<ra>b"
  using assms Real_ZF_1_2_L10 group3.OrderedGroup_ZF_1_L12
  by simp

text\<open>We can add sides of two inequalities\<close>

lemma (in real1) Real_ZF_1_2_L18: assumes "a\<lsq>b"  "c\<lsq>d"
  shows "a\<ra>c \<lsq> b\<ra>d"
  using assms Real_ZF_1_2_L10 group3.OrderedGroup_ZF_1_L5B
  by simp

text\<open>The order on real is reflexive.\<close>

lemma (in real1) real_ord_refl: assumes "a\<in>\<real>" shows "a\<lsq>a"
  using assms Real_ZF_1_2_L10 group3.OrderedGroup_ZF_1_L3
  by simp

text\<open>We can add a real number to both sides of an inequality.\<close>

lemma (in real1) add_num_to_ineq: assumes "a\<lsq>b" and "c\<in>\<real>"
  shows "a\<ra>c \<lsq> b\<ra>c"
  using assms Real_ZF_1_2_L10 IsAnOrdGroup_def by simp

text\<open>We can put a number on the other side of an inequality,
  changing its sign.\<close>

lemma (in real1) Real_ZF_1_2_L19: 
  assumes "a\<in>\<real>"  "b\<in>\<real>" and "c \<lsq> a\<ra>b"
  shows "c\<rs>b \<lsq> a"
  using assms  Real_ZF_1_2_L10 group3.OrderedGroup_ZF_1_L9C
  by simp

text\<open>What happens when one real number is not greater or equal than another?\<close>

lemma (in real1) Real_ZF_1_2_L20: assumes "a\<in>\<real>"  "b\<in>\<real>" and "\<not>(a\<lsq>b)"
  shows "b \<ls> a"
proof -
  from assms have I:
    "group3(\<real>,RealAddition,OrderOnReals)"
    "OrderOnReals {is total on} \<real>"
    "a\<in>\<real>"  "b\<in>\<real>"  "\<not>(\<langle>a,b\<rangle> \<in> OrderOnReals)"
    using Real_ZF_1_2_L10 by auto
  then have "\<langle>b,a\<rangle> \<in> OrderOnReals"
    by (rule group3.OrderedGroup_ZF_1_L8)
  then have "b \<lsq> a" by simp
  moreover from I have "a\<noteq>b" by (rule group3.OrderedGroup_ZF_1_L8)
  ultimately show "b \<ls> a" by auto
qed
 
text\<open>We can put a number on the other side of an inequality,
  changing its sign, version with a minus.\<close>

lemma (in real1) Real_ZF_1_2_L21: 
  assumes "a\<in>\<real>"  "b\<in>\<real>" and "c \<lsq> a\<rs>b"
  shows "c\<ra>b \<lsq> a"
  using assms Real_ZF_1_2_L10 group3.OrderedGroup_ZF_1_L5J
  by simp

text\<open>The order on reals is a relation on reals.\<close>

lemma (in real1) Real_ZF_1_2_L22: shows "OrderOnReals \<subseteq> \<real>\<times>\<real>"
  using Real_ZF_1_2_L10 IsAnOrdGroup_def 
  by simp

text\<open>A set that is bounded above in the sense defined by order 
  on reals is a subset of real numbers.\<close>

lemma (in real1) Real_ZF_1_2_L23: 
  assumes A1: "IsBoundedAbove(A,OrderOnReals)"
  shows "A \<subseteq> \<real>"
  using A1 Real_ZF_1_2_L22 Order_ZF_3_L1A
  by blast (* A1 has to be here *)

text\<open>Properties of the maximum of three real numbers.\<close>

lemma (in real1) Real_ZF_1_2_L24:
  assumes A1: "a\<in>\<real>"  "b\<in>\<real>"  "c\<in>\<real>"
  shows
  "Maximum(OrderOnReals,{a,b,c}) \<in> {a,b,c}"
  "Maximum(OrderOnReals,{a,b,c}) \<in> \<real>"
  "a \<lsq> Maximum(OrderOnReals,{a,b,c})"
  "b \<lsq> Maximum(OrderOnReals,{a,b,c})"
  "c \<lsq> Maximum(OrderOnReals,{a,b,c})"
proof -
  have "IsLinOrder(\<real>,OrderOnReals)"
    using Real_ZF_1_2_L10 group3.group_ord_total_is_lin
    by simp
  with A1 show 
    "Maximum(OrderOnReals,{a,b,c}) \<in> {a,b,c}"
    "Maximum(OrderOnReals,{a,b,c}) \<in> \<real>"
    "a \<lsq> Maximum(OrderOnReals,{a,b,c})"
    "b \<lsq> Maximum(OrderOnReals,{a,b,c})"
    "c \<lsq> Maximum(OrderOnReals,{a,b,c})"
    using Finite_ZF_1_L2A by auto
qed

text\<open>A form of transitivity for the order on reals.\<close>

lemma (in real1) real_strict_ord_transit:
  assumes A1: "a\<lsq>b" and A2: "b\<ls>c"
  shows "a\<ls>c"
proof -
  from A1 A2 have I:
    "group3(\<real>,RealAddition,OrderOnReals)"  
    "\<langle>a,b\<rangle> \<in> OrderOnReals"  "\<langle>b,c\<rangle> \<in> OrderOnReals \<and> b\<noteq>c"
    using Real_ZF_1_2_L10 by auto
  then have "\<langle>a,c\<rangle> \<in> OrderOnReals \<and> a\<noteq>c" by (rule group3.group_strict_ord_transit)
  then show "a\<ls>c" by simp
qed

text\<open>We can multiply a right hand side of an inequality between
  positive real numbers by a number that is greater than one.\<close>

lemma (in real1) Real_ZF_1_2_L25: 
  assumes "b \<in> \<real>\<^sub>+" and "a\<lsq>b" and "\<one>\<ls>c"
  shows "a\<ls>b\<cdot>c"
  using assms reals_are_ord_ring Real_ZF_1_2_L10 ring1.OrdRing_ZF_3_L17
  by simp

text\<open>We can move a real number to the other side of a strict inequality,
  changing its sign.\<close>

lemma (in real1) Real_ZF_1_2_L26:
  assumes "a\<in>\<real>"  "b\<in>\<real>" and  "a\<rs>b \<ls> c"
  shows "a \<ls> c\<ra>b"
  using assms Real_ZF_1_2_L10 group3.OrderedGroup_ZF_1_L12B
  by simp

text\<open>Real order is translation invariant.\<close>

lemma (in real1) real_ord_transl_inv: 
  assumes "a\<lsq>b" and "c\<in>\<real>"
  shows "c\<ra>a \<lsq> c\<ra>b"
  using assms Real_ZF_1_2_L10 IsAnOrdGroup_def
  by simp

text\<open>It is convenient to have the transitivity of the order on integers
  in the notation specific to \<open>real1\<close> context. This may be confusing
  for the presentation readers: even though \<open>\<zlq>\<close> and 
  \<open>\<lsq>\<close> are printed in the same way, they are different symbols
  in the source. In the \<open>real1\<close> context the former denotes 
  inequality between integers, and the latter denotes inequality between real
  numbers (classes of slopes). The next lemma is about transitivity of the
  order relation on integers.\<close>

lemma (in real1) int_order_transitive: 
  assumes A1: "a\<zlq>b"  "b\<zlq>c"
  shows "a\<zlq>c"
proof -
  from A1 have 
    "\<langle>a,b\<rangle> \<in> IntegerOrder" and "\<langle>b,c\<rangle> \<in> IntegerOrder"
    by auto
  then have "\<langle>a,c\<rangle> \<in> IntegerOrder"
    by (rule Int_ZF_2_L5)
  then show "a\<zlq>c" by simp
qed

text\<open>A property of nonempty subsets of real numbers that don't
  have a maximum: for any element we can find one that is (strictly) greater.\<close>

lemma (in real1) Real_ZF_1_2_L27:
  assumes "A\<subseteq>\<real>" and "\<not>HasAmaximum(OrderOnReals,A)" and "x\<in>A"
  shows "\<exists>y\<in>A. x\<ls>y"
  using assms Real_ZF_1_2_L10 group3.OrderedGroup_ZF_2_L2B
  by simp

text\<open>The next lemma shows what happens when one real number 
  is not greater or equal than another.\<close>

lemma (in real1) Real_ZF_1_2_L28:
  assumes "a\<in>\<real>"  "b\<in>\<real>" and "\<not>(a\<lsq>b)"
  shows "b\<ls>a"
proof -
  from assms have
    "group3(\<real>,RealAddition,OrderOnReals)"
    "OrderOnReals {is total on} \<real>"
    "a\<in>\<real>"  "b\<in>\<real>"  "\<langle>a,b\<rangle> \<notin> OrderOnReals"
    using Real_ZF_1_2_L10 by auto
  then have "\<langle>b,a\<rangle> \<in> OrderOnReals  \<and> b\<noteq>a"
    by (rule group3.OrderedGroup_ZF_1_L8)
  then show "b\<ls>a" by simp
qed

text\<open>If a real number is less than another, then the second one can not
  be less or equal that the first.\<close>

lemma (in real1) Real_ZF_1_2_L29: 
  assumes "a\<ls>b" shows "\<not>(b\<lsq>a)"
proof -
  from assms have
    "group3(\<real>,RealAddition,OrderOnReals)"
    "\<langle>a,b\<rangle> \<in> OrderOnReals"  "a\<noteq>b"
    using Real_ZF_1_2_L10 by auto
  then have "\<langle>b,a\<rangle> \<notin> OrderOnReals"
    by (rule group3.OrderedGroup_ZF_1_L8AA)
  then show "\<not>(b\<lsq>a)" by simp
qed

subsection\<open>Inverting reals\<close>

text\<open>In this section we tackle the issue of existence of (multiplicative) 
  inverses of real numbers and show that real numbers form an 
  ordered field. We also restate here some facts specific to ordered fields
  that we need for the construction. The actual proofs of most of these facts
  can be found in \<open>Field_ZF.thy\<close> and \<open>OrderedField_ZF.thy\<close>\<close>

text\<open>We rewrite the theorem from \<open>Int_ZF_2.thy\<close> that shows
  that for every positive slope we can find one that is almost equal and
  has an inverse.\<close>

lemma (in real1) pos_slopes_have_inv: assumes "f \<in> \<S>\<^sub>+"
  shows "\<exists>g\<in>\<S>. f\<sim>g \<and> (\<exists>h\<in>\<S>. g\<circ>h \<sim> id(int))"
  using assms PositiveSlopes_def Slopes_def PositiveIntegers_def
    int1.pos_slope_has_inv SlopeOp1_def SlopeOp2_def 
    BoundedIntMaps_def SlopeEquivalenceRel_def
  by simp

text\<open>The set of real numbers we are constructing is an ordered field.\<close>

theorem (in real1) reals_are_ord_field: shows 
  "IsAnOrdField(RealNumbers,RealAddition,RealMultiplication,OrderOnReals)"
proof -
  let ?R = "RealNumbers"
  let ?A = "RealAddition"
  let ?M = "RealMultiplication"
  let ?r = "OrderOnReals"
  have "ring1(?R,?A,?M,?r)" and "\<zero> \<noteq> \<one>"
    using reals_are_ord_ring OrdRing_ZF_1_L2 real_zero_not_one
    by auto
  moreover have "?M {is commutative on} ?R"
    using real_mult_commutative by simp
  moreover have
    "\<forall>a\<in>PositiveSet(?R,?A,?r). \<exists>b\<in>?R. a\<cdot>b = \<one>"
  proof
    fix a assume "a \<in> PositiveSet(?R,?A,?r)"
    then obtain f where I: "f\<in>\<S>\<^sub>+" and II: "a = [f]"
      using reals_are_ord_ring Real_ZF_1_2_L2 
      by auto
    then have "\<exists>g\<in>\<S>. f\<sim>g \<and> (\<exists>h\<in>\<S>. g\<circ>h \<sim> id(int))"
      using pos_slopes_have_inv by simp
    then obtain g where 
      III: "g\<in>\<S>" and IV: "f\<sim>g" and V: "\<exists>h\<in>\<S>. g\<circ>h \<sim> id(int)"
      by auto
    from V obtain h where VII: "h\<in>\<S>" and VIII: "g\<circ>h \<sim> id(int)"
      by auto
    from I III IV have "[f] = [g]"
      using Real_ZF_1_2_L1 Slopes_def Real_ZF_1_1_L5
      by auto
    with II III VII VIII have "a\<cdot>[h] = \<one>"
      using Real_ZF_1_1_L4  Real_ZF_1_1_L5A real_one_cl_identity
      by simp
    with VII show "\<exists>b\<in>?R. a\<cdot>b = \<one>" using Real_ZF_1_1_L3
      by auto
  qed
  ultimately show ?thesis using ring1.OrdField_ZF_1_L4
    by simp
qed

text\<open>Reals form a field.\<close>

lemma reals_are_field: 
  shows "IsAfield(RealNumbers,RealAddition,RealMultiplication)"
  using real1.reals_are_ord_field OrdField_ZF_1_L1A
  by simp

text\<open>Theorem proven in \<open>field0\<close> and \<open>field1\<close> contexts 
  are valid as applied to real numbers.\<close>

lemma field_cntxts_ok: shows 
  "field0(RealNumbers,RealAddition,RealMultiplication)"
  "field1(RealNumbers,RealAddition,RealMultiplication,OrderOnReals)"
  using reals_are_field real1.reals_are_ord_field
     field_field0 OrdField_ZF_1_L2 by auto

text\<open>If $a$ is positive, then $a^{-1}$ is also positive.\<close>

lemma (in real1) Real_ZF_1_3_L1: assumes "a \<in> \<real>\<^sub>+" 
  shows "a\<inverse> \<in> \<real>\<^sub>+"   "a\<inverse> \<in> \<real>"
  using assms field_cntxts_ok field1.OrdField_ZF_1_L8 PositiveSet_def
  by auto

text\<open>A technical fact about multiplying strict inequality by the inverse
  of one of the sides.\<close>

lemma (in real1) Real_ZF_1_3_L2: 
  assumes "a \<in> \<real>\<^sub>+" and "a\<inverse> \<ls> b"
  shows "\<one> \<ls> b\<cdot>a"
  using assms field_cntxts_ok field1.OrdField_ZF_2_L2
  by simp

text\<open>If $a$ is smaller than $b$, then $(b-a)^{-1}$ is positive.\<close>

lemma (in real1) Real_ZF_1_3_L3: assumes "a\<ls>b"
  shows "(b\<rs>a)\<inverse> \<in> \<real>\<^sub>+" 
  using assms field_cntxts_ok field1.OrdField_ZF_1_L9
  by simp

text\<open>We can put a positive factor on the other side of a strict
  inequality, changing it to its inverse.\<close>

lemma (in real1) Real_ZF_1_3_L4:
  assumes A1: "a\<in>\<real>"  "b\<in>\<real>\<^sub>+" and A2: "a\<cdot>b \<ls> c"
  shows "a \<ls> c\<cdot>b\<inverse>"
  using assms field_cntxts_ok field1.OrdField_ZF_2_L6
  by simp

text\<open>We can put a positive factor on the other side of a strict
  inequality, changing it to its inverse, version with the product
  initially on the right hand side.\<close>

lemma (in real1) Real_ZF_1_3_L4A:
  assumes A1: "b\<in>\<real>"  "c\<in>\<real>\<^sub>+" and A2: "a \<ls> b\<cdot>c"
  shows "a\<cdot>c\<inverse> \<ls> b"
  using assms field_cntxts_ok field1.OrdField_ZF_2_L6A
  by simp

text\<open>We can put a positive factor on the other side of an inequality, 
  changing it to its inverse, version with the product
  initially on the right hand side.\<close>

lemma (in real1) Real_ZF_1_3_L4B: 
  assumes A1: "b\<in>\<real>"  "c\<in>\<real>\<^sub>+" and A2: "a \<lsq> b\<cdot>c"
  shows "a\<cdot>c\<inverse> \<lsq> b"
  using assms field_cntxts_ok field1.OrdField_ZF_2_L5A
  by simp

text\<open>We can put a positive factor on the other side of an inequality, 
  changing it to its inverse, version with the product
  initially on the left hand side.\<close>

lemma (in real1) Real_ZF_1_3_L4C: 
  assumes A1: "a\<in>\<real>"  "b\<in>\<real>\<^sub>+" and A2: "a\<cdot>b \<lsq> c"
  shows "a \<lsq> c\<cdot>b\<inverse>"
  using assms field_cntxts_ok field1.OrdField_ZF_2_L5
  by simp

text\<open>A technical lemma about solving a strict inequality with three
  real numbers and inverse of a difference.\<close>

lemma (in real1) Real_ZF_1_3_L5:
  assumes "a\<ls>b" and "(b\<rs>a)\<inverse> \<ls> c"
  shows "\<one> \<ra> a\<cdot>c \<ls> b\<cdot>c"
  using assms field_cntxts_ok field1.OrdField_ZF_2_L9
  by simp

text\<open>We can multiply an inequality by the inverse of a positive number.\<close>

lemma (in real1) Real_ZF_1_3_L6:
  assumes "a\<lsq>b"  and "c\<in>\<real>\<^sub>+" shows "a\<cdot>c\<inverse> \<lsq> b\<cdot>c\<inverse>"
  using assms field_cntxts_ok field1.OrdField_ZF_2_L3
  by simp

text\<open>We can multiply a strict inequality by a positive number or its inverse.
\<close>

lemma (in real1) Real_ZF_1_3_L7:
  assumes "a\<ls>b"  and "c\<in>\<real>\<^sub>+" shows 
  "a\<cdot>c \<ls> b\<cdot>c"
  "c\<cdot>a \<ls> c\<cdot>b"
  "a\<cdot>c\<inverse> \<ls> b\<cdot>c\<inverse>"
  using assms field_cntxts_ok field1.OrdField_ZF_2_L4
  by auto

text\<open>An identity with three real numbers, inverse and cancelling.\<close>

lemma (in real1) Real_ZF_1_3_L8: assumes"a\<in>\<real>"  "b\<in>\<real>" "b\<noteq>\<zero>"  "c\<in>\<real>"
  shows "a\<cdot>b\<cdot>(c\<cdot>b\<inverse>) = a\<cdot>c"
  using assms field_cntxts_ok field0.Field_ZF_2_L6
  by simp

subsection\<open>Completeness\<close>

text\<open>This goal of this section is to show that the order on real numbers
  is complete, that is every subset of reals that is bounded above 
  has a smallest upper bound.\<close>

text\<open>If $m$ is an integer, then \<open>m\<^sup>R\<close> is a real number.
  Recall that in \<open>real1\<close> context \<open>m\<^sup>R\<close> denotes the class
  of the slope $n\mapsto m\cdot n$.\<close>

lemma (in real1) real_int_is_real: assumes "m \<in> int"
  shows "m\<^sup>R \<in> \<real>"
  using assms int1.Int_ZF_2_5_L1 Real_ZF_1_1_L3 by simp

text\<open>The negative of the real embedding of an integer is the embedding
  of the negative of the integer.\<close>

lemma (in real1) Real_ZF_1_4_L1: assumes "m \<in> int"
  shows "(\<zm>m)\<^sup>R = \<rm>(m\<^sup>R)"
  using assms int1.Int_ZF_2_5_L3 int1.Int_ZF_2_5_L1 Real_ZF_1_1_L4A
  by simp

text\<open>The embedding of sum of integers is the sum of embeddings.\<close>

lemma (in real1) Real_ZF_1_4_L1A: assumes "m \<in> int"  "k \<in> int"
  shows "m\<^sup>R \<ra> k\<^sup>R = ((m\<za>k)\<^sup>R)"
  using assms int1.Int_ZF_2_5_L1 SlopeOp1_def int1.Int_ZF_2_5_L3A 
    Real_ZF_1_1_L4 by simp

text\<open>The embedding of a difference of integers is the difference
  of embeddings.\<close>

lemma (in real1) Real_ZF_1_4_L1B: assumes A1: "m \<in> int"  "k \<in> int"
  shows "m\<^sup>R \<rs> k\<^sup>R = (m\<zs>k)\<^sup>R"
proof -
  from A1 have "(\<zm>k) \<in> int" using int0.Int_ZF_1_1_L4
    by simp
  with A1 have "(m\<zs>k)\<^sup>R = m\<^sup>R \<ra> (\<zm>k)\<^sup>R"
    using Real_ZF_1_4_L1A by simp
  with A1 show "m\<^sup>R \<rs> k\<^sup>R = (m\<zs>k)\<^sup>R"
    using Real_ZF_1_4_L1 by simp
qed

text\<open>The embedding of the product of integers is the product of embeddings.\<close>

lemma (in real1) Real_ZF_1_4_L1C: assumes "m \<in> int"  "k \<in> int"
  shows "m\<^sup>R \<cdot> k\<^sup>R = (m\<zmu>k)\<^sup>R"
  using assms int1.Int_ZF_2_5_L1 SlopeOp2_def int1.Int_ZF_2_5_L3B
    Real_ZF_1_1_L4 by simp

text\<open>For any real numbers there is an integer whose real version is
  greater or equal.\<close>

lemma (in real1) Real_ZF_1_4_L2: assumes A1: "a\<in>\<real>"
  shows "\<exists>m\<in>int. a \<lsq> m\<^sup>R"
proof -
  from A1 obtain f where I: "f\<in>\<S>" and II: "a = [f]"
    using Real_ZF_1_1_L3A by auto
  then have "\<exists>m\<in>int. \<exists>g\<in>\<S>.
    {\<langle>n,m\<zmu>n\<rangle> . n \<in> int} \<sim> g \<and> (f\<sim>g \<or> (g \<fp> (\<fm>f)) \<in> \<S>\<^sub>+)"
    using int1.Int_ZF_2_5_L2 Slopes_def SlopeOp1_def 
      BoundedIntMaps_def SlopeEquivalenceRel_def 
      PositiveIntegers_def PositiveSlopes_def
    by simp
  then obtain m g where III: "m\<in>int" and IV: "g\<in>\<S>" and
   "{\<langle>n,m\<zmu>n\<rangle> . n \<in> int} \<sim> g \<and> (f\<sim>g \<or> (g \<fp> (\<fm>f)) \<in> \<S>\<^sub>+)"
    by auto
  then have "m\<^sup>R = [g]" and "f \<sim> g \<or> (g \<fp> (\<fm>f)) \<in> \<S>\<^sub>+"
    using Real_ZF_1_1_L5A by auto
  with I II IV have "a \<lsq> m\<^sup>R" using Real_ZF_1_2_L12
    by simp
  with III show "\<exists>m\<in>int. a \<lsq> m\<^sup>R" by auto
qed

text\<open>For any real numbers there is an integer whose real version (embedding) 
  is less or equal.\<close>

lemma (in real1) Real_ZF_1_4_L3: assumes A1: "a\<in>\<real>"
  shows "{m \<in> int. m\<^sup>R \<lsq> a} \<noteq> 0"
proof -
  from A1 have "(\<rm>a) \<in> \<real>" using Real_ZF_1_1_L8
    by simp
  then obtain m where I: "m\<in>int" and II: "(\<rm>a) \<lsq> m\<^sup>R"
    using Real_ZF_1_4_L2 by auto
  let ?k = "GroupInv(int,IntegerAddition)`(m)"
  from A1 I II have "?k \<in> int" and "?k\<^sup>R \<lsq> a"
    using Real_ZF_1_2_L13 Real_ZF_1_4_L1 int0.Int_ZF_1_1_L4
    by auto
  then show ?thesis by auto
qed

text\<open>Embeddings of two integers are equal only if the integers are equal.\<close>

lemma (in real1) Real_ZF_1_4_L4: 
  assumes A1: "m \<in> int"  "k \<in> int" and A2: "m\<^sup>R = k\<^sup>R"
  shows "m=k"
proof -
  let ?r = "{\<langle>n, IntegerMultiplication ` \<langle>m, n\<rangle>\<rangle> . n \<in> int}"
  let ?s = "{\<langle>n, IntegerMultiplication ` \<langle>k, n\<rangle>\<rangle> . n \<in> int}"
  from A1 A2 have "?r \<sim> ?s"
    using int1.Int_ZF_2_5_L1 AlmostHoms_def Real_ZF_1_1_L5
    by simp
  with A1 have 
    "m \<in> int"  "k \<in> int"
    "\<langle>?r,?s\<rangle> \<in> QuotientGroupRel(AlmostHoms(int, IntegerAddition),
    AlHomOp1(int, IntegerAddition),FinRangeFunctions(int, int))"
    using SlopeEquivalenceRel_def Slopes_def SlopeOp1_def 
      BoundedIntMaps_def by auto
  then show "m=k" by (rule int1.Int_ZF_2_5_L6)
qed

text\<open>The embedding of integers preserves the order.\<close>

lemma (in real1) Real_ZF_1_4_L5: assumes A1: "m\<zlq>k"
  shows "m\<^sup>R \<lsq> k\<^sup>R"
proof -
  let ?r = "{\<langle>n, m\<zmu>n\<rangle> . n \<in> int}"
  let ?s = "{\<langle>n, k\<zmu>n\<rangle> . n \<in> int}"
  from A1 have "?r \<in> \<S>"  "?s \<in> \<S>"
    using int0.Int_ZF_2_L1A int1.Int_ZF_2_5_L1 by auto
  moreover from A1 have "?r \<sim> ?s \<or> ?s \<fp> (\<fm>?r)  \<in> \<S>\<^sub>+"
    using Slopes_def SlopeOp1_def BoundedIntMaps_def SlopeEquivalenceRel_def
      PositiveIntegers_def PositiveSlopes_def
      int1.Int_ZF_2_5_L4 by simp
  ultimately show "m\<^sup>R \<lsq> k\<^sup>R" using Real_ZF_1_2_L12
    by simp
qed

text\<open>The embedding of integers preserves the strict order.\<close>

lemma (in real1) Real_ZF_1_4_L5A: assumes A1: "m\<zlq>k"  "m\<noteq>k"
  shows "m\<^sup>R \<ls> k\<^sup>R"
proof -
  from A1 have "m\<^sup>R \<lsq> k\<^sup>R" using Real_ZF_1_4_L5
    by simp
  moreover
  from A1 have T: "m \<in> int"  "k \<in> int"
    using int0.Int_ZF_2_L1A by auto
  with A1 have "m\<^sup>R \<noteq> k\<^sup>R" using Real_ZF_1_4_L4
    by auto
  ultimately show "m\<^sup>R \<ls> k\<^sup>R" by simp
qed

text\<open>For any real number there is a positive integer
  whose real version is (strictly) greater. 
  This is Lemma 14 i) in  \cite{Arthan2004}.\<close>

lemma (in real1) Arthan_Lemma14i: assumes A1: "a\<in>\<real>"
  shows "\<exists>n\<in>\<int>\<^sub>+. a \<ls> n\<^sup>R"
proof -
  from A1 obtain m where I: "m\<in>int" and II: "a \<lsq> m\<^sup>R"
    using Real_ZF_1_4_L2 by auto
  let ?n = "GreaterOf(IntegerOrder,\<one>\<^sub>Z,m) \<za> \<one>\<^sub>Z"
  from I have T: "?n \<in>\<int>\<^sub>+" and "m \<zlq> ?n"  "m\<noteq>?n"
    using int0.Int_ZF_1_5_L7B by auto
  then have III: "m\<^sup>R \<ls> ?n\<^sup>R"
    using Real_ZF_1_4_L5A by simp
  with II have "a \<ls> ?n\<^sup>R" by (rule real_strict_ord_transit)
  with T show ?thesis by auto
qed

text\<open>If one embedding is less or equal than another, then the integers
  are also less or equal.\<close>

lemma (in real1) Real_ZF_1_4_L6: 
  assumes A1: "k \<in> int"  "m \<in> int" and A2: "m\<^sup>R \<lsq> k\<^sup>R"
  shows "m\<zlq>k"
proof -
  { assume A3: "\<langle>m,k\<rangle> \<notin> IntegerOrder"
    with A1 have "\<langle>k,m\<rangle> \<in> IntegerOrder"
      by (rule int0.Int_ZF_2_L19)
    then have "k\<^sup>R \<lsq> m\<^sup>R" using Real_ZF_1_4_L5
      by simp
    with A2 have "m\<^sup>R = k\<^sup>R" by (rule real_ord_antisym)
    with A1 have "k = m" using Real_ZF_1_4_L4
      by auto
    moreover from A1 A3 have "k\<noteq>m" by (rule int0.Int_ZF_2_L19)
    ultimately have False by simp
  } then show "m\<zlq>k" by auto
qed
    
text\<open>The floor function is well defined and has expected properties.\<close>

lemma (in real1) Real_ZF_1_4_L7: assumes A1: "a\<in>\<real>"
  shows 
  "IsBoundedAbove({m \<in> int. m\<^sup>R \<lsq> a},IntegerOrder)"
  "{m \<in> int. m\<^sup>R \<lsq> a} \<noteq> 0"
  "\<lfloor>a\<rfloor> \<in> int"
  "\<lfloor>a\<rfloor>\<^sup>R \<lsq> a"  
proof -
  let ?A = "{m \<in> int. m\<^sup>R \<lsq> a}"
  from A1 obtain K where I: "K\<in>int" and II: "a \<lsq> (K\<^sup>R)"
    using Real_ZF_1_4_L2 by auto
  { fix n assume "n \<in> ?A"
    then have III: "n \<in> int" and IV: "n\<^sup>R \<lsq> a"
      by auto
    from IV II have "(n\<^sup>R) \<lsq> (K\<^sup>R)"
      by (rule real_ord_transitive)
    with I III have "n\<zlq>K" using Real_ZF_1_4_L6
      by simp
  } then have "\<forall>n\<in>?A. \<langle>n,K\<rangle> \<in> IntegerOrder"
    by simp
  then show "IsBoundedAbove(?A,IntegerOrder)"
    by (rule Order_ZF_3_L10)
  moreover from A1 show "?A \<noteq> 0" using Real_ZF_1_4_L3
    by simp
  ultimately have "Maximum(IntegerOrder,?A) \<in> ?A"
    by (rule int0.int_bounded_above_has_max)
  then show "\<lfloor>a\<rfloor> \<in> int"   "\<lfloor>a\<rfloor>\<^sup>R \<lsq> a" by auto
qed

text\<open>Every integer whose embedding is less or equal a real number $a$
  is less or equal than the floor of $a$.\<close>

lemma (in real1) Real_ZF_1_4_L8: 
  assumes A1: "m \<in> int" and A2: "m\<^sup>R \<lsq> a"
  shows "m \<zlq> \<lfloor>a\<rfloor>"
proof -
  let ?A = "{m \<in> int. m\<^sup>R \<lsq> a}"
  from A2 have "IsBoundedAbove(?A,IntegerOrder)" and "?A\<noteq>0"
    using Real_ZF_1_2_L15 Real_ZF_1_4_L7 by auto
  then have "\<forall>x\<in>?A. \<langle>x,Maximum(IntegerOrder,?A)\<rangle> \<in> IntegerOrder"
    by (rule int0.int_bounded_above_has_max)
  with A1 A2 show "m \<zlq> \<lfloor>a\<rfloor>" by simp
qed

text\<open>Integer zero and one embed as real zero and one.\<close>

lemma (in real1) int_0_1_are_real_zero_one: 
  shows "\<zero>\<^sub>Z\<^sup>R = \<zero>"  "\<one>\<^sub>Z\<^sup>R = \<one>"
  using int1.Int_ZF_2_5_L7 BoundedIntMaps_def 
    real_one_cl_identity real_zero_cl_bounded_map
  by auto

text\<open>Integer two embeds as the real two.\<close>

lemma (in real1) int_two_is_real_two: shows "\<two>\<^sub>Z\<^sup>R = \<two>"
proof -
  have "\<two>\<^sub>Z\<^sup>R = \<one>\<^sub>Z\<^sup>R \<ra> \<one>\<^sub>Z\<^sup>R"
    using int0.int_zero_one_are_int Real_ZF_1_4_L1A
    by simp
  also have "\<dots> = \<two>" using int_0_1_are_real_zero_one
    by simp
  finally show "\<two>\<^sub>Z\<^sup>R = \<two>" by simp
qed

text\<open>A positive integer embeds as a positive (hence nonnegative) real.\<close>

lemma (in real1) int_pos_is_real_pos: assumes A1: "p\<in>\<int>\<^sub>+"
  shows 
  "p\<^sup>R \<in> \<real>"
  "\<zero> \<lsq> p\<^sup>R"
  "p\<^sup>R \<in> \<real>\<^sub>+"
proof -
  from A1 have I: "p \<in> int"  "\<zero>\<^sub>Z \<zlq> p"  "\<zero>\<^sub>Z \<noteq> p"
    using PositiveSet_def by auto
  then have "p\<^sup>R \<in> \<real>"  "\<zero>\<^sub>Z\<^sup>R \<lsq> p\<^sup>R"
    using real_int_is_real Real_ZF_1_4_L5 by auto
  then show "p\<^sup>R \<in> \<real>"  "\<zero> \<lsq> p\<^sup>R"
    using int_0_1_are_real_zero_one by auto
  moreover have "\<zero> \<noteq> p\<^sup>R"
  proof -
    { assume "\<zero> = p\<^sup>R"
      with I have False using int_0_1_are_real_zero_one 	
	int0.int_zero_one_are_int Real_ZF_1_4_L4 by auto
    } then show "\<zero> \<noteq> p\<^sup>R" by auto
  qed
  ultimately show "p\<^sup>R \<in> \<real>\<^sub>+" using PositiveSet_def
    by simp
qed

text\<open>The ordered field of reals we are constructing is archimedean, i.e., 
  if $x,y$ are its elements with $y$ positive, then there is a positive
  integer $M$ such that $x$ is smaller than $M^R y$. This is Lemma 14 ii) in \cite{Arthan2004}.\<close>

lemma (in real1) Arthan_Lemma14ii: assumes A1: "x\<in>\<real>"  "y \<in> \<real>\<^sub>+"
  shows "\<exists>M\<in>\<int>\<^sub>+. x \<ls> M\<^sup>R\<cdot>y"
proof -
  from A1 have 
    "\<exists>C\<in>\<int>\<^sub>+. x \<ls> C\<^sup>R" and "\<exists>D\<in>\<int>\<^sub>+. y\<inverse> \<ls> D\<^sup>R"
    using Real_ZF_1_3_L1 Arthan_Lemma14i by auto
  then obtain C D where 
    I: "C\<in>\<int>\<^sub>+" and II: "x \<ls> C\<^sup>R" and
    III: "D\<in>\<int>\<^sub>+" and IV: "y\<inverse> \<ls> D\<^sup>R"
    by auto
  let ?M = "C\<zmu>D"
  from I III have 
    T: "?M \<in> \<int>\<^sub>+"  "C\<^sup>R \<in> \<real>"  "D\<^sup>R \<in> \<real>"
    using int0.pos_int_closed_mul_unfold PositiveSet_def real_int_is_real
    by auto
  with A1 I III have "C\<^sup>R\<cdot>(D\<^sup>R\<cdot>y) = ?M\<^sup>R\<cdot>y"
    using PositiveSet_def Real_ZF_1_L6A Real_ZF_1_4_L1C
    by simp
  moreover from A1 I II IV have 
    "x \<ls> C\<^sup>R\<cdot>(D\<^sup>R\<cdot>y)"
    using int_pos_is_real_pos Real_ZF_1_3_L2 Real_ZF_1_2_L25
    by auto
  ultimately have "x \<ls> ?M\<^sup>R\<cdot>y"
    by auto
  with T show ?thesis by auto
qed

text\<open>Taking the floor function preserves the order.\<close>

lemma (in real1) Real_ZF_1_4_L9: assumes A1: "a\<lsq>b"
  shows "\<lfloor>a\<rfloor> \<zlq> \<lfloor>b\<rfloor>"
proof -
  from A1 have T: "a\<in>\<real>" using Real_ZF_1_2_L15
    by simp
  with A1 have "\<lfloor>a\<rfloor>\<^sup>R \<lsq> a" and "a\<lsq>b"
    using Real_ZF_1_4_L7 by auto
  then have "\<lfloor>a\<rfloor>\<^sup>R \<lsq> b" by (rule real_ord_transitive)
  moreover from T have "\<lfloor>a\<rfloor> \<in> int" using Real_ZF_1_4_L7
    by simp
 ultimately show "\<lfloor>a\<rfloor> \<zlq> \<lfloor>b\<rfloor>" using Real_ZF_1_4_L8
   by simp
qed

text\<open>If $S$ is bounded above and $p$ is a positive intereger, then
  $\Gamma(S,p)$ is well defined.\<close>

lemma (in real1) Real_ZF_1_4_L10: 
  assumes A1: "IsBoundedAbove(S,OrderOnReals)"  "S\<noteq>0" and A2: "p\<in>\<int>\<^sub>+"
  shows 
  "IsBoundedAbove({\<lfloor>p\<^sup>R\<cdot>x\<rfloor>. x\<in>S},IntegerOrder)"
  "\<Gamma>(S,p) \<in> {\<lfloor>p\<^sup>R\<cdot>x\<rfloor>. x\<in>S}"
  "\<Gamma>(S,p) \<in> int"
proof -
  let ?A = "{\<lfloor>p\<^sup>R\<cdot>x\<rfloor>. x\<in>S}"
  from A1 obtain X where I: "\<forall>x\<in>S. x\<lsq>X" 
    using IsBoundedAbove_def by auto
  { fix m assume "m \<in> ?A"
    then obtain x where "x\<in>S" and II: "m = \<lfloor>p\<^sup>R\<cdot>x\<rfloor>"
      by auto
    with I have "x\<lsq>X" by simp
    moreover from A2 have "\<zero> \<lsq> p\<^sup>R" using int_pos_is_real_pos
      by simp
    ultimately have "p\<^sup>R\<cdot>x \<lsq> p\<^sup>R\<cdot>X" using Real_ZF_1_2_L14
      by simp
    with II have "m \<zlq> \<lfloor>p\<^sup>R\<cdot>X\<rfloor>" using Real_ZF_1_4_L9
      by simp
  } then have "\<forall>m\<in>?A. \<langle>m,\<lfloor>p\<^sup>R\<cdot>X\<rfloor>\<rangle> \<in> IntegerOrder"
    by auto
  then show II: "IsBoundedAbove(?A,IntegerOrder)" 
    by (rule Order_ZF_3_L10)
  moreover from A1 have III: "?A \<noteq> 0" by simp
  ultimately have "Maximum(IntegerOrder,?A) \<in> ?A"
    by (rule int0.int_bounded_above_has_max)
  moreover from II III have "Maximum(IntegerOrder,?A) \<in> int"
    by (rule int0.int_bounded_above_has_max)
  ultimately show "\<Gamma>(S,p) \<in> {\<lfloor>p\<^sup>R\<cdot>x\<rfloor>. x\<in>S}" and "\<Gamma>(S,p) \<in> int" 
    by auto
qed

text\<open>If $p$ is a positive integer, then
  for all $s\in S$ the floor of $p\cdot x$ is not greater that $\Gamma(S,p)$.\<close>

lemma (in real1) Real_ZF_1_4_L11:
  assumes A1: "IsBoundedAbove(S,OrderOnReals)" and A2: "x\<in>S" and A3: "p\<in>\<int>\<^sub>+"
  shows "\<lfloor>p\<^sup>R\<cdot>x\<rfloor> \<zlq> \<Gamma>(S,p)"
proof -
  let ?A = "{\<lfloor>p\<^sup>R\<cdot>x\<rfloor>. x\<in>S}"
  from A2 have "S\<noteq>0" by auto
  with A1 A3 have "IsBoundedAbove(?A,IntegerOrder)"  "?A \<noteq> 0"
    using  Real_ZF_1_4_L10 by auto
  then have "\<forall>x\<in>?A. \<langle>x,Maximum(IntegerOrder,?A)\<rangle> \<in> IntegerOrder"
    by (rule int0.int_bounded_above_has_max)
  with A2 show "\<lfloor>p\<^sup>R\<cdot>x\<rfloor> \<zlq> \<Gamma>(S,p)" by simp
qed

text\<open>The candidate for supremum is an integer mapping with values 
  given by $\Gamma$.\<close>

lemma (in real1) Real_ZF_1_4_L12: 
  assumes A1: "IsBoundedAbove(S,OrderOnReals)"  "S\<noteq>0" and 
  A2: "g = {\<langle>p,\<Gamma>(S,p)\<rangle>. p\<in>\<int>\<^sub>+}"
  shows 
  "g : \<int>\<^sub>+\<rightarrow>int"
  "\<forall>n\<in>\<int>\<^sub>+. g`(n) = \<Gamma>(S,n)"
proof -
  from A1 have "\<forall>n\<in>\<int>\<^sub>+. \<Gamma>(S,n) \<in> int" using Real_ZF_1_4_L10
    by simp
  with A2 show I: "g : \<int>\<^sub>+\<rightarrow>int" using ZF_fun_from_total by simp
  { fix n assume "n\<in>\<int>\<^sub>+"
    with A2 I have "g`(n) = \<Gamma>(S,n)" using ZF_fun_from_tot_val
      by simp
  } then show "\<forall>n\<in>\<int>\<^sub>+. g`(n) = \<Gamma>(S,n)" by simp
qed

text\<open>Every integer is equal to the floor of its embedding.\<close>

lemma (in real1) Real_ZF_1_4_L14: assumes A1: "m \<in> int"
  shows "\<lfloor>m\<^sup>R\<rfloor> = m"
proof -
  let ?A = "{n \<in> int. n\<^sup>R \<lsq> m\<^sup>R }"
  have "antisym(IntegerOrder)" using int0.Int_ZF_2_L4
    by simp  
  moreover from A1 have "m \<in> ?A" 
    using real_int_is_real real_ord_refl by auto
  moreover from A1 have "\<forall>n \<in> ?A. \<langle>n,m\<rangle> \<in> IntegerOrder"
    using Real_ZF_1_4_L6 by auto
  ultimately show "\<lfloor>m\<^sup>R\<rfloor> = m" using Order_ZF_4_L14
    by auto
qed

text\<open>Floor of (real) zero is (integer) zero.\<close>

lemma (in real1) floor_01_is_zero_one: shows 
  "\<lfloor>\<zero>\<rfloor> = \<zero>\<^sub>Z"   "\<lfloor>\<one>\<rfloor> = \<one>\<^sub>Z"
proof -
  have "\<lfloor>(\<zero>\<^sub>Z)\<^sup>R\<rfloor> = \<zero>\<^sub>Z" and "\<lfloor>(\<one>\<^sub>Z)\<^sup>R\<rfloor> = \<one>\<^sub>Z"
    using int0.int_zero_one_are_int Real_ZF_1_4_L14
    by auto
  then show "\<lfloor>\<zero>\<rfloor> = \<zero>\<^sub>Z" and  "\<lfloor>\<one>\<rfloor> = \<one>\<^sub>Z"
    using int_0_1_are_real_zero_one
    by auto
qed

text\<open>Floor of (real) two is (integer) two.\<close>

lemma (in real1) floor_2_is_two: shows "\<lfloor>\<two>\<rfloor> = \<two>\<^sub>Z"
proof -
  have "\<lfloor>(\<two>\<^sub>Z)\<^sup>R\<rfloor> = \<two>\<^sub>Z" 
    using int0.int_two_three_are_int Real_ZF_1_4_L14 
    by simp
  then show "\<lfloor>\<two>\<rfloor> = \<two>\<^sub>Z" using int_two_is_real_two
    by simp
qed

text\<open>Floor of a product of embeddings of integers is equal to the
  product of integers.\<close>

lemma (in real1) Real_ZF_1_4_L14A: assumes A1: "m \<in> int"  "k \<in> int"
  shows  "\<lfloor>m\<^sup>R\<cdot>k\<^sup>R\<rfloor> = m\<zmu>k"
proof -
  from A1 have T: "m\<zmu>k \<in> int"
    using int0.Int_ZF_1_1_L5 by simp
  from A1 have "\<lfloor>m\<^sup>R\<cdot>k\<^sup>R\<rfloor> = \<lfloor>(m\<zmu>k)\<^sup>R\<rfloor>" using Real_ZF_1_4_L1C
    by simp
  with T show "\<lfloor>m\<^sup>R\<cdot>k\<^sup>R\<rfloor> = m\<zmu>k" using Real_ZF_1_4_L14
    by simp
qed

text\<open>Floor of the sum of a number and the embedding of an
  integer is the floor of the number plus the integer.\<close>

lemma (in real1) Real_ZF_1_4_L15: assumes A1: "x\<in>\<real>" and A2: "p \<in> int"
  shows "\<lfloor>x \<ra> p\<^sup>R\<rfloor> = \<lfloor>x\<rfloor> \<za> p"
proof -
  let ?A = "{n \<in> int. n\<^sup>R \<lsq> x \<ra> p\<^sup>R}"
  have "antisym(IntegerOrder)" using int0.Int_ZF_2_L4
    by simp
  moreover have "\<lfloor>x\<rfloor> \<za> p \<in> ?A"
  proof -
    from A1 A2 have "\<lfloor>x\<rfloor>\<^sup>R \<lsq> x" and "p\<^sup>R \<in> \<real>"
      using Real_ZF_1_4_L7 real_int_is_real by auto
    then have "\<lfloor>x\<rfloor>\<^sup>R \<ra> p\<^sup>R \<lsq> x \<ra> p\<^sup>R"
      using add_num_to_ineq by simp
    moreover from A1 A2 have "(\<lfloor>x\<rfloor> \<za> p)\<^sup>R = \<lfloor>x\<rfloor>\<^sup>R \<ra> p\<^sup>R"
      using Real_ZF_1_4_L7 Real_ZF_1_4_L1A by simp
    ultimately have "(\<lfloor>x\<rfloor> \<za> p)\<^sup>R \<lsq> x \<ra> p\<^sup>R"
      by simp
    moreover from A1 A2 have "\<lfloor>x\<rfloor> \<za> p \<in> int"
      using Real_ZF_1_4_L7 int0.Int_ZF_1_1_L5 by simp
    ultimately show "\<lfloor>x\<rfloor> \<za> p \<in> ?A" by auto
  qed
  moreover have "\<forall>n\<in>?A. n \<zlq> \<lfloor>x\<rfloor> \<za> p"
  proof
    fix n assume "n\<in>?A"
    then have I: "n \<in> int" and "n\<^sup>R \<lsq> x \<ra> p\<^sup>R"
      by auto
    with A1 A2 have "n\<^sup>R \<rs> p\<^sup>R \<lsq> x"
      using real_int_is_real Real_ZF_1_2_L19
      by simp
    with A2 I have "\<lfloor>(n\<zs>p)\<^sup>R\<rfloor> \<zlq> \<lfloor>x\<rfloor>"
      using Real_ZF_1_4_L1B Real_ZF_1_4_L9
      by simp
    moreover
    from A2 I have "n\<zs>p \<in> int"
      using int0.Int_ZF_1_1_L5 by simp
    then have "\<lfloor>(n\<zs>p)\<^sup>R\<rfloor> = n\<zs>p"
      using Real_ZF_1_4_L14 by simp
    ultimately have "n\<zs>p \<zlq> \<lfloor>x\<rfloor>"
      by simp
    with A2 I show "n \<zlq> \<lfloor>x\<rfloor> \<za> p"
      using int0.Int_ZF_2_L9C by simp
  qed
  ultimately show "\<lfloor>x \<ra> p\<^sup>R\<rfloor> = \<lfloor>x\<rfloor> \<za> p"
    using Order_ZF_4_L14 by auto
qed

text\<open>Floor of the difference of a number and the embedding of an
  integer is the floor of the number minus the integer.\<close>

lemma (in real1) Real_ZF_1_4_L16: assumes A1: "x\<in>\<real>" and A2: "p \<in> int"
  shows "\<lfloor>x \<rs> p\<^sup>R\<rfloor> = \<lfloor>x\<rfloor> \<zs> p"
proof -
  from A2 have "\<lfloor>x \<rs> p\<^sup>R\<rfloor> = \<lfloor>x \<ra> (\<zm>p)\<^sup>R\<rfloor>"
     using Real_ZF_1_4_L1 by simp
  with A1 A2 show "\<lfloor>x \<rs> p\<^sup>R\<rfloor> = \<lfloor>x\<rfloor> \<zs> p"
    using int0.Int_ZF_1_1_L4 Real_ZF_1_4_L15 by simp
qed

text\<open>The floor of sum of embeddings is the sum of the integers.\<close>

lemma (in real1) Real_ZF_1_4_L17: assumes "m \<in> int"  "n \<in> int"
  shows "\<lfloor>(m\<^sup>R) \<ra> n\<^sup>R\<rfloor> = m \<za> n"
  using assms real_int_is_real Real_ZF_1_4_L15 Real_ZF_1_4_L14
  by simp

text\<open>A lemma about adding one to floor.\<close>

lemma (in real1) Real_ZF_1_4_L17A: assumes A1: "a\<in>\<real>"
  shows "\<one> \<ra> \<lfloor>a\<rfloor>\<^sup>R = (\<one>\<^sub>Z \<za> \<lfloor>a\<rfloor>)\<^sup>R"
proof -
  have "\<one> \<ra> \<lfloor>a\<rfloor>\<^sup>R = \<one>\<^sub>Z\<^sup>R \<ra> \<lfloor>a\<rfloor>\<^sup>R"
    using int_0_1_are_real_zero_one by simp
  with A1 show "\<one> \<ra> \<lfloor>a\<rfloor>\<^sup>R = (\<one>\<^sub>Z \<za> \<lfloor>a\<rfloor>)\<^sup>R"
    using int0.int_zero_one_are_int Real_ZF_1_4_L7 Real_ZF_1_4_L1A
    by simp
qed

text\<open>The difference between the a number and the embedding of its floor
  is (strictly) less than one.\<close>

lemma (in real1) Real_ZF_1_4_L17B: assumes A1: "a\<in>\<real>"
  shows 
  "a \<rs> \<lfloor>a\<rfloor>\<^sup>R \<ls> \<one>"
  "a \<ls> (\<one>\<^sub>Z \<za> \<lfloor>a\<rfloor>)\<^sup>R"
proof -
  from A1 have T1: "\<lfloor>a\<rfloor> \<in> int"  "\<lfloor>a\<rfloor>\<^sup>R \<in> \<real>" and
    T2: "\<one> \<in> \<real>"  "a \<rs>  \<lfloor>a\<rfloor>\<^sup>R \<in> \<real>"
    using Real_ZF_1_4_L7 real_int_is_real Real_ZF_1_L6 Real_ZF_1_L4
    by auto
  { assume "\<one> \<lsq> a \<rs>  \<lfloor>a\<rfloor>\<^sup>R"
    with A1 T1 have "\<lfloor>\<one>\<^sub>Z\<^sup>R \<ra> \<lfloor>a\<rfloor>\<^sup>R\<rfloor> \<zlq> \<lfloor>a\<rfloor>"
      using Real_ZF_1_2_L21 Real_ZF_1_4_L9 int_0_1_are_real_zero_one 
      by simp
    with T1 have False 
      using int0.int_zero_one_are_int Real_ZF_1_4_L17
      int0.Int_ZF_1_2_L3AA by simp
  } then have I: "\<not>(\<one> \<lsq> a \<rs> \<lfloor>a\<rfloor>\<^sup>R)" by auto
  with T2 show II: "a \<rs> \<lfloor>a\<rfloor>\<^sup>R \<ls> \<one>"
    by (rule Real_ZF_1_2_L20)
   with A1 T1 I II have 
    "a \<ls> \<one> \<ra> \<lfloor>a\<rfloor>\<^sup>R"
    using Real_ZF_1_2_L26 by simp
  with A1 show "a \<ls> (\<one>\<^sub>Z \<za> \<lfloor>a\<rfloor>)\<^sup>R"
    using Real_ZF_1_4_L17A by simp
qed

text\<open>The next lemma corresponds to Lemma 14 iii) in \cite{Arthan2004}.
  It says that we can find a rational number between any two different
  real numbers.\<close>

lemma (in real1) Arthan_Lemma14iii: assumes A1: "x\<ls>y"
  shows "\<exists>M\<in>int. \<exists>N\<in>\<int>\<^sub>+.  x\<cdot>N\<^sup>R \<ls> M\<^sup>R \<and> M\<^sup>R \<ls> y\<cdot>N\<^sup>R"
proof -
  from A1 have "(y\<rs>x)\<inverse> \<in> \<real>\<^sub>+" using Real_ZF_1_3_L3
    by simp
  then have 
    "\<exists>N\<in>\<int>\<^sub>+. (y\<rs>x)\<inverse> \<ls> N\<^sup>R"
    using Arthan_Lemma14i PositiveSet_def by simp
  then obtain N where I: "N\<in>\<int>\<^sub>+" and II: "(y\<rs>x)\<inverse> \<ls> N\<^sup>R"
    by auto
  let ?M = "\<one>\<^sub>Z \<za> \<lfloor>x\<cdot>N\<^sup>R\<rfloor>"
  from A1 I have 
    T1: "x\<in>\<real>"  "N\<^sup>R \<in> \<real>"  "N\<^sup>R \<in> \<real>\<^sub>+"  "x\<cdot>N\<^sup>R \<in> \<real>"
    using Real_ZF_1_2_L15 PositiveSet_def real_int_is_real
      Real_ZF_1_L6 int_pos_is_real_pos by auto
  then have T2: "?M \<in> int" using
    int0.int_zero_one_are_int Real_ZF_1_4_L7 int0.Int_ZF_1_1_L5 
    by simp
  from T1 have III: "x\<cdot>N\<^sup>R \<ls> ?M\<^sup>R"
    using Real_ZF_1_4_L17B by simp
  from T1 have "(\<one> \<ra> \<lfloor>x\<cdot>N\<^sup>R\<rfloor>\<^sup>R) \<lsq> (\<one> \<ra> x\<cdot>N\<^sup>R)"
    using Real_ZF_1_4_L7  Real_ZF_1_L4 real_ord_transl_inv 
    by simp
  with T1 have "?M\<^sup>R \<lsq> (\<one> \<ra> x\<cdot>N\<^sup>R)"
    using Real_ZF_1_4_L17A by simp
  moreover from A1 II have "(\<one> \<ra> x\<cdot>N\<^sup>R) \<ls> y\<cdot>N\<^sup>R"
    using Real_ZF_1_3_L5 by simp
  ultimately have "?M\<^sup>R \<ls> y\<cdot>N\<^sup>R"
    by (rule real_strict_ord_transit)
  with I T2 III show ?thesis by auto
qed

text\<open>Some estimates for the homomorphism difference of the floor
  function.\<close>

lemma (in real1) Real_ZF_1_4_L18: assumes A1: "x\<in>\<real>"  "y\<in>\<real>"
  shows 
  "abs(\<lfloor>x\<ra>y\<rfloor> \<zs> \<lfloor>x\<rfloor> \<zs> \<lfloor>y\<rfloor>) \<zlq> \<two>\<^sub>Z"
proof -
  from A1 have T: 
    "\<lfloor>x\<rfloor>\<^sup>R \<in> \<real>"  "\<lfloor>y\<rfloor>\<^sup>R \<in> \<real>"  
    "x\<ra>y \<rs> (\<lfloor>x\<rfloor>\<^sup>R) \<in> \<real>"
     using Real_ZF_1_4_L7 real_int_is_real Real_ZF_1_L6
     by auto
  from A1 have 
    "\<zero> \<lsq> x \<rs> (\<lfloor>x\<rfloor>\<^sup>R) \<ra> (y \<rs> (\<lfloor>y\<rfloor>\<^sup>R))"
    "x \<rs>  (\<lfloor>x\<rfloor>\<^sup>R) \<ra> (y \<rs> (\<lfloor>y\<rfloor>\<^sup>R)) \<lsq> \<two>"
    using Real_ZF_1_4_L7 Real_ZF_1_2_L16 Real_ZF_1_2_L17
      Real_ZF_1_4_L17B Real_ZF_1_2_L18 by auto
  moreover from A1 T have 
    "x \<rs> (\<lfloor>x\<rfloor>\<^sup>R) \<ra> (y \<rs> (\<lfloor>y\<rfloor>\<^sup>R)) = x\<ra>y \<rs> (\<lfloor>x\<rfloor>\<^sup>R) \<rs> (\<lfloor>y\<rfloor>\<^sup>R)"
    using Real_ZF_1_L7A by simp
  ultimately have 
    "\<zero> \<lsq> x\<ra>y \<rs> (\<lfloor>x\<rfloor>\<^sup>R) \<rs> (\<lfloor>y\<rfloor>\<^sup>R)"
    "x\<ra>y \<rs> (\<lfloor>x\<rfloor>\<^sup>R) \<rs> (\<lfloor>y\<rfloor>\<^sup>R) \<lsq> \<two>"
    by auto
  then have 
    "\<lfloor>\<zero>\<rfloor> \<zlq> \<lfloor>x\<ra>y \<rs> (\<lfloor>x\<rfloor>\<^sup>R) \<rs> (\<lfloor>y\<rfloor>\<^sup>R)\<rfloor>"
    "\<lfloor>x\<ra>y \<rs> (\<lfloor>x\<rfloor>\<^sup>R) \<rs> (\<lfloor>y\<rfloor>\<^sup>R)\<rfloor> \<zlq> \<lfloor>\<two>\<rfloor>"
    using Real_ZF_1_4_L9 by auto
  then have 
    "\<zero>\<^sub>Z  \<zlq> \<lfloor>x\<ra>y \<rs> (\<lfloor>x\<rfloor>\<^sup>R) \<rs> (\<lfloor>y\<rfloor>\<^sup>R)\<rfloor>"
    "\<lfloor>x\<ra>y \<rs> (\<lfloor>x\<rfloor>\<^sup>R) \<rs> (\<lfloor>y\<rfloor>\<^sup>R)\<rfloor> \<zlq> \<two>\<^sub>Z"
    using floor_01_is_zero_one floor_2_is_two by auto
  moreover from A1 have
    "\<lfloor>x\<ra>y \<rs> (\<lfloor>x\<rfloor>\<^sup>R) \<rs> (\<lfloor>y\<rfloor>\<^sup>R)\<rfloor> = \<lfloor>x\<ra>y\<rfloor> \<zs> \<lfloor>x\<rfloor> \<zs> \<lfloor>y\<rfloor>"
    using Real_ZF_1_L6 Real_ZF_1_4_L7 real_int_is_real Real_ZF_1_4_L16
    by simp
  ultimately have
    "\<zero>\<^sub>Z \<zlq> \<lfloor>x\<ra>y\<rfloor> \<zs> \<lfloor>x\<rfloor> \<zs> \<lfloor>y\<rfloor>"
    "\<lfloor>x\<ra>y\<rfloor> \<zs> \<lfloor>x\<rfloor> \<zs> \<lfloor>y\<rfloor> \<zlq> \<two>\<^sub>Z"
    by auto
  then show "abs(\<lfloor>x\<ra>y\<rfloor> \<zs> \<lfloor>x\<rfloor> \<zs> \<lfloor>y\<rfloor>) \<zlq> \<two>\<^sub>Z"
    using int0.Int_ZF_2_L16 by simp
qed

text\<open>Suppose $S\neq \emptyset$ is bounded above and 
  $\Gamma(S,m) =\lfloor m^R\cdot x\rfloor$ for some positive integer $m$
  and $x\in S$. Then if $y\in S, x\leq y$ we also have 
  $\Gamma(S,m) =\lfloor m^R\cdot y\rfloor$.\<close>

lemma (in real1) Real_ZF_1_4_L20: 
  assumes A1: "IsBoundedAbove(S,OrderOnReals)"  "S\<noteq>0" and
  A2: "n\<in>\<int>\<^sub>+" "x\<in>S" and
  A3: "\<Gamma>(S,n) = \<lfloor>n\<^sup>R\<cdot>x\<rfloor>" and
  A4: "y\<in>S"  "x\<lsq>y"
  shows "\<Gamma>(S,n) = \<lfloor>n\<^sup>R\<cdot>y\<rfloor>"
proof -
  from A2 A4 have "\<lfloor>n\<^sup>R\<cdot>x\<rfloor> \<zlq> \<lfloor>(n\<^sup>R)\<cdot>y\<rfloor>"
    using int_pos_is_real_pos Real_ZF_1_2_L14 Real_ZF_1_4_L9
    by simp
  with A3 have "\<langle>\<Gamma>(S,n),\<lfloor>(n\<^sup>R)\<cdot>y\<rfloor>\<rangle> \<in> IntegerOrder"
    by simp
  moreover from A1 A2 A4 have "\<langle>\<lfloor>n\<^sup>R\<cdot>y\<rfloor>,\<Gamma>(S,n)\<rangle> \<in> IntegerOrder"
    using Real_ZF_1_4_L11 by simp
  ultimately show "\<Gamma>(S,n) = \<lfloor>n\<^sup>R\<cdot>y\<rfloor>"
    by (rule int0.Int_ZF_2_L3)
qed

text\<open>The homomorphism difference of $n\mapsto \Gamma(S,n)$ is bounded
  by $2$ on positive integers.\<close>

lemma (in real1) Real_ZF_1_4_L21: 
  assumes A1: "IsBoundedAbove(S,OrderOnReals)"  "S\<noteq>0" and
  A2: "m\<in>\<int>\<^sub>+"  "n\<in>\<int>\<^sub>+"
  shows "abs(\<Gamma>(S,m\<za>n) \<zs> \<Gamma>(S,m) \<zs> \<Gamma>(S,n)) \<zlq>  \<two>\<^sub>Z"
proof -
  from A2 have T: "m\<za>n \<in> \<int>\<^sub>+" using int0.pos_int_closed_add_unfolded
    by simp
  with A1 A2 have 
    "\<Gamma>(S,m) \<in> {\<lfloor>m\<^sup>R\<cdot>x\<rfloor>. x\<in>S}" and
    "\<Gamma>(S,n) \<in> {\<lfloor>n\<^sup>R\<cdot>x\<rfloor>. x\<in>S}" and
    "\<Gamma>(S,m\<za>n) \<in> {\<lfloor>(m\<za>n)\<^sup>R\<cdot>x\<rfloor>. x\<in>S}"
    using Real_ZF_1_4_L10 by auto
  then obtain a b c where I: "a\<in>S"  "b\<in>S"  "c\<in>S" 
    and II:
    "\<Gamma>(S,m) = \<lfloor>m\<^sup>R\<cdot>a\<rfloor>"  
    "\<Gamma>(S,n) = \<lfloor>n\<^sup>R\<cdot>b\<rfloor>"  
    "\<Gamma>(S,m\<za>n) = \<lfloor>(m\<za>n)\<^sup>R\<cdot>c\<rfloor>"
    by auto
  let ?d = "Maximum(OrderOnReals,{a,b,c})"
  from A1 I have "a\<in>\<real>"  "b\<in>\<real>"  "c\<in>\<real>"
    using Real_ZF_1_2_L23 by auto
  then have IV:
    "?d \<in> {a,b,c}"
    "?d \<in> \<real>"
    "a \<lsq> ?d"
    "b \<lsq> ?d"
    "c \<lsq> ?d"
    using Real_ZF_1_2_L24 by auto
  with I have V: "?d \<in> S" by auto
  from A1 T I II IV V have "\<Gamma>(S,m\<za>n) = \<lfloor>(m\<za>n)\<^sup>R\<cdot>?d\<rfloor>"
    using Real_ZF_1_4_L20 by blast
  also from A2 have "\<dots> = \<lfloor>((m\<^sup>R)\<ra>(n\<^sup>R))\<cdot>?d\<rfloor>"
    using Real_ZF_1_4_L1A PositiveSet_def by simp
  also from A2 IV have "\<dots> = \<lfloor>(m\<^sup>R)\<cdot>?d \<ra> (n\<^sup>R)\<cdot>?d\<rfloor>"
    using PositiveSet_def real_int_is_real Real_ZF_1_L7
    by simp
  finally have  "\<Gamma>(S,m\<za>n) =  \<lfloor>(m\<^sup>R)\<cdot>?d \<ra> (n\<^sup>R)\<cdot>?d\<rfloor>"
    by simp
  moreover from A1 A2 I II IV V have "\<Gamma>(S,m) = \<lfloor>m\<^sup>R\<cdot>?d\<rfloor>"
    using Real_ZF_1_4_L20 by blast
  moreover from A1 A2 I II IV V have  "\<Gamma>(S,n) = \<lfloor>n\<^sup>R\<cdot>?d\<rfloor>"
    using Real_ZF_1_4_L20 by blast
  moreover from A1 T I II IV V have "\<Gamma>(S,m\<za>n) = \<lfloor>(m\<za>n)\<^sup>R\<cdot>?d\<rfloor>"
    using Real_ZF_1_4_L20 by blast
  ultimately have "abs(\<Gamma>(S,m\<za>n) \<zs> \<Gamma>(S,m) \<zs> \<Gamma>(S,n)) =
    abs(\<lfloor>(m\<^sup>R)\<cdot>?d \<ra> (n\<^sup>R)\<cdot>?d\<rfloor> \<zs> \<lfloor>m\<^sup>R\<cdot>?d\<rfloor> \<zs> \<lfloor>n\<^sup>R\<cdot>?d\<rfloor>)"
    by simp
  with A2 IV show 
    "abs(\<Gamma>(S,m\<za>n) \<zs> \<Gamma>(S,m) \<zs> \<Gamma>(S,n)) \<zlq>  \<two>\<^sub>Z"
    using PositiveSet_def real_int_is_real Real_ZF_1_L6
      Real_ZF_1_4_L18 by simp
qed

text\<open>The next lemma provides sufficient condition for an odd function 
  to be an almost homomorphism. 
  It says for odd functions we only need to check that 
  the homomorphism difference
  (denoted \<open>\<delta>\<close> in the \<open>real1\<close> context) is bounded on positive 
  integers. This is really proven in \<open>Int_ZF_2.thy\<close>, but we
  restate it here for convenience. Recall from \<open>Group_ZF_3.thy\<close> that
  \<open>OddExtension\<close> of a function defined on the set of positive elements
  (of an ordered group) is the only odd function that is equal to the given
  one when restricted to positive elements.\<close>

lemma (in real1) Real_ZF_1_4_L21A: 
  assumes A1: "f:\<int>\<^sub>+\<rightarrow>int"  "\<forall>a\<in>\<int>\<^sub>+. \<forall>b\<in>\<int>\<^sub>+. abs(\<delta>(f,a,b)) \<zlq> L"
  shows "OddExtension(int,IntegerAddition,IntegerOrder,f) \<in> \<S>"
  using A1 int1.Int_ZF_2_1_L24 by auto (*A1 has to be here *)

text\<open>The candidate for (a representant of) the supremum of a 
  nonempty bounded above set is a slope.\<close>
  
lemma (in real1) Real_ZF_1_4_L22: 
  assumes A1: "IsBoundedAbove(S,OrderOnReals)"  "S\<noteq>0" and
  A2: "g = {\<langle>p,\<Gamma>(S,p)\<rangle>. p\<in>\<int>\<^sub>+}"
  shows "OddExtension(int,IntegerAddition,IntegerOrder,g) \<in> \<S>"
proof -
  from A1 A2 have "g: \<int>\<^sub>+\<rightarrow>int" by (rule Real_ZF_1_4_L12)
  moreover have "\<forall>m\<in>\<int>\<^sub>+. \<forall>n\<in>\<int>\<^sub>+. abs(\<delta>(g,m,n)) \<zlq> \<two>\<^sub>Z"
  proof -
    { fix m n assume A3: "m\<in>\<int>\<^sub>+"  "n\<in>\<int>\<^sub>+"
      then have "m\<za>n \<in> \<int>\<^sub>+"  "m\<in>\<int>\<^sub>+"  "n\<in>\<int>\<^sub>+" 
	using int0.pos_int_closed_add_unfolded
	by auto
      moreover from A1 A2 have "\<forall>n\<in>\<int>\<^sub>+. g`(n) = \<Gamma>(S,n)"
	by (rule Real_ZF_1_4_L12)
      ultimately have "\<delta>(g,m,n) = \<Gamma>(S,m\<za>n) \<zs> \<Gamma>(S,m) \<zs> \<Gamma>(S,n)"
	by simp
      moreover from A1 A3 have
	"abs(\<Gamma>(S,m\<za>n) \<zs> \<Gamma>(S,m) \<zs> \<Gamma>(S,n)) \<zlq>  \<two>\<^sub>Z"
	by (rule Real_ZF_1_4_L21)
      ultimately have "abs(\<delta>(g,m,n)) \<zlq> \<two>\<^sub>Z"
	by simp
    } then show "\<forall>m\<in>\<int>\<^sub>+. \<forall>n\<in>\<int>\<^sub>+. abs(\<delta>(g,m,n)) \<zlq> \<two>\<^sub>Z"
      by simp
  qed
  ultimately show ?thesis by (rule Real_ZF_1_4_L21A)
qed

text\<open>A technical lemma used in the proof that all elements
  of $S$ are less or equal than the candidate for supremum of $S$.\<close>

lemma (in real1) Real_ZF_1_4_L23:
  assumes A1: "f \<in> \<S>" and A2: "N \<in> int"  "M \<in> int" and
  A3: "\<forall>n\<in>\<int>\<^sub>+. M\<zmu>n \<zlq> f`(N\<zmu>n)"
  shows "M\<^sup>R \<lsq> [f]\<cdot>(N\<^sup>R)"
proof -
  let ?M\<^sub>S = "{\<langle>n, M\<zmu>n\<rangle> . n \<in> int}"
  let ?N\<^sub>S = "{\<langle>n, N\<zmu>n\<rangle> . n \<in> int}"
  from A1 A2 have T: "?M\<^sub>S \<in> \<S>"  "?N\<^sub>S \<in> \<S>"  "f\<circ>?N\<^sub>S \<in> \<S>"
    using int1.Int_ZF_2_5_L1 int1.Int_ZF_2_1_L11 SlopeOp2_def
    by auto
  moreover from A1 A2 A3 have "?M\<^sub>S \<sim> f\<circ>?N\<^sub>S \<or> f\<circ>?N\<^sub>S \<fp> (\<fm>?M\<^sub>S) \<in> \<S>\<^sub>+"
    using int1.Int_ZF_2_5_L8 SlopeOp2_def SlopeOp1_def Slopes_def
      BoundedIntMaps_def SlopeEquivalenceRel_def PositiveIntegers_def
      PositiveSlopes_def by simp
  ultimately have "[?M\<^sub>S] \<lsq> [f\<circ>?N\<^sub>S]" using Real_ZF_1_2_L12
    by simp
  with A1 T show "M\<^sup>R \<lsq> [f]\<cdot>(N\<^sup>R)" using Real_ZF_1_1_L4
    by simp
qed

text\<open>A technical lemma aimed used in the proof the candidate for supremum of 
  $S$ is less or equal than any upper bound for $S$.\<close>

lemma (in real1) Real_ZF_1_4_L23A:
  assumes A1: "f \<in> \<S>" and A2: "N \<in> int"  "M \<in> int" and
  A3: "\<forall>n\<in>\<int>\<^sub>+. f`(N\<zmu>n) \<zlq>  M\<zmu>n "
  shows "[f]\<cdot>(N\<^sup>R) \<lsq> M\<^sup>R"
proof -
  let ?M\<^sub>S = "{\<langle>n, M\<zmu>n\<rangle> . n \<in> int}"
  let ?N\<^sub>S = "{\<langle>n, N\<zmu>n\<rangle> . n \<in> int}"
  from A1 A2 have T: "?M\<^sub>S \<in> \<S>"  "?N\<^sub>S \<in> \<S>"  "f\<circ>?N\<^sub>S \<in> \<S>"
    using int1.Int_ZF_2_5_L1 int1.Int_ZF_2_1_L11 SlopeOp2_def
    by auto
  moreover from A1 A2 A3 have 
    "f\<circ>?N\<^sub>S \<sim> ?M\<^sub>S \<or>  ?M\<^sub>S \<fp> (\<fm>(f\<circ>?N\<^sub>S)) \<in> \<S>\<^sub>+"
    using int1.Int_ZF_2_5_L9 SlopeOp2_def SlopeOp1_def Slopes_def
      BoundedIntMaps_def SlopeEquivalenceRel_def PositiveIntegers_def
      PositiveSlopes_def by simp
  ultimately have "[f\<circ>?N\<^sub>S] \<lsq> [?M\<^sub>S]" using Real_ZF_1_2_L12
    by simp
  with A1 T show " [f]\<cdot>(N\<^sup>R)\<lsq> M\<^sup>R" using Real_ZF_1_1_L4
    by simp
qed

text\<open>The essential condition to claim that the candidate for supremum
  of $S$ is greater or equal than all elements of $S$.\<close>

lemma (in real1) Real_ZF_1_4_L24:
  assumes A1: "IsBoundedAbove(S,OrderOnReals)" and
  A2: "x\<ls>y"  "y\<in>S"  and
  A4: "N \<in> \<int>\<^sub>+"  "M \<in> int" and
  A5: "M\<^sup>R \<ls> y\<cdot>N\<^sup>R" and A6: "p \<in> \<int>\<^sub>+"
  shows "p\<zmu>M \<zlq> \<Gamma>(S,p\<zmu>N)"
proof -
  from A2 A4 A6 have T1:
    "N\<^sup>R \<in> \<real>\<^sub>+"   "y\<in>\<real>"   "p\<^sup>R \<in> \<real>\<^sub>+"
    "p\<zmu>N \<in> \<int>\<^sub>+"   "(p\<zmu>N)\<^sup>R \<in> \<real>\<^sub>+"    
    using int_pos_is_real_pos Real_ZF_1_2_L15 
    int0.pos_int_closed_mul_unfold by auto
  with A4 A6 have T2: 
    "p \<in> int"   "p\<^sup>R \<in> \<real>"   "N\<^sup>R \<in> \<real>"  "N\<^sup>R \<noteq> \<zero>"   "M\<^sup>R \<in> \<real>"
    using real_int_is_real PositiveSet_def by auto
  from T1 A5 have "\<lfloor>(p\<zmu>N)\<^sup>R\<cdot>(M\<^sup>R\<cdot>(N\<^sup>R)\<inverse>)\<rfloor> \<zlq> \<lfloor>(p\<zmu>N)\<^sup>R\<cdot>y\<rfloor>"
    using Real_ZF_1_3_L4A Real_ZF_1_3_L7 Real_ZF_1_4_L9
    by simp
  moreover from A1 A2 T1 have "\<lfloor>(p\<zmu>N)\<^sup>R\<cdot>y\<rfloor> \<zlq> \<Gamma>(S,p\<zmu>N)"
    using Real_ZF_1_4_L11 by simp
  ultimately have I: "\<lfloor>(p\<zmu>N)\<^sup>R\<cdot>(M\<^sup>R\<cdot>(N\<^sup>R)\<inverse>)\<rfloor> \<zlq> \<Gamma>(S,p\<zmu>N)"
    by (rule int_order_transitive)
  from A4 A6 have "(p\<zmu>N)\<^sup>R\<cdot>(M\<^sup>R\<cdot>(N\<^sup>R)\<inverse>) = p\<^sup>R\<cdot>N\<^sup>R\<cdot>(M\<^sup>R\<cdot>(N\<^sup>R)\<inverse>)"
    using PositiveSet_def Real_ZF_1_4_L1C by simp
  with A4 T2 have "\<lfloor>(p\<zmu>N)\<^sup>R\<cdot>(M\<^sup>R\<cdot>(N\<^sup>R)\<inverse>)\<rfloor> = p\<zmu>M"
    using Real_ZF_1_3_L8 Real_ZF_1_4_L14A by simp
  with I show "p\<zmu>M \<zlq> \<Gamma>(S,p\<zmu>N)" by simp
qed

text\<open>An obvious fact about odd extension
  of a function $p\mapsto \Gamma(s,p)$ that is used a couple of times 
  in proofs.\<close>

lemma (in real1) Real_ZF_1_4_L24A:
  assumes A1: "IsBoundedAbove(S,OrderOnReals)"  "S\<noteq>0" and A2: "p \<in> \<int>\<^sub>+"
  and A3:
  "h = OddExtension(int,IntegerAddition,IntegerOrder,{\<langle>p,\<Gamma>(S,p)\<rangle>. p\<in>\<int>\<^sub>+})"
  shows "h`(p) = \<Gamma>(S,p)"
proof -
  let ?g = "{\<langle>p,\<Gamma>(S,p)\<rangle>. p\<in>\<int>\<^sub>+}"
  from A1 have I: "?g : \<int>\<^sub>+\<rightarrow>int" using  Real_ZF_1_4_L12
    by blast
  with A2 A3 show "h`(p) = \<Gamma>(S,p)" 
    using int0.Int_ZF_1_5_L11 ZF_fun_from_tot_val
    by simp
qed

text\<open>The candidate for the supremum of $S$ is not smaller than 
  any element of $S$.\<close>

lemma (in real1) Real_ZF_1_4_L25:
  assumes A1: "IsBoundedAbove(S,OrderOnReals)" and 
  A2: "\<not>HasAmaximum(OrderOnReals,S)" and
  A3: "x\<in>S" and A4:
  "h = OddExtension(int,IntegerAddition,IntegerOrder,{\<langle>p,\<Gamma>(S,p)\<rangle>. p\<in>\<int>\<^sub>+})"
  shows "x \<lsq> [h]"
proof -
  from A1 A2 A3 have 
    "S \<subseteq> \<real>"  "\<not>HasAmaximum(OrderOnReals,S)"  "x\<in>S" 
    using Real_ZF_1_2_L23 by auto
  then have "\<exists>y\<in>S. x\<ls>y" by (rule Real_ZF_1_2_L27)
  then obtain y where I: "y\<in>S" and  II: "x\<ls>y"
    by auto
  from II have 
    "\<exists>M\<in>int. \<exists>N\<in>\<int>\<^sub>+.  x\<cdot>N\<^sup>R \<ls> M\<^sup>R \<and> M\<^sup>R \<ls> y\<cdot>N\<^sup>R"
    using Arthan_Lemma14iii by simp
  then obtain M N where III: "M \<in> int"  "N\<in>\<int>\<^sub>+" and 
    IV: "x\<cdot>N\<^sup>R \<ls> M\<^sup>R"  "M\<^sup>R \<ls> y\<cdot>N\<^sup>R"
    by auto
  from II III IV have V: "x \<lsq> M\<^sup>R\<cdot>(N\<^sup>R)\<inverse>"
    using int_pos_is_real_pos Real_ZF_1_2_L15 Real_ZF_1_3_L4
    by auto
  from A3 have VI: "S\<noteq>0" by auto
  with A1 A4 have T1: "h \<in> \<S>" using Real_ZF_1_4_L22
    by simp
  moreover from III have "N \<in> int"  "M \<in> int"
    using PositiveSet_def by auto
  moreover have "\<forall>n\<in>\<int>\<^sub>+. M\<zmu>n \<zlq> h`(N\<zmu>n)"
  proof
    let ?g = "{\<langle>p,\<Gamma>(S,p)\<rangle>. p\<in>\<int>\<^sub>+}"
    fix n assume A5: "n\<in>\<int>\<^sub>+"
    with III have T2: "N\<zmu>n \<in> \<int>\<^sub>+"
      using int0.pos_int_closed_mul_unfold by simp
    from III A5 have 
      "N\<zmu>n = n\<zmu>N"  and "n\<zmu>M = M\<zmu>n"
      using PositiveSet_def int0.Int_ZF_1_1_L5 by auto   
    moreover 
    from A1 I II III IV A5 have
      "IsBoundedAbove(S,OrderOnReals)"
      "x\<ls>y"  "y\<in>S"
      "N \<in> \<int>\<^sub>+"  "M \<in> int"
      "M\<^sup>R \<ls> y\<cdot>N\<^sup>R"  "n \<in> \<int>\<^sub>+"
      by auto
    then have "n\<zmu>M \<zlq> \<Gamma>(S,n\<zmu>N)" by (rule Real_ZF_1_4_L24)
    moreover from A1 A4 VI T2 have "h`(N\<zmu>n) = \<Gamma>(S,N\<zmu>n)"
      using Real_ZF_1_4_L24A by simp
    ultimately show "M\<zmu>n \<zlq> h`(N\<zmu>n)" by auto
  qed 
  ultimately have "M\<^sup>R \<lsq> [h]\<cdot>N\<^sup>R" using Real_ZF_1_4_L23
    by simp
  with III T1 have "M\<^sup>R\<cdot>(N\<^sup>R)\<inverse> \<lsq> [h]"
    using int_pos_is_real_pos Real_ZF_1_1_L3 Real_ZF_1_3_L4B
    by simp
  with V show "x \<lsq> [h]" by (rule real_ord_transitive)
qed

text\<open>The essential condition to claim that the candidate for supremum
  of $S$ is less or equal than any upper bound of $S$.\<close>

lemma (in real1) Real_ZF_1_4_L26:
  assumes A1: "IsBoundedAbove(S,OrderOnReals)" and
  A2: "x\<lsq>y"  "x\<in>S"  and
  A4: "N \<in> \<int>\<^sub>+"  "M \<in> int" and
  A5: "y\<cdot>N\<^sup>R \<ls> M\<^sup>R " and A6: "p \<in> \<int>\<^sub>+"
  shows "\<lfloor>(N\<zmu>p)\<^sup>R\<cdot>x\<rfloor> \<zlq> M\<zmu>p"
proof -
  from A2 A4 A6 have T:
    "p\<zmu>N \<in> \<int>\<^sub>+"  "p \<in> int"  "N \<in> int"  
    "p\<^sup>R \<in> \<real>\<^sub>+" "p\<^sup>R \<in> \<real>"  "N\<^sup>R \<in> \<real>"  "x \<in> \<real>"  "y \<in> \<real>"
    using int0.pos_int_closed_mul_unfold PositiveSet_def
      real_int_is_real Real_ZF_1_2_L15 int_pos_is_real_pos
    by auto
  with A2 have "(p\<zmu>N)\<^sup>R\<cdot>x \<lsq> (p\<zmu>N)\<^sup>R\<cdot>y"
    using int_pos_is_real_pos Real_ZF_1_2_L14A
    by simp
  moreover from A4 T have I: 
    "(p\<zmu>N)\<^sup>R = p\<^sup>R\<cdot>N\<^sup>R"
    "(p\<zmu>M)\<^sup>R = p\<^sup>R\<cdot>M\<^sup>R"
    using Real_ZF_1_4_L1C by auto
  ultimately have "(p\<zmu>N)\<^sup>R\<cdot>x \<lsq> p\<^sup>R\<cdot>N\<^sup>R\<cdot>y"
    by simp
  moreover
  from A5 T I have "p\<^sup>R\<cdot>(y\<cdot>N\<^sup>R) \<ls> (p\<zmu>M)\<^sup>R"
    using Real_ZF_1_3_L7 by simp
  with T have "p\<^sup>R\<cdot>N\<^sup>R\<cdot>y \<ls> (p\<zmu>M)\<^sup>R" using Real_ZF_1_1_L9
    by simp
  ultimately have "(p\<zmu>N)\<^sup>R\<cdot>x \<ls> (p\<zmu>M)\<^sup>R"
    by (rule real_strict_ord_transit)
  then have "\<lfloor>(p\<zmu>N)\<^sup>R\<cdot>x\<rfloor> \<zlq> \<lfloor>(p\<zmu>M)\<^sup>R\<rfloor>"
    using Real_ZF_1_4_L9 by simp
  moreover 
  from A4 T have "p\<zmu>M \<in> int" using int0.Int_ZF_1_1_L5
    by simp
  then have "\<lfloor>(p\<zmu>M)\<^sup>R\<rfloor> = p\<zmu>M" using Real_ZF_1_4_L14
    by simp
   moreover from A4 A6 have "p\<zmu>N = N\<zmu>p" and "p\<zmu>M = M\<zmu>p"
    using PositiveSet_def int0.Int_ZF_1_1_L5 by auto
  ultimately show "\<lfloor>(N\<zmu>p)\<^sup>R\<cdot>x\<rfloor> \<zlq> M\<zmu>p" by simp
qed

text\<open>A piece of the proof of the fact that the candidate for the supremum 
  of $S$ is not greater than any upper bound of $S$, done separately for 
  clarity (of mind).\<close>

lemma (in real1) Real_ZF_1_4_L27:
  assumes "IsBoundedAbove(S,OrderOnReals)"  "S\<noteq>0" and 
  "h = OddExtension(int,IntegerAddition,IntegerOrder,{\<langle>p,\<Gamma>(S,p)\<rangle>. p\<in>\<int>\<^sub>+})"
  and "p \<in> \<int>\<^sub>+" 
  shows "\<exists>x\<in>S. h`(p) = \<lfloor>p\<^sup>R\<cdot>x\<rfloor>"
  using assms Real_ZF_1_4_L10 Real_ZF_1_4_L24A by auto

text\<open>The candidate for the supremum of $S$ is not greater than 
  any upper bound of $S$.\<close>

lemma (in real1) Real_ZF_1_4_L28:
  assumes A1: "IsBoundedAbove(S,OrderOnReals)"  "S\<noteq>0"
  and A2: "\<forall>x\<in>S. x\<lsq>y" and A3:
  "h = OddExtension(int,IntegerAddition,IntegerOrder,{\<langle>p,\<Gamma>(S,p)\<rangle>. p\<in>\<int>\<^sub>+})"
  shows "[h] \<lsq> y"
proof -
  from A1 obtain a where "a\<in>S" by auto
  with A1 A2 A3 have T: "y\<in>\<real>"  "h \<in> \<S>"  "[h] \<in> \<real>"
    using Real_ZF_1_2_L15 Real_ZF_1_4_L22 Real_ZF_1_1_L3
    by auto
  { assume "\<not>([h] \<lsq> y)" 
    with T have "y \<ls> [h]" using Real_ZF_1_2_L28
      by blast
    then have "\<exists>M\<in>int. \<exists>N\<in>\<int>\<^sub>+.  y\<cdot>N\<^sup>R \<ls> M\<^sup>R \<and> M\<^sup>R \<ls> [h]\<cdot>N\<^sup>R"
      using Arthan_Lemma14iii by simp
    then obtain M N where I: "M\<in>int"  "N\<in>\<int>\<^sub>+" and
      II: "y\<cdot>N\<^sup>R \<ls> M\<^sup>R"  "M\<^sup>R \<ls> [h]\<cdot>N\<^sup>R"
      by auto
    from I have III: "N\<^sup>R \<in> \<real>\<^sub>+" using int_pos_is_real_pos
      by simp
    have "\<forall>p\<in>\<int>\<^sub>+. h`(N\<zmu>p) \<zlq>  M\<zmu>p"
    proof
      fix p assume A4: "p\<in>\<int>\<^sub>+"
      with A1 A3 I have "\<exists>x\<in>S. h`(N\<zmu>p) = \<lfloor>(N\<zmu>p)\<^sup>R\<cdot>x\<rfloor>"
	using int0.pos_int_closed_mul_unfold Real_ZF_1_4_L27
	by simp
      with A1 A2 I II A4 show "h`(N\<zmu>p) \<zlq>  M\<zmu>p"
	using Real_ZF_1_4_L26 by auto
    qed
    with T I have "[h]\<cdot>N\<^sup>R \<lsq> M\<^sup>R" 
      using PositiveSet_def Real_ZF_1_4_L23A
      by simp
    with T III have "[h] \<lsq>  M\<^sup>R\<cdot>(N\<^sup>R)\<inverse>"
      using Real_ZF_1_3_L4C by simp
    moreover from T II III have "M\<^sup>R\<cdot>(N\<^sup>R)\<inverse> \<ls> [h]"
      using Real_ZF_1_3_L4A by simp
    ultimately have False using Real_ZF_1_2_L29 by blast
  } then show "[h] \<lsq> y" by auto
qed

text\<open>Now we can prove that every nonempty subset of reals that is bounded
  above has a supremum. Proof by considering two cases: when the set has a
  maximum and when it does not.\<close>

lemma (in real1) real_order_complete:
  assumes A1: "IsBoundedAbove(S,OrderOnReals)"  "S\<noteq>0"
  shows "HasAminimum(OrderOnReals,\<Inter>a\<in>S. OrderOnReals``{a})"
proof -
  { assume "HasAmaximum(OrderOnReals,S)"
    with A1 have "HasAminimum(OrderOnReals,\<Inter>a\<in>S. OrderOnReals``{a})"
      using Real_ZF_1_2_L10 IsAnOrdGroup_def IsPartOrder_def
	Order_ZF_5_L6 by simp }
  moreover
  { assume A2: "\<not>HasAmaximum(OrderOnReals,S)"
    let ?h = "OddExtension(int,IntegerAddition,IntegerOrder,{\<langle>p,\<Gamma>(S,p)\<rangle>. p\<in>\<int>\<^sub>+})"
    let ?r = "OrderOnReals"
    from A1 have "antisym(OrderOnReals)"  "S\<noteq>0"
      using Real_ZF_1_2_L10 IsAnOrdGroup_def IsPartOrder_def by auto
    moreover from A1 A2 have "\<forall>x\<in>S. \<langle>x,[?h]\<rangle> \<in> ?r"
      using Real_ZF_1_4_L25 by simp
    moreover from A1 have "\<forall>y. (\<forall>x\<in>S. \<langle>x,y\<rangle> \<in> ?r) \<longrightarrow> \<langle>[?h],y\<rangle> \<in> ?r"
      using Real_ZF_1_4_L28 by simp
    ultimately have "HasAminimum(OrderOnReals,\<Inter>a\<in>S. OrderOnReals``{a})"
      by (rule Order_ZF_5_L5) }
  ultimately show ?thesis by blast
qed


text\<open>Finally, we are ready to formulate the main result: that the 
  construction of real numbers from the additive group of integers
  results in a complete ordered field. 
  This theorem completes the construction. It was fun.\<close>

theorem eudoxus_reals_are_reals: shows 
  "IsAmodelOfReals(RealNumbers,RealAddition,RealMultiplication,OrderOnReals)"
  using real1.reals_are_ord_field real1.real_order_complete 
    IsComplete_def IsAmodelOfReals_def by simp

end
