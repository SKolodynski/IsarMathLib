(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2005, 2006  Slawomir Kolodynski

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
WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES 
OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. 
IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, 
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, 
PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; 
OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, 
WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) 
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, 
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

section \<open>Groups 3\<close>

theory Group_ZF_3 imports Group_ZF_2 Finite1

begin

text\<open>In this theory we consider notions in group theory that are useful 
  for the construction of real numbers in the \<open>Real_ZF_x\<close> series of 
  theories.\<close>

subsection\<open>Group valued finite range functions\<close>

text\<open>In this section show that the group valued functions 
  $f : X\rightarrow G$, with the property that $f(X)$ is 
  a finite subset of $G$, is a group. Such functions play an important
  role in the construction of real numbers in the \<open>Real_ZF\<close> series.\<close>

text\<open>The following proves the essential condition to show that the set of 
  finite range functions is
  closed with respect to the lifted group operation.\<close>

lemma (in group0) Group_ZF_3_1_L1: 
  assumes A1: "F = P {lifted to function space over} X"
  and 
  A2: "s \<in> FinRangeFunctions(X,G)"  "r \<in>  FinRangeFunctions(X,G)" 
  shows "F`\<langle> s,r\<rangle> \<in> FinRangeFunctions(X,G)"
proof -
  let ?q = "F`\<langle> s,r\<rangle>"
  from A2 have T1:"s:X\<rightarrow>G" "r:X\<rightarrow>G"
    using FinRangeFunctions_def by auto
  with A1 have T2:"?q : X\<rightarrow>G"
    using group0_2_L1 monoid0.Group_ZF_2_1_L0
    by simp
  moreover have "?q``(X) \<in> Fin(G)"
  proof -
    from A2 have
      "{s`(x). x\<in>X} \<in> Fin(G)"
      "{r`(x). x\<in>X} \<in> Fin(G)"
      using Finite1_L18 by auto
    with A1 T1 T2 show ?thesis using 
      group_oper_fun Finite1_L15 Group_ZF_2_1_L3 func_imagedef
      by simp
  qed
  ultimately show ?thesis using FinRangeFunctions_def
    by simp
qed

text\<open>The set of group valued finite range functions is closed with respect 
  to the lifted group operation.\<close>

lemma (in group0) Group_ZF_3_1_L2:
  assumes A1: "F = P {lifted to function space over} X"
  shows "FinRangeFunctions(X,G) {is closed under} F"
proof -
  let ?A = "FinRangeFunctions(X,G)"
  from A1 have "\<forall>x\<in>?A. \<forall>y\<in>?A. F`\<langle> x,y\<rangle> \<in> ?A"
    using Group_ZF_3_1_L1 by simp
  then show ?thesis using IsOpClosed_def by simp
qed

text\<open>A composition of a finite range function with the group inverse is
  a finite range function.\<close>

lemma (in group0) Group_ZF_3_1_L3: 
  assumes A1: "s \<in> FinRangeFunctions(X,G)"
  shows "GroupInv(G,P) O s \<in> FinRangeFunctions(X,G)"
  using groupAssum assms group0_2_T2 Finite1_L20 by simp

text\<open>The set of finite range functions is s subgroup of the lifted group.\<close>

theorem Group_ZF_3_1_T1: 
  assumes A1: "IsAgroup(G,P)" 
  and A2: "F = P {lifted to function space over} X"
  and A3: "X\<noteq>0"
  shows "IsAsubgroup(FinRangeFunctions(X,G),F)"
proof -
  let ?e = "TheNeutralElement(G,P)"
  let ?S = "FinRangeFunctions(X,G)"
  from A1 have T1: "group0(G,P)" using group0_def 
    by simp
  with A1 A2 have T2:"group0(X\<rightarrow>G,F)"
    using group0.Group_ZF_2_1_T2 group0_def
    by simp
  moreover have "?S \<noteq> 0"
  proof -   
    from T1 A3 have 
      "ConstantFunction(X,?e) \<in> ?S"
      using group0.group0_2_L1 monoid0.unit_is_neutral
	Finite1_L17 by simp
    thus ?thesis by auto
  qed
  moreover have "?S \<subseteq> X\<rightarrow>G"
    using FinRangeFunctions_def by auto
  moreover from A2 T1 have
    "?S {is closed under} F"
    using group0.Group_ZF_3_1_L2
    by simp
  moreover from A1 A2 T1 have
    "\<forall>s \<in> ?S. GroupInv(X\<rightarrow>G,F)`(s) \<in> ?S"
    using FinRangeFunctions_def group0.Group_ZF_2_1_L6
      group0.Group_ZF_3_1_L3 by simp
  ultimately show ?thesis
    using group0.group0_3_T3 by simp
qed

subsection\<open>Almost homomorphisms\<close>

text\<open>An almost homomorphism is a group valued function 
  defined on a monoid $M$ 
  with the property that the set $\{ f(m+n)-f(m)-f(n)\}_{m,n \in M}$ is finite.
  This term is used by R. D. Arthan in "The Eudoxus Real Numbers". We use this
  term in the general group context and use the A`Campo's term "slopes" 
  (see his "A natural construction for the real numbers") to mean
  an almost homomorphism mapping interegers into themselves. 
  We consider almost homomorphisms because we use slopes to 
  define real numbers in the \<open>Real_ZF_x\<close> series.\<close>

text\<open>HomDiff is an acronym for "homomorphism difference". 
  This is the expression
  $s(mn)(s(m)s(n))^{-1}$, or $s(m+n)-s(m)-s(n)$ in the additive notation.
  It is equal to the neutral element of the group if $s$ is a homomorphism.
\<close>

definition
  "HomDiff(G,f,s,x) \<equiv> 
  f`\<langle>s`(f`\<langle> fst(x),snd(x)\<rangle>) , 
  (GroupInv(G,f)`(f`\<langle> s`(fst(x)),s`(snd(x))\<rangle>))\<rangle>"

text\<open>Almost homomorphisms are defined as those maps 
  $s:G\rightarrow G$ such that the 
  homomorphism difference takes only finite number of values on $G\times G$.
\<close>

definition
  "AlmostHoms(G,f) \<equiv> 
  {s \<in> G\<rightarrow>G.{HomDiff(G,f,s,x). x \<in> G\<times>G } \<in> Fin(G)}"

text\<open>AlHomOp1$(G,f)$ is the group operation on almost 
  homomorphisms defined in a natural way 
  by $(s\cdot r)(n) = s(n)\cdot r(n)$. In the terminology defined in 
  func1.thy this is the group operation $f$ (on $G$) 
  lifted to the function space $G\rightarrow G$ and restricted to the set 
  AlmostHoms$(G,f)$.\<close>

definition
  "AlHomOp1(G,f) \<equiv> 
  restrict(f {lifted to function space over} G,
  AlmostHoms(G,f)\<times>AlmostHoms(G,f))"
 
text\<open>We also define a composition (binary) operator on almost homomorphisms in 
  a natural way. We call that operator \<open>AlHomOp2\<close> - the second operation 
  on almost homomorphisms. Composition of almost homomorphisms is 
  used to define multiplication of real numbers in \<open>Real_ZF\<close> series.
\<close>

definition
  "AlHomOp2(G,f) \<equiv> 
  restrict(Composition(G),AlmostHoms(G,f)\<times>AlmostHoms(G,f))"
  
text\<open>This lemma provides more readable notation for the HomDiff
  definition. Not really intended to be used in proofs, but just to see the
  definition in the notation defined in the group0 locale.\<close>

lemma (in group0) HomDiff_notation:
  shows "HomDiff(G,P,s,\<langle> m,n\<rangle>) = s`(m\<cdot>n)\<cdot>(s`(m)\<cdot>s`(n))\<inverse>"
  using HomDiff_def by simp

text\<open>The next lemma shows the set from the definition of almost 
  homomorphism in a different form.\<close>

lemma (in group0) Group_ZF_3_2_L1A: shows
  "{HomDiff(G,P,s,x). x \<in> G\<times>G } = {s`(m\<cdot>n)\<cdot>(s`(m)\<cdot>s`(n))\<inverse>. \<langle> m,n\<rangle> \<in> G\<times>G}"
proof -
  have "\<forall>m\<in>G.\<forall>n\<in>G. HomDiff(G,P,s,\<langle> m,n\<rangle>) = s`(m\<cdot>n)\<cdot>(s`(m)\<cdot>s`(n))\<inverse>"
    using HomDiff_notation by simp
  then show ?thesis by (rule ZF1_1_L4A)
qed

text\<open>Let's define some notation. We inherit the notation and assumptions 
  from the group0 context (locale) 
  and add some. We will use AH to denote the set of almost homomorphisms.
  $\sim$ is the inverse (negative if the group is the group of integers) of 
  almost homomorphisms, $(\sim p)(n)= p(n)^{-1}$.  
  $\delta $ will denote the homomorphism difference specific
  for the group (HomDiff$(G,f)$). The notation $s \approx r$ will mean that
  $s,r$ are almost equal, that is they are in the equivalence relation 
  defined by the group of finite range
  functions (that is a normal subgroup of almost homomorphisms, 
  if the group is abelian). We show that 
  this is equivalent to the set $\{ s(n)\cdot r(n)^{-1}: n\in G\}$ being
  finite.
  We also add an assumption that the
  $G$ is abelian as many needed properties do not hold without that.\<close>

locale group1 = group0 +
  assumes isAbelian: "P {is commutative on} G"

  fixes AH 
  defines AH_def [simp]: "AH \<equiv> AlmostHoms(G,P)"

  fixes Op1 
  defines Op1_def [simp]: "Op1 \<equiv> AlHomOp1(G,P)"
 
  fixes Op2
  defines Op2_def [simp]: "Op2 \<equiv> AlHomOp2(G,P)"
  
  fixes FR 
  defines FR_def [simp]: "FR \<equiv> FinRangeFunctions(G,G)"

  fixes neg ("\<sim>_" [90] 91)
  defines neg_def [simp]: "\<sim>s \<equiv> GroupInv(G,P) O s"

  fixes \<delta>
  defines \<delta>_def [simp]: "\<delta>(s,x) \<equiv> HomDiff(G,P,s,x)"

  fixes AHprod (infix "\<bullet>" 69)
  defines AHprod_def [simp]: "s \<bullet> r \<equiv>  AlHomOp1(G,P)`\<langle>s,r\<rangle>"

  fixes AHcomp (infix "\<circ>" 70)
  defines AHcomp_def [simp]: "s \<circ> r \<equiv>  AlHomOp2(G,P)`\<langle>s,r\<rangle>"

  fixes AlEq (infix "\<approx>" 68)
  defines AlEq_def [simp]: 
  "s \<approx> r \<equiv> \<langle>s,r\<rangle> \<in> QuotientGroupRel(AH,Op1,FR)"


text\<open>HomDiff is a homomorphism on the lifted group structure.\<close>

lemma (in group1) Group_ZF_3_2_L1: 
  assumes A1: "s:G\<rightarrow>G"  "r:G\<rightarrow>G"
  and A2: "x \<in> G\<times>G"
  and A3: "F = P {lifted to function space over} G"
  shows "\<delta>(F`\<langle> s,r\<rangle>,x) = \<delta>(s,x)\<cdot>\<delta>(r,x)"
proof -
  let ?p = "F`\<langle> s,r\<rangle>"
  from A2 obtain m n where
    D1: "x = \<langle> m,n\<rangle>" "m\<in>G" "n\<in>G" 
    by auto
  then have T1:"m\<cdot>n \<in> G"
    using group0_2_L1 monoid0.group0_1_L1 by simp
  with A1 D1 have T2:
    "s`(m)\<in>G" "s`(n)\<in>G" "r`(m)\<in>G" 
    "r`(n)\<in>G" "s`(m\<cdot>n)\<in>G" "r`(m\<cdot>n)\<in>G"
    using apply_funtype by auto
  from A3 A1 have T3:"?p : G\<rightarrow>G"
    using group0_2_L1 monoid0.Group_ZF_2_1_L0
    by simp
  from D1 T3 have
    "\<delta>(?p,x) = ?p`(m\<cdot>n)\<cdot>((?p`(n))\<inverse>\<cdot>(?p`(m))\<inverse>)"
    using HomDiff_notation apply_funtype group_inv_of_two 
    by simp
  also from A3 A1 D1 T1 isAbelian T2 have
    "\<dots> = \<delta>(s,x)\<cdot> \<delta>(r,x)"
    using Group_ZF_2_1_L3 group0_4_L3 HomDiff_notation
    by simp
  finally show ?thesis by simp
qed

text\<open>The group operation lifted to the function space over $G$ preserves
  almost homomorphisms.\<close>

lemma (in group1) Group_ZF_3_2_L2: assumes A1: "s \<in> AH" "r \<in> AH"
  and A2: "F = P {lifted to function space over} G"
  shows "F`\<langle> s,r\<rangle> \<in> AH"
proof -
  let ?p = "F`\<langle> s,r\<rangle>"
  from A1 A2 have "?p : G\<rightarrow>G"
    using AlmostHoms_def group0_2_L1 monoid0.Group_ZF_2_1_L0
    by simp
  moreover have
    "{\<delta>(?p,x). x \<in> G\<times>G} \<in> Fin(G)"
  proof -
    from A1 have
      "{\<delta>(s,x). x \<in> G\<times>G } \<in> Fin(G)" 
      "{\<delta>(r,x). x \<in> G\<times>G } \<in> Fin(G)"
      using AlmostHoms_def by auto
    with groupAssum A1 A2 show ?thesis
      using IsAgroup_def IsAmonoid_def IsAssociative_def
      Finite1_L15 AlmostHoms_def Group_ZF_3_2_L1
      by auto
  qed
  ultimately show ?thesis using AlmostHoms_def
    by simp
qed

text\<open>The set of almost homomorphisms is closed under the 
  lifted group operation.\<close>

lemma (in group1) Group_ZF_3_2_L3:
  assumes "F = P {lifted to function space over} G"
  shows "AH {is closed under} F"
  using assms IsOpClosed_def Group_ZF_3_2_L2 by simp

text\<open>The terms in the homomorphism difference for a function
  are in the group.\<close>

lemma (in group1) Group_ZF_3_2_L4:
  assumes "s:G\<rightarrow>G" and "m\<in>G"  "n\<in>G"
  shows 
  "m\<cdot>n \<in> G" 
  "s`(m\<cdot>n) \<in> G"
  "s`(m) \<in> G" "s`(n) \<in> G"
  "\<delta>(s,\<langle> m,n\<rangle>) \<in> G"
  "s`(m)\<cdot>s`(n) \<in> G"
  using assms group_op_closed inverse_in_group  
    apply_funtype HomDiff_def by auto

text\<open>It is handy to have a version of \<open> Group_ZF_3_2_L4\<close>
  specifically for almost homomorphisms.\<close>
  
corollary (in group1) Group_ZF_3_2_L4A:  
  assumes "s \<in> AH" and "m\<in>G"  "n\<in>G"
  shows "m\<cdot>n \<in> G" 
  "s`(m\<cdot>n) \<in> G"
  "s`(m) \<in> G" "s`(n) \<in> G"
  "\<delta>(s,\<langle> m,n\<rangle>) \<in> G"
  "s`(m)\<cdot>s`(n) \<in> G"
  using assms AlmostHoms_def Group_ZF_3_2_L4
  by auto

text\<open>The terms in the homomorphism difference are in the group, 
  a different form.\<close>

lemma (in group1) Group_ZF_3_2_L4B:  
  assumes A1:"s \<in> AH" and A2:"x\<in>G\<times>G"
  shows "fst(x)\<cdot>snd(x) \<in> G" 
  "s`(fst(x)\<cdot>snd(x)) \<in> G"
  "s`(fst(x)) \<in> G" "s`(snd(x)) \<in> G"
  "\<delta>(s,x) \<in> G"
  "s`(fst(x))\<cdot>s`(snd(x)) \<in> G"
proof -
  let ?m = "fst(x)" 
  let ?n = "snd(x)"
  from A1 A2 show 
    "?m\<cdot>?n \<in> G"  "s`(?m\<cdot>?n) \<in> G" 
    "s`(?m) \<in> G" "s`(?n) \<in> G"
    "s`(?m)\<cdot>s`(?n) \<in> G"
    using Group_ZF_3_2_L4A
    by auto
  from A1 A2 have "\<delta>(s,\<langle> ?m,?n\<rangle>) \<in> G" using Group_ZF_3_2_L4A
    by simp
  moreover from A2 have "\<langle> ?m,?n\<rangle> = x" by auto
  ultimately show "\<delta>(s,x) \<in> G" by simp
qed

text\<open>What are the values of the inverse of an almost homomorphism?\<close>

lemma (in group1) Group_ZF_3_2_L5:
  assumes "s \<in> AH" and "n\<in>G"
  shows "(\<sim>s)`(n) = (s`(n))\<inverse>"
  using assms AlmostHoms_def comp_fun_apply by auto

text\<open>Homomorphism difference commutes with the inverse for almost
  homomorphisms.\<close>
  
lemma (in group1) Group_ZF_3_2_L6:  
  assumes A1:"s \<in> AH" and A2:"x\<in>G\<times>G"
  shows "\<delta>(\<sim>s,x) = (\<delta>(s,x))\<inverse>"
proof -
  let ?m = "fst(x)"
  let ?n = "snd(x)"
  have "\<delta>(\<sim>s,x) = (\<sim>s)`(?m\<cdot>?n)\<cdot>((\<sim>s)`(?m)\<cdot>(\<sim>s)`(?n))\<inverse>"
    using HomDiff_def by simp
  from A1 A2 isAbelian show ?thesis
    using Group_ZF_3_2_L4B HomDiff_def 
      Group_ZF_3_2_L5 group0_4_L4A
    by simp
qed

text\<open>The inverse of an almost homomorphism  maps the group into itself.\<close>

lemma (in group1) Group_ZF_3_2_L7: 
  assumes "s \<in> AH"
  shows "\<sim>s : G\<rightarrow>G"
  using groupAssum assms AlmostHoms_def group0_2_T2 comp_fun by auto

text\<open>The inverse of an almost homomorphism is an almost homomorphism.\<close>

lemma (in group1) Group_ZF_3_2_L8:
  assumes A1: "F = P {lifted to function space over} G"
  and A2: "s \<in> AH"
  shows "GroupInv(G\<rightarrow>G,F)`(s) \<in> AH"
proof -
  from A2 have "{\<delta>(s,x). x \<in> G\<times>G} \<in> Fin(G)"
    using AlmostHoms_def by simp
  with groupAssum  have
    "GroupInv(G,P)``{\<delta>(s,x). x \<in> G\<times>G} \<in> Fin(G)"
    using group0_2_T2 Finite1_L6A by blast
  moreover have 
     "GroupInv(G,P)``{\<delta>(s,x). x \<in> G\<times>G} =
    {(\<delta>(s,x))\<inverse>. x \<in> G\<times>G}"
  proof -
    from groupAssum have 
      "GroupInv(G,P) : G\<rightarrow>G"
      using group0_2_T2 by simp
    moreover from A2 have 
      "\<forall>x\<in>G\<times>G. \<delta>(s,x)\<in>G"
      using Group_ZF_3_2_L4B by simp
    ultimately show ?thesis 
      using func1_1_L17 by simp
  qed
  ultimately have "{(\<delta>(s,x))\<inverse>. x \<in> G\<times>G} \<in> Fin(G)"
    by simp
  moreover from A2 have
    "{(\<delta>(s,x))\<inverse>. x \<in> G\<times>G} = {\<delta>(\<sim>s,x). x \<in> G\<times>G}"
    using Group_ZF_3_2_L6 by simp
  ultimately have "{\<delta>(\<sim>s,x). x \<in> G\<times>G} \<in> Fin(G)"
    by simp
  with A2 groupAssum A1 show ?thesis
    using Group_ZF_3_2_L7 AlmostHoms_def Group_ZF_2_1_L6
    by simp
qed

text\<open>The function that assigns the neutral element everywhere 
  is an almost homomorphism.\<close>

lemma (in group1) Group_ZF_3_2_L9: shows
  "ConstantFunction(G,\<one>) \<in> AH" and "AH\<noteq>0"
proof -
  let ?z = "ConstantFunction(G,\<one>)"
  have "G\<times>G\<noteq>0" using group0_2_L1 monoid0.group0_1_L3A
    by blast
  moreover have "\<forall>x\<in>G\<times>G. \<delta>(?z,x) = \<one>"
  proof
    fix x assume A1:"x \<in> G \<times> G"
    then obtain m n where "x = \<langle> m,n\<rangle>" "m\<in>G" "n\<in>G"
      by auto
    then show "\<delta>(?z,x) = \<one>"
      using group0_2_L1 monoid0.group0_1_L1
	func1_3_L2 HomDiff_def group0_2_L2 
	group_inv_of_one by simp
  qed
  ultimately have "{\<delta>(?z,x). x\<in>G\<times>G} = {\<one>}" by (rule ZF1_1_L5)
  then show "?z \<in> AH" using group0_2_L2 Finite1_L16
    func1_3_L1 group0_2_L2 AlmostHoms_def by simp
  then show "AH\<noteq>0" by auto
qed

text\<open>If the group is abelian, then almost homomorphisms form a 
  subgroup of the lifted group.\<close>

lemma Group_ZF_3_2_L10:
  assumes A1: "IsAgroup(G,P)"
  and A2: "P {is commutative on} G"
  and A3: "F = P {lifted to function space over} G"
  shows "IsAsubgroup(AlmostHoms(G,P),F)"
proof -
  let ?AH = "AlmostHoms(G,P)"
  from A2 A1 have T1: "group1(G,P)"
    using group1_axioms.intro group0_def group1_def
    by simp
  from A1 A3 have "group0(G\<rightarrow>G,F)"
    using group0_def group0.Group_ZF_2_1_T2 by simp
  moreover from T1 have "?AH\<noteq>0"
    using group1.Group_ZF_3_2_L9 by simp
  moreover have T2:"?AH \<subseteq> G\<rightarrow>G"
    using AlmostHoms_def by auto
  moreover from T1 A3 have 
    "?AH {is closed under} F"
    using group1.Group_ZF_3_2_L3 by simp
  moreover from T1 A3 have
    "\<forall>s\<in>?AH. GroupInv(G\<rightarrow>G,F)`(s) \<in> ?AH"
    using group1.Group_ZF_3_2_L8 by simp
  ultimately show "IsAsubgroup(AlmostHoms(G,P),F)"
    using group0.group0_3_T3 by simp
qed

text\<open>If the group is abelian, then almost homomorphisms form a group
  with the first operation, hence we can use theorems proven in group0
  context aplied to this group.\<close>

lemma (in group1) Group_ZF_3_2_L10A: 
  shows "IsAgroup(AH,Op1)" "group0(AH,Op1)"
    using groupAssum isAbelian Group_ZF_3_2_L10 IsAsubgroup_def 
      AlHomOp1_def group0_def by auto

text\<open>The group of almost homomorphisms is abelian\<close>

lemma Group_ZF_3_2_L11: assumes A1: "IsAgroup(G,f)"
  and A2: "f {is commutative on} G"
  shows 
  "IsAgroup(AlmostHoms(G,f),AlHomOp1(G,f))"
  "AlHomOp1(G,f) {is commutative on} AlmostHoms(G,f)"
proof-
  let ?AH = "AlmostHoms(G,f)"
  let ?F = "f {lifted to function space over} G"
  from A1 A2 have "IsAsubgroup(?AH,?F)"
    using Group_ZF_3_2_L10 by simp
  then show "IsAgroup(?AH,AlHomOp1(G,f))"
    using IsAsubgroup_def AlHomOp1_def by simp
  from A1 have "?F : (G\<rightarrow>G)\<times>(G\<rightarrow>G)\<rightarrow>(G\<rightarrow>G)"
    using IsAgroup_def monoid0_def monoid0.Group_ZF_2_1_L0A
    by simp
  moreover have "?AH \<subseteq> G\<rightarrow>G"
    using AlmostHoms_def by auto
  moreover from A1 A2 have
    "?F {is commutative on} (G\<rightarrow>G)"
    using group0_def group0.Group_ZF_2_1_L7
    by simp
  ultimately show 
    "AlHomOp1(G,f){is commutative on} ?AH"
    using func_ZF_4_L1 AlHomOp1_def by simp
qed

text\<open>The first operation on homomorphisms acts in a natural way on its 
  operands.\<close>

lemma (in group1) Group_ZF_3_2_L12: 
  assumes "s\<in>AH"  "r\<in>AH" and "n\<in>G"
  shows "(s\<bullet>r)`(n) = s`(n)\<cdot>r`(n)"
  using assms AlHomOp1_def restrict AlmostHoms_def Group_ZF_2_1_L3
  by simp

text\<open>What is the group inverse in the group of almost homomorphisms?\<close>

lemma (in group1) Group_ZF_3_2_L13: 
  assumes A1: "s\<in>AH"
  shows 
  "GroupInv(AH,Op1)`(s) = GroupInv(G,P) O s"
  "GroupInv(AH,Op1)`(s) \<in> AH"
  "GroupInv(G,P) O s \<in> AH"
proof -
  let ?F = "P {lifted to function space over} G"
  from groupAssum isAbelian have "IsAsubgroup(AH,?F)" 
    using Group_ZF_3_2_L10 by simp
  with A1 show I: "GroupInv(AH,Op1)`(s) = GroupInv(G,P) O s"
    using AlHomOp1_def Group_ZF_2_1_L6A by simp
  from A1 show "GroupInv(AH,Op1)`(s) \<in> AH"
    using Group_ZF_3_2_L10A group0.inverse_in_group by simp
  with I show "GroupInv(G,P) O s \<in> AH" by simp
qed

text\<open>The group inverse in the group of almost homomorphisms acts in a 
  natural way on its operand.\<close>

lemma (in group1) Group_ZF_3_2_L14:
  assumes "s\<in>AH" and "n\<in>G"
  shows "(GroupInv(AH,Op1)`(s))`(n) = (s`(n))\<inverse>"
  using isAbelian assms Group_ZF_3_2_L13 AlmostHoms_def comp_fun_apply
  by auto

text\<open>The next lemma states that if $s,r$ are almost homomorphisms, then
  $s\cdot r^{-1}$ is also an almost homomorphism.\<close>

lemma Group_ZF_3_2_L15: assumes "IsAgroup(G,f)"
  and "f {is commutative on} G"
  and "AH = AlmostHoms(G,f)" "Op1 = AlHomOp1(G,f)"
  and "s \<in> AH"  "r \<in> AH"
  shows 
  "Op1`\<langle> s,r\<rangle> \<in> AH"
  "GroupInv(AH,Op1)`(r) \<in> AH"
  "Op1`\<langle> s,GroupInv(AH,Op1)`(r)\<rangle> \<in> AH"
  using assms group0_def group1_axioms.intro group1_def
      group1.Group_ZF_3_2_L10A group0.group0_2_L1 
      monoid0.group0_1_L1 group0.inverse_in_group by auto

text\<open>A version of \<open>Group_ZF_3_2_L15\<close> formulated in notation
  used in \<open>group1\<close> context. States that the product of almost
  homomorphisms is an almost homomorphism and the the product
  of an almost homomorphism with a (pointwise) inverse of an almost 
  homomorphism is an almost homomorphism.\<close>

corollary (in group1) Group_ZF_3_2_L16: assumes "s \<in> AH"  "r \<in> AH"
  shows "s\<bullet>r \<in> AH"  "s\<bullet>(\<sim>r) \<in> AH"
  using assms isAbelian group0_def group1_axioms group1_def
  Group_ZF_3_2_L15 Group_ZF_3_2_L13 by auto

subsection\<open>The classes of almost homomorphisms\<close>

text\<open>In the \<open>Real_ZF\<close> series we define real numbers as a quotient
  of the group of integer almost homomorphisms by the integer finite range
  functions. In this section we setup the background for that in the general
  group context.\<close>

text\<open>Finite range functions are almost homomorphisms.\<close>

lemma (in group1) Group_ZF_3_3_L1: shows "FR \<subseteq> AH"
proof
  fix s assume A1:"s \<in> FR"
  then have T1:"{s`(n). n \<in> G} \<in> Fin(G)"
    "{s`(fst(x)). x\<in>G\<times>G} \<in> Fin(G)"
    "{s`(snd(x)). x\<in>G\<times>G} \<in> Fin(G)"
    using Finite1_L18 Finite1_L6B by auto
  have "{s`(fst(x)\<cdot>snd(x)). x \<in> G\<times>G} \<in> Fin(G)"
  proof -
    have "\<forall>x\<in>G\<times>G. fst(x)\<cdot>snd(x) \<in> G"
      using group0_2_L1 monoid0.group0_1_L1 by simp
    moreover from T1 have "{s`(n). n \<in> G} \<in> Fin(G)" by simp
    ultimately show ?thesis by (rule Finite1_L6B)
  qed
  moreover have 
    "{(s`(fst(x))\<cdot>s`(snd(x)))\<inverse>. x\<in>G\<times>G} \<in> Fin(G)"
  proof -
    have "\<forall>g\<in>G. g\<inverse> \<in> G" using inverse_in_group 
      by simp
    moreover from T1 have 
      "{s`(fst(x))\<cdot>s`(snd(x)). x\<in>G\<times>G} \<in> Fin(G)"
      using group_oper_fun  Finite1_L15 by simp
    ultimately show ?thesis 
      by (rule Finite1_L6C)
  qed
  ultimately have "{\<delta>(s,x). x\<in>G\<times>G} \<in> Fin(G)"
    using HomDiff_def Finite1_L15  group_oper_fun 
    by simp
  with A1 show "s \<in> AH" 
    using FinRangeFunctions_def AlmostHoms_def 
    by simp
qed

text\<open>Finite range functions valued in an abelian group form a normal 
  subgroup of almost homomorphisms.\<close>

lemma Group_ZF_3_3_L2: assumes A1:"IsAgroup(G,f)"
  and A2:"f {is commutative on} G"
  shows
  "IsAsubgroup(FinRangeFunctions(G,G),AlHomOp1(G,f))"
  "IsAnormalSubgroup(AlmostHoms(G,f),AlHomOp1(G,f),
  FinRangeFunctions(G,G))"
proof -
  let ?H1 = "AlmostHoms(G,f)"
  let ?H2 = "FinRangeFunctions(G,G)"
  let ?F = "f {lifted to function space over} G"
  from A1 A2 have T1:"group0(G,f)"
    "monoid0(G,f)" "group1(G,f)"
    using group0_def group0.group0_2_L1  
      group1_axioms.intro group1_def
    by auto
  with A1 A2 have "IsAgroup(G\<rightarrow>G,?F)"
    "IsAsubgroup(?H1,?F)" "IsAsubgroup(?H2,?F)"
    using group0.Group_ZF_2_1_T2 Group_ZF_3_2_L10
      monoid0.group0_1_L3A Group_ZF_3_1_T1
    by auto
  then have 
    "IsAsubgroup(?H1\<inter>?H2,restrict(?F,?H1\<times>?H1))"
    using group0_3_L7 by simp
  moreover from T1 have "?H1\<inter>?H2 = ?H2"
    using group1.Group_ZF_3_3_L1 by auto
  ultimately show "IsAsubgroup(?H2,AlHomOp1(G,f))"
    using AlHomOp1_def by simp
  with A1 A2 show "IsAnormalSubgroup(AlmostHoms(G,f),AlHomOp1(G,f),
    FinRangeFunctions(G,G))"
    using Group_ZF_3_2_L11 Group_ZF_2_4_L6
    by simp
qed

text\<open>The group of almost homomorphisms divided by the subgroup of finite
  range functions is an abelian group.\<close>

theorem (in group1) Group_ZF_3_3_T1:
  shows 
  "IsAgroup(AH//QuotientGroupRel(AH,Op1,FR),QuotientGroupOp(AH,Op1,FR))"
  and
  "QuotientGroupOp(AH,Op1,FR) {is commutative on}
  (AH//QuotientGroupRel(AH,Op1,FR))"
  using groupAssum isAbelian Group_ZF_3_3_L2 Group_ZF_3_2_L10A 
    Group_ZF_2_4_T1 Group_ZF_3_2_L10A Group_ZF_3_2_L11  
    Group_ZF_3_3_L2 IsAnormalSubgroup_def Group_ZF_2_4_L6 by auto

text\<open>It is useful to have a direct statement that the 
  quotient group relation is an equivalence relation for the group of AH and
  subgroup FR.\<close>

lemma (in group1) Group_ZF_3_3_L3: shows
  "QuotientGroupRel(AH,Op1,FR) \<subseteq> AH \<times> AH" and
  "equiv(AH,QuotientGroupRel(AH,Op1,FR))"
  using groupAssum isAbelian QuotientGroupRel_def 
    Group_ZF_3_3_L2 Group_ZF_3_2_L10A group0.Group_ZF_2_4_L3 
  by auto

text\<open>The "almost equal" relation is symmetric.\<close>

lemma (in group1) Group_ZF_3_3_L3A: assumes A1: "s\<approx>r"
  shows "r\<approx>s"
proof -
  let ?R = "QuotientGroupRel(AH,Op1,FR)"
  from A1 have "equiv(AH,?R)" and "\<langle>s,r\<rangle> \<in> ?R"
    using Group_ZF_3_3_L3 by auto
  then have "\<langle>r,s\<rangle> \<in> ?R" by (rule equiv_is_sym)
  then show "r\<approx>s" by simp
qed

text\<open>Although we have bypassed this fact when proving that 
  group of almost homomorphisms divided by the subgroup of finite
  range functions is a group, it is still useful to know directly 
  that the first group operation on AH is congruent with respect to the
  quotient group relation.\<close>

lemma (in group1) Group_ZF_3_3_L4: 
  shows "Congruent2(QuotientGroupRel(AH,Op1,FR),Op1)"
  using groupAssum isAbelian Group_ZF_3_2_L10A Group_ZF_3_3_L2 
    Group_ZF_2_4_L5A by simp

text\<open>The class of an almost homomorphism $s$ is the neutral element
  of the quotient group of almost homomorphisms iff $s$ is a finite range
  function.\<close>

lemma (in group1) Group_ZF_3_3_L5: assumes "s \<in> AH" and
  "r = QuotientGroupRel(AH,Op1,FR)" and
  "TheNeutralElement(AH//r,QuotientGroupOp(AH,Op1,FR)) = e"
  shows "r``{s} = e \<longleftrightarrow> s \<in> FR"
  using groupAssum isAbelian assms Group_ZF_3_2_L11 
    group0_def Group_ZF_3_3_L2 group0.Group_ZF_2_4_L5E
  by simp

text\<open>The group inverse of a class of an almost homomorphism $f$
  is the class of the inverse of $f$.\<close>

lemma (in group1) Group_ZF_3_3_L6: 
  assumes A1: "s \<in> AH"  and 
  "r = QuotientGroupRel(AH,Op1,FR)" and 
  "F = ProjFun2(AH,r,Op1)"
  shows "r``{\<sim>s} = GroupInv(AH//r,F)`(r``{s})"
proof -
  from groupAssum isAbelian assms have
    "r``{GroupInv(AH, Op1)`(s)} = GroupInv(AH//r,F)`(r `` {s})"
    using Group_ZF_3_2_L10A Group_ZF_3_3_L2 QuotientGroupOp_def
      group0.Group_ZF_2_4_L7 by simp
  with A1 show ?thesis using Group_ZF_3_2_L13
    by simp
qed

subsection\<open>Compositions of almost homomorphisms\<close>

text\<open>The goal of this section is to establish some facts about composition
  of almost homomorphisms. needed for the real numbers construction in 
  \<open>Real_ZF_x\<close> series. In particular we show that the set of almost 
  homomorphisms is closed under composition and that composition
  is congruent with respect to the equivalence relation defined by the group
  of finite range functions (a normal subgroup of almost homomorphisms).\<close>

text\<open>The next formula restates the definition of the homomorphism 
  difference to express the value an almost homomorphism on a product.\<close>

lemma (in group1) Group_ZF_3_4_L1: 
  assumes "s\<in>AH" and  "m\<in>G"  "n\<in>G" 
  shows "s`(m\<cdot>n) = s`(m)\<cdot>s`(n)\<cdot>\<delta>(s,\<langle> m,n\<rangle>)"
  using isAbelian assms Group_ZF_3_2_L4A HomDiff_def group0_4_L5
  by simp

text\<open>What is the value of a composition of almost homomorhisms?\<close>

lemma (in group1) Group_ZF_3_4_L2:
  assumes "s\<in>AH"  "r\<in>AH" and "m\<in>G"
  shows "(s\<circ>r)`(m) = s`(r`(m))"  "s`(r`(m)) \<in> G"
  using assms AlmostHoms_def func_ZF_5_L3 restrict AlHomOp2_def
    apply_funtype by auto

text\<open>What is the homomorphism difference of a composition?\<close>

lemma (in group1) Group_ZF_3_4_L3:
  assumes A1: "s\<in>AH"  "r\<in>AH" and A2: "m\<in>G"  "n\<in>G"
  shows "\<delta>(s\<circ>r,\<langle> m,n\<rangle>) = 
  \<delta>(s,\<langle> r`(m),r`(n)\<rangle>)\<cdot>s`(\<delta>(r,\<langle> m,n\<rangle>))\<cdot>\<delta>(s,\<langle> r`(m)\<cdot>r`(n),\<delta>(r,\<langle> m,n\<rangle>)\<rangle>)"
proof -
  from A1 A2 have T1:
    "s`(r`(m))\<cdot> s`(r`(n)) \<in> G"
    "\<delta>(s,\<langle> r`(m),r`(n)\<rangle>)\<in> G" "s`(\<delta>(r,\<langle> m,n\<rangle>)) \<in>G" 
    "\<delta>(s,\<langle> (r`(m)\<cdot>r`(n)),\<delta>(r,\<langle> m,n\<rangle>)\<rangle>) \<in> G"
    using Group_ZF_3_4_L2 AlmostHoms_def apply_funtype 
      Group_ZF_3_2_L4A group0_2_L1 monoid0.group0_1_L1
    by auto
  from A1 A2 have "\<delta>(s\<circ>r,\<langle> m,n\<rangle>) =
    s`(r`(m)\<cdot>r`(n)\<cdot>\<delta>(r,\<langle> m,n\<rangle>))\<cdot>(s`((r`(m)))\<cdot>s`(r`(n)))\<inverse>"
    using HomDiff_def group0_2_L1 monoid0.group0_1_L1 Group_ZF_3_4_L2
      Group_ZF_3_4_L1 by simp
  moreover from A1 A2 have
    "s`(r`(m)\<cdot>r`(n)\<cdot>\<delta>(r,\<langle> m,n\<rangle>)) =
    s`(r`(m)\<cdot>r`(n))\<cdot>s`(\<delta>(r,\<langle> m,n\<rangle>))\<cdot>\<delta>(s,\<langle> (r`(m)\<cdot>r`(n)),\<delta>(r,\<langle> m,n\<rangle>)\<rangle>)"
    "s`(r`(m)\<cdot>r`(n)) = s`(r`(m))\<cdot>s`(r`(n))\<cdot>\<delta>(s,\<langle> r`(m),r`(n)\<rangle>)"
    using Group_ZF_3_2_L4A Group_ZF_3_4_L1 by auto
  moreover from T1 isAbelian have
    "s`(r`(m))\<cdot>s`(r`(n))\<cdot>\<delta>(s,\<langle> r`(m),r`(n)\<rangle>)\<cdot>
    s`(\<delta>(r,\<langle> m,n\<rangle>))\<cdot>\<delta>(s,\<langle> (r`(m)\<cdot>r`(n)),\<delta>(r,\<langle> m,n\<rangle>)\<rangle>)\<cdot>
    (s`((r`(m)))\<cdot>s`(r`(n)))\<inverse> = 
    \<delta>(s,\<langle> r`(m),r`(n)\<rangle>)\<cdot>s`(\<delta>(r,\<langle> m,n\<rangle>))\<cdot>\<delta>(s,\<langle> (r`(m)\<cdot>r`(n)),\<delta>(r,\<langle> m,n\<rangle>)\<rangle>)" 
    using group0_4_L6C by simp
  ultimately show ?thesis by simp
qed
  
text\<open>What is the homomorphism difference of a composition (another form)?
  Here we split the homomorphism difference of a composition 
  into a product of three factors.
  This will help us in proving that the range of homomorphism difference
  for the composition is finite, as each factor has finite range.\<close>

lemma (in group1) Group_ZF_3_4_L4:
  assumes A1: "s\<in>AH"  "r\<in>AH" and A2: "x \<in> G\<times>G"
  and A3:
  "A = \<delta>(s,\<langle> r`(fst(x)),r`(snd(x))\<rangle>)"
  "B = s`(\<delta>(r,x))"
  "C = \<delta>(s,\<langle> (r`(fst(x))\<cdot>r`(snd(x))),\<delta>(r,x)\<rangle>)"
  shows "\<delta>(s\<circ>r,x) = A\<cdot>B\<cdot>C"
proof -
  let ?m = "fst(x)"
  let ?n = "snd(x)"
  note A1
  moreover from A2 have "?m\<in>G" "?n\<in>G"
    by auto
  ultimately have
    "\<delta>(s\<circ>r,\<langle> ?m,?n\<rangle>) = 
    \<delta>(s,\<langle> r`(?m),r`(?n)\<rangle>)\<cdot>s`(\<delta>(r,\<langle> ?m,?n\<rangle>))\<cdot>
    \<delta>(s,\<langle> (r`(?m)\<cdot>r`(?n)),\<delta>(r,\<langle> ?m,?n\<rangle>)\<rangle>)"
    by (rule Group_ZF_3_4_L3)
  with A1 A2 A3 show ?thesis
    by auto
qed

text\<open>The range of the homomorphism difference of a composition
  of two almost homomorphisms is finite. This is the essential condition
  to show that a composition of almost homomorphisms is an almost 
  homomorphism.\<close>

lemma (in group1) Group_ZF_3_4_L5:
  assumes A1: "s\<in>AH"  "r\<in>AH"
  shows "{\<delta>(Composition(G)`\<langle> s,r\<rangle>,x). x \<in> G\<times>G} \<in> Fin(G)"
proof -
  from A1 have 
    "\<forall>x\<in>G\<times>G. \<langle> r`(fst(x)),r`(snd(x))\<rangle> \<in> G\<times>G"
    using Group_ZF_3_2_L4B by simp
  moreover from A1 have 
    "{\<delta>(s,x). x\<in>G\<times>G} \<in> Fin(G)"
    using AlmostHoms_def by simp
  ultimately have 
    "{\<delta>(s,\<langle> r`(fst(x)),r`(snd(x))\<rangle>). x\<in>G\<times>G} \<in> Fin(G)"
    by (rule Finite1_L6B)
  moreover have "{s`(\<delta>(r,x)). x\<in>G\<times>G} \<in> Fin(G)"
  proof -
    from A1 have "\<forall>m\<in>G. s`(m) \<in> G" 
      using AlmostHoms_def apply_funtype by auto
    moreover from A1 have "{\<delta>(r,x). x\<in>G\<times>G} \<in> Fin(G)"
      using AlmostHoms_def by simp
    ultimately show ?thesis
      by (rule Finite1_L6C)
  qed
  ultimately have
    "{\<delta>(s,\<langle> r`(fst(x)),r`(snd(x))\<rangle>)\<cdot>s`(\<delta>(r,x)). x\<in>G\<times>G} \<in> Fin(G)"
    using group_oper_fun Finite1_L15 by simp
  moreover have 
    "{\<delta>(s,\<langle> (r`(fst(x))\<cdot>r`(snd(x))),\<delta>(r,x)\<rangle>).  x\<in>G\<times>G} \<in> Fin(G)"
  proof -
    from A1 have 
    "\<forall>x\<in>G\<times>G. \<langle> (r`(fst(x))\<cdot>r`(snd(x))),\<delta>(r,x)\<rangle> \<in> G\<times>G"
      using Group_ZF_3_2_L4B by simp
    moreover from A1 have 
      "{\<delta>(s,x). x\<in>G\<times>G} \<in> Fin(G)"
      using AlmostHoms_def by simp
    ultimately show ?thesis by (rule Finite1_L6B)
  qed
  ultimately have
    "{\<delta>(s,\<langle> r`(fst(x)),r`(snd(x))\<rangle>)\<cdot>s`(\<delta>(r,x))\<cdot>
    \<delta>(s,\<langle> (r`(fst(x))\<cdot>r`(snd(x))),\<delta>(r,x)\<rangle>). x\<in>G\<times>G} \<in> Fin(G)"
    using group_oper_fun Finite1_L15 by simp
  moreover from A1 have "{\<delta>(s\<circ>r,x). x\<in>G\<times>G} = 
    {\<delta>(s,\<langle> r`(fst(x)),r`(snd(x))\<rangle>)\<cdot>s`(\<delta>(r,x))\<cdot>
    \<delta>(s,\<langle> (r`(fst(x))\<cdot>r`(snd(x))),\<delta>(r,x)\<rangle>). x\<in>G\<times>G}"
    using Group_ZF_3_4_L4 by simp
  ultimately have "{\<delta>(s\<circ>r,x). x\<in>G\<times>G} \<in> Fin(G)" by simp
  with A1 show ?thesis using restrict AlHomOp2_def
    by simp
qed

text\<open>Composition of almost homomorphisms is an almost homomorphism.\<close>

theorem (in group1) Group_ZF_3_4_T1:
  assumes A1: "s\<in>AH"  "r\<in>AH"
  shows "Composition(G)`\<langle> s,r\<rangle> \<in> AH" "s\<circ>r \<in> AH"
proof -
  from A1 have "\<langle> s,r\<rangle> \<in> (G\<rightarrow>G)\<times>(G\<rightarrow>G)"
    using AlmostHoms_def by simp
  then have "Composition(G)`\<langle> s,r\<rangle> : G\<rightarrow>G"
    using func_ZF_5_L1 apply_funtype by blast
  with A1 show "Composition(G)`\<langle> s,r\<rangle> \<in> AH" 
    using Group_ZF_3_4_L5 AlmostHoms_def
    by simp
  with A1 show  "s\<circ>r \<in> AH" using AlHomOp2_def restrict 
    by simp
qed

text\<open>The set of almost homomorphisms is closed under composition.
  The second operation on almost homomorphisms is associative.\<close>

lemma (in group1) Group_ZF_3_4_L6: shows 
  "AH {is closed under} Composition(G)"
  "AlHomOp2(G,P) {is associative on} AH"
proof -
  show "AH {is closed under} Composition(G)"
    using Group_ZF_3_4_T1 IsOpClosed_def by simp
  moreover have "AH \<subseteq> G\<rightarrow>G" using AlmostHoms_def
    by auto
  moreover have 
    "Composition(G) {is associative on} (G\<rightarrow>G)"
    using func_ZF_5_L5 by simp
  ultimately show "AlHomOp2(G,P) {is associative on} AH"
    using func_ZF_4_L3 AlHomOp2_def by simp
qed

text\<open>Type information related to the situation of two almost
  homomorphisms.\<close>

lemma (in group1) Group_ZF_3_4_L7: 
  assumes A1: "s\<in>AH"  "r\<in>AH" and A2: "n\<in>G"
  shows 
  "s`(n) \<in> G" "(r`(n))\<inverse> \<in> G" 
  "s`(n)\<cdot>(r`(n))\<inverse> \<in> G"   "s`(r`(n)) \<in> G"
proof -
  from A1 A2 show 
    "s`(n) \<in> G"
    "(r`(n))\<inverse> \<in> G"
    "s`(r`(n)) \<in> G"
    "s`(n)\<cdot>(r`(n))\<inverse> \<in> G"
    using AlmostHoms_def apply_type  
      group0_2_L1 monoid0.group0_1_L1 inverse_in_group
    by auto
qed

text\<open>Type information related to the situation of three almost
  homomorphisms.\<close>

lemma (in group1) Group_ZF_3_4_L8: 
  assumes A1: "s\<in>AH"  "r\<in>AH"  "q\<in>AH" and A2: "n\<in>G"
  shows 
  "q`(n)\<in>G"
  "s`(r`(n)) \<in> G"
  "r`(n)\<cdot>(q`(n))\<inverse> \<in> G"
  "s`(r`(n)\<cdot>(q`(n))\<inverse>) \<in> G"
  "\<delta>(s,\<langle> q`(n),r`(n)\<cdot>(q`(n))\<inverse>\<rangle>) \<in> G"
proof -
  from A1 A2 show 
    "q`(n)\<in> G"  "s`(r`(n)) \<in> G" "r`(n)\<cdot>(q`(n))\<inverse> \<in> G"
    using AlmostHoms_def apply_type  
      group0_2_L1 monoid0.group0_1_L1 inverse_in_group
    by auto
  with A1 A2 show "s`(r`(n)\<cdot>(q`(n))\<inverse>) \<in> G"
    "\<delta>(s,\<langle> q`(n),r`(n)\<cdot>(q`(n))\<inverse>\<rangle>) \<in> G"
    using AlmostHoms_def apply_type Group_ZF_3_2_L4A
    by auto
qed

text\<open>A formula useful in showing that the composition of almost
  homomorphisms is congruent with respect 
  to the quotient group relation.\<close>

lemma (in group1) Group_ZF_3_4_L9:
  assumes A1: "s1 \<in> AH"  "r1 \<in> AH"  "s2 \<in> AH"  "r2 \<in> AH"
  and A2: "n\<in>G"
  shows "(s1\<circ>r1)`(n)\<cdot>((s2\<circ>r2)`(n))\<inverse> =
  s1`(r2`(n))\<cdot> (s2`(r2`(n)))\<inverse>\<cdot>s1`(r1`(n)\<cdot>(r2`(n))\<inverse>)\<cdot>
  \<delta>(s1,\<langle> r2`(n),r1`(n)\<cdot>(r2`(n))\<inverse>\<rangle>)"
proof -
  from A1 A2 isAbelian have
    "(s1\<circ>r1)`(n)\<cdot>((s2\<circ>r2)`(n))\<inverse> =
    s1`(r2`(n)\<cdot>(r1`(n)\<cdot>(r2`(n))\<inverse>))\<cdot>(s2`(r2`(n)))\<inverse>"
    using Group_ZF_3_4_L2 Group_ZF_3_4_L7 group0_4_L6A
      group_oper_assoc by simp
  with A1 A2 have "(s1\<circ>r1)`(n)\<cdot>((s2\<circ>r2)`(n))\<inverse> = s1`(r2`(n))\<cdot>
    s1`(r1`(n)\<cdot>(r2`(n))\<inverse>)\<cdot>\<delta>(s1,\<langle> r2`(n),r1`(n)\<cdot>(r2`(n))\<inverse>\<rangle>)\<cdot>
    (s2`(r2`(n)))\<inverse>"
    using Group_ZF_3_4_L8 Group_ZF_3_4_L1 by simp
  with A1 A2 isAbelian show ?thesis using
    Group_ZF_3_4_L8 group0_4_L7 by simp
qed

text\<open>The next lemma shows a formula that translates an expression
  in terms of the first group operation on almost homomorphisms and the
  group inverse in the group of almost homomorphisms to an expression using
  only the underlying group operations.\<close>

lemma (in group1) Group_ZF_3_4_L10: assumes A1: "s \<in> AH"  "r \<in> AH"
  and A2: "n \<in> G"
  shows "(s\<bullet>(GroupInv(AH,Op1)`(r)))`(n) = s`(n)\<cdot>(r`(n))\<inverse>"
proof -
  from A1 A2 show ?thesis
    using isAbelian Group_ZF_3_2_L13 Group_ZF_3_2_L12 Group_ZF_3_2_L14
    by simp
qed

text\<open>A neccessary condition for two a. h. to be almost equal.\<close>

lemma (in group1) Group_ZF_3_4_L11:
  assumes A1: "s\<approx>r"
  shows "{s`(n)\<cdot>(r`(n))\<inverse>. n\<in>G} \<in> Fin(G)"
proof -
  from A1 have "s\<in>AH" "r\<in>AH"
    using QuotientGroupRel_def by auto
  moreover from A1 have 
    "{(s\<bullet>(GroupInv(AH,Op1)`(r)))`(n). n\<in>G} \<in> Fin(G)"
    using QuotientGroupRel_def Finite1_L18 by simp
  ultimately show ?thesis
    using Group_ZF_3_4_L10 by simp
qed

text\<open>A sufficient condition for two a. h. to be almost equal.\<close>

lemma (in group1) Group_ZF_3_4_L12: assumes A1: "s\<in>AH"  "r\<in>AH"
  and A2: "{s`(n)\<cdot>(r`(n))\<inverse>. n\<in>G} \<in> Fin(G)"
  shows "s\<approx>r"
proof -
  from groupAssum isAbelian A1 A2 show ?thesis
    using Group_ZF_3_2_L15 AlmostHoms_def 
    Group_ZF_3_4_L10 Finite1_L19 QuotientGroupRel_def
    by simp
qed

text\<open>Another sufficient consdition for two a.h. to be almost
  equal. It is actually just an expansion of the definition
  of the quotient group relation.\<close>

lemma (in group1) Group_ZF_3_4_L12A: assumes "s\<in>AH"  "r\<in>AH"
  and "s\<bullet>(GroupInv(AH,Op1)`(r)) \<in> FR"
  shows "s\<approx>r"  "r\<approx>s"
proof  -
  from assms show "s\<approx>r" using assms QuotientGroupRel_def 
    by simp
  then show "r\<approx>s" by (rule Group_ZF_3_3_L3A)
qed

text\<open>Another necessary condition for two a.h. to be almost
  equal. It is actually just an expansion of the definition
  of the quotient group relation.\<close>

lemma (in group1) Group_ZF_3_4_L12B: assumes "s\<approx>r"
  shows "s\<bullet>(GroupInv(AH,Op1)`(r)) \<in> FR"
  using assms QuotientGroupRel_def by simp

text\<open>The next lemma states the essential condition for 
  the composition of a. h. to be congruent
  with respect to the quotient group relation for the subgroup of finite 
  range functions.\<close> 

lemma (in group1) Group_ZF_3_4_L13: 
  assumes A1: "s1\<approx>s2"  "r1\<approx>r2"
  shows "(s1\<circ>r1) \<approx> (s2\<circ>r2)"
proof -
  have "{s1`(r2`(n))\<cdot> (s2`(r2`(n)))\<inverse>. n\<in>G} \<in> Fin(G)"
  proof -
    from A1 have "\<forall>n\<in>G. r2`(n) \<in> G"
      using QuotientGroupRel_def AlmostHoms_def apply_funtype
      by auto
    moreover from A1 have "{s1`(n)\<cdot>(s2`(n))\<inverse>. n\<in>G} \<in> Fin(G)"
      using Group_ZF_3_4_L11 by simp
    ultimately show ?thesis by (rule Finite1_L6B)
  qed
  moreover have "{s1`(r1`(n)\<cdot>(r2`(n))\<inverse>). n \<in> G} \<in> Fin(G)"
  proof -
    from A1 have "\<forall>n\<in>G. s1`(n)\<in>G"
      using QuotientGroupRel_def AlmostHoms_def apply_funtype
      by auto
    moreover from A1 have "{r1`(n)\<cdot>(r2`(n))\<inverse>. n\<in>G} \<in> Fin(G)"
      using Group_ZF_3_4_L11 by simp
    ultimately show ?thesis by (rule Finite1_L6C)
  qed
  ultimately have
    "{s1`(r2`(n))\<cdot> (s2`(r2`(n)))\<inverse>\<cdot>s1`(r1`(n)\<cdot>(r2`(n))\<inverse>). 
    n\<in>G} \<in> Fin(G)"
    using group_oper_fun Finite1_L15 by simp
  moreover have 
    "{\<delta>(s1,\<langle> r2`(n),r1`(n)\<cdot>(r2`(n))\<inverse>\<rangle>). n\<in>G} \<in> Fin(G)"
  proof -
    from A1 have "\<forall>n\<in>G. \<langle> r2`(n),r1`(n)\<cdot>(r2`(n))\<inverse>\<rangle> \<in> G\<times>G" 
      using QuotientGroupRel_def Group_ZF_3_4_L7 by auto
    moreover from A1 have "{\<delta>(s1,x). x \<in> G\<times>G} \<in> Fin(G)"
      using QuotientGroupRel_def AlmostHoms_def by simp
    ultimately show ?thesis by (rule Finite1_L6B)
  qed
  ultimately have
    "{s1`(r2`(n))\<cdot> (s2`(r2`(n)))\<inverse>\<cdot>s1`(r1`(n)\<cdot>(r2`(n))\<inverse>)\<cdot>
    \<delta>(s1,\<langle> r2`(n),r1`(n)\<cdot>(r2`(n))\<inverse>\<rangle>). n\<in>G} \<in> Fin(G)"
    using group_oper_fun Finite1_L15 by simp
  with A1 show ?thesis using
    QuotientGroupRel_def Group_ZF_3_4_L9 
    Group_ZF_3_4_T1 Group_ZF_3_4_L12 by simp
qed

text\<open>Composition of a. h. to is congruent
  with respect to the quotient group relation for the subgroup of finite 
  range functions. Recall that if an operation say "$\circ $" on $X$ is 
  congruent with respect to an equivalence relation $R$ then we can 
  define the operation 
  on the quotient space $X/R$ by $[s]_R\circ [r]_R := [s\circ r]_R$ and this
  definition will be correct i.e. it will not depend on the choice of 
  representants for the classes $[x]$ and $[y]$. This is why we want it here.\<close>

lemma (in group1) Group_ZF_3_4_L13A: shows
  "Congruent2(QuotientGroupRel(AH,Op1,FR),Op2)"
proof -
  show ?thesis using Group_ZF_3_4_L13 Congruent2_def
    by simp
qed
  
text\<open>The homomorphism difference for the identity function is equal to
  the neutral element of the group (denoted $e$ in the group1 context).\<close>

lemma (in group1) Group_ZF_3_4_L14: assumes A1: "x \<in> G\<times>G"
  shows "\<delta>(id(G),x) = \<one>"
proof -
  from A1 show ?thesis using
    group0_2_L1 monoid0.group0_1_L1 HomDiff_def id_conv group0_2_L6
    by simp
qed
 
text\<open>The identity function ($I(x) = x$) on $G$ is an almost homomorphism.\<close>

lemma (in group1) Group_ZF_3_4_L15: shows "id(G) \<in> AH"
proof -
  have "G\<times>G \<noteq> 0" using group0_2_L1 monoid0.group0_1_L3A 
    by blast
  then show ?thesis using Group_ZF_3_4_L14 group0_2_L2
    id_type AlmostHoms_def by simp
qed
  
text\<open>Almost homomorphisms form a monoid with composition.
  The identity function on the group is the neutral element there.\<close>

lemma (in group1) Group_ZF_3_4_L16: 
  shows
  "IsAmonoid(AH,Op2)"
  "monoid0(AH,Op2)"
  "id(G) = TheNeutralElement(AH,Op2)"
proof-
  let ?i = "TheNeutralElement(G\<rightarrow>G,Composition(G))"
  have
    "IsAmonoid(G\<rightarrow>G,Composition(G))"
    "monoid0(G\<rightarrow>G,Composition(G))"
    using monoid0_def Group_ZF_2_5_L2 by auto
  moreover have "AH {is closed under} Composition(G)" 
    using Group_ZF_3_4_L6 by simp
  moreover have "AH \<subseteq> G\<rightarrow>G"
    using AlmostHoms_def by auto
  moreover have "?i \<in> AH"
    using Group_ZF_2_5_L2 Group_ZF_3_4_L15 by simp
  moreover have "id(G) =  ?i"
    using Group_ZF_2_5_L2 by simp
  ultimately show 
    "IsAmonoid(AH,Op2)"
    "monoid0(AH,Op2)"
    "id(G) = TheNeutralElement(AH,Op2)"
    using monoid0.group0_1_T1 group0_1_L6 AlHomOp2_def monoid0_def
    by auto
qed

text\<open>We can project the monoid of almost homomorphisms with composition
  to the group of almost homomorphisms divided by the subgroup of finite
  range functions. The class of the identity function is the neutral element
  of the quotient (monoid).\<close>

theorem (in group1) Group_ZF_3_4_T2:
  assumes A1: "R = QuotientGroupRel(AH,Op1,FR)"
  shows 
  "IsAmonoid(AH//R,ProjFun2(AH,R,Op2))"
  "R``{id(G)} = TheNeutralElement(AH//R,ProjFun2(AH,R,Op2))"
proof - 
  have "group0(AH,Op1)" using Group_ZF_3_2_L10A group0_def
    by simp
  with A1 groupAssum isAbelian show 
    "IsAmonoid(AH//R,ProjFun2(AH,R,Op2))"
    "R``{id(G)} = TheNeutralElement(AH//R,ProjFun2(AH,R,Op2))"
    using Group_ZF_3_3_L2 group0.Group_ZF_2_4_L3 Group_ZF_3_4_L13A 
      Group_ZF_3_4_L16 monoid0.Group_ZF_2_2_T1 Group_ZF_2_2_L1
    by auto
qed

subsection\<open>Shifting almost homomorphisms\<close>

text\<open>In this this section we consider what happens if we multiply
  an almost homomorphism by a group element. We show that the
  resulting function is also an a. h., and almost equal to the original
  one. This is used only for slopes (integer a.h.) in \<open>Int_ZF_2\<close>
  where we need to correct a positive slopes by adding a constant, so that
  it is at least $2$ on positive integers.\<close>

text\<open>If $s$ is an almost homomorphism and $c$ is some constant from the group, 
  then $s\cdot c$ is an almost homomorphism.\<close>

lemma (in group1) Group_ZF_3_5_L1: 
  assumes A1: "s \<in> AH" and A2: "c\<in>G" and
  A3: "r = {\<langle>x,s`(x)\<cdot>c\<rangle>. x\<in>G}"
  shows
  "\<forall>x\<in>G. r`(x) = s`(x)\<cdot>c"
  "r \<in> AH"
  "s \<approx> r"
proof -
  from A1 A2 A3 have I: "r:G\<rightarrow>G"
    using AlmostHoms_def apply_funtype group_op_closed 
    ZF_fun_from_total by auto
  with A3 show II: "\<forall>x\<in>G. r`(x) = s`(x)\<cdot>c"
    using ZF_fun_from_tot_val by simp
  with isAbelian A1 A2 have III:
    "\<forall>p \<in> G\<times>G. \<delta>(r,p) = \<delta>(s,p)\<cdot>c\<inverse>"
    using group_op_closed AlmostHoms_def apply_funtype
    HomDiff_def group0_4_L7 by auto
  have "{\<delta>(r,p). p \<in> G\<times>G} \<in> Fin(G)"
  proof -
    from A1 A2 have
      "{\<delta>(s,p). p \<in> G\<times>G} \<in> Fin(G)"   "c\<inverse>\<in>G"
      using AlmostHoms_def inverse_in_group by auto
    then have "{\<delta>(s,p)\<cdot>c\<inverse>. p \<in> G\<times>G} \<in> Fin(G)"
      using group_oper_fun Finite1_L16AA
      by simp
    moreover from III have
      "{\<delta>(r,p). p \<in> G\<times>G} = {\<delta>(s,p)\<cdot>c\<inverse>. p \<in> G\<times>G}"
      by (rule ZF1_1_L4B)
    ultimately show ?thesis by simp
  qed
  with I show IV: "r \<in> AH" using AlmostHoms_def
    by simp
  from isAbelian A1 A2 I II have 
    "\<forall>n \<in> G. s`(n)\<cdot>(r`(n))\<inverse> = c\<inverse>"
    using AlmostHoms_def apply_funtype group0_4_L6AB
    by auto
  then have "{s`(n)\<cdot>(r`(n))\<inverse>. n\<in>G} = {c\<inverse>. n\<in>G}"
    by (rule ZF1_1_L4B)
  with A1 A2 IV show "s \<approx> r"
    using group0_2_L1 monoid0.group0_1_L3A 
      inverse_in_group Group_ZF_3_4_L12 by simp
qed
  
end