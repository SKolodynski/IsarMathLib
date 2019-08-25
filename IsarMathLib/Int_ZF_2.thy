(*    This file is a part of IsarMathLib - 
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

section \<open>Integers 2\<close>

theory Int_ZF_2 imports func_ZF_1 Int_ZF_1 IntDiv_ZF_IML Group_ZF_3

begin

text\<open>In this theory file we consider the properties of integers that are 
  needed for the real numbers construction in \<open>Real_ZF\<close> series.\<close>

subsection\<open>Slopes\<close>

text\<open>In this section we study basic properties of slopes - the integer 
  almost homomorphisms. 
  The general definition of an almost homomorphism $f$ on a group $G$ 
  written in additive notation requires the set 
  $\{f(m+n) - f(m) - f(n): m,n\in G\}$ to be finite.
  In this section we establish a definition that is equivalent for integers: 
  that for all integer $m,n$ we have $|f(m+n) - f(m) - f(n)| \leq L$ for
  some $L$.\<close>

text\<open>First we extend the standard notation for integers with notation related
  to slopes. We define slopes as almost homomorphisms on the additive group of
  integers. The set of slopes is denoted \<open>\<S>\<close>. We also define "positive" 
  slopes as those that take infinite number of positive values on positive integers.
  We write \<open>\<delta>(s,m,n)\<close> to denote the homomorphism 
  difference of $s$ at $m,n$ (i.e the expression $s(m+n) - s(m) - s(n)$).
  We denote \<open>max\<delta>(s)\<close> the maximum absolute value of homomorphism 
  difference of $s$ as $m,n$ range over integers.
  If $s$ is a slope, 
  then the set of homomorphism differences is finite and 
  this maximum exists.
  In \<open>Group_ZF_3\<close> we define the equivalence relation on 
  almost homomorphisms using the notion of a quotient group relation
  and use "\<open>\<approx>\<close>" to denote it. As here this symbol seems to be hogged
  by the standard Isabelle, we will use "\<open>\<sim>\<close>" instead "\<open>\<approx>\<close>".
  We show in this section that $s\sim r$ iff for some $L$ we 
  have $|s(m)-r(m)| \leq L$ for all integer $m$.
  The "\<open>\<fp>\<close>" denotes the first operation on almost homomorphisms. 
  For slopes this is addition of functions defined in the natural way.
  The "\<open>\<circ>\<close>" symbol denotes the second operation on almost homomorphisms
  (see \<open>Group_ZF_3\<close> for definition), 
  defined for the group of integers.  In short "\<open>\<circ>\<close>" 
  is the composition of slopes.
  The "\<open>\<inverse>\<close>" symbol acts as an infix operator that assigns the value 
  $\min\{n\in Z_+: p\leq f(n)\}$ to a pair (of sets) $f$ and $p$. 
  In application
  $f$ represents a function defined on $Z_+$ and $p$ is a positive integer.
  We choose this notation because we use it to construct the right inverse 
  in the ring of classes of slopes and show that this ring is in fact a field.
  To study the homomorphism difference of the function defined by $p\mapsto f^{-1}(p)$
  we introduce the symbol \<open>\<epsilon>\<close> defined as 
  $\varepsilon(f,\langle m,n \rangle ) = f^{-1}(m+n)-f^{-1}(m)-f^{-1}(n)$. Of course the intention is
  to use the fact that $\varepsilon(f,\langle m,n \rangle )$ is the homomorphism difference
  of the function $g$ defined as $g(m) = f^{-1}(m)$. We also define $\gamma (s,m,n)$ as the 
  expression $\delta(f,m,-n)+s(0)-\delta (f,n,-n)$. This is useful because of the identity 
  $f(m-n) = \gamma (m,n) + f(m)-f(n)$ that allows to obtain bounds on the value of a slope
  at the difference of of two integers.
  For every integer $m$ we introduce notation $m^S$ defined by $m^E(n)=m\cdot n$. The mapping
  $q\mapsto q^S$ embeds integers into \<open>\<S>\<close> preserving the order, (that is, 
  maps positive integers into \<open>\<S>\<^sub>+\<close>).\<close>

locale int1 = int0 +

  fixes slopes ("\<S>" )
  defines slopes_def[simp]: "\<S> \<equiv> AlmostHoms(\<int>,IntegerAddition)"

  fixes posslopes ("\<S>\<^sub>+")
  defines posslopes_def[simp]: "\<S>\<^sub>+ \<equiv> {s\<in>\<S>. s``(\<int>\<^sub>+) \<inter> \<int>\<^sub>+ \<notin> Fin(\<int>)}"
 
  fixes \<delta> 
  defines \<delta>_def[simp]: "\<delta>(s,m,n) \<equiv> s`(m\<ra>n)\<rs>s`(m)\<rs>s`(n)"

  fixes maxhomdiff ("max\<delta>" )
  defines maxhomdiff_def[simp]: 
  "max\<delta>(s) \<equiv> Maximum(IntegerOrder,{abs(\<delta>(s,m,n)). \<langle> m,n\<rangle> \<in> \<int>\<times>\<int>})"

  fixes AlEqRel
  defines AlEqRel_def[simp]: 
  "AlEqRel \<equiv> QuotientGroupRel(\<S>,AlHomOp1(\<int>,IntegerAddition),FinRangeFunctions(\<int>,\<int>))"

  fixes AlEq (infix "\<sim>" 68)
  defines AlEq_def[simp]: "s \<sim> r \<equiv> \<langle> s,r\<rangle> \<in> AlEqRel"

  fixes slope_add (infix "\<fp>" 70)
  defines slope_add_def[simp]: "s \<fp> r \<equiv>  AlHomOp1(\<int>,IntegerAddition)`\<langle> s,r\<rangle>"

  fixes slope_comp (infix "\<circ>" 70)
  defines slope_comp_def[simp]: "s \<circ> r \<equiv>  AlHomOp2(\<int>,IntegerAddition)`\<langle> s,r\<rangle>"

  fixes neg ("\<fm>_" [90] 91)
  defines neg_def[simp]: "\<fm>s \<equiv> GroupInv(\<int>,IntegerAddition) O s"

  fixes slope_inv (infix "\<inverse>" 71)
  defines slope_inv_def[simp]: 
  "f\<inverse>(p) \<equiv> Minimum(IntegerOrder,{n\<in>\<int>\<^sub>+. p \<lsq> f`(n)})"
  fixes \<epsilon>
  defines \<epsilon>_def[simp]: 
  "\<epsilon>(f,p) \<equiv> f\<inverse>(fst(p)\<ra>snd(p)) \<rs> f\<inverse>(fst(p)) \<rs> f\<inverse>(snd(p))"

  fixes \<gamma> 
  defines \<gamma>_def[simp]:
  "\<gamma>(s,m,n) \<equiv> \<delta>(s,m,\<rm>n) \<rs> \<delta>(s,n,\<rm>n) \<ra> s`(\<zero>)"

  fixes intembed ("_\<^sup>S")
  defines intembed_def[simp]: "m\<^sup>S \<equiv> {\<langle>n,m\<cdot>n\<rangle>. n\<in>\<int>}"

text\<open>We can use theorems proven in the \<open>group1\<close> context.\<close>

lemma (in int1) Int_ZF_2_1_L1: shows "group1(\<int>,IntegerAddition)"
  using Int_ZF_1_T2 group1_axioms.intro group1_def by simp

text\<open>Type information related to the homomorphism difference expression.\<close>

lemma (in int1) Int_ZF_2_1_L2: assumes "f\<in>\<S>" and "n\<in>\<int>" "m\<in>\<int>"
  shows 
  "m\<ra>n \<in> \<int>"  
  "f`(m\<ra>n) \<in> \<int>"  
  "f`(m) \<in> \<int>"   "f`(n) \<in> \<int>"
  "f`(m) \<ra> f`(n) \<in> \<int>"  
  "HomDiff(\<int>,IntegerAddition,f,\<langle> m,n\<rangle>) \<in> \<int>" 
  using assms Int_ZF_2_1_L1 group1.Group_ZF_3_2_L4A
  by auto

text\<open>Type information related to the homomorphism difference expression.\<close>

lemma (in int1) Int_ZF_2_1_L2A: 
  assumes "f:\<int>\<rightarrow>\<int>" and "n\<in>\<int>"  "m\<in>\<int>"
  shows 
  "m\<ra>n \<in> \<int>" 
  "f`(m\<ra>n) \<in> \<int>"   "f`(m) \<in> \<int>"   "f`(n) \<in> \<int>"
  "f`(m) \<ra> f`(n) \<in> \<int>" 
  "HomDiff(\<int>,IntegerAddition,f,\<langle> m,n\<rangle>) \<in> \<int>"
  using assms Int_ZF_2_1_L1 group1.Group_ZF_3_2_L4
  by auto

text\<open>Slopes map integers into integers.\<close>

lemma (in int1) Int_ZF_2_1_L2B: 
  assumes A1: "f\<in>\<S>" and A2: "m\<in>\<int>" 
  shows "f`(m) \<in> \<int>"
proof -
  from A1 have "f:\<int>\<rightarrow>\<int>" using AlmostHoms_def by simp
  with A2 show "f`(m) \<in> \<int>" using apply_funtype by simp
qed

text\<open>The homomorphism difference in multiplicative notation is defined as
  the expression $s(m\cdot n)\cdot(s(m)\cdot s(n))^{-1}$. The next lemma 
  shows that 
  in the additive notation used for integers the homomorphism 
  difference is $f(m+n) - f(m) - f(n)$ which we denote as \<open>\<delta>(f,m,n)\<close>.\<close>

lemma (in int1) Int_ZF_2_1_L3: 
  assumes "f:\<int>\<rightarrow>\<int>" and "m\<in>\<int>"  "n\<in>\<int>"
  shows "HomDiff(\<int>,IntegerAddition,f,\<langle> m,n\<rangle>) = \<delta>(f,m,n)"
  using assms Int_ZF_2_1_L2A Int_ZF_1_T2 group0.group0_4_L4A 
    HomDiff_def by auto

text\<open>The next formula restates the definition of the homomorphism 
  difference to express the value an almost homomorphism on a sum.\<close>

lemma (in int1) Int_ZF_2_1_L3A: 
  assumes A1: "f\<in>\<S>" and A2: "m\<in>\<int>"  "n\<in>\<int>"
  shows 
  "f`(m\<ra>n) = f`(m)\<ra>(f`(n)\<ra>\<delta>(f,m,n))"
proof -
  from A1 A2 have
    T: "f`(m)\<in> \<int>"  "f`(n) \<in> \<int>"  "\<delta>(f,m,n) \<in> \<int>" and
    "HomDiff(\<int>,IntegerAddition,f,\<langle> m,n\<rangle>) = \<delta>(f,m,n)"  
    using Int_ZF_2_1_L2 AlmostHoms_def Int_ZF_2_1_L3 by auto
  with A1 A2 show  "f`(m\<ra>n) = f`(m)\<ra>(f`(n)\<ra>\<delta>(f,m,n))" 
    using Int_ZF_2_1_L3 Int_ZF_1_L3 
      Int_ZF_2_1_L1 group1.Group_ZF_3_4_L1 
    by simp
qed

text\<open>The homomorphism difference of any integer function is integer.\<close>

lemma (in int1) Int_ZF_2_1_L3B: 
  assumes "f:\<int>\<rightarrow>\<int>" and "m\<in>\<int>"  "n\<in>\<int>"
  shows "\<delta>(f,m,n) \<in> \<int>"
  using assms Int_ZF_2_1_L2A Int_ZF_2_1_L3 by simp

text\<open>The value of an integer function at a sum expressed in 
  terms of \<open>\<delta>\<close>.\<close>

lemma (in int1) Int_ZF_2_1_L3C: assumes A1: "f:\<int>\<rightarrow>\<int>" and A2: "m\<in>\<int>"  "n\<in>\<int>"
  shows "f`(m\<ra>n) = \<delta>(f,m,n) \<ra> f`(n) \<ra> f`(m)"
proof -
  from A1 A2 have T:
    "\<delta>(f,m,n) \<in> \<int>"  "f`(m\<ra>n) \<in> \<int>"  "f`(m) \<in> \<int>"  "f`(n) \<in> \<int>"
    using Int_ZF_1_1_L5 apply_funtype by auto
  then show "f`(m\<ra>n) = \<delta>(f,m,n) \<ra> f`(n) \<ra> f`(m)"
    using Int_ZF_1_2_L15 by simp
qed


text\<open>The next lemma presents two ways the set of homomorphism differences
  can be written.\<close>

lemma (in int1) Int_ZF_2_1_L4: assumes A1: "f:\<int>\<rightarrow>\<int>"
  shows "{abs(HomDiff(\<int>,IntegerAddition,f,x)). x \<in> \<int>\<times>\<int>} =
  {abs(\<delta>(f,m,n)). \<langle> m,n\<rangle> \<in> \<int>\<times>\<int>}"
proof -
  from A1 have "\<forall>m\<in>\<int>. \<forall>n\<in>\<int>. 
    abs(HomDiff(\<int>,IntegerAddition,f,\<langle> m,n\<rangle>)) = abs(\<delta>(f,m,n))"
    using Int_ZF_2_1_L3 by simp
  then show ?thesis by (rule ZF1_1_L4A)
qed

text\<open>If $f$ maps integers into integers and 
  for all $m,n\in Z$ we have $|f(m+n) - f(m) - f(n)| \leq L$ for some $L$,
  then $f$ is a slope.\<close>

lemma (in int1) Int_ZF_2_1_L5: assumes A1: "f:\<int>\<rightarrow>\<int>"
  and A2: "\<forall>m\<in>\<int>.\<forall>n\<in>\<int>. abs(\<delta>(f,m,n)) \<lsq> L"
  shows "f\<in>\<S>"
proof -
  let ?Abs = "AbsoluteValue(\<int>,IntegerAddition,IntegerOrder)"
  have "group3(\<int>,IntegerAddition,IntegerOrder)" 
    "IntegerOrder {is total on} \<int>"
    using Int_ZF_2_T1 by auto
  moreover from A1 A2 have 
    "\<forall>x\<in>\<int>\<times>\<int>. HomDiff(\<int>,IntegerAddition,f,x) \<in> \<int> \<and>
    \<langle>?Abs`(HomDiff(\<int>,IntegerAddition,f,x)),L \<rangle> \<in> IntegerOrder"
    using Int_ZF_2_1_L2A Int_ZF_2_1_L3 by auto
  ultimately have 
    "IsBounded({HomDiff(\<int>,IntegerAddition,f,x). x\<in>\<int>\<times>\<int>},IntegerOrder)"
    by (rule group3.OrderedGroup_ZF_3_L9A)
  with A1 show "f \<in> \<S>" using Int_bounded_iff_fin AlmostHoms_def
    by simp
qed

text\<open>The absolute value of homomorphism difference 
  of a slope $s$ does not exceed \<open>max\<delta>(s)\<close>.\<close>

lemma (in int1) Int_ZF_2_1_L7: 
  assumes A1: "s\<in>\<S>" and A2: "n\<in>\<int>"  "m\<in>\<int>"
  shows 
  "abs(\<delta>(s,m,n)) \<lsq> max\<delta>(s)"   
  "\<delta>(s,m,n) \<in> \<int>"   "max\<delta>(s) \<in> \<int>"
  "(\<rm>max\<delta>(s)) \<lsq> \<delta>(s,m,n)"
proof -
  from A1 A2 show T: "\<delta>(s,m,n) \<in> \<int>"
    using Int_ZF_2_1_L2 Int_ZF_1_1_L5 by simp
  let ?A = "{abs(HomDiff(\<int>,IntegerAddition,s,x)). x\<in>\<int>\<times>\<int>}"
  let ?B = "{abs(\<delta>(s,m,n)). \<langle> m,n\<rangle> \<in> \<int>\<times>\<int>}"
  let ?d = "abs(\<delta>(s,m,n))"
  have "IsLinOrder(\<int>,IntegerOrder)" using Int_ZF_2_T1
    by simp
  moreover have "?A \<in> Fin(\<int>)" 
  proof -
    have "\<forall>k\<in>\<int>. abs(k) \<in> \<int>" using Int_ZF_2_L14 by simp
    moreover from A1 have 
      "{HomDiff(\<int>,IntegerAddition,s,x). x \<in> \<int>\<times>\<int>} \<in> Fin(\<int>)"
      using AlmostHoms_def by simp
    ultimately show "?A \<in> Fin(\<int>)" by (rule Finite1_L6C)
  qed
  moreover have "?A\<noteq>0" by auto
  ultimately have "\<forall>k\<in>?A. \<langle>k,Maximum(IntegerOrder,?A)\<rangle> \<in> IntegerOrder"
    by (rule Finite_ZF_1_T2)
  moreover from A1 A2 have "?d\<in>?A" using AlmostHoms_def Int_ZF_2_1_L4
    by auto
  ultimately have "?d \<lsq> Maximum(IntegerOrder,?A)" by auto 
  with A1 show "?d \<lsq> max\<delta>(s)"  "max\<delta>(s) \<in> \<int>"
    using AlmostHoms_def Int_ZF_2_1_L4 Int_ZF_2_L1A 
    by auto
  with T show "(\<rm>max\<delta>(s)) \<lsq> \<delta>(s,m,n)"
    using Int_ZF_1_3_L19 by simp
qed

text\<open>A useful estimate for the value of a slope at $0$, plus some type information
  for slopes.\<close>

lemma (in int1) Int_ZF_2_1_L8: assumes A1: "s\<in>\<S>"
  shows 
  "abs(s`(\<zero>)) \<lsq> max\<delta>(s)"
  "\<zero> \<lsq> max\<delta>(s)"  
  "abs(s`(\<zero>)) \<in> \<int>"   "max\<delta>(s) \<in> \<int>"
  "abs(s`(\<zero>)) \<ra> max\<delta>(s) \<in> \<int>"
proof -
  from A1 have "s`(\<zero>) \<in> \<int>" 
    using int_zero_one_are_int Int_ZF_2_1_L2B by simp
  then have I: "\<zero> \<lsq> abs(s`(\<zero>))"  
    and "abs(\<delta>(s,\<zero>,\<zero>)) = abs(s`(\<zero>))" 
    using int_abs_nonneg int_zero_one_are_int Int_ZF_1_1_L4 
      Int_ZF_2_L17 by auto
  moreover from A1 have "abs(\<delta>(s,\<zero>,\<zero>)) \<lsq> max\<delta>(s)"
    using int_zero_one_are_int Int_ZF_2_1_L7 by simp
  ultimately show II: "abs(s`(\<zero>)) \<lsq> max\<delta>(s)"
    by simp
  with I show "\<zero>\<lsq>max\<delta>(s)" by (rule Int_order_transitive)
  with II show 
    "max\<delta>(s) \<in> \<int>"   "abs(s`(\<zero>)) \<in> \<int>" 
    "abs(s`(\<zero>)) \<ra> max\<delta>(s) \<in> \<int>"
    using Int_ZF_2_L1A Int_ZF_1_1_L5 by auto
qed

text\<open>Int \<open>Group_ZF_3.thy\<close> we show that finite range functions 
  valued in an abelian group 
  form a normal subgroup of almost homomorphisms. 
  This allows to define the equivalence relation 
  between almost homomorphisms as the relation resulting from dividing 
  by that normal subgroup. 
  Then we show in \<open>Group_ZF_3_4_L12\<close> that if the difference of $f$ and $g$ 
  has finite range (actually $f(n)\cdot g(n)^{-1}$ as we use multiplicative 
  notation 
  in \<open>Group_ZF_3.thy\<close>), then $f$ and $g$ are equivalent.
  The next lemma translates that fact into the notation used in \<open>int1\<close> 
  context.\<close>

lemma (in int1) Int_ZF_2_1_L9: assumes A1: "s\<in>\<S>"  "r\<in>\<S>"
  and A2: "\<forall>m\<in>\<int>. abs(s`(m)\<rs>r`(m)) \<lsq> L"
  shows "s \<sim> r"
proof -
  from A1 A2 have 
    "\<forall>m\<in>\<int>. s`(m)\<rs>r`(m) \<in> \<int> \<and> abs(s`(m)\<rs>r`(m)) \<lsq> L"
    using Int_ZF_2_1_L2B Int_ZF_1_1_L5 by simp
  then have
    "IsBounded({s`(n)\<rs>r`(n). n\<in>\<int>}, IntegerOrder)"
    by (rule Int_ZF_1_3_L20)
  with A1 show "s \<sim> r" using Int_bounded_iff_fin 
    Int_ZF_2_1_L1 group1.Group_ZF_3_4_L12 by simp
qed

text\<open>A neccessary condition for two slopes to be almost equal. 
  For slopes the definition postulates the 
  set $\{f(m)-g(m): m\in Z\}$ to be finite. 
  This lemma shows that this implies that
  $|f(m)-g(m)|$ is bounded (by some integer) as $m$ varies over integers.
  We also mention here that in this context \<open>s \<sim> r\<close> implies that both
  $s$ and $r$ are slopes.\<close>

lemma (in int1) Int_ZF_2_1_L9A: assumes "s \<sim> r" 
  shows 
  "\<exists>L\<in>\<int>. \<forall>m\<in>\<int>. abs(s`(m)\<rs>r`(m)) \<lsq> L"
  "s\<in>\<S>"  "r\<in>\<S>"
  using assms Int_ZF_2_1_L1 group1.Group_ZF_3_4_L11 
    Int_ZF_1_3_L20AA QuotientGroupRel_def by auto

text\<open>Let's recall that the relation of almost equality is an equivalence relation
  on the set of slopes.\<close>

lemma (in int1) Int_ZF_2_1_L9B: shows
  "AlEqRel \<subseteq> \<S>\<times>\<S>"
  "equiv(\<S>,AlEqRel)"
  using Int_ZF_2_1_L1 group1.Group_ZF_3_3_L3 by auto

text\<open>Another version of sufficient condition for two slopes to be almost
  equal: if the difference of two slopes is a finite range function, then
  they are almost equal.\<close>

lemma (in int1) Int_ZF_2_1_L9C: assumes "s\<in>\<S>"  "r\<in>\<S>" and 
  "s \<fp> (\<fm>r) \<in> FinRangeFunctions(\<int>,\<int>)"
  shows  
  "s \<sim> r"  
  "r \<sim> s"
  using assms Int_ZF_2_1_L1 
    group1.Group_ZF_3_2_L13 group1.Group_ZF_3_4_L12A
  by auto


text\<open>If two slopes are almost equal, then the difference has finite range.
  This is the inverse of \<open>Int_ZF_2_1_L9C\<close>.\<close>

lemma (in int1) Int_ZF_2_1_L9D: assumes A1: "s \<sim> r"
  shows "s \<fp> (\<fm>r) \<in> FinRangeFunctions(\<int>,\<int>)"
proof -
  let ?G = "\<int>"
  let ?f = "IntegerAddition"
  from A1 have "AlHomOp1(?G, ?f)`\<langle>s,GroupInv(AlmostHoms(?G, ?f),AlHomOp1(?G, ?f))`(r)\<rangle> 
    \<in> FinRangeFunctions(?G, ?G)"
    using Int_ZF_2_1_L1 group1.Group_ZF_3_4_L12B by auto
  with A1 show "s \<fp> (\<fm>r) \<in> FinRangeFunctions(\<int>,\<int>)"
    using Int_ZF_2_1_L9A Int_ZF_2_1_L1 group1.Group_ZF_3_2_L13
    by simp
qed
  
text\<open>What is the value of a composition of slopes?\<close>

lemma (in int1) Int_ZF_2_1_L10: 
  assumes "s\<in>\<S>"  "r\<in>\<S>" and "m\<in>\<int>"
  shows "(s\<circ>r)`(m) = s`(r`(m))"  "s`(r`(m)) \<in> \<int>"
  using assms Int_ZF_2_1_L1 group1.Group_ZF_3_4_L2 by auto

text\<open>Composition of slopes is a slope.\<close>

lemma (in int1) Int_ZF_2_1_L11:
  assumes "s\<in>\<S>"  "r\<in>\<S>"
  shows "s\<circ>r \<in> \<S>"
  using assms Int_ZF_2_1_L1 group1.Group_ZF_3_4_T1 by simp

text\<open>Negative of a slope is a slope.\<close>

lemma (in int1) Int_ZF_2_1_L12: assumes "s\<in>\<S>" shows "\<fm>s \<in> \<S>"
  using assms Int_ZF_1_T2 Int_ZF_2_1_L1 group1.Group_ZF_3_2_L13 
  by simp

text\<open>What is the value of a negative of a slope?\<close>

lemma (in int1) Int_ZF_2_1_L12A: 
  assumes "s\<in>\<S>" and "m\<in>\<int>" shows "(\<fm>s)`(m) = \<rm>(s`(m))"
  using assms Int_ZF_2_1_L1 group1.Group_ZF_3_2_L5
  by simp

text\<open>What are the values of a sum of slopes?\<close>

lemma (in int1) Int_ZF_2_1_L12B: assumes "s\<in>\<S>"  "r\<in>\<S>" and "m\<in>\<int>"
  shows "(s\<fp>r)`(m) = s`(m) \<ra> r`(m)"
  using assms Int_ZF_2_1_L1 group1.Group_ZF_3_2_L12
  by simp

text\<open>Sum of slopes is a slope.\<close>

lemma (in int1) Int_ZF_2_1_L12C: assumes "s\<in>\<S>"  "r\<in>\<S>"
  shows "s\<fp>r \<in> \<S>"
  using assms Int_ZF_2_1_L1 group1.Group_ZF_3_2_L16
  by simp

text\<open>A simple but useful identity.\<close>

lemma (in int1) Int_ZF_2_1_L13: 
  assumes "s\<in>\<S>" and "n\<in>\<int>"  "m\<in>\<int>"
  shows "s`(n\<cdot>m) \<ra> (s`(m) \<ra> \<delta>(s,n\<cdot>m,m)) = s`((n\<ra>\<one>)\<cdot>m)"
  using assms Int_ZF_1_1_L5 Int_ZF_2_1_L2B Int_ZF_1_2_L9 Int_ZF_1_2_L7
  by simp

text\<open>Some estimates for the absolute value of a slope at the opposite 
  integer.\<close>

lemma (in int1) Int_ZF_2_1_L14: assumes A1: "s\<in>\<S>" and A2: "m\<in>\<int>"
  shows 
  "s`(\<rm>m) = s`(\<zero>) \<rs> \<delta>(s,m,\<rm>m) \<rs> s`(m)"
  "abs(s`(m)\<ra>s`(\<rm>m)) \<lsq> \<two>\<cdot>max\<delta>(s)"
  "abs(s`(\<rm>m)) \<lsq> \<two>\<cdot>max\<delta>(s) \<ra> abs(s`(m))"
  "s`(\<rm>m) \<lsq> abs(s`(\<zero>)) \<ra> max\<delta>(s) \<rs> s`(m)"
proof -
  from A1 A2 have T:
    "(\<rm>m) \<in> \<int>"  "abs(s`(m)) \<in> \<int>"  "s`(\<zero>) \<in> \<int>"  "abs(s`(\<zero>)) \<in> \<int>"  
    "\<delta>(s,m,\<rm>m) \<in> \<int>"   "s`(m) \<in> \<int>"   "s`(\<rm>m) \<in> \<int>"  
    "(\<rm>(s`(m))) \<in> \<int>"  "s`(\<zero>) \<rs> \<delta>(s,m,\<rm>m) \<in> \<int>"
    using Int_ZF_1_1_L4 Int_ZF_2_1_L2B Int_ZF_2_L14 Int_ZF_2_1_L2 
      Int_ZF_1_1_L5 int_zero_one_are_int by auto
  with A2 show I: "s`(\<rm>m) = s`(\<zero>) \<rs> \<delta>(s,m,\<rm>m) \<rs> s`(m)"
    using Int_ZF_1_1_L4 Int_ZF_1_2_L15 by simp
  from T have "abs(s`(\<zero>) \<rs> \<delta>(s,m,\<rm>m)) \<lsq> abs(s`(\<zero>)) \<ra> abs(\<delta>(s,m,\<rm>m))"
    using Int_triangle_ineq1 by simp
  moreover from A1 A2 T have "abs(s`(\<zero>)) \<ra> abs(\<delta>(s,m,\<rm>m)) \<lsq>  \<two>\<cdot>max\<delta>(s)"
    using Int_ZF_2_1_L7 Int_ZF_2_1_L8 Int_ZF_1_3_L21 by simp
  ultimately have "abs(s`(\<zero>) \<rs> \<delta>(s,m,\<rm>m)) \<lsq> \<two>\<cdot>max\<delta>(s)"
    by (rule Int_order_transitive)
  moreover
  from I have "s`(m) \<ra> s`(\<rm>m) = s`(m) \<ra> (s`(\<zero>) \<rs> \<delta>(s,m,\<rm>m) \<rs> s`(m))"
    by simp
  with T have "abs(s`(m) \<ra> s`(\<rm>m)) = abs(s`(\<zero>) \<rs> \<delta>(s,m,\<rm>m))"
    using Int_ZF_1_2_L3 by simp
  ultimately show "abs(s`(m)\<ra>s`(\<rm>m)) \<lsq> \<two>\<cdot>max\<delta>(s)"
    by simp
  from I have "abs(s`(\<rm>m)) = abs(s`(\<zero>) \<rs> \<delta>(s,m,\<rm>m) \<rs> s`(m))"
    by simp
  with T have 
    "abs(s`(\<rm>m)) \<lsq> abs(s`(\<zero>)) \<ra> abs(\<delta>(s,m,\<rm>m)) \<ra> abs(s`(m))"
    using int_triangle_ineq3 by simp
  moreover from A1 A2 T have
    "abs(s`(\<zero>)) \<ra> abs(\<delta>(s,m,\<rm>m)) \<ra> abs(s`(m)) \<lsq> \<two>\<cdot>max\<delta>(s) \<ra> abs(s`(m))"
    using Int_ZF_2_1_L7 Int_ZF_2_1_L8 Int_ZF_1_3_L21 int_ord_transl_inv by simp
  ultimately show "abs(s`(\<rm>m)) \<lsq> \<two>\<cdot>max\<delta>(s) \<ra> abs(s`(m))"
    by (rule Int_order_transitive)
  from T have "s`(\<zero>) \<rs> \<delta>(s,m,\<rm>m) \<lsq> abs(s`(\<zero>)) \<ra> abs(\<delta>(s,m,\<rm>m))"
    using Int_ZF_2_L15E by simp
  moreover from A1 A2 T have 
    "abs(s`(\<zero>)) \<ra> abs(\<delta>(s,m,\<rm>m)) \<lsq> abs(s`(\<zero>)) \<ra> max\<delta>(s)"
    using Int_ZF_2_1_L7 int_ord_transl_inv by simp
  ultimately have "s`(\<zero>) \<rs> \<delta>(s,m,\<rm>m) \<lsq> abs(s`(\<zero>)) \<ra> max\<delta>(s)"
    by (rule Int_order_transitive)
  with T have 
    "s`(\<zero>) \<rs> \<delta>(s,m,\<rm>m) \<rs> s`(m) \<lsq> abs(s`(\<zero>)) \<ra> max\<delta>(s) \<rs> s`(m)"
    using int_ord_transl_inv by simp
  with I show "s`(\<rm>m) \<lsq> abs(s`(\<zero>)) \<ra> max\<delta>(s) \<rs> s`(m)"
    by simp
qed

text\<open>An identity that expresses the value of an integer function at the opposite
  integer in terms of the value of that function at the integer, zero, and the 
  homomorphism difference. We have a similar identity in \<open>Int_ZF_2_1_L14\<close>, but
  over there we assume that $f$ is a slope.\<close>

lemma (in int1) Int_ZF_2_1_L14A: assumes A1: "f:\<int>\<rightarrow>\<int>" and A2: "m\<in>\<int>"
  shows "f`(\<rm>m) = (\<rm>\<delta>(f,m,\<rm>m)) \<ra> f`(\<zero>) \<rs> f`(m)"
proof -
  from A1 A2 have T:
    "f`(\<rm>m) \<in> \<int>"  "\<delta>(f,m,\<rm>m) \<in> \<int>"  "f`(\<zero>) \<in> \<int>"  "f`(m) \<in> \<int>"
    using Int_ZF_1_1_L4 Int_ZF_1_1_L5 int_zero_one_are_int apply_funtype 
    by auto
   with A2 show "f`(\<rm>m) = (\<rm>\<delta>(f,m,\<rm>m)) \<ra> f`(\<zero>) \<rs> f`(m)"
     using Int_ZF_1_1_L4 Int_ZF_1_2_L15 by simp
qed

text\<open>The next lemma allows to use the expression \<open>maxf(f,\<zero>..M-1)\<close>. 
  Recall that \<open>maxf(f,A)\<close> is the maximum of (function) $f$ on 
  (the set) $A$.\<close>

lemma (in int1) Int_ZF_2_1_L15:
  assumes "s\<in>\<S>" and "M \<in> \<int>\<^sub>+"
  shows 
  "maxf(s,\<zero>..(M\<rs>\<one>)) \<in> \<int>"
  "\<forall>n \<in> \<zero>..(M\<rs>\<one>). s`(n) \<lsq> maxf(s,\<zero>..(M\<rs>\<one>))"
  "minf(s,\<zero>..(M\<rs>\<one>)) \<in> \<int>"
  "\<forall>n \<in> \<zero>..(M\<rs>\<one>). minf(s,\<zero>..(M\<rs>\<one>)) \<lsq> s`(n)"
  using assms AlmostHoms_def Int_ZF_1_5_L6 Int_ZF_1_4_L2
  by auto

text\<open>A lower estimate for the value of a slope at $nM+k$.\<close>

lemma (in int1) Int_ZF_2_1_L16:
  assumes A1: "s\<in>\<S>"  and A2: "m\<in>\<int>" and A3: "M \<in> \<int>\<^sub>+" and A4: "k \<in> \<zero>..(M\<rs>\<one>)"
  shows "s`(m\<cdot>M) \<ra> (minf(s,\<zero>..(M\<rs>\<one>))\<rs> max\<delta>(s)) \<lsq> s`(m\<cdot>M\<ra>k)"
proof -
  from A3 have "\<zero>..(M\<rs>\<one>) \<subseteq> \<int>"
    using Int_ZF_1_5_L6 by simp
  with A1 A2 A3 A4 have T: "m\<cdot>M \<in> \<int>"   "k \<in> \<int>"  "s`(m\<cdot>M) \<in> \<int>"
    using PositiveSet_def Int_ZF_1_1_L5  Int_ZF_2_1_L2B
    by auto
  with A1 A3 A4 have 
    "s`(m\<cdot>M) \<ra> (minf(s,\<zero>..(M\<rs>\<one>)) \<rs> max\<delta>(s)) \<lsq> s`(m\<cdot>M) \<ra> (s`(k) \<ra> \<delta>(s,m\<cdot>M,k))"
    using Int_ZF_2_1_L15 Int_ZF_2_1_L7 int_ineq_add_sides int_ord_transl_inv
    by simp
  with A1 T show ?thesis using Int_ZF_2_1_L3A by simp
qed

text\<open>Identity is a slope.\<close>

lemma (in int1) Int_ZF_2_1_L17: shows "id(\<int>) \<in> \<S>"
  using Int_ZF_2_1_L1 group1.Group_ZF_3_4_L15 by simp

text\<open>Simple identities about (absolute value of) homomorphism differences.\<close>

lemma (in int1) Int_ZF_2_1_L18:  
  assumes A1: "f:\<int>\<rightarrow>\<int>" and A2: "m\<in>\<int>"  "n\<in>\<int>"
  shows 
  "abs(f`(n) \<ra> f`(m) \<rs> f`(m\<ra>n)) = abs(\<delta>(f,m,n))"
  "abs(f`(m) \<ra> f`(n) \<rs> f`(m\<ra>n)) = abs(\<delta>(f,m,n))"
  "(\<rm>(f`(m))) \<rs> f`(n) \<ra> f`(m\<ra>n) = \<delta>(f,m,n)"
  "(\<rm>(f`(n))) \<rs> f`(m) \<ra> f`(m\<ra>n) = \<delta>(f,m,n)"
  "abs((\<rm>f`(m\<ra>n)) \<ra> f`(m) \<ra> f`(n)) = abs(\<delta>(f,m,n))"
proof -
  from A1 A2 have T: 
    "f`(m\<ra>n) \<in> \<int>"  "f`(m) \<in> \<int>"  "f`(n) \<in> \<int>"
    "f`(m\<ra>n) \<rs> f`(m) \<rs>  f`(n)  \<in> \<int>"
    "(\<rm>(f`(m))) \<in> \<int>"
    "(\<rm>f`(m\<ra>n)) \<ra> f`(m) \<ra> f`(n) \<in> \<int>"
    using apply_funtype Int_ZF_1_1_L4 Int_ZF_1_1_L5 by auto
  then have 
    "abs(\<rm>(f`(m\<ra>n) \<rs> f`(m) \<rs>  f`(n))) = abs(f`(m\<ra>n) \<rs> f`(m) \<rs>  f`(n))"
    using Int_ZF_2_L17 by simp
  moreover from T have 
    "(\<rm>(f`(m\<ra>n) \<rs> f`(m) \<rs>  f`(n))) = f`(n) \<ra> f`(m) \<rs> f`(m\<ra>n)"
    using Int_ZF_1_2_L9A by simp
  ultimately show "abs(f`(n) \<ra> f`(m) \<rs> f`(m\<ra>n)) = abs(\<delta>(f,m,n))"
    by simp
  moreover from T have "f`(n) \<ra> f`(m) = f`(m) \<ra> f`(n)"
    using Int_ZF_1_1_L5 by simp
  ultimately show "abs(f`(m) \<ra> f`(n) \<rs> f`(m\<ra>n)) = abs(\<delta>(f,m,n))"
    by simp
  from T show 
    "(\<rm>(f`(m))) \<rs> f`(n) \<ra> f`(m\<ra>n) = \<delta>(f,m,n)"
    "(\<rm>(f`(n))) \<rs> f`(m) \<ra> f`(m\<ra>n) = \<delta>(f,m,n)"
    using Int_ZF_1_2_L9 by auto
  from T have 
    "abs((\<rm>f`(m\<ra>n)) \<ra> f`(m) \<ra> f`(n)) =
    abs(\<rm>((\<rm>f`(m\<ra>n)) \<ra> f`(m) \<ra> f`(n)))"
    using Int_ZF_2_L17 by simp
  also from T have 
    "abs(\<rm>((\<rm>f`(m\<ra>n)) \<ra> f`(m) \<ra> f`(n))) = abs(\<delta>(f,m,n))"
    using Int_ZF_1_2_L9 by simp
  finally show "abs((\<rm>f`(m\<ra>n)) \<ra> f`(m) \<ra> f`(n)) = abs(\<delta>(f,m,n))"
    by simp
qed
  
text\<open>Some identities about the homomorphism difference of odd functions.\<close>

lemma (in int1) Int_ZF_2_1_L19: 
  assumes A1: "f:\<int>\<rightarrow>\<int>" and A2: "\<forall>x\<in>\<int>. (\<rm>f`(\<rm>x)) = f`(x)"
  and A3: "m\<in>\<int>"  "n\<in>\<int>"
  shows
  "abs(\<delta>(f,\<rm>m,m\<ra>n)) = abs(\<delta>(f,m,n))"
  "abs(\<delta>(f,\<rm>n,m\<ra>n)) = abs(\<delta>(f,m,n))"
  "\<delta>(f,n,\<rm>(m\<ra>n)) = \<delta>(f,m,n)"
  "\<delta>(f,m,\<rm>(m\<ra>n)) = \<delta>(f,m,n)"
  "abs(\<delta>(f,\<rm>m,\<rm>n)) = abs(\<delta>(f,m,n))"
proof -
  from A1 A2 A3 show 
    "abs(\<delta>(f,\<rm>m,m\<ra>n)) = abs(\<delta>(f,m,n))"
    "abs(\<delta>(f,\<rm>n,m\<ra>n)) = abs(\<delta>(f,m,n))"
    using Int_ZF_1_2_L3 Int_ZF_2_1_L18 by auto
  from A3 have T: "m\<ra>n \<in> \<int>" using Int_ZF_1_1_L5 by simp
  from A1 A2 have I: "\<forall>x\<in>\<int>. f`(\<rm>x) = (\<rm>f`(x))"
    using Int_ZF_1_5_L13 by simp
  with A1 A2 A3 T show 
    "\<delta>(f,n,\<rm>(m\<ra>n)) = \<delta>(f,m,n)"
    "\<delta>(f,m,\<rm>(m\<ra>n)) = \<delta>(f,m,n)"
    using Int_ZF_1_2_L3 Int_ZF_2_1_L18 by auto
  from A3 have 
    "abs(\<delta>(f,\<rm>m,\<rm>n)) = abs(f`(\<rm>(m\<ra>n)) \<rs> f`(\<rm>m) \<rs> f`(\<rm>n))"
    using Int_ZF_1_1_L5 by simp
  also from A1 A2 A3 T I have "\<dots> = abs(\<delta>(f,m,n))"
    using Int_ZF_2_1_L18 by simp
  finally show "abs(\<delta>(f,\<rm>m,\<rm>n)) = abs(\<delta>(f,m,n))" by simp
qed

text\<open>Recall that $f$ is a slope iff $f(m+n)-f(m)-f(n)$ is bounded
  as $m,n$ ranges over integers. The next lemma is the first 
  step in showing that we only need to check this condition as $m,n$ ranges
  over positive intergers. Namely we show that if the condition holds for
  positive integers, then it holds if one integer is positive and the second 
  one is nonnegative.\<close>

lemma (in int1) Int_ZF_2_1_L20: assumes A1: "f:\<int>\<rightarrow>\<int>" and
  A2: "\<forall>a\<in>\<int>\<^sub>+. \<forall>b\<in>\<int>\<^sub>+. abs(\<delta>(f,a,b)) \<lsq> L" and
  A3:  "m\<in>\<int>\<^sup>+"  "n\<in>\<int>\<^sub>+"
  shows 
  "\<zero> \<lsq> L"
  "abs(\<delta>(f,m,n)) \<lsq> L \<ra> abs(f`(\<zero>))"
proof -       
  from A1 A2 have 
    "\<delta>(f,\<one>,\<one>) \<in> \<int>"  and "abs(\<delta>(f,\<one>,\<one>)) \<lsq> L" 
    using int_one_two_are_pos PositiveSet_def Int_ZF_2_1_L3B
    by auto
  then show I: "\<zero> \<lsq> L" using Int_ZF_1_3_L19 by simp
  from A1 A3 have T: 
    "n \<in> \<int>"  "f`(n) \<in> \<int>"  "f`(\<zero>) \<in> \<int>"  
    "\<delta>(f,m,n) \<in> \<int>"  "abs(\<delta>(f,m,n)) \<in> \<int>"
    using PositiveSet_def int_zero_one_are_int apply_funtype
      Nonnegative_def Int_ZF_2_1_L3B Int_ZF_2_L14 by auto
  from A3 have "m=\<zero> \<or> m\<in>\<int>\<^sub>+" using Int_ZF_1_5_L3A by auto
  moreover
  { assume "m = \<zero>"
    with T I have "abs(\<delta>(f,m,n)) \<lsq> L \<ra> abs(f`(\<zero>))"
      using Int_ZF_1_1_L4 Int_ZF_1_2_L3 Int_ZF_2_L17 
	int_ord_is_refl refl_def Int_ZF_2_L15F by simp }
  moreover
  { assume "m\<in>\<int>\<^sub>+"
    with A2 A3 T have "abs(\<delta>(f,m,n)) \<lsq> L \<ra> abs(f`(\<zero>))"
       using int_abs_nonneg Int_ZF_2_L15F by simp }
   ultimately show "abs(\<delta>(f,m,n)) \<lsq> L \<ra> abs(f`(\<zero>))"
     by auto
qed

text\<open>If the slope condition holds for all pairs of integers such that one integer is 
  positive and the second one is nonnegative, then it holds when both integers are 
  nonnegative.\<close>

lemma (in int1) Int_ZF_2_1_L21: assumes A1: "f:\<int>\<rightarrow>\<int>" and
  A2: "\<forall>a\<in>\<int>\<^sup>+. \<forall>b\<in>\<int>\<^sub>+. abs(\<delta>(f,a,b)) \<lsq> L" and
  A3: "n\<in>\<int>\<^sup>+"  "m\<in>\<int>\<^sup>+"
  shows "abs(\<delta>(f,m,n)) \<lsq> L \<ra> abs(f`(\<zero>))"
proof -
  from A1 A2 have 
    "\<delta>(f,\<one>,\<one>) \<in> \<int>"  and "abs(\<delta>(f,\<one>,\<one>)) \<lsq> L" 
    using int_one_two_are_pos PositiveSet_def Nonnegative_def Int_ZF_2_1_L3B
    by auto
  then have I: "\<zero> \<lsq> L" using Int_ZF_1_3_L19 by simp
  from A1 A3 have T: 
    "m \<in> \<int>"  "f`(m) \<in> \<int>"  "f`(\<zero>) \<in> \<int>"  "(\<rm>f`(\<zero>)) \<in> \<int>"  
    "\<delta>(f,m,n) \<in> \<int>"  "abs(\<delta>(f,m,n)) \<in> \<int>"
    using int_zero_one_are_int apply_funtype Nonnegative_def 
      Int_ZF_2_1_L3B Int_ZF_2_L14 Int_ZF_1_1_L4 by auto
  from A3 have "n=\<zero> \<or> n\<in>\<int>\<^sub>+" using Int_ZF_1_5_L3A by auto
  moreover
  { assume "n=\<zero>"
     with T have "\<delta>(f,m,n) = \<rm>f`(\<zero>)"
      using Int_ZF_1_1_L4 by simp
    with T have "abs(\<delta>(f,m,n)) = abs(f`(\<zero>))"
      using Int_ZF_2_L17 by simp
    with T have "abs(\<delta>(f,m,n)) \<lsq> abs(f`(\<zero>))"
      using int_ord_is_refl refl_def by simp
    with T I have "abs(\<delta>(f,m,n)) \<lsq> L \<ra> abs(f`(\<zero>))"
      using Int_ZF_2_L15F by simp }
  moreover
  { assume "n\<in>\<int>\<^sub>+"
    with A2 A3 T have "abs(\<delta>(f,m,n)) \<lsq> L \<ra> abs(f`(\<zero>))"
      using int_abs_nonneg Int_ZF_2_L15F by simp }
  ultimately show  "abs(\<delta>(f,m,n)) \<lsq> L \<ra> abs(f`(\<zero>))"
    by auto
qed

text\<open>If the homomorphism difference is bounded on \<open>\<int>\<^sub>+\<times>\<int>\<^sub>+\<close>, 
  then it is bounded on \<open>\<int>\<^sup>+\<times>\<int>\<^sup>+\<close>.\<close>

lemma (in int1) Int_ZF_2_1_L22: assumes A1: "f:\<int>\<rightarrow>\<int>" and
  A2: "\<forall>a\<in>\<int>\<^sub>+. \<forall>b\<in>\<int>\<^sub>+. abs(\<delta>(f,a,b)) \<lsq> L"
  shows "\<exists>M. \<forall>m\<in>\<int>\<^sup>+. \<forall>n\<in>\<int>\<^sup>+. abs(\<delta>(f,m,n)) \<lsq> M"
proof -
  from A1 A2 have 
    "\<forall>m\<in>\<int>\<^sup>+. \<forall>n\<in>\<int>\<^sup>+. abs(\<delta>(f,m,n)) \<lsq> L \<ra> abs(f`(\<zero>)) \<ra> abs(f`(\<zero>))"
    using Int_ZF_2_1_L20 Int_ZF_2_1_L21 by simp
  then show ?thesis by auto
qed

text\<open>For odd functions we can do better than in \<open>Int_ZF_2_1_L22\<close>: 
  if the homomorphism 
  difference of $f$ is bounded on \<open>\<int>\<^sup>+\<times>\<int>\<^sup>+\<close>, then it is bounded 
  on \<open>\<int>\<times>\<int>\<close>, hence $f$ is a slope. 
  Loong prof by splitting the \<open>\<int>\<times>\<int>\<close> into six subsets.\<close>

lemma (in int1) Int_ZF_2_1_L23: assumes A1: "f:\<int>\<rightarrow>\<int>" and
  A2: "\<forall>a\<in>\<int>\<^sub>+. \<forall>b\<in>\<int>\<^sub>+. abs(\<delta>(f,a,b)) \<lsq> L"
  and A3: "\<forall>x\<in>\<int>. (\<rm>f`(\<rm>x)) = f`(x)"
  shows (*"\<exists>M. \<forall>m\<in>\<int>. \<forall>n\<in>\<int>. abs(\<delta>(f,m,n)) \<lsq> M"*) "f\<in>\<S>"
proof -
  from A1 A2 have
    "\<exists>M.\<forall>a\<in>\<int>\<^sup>+. \<forall>b\<in>\<int>\<^sup>+. abs(\<delta>(f,a,b)) \<lsq> M"
    by (rule Int_ZF_2_1_L22)
  then obtain M where I: "\<forall>m\<in>\<int>\<^sup>+. \<forall>n\<in>\<int>\<^sup>+. abs(\<delta>(f,m,n)) \<lsq> M"
    by auto
  { fix a b assume A4: "a\<in>\<int>"  "b\<in>\<int>"
    then have 
      "\<zero>\<lsq>a \<and> \<zero>\<lsq>b  \<or>  a\<lsq>\<zero> \<and> b\<lsq>\<zero>  \<or>  
      a\<lsq>\<zero> \<and> \<zero>\<lsq>b \<and> \<zero> \<lsq> a\<ra>b  \<or> a\<lsq>\<zero> \<and> \<zero>\<lsq>b \<and> a\<ra>b \<lsq> \<zero>  \<or>  
      \<zero>\<lsq>a \<and> b\<lsq>\<zero> \<and> \<zero> \<lsq> a\<ra>b  \<or>  \<zero>\<lsq>a \<and> b\<lsq>\<zero> \<and> a\<ra>b \<lsq> \<zero>"
      using int_plane_split_in6 by simp
    moreover
    { assume "\<zero>\<lsq>a \<and> \<zero>\<lsq>b" 
      then have "a\<in>\<int>\<^sup>+"  "b\<in>\<int>\<^sup>+"
	using Int_ZF_2_L16 by auto
      with I have "abs(\<delta>(f,a,b)) \<lsq> M" by simp }
    moreover
    { assume "a\<lsq>\<zero> \<and> b\<lsq>\<zero>"
      with I have "abs(\<delta>(f,\<rm>a,\<rm>b)) \<lsq> M"
	using Int_ZF_2_L10A Int_ZF_2_L16 by simp
      with A1 A3 A4 have "abs(\<delta>(f,a,b)) \<lsq> M"
	using Int_ZF_2_1_L19 by simp }
    moreover
    { assume "a\<lsq>\<zero> \<and> \<zero>\<lsq>b \<and> \<zero> \<lsq> a\<ra>b"
      with I have "abs(\<delta>(f,\<rm>a,a\<ra>b)) \<lsq> M"
	using Int_ZF_2_L10A Int_ZF_2_L16 by simp
      with A1 A3 A4 have "abs(\<delta>(f,a,b)) \<lsq> M"
	using Int_ZF_2_1_L19 by simp } 
    moreover
    { assume "a\<lsq>\<zero> \<and> \<zero>\<lsq>b \<and> a\<ra>b \<lsq> \<zero>"
      with I have "abs(\<delta>(f,b,\<rm>(a\<ra>b))) \<lsq> M"
	using Int_ZF_2_L10A Int_ZF_2_L16 by simp
      with A1 A3 A4 have "abs(\<delta>(f,a,b)) \<lsq> M"
	using Int_ZF_2_1_L19 by simp }
    moreover
    { assume "\<zero>\<lsq>a \<and> b\<lsq>\<zero> \<and> \<zero> \<lsq> a\<ra>b"
      with I have "abs(\<delta>(f,\<rm>b,a\<ra>b)) \<lsq> M"
	using Int_ZF_2_L10A Int_ZF_2_L16 by simp
      with A1 A3 A4 have "abs(\<delta>(f,a,b)) \<lsq> M"
	using Int_ZF_2_1_L19 by simp }
    moreover
    { assume "\<zero>\<lsq>a \<and> b\<lsq>\<zero> \<and> a\<ra>b \<lsq> \<zero>" 
      with I have "abs(\<delta>(f,a,\<rm>(a\<ra>b))) \<lsq> M"
	using Int_ZF_2_L10A Int_ZF_2_L16 by simp
      with A1 A3 A4 have "abs(\<delta>(f,a,b)) \<lsq> M"
	using Int_ZF_2_1_L19 by simp }
    ultimately have "abs(\<delta>(f,a,b)) \<lsq> M" by auto } 
  then have "\<forall>m\<in>\<int>. \<forall>n\<in>\<int>. abs(\<delta>(f,m,n)) \<lsq> M" by simp
  with A1 show "f\<in>\<S>" by (rule Int_ZF_2_1_L5)
qed

text\<open>If the homomorphism difference of a function defined 
  on positive integers is bounded, then the odd extension
  of this function is a slope.\<close>

lemma (in int1) Int_ZF_2_1_L24: 
  assumes A1: "f:\<int>\<^sub>+\<rightarrow>\<int>" and A2: "\<forall>a\<in>\<int>\<^sub>+. \<forall>b\<in>\<int>\<^sub>+. abs(\<delta>(f,a,b)) \<lsq> L"
  shows "OddExtension(\<int>,IntegerAddition,IntegerOrder,f) \<in> \<S>"
proof -
  let ?g = "OddExtension(\<int>,IntegerAddition,IntegerOrder,f)"
  from A1 have "?g : \<int>\<rightarrow>\<int>"
    using Int_ZF_1_5_L10 by simp
  moreover have "\<forall>a\<in>\<int>\<^sub>+. \<forall>b\<in>\<int>\<^sub>+. abs(\<delta>(?g,a,b)) \<lsq> L"
  proof -
    { fix a b assume A3: "a\<in>\<int>\<^sub>+"  "b\<in>\<int>\<^sub>+"
      with A1 have "abs(\<delta>(f,a,b)) =  abs(\<delta>(?g,a,b))"
	using pos_int_closed_add_unfolded Int_ZF_1_5_L11 
	by simp
      moreover from A2 A3 have "abs(\<delta>(f,a,b)) \<lsq> L" by simp
      ultimately have "abs(\<delta>(?g,a,b)) \<lsq> L" by simp
    } then show ?thesis by simp
  qed
  moreover from A1 have "\<forall>x\<in>\<int>. (\<rm>?g`(\<rm>x)) = ?g`(x)"
    using int_oddext_is_odd_alt by simp
  ultimately show "?g \<in> \<S>" by (rule Int_ZF_2_1_L23)
qed

text\<open>Type information related to $\gamma$.\<close>

lemma (in int1) Int_ZF_2_1_L25: 
  assumes A1: "f:\<int>\<rightarrow>\<int>" and A2: "m\<in>\<int>"  "n\<in>\<int>"
  shows 
  "\<delta>(f,m,\<rm>n) \<in> \<int>"
  "\<delta>(f,n,\<rm>n) \<in> \<int>"
  "(\<rm>\<delta>(f,n,\<rm>n)) \<in> \<int>"
  "f`(\<zero>) \<in> \<int>"
  "\<gamma>(f,m,n)  \<in> \<int>"
proof -
  from A1 A2 show T1:
    "\<delta>(f,m,\<rm>n) \<in> \<int>"  "f`(\<zero>) \<in> \<int>"
    using Int_ZF_1_1_L4 Int_ZF_2_1_L3B int_zero_one_are_int apply_funtype
    by auto
  from A2 have "(\<rm>n) \<in> \<int>"
    using Int_ZF_1_1_L4 by simp
  with A1 A2 show "\<delta>(f,n,\<rm>n) \<in> \<int>"
    using Int_ZF_2_1_L3B by simp
  then show "(\<rm>\<delta>(f,n,\<rm>n)) \<in> \<int>"
    using Int_ZF_1_1_L4 by simp
  with T1 show "\<gamma>(f,m,n)  \<in> \<int>"
    using Int_ZF_1_1_L5 by simp
qed 

text\<open>A couple of formulae involving $f(m-n)$ and $\gamma(f,m,n)$.\<close>

lemma (in int1) Int_ZF_2_1_L26: 
  assumes A1: "f:\<int>\<rightarrow>\<int>" and A2: "m\<in>\<int>"  "n\<in>\<int>"
  shows 
  "f`(m\<rs>n) = \<gamma>(f,m,n) \<ra> f`(m) \<rs> f`(n)"
  "f`(m\<rs>n) = \<gamma>(f,m,n) \<ra> (f`(m) \<rs> f`(n))"
  "f`(m\<rs>n) \<ra> (f`(n) \<rs> \<gamma>(f,m,n)) = f`(m)"
proof -
  from A1 A2 have T:
    "(\<rm>n) \<in> \<int>"  "\<delta>(f,m,\<rm>n) \<in> \<int>"  
    "f`(\<zero>) \<in> \<int>"  "f`(m) \<in> \<int>"  "f`(n) \<in> \<int>"  "(\<rm>f`(n)) \<in> \<int>"
    "(\<rm>\<delta>(f,n,\<rm>n)) \<in> \<int>"  
    "(\<rm>\<delta>(f,n,\<rm>n))  \<ra> f`(\<zero>) \<in> \<int>"
    "\<gamma>(f,m,n) \<in> \<int>"
    using  Int_ZF_1_1_L4 Int_ZF_2_1_L25 apply_funtype Int_ZF_1_1_L5 
    by auto
   with A1 A2 have "f`(m\<rs>n) = 
    \<delta>(f,m,\<rm>n) \<ra> ((\<rm>\<delta>(f,n,\<rm>n)) \<ra> f`(\<zero>) \<rs> f`(n)) \<ra> f`(m)"
    using Int_ZF_2_1_L3C Int_ZF_2_1_L14A by simp
  with T have "f`(m\<rs>n) =
    \<delta>(f,m,\<rm>n) \<ra> ((\<rm>\<delta>(f,n,\<rm>n)) \<ra> f`(\<zero>)) \<ra> f`(m) \<rs> f`(n)"
    using Int_ZF_1_2_L16 by simp
  moreover from T have 
    "\<delta>(f,m,\<rm>n) \<ra> ((\<rm>\<delta>(f,n,\<rm>n)) \<ra> f`(\<zero>)) = \<gamma>(f,m,n)"
    using Int_ZF_1_1_L7 by simp
  ultimately show  I: "f`(m\<rs>n) = \<gamma>(f,m,n) \<ra> f`(m) \<rs> f`(n)"
    by simp
  then have "f`(m\<rs>n) \<ra> (f`(n) \<rs> \<gamma>(f,m,n)) = 
    (\<gamma>(f,m,n) \<ra> f`(m) \<rs> f`(n)) \<ra> (f`(n) \<rs> \<gamma>(f,m,n))"
    by simp
  moreover from T have "\<dots> = f`(m)" using Int_ZF_1_2_L18 
    by simp
  ultimately show "f`(m\<rs>n) \<ra> (f`(n) \<rs> \<gamma>(f,m,n)) = f`(m)"
    by simp
  from T have "\<gamma>(f,m,n) \<in> \<int>"  "f`(m) \<in> \<int>"  "(\<rm>f`(n)) \<in> \<int>"
    by auto
  then have 
    "\<gamma>(f,m,n) \<ra> f`(m) \<ra> (\<rm>f`(n)) =  \<gamma>(f,m,n) \<ra> (f`(m) \<ra> (\<rm>f`(n)))"
    by (rule Int_ZF_1_1_L7)
  with I show  "f`(m\<rs>n) = \<gamma>(f,m,n) \<ra> (f`(m) \<rs> f`(n))" by simp
qed

text\<open>A formula expressing the difference between $f(m-n-k)$ and
  $f(m)-f(n)-f(k)$ in terms of $\gamma$.\<close>

lemma (in int1) Int_ZF_2_1_L26A: 
  assumes A1: "f:\<int>\<rightarrow>\<int>" and A2: "m\<in>\<int>"  "n\<in>\<int>"  "k\<in>\<int>"
  shows 
  "f`(m\<rs>n\<rs>k) \<rs> (f`(m)\<rs> f`(n) \<rs> f`(k)) = \<gamma>(f,m\<rs>n,k) \<ra> \<gamma>(f,m,n)"
proof -
  from A1 A2 have 
    T: "m\<rs>n \<in> \<int>" "\<gamma>(f,m\<rs>n,k) \<in> \<int>"  "f`(m) \<rs> f`(n) \<rs> f`(k) \<in> \<int>" and
    T1: "\<gamma>(f,m,n) \<in> \<int>"  "f`(m) \<rs> f`(n) \<in> \<int>"  "(\<rm>f`(k)) \<in> \<int>"
    using Int_ZF_1_1_L4 Int_ZF_1_1_L5 Int_ZF_2_1_L25 apply_funtype 
    by auto
  from A1 A2 have 
    "f`(m\<rs>n) \<rs> f`(k) = \<gamma>(f,m,n) \<ra> (f`(m) \<rs> f`(n)) \<ra> (\<rm>f`(k))"
    using Int_ZF_2_1_L26 by simp
  also from T1 have "\<dots> = \<gamma>(f,m,n) \<ra> (f`(m) \<rs> f`(n) \<ra> (\<rm>f`(k)))"
    by (rule Int_ZF_1_1_L7)
  finally have 
    "f`(m\<rs>n) \<rs> f`(k) = \<gamma>(f,m,n) \<ra> (f`(m) \<rs> f`(n) \<rs> f`(k))"
    by simp
  moreover from A1 A2 T have
    "f`(m\<rs>n\<rs>k) =  \<gamma>(f,m\<rs>n,k) \<ra> (f`(m\<rs>n)\<rs>f`(k))"
    using Int_ZF_2_1_L26 by simp
  ultimately have 
    "f`(m\<rs>n\<rs>k) \<rs> (f`(m)\<rs> f`(n) \<rs> f`(k)) = 
    \<gamma>(f,m\<rs>n,k) \<ra> ( \<gamma>(f,m,n) \<ra> (f`(m) \<rs> f`(n) \<rs> f`(k))) 
    \<rs> (f`(m)\<rs> f`(n) \<rs> f`(k))"
    by simp
  with T T1 show ?thesis 
    using Int_ZF_1_2_L17 by simp
qed


text\<open>If $s$ is a slope, then $\gamma (s,m,n)$ is uniformly bounded.\<close>

lemma (in int1) Int_ZF_2_1_L27: assumes A1: "s\<in>\<S>"
  shows "\<exists>L\<in>\<int>. \<forall>m\<in>\<int>.\<forall>n\<in>\<int>. abs(\<gamma>(s,m,n)) \<lsq> L"
proof -
  let ?L = "max\<delta>(s) \<ra> max\<delta>(s) \<ra> abs(s`(\<zero>))"
  from A1 have T: 
    "max\<delta>(s) \<in> \<int>"  "abs(s`(\<zero>)) \<in> \<int>"  "?L \<in> \<int>"
    using Int_ZF_2_1_L8 int_zero_one_are_int Int_ZF_2_1_L2B 
      Int_ZF_2_L14 Int_ZF_1_1_L5 by auto
  moreover
  { fix m 
    fix n
    assume A2: "m\<in>\<int>"  "n\<in>\<int>"
    with A1 have T: 
      "(\<rm>n) \<in> \<int>"
      "\<delta>(s,m,\<rm>n) \<in> \<int>"
      "\<delta>(s,n,\<rm>n) \<in> \<int>"
      "(\<rm>\<delta>(s,n,\<rm>n)) \<in> \<int>"
      "s`(\<zero>) \<in> \<int>"  "abs(s`(\<zero>)) \<in> \<int>"
      using Int_ZF_1_1_L4 AlmostHoms_def Int_ZF_2_1_L25 Int_ZF_2_L14
      by auto
    with T have
      "abs(\<delta>(s,m,\<rm>n) \<rs> \<delta>(s,n,\<rm>n) \<ra> s`(\<zero>)) \<lsq>
      abs(\<delta>(s,m,\<rm>n)) \<ra> abs(\<rm>\<delta>(s,n,\<rm>n)) \<ra> abs(s`(\<zero>))"
      using Int_triangle_ineq3 by simp
    moreover from A1 A2 T have 
      "abs(\<delta>(s,m,\<rm>n)) \<ra> abs(\<rm>\<delta>(s,n,\<rm>n)) \<ra> abs(s`(\<zero>)) \<lsq> ?L"
      using Int_ZF_2_1_L7 int_ineq_add_sides int_ord_transl_inv Int_ZF_2_L17
      by simp
   ultimately have "abs(\<delta>(s,m,\<rm>n) \<rs> \<delta>(s,n,\<rm>n) \<ra> s`(\<zero>)) \<lsq> ?L"
      by (rule Int_order_transitive)    
    then have "abs(\<gamma>(s,m,n)) \<lsq> ?L" by simp }
  ultimately show "\<exists>L\<in>\<int>. \<forall>m\<in>\<int>.\<forall>n\<in>\<int>. abs(\<gamma>(s,m,n)) \<lsq> L"
    by auto
qed


text\<open>If $s$ is a slope, then $s(m) \leq s(m-1) + M$, where $L$ does not depend
  on $m$.\<close>

lemma (in int1) Int_ZF_2_1_L28: assumes A1: "s\<in>\<S>"
  shows "\<exists>M\<in>\<int>. \<forall>m\<in>\<int>. s`(m) \<lsq> s`(m\<rs>\<one>) \<ra> M"
proof -
  from A1 have
    "\<exists>L\<in>\<int>. \<forall>m\<in>\<int>.\<forall>n\<in>\<int>.abs(\<gamma>(s,m,n)) \<lsq> L"
    using Int_ZF_2_1_L27 by simp
  then obtain L where T: "L\<in>\<int>" and "\<forall>m\<in>\<int>.\<forall>n\<in>\<int>.abs(\<gamma>(s,m,n)) \<lsq> L"
    using Int_ZF_2_1_L27 by auto
  then have I: "\<forall>m\<in>\<int>.abs(\<gamma>(s,m,\<one>)) \<lsq> L"
    using int_zero_one_are_int by simp
  let ?M = "s`(\<one>) \<ra> L"
  from A1 T have "?M \<in> \<int>"
    using int_zero_one_are_int Int_ZF_2_1_L2B Int_ZF_1_1_L5
    by simp
  moreover
  { fix m assume A2: "m\<in>\<int>"
    with A1 have 
      T1: "s:\<int>\<rightarrow>\<int>"  "m\<in>\<int>"  "\<one>\<in>\<int>" and
      T2: "\<gamma>(s,m,\<one>) \<in> \<int>"  "s`(\<one>) \<in> \<int>"
      using int_zero_one_are_int AlmostHoms_def 
	Int_ZF_2_1_L25 by auto
    from A2 T1 have T3: "s`(m\<rs>\<one>) \<in> \<int>"
      using Int_ZF_1_1_L5 apply_funtype by simp
    from I A2 T2 have 
      "(\<rm>\<gamma>(s,m,\<one>)) \<lsq> abs(\<gamma>(s,m,\<one>))"
      "abs(\<gamma>(s,m,\<one>)) \<lsq> L"
      using Int_ZF_2_L19C by auto
    then have "(\<rm>\<gamma>(s,m,\<one>)) \<lsq> L"
      by (rule Int_order_transitive)
    with T2 T3 have 
      "s`(m\<rs>\<one>) \<ra> (s`(\<one>) \<rs> \<gamma>(s,m,\<one>)) \<lsq> s`(m\<rs>\<one>) \<ra> ?M"
      using int_ord_transl_inv by simp
    moreover from T1 have
      "s`(m\<rs>\<one>) \<ra> (s`(\<one>) \<rs> \<gamma>(s,m,\<one>)) = s`(m)"
      by (rule Int_ZF_2_1_L26)
    ultimately have "s`(m) \<lsq> s`(m\<rs>\<one>) \<ra> ?M"  by simp  }
  ultimately show "\<exists>M\<in>\<int>. \<forall>m\<in>\<int>. s`(m) \<lsq> s`(m\<rs>\<one>) \<ra> M"
    by auto
qed

text\<open>If $s$ is a slope, then the difference between 
  $s(m-n-k)$ and $s(m)-s(n)-s(k)$ is uniformly bounded.\<close>

lemma (in int1) Int_ZF_2_1_L29: assumes A1: "s\<in>\<S>"
  shows 
  "\<exists>M\<in>\<int>. \<forall>m\<in>\<int>.\<forall>n\<in>\<int>.\<forall>k\<in>\<int>. abs(s`(m\<rs>n\<rs>k) \<rs> (s`(m)\<rs>s`(n)\<rs>s`(k))) \<lsq>M"
proof -
  from A1 have "\<exists>L\<in>\<int>. \<forall>m\<in>\<int>.\<forall>n\<in>\<int>. abs(\<gamma>(s,m,n)) \<lsq> L"
    using Int_ZF_2_1_L27 by simp
  then obtain L where I: "L\<in>\<int>" and 
    II: "\<forall>m\<in>\<int>.\<forall>n\<in>\<int>. abs(\<gamma>(s,m,n)) \<lsq> L"
    by auto
  from I have "L\<ra>L \<in> \<int>"
    using Int_ZF_1_1_L5 by simp
  moreover
  { fix m n k assume A2: "m\<in>\<int>"  "n\<in>\<int>"  "k\<in>\<int>"
    with A1 have T: 
      "m\<rs>n \<in> \<int>"  "\<gamma>(s,m\<rs>n,k) \<in> \<int>"  "\<gamma>(s,m,n) \<in> \<int>"
      using Int_ZF_1_1_L5 AlmostHoms_def Int_ZF_2_1_L25 
      by auto
    then have 
      I: "abs(\<gamma>(s,m\<rs>n,k) \<ra> \<gamma>(s,m,n)) \<lsq> abs(\<gamma>(s,m\<rs>n,k)) \<ra> abs(\<gamma>(s,m,n))"
      using Int_triangle_ineq by simp
    from II A2 T have 
      "abs(\<gamma>(s,m\<rs>n,k)) \<lsq> L"
      "abs(\<gamma>(s,m,n)) \<lsq> L"
      by auto
    then have "abs(\<gamma>(s,m\<rs>n,k)) \<ra> abs(\<gamma>(s,m,n)) \<lsq> L\<ra>L"
      using int_ineq_add_sides by simp
    with I have "abs(\<gamma>(s,m\<rs>n,k) \<ra> \<gamma>(s,m,n)) \<lsq> L\<ra>L"
      by (rule Int_order_transitive)
    moreover from A1 A2 have 
      "s`(m\<rs>n\<rs>k) \<rs> (s`(m)\<rs> s`(n) \<rs> s`(k)) = \<gamma>(s,m\<rs>n,k) \<ra> \<gamma>(s,m,n)"
      using AlmostHoms_def Int_ZF_2_1_L26A by simp
    ultimately have 
      "abs(s`(m\<rs>n\<rs>k) \<rs> (s`(m)\<rs> s`(n) \<rs> s`(k))) \<lsq> L\<ra>L"
      by simp }
  ultimately show ?thesis by auto
qed

text\<open>If $s$ is a slope, then we can find integers $M,K$ such that
  $s(m-n-k) \leq s(m)-s(n)-s(k) + M$ and $s(m)-s(n)-s(k) + K \leq s(m-n-k)$, 
  for all integer $m,n,k$.\<close>

lemma (in int1) Int_ZF_2_1_L30: assumes A1: "s\<in>\<S>"
  shows 
  "\<exists>M\<in>\<int>. \<forall>m\<in>\<int>.\<forall>n\<in>\<int>.\<forall>k\<in>\<int>. s`(m\<rs>n\<rs>k) \<lsq> s`(m)\<rs>s`(n)\<rs>s`(k)\<ra>M"
  "\<exists>K\<in>\<int>. \<forall>m\<in>\<int>.\<forall>n\<in>\<int>.\<forall>k\<in>\<int>. s`(m)\<rs>s`(n)\<rs>s`(k)\<ra>K \<lsq> s`(m\<rs>n\<rs>k)"
proof -
  from A1 have
    "\<exists>M\<in>\<int>. \<forall>m\<in>\<int>.\<forall>n\<in>\<int>.\<forall>k\<in>\<int>. abs(s`(m\<rs>n\<rs>k) \<rs> (s`(m)\<rs>s`(n)\<rs>s`(k))) \<lsq>M"
    using Int_ZF_2_1_L29 by simp
  then obtain M where I: "M\<in>\<int>" and II:
    "\<forall>m\<in>\<int>.\<forall>n\<in>\<int>.\<forall>k\<in>\<int>. abs(s`(m\<rs>n\<rs>k) \<rs> (s`(m)\<rs>s`(n)\<rs>s`(k))) \<lsq>M"
    by auto
  from I have III: "(\<rm>M) \<in> \<int>" using Int_ZF_1_1_L4 by simp
  { fix m n k assume A2: "m\<in>\<int>"  "n\<in>\<int>"  "k\<in>\<int>"
    with A1 have "s`(m\<rs>n\<rs>k) \<in> \<int>"  and "s`(m)\<rs>s`(n)\<rs>s`(k) \<in> \<int>"
      using Int_ZF_1_1_L5 Int_ZF_2_1_L2B by auto
    moreover from II A2 have
      "abs(s`(m\<rs>n\<rs>k) \<rs> (s`(m)\<rs>s`(n)\<rs>s`(k))) \<lsq>M"
      by simp
    ultimately have 
      "s`(m\<rs>n\<rs>k) \<lsq> s`(m)\<rs>s`(n)\<rs>s`(k)\<ra>M \<and> 
      s`(m)\<rs>s`(n)\<rs>s`(k) \<rs> M \<lsq> s`(m\<rs>n\<rs>k)"
      using Int_triangle_ineq2 by simp
  } then have 
      "\<forall>m\<in>\<int>.\<forall>n\<in>\<int>.\<forall>k\<in>\<int>. s`(m\<rs>n\<rs>k) \<lsq> s`(m)\<rs>s`(n)\<rs>s`(k)\<ra>M"
      "\<forall>m\<in>\<int>.\<forall>n\<in>\<int>.\<forall>k\<in>\<int>. s`(m)\<rs>s`(n)\<rs>s`(k) \<rs> M \<lsq> s`(m\<rs>n\<rs>k)"
    by auto
  with I III show  
    "\<exists>M\<in>\<int>. \<forall>m\<in>\<int>.\<forall>n\<in>\<int>.\<forall>k\<in>\<int>. s`(m\<rs>n\<rs>k) \<lsq> s`(m)\<rs>s`(n)\<rs>s`(k)\<ra>M"
    "\<exists>K\<in>\<int>. \<forall>m\<in>\<int>.\<forall>n\<in>\<int>.\<forall>k\<in>\<int>. s`(m)\<rs>s`(n)\<rs>s`(k)\<ra>K \<lsq> s`(m\<rs>n\<rs>k)"
    by auto
qed

text\<open>By definition functions $f,g$ are almost equal if $f-g$* is bounded. 
  In the next lemma we show it is sufficient to check the boundedness on positive
  integers.\<close>

lemma (in int1) Int_ZF_2_1_L31: assumes A1: "s\<in>\<S>"  "r\<in>\<S>" 
  and A2: "\<forall>m\<in>\<int>\<^sub>+. abs(s`(m)\<rs>r`(m)) \<lsq> L"
  shows "s \<sim> r"
proof -
  let ?a = "abs(s`(\<zero>) \<rs> r`(\<zero>))"
  let ?c = "\<two>\<cdot>max\<delta>(s) \<ra> \<two>\<cdot>max\<delta>(r) \<ra> L"
  let ?M = "Maximum(IntegerOrder,{?a,L,?c})"
  from A2 have "abs(s`(\<one>)\<rs>r`(\<one>)) \<lsq> L"
    using int_one_two_are_pos by simp
  then have T: "L\<in>\<int>" using Int_ZF_2_L1A by simp
  moreover from A1 have "?a \<in> \<int>"
    using int_zero_one_are_int Int_ZF_2_1_L2B 
      Int_ZF_1_1_L5 Int_ZF_2_L14 by simp
  moreover from A1 T have "?c \<in> \<int>"
    using Int_ZF_2_1_L8 int_two_three_are_int Int_ZF_1_1_L5
    by simp
  ultimately have 
    I: "?a \<lsq> ?M" and
    II: "L \<lsq> ?M" and 
    III: "?c \<lsq> ?M"
    using Int_ZF_1_4_L1A by auto
  
  { fix m assume A5: "m\<in>\<int>"
    with A1 have T: 
      "s`(m) \<in> \<int>"  "r`(m) \<in> \<int>"  "s`(m) \<rs> r`(m) \<in> \<int>"
      "s`(\<rm>m) \<in> \<int>"  "r`(\<rm>m) \<in> \<int>"
      using Int_ZF_2_1_L2B Int_ZF_1_1_L4 Int_ZF_1_1_L5 
      by auto
    from A5 have "m=\<zero> \<or> m\<in>\<int>\<^sub>+ \<or> (\<rm>m) \<in> \<int>\<^sub>+"
      using int_decomp_cases by simp
    moreover
    { assume "m=\<zero>"
      with I have "abs(s`(m) \<rs> r`(m)) \<lsq> ?M"
	by simp }
    moreover
    { assume "m\<in>\<int>\<^sub>+"
      with A2 II have 
	"abs(s`(m)\<rs>r`(m)) \<lsq> L" and "L\<lsq>?M"
	by auto
      then have "abs(s`(m)\<rs>r`(m)) \<lsq> ?M"
	by (rule Int_order_transitive) }
    moreover
    { assume A6: "(\<rm>m) \<in> \<int>\<^sub>+"
      from T have "abs(s`(m)\<rs>r`(m)) \<lsq> 
	abs(s`(m)\<ra>s`(\<rm>m)) \<ra> abs(r`(m)\<ra>r`(\<rm>m)) \<ra> abs(s`(\<rm>m)\<rs>r`(\<rm>m))"
	using Int_ZF_1_3_L22A by simp
      moreover 
      from A1 A2 III A5 A6 have
	"abs(s`(m)\<ra>s`(\<rm>m)) \<ra> abs(r`(m)\<ra>r`(\<rm>m)) \<ra> abs(s`(\<rm>m)\<rs>r`(\<rm>m)) \<lsq> ?c"
	"?c \<lsq> ?M"
	using Int_ZF_2_1_L14 int_ineq_add_sides by auto
      then have 
	"abs(s`(m)\<ra>s`(\<rm>m)) \<ra> abs(r`(m)\<ra>r`(\<rm>m)) \<ra> abs(s`(\<rm>m)\<rs>r`(\<rm>m)) \<lsq> ?M"
	by (rule Int_order_transitive)
      ultimately have  "abs(s`(m)\<rs>r`(m)) \<lsq> ?M"
	by (rule Int_order_transitive) }
    ultimately have "abs(s`(m) \<rs> r`(m)) \<lsq> ?M"
      by auto
  } then have "\<forall>m\<in>\<int>. abs(s`(m)\<rs>r`(m)) \<lsq> ?M"
    by simp
  with A1 show "s \<sim> r" by (rule Int_ZF_2_1_L9)
qed

text\<open>A sufficient condition for an odd slope to be almost equal to identity:
  If for all positive integers the value of the slope at $m$ is between $m$ and
  $m$ plus some constant independent of $m$, then the slope is almost identity.\<close>

lemma (in int1) Int_ZF_2_1_L32: assumes A1: "s\<in>\<S>"  "M\<in>\<int>"
  and A2: "\<forall>m\<in>\<int>\<^sub>+. m \<lsq> s`(m) \<and> s`(m) \<lsq> m\<ra>M"
  shows "s \<sim> id(\<int>)"
proof -
  let ?r = "id(\<int>)"
  from A1 have "s\<in>\<S>"  "?r \<in> \<S>"
    using Int_ZF_2_1_L17 by auto
  moreover from A1 A2 have "\<forall>m\<in>\<int>\<^sub>+. abs(s`(m)\<rs>?r`(m)) \<lsq> M"
    using Int_ZF_1_3_L23 PositiveSet_def id_conv by simp
  ultimately show "s \<sim> id(\<int>)" by (rule Int_ZF_2_1_L31)
qed

text\<open>A lemma about adding a constant to slopes. This is actually proven in
  \<open>Group_ZF_3_5_L1\<close>, in \<open>Group_ZF_3.thy\<close> here we just refer to 
  that lemma to show it in notation used for integers. Unfortunately we have
  to use raw set notation in the proof.\<close>

lemma (in int1) Int_ZF_2_1_L33:
  assumes A1: "s\<in>\<S>" and A2: "c\<in>\<int>" and 
  A3: "r = {\<langle>m,s`(m)\<ra>c\<rangle>. m\<in>\<int>}"
  shows
  "\<forall>m\<in>\<int>. r`(m) = s`(m)\<ra>c"
  "r\<in>\<S>"
  "s \<sim> r"
proof -
  let ?G = "\<int>"
  let ?f = "IntegerAddition"
  let ?AH = "AlmostHoms(?G, ?f)"
  from assms have I:
    "group1(?G, ?f)"
    "s \<in> AlmostHoms(?G, ?f)"
    "c \<in> ?G"
    "r = {\<langle>x, ?f`\<langle>s`(x), c\<rangle>\<rangle>. x \<in> ?G}"
    using Int_ZF_2_1_L1 by auto
  then have "\<forall>x\<in>?G. r`(x) = ?f`\<langle>s`(x),c\<rangle>"
    by (rule group1.Group_ZF_3_5_L1)
  moreover from I have "r \<in> AlmostHoms(?G, ?f)"
    by (rule group1.Group_ZF_3_5_L1)
  moreover from I have 
    "\<langle>s, r\<rangle> \<in> QuotientGroupRel(AlmostHoms(?G, ?f), AlHomOp1(?G, ?f), FinRangeFunctions(?G, ?G))"
    by (rule group1.Group_ZF_3_5_L1)
  ultimately show 
    "\<forall>m\<in>\<int>. r`(m) = s`(m)\<ra>c"
    "r\<in>\<S>"
    "s \<sim> r"
    by auto
qed  

subsection\<open>Composing slopes\<close>

text\<open>Composition of slopes is not commutative. However, as we show in this 
  section if $f$ and $g$ are slopes then the range of $f\circ g - g\circ f$ 
  is bounded. This allows to show that the multiplication of real 
  numbers is commutative.\<close>

text\<open>Two useful estimates.\<close>

lemma (in int1) Int_ZF_2_2_L1: 
  assumes A1: "f:\<int>\<rightarrow>\<int>" and A2: "p\<in>\<int>"  "q\<in>\<int>"
  shows 
  "abs(f`((p\<ra>\<one>)\<cdot>q)\<rs>(p\<ra>\<one>)\<cdot>f`(q)) \<lsq> abs(\<delta>(f,p\<cdot>q,q))\<ra>abs(f`(p\<cdot>q)\<rs>p\<cdot>f`(q))"
  "abs(f`((p\<rs>\<one>)\<cdot>q)\<rs>(p\<rs>\<one>)\<cdot>f`(q)) \<lsq> abs(\<delta>(f,(p\<rs>\<one>)\<cdot>q,q))\<ra>abs(f`(p\<cdot>q)\<rs>p\<cdot>f`(q))"
proof -
  let ?R = "\<int>"
  let ?A = "IntegerAddition"
  let ?M = "IntegerMultiplication"
  let ?I = "GroupInv(?R, ?A)"
  let ?a = "f`((p\<ra>\<one>)\<cdot>q)"
  let ?b = "p"
  let ?c = "f`(q)"
  let ?d = "f`(p\<cdot>q)"
  from A1 A2 have T1:
    "ring0(?R, ?A, ?M)"  "?a \<in> ?R"  "?b \<in> ?R"  "?c \<in> ?R"  "?d \<in> ?R"
    using  Int_ZF_1_1_L2 int_zero_one_are_int Int_ZF_1_1_L5 apply_funtype 
    by auto
  then have 
    "?A`\<langle>?a,?I`(?M`\<langle>?A`\<langle>?b, TheNeutralElement(?R, ?M)\<rangle>,?c\<rangle>)\<rangle> =
    ?A`\<langle>?A`\<langle>?A`\<langle>?a,?I`(?d)\<rangle>,?I`(?c)\<rangle>,?A`\<langle>?d, ?I`(?M`\<langle>?b, ?c\<rangle>)\<rangle>\<rangle>"
    by (rule ring0.Ring_ZF_2_L2)
  with A2 have 
    "f`((p\<ra>\<one>)\<cdot>q)\<rs>(p\<ra>\<one>)\<cdot>f`(q) = \<delta>(f,p\<cdot>q,q)\<ra>(f`(p\<cdot>q)\<rs>p\<cdot>f`(q))"
    using int_zero_one_are_int Int_ZF_1_1_L1 Int_ZF_1_1_L4 by simp
  moreover from A1 A2 T1 have "\<delta>(f,p\<cdot>q,q) \<in> \<int>" "f`(p\<cdot>q)\<rs>p\<cdot>f`(q) \<in> \<int>"
    using Int_ZF_1_1_L5 apply_funtype by auto
  ultimately show 
    "abs(f`((p\<ra>\<one>)\<cdot>q)\<rs>(p\<ra>\<one>)\<cdot>f`(q)) \<lsq> abs(\<delta>(f,p\<cdot>q,q))\<ra>abs(f`(p\<cdot>q)\<rs>p\<cdot>f`(q))"
    using Int_triangle_ineq by simp
  from A1 A2 have T1: 
    "f`((p\<rs>\<one>)\<cdot>q) \<in> \<int>"   "p\<in>\<int>"  "f`(q) \<in> \<int>"   "f`(p\<cdot>q) \<in> \<int>" 
    using int_zero_one_are_int Int_ZF_1_1_L5 apply_funtype by auto
  then have
    "f`((p\<rs>\<one>)\<cdot>q)\<rs>(p\<rs>\<one>)\<cdot>f`(q) = (f`(p\<cdot>q)\<rs>p\<cdot>f`(q))\<rs>(f`(p\<cdot>q)\<rs>f`((p\<rs>\<one>)\<cdot>q)\<rs>f`(q))"
    by (rule Int_ZF_1_2_L6)
  with A2 have "f`((p\<rs>\<one>)\<cdot>q)\<rs>(p\<rs>\<one>)\<cdot>f`(q) = (f`(p\<cdot>q)\<rs>p\<cdot>f`(q))\<rs>\<delta>(f,(p\<rs>\<one>)\<cdot>q,q)"
    using Int_ZF_1_2_L7 by simp
  moreover from A1 A2 have 
    "f`(p\<cdot>q)\<rs>p\<cdot>f`(q) \<in> \<int>"   "\<delta>(f,(p\<rs>\<one>)\<cdot>q,q) \<in> \<int>" 
    using Int_ZF_1_1_L5 int_zero_one_are_int apply_funtype by auto
  ultimately show 
    "abs(f`((p\<rs>\<one>)\<cdot>q)\<rs>(p\<rs>\<one>)\<cdot>f`(q)) \<lsq> abs(\<delta>(f,(p\<rs>\<one>)\<cdot>q,q))\<ra>abs(f`(p\<cdot>q)\<rs>p\<cdot>f`(q))"
    using Int_triangle_ineq1 by simp
qed
  
text\<open>If $f$ is a slope, then 
  $|f(p\cdot q)-p\cdot f(q)|\leq (|p|+1)\cdot$\<open>max\<delta>(f)\<close>. 
  The proof is by induction on $p$ and the next lemma is the induction step for the case when $0\leq p$.\<close>

lemma (in int1) Int_ZF_2_2_L2: 
  assumes A1: "f\<in>\<S>" and A2: "\<zero>\<lsq>p"  "q\<in>\<int>"
  and A3: "abs(f`(p\<cdot>q)\<rs>p\<cdot>f`(q)) \<lsq> (abs(p)\<ra>\<one>)\<cdot>max\<delta>(f)"
  shows 
  "abs(f`((p\<ra>\<one>)\<cdot>q)\<rs>(p\<ra>\<one>)\<cdot>f`(q)) \<lsq> (abs(p\<ra>\<one>)\<ra> \<one>)\<cdot>max\<delta>(f)"
proof -
  from A2 have "q\<in>\<int>"  "p\<cdot>q \<in> \<int>" 
    using Int_ZF_2_L1A Int_ZF_1_1_L5 by auto
  with A1 have I: "abs(\<delta>(f,p\<cdot>q,q)) \<lsq> max\<delta>(f)" by (rule Int_ZF_2_1_L7)
  moreover note A3
  moreover from A1 A2 have
    "abs(f`((p\<ra>\<one>)\<cdot>q)\<rs>(p\<ra>\<one>)\<cdot>f`(q)) \<lsq> abs(\<delta>(f,p\<cdot>q,q))\<ra>abs(f`(p\<cdot>q)\<rs>p\<cdot>f`(q))"
    using AlmostHoms_def Int_ZF_2_L1A Int_ZF_2_2_L1 by simp
  ultimately have 
    "abs(f`((p\<ra>\<one>)\<cdot>q)\<rs>(p\<ra>\<one>)\<cdot>f`(q)) \<lsq> max\<delta>(f)\<ra>(abs(p)\<ra>\<one>)\<cdot>max\<delta>(f)"
    by (rule Int_ZF_2_L15)
  moreover from I A2 have 
    "max\<delta>(f)\<ra>(abs(p)\<ra>\<one>)\<cdot>max\<delta>(f) = (abs(p\<ra>\<one>)\<ra> \<one>)\<cdot>max\<delta>(f)"
    using Int_ZF_2_L1A Int_ZF_1_2_L2 by simp
  ultimately show
    "abs(f`((p\<ra>\<one>)\<cdot>q)\<rs>(p\<ra>\<one>)\<cdot>f`(q)) \<lsq> (abs(p\<ra>\<one>)\<ra> \<one>)\<cdot>max\<delta>(f)"
    by simp
qed

text\<open>If $f$ is a slope, then 
  $|f(p\cdot q)-p\cdot f(q)|\leq (|p|+1)\cdot$\<open>max\<delta>\<close>. 
  The proof is by induction on $p$ and the next lemma is the induction step for the case when $p\leq 0$.\<close>

lemma (in int1) Int_ZF_2_2_L3: 
  assumes A1: "f\<in>\<S>" and A2: "p\<lsq>\<zero>"  "q\<in>\<int>"
  and A3: "abs(f`(p\<cdot>q)\<rs>p\<cdot>f`(q)) \<lsq> (abs(p)\<ra>\<one>)\<cdot>max\<delta>(f)"
  shows  "abs(f`((p\<rs>\<one>)\<cdot>q)\<rs>(p\<rs>\<one>)\<cdot>f`(q)) \<lsq> (abs(p\<rs>\<one>)\<ra> \<one>)\<cdot>max\<delta>(f)"
proof -
  from A2 have "q\<in>\<int>"  "(p\<rs>\<one>)\<cdot>q \<in> \<int>" 
    using Int_ZF_2_L1A int_zero_one_are_int Int_ZF_1_1_L5 by auto
  with A1 have I: "abs(\<delta>(f,(p\<rs>\<one>)\<cdot>q,q)) \<lsq> max\<delta>(f)" by (rule Int_ZF_2_1_L7)
  moreover note A3
  moreover from A1 A2 have 
    "abs(f`((p\<rs>\<one>)\<cdot>q)\<rs>(p\<rs>\<one>)\<cdot>f`(q)) \<lsq> abs(\<delta>(f,(p\<rs>\<one>)\<cdot>q,q))\<ra>abs(f`(p\<cdot>q)\<rs>p\<cdot>f`(q))"
    using AlmostHoms_def Int_ZF_2_L1A Int_ZF_2_2_L1 by simp
  ultimately have 
    "abs(f`((p\<rs>\<one>)\<cdot>q)\<rs>(p\<rs>\<one>)\<cdot>f`(q)) \<lsq> max\<delta>(f)\<ra>(abs(p)\<ra>\<one>)\<cdot>max\<delta>(f)"
    by (rule Int_ZF_2_L15)
  with I A2 show ?thesis using Int_ZF_2_L1A Int_ZF_1_2_L5 by simp
qed

text\<open>If $f$ is a slope, then 
  $|f(p\cdot q)-p\cdot f(q)|\leq (|p|+1)\cdot$\<open>max\<delta>\<close>$(f)$.
  Proof by cases on $0 \leq p$.\<close> 

lemma (in int1) Int_ZF_2_2_L4: 
  assumes A1: "f\<in>\<S>" and A2: "p\<in>\<int>" "q\<in>\<int>"
  shows "abs(f`(p\<cdot>q)\<rs>p\<cdot>f`(q)) \<lsq> (abs(p)\<ra>\<one>)\<cdot>max\<delta>(f)"
proof -
  { assume "\<zero>\<lsq>p"
    moreover from A1 A2 have "abs(f`(\<zero>\<cdot>q)\<rs>\<zero>\<cdot>f`(q)) \<lsq> (abs(\<zero>)\<ra>\<one>)\<cdot>max\<delta>(f)"
      using int_zero_one_are_int Int_ZF_2_1_L2B Int_ZF_1_1_L4 
	Int_ZF_2_1_L8 Int_ZF_2_L18 by simp
    moreover from A1 A2 have 
      "\<forall>p. \<zero>\<lsq>p \<and> abs(f`(p\<cdot>q)\<rs>p\<cdot>f`(q)) \<lsq> (abs(p)\<ra>\<one>)\<cdot>max\<delta>(f) \<longrightarrow>
      abs(f`((p\<ra>\<one>)\<cdot>q)\<rs>(p\<ra>\<one>)\<cdot>f`(q)) \<lsq> (abs(p\<ra>\<one>)\<ra> \<one>)\<cdot>max\<delta>(f)"
      using Int_ZF_2_2_L2 by simp
    ultimately have "abs(f`(p\<cdot>q)\<rs>p\<cdot>f`(q)) \<lsq> (abs(p)\<ra>\<one>)\<cdot>max\<delta>(f)" 
      by (rule Induction_on_int) }
  moreover
  { assume "\<not>(\<zero>\<lsq>p)"
    with A2 have "p\<lsq>\<zero>" using Int_ZF_2_L19A by simp
    moreover from A1 A2 have "abs(f`(\<zero>\<cdot>q)\<rs>\<zero>\<cdot>f`(q)) \<lsq> (abs(\<zero>)\<ra>\<one>)\<cdot>max\<delta>(f)"
      using int_zero_one_are_int Int_ZF_2_1_L2B Int_ZF_1_1_L4
	Int_ZF_2_1_L8 Int_ZF_2_L18 by simp
    moreover from A1 A2 have 
      "\<forall>p. p\<lsq>\<zero> \<and> abs(f`(p\<cdot>q)\<rs>p\<cdot>f`(q)) \<lsq> (abs(p)\<ra>\<one>)\<cdot>max\<delta>(f) \<longrightarrow>
      abs(f`((p\<rs>\<one>)\<cdot>q)\<rs>(p\<rs>\<one>)\<cdot>f`(q)) \<lsq> (abs(p\<rs>\<one>)\<ra> \<one>)\<cdot>max\<delta>(f)"
      using Int_ZF_2_2_L3 by simp
    ultimately have "abs(f`(p\<cdot>q)\<rs>p\<cdot>f`(q)) \<lsq> (abs(p)\<ra>\<one>)\<cdot>max\<delta>(f)" 
      by (rule Back_induct_on_int) }
  ultimately show ?thesis by blast
qed

text\<open>The next elegant result is Lemma 7 in the Arthan's paper \cite{Arthan2004}.\<close>

lemma (in int1) Arthan_Lem_7: 
 assumes A1: "f\<in>\<S>" and A2: "p\<in>\<int>"  "q\<in>\<int>"
  shows "abs(q\<cdot>f`(p)\<rs>p\<cdot>f`(q)) \<lsq> (abs(p)\<ra>abs(q)\<ra>\<two>)\<cdot>max\<delta>(f)"
proof -
  from A1 A2 have T:
    "q\<cdot>f`(p)\<rs>f`(p\<cdot>q) \<in> \<int>" 
    "f`(p\<cdot>q)\<rs>p\<cdot>f`(q) \<in> \<int>"
    "f`(q\<cdot>p) \<in> \<int>"  "f`(p\<cdot>q) \<in> \<int>"
    "q\<cdot>f`(p) \<in> \<int>"  "p\<cdot>f`(q) \<in> \<int>" 
    "max\<delta>(f) \<in> \<int>"
    "abs(q) \<in> \<int>"  "abs(p) \<in> \<int>"
    using Int_ZF_1_1_L5 Int_ZF_2_1_L2B Int_ZF_2_1_L7 Int_ZF_2_L14 by auto
  moreover have "abs(q\<cdot>f`(p)\<rs>f`(p\<cdot>q)) \<lsq> (abs(q)\<ra>\<one>)\<cdot>max\<delta>(f)"
  proof -
    from A1 A2 have "abs(f`(q\<cdot>p)\<rs>q\<cdot>f`(p)) \<lsq> (abs(q)\<ra>\<one>)\<cdot>max\<delta>(f)"
      using Int_ZF_2_2_L4 by simp
    with T A2 show ?thesis
      using Int_ZF_2_L20 Int_ZF_1_1_L5 by simp
  qed
  moreover from A1 A2 have "abs(f`(p\<cdot>q)\<rs>p\<cdot>f`(q)) \<lsq> (abs(p)\<ra>\<one>)\<cdot>max\<delta>(f)"
    using Int_ZF_2_2_L4 by simp
  ultimately have 
    "abs(q\<cdot>f`(p)\<rs>f`(p\<cdot>q)\<ra>(f`(p\<cdot>q)\<rs>p\<cdot>f`(q))) \<lsq> (abs(q)\<ra>\<one>)\<cdot>max\<delta>(f)\<ra>(abs(p)\<ra>\<one>)\<cdot>max\<delta>(f)"
    using Int_ZF_2_L21 by simp
  with T show ?thesis using Int_ZF_1_2_L9 int_zero_one_are_int Int_ZF_1_2_L10
    by simp
qed

text\<open>This is Lemma 8 in the Arthan's paper.\<close>

lemma (in int1) Arthan_Lem_8: assumes A1: "f\<in>\<S>"
  shows "\<exists>A B. A\<in>\<int> \<and> B\<in>\<int> \<and> (\<forall>p\<in>\<int>. abs(f`(p)) \<lsq> A\<cdot>abs(p)\<ra>B)"
proof -
  let ?A = "max\<delta>(f) \<ra> abs(f`(\<one>))"
  let ?B = "\<three>\<cdot>max\<delta>(f)"
  from A1 have "?A\<in>\<int>" "?B\<in>\<int>"
    using int_zero_one_are_int Int_ZF_1_1_L5 Int_ZF_2_1_L2B 
      Int_ZF_2_1_L7 Int_ZF_2_L14 by auto
  moreover have "\<forall>p\<in>\<int>. abs(f`(p)) \<lsq> ?A\<cdot>abs(p)\<ra>?B"
  proof
    fix p assume A2: "p\<in>\<int>" 
    with A1 have T: 
      "f`(p) \<in> \<int>"  "abs(p) \<in> \<int>"  "f`(\<one>) \<in> \<int>" 
      "p\<cdot>f`(\<one>) \<in> \<int>"  "\<three>\<in>\<int>"  "max\<delta>(f) \<in> \<int>"
      using Int_ZF_2_1_L2B Int_ZF_2_L14 int_zero_one_are_int 
	Int_ZF_1_1_L5 Int_ZF_2_1_L7 by auto
    from A1 A2 have 
      "abs(\<one>\<cdot>f`(p)\<rs>p\<cdot>f`(\<one>)) \<lsq> (abs(p)\<ra>abs(\<one>)\<ra>\<two>)\<cdot>max\<delta>(f)"
      using int_zero_one_are_int Arthan_Lem_7 by simp
    with T have "abs(f`(p)) \<lsq> abs(p\<cdot>f`(\<one>))\<ra>(abs(p)\<ra>\<three>)\<cdot>max\<delta>(f)"
      using Int_ZF_2_L16A Int_ZF_1_1_L4 Int_ZF_1_2_L11 
	Int_triangle_ineq2 by simp
    with A2 T show "abs(f`(p)) \<lsq> ?A\<cdot>abs(p)\<ra>?B"
      using Int_ZF_1_3_L14 by simp
  qed
  ultimately show ?thesis by auto
qed

text\<open>If $f$ and $g$ are slopes, then $f\circ g$ is equivalent 
  (almost equal) to $g\circ f$. This is Theorem 9 in Arthan's paper \cite{Arthan2004}.\<close>

theorem (in int1) Arthan_Th_9: assumes A1: "f\<in>\<S>"  "g\<in>\<S>"
  shows "f\<circ>g \<sim> g\<circ>f"
proof -
   from A1 have 
      "\<exists>A B. A\<in>\<int> \<and> B\<in>\<int> \<and> (\<forall>p\<in>\<int>. abs(f`(p)) \<lsq> A\<cdot>abs(p)\<ra>B)"
      "\<exists>C D. C\<in>\<int> \<and> D\<in>\<int> \<and> (\<forall>p\<in>\<int>. abs(g`(p)) \<lsq> C\<cdot>abs(p)\<ra>D)"
      using Arthan_Lem_8 by auto
    then obtain A B C D where D1: "A\<in>\<int>" "B\<in>\<int>" "C\<in>\<int>" "D\<in>\<int>" and D2: 
      "\<forall>p\<in>\<int>. abs(f`(p)) \<lsq> A\<cdot>abs(p)\<ra>B"
      "\<forall>p\<in>\<int>. abs(g`(p)) \<lsq> C\<cdot>abs(p)\<ra>D"
      by auto
    let ?E = "max\<delta>(g)\<cdot>(A\<ra>\<one>) \<ra> max\<delta>(f)\<cdot>(C\<ra>\<one>)"
    let ?F = "(B\<cdot>max\<delta>(g) \<ra> \<two>\<cdot>max\<delta>(g)) \<ra> (D\<cdot>max\<delta>(f) \<ra> \<two>\<cdot>max\<delta>(f))"
  { fix p assume A2: "p\<in>\<int>"
    with A1 have T1:
      "g`(p) \<in> \<int>"  "f`(p) \<in> \<int>"  "abs(p) \<in> \<int>"  "\<two> \<in> \<int>"
      "f`(g`(p)) \<in> \<int>"  "g`(f`(p)) \<in> \<int>"  "f`(g`(p)) \<rs> g`(f`(p)) \<in> \<int>"
      "p\<cdot>f`(g`(p)) \<in> \<int>"  "p\<cdot>g`(f`(p)) \<in> \<int>"
      "abs(f`(g`(p))\<rs>g`(f`(p))) \<in> \<int>"
      using Int_ZF_2_1_L2B Int_ZF_2_1_L10 Int_ZF_1_1_L5 Int_ZF_2_L14 int_two_three_are_int
      by auto
    with A1 A2 have
      "abs((f`(g`(p))\<rs>g`(f`(p)))\<cdot>p) \<lsq> 
      (abs(p)\<ra>abs(f`(p))\<ra>\<two>)\<cdot>max\<delta>(g) \<ra> (abs(p)\<ra>abs(g`(p))\<ra>\<two>)\<cdot>max\<delta>(f)"
      using Arthan_Lem_7 Int_ZF_1_2_L10A Int_ZF_1_2_L12 by simp
    moreover have 
      "(abs(p)\<ra>abs(f`(p))\<ra>\<two>)\<cdot>max\<delta>(g) \<ra> (abs(p)\<ra>abs(g`(p))\<ra>\<two>)\<cdot>max\<delta>(f) \<lsq>
      ((max\<delta>(g)\<cdot>(A\<ra>\<one>) \<ra> max\<delta>(f)\<cdot>(C\<ra>\<one>)))\<cdot>abs(p) \<ra>
      ((B\<cdot>max\<delta>(g) \<ra> \<two>\<cdot>max\<delta>(g)) \<ra> (D\<cdot>max\<delta>(f) \<ra> \<two>\<cdot>max\<delta>(f)))"
    proof -
      from D2 A2 T1 have 
	"abs(p)\<ra>abs(f`(p))\<ra>\<two> \<lsq> abs(p)\<ra>(A\<cdot>abs(p)\<ra>B)\<ra>\<two>"
	"abs(p)\<ra>abs(g`(p))\<ra>\<two> \<lsq> abs(p)\<ra>(C\<cdot>abs(p)\<ra>D)\<ra>\<two>"
	using Int_ZF_2_L15C by auto
      with A1 have 
	"(abs(p)\<ra>abs(f`(p))\<ra>\<two>)\<cdot>max\<delta>(g) \<lsq> (abs(p)\<ra>(A\<cdot>abs(p)\<ra>B)\<ra>\<two>)\<cdot>max\<delta>(g)"
	"(abs(p)\<ra>abs(g`(p))\<ra>\<two>)\<cdot>max\<delta>(f) \<lsq> (abs(p)\<ra>(C\<cdot>abs(p)\<ra>D)\<ra>\<two>)\<cdot>max\<delta>(f)"
	using Int_ZF_2_1_L8 Int_ZF_1_3_L13 by auto
      moreover from A1 D1 T1 have 
	"(abs(p)\<ra>(A\<cdot>abs(p)\<ra>B)\<ra>\<two>)\<cdot>max\<delta>(g) = 
	max\<delta>(g)\<cdot>(A\<ra>\<one>)\<cdot>abs(p) \<ra> (B\<cdot>max\<delta>(g) \<ra> \<two>\<cdot>max\<delta>(g))"
	"(abs(p)\<ra>(C\<cdot>abs(p)\<ra>D)\<ra>\<two>)\<cdot>max\<delta>(f) = 
	max\<delta>(f)\<cdot>(C\<ra>\<one>)\<cdot>abs(p) \<ra> (D\<cdot>max\<delta>(f) \<ra> \<two>\<cdot>max\<delta>(f))"
	using Int_ZF_2_1_L8 Int_ZF_1_2_L13 by auto
      ultimately have 
	"(abs(p)\<ra>abs(f`(p))\<ra>\<two>)\<cdot>max\<delta>(g) \<ra> (abs(p)\<ra>abs(g`(p))\<ra>\<two>)\<cdot>max\<delta>(f) \<lsq>
	(max\<delta>(g)\<cdot>(A\<ra>\<one>)\<cdot>abs(p) \<ra> (B\<cdot>max\<delta>(g) \<ra> \<two>\<cdot>max\<delta>(g))) \<ra> 
	(max\<delta>(f)\<cdot>(C\<ra>\<one>)\<cdot>abs(p) \<ra> (D\<cdot>max\<delta>(f) \<ra> \<two>\<cdot>max\<delta>(f)))"
	using int_ineq_add_sides by simp
      moreover from A1 A2 D1 have "abs(p) \<in> \<int>"
	"max\<delta>(g)\<cdot>(A\<ra>\<one>) \<in> \<int>"  "B\<cdot>max\<delta>(g) \<ra> \<two>\<cdot>max\<delta>(g) \<in> \<int>"
	"max\<delta>(f)\<cdot>(C\<ra>\<one>) \<in> \<int>"  "D\<cdot>max\<delta>(f) \<ra> \<two>\<cdot>max\<delta>(f) \<in> \<int>" 
	using Int_ZF_2_L14 Int_ZF_2_1_L8 int_zero_one_are_int 
	  Int_ZF_1_1_L5 int_two_three_are_int by auto
      ultimately show ?thesis using Int_ZF_1_2_L14 by simp
    qed
    ultimately have
      "abs((f`(g`(p))\<rs>g`(f`(p)))\<cdot>p) \<lsq> ?E\<cdot>abs(p) \<ra> ?F"
      by (rule Int_order_transitive)
    with A2 T1 have
      "abs(f`(g`(p))\<rs>g`(f`(p)))\<cdot>abs(p) \<lsq> ?E\<cdot>abs(p) \<ra> ?F"
      "abs(f`(g`(p))\<rs>g`(f`(p))) \<in> \<int>"
      using Int_ZF_1_3_L5 by auto
  } then have 
      "\<forall>p\<in>\<int>. abs(f`(g`(p))\<rs>g`(f`(p))) \<in> \<int>"
      "\<forall>p\<in>\<int>. abs(f`(g`(p))\<rs>g`(f`(p)))\<cdot>abs(p) \<lsq> ?E\<cdot>abs(p) \<ra> ?F"
    by auto
  moreover from A1 D1 have "?E \<in> \<int>"  "?F \<in> \<int>"
    using int_zero_one_are_int int_two_three_are_int Int_ZF_2_1_L8 Int_ZF_1_1_L5
    by auto
  ultimately have
    "\<exists>L. \<forall>p\<in>\<int>. abs(f`(g`(p))\<rs>g`(f`(p))) \<lsq> L"
    by (rule Int_ZF_1_7_L1)
  with A1 obtain L where "\<forall>p\<in>\<int>. abs((f\<circ>g)`(p)\<rs>(g\<circ>f)`(p)) \<lsq> L"
    using Int_ZF_2_1_L10 by auto
  moreover from A1 have "f\<circ>g \<in> \<S>"  "g\<circ>f \<in> \<S>"
    using Int_ZF_2_1_L11 by auto
  ultimately show "f\<circ>g \<sim> g\<circ>f" using Int_ZF_2_1_L9 by auto
qed
 
end
