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

THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES,
INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT,
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open>Integers - introduction\<close>

theory Int_ZF_IML imports OrderedGroup_ZF_1 Finite_ZF_1 ZF.Int Nat_ZF_IML

begin

text\<open>This theory file is an interface between the old-style Isabelle 
  (ZF logic) material on integers and the IsarMathLib project. Here we
  redefine the meta-level operations on integers 
  (addition and multiplication) to convert them to ZF-functions and show
  that integers form a commutative group with respect to addition and 
  commutative monoid with respect to multiplication. Similarly, we redefine the
  order on integers as a relation, that is a subset of $Z\times Z$. 
  We show that a subset of intergers is bounded iff it is finite.
  As we are forced to use standard Isabelle notation with all these
  dollar signs, sharps etc. to denote "type coercions" (?) the notation
  is often ugly and difficult to read.\<close>

subsection\<open>Addition and multiplication as ZF-functions.\<close>

text\<open>In this section we provide definitions of addition and multiplication
  as subsets of $(Z\times Z)\times Z$. We 
  use the (higher order) relation defined in the standard 
  \<open>Int\<close> theory to define a subset of $Z\times Z$ that 
  constitutes the ZF order relation 
  corresponding to it. We define the set of positive integers 
  using the notion of 
  positive set from the \<open>OrderedGroup_ZF\<close> theory.\<close>

text\<open>Definition of addition of integers as a binary operation 
  on \<open>int\<close>.
  Recall that in standard Isabelle/ZF \<open>int\<close> is the set of integers 
  and the sum of integers is denoted by prependig $+$ with a dollar sign.\<close>

definition
  "IntegerAddition \<equiv> { \<langle> x,c\<rangle> \<in> (int\<times>int)\<times>int. fst(x) $+ snd(x) = c}"

text\<open>Definition of multiplication of integers as a binary operation 
  on \<open>int\<close>. In standard Isabelle/ZF product of integers is denoted by
  prepending the dollar sign to \<open>*\<close>.  
\<close>

definition
  "IntegerMultiplication \<equiv> 
    { \<langle> x,c\<rangle> \<in> (int\<times>int)\<times>int. fst(x) $* snd(x) = c}"

text\<open>Definition of natural order on integers as a relation on \<open>int\<close>.
  In the standard Isabelle/ZF the inequality relation on integers
  is denoted \<open>\<le>\<close> prepended with the dollar sign.\<close>

definition
  "IntegerOrder \<equiv> {p \<in> int\<times>int. fst(p) $\<le> snd(p)}"

text\<open>This defines the set of positive integers.\<close>

definition
  "PositiveIntegers \<equiv> PositiveSet(int,IntegerAddition,IntegerOrder)"

text\<open>IntegerAddition and IntegerMultiplication are functions on 
  \<open>int \<times> int\<close>.\<close>

lemma Int_ZF_1_L1: shows
  "IntegerAddition : int\<times>int \<rightarrow> int"
  "IntegerMultiplication : int\<times>int \<rightarrow> int"
proof -
  have
    "{\<langle> x,c\<rangle> \<in> (int\<times>int)\<times>int. fst(x) $+ snd(x) = c} \<in> int\<times>int\<rightarrow>int" 
    "{\<langle> x,c\<rangle> \<in> (int\<times>int)\<times>int. fst(x) $* snd(x) = c} \<in> int\<times>int\<rightarrow>int"
    using func1_1_L11A by auto
  then show "IntegerAddition : int\<times>int \<rightarrow> int" 
    "IntegerMultiplication : int\<times>int \<rightarrow> int"
    using IntegerAddition_def IntegerMultiplication_def by auto
qed

text\<open>The next context (locale) defines notation used for integers.
  We define \<open>\<zero>\<close> to denote the neutral element of addition, 
  \<open>\<one>\<close> as the
  unit of the multiplicative monoid. We introduce notation \<open>m\<lsq>n\<close> 
  for integers and write \<open>m..n\<close> to denote the integer interval 
  with endpoints in $m$ and $n$. 
  \<open>abs(m)\<close> means the absolute value of $m$. This is a function
  defined in \<open>OrderedGroup\<close> that assigns $x$ to itself if $x$ is 
  positive and assigns the opposite of $x$ if $x\leq 0$. 
  Unforunately we cannot 
  use the $|\cdot|$ notation as in the \<open>OrderedGroup\<close> theory as this 
  notation has been hogged by the standard Isabelle's \<open>Int\<close> theory.
  The notation \<open>\<sm>A\<close> where $A$ is a subset of integers means the 
  set $\{-m: m\in A\}$. The symbol \<open>maxf(f,M)\<close> denotes tha maximum 
  of function $f$ over the set $A$. We also introduce a similar notation
  for the minimum.\<close>

locale int0 =

  fixes ints ("\<int>")
  defines ints_def [simp]: "\<int> \<equiv> int"

  fixes ia (infixl "\<ra>" 69)
  defines ia_def [simp]: "a\<ra>b \<equiv> IntegerAddition`\<langle> a,b\<rangle>"

  fixes iminus ("\<rm> _" 72)
  defines rminus_def [simp]: "\<rm>a \<equiv> GroupInv(\<int>,IntegerAddition)`(a)"

  fixes isub (infixl "\<rs>" 69)
  defines isub_def [simp]: "a\<rs>b \<equiv> a\<ra> (\<rm> b)"

  fixes imult (infixl "\<cdot>" 70)
  defines imult_def [simp]: "a\<cdot>b \<equiv> IntegerMultiplication`\<langle> a,b\<rangle>"

  fixes setneg ("\<sm> _" 72)
  defines setneg_def [simp]: "\<sm>A \<equiv> GroupInv(\<int>,IntegerAddition)``(A)"

  fixes izero ("\<zero>")
  defines izero_def [simp]: "\<zero> \<equiv> TheNeutralElement(\<int>,IntegerAddition)"

  fixes ione ("\<one>")
  defines ione_def [simp]: "\<one> \<equiv> TheNeutralElement(\<int>,IntegerMultiplication)"

  fixes itwo ("\<two>")
  defines itwo_def [simp]: "\<two> \<equiv> \<one>\<ra>\<one>"
 
  fixes ithree ("\<three>")
  defines ithree_def [simp]: "\<three> \<equiv> \<two>\<ra>\<one>"
  
  fixes nonnegative ("\<int>\<^sup>+")
  defines nonnegative_def [simp]: 
  "\<int>\<^sup>+ \<equiv> Nonnegative(\<int>,IntegerAddition,IntegerOrder)"

  fixes positive ("\<int>\<^sub>+")
  defines positive_def [simp]: 
  "\<int>\<^sub>+ \<equiv> PositiveSet(\<int>,IntegerAddition,IntegerOrder)"

  fixes abs 
  defines abs_def [simp]: 
  "abs(m) \<equiv> AbsoluteValue(\<int>,IntegerAddition,IntegerOrder)`(m)"
  
  fixes lesseq (infix "\<lsq>" 60)
  defines lesseq_def [simp]: "m \<lsq> n \<equiv> \<langle>m,n\<rangle> \<in> IntegerOrder"

  fixes interval (infix ".." 70)
  defines interval_def [simp]: "m..n \<equiv> Interval(IntegerOrder,m,n)"

  fixes maxf
  defines maxf_def [simp]: "maxf(f,A) \<equiv> Maximum(IntegerOrder,f``(A))"

  fixes minf
  defines minf_def [simp]: "minf(f,A) \<equiv> Minimum(IntegerOrder,f``(A))"

text\<open>IntegerAddition adds integers and IntegerMultiplication multiplies
  integers. This states that the ZF functions \<open>IntegerAddition\<close> and
  \<open>IntegerMultiplication\<close> give the same results as the higher-order
  equivalents defined in the standard \<open>Int\<close> theory.\<close>

lemma (in int0) Int_ZF_1_L2: assumes A1: "a \<in> \<int>"  "b \<in> \<int>"
  shows 
  "a\<ra>b = a $+ b"  
  "a\<cdot>b = a $* b"
proof -
  let ?x = "\<langle> a,b\<rangle>"
  let ?c = "a $+ b"
  let ?d = "a $* b"
  from A1 have 
    "\<langle> ?x,?c\<rangle> \<in> {\<langle> x,c\<rangle> \<in> (\<int>\<times>\<int>)\<times>\<int>. fst(x) $+ snd(x) = c}"
    "\<langle> ?x,?d\<rangle> \<in> {\<langle> x,d\<rangle> \<in> (\<int>\<times>\<int>)\<times>\<int>. fst(x) $* snd(x) = d}"
    by auto
  then show "a\<ra>b = a $+ b"  "a\<cdot>b = a $* b"
    using IntegerAddition_def IntegerMultiplication_def 
      Int_ZF_1_L1 apply_iff by auto
qed
 
text\<open>Integer addition and multiplication are associative.\<close>

lemma (in int0) Int_ZF_1_L3: 
  assumes "x\<in>\<int>"  "y\<in>\<int>"  "z\<in>\<int>"
  shows "x\<ra>y\<ra>z = x\<ra>(y\<ra>z)"  "x\<cdot>y\<cdot>z = x\<cdot>(y\<cdot>z)"
  using assms Int_ZF_1_L2 zadd_assoc zmult_assoc by auto

text\<open>Integer addition and multiplication are commutative.\<close>

lemma (in int0) Int_ZF_1_L4:
  assumes "x\<in>\<int>"  "y\<in>\<int>"
  shows "x\<ra>y = y\<ra>x"  "x\<cdot>y = y\<cdot>x"
  using assms Int_ZF_1_L2 zadd_commute zmult_commute 
  by auto

text\<open>Zero is neutral for addition and one for multiplication.\<close>

lemma (in int0) Int_ZF_1_L5: assumes A1:"x\<in>\<int>"
  shows "($# 0) \<ra> x = x \<and> x \<ra> ($# 0) = x"
  "($# 1)\<cdot>x = x \<and> x\<cdot>($# 1) = x"
proof -
  from A1 show "($# 0) \<ra> x = x \<and> x \<ra> ($# 0) = x"
    using  Int_ZF_1_L2 zadd_int0 Int_ZF_1_L4 by simp
  from A1 have "($# 1)\<cdot>x = x"
    using Int_ZF_1_L2 zmult_int1 by simp
  with A1 show "($# 1)\<cdot>x = x \<and> x\<cdot>($# 1) = x"
    using Int_ZF_1_L4 by simp
qed
    
text\<open>Zero is neutral for addition and one for multiplication.\<close>

lemma (in int0) Int_ZF_1_L6: shows "($# 0)\<in>\<int> \<and> 
  (\<forall>x\<in>\<int>. ($# 0)\<ra>x = x \<and> x\<ra>($# 0) = x)"
  "($# 1)\<in>\<int> \<and> 
  (\<forall>x\<in>\<int>. ($# 1)\<cdot>x = x \<and> x\<cdot>($# 1) = x)"
  using Int_ZF_1_L5 by auto

text\<open>Integers with addition and integers with multiplication
  form monoids.\<close>
 
theorem (in int0) Int_ZF_1_T1: shows
  "IsAmonoid(\<int>,IntegerAddition)"
  "IsAmonoid(\<int>,IntegerMultiplication)"
proof -
   have  
    "\<exists>e\<in>\<int>. \<forall>x\<in>\<int>. e\<ra>x = x \<and> x\<ra>e = x"
     "\<exists>e\<in>\<int>. \<forall>x\<in>\<int>. e\<cdot>x = x \<and> x\<cdot>e = x"
     using int0.Int_ZF_1_L6 by auto
   then show "IsAmonoid(\<int>,IntegerAddition)"
     "IsAmonoid(\<int>,IntegerMultiplication)" using 
     IsAmonoid_def IsAssociative_def Int_ZF_1_L1 Int_ZF_1_L3 
     by auto
qed

text\<open>Zero is the neutral element of the integers with addition
  and one is the neutral element of the integers with multiplication.\<close>

lemma (in int0) Int_ZF_1_L8: shows "($# 0) = \<zero>"  "($# 1) = \<one>"
proof -
  have "monoid0(\<int>,IntegerAddition)"
    using Int_ZF_1_T1 monoid0_def by simp
  moreover have 
    "($# 0)\<in>\<int> \<and>
    (\<forall>x\<in>\<int>. IntegerAddition`\<langle>$# 0,x\<rangle> = x \<and> 
    IntegerAddition`\<langle>x ,$# 0\<rangle> = x)"
    using Int_ZF_1_L6 by auto
  ultimately have "($# 0) = TheNeutralElement(\<int>,IntegerAddition)"
    by (rule monoid0.group0_1_L4)
  then show "($# 0) = \<zero>" by simp
  have "monoid0(int,IntegerMultiplication)"
    using Int_ZF_1_T1 monoid0_def by simp
  moreover have "($# 1) \<in> int \<and> 
    (\<forall>x\<in>int. IntegerMultiplication`\<langle>$# 1, x\<rangle> = x \<and> 
    IntegerMultiplication`\<langle>x ,$# 1\<rangle> = x)"
    using Int_ZF_1_L6 by auto
  ultimately have
    "($# 1) = TheNeutralElement(int,IntegerMultiplication)"
    by (rule monoid0.group0_1_L4)
  then show  "($# 1) = \<one>" by simp
qed

text\<open>$0$  and $1$, as defined in \<open>int0\<close> context, are integers.\<close>

lemma (in int0) Int_ZF_1_L8A: shows "\<zero> \<in> \<int>"  "\<one> \<in> \<int>"
proof -
  have "($# 0) \<in> \<int>"  "($# 1) \<in> \<int>" by auto
  then show "\<zero> \<in> \<int>"  "\<one> \<in> \<int>" using Int_ZF_1_L8 by auto
qed

text\<open>Zero is not one.\<close>

lemma (in int0) int_zero_not_one: shows "\<zero> \<noteq> \<one>"
proof -
  have "($# 0) \<noteq> ($# 1)" by simp
  then show "\<zero> \<noteq> \<one>" using Int_ZF_1_L8 by simp
qed

text\<open>The set of integers is not empty, of course.\<close>

lemma (in int0) int_not_empty: shows "\<int> \<noteq> 0"
  using Int_ZF_1_L8A by auto

text\<open>The set of integers has more than just zero in it.\<close>

lemma (in int0) int_not_trivial: shows "\<int> \<noteq> {\<zero>}"
  using Int_ZF_1_L8A int_zero_not_one by blast
  
text\<open>Each integer has an inverse (in the addition sense).\<close>

lemma (in int0) Int_ZF_1_L9: assumes A1: "g \<in> \<int>"
  shows "\<exists> b\<in>\<int>. g\<ra>b = \<zero>"
proof -
  from A1 have "g\<ra> $-g = \<zero>"
    using Int_ZF_1_L2 Int_ZF_1_L8 by simp
  thus ?thesis by auto
qed

text\<open>Integers with addition form an abelian group. This also shows
  that we can apply all theorems proven in the proof contexts (locales) 
  that require the assumpion that some pair of sets form a group like 
  locale \<open>group0\<close>.\<close>
 
theorem Int_ZF_1_T2: shows
  "IsAgroup(int,IntegerAddition)"
  "IntegerAddition {is commutative on} int"
  "group0(int,IntegerAddition)"
  using int0.Int_ZF_1_T1 int0.Int_ZF_1_L9 IsAgroup_def
  group0_def int0.Int_ZF_1_L4 IsCommutative_def by auto

text\<open>What is the additive group inverse in the group of integers?\<close>

lemma (in int0) Int_ZF_1_L9A: assumes A1: "m\<in>\<int>" 
  shows "$-m = \<rm>m"
proof - 
   from A1 have "m\<in>int" "$-m \<in> int" "IntegerAddition`\<langle> m,$-m\<rangle> = 
     TheNeutralElement(int,IntegerAddition)"
    using zminus_type Int_ZF_1_L2 Int_ZF_1_L8 by auto
  then have "$-m = GroupInv(int,IntegerAddition)`(m)"
    using Int_ZF_1_T2 group0.group0_2_L9 by blast
  then show ?thesis by simp
qed

text\<open>Subtracting integers corresponds to adding the negative.\<close>

lemma (in int0) Int_ZF_1_L10: assumes A1: "m\<in>\<int>"  "n\<in>\<int>"
  shows "m\<rs>n = m $+ $-n"
  using assms Int_ZF_1_T2  group0.inverse_in_group Int_ZF_1_L9A Int_ZF_1_L2
  by simp

text\<open>Negative of zero is zero.\<close>

lemma (in int0) Int_ZF_1_L11: shows "(\<rm>\<zero>) = \<zero>"
  using Int_ZF_1_T2  group0.group_inv_of_one by simp

text\<open>A trivial calculation lemma that allows to subtract and add one.\<close>

lemma Int_ZF_1_L12: 
  assumes "m\<in>int" shows "m $- $#1 $+ $#1 = m"
  using assms eq_zdiff_iff by auto

text\<open>A trivial calculation lemma that allows to subtract and add one,
  version with ZF-operation.\<close>

lemma (in int0) Int_ZF_1_L13: assumes "m\<in>\<int>" 
  shows "(m $- $#1) \<ra> \<one> = m"
  using assms Int_ZF_1_L8A Int_ZF_1_L2 Int_ZF_1_L8 Int_ZF_1_L12
  by simp

text\<open>Adding or subtracing one changes integers.\<close>

lemma (in int0) Int_ZF_1_L14: assumes A1: "m\<in>\<int>" 
  shows 
  "m\<ra>\<one> \<noteq> m"
  "m\<rs>\<one> \<noteq> m"
proof -
  { assume "m\<ra>\<one> = m" 
    with A1 have 
      "group0(\<int>,IntegerAddition)"  
      "m\<in>\<int>"  "\<one>\<in>\<int>"
      "IntegerAddition`\<langle>m,\<one>\<rangle> = m" 
      using Int_ZF_1_T2 Int_ZF_1_L8A by auto
    then have "\<one> = TheNeutralElement(\<int>,IntegerAddition)"
      by (rule group0.group0_2_L7)
    then have False using int_zero_not_one by simp
  } then show I: "m\<ra>\<one> \<noteq> m" by auto
  { from A1 have "m \<rs> \<one> \<ra> \<one> = m"
      using Int_ZF_1_L8A Int_ZF_1_T2 group0.inv_cancel_two
      by simp
    moreover assume "m\<rs>\<one> = m"
    ultimately have "m \<ra> \<one> = m" by simp
    with I have False by simp
  } then show "m\<rs>\<one> \<noteq> m" by auto
qed

text\<open>If the difference is zero, the integers are equal.\<close>

lemma (in int0) Int_ZF_1_L15: 
  assumes A1: "m\<in>\<int>"  "n\<in>\<int>" and A2: "m\<rs>n = \<zero>"
  shows "m=n" 
proof -
  let ?G = "\<int>"
  let ?f = "IntegerAddition"
  from A1 A2 have
    "group0(?G, ?f)"
    "m \<in> ?G"  "n \<in> ?G"
    "?f`\<langle>m, GroupInv(?G, ?f)`(n)\<rangle> = TheNeutralElement(?G, ?f)"
    using Int_ZF_1_T2 by auto
  then show "m=n" by (rule group0.group0_2_L11A)
qed

subsection\<open>Integers as an ordered group\<close>

text\<open>In this section we define order on integers as a relation, that is a 
  subset of $Z\times Z$ and show that integers form an ordered group.\<close>

text\<open>The next lemma interprets the order definition one way.\<close>

lemma (in int0) Int_ZF_2_L1: 
  assumes A1: "m\<in>\<int>" "n\<in>\<int>" and A2: "m $\<le> n"
  shows "m \<lsq> n"
proof -
  from A1 A2 have "\<langle> m,n\<rangle> \<in> {x\<in>\<int>\<times>\<int>. fst(x) $\<le> snd(x)}" 
    by simp
  then show ?thesis using IntegerOrder_def by simp
qed

text\<open>The next lemma interprets the definition the other way.\<close>

lemma (in int0) Int_ZF_2_L1A: assumes A1: "m \<lsq> n" 
  shows "m $\<le> n" "m\<in>\<int>" "n\<in>\<int>"
proof -
  from A1 have "\<langle> m,n\<rangle> \<in> {p\<in>\<int>\<times>\<int>. fst(p) $\<le> snd(p)}"
    using IntegerOrder_def by simp
  thus "m $\<le> n"  "m\<in>\<int>"  "n\<in>\<int>" by auto
qed

text\<open>Integer order is a relation on integers.\<close>

lemma Int_ZF_2_L1B: shows "IntegerOrder \<subseteq> int\<times>int"
proof
  fix x assume "x\<in>IntegerOrder" 
  then have "x \<in> {p\<in>int\<times>int. fst(p) $\<le> snd(p)}"
    using IntegerOrder_def by simp
  then show "x\<in>int\<times>int" by simp
qed

text\<open>The way we define the notion of being bounded below,
  its sufficient for the relation to be on integers for
  all bounded below sets to be subsets of integers.\<close>

lemma (in int0) Int_ZF_2_L1C: 
  assumes A1: "IsBoundedBelow(A,IntegerOrder)"
  shows "A\<subseteq>\<int>"
proof -
  from A1 have 
    "IntegerOrder \<subseteq> \<int>\<times>\<int>"
    "IsBoundedBelow(A,IntegerOrder)"
    using Int_ZF_2_L1B by auto
  then show "A\<subseteq>\<int>" by (rule Order_ZF_3_L1B)
qed

text\<open>The order on integers is reflexive.\<close>

lemma (in int0) int_ord_is_refl: shows "refl(\<int>,IntegerOrder)"
  using Int_ZF_2_L1 zle_refl refl_def by auto

text\<open>The essential condition to show antisymmetry of the order on integers.\<close>

lemma (in int0) Int_ZF_2_L3: 
  assumes A1: "m \<lsq> n"  "n \<lsq> m"  
  shows "m=n"
proof -
  from A1 have "m $\<le> n"  "n $\<le> m"  "m\<in>\<int>"  "n\<in>\<int>"
    using Int_ZF_2_L1A by auto
  then show "m=n" using zle_anti_sym by auto
qed
  
text\<open>The order on integers is antisymmetric.\<close>

lemma (in int0) Int_ZF_2_L4: shows "antisym(IntegerOrder)"
proof -
  have "\<forall>m n. m \<lsq> n  \<and> n \<lsq> m \<longrightarrow> m=n"
    using Int_ZF_2_L3 by auto
  then show ?thesis using imp_conj antisym_def by simp
qed

text\<open>The essential condition to show that the order on integers is 
  transitive.\<close>

lemma Int_ZF_2_L5: 
  assumes A1: "\<langle>m,n\<rangle> \<in> IntegerOrder"  "\<langle>n,k\<rangle> \<in> IntegerOrder"
  shows "\<langle>m,k\<rangle> \<in> IntegerOrder"
proof -
  from A1 have T1: "m $\<le> n" "n $\<le> k" and T2: "m\<in>int" "k\<in>int"
    using int0.Int_ZF_2_L1A by auto
  from T1 have "m $\<le> k" by (rule zle_trans)
  with T2 show ?thesis using int0.Int_ZF_2_L1 by simp
qed

text\<open>The order on integers is 
  transitive. This version is stated in the \<open>int0\<close> context 
  using notation for integers.\<close>

lemma (in int0) Int_order_transitive: 
  assumes A1: "m\<lsq>n"  "n\<lsq>k"
  shows "m\<lsq>k"
proof -
  from A1 have "\<langle> m,n\<rangle> \<in> IntegerOrder"  "\<langle> n,k\<rangle> \<in> IntegerOrder"
    by auto
  then have "\<langle> m,k\<rangle> \<in> IntegerOrder" by (rule Int_ZF_2_L5)
  then show "m\<lsq>k" by simp
qed

text\<open>The order on integers is transitive.\<close>

lemma Int_ZF_2_L6: shows "trans(IntegerOrder)"
proof -
  have "\<forall> m n k. 
    \<langle>m, n\<rangle> \<in> IntegerOrder \<and> \<langle>n, k\<rangle> \<in> IntegerOrder \<longrightarrow> 
    \<langle>m, k\<rangle> \<in> IntegerOrder"
    using Int_ZF_2_L5 by blast
  then show ?thesis by (rule Fol1_L2)
qed

text\<open>The order on integers is a partial order.\<close>

lemma Int_ZF_2_L7: shows "IsPartOrder(int,IntegerOrder)"
  using int0.int_ord_is_refl int0.Int_ZF_2_L4 
    Int_ZF_2_L6 IsPartOrder_def by simp

text\<open>The essential condition to show that the order on integers is 
  preserved by translations.\<close>

lemma (in int0) int_ord_transl_inv: 
  assumes A1: "k \<in> \<int>" and A2: "m \<lsq> n" 
  shows "m\<ra>k \<lsq> n\<ra>k "  "k\<ra>m\<lsq> k\<ra>n "
proof -
  from A2 have "m $\<le> n" and "m\<in>\<int>" "n\<in>\<int>" 
    using Int_ZF_2_L1A by auto  
  with A1 show "m\<ra>k \<lsq> n\<ra>k "  "k\<ra>m\<lsq> k\<ra>n "
    using zadd_right_cancel_zle zadd_left_cancel_zle
    Int_ZF_1_L2 Int_ZF_1_L1 apply_funtype
    Int_ZF_1_L2 Int_ZF_2_L1 Int_ZF_1_L2 by auto
qed

text\<open>Integers form a linearly ordered group. We can apply all theorems
  proven in group3 context to integers.\<close>

theorem (in int0) Int_ZF_2_T1: shows
  "IsAnOrdGroup(\<int>,IntegerAddition,IntegerOrder)"
  "IntegerOrder {is total on} \<int>"
  "group3(\<int>,IntegerAddition,IntegerOrder)"
  "IsLinOrder(\<int>,IntegerOrder)"
proof -
  have "\<forall>k\<in>\<int>. \<forall>m n. m \<lsq> n  \<longrightarrow> 
    m\<ra>k \<lsq> n\<ra>k \<and> k\<ra>m\<lsq> k\<ra>n"
    using int_ord_transl_inv by simp
  then show T1: "IsAnOrdGroup(\<int>,IntegerAddition,IntegerOrder)" using
    Int_ZF_1_T2 Int_ZF_2_L1B Int_ZF_2_L7 IsAnOrdGroup_def
    by simp
  then show "group3(\<int>,IntegerAddition,IntegerOrder)"
    using group3_def by simp
  have "\<forall>n\<in>\<int>. \<forall>m\<in>\<int>. n\<lsq>m \<or> m\<lsq>n"
    using zle_linear Int_ZF_2_L1 by auto
  then show "IntegerOrder {is total on} \<int>"
    using IsTotal_def by simp
  with T1 show "IsLinOrder(\<int>,IntegerOrder)"
    using IsAnOrdGroup_def IsPartOrder_def IsLinOrder_def by simp
qed

text\<open>If a pair $(i,m)$ belongs to the order relation on integers and
  $i\neq m$, then $i<m$ in the sense of defined in the standard Isabelle's 
  Int.thy.\<close>

lemma (in int0) Int_ZF_2_L9: assumes A1: "i \<lsq> m" and A2: "i\<noteq>m"
  shows "i $< m"
proof -
  from A1 have "i $\<le> m"  "i\<in>\<int>"  "m\<in>\<int>" 
    using Int_ZF_2_L1A by auto
  with A2 show "i $< m" using zle_def by simp
qed

text\<open>This shows how Isabelle's \<open>$<\<close> operator translates to IsarMathLib
  notation.\<close>

lemma (in int0) Int_ZF_2_L9AA: assumes A1: "m\<in>\<int>"  "n\<in>\<int>"
  and A2: "m $< n"
  shows "m\<lsq>n"  "m \<noteq> n"
  using assms zle_def Int_ZF_2_L1 by auto

text\<open>A small technical lemma about putting one on the other side
  of an inequality.\<close>

lemma (in int0) Int_ZF_2_L9A: 
  assumes A1: "k\<in>\<int>" and A2: "m \<lsq> k $- ($# 1)"
  shows "m\<ra>\<one> \<lsq> k"
proof -
  from A2 have "m\<ra>\<one> \<lsq> (k $- ($# 1)) \<ra> \<one>"
    using Int_ZF_1_L8A int_ord_transl_inv by simp
  with A1 show "m\<ra>\<one> \<lsq> k"
    using Int_ZF_1_L13 by simp
qed

text\<open>We can put any integer on the other side of an inequality reversing
  its sign.\<close>

lemma (in int0) Int_ZF_2_L9B: assumes "i\<in>\<int>"  "m\<in>\<int>"  "k\<in>\<int>"
  shows "i\<ra>m \<lsq> k  \<longleftrightarrow> i \<lsq> k\<rs>m"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L9A
  by simp

text\<open>A special case of \<open>Int_ZF_2_L9B\<close> with weaker assumptions.\<close>

lemma (in int0) Int_ZF_2_L9C: 
  assumes "i\<in>\<int>"  "m\<in>\<int>" and "i\<rs>m \<lsq> k" 
  shows "i \<lsq> k\<ra>m"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L9B
  by simp
  
text\<open>Taking (higher order) minus on both sides of inequality reverses it.\<close>

lemma (in int0) Int_ZF_2_L10: assumes "k \<lsq> i"
  shows 
  "(\<rm>i) \<lsq> (\<rm>k)"   
  "$-i \<lsq> $-k" 
  using assms Int_ZF_2_L1A Int_ZF_1_L9A Int_ZF_2_T1 
    group3.OrderedGroup_ZF_1_L5 by auto


text\<open>Taking minus on both sides of inequality reverses it, 
  version with a negative on one side.\<close>

lemma (in int0) Int_ZF_2_L10AA: assumes "n\<in>\<int>"  "m\<lsq>(\<rm>n)"
  shows "n\<lsq>(\<rm>m)"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L5AD
  by simp

text\<open>We can cancel the same element on on both sides of an inequality,
  a version with minus on both sides.\<close>

lemma (in int0) Int_ZF_2_L10AB: 
  assumes "m\<in>\<int>"  "n\<in>\<int>"  "k\<in>\<int>" and "m\<rs>n \<lsq> m\<rs>k"
  shows "k\<lsq>n"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L5AF
  by simp

text\<open>If an integer is nonpositive, then its opposite is nonnegative.\<close>

lemma (in int0) Int_ZF_2_L10A: assumes "k \<lsq> \<zero>"
  shows "\<zero>\<lsq>(\<rm>k)"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L5A by simp

text\<open>If the opposite of an integers is nonnegative, then the integer 
  is nonpositive.\<close>

lemma (in int0) Int_ZF_2_L10B: 
  assumes "k\<in>\<int>" and "\<zero>\<lsq>(\<rm>k)"
  shows "k\<lsq>\<zero>"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L5AA by simp

text\<open>Adding one to an integer corresponds to taking a successor for a natural
  number.\<close>

lemma (in int0) Int_ZF_2_L11: 
  shows "i $+ $# n $+ ($# 1)  =  i $+ $# succ(n)"
proof -
  have "$# succ(n) = $#1 $+ $# n" using int_succ_int_1 by blast
  then have "i $+ $# succ(n) = i $+ ($# n  $+ $#1)"
    using zadd_commute by simp
  then show ?thesis using zadd_assoc by simp
qed

text\<open>Adding a natural number increases integers.\<close>

lemma (in int0) Int_ZF_2_L12: assumes A1: "i\<in>\<int>" and A2: "n\<in>nat"
  shows "i \<lsq> i $+ $#n"
proof -
  { assume "n = 0" 
    with A1 have "i \<lsq> i $+ $#n" using zadd_int0 int_ord_is_refl refl_def
      by simp }
  moreover
  { assume "n\<noteq>0" 
    with A2 obtain k where "k\<in>nat" "n = succ(k)" 
      using Nat_ZF_1_L3 by auto
    with A1 have "i \<lsq> i $+ $#n"
      using zless_succ_zadd zless_imp_zle Int_ZF_2_L1 by simp }
  ultimately show ?thesis by blast
qed

text\<open>Adding one increases integers.\<close>

lemma (in int0) Int_ZF_2_L12A: assumes A1: "j\<lsq>k"
  shows "j \<lsq> k $+ $#1"  "j \<lsq> k\<ra>\<one>"
proof -
  from A1 have T1:"j\<in>\<int>" "k\<in>\<int>" "j $\<le> k" 
    using Int_ZF_2_L1A by auto  
  moreover from T1 have "k $\<le> k $+ $#1" using Int_ZF_2_L12 Int_ZF_2_L1A
    by simp
  ultimately have "j $\<le> k $+ $#1" using zle_trans by fast
  with T1 show "j \<lsq> k $+ $#1" using Int_ZF_2_L1 by simp
  with T1 have "j\<lsq> k\<ra>$#1"
    using Int_ZF_1_L2 by simp
  then show "j \<lsq> k\<ra>\<one>" using Int_ZF_1_L8 by simp
qed

text\<open>Adding one increases integers, yet one more version.\<close>

lemma (in int0) Int_ZF_2_L12B: assumes A1: "m\<in>\<int>" shows "m \<lsq> m\<ra>\<one>"
  using assms int_ord_is_refl refl_def Int_ZF_2_L12A by simp

text\<open>If $k+1 = m+n$, where $n$ is a non-zero natural number, then 
  $m\leq k$.\<close>

lemma (in int0) Int_ZF_2_L13: 
  assumes A1: "k\<in>\<int>" "m\<in>\<int>" and A2: "n\<in>nat" 
  and A3: "k $+ ($# 1) = m $+ $# succ(n)"
  shows "m \<lsq> k"
proof -
  from A1 have "k\<in>\<int>" "m $+ $# n \<in> \<int>" by auto
  moreover from assms have "k $+ $# 1 = m $+ $# n $+ $#1"
    using Int_ZF_2_L11 by simp
  ultimately have "k = m $+ $# n" using zadd_right_cancel by simp
  with A1 A2 show ?thesis using Int_ZF_2_L12 by simp
qed

text\<open>The absolute value of an integer is an integer.\<close>

lemma (in int0) Int_ZF_2_L14: assumes A1: "m\<in>\<int>"
  shows "abs(m) \<in> \<int>"
proof -
  have "AbsoluteValue(\<int>,IntegerAddition,IntegerOrder) : \<int>\<rightarrow>\<int>"
    using Int_ZF_2_T1 group3.OrderedGroup_ZF_3_L1 by simp
  with A1 show ?thesis using apply_funtype by simp
qed

text\<open>If two integers are nonnegative, then the opposite
  of one is less or equal than the other and the sum is also nonnegative.\<close>

lemma (in int0) Int_ZF_2_L14A: 
  assumes "\<zero>\<lsq>m"  "\<zero>\<lsq>n"
  shows 
  "(\<rm>m) \<lsq> n"
  "\<zero> \<lsq> m \<ra> n"
  using assms Int_ZF_2_T1 
    group3.OrderedGroup_ZF_1_L5AC group3.OrderedGroup_ZF_1_L12
  by auto

text\<open>We can increase components in an estimate.\<close>

lemma (in int0) Int_ZF_2_L15: 
  assumes "b\<lsq>b\<^sub>1" "c\<lsq>c\<^sub>1" and "a\<lsq>b\<ra>c"
  shows "a\<lsq>b\<^sub>1\<ra>c\<^sub>1"
proof -
  from assms have "group3(\<int>,IntegerAddition,IntegerOrder)" 
    "\<langle>a,IntegerAddition`\<langle> b,c\<rangle>\<rangle> \<in> IntegerOrder" 
    "\<langle>b,b\<^sub>1\<rangle> \<in> IntegerOrder" "\<langle>c,c\<^sub>1\<rangle> \<in> IntegerOrder"
    using Int_ZF_2_T1 by auto
  then have "\<langle>a,IntegerAddition`\<langle> b\<^sub>1,c\<^sub>1\<rangle>\<rangle> \<in> IntegerOrder" 
    by (rule group3.OrderedGroup_ZF_1_L5E)
  thus ?thesis by simp
qed
 
text\<open>We can add or subtract the sides of two inequalities.\<close>

lemma (in int0) int_ineq_add_sides: 
  assumes "a\<lsq>b" and "c\<lsq>d"  
  shows 
  "a\<ra>c \<lsq> b\<ra>d"
  "a\<rs>d \<lsq> b\<rs>c"
  using assms Int_ZF_2_T1 
    group3.OrderedGroup_ZF_1_L5B group3.OrderedGroup_ZF_1_L5I
  by auto

text\<open>We can increase the second component in an estimate.\<close>

lemma (in int0) Int_ZF_2_L15A: 
  assumes "b\<in>\<int>" and "a\<lsq>b\<ra>c" and A3: "c\<lsq>c\<^sub>1" 
  shows "a\<lsq>b\<ra>c\<^sub>1"
proof - 
  from assms have 
    "group3(\<int>,IntegerAddition,IntegerOrder)" 
    "b \<in> \<int>"
    "\<langle>a,IntegerAddition`\<langle> b,c\<rangle>\<rangle> \<in> IntegerOrder" 
    "\<langle>c,c\<^sub>1\<rangle> \<in> IntegerOrder"
    using Int_ZF_2_T1 by auto
  then have "\<langle>a,IntegerAddition`\<langle> b,c\<^sub>1\<rangle>\<rangle> \<in> IntegerOrder" 
     by (rule group3.OrderedGroup_ZF_1_L5D)
   thus ?thesis by simp
qed

text\<open>If we increase the second component in a sum of three
  integers, the whole sum inceases.\<close>

lemma (in int0) Int_ZF_2_L15C: 
  assumes A1: "m\<in>\<int>"  "n\<in>\<int>" and A2: "k \<lsq> L"
  shows "m\<ra>k\<ra>n \<lsq> m\<ra>L\<ra>n"
proof -
  let ?P = "IntegerAddition"
  from assms have
    "group3(int,?P,IntegerOrder)"
    "m \<in> int"  "n \<in> int"
    "\<langle>k,L\<rangle> \<in> IntegerOrder"
    using Int_ZF_2_T1 by auto
  then have "\<langle>?P`\<langle>?P`\<langle> m,k\<rangle>,n\<rangle>, ?P`\<langle>?P`\<langle> m,L\<rangle>,n\<rangle> \<rangle> \<in> IntegerOrder"
    by (rule group3.OrderedGroup_ZF_1_L10)
  then show "m\<ra>k\<ra>n \<lsq> m\<ra>L\<ra>n" by simp
qed

text\<open>We don't decrease an integer by adding a nonnegative one.\<close>

lemma (in int0) Int_ZF_2_L15D:
  assumes "\<zero>\<lsq>n"  "m\<in>\<int>"
  shows "m \<lsq> n\<ra>m"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L5F
  by simp

text\<open>Some inequalities about the sum of two integers
  and its absolute value.\<close>

lemma (in int0) Int_ZF_2_L15E:
  assumes "m\<in>\<int>"  "n\<in>\<int>"
  shows 
  "m\<ra>n \<lsq> abs(m)\<ra>abs(n)"
  "m\<rs>n \<lsq> abs(m)\<ra>abs(n)"
  "(\<rm>m)\<ra>n \<lsq> abs(m)\<ra>abs(n)"
  "(\<rm>m)\<rs>n \<lsq> abs(m)\<ra>abs(n)"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_3_L6A
  by auto

text\<open>We can add a nonnegative
  integer to the right hand side of an inequality.\<close>

lemma (in int0) Int_ZF_2_L15F:  assumes "m\<lsq>k"  and "\<zero>\<lsq>n"
  shows "m \<lsq> k\<ra>n"  "m \<lsq> n\<ra>k"  
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L5G
  by auto

text\<open>Triangle inequality for integers.\<close>

lemma (in int0) Int_triangle_ineq: 
  assumes "m\<in>\<int>"  "n\<in>\<int>"
  shows "abs(m\<ra>n)\<lsq>abs(m)\<ra>abs(n)"
  using assms Int_ZF_1_T2 Int_ZF_2_T1 group3.OrdGroup_triangle_ineq
  by simp

text\<open>Taking absolute value does not change nonnegative integers.\<close>

lemma (in int0) Int_ZF_2_L16:
  assumes "\<zero>\<lsq>m" shows  "m\<in>\<int>\<^sup>+" and "abs(m) = m"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L2 
    group3.OrderedGroup_ZF_3_L2 by auto

text\<open>$0\leq 1$, so $|1| = 1$.\<close>

lemma (in int0) Int_ZF_2_L16A: shows "\<zero>\<lsq>\<one>" and "abs(\<one>) = \<one>"
proof -
  have "($# 0) \<in> \<int>" "($# 1)\<in> \<int>" by auto
  then have "\<zero>\<lsq>\<zero>" and T1: "\<one>\<in>\<int>" 
    using Int_ZF_1_L8 int_ord_is_refl refl_def by auto
  then have "\<zero>\<lsq>\<zero>\<ra>\<one>" using Int_ZF_2_L12A by simp
  with T1 show "\<zero>\<lsq>\<one>" using Int_ZF_1_T2 group0.group0_2_L2
    by simp
  then show "abs(\<one>) = \<one>" using Int_ZF_2_L16 by simp
qed

text\<open>$1\leq 2$.\<close>

lemma (in int0) Int_ZF_2_L16B: shows "\<one>\<lsq>\<two>"
proof -
  have "($# 1)\<in> \<int>" by simp
  then show "\<one>\<lsq>\<two>" 
    using Int_ZF_1_L8 int_ord_is_refl refl_def Int_ZF_2_L12A 
    by simp
qed

text\<open>Integers greater or equal one are greater or equal zero.\<close>

lemma (in int0) Int_ZF_2_L16C: 
  assumes A1: "\<one>\<lsq>a" shows 
  "\<zero>\<lsq>a"  "a\<noteq>\<zero>"
  "\<two> \<lsq> a\<ra>\<one>"
  "\<one> \<lsq> a\<ra>\<one>"
  "\<zero> \<lsq> a\<ra>\<one>"
proof -
  from A1 have "\<zero>\<lsq>\<one>" and "\<one>\<lsq>a" 
    using Int_ZF_2_L16A by auto
  then show "\<zero>\<lsq>a" by (rule Int_order_transitive)
  have I: "\<zero>\<lsq>\<one>" using Int_ZF_2_L16A by simp 
  have "\<one>\<lsq>\<two>" using Int_ZF_2_L16B by simp
  moreover from A1 show "\<two> \<lsq> a\<ra>\<one>"
    using Int_ZF_1_L8A int_ord_transl_inv by simp
  ultimately show "\<one> \<lsq> a\<ra>\<one>" by (rule Int_order_transitive)
  with I show "\<zero> \<lsq> a\<ra>\<one>" by (rule Int_order_transitive)
  from A1 show "a\<noteq>\<zero>" using
    Int_ZF_2_L16A Int_ZF_2_L3 int_zero_not_one by auto 
qed

text\<open>Absolute value is the same for an integer and its opposite.\<close>

lemma (in int0) Int_ZF_2_L17: 
  assumes "m\<in>\<int>" shows "abs(\<rm>m) = abs(m)"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_3_L7A by simp

text\<open>The absolute value of zero is zero.\<close>

lemma (in int0) Int_ZF_2_L18: shows "abs(\<zero>) = \<zero>"
  using Int_ZF_2_T1 group3.OrderedGroup_ZF_3_L2A by simp

text\<open>A different version of the triangle inequality.\<close>

lemma (in int0) Int_triangle_ineq1: 
  assumes A1: "m\<in>\<int>"  "n\<in>\<int>"
  shows 
  "abs(m\<rs>n) \<lsq> abs(n)\<ra>abs(m)"
  "abs(m\<rs>n) \<lsq> abs(m)\<ra>abs(n)"
proof -
  have "$-n \<in> \<int>" by simp
  with A1 have "abs(m\<rs>n) \<lsq> abs(m)\<ra>abs(\<rm>n)"
    using Int_ZF_1_L9A Int_triangle_ineq by simp
  with A1 show 
    "abs(m\<rs>n) \<lsq> abs(n)\<ra>abs(m)"
    "abs(m\<rs>n) \<lsq> abs(m)\<ra>abs(n)" 
    using Int_ZF_2_L17 Int_ZF_2_L14 Int_ZF_1_T2 IsCommutative_def
    by auto
qed

text\<open>Another version of the triangle inequality.\<close>

lemma (in int0) Int_triangle_ineq2: 
  assumes "m\<in>\<int>"  "n\<in>\<int>"
  and "abs(m\<rs>n) \<lsq> k"
  shows 
  "abs(m) \<lsq> abs(n)\<ra>k"
  "m\<rs>k \<lsq> n"
  "m \<lsq> n\<ra>k"
  "n\<rs>k \<lsq> m"
  using assms Int_ZF_1_T2 Int_ZF_2_T1 
    group3.OrderedGroup_ZF_3_L7D group3.OrderedGroup_ZF_3_L7E
  by auto

text\<open>Triangle inequality with three integers. We could use
  \<open>OrdGroup_triangle_ineq3\<close>, but since simp cannot translate
  the notation directly, it is simpler to reprove it for integers.\<close>

lemma (in int0) Int_triangle_ineq3: 
  assumes A1: "m\<in>\<int>"  "n\<in>\<int>"  "k\<in>\<int>"
  shows "abs(m\<ra>n\<ra>k) \<lsq> abs(m)\<ra>abs(n)\<ra>abs(k)"
proof -
  from A1 have T: "m\<ra>n \<in> \<int>"  "abs(k) \<in> \<int>"
    using Int_ZF_1_T2 group0.group_op_closed  Int_ZF_2_L14
    by auto
  with A1 have "abs(m\<ra>n\<ra>k) \<lsq> abs(m\<ra>n) \<ra> abs(k)"
    using Int_triangle_ineq by simp
  moreover from A1 T have 
    "abs(m\<ra>n) \<ra> abs(k) \<lsq> abs(m) \<ra> abs(n) \<ra> abs(k)"
    using Int_triangle_ineq int_ord_transl_inv by simp
  ultimately show ?thesis by (rule Int_order_transitive)
qed

text\<open>The next lemma shows what happens when one integers is not
  greater or equal than another.\<close>
(* trying to use OrderedGroup_ZF_1_L8  results in a longer proof, 
  simp and auto loop here*) 
lemma (in int0) Int_ZF_2_L19: 
  assumes A1: "m\<in>\<int>"  "n\<in>\<int>" and A2: "\<not>(n\<lsq>m)"
  shows "m\<lsq>n"  "(\<rm>n) \<lsq> (\<rm>m)"  "m\<noteq>n"
proof -
  from A1 A2 show "m\<lsq>n" using Int_ZF_2_T1 IsTotal_def 
    by auto
  then show "(\<rm>n) \<lsq> (\<rm>m)" using Int_ZF_2_L10 
    by simp
  from A1 have "n \<lsq> n" using int_ord_is_refl refl_def 
    by simp
  with A2 show "m\<noteq>n" by auto
qed

text\<open>If one integer is greater or equal and not equal to another,
  then it is not smaller or equal.\<close>

lemma (in int0) Int_ZF_2_L19AA: assumes A1: "m\<lsq>n" and A2: "m\<noteq>n"
  shows "\<not>(n\<lsq>m)"
proof -
  from A1 A2 have 
    "group3(\<int>, IntegerAddition, IntegerOrder)"
    "\<langle>m,n\<rangle> \<in> IntegerOrder"
    "m\<noteq>n"
    using Int_ZF_2_T1 by auto
  then have "\<langle>n,m\<rangle> \<notin> IntegerOrder" 
    by (rule group3.OrderedGroup_ZF_1_L8AA)
  thus "\<not>(n\<lsq>m)" by simp
qed

text\<open>The next lemma allows to prove theorems for the case of positive and 
  negative integers separately.\<close>

lemma (in int0) Int_ZF_2_L19A: assumes A1: "m\<in>\<int>" and A2: "\<not>(\<zero>\<lsq>m)"
  shows "m\<lsq>\<zero>"  "\<zero> \<lsq> (\<rm>m)"  "m\<noteq>\<zero>"
proof -
  from A1 have T: "\<zero> \<in> \<int>"
    using Int_ZF_1_T2 group0.group0_2_L2 by auto
  with A1 A2 show "m\<lsq>\<zero>" using Int_ZF_2_L19 by blast
  from A1 T A2 show "m\<noteq>\<zero>"  by (rule Int_ZF_2_L19)
  from A1 T A2 have "(\<rm>\<zero>)\<lsq>(\<rm>m)" by (rule Int_ZF_2_L19)
  then show "\<zero> \<lsq> (\<rm>m)"
    using Int_ZF_1_T2 group0.group_inv_of_one by simp
qed

text\<open>We can prove a theorem about integers by proving that
  it holds for $m=0$, $m\in$\<open>\<int>\<^sub>+\<close> and $-m\in$\<open>\<int>\<^sub>+\<close>.\<close>

lemma (in int0) Int_ZF_2_L19B: 
  assumes "m\<in>\<int>" and "Q(\<zero>)" and "\<forall>n\<in>\<int>\<^sub>+. Q(n)" and "\<forall>n\<in>\<int>\<^sub>+. Q(\<rm>n)"
  shows "Q(m)"
proof -
  let ?G = "\<int>"
  let ?P = "IntegerAddition"
  let ?r = "IntegerOrder"
  let ?b = "m"
  from assms have 
    "group3(?G, ?P, ?r)"
    "?r {is total on} ?G"
    "?b \<in> ?G"
    "Q(TheNeutralElement(?G, ?P))"
    "\<forall>a\<in>PositiveSet(?G, ?P, ?r). Q(a)"
    "\<forall>a\<in>PositiveSet(?G, ?P, ?r). Q(GroupInv(?G, ?P)`(a))"
    using Int_ZF_2_T1 by auto
  then show "Q(?b)" by (rule group3.OrderedGroup_ZF_1_L18)
qed

text\<open>An integer is not greater than its absolute value.\<close>

lemma (in int0) Int_ZF_2_L19C: assumes A1: "m\<in>\<int>"
  shows 
  "m \<lsq> abs(m)"
  "(\<rm>m) \<lsq> abs(m)"
  using assms Int_ZF_2_T1 
    group3.OrderedGroup_ZF_3_L5 group3.OrderedGroup_ZF_3_L6
  by auto

text\<open>$|m-n| = |n-m|$.\<close>

lemma (in int0) Int_ZF_2_L20: assumes "m\<in>\<int>"  "n\<in>\<int>"
  shows "abs(m\<rs>n) = abs(n\<rs>m)"
  using assms Int_ZF_2_T1 group3.OrderedGroup_ZF_3_L7B by simp

text\<open>We can add the sides of inequalities with absolute values.\<close>

lemma (in int0) Int_ZF_2_L21: 
  assumes A1: "m\<in>\<int>" "n\<in>\<int>"
  and A2: "abs(m) \<lsq> k"  "abs(n) \<lsq> l"
  shows 
  "abs(m\<ra>n) \<lsq> k \<ra> l"
  "abs(m\<rs>n) \<lsq> k \<ra> l"
  using assms Int_ZF_1_T2 Int_ZF_2_T1 
    group3.OrderedGroup_ZF_3_L7C group3.OrderedGroup_ZF_3_L7CA
  by auto
  
text\<open>Absolute value is nonnegative.\<close>

lemma (in int0) int_abs_nonneg: assumes A1: "m\<in>\<int>"
  shows "abs(m) \<in> \<int>\<^sup>+"  "\<zero> \<lsq> abs(m)" 
proof -
  have "AbsoluteValue(\<int>,IntegerAddition,IntegerOrder) : \<int>\<rightarrow>\<int>\<^sup>+"
    using Int_ZF_2_T1 group3.OrderedGroup_ZF_3_L3C by simp
  with A1 show "abs(m) \<in> \<int>\<^sup>+" using apply_funtype
    by simp
  then show "\<zero> \<lsq> abs(m)" 
    using Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L2 by simp
qed

text\<open>If an nonnegative integer is less or equal than another,
  then so is its absolute value.\<close>

lemma (in int0) Int_ZF_2_L23: 
  assumes "\<zero>\<lsq>m"   "m\<lsq>k"
  shows "abs(m) \<lsq> k"
  using assms Int_ZF_2_L16 by simp(* this is probably not worth the effort*)

subsection\<open>Induction on integers.\<close>

text\<open>In this section we show some induction lemmas for integers. 
  The basic tools are the induction on natural numbers and the fact that
  integers can be written as a sum of a smaller integer and a natural number.
\<close>

text\<open>An integer can be written a a sum of a smaller integer and a natural 
  number.\<close>

lemma (in int0) Int_ZF_3_L2: assumes A1: "i \<lsq> m"
  shows "\<exists>n\<in>nat. m = i $+ $# n"
proof -
  let ?n = "0"
  { assume A2: "i=m"  
    from A1 A2 have "?n \<in> nat" "m = i $+ $# ?n"
      using Int_ZF_2_L1A zadd_int0_right by auto
    hence "\<exists>n\<in>nat. m = i $+ $# n" by blast }
  moreover
  { assume A3: "i\<noteq>m" 
    with A1 have "i $< m" "i\<in>\<int>" "m\<in>\<int>"   
      using Int_ZF_2_L9 Int_ZF_2_L1A by auto
    then obtain k where D1: "k\<in>nat" "m = i $+ $# succ(k)"
      using zless_imp_succ_zadd_lemma by auto
    let ?n = "succ(k)"
    from D1 have "?n\<in>nat" "m = i $+ $# ?n" by auto
    hence "\<exists>n\<in>nat. m = i $+ $# n" by simp }
  ultimately show ?thesis by blast
qed

text\<open>Induction for integers, the induction step.\<close>

lemma (in int0) Int_ZF_3_L6: assumes A1: "i\<in>\<int>" 
  and A2: "\<forall>m. i\<lsq>m \<and> Q(m) \<longrightarrow> Q(m $+ ($# 1))"
  shows "\<forall>k\<in>nat. Q(i $+ ($# k)) \<longrightarrow> Q(i $+ ($# succ(k)))"
proof
  fix k assume A3: "k\<in>nat" show "Q(i $+ $# k) \<longrightarrow> Q(i $+ $# succ(k))"
  proof
    assume A4: "Q(i $+ $# k)"
    from A1 A3 have "i\<lsq> i $+ ($# k)" using Int_ZF_2_L12
      by simp
    with A4 A2 have "Q(i $+ ($# k) $+ ($# 1))" by simp
    then show "Q(i $+ ($# succ(k)))" using Int_ZF_2_L11 by simp
  qed
qed

text\<open>Induction on integers, version with higher-order increment function.\<close>

lemma (in int0) Int_ZF_3_L7: 
  assumes A1: "i\<lsq>k" and A2: "Q(i)"
  and A3: "\<forall>m. i\<lsq>m \<and> Q(m) \<longrightarrow> Q(m $+ ($# 1))"
  shows "Q(k)"
proof -
  from A1 obtain n where D1: "n\<in>nat" and D2: "k = i $+ $# n"
    using Int_ZF_3_L2 by auto
  from A1 have T1: "i\<in>\<int>" using Int_ZF_2_L1A by simp
  note \<open>n\<in>nat\<close>
  moreover from A1 A2 have "Q(i $+ $#0)" 
    using Int_ZF_2_L1A zadd_int0 by simp
  moreover from T1 A3 have 
    "\<forall>k\<in>nat. Q(i $+ ($# k)) \<longrightarrow> Q(i $+ ($# succ(k)))"
    by (rule Int_ZF_3_L6)
  ultimately have "Q(i $+ ($# n))" by (rule ind_on_nat) 
  with D2 show "Q(k)" by simp
qed

text\<open>Induction on integer, implication between two forms of the induction
  step.\<close>

lemma (in int0) Int_ZF_3_L7A: assumes 
  A1: "\<forall>m. i\<lsq>m \<and> Q(m) \<longrightarrow> Q(m\<ra>\<one>)"
  shows "\<forall>m. i\<lsq>m \<and> Q(m) \<longrightarrow> Q(m $+ ($# 1))"
proof -
  { fix m assume "i\<lsq>m \<and> Q(m)" 
    with A1 have T1: "m\<in>\<int>" "Q(m\<ra>\<one>)" using Int_ZF_2_L1A by auto
    then have "m\<ra>\<one> = m\<ra>($# 1)" using Int_ZF_1_L8 by simp
    with T1 have "Q(m $+ ($# 1))" using Int_ZF_1_L2
      by simp
  } then show ?thesis by simp
qed

text\<open>Induction on integers, version with ZF increment function.\<close>

theorem (in int0) Induction_on_int: 
  assumes A1: "i\<lsq>k" and A2: "Q(i)"
  and A3: "\<forall>m. i\<lsq>m \<and> Q(m) \<longrightarrow> Q(m\<ra>\<one>)"
  shows "Q(k)"
proof -
  from A3 have "\<forall>m. i\<lsq>m \<and> Q(m) \<longrightarrow> Q(m $+ ($# 1))"
    by (rule Int_ZF_3_L7A)
  with A1 A2 show ?thesis by (rule Int_ZF_3_L7)
qed

text\<open>Another form of induction on integers. This rewrites the basic theorem 
   \<open>Int_ZF_3_L7\<close> substituting $P(-k)$ for $Q(k)$.\<close>

lemma (in int0) Int_ZF_3_L7B: assumes A1: "i\<lsq>k" and A2: "P($-i)"
  and A3: "\<forall>m. i\<lsq>m \<and> P($-m) \<longrightarrow> P($-(m $+ ($# 1)))"
  shows "P($-k)"
proof -
  from A1 A2 A3 show "P($-k)" by (rule Int_ZF_3_L7)
qed

text\<open>Another induction on integers. This rewrites Int\_ZF\_3\_L7
  substituting $-k$ for $k$ and $-i$ for $i$.\<close>

lemma (in int0) Int_ZF_3_L8: assumes A1: "k\<lsq>i" and A2: "P(i)" 
  and A3: "\<forall>m. $-i\<lsq>m \<and> P($-m) \<longrightarrow> P($-(m $+ ($# 1)))"
  shows "P(k)"
proof -
  from A1 have T1: "$-i\<lsq>$-k" using Int_ZF_2_L10 by simp
  from A1 A2 have T2: "P($- $- i)" using Int_ZF_2_L1A zminus_zminus
    by simp
  from T1 T2 A3 have "P($-($-k))" by (rule Int_ZF_3_L7)
  with A1 show "P(k)" using Int_ZF_2_L1A zminus_zminus by simp
qed

text\<open>An implication between two forms of induction steps.\<close>

lemma (in int0) Int_ZF_3_L9: assumes A1: "i\<in>\<int>"
  and A2: "\<forall>n. n\<lsq>i \<and> P(n) \<longrightarrow> P(n $+ $-($#1))"    
  shows "\<forall>m. $-i\<lsq>m \<and> P($-m) \<longrightarrow> P($-(m $+ ($# 1)))"
proof
  fix m show "$-i\<lsq>m \<and> P($-m) \<longrightarrow> P($-(m $+ ($# 1)))"
  proof
    assume A3: "$- i \<lsq> m \<and> P($- m)"
    then have "$- i \<lsq> m" by simp
    then have "$-m \<lsq> $- ($- i)" by (rule Int_ZF_2_L10)
    with A1 A2 A3 show "P($-(m $+ ($# 1)))"
      using zminus_zminus zminus_zadd_distrib by simp
  qed
qed

text\<open>Backwards induction on integers, version with higher-order decrement
  function.\<close>

lemma (in int0) Int_ZF_3_L9A: assumes A1: "k\<lsq>i" and A2: "P(i)" 
  and A3: "\<forall>n. n\<lsq>i \<and> P(n) \<longrightarrow>P(n $+ $-($#1)) "
  shows "P(k)"
proof -
  from A1 have T1: "i\<in>\<int>" using Int_ZF_2_L1A by simp
  from T1 A3 have T2: "\<forall>m. $-i\<lsq>m \<and> P($-m) \<longrightarrow> P($-(m $+ ($# 1)))"
    by (rule Int_ZF_3_L9)
  from A1 A2 T2 show "P(k)" by (rule Int_ZF_3_L8)
qed

text\<open>Induction on integers, implication between two forms of the induction
  step.\<close>

lemma (in int0) Int_ZF_3_L10: assumes
  A1: "\<forall>n. n\<lsq>i \<and> P(n) \<longrightarrow> P(n\<rs>\<one>)"
  shows "\<forall>n. n\<lsq>i \<and> P(n) \<longrightarrow> P(n $+ $-($#1))"
proof -
  { fix n assume "n\<lsq>i \<and> P(n)"
    with A1 have T1: "n\<in>\<int>" "P(n\<rs>\<one>)" using Int_ZF_2_L1A by auto
    then have "n\<rs>\<one> = n\<rs>($# 1)" using Int_ZF_1_L8 by simp
    with T1 have "P(n $+ $-($#1))" using Int_ZF_1_L10 by simp
  } then show ?thesis by simp
qed

text\<open>Backwards induction on integers.\<close>

theorem (in int0) Back_induct_on_int: 
  assumes A1: "k\<lsq>i" and A2: "P(i)" 
  and A3: "\<forall>n. n\<lsq>i \<and> P(n) \<longrightarrow> P(n\<rs>\<one>)"
  shows "P(k)"
proof -
  from A3 have "\<forall>n. n\<lsq>i \<and> P(n) \<longrightarrow> P(n $+ $-($#1))"
    by (rule Int_ZF_3_L10)
  with A1 A2 show "P(k)" by (rule Int_ZF_3_L9A)
qed
    
subsection\<open>Bounded vs. finite subsets of integers\<close>

text\<open>The goal of this section is to establish that a subset of integers 
  is bounded is and only is it is finite. The fact that all finite sets 
  are bounded is already shown for all linearly ordered groups in 
  \<open>OrderedGroups_ZF.thy\<close>. To show the other implication we
  show that all intervals starting at 0 are finite and then use a result from
  \<open>OrderedGroups_ZF.thy\<close>.\<close>

text\<open>There are no integers between $k$ and $k+1$.\<close>

lemma (in int0) Int_ZF_4_L1: 
  assumes A1: "k\<in>\<int>" "m\<in>\<int>" "n\<in>nat" and A2: "k $+ $#1 = m $+ $#n"
  shows "m =  k $+ $#1 \<or> m \<lsq> k"
proof -
  { assume "n=0" 
    with A1 A2 have "m =  k $+ $#1 \<or> m \<lsq> k" 
      using zadd_int0 by simp }
  moreover
  { assume "n\<noteq>0" 
    with A1 obtain j where D1: "j\<in>nat" "n = succ(j)"
      using Nat_ZF_1_L3 by auto
    with A1 A2 D1 have "m =  k $+ $#1 \<or> m \<lsq> k" 
      using Int_ZF_2_L13 by simp }
  ultimately show ?thesis by blast
qed

text\<open>A trivial calculation lemma that allows to subtract and add one.\<close>

lemma Int_ZF_4_L1A: 
  assumes "m\<in>int" shows "m $- $#1 $+ $#1 = m"
  using assms eq_zdiff_iff by auto

text\<open>There are no integers between $k$ and $k+1$, another formulation.\<close>

lemma (in int0) Int_ZF_4_L1B: assumes A1: "m \<lsq> L"
  shows 
  "m = L \<or> m\<ra>\<one> \<lsq> L"
  "m = L \<or> m \<lsq> L\<rs>\<one>" 
proof -
  let ?k = "L $- $#1"
  from A1 have T1: "m\<in>\<int>"  "L\<in>\<int>"  "L = ?k $+ $#1" 
    using Int_ZF_2_L1A Int_ZF_4_L1A by auto
  moreover from A1 obtain n where D1: "n\<in>nat"  "L = m $+ $# n"
    using Int_ZF_3_L2 by auto
  ultimately have "m = L \<or> m \<lsq> ?k"
    using Int_ZF_4_L1 by simp
  with T1 show "m = L   \<or>  m\<ra>\<one> \<lsq> L"
    using Int_ZF_2_L9A by auto
  with T1 show "m = L \<or> m \<lsq> L\<rs>\<one>"
    using Int_ZF_1_L8A Int_ZF_2_L9B by simp
qed

text\<open>If $j\in m..k+1$, then $j\in m..n$ or $j=k+1$.\<close>

lemma (in int0) Int_ZF_4_L2: assumes A1: "k\<in>\<int>"
  and A2: "j \<in> m..(k $+ $#1)"
  shows "j \<in> m..k \<or> j \<in> {k $+ $#1}"
proof -
  from A2 have T1: "m\<lsq>j" "j\<lsq>(k $+ $#1)" using Order_ZF_2_L1A 
    by auto
  then have T2: "m\<in>\<int>" "j\<in>\<int>" using Int_ZF_2_L1A by auto 
  from T1 obtain n where "n\<in>nat" "k $+ $#1 = j $+ $# n"
    using Int_ZF_3_L2 by auto
  with A1 T1 T2 have "(m\<lsq>j \<and> j \<lsq> k) \<or> j \<in> {k $+ $#1}"
    using Int_ZF_4_L1 by auto
  then show ?thesis using Order_ZF_2_L1B by auto
qed

text\<open>Extending an integer interval by one is the same as adding the new 
  endpoint.\<close>

lemma (in int0) Int_ZF_4_L3: assumes A1: "m\<lsq> k"
  shows "m..(k $+ $#1) = m..k \<union> {k $+ $#1}"
proof
  from A1 have T1: "m\<in>\<int>" "k\<in>\<int>" using Int_ZF_2_L1A by auto
  then show "m .. (k $+ $# 1) \<subseteq> m .. k \<union> {k $+ $# 1}"
    using Int_ZF_4_L2 by auto
  from T1 have "m\<lsq> m" using Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L3
    by simp
  with T1 A1 have "m .. k \<subseteq> m .. (k $+ $# 1)"
    using Int_ZF_2_L12 Int_ZF_2_L6 Order_ZF_2_L3 by simp
  with T1 A1 show "m..k \<union> {k $+ $#1} \<subseteq> m..(k $+ $#1)"
    using Int_ZF_2_L12A int_ord_is_refl Order_ZF_2_L2 by auto
qed

text\<open>Integer intervals are finite - induction step.\<close>

lemma (in int0) Int_ZF_4_L4: 
  assumes A1: "i\<lsq>m" and A2: "i..m \<in> Fin(\<int>)"
  shows "i..(m $+ $#1) \<in> Fin(\<int>)"
  using assms Int_ZF_4_L3 by simp

text\<open>Integer intervals are finite.\<close>

lemma (in int0) Int_ZF_4_L5: assumes A1: "i\<in>\<int>" "k\<in>\<int>"
  shows "i..k \<in> Fin(\<int>)"
proof -
  { assume A2: "i\<lsq>k"
    moreover from A1 have "i..i \<in> Fin(\<int>)"
      using int_ord_is_refl Int_ZF_2_L4 Order_ZF_2_L4 by simp
    moreover from A2 have 
      "\<forall>m. i\<lsq>m \<and> i..m \<in> Fin(\<int>) \<longrightarrow> i..(m $+ $#1) \<in> Fin(\<int>)"
      using Int_ZF_4_L4 by simp
    ultimately have "i..k \<in> Fin(\<int>)" by (rule Int_ZF_3_L7) }
  moreover 
  { assume "\<not> i \<lsq> k"
    then have "i..k \<in> Fin(\<int>)" using Int_ZF_2_L6 Order_ZF_2_L5
      by simp }
  ultimately show ?thesis by blast
qed

text\<open>Bounded integer sets are finite.\<close>

lemma (in int0) Int_ZF_4_L6: assumes A1: "IsBounded(A,IntegerOrder)"
  shows "A \<in> Fin(\<int>)"
proof -
  have T1: "\<forall>m \<in> Nonnegative(\<int>,IntegerAddition,IntegerOrder).
    $#0..m \<in> Fin(\<int>)" 
  proof
    fix m assume "m \<in> Nonnegative(\<int>,IntegerAddition,IntegerOrder)"
    then have "m\<in>\<int>" using Int_ZF_2_T1 group3.OrderedGroup_ZF_1_L4E
      by auto
    then show "$#0..m \<in> Fin(\<int>)" using Int_ZF_4_L5 by simp
  qed
  have "group3(\<int>,IntegerAddition,IntegerOrder)"
    using Int_ZF_2_T1 by simp
  moreover from T1 have "\<forall>m \<in> Nonnegative(\<int>,IntegerAddition,IntegerOrder).
    Interval(IntegerOrder,TheNeutralElement(\<int>,IntegerAddition),m) 
    \<in> Fin(\<int>)" using Int_ZF_1_L8 by simp
  moreover note A1
  ultimately show "A \<in> Fin(\<int>)" by (rule group3.OrderedGroup_ZF_2_T1)
qed

text\<open>A subset of integers is bounded iff it is finite.\<close>

theorem (in int0) Int_bounded_iff_fin: 
  shows "IsBounded(A,IntegerOrder)\<longleftrightarrow> A\<in>Fin(\<int>)"
  using Int_ZF_4_L6 Int_ZF_2_T1 group3.ord_group_fin_bounded 
  by blast

text\<open>The image of an interval by any integer function is
  finite, hence bounded.\<close>

lemma (in int0) Int_ZF_4_L8: 
  assumes A1: "i\<in>\<int>"  "k\<in>\<int>" and A2: "f:\<int>\<rightarrow>\<int>"
  shows 
  "f``(i..k) \<in> Fin(\<int>)"
  "IsBounded(f``(i..k),IntegerOrder)"
  using assms Int_ZF_4_L5 Finite1_L6A Int_bounded_iff_fin
  by auto

text\<open>If for every integer we can find one in $A$ that is greater or equal,
  then $A$ is is not bounded above, hence infinite.\<close>

lemma (in int0) Int_ZF_4_L9: assumes A1: "\<forall>m\<in>\<int>. \<exists>k\<in>A. m\<lsq>k"
  shows 
  "\<not>IsBoundedAbove(A,IntegerOrder)"
  "A \<notin> Fin(\<int>)"
proof -
  have "\<int> \<noteq> {\<zero>}"
    using Int_ZF_1_L8A int_zero_not_one by blast
  with A1 show 
    "\<not>IsBoundedAbove(A,IntegerOrder)"
    "A \<notin> Fin(\<int>)"
    using Int_ZF_2_T1 group3.OrderedGroup_ZF_2_L2A
    by auto
qed


end
