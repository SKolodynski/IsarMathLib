(*   This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2005 - 2008  Slawomir Kolodynski

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

section \<open>Order relations - introduction\<close>

theory Order_ZF imports Fol1

begin

text\<open>This theory file considers various notion related to order. We redefine
  the notions of a total order, linear order and partial order to have the 
  same terminology as Wikipedia (I found it very consistent across different 
  areas of math). We also define and study the notions of intervals and bounded
  sets. We show the inclusion relations between the intervals with endpoints
  being in certain order. We also show that union of bounded sets are bounded. 
  This allows to show in \<open>Finite_ZF.thy\<close> that finite sets are bounded.\<close>

subsection\<open>Definitions\<close>

text\<open>In this section we formulate the definitions related to order 
  relations.\<close>

text\<open>A relation $r$ is ''total'' on a set $X$ if for all elements 
  $a,b$ of $X$ we have $a$ is in relation with $b$ or $b$ is in relation
  with $a$. An example is the $\leq $ relation on numbers.
\<close>

definition
  IsTotal (infixl "{is total on}" 65) where
  "r {is total on} X \<equiv> (\<forall>a\<in>X.\<forall>b\<in>X. \<langle> a,b\<rangle> \<in> r \<or> \<langle> b,a\<rangle> \<in> r)"

text\<open>A relation $r$ is a partial order on $X$ if it is reflexive on $X$
  (i.e. $\langle x,x \rangle$ for every $x\in X$), antisymmetric 
  (if $\langle x, y\rangle \in r $ and $\langle y, x\rangle \in r $, then
  $x=y$) and transitive $\langle x, y\rangle \in r $ and 
  $\langle y, z\rangle \in r $ implies $\langle x, z\rangle \in r $). 
\<close>

definition
  "IsPartOrder(X,r) \<equiv> (refl(X,r) \<and> antisym(r) \<and> trans(r))"

text\<open>We define a linear order as a binary relation that is antisymmetric, 
  transitive and total. Note that this terminology is different than the
  one used the standard Order.thy file.\<close>

definition
  "IsLinOrder(X,r) \<equiv> ( antisym(r) \<and> trans(r) \<and> (r {is total on} X))"

text\<open>A set is bounded above if there is that is an upper
  bound for it,  i.e. there are some $u$ such that 
  $\langle x, u\rangle \in r$ for all $x\in A$. 
  In addition, the empty set is defined as bounded.\<close>

definition
  "IsBoundedAbove(A,r) \<equiv> ( A=0 \<or> (\<exists>u. \<forall>x\<in>A. \<langle> x,u\<rangle> \<in> r))"

text\<open>We define sets bounded below analogously.\<close>

definition
  "IsBoundedBelow(A,r) \<equiv> (A=0 \<or> (\<exists>l. \<forall>x\<in>A. \<langle> l,x\<rangle> \<in> r))"

text\<open>A set is bounded if it is bounded below and above.\<close>

definition
  "IsBounded(A,r) \<equiv> (IsBoundedAbove(A,r) \<and> IsBoundedBelow(A,r))"

text\<open>The notation for the definition of an interval may be mysterious for some
  readers, see lemma \<open>Order_ZF_2_L1\<close> for more intuitive notation.\<close>

definition
  "Interval(r,a,b) \<equiv> r``{a} \<inter> r-``{b}"

text\<open>We also define the maximum (the greater of) two elemnts 
  in the obvious way.\<close>

definition
  "GreaterOf(r,a,b) \<equiv> (if \<langle> a,b\<rangle> \<in> r then b else a)"

text\<open>The definition a a minimum (the smaller of) two elements.\<close>

definition
  "SmallerOf(r,a,b) \<equiv> (if \<langle> a,b\<rangle> \<in> r then a else b)"

text\<open>We say that a set has a maximum if it has an element that is 
  not smaller that any other one. We show that
  under some conditions this element of the set is unique (if exists).\<close>

definition
  "HasAmaximum(r,A) \<equiv> \<exists>M\<in>A.\<forall>x\<in>A. \<langle> x,M\<rangle> \<in> r"

text\<open>A similar definition what it means that a set has a minimum.\<close>

definition
  "HasAminimum(r,A) \<equiv> \<exists>m\<in>A.\<forall>x\<in>A. \<langle> m,x\<rangle> \<in> r"

text\<open>Definition of the maximum of a set.\<close>

definition
  "Maximum(r,A) \<equiv> THE M. M\<in>A \<and> (\<forall>x\<in>A. \<langle> x,M\<rangle> \<in> r)"

text\<open>Definition of a minimum of a set.\<close>

definition
  "Minimum(r,A) \<equiv> THE m. m\<in>A \<and> (\<forall>x\<in>A. \<langle> m,x\<rangle> \<in> r)"

text\<open>The supremum of a set $A$ is defined as the minimum of the set of
  upper bounds, i.e. the set 
  $\{u.\forall_{a\in A} \langle a,u\rangle \in r\}=\bigcap_{a\in A} r\{a\}$. 
   Recall that in Isabelle/ZF
  \<open>r-``(A)\<close> denotes the inverse image of the set $A$ by relation $r$
  (i.e. \<open>r-``(A)\<close>=$\{ x: \langle x,y\rangle\in r$ for some $y\in A\}$).\<close>

definition
  "Supremum(r,A) \<equiv> Minimum(r,\<Inter>a\<in>A. r``{a})"

text\<open>Infimum is defined analogously.\<close>

definition
  "Infimum(r,A) \<equiv> Maximum(r,\<Inter>a\<in>A. r-``{a})"

text\<open>We define a relation to be complete if every nonempty bounded
  above set has a supremum.\<close>

definition
  IsComplete ("_ {is complete}") where
  "r {is complete} \<equiv> 
  \<forall>A. IsBoundedAbove(A,r) \<and> A\<noteq>0 \<longrightarrow> HasAminimum(r,\<Inter>a\<in>A. r``{a})"

text\<open>The essential condition to show that a total relation is reflexive.\<close>

lemma Order_ZF_1_L1: assumes "r {is total on} X" and "a\<in>X"
  shows "\<langle>a,a\<rangle> \<in> r" using assms IsTotal_def by auto

text\<open>A total relation is reflexive.\<close>

lemma total_is_refl:
  assumes "r {is total on} X"
  shows "refl(X,r)" using assms Order_ZF_1_L1 refl_def by simp

text\<open>A linear order is partial order.\<close>

lemma Order_ZF_1_L2: assumes "IsLinOrder(X,r)" 
  shows "IsPartOrder(X,r)" 
  using assms IsLinOrder_def IsPartOrder_def refl_def Order_ZF_1_L1
  by auto

text\<open>Partial order that is total is linear.\<close>

lemma Order_ZF_1_L3: 
  assumes "IsPartOrder(X,r)" and "r {is total on} X"
  shows "IsLinOrder(X,r)"
  using assms IsPartOrder_def IsLinOrder_def
  by simp

text\<open>Relation that is total on a set is total on any subset.\<close>

lemma Order_ZF_1_L4: assumes "r {is total on} X" and "A\<subseteq>X"
  shows "r {is total on} A"
  using assms IsTotal_def by auto

text\<open>A linear relation is linear on any subset.\<close>

lemma ord_linear_subset: assumes  "IsLinOrder(X,r)" and "A\<subseteq>X"
  shows  "IsLinOrder(A,r)" 
  using assms IsLinOrder_def Order_ZF_1_L4 by blast

text\<open>If the relation is total, then every set is a union of those elements
  that are nongreater than a given one and nonsmaller than a given one.\<close>

lemma Order_ZF_1_L5: 
  assumes "r {is total on} X" and "A\<subseteq>X" and "a\<in>X"
  shows "A = {x\<in>A. \<langle>x,a\<rangle> \<in> r} \<union> {x\<in>A. \<langle>a,x\<rangle> \<in> r}"
  using assms IsTotal_def by auto

text\<open>A technical fact about reflexive relations.\<close>

lemma refl_add_point: 
  assumes "refl(X,r)" and "A \<subseteq> B \<union> {x}" and "B \<subseteq> X" and
  "x \<in> X" and "\<forall>y\<in>B. \<langle>y,x\<rangle> \<in> r"
  shows "\<forall>a\<in>A. \<langle>a,x\<rangle> \<in> r"
  using assms refl_def by auto
  
subsection\<open>Intervals\<close>

text\<open>In this section we discuss intervals.\<close>

text\<open>The next lemma explains the notation of the definition of an interval.\<close>

lemma Order_ZF_2_L1: 
  shows "x \<in> Interval(r,a,b) \<longleftrightarrow> \<langle> a,x\<rangle> \<in> r \<and> \<langle> x,b\<rangle> \<in> r"
  using Interval_def by auto

text\<open>Since there are some problems with applying the above lemma 
  (seems that simp and auto don't handle equivalence very well), we
  split \<open>Order_ZF_2_L1\<close> into two lemmas.\<close>

lemma Order_ZF_2_L1A: assumes "x \<in> Interval(r,a,b)"
  shows "\<langle> a,x\<rangle> \<in> r"  "\<langle> x,b\<rangle> \<in> r"
  using assms  Order_ZF_2_L1 by auto

text\<open>\<open>Order_ZF_2_L1\<close>, implication from right to left.\<close>

lemma Order_ZF_2_L1B: assumes "\<langle> a,x\<rangle> \<in> r"  "\<langle> x,b\<rangle> \<in> r"
  shows "x \<in> Interval(r,a,b)"
  using assms Order_ZF_2_L1 by simp

text\<open>If the relation is reflexive, the endpoints belong to the interval.\<close>

lemma Order_ZF_2_L2: assumes "refl(X,r)" 
  and "a\<in>X"  "b\<in>X" and "\<langle> a,b\<rangle> \<in> r"
  shows 
  "a \<in> Interval(r,a,b)"  
  "b \<in> Interval(r,a,b)"  
  using assms refl_def Order_ZF_2_L1 by auto

text\<open>Under the assumptions of \<open>Order_ZF_2_L2\<close>, the interval is 
  nonempty.\<close>

lemma Order_ZF_2_L2A: assumes "refl(X,r)" 
  and "a\<in>X"  "b\<in>X" and "\<langle> a,b\<rangle> \<in> r"
  shows "Interval(r,a,b) \<noteq> 0"
proof -
  from assms have "a \<in> Interval(r,a,b)"
    using Order_ZF_2_L2 by simp
  then show "Interval(r,a,b) \<noteq> 0" by auto
qed

text\<open>If $a,b,c,d$ are in this order, then $[b,c]\subseteq [a,d]$. We
  only need trasitivity for this to be true.\<close>

lemma Order_ZF_2_L3: 
  assumes A1: "trans(r)" and A2:"\<langle> a,b\<rangle>\<in>r"  "\<langle> b,c\<rangle>\<in>r"  "\<langle> c,d\<rangle>\<in>r"
shows "Interval(r,b,c) \<subseteq> Interval(r,a,d)"
proof
  fix x assume A3: "x \<in> Interval(r, b, c)"
  note A1
  moreover from A2 A3 have "\<langle> a,b\<rangle> \<in> r \<and> \<langle> b,x\<rangle> \<in> r" using Order_ZF_2_L1A
    by simp
  ultimately have T1: "\<langle> a,x\<rangle> \<in> r" by (rule Fol1_L3)
  note A1
  moreover from A2 A3 have "\<langle> x,c\<rangle> \<in> r \<and> \<langle> c,d\<rangle> \<in> r" using Order_ZF_2_L1A
    by simp
  ultimately have "\<langle> x,d\<rangle> \<in> r" by (rule Fol1_L3)
  with T1 show "x \<in> Interval(r,a,d)" using Order_ZF_2_L1B
    by simp
qed

text\<open>For reflexive and antisymmetric relations the interval with equal 
  endpoints consists only of that endpoint.\<close>

lemma Order_ZF_2_L4: 
  assumes A1: "refl(X,r)" and A2: "antisym(r)" and A3: "a\<in>X"
  shows "Interval(r,a,a) = {a}"
proof
  from A1 A3 have "\<langle> a,a\<rangle> \<in> r" using refl_def by simp
  with A1 A3 show "{a} \<subseteq> Interval(r,a,a)" using Order_ZF_2_L2 by simp
  from A2 show "Interval(r,a,a) \<subseteq> {a}" using Order_ZF_2_L1A Fol1_L4
    by fast
qed

text\<open>For transitive relations the endpoints have to be in the relation for
  the interval to be nonempty.\<close>

lemma Order_ZF_2_L5: assumes A1: "trans(r)" and A2: "\<langle> a,b\<rangle> \<notin> r"
  shows "Interval(r,a,b) = 0"
proof -
  { assume "Interval(r,a,b)\<noteq>0" then obtain x where "x \<in> Interval(r,a,b)"
    by auto
  with A1 A2 have False using Order_ZF_2_L1A Fol1_L3 by fast
  } thus ?thesis by auto
qed

text\<open>If a relation is defined on a set, then intervals are subsets of that
  set.\<close>

lemma Order_ZF_2_L6: assumes A1: "r \<subseteq> X\<times>X"
  shows "Interval(r,a,b) \<subseteq> X"
  using assms Interval_def by auto

subsection\<open>Bounded sets\<close>

text\<open>In this section we consider properties of bounded sets.\<close>

text\<open>For reflexive relations singletons are bounded.\<close>

lemma Order_ZF_3_L1: assumes "refl(X,r)" and "a\<in>X"
  shows "IsBounded({a},r)"
  using assms refl_def IsBoundedAbove_def IsBoundedBelow_def
    IsBounded_def by auto

text\<open>Sets that are bounded above are contained in the domain of 
  the relation.\<close>

lemma Order_ZF_3_L1A: assumes "r \<subseteq> X\<times>X" 
  and "IsBoundedAbove(A,r)"
  shows "A\<subseteq>X" using assms IsBoundedAbove_def by auto

text\<open>Sets that are bounded below are contained in the domain of 
  the relation.\<close>

lemma Order_ZF_3_L1B: assumes "r \<subseteq> X\<times>X" 
  and "IsBoundedBelow(A,r)"
  shows "A\<subseteq>X" using assms IsBoundedBelow_def by auto

text\<open>For a total relation, the greater of two elements, 
  as defined above, is indeed greater of any of the two.\<close>

lemma Order_ZF_3_L2: assumes "r {is total on} X"
  and "x\<in>X" "y\<in>X"
  shows 
  "\<langle>x,GreaterOf(r,x,y)\<rangle> \<in> r" 
  "\<langle>y,GreaterOf(r,x,y)\<rangle> \<in> r"
  "\<langle>SmallerOf(r,x,y),x\<rangle> \<in> r" 
  "\<langle>SmallerOf(r,x,y),y\<rangle> \<in> r"
  using assms IsTotal_def Order_ZF_1_L1 GreaterOf_def SmallerOf_def
  by auto

text\<open>If $A$ is bounded above by $u$, $B$ is bounded above by $w$,
  then $A\cup B$ is bounded above by the greater of $u,w$.\<close>

lemma Order_ZF_3_L2B:  
  assumes A1: "r {is total on} X" and A2: "trans(r)"
  and A3: "u\<in>X" "w\<in>X" 
  and A4: "\<forall>x\<in>A. \<langle> x,u\<rangle> \<in> r" "\<forall>x\<in>B. \<langle> x,w\<rangle> \<in> r"
  shows "\<forall>x\<in>A\<union>B. \<langle>x,GreaterOf(r,u,w)\<rangle> \<in> r"
proof
  let ?v = "GreaterOf(r,u,w)"
  from A1 A3 have T1: "\<langle> u,?v\<rangle> \<in> r" and T2: "\<langle> w,?v\<rangle> \<in> r"
    using Order_ZF_3_L2 by auto
  fix x assume A5: "x\<in>A\<union>B" show "\<langle>x,?v\<rangle> \<in> r"
  proof -
    { assume "x\<in>A"
    with A4 T1 have "\<langle> x,u\<rangle> \<in> r \<and> \<langle> u,?v\<rangle> \<in> r" by simp
    with A2 have "\<langle>x,?v\<rangle> \<in> r" by (rule Fol1_L3) }
  moreover
  { assume "x\<notin>A" 
    with A5 A4 T2 have "\<langle> x,w\<rangle> \<in> r \<and> \<langle> w,?v\<rangle> \<in> r" by simp
    with A2 have "\<langle>x,?v\<rangle> \<in> r" by (rule Fol1_L3) }
  ultimately show ?thesis by auto
  qed
qed

text\<open>For total and transitive relation the union of two sets bounded 
  above is bounded above.\<close>

lemma Order_ZF_3_L3: 
  assumes A1: "r {is total on} X" and A2: "trans(r)"
  and A3: "IsBoundedAbove(A,r)" "IsBoundedAbove(B,r)"
  and A4: "r \<subseteq> X\<times>X"
  shows "IsBoundedAbove(A\<union>B,r)"
proof -
  { assume "A=0 \<or> B=0" 
    with A3 have "IsBoundedAbove(A\<union>B,r)" by auto }
  moreover
  { assume "\<not> (A = 0 \<or> B = 0)"
    then have T1: "A\<noteq>0" "B\<noteq>0" by auto
    with A3 obtain u w where D1: "\<forall>x\<in>A. \<langle> x,u\<rangle> \<in> r" "\<forall>x\<in>B. \<langle> x,w\<rangle> \<in> r"
      using IsBoundedAbove_def by auto
    let ?U = "GreaterOf(r,u,w)"
    from T1 A4 D1 have "u\<in>X" "w\<in>X" by auto
    with A1 A2 D1 have "\<forall>x\<in>A\<union>B.\<langle> x,?U\<rangle> \<in> r"
      using Order_ZF_3_L2B by blast
    then have "IsBoundedAbove(A\<union>B,r)"
      using IsBoundedAbove_def by auto }
  ultimately show ?thesis by auto
qed
  
text\<open>For total and transitive relations if a set $A$ is bounded above then 
  $A\cup \{a\}$ is bounded above.\<close>

lemma Order_ZF_3_L4: 
  assumes A1: "r {is total on} X" and A2: "trans(r)"
  and A3: "IsBoundedAbove(A,r)" and A4: "a\<in>X" and A5: "r \<subseteq> X\<times>X"
  shows "IsBoundedAbove(A\<union>{a},r)"
proof -
  from A1 have "refl(X,r)"
    using total_is_refl by simp
  with assms show ?thesis using
    Order_ZF_3_L1 IsBounded_def Order_ZF_3_L3 by simp
qed

text\<open>If $A$ is bounded below by $l$, $B$ is bounded below by $m$,
  then $A\cup B$ is bounded below by the smaller of $u,w$.\<close>

lemma Order_ZF_3_L5B:  
  assumes A1: "r {is total on} X" and A2: "trans(r)"
  and A3: "l\<in>X" "m\<in>X" 
  and A4: "\<forall>x\<in>A. \<langle> l,x\<rangle> \<in> r" "\<forall>x\<in>B. \<langle> m,x\<rangle> \<in> r"
  shows "\<forall>x\<in>A\<union>B. \<langle>SmallerOf(r,l,m),x\<rangle> \<in> r"
proof
  let ?k = "SmallerOf(r,l,m)"
  from A1 A3 have T1: "\<langle> ?k,l\<rangle> \<in> r" and T2: "\<langle> ?k,m\<rangle> \<in> r"
    using Order_ZF_3_L2 by auto
  fix x assume A5: "x\<in>A\<union>B" show "\<langle>?k,x\<rangle> \<in> r"
  proof -
    { assume "x\<in>A"
      with A4 T1 have "\<langle> ?k,l\<rangle> \<in> r \<and> \<langle> l,x\<rangle> \<in> r" by simp
      with A2 have "\<langle>?k,x\<rangle> \<in> r" by (rule Fol1_L3) }
    moreover
    { assume "x\<notin>A" 
      with A5 A4 T2 have "\<langle> ?k,m\<rangle> \<in> r \<and> \<langle> m,x\<rangle> \<in> r" by simp
      with A2 have "\<langle>?k,x\<rangle> \<in> r" by (rule Fol1_L3) }
    ultimately show ?thesis by auto
  qed
qed

text\<open>For total and transitive relation the union of two sets bounded 
  below is bounded below.\<close>

lemma Order_ZF_3_L6: 
  assumes A1: "r {is total on} X" and A2: "trans(r)"
  and A3: "IsBoundedBelow(A,r)" "IsBoundedBelow(B,r)"
  and A4: "r \<subseteq> X\<times>X"
  shows "IsBoundedBelow(A\<union>B,r)"
proof -
  { assume "A=0 \<or> B=0" 
    with A3 have ?thesis by auto }
  moreover
  { assume "\<not> (A = 0 \<or> B = 0)"
    then have T1: "A\<noteq>0" "B\<noteq>0" by auto
    with A3 obtain l m where D1: "\<forall>x\<in>A. \<langle> l,x\<rangle> \<in> r" "\<forall>x\<in>B. \<langle> m,x\<rangle> \<in> r"
      using IsBoundedBelow_def by auto
    let ?L = "SmallerOf(r,l,m)"
    from T1 A4 D1 have T1: "l\<in>X" "m\<in>X" by auto
    with A1 A2 D1 have "\<forall>x\<in>A\<union>B.\<langle> ?L,x\<rangle> \<in> r"
      using Order_ZF_3_L5B by blast
    then have "IsBoundedBelow(A\<union>B,r)"
      using IsBoundedBelow_def by auto }
  ultimately show ?thesis by auto
qed

text\<open>For total and transitive relations if a set $A$ is bounded below then 
  $A\cup \{a\}$ is bounded below.\<close>

lemma Order_ZF_3_L7:
  assumes A1: "r {is total on} X" and A2: "trans(r)"
  and A3: "IsBoundedBelow(A,r)" and A4: "a\<in>X" and A5: "r \<subseteq> X\<times>X"
  shows "IsBoundedBelow(A\<union>{a},r)"
proof -
  from A1 have "refl(X,r)"
    using total_is_refl by simp
  with assms show ?thesis using
    Order_ZF_3_L1 IsBounded_def Order_ZF_3_L6 by simp
qed

text\<open>For total and transitive relations unions of two bounded sets are 
  bounded.\<close>

theorem Order_ZF_3_T1: 
  assumes "r {is total on} X" and "trans(r)" 
  and "IsBounded(A,r)" "IsBounded(B,r)"
  and "r \<subseteq> X\<times>X"
  shows "IsBounded(A\<union>B,r)"
  using assms Order_ZF_3_L3 Order_ZF_3_L6 Order_ZF_3_L7 IsBounded_def
  by simp

text\<open>For total and transitive relations if a set $A$ is bounded then 
  $A\cup \{a\}$ is bounded.\<close>

lemma Order_ZF_3_L8: 
  assumes "r {is total on} X" and "trans(r)"
  and "IsBounded(A,r)" and "a\<in>X" and "r \<subseteq> X\<times>X"
  shows "IsBounded(A\<union>{a},r)"
  using assms total_is_refl Order_ZF_3_L1 Order_ZF_3_T1 by blast

text\<open>A sufficient condition for a set to be bounded below.\<close>

lemma Order_ZF_3_L9: assumes A1: "\<forall>a\<in>A. \<langle>l,a\<rangle> \<in> r"
  shows "IsBoundedBelow(A,r)"
proof -
  from A1 have "\<exists>l. \<forall>x\<in>A. \<langle>l,x\<rangle> \<in> r"
    by auto
  then show "IsBoundedBelow(A,r)"
    using IsBoundedBelow_def by simp
qed

text\<open>A sufficient condition for a set to be bounded above.\<close>

lemma Order_ZF_3_L10: assumes A1: "\<forall>a\<in>A. \<langle>a,u\<rangle> \<in> r"
  shows "IsBoundedAbove(A,r)"
proof -
  from A1 have "\<exists>u. \<forall>x\<in>A. \<langle>x,u\<rangle> \<in> r"
    by auto
  then show "IsBoundedAbove(A,r)"
    using IsBoundedAbove_def by simp
qed

text\<open>Intervals are bounded.\<close>
(*proof that uses Order_ZF_3_L9 and Order_ZF_3_L10 and is not shorter *)
lemma Order_ZF_3_L11: shows 
  "IsBoundedAbove(Interval(r,a,b),r)"
  "IsBoundedBelow(Interval(r,a,b),r)"
  "IsBounded(Interval(r,a,b),r)"
proof -
  { fix x assume "x \<in> Interval(r,a,b)" 
    then have "\<langle> x,b\<rangle> \<in> r"  "\<langle> a,x\<rangle> \<in> r" 
      using Order_ZF_2_L1A by auto
  } then have 
      "\<exists>u. \<forall>x\<in>Interval(r,a,b). \<langle> x,u\<rangle> \<in> r" 
      "\<exists>l. \<forall>x\<in>Interval(r,a,b). \<langle> l,x\<rangle> \<in> r"
    by auto
  then show 
    "IsBoundedAbove(Interval(r,a,b),r)"
    "IsBoundedBelow(Interval(r,a,b),r)"
    "IsBounded(Interval(r,a,b),r)"
    using IsBoundedAbove_def IsBoundedBelow_def IsBounded_def
    by auto
qed

text\<open>A subset of a set that is bounded below is bounded below.\<close>

lemma Order_ZF_3_L12: assumes A1: "IsBoundedBelow(A,r)" and A2: "B\<subseteq>A"
  shows "IsBoundedBelow(B,r)"
proof -
  { assume "A = 0"
    with assms have "IsBoundedBelow(B,r)" 
      using IsBoundedBelow_def by auto }
  moreover
  { assume "A \<noteq> 0"
    with A1 have "\<exists>l. \<forall>x\<in>A. \<langle>l,x\<rangle> \<in> r"
      using IsBoundedBelow_def by simp
    with A2 have "\<exists>l.\<forall>x\<in>B. \<langle>l,x\<rangle> \<in> r" by auto
    then have "IsBoundedBelow(B,r)" using IsBoundedBelow_def
      by auto }
  ultimately show "IsBoundedBelow(B,r)" by auto
qed

text\<open>A subset of a set that is bounded above is bounded above.\<close>

lemma Order_ZF_3_L13: assumes A1: "IsBoundedAbove(A,r)" and A2: "B\<subseteq>A"
  shows "IsBoundedAbove(B,r)"
proof -
  { assume "A = 0"
    with assms have "IsBoundedAbove(B,r)" 
      using IsBoundedAbove_def by auto }
  moreover
  { assume "A \<noteq> 0"
    with A1 have "\<exists>u. \<forall>x\<in>A. \<langle>x,u\<rangle> \<in> r"
      using IsBoundedAbove_def by simp
    with A2 have "\<exists>u.\<forall>x\<in>B. \<langle>x,u\<rangle> \<in> r" by auto
    then have "IsBoundedAbove(B,r)" using IsBoundedAbove_def
      by auto }
  ultimately show "IsBoundedAbove(B,r)" by auto
qed

text\<open>If for every element of $X$ we can find one in $A$ 
  that is greater, then the $A$ can not be bounded above.
  Works for relations that are total, transitive and antisymmetric,
  (i.e. for linear order relations).\<close>

lemma Order_ZF_3_L14:  
  assumes A1: "r {is total on} X" 
  and A2: "trans(r)" and A3: "antisym(r)"
  and A4: "r \<subseteq> X\<times>X" and A5: "X\<noteq>0" 
  and A6: "\<forall>x\<in>X. \<exists>a\<in>A. x\<noteq>a \<and> \<langle>x,a\<rangle> \<in> r"
  shows "\<not>IsBoundedAbove(A,r)"
proof -
  { from A5 A6 have I: "A\<noteq>0" by auto
    moreover assume "IsBoundedAbove(A,r)"
    ultimately obtain u where II: "\<forall>x\<in>A. \<langle> x,u\<rangle> \<in> r"
      using IsBounded_def IsBoundedAbove_def by auto
    with A4 I have "u\<in>X" by auto
    with A6 obtain b where "b\<in>A" and III: "u\<noteq>b" and "\<langle>u,b\<rangle> \<in> r"
      by auto
    with II have "\<langle>b,u\<rangle> \<in> r"  "\<langle>u,b\<rangle> \<in> r" by auto
    with A3 have "b=u" by (rule Fol1_L4)
    with III have False by simp
  } thus "\<not>IsBoundedAbove(A,r)" by auto
qed

text\<open>The set of elements in a set $A$ that are nongreater than 
  a given element is bounded above.\<close>

lemma Order_ZF_3_L15: shows "IsBoundedAbove({x\<in>A. \<langle>x,a\<rangle> \<in> r},r)"
  using IsBoundedAbove_def by auto

text\<open>If $A$ is bounded below, then the set of elements in a set $A$ 
  that are nongreater than a given element is bounded.\<close>

lemma Order_ZF_3_L16: assumes A1: "IsBoundedBelow(A,r)"
  shows "IsBounded({x\<in>A. \<langle>x,a\<rangle> \<in> r},r)"
proof -
  { assume "A=0" 
    then have "IsBounded({x\<in>A. \<langle>x,a\<rangle> \<in> r},r)"
      using IsBoundedBelow_def IsBoundedAbove_def IsBounded_def
      by auto }
  moreover
  { assume "A\<noteq>0"
    with A1 obtain l where I: "\<forall>x\<in>A. \<langle>l,x\<rangle> \<in> r"
      using IsBoundedBelow_def by auto
    then have "\<forall>y\<in>{x\<in>A. \<langle>x,a\<rangle> \<in> r}. \<langle>l,y\<rangle> \<in> r" by simp
    then have "IsBoundedBelow({x\<in>A. \<langle>x,a\<rangle> \<in> r},r)"
      by (rule Order_ZF_3_L9)
    then have "IsBounded({x\<in>A. \<langle>x,a\<rangle> \<in> r},r)" 
      using Order_ZF_3_L15 IsBounded_def by simp }
  ultimately show ?thesis by blast
qed

end
