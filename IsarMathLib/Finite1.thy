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

section \<open>Finite sets\<close>

theory Finite1 imports ZF.EquivClass ZF.Finite func1 ZF1

begin

text\<open>This theory extends Isabelle standard \<open>Finite\<close> theory.
  It is obsolete and should not be used for new development.
  Use the \<open>Finite_ZF\<close> instead.\<close>

subsection\<open>Finite powerset\<close>

text\<open>In this section we consider various properties of \<open>Fin\<close>
  datatype (even though there are no datatypes in ZF set theory).\<close>

(*text{*Intersection of a collection is contained in every element 
of the collection.*}
lemma ZF11: assumes A: "A \<in> M" shows "\<Inter>M \<subseteq> A";
proof
  fix x;
  assume A1: "x \<in> \<Inter>M"
  from A1 A show "x \<in> A" ..
qed;

text{*Intersection of a nonempty collection $M$ of subsets of 
  $X$ is a subset of $X$. *}

lemma ZF12: assumes A1: "\<forall>A\<in> M. A\<subseteq>X" and A2:"M\<noteq>0" 
  shows "(\<Inter> M) \<subseteq> X";
proof -;
 from A2 have "\<forall> A\<in> M. (\<Inter> M \<subseteq> A)" using ZF11 by simp;
 with A1 A2 show  "(\<Inter> M) \<subseteq> X" by fast;
qed; *)


text\<open>In \<open>Topology_ZF\<close> theory we consider 
  induced topology that is 
  obtained by taking a subset of a topological space. To show that a topology 
  restricted to a subset is also a topology 
  on that subset we may need a fact that 
  if $T$ is a collection of sets and $A$ is a set then every finite collection
  $\{ V_i \}$ is of the form $V_i=U_i \cap A$, where $\{U_i\}$ is a finite 
  subcollection of $T$. This is one of those trivial 
  facts that require suprisingly 
  long formal proof. 
  Actually, the need for this fact is avoided by requiring intersection 
  two open sets to be open (rather than intersection of 
  a finite number of open sets). 
  Still, the fact is left here as an example of a proof by induction.
  We will use \<open>Fin_induct\<close> lemma from Finite.thy. 
  First we define a property of
  finite sets that we want to show.\<close>

definition
  "Prfin(T,A,M) \<equiv> ( (M = 0) | (\<exists>N\<in> Fin(T). \<forall>V\<in> M. \<exists> U\<in> N. (V = U\<inter>A)))"

text\<open>Now we show the main induction step in a separate lemma. This will make 
  the proof of the theorem FinRestr below look short and nice. 
  The premises of the \<open>ind_step\<close> lemma are those needed by 
  the main induction step in 
  lemma \<open>Fin_induct\<close> (see standard Isabelle's Finite.thy).\<close>

lemma ind_step: assumes  A: "\<forall> V\<in> TA. \<exists> U\<in>T. V=U\<inter>A" 
  and A1: "W\<in>TA" and A2: "M\<in> Fin(TA)" 
  and A3: "W\<notin>M" and A4: "Prfin(T,A,M)" 
  shows "Prfin(T,A,cons(W,M))"
proof -
  { assume A7: "M=0" have "Prfin(T, A, cons(W, M))"
    proof-
      from A1 A obtain U where A5: "U\<in>T" and A6: "W=U\<inter>A" by fast
      let ?N = "{U}"
      from A5 have T1: "?N \<in> Fin(T)" by simp
      from A7 A6 have T2: "\<forall>V\<in> cons(W,M). \<exists> U\<in>?N. V=U\<inter>A" by simp
      from A7 T1 T2 show  "Prfin(T, A, cons(W, M))" 
	using Prfin_def by auto   
    qed }
  moreover
  { assume A8:"M\<noteq>0" have "Prfin(T, A, cons(W, M))"
    proof-
      from A1 A obtain U where A5: "U\<in>T" and A6:"W=U\<inter>A" by fast
      from A8 A4 obtain N0 
	where A9: "N0\<in> Fin(T)" and A10: "\<forall>V\<in> M. \<exists> U0\<in> N0. (V = U0\<inter>A)" 
	using Prfin_def by auto
      let ?N = "cons(U,N0)"
      from A5 A9 have "?N \<in> Fin(T)" by simp
      moreover from A10 A6 have "\<forall>V\<in> cons(W,M). \<exists> U\<in>?N. V=U\<inter>A" by simp
      ultimately have "\<exists> N\<in> Fin(T).\<forall>V\<in> cons(W,M). \<exists> U\<in>N. V=U\<inter>A" by auto
      with A8 show "Prfin(T, A, cons(W, M))" 
	using Prfin_def by simp
    qed }
  ultimately show ?thesis by auto 
qed

text\<open>Now we are ready to prove the statement we need.\<close>

theorem FinRestr0: assumes A: "\<forall> V \<in> TA. \<exists> U\<in> T. V=U\<inter>A"
  shows "\<forall> M\<in> Fin(TA). Prfin(T,A,M)"
proof -
  { fix M
    assume "M \<in> Fin(TA)"
    moreover have "Prfin(T,A,0)" using Prfin_def by simp
    moreover
    { fix W M assume "W\<in>TA" "M\<in> Fin(TA)" "W\<notin>M" "Prfin(T,A,M)"
      with A have "Prfin(T,A,cons(W,M))" by (rule ind_step) }
    ultimately have "Prfin(T,A,M)" by (rule Fin_induct)
  } thus ?thesis by simp
qed

text\<open>This is a different form of the above theorem:\<close>

theorem ZF1FinRestr: 
  assumes A1:"M\<in> Fin(TA)" and A2: "M\<noteq>0" 
  and A3: "\<forall> V\<in> TA. \<exists> U\<in> T. V=U\<inter>A"
  shows "\<exists>N\<in> Fin(T). (\<forall>V\<in> M. \<exists> U\<in> N. (V = U\<inter>A)) \<and> N\<noteq>0"
proof -
  from A3 A1 have "Prfin(T,A,M)" using FinRestr0 by blast
  then have "\<exists>N\<in> Fin(T). \<forall>V\<in> M. \<exists> U\<in> N. (V = U\<inter>A)" 
    using A2 Prfin_def by simp
  then obtain N where 
    D1:"N\<in> Fin(T) \<and> (\<forall>V\<in> M. \<exists> U\<in> N. (V = U\<inter>A))" by auto
  with A2 have "N\<noteq>0" by auto
  with D1 show ?thesis by auto
qed

text\<open>Purely technical lemma used in \<open>Topology_ZF_1\<close> to show 
  that if a topology is $T_2$, then it is $T_1$.\<close>

lemma Finite1_L2: 
  assumes A:"\<exists>U V. (U\<in>T \<and> V\<in>T \<and> x\<in>U \<and> y\<in>V \<and> U\<inter>V=0)"
  shows "\<exists>U\<in>T. (x\<in>U \<and> y\<notin>U)"
proof -
  from A obtain U V where D1:"U\<in>T \<and> V\<in>T \<and> x\<in>U \<and> y\<in>V \<and> U\<inter>V=0" by auto
  with D1 show ?thesis by auto
qed

text\<open>A collection closed with respect to taking a union of two sets 
  is closed under taking finite unions. Proof by induction with 
  the induction step formulated in a separate lemma.\<close>

lemma Finite1_L3_IndStep: 
  assumes A1:"\<forall>A B. ((A\<in>C \<and> B\<in>C) \<longrightarrow> A\<union>B\<in>C)" 
  and A2: "A\<in>C" and A3: "N\<in>Fin(C)" and A4:"A\<notin>N" and A5:"\<Union>N \<in> C" 
  shows "\<Union>cons(A,N) \<in> C"
proof -
  have "\<Union> cons(A,N) = A\<union> \<Union>N" by blast
  with A1 A2 A5 show ?thesis by simp
qed

text\<open>The lemma: a collection closed with respect to taking a union of two sets 
  is closed under taking finite unions.\<close>

lemma Finite1_L3:
  assumes A1: "0 \<in> C" and A2: "\<forall>A B. ((A\<in>C \<and> B\<in>C) \<longrightarrow> A\<union>B\<in>C)" and 
  A3: "N\<in> Fin(C)"
  shows "\<Union>N\<in>C"
proof -
  note A3
  moreover from A1 have "\<Union>0 \<in> C" by simp
  moreover 
  { fix A N 
    assume "A\<in>C" "N\<in>Fin(C)" "A\<notin>N" "\<Union>N \<in> C" 
    with A2 have "\<Union>cons(A,N) \<in> C" by (rule Finite1_L3_IndStep) } 
  ultimately show "\<Union>N\<in> C" by (rule Fin_induct)
qed

text\<open>A collection closed with respect to taking a intersection of two sets 
  is closed under taking finite intersections. 
  Proof by induction with 
  the induction step formulated in a separate lemma. This is sligltly more 
  involved than the union case in \<open>Finite1_L3\<close>, because the intersection
  of empty collection is undefined (or should be treated as such). 
  To simplify notation we define the property to be proven for finite sets 
  as a separate notion.
\<close>

definition
  "IntPr(T,N) \<equiv> (N = 0 | \<Inter>N \<in> T)"

text\<open>The induction step.\<close>

lemma Finite1_L4_IndStep:
  assumes A1: "\<forall>A B. ((A\<in>T \<and> B\<in>T) \<longrightarrow> A\<inter>B\<in>T)"
  and A2: "A\<in>T" and A3:"N\<in>Fin(T)" and A4:"A\<notin>N" and A5:"IntPr(T,N)"
  shows "IntPr(T,cons(A,N))"
proof -
  { assume A6: "N=0" 
    with A2 have "IntPr(T,cons(A,N))"
      using IntPr_def by simp }
  moreover
  { assume A7: "N\<noteq>0" have "IntPr(T, cons(A, N))"
    proof -
      from A7 A5 A2 A1 have "\<Inter>N \<inter> A \<in> T" using IntPr_def by simp
      moreover from A7 have "\<Inter>cons(A, N) = \<Inter>N \<inter> A" by auto
      ultimately show "IntPr(T, cons(A, N))" using IntPr_def by simp
    qed }
  ultimately show ?thesis by auto
qed

text\<open>The lemma.\<close>

lemma Finite1_L4:  
  assumes A1: "\<forall>A B. A\<in>T \<and> B\<in>T \<longrightarrow> A\<inter>B \<in> T"
  and A2: "N\<in>Fin(T)"
  shows "IntPr(T,N)"
proof -
  note A2
  moreover have "IntPr(T,0)" using IntPr_def by simp
  moreover 
  { fix A N 
    assume "A\<in>T" "N\<in>Fin(T)" "A\<notin>N" "IntPr(T,N)"
    with A1 have  "IntPr(T,cons(A,N))" by (rule Finite1_L4_IndStep) }
  ultimately show "IntPr(T,N)" by (rule Fin_induct)
qed

text\<open>Next is a restatement of the above lemma that 
  does not depend on the IntPr meta-function.\<close>

lemma Finite1_L5: 
  assumes A1: "\<forall>A B. ((A\<in>T \<and> B\<in>T) \<longrightarrow> A\<inter>B\<in>T)" 
  and A2: "N\<noteq>0" and A3: "N\<in>Fin(T)"
  shows "\<Inter>N \<in> T"
proof -
  from A1 A3 have "IntPr(T,N)" using Finite1_L4 by simp
  with A2 show ?thesis using IntPr_def by simp
qed

text\<open>The images of finite subsets by a meta-function are finite. 
  For example in topology if we have a finite collection of sets, then closing 
  each of them results in a finite collection of closed sets. This is a very 
  useful lemma with many unexpected applications.
  The proof is by induction. The next lemma is the induction step.\<close>

lemma fin_image_fin_IndStep: 
  assumes "\<forall>V\<in>B. K(V)\<in>C"
  and "U\<in>B" and "N\<in>Fin(B)" and "U\<notin>N" and "{K(V). V\<in>N}\<in>Fin(C)"
  shows "{K(V). V\<in>cons(U,N)} \<in> Fin(C)"
  using assms by simp

text\<open>The lemma:\<close>

lemma fin_image_fin: 
  assumes A1: "\<forall>V\<in>B. K(V)\<in>C" and A2: "N\<in>Fin(B)"
  shows "{K(V). V\<in>N} \<in> Fin(C)"
proof -
  note A2
  moreover have "{K(V). V\<in>0} \<in> Fin(C)" by simp
  moreover
  { fix U N
    assume "U\<in>B" "N\<in>Fin(B)" "U\<notin>N" "{K(V). V\<in>N}\<in>Fin(C)"
    with A1 have "{K(V). V\<in>cons(U,N)} \<in> Fin(C)"
      by (rule fin_image_fin_IndStep) }
  ultimately show ?thesis by (rule Fin_induct)
qed

text\<open>The image of a finite set is finite.\<close>

lemma Finite1_L6A: assumes A1: "f:X\<rightarrow>Y" and A2: "N \<in> Fin(X)"
  shows "f``(N) \<in> Fin(Y)"
proof -
  from A1 have "\<forall>x\<in>X. f`(x) \<in> Y" 
    using apply_type by simp
  moreover note A2
  ultimately have "{f`(x). x\<in>N} \<in> Fin(Y)"
    by (rule fin_image_fin)
  with A1 A2 show ?thesis
    using FinD func_imagedef by simp
qed

text\<open>If the set defined by a meta-function is finite, then every set 
  defined by a composition of this meta function with another one is finite.\<close>

lemma Finite1_L6B: 
  assumes A1: "\<forall>x\<in>X. a(x) \<in> Y" and A2: "{b(y).y\<in>Y} \<in> Fin(Z)"
  shows "{b(a(x)).x\<in>X} \<in> Fin(Z)"
proof -
  from A1 have "{b(a(x)).x\<in>X} \<subseteq> {b(y).y\<in>Y}" by auto
  with A2 show ?thesis using Fin_subset_lemma by blast
qed

text\<open>If the set defined by a meta-function is finite, then every set 
  defined by a composition of this meta function with another one is finite.\<close>

lemma Finite1_L6C: 
  assumes A1: "\<forall>y\<in>Y. b(y) \<in> Z" and A2: "{a(x). x\<in>X} \<in> Fin(Y)"
  shows "{b(a(x)).x\<in>X} \<in> Fin(Z)"
proof -
  let ?N = "{a(x). x\<in>X}"
  from A1 A2 have "{b(y). y \<in> ?N} \<in> Fin(Z)"
    by (rule fin_image_fin)
  moreover have "{b(a(x)). x\<in>X} = {b(y). y\<in> ?N}" 
    by auto
  ultimately show ?thesis by simp
qed

text\<open>If an intersection of a collection is not empty, then the collection is
  not empty. We are (ab)using the fact the the intesection of empty collection 
  is defined to be empty and prove by contradiction. Should be in ZF1.thy\<close>

lemma Finite1_L9: assumes A1:"\<Inter>A \<noteq> 0" shows "A\<noteq>0"
proof -
  { assume A2: "\<not> A \<noteq> 0" 
    with A1 have False by simp
  } thus ?thesis by auto 
qed

text\<open>Cartesian product of finite sets is finite.\<close>

lemma Finite1_L12: assumes A1: "A \<in> Fin(A)" and A2: "B \<in> Fin(B)"
  shows "A\<times>B \<in> Fin(A\<times>B)"
proof -
  have T1:"\<forall>a\<in>A. \<forall>b\<in>B. {\<langle> a,b\<rangle>} \<in> Fin(A\<times>B)" by simp
  have "\<forall>a\<in>A. {{\<langle> a,b\<rangle>}. b \<in> B} \<in> Fin(Fin(A\<times>B))"
  proof
    fix a assume A3: "a \<in> A"
    with T1 have "\<forall>b\<in>B. {\<langle> a,b\<rangle>} \<in> Fin(A\<times>B)" 
      by simp
    moreover note A2
    ultimately show "{{\<langle> a,b\<rangle>}. b \<in> B} \<in> Fin(Fin(A\<times>B))"
      by (rule fin_image_fin)
  qed
  then have "\<forall>a\<in>A. \<Union> {{\<langle> a,b\<rangle>}. b \<in> B} \<in> Fin(A\<times>B)"
    using Fin_UnionI by simp
  moreover have 
    "\<forall>a\<in>A. \<Union> {{\<langle> a,b\<rangle>}. b \<in> B} = {a}\<times> B" by blast
  ultimately have "\<forall>a\<in>A. {a}\<times> B \<in> Fin(A\<times>B)" by simp
  moreover note A1 
  ultimately have "{{a}\<times> B. a\<in>A} \<in> Fin(Fin(A\<times>B))"
    by (rule fin_image_fin)
  then have "\<Union>{{a}\<times> B. a\<in>A} \<in> Fin(A\<times>B)"
    using Fin_UnionI by simp
  moreover have "\<Union>{{a}\<times> B. a\<in>A} = A\<times>B" by blast
  ultimately show ?thesis by simp
qed

text\<open>We define the characterisic meta-function that is the identity
  on a set and assigns a default value everywhere else.\<close>

definition
  "Characteristic(A,default,x) \<equiv> (if x\<in>A then x else default)"

text\<open>A finite subset is a finite subset of itself.\<close>

lemma Finite1_L13: 
  assumes A1:"A \<in> Fin(X)" shows "A \<in> Fin(A)"
proof -
  { assume "A=0" hence "A \<in> Fin(A)" by simp }
  moreover
  { assume A2: "A\<noteq>0" then obtain c where D1:"c\<in>A" 
      by auto
    then have "\<forall>x\<in>X. Characteristic(A,c,x) \<in> A"
      using Characteristic_def by simp
    moreover note A1
    ultimately have 
      "{Characteristic(A,c,x). x\<in>A} \<in> Fin(A)" 
      by (rule fin_image_fin)
    moreover from D1 have 
      "{Characteristic(A,c,x). x\<in>A} = A"
      using Characteristic_def by simp
    ultimately have "A \<in> Fin(A)" by simp }
  ultimately show ?thesis by blast
qed

text\<open>Cartesian product of finite subsets is a finite subset of 
  cartesian product.\<close>

lemma Finite1_L14: assumes A1: "A \<in> Fin(X)" "B \<in> Fin(Y)"
  shows "A\<times>B \<in> Fin(X\<times>Y)"
proof -
  from A1 have "A\<times>B \<subseteq> X\<times>Y" using FinD by auto
  then have "Fin(A\<times>B) \<subseteq> Fin(X\<times>Y)" using Fin_mono by simp
  moreover from A1 have "A\<times>B \<in> Fin(A\<times>B)"
    using Finite1_L13 Finite1_L12 by simp
  ultimately show ?thesis by auto
qed

text\<open>The next lemma is needed in the \<open>Group_ZF_3\<close> theory in a 
  couple of places.\<close>

lemma Finite1_L15: 
  assumes A1: "{b(x). x\<in>A} \<in> Fin(B)"  "{c(x). x\<in>A} \<in> Fin(C)"
  and A2: "f : B\<times>C\<rightarrow>E"
  shows "{f`\<langle> b(x),c(x)\<rangle>. x\<in>A} \<in> Fin(E)"
proof -
  from A1 have "{b(x). x\<in>A}\<times>{c(x). x\<in>A} \<in> Fin(B\<times>C)"
    using Finite1_L14 by simp
  moreover have 
    "{\<langle> b(x),c(x)\<rangle>. x\<in>A} \<subseteq> {b(x). x\<in>A}\<times>{c(x). x\<in>A}" 
    by blast
  ultimately have T0: "{\<langle> b(x),c(x)\<rangle>. x\<in>A} \<in> Fin(B\<times>C)"
    by (rule Fin_subset_lemma)
  with A2 have T1: "f``{\<langle> b(x),c(x)\<rangle>. x\<in>A} \<in> Fin(E)"
    using Finite1_L6A by auto
  from T0 have "\<forall>x\<in>A. \<langle> b(x),c(x)\<rangle> \<in> B\<times>C"
    using FinD by auto
  with A2 have 
    "f``{\<langle> b(x),c(x)\<rangle>. x\<in>A} = {f`\<langle> b(x),c(x)\<rangle>. x\<in>A}"
    using func1_1_L17 by simp
  with T1 show ?thesis by simp
qed

text\<open>Singletons are in the finite powerset.\<close>

lemma Finite1_L16: assumes "x\<in>X" shows "{x} \<in> Fin(X)"
  using assms emptyI consI by simp

text\<open>A special case of \<open>Finite1_L15\<close> where the second
  set is a singleton. \<open>Group_ZF_3\<close> theory this corresponds 
  to the situation where we multiply by a constant.\<close>

lemma Finite1_L16AA: assumes "{b(x). x\<in>A} \<in> Fin(B)" 
  and "c\<in>C" and "f : B\<times>C\<rightarrow>E"
  shows "{f`\<langle> b(x),c\<rangle>. x\<in>A} \<in> Fin(E)"
proof -
  from assms have 
    "\<forall>y\<in>B. f`\<langle>y,c\<rangle> \<in> E"
    "{b(x). x\<in>A} \<in> Fin(B)"
    using apply_funtype by auto
  then show ?thesis by (rule Finite1_L6C)
qed

text\<open>First order version of the induction for the finite powerset.\<close>

lemma Finite1_L16B: assumes A1: "P(0)" and A2: "B\<in>Fin(X)"
  and A3: "\<forall>A\<in>Fin(X).\<forall>x\<in>X. x\<notin>A \<and> P(A)\<longrightarrow>P(A\<union>{x})"
  shows "P(B)"
proof -
  note \<open>B\<in>Fin(X)\<close> and \<open>P(0)\<close>
  moreover
  { fix A x
    assume  "x \<in> X"  "A \<in> Fin(X)"  "x \<notin> A"  "P(A)"
    moreover have "cons(x,A) = A\<union>{x}" by auto
    moreover note A3
    ultimately have "P(cons(x,A))" by simp }
  ultimately show  "P(B)" by (rule Fin_induct)
qed

subsection\<open>Finite range functions\<close>

text\<open>In this section we define functions 
  $f : X\rightarrow Y$, with the property that $f(X)$ is 
  a finite subset of $Y$. Such functions play a important
  role in the construction of real numbers in the \<open>Real_ZF\<close> series. 
\<close>

text\<open>Definition of finite range functions.\<close>

definition
  "FinRangeFunctions(X,Y) \<equiv> {f:X\<rightarrow>Y. f``(X) \<in> Fin(Y)}"

text\<open>Constant functions have finite range.\<close>

lemma Finite1_L17: assumes "c\<in>Y" and "X\<noteq>0"
  shows "ConstantFunction(X,c) \<in> FinRangeFunctions(X,Y)"
  using assms  func1_3_L1 func_imagedef func1_3_L2 Finite1_L16 
    FinRangeFunctions_def by simp

text\<open>Finite range functions have finite range.\<close>

lemma Finite1_L18: assumes "f \<in> FinRangeFunctions(X,Y)"
  shows "{f`(x). x\<in>X} \<in> Fin(Y)"
  using assms FinRangeFunctions_def func_imagedef by simp

text\<open>An alternative form of the definition of finite range functions.\<close>

lemma Finite1_L19: assumes "f:X\<rightarrow>Y"
  and "{f`(x). x\<in>X} \<in> Fin(Y)"
  shows "f \<in> FinRangeFunctions(X,Y)"
  using assms func_imagedef FinRangeFunctions_def by simp

text\<open>A composition of a finite range function with another function is 
  a finite range function.\<close>

lemma Finite1_L20: assumes A1:"f \<in> FinRangeFunctions(X,Y)"
  and A2: "g : Y\<rightarrow>Z"
  shows "g O f \<in> FinRangeFunctions(X,Z)"
proof - 
  from A1 A2 have "g``{f`(x). x\<in>X} \<in> Fin(Z)"
    using Finite1_L18 Finite1_L6A
    by simp
  with A1 A2 have "{(g O f)`(x). x\<in>X} \<in> Fin(Z)"
    using FinRangeFunctions_def apply_funtype 
      func1_1_L17 comp_fun_apply by auto
  with A1 A2 show ?thesis using 
    FinRangeFunctions_def comp_fun Finite1_L19
    by auto
qed

text\<open>Image of any subset of the domain of a finite range function is finite.\<close>

lemma Finite1_L21: 
  assumes "f \<in> FinRangeFunctions(X,Y)" and "A\<subseteq>X"
  shows "f``(A) \<in> Fin(Y)" 
proof -
  from assms have "f``(X) \<in> Fin(Y)"  "f``(A) \<subseteq> f``(X)"
    using FinRangeFunctions_def func1_1_L8
    by auto
  then show "f``(A) \<in> Fin(Y)" using Fin_subset_lemma
    by blast
qed
  
end