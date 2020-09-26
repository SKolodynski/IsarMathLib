(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2005-2008  Slawomir Kolodynski

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

section \<open>Equivalence relations\<close>

theory EquivClass1 imports ZF.EquivClass func_ZF ZF1

begin

text\<open>In this theory file we extend the  work on equivalence relations 
  done in the standard Isabelle's EquivClass theory. That development
  is very good and all, but we really would prefer an approach contained within
  the a standard ZF set theory, without extensions specific to Isabelle.
  That is why this theory is written.
\<close>

subsection\<open>Congruent functions and projections on the quotient\<close>

text\<open>Suppose we have a set $X$ with a relation 
  $r\subseteq X\times X$ and a function $f: X\rightarrow X$. 
  The function $f$ can be compatible (congruent) with $r$ in the sense that
  if two elements $x,y$ are related then the values $f(x), f(x)$ 
  are also related. This is especially useful if $r$ is an 
  equivalence relation as it allows to "project" the function
  to the quotient space $X/r$ (the set of equivalence classes of $r$)
  and create a new function $F$ that satifies the formula
  $F([x]_r) = [f(x)]_r$. When $f$ is congruent with respect 
  to $r$ such definition of the value of $F$ on the equivalence class
  $[x]_r$ does not depend on which $x$ we choose to represent the class.
  In this section we also consider binary operations that are congruent
  with respect to a relation. These are important in algebra - the
  congruency condition allows to project the operation 
  to obtain the operation on the quotient space. 
\<close>

text\<open>First we define the notion of function that maps equivalent 
  elements to equivalent values. We use similar names as
  in the Isabelle's standard \<open>EquivClass\<close> theory to indicate 
  the conceptual correspondence of the notions.\<close>

definition
  "Congruent(r,f) \<equiv>
  (\<forall>x y. \<langle>x,y\<rangle> \<in> r  \<longrightarrow> \<langle>f`(x),f`(y)\<rangle> \<in> r)"

text\<open>Now we will define the projection of
  a function onto the quotient space. In standard math the equivalence class
  of $x$ with respect to relation $r$ is usually denoted $[x]_r$. Here we reuse
  notation $r\{ x\}$ instead. This means the image of the set $\{ x\}$ 
  with respect to the relation, which, for equivalence relations is 
  exactly its equivalence class if you think about it.\<close>

definition
  "ProjFun(A,r,f) \<equiv>
  {\<langle>c,\<Union>x\<in>c. r``{f`(x)}\<rangle>. c \<in> (A//r)}"

text\<open>Elements of equivalence classes belong to the set.\<close>

lemma EquivClass_1_L1: 
  assumes A1: "equiv(A,r)" and A2: "C \<in> A//r" and A3: "x\<in>C"
  shows "x\<in>A"
proof -
  from A2 have "C \<subseteq> \<Union> (A//r)" by auto
  with A1 A3 show "x\<in>A"
    using Union_quotient by auto
qed

text\<open>The image of a subset of $X$ under projection is a subset
  of $A/r$.\<close>

lemma EquivClass_1_L1A: 
  assumes "A\<subseteq>X" shows "{r``{x}. x\<in>A} \<subseteq> X//r"
  using assms quotientI by auto

text\<open>If an element belongs to an equivalence class, then its image
  under relation is this equivalence class.\<close>

lemma EquivClass_1_L2: 
  assumes A1: "equiv(A,r)"  "C \<in> A//r" and A2: "x\<in>C"
  shows "r``{x} = C"
proof -
  from A1 A2 have "x \<in> r``{x}" 
    using EquivClass_1_L1  equiv_class_self by simp
  with A2 have I: "r``{x}\<inter>C \<noteq> 0" by auto
  from A1 A2 have "r``{x} \<in> A//r"
    using EquivClass_1_L1 quotientI by simp
  with A1 I show ?thesis
    using quotient_disj by blast
qed
      
text\<open>Elements that belong to the same equivalence class are equivalent.\<close>

lemma EquivClass_1_L2A:
  assumes "equiv(A,r)"  "C \<in> A//r"  "x\<in>C"  "y\<in>C"
  shows "\<langle>x,y\<rangle> \<in> r" 
  using assms EquivClass_1_L2 EquivClass_1_L1 equiv_class_eq_iff
  by simp

text\<open>Every $x$ is in the class of $y$, then they are equivalent.\<close>

lemma EquivClass_1_L2B: 
  assumes A1: "equiv(A,r)" and A2: "y\<in>A" and A3: "x \<in> r``{y}"
  shows "\<langle>x,y\<rangle> \<in> r"
proof -
  from A2 have  "r``{y} \<in> A//r"
    using quotientI by simp
  with A1 A3 show ?thesis using
    EquivClass_1_L1 equiv_class_self equiv_class_nondisjoint by blast
qed
  
text\<open>If a function is congruent then the equivalence classes of the values
  that come from the arguments from the same class are the same.\<close>

lemma EquivClass_1_L3: 
  assumes A1: "equiv(A,r)" and A2: "Congruent(r,f)" 
  and A3: "C \<in> A//r"  "x\<in>C"  "y\<in>C" 
  shows "r``{f`(x)} = r``{f`(y)}"
proof -
  from A1 A3 have "\<langle>x,y\<rangle> \<in> r"
    using EquivClass_1_L2A by simp
  with A2 have  "\<langle>f`(x),f`(y)\<rangle> \<in> r"
    using Congruent_def by simp
  with A1 show ?thesis using equiv_class_eq by simp
qed

text\<open>The values of congruent functions are in the space.\<close>

lemma EquivClass_1_L4:
  assumes A1: "equiv(A,r)" and A2: "C \<in> A//r"  "x\<in>C"
  and A3: "Congruent(r,f)"
  shows "f`(x) \<in> A"
proof -
  from A1 A2 have "x\<in>A"
    using EquivClass_1_L1 by simp
  with A1 have "\<langle>x,x\<rangle> \<in> r"
    using equiv_def refl_def by simp
  with A3 have  "\<langle>f`(x),f`(x)\<rangle> \<in> r"
    using Congruent_def by simp
  with A1 show ?thesis using equiv_type by auto
qed

text\<open>Equivalence classes are not empty.\<close>

lemma EquivClass_1_L5: 
  assumes A1: "refl(A,r)" and A2: "C \<in> A//r"
  shows "C\<noteq>0"
proof -
  from A2 obtain x where I: "C = r``{x}" and "x\<in>A"
    using quotient_def by auto
  from A1 \<open>x\<in>A\<close> have "x \<in> r``{x}" using refl_def by auto
  with I show ?thesis by auto
qed
  
text\<open>To avoid using an axiom of choice, we define the projection using 
  the expression $\bigcup _{x\in C} r(\{f(x)\})$. 
  The next lemma shows that for
  congruent function this is in the quotient space $A/r$.\<close>

lemma EquivClass_1_L6:
  assumes A1: "equiv(A,r)" and A2: "Congruent(r,f)" 
  and A3: "C \<in> A//r"
  shows "(\<Union>x\<in>C. r``{f`(x)}) \<in> A//r"
proof -
  from A1 have "refl(A,r)" unfolding equiv_def by simp
  with A3 have "C\<noteq>0" using EquivClass_1_L5 by simp
  moreover from A2 A3 A1 have "\<forall>x\<in>C. r``{f`(x)} \<in> A//r"
    using EquivClass_1_L4 quotientI by auto
  moreover from A1 A2 A3 have 
    "\<forall>x y. x\<in>C \<and> y\<in>C \<longrightarrow> r``{f`(x)} = r``{f`(y)}" 
    using EquivClass_1_L3 by blast
  ultimately show ?thesis by (rule ZF1_1_L2)
qed

text\<open>Congruent functions can be projected.\<close>

lemma EquivClass_1_T0: 
  assumes "equiv(A,r)"  "Congruent(r,f)"
  shows "ProjFun(A,r,f) : A//r \<rightarrow> A//r"
  using assms EquivClass_1_L6 ProjFun_def ZF_fun_from_total
  by simp
  
text\<open>We now define congruent functions of two variables (binary funtions). 
  The predicate \<open>Congruent2\<close> corresponds to \<open>congruent2\<close> 
  in Isabelle's standard \<open>EquivClass\<close> theory, 
  but uses ZF-functions rather than meta-functions.\<close>

definition
  "Congruent2(r,f) \<equiv>
  (\<forall>x\<^sub>1 x\<^sub>2 y\<^sub>1 y\<^sub>2. \<langle>x\<^sub>1,x\<^sub>2\<rangle> \<in> r \<and> \<langle>y\<^sub>1,y\<^sub>2\<rangle> \<in> r  \<longrightarrow> 
  \<langle>f`\<langle>x\<^sub>1,y\<^sub>1\<rangle>, f`\<langle>x\<^sub>2,y\<^sub>2\<rangle> \<rangle> \<in> r)"


text\<open>Next we define the notion of projecting a binary operation
  to the quotient space. This is a very important concept that
  allows to define quotient groups, among other things.\<close>

definition 
  "ProjFun2(A,r,f) \<equiv>
  {\<langle>p,\<Union> z \<in> fst(p)\<times>snd(p). r``{f`(z)}\<rangle>. p \<in> (A//r)\<times>(A//r) }"


text\<open>The following lemma is a two-variables equivalent 
  of \<open>EquivClass_1_L3\<close>.\<close>

lemma EquivClass_1_L7: 
  assumes A1: "equiv(A,r)" and A2: "Congruent2(r,f)"
  and A3: "C\<^sub>1 \<in> A//r"  "C\<^sub>2 \<in> A//r" 
  and A4: "z\<^sub>1 \<in> C\<^sub>1\<times>C\<^sub>2"  "z\<^sub>2 \<in> C\<^sub>1\<times>C\<^sub>2"
  shows "r``{f`(z\<^sub>1)} = r``{f`(z\<^sub>2)}"
proof -
  from A4 obtain x\<^sub>1 y\<^sub>1 x\<^sub>2 y\<^sub>2 where 
    "x\<^sub>1\<in>C\<^sub>1" and "y\<^sub>1\<in>C\<^sub>2" and "z\<^sub>1 = \<langle>x\<^sub>1,y\<^sub>1\<rangle>" and 
    "x\<^sub>2\<in>C\<^sub>1" and "y\<^sub>2\<in>C\<^sub>2" and "z\<^sub>2 = \<langle>x\<^sub>2,y\<^sub>2\<rangle>" 
    by auto
  with A1 A3 have "\<langle>x\<^sub>1,x\<^sub>2\<rangle> \<in> r" and "\<langle>y\<^sub>1,y\<^sub>2\<rangle> \<in> r"
    using EquivClass_1_L2A by auto
  with A2 have "\<langle>f`\<langle>x\<^sub>1,y\<^sub>1\<rangle>,f`\<langle>x\<^sub>2,y\<^sub>2\<rangle>\<rangle> \<in> r"
    using Congruent2_def by simp
  with A1 \<open>z\<^sub>1 = \<langle>x\<^sub>1,y\<^sub>1\<rangle>\<close> \<open>z\<^sub>2 = \<langle>x\<^sub>2,y\<^sub>2\<rangle>\<close> show ?thesis 
    using equiv_class_eq by simp
qed

text\<open>The values of congruent functions of two variables are in the space.\<close>

lemma EquivClass_1_L8:
  assumes A1: "equiv(A,r)" and A2: "C\<^sub>1 \<in> A//r" and A3: "C\<^sub>2 \<in> A//r"
  and A4: "z \<in> C\<^sub>1\<times>C\<^sub>2" and A5: "Congruent2(r,f)"
  shows "f`(z) \<in> A"
proof -
  from A4 obtain x y where "x\<in>C\<^sub>1" and "y\<in>C\<^sub>2" and "z = \<langle>x,y\<rangle>"  
    by auto
  with A1 A2 A3 have "x\<in>A" and "y\<in>A" 
    using EquivClass_1_L1 by auto
  with A1 A4 have "\<langle>x,x\<rangle> \<in> r" and "\<langle>y,y\<rangle> \<in> r"
    using equiv_def refl_def by auto
  with A5 have "\<langle>f`\<langle>x,y\<rangle>, f`\<langle>x,y\<rangle> \<rangle> \<in> r"
    using Congruent2_def by simp
  with A1 \<open>z = \<langle>x,y\<rangle>\<close> show ?thesis using equiv_type by auto
qed

text\<open>The values of congruent functions are in the space. Note that
  although this lemma is intended to be used with functions, we don't
  need to assume that $f$ is a function.\<close>

lemma EquivClass_1_L8A:
  assumes A1: "equiv(A,r)" and A2: "x\<in>A"  "y\<in>A"
  and A3: "Congruent2(r,f)"
  shows "f`\<langle>x,y\<rangle> \<in> A"
proof -
  from A1 A2 have "r``{x} \<in> A//r" "r``{y} \<in> A//r" 
    "\<langle>x,y\<rangle> \<in> r``{x}\<times>r``{y}"
    using equiv_class_self quotientI by auto
  with A1 A3 show ?thesis using EquivClass_1_L8 by simp
qed
  
text\<open>The following lemma is a two-variables equivalent of 
  \<open>EquivClass_1_L6\<close>.\<close>

lemma EquivClass_1_L9:
  assumes A1: "equiv(A,r)" and A2: "Congruent2(r,f)" 
  and A3: "p \<in> (A//r)\<times>(A//r)"
  shows "(\<Union> z \<in> fst(p)\<times>snd(p). r``{f`(z)}) \<in> A//r"
proof -
  from A3 have "fst(p) \<in> A//r" and "snd(p) \<in> A//r"
    by auto
  with A1 A2 have 
    I: "\<forall>z \<in> fst(p)\<times>snd(p). f`(z) \<in> A"
    using EquivClass_1_L8 by simp
  from A3 A1 have "fst(p)\<times>snd(p) \<noteq> 0" 
    using equiv_def EquivClass_1_L5 Sigma_empty_iff
    by auto
  moreover from A1 I have 
    "\<forall>z \<in> fst(p)\<times>snd(p). r``{f`(z)} \<in> A//r"
    using quotientI by simp
  moreover from A1 A2 \<open>fst(p) \<in> A//r\<close> \<open>snd(p) \<in> A//r\<close> have
    "\<forall>z\<^sub>1 z\<^sub>2. z\<^sub>1 \<in> fst(p)\<times>snd(p) \<and> z\<^sub>2 \<in> fst(p)\<times>snd(p) \<longrightarrow> 
    r``{f`(z\<^sub>1)} = r``{f`(z\<^sub>2)}"
    using EquivClass_1_L7 by blast
   ultimately show ?thesis by (rule ZF1_1_L2)
qed

text\<open>Congruent functions of two variables can be projected.\<close>

theorem EquivClass_1_T1: 
  assumes "equiv(A,r)"  "Congruent2(r,f)"
  shows "ProjFun2(A,r,f) : (A//r)\<times>(A//r) \<rightarrow> A//r"
  using assms EquivClass_1_L9 ProjFun2_def ZF_fun_from_total 
  by simp

(*text{*We define the projection on the quotient space as a function that takes
  an element of $A$ and assigns its equivalence class in $A/r$.*}

constdefs
  "Proj(A,r) \<equiv> {<x,c> \<in> A\<times>(A//r). r``{x} = c}"*)

text\<open>The projection diagram commutes. I wish I knew how to draw this diagram
  in LaTeX.\<close>

lemma EquivClass_1_L10: 
  assumes A1: "equiv(A,r)" and A2: "Congruent2(r,f)" 
  and A3: "x\<in>A"  "y\<in>A"
  shows "ProjFun2(A,r,f)`\<langle>r``{x},r``{y}\<rangle> = r``{f`\<langle>x,y\<rangle>}"
proof -
  from A3 A1 have "r``{x} \<times> r``{y} \<noteq> 0"
    using quotientI equiv_def EquivClass_1_L5 Sigma_empty_iff
    by auto
  moreover have 
    "\<forall>z \<in> r``{x}\<times>r``{y}.  r``{f`(z)} = r``{f`\<langle>x,y\<rangle>}"
  proof
    fix z assume A4: "z \<in> r``{x}\<times>r``{y}"
    from A1 A3 have 
      "r``{x} \<in> A//r" "r``{y} \<in> A//r"
      "\<langle>x,y\<rangle> \<in> r``{x}\<times>r``{y}"
      using quotientI equiv_class_self by auto
    with A1 A2 A4 show
      "r``{f`(z)} = r``{f`\<langle>x,y\<rangle>}"
      using EquivClass_1_L7 by blast
  qed
  ultimately have 
    "(\<Union>z \<in> r``{x}\<times>r``{y}. r``{f`(z)}) =  r``{f`\<langle>x,y\<rangle>}"
    by (rule ZF1_1_L1)
  moreover have 
    "ProjFun2(A,r,f)`\<langle>r``{x},r``{y}\<rangle> = (\<Union>z \<in> r``{x}\<times>r``{y}. r``{f`(z)})"
    proof -
      from assms have 
	"ProjFun2(A,r,f) : (A//r)\<times>(A//r) \<rightarrow> A//r"
	"\<langle>r``{x},r``{y}\<rangle> \<in> (A//r)\<times>(A//r)"
	using EquivClass_1_T1 quotientI by auto
      then show ?thesis using ProjFun2_def ZF_fun_from_tot_val
	by auto
    qed
  ultimately show ?thesis by simp
qed

subsection\<open>Projecting commutative, associative and distributive operations.\<close>

text\<open>In this section we show that if the operations are congruent with
  respect to an equivalence relation then the projection to the quotient 
  space preserves commutativity, associativity and distributivity.\<close>

text\<open>The projection of commutative operation is commutative.\<close>

lemma EquivClass_2_L1: assumes 
  A1: "equiv(A,r)" and A2: "Congruent2(r,f)"
  and A3: "f {is commutative on} A"
  and A4: "c1 \<in> A//r"  "c2 \<in> A//r"
  shows "ProjFun2(A,r,f)`\<langle>c1,c2\<rangle> = ProjFun2(A,r,f)`\<langle>c2,c1\<rangle>"
proof -
  from A4 obtain x y where D1:
    "c1 = r``{x}"  "c2 = r``{y}"
    "x\<in>A"  "y\<in>A"
    using quotient_def by auto
  with A1 A2 have "ProjFun2(A,r,f)`\<langle>c1,c2\<rangle> = r``{f`\<langle>x,y\<rangle>}"
    using EquivClass_1_L10 by simp
  also from A3 D1 have
    "r``{f`\<langle>x,y\<rangle>} = r``{f`\<langle>y,x\<rangle>}"
    using IsCommutative_def by simp
  also from A1 A2 D1 have
    "r``{f`\<langle>y,x\<rangle>} = ProjFun2(A,r,f)` \<langle>c2,c1\<rangle>"
    using EquivClass_1_L10 by simp
  finally show ?thesis by simp
qed

text\<open>The projection of commutative operation is commutative.\<close>

theorem EquivClass_2_T1:
  assumes "equiv(A,r)" and "Congruent2(r,f)"
  and "f {is commutative on} A"
  shows "ProjFun2(A,r,f) {is commutative on} A//r"
  using assms IsCommutative_def EquivClass_2_L1 by simp
    
text\<open>The projection of an associative operation is associative.\<close>

lemma EquivClass_2_L2: 
  assumes A1: "equiv(A,r)" and A2: "Congruent2(r,f)"
  and A3: "f {is associative on} A"
  and A4: "c1 \<in> A//r"  "c2 \<in> A//r"  "c3 \<in> A//r"
  and A5: "g = ProjFun2(A,r,f)"
  shows "g`\<langle>g`\<langle>c1,c2\<rangle>,c3\<rangle> = g`\<langle>c1,g`\<langle>c2,c3\<rangle>\<rangle>"
proof -
  from A4 obtain x y z where D1:
    "c1 = r``{x}"  "c2 = r``{y}"  "c3 = r``{z}"
    "x\<in>A"  "y\<in>A"  "z\<in>A"
    using quotient_def by auto
  with A3 have T1:"f`\<langle>x,y\<rangle> \<in> A"  "f`\<langle>y,z\<rangle> \<in> A"
    using IsAssociative_def apply_type by auto
  with A1 A2 D1 A5 have 
    "g`\<langle>g`\<langle>c1,c2\<rangle>,c3\<rangle> =  r``{f`\<langle>f`\<langle>x,y\<rangle>,z\<rangle>}"
    using EquivClass_1_L10 by simp
  also from D1 A3 have 
    "\<dots> = r``{f`\<langle>x,f`\<langle>y,z\<rangle> \<rangle>}"
    using IsAssociative_def by simp
  also from T1 A1 A2 D1 A5 have
    "\<dots> = g`\<langle>c1,g`\<langle>c2,c3\<rangle>\<rangle>"
    using EquivClass_1_L10 by simp
  finally show ?thesis by simp
qed

text\<open>The projection of an associative operation is associative on the
  quotient.\<close>

theorem EquivClass_2_T2:
  assumes A1: "equiv(A,r)" and A2: "Congruent2(r,f)"
  and A3: "f {is associative on} A"
  shows "ProjFun2(A,r,f) {is associative on} A//r"
proof -
  let ?g = "ProjFun2(A,r,f)"
  from A1 A2 have 
    "?g \<in> (A//r)\<times>(A//r) \<rightarrow> A//r"
    using EquivClass_1_T1 by simp
  moreover from A1 A2 A3 have
    "\<forall>c1 \<in> A//r.\<forall>c2 \<in> A//r.\<forall>c3 \<in> A//r.
    ?g`\<langle>?g`\<langle>c1,c2\<rangle>,c3\<rangle> = ?g`\<langle>c1,?g`\<langle>c2,c3\<rangle>\<rangle>"
    using EquivClass_2_L2 by simp
  ultimately show ?thesis
    using IsAssociative_def by simp
qed

text\<open>The essential condition to show that distributivity is preserved by 
  projections to quotient spaces, provided both operations are congruent
  with respect to the equivalence relation.\<close>

lemma EquivClass_2_L3: 
  assumes A1: "IsDistributive(X,A,M)"
  and A2: "equiv(X,r)" 
  and A3: "Congruent2(r,A)" "Congruent2(r,M)"
  and A4: "a \<in> X//r"  "b \<in> X//r"  "c \<in> X//r"
  and A5: "A\<^sub>p = ProjFun2(X,r,A)" "M\<^sub>p = ProjFun2(X,r,M)"
  shows "M\<^sub>p`\<langle>a,A\<^sub>p`\<langle>b,c\<rangle>\<rangle> = A\<^sub>p`\<langle> M\<^sub>p`\<langle>a,b\<rangle>,M\<^sub>p`\<langle>a,c\<rangle>\<rangle> \<and> 
  M\<^sub>p`\<langle> A\<^sub>p`\<langle>b,c\<rangle>,a \<rangle> = A\<^sub>p`\<langle> M\<^sub>p`\<langle>b,a\<rangle>, M\<^sub>p`\<langle>c,a\<rangle>\<rangle>"
proof
  from A4 obtain x y z where "x\<in>X"  "y\<in>X"  "z\<in>X"
    "a = r``{x}"  "b = r``{y}"  "c = r``{z}"   
    using quotient_def by auto
  with A1 A2 A3 A5 show 
    "M\<^sub>p`\<langle>a,A\<^sub>p`\<langle>b,c\<rangle>\<rangle> = A\<^sub>p`\<langle> M\<^sub>p`\<langle>a,b\<rangle>,M\<^sub>p`\<langle>a,c\<rangle>\<rangle>" and
    "M\<^sub>p`\<langle> A\<^sub>p`\<langle>b,c\<rangle>,a \<rangle> = A\<^sub>p`\<langle> M\<^sub>p`\<langle>b,a\<rangle>, M\<^sub>p`\<langle>c,a\<rangle>\<rangle>"  
    using EquivClass_1_L8A EquivClass_1_L10 IsDistributive_def
    by auto
qed

text\<open>Distributivity is preserved by 
  projections to quotient spaces, provided both operations are congruent
  with respect to the equivalence relation.\<close>

lemma EquivClass_2_L4: assumes A1: "IsDistributive(X,A,M)"
  and A2: "equiv(X,r)" 
  and A3: "Congruent2(r,A)" "Congruent2(r,M)"
  shows "IsDistributive(X//r,ProjFun2(X,r,A),ProjFun2(X,r,M))"
proof-
 let ?A\<^sub>p = "ProjFun2(X,r,A)" 
 let ?M\<^sub>p = "ProjFun2(X,r,M)"
 from A1 A2 A3 have
   "\<forall>a\<in>X//r.\<forall>b\<in>X//r.\<forall>c\<in>X//r.
   ?M\<^sub>p`\<langle>a,?A\<^sub>p`\<langle>b,c\<rangle>\<rangle> = ?A\<^sub>p`\<langle>?M\<^sub>p`\<langle>a,b\<rangle>,?M\<^sub>p`\<langle>a,c\<rangle>\<rangle> \<and> 
   ?M\<^sub>p`\<langle>?A\<^sub>p`\<langle>b,c\<rangle>,a\<rangle> = ?A\<^sub>p`\<langle>?M\<^sub>p`\<langle>b,a\<rangle>,?M\<^sub>p`\<langle>c,a\<rangle>\<rangle>"
   using EquivClass_2_L3 by simp
 then show ?thesis using IsDistributive_def by simp
qed

subsection\<open>Saturated sets\<close>

text\<open>In this section we consider sets that are saturated 
  with respect to an equivalence
  relation. A set $A$ is saturated with respect to a relation 
  $r$ if $A=r^{-1}(r(A))$. 
  For equivalence relations saturated sets are unions of equivalence classes.
  This makes them useful as a tool to define subsets of 
  the quotient space using properties
  of representants. Namely, we often define a set 
  $B\subseteq X/r$ by saying that
  $[x]_r \in B$ iff $x\in A$. 
  If $A$ is a saturated set, this definition is consistent in 
  the sense that it does not depend on the choice of $x$ to 
  represent $[x]_r$.\<close>

text\<open>The following defines the notion of a saturated set. 
  Recall that in Isabelle 
  \<open>r-``(A)\<close> is the inverse image of $A$ with respect to relation $r$. 
  This definition is not specific to equivalence relations.\<close>

definition
  "IsSaturated(r,A) \<equiv> A = r-``(r``(A))"

text\<open>For equivalence relations a set is saturated iff it is an image 
  of itself.\<close>

lemma EquivClass_3_L1: assumes A1: "equiv(X,r)"
  shows "IsSaturated(r,A) \<longleftrightarrow> A = r``(A)"
proof
  assume "IsSaturated(r,A)"
  then have "A = (converse(r) O r)``(A)"
    using IsSaturated_def vimage_def image_comp
    by simp
  also from A1 have "\<dots> = r``(A)"
    using equiv_comp_eq by simp
  finally show "A = r``(A)" by simp
next assume "A = r``(A)"
  with A1 have "A = (converse(r) O r)``(A)"
    using equiv_comp_eq by simp
  also have "\<dots> =  r-``(r``(A))"
    using vimage_def image_comp by simp
  finally have "A =  r-``(r``(A))" by simp
  then show "IsSaturated(r,A)" using IsSaturated_def
    by simp
qed
  
text\<open>For equivalence relations sets are contained in their images.\<close> 

lemma EquivClass_3_L2: assumes A1: "equiv(X,r)" and A2: "A\<subseteq>X"
  shows "A \<subseteq> r``(A)"
proof
  fix a assume "a\<in>A"
  with A1 A2 have "a \<in> r``{a}"
    using equiv_class_self by auto
  with \<open>a\<in>A\<close> show "a \<in> r``(A)" by auto
qed
  
text\<open>The next lemma shows that if "$\sim$" 
  is an equivalence relation and a set 
  $A$ is such that $a\in A$ and $a\sim b$ implies $b\in A$, then
  $A$ is saturated with respect to the relation.\<close>

lemma EquivClass_3_L3: assumes A1: "equiv(X,r)"
  and A2: "r \<subseteq> X\<times>X" and A3: "A\<subseteq>X"
  and A4: "\<forall>x\<in>A. \<forall>y\<in>X. \<langle>x,y\<rangle> \<in> r \<longrightarrow> y\<in>A"
  shows "IsSaturated(r,A)"
proof -
  from A2 A4 have "r``(A) \<subseteq> A"
    using image_iff by blast
  moreover from A1 A3 have "A \<subseteq> r``(A)"
    using EquivClass_3_L2 by simp
  ultimately have "A = r``(A)" by auto
  with A1 show "IsSaturated(r,A)" using EquivClass_3_L1
    by simp
qed

text\<open>If $A\subseteq X$ and $A$ is saturated and $x\sim y$, then $x\in A$ iff
  $y\in A$. Here we show only one direction.\<close>

lemma EquivClass_3_L4: assumes A1: "equiv(X,r)"
  and A2: "IsSaturated(r,A)" and A3: "A\<subseteq>X"
  and A4: "\<langle>x,y\<rangle> \<in> r" 
  and A5: "x\<in>X"  "y\<in>A"
  shows "x\<in>A"
proof -
  from A1 A5 have "x \<in> r``{x}"
    using equiv_class_self by simp
  with A1 A3 A4 A5 have "x \<in> r``(A)"
    using equiv_class_eq equiv_class_self
    by auto
  with A1 A2 show "x\<in>A"
    using EquivClass_3_L1 by simp
qed

text\<open>If $A\subseteq X$ and $A$ is saturated and $x\sim y$, then $x\in A$ iff
  $y\in A$.\<close>

lemma EquivClass_3_L5: assumes A1: "equiv(X,r)"
  and A2: "IsSaturated(r,A)" and A3: "A\<subseteq>X"
  and A4: "x\<in>X"  "y\<in>X"
  and A5: "\<langle>x,y\<rangle> \<in> r"
  shows "x\<in>A \<longleftrightarrow> y\<in>A"
proof
  assume "y\<in>A" 
  with assms show "x\<in>A" using EquivClass_3_L4
    by simp
next assume "x\<in>A"
  from A1 A5 have "\<langle>y,x\<rangle> \<in> r"
    using equiv_is_sym by blast
  with A1 A2 A3 A4 \<open>x\<in>A\<close> show "y\<in>A"
    using EquivClass_3_L4 by simp
qed
  
text\<open>If $A$ is saturated then $x\in A$ iff its class is in the projection 
  of $A$.\<close>

lemma EquivClass_3_L6: assumes A1: "equiv(X,r)"
  and A2: "IsSaturated(r,A)" and A3: "A\<subseteq>X" and A4: "x\<in>X"
  and A5: "B = {r``{x}. x\<in>A}"
  shows "x\<in>A \<longleftrightarrow> r``{x} \<in> B"
proof
  assume "x\<in>A"
  with A5 show "r``{x} \<in> B" by auto
next assume "r``{x} \<in> B"
  with A5 obtain y where "y \<in> A" and "r``{x} = r``{y}"
    by auto
  with A1 A3 have "\<langle>x,y\<rangle> \<in> r"
    using eq_equiv_class by auto
  with A1 A2 A3 A4  \<open>y \<in> A\<close> show "x\<in>A"
    using EquivClass_3_L4 by simp
qed

text\<open>A technical lemma involving a projection of a saturated set and a 
  logical epression with exclusive or. Note that we don't really care 
  what \<open>Xor\<close> is here, this is true for any predicate.\<close>

lemma EquivClass_3_L7: assumes "equiv(X,r)"
  and "IsSaturated(r,A)" and "A\<subseteq>X"
  and "x\<in>X"  "y\<in>X"
  and "B = {r``{x}. x\<in>A}"
  and "(x\<in>A) Xor (y\<in>A)"
  shows "(r``{x} \<in> B)  Xor (r``{y} \<in> B)"
  using assms EquivClass_3_L6 by simp
    
end
