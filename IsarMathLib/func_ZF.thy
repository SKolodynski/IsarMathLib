(* 
    This file is a part of IsarMathLib - 
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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.*)


section \<open>Binary operations\<close>

theory func_ZF imports func1

begin

text\<open>In this theory we consider properties of functions that are binary 
  operations, that is they map $X\times X$ into $X$.\<close>

subsection\<open>Lifting operations to a function space\<close>

text\<open>It happens quite often that we have a binary operation on some set and
  we need a similar operation that is defined for functions on that set. 
  For example once we know how to add real numbers we also know how to add
  real-valued functions: for $f,g:X \rightarrow \mathbf{R}$ we define
  $(f+g)(x) = f(x) + g(x)$. Note that formally the $+$ means something 
  different on the left hand side of this equality than on the 
  right hand side.
  This section aims at formalizing this process.
  We will call it "lifting to a function space", if you have a 
  suggestion for a better name, please let me know.\<close>
 
text\<open>Since we are writing in generic set notation, 
  the definition below is a bit complicated. Here it what it says:
  Given a set $X$ and another set $f$ (that represents a binary function on $X$) 
  we are defining $f$ lifted to function space over $X$
  as the binary function (a set of pairs) on the space 
  $F = X \rightarrow \textrm{range}(f)$ such that the value of this function
  on pair $\langle a,b \rangle$ of functions on $X$ is another function $c$ on $X$
  with values defined by $c(x) = f\langle a(x), b(x)\rangle$. 
\<close>

definition
Lift2FcnSpce (infix "{lifted to function space over}" 65) where
 "f {lifted to function space over} X \<equiv> 
  {\<langle> p,{\<langle>x,f`\<langle>fst(p)`(x),snd(p)`(x)\<rangle>\<rangle>. x \<in> X}\<rangle>. 
  p \<in> (X\<rightarrow>range(f))\<times>(X\<rightarrow>range(f))}"

text\<open>The result of the lift belongs to the function space.\<close>

lemma func_ZF_1_L1: 
  assumes A1: "f : Y\<times>Y\<rightarrow>Y" 
  and A2: "p \<in>(X\<rightarrow>range(f))\<times>(X\<rightarrow>range(f))"
  shows 
  "{\<langle>x,f`\<langle>fst(p)`(x),snd(p)`(x)\<rangle>\<rangle>. x \<in> X} : X\<rightarrow>range(f)"
  proof -
    have "\<forall>x\<in>X. f`\<langle>fst(p)`(x),snd(p)`(x)\<rangle> \<in> range(f)"
    proof
      fix x assume "x\<in>X"
      let ?p = "\<langle>fst(p)`(x),snd(p)`(x)\<rangle>"
      from A2 \<open>x\<in>X\<close> have 
	"fst(p)`(x) \<in> range(f)"  "snd(p)`(x) \<in> range(f)"
	using apply_type by auto
      with A1 have "?p \<in> Y\<times>Y"
	using func1_1_L5B by blast
      with A1 have "\<langle>?p, f`(?p)\<rangle> \<in> f"
	using apply_Pair by simp
      with A1 show 
	"f`(?p) \<in> range(f)"
	using rangeI by simp
    qed
    then show ?thesis using ZF_fun_from_total by simp
qed

text\<open>The values of the lift are defined by the value of the liftee in a 
  natural way.\<close>

lemma func_ZF_1_L2: 
  assumes A1: "f : Y\<times>Y\<rightarrow>Y" 
  and A2: "p \<in> (X\<rightarrow>range(f))\<times>(X\<rightarrow>range(f))" and A3: "x\<in>X"
  and A4: "P = {\<langle>x,f`\<langle>fst(p)`(x),snd(p)`(x)\<rangle>\<rangle>. x \<in> X}"
  shows "P`(x) = f`\<langle>fst(p)`(x),snd(p)`(x)\<rangle>" 
proof -
  from A1 A2 have 
    "{\<langle>x,f`\<langle>fst(p)`(x),snd(p)`(x)\<rangle>\<rangle>. x \<in> X} : X \<rightarrow> range(f)"
    using func_ZF_1_L1 by simp
  with A4 have "P :  X \<rightarrow> range(f)" by simp
  with  A3 A4 show "P`(x) = f`\<langle>fst(p)`(x),snd(p)`(x)\<rangle>"
    using ZF_fun_from_tot_val by simp
qed

text\<open>Function lifted to a function space results in  function space 
  operator.\<close>

theorem func_ZF_1_L3: 
  assumes "f : Y\<times>Y\<rightarrow>Y"
  and "F = f {lifted to function space over} X"
  shows "F : (X\<rightarrow>range(f))\<times>(X\<rightarrow>range(f))\<rightarrow>(X\<rightarrow>range(f))"
  using assms Lift2FcnSpce_def func_ZF_1_L1 ZF_fun_from_total 
  by simp

text\<open>The values of the lift are defined by the values of the liftee in
  the natural way.\<close>

theorem func_ZF_1_L4: 
  assumes A1: "f : Y\<times>Y\<rightarrow>Y"
  and A2: "F = f {lifted to function space over} X"
  and A3: "s:X\<rightarrow>range(f)" "r:X\<rightarrow>range(f)"  
  and A4: "x\<in>X"
  shows "(F`\<langle>s,r\<rangle>)`(x) = f`\<langle>s`(x),r`(x)\<rangle>"
proof -
  let ?p = "\<langle>s,r\<rangle>"
  let ?P = "{\<langle>x,f`\<langle>fst(?p)`(x),snd(?p)`(x)\<rangle>\<rangle>. x \<in> X}" 
  from A1 A3 A4 have
    "f : Y\<times>Y\<rightarrow>Y"  "?p \<in> (X\<rightarrow>range(f))\<times>(X\<rightarrow>range(f))"
    "x\<in>X"  "?P = {\<langle>x,f`\<langle>fst(?p)`(x),snd(?p)`(x)\<rangle>\<rangle>. x \<in> X}" 
    by auto
  then have "?P`(x) = f`\<langle>fst(?p)`(x),snd(?p)`(x)\<rangle>"
    by (rule func_ZF_1_L2)
  hence "?P`(x) = f`\<langle>s`(x),r`(x)\<rangle>" by auto
  moreover have "?P = F`\<langle>s,r\<rangle>"
  proof -
    from A1 A2 have "F : (X\<rightarrow>range(f))\<times>(X\<rightarrow>range(f))\<rightarrow>(X\<rightarrow>range(f))"
      using func_ZF_1_L3 by simp
    moreover from A3 have "?p \<in> (X\<rightarrow>range(f))\<times>(X\<rightarrow>range(f))"
      by auto
    moreover from A2 have
      "F = {\<langle>p,{\<langle>x,f`\<langle>fst(p)`(x),snd(p)`(x)\<rangle>\<rangle>. x \<in> X}\<rangle>. 
      p \<in> (X\<rightarrow>range(f))\<times>(X\<rightarrow>range(f))}"
      using Lift2FcnSpce_def by simp
    ultimately show ?thesis using ZF_fun_from_tot_val
      by simp
  qed
  ultimately show "(F`\<langle>s,r\<rangle>)`(x) = f`\<langle>s`(x),r`(x)\<rangle>" by auto
qed

subsection\<open>Associative and commutative operations\<close>

text\<open>In this section we define associative and commutative operations 
  and prove that they remain such when we lift them
  to a function space.\<close>

text\<open>Typically we say that a binary operation "$\cdot $" 
  on a set $G$ is ''associative''
  if $(x\cdot y)\cdot z = x\cdot (y\cdot z)$ for all $x,y,z \in G$.
  Our actual definition below does not use the multiplicative notation
  so that we can apply it equally to the additive notation $+$ 
  or whatever infix symbol we may want to use. 
  Instead, we use the generic set theory notation
  and write $P\langle x,y \rangle$ to denote the value of the operation
  $P$ on a pair $\langle x,y \rangle \in G\times G$.\<close>

definition 
  IsAssociative (infix "{is associative on}" 65) where
  "P {is associative on} G \<equiv> P : G\<times>G\<rightarrow>G \<and> 
  (\<forall> x \<in> G. \<forall> y \<in> G. \<forall> z \<in> G. 
  ( P`(\<langle>P`(\<langle>x,y\<rangle>),z\<rangle>) = P`( \<langle>x,P`(\<langle>y,z\<rangle>)\<rangle> )))"

text\<open>A binary function $f: X\times X \rightarrow Y$ is commutative
  if $f\langle x,y \rangle = f\langle y,x \rangle$. Note that
  in the definition of associativity above we talk about binary
  ''operation'' and here we say use the term binary ''function''. 
  This is not set in stone, but usually the word "operation" is used 
  when the range is a factor of the domain, while the word "function"
  allows the range to be a completely unrelated set.\<close>

definition
  IsCommutative (infix "{is commutative on}" 65) where
  "f {is commutative on} G \<equiv> \<forall>x\<in>G. \<forall>y\<in>G. f`\<langle>x,y\<rangle> = f`\<langle>y,x\<rangle>"

text\<open>The lift of a commutative function is commutative.\<close>

lemma func_ZF_2_L1:
  assumes A1: "f : G\<times>G\<rightarrow>G"
  and A2: "F = f {lifted to function space over} X"
  and A3: "s : X\<rightarrow>range(f)" "r : X\<rightarrow>range(f)" 
  and A4: "f {is commutative on} G"
  shows "F`\<langle>s,r\<rangle> = F`\<langle>r,s\<rangle>" 
proof -
  from A1 A2 have 
    "F : (X\<rightarrow>range(f))\<times>(X\<rightarrow>range(f))\<rightarrow>(X\<rightarrow>range(f))"
    using func_ZF_1_L3 by simp 
  with A3 have 
    "F`\<langle>s,r\<rangle> : X\<rightarrow>range(f)" and "F`\<langle>r,s\<rangle> : X\<rightarrow>range(f)"
    using apply_type by auto
  moreover have 
    "\<forall>x\<in>X. (F`\<langle>s,r\<rangle>)`(x) = (F`\<langle>r,s\<rangle>)`(x)"
  proof
    fix x assume "x\<in>X"
    from A1 have "range(f)\<subseteq>G"
      using func1_1_L5B by simp
    with A3 \<open>x\<in>X\<close> have "s`(x) \<in> G" and "r`(x) \<in> G"
      using apply_type by auto
    with A1 A2 A3 A4 \<open>x\<in>X\<close> show 
      "(F`\<langle>s,r\<rangle>)`(x) = (F`\<langle>r,s\<rangle>)`(x)"
      using func_ZF_1_L4 IsCommutative_def by simp
  qed
  ultimately show ?thesis using fun_extension_iff
    by simp
qed

text\<open>The lift of a commutative function is commutative 
  on the function space.\<close>

lemma func_ZF_2_L2:
  assumes "f : G\<times>G\<rightarrow>G"
  and "f {is commutative on} G"
  and "F = f {lifted to function space over} X"
  shows "F {is commutative on} (X\<rightarrow>range(f))"
  using assms IsCommutative_def func_ZF_2_L1 by simp
  
text\<open>The lift of an associative function is associative.\<close>

lemma func_ZF_2_L3:
  assumes A2: "F = f {lifted to function space over} X"
  and A3: "s : X\<rightarrow>range(f)" "r : X\<rightarrow>range(f)" "q : X\<rightarrow>range(f)"
  and A4: "f {is associative on} G"
  shows "F`\<langle>F`\<langle>s,r\<rangle>,q\<rangle> = F`\<langle>s,F`\<langle>r,q\<rangle>\<rangle>"
proof -
  from A4 A2 have 
    "F : (X\<rightarrow>range(f))\<times>(X\<rightarrow>range(f))\<rightarrow>(X\<rightarrow>range(f))"
    using IsAssociative_def func_ZF_1_L3 by auto
  with A3 have I:
    "F`\<langle>s,r\<rangle> : X\<rightarrow>range(f)"
    "F`\<langle>r,q\<rangle> : X\<rightarrow>range(f)"
    "F`\<langle>F`\<langle>s,r\<rangle>,q\<rangle> : X\<rightarrow>range(f)"
    "F`\<langle>s,F`\<langle>r,q\<rangle>\<rangle>: X\<rightarrow>range(f)"
    using apply_type by auto
  moreover have
    "\<forall>x\<in>X. (F`\<langle>F`\<langle>s,r\<rangle>,q\<rangle>)`(x) = (F`\<langle>s,F`\<langle>r,q\<rangle>\<rangle>)`(x)"
  proof
    fix x assume "x\<in>X"
    from A4 have "f:G\<times>G\<rightarrow>G"
      using IsAssociative_def by simp
    then have "range(f)\<subseteq>G"
      using func1_1_L5B by simp
    with A3 \<open>x\<in>X\<close> have 
      "s`(x) \<in> G" "r`(x) \<in> G" "q`(x) \<in> G"
      using apply_type by auto
    with A2 I A3 A4 \<open>x\<in>X\<close> \<open>f:G\<times>G\<rightarrow>G\<close> show 
      "(F`\<langle>F`\<langle>s,r\<rangle>,q\<rangle>)`(x) = (F`\<langle>s,F`\<langle>r,q\<rangle>\<rangle>)`(x)"
      using func_ZF_1_L4 IsAssociative_def by simp
  qed
  ultimately show ?thesis using fun_extension_iff
    by simp
qed

text\<open>The lift of an associative function is associative 
  on the function space.\<close>

lemma func_ZF_2_L4:
  assumes A1: "f {is associative on} G"
  and A2: "F = f {lifted to function space over} X"
  shows "F {is associative on} (X\<rightarrow>range(f))"
proof -
  from A1 A2 have
    "F : (X\<rightarrow>range(f))\<times>(X\<rightarrow>range(f))\<rightarrow>(X\<rightarrow>range(f))"
    using IsAssociative_def func_ZF_1_L3 by auto
  moreover from A1 A2 have
    "\<forall>s \<in> X\<rightarrow>range(f). \<forall> r \<in> X\<rightarrow>range(f). \<forall>q \<in> X\<rightarrow>range(f).
    F`\<langle>F`\<langle>s,r\<rangle>,q\<rangle> = F`\<langle>s,F`\<langle>r,q\<rangle>\<rangle>"
    using func_ZF_2_L3 by simp
  ultimately show ?thesis using IsAssociative_def 
    by simp
qed

subsection\<open>Restricting operations\<close>

text\<open>In this section we consider conditions under which
  restriction of the operation to a set
  inherits properties like commutativity and associativity.\<close>

text\<open>The commutativity is inherited when restricting a function to a set.\<close>

lemma func_ZF_4_L1: 
  assumes A1: "f:X\<times>X\<rightarrow>Y" and A2: "A\<subseteq>X"
  and A3: "f {is commutative on} X"
  shows "restrict(f,A\<times>A) {is commutative on} A"
proof -
  { fix x y assume "x\<in>A" and "y\<in>A"
    with A2 have "x\<in>X" and "y\<in>X" by auto
    with A3 \<open>x\<in>A\<close> \<open>y\<in>A\<close> have 
      "restrict(f,A\<times>A)`\<langle>x,y\<rangle> = restrict(f,A\<times>A)`\<langle>y,x\<rangle>"
      using IsCommutative_def restrict_if by simp }
  then show ?thesis using IsCommutative_def by simp
qed
  
text\<open>Next we define what it means that a set is closed with 
  respect to an operation.\<close>

definition
  IsOpClosed (infix "{is closed under}" 65) where
  "A {is closed under} f \<equiv> \<forall>x\<in>A. \<forall>y\<in>A. f`\<langle>x,y\<rangle> \<in> A"

text\<open>Associative operation restricted to a set that is closed with
  resp. to this operation is associative.\<close>

lemma func_ZF_4_L2:assumes A1: "f {is associative on} X"
  and A2: "A\<subseteq>X" and A3: "A {is closed under} f"
  and A4: "x\<in>A" "y\<in>A" "z\<in>A"
  and A5: "g = restrict(f,A\<times>A)"
  shows "g`\<langle>g`\<langle>x,y\<rangle>,z\<rangle> = g`\<langle>x,g`\<langle>y,z\<rangle>\<rangle>"
proof - 
  from A4 A2 have I: "x\<in>X" "y\<in>X" "z\<in>X"
    by auto
  from A3 A4 A5 have
    "g`\<langle>g`\<langle>x,y\<rangle>,z\<rangle> = f`\<langle>f`\<langle>x,y\<rangle>,z\<rangle>"
    "g`\<langle>x,g`\<langle>y,z\<rangle>\<rangle> = f`\<langle>x,f`\<langle>y,z\<rangle>\<rangle>"
    using IsOpClosed_def restrict_if by auto
  moreover from A1 I have
    "f`\<langle>f`\<langle>x,y\<rangle>,z\<rangle> = f`\<langle>x,f`\<langle>y,z\<rangle>\<rangle>"
    using IsAssociative_def by simp
  ultimately show ?thesis by simp
qed

text\<open>An associative operation restricted to a set that is closed with
  resp. to this operation is associative on the set.\<close>

lemma func_ZF_4_L3: assumes A1: "f {is associative on} X"
  and A2: "A\<subseteq>X" and A3: "A {is closed under} f"
  shows "restrict(f,A\<times>A) {is associative on} A"
proof -
  let ?g = "restrict(f,A\<times>A)"
  from A1 have "f:X\<times>X\<rightarrow>X"
    using IsAssociative_def by simp
  moreover from A2 have "A\<times>A \<subseteq> X\<times>X" by auto
  moreover from A3 have "\<forall>p \<in> A\<times>A. ?g`(p) \<in> A"
    using IsOpClosed_def restrict_if by auto
  ultimately have "?g : A\<times>A\<rightarrow>A"
    using func1_2_L4 by simp
  moreover from  A1 A2 A3 have
    "\<forall> x \<in> A. \<forall> y \<in> A. \<forall> z \<in> A.
    ?g`\<langle>?g`\<langle>x,y\<rangle>,z\<rangle> = ?g`\<langle> x,?g`\<langle>y,z\<rangle>\<rangle>"
    using func_ZF_4_L2 by simp
  ultimately show ?thesis 
    using IsAssociative_def by simp
qed

text\<open>The essential condition to show that if a set $A$ is closed 
  with respect to an operation, 
  then it is closed under this operation restricted 
  to any superset of $A$.\<close>

lemma func_ZF_4_L4: assumes "A {is closed under} f"
  and "A\<subseteq>B" and "x\<in>A"  "y\<in>A" and "g = restrict(f,B\<times>B)"
  shows "g`\<langle>x,y\<rangle> \<in> A"
  using assms IsOpClosed_def restrict by auto

text\<open>If a set $A$ is closed under an operation, 
  then it is closed under this operation restricted 
  to any superset of $A$.\<close>

lemma func_ZF_4_L5: 
  assumes A1: "A {is closed under} f"
  and A2: "A\<subseteq>B"
  shows "A {is closed under} restrict(f,B\<times>B)"
proof -
  let ?g = "restrict(f,B\<times>B)"
  from A1 A2 have "\<forall>x\<in>A. \<forall>y\<in>A. ?g`\<langle>x,y\<rangle> \<in> A"
    using func_ZF_4_L4 by simp
  then show ?thesis using IsOpClosed_def by simp
qed

text\<open>The essential condition to show that intersection of sets that are
  closed with respect to an operation is closed with respect 
  to the operation.\<close>

lemma func_ZF_4_L6:
  assumes "A {is closed under} f" 
  and "B {is closed under} f"
  and "x \<in> A\<inter>B" "y\<in> A\<inter>B"
  shows "f`\<langle>x,y\<rangle> \<in> A\<inter>B" using assms IsOpClosed_def by auto

text\<open>Intersection of sets that are
  closed with respect to an operation is closed under 
  the operation.\<close>

lemma func_ZF_4_L7:
  assumes "A {is closed under} f"
  "B {is closed under} f"
  shows "A\<inter>B {is closed under} f"
  using assms IsOpClosed_def by simp

subsection\<open>Compositions\<close>

text\<open>For any set $X$ we can consider a binary operation 
  on the set of functions 
  $f:X\rightarrow X$ defined by $C(f,g) = f\circ g$. Composition of functions 
  (or relations) is defined in the standard Isabelle distribution as a higher
  order function and denoted with the letter \<open>O\<close>. 
  In this section we consider the corresponding two-argument 
  ZF-function (binary operation), that is a subset of 
  $((X\rightarrow X)\times (X\rightarrow X))\times (X\rightarrow X)$.\<close>

text\<open>We define the notion of composition on the set $X$ as the
  binary operation on the function space $X\rightarrow X$
  that takes two functions and creates the their composition.\<close>

definition
  "Composition(X) \<equiv> 
  {\<langle>p,fst(p) O snd(p)\<rangle>. p \<in> (X\<rightarrow>X)\<times>(X\<rightarrow>X)}"

text\<open>Composition operation is a function that maps 
  $(X\rightarrow X)\times (X\rightarrow X)$ into $X\rightarrow X$.\<close>

lemma func_ZF_5_L1: shows "Composition(X) : (X\<rightarrow>X)\<times>(X\<rightarrow>X)\<rightarrow>(X\<rightarrow>X)"
  using comp_fun Composition_def ZF_fun_from_total by simp

text\<open>The value of the composition operation is the composition of arguments.\<close>

lemma func_ZF_5_L2: assumes "f:X\<rightarrow>X" and "g:X\<rightarrow>X"
  shows "Composition(X)`\<langle>f,g\<rangle> = f O g" 
proof -
  from assms have 
    "Composition(X) : (X\<rightarrow>X)\<times>(X\<rightarrow>X)\<rightarrow>(X\<rightarrow>X)"
    "\<langle>f,g\<rangle> \<in> (X\<rightarrow>X)\<times>(X\<rightarrow>X)"
    "Composition(X) = {\<langle>p,fst(p) O snd(p)\<rangle>. p \<in> (X\<rightarrow>X)\<times>(X\<rightarrow>X)}"
    using  func_ZF_5_L1 Composition_def by auto
  then show "Composition(X)`\<langle>f,g\<rangle> = f O g"
    using  ZF_fun_from_tot_val by auto
qed

text\<open>What is the value of a composition on an argument?\<close>

lemma func_ZF_5_L3: assumes "f:X\<rightarrow>X" and "g:X\<rightarrow>X" and "x\<in>X"
  shows "(Composition(X)`\<langle>f,g\<rangle>)`(x) = f`(g`(x))"
  using assms func_ZF_5_L2 comp_fun_apply by simp
  
text\<open>The essential condition to show that composition is associative.\<close>

lemma func_ZF_5_L4: assumes A1: "f:X\<rightarrow>X" "g:X\<rightarrow>X" "h:X\<rightarrow>X"
  and A2: "C = Composition(X)"
  shows "C`\<langle>C`\<langle>f,g\<rangle>,h\<rangle> = C`\<langle> f,C`\<langle>g,h\<rangle>\<rangle>"
proof - 
  from A2 have "C : ((X\<rightarrow>X)\<times>(X\<rightarrow>X))\<rightarrow>(X\<rightarrow>X)"
    using func_ZF_5_L1 by simp
  with A1 have I:
    "C`\<langle>f,g\<rangle> : X\<rightarrow>X"
    "C`\<langle>g,h\<rangle> : X\<rightarrow>X"
    "C`\<langle>C`\<langle>f,g\<rangle>,h\<rangle> : X\<rightarrow>X"
    "C`\<langle> f,C`\<langle>g,h\<rangle>\<rangle> : X\<rightarrow>X"
    using apply_funtype by auto
  moreover have 
    "\<forall> x \<in> X. C`\<langle>C`\<langle>f,g\<rangle>,h\<rangle>`(x) = C`\<langle>f,C`\<langle>g,h\<rangle>\<rangle>`(x)"
  proof
    fix x assume "x\<in>X"
    with A1 A2 I have 
      "C`\<langle>C`\<langle>f,g\<rangle>,h\<rangle> ` (x) = f`(g`(h`(x)))"
      "C`\<langle> f,C`\<langle>g,h\<rangle>\<rangle>`(x) = f`(g`(h`(x)))"
      using func_ZF_5_L3 apply_funtype by auto
    then show "C`\<langle>C`\<langle>f,g\<rangle>,h\<rangle>`(x) = C`\<langle> f,C`\<langle>g,h\<rangle>\<rangle>`(x)"
      by simp
    qed
  ultimately show ?thesis using fun_extension_iff by simp
qed
  
text\<open>Composition is an associative operation on $X\rightarrow X$ (the space
  of functions that map $X$ into itself).\<close>

lemma func_ZF_5_L5: shows "Composition(X) {is associative on} (X\<rightarrow>X)"
proof -
  let ?C = "Composition(X)"
  have "\<forall>f\<in>X\<rightarrow>X. \<forall>g\<in>X\<rightarrow>X. \<forall>h\<in>X\<rightarrow>X.
    ?C`\<langle>?C`\<langle>f,g\<rangle>,h\<rangle> = ?C`\<langle>f,?C`\<langle>g,h\<rangle>\<rangle>"
    using func_ZF_5_L4 by simp
  then show ?thesis using func_ZF_5_L1 IsAssociative_def
    by simp
qed

subsection\<open>Identity function\<close>

text\<open>In this section we show some additional facts about the identity 
  function defined in the standard Isabelle's \<open>Perm\<close> theory.\<close>

text\<open>A function that maps every point to itself is the identity on its domain.\<close>

lemma indentity_fun: assumes A1: "f:X\<rightarrow>Y" and A2:"\<forall>x\<in>X. f`(x)=x"
  shows "f = id(X)"
proof -
  from assms have "f:X\<rightarrow>Y" and "id(X):X\<rightarrow>X" and "\<forall>x\<in>X. f`(x) = id(X)`(x)"
    using id_type id_conv by auto 
  then show ?thesis by (rule func_eq)
qed

text\<open>Composing a function with identity does not change the function.\<close>

lemma func_ZF_6_L1A: assumes A1: "f : X\<rightarrow>X"
  shows "Composition(X)`\<langle>f,id(X)\<rangle> = f"
  "Composition(X)`\<langle>id(X),f\<rangle> = f"
proof -
  have "Composition(X) : (X\<rightarrow>X)\<times>(X\<rightarrow>X)\<rightarrow>(X\<rightarrow>X)"
    using func_ZF_5_L1 by simp
  with A1 have "Composition(X)`\<langle>id(X),f\<rangle> : X\<rightarrow>X"
    "Composition(X)`\<langle>f,id(X)\<rangle> : X\<rightarrow>X"
    using id_type apply_funtype by auto
  moreover note A1
  moreover from A1 have 
    "\<forall>x\<in>X. (Composition(X)`\<langle>id(X),f\<rangle>)`(x) = f`(x)"
    "\<forall>x\<in>X. (Composition(X)`\<langle>f,id(X)\<rangle>)`(x) = f`(x)"
    using id_type func_ZF_5_L3 apply_funtype id_conv
    by auto
  ultimately show "Composition(X)`\<langle>id(X),f\<rangle> = f"
    "Composition(X)`\<langle>f,id(X)\<rangle> = f"
    using fun_extension_iff by auto
qed

text\<open>An intuitively clear, but surprsingly nontrivial fact:identity is the only function from 
  a singleton to itself.\<close>

lemma singleton_fun_id: shows "({x} \<rightarrow> {x}) = {id({x})}"
proof
  show "{id({x})} \<subseteq> ({x} \<rightarrow> {x})"
    using id_def by simp
  { let ?g = "id({x})"
    fix f assume "f : {x} \<rightarrow> {x}"
    then have "f : {x} \<rightarrow> {x}" and "?g : {x} \<rightarrow> {x}"
      using id_def by auto
    moreover from \<open>f : {x} \<rightarrow> {x}\<close> have "\<forall>x \<in> {x}. f`(x) = ?g`(x)"
      using apply_funtype id_def by auto
    ultimately have "f = ?g" by (rule func_eq)
  } then show  "({x} \<rightarrow> {x}) \<subseteq> {id({x})}" by auto
qed

text\<open>Another trivial fact: identity is the only bijection of a singleton
  with itself.\<close>

lemma single_bij_id: shows "bij({x},{x}) = {id({x})}"
proof
  show "{id({x})} \<subseteq> bij({x},{x})" using id_bij
    by simp
  { fix f assume "f \<in> bij({x},{x})"
    then have "f : {x} \<rightarrow> {x}" using bij_is_fun
      by simp
    then have "f \<in> {id({x})}" using singleton_fun_id
      by simp
  } then show "bij({x},{x}) \<subseteq> {id({x})}" by auto
qed

text\<open>A kind of induction for the identity: if a function
  $f$ is the identity on a set with a fixpoint of $f$
  removed, then it is the indentity on the whole set.\<close>

lemma id_fixpoint_rem: assumes A1: "f:X\<rightarrow>X" and
  A2: "p\<in>X" and A3: "f`(p) = p" and 
  A4: "restrict(f, X-{p}) = id(X-{p})"
  shows "f = id(X)"
proof -
  from A1 have "f: X\<rightarrow>X" and "id(X) : X\<rightarrow>X"
    using id_def by auto
  moreover
  { fix x assume "x\<in>X"
    { assume "x \<in> X-{p}"
      then have "f`(x) = restrict(f, X-{p})`(x)"
	using restrict by simp
      with A4 \<open>x \<in> X-{p}\<close> have "f`(x) = x"
	using id_def by simp }
    with A2 A3 \<open>x\<in>X\<close> have "f`(x) = x" by auto
  } then have "\<forall>x\<in>X. f`(x) = id(X)`(x)"
    using id_def by simp
  ultimately show "f = id(X)" by (rule func_eq)
qed

subsection\<open>Lifting to subsets\<close>

text\<open>Suppose we have a binary operation $f : X \times X \rightarrow X$
  written additively as $f\langle x,y\rangle = x + y$. Such operation
  naturally defines another binary operation on the subsets of $X$
  that satisfies $A+B = \{ x+y : x \in A, y\in B\}$. This new operation 
  which we will call "$f$ lifted to subsets" inherits many properties
  of $f$, such as associativity, commutativity and existence of the 
  neutral element. This notion is useful for considering interval arithmetics.
\<close>

text\<open>The next definition describes the notion of a binary operation
  lifted to subsets. It is written in a way that might be a bit unexpected,
  but really it is the same as the intuitive definition, but shorter.
  In the definition we take a pair $p \in Pow(X)\times Pow(X)$, say
  $p = \langle A, B\rangle $, where $A,B \subseteq X$. 
  Then we assign this pair of sets the set 
  $\{f\langle x,y \rangle : x\in A, y\in B \} = \{ f(x'): x' \in A\times B\}$
  The set on the right hand side is the same as the image
  of $A\times B$ under $f$. In the definition we don't use $A$ and $B$ symbols,
  but write \<open>fst(p)\<close> and \<open>snd(p)\<close>, resp. Recall that in Isabelle/ZF
  \<open>fst(p)\<close> and  \<open>snd(p)\<close> denote the first and second components
  of an ordered pair $p$.
  See the lemma \<open>lift_subsets_explained\<close> for a more intuitive
  notation.\<close>

definition
  Lift2Subsets (infix "{lifted to subsets of}" 65) where
  "f {lifted to subsets of} X \<equiv> 
  {\<langle>p, f``(fst(p)\<times>snd(p))\<rangle>. p \<in> Pow(X)\<times>Pow(X)}"


text\<open>The lift to subsets defines a binary operation on the subsets.\<close>

lemma lift_subsets_binop: assumes A1: "f : X \<times> X \<rightarrow> Y"
  shows "(f {lifted to subsets of} X) : Pow(X) \<times> Pow(X) \<rightarrow> Pow(Y)"
proof -
  let ?F = "{\<langle>p, f``(fst(p)\<times>snd(p))\<rangle>. p \<in> Pow(X)\<times>Pow(X)}"
  from A1 have "\<forall>p \<in> Pow(X) \<times> Pow(X). f``(fst(p)\<times>snd(p)) \<in> Pow(Y)"
    using func1_1_L6 by simp
  then have "?F : Pow(X) \<times> Pow(X) \<rightarrow> Pow(Y)"
    by (rule ZF_fun_from_total)
  then show ?thesis unfolding Lift2Subsets_def by simp
qed

text\<open>The definition of the lift to subsets rewritten in a more intuitive
  notation. We would like to write the last assertion as
  \<open>F`\<langle>A,B\<rangle> = {f`\<langle>x,y\<rangle>. x \<in> A, y \<in> B}\<close>, but Isabelle/ZF does not allow
  such syntax.\<close>

lemma lift_subsets_explained: assumes A1: "f : X\<times>X \<rightarrow> Y"
  and A2: "A \<subseteq> X"  "B \<subseteq> X" and A3: "F = f {lifted to subsets of} X"
  shows 
  "F`\<langle>A,B\<rangle> \<subseteq> Y" and
  "F`\<langle>A,B\<rangle> = f``(A\<times>B)"
  "F`\<langle>A,B\<rangle> = {f`(p). p \<in> A\<times>B}"
  "F`\<langle>A,B\<rangle> = {f`\<langle>x,y\<rangle> . \<langle>x,y\<rangle> \<in> A\<times>B}"
proof -
  let ?p = "\<langle>A,B\<rangle>"
  from assms have 
    I: "F : Pow(X) \<times> Pow(X) \<rightarrow> Pow(Y)" and  "?p \<in> Pow(X) \<times> Pow(X)"
    using lift_subsets_binop by auto
  moreover from A3 have "F = {\<langle>p, f``(fst(p)\<times>snd(p))\<rangle>. p \<in> Pow(X)\<times>Pow(X)}"
    unfolding  Lift2Subsets_def by simp
  ultimately show "F`\<langle>A,B\<rangle> =  f``(A\<times>B)"
    using  ZF_fun_from_tot_val by auto
  also
  from A1 A2 have "A\<times>B \<subseteq> X\<times>X" by auto
  with A1 have "f``(A\<times>B) = {f`(p). p \<in> A\<times>B}"
    by (rule func_imagedef)
  finally show  "F`\<langle>A,B\<rangle> = {f`(p) . p \<in> A\<times>B}" by simp
  also
  have "\<forall>x\<in>A. \<forall>y \<in> B. f`\<langle>x,y\<rangle> = f`\<langle>x,y\<rangle>" by simp
  then have "{f`(p). p \<in> A\<times>B} = {f`\<langle>x,y\<rangle>.  \<langle>x,y\<rangle> \<in> A\<times>B}"
    by (rule ZF1_1_L4A)
  finally show "F`\<langle>A,B\<rangle> = {f`\<langle>x,y\<rangle> . \<langle>x,y\<rangle> \<in> A\<times>B}"
    by simp
  from A2 I show "F`\<langle>A,B\<rangle> \<subseteq> Y" using apply_funtype by blast
qed

text\<open>A sufficient condition for a point to belong to a result of
  lifting to subsets.\<close>

lemma lift_subset_suff:  assumes A1: "f : X \<times> X \<rightarrow> Y" and 
  A2: "A \<subseteq> X"  "B \<subseteq> X" and A3: "x\<in>A" "y\<in>B" and
  A4: "F = f {lifted to subsets of} X"
  shows "f`\<langle>x,y\<rangle> \<in> F`\<langle>A,B\<rangle>"
proof -
  from A3 have "f`\<langle>x,y\<rangle> \<in> {f`(p) . p \<in> A\<times>B}" by auto
  moreover from A1 A2 A4 have "{f`(p). p \<in> A\<times>B} = F`\<langle>A,B\<rangle> "
    using lift_subsets_explained by simp
  ultimately show "f`\<langle>x,y\<rangle> \<in> F`\<langle>A,B\<rangle>" by simp
qed

text\<open>A kind of converse of \<open>lift_subset_apply\<close>, providing
  a necessary condition for a point to be in the result of lifting to 
  subsets.\<close>

lemma lift_subset_nec: assumes A1: "f : X \<times> X \<rightarrow> Y" and 
  A2: "A \<subseteq> X"  "B \<subseteq> X" and 
  A3: "F = f {lifted to subsets of} X" and
  A4: "z \<in> F`\<langle>A,B\<rangle>"
  shows "\<exists>x y. x\<in>A \<and> y\<in>B \<and> z = f`\<langle>x,y\<rangle>"
proof -
  from A1 A2 A3 have "F`\<langle>A,B\<rangle> = {f`(p). p \<in> A\<times>B}"
    using lift_subsets_explained by simp
  with A4 show ?thesis by auto
qed

text\<open>Lifting to subsets inherits commutativity.\<close>

lemma lift_subset_comm: assumes A1: "f : X \<times> X \<rightarrow> Y" and 
  A2: "f {is commutative on} X" and
  A3: "F = f {lifted to subsets of} X"
  shows "F {is commutative on} Pow(X)"
proof -
  have "\<forall>A \<in> Pow(X). \<forall>B \<in> Pow(X). F`\<langle>A,B\<rangle> = F`\<langle>B,A\<rangle>"
  proof -
    { fix A assume "A \<in> Pow(X)"
      fix B assume "B \<in> Pow(X)"
      have  "F`\<langle>A,B\<rangle> = F`\<langle>B,A\<rangle>"
      proof -
	have "\<forall>z \<in>  F`\<langle>A,B\<rangle>. z \<in>  F`\<langle>B,A\<rangle>"
	proof
	  fix z assume I: "z \<in> F`\<langle>A,B\<rangle>"
	  with A1 A3 \<open>A \<in> Pow(X)\<close> \<open>B \<in> Pow(X)\<close> have 
	    "\<exists>x y. x\<in>A \<and> y\<in>B \<and> z = f`\<langle>x,y\<rangle>"
	    using lift_subset_nec by simp
	  then obtain x y where "x\<in>A" and "y\<in>B" and "z = f`\<langle>x,y\<rangle>"
	    by auto
	  with A2 \<open>A \<in> Pow(X)\<close> \<open>B \<in> Pow(X)\<close> have "z = f`\<langle>y,x\<rangle>"
	    using IsCommutative_def by auto
	  with A1 A3 I \<open>A \<in> Pow(X)\<close> \<open>B \<in> Pow(X)\<close> \<open>x\<in>A\<close> \<open>y\<in>B\<close> 
	  show "z \<in> F`\<langle>B,A\<rangle>" using lift_subset_suff by simp
	qed
	moreover have "\<forall>z \<in>  F`\<langle>B,A\<rangle>. z \<in>  F`\<langle>A,B\<rangle>"
	proof
	  fix z assume I: "z \<in> F`\<langle>B,A\<rangle>"
	  with A1 A3 \<open>A \<in> Pow(X)\<close> \<open>B \<in> Pow(X)\<close> have 
	    "\<exists>x y. x\<in>B \<and> y\<in>A \<and> z = f`\<langle>x,y\<rangle>"
	    using lift_subset_nec by simp
	  then obtain x y where "x\<in>B" and "y\<in>A" and "z = f`\<langle>x,y\<rangle>"
	    by auto
	  with A2 \<open>A \<in> Pow(X)\<close> \<open>B \<in> Pow(X)\<close> have "z = f`\<langle>y,x\<rangle>"
	    using IsCommutative_def by auto
	  with A1 A3 I \<open>A \<in> Pow(X)\<close> \<open>B \<in> Pow(X)\<close> \<open>x\<in>B\<close> \<open>y\<in>A\<close> 
	  show "z \<in> F`\<langle>A,B\<rangle>" using lift_subset_suff by simp
	qed
	ultimately show "F`\<langle>A,B\<rangle> = F`\<langle>B,A\<rangle>" by auto
      qed
    } thus ?thesis by auto
  qed
  then show "F {is commutative on} Pow(X)" 
    unfolding IsCommutative_def by auto
qed

text\<open>Lifting to subsets inherits associativity. 
  To show that 
  $F\langle \langle A,B\rangle C\rangle = F\langle A,F\langle B,C\rangle\rangle$ 
  we prove two inclusions and the proof of the second inclusion is very similar
  to the proof of the first one.\<close>

lemma lift_subset_assoc:  assumes A1: "f : X \<times> X \<rightarrow> X" and 
  A2: "f {is associative on} X" and
  A3: "F = f {lifted to subsets of} X"
  shows "F {is associative on} Pow(X)"
proof -
  from A1 A3 have "F : Pow(X)\<times>Pow(X) \<rightarrow> Pow(X)"
    using lift_subsets_binop by simp
  moreover have "\<forall>A \<in> Pow(X).\<forall>B \<in> Pow(X). \<forall>C \<in> Pow(X). 
    F`\<langle>F`\<langle>A,B\<rangle>,C\<rangle> = F`\<langle>A,F`\<langle>B,C\<rangle>\<rangle>"
  proof -
    { fix A B C
      assume "A \<in> Pow(X)"  "B \<in> Pow(X)"  "C \<in> Pow(X)"
      have "F`\<langle>F`\<langle>A,B\<rangle>,C\<rangle> \<subseteq> F`\<langle>A,F`\<langle>B,C\<rangle>\<rangle>"
      proof
	fix z assume I: "z \<in> F`\<langle>F`\<langle>A,B\<rangle>,C\<rangle>"
	from A1 A3 \<open>A \<in> Pow(X)\<close>  \<open>B \<in> Pow(X)\<close>
	have "F`\<langle>A,B\<rangle> \<in> Pow(X)"
	  using lift_subsets_binop apply_funtype by blast
	with A1 A3 \<open>C \<in> Pow(X)\<close> I have
	  "\<exists>x y. x \<in> F`\<langle>A,B\<rangle> \<and> y \<in> C \<and> z = f`\<langle>x,y\<rangle>"
	  using lift_subset_nec by simp
	then obtain x y where 
	  II: "x \<in> F`\<langle>A,B\<rangle>" and "y \<in> C" and III: "z = f`\<langle>x,y\<rangle>"
	  by auto
	from A1 A3 \<open>A \<in> Pow(X)\<close>  \<open>B \<in> Pow(X)\<close> II have
	  "\<exists> s t. s \<in> A \<and> t \<in> B \<and> x = f`\<langle>s,t\<rangle>"
	  using lift_subset_nec by auto
	then obtain s t where "s\<in>A" and "t\<in>B" and "x = f`\<langle>s,t\<rangle>"
	  by auto
	with A2 \<open>A \<in> Pow(X)\<close>  \<open>B \<in> Pow(X)\<close> \<open>C \<in> Pow(X)\<close> III 
	  \<open>s\<in>A\<close> \<open>t\<in>B\<close> \<open>y\<in>C\<close> have IV: "z = f`\<langle>s, f`\<langle>t,y\<rangle>\<rangle>"
	  using IsAssociative_def by blast
	from A1 A3 \<open>B \<in> Pow(X)\<close>  \<open>C \<in> Pow(X)\<close>  \<open>t\<in>B\<close>  \<open>y\<in>C\<close>
	have "f`\<langle>t,y\<rangle> \<in> F`\<langle>B,C\<rangle>" using lift_subset_suff by simp
	moreover from A1 A3 \<open>B \<in> Pow(X)\<close>  \<open>C \<in> Pow(X)\<close>
	have "F`\<langle>B,C\<rangle> \<subseteq> X" using lift_subsets_binop apply_funtype 
	  by blast
	moreover note A1 A3 \<open>A \<in> Pow(X)\<close> \<open>s\<in>A\<close> IV
	ultimately show "z \<in> F`\<langle>A,F`\<langle>B,C\<rangle>\<rangle>"
	  using lift_subset_suff by simp
      qed
      moreover have "F`\<langle>A,F`\<langle>B,C\<rangle>\<rangle> \<subseteq> F`\<langle>F`\<langle>A,B\<rangle>,C\<rangle>"
      proof
	fix z assume I: "z \<in> F`\<langle>A,F`\<langle>B,C\<rangle>\<rangle>"
	from A1 A3 \<open>B \<in> Pow(X)\<close>  \<open>C \<in> Pow(X)\<close>
	have "F`\<langle>B,C\<rangle> \<in> Pow(X)"
	  using lift_subsets_binop apply_funtype by blast
	with A1 A3 \<open>A \<in> Pow(X)\<close> I have
	  "\<exists>x y. x \<in> A \<and> y \<in> F`\<langle>B,C\<rangle> \<and> z = f`\<langle>x,y\<rangle>"
	  using lift_subset_nec by simp
	then obtain x y where 
	  "x \<in> A" and II: "y \<in> F`\<langle>B,C\<rangle>" and III: "z = f`\<langle>x,y\<rangle>"
	  by auto
	from A1 A3 \<open>B \<in> Pow(X)\<close>  \<open>C \<in> Pow(X)\<close> II have
	  "\<exists> s t. s \<in> B \<and> t \<in> C \<and> y = f`\<langle>s,t\<rangle>"
	  using lift_subset_nec by auto
	then obtain s t where "s\<in>B" and "t\<in>C" and "y = f`\<langle>s,t\<rangle>"
	  by auto
	with III have "z = f`\<langle>x,f`\<langle>s,t\<rangle>\<rangle>" by simp
	moreover from  A2 \<open>A \<in> Pow(X)\<close>  \<open>B \<in> Pow(X)\<close>  \<open>C \<in> Pow(X)\<close>
	  \<open>x\<in>A\<close> \<open>s\<in>B\<close> \<open>t\<in>C\<close> have "f`\<langle>f`\<langle>x,s\<rangle>,t\<rangle> = f`\<langle>x,f`\<langle>s,t\<rangle>\<rangle>"
	  using IsAssociative_def by blast
	ultimately have IV: "z = f`\<langle>f`\<langle>x,s\<rangle>,t\<rangle>" by simp
	from A1 A3 \<open>A \<in> Pow(X)\<close>  \<open>B \<in> Pow(X)\<close>  \<open>x\<in>A\<close>  \<open>s\<in>B\<close>
	have "f`\<langle>x,s\<rangle> \<in> F`\<langle>A,B\<rangle>" using lift_subset_suff by simp
	moreover from A1 A3 \<open>A \<in> Pow(X)\<close>  \<open>B \<in> Pow(X)\<close>
	have "F`\<langle>A,B\<rangle> \<subseteq> X" using lift_subsets_binop apply_funtype 
	  by blast
	moreover note A1 A3 \<open>C \<in> Pow(X)\<close> \<open>t\<in>C\<close> IV
	ultimately show "z \<in> F`\<langle>F`\<langle>A,B\<rangle>,C\<rangle>"
	  using lift_subset_suff by simp
      qed
      ultimately have "F`\<langle>F`\<langle>A,B\<rangle>,C\<rangle> = F`\<langle>A,F`\<langle>B,C\<rangle>\<rangle>" by auto
    } thus ?thesis by auto
  qed
  ultimately show ?thesis unfolding IsAssociative_def
    by auto
qed

subsection\<open>Distributive operations\<close>

text\<open>In this section we deal with pairs of operations such that one is
  distributive with respect to the other, that is 
  $a\cdot (b+c) = a\cdot b + a\cdot c$ and
  $(b+c)\cdot a = b\cdot a + c\cdot a$. We show that this property is 
  preserved under restriction to a set closed with respect to both 
  operations. In \<open>EquivClass1\<close> theory we show that this property is 
  preserved by projections to the quotient space if both operations are 
  congruent with respect to the equivalence relation.\<close>

text\<open>We define distributivity as a statement about three sets. The first 
  set is the set on which the operations act. The second set is the 
  additive operation (a ZF function) and the third is the multiplicative
  operation.\<close>

definition
  "IsDistributive(X,A,M) \<equiv> (\<forall>a\<in>X.\<forall>b\<in>X.\<forall>c\<in>X.
  M`\<langle>a,A`\<langle>b,c\<rangle>\<rangle> = A`\<langle>M`\<langle>a,b\<rangle>,M`\<langle>a,c\<rangle>\<rangle> \<and> 
  M`\<langle>A`\<langle>b,c\<rangle>,a\<rangle> = A`\<langle>M`\<langle>b,a\<rangle>,M`\<langle>c,a\<rangle> \<rangle>)"

text\<open>The essential condition to show that distributivity is preserved by 
  restrictions to sets that are closed with
  respect to both operations.\<close>

lemma func_ZF_7_L1: 
  assumes A1: "IsDistributive(X,A,M)"
  and A2: "Y\<subseteq>X"
  and A3: "Y {is closed under} A"  "Y {is closed under} M"
  and A4: "A\<^sub>r = restrict(A,Y\<times>Y)" "M\<^sub>r = restrict(M,Y\<times>Y)"
  and A5: "a\<in>Y"  "b\<in>Y"  "c\<in>Y"
  shows "M\<^sub>r`\<langle> a,A\<^sub>r`\<langle>b,c\<rangle> \<rangle>  = A\<^sub>r`\<langle> M\<^sub>r`\<langle>a,b\<rangle>,M\<^sub>r`\<langle>a,c\<rangle> \<rangle>  \<and> 
  M\<^sub>r`\<langle> A\<^sub>r`\<langle>b,c\<rangle>,a \<rangle> = A\<^sub>r`\<langle> M\<^sub>r`\<langle>b,a\<rangle>, M\<^sub>r`\<langle>c,a\<rangle> \<rangle>"
proof -
  from A3 A5 have "A`\<langle>b,c\<rangle> \<in> Y"  "M`\<langle>a,b\<rangle> \<in> Y"  "M`\<langle>a,c\<rangle> \<in> Y"
    "M`\<langle>b,a\<rangle> \<in> Y"  "M`\<langle>c,a\<rangle> \<in> Y" using IsOpClosed_def by auto
  with A5 A4 have 
    "A\<^sub>r`\<langle>b,c\<rangle> \<in> Y"  "M\<^sub>r`\<langle>a,b\<rangle> \<in> Y"  "M\<^sub>r`\<langle>a,c\<rangle> \<in> Y"
    "M\<^sub>r`\<langle>b,a\<rangle> \<in> Y"  "M\<^sub>r`\<langle>c,a\<rangle> \<in> Y"
    using restrict by auto
  with A1 A2 A4 A5 show ?thesis
    using restrict IsDistributive_def by auto
qed
  
text\<open>Distributivity is preserved by restrictions to sets that are closed with
  respect to both operations.\<close>

lemma func_ZF_7_L2: 
  assumes "IsDistributive(X,A,M)"
  and "Y\<subseteq>X"
  and "Y {is closed under} A" 
  "Y {is closed under} M"
  and "A\<^sub>r = restrict(A,Y\<times>Y)" "M\<^sub>r = restrict(M,Y\<times>Y)"
  shows "IsDistributive(Y,A\<^sub>r,M\<^sub>r)"
proof -
  from assms have "\<forall>a\<in>Y.\<forall>b\<in>Y.\<forall>c\<in>Y. 
    M\<^sub>r`\<langle> a,A\<^sub>r`\<langle>b,c\<rangle> \<rangle> = A\<^sub>r`\<langle> M\<^sub>r`\<langle>a,b\<rangle>,M\<^sub>r`\<langle>a,c\<rangle> \<rangle> \<and> 
    M\<^sub>r`\<langle> A\<^sub>r`\<langle>b,c\<rangle>,a \<rangle> = A\<^sub>r`\<langle> M\<^sub>r`\<langle>b,a\<rangle>,M\<^sub>r`\<langle>c,a\<rangle>\<rangle>"
    using func_ZF_7_L1 by simp
  then show ?thesis using IsDistributive_def by simp
qed


end
