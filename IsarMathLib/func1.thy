(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2005 - 2019  Slawomir Kolodynski

    This program is free software Redistribution and use in source and binary forms, 
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
PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES LOSS OF USE, DATA, OR PROFITS 
OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, 
WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR 
OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, 
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. *)

section \<open>Functions - introduction\<close>

theory func1 imports ZF.func Fol1 ZF1

begin

text\<open>This theory covers basic properties of function spaces.
  A set of functions with domain $X$ and values in the set $Y$
  is denoted in Isabelle as $X\rightarrow Y$. It just happens
  that the colon ":" is a synonym of the set membership symbol
  $\in$ in Isabelle/ZF so we can write $f:X\rightarrow Y$ instead of 
  $f \in X\rightarrow Y$. This is the only case that we use the colon 
  instead of the regular set membership symbol.\<close>

subsection\<open>Properties of functions, function spaces and (inverse) images.\<close>

text\<open>Functions in ZF are sets of pairs. This means
  that if $f: X\rightarrow Y $ then $f\subseteq X\times Y$.
  This section is mostly about consequences of this understanding 
  of the notion of function.
\<close>

text\<open>We define the notion of function that preserves a collection here.
  Given two collection of sets a function preserves the collections if 
  the inverse image of sets in one collection belongs to the second one.
  This notion does not have a name in romantic math. It is used to define 
  continuous functions in \<open>Topology_ZF_2\<close> theory. 
  We define it here so that we can 
  use it for other purposes, like defining measurable functions.
  Recall that \<open>f-``(A)\<close> means the inverse image of the set $A$.\<close>

definition
  "PresColl(f,S,T) \<equiv> \<forall> A\<in>T. f-``(A)\<in>S"

text\<open>A definition that allows to get the first factor of the
  domain of a binary function $f: X\times Y \rightarrow Z$.\<close>

definition
  "fstdom(f) \<equiv> domain(domain(f))"

text\<open>If a function maps $A$ into another set, then $A$ is the 
  domain of the function.\<close>

lemma func1_1_L1: assumes "f:A\<rightarrow>C" shows "domain(f) = A"
  using assms domain_of_fun by simp

text\<open>Standard Isabelle defines a \<open>function(f)\<close> predicate.
  The next lemma shows that our functions satisfy that predicate. 
  It is a special version of Isabelle's \<open>fun_is_function\<close>.\<close>

lemma fun_is_fun: assumes "f:X\<rightarrow>Y" shows "function(f)"
  using assms fun_is_function by simp

text\<open>A lemma explains what \<open>fstdom\<close> is for.\<close>

lemma fstdomdef: assumes A1: "f: X\<times>Y \<rightarrow> Z" and A2: "Y\<noteq>0" 
  shows "fstdom(f) = X"
proof -
  from A1 have "domain(f) = X\<times>Y" using func1_1_L1
    by simp
  with A2 show "fstdom(f) = X" unfolding fstdom_def by auto
qed

text\<open>A version of the \<open>Pi_type\<close> lemma from the standard Isabelle/ZF library.\<close>

lemma func1_1_L1A: assumes A1: "f:X\<rightarrow>Y" and A2: "\<forall>x\<in>X. f`(x) \<in> Z"
  shows "f:X\<rightarrow>Z"
proof -
  { fix x assume "x\<in>X" 
    with A2 have "f`(x) \<in> Z" by simp }
  with A1 show "f:X\<rightarrow>Z" by (rule Pi_type)
qed

text\<open>A variant of \<open>func1_1_L1A\<close>.\<close>

lemma func1_1_L1B: assumes A1: "f:X\<rightarrow>Y" and A2: "Y\<subseteq>Z"
  shows "f:X\<rightarrow>Z"
proof -
  from A1 A2 have "\<forall>x\<in>X. f`(x) \<in> Z"
    using apply_funtype by auto
  with A1 show  "f:X\<rightarrow>Z" using func1_1_L1A by blast
qed

text\<open>There is a value for each argument.\<close>

lemma func1_1_L2: assumes A1: "f:X\<rightarrow>Y"  "x\<in>X" 
  shows "\<exists>y\<in>Y. \<langle>x,y\<rangle> \<in> f"  
proof-
  from A1 have "f`(x) \<in> Y" using apply_type by simp
  moreover from A1 have "\<langle> x,f`(x)\<rangle>\<in> f" using apply_Pair by simp
  ultimately show ?thesis by auto
qed

text\<open>The inverse image is the image of converse. True for relations as well.\<close>

lemma vimage_converse: shows "r-``(A) = converse(r)``(A)"
  using vimage_iff image_iff converse_iff by auto

text\<open>The image is the inverse image of converse.\<close>

lemma image_converse: shows "converse(r)-``(A) = r``(A)"
  using vimage_iff image_iff converse_iff by auto

text\<open>The inverse image by a composition is the composition of inverse images.\<close>

lemma vimage_comp: shows "(r O s)-``(A) = s-``(r-``(A))"
  using vimage_converse converse_comp image_comp image_converse by simp 

text\<open>A version of \<open>vimage_comp\<close> for three functions.\<close>

lemma vimage_comp3: shows "(r O s O t)-``(A) = t-``(s-``(r-``(A)))"
  using vimage_comp by simp

text\<open>Inverse image of any set is contained in the domain.\<close>

lemma func1_1_L3: assumes A1: "f:X\<rightarrow>Y" shows "f-``(D) \<subseteq> X"
proof-
   have "\<forall>x. x\<in>f-``(D) \<longrightarrow> x \<in> domain(f)"
      using  vimage_iff domain_iff by auto
    with A1 have "\<forall>x. (x \<in> f-``(D)) \<longrightarrow> (x\<in>X)" using func1_1_L1 by simp
    then show ?thesis by auto
qed

text\<open>The inverse image of the range is the domain.\<close>

lemma func1_1_L4: assumes "f:X\<rightarrow>Y" shows "f-``(Y) = X"
  using assms func1_1_L3 func1_1_L2 vimage_iff by blast

text\<open>The arguments belongs to the domain and values to the range.\<close>

lemma func1_1_L5: 
  assumes A1: "\<langle> x,y\<rangle> \<in> f" and A2: "f:X\<rightarrow>Y"  
  shows "x\<in>X \<and> y\<in>Y" 
proof
  from A1 A2 show "x\<in>X" using apply_iff by simp
  with A2 have "f`(x)\<in> Y" using apply_type by simp
  with A1 A2 show "y\<in>Y" using apply_iff by simp
qed

text\<open>Function is a subset of cartesian product.\<close>

lemma fun_subset_prod: assumes A1: "f:X\<rightarrow>Y" shows "f \<subseteq> X\<times>Y"
proof
  fix p assume "p \<in> f"
  with A1 have "\<exists>x\<in>X. p = \<langle>x, f`(x)\<rangle>"
    using Pi_memberD by simp
  then obtain x where I: "p = \<langle>x, f`(x)\<rangle>"
    by auto
  with A1 \<open>p \<in> f\<close> have "x\<in>X \<and> f`(x) \<in> Y"
    using func1_1_L5 by blast
  with I show "p \<in> X\<times>Y" by auto
qed
  
text\<open>The (argument, value) pair belongs to the graph of the function.\<close>

lemma func1_1_L5A: 
  assumes A1: "f:X\<rightarrow>Y"  "x\<in>X"  "y = f`(x)"
  shows "\<langle>x,y\<rangle> \<in> f"  "y \<in> range(f)" 
proof -
  from A1 show "\<langle>x,y\<rangle> \<in> f" using apply_Pair by simp
  then show "y \<in> range(f)" using rangeI by simp
qed

text\<open>The next theorem illustrates the meaning of the concept of 
  function in ZF.\<close>

theorem fun_is_set_of_pairs: assumes A1: "f:X\<rightarrow>Y"
  shows "f = {\<langle>x, f`(x)\<rangle>. x \<in> X}"
proof
  from A1 show "{\<langle>x, f`(x)\<rangle>. x \<in> X} \<subseteq> f" using func1_1_L5A
    by auto
next
  { fix p assume "p \<in> f"
    with A1 have "p \<in> X\<times>Y" using fun_subset_prod
      by auto
    with A1 \<open>p \<in> f\<close> have "p \<in> {\<langle>x, f`(x)\<rangle>. x \<in> X}" 
      using apply_equality by auto
  } thus "f \<subseteq> {\<langle>x, f`(x)\<rangle>. x \<in> X}" by auto
qed

text\<open>The range of function that maps $X$ into $Y$ is contained in $Y$.\<close>

lemma func1_1_L5B: 
  assumes  A1: "f:X\<rightarrow>Y" shows "range(f) \<subseteq> Y"
proof
  fix y assume "y \<in> range(f)"
  then obtain x where "\<langle> x,y\<rangle> \<in> f"
    using range_def converse_def domain_def by auto
  with A1 show "y\<in>Y" using func1_1_L5 by blast
qed

text\<open>The image of any set is contained in the range.\<close>

lemma func1_1_L6: assumes A1: "f:X\<rightarrow>Y" 
  shows "f``(B) \<subseteq> range(f)" and "f``(B) \<subseteq> Y"
proof -
  show "f``(B) \<subseteq> range(f)" using image_iff rangeI by auto
  with A1 show "f``(B) \<subseteq> Y" using func1_1_L5B by blast
qed  

text\<open>The inverse image of any set is contained in the domain.\<close>

lemma func1_1_L6A: assumes A1: "f:X\<rightarrow>Y" shows "f-``(A)\<subseteq>X"
proof
  fix x
  assume A2: "x\<in>f-``(A)" then obtain y where "\<langle> x,y\<rangle> \<in> f" 
    using vimage_iff by auto
  with A1 show  "x\<in>X" using func1_1_L5 by fast
qed

text\<open>Image of a greater set is greater.\<close>

lemma func1_1_L8: assumes A1: "A\<subseteq>B"  shows "f``(A)\<subseteq> f``(B)"
  using assms image_Un by auto

text\<open>A set is contained in the the inverse image of its image.
  There is similar theorem in \<open>equalities.thy\<close>
  (\<open>function_image_vimage\<close>)
  which shows that the image of inverse image of a set 
  is contained in the set.\<close>

lemma func1_1_L9: assumes A1: "f:X\<rightarrow>Y" and A2: "A\<subseteq>X"
  shows "A \<subseteq> f-``(f``(A))"
proof -
  from A1 A2 have "\<forall>x\<in>A. \<langle> x,f`(x)\<rangle> \<in> f"  using apply_Pair by auto
  then show ?thesis using image_iff by auto
qed

text\<open>The inverse image of the image of the domain is the domain.\<close>

lemma inv_im_dom: assumes A1: "f:X\<rightarrow>Y" shows "f-``(f``(X)) = X"
proof
  from A1 show "f-``(f``(X)) \<subseteq> X" using func1_1_L3 by simp
  from A1 show "X \<subseteq> f-``(f``(X))" using func1_1_L9 by simp
qed

text\<open>A technical lemma needed to make the \<open>func1_1_L11\<close> 
  proof more clear.\<close>

lemma func1_1_L10: 
  assumes A1: "f \<subseteq> X\<times>Y" and A2: "\<exists>!y. (y\<in>Y \<and> \<langle>x,y\<rangle> \<in> f)"
  shows "\<exists>!y. \<langle>x,y\<rangle> \<in> f"
proof
  from A2 show "\<exists>y. \<langle>x, y\<rangle> \<in> f" by auto
  fix y n assume "\<langle>x,y\<rangle> \<in> f" and "\<langle>x,n\<rangle> \<in> f"
  with A1 A2 show "y=n" by auto
qed

text\<open>If $f\subseteq X\times Y$ and for every $x\in X$ there is exactly 
one $y\in Y$ such that $(x,y)\in f$ then $f$ maps $X$ to $Y$.\<close>

lemma func1_1_L11: 
  assumes "f \<subseteq> X\<times>Y" and "\<forall>x\<in>X. \<exists>!y. y\<in>Y \<and> \<langle>x,y\<rangle> \<in> f"
  shows "f: X\<rightarrow>Y" using assms func1_1_L10 Pi_iff_old by simp

text\<open>A set defined by a lambda-type expression is a fuction. There is a 
  similar lemma in func.thy, but I had problems with lambda expressions syntax
  so I could not apply it. This lemma is a workaround for this. Besides, lambda
  expressions are not readable.
\<close>

lemma func1_1_L11A: assumes A1: "\<forall>x\<in>X. b(x) \<in> Y"
  shows "{\<langle> x,y\<rangle> \<in> X\<times>Y. b(x) = y} : X\<rightarrow>Y"
proof -
  let ?f = "{\<langle> x,y\<rangle> \<in> X\<times>Y. b(x) = y}"
  have "?f \<subseteq> X\<times>Y" by auto
  moreover have "\<forall>x\<in>X. \<exists>!y. y\<in>Y \<and> \<langle> x,y\<rangle> \<in> ?f"
  proof
    fix x assume A2: "x\<in>X"
    show "\<exists>!y. y\<in>Y \<and> \<langle>x, y\<rangle> \<in> {\<langle>x,y\<rangle> \<in> X\<times>Y . b(x) = y}"
    proof
      from A2 A1 show 
        "\<exists>y. y\<in>Y \<and> \<langle>x, y\<rangle> \<in> {\<langle>x,y\<rangle> \<in> X\<times>Y . b(x) = y}"
	by simp
    next
      fix y y1
      assume "y\<in>Y \<and> \<langle>x, y\<rangle> \<in> {\<langle>x,y\<rangle> \<in> X\<times>Y . b(x) = y}"
	and "y1\<in>Y \<and> \<langle>x, y1\<rangle> \<in> {\<langle>x,y\<rangle> \<in> X\<times>Y . b(x) = y}"
      then show "y = y1" by simp
    qed
  qed
  ultimately show "{\<langle> x,y\<rangle> \<in> X\<times>Y. b(x) = y} : X\<rightarrow>Y" 
    using func1_1_L11 by simp
qed

text\<open>The next lemma will replace \<open>func1_1_L11A\<close> one day.\<close>

lemma ZF_fun_from_total: assumes A1: "\<forall>x\<in>X. b(x) \<in> Y"
  shows "{\<langle>x,b(x)\<rangle>. x\<in>X} : X\<rightarrow>Y"
proof -
  let ?f = "{\<langle>x,b(x)\<rangle>. x\<in>X}"
  { fix x assume A2: "x\<in>X"
    have "\<exists>!y. y\<in>Y \<and> \<langle>x, y\<rangle> \<in> ?f"
    proof
	from A1 A2 show "\<exists>y. y\<in>Y \<and> \<langle>x, y\<rangle> \<in> ?f"
	by simp
    next fix y y1 assume "y\<in>Y \<and> \<langle>x, y\<rangle> \<in> ?f"
	and "y1\<in>Y \<and> \<langle>x, y1\<rangle> \<in> ?f"
      then show "y = y1" by simp
    qed
  } then have "\<forall>x\<in>X. \<exists>!y. y\<in>Y \<and> \<langle> x,y\<rangle> \<in> ?f"
    by simp
  moreover from A1 have "?f \<subseteq> X\<times>Y" by auto
  ultimately show ?thesis using func1_1_L11
    by simp
qed
 
text\<open>The value of a function defined by a meta-function is this 
  meta-function.\<close>

lemma func1_1_L11B: 
  assumes A1: "f:X\<rightarrow>Y"   "x\<in>X"
  and A2: "f = {\<langle> x,y\<rangle> \<in> X\<times>Y. b(x) = y}"
  shows "f`(x) = b(x)"
proof -
  from A1 have "\<langle> x,f`(x)\<rangle> \<in> f" using apply_iff by simp
  with A2 show ?thesis by simp
qed

text\<open>The next lemma will replace \<open>func1_1_L11B\<close> one day.\<close>

lemma ZF_fun_from_tot_val: 
  assumes A1: "f:X\<rightarrow>Y"   "x\<in>X"
  and A2: "f = {\<langle>x,b(x)\<rangle>. x\<in>X}"
  shows "f`(x) = b(x)"
proof -
  from A1 have "\<langle> x,f`(x)\<rangle> \<in> f" using apply_iff by simp
   with A2 show ?thesis by simp
qed

text\<open>Identical meaning as \<open> ZF_fun_from_tot_val\<close>, but
  phrased a bit differently.\<close>

lemma ZF_fun_from_tot_val0: 
  assumes "f:X\<rightarrow>Y" and "f = {\<langle>x,b(x)\<rangle>. x\<in>X}"
  shows "\<forall>x\<in>X. f`(x) = b(x)"
  using assms ZF_fun_from_tot_val by simp

text\<open>Another way of expressing that lambda expression is a function.\<close>

lemma lam_is_fun_range: assumes "f={\<langle>x,g(x)\<rangle>. x\<in>X}"
  shows "f:X\<rightarrow>range(f)"
proof -
  have "\<forall>x\<in>X. g(x) \<in> range({\<langle>x,g(x)\<rangle>. x\<in>X})" unfolding range_def 
    by auto
  then have "{\<langle>x,g(x)\<rangle>. x\<in>X} : X\<rightarrow>range({\<langle>x,g(x)\<rangle>. x\<in>X})" by (rule ZF_fun_from_total)
  with assms show ?thesis by auto
qed

text\<open>Yet another way of expressing value of a function.\<close>

lemma ZF_fun_from_tot_val1:
  assumes "x\<in>X" shows "{\<langle>x,b(x)\<rangle>. x\<in>X}`(x)=b(x)"
proof -
  let ?f = "{\<langle>x,b(x)\<rangle>. x\<in>X}"
  have "?f:X\<rightarrow>range(?f)" using lam_is_fun_range by simp
  with assms show ?thesis using ZF_fun_from_tot_val0 by simp
qed

text\<open>We can extend a function by specifying its values on a set
  disjoint with the domain.\<close>

lemma func1_1_L11C: assumes A1: "f:X\<rightarrow>Y" and A2: "\<forall>x\<in>A. b(x)\<in>B"
  and A3: "X\<inter>A = 0" and Dg: "g = f \<union> {\<langle>x,b(x)\<rangle>. x\<in>A}"
  shows 
  "g : X\<union>A \<rightarrow> Y\<union>B"
  "\<forall>x\<in>X. g`(x) = f`(x)"
  "\<forall>x\<in>A. g`(x) = b(x)"
proof -
  let ?h = "{\<langle>x,b(x)\<rangle>. x\<in>A}"
  from A1 A2 A3 have 
    I: "f:X\<rightarrow>Y"  "?h : A\<rightarrow>B"  "X\<inter>A = 0"
    using ZF_fun_from_total by auto
  then have "f\<union>?h : X\<union>A \<rightarrow> Y\<union>B"
    by (rule fun_disjoint_Un)
  with Dg show "g : X\<union>A \<rightarrow> Y\<union>B" by simp
  { fix x assume A4: "x\<in>A"
    with A1 A3 have "(f\<union>?h)`(x) = ?h`(x)"
      using func1_1_L1 fun_disjoint_apply2
      by blast
    moreover from I A4 have "?h`(x) = b(x)"
      using ZF_fun_from_tot_val by simp
    ultimately have "(f\<union>?h)`(x) = b(x)"
      by simp
  } with Dg show "\<forall>x\<in>A. g`(x) = b(x)" by simp
  { fix x assume A5: "x\<in>X"
    with A3 I have "x \<notin> domain(?h)"
      using func1_1_L1 by auto
    then have "(f\<union>?h)`(x) = f`(x)"
      using fun_disjoint_apply1 by simp
  } with Dg show "\<forall>x\<in>X. g`(x) = f`(x)" by simp
qed

text\<open>We can extend a function by specifying its value at a point that
  does not belong to the domain.\<close>

lemma func1_1_L11D: assumes A1: "f:X\<rightarrow>Y" and A2: "a\<notin>X"
  and Dg: "g = f \<union> {\<langle>a,b\<rangle>}"
  shows 
  "g : X\<union>{a} \<rightarrow> Y\<union>{b}"
  "\<forall>x\<in>X. g`(x) = f`(x)"
  "g`(a) = b"
proof -
  let ?h = "{\<langle>a,b\<rangle>}"
  from A1 A2 Dg have I:
    "f:X\<rightarrow>Y"  "\<forall>x\<in>{a}. b\<in>{b}"  "X\<inter>{a} = 0"  "g = f \<union> {\<langle>x,b\<rangle>. x\<in>{a}}"
    by auto
  then show "g : X\<union>{a} \<rightarrow> Y\<union>{b}"
    by (rule func1_1_L11C)
  from I show "\<forall>x\<in>X. g`(x) = f`(x)"
    by (rule func1_1_L11C)
  from I have "\<forall>x\<in>{a}. g`(x) = b"
    by (rule func1_1_L11C)
  then show "g`(a) = b" by auto
qed

text\<open>A technical lemma about extending a function both by defining
  on a set disjoint with the domain and on a point that does not belong
  to any of those sets.\<close>

lemma func1_1_L11E:
  assumes A1: "f:X\<rightarrow>Y" and 
  A2: "\<forall>x\<in>A. b(x)\<in>B" and 
  A3: "X\<inter>A = 0" and A4: "a\<notin> X\<union>A"
  and Dg: "g = f \<union> {\<langle>x,b(x)\<rangle>. x\<in>A} \<union> {\<langle>a,c\<rangle>}"
  shows
  "g : X\<union>A\<union>{a} \<rightarrow> Y\<union>B\<union>{c}"
  "\<forall>x\<in>X. g`(x) = f`(x)"
  "\<forall>x\<in>A. g`(x) = b(x)"
  "g`(a) = c"
proof -
  let ?h = "f \<union> {\<langle>x,b(x)\<rangle>. x\<in>A}"
  from assms show "g : X\<union>A\<union>{a} \<rightarrow> Y\<union>B\<union>{c}"
    using func1_1_L11C func1_1_L11D by simp
  from A1 A2 A3 have I:
    "f:X\<rightarrow>Y"  "\<forall>x\<in>A. b(x)\<in>B"  "X\<inter>A = 0"  "?h = f \<union> {\<langle>x,b(x)\<rangle>. x\<in>A}"
    by auto
  from assms have 
    II: "?h : X\<union>A \<rightarrow> Y\<union>B"  "a\<notin> X\<union>A"  "g = ?h \<union> {\<langle>a,c\<rangle>}"
    using func1_1_L11C by auto
  then have III: "\<forall>x\<in>X\<union>A. g`(x) = ?h`(x)" by (rule func1_1_L11D)
  moreover from I have  "\<forall>x\<in>X. ?h`(x) = f`(x)"
    by (rule func1_1_L11C)
  ultimately show "\<forall>x\<in>X. g`(x) = f`(x)" by simp
  from I have "\<forall>x\<in>A. ?h`(x) = b(x)" by (rule func1_1_L11C)
  with III show "\<forall>x\<in>A. g`(x) = b(x)" by simp
  from II show "g`(a) = c" by (rule func1_1_L11D)
qed

text\<open>A way of defining a function on a union of two possibly overlapping sets. We decompose the 
union into two differences and the intersection and define a function separately on each part.\<close>

lemma fun_union_overlap: assumes "\<forall>x\<in>A\<inter>B. h(x) \<in> Y"  "\<forall>x\<in>A-B. f(x) \<in> Y"  "\<forall>x\<in>B-A. g(x) \<in> Y"
  shows "{\<langle>x,if x\<in>A-B then f(x) else if x\<in>B-A then g(x) else h(x)\<rangle>. x \<in> A\<union>B}: A\<union>B \<rightarrow> Y"
proof -
  let ?F = "{\<langle>x,if x\<in>A-B then f(x) else if x\<in>B-A then g(x) else h(x)\<rangle>. x \<in> A\<inter>B}"
  from assms have "\<forall>x\<in>A\<union>B. (if x\<in>A-B then f(x) else if x\<in>B-A then g(x) else h(x)) \<in> Y"
    by auto
  then show ?thesis by (rule ZF_fun_from_total)
qed

text\<open>Inverse image of intersection is the intersection of inverse images.\<close>

lemma invim_inter_inter_invim: assumes "f:X\<rightarrow>Y"
  shows "f-``(A\<inter>B) = f-``(A) \<inter> f-``(B)"
  using assms fun_is_fun function_vimage_Int by simp

text\<open>The inverse image of an intersection of a nonempty collection of sets 
  is the intersection of the 
  inverse images. This generalizes \<open>invim_inter_inter_invim\<close> 
  which is proven for the case of two sets.\<close>

lemma func1_1_L12:
  assumes A1: "B \<subseteq> Pow(Y)" and A2: "B\<noteq>0" and A3: "f:X\<rightarrow>Y"
  shows "f-``(\<Inter>B) = (\<Inter>U\<in>B. f-``(U))"
proof
  from A2 show  "f-``(\<Inter>B) \<subseteq> (\<Inter>U\<in>B. f-``(U))" by blast
  show "(\<Inter>U\<in>B. f-``(U)) \<subseteq> f-``(\<Inter>B)"
  proof
    fix x assume A4: "x \<in> (\<Inter>U\<in>B. f-``(U))"
    from A3 have "\<forall>U\<in>B. f-``(U) \<subseteq> X" using func1_1_L6A by simp
    with A4 have "\<forall>U\<in>B. x\<in>X" by auto
    with A2 have "x\<in>X" by auto
    with A3 have "\<exists>!y. \<langle> x,y\<rangle> \<in> f" using Pi_iff_old by simp
    with A2 A4 show "x \<in> f-``(\<Inter>B)" using vimage_iff by blast
  qed
qed


text\<open>The inverse image of a set does not change when we intersect
  the set with the image of the domain.\<close>

lemma inv_im_inter_im: assumes "f:X\<rightarrow>Y" 
  shows "f-``(A \<inter> f``(X)) = f-``(A)"
  using assms invim_inter_inter_invim inv_im_dom func1_1_L6A
  by blast

text\<open>If the inverse image of a set is not empty, then the set is not empty.
  Proof by contradiction.\<close>

lemma func1_1_L13: assumes A1:"f-``(A) \<noteq> 0" shows "A\<noteq>0"
  using assms by auto

text\<open>If the image of a set is not empty, then the set is not empty.
  Proof by contradiction.\<close>

lemma func1_1_L13A: assumes A1: "f``(A)\<noteq>0" shows "A\<noteq>0"
  using assms by auto

text\<open>What is the inverse image of a singleton?\<close>

lemma func1_1_L14: assumes "f\<in>X\<rightarrow>Y" 
  shows "f-``({y}) = {x\<in>X. f`(x) = y}" 
  using assms func1_1_L6A vimage_singleton_iff apply_iff by auto

text\<open>A lemma that can be used instead \<open>fun_extension_iff\<close>
  to show that two functions are equal\<close>

lemma func_eq: assumes "f: X\<rightarrow>Y"  "g: X\<rightarrow>Z"
  and  "\<forall>x\<in>X. f`(x) = g`(x)"
  shows "f = g" using assms fun_extension_iff by simp

text\<open>Function defined on a singleton is a single pair.\<close>

lemma func_singleton_pair: assumes A1: "f : {a}\<rightarrow>X"
  shows "f = {\<langle>a, f`(a)\<rangle>}"
proof -
  let ?g = "{\<langle>a, f`(a)\<rangle>}"
  note A1
  moreover have "?g : {a} \<rightarrow> {f`(a)}" using singleton_fun by simp
  moreover have "\<forall>x \<in> {a}. f`(x) = ?g`(x)" using singleton_apply
    by simp
  ultimately show "f = ?g" by (rule func_eq)
qed

text\<open>A single pair is a function on a singleton. This is
  similar to \<open>singleton_fun\<close> from standard Isabelle/ZF.\<close>

lemma pair_func_singleton: assumes A1: "y \<in> Y"
  shows "{\<langle>x,y\<rangle>} : {x} \<rightarrow> Y"
proof -
  have "{\<langle>x,y\<rangle>} : {x} \<rightarrow> {y}" using singleton_fun by simp
  moreover from A1 have "{y} \<subseteq> Y" by simp
  ultimately show "{\<langle>x,y\<rangle>} : {x} \<rightarrow> Y"
    by (rule func1_1_L1B)
qed

text\<open>The value of a pair on the first element is the second one.\<close>

lemma pair_val: shows "{\<langle>x,y\<rangle>}`(x) = y"
  using singleton_fun apply_equality by simp
  
text\<open>A more familiar definition of inverse image.\<close>

lemma func1_1_L15: assumes A1: "f:X\<rightarrow>Y"
  shows "f-``(A) = {x\<in>X. f`(x) \<in> A}"
proof -
  have "f-``(A) = (\<Union>y\<in>A . f-``{y})" 
    by (rule vimage_eq_UN)
  with A1 show ?thesis using func1_1_L14 by auto
qed

text\<open>A more familiar definition of image.\<close>

lemma func_imagedef: assumes A1: "f:X\<rightarrow>Y" and A2: "A\<subseteq>X"
  shows "f``(A) = {f`(x). x \<in> A}"
proof
  from A1 show "f``(A) \<subseteq> {f`(x). x \<in> A}"
    using image_iff apply_iff by auto
  show "{f`(x). x \<in> A} \<subseteq> f``(A)"
  proof
    fix y assume "y \<in> {f`(x). x \<in> A}"
    then obtain x where "x\<in>A" and  "y = f`(x)"
      by auto
    with A1 A2 have "\<langle>x,y\<rangle> \<in> f" using apply_iff by force  
    with A1 A2 \<open>x\<in>A\<close> show "y \<in> f``(A)" using image_iff by auto
  qed
qed

text\<open>The image of a set contained in domain under identity is the same set.\<close>

lemma image_id_same: assumes "A\<subseteq>X" shows "id(X)``(A) = A"
  using assms id_type id_conv by auto

text\<open>The inverse image of a set contained in domain under identity is the same set.\<close>

lemma vimage_id_same: assumes "A\<subseteq>X" shows "id(X)-``(A) = A"
  using assms id_type id_conv by auto

text\<open>What is the image of a singleton?\<close>

lemma singleton_image: 
  assumes "f\<in>X\<rightarrow>Y" and "x\<in>X"
  shows "f``{x} = {f`(x)}"
  using assms func_imagedef by auto

text\<open>If an element of the domain of a function belongs to a set, 
  then its value belongs to the imgage of that set.\<close>

lemma func1_1_L15D: assumes "f:X\<rightarrow>Y"  "x\<in>A"  "A\<subseteq>X"
  shows "f`(x) \<in> f``(A)"
  using assms func_imagedef by auto

text\<open>Range is the image of the domain. Isabelle/ZF defines
  \<open>range(f)\<close> as \<open>domain(converse(f))\<close>,
  and that's why we have something to prove here.\<close>

lemma range_image_domain: 
  assumes A1: "f:X\<rightarrow>Y" shows "f``(X) = range(f)"
proof
  show "f``(X) \<subseteq> range(f)" using image_def by auto
  { fix y assume "y \<in> range(f)"
    then obtain x where "\<langle>y,x\<rangle> \<in> converse(f)" by auto
    with A1 have "x\<in>X" using func1_1_L5 by blast
    with A1 have "f`(x) \<in> f``(X)" using func_imagedef
      by auto
    with A1  \<open>\<langle>y,x\<rangle> \<in> converse(f)\<close> have "y \<in> f``(X)"
      using apply_equality by auto
  } then show "range(f) \<subseteq> f``(X)" by auto
qed
    
text\<open>The difference of images is contained in the image of difference.\<close>

lemma diff_image_diff: assumes A1: "f: X\<rightarrow>Y" and A2: "A\<subseteq>X"
  shows "f``(X) - f``(A) \<subseteq> f``(X-A)"
proof
  fix y assume "y \<in> f``(X) - f``(A)"
  hence "y \<in> f``(X)" and I: "y \<notin> f``(A)" by auto
  with A1 obtain x where "x\<in>X" and II: "y = f`(x)"
    using func_imagedef by auto
  with A1 A2 I have "x\<notin>A"
    using func1_1_L15D by auto
  with \<open>x\<in>X\<close> have "x \<in> X-A" "X-A \<subseteq> X" by auto
  with A1 II show "y \<in> f``(X-A)"
    using func1_1_L15D by simp
qed

text\<open>The image of an intersection is contained in the 
  intersection of the images.\<close>

lemma image_of_Inter: assumes  A1: "f:X\<rightarrow>Y" and
  A2: "I\<noteq>0" and A3: "\<forall>i\<in>I. P(i) \<subseteq> X"
  shows "f``(\<Inter>i\<in>I. P(i)) \<subseteq> ( \<Inter>i\<in>I. f``(P(i)) )"
proof
  fix y assume A4: "y \<in> f``(\<Inter>i\<in>I. P(i))"
  from A1 A2 A3 have "f``(\<Inter>i\<in>I. P(i)) = {f`(x). x \<in> ( \<Inter>i\<in>I. P(i) )}"
    using ZF1_1_L7 func_imagedef by simp
  with A4 obtain x where "x \<in> ( \<Inter>i\<in>I. P(i) )" and "y = f`(x)"
    by auto
  with A1 A2 A3 show "y \<in> ( \<Inter>i\<in>I. f``(P(i)) )" using func_imagedef
    by auto
qed

text\<open>The image of union is the union of images.\<close>

lemma image_of_Union: assumes A1: "f:X\<rightarrow>Y" and A2: "\<forall>A\<in>M. A\<subseteq>X"
  shows "f``(\<Union>M) = \<Union>{f``(A). A\<in>M}"
proof
  from A2 have "\<Union>M \<subseteq> X" by auto
  { fix y assume "y \<in> f``(\<Union>M)"
    with A1 \<open>\<Union>M \<subseteq> X\<close> obtain x where "x\<in>\<Union>M" and I: "y = f`(x)" 
      using func_imagedef by auto
    then obtain A where "A\<in>M" and "x\<in>A" by auto
    with assms I have "y \<in> \<Union>{f``(A). A\<in>M}" using func_imagedef by auto
  } thus "f``(\<Union>M) \<subseteq> \<Union>{f``(A). A\<in>M}" by auto
  { fix y assume "y \<in> \<Union>{f``(A). A\<in>M}"
    then obtain A where "A\<in>M" and "y \<in> f``(A)" by auto
    with assms \<open>\<Union>M \<subseteq> X\<close> have "y \<in> f``(\<Union>M)" using func_imagedef by auto
  } thus "\<Union>{f``(A). A\<in>M} \<subseteq> f``(\<Union>M)" by auto
qed

text\<open>The image of a nonempty subset of domain is nonempty.\<close>

lemma func1_1_L15A: 
  assumes A1: "f: X\<rightarrow>Y" and A2: "A\<subseteq>X" and A3: "A\<noteq>0"
  shows "f``(A) \<noteq> 0"
proof -
  from A3 obtain x where "x\<in>A" by auto
  with A1 A2 have "f`(x) \<in> f``(A)"
    using func_imagedef by auto
  then show "f``(A) \<noteq> 0" by auto
qed

text\<open>The next lemma allows to prove statements about the values in the
  domain of a function given a statement about values in the range.\<close>

lemma func1_1_L15B: 
  assumes "f:X\<rightarrow>Y" and "A\<subseteq>X" and "\<forall>y\<in>f``(A). P(y)"
  shows "\<forall>x\<in>A. P(f`(x))"
  using assms func_imagedef by simp
  
text\<open>An image of an image is the image of a composition.\<close>

lemma func1_1_L15C: assumes  A1: "f:X\<rightarrow>Y" and A2: "g:Y\<rightarrow>Z"
  and A3: "A\<subseteq>X"
  shows 
  "g``(f``(A)) =  {g`(f`(x)). x\<in>A}"
  "g``(f``(A)) = (g O f)``(A)"
proof -
  from A1 A3 have "{f`(x). x\<in>A} \<subseteq> Y"
    using apply_funtype by auto
  with A2 have "g``{f`(x). x\<in>A} = {g`(f`(x)). x\<in>A}"
    using func_imagedef by auto
  with A1 A3 show I: "g``(f``(A)) =  {g`(f`(x)). x\<in>A}" 
    using func_imagedef by simp
  from A1 A3 have "\<forall>x\<in>A. (g O f)`(x) = g`(f`(x))"
    using comp_fun_apply by auto
  with I have "g``(f``(A)) = {(g O f)`(x). x\<in>A}"
    by simp
  moreover from A1 A2 A3 have "(g O f)``(A) = {(g O f)`(x). x\<in>A}"
    using comp_fun func_imagedef by blast
  ultimately show "g``(f``(A)) = (g O f)``(A)"
    by simp
qed
 
text\<open>What is the image of a set defined by a meta-fuction?\<close>

lemma func1_1_L17: 
  assumes A1: "f \<in> X\<rightarrow>Y" and A2: "\<forall>x\<in>A. b(x) \<in> X"
  shows "f``({b(x). x\<in>A}) = {f`(b(x)). x\<in>A}"
proof -
  from A2 have "{b(x). x\<in>A} \<subseteq> X" by auto
  with A1 show ?thesis using func_imagedef by auto
qed

text\<open>What are the values of composition of three functions?\<close>

lemma func1_1_L18: assumes A1: "f:A\<rightarrow>B"  "g:B\<rightarrow>C"  "h:C\<rightarrow>D"
  and A2: "x\<in>A"
  shows
  "(h O g O f)`(x) \<in> D"
  "(h O g O f)`(x) = h`(g`(f`(x)))"  
proof -
  from A1 have "(h O g O f) : A\<rightarrow>D"
    using comp_fun by blast
  with A2 show "(h O g O f)`(x) \<in> D" using apply_funtype
    by simp
  from A1 A2 have "(h O g O f)`(x) = h`( (g O f)`(x))"
    using comp_fun comp_fun_apply by blast
  with A1 A2 show "(h O g O f)`(x) = h`(g`(f`(x)))"
    using comp_fun_apply by simp
qed

text\<open>A composition of functions is a function. This is a slight
  generalization of standard Isabelle's \<open>comp_fun\<close>
\<close>

lemma comp_fun_subset: 
  assumes A1: "g:A\<rightarrow>B"  and A2: "f:C\<rightarrow>D" and A3: "B \<subseteq> C"
  shows "f O g : A \<rightarrow> D"
proof -
  from A1 A3 have "g:A\<rightarrow>C" by (rule func1_1_L1B) 
  with A2 show "f O g : A \<rightarrow> D" using comp_fun by simp
qed

text\<open>This lemma supersedes the lemma \<open>comp_eq_id_iff\<close> 
  in Isabelle/ZF. Contributed by Victor Porton.\<close>

lemma comp_eq_id_iff1: assumes A1: "g: B\<rightarrow>A" and A2: "f: A\<rightarrow>C"
  shows "(\<forall>y\<in>B. f`(g`(y)) = y) \<longleftrightarrow> f O g = id(B)"
proof -
  from assms have "f O g: B\<rightarrow>C" and "id(B): B\<rightarrow>B"
    using comp_fun id_type by auto
  then have "(\<forall>y\<in>B. (f O g)`y = id(B)`(y)) \<longleftrightarrow> f O g = id(B)" 
    by (rule fun_extension_iff)
  moreover from A1 have 
    "\<forall>y\<in>B. (f O g)`y = f`(g`y)" and "\<forall>y\<in>B. id(B)`(y) = y"
    by auto
  ultimately show "(\<forall>y\<in>B. f`(g`y) = y) \<longleftrightarrow> f O g = id(B)" by simp
qed
  
text\<open>A lemma about a value of a function that is a union of 
  some collection of functions.\<close>

lemma fun_Union_apply: assumes A1: "\<Union>F : X\<rightarrow>Y" and 
  A2: "f\<in>F" and A3: "f:A\<rightarrow>B" and A4: "x\<in>A"
  shows "(\<Union>F)`(x) = f`(x)"
proof -
  from A3 A4 have "\<langle>x, f`(x)\<rangle> \<in> f" using apply_Pair
    by simp
  with A2 have "\<langle>x, f`(x)\<rangle> \<in> \<Union>F" by auto
  with A1 show "(\<Union>F)`(x) = f`(x)" using apply_equality
    by simp
qed

subsection\<open>Functions restricted to a set\<close>

text\<open>Standard Isabelle/ZF defines the notion \<open>restrict(f,A)\<close> 
  of to mean a function (or relation) $f$ restricted to a set.
  This means that if $f$ is a function defined on $X$ and $A$
  is a subset of $X$ then \<open>restrict(f,A)\<close> is a function 
  whith the same values as $f$, but whose domain is $A$.\<close>
 
text\<open>What is the inverse image of a set under a restricted fuction?\<close>

lemma func1_2_L1: assumes A1: "f:X\<rightarrow>Y" and A2: "B\<subseteq>X"
  shows "restrict(f,B)-``(A) = f-``(A) \<inter> B"
proof -
  let ?g = "restrict(f,B)"
  from A1 A2 have "?g:B\<rightarrow>Y" 
    using restrict_type2 by simp
  with A2 A1 show "?g-``(A) = f-``(A) \<inter> B"
    using func1_1_L15 restrict_if by auto
qed
   
text\<open>A criterion for when one function is a restriction of another.
  The lemma below provides a result useful in the actual proof of the 
  criterion and applications.\<close>

lemma func1_2_L2: 
  assumes A1: "f:X\<rightarrow>Y" and A2: "g \<in> A\<rightarrow>Z" 
  and A3: "A\<subseteq>X" and A4: "f \<inter> A\<times>Z = g"
  shows "\<forall>x\<in>A. g`(x) = f`(x)"
proof
  fix x assume "x\<in>A"
  with A2 have "\<langle> x,g`(x)\<rangle> \<in> g" using apply_Pair by simp
  with A4 A1 show "g`(x) = f`(x)"  using apply_iff by auto 
qed

text\<open>Here is the actual criterion.\<close>

lemma func1_2_L3: 
  assumes A1: "f:X\<rightarrow>Y" and A2: "g:A\<rightarrow>Z" 
  and A3: "A\<subseteq>X" and A4: "f \<inter> A\<times>Z = g"
  shows "g = restrict(f,A)"
proof
  from A4 show "g \<subseteq> restrict(f, A)" using restrict_iff by auto
  show "restrict(f, A) \<subseteq> g"
  proof
    fix z assume A5:"z \<in> restrict(f,A)"
    then obtain x y where D1:"z\<in>f \<and> x\<in>A  \<and> z = \<langle>x,y\<rangle>"
      using restrict_iff by auto
    with A1 have "y = f`(x)" using apply_iff by auto
    with A1 A2 A3 A4 D1 have "y = g`(x)" using func1_2_L2 by simp
    with A2 D1 show "z\<in>g" using apply_Pair by simp
  qed
qed

text\<open>Which function space a restricted function belongs to?\<close>

lemma func1_2_L4: 
  assumes A1: "f:X\<rightarrow>Y" and A2: "A\<subseteq>X" and A3: "\<forall>x\<in>A. f`(x) \<in> Z"
  shows "restrict(f,A) : A\<rightarrow>Z"
proof -
  let ?g = "restrict(f,A)"
  from A1 A2 have "?g : A\<rightarrow>Y" 
    using restrict_type2 by simp
  moreover { 
    fix x assume "x\<in>A" 
    with A1 A3 have "?g`(x) \<in> Z" using restrict by simp}
  ultimately show ?thesis by (rule Pi_type)
qed

text\<open>A simpler case of \<open>func1_2_L4\<close>, where
  the range of the original and restricted function are the same.
\<close>

corollary restrict_fun: assumes A1: "f:X\<rightarrow>Y" and A2: "A\<subseteq>X"
  shows "restrict(f,A) : A \<rightarrow> Y"
proof -
  from assms have "\<forall>x\<in>A. f`(x) \<in> Y" using apply_funtype
    by auto
  with assms show ?thesis using func1_2_L4 by simp
qed

text\<open>A composition of two functions is the same as 
  composition with a restriction.\<close>

lemma comp_restrict: 
  assumes A1: "f : A\<rightarrow>B" and A2: "g : X \<rightarrow> C" and A3: "B\<subseteq>X"
  shows "g O f = restrict(g,B) O f"
proof -
  from assms have "g O f : A \<rightarrow> C" using comp_fun_subset
    by simp
  moreover from assms have "restrict(g,B) O f : A \<rightarrow> C"
    using restrict_fun comp_fun by simp
  moreover from A1 have 
    "\<forall>x\<in>A. (g O f)`(x) = (restrict(g,B) O f)`(x)"
    using comp_fun_apply apply_funtype restrict
    by simp
  ultimately show "g O f = restrict(g,B) O f"
    by (rule func_eq)
qed

text\<open>A way to look at restriction. Contributed by Victor Porton.\<close>

lemma right_comp_id_any: shows "r O id(C) = restrict(r,C)"
  unfolding restrict_def by auto
 
subsection\<open>Constant functions\<close>

text\<open>Constant functions are trivial, but still we need to 
  prove some properties to shorten proofs.\<close>

text\<open>We define constant($=c$) functions on a set $X$ 
  in a natural way as ConstantFunction$(X,c)$.\<close>

definition
  "ConstantFunction(X,c) \<equiv> X\<times>{c}"

text\<open>Constant function belongs to the function space.\<close>

lemma func1_3_L1: 
  assumes A1: "c\<in>Y" shows "ConstantFunction(X,c) : X\<rightarrow>Y"
proof -
   from A1 have "X\<times>{c} = {\<langle> x,y\<rangle> \<in> X\<times>Y. c = y}" 
     by auto
   with A1 show ?thesis using func1_1_L11A ConstantFunction_def
     by simp
qed

text\<open>Constant function is equal to the constant on its domain.\<close>

lemma func1_3_L2: assumes A1: "x\<in>X"
  shows "ConstantFunction(X,c)`(x) = c"
proof -
  have "ConstantFunction(X,c) \<in> X\<rightarrow>{c}"
    using func1_3_L1 by simp
  moreover from A1 have "\<langle> x,c\<rangle> \<in> ConstantFunction(X,c)"
    using ConstantFunction_def by simp
  ultimately show ?thesis using apply_iff by simp
qed

subsection\<open>Injections, surjections, bijections etc.\<close>

text\<open>In this section we prove the properties of the spaces
  of injections, surjections and bijections that we can't find in the
  standard Isabelle's \<open>Perm.thy\<close>.\<close>

text\<open>For injections the image a difference of two sets is
  the difference of images\<close>

lemma inj_image_dif: 
  assumes A1: "f \<in> inj(A,B)" and A2: "C \<subseteq> A"
  shows "f``(A-C) = f``(A) - f``(C)"
proof
  show "f``(A - C) \<subseteq> f``(A) - f``(C)"
  proof
    fix y assume A3: "y \<in> f``(A - C)"
    from A1 have "f:A\<rightarrow>B" using inj_def by simp
    moreover have "A-C \<subseteq> A" by auto
    ultimately have "f``(A-C) = {f`(x). x \<in> A-C}"
      using func_imagedef by simp
    with A3 obtain x where I: "f`(x) = y" and "x \<in> A-C" 
      by auto
    hence "x\<in>A" by auto
    with \<open>f:A\<rightarrow>B\<close> I have "y \<in> f``(A)"
      using func_imagedef by auto
    moreover have "y \<notin>  f``(C)"
    proof -
      { assume "y \<in> f``(C)"
	with A2 \<open>f:A\<rightarrow>B\<close> obtain x\<^sub>0 
	  where II: "f`(x\<^sub>0) = y" and "x\<^sub>0 \<in> C"
	  using func_imagedef by auto
	with A1 A2 I \<open>x\<in>A\<close> have
	  "f \<in> inj(A,B)" "f`(x) = f`(x\<^sub>0)"  "x\<in>A" "x\<^sub>0 \<in> A"
	  by auto
	then have "x = x\<^sub>0" by (rule inj_apply_equality)
	with \<open>x \<in> A-C\<close> \<open>x\<^sub>0 \<in> C\<close> have False by simp
      } thus ?thesis by auto
    qed
    ultimately show "y \<in> f``(A) - f``(C)" by simp
  qed
  from A1 A2 show "f``(A) - f``(C) \<subseteq> f``(A-C)"
    using inj_def diff_image_diff by auto
qed

text\<open>For injections the image of intersection is the intersection of images.\<close>

lemma inj_image_inter: assumes A1: "f \<in> inj(X,Y)" and A2: "A\<subseteq>X" "B\<subseteq>X"
  shows "f``(A\<inter>B) = f``(A) \<inter> f``(B)"
proof
  show "f``(A\<inter>B) \<subseteq> f``(A) \<inter> f``(B)" using image_Int_subset by simp
  { from A1 have "f:X\<rightarrow>Y" using inj_def by simp 
    fix y assume "y \<in> f``(A) \<inter> f``(B)"
    then have "y \<in> f``(A)" and  "y \<in> f``(B)" by auto
    with A2 \<open>f:X\<rightarrow>Y\<close> obtain x\<^sub>A x\<^sub>B where 
    "x\<^sub>A \<in> A" "x\<^sub>B \<in> B" and I: "y = f`(x\<^sub>A)"  "y = f`(x\<^sub>B)"
      using func_imagedef by auto
    with A2 have "x\<^sub>A \<in> X" "x\<^sub>B \<in> X" and " f`(x\<^sub>A) =  f`(x\<^sub>B)" by auto 
    with A1 have "x\<^sub>A = x\<^sub>B" using inj_def by auto
    with \<open>x\<^sub>A \<in> A\<close> \<open>x\<^sub>B \<in> B\<close> have "f`(x\<^sub>A) \<in> {f`(x). x \<in> A\<inter>B}" by auto
    moreover from A2 \<open>f:X\<rightarrow>Y\<close> have "f``(A\<inter>B) = {f`(x). x \<in> A\<inter>B}"
      using func_imagedef by blast
    ultimately have "f`(x\<^sub>A) \<in> f``(A\<inter>B)" by simp 
    with I have "y \<in> f``(A\<inter>B)" by simp 
  } thus "f``(A) \<inter> f``(B) \<subseteq> f``(A \<inter> B)" by auto
qed

text\<open>For surjection from $A$ to $B$ the image of 
  the domain is $B$.\<close>

lemma surj_range_image_domain: assumes A1: "f \<in> surj(A,B)"
  shows "f``(A) = B"
proof -
  from A1 have "f``(A) = range(f)" 
    using surj_def range_image_domain by auto
  with A1 show "f``(A) = B"  using surj_range
    by simp
qed

text\<open>For injections the inverse image of an image is the same set.\<close>

lemma inj_vimage_image: assumes "f \<in> inj(X,Y)" and "A\<subseteq>X"
  shows "f-``(f``(A)) = A"
proof -
  have "f-``(f``(A)) = (converse(f) O f)``(A)" 
    using vimage_converse image_comp by simp
  with assms show ?thesis using left_comp_inverse image_id_same
    by simp
qed

text\<open>For surjections the image of an inverse image is the same set.\<close>

lemma surj_image_vimage: assumes A1: "f \<in> surj(X,Y)" and A2: "A\<subseteq>Y"
  shows "f``(f-``(A)) = A"
proof -
  have "f``(f-``(A)) = (f O converse(f))``(A)"
    using vimage_converse image_comp by simp
  with assms show ?thesis using right_comp_inverse image_id_same
    by simp
qed

text\<open>A lemma about how a surjection maps collections of subsets in domain and rangge.\<close>

lemma surj_subsets: assumes A1: "f \<in> surj(X,Y)" and A2: "B \<subseteq> Pow(Y)"
  shows "{ f``(U). U \<in> {f-``(V). V\<in>B} } = B"
proof
  { fix W assume "W \<in> { f``(U). U \<in> {f-``(V). V\<in>B} }"
    then obtain U where I: "U \<in> {f-``(V). V\<in>B}" and II: "W = f``(U)" by auto
    then obtain V where "V\<in>B" and "U = f-``(V)" by auto
    with II have "W = f``(f-``(V))" by simp
    moreover from assms \<open>V\<in>B\<close> have "f \<in> surj(X,Y)" and "V\<subseteq>Y" by auto 
    ultimately have "W=V" using surj_image_vimage by simp
    with \<open>V\<in>B\<close> have "W \<in> B" by simp 
  } thus "{ f``(U). U \<in> {f-``(V). V\<in>B} } \<subseteq> B" by auto
  { fix W assume "W\<in>B"
    let ?U = "f-``(W)"
    from \<open>W\<in>B\<close> have "?U \<in> {f-``(V). V\<in>B}" by auto
    moreover from A1 A2 \<open>W\<in>B\<close> have "W = f``(?U)" using surj_image_vimage by auto  
    ultimately have "W \<in> { f``(U). U \<in> {f-``(V). V\<in>B} }" by auto 
  } thus "B \<subseteq> { f``(U). U \<in> {f-``(V). V\<in>B} }" by auto
qed

text\<open>Restriction of an bijection to a set without a point
  is a a bijection.\<close>

lemma bij_restrict_rem: 
  assumes A1: "f \<in> bij(A,B)" and A2: "a\<in>A"
  shows "restrict(f, A-{a}) \<in> bij(A-{a}, B-{f`(a)})"
proof -
  let ?C = "A-{a}"
  from A1 have "f \<in> inj(A,B)"  "?C \<subseteq> A"
    using bij_def by auto
  then have "restrict(f,?C) \<in> bij(?C, f``(?C))"
    using restrict_bij by simp
  moreover have "f``(?C) =  B-{f`(a)}"
  proof -
    from A2 \<open>f \<in> inj(A,B)\<close> have "f``(?C) = f``(A) - f``{a}"
      using inj_image_dif by simp
    moreover from A1 have "f``(A) = B" 
      using bij_def surj_range_image_domain by auto
    moreover from A1 A2 have "f``{a} = {f`(a)}"
      using bij_is_fun singleton_image by blast
    ultimately show "f``(?C) =  B-{f`(a)}" by simp
  qed
  ultimately show ?thesis by simp
qed

text\<open>The domain of a bijection between $X$ and $Y$ is $X$.\<close>

lemma domain_of_bij: 
  assumes A1: "f \<in> bij(X,Y)" shows "domain(f) = X"
proof -
  from A1 have "f:X\<rightarrow>Y" using bij_is_fun by simp
  then show "domain(f) = X" using func1_1_L1 by simp
qed

text\<open>The value of the inverse of an injection on a point of the image 
  of a set belongs to that set.\<close>

lemma inj_inv_back_in_set: 
  assumes A1: "f \<in> inj(A,B)" and A2: "C\<subseteq>A" and A3: "y \<in> f``(C)"
  shows 
  "converse(f)`(y) \<in> C"
  "f`(converse(f)`(y)) = y"
proof -
  from A1 have I: "f:A\<rightarrow>B" using inj_is_fun by simp
  with A2 A3 obtain x where II: "x\<in>C"   "y = f`(x)"
    using func_imagedef by auto
  with A1 A2 show "converse(f)`(y) \<in> C" using left_inverse
    by auto
  from A1 A2 I II show "f`(converse(f)`(y)) = y"
    using func1_1_L5A right_inverse by auto
qed

text\<open>For injections if a value at a point 
  belongs to the image of a set, then the point
  belongs to the set.\<close>

lemma inj_point_of_image: 
  assumes A1: "f \<in> inj(A,B)" and A2: "C\<subseteq>A" and
  A3: "x\<in>A" and A4: "f`(x) \<in> f``(C)"
  shows "x \<in> C"
proof -
  from A1 A2 A4 have "converse(f)`(f`(x)) \<in> C"
    using inj_inv_back_in_set by simp
  moreover from A1 A3 have "converse(f)`(f`(x)) = x"
    using left_inverse_eq by simp
  ultimately show "x \<in> C" by simp
qed

text\<open>For injections the image of intersection is 
  the intersection of images.\<close>

lemma inj_image_of_Inter: assumes A1: "f \<in> inj(A,B)" and
  A2: "I\<noteq>0" and A3: "\<forall>i\<in>I. P(i) \<subseteq> A"
  shows "f``(\<Inter>i\<in>I. P(i)) = ( \<Inter>i\<in>I. f``(P(i)) )"
proof
  from A1 A2 A3 show "f``(\<Inter>i\<in>I. P(i)) \<subseteq> ( \<Inter>i\<in>I. f``(P(i)) )"
    using inj_is_fun image_of_Inter by auto
  from A1 A2 A3 have "f:A\<rightarrow>B"  and "( \<Inter>i\<in>I. P(i) ) \<subseteq> A"
    using inj_is_fun ZF1_1_L7 by auto
  then have I: "f``(\<Inter>i\<in>I. P(i)) = { f`(x). x \<in> ( \<Inter>i\<in>I. P(i) ) }"
    using func_imagedef by simp
  { fix y assume A4: "y \<in> ( \<Inter>i\<in>I. f``(P(i)) )"
    let ?x = "converse(f)`(y)"
    from A2 obtain i\<^sub>0 where "i\<^sub>0 \<in> I" by auto
    with A1 A4 have II: "y \<in> range(f)" using inj_is_fun func1_1_L6
      by auto
    with A1 have III: "f`(?x) = y" using right_inverse by simp
    from A1 II have IV: "?x \<in> A" using inj_converse_fun apply_funtype 
      by blast
    { fix i assume "i\<in>I"
      with A3 A4 III have "P(i) \<subseteq> A" and "f`(?x) \<in>  f``(P(i))" 
	by auto
      with A1 IV have "?x \<in> P(i)" using inj_point_of_image
	by blast
    } then have "\<forall>i\<in>I. ?x \<in> P(i)" by simp
    with A2 I have "f`(?x) \<in> f``( \<Inter>i\<in>I. P(i) )"
      by auto
    with III have "y \<in>  f``( \<Inter>i\<in>I. P(i) )" by simp
  } then show "( \<Inter>i\<in>I. f``(P(i)) ) \<subseteq>  f``( \<Inter>i\<in>I. P(i) )"
    by auto
qed

text\<open>An injection is injective onto its range. Suggested by Victor Porton.\<close>

lemma inj_inj_range: assumes "f \<in> inj(A,B)"
  shows "f \<in> inj(A,range(f))"
  using assms inj_def range_of_fun by auto


text\<open>An injection is a bijection on its range. Suggested by Victor Porton.\<close>

lemma inj_bij_range: assumes "f \<in> inj(A,B)" 
  shows "f \<in> bij(A,range(f))"
proof -
  from assms have "f \<in> surj(A,range(f))" using inj_def fun_is_surj
    by auto
  with assms show ?thesis using inj_inj_range bij_def by simp
qed
  
text\<open>A lemma about extending a surjection by one point.\<close>

lemma surj_extend_point: 
  assumes A1: "f \<in> surj(X,Y)" and A2: "a\<notin>X" and
  A3: "g = f \<union> {\<langle>a,b\<rangle>}"
  shows "g \<in> surj(X\<union>{a},Y\<union>{b})"
proof -
  from A1 A2 A3 have "g : X\<union>{a} \<rightarrow> Y\<union>{b}"
    using surj_def func1_1_L11D by simp
  moreover have "\<forall>y \<in> Y\<union>{b}. \<exists>x \<in> X\<union>{a}. y = g`(x)"
  proof
    fix y assume "y \<in>  Y \<union> {b}"
    then have "y \<in> Y \<or> y = b" by auto
    moreover
    { assume "y \<in> Y"
      with A1 obtain x where "x\<in>X" and "y = f`(x)"
	using surj_def by auto
      with A1 A2 A3 have "x \<in>  X\<union>{a}" and "y = g`(x)"
	using surj_def func1_1_L11D by auto
      then have "\<exists>x \<in> X\<union>{a}. y = g`(x)" by auto }
    moreover
    { assume "y = b"
      with A1 A2 A3 have "y = g`(a)"
	using surj_def func1_1_L11D by auto
      then have "\<exists>x \<in> X\<union>{a}. y = g`(x)" by auto }
    ultimately show "\<exists>x \<in> X\<union>{a}. y = g`(x)"
      by auto
  qed
  ultimately show "g \<in> surj(X\<union>{a},Y\<union>{b})"
    using surj_def by auto
qed

text\<open>A lemma about extending an injection by one point. 
  Essentially the same as standard Isabelle's \<open>inj_extend\<close>.
\<close>

lemma inj_extend_point: assumes "f \<in> inj(X,Y)" "a\<notin>X" "b\<notin>Y"
  shows "(f \<union> {\<langle>a,b\<rangle>}) \<in> inj(X\<union>{a},Y\<union>{b})"
proof -
  from assms have "cons(\<langle>a,b\<rangle>,f) \<in> inj(cons(a, X), cons(b, Y))"
    using assms inj_extend by simp
  moreover have "cons(\<langle>a,b\<rangle>,f) = f \<union> {\<langle>a,b\<rangle>}" and
    "cons(a, X) = X\<union>{a}" and "cons(b, Y) = Y\<union>{b}"
    by auto
  ultimately show ?thesis by simp
qed

text\<open>A lemma about extending a bijection by one point.\<close>

lemma bij_extend_point: assumes "f \<in> bij(X,Y)" "a\<notin>X" "b\<notin>Y"
  shows "(f \<union> {\<langle>a,b\<rangle>}) \<in> bij(X\<union>{a},Y\<union>{b})"
  using assms surj_extend_point inj_extend_point bij_def
  by simp

text\<open>A quite general form of the $a^{-1}b = 1$ 
  implies $a=b$ law.\<close>

lemma comp_inv_id_eq: 
  assumes A1: "converse(b) O a = id(A)" and
  A2: "a \<subseteq> A\<times>B" "b \<in> surj(A,B)"
  shows "a = b"
proof -
  from A1 have "(b O converse(b)) O a = b O id(A)"
    using comp_assoc by simp
  with A2 have "id(B) O a = b O id(A)" 
    using right_comp_inverse by simp
  moreover
  from A2 have "a \<subseteq> A\<times>B" and "b \<subseteq> A\<times>B"
    using surj_def fun_subset_prod
    by auto
  then have "id(B) O a = a" and "b O id(A) = b"
    using left_comp_id right_comp_id by auto
  ultimately show "a = b" by simp
qed

text\<open>A special case of \<open>comp_inv_id_eq\<close> - 
  the $a^{-1}b = 1$ implies $a=b$ law for bijections.\<close>

lemma comp_inv_id_eq_bij: 
  assumes A1: "a \<in> bij(A,B)" "b \<in> bij(A,B)" and
  A2: "converse(b) O a = id(A)"
  shows "a = b"
proof -
  from A1 have  "a \<subseteq> A\<times>B" and "b \<in> surj(A,B)"
    using bij_def surj_def fun_subset_prod
    by auto
  with A2 show "a = b" by (rule comp_inv_id_eq)
qed

text\<open>Converse of a converse of a bijection is the same bijection. 
This is a special case of \<open>converse_converse\<close> from standard Isabelle's 
\<open>equalities\<close> theory where it is proved for relations.\<close>

lemma bij_converse_converse: assumes "a \<in> bij(A,B)" 
  shows "converse(converse(a)) = a"
proof -
  from assms have "a \<subseteq> A\<times>B" using bij_def surj_def fun_subset_prod by simp
  then show ?thesis using converse_converse by simp
qed

text\<open>If a composition of bijections is identity, then one is the inverse
  of the other.\<close>

lemma comp_id_conv: assumes A1: "a \<in> bij(A,B)" "b \<in> bij(B,A)" and
  A2: "b O a = id(A)"
  shows "a = converse(b)" and "b = converse(a)"
proof -
  from A1 have "a \<in> bij(A,B)" and "converse(b) \<in> bij(A,B)" using bij_converse_bij 
    by auto
  moreover from assms have "converse(converse(b)) O a = id(A)" 
    using bij_converse_converse by simp
  ultimately show "a = converse(b)" by (rule comp_inv_id_eq_bij)
  with assms show "b = converse(a)" using bij_converse_converse by simp
qed

text\<open>A version of \<open>comp_id_conv\<close> with weaker assumptions.\<close>

lemma comp_conv_id: assumes A1: "a \<in> bij(A,B)" and A2: "b:B\<rightarrow>A" and
  A3: "\<forall>x\<in>A. b`(a`(x)) = x"
  shows "b \<in> bij(B,A)" and  "a = converse(b)" and "b = converse(a)"
proof -
  have "b \<in> surj(B,A)"
  proof -
    have "\<forall>x\<in>A. \<exists>y\<in>B. b`(y) = x"
    proof -
      { fix x assume "x\<in>A"
        let ?y = "a`(x)"
        from A1 A3 \<open>x\<in>A\<close> have "?y\<in>B" and "b`(?y) = x" 
          using bij_def inj_def apply_funtype by auto
        hence "\<exists>y\<in>B. b`(y) = x" by auto
      } thus ?thesis by simp 
    qed
    with A2 show "b \<in> surj(B,A)" using surj_def by simp
  qed
  moreover have "b \<in> inj(B,A)"
  proof -
    have "\<forall>w\<in>B.\<forall>y\<in>B. b`(w) = b`(y) \<longrightarrow> w=y"
    proof -
      { fix w y assume "w\<in>B"  "y\<in>B" and I: "b`(w) = b`(y)"
        from A1 have "a \<in> surj(A,B)" unfolding bij_def by simp
        with \<open>w\<in>B\<close> obtain x\<^sub>w where "x\<^sub>w \<in> A" and II: "a`(x\<^sub>w) = w"
          using surj_def by auto
        with I have "b`(a`(x\<^sub>w)) = b`(y)" by simp 
        moreover from \<open>a \<in> surj(A,B)\<close> \<open>y\<in>B\<close> obtain x\<^sub>y where 
          "x\<^sub>y \<in> A" and III: "a`(x\<^sub>y) = y"
          using surj_def by auto
        moreover from A3 \<open>x\<^sub>w \<in> A\<close>  \<open>x\<^sub>y \<in> A\<close> have "b`(a`(x\<^sub>w)) = x\<^sub>w" and  "b`(a`(x\<^sub>y)) = x\<^sub>y"
          by auto
        ultimately have "x\<^sub>w = x\<^sub>y" by simp
        with II III have "w=y" by simp 
      } thus ?thesis by auto  
    qed
    with A2 show "b \<in> inj(B,A)" using inj_def by auto
  qed
  ultimately show "b \<in> bij(B,A)" using bij_def by simp
  from assms have "b O a = id(A)" using bij_def inj_def comp_eq_id_iff1 by auto
  with A1 \<open>b \<in> bij(B,A)\<close> show "a = converse(b)" and "b = converse(a)"
    using comp_id_conv by auto
qed  
 
 
text\<open>For a surjection the union if images of singletons
  is the whole range.\<close>

lemma surj_singleton_image: assumes A1: "f \<in> surj(X,Y)"
  shows "(\<Union>x\<in>X. {f`(x)}) = Y"
proof
  from A1 show "(\<Union>x\<in>X. {f`(x)}) \<subseteq> Y"
    using surj_def apply_funtype by auto
next 
  { fix y assume "y \<in> Y"
    with A1 have "y \<in> (\<Union>x\<in>X. {f`(x)})"
      using surj_def by auto
  } then show  "Y \<subseteq> (\<Union>x\<in>X. {f`(x)})" by auto
qed

subsection\<open>Functions of two variables\<close>

text\<open>In this section we consider functions whose domain is a cartesian product
  of two sets. Such functions are called functions of two variables (although really 
  in ZF all functions admit only one argument). 
  For every function of two variables we can define families of 
  functions of one variable by fixing the other variable. This section 
  establishes basic definitions and results for this concept.\<close>


text\<open>We can create functions of two variables by combining functions of one variable.\<close>

lemma cart_prod_fun: assumes "f\<^sub>1:X\<^sub>1\<rightarrow>Y\<^sub>1"  "f\<^sub>2:X\<^sub>2\<rightarrow>Y\<^sub>2" and
  "g = {\<langle>p,\<langle>f\<^sub>1`(fst(p)),f\<^sub>2`(snd(p))\<rangle>\<rangle>. p \<in> X\<^sub>1\<times>X\<^sub>2}"
  shows "g: X\<^sub>1\<times>X\<^sub>2 \<rightarrow> Y\<^sub>1\<times>Y\<^sub>2" using assms apply_funtype  ZF_fun_from_total by simp

text\<open>A reformulation of \<open>cart_prod_fun\<close> above in a sligtly different notation.\<close>

lemma prod_fun:
  assumes "f:X\<^sub>1\<rightarrow>X\<^sub>2"  "g:X\<^sub>3\<rightarrow>X\<^sub>4"
  shows "{\<langle>\<langle>x,y\<rangle>,\<langle>f`x,g`y\<rangle>\<rangle>. \<langle>x,y\<rangle>\<in>X\<^sub>1\<times>X\<^sub>3}:X\<^sub>1\<times>X\<^sub>3\<rightarrow>X\<^sub>2\<times>X\<^sub>4" 
proof -
  have "{\<langle>\<langle>x,y\<rangle>,\<langle>f`x,g`y\<rangle>\<rangle>. \<langle>x,y\<rangle>\<in>X\<^sub>1\<times>X\<^sub>3} = {\<langle>p,\<langle>f`(fst(p)),g`(snd(p))\<rangle>\<rangle>. p \<in> X\<^sub>1\<times>X\<^sub>3}"
    by auto
  with assms show ?thesis using cart_prod_fun by simp 
qed

text\<open>Product of two surjections is a surjection.\<close>

theorem prod_functions_surj:
  assumes "f\<in>surj(A,B)" "g\<in>surj(C,D)"
  shows "{\<langle>\<langle>a1,a2\<rangle>,\<langle>f`a1,g`a2\<rangle>\<rangle>.\<langle>a1,a2\<rangle>\<in>A\<times>C} \<in> surj(A\<times>C,B\<times>D)"
proof -
  let ?h = "{\<langle>\<langle>x, y\<rangle>, f`(x), g`(y)\<rangle> . \<langle>x,y\<rangle> \<in> A \<times> C}"
  from assms have fun: "f:A\<rightarrow>B""g:C\<rightarrow>D" unfolding surj_def by auto
  then have pfun: "?h : A \<times> C \<rightarrow> B \<times> D" using prod_fun by auto
  {
    fix b assume "b\<in>B\<times>D"
    then obtain b1 b2 where "b=\<langle>b1,b2\<rangle>" "b1\<in>B" "b2\<in>D" by auto
    with assms obtain a1 a2 where "f`(a1)=b1" "g`(a2)=b2" "a1\<in>A" "a2\<in>C" 
      unfolding surj_def by blast
    hence "\<langle>\<langle>a1,a2\<rangle>,\<langle>b1,b2\<rangle>\<rangle> \<in> ?h" by auto
    with pfun have "?h`\<langle>a1,a2\<rangle>=\<langle>b1,b2\<rangle>" using apply_equality by auto
    with \<open>b=\<langle>b1,b2\<rangle>\<close> \<open>a1\<in>A\<close> \<open>a2\<in>C\<close> have "\<exists>a\<in>A\<times>C. ?h`(a)=b" 
      by auto
  } hence "\<forall>b\<in>B\<times>D. \<exists>a\<in>A\<times>C. ?h`(a) = b" by auto
  with pfun show ?thesis unfolding surj_def by auto
qed


text\<open>For a function of two variables created from functions of one variable as in 
  \<open>cart_prod_fun\<close> above, the inverse image of a cartesian product of sets is the 
  cartesian product of inverse images.\<close>

lemma cart_prod_fun_vimage: assumes "f\<^sub>1:X\<^sub>1\<rightarrow>Y\<^sub>1"  "f\<^sub>2:X\<^sub>2\<rightarrow>Y\<^sub>2" and
  "g = {\<langle>p,\<langle>f\<^sub>1`(fst(p)),f\<^sub>2`(snd(p))\<rangle>\<rangle>. p \<in> X\<^sub>1\<times>X\<^sub>2}"
  shows "g-``(A\<^sub>1\<times>A\<^sub>2) = f\<^sub>1-``(A\<^sub>1) \<times> f\<^sub>2-``(A\<^sub>2)"
proof -
  from assms have "g: X\<^sub>1\<times>X\<^sub>2 \<rightarrow> Y\<^sub>1\<times>Y\<^sub>2" using cart_prod_fun 
    by simp
  then have "g-``(A\<^sub>1\<times>A\<^sub>2) = {p \<in> X\<^sub>1\<times>X\<^sub>2. g`(p) \<in> A\<^sub>1\<times>A\<^sub>2}" using func1_1_L15 
    by simp
  with assms \<open>g: X\<^sub>1\<times>X\<^sub>2 \<rightarrow> Y\<^sub>1\<times>Y\<^sub>2\<close> show "g-``(A\<^sub>1\<times>A\<^sub>2) = f\<^sub>1-``(A\<^sub>1) \<times> f\<^sub>2-``(A\<^sub>2)" 
    using ZF_fun_from_tot_val func1_1_L15 by auto
qed
  
text\<open>For a function of two variables defined on $X\times Y$, if we fix an 
  $x\in X$ we obtain a function on $Y$.
  Note that if \<open>domain(f)\<close> is $X\times Y$, \<open>range(domain(f))\<close> 
  extracts $Y$ from $X\times Y$.\<close>

definition
  "Fix1stVar(f,x) \<equiv> {\<langle>y,f`\<langle>x,y\<rangle>\<rangle>. y \<in> range(domain(f))}"
  
text\<open>For every $y\in Y$ we can fix the second variable in a binary function
  $f: X\times Y \rightarrow Z$ to get a function on $X$.\<close>

definition
  "Fix2ndVar(f,y) \<equiv> {\<langle>x,f`\<langle>x,y\<rangle>\<rangle>. x \<in> domain(domain(f))}"

text\<open>We defined \<open>Fix1stVar\<close> and \<open>Fix2ndVar\<close> so that
  the domain of the function is not listed in the arguments, but is recovered 
  from the function. The next lemma is a technical fact that makes it easier
  to use this definition.\<close>

lemma fix_var_fun_domain: assumes A1: "f : X\<times>Y \<rightarrow> Z"
  shows
  "x\<in>X \<longrightarrow> Fix1stVar(f,x) = {\<langle>y,f`\<langle>x,y\<rangle>\<rangle>. y \<in> Y}"
  "y\<in>Y \<longrightarrow> Fix2ndVar(f,y) = {\<langle>x,f`\<langle>x,y\<rangle>\<rangle>. x \<in> X}"
proof -
  from A1 have I: "domain(f) = X\<times>Y" using func1_1_L1 by simp
  { assume "x\<in>X"
    with I have "range(domain(f)) = Y" by auto
    then have "Fix1stVar(f,x) = {\<langle>y,f`\<langle>x,y\<rangle>\<rangle>. y \<in> Y}"
      using Fix1stVar_def by simp
  } then show "x\<in>X \<longrightarrow> Fix1stVar(f,x) = {\<langle>y,f`\<langle>x,y\<rangle>\<rangle>. y \<in> Y}"
    by simp
  { assume "y\<in>Y"
    with I have "domain(domain(f)) = X" by auto
    then have "Fix2ndVar(f,y) = {\<langle>x,f`\<langle>x,y\<rangle>\<rangle>. x \<in> X}"
      using Fix2ndVar_def by simp
  } then show "y\<in>Y \<longrightarrow> Fix2ndVar(f,y) = {\<langle>x,f`\<langle>x,y\<rangle>\<rangle>. x \<in> X}"
    by simp
qed
    
text\<open>If we fix the first variable, we get a function of the second variable.\<close>

lemma fix_1st_var_fun: assumes A1: "f : X\<times>Y \<rightarrow> Z" and A2: "x\<in>X"
  shows "Fix1stVar(f,x) : Y \<rightarrow> Z"
proof -
  from A1 A2 have "\<forall>y\<in>Y. f`\<langle>x,y\<rangle> \<in> Z"
    using apply_funtype by simp
  then have "{\<langle>y,f`\<langle>x,y\<rangle>\<rangle>. y \<in> Y} :  Y \<rightarrow> Z" using ZF_fun_from_total by simp
  with A1 A2 show "Fix1stVar(f,x) : Y \<rightarrow> Z" using fix_var_fun_domain by simp
qed

text\<open>If we fix the second variable, we get a function of the first
  variable.\<close>

lemma fix_2nd_var_fun: assumes A1: "f : X\<times>Y \<rightarrow> Z" and A2: "y\<in>Y"
  shows "Fix2ndVar(f,y) : X \<rightarrow> Z"
proof -
  from A1 A2 have "\<forall>x\<in>X. f`\<langle>x,y\<rangle> \<in> Z"
    using apply_funtype by simp
  then have "{\<langle>x,f`\<langle>x,y\<rangle>\<rangle>. x \<in> X} :  X \<rightarrow> Z"
    using ZF_fun_from_total by simp
  with A1 A2 show "Fix2ndVar(f,y) : X \<rightarrow> Z"
    using fix_var_fun_domain by simp 
qed

text\<open>What is the value of \<open>Fix1stVar(f,x)\<close> at $y\in Y$
  and the value of \<open>Fix2ndVar(f,y)\<close> at $x\in X$"?\<close>

lemma fix_var_val: 
  assumes A1: "f : X\<times>Y \<rightarrow> Z" and A2: "x\<in>X"  "y\<in>Y"
  shows 
  "Fix1stVar(f,x)`(y) = f`\<langle>x,y\<rangle>"
  "Fix2ndVar(f,y)`(x) = f`\<langle>x,y\<rangle>"
proof -
  let ?f\<^sub>1 = "{\<langle>y,f`\<langle>x,y\<rangle>\<rangle>. y \<in> Y}"
  let ?f\<^sub>2 = "{\<langle>x,f`\<langle>x,y\<rangle>\<rangle>. x \<in> X}"
  from A1 A2 have I:
    "Fix1stVar(f,x) = ?f\<^sub>1"
    "Fix2ndVar(f,y) = ?f\<^sub>2"
    using fix_var_fun_domain by auto
  moreover from A1 A2 have
    "Fix1stVar(f,x) : Y \<rightarrow> Z"
    "Fix2ndVar(f,y) : X \<rightarrow> Z"
    using fix_1st_var_fun fix_2nd_var_fun by auto
  ultimately have "?f\<^sub>1 : Y \<rightarrow> Z" and  "?f\<^sub>2 : X \<rightarrow> Z"
    by auto
  with A2 have "?f\<^sub>1`(y) = f`\<langle>x,y\<rangle>" and "?f\<^sub>2`(x) = f`\<langle>x,y\<rangle>"
    using ZF_fun_from_tot_val by auto
  with I show
    "Fix1stVar(f,x)`(y) = f`\<langle>x,y\<rangle>"
    "Fix2ndVar(f,y)`(x) = f`\<langle>x,y\<rangle>"
    by auto
qed

text\<open>Fixing the second variable commutes with restrictig the domain.\<close>

lemma fix_2nd_var_restr_comm: 
  assumes A1: "f : X\<times>Y \<rightarrow> Z" and A2: "y\<in>Y" and A3: "X\<^sub>1 \<subseteq> X"
  shows "Fix2ndVar(restrict(f,X\<^sub>1\<times>Y),y) = restrict(Fix2ndVar(f,y),X\<^sub>1)"
proof -
  let ?g = "Fix2ndVar(restrict(f,X\<^sub>1\<times>Y),y)"
  let ?h = "restrict(Fix2ndVar(f,y),X\<^sub>1)"
  from A3 have I: "X\<^sub>1\<times>Y \<subseteq> X\<times>Y" by auto
  with A1 have II: "restrict(f,X\<^sub>1\<times>Y) : X\<^sub>1\<times>Y \<rightarrow> Z"
    using restrict_type2 by simp
  with A2 have "?g : X\<^sub>1 \<rightarrow> Z"
    using fix_2nd_var_fun by simp
  moreover
  from A1 A2 have III: "Fix2ndVar(f,y) : X \<rightarrow> Z"
    using fix_2nd_var_fun by simp
  with A3 have "?h : X\<^sub>1 \<rightarrow> Z"
    using restrict_type2 by simp
  moreover
  { fix z assume A4: "z \<in> X\<^sub>1"
    with A2 I II have "?g`(z) = f`\<langle>z,y\<rangle>"
      using restrict fix_var_val by simp
    also from A1 A2 A3 A4 have "f`\<langle>z,y\<rangle> = ?h`(z)"
      using restrict fix_var_val by auto
    finally have "?g`(z) = ?h`(z)" by simp
  } then have "\<forall>z \<in> X\<^sub>1. ?g`(z) = ?h`(z)" by simp
  ultimately show "?g = ?h" by (rule func_eq)
qed

text\<open>The next lemma expresses the inverse image of a set by function with fixed 
first variable in terms of the original function.\<close>

lemma fix_1st_var_vimage:
  assumes A1: "f : X\<times>Y \<rightarrow> Z" and A2: "x\<in>X" 
  shows "Fix1stVar(f,x)-``(A) = {y\<in>Y. \<langle>x,y\<rangle> \<in> f-``(A)}"
proof -
  from assms have "Fix1stVar(f,x)-``(A) = {y\<in>Y. Fix1stVar(f,x)`(y) \<in> A}"
    using fix_1st_var_fun func1_1_L15 by blast
  with assms show ?thesis using fix_var_val func1_1_L15 by auto
qed

text\<open>The next lemma expresses the inverse image of a set by function with fixed 
second variable in terms of the original function.\<close>

lemma fix_2nd_var_vimage:
  assumes A1: "f : X\<times>Y \<rightarrow> Z" and A2: "y\<in>Y" 
  shows "Fix2ndVar(f,y)-``(A) = {x\<in>X. \<langle>x,y\<rangle> \<in> f-``(A)}"
proof -
  from assms have I: "Fix2ndVar(f,y)-``(A) = {x\<in>X. Fix2ndVar(f,y)`(x) \<in> A}"
    using fix_2nd_var_fun func1_1_L15 by blast
  with assms show ?thesis using fix_var_val func1_1_L15 by auto
qed

end
