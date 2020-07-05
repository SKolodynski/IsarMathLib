(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2008  Slawomir Kolodynski

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

section \<open>More on functions\<close>

theory func_ZF_1 imports ZF.Order Order_ZF_1a func_ZF

begin  

text\<open>In this theory we consider 
  some properties of functions related to order relations\<close>

subsection\<open>Functions and order\<close>

text\<open>This section deals with functions between ordered sets.\<close>

text\<open>If every value of a function on a set is bounded below by
  a constant, then the image of the set is bounded below.\<close>

lemma func_ZF_8_L1: 
  assumes "f:X\<rightarrow>Y" and "A\<subseteq>X" and "\<forall>x\<in>A. \<langle>L,f`(x)\<rangle> \<in> r"
  shows "IsBoundedBelow(f``(A),r)"
proof -
  from assms have "\<forall>y \<in> f``(A). \<langle>L,y\<rangle> \<in> r"
    using func_imagedef by simp
  then show "IsBoundedBelow(f``(A),r)" 
    by (rule Order_ZF_3_L9)
qed

text\<open>If every value of a function on a set is bounded above by
  a constant, then the image of the set is bounded above.\<close>

lemma func_ZF_8_L2:  
  assumes "f:X\<rightarrow>Y" and "A\<subseteq>X" and "\<forall>x\<in>A. \<langle>f`(x),U\<rangle> \<in> r"
  shows "IsBoundedAbove(f``(A),r)"
proof -
  from assms have "\<forall>y \<in> f``(A). \<langle>y,U\<rangle> \<in> r"
    using func_imagedef by simp
  then show "IsBoundedAbove(f``(A),r)" 
    by (rule Order_ZF_3_L10)
qed

text\<open>Identity is an order isomorphism.\<close>

lemma id_ord_iso: shows "id(X) \<in> ord_iso(X,r,X,r)"
  using id_bij id_def ord_iso_def by simp

text\<open>Identity is the only order automorphism 
  of a singleton.\<close>

lemma id_ord_auto_singleton: 
  shows "ord_iso({x},r,{x},r) = {id({x})}"
  using id_ord_iso ord_iso_def single_bij_id
  by auto 
      
text\<open>The image of a maximum by an order isomorphism
  is a maximum. Note that from the fact the $r$ is 
  antisymmetric and $f$ is an order isomorphism between
  $(A,r)$ and $(B,R)$ we can not conclude that $R$ is
  antisymmetric (we can only show that $R\cap (B\times B)$ is).
\<close>

lemma max_image_ord_iso: 
  assumes A1: "antisym(r)" and A2: "antisym(R)" and 
  A3: "f \<in> ord_iso(A,r,B,R)" and
  A4: "HasAmaximum(r,A)"
  shows "HasAmaximum(R,B)" and "Maximum(R,B) = f`(Maximum(r,A))"
proof -
  let ?M = "Maximum(r,A)"
  from A1 A4 have "?M \<in> A" using Order_ZF_4_L3 by simp
  from A3 have "f:A\<rightarrow>B" using ord_iso_def bij_is_fun
    by simp
  with \<open>?M \<in> A\<close> have I: "f`(?M) \<in> B"
    using apply_funtype by simp
  { fix y assume "y \<in> B"
    let ?x = "converse(f)`(y)" 
    from A3 have "converse(f) \<in> ord_iso(B,R,A,r)"
      using ord_iso_sym by simp
    then have "converse(f): B \<rightarrow> A"
      using ord_iso_def bij_is_fun by simp
    with \<open>y \<in> B\<close> have "?x \<in> A"
      by simp
    with A1 A3 A4 \<open>?x \<in> A\<close> \<open>?M \<in> A\<close> have "\<langle>f`(?x), f`(?M)\<rangle> \<in> R"
      using Order_ZF_4_L3 ord_iso_apply by simp
    with A3 \<open>y \<in> B\<close> have "\<langle>y, f`(?M)\<rangle> \<in> R"
      using right_inverse_bij ord_iso_def by auto
  } then have II: "\<forall>y \<in> B. \<langle>y, f`(?M)\<rangle> \<in> R" by simp
  with A2 I show "Maximum(R,B) = f`(?M)"
    by (rule Order_ZF_4_L14)
  from I II show "HasAmaximum(R,B)"
    using HasAmaximum_def by auto
qed

text\<open>Maximum is a fixpoint of order automorphism.\<close>

lemma max_auto_fixpoint: 
  assumes "antisym(r)" and "f \<in> ord_iso(A,r,A,r)"
  and "HasAmaximum(r,A)"
  shows "Maximum(r,A) = f`(Maximum(r,A))"
  using assms max_image_ord_iso by blast      

text\<open>If two sets are order isomorphic and 
  we remove $x$ and $f(x)$, respectively, from the sets, 
  then they are still order isomorphic.\<close>

lemma ord_iso_rem_point: 
  assumes A1: "f \<in> ord_iso(A,r,B,R)" and A2: "a \<in> A"
  shows "restrict(f,A-{a}) \<in> ord_iso(A-{a},r,B-{f`(a)},R)"
proof -
  let ?f\<^sub>0 = "restrict(f,A-{a})"
  have "A-{a} \<subseteq> A" by auto
  with A1 have "?f\<^sub>0 \<in> ord_iso(A-{a},r,f``(A-{a}),R)"
    using ord_iso_restrict_image by simp
  moreover 
  from A1 have "f \<in> inj(A,B)" 
    using ord_iso_def bij_def by simp
  with A2  have "f``(A-{a}) = f``(A) - f``{a}"
    using inj_image_dif by simp
  moreover from A1 have "f``(A) = B" 
    using ord_iso_def bij_def surj_range_image_domain 
    by auto
  moreover 
  from A1 have "f: A\<rightarrow>B"
    using ord_iso_def bij_is_fun by simp
  with A2 have "f``{a} = {f`(a)}"
    using singleton_image by simp
  ultimately show ?thesis by simp
qed
  
text\<open>If two sets are order isomorphic and 
  we remove maxima from the sets, then they are still
  order isomorphic.\<close>

corollary ord_iso_rem_max: 
  assumes A1: "antisym(r)" and "f \<in> ord_iso(A,r,B,R)" and
  A4: "HasAmaximum(r,A)" and  A5: "M = Maximum(r,A)"
  shows "restrict(f,A-{M}) \<in> ord_iso(A-{M}, r, B-{f`(M)},R)"
  using assms Order_ZF_4_L3 ord_iso_rem_point by simp


text\<open>Lemma about extending order isomorphisms by adding one point
  to the domain.\<close>

lemma ord_iso_extend:  assumes A1: "f \<in> ord_iso(A,r,B,R)" and
  A2: "M\<^sub>A \<notin> A" "M\<^sub>B \<notin> B" and
  A3: "\<forall>a\<in>A. \<langle>a, M\<^sub>A\<rangle> \<in> r"  "\<forall>b\<in>B. \<langle>b, M\<^sub>B\<rangle> \<in> R" and
  A4: "antisym(r)"  "antisym(R)" and
  A5: "\<langle>M\<^sub>A,M\<^sub>A\<rangle> \<in> r \<longleftrightarrow> \<langle>M\<^sub>B,M\<^sub>B\<rangle> \<in> R"  
  shows "f \<union> {\<langle> M\<^sub>A,M\<^sub>B\<rangle>} \<in> ord_iso(A\<union>{M\<^sub>A} ,r,B\<union>{M\<^sub>B} ,R)"
proof -
  let ?g = "f \<union> {\<langle> M\<^sub>A,M\<^sub>B\<rangle>}"
  from A1 A2 have
    "?g : A\<union>{M\<^sub>A} \<rightarrow> B\<union>{M\<^sub>B}" and
    I: "\<forall>x\<in>A. ?g`(x) = f`(x)" and II: "?g`(M\<^sub>A) = M\<^sub>B"
    using ord_iso_def bij_def inj_def func1_1_L11D
    by auto
  from A1 A2 have "?g \<in> bij(A\<union>{M\<^sub>A},B\<union>{M\<^sub>B}) "
    using ord_iso_def bij_extend_point by simp
  moreover have "\<forall>x \<in> A\<union>{M\<^sub>A}. \<forall> y \<in> A\<union>{M\<^sub>A}.
    \<langle>x,y\<rangle> \<in> r \<longleftrightarrow> \<langle>?g`(x), ?g`(y)\<rangle> \<in> R"
  proof -
    { fix x y
      assume "x \<in> A\<union>{M\<^sub>A}" and "y \<in> A\<union>{M\<^sub>A}"
      then have "x\<in>A \<and> y \<in> A \<or> x\<in>A \<and> y = M\<^sub>A \<or>
	x = M\<^sub>A \<and> y \<in> A \<or> x = M\<^sub>A \<and> y = M\<^sub>A"
	by auto
      moreover
      { assume "x\<in>A \<and> y \<in> A"
	with A1 I have "\<langle>x,y\<rangle> \<in> r \<longleftrightarrow> \<langle>?g`(x), ?g`(y)\<rangle> \<in> R" 
	  using ord_iso_def by simp }
      moreover
      { assume "x\<in>A \<and> y = M\<^sub>A"
	with A1 A3 I II have "\<langle>x,y\<rangle> \<in> r \<longleftrightarrow> \<langle>?g`(x), ?g`(y)\<rangle> \<in> R" 
	  using ord_iso_def bij_def inj_def apply_funtype
	  by auto }
      moreover
      { assume "x = M\<^sub>A \<and> y \<in> A"
	with A2 A3 A4 have "\<langle>x,y\<rangle> \<notin> r"
	  using antisym_def by auto
	moreover
	{ assume A6: "\<langle>?g`(x), ?g`(y)\<rangle> \<in> R"
	  from A1 I II \<open>x = M\<^sub>A \<and> y \<in> A\<close> have 
	    III: "?g`(y) \<in> B"  "?g`(x) = M\<^sub>B"
	    using ord_iso_def bij_def inj_def apply_funtype
	    by auto
	  with A3 have "\<langle>?g`(y), ?g`(x)\<rangle> \<in> R" by simp
	  with A4 A6 have "?g`(y) = ?g`(x)" using antisym_def
	    by auto
	  with A2 III have False by simp
	} hence "\<langle>?g`(x), ?g`(y)\<rangle> \<notin> R" by auto
	ultimately have "\<langle>x,y\<rangle> \<in> r \<longleftrightarrow> \<langle>?g`(x), ?g`(y)\<rangle> \<in> R" 
	by simp }
      moreover
      { assume "x = M\<^sub>A \<and> y = M\<^sub>A"
	with A5 II have "\<langle>x,y\<rangle> \<in> r \<longleftrightarrow> \<langle>?g`(x), ?g`(y)\<rangle> \<in> R" 
	  by simp }
      ultimately have "\<langle>x,y\<rangle> \<in> r \<longleftrightarrow> \<langle>?g`(x), ?g`(y)\<rangle> \<in> R" 
	by auto
    } thus ?thesis by auto
  qed 
  ultimately show ?thesis using ord_iso_def
    by simp
qed

text\<open>A kind of converse to \<open>ord_iso_rem_max\<close>: if two
  linearly ordered sets sets are order isomorphic 
  after removing the maxima, then they are order isomorphic.\<close>

lemma rem_max_ord_iso: 
  assumes A1: "IsLinOrder(X,r)"  "IsLinOrder(Y,R)" and 
  A2: "HasAmaximum(r,X)"  "HasAmaximum(R,Y)"
  "ord_iso(X - {Maximum(r,X)},r,Y - {Maximum(R,Y)},R) \<noteq> 0"
  shows "ord_iso(X,r,Y,R) \<noteq> 0"
proof -
  let ?M\<^sub>A = "Maximum(r,X)"
  let ?A = "X - {?M\<^sub>A}"
  let ?M\<^sub>B = "Maximum(R,Y)"
  let ?B = "Y - {?M\<^sub>B}"
  from A2 obtain f where "f \<in> ord_iso(?A,r,?B,R)"
    by auto
  moreover have "?M\<^sub>A \<notin> ?A" and "?M\<^sub>B \<notin> ?B"
    by auto
  moreover from A1 A2 have 
    "\<forall>a\<in>?A. \<langle>a,?M\<^sub>A\<rangle> \<in> r" and "\<forall>b\<in>?B. \<langle>b,?M\<^sub>B\<rangle> \<in> R"
    using IsLinOrder_def Order_ZF_4_L3 by auto
  moreover from A1 have "antisym(r)" and "antisym(R)"
    using IsLinOrder_def by auto
  moreover from A1 A2 have "\<langle>?M\<^sub>A,?M\<^sub>A\<rangle> \<in> r \<longleftrightarrow> \<langle>?M\<^sub>B,?M\<^sub>B\<rangle> \<in> R"
    using IsLinOrder_def Order_ZF_4_L3 IsLinOrder_def 
      total_is_refl refl_def by auto
  ultimately have 
    "f \<union> {\<langle> ?M\<^sub>A,?M\<^sub>B\<rangle>} \<in> ord_iso(?A\<union>{?M\<^sub>A} ,r,?B\<union>{?M\<^sub>B} ,R)"
    by (rule ord_iso_extend)
  moreover from A1 A2 have 
    "?A\<union>{?M\<^sub>A} = X" and "?B\<union>{?M\<^sub>B} = Y"
  using IsLinOrder_def Order_ZF_4_L3 by auto
  ultimately show "ord_iso(X,r,Y,R) \<noteq> 0"
    using ord_iso_extend by auto
qed
  
subsection\<open>Functions in cartesian products\<close>

text\<open>In this section we consider maps arising naturally
  in cartesian products.\<close>

text\<open>There is a natural bijection etween $X=Y\times \{ y\}$ (a "slice")
  and $Y$. 
  We will call this the \<open>SliceProjection(Y\<times>{y})\<close>. 
  This is really the ZF equivalent of the meta-function \<open>fst(x)\<close>.
\<close>

definition
  "SliceProjection(X) \<equiv> {\<langle>p,fst(p)\<rangle>. p \<in> X }"

text\<open>A slice projection is a bijection between $X\times\{ y\}$ and $X$.\<close>

lemma slice_proj_bij: shows 
  "SliceProjection(X\<times>{y}): X\<times>{y} \<rightarrow> X"
  "domain(SliceProjection(X\<times>{y})) = X\<times>{y}"
  "\<forall>p\<in>X\<times>{y}. SliceProjection(X\<times>{y})`(p) = fst(p)"
  "SliceProjection(X\<times>{y}) \<in> bij(X\<times>{y},X)"
proof -
  let ?P = "SliceProjection(X\<times>{y})"
  have  "\<forall>p \<in> X\<times>{y}. fst(p) \<in> X" by simp
  moreover from this have 
    "{\<langle>p,fst(p)\<rangle>. p \<in> X\<times>{y} } : X\<times>{y} \<rightarrow> X"
    by (rule ZF_fun_from_total)
  ultimately show 
    I: "?P: X\<times>{y} \<rightarrow> X" and II: "\<forall>p\<in>X\<times>{y}. ?P`(p) = fst(p)"
    using ZF_fun_from_tot_val SliceProjection_def by auto
  hence
    "\<forall>a \<in> X\<times>{y}. \<forall> b \<in> X\<times>{y}. ?P`(a) = ?P`(b) \<longrightarrow> a=b"
    by auto
  with I have "?P \<in> inj(X\<times>{y},X)" using inj_def 
    by simp
  moreover from II have "\<forall>x\<in>X. \<exists>p\<in>X\<times>{y}. ?P`(p) = x" 
    by simp
  with I have "?P \<in> surj(X\<times>{y},X)" using surj_def
    by simp
  ultimately show "?P \<in> bij(X\<times>{y},X)"
    using bij_def by simp
  from I show "domain(SliceProjection(X\<times>{y})) = X\<times>{y}"
    using func1_1_L1 by simp
qed

text\<open> Given 2 functions $f:A\to B$ and $g:C\to D$ , we can consider a function $h:A\times C \to B\times D$
such that $h(x,y)=\langle f(x),g(y)\rangle$ \<close>

definition
  ProdFunction where
  "ProdFunction(f,g) \<equiv> {\<langle>z,\<langle>f`(fst(z)),g`(snd(z))\<rangle>\<rangle>. z\<in>domain(f)\<times>domain(g)}"

text\<open> For given functions $f:A\to B$ and $g:C\to D$ the function \<open>ProdFunction(f,g)\<close>
  maps $A\times C$ to $B\times D$. \<close>

lemma prodFunction:
  assumes "f:A\<rightarrow>B" "g:C\<rightarrow>D"
  shows "ProdFunction(f,g):(A\<times>C)\<rightarrow>(B\<times>D)"
proof-
  from assms have "\<forall>z \<in> domain(f)\<times>domain(g). \<langle>f`(fst(z)),g`(snd(z))\<rangle> \<in> B\<times>D" 
    using func1_1_L1 apply_type by auto 
  with assms show ?thesis unfolding ProdFunction_def using func1_1_L1 ZF_fun_from_total
    by simp 
qed

text\<open> For given functions $f:A\to B$ and $g:C\to D$ and points $x\in A$, $y\in C$ the value of the 
  function \<open>ProdFunction(f,g)\<close> on $\langle x,y \rangle$ is $\langle f(x),g(y) \rangle$. \<close>

lemma prodFunctionApp:
  assumes "f:A\<rightarrow>B" "g:C\<rightarrow>D" "x\<in>A" "y\<in>C"
  shows "ProdFunction(f,g)`\<langle>x,y\<rangle> = \<langle>f`(x),g`(y)\<rangle>"
proof -
  let ?z = "\<langle>x,y\<rangle>"
  from assms have "?z \<in> A\<times>C" and "ProdFunction(f,g):(A\<times>C)\<rightarrow>(B\<times>D)"
    using prodFunction by auto 
  moreover from assms(1,2) have "ProdFunction(f,g) = {\<langle>z,\<langle>f`(fst(z)),g`(snd(z))\<rangle>\<rangle>. z\<in>A\<times>C}"
    unfolding ProdFunction_def using func1_1_L1 by blast
  ultimately show ?thesis using ZF_fun_from_tot_val by auto 
qed

text\<open>Somewhat technical lemma about inverse image of a set by a \<open>ProdFunction(f,f)\<close>. \<close>

lemma prodFunVimage: assumes "x\<in>X" "f:X\<rightarrow>Y"
  shows "\<langle>x,t\<rangle> \<in> ProdFunction(f,f)-``(V) \<longleftrightarrow> t\<in>X \<and> \<langle>f`x,f`t\<rangle> \<in> V"
proof -
  from assms(2) have T:"ProdFunction(f,f)-``(V) = {z \<in> X\<times>X. ProdFunction(f,f)`(z) \<in> V}"
    using prodFunction func1_1_L15 by blast 
  with assms show ?thesis using prodFunctionApp by auto 
qed


subsection\<open>Induced relations and order isomorphisms\<close>

text\<open>When we have two sets $X,Y$, function $f:X\rightarrow Y$ and
  a relation $R$ on $Y$ we can define a relation $r$ on $X$
  by saying that $x\ r\ y$ if and only if $f(x) \ R \ f(y)$. 
  This is especially interesting when $f$ is a bijection as all reasonable
  properties of $R$ are inherited by $r$. This section treats mostly the case
  when $R$ is an order relation and $f$ is a bijection.
  The standard Isabelle's \<open>Order\<close> theory 
  defines the notion of a space of order isomorphisms
  between two sets relative to a relation. We expand that material
  proving that order isomrphisms preserve interesting properties
  of the relation.\<close>

text\<open>We call the relation created by a relation on $Y$ and a mapping
  $f:X\rightarrow Y$ the \<open>InducedRelation(f,R)\<close>.\<close>

definition
  "InducedRelation(f,R) \<equiv> 
  {p \<in> domain(f)\<times>domain(f). \<langle>f`(fst(p)),f`(snd(p))\<rangle> \<in> R}"

text\<open>A reformulation of the definition of the relation induced by
  a function.\<close>

lemma def_of_ind_relA: 
  assumes "\<langle>x,y\<rangle> \<in> InducedRelation(f,R)"
  shows "\<langle>f`(x),f`(y)\<rangle> \<in> R"
  using assms InducedRelation_def by simp

text\<open>A reformulation of the definition of the relation induced by
  a function, kind of converse of \<open>def_of_ind_relA\<close>.\<close>

lemma def_of_ind_relB: assumes "f:A\<rightarrow>B" and 
  "x\<in>A"  "y\<in>A" and "\<langle>f`(x),f`(y)\<rangle> \<in> R"
  shows "\<langle>x,y\<rangle> \<in> InducedRelation(f,R)"
  using assms func1_1_L1 InducedRelation_def by simp

text\<open>A property of order isomorphisms that is missing from
  standard Isabelle's \<open>Order.thy\<close>.\<close>

lemma ord_iso_apply_conv: 
  assumes "f \<in> ord_iso(A,r,B,R)" and
  "\<langle>f`(x),f`(y)\<rangle> \<in> R" and "x\<in>A"  "y\<in>A"
  shows "\<langle>x,y\<rangle> \<in> r"
  using assms ord_iso_def by simp

text\<open>The next lemma tells us where the induced relation is defined\<close>

lemma ind_rel_domain: 
  assumes  "R \<subseteq> B\<times>B" and "f:A\<rightarrow>B"
  shows "InducedRelation(f,R) \<subseteq> A\<times>A"
  using assms func1_1_L1 InducedRelation_def
  by auto

text\<open>A bijection is an order homomorphisms between a relation
  and the induced one.\<close>

lemma bij_is_ord_iso: assumes A1: "f \<in> bij(A,B)"
  shows "f \<in> ord_iso(A,InducedRelation(f,R),B,R)"
proof -
  let ?r = "InducedRelation(f,R)"
  { fix x y assume A2: "x\<in>A"  "y\<in>A"
    have "\<langle>x,y\<rangle> \<in> ?r \<longleftrightarrow> \<langle>f`(x),f`(y)\<rangle> \<in> R" 
    proof
      assume "\<langle>x,y\<rangle> \<in> ?r" then show "\<langle>f`(x),f`(y)\<rangle> \<in> R" 
	using def_of_ind_relA by simp
    next assume "\<langle>f`(x),f`(y)\<rangle> \<in> R"
      with A1 A2 show "\<langle>x,y\<rangle> \<in> ?r"
	using bij_is_fun def_of_ind_relB by blast 
    qed }
  with A1 show "f \<in> ord_iso(A,InducedRelation(f,R),B,R)"
    using ord_isoI by simp
qed

text\<open>An order isomoprhism preserves antisymmetry.\<close>

lemma ord_iso_pres_antsym: assumes A1: "f \<in> ord_iso(A,r,B,R)" and 
  A2: "r \<subseteq> A\<times>A" and A3: "antisym(R)"
  shows "antisym(r)"
proof -
  { fix x y
    assume A4: "\<langle>x,y\<rangle> \<in> r"   "\<langle>y,x\<rangle> \<in> r"
    from A1 have "f \<in> inj(A,B)"
      using ord_iso_is_bij bij_is_inj by simp
    moreover
    from A1 A2 A4 have 
      "\<langle>f`(x), f`(y)\<rangle> \<in> R" and "\<langle>f`(y), f`(x)\<rangle> \<in> R"
      using ord_iso_apply by auto
    with A3 have "f`(x) = f`(y)" by (rule Fol1_L4)
    moreover from A2 A4 have "x\<in>A"  "y\<in>A" by auto
    ultimately have "x=y" by (rule inj_apply_equality)
  } then have "\<forall>x y. \<langle>x,y\<rangle> \<in> r \<and> \<langle>y,x\<rangle> \<in> r \<longrightarrow> x=y" by auto
  then show "antisym(r)" using imp_conj antisym_def
    by simp
qed      

text\<open>Order isomoprhisms preserve transitivity.\<close>

lemma ord_iso_pres_trans: assumes A1: "f \<in> ord_iso(A,r,B,R)" and 
  A2: "r \<subseteq> A\<times>A" and A3: "trans(R)"
  shows "trans(r)"
proof -
  { fix x y z
    assume A4: "\<langle>x, y\<rangle> \<in> r"   "\<langle>y, z\<rangle> \<in> r"
    note A1
    moreover
    from A1 A2 A4 have 
      "\<langle>f`(x), f`(y)\<rangle> \<in> R \<and> \<langle>f`(y), f`(z)\<rangle> \<in> R"
      using ord_iso_apply by auto
    with A3 have "\<langle>f`(x),f`(z)\<rangle> \<in> R" by (rule Fol1_L3)
    moreover from A2 A4 have "x\<in>A"  "z\<in>A" by auto
    ultimately have "\<langle>x, z\<rangle> \<in> r" using ord_iso_apply_conv
      by simp
  } then have  "\<forall> x y z. \<langle>x, y\<rangle> \<in> r \<and> \<langle>y, z\<rangle> \<in> r \<longrightarrow> \<langle>x, z\<rangle> \<in> r"
    by blast
  then show "trans(r)" by (rule Fol1_L2)
qed
     
text\<open>Order isomorphisms preserve totality.\<close>

lemma ord_iso_pres_tot: assumes A1: "f \<in> ord_iso(A,r,B,R)" and 
  A2: "r \<subseteq> A\<times>A" and A3: "R  {is total on} B"
  shows "r  {is total on} A"
proof -
  { fix x y
    assume "x\<in>A"  "y\<in>A"  "\<langle>x,y\<rangle> \<notin> r"  
    with A1 have "\<langle>f`(x),f`(y)\<rangle> \<notin> R" using ord_iso_apply_conv
      by auto
    moreover 
    from A1 have "f:A\<rightarrow>B" using ord_iso_is_bij bij_is_fun 
      by simp
    with A3 \<open>x\<in>A\<close>  \<open>y\<in>A\<close> have 
      "\<langle>f`(x),f`(y)\<rangle> \<in>  R \<or> \<langle>f`(y),f`(x)\<rangle> \<in>  R"
      using apply_funtype IsTotal_def by simp
    ultimately have "\<langle>f`(y),f`(x)\<rangle> \<in>  R" by simp
    with A1 \<open>x\<in>A\<close>  \<open>y\<in>A\<close> have "\<langle>y,x\<rangle> \<in> r" 
      using ord_iso_apply_conv  by simp
  } then have "\<forall>x\<in>A. \<forall>y\<in>A. \<langle>x,y\<rangle> \<in> r \<or>  \<langle>y,x\<rangle> \<in> r"
    by blast
  then show "r  {is total on} A" using IsTotal_def
    by simp
qed

text\<open>Order isomorphisms preserve linearity.\<close>

lemma ord_iso_pres_lin: assumes "f \<in> ord_iso(A,r,B,R)" and 
  "r \<subseteq> A\<times>A" and "IsLinOrder(B,R)"
  shows "IsLinOrder(A,r)"
  using assms ord_iso_pres_antsym ord_iso_pres_trans ord_iso_pres_tot
    IsLinOrder_def by simp

text\<open>If a relation is a linear order, then the relation induced
  on another set by a bijection is also a linear order.\<close>

lemma ind_rel_pres_lin: 
  assumes A1: "f \<in> bij(A,B)" and A2: "IsLinOrder(B,R)"
  shows "IsLinOrder(A,InducedRelation(f,R))"
proof -
  let ?r = "InducedRelation(f,R)"
  from A1 have "f \<in> ord_iso(A,?r,B,R)" and "?r \<subseteq> A\<times>A"
    using bij_is_ord_iso domain_of_bij InducedRelation_def 
    by auto
  with A2 show "IsLinOrder(A,?r)" using ord_iso_pres_lin 
    by simp
qed

text\<open>The image by an order isomorphism 
  of a bounded above and nonempty set is bounded above.\<close>

lemma ord_iso_pres_bound_above: 
  assumes A1: "f \<in> ord_iso(A,r,B,R)" and A2: "r \<subseteq> A\<times>A" and
  A3: "IsBoundedAbove(C,r)"   "C\<noteq>0"
  shows "IsBoundedAbove(f``(C),R)"   "f``(C) \<noteq> 0"
proof -
  from A3 obtain u where I: "\<forall>x\<in>C. \<langle>x,u\<rangle> \<in> r"
    using IsBoundedAbove_def by auto
  from A1 have "f:A\<rightarrow>B" using ord_iso_is_bij bij_is_fun
    by simp
  from A2 A3 have "C\<subseteq>A" using Order_ZF_3_L1A by blast
  from A3 obtain x where "x\<in>C" by auto
  with A2 I have "u\<in>A" by auto
  { fix y assume "y \<in> f``(C)"
    with \<open>f:A\<rightarrow>B\<close> \<open>C\<subseteq>A\<close> obtain x where "x\<in>C" and "y = f`(x)"
      using func_imagedef by auto
    with A1 I \<open>C\<subseteq>A\<close>  \<open>u\<in>A\<close> have "\<langle>y,f`(u)\<rangle> \<in> R"
      using ord_iso_apply by auto
  } then have "\<forall>y \<in> f``(C).  \<langle>y,f`(u)\<rangle> \<in> R" by simp
  then show "IsBoundedAbove(f``(C),R)" by (rule Order_ZF_3_L10)
  from A3 \<open>f:A\<rightarrow>B\<close> \<open>C\<subseteq>A\<close> show "f``(C) \<noteq> 0" using func1_1_L15A
    by simp
qed

text\<open>Order isomorphisms preserve the property of having a minimum.\<close>

lemma ord_iso_pres_has_min: 
  assumes A1: "f \<in> ord_iso(A,r,B,R)" and  A2: "r \<subseteq> A\<times>A" and 
  A3: "C\<subseteq>A" and A4: "HasAminimum(R,f``(C))"
  shows "HasAminimum(r,C)"
proof -
  from A4 obtain m where 
    I: "m \<in> f``(C)" and II: "\<forall>y \<in> f``(C). \<langle>m,y\<rangle> \<in> R"
    using HasAminimum_def by auto
  let ?k = "converse(f)`(m)"
  from A1 have "f:A\<rightarrow>B" using ord_iso_is_bij bij_is_fun
    by simp
  from A1 have "f \<in> inj(A,B)" using ord_iso_is_bij bij_is_inj
    by simp
  with A3 I have "?k \<in> C" and III: "f`(?k) = m" 
    using inj_inv_back_in_set by auto
  moreover
  { fix x assume A5: "x\<in>C"
    with A3 II \<open>f:A\<rightarrow>B\<close> \<open>?k \<in> C\<close> III have
      "?k \<in> A"   "x\<in>A"  "\<langle>f`(?k),f`(x)\<rangle> \<in> R"
      using func_imagedef by auto
    with A1 have "\<langle>?k,x\<rangle> \<in> r" using ord_iso_apply_conv
      by simp
  } then have "\<forall>x\<in>C.  \<langle>?k,x\<rangle> \<in> r" by simp
  ultimately show "HasAminimum(r,C)" using HasAminimum_def by auto
qed

text\<open>Order isomorhisms preserve the images of relations.
  In other words taking the image of a point by a relation
  commutes with the function.\<close>

lemma ord_iso_pres_rel_image: 
  assumes A1: "f \<in> ord_iso(A,r,B,R)" and  
  A2: "r \<subseteq> A\<times>A"  "R \<subseteq> B\<times>B" and 
  A3: "a\<in>A"
  shows "f``(r``{a}) = R``{f`(a)}"
proof
  from A1 have "f:A\<rightarrow>B" using ord_iso_is_bij bij_is_fun
    by simp
  moreover from A2 A3 have I: "r``{a} \<subseteq> A" by auto
  ultimately have I: "f``(r``{a}) = {f`(x). x \<in> r``{a} }"
    using func_imagedef by simp
  { fix y assume A4: "y \<in> f``(r``{a})" 
    with I obtain x where 
      "x \<in> r``{a}" and II: "y = f`(x)"
      by auto
    with A1 A2 have "\<langle>f`(a),f`(x)\<rangle> \<in> R" using ord_iso_apply
      by auto
    with II have "y \<in>  R``{f`(a)}" by auto
  } then show  "f``(r``{a}) \<subseteq> R``{f`(a)}" by auto
  { fix y assume A5: "y \<in> R``{f`(a)}" 
    let ?x = "converse(f)`(y)"
    from A2 A5 have 
      "\<langle>f`(a),y\<rangle> \<in> R"  "f`(a) \<in> B"  and IV: "y\<in>B"
      by auto
    with A1 have III: "\<langle>converse(f)`(f`(a)),?x\<rangle> \<in> r"
      using ord_iso_converse by simp
    moreover from A1 A3 have "converse(f)`(f`(a)) = a"
      using ord_iso_is_bij left_inverse_bij by blast
    ultimately have "f`(?x) \<in> {f`(x). x \<in>  r``{a} }"
      by auto
    moreover from A1 IV have "f`(?x) = y"
      using ord_iso_is_bij right_inverse_bij by blast
    moreover from A1 I have "f``(r``{a}) = {f`(x). x \<in>  r``{a} }"
      using ord_iso_is_bij bij_is_fun func_imagedef by blast
    ultimately have "y \<in> f``(r``{a})" by simp
  } then show "R``{f`(a)} \<subseteq> f``(r``{a})" by auto
qed

text\<open>Order isomorphisms preserve collections of upper bounds.\<close>

lemma ord_iso_pres_up_bounds: 
  assumes A1: "f \<in> ord_iso(A,r,B,R)" and  
  A2: "r \<subseteq> A\<times>A"  "R \<subseteq> B\<times>B" and 
  A3: "C\<subseteq>A" 
  shows "{f``(r``{a}). a\<in>C} = {R``{b}. b \<in> f``(C)}"
proof
  from A1 have "f:A\<rightarrow>B"
      using ord_iso_is_bij bij_is_fun by simp
  { fix Y assume "Y \<in> {f``(r``{a}). a\<in>C}"
    then obtain a where "a\<in>C" and I: "Y = f``(r``{a})"
      by auto
    from A3 \<open>a\<in>C\<close> have "a\<in>A" by auto
    with A1 A2 have "f``(r``{a}) = R``{f`(a)}"
      using ord_iso_pres_rel_image by simp
    moreover from A3 \<open>f:A\<rightarrow>B\<close> \<open>a\<in>C\<close> have "f`(a) \<in> f``(C)"
      using func_imagedef by auto
    ultimately have "f``(r``{a}) \<in> { R``{b}. b \<in> f``(C) }"
      by auto
    with I have "Y \<in> { R``{b}. b \<in> f``(C) }" by simp
  } then show "{f``(r``{a}). a\<in>C} \<subseteq> {R``{b}. b \<in> f``(C)}"
    by blast
  { fix Y assume "Y \<in> {R``{b}. b \<in> f``(C)}"
    then obtain b where "b \<in> f``(C)" and II: "Y = R``{b}"
      by auto
    with A3 \<open>f:A\<rightarrow>B\<close> obtain a where "a\<in>C" and "b = f`(a)"
      using func_imagedef by auto
    with A3 II have "a\<in>A" and "Y = R``{f`(a)}" by auto 
    with A1 A2 have "Y = f``(r``{a})"
      using ord_iso_pres_rel_image by simp
    with \<open>a\<in>C\<close> have "Y \<in> {f``(r``{a}). a\<in>C}" by auto
  } then show "{R``{b}. b \<in> f``(C)} \<subseteq> {f``(r``{a}). a\<in>C}"
    by auto
qed
    
text\<open>The image of the set of upper bounds is the set of upper bounds
  of the image.\<close>
  
lemma ord_iso_pres_min_up_bounds: 
  assumes A1: "f \<in> ord_iso(A,r,B,R)" and  A2: "r \<subseteq> A\<times>A"  "R \<subseteq> B\<times>B" and 
  A3: "C\<subseteq>A" and A4: "C\<noteq>0"
  shows "f``(\<Inter>a\<in>C. r``{a}) = (\<Inter>b\<in>f``(C). R``{b})"
proof -
  from A1 have "f \<in> inj(A,B)"
    using ord_iso_is_bij bij_is_inj by simp
  moreover note A4
  moreover from A2 A3 have "\<forall>a\<in>C. r``{a} \<subseteq> A" by auto
  ultimately have 
    "f``(\<Inter>a\<in>C. r``{a}) = ( \<Inter>a\<in>C. f``(r``{a}) )"
    using inj_image_of_Inter by simp
  also from A1 A2 A3 have
    "( \<Inter>a\<in>C. f``(r``{a}) ) = ( \<Inter>b\<in>f``(C). R``{b} )"
    using ord_iso_pres_up_bounds by simp
  finally show "f``(\<Inter>a\<in>C. r``{a}) = (\<Inter>b\<in>f``(C). R``{b})"
    by simp
qed

text\<open>Order isomorphisms preserve completeness.\<close>

lemma ord_iso_pres_compl: 
  assumes A1: "f \<in> ord_iso(A,r,B,R)" and 
  A2: "r \<subseteq> A\<times>A"  "R \<subseteq> B\<times>B" and A3: "R {is complete}"
  shows "r {is complete}"
proof -
  { fix C
    assume A4: "IsBoundedAbove(C,r)"  "C\<noteq>0"
    with A1 A2 A3 have 
      "HasAminimum(R,\<Inter>b \<in> f``(C). R``{b})"
      using ord_iso_pres_bound_above IsComplete_def
      by simp
    moreover
    from A2 \<open>IsBoundedAbove(C,r)\<close> have I: "C \<subseteq> A" using Order_ZF_3_L1A
      by blast
    with A1 A2 \<open>C\<noteq>0\<close> have "f``(\<Inter>a\<in>C. r``{a}) = (\<Inter>b\<in>f``(C). R``{b})"
      using ord_iso_pres_min_up_bounds by simp
    ultimately have "HasAminimum(R,f``(\<Inter>a\<in>C. r``{a}))"
      by simp
    moreover
    from A2 have "\<forall>a\<in>C. r``{a} \<subseteq> A" 
      by auto
    with \<open>C\<noteq>0\<close> have "( \<Inter>a\<in>C. r``{a} ) \<subseteq> A" using ZF1_1_L7 
      by simp
    moreover note A1 A2 
    ultimately have "HasAminimum(r, \<Inter>a\<in>C. r``{a} )"
      using ord_iso_pres_has_min by simp
  } then show "r {is complete}" using IsComplete_def
    by simp
qed

text\<open>If the original relation is complete, then the induced
  one is complete.\<close>

lemma ind_rel_pres_compl: assumes A1: "f \<in> bij(A,B)"
  and A2: "R \<subseteq> B\<times>B" and A3: "R {is complete}"
  shows "InducedRelation(f,R) {is complete}"
proof -
  let ?r = "InducedRelation(f,R)"
  from A1 have "f \<in> ord_iso(A,?r,B,R)"
    using bij_is_ord_iso by simp
  moreover from A1 A2 have "?r \<subseteq> A\<times>A"
    using bij_is_fun ind_rel_domain by simp
  moreover note A2 A3
  ultimately show "?r {is complete}"
    using ord_iso_pres_compl by simp 
qed
  

end
