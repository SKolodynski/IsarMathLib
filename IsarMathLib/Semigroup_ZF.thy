(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2007-2009  Slawomir Kolodynski

    This progr\rightarowam is free software; Redistribution and use in source and binary forms, 
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

section \<open>Semigroups\<close>

theory Semigroup_ZF imports Partitions_ZF Fold_ZF Enumeration_ZF

begin

text\<open>It seems that the minimal setup needed to talk about a product of a 
  sequence is a set with a binary operation. 
  Such object is called "magma". However, interesting properties
  show up when the binary operation is associative and such alebraic structure
  is called a semigroup. 
  In this theory file we define and study sequences of partial 
  products of sequences of magma and semigroup elements.\<close>

subsection\<open>Products of sequences of semigroup elements\<close>

text\<open>Semigroup is a a magma in which the binary operation is associative.
  In this section we mostly study the products of sequences of elements 
  of semigroup. The goal is to establish the fact that taking the product of 
  a sequence is distributive with respect to concatenation of sequences, 
  i.e for two sequences $a,b$ of the semigroup elements we have 
  $\prod (a\sqcup b) = (\prod a)\cdot (\prod b)$, where "$a \sqcup b$" 
  is concatenation of $a$ and $b$ ($a$\<open>++\<close>$b$ in Haskell notation).
  Less formally, we want to show that we can discard parantheses in 
  expressions of the form 
  $(a_0\cdot a_1\cdot .. \cdot a_n)\cdot (b_0\cdot .. \cdot b_k)$.
\<close>

text\<open>First we define a notion similar to \<open>Fold\<close>, except that
  that the initial element of the fold is given by the first element
  of sequence. By analogy with Haskell fold we call that \<open>Fold1\<close>
\<close>

definition
  "Fold1(f,a) \<equiv> Fold(f,a`(0),Tail(a))"

text\<open>The definition of the \<open>semigr0\<close> context below introduces notation
  for writing about finite sequences and semigroup products. 
  In the context we fix the carrier and
  denote it $G$. The binary operation on $G$ is called $f$. 
  All theorems proven in the context \<open>semigr0\<close> 
  will implicitly assume that $f$ is an associative operation on $G$.
  We will use multiplicative notation for the semigroup operation.
  The product of a sequence $a$ is denoted $\prod a$.
  We will write
  $a\hookleftarrow x$ for the result of appending an element $x$ to
  the finite sequence (list) $a$. This is a bit nonstandard, 
  but I don't have a better idea for the "append" notation. Finally,
  $a\sqcup b$ will denote the concatenation of the lists $a$ and $b$.\<close>

locale semigr0 =
  
  fixes G f

  assumes assoc_assum: "f {is associative on} G"

  fixes prod (infixl "\<cdot>" 72)
  defines prod_def [simp]: "x \<cdot> y \<equiv> f`\<langle>x,y\<rangle>"

  fixes seqprod ("\<Prod> _" 71)
  defines seqprod_def [simp]: "\<Prod> a \<equiv> Fold1(f,a)"

  fixes append (infix "\<hookleftarrow>" 72)
  defines append_def [simp]: "a \<hookleftarrow> x \<equiv> Append(a,x)"

  fixes concat (infixl "\<squnion>" 69)
  defines concat_def [simp]: "a \<squnion> b \<equiv> Concat(a,b)"

text\<open>The next lemma shows our assumption on the associativity
  of the semigroup operation in the notation defined in in the 
  \<open>semigr0\<close> context.\<close>

lemma (in semigr0) semigr_assoc: assumes "x \<in> G"  "y \<in> G"  "z \<in> G"
  shows "x\<cdot>y\<cdot>z = x\<cdot>(y\<cdot>z)"
  using assms assoc_assum IsAssociative_def by simp

text\<open>In the way we define associativity the assumption that
  $f$ is associative on $G$ also implies that it is a binary
  operation on $X$.\<close>

lemma (in semigr0) semigr_binop: shows "f : G\<times>G \<rightarrow> G"
  using assoc_assum IsAssociative_def by simp

text\<open>Semigroup operation is closed.\<close>

lemma (in semigr0) semigr_closed: 
  assumes "a\<in>G"  "b\<in>G" shows "a\<cdot>b \<in> G"
  using assms semigr_binop apply_funtype by simp

text\<open>Lemma \<open>append_1elem\<close> written in the notation used in 
  the \<open>semigr0\<close> context.\<close>

lemma (in semigr0) append_1elem_nice: 
  assumes "n \<in> nat" and "a: n \<rightarrow> X" and "b : 1 \<rightarrow> X"
  shows "a \<squnion> b = a \<hookleftarrow> b`(0)"
  using assms append_1elem by simp

text\<open>Lemma \<open>concat_init_last_elem\<close> rewritten
  in the notation used in the \<open>semigr0\<close> context.\<close>

lemma (in semigr0) concat_init_last: 
  assumes "n \<in> nat"  "k \<in> nat" and 
  "a: n \<rightarrow> X"  and "b : succ(k) \<rightarrow> X"
  shows "(a \<squnion> Init(b)) \<hookleftarrow> b`(k) = a \<squnion> b"
  using assms concat_init_last_elem by simp

text\<open>The product of semigroup (actually, magma -- we don't
   need associativity for this) elements is in the semigroup.\<close>

lemma (in semigr0) prod_type: 
  assumes "n \<in> nat" and "a : succ(n) \<rightarrow> G"
  shows "(\<Prod> a) \<in> G"
proof -
  from assms have 
    "succ(n) \<in> nat"  "f : G\<times>G \<rightarrow> G"  "Tail(a) : n \<rightarrow> G"
    using semigr_binop tail_props by auto
  moreover from assms have "a`(0) \<in> G" and "G \<noteq> 0"
    using empty_in_every_succ apply_funtype
    by auto
  ultimately show "(\<Prod> a) \<in> G" using Fold1_def fold_props
    by simp
qed

text\<open>What is the product of one element list?\<close>

lemma (in semigr0) prod_of_1elem: assumes A1: "a: 1 \<rightarrow> G"
  shows "(\<Prod> a) = a`(0)"
proof -
  have "f : G\<times>G \<rightarrow> G" using semigr_binop by simp
  moreover from A1 have "Tail(a) : 0 \<rightarrow> G" using tail_props
    by blast
  moreover from A1 have "a`(0) \<in> G" and "G \<noteq> 0" 
    using apply_funtype by auto
  ultimately show "(\<Prod> a) =  a`(0)" using fold_empty Fold1_def 
    by simp
qed

text\<open>What happens to the product of a list when we append an element 
  to the list?\<close>

lemma (in semigr0) prod_append: assumes A1: "n \<in> nat" and
  A2: "a : succ(n) \<rightarrow> G" and A3: "x\<in>G"
  shows "(\<Prod> a\<hookleftarrow>x) = (\<Prod> a) \<cdot> x"
proof -
  from A1 A2 have I: "Tail(a) : n \<rightarrow> G"  "a`(0) \<in> G"
    using tail_props empty_in_every_succ apply_funtype
    by auto
  from assms have "(\<Prod> a\<hookleftarrow>x) = Fold(f,a`(0),Tail(a)\<hookleftarrow>x)"
    using head_of_append tail_append_commute Fold1_def
    by simp
  also from A1 A3 I have "\<dots> = (\<Prod> a) \<cdot> x"
    using semigr_binop fold_append Fold1_def 
    by simp
  finally show ?thesis by simp
qed

text\<open>The main theorem of the section: taking the product of 
  a sequence is distributive with respect to concatenation of sequences.
  The proof is by induction on the length of the second list.\<close>

theorem (in semigr0) prod_conc_distr: 
  assumes A1: "n \<in> nat"  "k \<in> nat" and
  A2: "a : succ(n) \<rightarrow> G"   "b: succ(k) \<rightarrow> G"
  shows "(\<Prod> a) \<cdot> (\<Prod> b) = \<Prod> (a \<squnion> b)"
proof -
  from A1 have "k \<in> nat" by simp
  moreover have "\<forall>b \<in> succ(0) \<rightarrow> G. (\<Prod> a) \<cdot> (\<Prod> b) = \<Prod> (a \<squnion> b)"
  proof -
    { fix b assume A3: "b : succ(0) \<rightarrow> G"
      with A1 A2 have
	"succ(n) \<in> nat"  "a : succ(n) \<rightarrow> G"  "b : 1 \<rightarrow> G" 
	by auto
      then have "a \<squnion> b = a \<hookleftarrow> b`(0)" by (rule append_1elem_nice)
      with A1 A2 A3 have "(\<Prod> a) \<cdot> (\<Prod> b) = \<Prod> (a \<squnion> b)"
	using apply_funtype prod_append semigr_binop prod_of_1elem
	by simp
    } thus ?thesis by simp
  qed
  moreover have "\<forall>j \<in> nat. 
    (\<forall>b \<in> succ(j) \<rightarrow> G. (\<Prod> a) \<cdot> (\<Prod> b) = \<Prod> (a \<squnion> b)) \<longrightarrow>
    (\<forall>b \<in> succ(succ(j)) \<rightarrow> G. (\<Prod> a) \<cdot> (\<Prod> b) = \<Prod> (a \<squnion> b))"
  proof -
    { fix j assume A4: "j \<in> nat" and 
      A5: "(\<forall>b \<in> succ(j) \<rightarrow> G. (\<Prod> a) \<cdot> (\<Prod> b) = \<Prod> (a \<squnion> b))"
      { fix b assume A6: "b : succ(succ(j)) \<rightarrow> G"
	let ?c = "Init(b)"
	from A4 A6 have  T: "b`(succ(j)) \<in> G" and
	  I: "?c : succ(j) \<rightarrow> G" and II: "b = ?c\<hookleftarrow>b`(succ(j))"
	  using apply_funtype init_props by auto
	from A1 A2 A4 A6 have
	  "succ(n) \<in> nat"  "succ(j) \<in> nat"
	  "a : succ(n) \<rightarrow> G"  "b : succ(succ(j)) \<rightarrow> G"
	  by auto
	then have III: "(a \<squnion> ?c) \<hookleftarrow> b`(succ(j)) = a \<squnion> b"
	  by (rule concat_init_last)
	from A4 I T have "(\<Prod> ?c\<hookleftarrow>b`(succ(j))) = (\<Prod> ?c) \<cdot> b`(succ(j))"
	  by (rule prod_append)
	with II have 
	  "(\<Prod> a) \<cdot> (\<Prod> b) = (\<Prod> a) \<cdot> ((\<Prod> ?c) \<cdot> b`(succ(j)))"
	  by simp
	moreover from A1 A2 A4 T I have
	  "(\<Prod> a) \<in> G"  "(\<Prod> ?c) \<in> G"  "b`(succ(j)) \<in> G"
	  using prod_type by auto
	ultimately have 
	  "(\<Prod> a) \<cdot> (\<Prod> b) =  ((\<Prod> a) \<cdot> (\<Prod> ?c)) \<cdot> b`(succ(j))"
	  using semigr_assoc by auto
	with A5 I have "(\<Prod> a) \<cdot> (\<Prod> b) = (\<Prod> (a \<squnion> ?c))\<cdot>b`(succ(j))"
	  by simp
	moreover
	from A1 A2 A4 I have
	  T1: "succ(n) \<in> nat"  "succ(j) \<in> nat" and
	  "a : succ(n) \<rightarrow> G"   "?c : succ(j) \<rightarrow> G"
	  by auto
	then have "Concat(a,?c): succ(n) #+ succ(j) \<rightarrow> G"
	  by (rule concat_props)
	with A1 A4 T have
	  "succ(n #+ j) \<in> nat"   
	  "a \<squnion> ?c : succ(succ(n #+j)) \<rightarrow> G"
	  "b`(succ(j)) \<in> G"
	  using succ_plus by auto
	then have 
	  "(\<Prod> (a \<squnion> ?c)\<hookleftarrow>b`(succ(j))) = (\<Prod> (a \<squnion> ?c))\<cdot>b`(succ(j))"
	  by (rule prod_append)
	with III have "(\<Prod> (a \<squnion> ?c))\<cdot>b`(succ(j)) =  \<Prod> (a \<squnion> b)"
	  by simp
	ultimately have "(\<Prod> a) \<cdot> (\<Prod> b) = \<Prod> (a \<squnion> b)"
	  by simp
      } hence "(\<forall>b \<in> succ(succ(j)) \<rightarrow> G. (\<Prod> a) \<cdot> (\<Prod> b) = \<Prod> (a \<squnion> b))"
	by simp
    } thus ?thesis by blast
  qed
  ultimately have "\<forall>b \<in> succ(k) \<rightarrow> G. (\<Prod> a) \<cdot> (\<Prod> b) = \<Prod> (a \<squnion> b)"
    by (rule ind_on_nat)
  with A2 show "(\<Prod> a) \<cdot> (\<Prod> b) = \<Prod> (a \<squnion> b)" by simp
qed

text\<open> $a\cdot b \cdot (c\cdot d) = a\cdot (b \cdot c) \cdot d$ for
  semigrouop elements $a,b,c,d \in G$. The \<open>Commutative semigroups\<close> section
  below contains a couple of rearrangements that need commutativity of the semigroup
  operation, but this one uses only associativity, so it's here. \<close>

lemma (in semigr0) rearr4elem_assoc: 
  assumes "a\<in>G"  "b\<in>G"  "c\<in>G"  "d\<in>G"
  shows "a\<cdot>b\<cdot>(c\<cdot>d) = a\<cdot>(b\<cdot>c)\<cdot>d"
proof -
  from assms have "a\<cdot>b\<cdot>(c\<cdot>d) = a\<cdot>b\<cdot>c\<cdot>d" using semigr_closed semigr_assoc
    by simp
  with assms(1,2,3) show ?thesis using semigr_assoc by simp
qed

subsection\<open>Products over sets of indices\<close>

text\<open>In this section we study the properties of 
  expressions of the form
  $\prod_{i\in \Lambda} a_i = a_{i_0}\cdot a_{i_1} \cdot .. \cdot a_{i-1}$,
  i.e. what we denote as \<open>\<pr>(\<Lambda>,a)\<close>. $\Lambda$ here is
  a finite subset of some set $X$ and $a$ is a function defined
  on $X$ with values in the semigroup $G$.\<close>


text\<open>Suppose $a: X \rightarrow G$ is an indexed family of elements
  of a semigroup $G$ and 
  $\Lambda = \{i_0, i_1, .. , i_{n-1}\} \subseteq \mathbb{N}$ is a finite 
  set of indices. We want to define 
  $\prod_{i\in \Lambda} a_i = a_{i_0}\cdot a_{i_1} \cdot .. \cdot a_{i-1}$.
  To do that we use the notion of \<open>Enumeration\<close> defined in the
  \<open>Enumeration_ZF\<close> theory file that takes a set of indices and 
  lists them in increasing order, thus converting it to list. Then we use 
  the \<open>Fold1\<close> to multiply the resulting list. Recall that in 
  Isabelle/ZF the capital letter ''O'' denotes the composition of two 
  functions (or relations).
\<close>

definition
  "SetFold(f,a,\<Lambda>,r) = Fold1(f,a O Enumeration(\<Lambda>,r))"

text\<open>For 
  a finite subset $\Lambda$ of a linearly ordered set $X$
  we will write $\sigma (\Lambda )$ 
  to denote the enumeration of the elements of $\Lambda$, i.e. the only 
  order isomorphism $|\Lambda | \rightarrow \Lambda$, where 
  $|\Lambda | \in \mathbb{N}$ is the number of elements of $\Lambda $.
  We also define
  notation for taking a product over a set of indices of some sequence
  of semigroup elements. The product of semigroup
  elements over some set $\Lambda \subseteq X$ of indices
  of a sequence $a: X \rightarrow G$ (i.e. $\prod_{i\in \Lambda} a_i$) 
  is denoted \<open>\<pr>(\<Lambda>,a)\<close>.
  In the \<open>semigr1\<close> context we assume that $a$ is a 
  function defined on some
  linearly ordered set $X$ with values in the semigroup $G$.
\<close>

locale semigr1 = semigr0 +
  
  fixes X r
  assumes linord: "IsLinOrder(X,r)"

  fixes a
  assumes a_is_fun: "a : X \<rightarrow> G"

  fixes \<sigma>
  defines \<sigma>_def [simp]: "\<sigma>(A) \<equiv> Enumeration(A,r)"

  fixes setpr ("\<pr>")
  defines setpr_def [simp]: "\<pr>(\<Lambda>,b) \<equiv> SetFold(f,b,\<Lambda>,r)"

text\<open>We can use the \<open>enums\<close> locale in the \<open>semigr0\<close> 
  context.\<close>

lemma (in semigr1) enums_valid_in_semigr1: shows "enums(X,r)"
  using linord enums_def by simp

text\<open>Definition of product over a set expressed
  in notation of the \<open>semigr0\<close> locale.\<close>

lemma (in semigr1) setproddef: 
  shows "\<pr>(\<Lambda>,a) = \<Prod> (a O \<sigma>(\<Lambda>))"
  using SetFold_def by simp

text\<open>A composition of enumeration of a nonempty 
  finite subset of $\mathbb{N}$
  with a sequence of elements of $G$ is a nonempty list of elements of $G$.
  This implies that a product over set of a finite set of indices belongs
  to the (carrier of) semigroup.
\<close>

lemma (in semigr1) setprod_type: assumes 
  A1: "\<Lambda> \<in> FinPow(X)" and A2: "\<Lambda>\<noteq>0"
  shows 
  "\<exists>n \<in> nat . |\<Lambda>| = succ(n) \<and> a O \<sigma>(\<Lambda>) : succ(n) \<rightarrow> G"
  and "\<pr>(\<Lambda>,a) \<in> G"
proof -
  from assms obtain n where "n \<in> nat" and "|\<Lambda>| = succ(n)"
    using card_non_empty_succ by auto
  from A1 have "\<sigma>(\<Lambda>) : |\<Lambda>| \<rightarrow> \<Lambda>"
    using enums_valid_in_semigr1 enums.enum_props 
    by simp
  with A1 have "a O \<sigma>(\<Lambda>): |\<Lambda>| \<rightarrow> G"
    using a_is_fun FinPow_def comp_fun_subset 
    by simp
  with \<open>n \<in> nat\<close> and \<open>|\<Lambda>| = succ(n)\<close> show 
    "\<exists>n \<in> nat . |\<Lambda>| = succ(n) \<and> a O \<sigma>(\<Lambda>) : succ(n) \<rightarrow> G"
    by auto
  from  \<open>n \<in> nat\<close> \<open>|\<Lambda>| = succ(n)\<close> \<open>a O \<sigma>(\<Lambda>): |\<Lambda>| \<rightarrow> G\<close>
  show "\<pr>(\<Lambda>,a) \<in> G" using prod_type setproddef 
    by auto
qed

text\<open>The \<open>enum_append\<close> lemma from the 
  \<open>Enemeration\<close> theory specialized for natural
  numbers.\<close> 

lemma (in semigr1) semigr1_enum_append: 
  assumes "\<Lambda> \<in> FinPow(X)" and
  "n \<in> X - \<Lambda>" and "\<forall>k\<in>\<Lambda>. \<langle>k,n\<rangle> \<in> r"
  shows "\<sigma>(\<Lambda> \<union> {n}) = \<sigma>(\<Lambda>)\<hookleftarrow> n"
  using assms  FinPow_def enums_valid_in_semigr1 
    enums.enum_append by simp

text\<open>What is product over a singleton?\<close>

lemma (in semigr1) gen_prod_singleton: 
  assumes A1: "x \<in> X"
  shows  "\<pr>({x},a) = a`(x)"
proof -
  from A1 have "\<sigma>({x}): 1 \<rightarrow> X" and  "\<sigma>({x})`(0) = x"
    using enums_valid_in_semigr1 enums.enum_singleton
    by auto
  then show "\<pr>({x},a) = a`(x)"
    using a_is_fun comp_fun setproddef prod_of_1elem 
      comp_fun_apply by simp
qed

text\<open>A generalization of \<open>prod_append\<close> to the products
  over sets of indices.\<close>

lemma (in semigr1) gen_prod_append: 
  assumes
  A1: "\<Lambda> \<in> FinPow(X)" and A2: "\<Lambda> \<noteq> 0" and
  A3: "n \<in> X -  \<Lambda>" and
  A4: "\<forall>k\<in>\<Lambda>. \<langle>k,n\<rangle> \<in> r"
  shows "\<pr>(\<Lambda> \<union> {n}, a) = (\<pr>(\<Lambda>,a)) \<cdot> a`(n)"
proof -
  have "\<pr>(\<Lambda> \<union> {n}, a) =  \<Prod> (a O \<sigma>(\<Lambda> \<union> {n}))"
    using setproddef by simp
  also from A1 A3 A4 have "\<dots> = \<Prod> (a O (\<sigma>(\<Lambda>)\<hookleftarrow> n))"
    using semigr1_enum_append by simp
  also have "\<dots> = \<Prod> ((a O \<sigma>(\<Lambda>))\<hookleftarrow> a`(n))"
  proof -
    from A1 A3 have 
      "|\<Lambda>| \<in> nat" and "\<sigma>(\<Lambda>) : |\<Lambda>| \<rightarrow> X" and "n \<in> X" 
      using card_fin_is_nat enums_valid_in_semigr1 enums.enum_fun
      by auto
    then show ?thesis using a_is_fun list_compose_append
      by simp
  qed
  also from assms have "\<dots> = (\<Prod> (a O \<sigma>(\<Lambda>)))\<cdot>a`(n)"
    using a_is_fun setprod_type apply_funtype prod_append
    by blast
  also have "\<dots> = (\<pr>(\<Lambda>,a)) \<cdot> a`(n)" 
    using SetFold_def by simp
  finally show "\<pr>(\<Lambda> \<union> {n}, a) = (\<pr>(\<Lambda>,a)) \<cdot> a`(n)"
    by simp
qed

text\<open>Very similar to \<open>gen_prod_append\<close>: a relation
  between a product over a set of indices and the product
  over the set with the maximum removed.\<close>

lemma (in semigr1) gen_product_rem_point:
  assumes A1: "A \<in> FinPow(X)" and
  A2: "n \<in> A" and  A4: "A - {n} \<noteq> 0" and
  A3: "\<forall>k\<in>A. \<langle>k, n\<rangle> \<in> r"
  shows
  "(\<pr>(A - {n},a)) \<cdot> a`(n) = \<pr>(A, a)"
proof -
  let ?\<Lambda> = "A - {n}"
  from A1 A2 have "?\<Lambda> \<in> FinPow(X)" and "n \<in> X -  ?\<Lambda>"
    using fin_rem_point_fin FinPow_def by auto
  with A3 A4 have "\<pr>(?\<Lambda> \<union> {n}, a) = (\<pr>(?\<Lambda>,a)) \<cdot> a`(n)"
    using a_is_fun gen_prod_append by blast
  with A2 show ?thesis using rem_add_eq by simp
qed

subsection\<open>Commutative semigroups\<close>

text\<open>Commutative semigroups are those whose operation is 
  commutative, i.e. $a\cdot b = b\cdot a$. This implies that
  for any permutation $s : n \rightarrow n$ we have
  $\prod_{j=0}^n a_j = \prod_{j=0}^n a_{s (j)}$,
  or, closer to the notation we are using in the \<open>semigr0\<close>
  context, $\prod a = \prod (a \circ s )$. Maybe one day we 
  will be able to prove this, but for now the goal is to prove 
  something simpler: that if the semigroup operation is commutative
  taking the product of a sequence is distributive with respect
  to the operation: 
  $\prod_{j=0}^n (a_j\cdot b_j) = \left(\prod_{j=0}^n a_j)\right) \left(\prod_{j=0}^n b_j)\right)$.
  Many of the rearrangements (namely those that don't use the inverse)
  proven in the \<open>AbelianGroup_ZF\<close> theory hold in fact in semigroups.
  Some of them will be reproven in this section.\<close>

text\<open>A rearrangement with 3 elements.\<close>

lemma (in semigr0) rearr3elems:
  assumes "f {is commutative on} G" and "a\<in>G"  "b\<in>G"  "c\<in>G"
  shows "a\<cdot>b\<cdot>c = a\<cdot>c\<cdot>b"
  using assms semigr_assoc IsCommutative_def by simp

text\<open>A rearrangement of four elements.\<close>

lemma (in semigr0) rearr4elems: 
  assumes A1: "f {is commutative on} G" and 
  A2: "a\<in>G"  "b\<in>G"  "c\<in>G"  "d\<in>G"
  shows "a\<cdot>b\<cdot>(c\<cdot>d) = a\<cdot>c\<cdot>(b\<cdot>d)"
proof -
  from A2 have "a\<cdot>b\<cdot>(c\<cdot>d) = a\<cdot>b\<cdot>c\<cdot>d"
    using semigr_closed semigr_assoc by simp
  also have "a\<cdot>b\<cdot>c\<cdot>d =  a\<cdot>c\<cdot>(b\<cdot>d)"
  proof -
    from A1 A2 have "a\<cdot>b\<cdot>c\<cdot>d = c\<cdot>(a\<cdot>b)\<cdot>d"
      using IsCommutative_def semigr_closed 
      by simp
    also from A2 have "\<dots> =  c\<cdot>a\<cdot>b\<cdot>d"
      using semigr_closed semigr_assoc 
      by simp
    also from A1 A2 have "\<dots> = a\<cdot>c\<cdot>b\<cdot>d"
      using IsCommutative_def semigr_closed 
      by simp
    also from A2 have "\<dots> = a\<cdot>c\<cdot>(b\<cdot>d)" 
      using semigr_closed semigr_assoc
      by simp
    finally show  "a\<cdot>b\<cdot>c\<cdot>d =  a\<cdot>c\<cdot>(b\<cdot>d)" by simp
  qed
  finally show  "a\<cdot>b\<cdot>(c\<cdot>d) = a\<cdot>c\<cdot>(b\<cdot>d)"
    by simp
qed
  
text\<open>We start with a version of \<open>prod_append\<close> that will shorten a bit
  the proof of the main theorem.\<close>

lemma (in semigr0) shorter_seq: assumes A1: "k \<in> nat" and
  A2: "a \<in> succ(succ(k)) \<rightarrow> G" 
  shows "(\<Prod> a) = (\<Prod> Init(a)) \<cdot> a`(succ(k))"
proof -
  let ?x = "Init(a)"
  from assms have
    "a`(succ(k)) \<in> G" and "?x : succ(k) \<rightarrow> G"
    using apply_funtype init_props by auto
  with A1 have "(\<Prod> ?x\<hookleftarrow>a`(succ(k))) = (\<Prod> ?x) \<cdot> a`(succ(k))"
    using prod_append by simp
  with assms show ?thesis using init_props
    by simp
qed

text\<open>A lemma useful in the induction step of the main theorem.\<close>

lemma (in semigr0) prod_distr_ind_step:
  assumes A1: "k \<in> nat" and
  A2: "a : succ(succ(k)) \<rightarrow> G" and
  A3: "b : succ(succ(k)) \<rightarrow> G" and
  A4: "c : succ(succ(k)) \<rightarrow> G" and
  A5: "\<forall>j\<in>succ(succ(k)). c`(j) = a`(j) \<cdot> b`(j)"
  shows
  "Init(a) : succ(k) \<rightarrow> G"
  "Init(b) : succ(k) \<rightarrow> G"
  "Init(c) : succ(k) \<rightarrow> G"
  "\<forall>j\<in>succ(k). Init(c)`(j) = Init(a)`(j) \<cdot> Init(b)`(j)"
proof -
  from A1 A2 A3 A4 show 
    "Init(a) : succ(k) \<rightarrow> G"
    "Init(b) : succ(k) \<rightarrow> G"
    "Init(c) : succ(k) \<rightarrow> G"
    using init_props by auto
  from A1 have T: "succ(k) \<in> nat" by simp
  from T A2 have "\<forall>j\<in>succ(k). Init(a)`(j) = a`(j)"
    by (rule init_props)
  moreover from T A3 have "\<forall>j\<in>succ(k). Init(b)`(j) = b`(j)"
     by (rule init_props)
   moreover from T A4 have "\<forall>j\<in>succ(k). Init(c)`(j) = c`(j)"
     by (rule init_props)
   moreover from A5 have "\<forall>j\<in>succ(k). c`(j) = a`(j) \<cdot> b`(j)"
     by simp
   ultimately show "\<forall>j\<in>succ(k). Init(c)`(j) = Init(a)`(j) \<cdot> Init(b)`(j)"
     by simp
qed

text\<open>For commutative operations taking the product of a sequence 
  is distributive with respect to the operation.
  This version will probably not be used in applications,
  it is formulated in a way that is easier to prove by induction.
  For a more convenient formulation see \<open>prod_comm_distrib\<close>.
  The proof by induction on the length of the sequence.\<close>

theorem (in semigr0) prod_comm_distr: 
  assumes A1: "f {is commutative on} G" and A2: "n\<in>nat" 
  shows "\<forall> a b c. 
  (a : succ(n)\<rightarrow>G \<and> b : succ(n)\<rightarrow>G \<and> c : succ(n)\<rightarrow>G \<and> 
  (\<forall>j\<in>succ(n). c`(j) = a`(j) \<cdot> b`(j))) \<longrightarrow>
  (\<Prod> c) = (\<Prod> a) \<cdot> (\<Prod> b)"
proof -
  note A2
  moreover have "\<forall> a b c. 
    (a : succ(0)\<rightarrow>G \<and> b : succ(0)\<rightarrow>G \<and> c : succ(0)\<rightarrow>G \<and> 
    (\<forall>j\<in>succ(0). c`(j) = a`(j) \<cdot> b`(j))) \<longrightarrow>
    (\<Prod> c) = (\<Prod> a) \<cdot> (\<Prod> b)"
  proof -
    { fix a b c 
      assume "a : succ(0)\<rightarrow>G \<and> b : succ(0)\<rightarrow>G \<and> c : succ(0)\<rightarrow>G \<and> 
	(\<forall>j\<in>succ(0). c`(j) = a`(j) \<cdot> b`(j))"
      then have
	I: "a : 1\<rightarrow>G"  "b : 1\<rightarrow>G"  "c : 1\<rightarrow>G" and
	II: "c`(0) = a`(0) \<cdot> b`(0)" by auto
      from I have
	"(\<Prod> a) = a`(0)" and "(\<Prod> b) = b`(0)" and "(\<Prod> c) = c`(0)"
	using prod_of_1elem by auto
      with II have "(\<Prod> c) = (\<Prod> a) \<cdot> (\<Prod> b)" by simp
    } then show ?thesis using Fold1_def by simp
  qed
  moreover have "\<forall>k \<in> nat. 
    (\<forall> a b c. 
    (a : succ(k)\<rightarrow>G \<and> b : succ(k)\<rightarrow>G \<and> c : succ(k)\<rightarrow>G \<and> 
    (\<forall>j\<in>succ(k). c`(j) = a`(j) \<cdot> b`(j))) \<longrightarrow>
    (\<Prod> c) = (\<Prod> a) \<cdot> (\<Prod> b)) \<longrightarrow>
    (\<forall> a b c. 
    (a : succ(succ(k))\<rightarrow>G \<and> b : succ(succ(k))\<rightarrow>G \<and> c : succ(succ(k))\<rightarrow>G \<and> 
    (\<forall>j\<in>succ(succ(k)). c`(j) = a`(j) \<cdot> b`(j))) \<longrightarrow>
    (\<Prod> c) = (\<Prod> a) \<cdot> (\<Prod> b))"
  proof
    fix k assume "k \<in> nat"
    show "(\<forall>a b c.
      a \<in> succ(k) \<rightarrow> G \<and>
      b \<in> succ(k) \<rightarrow> G \<and> c \<in> succ(k) \<rightarrow> G \<and> 
      (\<forall>j\<in>succ(k). c`(j) = a`(j) \<cdot> b`(j)) \<longrightarrow>
      (\<Prod> c) = (\<Prod> a) \<cdot> (\<Prod> b)) \<longrightarrow>
      (\<forall>a b c.
      a \<in> succ(succ(k)) \<rightarrow> G \<and>
      b \<in> succ(succ(k)) \<rightarrow> G \<and>
      c \<in> succ(succ(k)) \<rightarrow> G \<and> 
      (\<forall>j\<in>succ(succ(k)). c`(j) = a`(j) \<cdot> b`(j)) \<longrightarrow>
      (\<Prod> c) = (\<Prod> a) \<cdot> (\<Prod> b))"
    proof
      assume A3: "\<forall>a b c.
	a \<in> succ(k) \<rightarrow> G \<and>
	b \<in> succ(k) \<rightarrow> G \<and> c \<in> succ(k) \<rightarrow> G \<and> 
	(\<forall>j\<in>succ(k). c`(j) = a`(j) \<cdot> b`(j)) \<longrightarrow>
	(\<Prod> c) = (\<Prod> a) \<cdot> (\<Prod> b)"
      show "\<forall>a b c.
	a \<in> succ(succ(k)) \<rightarrow> G \<and>
	b \<in> succ(succ(k)) \<rightarrow> G \<and>
	c \<in> succ(succ(k)) \<rightarrow> G \<and> 
	(\<forall>j\<in>succ(succ(k)). c`(j) = a`(j) \<cdot> b`(j)) \<longrightarrow>
	(\<Prod> c) = (\<Prod> a) \<cdot> (\<Prod> b)"
      proof -
	{ fix a b c 
	  assume 
	    "a \<in> succ(succ(k)) \<rightarrow> G \<and>
	    b \<in> succ(succ(k)) \<rightarrow> G \<and>
	    c \<in> succ(succ(k)) \<rightarrow> G \<and> 
	    (\<forall>j\<in>succ(succ(k)). c`(j) = a`(j) \<cdot> b`(j))"
	  with \<open>k \<in> nat\<close> have I:
	    "a : succ(succ(k)) \<rightarrow> G"
	    "b : succ(succ(k)) \<rightarrow> G"
	    "c : succ(succ(k)) \<rightarrow> G"
	    and II: "\<forall>j\<in>succ(succ(k)). c`(j) = a`(j) \<cdot> b`(j)"
	    by auto   
	  let ?x = "Init(a)"
          let ?y = "Init(b)"
          let ?z = "Init(c)"
	  from \<open>k \<in> nat\<close> I have III:
	    "(\<Prod> a) = (\<Prod> ?x) \<cdot> a`(succ(k))"
	    "(\<Prod> b) = (\<Prod> ?y) \<cdot> b`(succ(k))" and
	    IV: "(\<Prod> c) = (\<Prod> ?z) \<cdot> c`(succ(k))"
	    using  shorter_seq by auto
	  moreover
	  from  \<open>k \<in> nat\<close> I II have
	    "?x : succ(k) \<rightarrow> G"
	    "?y : succ(k) \<rightarrow> G"
	    "?z : succ(k) \<rightarrow> G" and
	    "\<forall>j\<in>succ(k). ?z`(j) = ?x`(j) \<cdot> ?y`(j)"
	    using prod_distr_ind_step by auto
	  with A3 II IV have
	    "(\<Prod> c) = (\<Prod> ?x)\<cdot>(\<Prod> ?y)\<cdot>(a`(succ(k)) \<cdot> b`(succ(k)))"
	    by simp
	  moreover from A1 \<open>k \<in> nat\<close> I III have
	    "(\<Prod> ?x)\<cdot>(\<Prod> ?y)\<cdot>(a`(succ(k)) \<cdot> b`(succ(k)))=
	    (\<Prod> a) \<cdot> (\<Prod> b)" 
	    using init_props prod_type apply_funtype 
	      rearr4elems by simp
	  ultimately have "(\<Prod> c) = (\<Prod> a) \<cdot> (\<Prod> b)"
	    by simp
	} thus ?thesis by auto
      qed
    qed
  qed
  ultimately show ?thesis by (rule ind_on_nat)
qed

text\<open>A reformulation of \<open>prod_comm_distr\<close> that is more
  convenient in applications.\<close>

theorem (in semigr0) prod_comm_distrib:
  assumes  "f {is commutative on} G" and "n\<in>nat" and
  "a : succ(n)\<rightarrow>G"  "b : succ(n)\<rightarrow>G"  "c : succ(n)\<rightarrow>G" and
  "\<forall>j\<in>succ(n). c`(j) = a`(j) \<cdot> b`(j)"
  shows "(\<Prod> c) = (\<Prod> a) \<cdot> (\<Prod> b)"
  using assms prod_comm_distr by simp

text\<open>A product of two products over disjoint sets of indices is the 
  product over the union.\<close>

lemma (in semigr1) prod_bisect:
  assumes  A1: "f {is commutative on} G"  and A2: "\<Lambda> \<in> FinPow(X)"
  shows 
  "\<forall>P \<in>  Bisections(\<Lambda>). \<pr>(\<Lambda>,a) = (\<pr>(fst(P),a))\<cdot>(\<pr>(snd(P),a))"
proof -
  have "IsLinOrder(X,r)" using linord by simp
  moreover have 
    "\<forall>P \<in>  Bisections(0). \<pr>(0,a) = (\<pr>(fst(P),a))\<cdot>(\<pr>(snd(P),a))"
    using bisec_empty by simp
  moreover have "\<forall> A \<in> FinPow(X). 
    ( \<forall> n \<in> X - A. 
    (\<forall>P \<in>  Bisections(A). \<pr>(A,a) = (\<pr>(fst(P),a))\<cdot>(\<pr>(snd(P),a))) 
    \<and> (\<forall>k\<in>A. \<langle>k,n\<rangle> \<in> r ) \<longrightarrow> 
    (\<forall>Q \<in>  Bisections(A \<union> {n}). 
    \<pr>(A \<union> {n},a) = (\<pr>(fst(Q),a))\<cdot>(\<pr>(snd(Q),a))))"
  proof -
    { fix A assume "A \<in> FinPow(X)"
      fix n assume "n \<in> X - A"
      have "( \<forall>P \<in> Bisections(A). 
	\<pr>(A,a) = (\<pr>(fst(P),a))\<cdot>(\<pr>(snd(P),a))) 
	\<and> (\<forall>k\<in>A. \<langle>k,n\<rangle> \<in> r )  \<longrightarrow> 
	(\<forall>Q \<in>  Bisections(A \<union> {n}). 
	\<pr>(A \<union> {n},a) = (\<pr>(fst(Q),a))\<cdot>(\<pr>(snd(Q),a)))"
      proof -
	{ assume I:
	  "\<forall>P \<in> Bisections(A). \<pr>(A,a) = (\<pr>(fst(P),a))\<cdot>(\<pr>(snd(P),a))"
	  and II: "\<forall>k\<in>A. \<langle>k,n\<rangle> \<in> r"
	  have "\<forall>Q \<in>  Bisections(A \<union> {n}). 
	    \<pr>(A \<union> {n},a) = (\<pr>(fst(Q),a))\<cdot>(\<pr>(snd(Q),a))"
	  proof -
	    { fix Q assume "Q \<in>  Bisections(A \<union> {n})"
	      let ?Q\<^sub>0 = "fst(Q)"
	      let ?Q\<^sub>1 = "snd(Q)"	      
	      from \<open>A \<in> FinPow(X)\<close> \<open>n \<in> X - A\<close> have "A \<union> {n} \<in> FinPow(X)"
		using singleton_in_finpow union_finpow by auto
	      with \<open>Q \<in>  Bisections(A \<union> {n})\<close> have
		"?Q\<^sub>0 \<in> FinPow(X)" "?Q\<^sub>0 \<noteq> 0" and "?Q\<^sub>1 \<in> FinPow(X)" "?Q\<^sub>1 \<noteq> 0"
		using bisect_fin bisec_is_pair Bisections_def by auto
	      then have "\<pr>(?Q\<^sub>0,a) \<in> G" and "\<pr>(?Q\<^sub>1,a) \<in> G"
		using a_is_fun setprod_type by auto
	      from \<open>Q \<in> Bisections(A \<union> {n})\<close> \<open>A \<in> FinPow(X)\<close> \<open>n \<in> X-A\<close>
	      have "refl(X,r)"  "?Q\<^sub>0 \<subseteq> A \<union> {n}"  "?Q\<^sub>1 \<subseteq> A \<union> {n}" 
		"A \<subseteq> X" and "n \<in> X"
		using linord IsLinOrder_def total_is_refl Bisections_def
		FinPow_def by auto
	      from \<open>refl(X,r)\<close>  \<open>?Q\<^sub>0 \<subseteq> A \<union> {n}\<close>  \<open>A \<subseteq> X\<close> \<open>n \<in> X\<close> II 
	      have III: "\<forall>k \<in> ?Q\<^sub>0. \<langle>k, n\<rangle> \<in> r" by (rule refl_add_point)
	      from \<open>refl(X,r)\<close>  \<open>?Q\<^sub>1 \<subseteq> A \<union> {n}\<close>  \<open>A \<subseteq> X\<close> \<open>n \<in> X\<close> II 
	      have  IV: "\<forall>k \<in> ?Q\<^sub>1. \<langle>k, n\<rangle> \<in> r" by (rule refl_add_point)
	      from \<open>n \<in> X - A\<close> \<open>Q \<in>  Bisections(A \<union> {n})\<close> have
		"?Q\<^sub>0 = {n} \<or> ?Q\<^sub>1 = {n} \<or> \<langle>?Q\<^sub>0 - {n},?Q\<^sub>1-{n}\<rangle> \<in>  Bisections(A)"
		using bisec_is_pair bisec_add_point by simp
	      moreover
	      { assume "?Q\<^sub>1 = {n}"
		from \<open>n \<in> X - A\<close> have "n \<notin> A" by auto
		moreover 
		from  \<open>Q \<in>  Bisections(A \<union> {n})\<close> 
		have "\<langle>?Q\<^sub>0,?Q\<^sub>1 \<rangle> \<in>  Bisections(A \<union> {n})"
		  using bisec_is_pair by simp
		with \<open>?Q\<^sub>1 = {n}\<close> have "\<langle>?Q\<^sub>0, {n}\<rangle> \<in>  Bisections(A \<union> {n})"
		  by simp
		ultimately have "?Q\<^sub>0 = A" and "A \<noteq> 0" 
		  using set_point_bisec by auto
		with \<open>A \<in> FinPow(X)\<close> \<open>n \<in> X - A\<close> II \<open>?Q\<^sub>1 = {n}\<close> 
		have "\<pr>(A \<union> {n},a) = (\<pr>(?Q\<^sub>0,a))\<cdot>\<pr>(?Q\<^sub>1,a)"
		  using a_is_fun gen_prod_append gen_prod_singleton 
		  by simp }
	      moreover
	      { assume "?Q\<^sub>0 = {n}"
		from \<open>n \<in> X - A\<close> have "n \<in> X" by auto
		then have "{n} \<in> FinPow(X)" and "{n} \<noteq> 0"
		  using singleton_in_finpow by auto
		from \<open>n \<in> X - A\<close> have "n \<notin> A" by auto
		moreover 
		from  \<open>Q \<in> Bisections(A \<union> {n})\<close>
		have "\<langle>?Q\<^sub>0, ?Q\<^sub>1\<rangle> \<in>  Bisections(A \<union> {n})"
		  using bisec_is_pair by simp
		with \<open>?Q\<^sub>0 = {n}\<close> have "\<langle>{n}, ?Q\<^sub>1\<rangle> \<in>  Bisections(A \<union> {n})"
		  by simp
		ultimately have "?Q\<^sub>1 = A" and "A \<noteq> 0" using point_set_bisec
		  by auto
		with A1 \<open>A \<in> FinPow(X)\<close> \<open>n \<in> X - A\<close> II
		  \<open>{n} \<in> FinPow(X)\<close>  \<open>{n} \<noteq> 0\<close> \<open>?Q\<^sub>0 = {n}\<close>
		have "\<pr>(A \<union> {n},a) = (\<pr>(?Q\<^sub>0,a))\<cdot>(\<pr>(?Q\<^sub>1,a))"
		  using a_is_fun gen_prod_append gen_prod_singleton 
		    setprod_type IsCommutative_def by auto }
	      moreover
	      { assume A4: "\<langle>?Q\<^sub>0 - {n},?Q\<^sub>1 - {n}\<rangle> \<in>  Bisections(A)"
		with \<open>A \<in> FinPow(X)\<close> have 
		  "?Q\<^sub>0 - {n} \<in> FinPow(X)" "?Q\<^sub>0 - {n} \<noteq> 0" and 
		  "?Q\<^sub>1 - {n} \<in> FinPow(X)" "?Q\<^sub>1 - {n} \<noteq> 0"
		  using FinPow_def Bisections_def by auto
		with \<open>n \<in> X - A\<close> have 
		  "\<pr>(?Q\<^sub>0 - {n},a) \<in> G"  "\<pr>(?Q\<^sub>1 - {n},a) \<in> G"  and
		  T: "a`(n) \<in> G"
		  using a_is_fun setprod_type apply_funtype by auto
		from \<open>Q \<in> Bisections(A \<union> {n})\<close> A4 have
		  "(\<langle>?Q\<^sub>0, ?Q\<^sub>1 - {n}\<rangle> \<in> Bisections(A) \<and> n \<in> ?Q\<^sub>1) \<or> 
		  (\<langle>?Q\<^sub>0 - {n}, ?Q\<^sub>1\<rangle> \<in> Bisections(A) \<and> n \<in> ?Q\<^sub>0) "
		  using bisec_is_pair bisec_add_point_case3 by auto
		moreover
		{ assume "\<langle>?Q\<^sub>0, ?Q\<^sub>1 - {n}\<rangle> \<in> Bisections(A)" and "n \<in> ?Q\<^sub>1"
		  then have "A \<noteq> 0" using bisec_props by simp
		  with A2 \<open>A \<in> FinPow(X)\<close> \<open>n \<in> X - A\<close> I II T IV
		    \<open>\<langle>?Q\<^sub>0, ?Q\<^sub>1 - {n}\<rangle> \<in> Bisections(A)\<close> \<open>\<pr>(?Q\<^sub>0,a) \<in> G\<close> 
		    \<open>\<pr>(?Q\<^sub>1 - {n},a) \<in> G\<close> \<open>?Q\<^sub>1 \<in> FinPow(X)\<close> 
		    \<open>n \<in> ?Q\<^sub>1\<close> \<open>?Q\<^sub>1 - {n} \<noteq> 0\<close>
		  have "\<pr>(A \<union> {n},a) = (\<pr>(?Q\<^sub>0,a))\<cdot>(\<pr>(?Q\<^sub>1,a))"
		    using gen_prod_append semigr_assoc gen_product_rem_point 
		    by simp }
		moreover
		{ assume "\<langle>?Q\<^sub>0 - {n}, ?Q\<^sub>1\<rangle> \<in> Bisections(A)" and "n \<in> ?Q\<^sub>0"
		  then have "A \<noteq> 0" using bisec_props by simp
		  with A1 A2 \<open>A \<in> FinPow(X)\<close> \<open>n \<in> X - A\<close> I II III T 
		    \<open>\<langle>?Q\<^sub>0 - {n}, ?Q\<^sub>1\<rangle>\<in>Bisections(A)\<close> \<open>\<pr>(?Q\<^sub>0 - {n},a)\<in>G\<close> 
		    \<open>\<pr>(?Q\<^sub>1,a) \<in> G\<close> \<open>?Q\<^sub>0 \<in> FinPow(X)\<close> \<open>n \<in> ?Q\<^sub>0\<close> \<open>?Q\<^sub>0-{n}\<noteq>0\<close>
		  have "\<pr>(A \<union> {n},a) = (\<pr>(?Q\<^sub>0,a))\<cdot>(\<pr>(?Q\<^sub>1,a))"
		    using gen_prod_append rearr3elems gen_product_rem_point 
		      by simp }
		ultimately have
		  "\<pr>(A \<union> {n},a) = (\<pr>(?Q\<^sub>0,a))\<cdot>(\<pr>(?Q\<^sub>1,a))"
		  by auto }
	      ultimately have "\<pr>(A \<union> {n},a) = (\<pr>(?Q\<^sub>0,a))\<cdot>(\<pr>(?Q\<^sub>1,a))"
		by auto	
	    } thus ?thesis by simp
	  qed
	} thus ?thesis by simp
      qed
    } thus ?thesis by simp
  qed  
  moreover note A2
  ultimately show ?thesis by (rule fin_ind_add_max)
qed

text\<open>A better looking reformulation of \<open>prod_bisect\<close>.
\<close>

theorem (in semigr1) prod_disjoint: assumes
  A1: "f {is commutative on} G"  and 
  A2: "A \<in> FinPow(X)" "A \<noteq> 0" and
  A3: "B \<in> FinPow(X)" "B \<noteq> 0" and
  A4: "A \<inter> B = 0"
  shows "\<pr>(A\<union>B,a) = (\<pr>(A,a))\<cdot>(\<pr>(B,a))"
proof -
  from A2 A3 A4 have "\<langle>A,B\<rangle> \<in> Bisections(A\<union>B)"
    using is_bisec by simp
  with A1 A2 A3 show ?thesis
    using a_is_fun union_finpow prod_bisect by simp
qed

text\<open>A generalization of \<open>prod_disjoint\<close>.\<close>

lemma (in semigr1) prod_list_of_lists: assumes
  A1: "f {is commutative on} G"  and A2: "n \<in> nat"
  shows "\<forall>M \<in> succ(n) \<rightarrow> FinPow(X). 
  M {is partition} \<longrightarrow> 
  (\<Prod> {\<langle>i,\<pr>(M`(i),a)\<rangle>. i \<in> succ(n)}) = 
  (\<pr>(\<Union>i \<in> succ(n). M`(i),a))"
proof -
  note A2
  moreover have "\<forall>M \<in> succ(0) \<rightarrow> FinPow(X). 
    M {is partition} \<longrightarrow> 
    (\<Prod> {\<langle>i,\<pr>(M`(i),a)\<rangle>. i \<in> succ(0)}) = (\<pr>(\<Union>i \<in> succ(0). M`(i),a))"
    using a_is_fun func1_1_L1 Partition_def apply_funtype setprod_type
      list_len1_singleton prod_of_1elem 
    by simp
  moreover have "\<forall>k \<in> nat. 
    (\<forall>M \<in> succ(k) \<rightarrow> FinPow(X). 
    M {is partition} \<longrightarrow> 
    (\<Prod> {\<langle>i,\<pr>(M`(i),a)\<rangle>. i \<in> succ(k)}) = 
    (\<pr>(\<Union>i \<in> succ(k). M`(i),a))) \<longrightarrow>
    (\<forall>M \<in> succ(succ(k)) \<rightarrow> FinPow(X). 
    M {is partition} \<longrightarrow> 
    (\<Prod> {\<langle>i,\<pr>(M`(i),a)\<rangle>. i \<in> succ(succ(k))}) = 
    (\<pr>(\<Union>i \<in> succ(succ(k)). M`(i),a)))"
  proof -
    { fix k assume "k \<in> nat"
      assume A3: "\<forall>M \<in> succ(k) \<rightarrow> FinPow(X). 
	M {is partition} \<longrightarrow> 
	(\<Prod> {\<langle>i,\<pr>(M`(i),a)\<rangle>. i \<in> succ(k)}) = 
	(\<pr>(\<Union>i \<in> succ(k). M`(i),a))"
      have "(\<forall>N \<in> succ(succ(k)) \<rightarrow> FinPow(X). 
	N {is partition} \<longrightarrow> 
	(\<Prod> {\<langle>i,\<pr>(N`(i),a)\<rangle>. i \<in> succ(succ(k))}) = 
	(\<pr>(\<Union>i \<in> succ(succ(k)). N`(i),a)))"
      proof -
	{ fix N assume A4: "N : succ(succ(k)) \<rightarrow> FinPow(X)"
	  assume A5: "N {is partition}"
	  with A4 have I: "\<forall>i \<in> succ(succ(k)). N`(i) \<noteq> 0"
	    using func1_1_L1 Partition_def by simp
	  let ?b = "{\<langle>i,\<pr>(N`(i),a)\<rangle>. i \<in> succ(succ(k))}"
	  let ?c = "{\<langle>i,\<pr>(N`(i),a)\<rangle>. i \<in> succ(k)}"
	  have II: "\<forall>i \<in> succ(succ(k)). \<pr>(N`(i),a) \<in> G"
	  proof 
	    fix i assume "i \<in> succ(succ(k))"
	    with A4 I have "N`(i) \<in> FinPow(X)" and "N`(i) \<noteq> 0"
	      using apply_funtype by auto
	    then show "\<pr>(N`(i),a) \<in> G" using setprod_type
	      by simp
	  qed
	  hence "\<forall>i \<in> succ(k).  \<pr>(N`(i),a) \<in> G" by auto
	  then have "?c : succ(k) \<rightarrow> G" by (rule ZF_fun_from_total)
	  have "?b = {\<langle>i,\<pr>(N`(i),a)\<rangle>. i \<in> succ(succ(k))}"
	    by simp
	  with II have "?b = Append(?c,\<pr>(N`(succ(k)),a))"
	    by (rule set_list_append)
	  with  II  \<open>k \<in> nat\<close> \<open>?c : succ(k) \<rightarrow> G\<close> 
	  have "(\<Prod> ?b) = (\<Prod> ?c)\<cdot>(\<pr>(N`(succ(k)),a))"
	    using prod_append by simp
	  also have 
	    "\<dots> =  (\<pr>(\<Union>i \<in> succ(k). N`(i),a))\<cdot>(\<pr>(N`(succ(k)),a))"
	  proof -
	    let ?M = "restrict(N,succ(k))"
	    have "succ(k) \<subseteq> succ(succ(k))" by auto
	    with \<open>N : succ(succ(k)) \<rightarrow> FinPow(X)\<close>
	    have "?M : succ(k) \<rightarrow> FinPow(X)" and
	      III: "\<forall>i \<in> succ(k). ?M`(i) = N`(i)"
	      using restrict_type2 restrict apply_funtype 
	      by auto
	    with A5 \<open>?M : succ(k) \<rightarrow> FinPow(X)\<close>have "?M {is partition}"
	      using func1_1_L1 Partition_def by simp
	    with A3 \<open>?M : succ(k) \<rightarrow> FinPow(X)\<close> have
	      "(\<Prod> {\<langle>i,\<pr>(?M`(i),a)\<rangle>. i \<in> succ(k)}) = 
	      (\<pr>(\<Union>i \<in> succ(k). ?M`(i),a))"
	      by blast
	    with III show ?thesis by simp
	  qed
	  also have "\<dots> = (\<pr>(\<Union>i \<in> succ(succ(k)). N`(i),a))"
	  proof -
	    let ?A = "\<Union>i \<in> succ(k). N`(i)"
	    let ?B = "N`(succ(k))"
	    from A4 \<open>k \<in> nat\<close> have "succ(k) \<in> nat" and
	      "\<forall>i \<in> succ(k). N`(i) \<in> FinPow(X)"
	      using apply_funtype by auto
	    then have "?A \<in> FinPow(X)" by (rule union_fin_list_fin)
	    moreover from I have "?A \<noteq> 0" by auto
	    moreover from A4 I have 
	      "N`(succ(k)) \<in> FinPow(X)" and "N`(succ(k)) \<noteq> 0"
	      using apply_funtype by auto
	    moreover from \<open>succ(k) \<in> nat\<close> A4 A5 have "?A \<inter> ?B = 0"
	      by (rule list_partition)
	    moreover note A1
	    ultimately have "\<pr>(?A\<union>?B,a) = (\<pr>(?A,a))\<cdot>(\<pr>(?B,a))"
	      using prod_disjoint by simp
	    moreover have "?A \<union> ?B = (\<Union>i \<in> succ(succ(k)). N`(i))"
	      by auto
	    ultimately show ?thesis by simp
	  qed
	  finally have "(\<Prod> {\<langle>i,\<pr>(N`(i),a)\<rangle>. i \<in> succ(succ(k))}) = 
	    (\<pr>(\<Union>i \<in> succ(succ(k)). N`(i),a))"
	    by simp
	  } thus ?thesis by auto
	qed
	} thus ?thesis by simp
  qed
  ultimately show ?thesis by (rule ind_on_nat)
qed

text\<open>A more convenient reformulation of \<open>prod_list_of_lists\<close>.
\<close>

theorem (in semigr1) prod_list_of_sets: 
  assumes A1: "f {is commutative on} G"  and 
  A2: "n \<in> nat"  "n \<noteq> 0" and
  A3: "M : n \<rightarrow> FinPow(X)"   "M {is partition}"
  shows
  "(\<Prod> {\<langle>i,\<pr>(M`(i),a)\<rangle>. i \<in> n}) = (\<pr>(\<Union>i \<in> n. M`(i),a))"
proof -
  from A2 obtain k where "k \<in> nat" and "n = succ(k)"
    using Nat_ZF_1_L3 by auto
  with A1 A3 show ?thesis using prod_list_of_lists
    by simp
qed

text\<open>The definition of the product 
  \<open>\<pr>(A,a) \<equiv> SetFold(f,a,A,r)\<close> of a some (finite) set of 
  semigroup elements requires that $r$ is a linear order on the set 
  of indices $A$. This is necessary so that we know in which order
  we are multiplying the elements. The product over $A$ is defined 
  so that we have $\prod_A a = \prod a \circ \sigma(A)$ where
  $\sigma : |A| \rightarrow A$ is the enumeration of $A$ (the only
  order isomorphism between the number of elements in $A$ and $A$), see
  lemma \<open>setproddef\<close>.
  However, if the operation is commutative, the order is irrelevant. 
  The next theorem formalizes that fact stating that we can replace
  the enumeration $\sigma (A)$ by any bijection between $|A|$ and $A$.
  In a way this is a generalization of \<open>setproddef\<close>. 
  The proof is based on application of \<open>prod_list_of_sets\<close>
  to the finite collection of singletons that comprise $A$.\<close>

theorem (in semigr1) prod_order_irr: 
  assumes A1: "f {is commutative on} G" and
  A2: "A \<in> FinPow(X)" "A \<noteq> 0" and
  A3: "b \<in> bij(|A|,A)"
  shows "(\<Prod> (a O b)) = \<pr>(A,a)"
proof -
  let ?n = "|A|"
  let ?M = "{\<langle>k, {b`(k)}\<rangle>. k \<in> ?n}"
  have "(\<Prod> (a O b)) = (\<Prod> {\<langle>i,\<pr>(?M`(i),a)\<rangle>. i \<in> ?n})"
  proof -
    have "\<forall>i \<in> ?n. \<pr>(?M`(i),a) = (a O b)`(i)"
    proof
      fix i assume "i \<in> ?n"
      with A2 A3 \<open>i \<in> ?n\<close> have "b`(i) \<in> X" 
	using bij_def inj_def apply_funtype FinPow_def
	by auto
      then have "\<pr>({b`(i)},a) = a`(b`(i))" 
	using gen_prod_singleton by simp
      with A3 \<open>i \<in> ?n\<close> have "\<pr>({b`(i)},a) = (a O b)`(i)"
	using bij_def inj_def comp_fun_apply by auto
      with \<open>i \<in> ?n\<close> A3 show "\<pr>(?M`(i),a) = (a O b)`(i)"
	using bij_def inj_partition by auto
    qed
    hence "{\<langle>i,\<pr>(?M`(i),a)\<rangle>. i \<in> ?n} = {\<langle>i,(a O b)`(i)\<rangle>. i \<in> ?n}"
      by simp
    moreover have "{\<langle>i,(a O b)`(i)\<rangle>. i \<in> ?n} = a O b"
    proof -
      from A3 have "b : ?n \<rightarrow> A" using bij_def inj_def by simp
      moreover from A2 have "A \<subseteq> X" using FinPow_def by simp
      ultimately have "b : ?n \<rightarrow> X" by (rule func1_1_L1B)
      then have "a O b: ?n \<rightarrow> G" using a_is_fun comp_fun
	by simp
      then show "{\<langle>i,(a O b)`(i)\<rangle>. i \<in> ?n} = a O b"
	using fun_is_set_of_pairs by simp
    qed
    ultimately show ?thesis by simp
  qed
  also have "\<dots> = (\<pr>(\<Union>i \<in> ?n. ?M`(i),a))"
  proof -
    note A1
    moreover from A2 have "?n \<in> nat" and "?n \<noteq> 0"
      using card_fin_is_nat card_non_empty_non_zero by auto
    moreover have "?M : ?n \<rightarrow> FinPow(X)" and "?M {is partition}"
    proof -
      from A2 A3 have "\<forall>k \<in> ?n. {b`(k)} \<in>  FinPow(X)"
	using bij_def inj_def apply_funtype FinPow_def
	  singleton_in_finpow by auto
      then show "?M : ?n \<rightarrow> FinPow(X)" using ZF_fun_from_total
	by simp
      from A3 show "?M {is partition}" using bij_def inj_partition
	by auto
    qed
    ultimately show
      "(\<Prod> {\<langle>i,\<pr>(?M`(i),a)\<rangle>. i \<in> ?n}) = (\<pr>(\<Union>i \<in> ?n. ?M`(i),a))"
      by (rule prod_list_of_sets)
  qed
  also from A3 have "(\<pr>(\<Union>i \<in> ?n. ?M`(i),a)) = \<pr>(A,a)"
    using bij_def inj_partition surj_singleton_image
    by auto
  finally show ?thesis by simp
qed

text\<open>Another way of expressing the fact that the product dos not depend
  on the order.\<close>

corollary (in semigr1) prod_bij_same: 
  assumes "f {is commutative on} G" and
  "A \<in> FinPow(X)" "A \<noteq> 0" and
  "b \<in> bij(|A|,A)" "c \<in> bij(|A|,A)"
  shows "(\<Prod> (a O b)) = (\<Prod> (a O c))"
  using assms prod_order_irr by simp
    
end
