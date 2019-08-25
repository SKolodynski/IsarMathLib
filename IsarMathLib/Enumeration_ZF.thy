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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open>Enumerations\<close>

theory Enumeration_ZF imports NatOrder_ZF FiniteSeq_ZF FinOrd_ZF

begin

text\<open>Suppose $r$ is a linear order on a set $A$ that has $n$ elements, 
  where $n \in\mathbb{N}$ . In the \<open>FinOrd_ZF\<close>
  theory we prove a theorem stating that there is a unique
  order isomorphism between $n = \{0,1,..,n-1\}$ (with natural order) and
  $A$. Another way of stating that is that there is
  a unique way of counting the elements of $A$ in the order increasing
  according to relation $r$. Yet another way of stating the same thing is 
  that there is a unique sorted list of elements of $A$. We will call this
  list the \<open>Enumeration\<close> of $A$.\<close>

subsection\<open>Enumerations: definition and notation\<close>

text\<open>In this section we introduce the notion of enumeration
  and define a proof context (a ''locale'' in Isabelle terms)
  that sets up the notation for writing about enumarations.\<close>

text\<open>We define enumeration as the only order isomorphism beween 
  a set $A$ and the number of its elements. We are using 
  the formula $\bigcup \{x\} = x$ to extract the only element
  from a singleton. \<open>Le\<close> is the (natural) order on natural 
  numbers, defined is \<open>Nat_ZF\<close> theory in the standard 
  Isabelle library.\<close>

definition
  "Enumeration(A,r) \<equiv> \<Union> ord_iso(|A|,Le,A,r)"

text\<open>To set up the notation we define a locale \<open>enums\<close>. In this
  locale we will assume that $r$ is a linear order on some set $X$. 
  In most applications this set will be just the set of natural numbers.
  Standard Isabelle uses $\leq $ to denote the "less or equal" relation
  on natural numbers. We will use the \<open>\<lsq>\<close> symbol to denote
  the relation $r$. Those two symbols usually look the same in the presentation,
  but they are different in the source.To shorten the notation the enumeration
  \<open>Enumeration(A,r)\<close> will be denoted as $\sigma (A)$.
  Similarly as in the \<open>Semigroup\<close> theory we will write
  $a\hookleftarrow x$ for the result of appending an element $x$ to
  the finite sequence (list) $a$. Finally,
  $a\sqcup b$ will denote the concatenation of the lists $a$ and $b$.\<close>

locale enums =

  fixes X r
  assumes linord: "IsLinOrder(X,r)"

  fixes ler (infix "\<lsq>" 70)
  defines ler_def[simp]: "x \<lsq> y \<equiv> \<langle>x,y\<rangle> \<in> r"

  fixes \<sigma>
  defines \<sigma>_def [simp]: "\<sigma>(A) \<equiv> Enumeration(A,r)"

  fixes append (infix "\<hookleftarrow>" 72)
  defines append_def[simp]: "a \<hookleftarrow> x \<equiv> Append(a,x)"

  fixes concat (infixl "\<squnion>" 69)
  defines concat_def[simp]: "a \<squnion> b \<equiv> Concat(a,b)"

subsection\<open>Properties of enumerations\<close>

text\<open>In this section we prove basic facts about enumerations.\<close>

text\<open>A special case of the existence and uniqueess 
  of the order isomorphism for finite sets
  when the first set is a natural number.\<close>

lemma (in enums) ord_iso_nat_fin:  
  assumes "A \<in> FinPow(X)" and "n \<in> nat" and "A \<approx> n"
  shows "\<exists>!f. f \<in> ord_iso(n,Le,A,r)"
  using assms NatOrder_ZF_1_L2 linord nat_finpow_nat 
    fin_ord_iso_ex_uniq by simp
  
text\<open>An enumeration is an order isomorhism, a bijection, and a list.\<close>

lemma (in enums) enum_props: assumes "A \<in> FinPow(X)"
  shows 
  "\<sigma>(A) \<in> ord_iso(|A|,Le, A,r)"
  "\<sigma>(A) \<in> bij(|A|,A)"
  "\<sigma>(A) : |A| \<rightarrow> A"
proof -
  from assms have
    "IsLinOrder(nat,Le)" and "|A| \<in> FinPow(nat)" and  "A \<approx> |A|"
    using NatOrder_ZF_1_L2 card_fin_is_nat nat_finpow_nat 
    by auto
  with assms show "\<sigma>(A) \<in> ord_iso(|A|,Le, A,r)"
    using linord fin_ord_iso_ex_uniq sigleton_extract 
      Enumeration_def by simp
  then show "\<sigma>(A) \<in> bij(|A|,A)" and "\<sigma>(A) : |A| \<rightarrow> A"
    using ord_iso_def bij_def surj_def
    by auto
qed

text\<open>A corollary from \<open>enum_props\<close>. Could have been attached as 
  another assertion, but this slows down verification of some other proofs.
\<close>

lemma (in enums) enum_fun: assumes "A \<in> FinPow(X)"
  shows "\<sigma>(A) : |A| \<rightarrow> X"
proof -
  from assms have "\<sigma>(A) : |A| \<rightarrow> A" and "A\<subseteq>X"
    using enum_props  FinPow_def by auto
  then show "\<sigma>(A) : |A| \<rightarrow> X" by (rule func1_1_L1B)
qed  

text\<open>If a list is an order isomorphism then it must be the enumeration.
\<close>

lemma (in enums) ord_iso_enum: assumes A1: "A \<in> FinPow(X)" and
  A2: "n \<in> nat" and A3: "f \<in> ord_iso(n,Le,A,r)"
  shows "f = \<sigma>(A)"
proof -
  from A3 have "n \<approx> A" using ord_iso_def eqpoll_def
    by auto
  then have "A \<approx> n" by (rule eqpoll_sym)
  with A1 A2 have "\<exists>!f. f \<in> ord_iso(n,Le,A,r)"
    using ord_iso_nat_fin by simp
  with assms \<open>A \<approx> n\<close> show "f = \<sigma>(A)"
    using enum_props card_card by blast
qed

text\<open>What is the enumeration of the empty set?\<close>

lemma (in enums) empty_enum: shows "\<sigma>(0) = 0"
proof -
  have 
    "0 \<in> FinPow(X)" and "0 \<in> nat" and "0 \<in> ord_iso(0,Le,0,r)"
    using empty_in_finpow empty_ord_iso_empty 
    by auto
  then show "\<sigma>(0) = 0" using ord_iso_enum 
    by blast
qed
  
text\<open>Adding a new maximum to a set appends it to the enumeration.\<close>

lemma (in enums) enum_append: 
  assumes A1: "A \<in> FinPow(X)" and A2: "b \<in> X-A" and 
  A3: "\<forall>a\<in>A. a\<lsq>b"
  shows " \<sigma>(A \<union> {b}) = \<sigma>(A)\<hookleftarrow> b"
proof -
  let ?f = "\<sigma>(A) \<union> {\<langle>|A|,b\<rangle>}"
  from A1 have "|A| \<in> nat" using card_fin_is_nat
    by simp
  from A1 A2 have "A \<union> {b} \<in> FinPow(X)"
    using singleton_in_finpow union_finpow by simp
  moreover from this have "|A \<union> {b}| \<in> nat" 
    using card_fin_is_nat by simp
  moreover have "?f \<in> ord_iso(|A \<union> {b}| , Le, A \<union> {b} ,r)"
  proof -
    from A1 A2 have 
      "\<sigma>(A) \<in> ord_iso(|A|,Le, A,r)" and 
      "|A| \<notin> |A|" and "b \<notin> A"
      using enum_props  mem_not_refl by auto
    moreover from \<open>|A| \<in> nat\<close> have 
      "\<forall>k \<in> |A|. \<langle>k, |A|\<rangle> \<in> Le" 
      using elem_nat_is_nat by blast
    moreover from A3 have "\<forall>a\<in>A. \<langle>a,b\<rangle> \<in> r" by simp
    moreover have "antisym(Le)" and "antisym(r)"
      using linord NatOrder_ZF_1_L2 IsLinOrder_def by auto
    moreover
    from  A2 \<open>|A| \<in> nat\<close> have
      "\<langle>|A|,|A|\<rangle> \<in> Le" and  "\<langle>b,b\<rangle> \<in> r"
      using linord NatOrder_ZF_1_L2 IsLinOrder_def 
	total_is_refl refl_def by auto
    hence "\<langle>|A|,|A|\<rangle> \<in> Le \<longleftrightarrow> \<langle>b,b\<rangle> \<in> r" by simp
    ultimately have "?f \<in> ord_iso(|A| \<union> {|A|} , Le, A \<union> {b} ,r)"
      by (rule ord_iso_extend)
    with A1 A2 show "?f \<in> ord_iso(|A \<union> {b}| , Le, A \<union> {b} ,r)"
      using card_fin_add_one by simp
  qed
  ultimately have "?f = \<sigma>(A \<union> {b})"
    using ord_iso_enum by simp
  moreover have "\<sigma>(A)\<hookleftarrow> b = ?f"
  proof -
    have "\<sigma>(A)\<hookleftarrow> b = \<sigma>(A) \<union> {\<langle>domain(\<sigma>(A)),b\<rangle>}"
      using Append_def by simp
    moreover from A1 have "domain(\<sigma>(A)) = |A|"
      using enum_props func1_1_L1 by blast
    ultimately show "\<sigma>(A)\<hookleftarrow> b = ?f" by simp
  qed
  ultimately show "\<sigma>(A \<union> {b}) = \<sigma>(A)\<hookleftarrow> b" by simp
qed

text\<open>What is the enumeration of a singleton?\<close>

lemma (in enums) enum_singleton: 
  assumes A1: "x\<in>X" shows "\<sigma>({x}): 1 \<rightarrow> X" and "\<sigma>({x})`(0) = x"
  proof -
    from A1 have 
      "0 \<in> FinPow(X)" and "x \<in> (X - 0)" and "\<forall>a\<in>0. a\<lsq>x"
      using empty_in_finpow by auto
    then have "\<sigma>(0 \<union> {x}) = \<sigma>(0)\<hookleftarrow> x" by (rule enum_append)
    with A1 show "\<sigma>({x}): 1 \<rightarrow> X" and "\<sigma>({x})`(0) = x"
      using empty_enum empty_append1 by auto
qed


end