(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2007  Slawomir Kolodynski

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
section \<open>Inductive sequences\<close>

theory InductiveSeq_ZF imports Nat_ZF_IML FiniteSeq_ZF

begin

text\<open>In this theory we discuss sequences defined by conditions of the form
  $a_0 = x,\  a_{n+1} = f(a_n)$ and similar.\<close>

subsection\<open>Sequences defined by induction\<close>

text\<open>One way of defining a sequence (that is a function $a:\mathbb{N}\rightarrow X$)
  is to provide the first element of the sequence and a function to find the next 
  value when we have the current one. This is usually called "defining a sequence
  by induction". In this section we set up the notion of
  a sequence defined by induction and prove the theorems needed to use it.\<close>

text\<open>First we define a helper notion of the sequence defined inductively up to a 
  given natural number $n$.\<close>

definition
  "InductiveSequenceN(x,f,n) \<equiv> 
  THE a. a: succ(n) \<rightarrow> domain(f) \<and> a`(0) = x \<and> (\<forall>k\<in>n. a`(succ(k)) = f`(a`(k)))"

text\<open>From that we define the inductive sequence on the 
  whole set of natural numbers. Recall that in Isabelle/ZF the set of natural numbers
  is denoted \<open>nat\<close>.\<close>

definition
  "InductiveSequence(x,f) \<equiv> \<Union>n\<in>nat. InductiveSequenceN(x,f,n)"

text\<open>First we will consider the question of existence and uniqueness 
  of finite inductive sequences. The proof
  is by induction and the next lemma is the $P(0)$ step. To understand the notation
  recall that for natural numbers in set theory we have $n = \{0,1,..,n-1\}$ and
  \<open>succ(n)\<close>$ = \{0,1,..,n\}$.\<close>

lemma indseq_exun0: assumes A1: "f: X\<rightarrow>X" and A2: "x\<in>X"
  shows 
  "\<exists>! a. a: succ(0) \<rightarrow> X \<and> a`(0) = x \<and> ( \<forall>k\<in>0. a`(succ(k)) = f`(a`(k)) )"
proof
  fix a b
  assume A3:  
    "a: succ(0) \<rightarrow> X \<and> a`(0) = x \<and> ( \<forall>k\<in>0. a`(succ(k)) = f`(a`(k)) )"
    "b: succ(0) \<rightarrow> X \<and> b`(0) = x \<and> ( \<forall>k\<in>0. b`(succ(k)) = f`(b`(k)) )"
  moreover have "succ(0) = {0}" by auto
  ultimately have "a: {0} \<rightarrow> X"  "b: {0} \<rightarrow> X" by auto
  then have "a = {\<langle>0, a`(0)\<rangle>}"   "b = {\<langle>0, b`(0)\<rangle>}" using func_singleton_pair
    by auto
  with A3 show "a=b" by simp
next 
  let ?a = "{\<langle>0,x\<rangle>}"
  have "?a : {0} \<rightarrow> {x}" using singleton_fun by simp
  moreover from A1 A2 have "{x} \<subseteq> X" by simp
  ultimately have "?a : {0} \<rightarrow> X"
    using func1_1_L1B by blast
  moreover have "{0} = succ(0)" by auto
  ultimately have "?a : succ(0) \<rightarrow> X" by simp
  with A1 show 
    "\<exists> a. a: succ(0) \<rightarrow> X \<and> a`(0) = x \<and> (\<forall>k\<in>0. a`(succ(k)) = f`(a`(k)))"
    using singleton_apply by auto
qed

text\<open>A lemma about restricting finite sequences needed for the proof of
  the inductive step of the existence and uniqueness of finite inductive seqences.\<close>

lemma indseq_restrict: 
  assumes A1: "f: X\<rightarrow>X" and A2: "x\<in>X" and A3: "n \<in> nat" and
  A4: "a: succ(succ(n))\<rightarrow> X \<and> a`(0) = x \<and> (\<forall>k\<in>succ(n). a`(succ(k)) = f`(a`(k)))"
  and A5: "a\<^sub>r = restrict(a,succ(n))"
  shows 
  "a\<^sub>r: succ(n) \<rightarrow> X \<and> a\<^sub>r`(0) = x \<and> ( \<forall>k\<in>n. a\<^sub>r`(succ(k)) = f`(a\<^sub>r`(k)) )"
proof -
  from A3 have "succ(n) \<subseteq> succ(succ(n))" by auto
  with A4 A5 have "a\<^sub>r: succ(n) \<rightarrow> X" using restrict_type2 by auto
  moreover
  from A3 have "0 \<in> succ(n)" using empty_in_every_succ by simp
  with A4 A5 have "a\<^sub>r`(0) = x" using restrict_if by simp
  moreover from A3 A4 A5 have "\<forall>k\<in>n. a\<^sub>r`(succ(k)) = f`(a\<^sub>r`(k))"
    using succ_ineq restrict_if by auto
  ultimately show ?thesis by simp
qed

  
text\<open>Existence and uniqueness of finite inductive sequences. The proof
  is by induction and the next lemma is the inductive step.\<close>

lemma indseq_exun_ind: 
  assumes A1: "f: X\<rightarrow>X" and A2: "x\<in>X" and A3: "n \<in> nat" and 
  A4: "\<exists>! a. a: succ(n) \<rightarrow> X \<and> a`(0) = x \<and> (\<forall>k\<in>n. a`(succ(k)) = f`(a`(k)))"
  shows 
  "\<exists>! a. a: succ(succ(n)) \<rightarrow> X \<and> a`(0) = x \<and> 
  ( \<forall>k\<in>succ(n). a`(succ(k)) = f`(a`(k)) )"
proof
  fix a b assume
    A5: "a: succ(succ(n)) \<rightarrow> X \<and> a`(0) = x \<and> 
    ( \<forall>k\<in>succ(n). a`(succ(k)) = f`(a`(k)) )" and
    A6: "b: succ(succ(n)) \<rightarrow> X \<and> b`(0) = x \<and> 
    ( \<forall>k\<in>succ(n). b`(succ(k)) = f`(b`(k)) )"
  show "a = b"
  proof -
    let ?a\<^sub>r = "restrict(a,succ(n))"
    let ?b\<^sub>r = "restrict(b,succ(n))"
    note A1 A2 A3 A5
    moreover have "?a\<^sub>r = restrict(a,succ(n))" by simp
    ultimately have I:
      "?a\<^sub>r: succ(n) \<rightarrow> X \<and> ?a\<^sub>r`(0) = x \<and> ( \<forall>k\<in>n. ?a\<^sub>r`(succ(k)) = f`(?a\<^sub>r`(k)) )"
      by (rule indseq_restrict)
    note A1 A2 A3 A6
    moreover have "?b\<^sub>r = restrict(b,succ(n))" by simp
    ultimately have
      "?b\<^sub>r: succ(n) \<rightarrow> X \<and> ?b\<^sub>r`(0) = x \<and> ( \<forall>k\<in>n. ?b\<^sub>r`(succ(k)) = f`(?b\<^sub>r`(k)) )"
      by (rule indseq_restrict)
    with A4 I have II: "?a\<^sub>r = ?b\<^sub>r" by blast
    from A3 have "succ(n) \<in> nat" by simp
    moreover from A5 A6 have 
      "a: succ(succ(n)) \<rightarrow> X" and "b: succ(succ(n)) \<rightarrow> X"
      by auto
    moreover note II
    moreover 
    have T: "n \<in> succ(n)" by simp
    then have "?a\<^sub>r`(n) = a`(n)" and "?b\<^sub>r`(n) = b`(n)" using restrict
      by auto
    with A5 A6 II T have "a`(succ(n)) = b`(succ(n))" by simp
    ultimately show "a = b" by (rule finseq_restr_eq)
  qed
next show 
    "\<exists> a. a: succ(succ(n)) \<rightarrow> X \<and> a`(0) = x \<and> 
    ( \<forall>k\<in>succ(n). a`(succ(k)) = f`(a`(k)) )"
  proof -
    from A4 obtain a where III: "a: succ(n) \<rightarrow> X" and IV: "a`(0) = x" 
      and V: "\<forall>k\<in>n. a`(succ(k)) = f`(a`(k))" by auto
    let ?b = "a \<union> {\<langle>succ(n), f`(a`(n))\<rangle>}"
    from A1 III have
      VI: "?b : succ(succ(n)) \<rightarrow> X" and
      VII: "\<forall>k \<in> succ(n). ?b`(k) = a`(k)" and 
      VIII: "?b`(succ(n)) = f`(a`(n))" 
      using apply_funtype finseq_extend by auto
    from A3 have "0 \<in> succ(n)" using empty_in_every_succ by simp
    with IV VII have IX: "?b`(0) = x" by auto
    { fix k assume "k \<in> succ(n)"
      then have "k\<in>n \<or> k = n" by auto
      moreover
      { assume A7: "k \<in> n"
	with A3 VII have "?b`(succ(k)) = a`(succ(k))"
	  using succ_ineq by auto
	also from A7 V VII have "a`(succ(k)) = f`(?b`(k))" by simp
	finally have "?b`(succ(k)) =  f`(?b`(k))" by simp }
      moreover
      { assume A8: "k = n"
	with VIII have "?b`(succ(k)) =  f`(a`(k))" by simp
	with A8 VII VIII have "?b`(succ(k)) =  f`(?b`(k))" by simp }
      ultimately have "?b`(succ(k)) =  f`(?b`(k))" by auto
    } then have "\<forall>k \<in> succ(n). ?b`(succ(k)) =  f`(?b`(k))" by simp
    with VI IX show ?thesis by auto
  qed
qed

text\<open>The next lemma combines \<open>indseq_exun0\<close> and \<open>indseq_exun_ind\<close> 
  to show the existence and uniqueness of finite sequences defined by induction.\<close>

lemma indseq_exun: 
  assumes A1: "f: X\<rightarrow>X" and A2: "x\<in>X" and A3: "n \<in> nat"
  shows 
  "\<exists>! a. a: succ(n) \<rightarrow> X \<and> a`(0) = x \<and> (\<forall>k\<in>n. a`(succ(k)) = f`(a`(k)))"
proof -
  note A3
  moreover from A1 A2 have
    "\<exists>! a. a: succ(0) \<rightarrow> X \<and> a`(0) = x \<and> ( \<forall>k\<in>0. a`(succ(k)) = f`(a`(k)) )"
    using indseq_exun0 by simp
  moreover from A1 A2 have "\<forall>k \<in> nat.
    ( \<exists>! a. a: succ(k) \<rightarrow> X \<and> a`(0) = x \<and> 
    ( \<forall>i\<in>k. a`(succ(i)) = f`(a`(i)) )) \<longrightarrow>
    ( \<exists>! a. a: succ(succ(k)) \<rightarrow> X \<and> a`(0) = x \<and> 
    ( \<forall>i\<in>succ(k). a`(succ(i)) = f`(a`(i)) ) )"
    using indseq_exun_ind by simp
  ultimately show
    "\<exists>! a. a: succ(n) \<rightarrow> X \<and> a`(0) = x \<and> ( \<forall>k\<in>n. a`(succ(k)) = f`(a`(k)) )"
    by (rule ind_on_nat)
qed
  
text\<open>We are now ready to prove the main theorem about finite inductive sequences.\<close>

theorem fin_indseq_props: 
  assumes A1: "f: X\<rightarrow>X" and A2: "x\<in>X" and A3: "n \<in> nat" and
  A4: "a = InductiveSequenceN(x,f,n)"
  shows
  "a: succ(n) \<rightarrow> X"
  "a`(0) = x"
  "\<forall>k\<in>n. a`(succ(k)) = f`(a`(k))"
proof -
  let ?i = "THE a. a: succ(n) \<rightarrow> X \<and> a`(0) = x \<and> 
    ( \<forall>k\<in>n. a`(succ(k)) = f`(a`(k)) )"
  from A1 A2 A3 have 
    "\<exists>! a. a: succ(n) \<rightarrow> X \<and> a`(0) = x \<and> ( \<forall>k\<in>n. a`(succ(k)) = f`(a`(k)) )"
    using indseq_exun by simp
  then have 
    "?i: succ(n) \<rightarrow> X \<and> ?i`(0) = x \<and> ( \<forall>k\<in>n. ?i`(succ(k)) = f`(?i`(k)) )"
    by (rule theI)
  moreover from A1 A4 have "a = ?i"
    using InductiveSequenceN_def func1_1_L1 by simp
  ultimately show 
    "a: succ(n) \<rightarrow> X"   "a`(0) = x"   "\<forall>k\<in>n. a`(succ(k)) = f`(a`(k))"
    by auto
qed

text\<open>A corollary about the domain of a finite inductive sequence.\<close>

corollary fin_indseq_domain: 
  assumes A1: "f: X\<rightarrow>X" and A2: "x\<in>X" and A3: "n \<in> nat" 
  shows "domain(InductiveSequenceN(x,f,n)) = succ(n)"
proof -
  from assms have "InductiveSequenceN(x,f,n) : succ(n) \<rightarrow> X"
    using fin_indseq_props by simp
  then show ?thesis using func1_1_L1 by simp
qed

text\<open>The collection of finite sequences defined by induction is consistent
  in the sense that the restriction of the sequence defined on a larger
  set to the smaller set is the same as the sequence defined on the smaller set.\<close>

lemma indseq_consistent: assumes A1: "f: X\<rightarrow>X" and A2: "x\<in>X" and 
  A3: "i \<in> nat"  "j \<in> nat" and A4: "i \<subseteq> j"
  shows 
  "restrict(InductiveSequenceN(x,f,j),succ(i)) = InductiveSequenceN(x,f,i)"
proof -
  let ?a = "InductiveSequenceN(x,f,j)"
  let ?b = "restrict(InductiveSequenceN(x,f,j),succ(i))"
  let ?c = "InductiveSequenceN(x,f,i)"
  from A1 A2 A3 have 
    "?a: succ(j) \<rightarrow> X"  "?a`(0) = x"   "\<forall>k\<in>j. ?a`(succ(k)) = f`(?a`(k))"
    using fin_indseq_props by auto
  with A3 A4 have
    "?b: succ(i) \<rightarrow> X \<and> ?b`(0) = x \<and> ( \<forall>k\<in>i. ?b`(succ(k)) = f`(?b`(k)))"
    using succ_subset restrict_type2 empty_in_every_succ restrict succ_ineq
    by auto
  moreover from A1 A2 A3 have
    "?c: succ(i) \<rightarrow> X \<and> ?c`(0) = x \<and> ( \<forall>k\<in>i. ?c`(succ(k)) = f`(?c`(k)))"
    using fin_indseq_props by simp
  moreover from A1 A2 A3 have
    "\<exists>! a. a: succ(i) \<rightarrow> X \<and> a`(0) = x \<and> ( \<forall>k\<in>i. a`(succ(k)) = f`(a`(k)) )"
    using indseq_exun by simp
  ultimately show "?b = ?c" by blast
qed

text\<open>For any two natural numbers one of the corresponding inductive sequences
  is contained in the other.\<close>

lemma indseq_subsets: assumes A1: "f: X\<rightarrow>X" and A2: "x\<in>X" and 
  A3: "i \<in> nat"  "j \<in> nat" and 
  A4: "a = InductiveSequenceN(x,f,i)"  "b = InductiveSequenceN(x,f,j)"
  shows "a \<subseteq> b \<or> b \<subseteq> a"
proof -
  from A3 have "i\<subseteq>j \<or> j\<subseteq>i" using nat_incl_total by simp
  moreover
  { assume "i\<subseteq>j"
    with A1 A2 A3 A4 have "restrict(b,succ(i)) = a" 
      using indseq_consistent by simp
    moreover have "restrict(b,succ(i)) \<subseteq> b" 
      using restrict_subset by simp
    ultimately have "a \<subseteq> b \<or> b \<subseteq> a" by simp }
  moreover
  { assume "j\<subseteq>i"
    with A1 A2 A3 A4 have "restrict(a,succ(j)) = b" 
      using indseq_consistent by simp
    moreover have "restrict(a,succ(j)) \<subseteq> a" 
      using restrict_subset by simp
    ultimately have "a \<subseteq> b \<or> b \<subseteq> a" by simp }
  ultimately show  "a \<subseteq> b \<or> b \<subseteq> a" by auto
qed

text\<open>The first theorem about properties of infinite inductive sequences:
  inductive sequence is a indeed a sequence (i.e. a function on the set of 
  natural numbers.\<close>

theorem indseq_seq: assumes  A1: "f: X\<rightarrow>X" and A2: "x\<in>X"
  shows "InductiveSequence(x,f) : nat \<rightarrow> X"
proof -
  let ?S = "{InductiveSequenceN(x,f,n). n \<in> nat}"
  { fix a assume "a\<in>?S"
    then obtain n where "n \<in> nat" and "a =  InductiveSequenceN(x,f,n)"
      by auto
    with A1 A2 have "a : succ(n)\<rightarrow>X" using fin_indseq_props
      by simp
    then have "\<exists>A B. a:A\<rightarrow>B" by auto
  } then have "\<forall>a \<in> ?S. \<exists>A B. a:A\<rightarrow>B" by auto
  moreover
  { fix a b assume "a\<in>?S"   "b\<in>?S"
    then obtain i j where "i\<in>nat"  "j\<in>nat" and
      "a = InductiveSequenceN(x,f,i)"   "b = InductiveSequenceN(x,f,j)"
      by auto
    with A1 A2 have "a\<subseteq>b \<or> b\<subseteq>a" using indseq_subsets by simp
  } then have "\<forall>a\<in>?S. \<forall>b\<in>?S. a\<subseteq>b \<or> b\<subseteq>a" by auto
  ultimately have "\<Union>?S : domain(\<Union>?S) \<rightarrow> range(\<Union>?S)"
    using fun_Union by simp
  with A1 A2 have I: "\<Union>?S : nat \<rightarrow> range(\<Union>?S)"
    using domain_UN fin_indseq_domain nat_union_succ by simp
  moreover
  { fix k assume A3: "k \<in> nat"
    let ?y = "(\<Union>?S)`(k)"
    note I A3
    moreover have "?y = (\<Union>?S)`(k)" by simp
    ultimately have "\<langle>k,?y\<rangle> \<in> (\<Union>?S)" by (rule func1_1_L5A)
    then obtain n where "n \<in> nat" and II: "\<langle>k,?y\<rangle> \<in> InductiveSequenceN(x,f,n)"
      by auto
    with A1 A2 have "InductiveSequenceN(x,f,n): succ(n) \<rightarrow> X" 
      using fin_indseq_props by simp
    with II have "?y \<in> X" using func1_1_L5 by blast
  } then have "\<forall>k \<in> nat.  (\<Union>?S)`(k) \<in> X" by simp
  ultimately have "\<Union>?S : nat \<rightarrow> X" using func1_1_L1A
    by blast
  then show "InductiveSequence(x,f) : nat \<rightarrow> X"
    using InductiveSequence_def by simp
qed

text\<open>Restriction of an inductive sequence to a finite domain
  is the corresponding finite inductive sequence.\<close>

lemma indseq_restr_eq: 
  assumes A1: "f: X\<rightarrow>X" and A2: "x\<in>X" and A3: "n \<in> nat"
  shows 
  "restrict(InductiveSequence(x,f),succ(n)) = InductiveSequenceN(x,f,n)"
proof -
  let ?a = "InductiveSequence(x,f)"
  let ?b = "InductiveSequenceN(x,f,n)"
  let ?S = "{InductiveSequenceN(x,f,n). n \<in> nat}"
  from A1 A2 A3 have 
    I: "?a : nat \<rightarrow> X"  and "succ(n) \<subseteq> nat"
    using indseq_seq succnat_subset_nat by auto
  then have "restrict(?a,succ(n)) : succ(n) \<rightarrow> X"
    using restrict_type2 by simp
  moreover from A1 A2 A3 have "?b : succ(n) \<rightarrow> X"
    using fin_indseq_props by simp
  moreover
  { fix k assume A4: "k \<in> succ(n)"
    from A1 A2 A3 I have
      "\<Union>?S : nat \<rightarrow> X"   "?b \<in> ?S"  "?b : succ(n) \<rightarrow> X"
      using InductiveSequence_def fin_indseq_props by auto
    with A4 have "restrict(?a,succ(n))`(k) = ?b`(k)"
      using fun_Union_apply InductiveSequence_def restrict_if
      by simp
  } then have "\<forall>k \<in> succ(n). restrict(?a,succ(n))`(k) = ?b`(k)" 
    by simp
  ultimately show ?thesis by (rule func_eq)
qed

text\<open>The first element of the inductive sequence starting at $x$ and generated by $f$
  is indeed $x$.\<close>

theorem indseq_valat0: assumes A1: "f: X\<rightarrow>X" and A2: "x\<in>X"
  shows "InductiveSequence(x,f)`(0) = x"
proof -
  let ?a = "InductiveSequence(x,f)"
  let ?b = "InductiveSequenceN(x,f,0)"
  have T: "0\<in>nat"  "0 \<in> succ(0)" by auto
  with A1 A2 have "?b`(0) = x" 
    using fin_indseq_props by simp
  moreover from T have "restrict(?a,succ(0))`(0) = ?a`(0)"
    using restrict_if by simp
  moreover from A1 A2 T have 
    "restrict(?a,succ(0)) = ?b"
    using indseq_restr_eq by simp
  ultimately show "?a`(0) = x" by simp
qed

text\<open>An infinite inductive sequence satisfies the 
  inductive relation that defines it.\<close>
  
theorem indseq_vals: 
  assumes A1: "f: X\<rightarrow>X" and A2: "x\<in>X"  and A3: "n \<in> nat"
  shows 
  "InductiveSequence(x,f)`(succ(n)) = f`(InductiveSequence(x,f)`(n))"
proof -
  let ?a = "InductiveSequence(x,f)"
  let ?b = "InductiveSequenceN(x,f,succ(n))"
  from A3 have T: 
    "succ(n) \<in> succ(succ(n))"  
    "succ(succ(n)) \<in> nat" 
    "n \<in> succ(succ(n))"
    by auto    
  then have "?a`(succ(n)) = restrict(?a,succ(succ(n)))`(succ(n))"
    using restrict_if by simp
  also from A1 A2 T have "\<dots> = f`(restrict(?a,succ(succ(n)))`(n))"
    using indseq_restr_eq fin_indseq_props by simp
  also from T have "\<dots> = f`(?a`(n))" using restrict_if by simp
  finally show "?a`(succ(n)) = f`(?a`(n))" by simp
qed

subsection\<open>Images of inductive sequences\<close>

text\<open>In this section we consider the properties of sets that are
  images of inductive sequences, that is are of the form
  $\{f^{(n)} (x) : n \in N\}$ for some $x$ in the domain of $f$,
  where $f^{(n)}$ denotes the $n$'th
  iteration of the function $f$. For a function $f:X\rightarrow X$ and
  a point $x\in X$ such set is set is sometimes called 
  the orbit of $x$ generated by $f$.\<close>

text\<open>The basic properties of orbits.\<close>

theorem ind_seq_image: assumes A1: "f: X\<rightarrow>X" and A2: "x\<in>X"  and 
  A3: "A = InductiveSequence(x,f)``(nat)"
  shows "x\<in>A" and "\<forall>y\<in>A. f`(y) \<in> A" 
proof -
  let ?a = "InductiveSequence(x,f)"
  from A1 A2 have "?a : nat \<rightarrow> X" using indseq_seq
    by simp
  with A3 have I: "A = {?a`(n). n \<in> nat}" using func_imagedef
    by auto hence "?a`(0) \<in> A" by auto
  with A1 A2 show "x\<in>A" using indseq_valat0 by simp
  { fix y assume "y\<in>A"
    with I obtain n where II: "n \<in> nat" and III: "y = ?a`(n)"
      by auto
    with A1 A2 have "?a`(succ(n)) = f`(y)"
      using indseq_vals by simp
    moreover from I II have "?a`(succ(n)) \<in> A" by auto
    ultimately have "f`(y) \<in> A" by simp
  } then show "\<forall>y\<in>A. f`(y) \<in> A" by simp
qed

subsection\<open>Subsets generated by a binary operation\<close>

text\<open>In algebra we often talk about sets "generated" by an element,
  that is sets of the form (in multiplicative notation) $\{a^n | n\in Z\}$.
  This is a related to a general notion of "power" 
  (as in $a^n = a\cdot a \cdot .. \cdot a$ ) or multiplicity $n\cdot a = a+a+..+a$.
  The intuitive meaning of such notions is obvious, but we need to do some
  work to be able to use it in the formalized setting. This sections is devoted
  to sequences that are created by repeatedly applying a binary operation with the 
  second argument fixed to some constant.\<close>

text\<open>Basic propertes of sets generated by binary operations.\<close>

theorem binop_gen_set: 
  assumes A1: "f: X\<times>Y \<rightarrow> X" and A2: "x\<in>X"  "y\<in>Y" and
  A3: "a = InductiveSequence(x,Fix2ndVar(f,y))"
  shows
  "a : nat \<rightarrow> X"
  "a``(nat) \<in> Pow(X)"
  "x \<in> a``(nat)"
  "\<forall>z \<in> a``(nat). Fix2ndVar(f,y)`(z) \<in> a``(nat)"
proof -
  let ?g = "Fix2ndVar(f,y)"
  from A1 A2 have I: "?g : X\<rightarrow>X"
    using fix_2nd_var_fun by simp
  with A2 A3 show "a : nat \<rightarrow> X"
    using indseq_seq by simp
  then show "a``(nat) \<in> Pow(X)" using func1_1_L6 by simp
  from A2 A3 I show "x \<in> a``(nat)" using ind_seq_image by blast
  from A2 A3 I have
    "?g : X\<rightarrow>X"  "x\<in>X"  "a``(nat) = InductiveSequence(x,?g)``(nat)"
    by auto
  then show "\<forall>z \<in> a``(nat). Fix2ndVar(f,y)`(z) \<in> a``(nat)"
    by (rule ind_seq_image)
qed

text\<open>A simple corollary to the theorem \<open>binop_gen_set\<close>: a set
  that contains all iterations of the application of a binary operation
  exists.\<close>

lemma binop_gen_set_ex: assumes A1: "f: X\<times>Y \<rightarrow> X" and A2: "x\<in>X"  "y\<in>Y"
  shows "{A \<in> Pow(X). x\<in>A \<and> (\<forall>z \<in> A. f`\<langle>z,y\<rangle> \<in> A) } \<noteq> 0"
proof -
  let ?a = "InductiveSequence(x,Fix2ndVar(f,y))" 
  let ?A = "?a``(nat)"
  from A1 A2 have I: "?A \<in> Pow(X)" and "x \<in> ?A" using binop_gen_set 
    by auto
  moreover
  { fix z assume T: "z\<in>?A"
    with A1 A2 have "Fix2ndVar(f,y)`(z) \<in> ?A"
      using binop_gen_set by simp
    moreover
    from I T have "z \<in> X" by auto
    with A1 A2 have "Fix2ndVar(f,y)`(z) = f`\<langle>z,y\<rangle>"
      using fix_var_val by simp
    ultimately have "f`\<langle>z,y\<rangle> \<in> ?A" by simp
  } then have "\<forall>z \<in> ?A. f`\<langle>z,y\<rangle> \<in> ?A" by simp
  ultimately show ?thesis by auto
qed

text\<open>A more general version of \<open> binop_gen_set\<close> where the generating
  binary operation acts on a larger set.\<close>

theorem binop_gen_set1: assumes A1: "f: X\<times>Y \<rightarrow> X" and 
  A2: "X\<^sub>1 \<subseteq> X" and A3: "x\<in>X\<^sub>1"  "y\<in>Y" and
  A4: "\<forall>t\<in>X\<^sub>1. f`\<langle>t,y\<rangle> \<in> X\<^sub>1" and 
  A5: "a = InductiveSequence(x,Fix2ndVar(restrict(f,X\<^sub>1\<times>Y),y))"
shows 
  "a : nat \<rightarrow> X\<^sub>1"
  "a``(nat) \<in> Pow(X\<^sub>1)"
  "x \<in> a``(nat)"
  "\<forall>z \<in> a``(nat). Fix2ndVar(f,y)`(z) \<in> a``(nat)"
  "\<forall>z \<in> a``(nat). f`\<langle>z,y\<rangle> \<in> a``(nat)"
proof -
  let ?h = "restrict(f,X\<^sub>1\<times>Y)"
  let ?g = "Fix2ndVar(?h,y)"
  from A2 have "X\<^sub>1\<times>Y \<subseteq> X\<times>Y" by auto
  with A1 have I: "?h : X\<^sub>1\<times>Y \<rightarrow> X"
    using restrict_type2 by simp
  with A3 have II: "?g: X\<^sub>1 \<rightarrow> X" using fix_2nd_var_fun by simp
  from A3 A4 I have "\<forall>t\<in>X\<^sub>1. ?g`(t) \<in> X\<^sub>1"
    using restrict fix_var_val by simp
  with II have III: "?g : X\<^sub>1 \<rightarrow> X\<^sub>1" using func1_1_L1A by blast
  with A3 A5 show "a : nat \<rightarrow> X\<^sub>1" using indseq_seq by simp
  then show IV: "a``(nat) \<in> Pow(X\<^sub>1)" using func1_1_L6 by simp
  from A3 A5 III show "x \<in> a``(nat)" using ind_seq_image by blast
  from A3 A5 III have 
    "?g : X\<^sub>1 \<rightarrow> X\<^sub>1"   "x\<in>X\<^sub>1"  "a``(nat) =  InductiveSequence(x,?g)``(nat)"
    by auto
  then have "\<forall>z \<in> a``(nat). Fix2ndVar(?h,y)`(z) \<in> a``(nat)" 
    by (rule ind_seq_image)
  moreover
  { fix z assume "z \<in> a``(nat)"
    with IV have "z \<in> X\<^sub>1" by auto
    with A1 A2 A3 have "?g`(z) = Fix2ndVar(f,y)`(z)"
      using fix_2nd_var_restr_comm restrict by simp
  } then have "\<forall>z \<in> a``(nat). ?g`(z) = Fix2ndVar(f,y)`(z)" by simp
  ultimately show "\<forall>z \<in> a``(nat). Fix2ndVar(f,y)`(z) \<in> a``(nat)" by simp
  moreover
  { fix z assume "z \<in> a``(nat)"
    with A2 IV have "z\<in>X" by auto
    with A1 A3 have "Fix2ndVar(f,y)`(z) = f`\<langle>z,y\<rangle>"
      using fix_var_val by simp
  } then have "\<forall>z \<in> a``(nat). Fix2ndVar(f,y)`(z) = f`\<langle>z,y\<rangle>"
    by simp
  ultimately show "\<forall>z \<in> a``(nat). f`\<langle>z,y\<rangle> \<in> a``(nat)"
    by simp
qed

text\<open>A generalization of \<open> binop_gen_set_ex\<close> that applies when the binary
  operation acts on a larger set. This is used in our Metamath translation
  to prove the existence of the set of real natural numbers. 
  Metamath defines the real natural numbers as the smallest set that cantains
  $1$ and is closed with respect to operation of adding $1$.\<close>

lemma binop_gen_set_ex1: assumes A1: "f: X\<times>Y \<rightarrow> X" and 
  A2: "X\<^sub>1 \<subseteq> X" and A3: "x\<in>X\<^sub>1"  "y\<in>Y" and
  A4: "\<forall>t\<in>X\<^sub>1. f`\<langle>t,y\<rangle> \<in> X\<^sub>1"
  shows "{A \<in> Pow(X\<^sub>1). x\<in>A \<and> (\<forall>z \<in> A. f`\<langle>z,y\<rangle> \<in> A) } \<noteq> 0"
proof -
  let ?a = "InductiveSequence(x,Fix2ndVar(restrict(f,X\<^sub>1\<times>Y),y))"
  let ?A = "?a``(nat)"
  from A1 A2 A3 A4 have 
    "?A \<in> Pow(X\<^sub>1)"   "x \<in> ?A"   "\<forall>z \<in> ?A. f`\<langle>z,y\<rangle> \<in> ?A"
    using binop_gen_set1 by auto
  thus ?thesis by auto
qed

subsection\<open>Inductive sequences with changing generating function\<close>

text\<open>A seemingly more general form of a sequence defined by induction 
  is a sequence generated by the difference equation $x_{n+1} = f_{n} (x_n)$
  where $n\mapsto f_n$ is a given sequence of functions such 
  that each maps $X$ into inself. 
  For example when 
  $f_n (x) := x + x_n$ then the equation $S_{n+1} = f_{n} (S_n)$ describes
  the sequence $n \mapsto S_n = s_0 +\sum_{i=0}^n x_n$, i.e. the sequence of 
  partial sums of the sequence $\{s_0, x_0, x_1, x_3,..\}$. 
\<close>

text\<open>The situation where the function that we iterate changes with $n$ can be 
  derived from the simpler case if we define the generating function appropriately.
  Namely, we replace the generating function in the definitions of 
  \<open>InductiveSequenceN\<close> by the function $f: X\times n \rightarrow X\times n$, 
  $f\langle x,k\rangle = \langle f_k(x), k+1 \rangle$ if $k < n$,  
  $\langle f_k(x), k \rangle$ otherwise. The first notion defines the expression 
  we will use to define the generating function. 
  To understand the notation recall that in standard Isabelle/ZF
  for a pair $s=\langle x,n \rangle$ we have \<open>fst\<close>$(s)=x$ and 
  \<open>snd\<close>$(s)=n$.\<close>

definition
  "StateTransfFunNMeta(F,n,s) \<equiv> 
  if (snd(s) \<in> n) then \<langle>F`(snd(s))`(fst(s)), succ(snd(s))\<rangle> else s"

text\<open>Then we define the actual generating function on sets of pairs
  from $X\times \{0,1, .. ,n\}$.\<close>

definition
  "StateTransfFunN(X,F,n) \<equiv> {\<langle>s, StateTransfFunNMeta(F,n,s)\<rangle>. s \<in> X\<times>succ(n)}"

text\<open>Having the generating function we can define the expression
  that we cen use to define the inductive sequence generates.\<close>

definition
  "StatesSeq(x,X,F,n) \<equiv> 
  InductiveSequenceN(\<langle>x,0\<rangle>, StateTransfFunN(X,F,n),n)"

text\<open>Finally we can define the sequence given by a initial point $x$,
  and a sequence $F$ of $n$ functions.\<close>

definition
  "InductiveSeqVarFN(x,X,F,n) \<equiv> {\<langle>k,fst(StatesSeq(x,X,F,n)`(k))\<rangle>. k \<in> succ(n)}"

text\<open>The state transformation function (\<open>StateTransfFunN\<close> is 
  a function that transforms $X\times n$ into itself.\<close>

lemma state_trans_fun: assumes A1: "n \<in> nat" and A2: "F: n \<rightarrow> (X\<rightarrow>X)"
  shows "StateTransfFunN(X,F,n): X\<times>succ(n) \<rightarrow> X\<times>succ(n)"
proof -
  { fix s assume A3: "s \<in> X\<times>succ(n)"
    let ?x = "fst(s)"
    let ?k = "snd(s)"
    let ?S = "StateTransfFunNMeta(F,n,s)"
    from A3 have T: "?x \<in> X"  "?k \<in> succ(n)" and "\<langle>?x,?k\<rangle> = s" by auto
    { assume A4: "?k \<in> n"
      with A1 have "succ(?k) \<in> succ(n)" using succ_ineq by simp
      with A2 T A4 have "?S \<in> X\<times>succ(n)"
	using apply_funtype StateTransfFunNMeta_def by simp }
    with A2 A3 T have "?S \<in> X\<times>succ(n)"
      using apply_funtype StateTransfFunNMeta_def by auto
  } then have "\<forall>s \<in> X\<times>succ(n). StateTransfFunNMeta(F,n,s) \<in> X\<times>succ(n)"
    by simp
  then have 
    "{\<langle>s, StateTransfFunNMeta(F,n,s)\<rangle>. s \<in> X\<times>succ(n)} : X\<times>succ(n) \<rightarrow> X\<times>succ(n)"
    by (rule ZF_fun_from_total)
  then show "StateTransfFunN(X,F,n): X\<times>succ(n) \<rightarrow> X\<times>succ(n)"
    using StateTransfFunN_def by simp
qed

text\<open>We can apply \<open>fin_indseq_props\<close> to the sequence used in the
  definition of \<open>InductiveSeqVarFN\<close> to get the properties of the sequence
  of states generated by the \<open>StateTransfFunN\<close>.\<close>

lemma states_seq_props:
  assumes A1: "n \<in> nat" and A2: "F: n \<rightarrow> (X\<rightarrow>X)" and A3: "x\<in>X" and 
  A4: "b = StatesSeq(x,X,F,n)"
  shows
  "b : succ(n) \<rightarrow> X\<times>succ(n)"
  "b`(0) = \<langle>x,0\<rangle>"
  "\<forall>k \<in> succ(n). snd(b`(k)) = k"  
  "\<forall>k\<in>n. b`(succ(k)) = \<langle>F`(k)`(fst(b`(k))), succ(k)\<rangle>"
proof -
  let ?f = "StateTransfFunN(X,F,n)"
  from A1 A2 have I: "?f : X\<times>succ(n) \<rightarrow> X\<times>succ(n)"
    using state_trans_fun by simp
  moreover from A1 A3 have II: "\<langle>x,0\<rangle> \<in> X\<times>succ(n)"
    using empty_in_every_succ by simp
  moreover note A1
  moreover from A4 have III: "b = InductiveSequenceN(\<langle>x,0\<rangle>,?f,n)"
    using StatesSeq_def by simp
  ultimately show IV: "b : succ(n) \<rightarrow> X\<times>succ(n)"
    by (rule fin_indseq_props)
  from I II A1 III show V: "b`(0) = \<langle>x,0\<rangle>"
    by (rule fin_indseq_props)
  from I II A1 III have VI: "\<forall>k\<in>n. b`(succ(k)) = ?f`(b`(k))"
    by (rule fin_indseq_props)
  { fix k 
    note I
    moreover
    assume A5: "k \<in> n" hence "k \<in> succ(n)" by auto
    with IV have "b`(k) \<in>  X\<times>succ(n)" using apply_funtype by simp
    moreover have "?f = {\<langle>s, StateTransfFunNMeta(F,n,s)\<rangle>. s \<in> X\<times>succ(n)}"
      using StateTransfFunN_def by simp
    ultimately have "?f`(b`(k)) =  StateTransfFunNMeta(F,n,b`(k))"
      by (rule ZF_fun_from_tot_val)
  } then have VII: "\<forall>k \<in> n. ?f`(b`(k)) =  StateTransfFunNMeta(F,n,b`(k))"
    by simp
  { fix k assume A5: "k \<in> succ(n)"
    note A1 A5
    moreover from V have " snd(b`(0)) = 0" by simp
    moreover from VI VII have 
      "\<forall>j\<in>n. snd(b`(j)) = j \<longrightarrow> snd(b`(succ(j))) = succ(j)"
      using StateTransfFunNMeta_def by auto
    ultimately have "snd(b`(k)) = k" by (rule fin_nat_ind)
  } then show "\<forall>k \<in> succ(n). snd(b`(k)) = k" by simp
  with VI VII show "\<forall>k\<in>n. b`(succ(k)) = \<langle>F`(k)`(fst(b`(k))), succ(k)\<rangle>"
    using StateTransfFunNMeta_def by auto
qed

text\<open>Basic properties of sequences defined by equation $x_{n+1}=f_n (x_n)$.\<close>

theorem fin_indseq_var_f_props: 
  assumes A1: "n \<in> nat" and A2: "x\<in>X" and A3: "F: n \<rightarrow> (X\<rightarrow>X)" and 
  A4: "a = InductiveSeqVarFN(x,X,F,n)"
  shows
  "a: succ(n) \<rightarrow> X"
  "a`(0) = x"
  "\<forall>k\<in>n. a`(succ(k)) = F`(k)`(a`(k))"
proof -
  let ?f = "StateTransfFunN(X,F,n)"
  let ?b = "StatesSeq(x,X,F,n)"
  from A1 A2 A3 have "?b : succ(n) \<rightarrow> X\<times>succ(n)"
    using states_seq_props by simp
  then have "\<forall>k \<in> succ(n). ?b`(k) \<in> X\<times>succ(n)"
    using apply_funtype by simp
  hence "\<forall>k \<in> succ(n). fst(?b`(k)) \<in> X" by auto
  then have I: "{\<langle>k,fst(?b`(k))\<rangle>. k \<in> succ(n)} : succ(n) \<rightarrow> X"
    by (rule ZF_fun_from_total)
  with A4 show II: "a: succ(n) \<rightarrow> X" using InductiveSeqVarFN_def
    by simp
  moreover from A1 have "0 \<in> succ(n)" using empty_in_every_succ
    by simp
  moreover from A4 have III: 
    "a = {\<langle>k,fst(StatesSeq(x,X,F,n)`(k))\<rangle>. k \<in> succ(n)}"
    using InductiveSeqVarFN_def by simp
  ultimately have "a`(0) = fst(?b`(0))"
    by (rule ZF_fun_from_tot_val)
  with A1 A2 A3 show "a`(0) = x" using states_seq_props by auto
  { fix k
    assume A5: "k \<in> n"
    with A1 have T1: "succ(k) \<in> succ(n)" and T2: "k \<in> succ(n)"
      using succ_ineq by auto
    from II T1 III have "a`(succ(k)) = fst(?b`(succ(k)))"
      by (rule ZF_fun_from_tot_val)
    with A1 A2 A3 A5 have "a`(succ(k)) = F`(k)`(fst(?b`(k)))"
      using states_seq_props by simp
    moreover from II T2 III have "a`(k) = fst(?b`(k))"
      by (rule ZF_fun_from_tot_val)
    ultimately have "a`(succ(k)) =  F`(k)`(a`(k))"
      by simp
  } then show "\<forall>k\<in>n. a`(succ(k)) = F`(k)`(a`(k))"
    by simp
qed

text\<open>A consistency condition: if we make the sequence of 
  generating functions shorter, then we get a shorter inductive 
  sequence with the same values as in the original sequence.\<close>

lemma fin_indseq_var_f_restrict: assumes 
  A1: "n \<in> nat"  "i \<in> nat"  "x\<in>X"  "F: n \<rightarrow> (X\<rightarrow>X)"   "G: i \<rightarrow> (X\<rightarrow>X)"
  and A2: "i \<subseteq> n" and  A3: "\<forall>j\<in>i. G`(j) = F`(j)" and A4: "k \<in> succ(i)"
  shows "InductiveSeqVarFN(x,X,G,i)`(k) = InductiveSeqVarFN(x,X,F,n)`(k)"
proof -
  let ?a = "InductiveSeqVarFN(x,X,F,n)"
  let ?b = "InductiveSeqVarFN(x,X,G,i)"
  from A1 A4 have "i \<in> nat"  "k \<in> succ(i)" by auto
  moreover from A1 have "?b`(0) = ?a`(0)"
    using fin_indseq_var_f_props by simp
  moreover from A1 A2 A3 have
    "\<forall>j\<in>i. ?b`(j) = ?a`(j) \<longrightarrow> ?b`(succ(j)) = ?a`(succ(j))"
    using fin_indseq_var_f_props by auto
  ultimately show "?b`(k) = ?a`(k)"
    by (rule fin_nat_ind)
qed
  

(*text{*If we make the sequence of generating funtions shorter, the resulting
  sequence will be shorter.*}

lemma fin_indseq_var_f_restrict:
  assumes A1: "n \<in> nat" and A2: "x\<in>X" and 
  A3: "F: n \<rightarrow> (X\<rightarrow>X)" and A4: "k \<le> n" and
  A5: "a = restrict(InductiveSeqVarFN(x,X,F,n),k)" and
  A6: "b = InductiveSeqVarFN(x,X,restrict(F,k),k)"
  shows "a = b"
proof -*)
  
end