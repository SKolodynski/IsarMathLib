(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2007-2025  Slawomir Kolodynski

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

theory InductiveSeq_ZF imports Nat_ZF_IML FiniteSeq_ZF FinOrd_ZF

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

text\<open>Since we have uniqueness we can show the inverse of \<open>fin_indseq_props\<close>: 
  a sequence that satisfies the inductive sequence properties listed there 
  is the inductively defined sequence. \<close>

lemma is_fin_indseq: 
  assumes "n \<in> nat" "f: X\<rightarrow>X" "x\<in>X" and
  "a: succ(n) \<rightarrow> X" "a`(0) = x" "\<forall>k\<in>n. a`(succ(k)) = f`(a`(k))"
  shows "a = InductiveSequenceN(x,f,n)"
proof -
  let ?b = "InductiveSequenceN(x,f,n)"
  from assms(1,2,3) have 
    "?b: succ(n) \<rightarrow> X" "?b`(0) = x" "\<forall>k\<in>n. ?b`(succ(k)) = f`(?b`(k))"
    using fin_indseq_props by simp_all
  with assms show ?thesis using indseq_exun by blast
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

text\<open>The inductive sequence generated by applying a function 0 times is just
  the singleton list containing the starting point.\<close>

lemma indseq_empty: assumes "f: X\<rightarrow>X" "x\<in>X"
  shows 
    "InductiveSequenceN(x,f,0):{0}\<rightarrow>X"
    "InductiveSequenceN(x,f,0) = {\<langle>0,x\<rangle>}"
proof -
  let ?a = "InductiveSequenceN(x,f,0)"
  from assms have "?a:succ(0)\<rightarrow>X" and "?a`(0) = x"
    using fin_indseq_props(1,2) by simp_all
  moreover have "succ(0) = {0}" by auto
  ultimately show "?a:{0}\<rightarrow>X" by auto
  then have "?a = {\<langle>0,?a`(0)\<rangle>}" using func_singleton_pair 
    by simp
  with\<open>?a`(0) = x\<close> show "?a = {\<langle>0,x\<rangle>}" by simp 
qed

text\<open>The tail of an inductive sequence generated by $f$ and started from $x$
  is the same as the inductive sequence started from $f(x)$.\<close>

lemma indseq_tail: assumes "n \<in> nat" "f: X\<rightarrow>X" "x\<in>X" 
  shows "Tail(InductiveSequenceN(x,f,succ(n))) = InductiveSequenceN(f`(x),f,n)"
proof -
  let ?a = "Tail(InductiveSequenceN(x,f,succ(n)))"
  from assms(2,3) have "f`(x)\<in>X" using apply_funtype by simp
  have  "?a: succ(n) \<rightarrow> X" "?a`(0) = f`(x)" and 
        "\<forall>k\<in>n. ?a`(succ(k)) = f`(?a`(k))"
  proof -
    let ?b = "InductiveSequenceN(x,f,succ(n))"
    from assms have I: "succ(n)\<in>nat" "?b: succ(succ(n)) \<rightarrow> X"
      using fin_indseq_props(1) by simp_all
    then show "Tail(?b):succ(n)\<rightarrow>X" using tail_props by simp
    from assms(1) I have II: "Tail(?b)`(0) = ?b`(succ(0))"
      using tail_props empty_in_every_succ by blast
    from assms \<open>succ(n)\<in>nat\<close> have "?b`(succ(0)) = f`(?b`(0))" 
      using fin_indseq_props(3) empty_in_every_succ by blast
    moreover from assms(2,3) \<open>succ(n)\<in>nat\<close> have "?b`(0) = x"
      using fin_indseq_props(2) by simp
    ultimately have "?b`(succ(0)) = f`(x)" by simp
    with II show "?a`(0) = f`(x)" by simp
    { fix k assume "k\<in>n"
      from I have III: "\<forall>k\<in>succ(n). ?a`(k) = ?b`(succ(k))"
        using tail_props by blast
      with assms(1) \<open>k\<in>n\<close> have "?a`(succ(k)) = ?b`(succ(succ(k)))"
        using succ_ineq by blast
      with assms \<open>k\<in>n\<close> III have "?a`(succ(k)) = f`(?a`(k))" 
        using succ_ineq fin_indseq_props(3) by simp
    } then show "\<forall>k\<in>n. ?a`(succ(k)) = f`(?a`(k))"
      by simp
  qed
  with assms(1,2) \<open>f`(x)\<in>X\<close> show ?thesis by (rule is_fin_indseq)
qed    

text\<open>The first theorem about properties of infinite inductive sequences:
  inductive sequence is a indeed a sequence (i.e. a function on the set of 
  natural numbers).\<close>

theorem indseq_seq: assumes  A1: "f: X\<rightarrow>X" and A2: "x\<in>X"
  shows "InductiveSequence(x,f) : nat \<rightarrow> X"
proof -
  let ?S = "{InductiveSequenceN(x,f,n). n \<in> nat}"
  { fix a assume "a\<in>?S"
    then obtain n where "n \<in> nat" and "a = InductiveSequenceN(x,f,n)"
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
  } hence "\<forall>a\<in>?S. \<forall>b\<in>?S. a\<subseteq>b \<or> b\<subseteq>a" by auto
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
 
text\<open>Basic properties of finite sequences defined by equation $x_{n+1}=f_n (x_n)$.\<close>

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

text\<open>Uniqueness lemma for sequences generated by equation $x_{n+1}=f_n (x_n)$:\<close>

lemma fin_indseq_var_f_uniq: assumes "n\<in>nat" "x\<in>X" "F: n \<rightarrow> (X\<rightarrow>X)"
  and "a: succ(n) \<rightarrow> X" "a`(0) = x" "\<forall>k\<in>n. a`(succ(k)) = (F`(k))`(a`(k))"
  and "b: succ(n) \<rightarrow> X" "b`(0) = x" "\<forall>k\<in>n. b`(succ(k)) = (F`(k))`(b`(k))"
  shows "a=b"
proof -
  have "\<forall>k\<in>succ(n). a`(k) = b`(k)"
  proof -
    let ?A = "{i\<in>succ(succ(n)). \<forall>k\<in>i.  a`(k) = b`(k)}"
    let ?m = "Maximum(Le,?A)"
    from assms(1) have I: "succ(succ(n)) \<in> nat" "?A\<subseteq>succ(succ(n))" by auto
    moreover 
    from assms(1,5,8) have "succ(0) \<in> ?A" using empty_in_every_succ succ_ineq
      by simp
    hence II: "?A\<noteq>0" by auto
    ultimately have "?m\<in>?A" by (rule nat_max_props)
    moreover have "?m = succ(n)"
    proof -
      { assume "?m \<noteq> succ(n)"
        from I II have III: "\<forall>k\<in>?A. k \<le> ?m" by (rule nat_max_props)
        have "succ(?m) \<in> ?A"
        proof -
          from \<open>?m \<noteq> succ(n)\<close> \<open>?m\<in>?A\<close> have "?m\<in>succ(n)" 
            using mem_succ_not_eq by blast
          from I II have "?m \<in> nat" by (rule nat_max_props)
          from \<open>succ(0) \<in> ?A\<close> III have "succ(0) \<le> ?m" by blast
          hence "?m \<noteq> 0" by auto
          with \<open>?m \<in> nat\<close> obtain k where "k\<in>nat" "?m = succ(k)"
            using Nat_ZF_1_L3 by auto
          with assms(1) \<open>?m\<in>succ(n)\<close> have "k\<in>n" using succ_mem by simp
          with assms(6,9) \<open>?m = succ(k)\<close> \<open>?m\<in>?A\<close> 
          have "a`(?m) = b`(?m)" using succ_explained by simp
          with assms(1) \<open>?m\<in>?A\<close> \<open>?m\<in>succ(n)\<close> show "succ(?m) \<in> ?A"
            using succ_explained succ_ineq by blast
        qed
        with III have "succ(?m) \<le> ?m" by (rule property_holds)
        hence False by auto
      } thus ?thesis by auto
    qed 
    ultimately show ?thesis by simp
  qed
  with assms(4,7) show "a=b" by (rule func_eq)
qed

text\<open>A sequence that has the properties of sequences generated by equation $x_{n+1}=f_n (x_n)$
  must be the one generated by this equation.\<close>

theorem is_fin_indseq_var_f:  assumes "n\<in>nat" "x\<in>X" "F: n \<rightarrow> (X\<rightarrow>X)"
  and "a: succ(n) \<rightarrow> X" "a`(0) = x" "\<forall>k\<in>n. a`(succ(k)) = (F`(k))`(a`(k))"
shows "a = InductiveSeqVarFN(x,X,F,n)"
proof -
  let ?b = "InductiveSeqVarFN(x,X,F,n)"
  from assms(1,2,3) have "?b: succ(n) \<rightarrow> X"  "?b`(0) = x" 
    and "\<forall>k\<in>n. ?b`(succ(k)) = F`(k)`(?b`(k))"
    using fin_indseq_var_f_props by simp_all
  with assms show ?thesis by (rule fin_indseq_var_f_uniq)
qed

text\<open>Analogously to the case of a constant generation function we can definite
  infinite sequence generated by a an infinite sequence of generating functions
  by taking the union of the finite ones. 
  In the definition $x\in X$ is the starting point, $X$ is the common domain of the
  generating functions and $F$ is a sequence of functions mapping $X$ to itself.\<close>

definition
  "InductiveSeqVarF(x,X,\<F>) \<equiv> \<Union>n\<in>nat. InductiveSeqVarFN(x,X,restrict(\<F>,n),n)"

text\<open>Suppose we are given a sequence of functions $S=\{f_n\}_{n\in \mathbb{N}}$
  such that $f_n:\{ 0,...,n\}\rightarrow X$ and $f_n$'s are compatible in the sense that
  for all $n\in \mathbb{N}$ and $k < n$ the restriction of $f_n$ to $\{ 0,...,k\}$
  is the same as $f_k$. Then the union $f=\bigcup_{n\in \mathbb{N}} f_n$ is a sequence
  that maps $\mathbb{N}$ to $X$ and for $n\in\mathbb{N}$ we have $f(n)=f_n(n)$. \<close>

lemma compatible_seq: assumes "\<forall>n\<in>nat. 
  S`(n):succ(n)\<rightarrow>X \<and> (\<forall>k\<in>n. restrict(S`(n),succ(k)) = S`(k))" 
  defines "f \<equiv> \<Union>{S`(n). n\<in>nat}"
  shows 
    "f:nat\<rightarrow>X" 
    "\<forall>n\<in>nat. S`(n) = restrict(f,succ(n))"
    "\<forall>n\<in>nat. \<forall>m\<in>succ(n). f`(m) = (S`(n))`(m)"
proof -
  let ?\<S> = "{S`(n). n\<in>nat}"
  from assms(1) have I: "\<forall>a \<in> ?\<S>. \<exists>A B. a:A\<rightarrow>B" by auto
  { fix a b assume "a\<in>?\<S>"   "b\<in>?\<S>"
    then obtain i j where "i\<in>nat"  "j\<in>nat" and "a=S`(i)" "b=S`(j)" 
      by auto
    from \<open>i\<in>nat\<close> \<open>j\<in>nat\<close> have "i\<subseteq>j \<or> j\<subseteq>i" using nat_incl_total by simp
    moreover have "i\<subseteq>j \<longrightarrow> a\<subseteq>b"
    proof
      assume "i\<subseteq>j" 
      with \<open>i\<in>nat\<close> \<open>j\<in>nat\<close> have "i\<in>j \<or> i=j" using nat_incl_mem_eq
        by simp
      moreover
      { assume "i\<in>j"
        with assms(1) \<open>j\<in>nat\<close> \<open>a=S`(i)\<close> \<open>b=S`(j)\<close> have "restrict(b,succ(i)) = a" 
          by simp
        then have "a\<subseteq>b" using restrict_subset by blast
      }
      moreover from \<open>a=S`(i)\<close> \<open>b=S`(j)\<close> have "i=j \<longrightarrow> a\<subseteq>b"
        by simp
      ultimately show "a\<subseteq>b" by blast
    qed
    moreover have "j\<subseteq>i \<longrightarrow> b\<subseteq>a"
    proof
      assume "j\<subseteq>i"
      with \<open>i\<in>nat\<close> \<open>j\<in>nat\<close> have "j\<in>i \<or> j=i" using nat_incl_mem_eq
        by simp
      moreover
      { assume "j\<in>i"
        with assms(1) \<open>i\<in>nat\<close> \<open>a=S`(i)\<close> \<open>b=S`(j)\<close> have "restrict(a,succ(j)) = b" 
          by simp
        then have "b\<subseteq>a" using restrict_subset by blast
      }
      moreover from \<open>a=S`(i)\<close> \<open>b=S`(j)\<close> have "i=j \<longrightarrow> b\<subseteq>a" by simp
      ultimately show "b\<subseteq>a" by blast
    qed
    ultimately have "a\<subseteq>b \<or> b\<subseteq>a" by auto
  } hence "\<forall>a\<in>?\<S>. \<forall>b\<in>?\<S>. a\<subseteq>b \<or> b\<subseteq>a" by auto
  with I have "\<Union>?\<S> : domain(\<Union>?\<S>) \<rightarrow> range(\<Union>?\<S>)"
    using fun_Union by simp
  moreover
  from assms(1) have "domain(\<Union>?\<S>) = (\<Union>n\<in>nat. domain(S`(n)))" and
    "\<forall>n\<in>nat. domain(S`(n)) = succ(n)"
    using domain_Union func1_1_L1 by auto
  then have "domain(\<Union>?\<S>) = nat" using nat_union_succ by simp
  moreover
  have "range(\<Union>?\<S>) = (\<Union>n\<in>nat. range(S`(n)))"
    using range_Union by simp
  with assms(1) have "range(\<Union>?\<S>) \<subseteq> X"
    using func1_1_L5B by force
  ultimately have "\<Union>?\<S> : nat \<rightarrow> X" using func1_1_L1B
    by simp
  with assms(2) show "f:nat\<rightarrow>X" by simp
  { fix n assume "n\<in>nat"
    with assms have 
      "S`(n):succ(n)\<rightarrow>X" "succ(n) \<subseteq> nat" "S`(n) \<subseteq> f"
      using succnat_subset_nat by auto
    with \<open>f:nat\<rightarrow>X\<close> have "S`(n) = restrict(f,succ(n))"
      using fun_restrict_eq by simp
  } thus "\<forall>n\<in>nat. S`(n) = restrict(f,succ(n))" by simp
  then show "\<forall>n\<in>nat. \<forall>m\<in>succ(n). f`(m) = (S`(n))`(m)"
    using restrict by simp
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

text\<open>The sequence of finite sequences with values defined by 
  the \<open>InductiveSeqVarFN\<close> and a generating sequence of functions
  $F:\mathbb{N}\rightarrow (X\rightarrow X)$ 
  satisfies the assumptions of lemma \<open>compatible_seq\<close>.\<close>

lemma inductive_seq_var_compat:
  assumes "n \<in> nat" "x\<in>X" "\<F>: nat \<rightarrow> (X\<rightarrow>X)"
  defines "S \<equiv> {\<langle>n,InductiveSeqVarFN(x,X,restrict(\<F>,n),n)\<rangle>. n\<in>nat}"
  shows "S`(n): succ(n)\<rightarrow>X" and "\<forall>k\<in>n. restrict(S`(n),succ(k)) = S`(k)" 
proof -
  let ?F = "restrict(\<F>,n)"
  let ?a = "InductiveSeqVarFN(x,X,?F,n)"
  from assms(1,3,4) have "S`(n) = ?a" and "?F: n \<rightarrow> (X\<rightarrow>X)"
    using ZF_fun_from_tot_val1 nat_subset_nat restrict_fun 
      by simp_all
  with assms(1,2) show "S`(n): succ(n) \<rightarrow> X"
    using fin_indseq_var_f_props(1) by simp
  { fix k assume "k\<in>n"
    with assms(1) have "k\<in>nat" "k\<subseteq>n" "succ(k) \<subseteq> succ(n)"
      using elem_nat_is_nat(2,3) nat_leq_subset_iff succ_subset
        by simp_all 
    let ?G = "restrict(?F,k)" 
    let ?b = "InductiveSeqVarFN(x,X,restrict(\<F>,k),k)"
    from \<open>?F: n \<rightarrow> (X\<rightarrow>X)\<close> \<open>k\<subseteq>n\<close> have "?G: k \<rightarrow> (X\<rightarrow>X)"
      using restrict_fun by blast
    from assms(2,3,4) \<open>k\<in>nat\<close> have "S`(k) = ?b" and
      "restrict(\<F>,k):k\<rightarrow> (X\<rightarrow>X)" and "S`(k): succ(k) \<rightarrow> X" 
      using ZF_fun_from_tot_val1 nat_subset_nat restrict_fun 
        fin_indseq_var_f_props(1) by simp_all 
    { fix j assume "j\<in>succ(k)" 
      with assms(1,2) \<open>k\<in>nat\<close> \<open>?F: n \<rightarrow> (X\<rightarrow>X)\<close> \<open>?G: k \<rightarrow> (X\<rightarrow>X)\<close> \<open>k\<subseteq>n\<close>
      have "InductiveSeqVarFN(x,X,?G,k)`(j) = ?a`(j)"
        using fin_indseq_var_f_restrict by simp
      with \<open>k\<subseteq>n\<close> \<open>S`(k)=?b\<close> \<open>S`(n) = ?a\<close> have "(S`(k))`(j) = (S`(n))`(j)"
        using restrict_restric_subset by simp
    } hence "\<forall>j\<in>succ(k). (S`(k))`(j) = (S`(n))`(j)" by simp
    with \<open>S`(n): succ(n)\<rightarrow>X\<close> \<open>S`(k): succ(k)\<rightarrow>X\<close> \<open>succ(k)\<subseteq>succ(n)\<close>
    have "restrict(S`(n),succ(k)) = S`(k)" using fun_restrict_eq_vals
      by simp
  } thus "\<forall>k\<in>n. restrict(S`(n),succ(k)) = S`(k)" by simp
qed

text\<open>If $\mathcal{F}:\mathbb{N}\rightarrow (X\rightarrow X)$ is an (infinite) sequence
  of functions mapping $X$ into itself and $x\in X$ then \<open>s=InductiveSeqVarF(x,X,\<F>)\<close>
  is a well defined sequence of elements of $X$ that satisfies the recursive
  relation $s_{n+1} = \mathcal{F}_n(s_n)$. \<close>

theorem indseq_var_seq: assumes "x\<in>X" "\<F>: nat \<rightarrow> (X\<rightarrow>X)"
  defines "s \<equiv> InductiveSeqVarF(x,X,\<F>)"
  shows "s:nat\<rightarrow>X" "s`(0) = x" and "\<forall>n\<in>nat. s`(n #+ 1) = (\<F>`(n))`(s`(n))"
proof -
  let ?S = "{\<langle>n,InductiveSeqVarFN(x,X,restrict(\<F>,n),n)\<rangle>. n\<in>nat}"
  from assms have 
    I: "\<forall>n\<in>nat. ?S`(n) = InductiveSeqVarFN(x,X,restrict(\<F>,n),n)" and
    II: "\<forall>n\<in>nat. 
        ?S`(n): succ(n)\<rightarrow>X \<and> (\<forall>k\<in>n. restrict(?S`(n),succ(k)) = ?S`(k))"
    and "s = (\<Union>{?S`(n). n\<in>nat})"
    using ZF_fun_from_tot_val2 inductive_seq_var_compat 
    unfolding InductiveSeqVarF_def by simp_all
  from \<open>s = (\<Union>{?S`(n). n\<in>nat})\<close> II show "s:nat\<rightarrow>X"
    using compatible_seq(1) by simp
  { fix n assume "n\<in>nat"
    let ?F = "restrict(\<F>,n #+ 1)"
    let ?a = "InductiveSeqVarFN(x,X,?F,n #+ 1)"
    from I \<open>n\<in>nat\<close> have "?S`(n #+ 1) = ?a" by simp
    from \<open>n\<in>nat\<close> \<open>s = (\<Union>{?S`(n). n\<in>nat})\<close> II have 
      "?S`(n #+ 1) = restrict(s,succ((n #+ 1)))"
      using compatible_seq(2) by blast
    with \<open>n\<in>nat\<close> \<open>?S`(n #+ 1) = ?a\<close> have "?a`(0) = s`(0)" and
      III: "?a`(n) = s`(n)" "?a`(succ(n)) = s`(n #+ 1)"
      using empty_in_every_succ by auto
    from assms(1,2) I \<open>n\<in>nat\<close> \<open>?a`(0) = s`(0)\<close> have
      "s`(0) = x" and "\<forall>k\<in>n #+ 1. ?a`(succ(k)) = ?F`(k)`(?a`(k))"
      using nat_subset_nat restrict_fun fin_indseq_var_f_props(2,3) 
      by simp_all
    with \<open>n\<in>nat\<close> III have "s`(0) = x \<and> s`(n #+ 1) = (\<F>`(n))`(s`(n))"
      using nat_less_add_one(2) by simp
  } thus "s`(0) = x" and "\<forall>n\<in>nat. s`(n #+ 1) = (\<F>`(n))`(s`(n))" 
    by auto
qed


subsection\<open>The Pascal's triangle\<close>

text\<open>One possible application of the inductive sequences is to define the Pascal's triangle.
  The Pascal's triangle can be defined directly as $P_{n,k} = {n\choose k}= \frac{n!}{k!(n-k)!}$ 
  for $n\geq k \geq 0$. Formalizing this definition (or explaining to a 10-years old) 
  is quite difficult as it depends on the definition of factorial and 
  some facts about factorizing natural numbers needed to show
  that the quotient in $\frac{n!}{k!(n-k)!}$ is always a natural number. Another approach uses
  induction and the property that each number in the array is the sum of the two numbers directly 
  above it.\<close>

text\<open>To shorten the definition of the function generating the Pascal's trangle we first
  define expression for the k'th element in the row following given row $r$. 
  The rows are represented as lists, i.e. functions $r:n\rightarrow \mathbb{N}$ (recall that
  for natural numbers we have $n=\{ 0,1,2,...,n-1\})$.
  The value of the next row is 1 at the beginning and equals $r(k-1)+r(k)$ 
  otherwise. A careful reader might wonder why we do not require the values to be 1
  on the right boundary of the Pascal's triangle. We are able to show this as a theorem 
  (see \<open>binom_right_boundary\<close> below) using the fact that in Isabelle/ZF the value of a function
  on an argument that is outside of the domain is the empty set, which is the same as zero of 
  natural numbers. \<close>

definition 
  "BinomElem(r,k) \<equiv> if k=0 then 1 else r`(pred(k)) #+ r`(k)"  

text\<open>Next we define a function that takes a row in a Pascal's triangle and returns the next row. \<close>

definition 
  "GenBinom \<equiv> {\<langle>r,{\<langle>k,BinomElem(r,k)\<rangle>. k\<in>succ(domain(r))}\<rangle>. r\<in>NELists(nat)}"

text\<open>The function generating rows of the Pascal's triangle is indeed a function that maps
  nonempty lists of natural numbers into nonempty lists of natural numbers. \<close>

lemma gen_binom_fun: shows "GenBinom: NELists(nat) \<rightarrow> NELists(nat)"
proof -
  { fix r assume "r \<in> NELists(nat)"
    then obtain n where "n\<in>nat" and "r:succ(n)\<rightarrow>nat" 
      unfolding NELists_def by auto
    then have "domain(r) = succ(n)" using func1_1_L1 by simp
    let ?r\<^sub>1 = "{\<langle>k,BinomElem(r,k)\<rangle>. k\<in>succ(domain(r))}"
    have "\<forall>k\<in>succ(domain(r)). BinomElem(r,k) \<in> nat"
      unfolding BinomElem_def by simp
    then have "?r\<^sub>1: succ(domain(r))\<rightarrow>nat"
      by (rule ZF_fun_from_total)
    with \<open>n\<in>nat\<close> \<open>domain(r) = succ(n)\<close> have "?r\<^sub>1\<in>NELists(nat)"
      unfolding NELists_def by auto
  } then show ?thesis using ZF_fun_from_total unfolding GenBinom_def 
    by simp
qed

text\<open>The value of the function \<open>GenBinom\<close> at a nonempty list $r$ is a list of length
  one greater than the length of $r$.\<close>

lemma gen_binom_fun_val: assumes "n\<in>nat" "r:succ(n)\<rightarrow>nat"
  shows "GenBinom`(r):succ(succ(n)) \<rightarrow> nat"
proof -
  let ?B = "{\<langle>r,{\<langle>k,BinomElem(r,k)\<rangle>. k\<in>succ(domain(r))}\<rangle>. r\<in>NELists(nat)}"
  let ?r\<^sub>1 = "{\<langle>k,BinomElem(r,k)\<rangle>. k\<in>succ(domain(r))}"
  from assms have "r\<in>NELists(nat)" unfolding NELists_def by blast
  then have "?B`(r) = ?r\<^sub>1" using ZF_fun_from_tot_val1 by simp
  have "\<forall>k\<in>succ(domain(r)). BinomElem(r,k) \<in> nat"
    unfolding BinomElem_def by simp
  then have "?r\<^sub>1: succ(domain(r))\<rightarrow>nat"
    by (rule ZF_fun_from_total)
  with assms(2) \<open>?B`(r) = ?r\<^sub>1\<close> show ?thesis
    using func1_1_L1 unfolding GenBinom_def by simp
qed

text\<open>Now we are ready to define the Pascal's triangle as the inductive sequence that
  starts from a singleton list $0\mapsto 1$ and is generated by iterations of the 
  \<open>GenBinom\<close> function. \<close>

definition
  "PascalTriangle \<equiv> InductiveSequence({\<langle>0,1\<rangle>},GenBinom)"

text\<open>The singleton list containing 1 (i.e. the starting point of the inductive sequence 
  that defines the \<open>PascalTriangle\<close>) is a finite list and 
  the \<open>PascalTriangle\<close> is a sequence (an infinite list) of nonempty lists of natural numbers.\<close>

lemma pascal_sequence: 
  shows "{\<langle>0,1\<rangle>} \<in> NELists(nat)" and "PascalTriangle: nat \<rightarrow> NELists(nat)"
  using list_len1_singleton(2) gen_binom_fun indseq_seq
  unfolding PascalTriangle_def
  by auto

text\<open>The \<open>GenBinom\<close> function creates the next row of the Pascal's triangle
  from the previous one. \<close>

lemma binom_gen: assumes "n\<in>nat"
  shows "PascalTriangle`(succ(n)) = GenBinom`(PascalTriangle`(n))"
  using assms pascal_sequence gen_binom_fun indseq_vals
  unfolding PascalTriangle_def by simp

text\<open>The $n$'th row of the Pascal's triangle is a list of $n+1$ natural numbers. \<close>

lemma pascal_row_list: 
  assumes "n\<in>nat" shows "PascalTriangle`(n):succ(n)\<rightarrow>nat"
proof -
  from assms(1) have "n\<in>nat" and "PascalTriangle`(0):succ(0)\<rightarrow>nat"
    using gen_binom_fun pascal_sequence(1) indseq_valat0 list_len1_singleton(1)
    unfolding PascalTriangle_def by auto
  moreover have 
    "\<forall>k\<in>nat. PascalTriangle`(k):succ(k)\<rightarrow>nat \<longrightarrow> 
      PascalTriangle`(succ(k)):succ(succ(k))\<rightarrow>nat"
  proof -
    { fix k assume "k\<in>nat" and "PascalTriangle`(k):succ(k)\<rightarrow>nat"
      then have "PascalTriangle`(succ(k)):succ(succ(k))\<rightarrow>nat"
        using gen_binom_fun_val gen_binom_fun pascal_sequence(1) indseq_vals 
        unfolding NELists_def PascalTriangle_def
        by auto        
    } thus ?thesis by simp
  qed
  ultimately show ?thesis by (rule ind_on_nat)
qed

text\<open>In our approach the Pascal's triangle is a list of lists. The value
  at index $n\in \mathbb{N}$ is a list of length $n+1$ (see \<open>pascal_row_list\<close> above).
  Hence, the largest index in the domain of this list is $n$. However,  
  we can still show that the value of that list at index $n+1$ is 0, because in Isabelle/ZF
  (as well as in Metamath) the value of a function at a point outside of the domain is the empty
  set, which happens to be the same as the natural number 0. \<close>

lemma pascal_val_beyond: assumes "n\<in>nat" 
  shows "(PascalTriangle`(n))`(succ(n)) = 0"
proof -
  from assms have "domain(PascalTriangle`(n)) = succ(n)"
    using pascal_row_list func1_1_L1 by blast 
  then show ?thesis using mem_self apply_0
    by simp
qed

text\<open>For $n>0$ the Pascal's triangle values at $(n,k)$ are given by the \<open>BinomElem\<close> expression. \<close>

lemma pascal_row_val: assumes "n\<in>nat" "k\<in>succ(succ(n))"
  shows "(PascalTriangle`(succ(n)))`(k) = BinomElem(PascalTriangle`(n),k)"
proof -
  let ?B = "{\<langle>r,{\<langle>k,BinomElem(r,k)\<rangle>. k\<in>succ(domain(r))}\<rangle>. r\<in>NELists(nat)}"
  let ?r = "PascalTriangle`(n)" 
  let ?B\<^sub>r = "{\<langle>k,BinomElem(?r,k)\<rangle>. k\<in>succ(succ(n))}"
  from assms(1) have "?r \<in> NELists(nat)" and "?r : succ(n)\<rightarrow>nat"
    using pascal_sequence(2) apply_funtype pascal_row_list
    by auto
  then have "?B`(?r) = ?B\<^sub>r" using func1_1_L1 ZF_fun_from_tot_val1 
    by simp
  moreover from assms(1) have "?B`(?r) = PascalTriangle`(succ(n))"
    using binom_gen unfolding GenBinom_def by simp
  moreover from assms(2) have "?B\<^sub>r`(k) = BinomElem(?r,k)"
    by (rule ZF_fun_from_tot_val1)
  ultimately show ?thesis by simp
qed

text\<open>The notion that will actually be used is the binomial coefficient ${n\choose k}$
  which we define as the value at the right place of the Pascal's triangle. \<close>

definition
  "Binom(n,k) \<equiv> (PascalTriangle`(n))`(k)"

text\<open>Entries in the Pascal's triangle are natural numbers. 
  Since in Isabelle/ZF the value of a function at a point 
  that is outside of the domain is the empty set (which is the same as zero of natural numbers) 
  we do not need any assumption on $k$.\<close>

lemma binom_in_nat: assumes "n\<in>nat" shows "Binom(n,k) \<in> nat"
proof -
  { assume "k \<in> succ(n)"
    with assms have "(PascalTriangle`(n))`(k) \<in> nat"
      using pascal_row_list apply_funtype by blast
  }
  moreover
  { assume "k \<notin> succ(n)"
    from assms have "domain(PascalTriangle`(n)) = succ(n)"
      using pascal_row_list func1_1_L1 by blast
    with \<open>k \<notin> succ(n)\<close> have "(PascalTriangle`(n))`(k) = 0"
      using apply_0 by simp
    hence "(PascalTriangle`(n))`(k) \<in> nat" by simp
  }
  ultimately show ?thesis unfolding Binom_def by blast
qed

text\<open>The top of the Pascal's triangle is equal to 1 (i.e. ${0\choose 0}=1$).
  This is an easy fact that it is useful to have handy as it  is at the start of a 
  couple of inductive arguments. \<close>

lemma binom_zero_zero: shows "Binom(0,0) = 1"
  using gen_binom_fun pascal_sequence(1) indseq_valat0 pair_val
    unfolding Binom_def PascalTriangle_def by auto

text\<open>The binomial coefficients are 1 on the left boundary of the Pascal's triangle.\<close>

theorem binom_left_boundary: assumes "n\<in>nat" shows "Binom(n,0) = 1"
proof -
  { assume "n\<noteq>0"
    with assms obtain k where "k\<in>nat" and "n = succ(k)"
      using Nat_ZF_1_L3 by blast
    then have "Binom(n,0) = 1" using empty_in_every_succ pascal_row_val
      unfolding BinomElem_def Binom_def by simp    
  }
  then show ?thesis using binom_zero_zero by blast
qed

text\<open>The main recursive property of binomial coefficients: 
  each number in the ${n\choose k}$, $n>0, 0\neq k\leq n$ array 
  (i.e. the Pascal's triangle except the top) 
  is the sum of the two numbers directly  above it. The statement looks like it has an 
  off-by-one error in the assumptions, but it's ok and needed later. \<close>

theorem binom_prop: assumes "n\<in>nat" "k \<le> n #+ 1" "k\<noteq>0"
  shows "Binom(n #+ 1,k) = Binom(n,k #- 1) #+ Binom(n,k)"
proof -
  let ?P = "PascalTriangle"
  from assms(1,2) have "k\<in>nat" and "k \<in> succ(succ(n))"
    using le_in_nat nat_mem_lt(2) by auto
  with assms(1) have "Binom(n #+ 1,k) = BinomElem(?P`(n),k)"
    unfolding Binom_def using pascal_row_val by simp
  also from assms(3) \<open>k\<in>nat\<close> have
    "BinomElem(?P`(n),k) = (?P`(n))`(k #- 1) #+ (?P`(n))`(k)"
    unfolding BinomElem_def using pred_minus_one by simp
  also have "(?P`(n))`(k #- 1) #+ (?P`(n))`(k) =  Binom(n,k #- 1) #+ Binom(n,k)"
    unfolding Binom_def by simp
  finally show ?thesis by simp
qed

text\<open>A version \<open>binom_prop\<close> where we write $k+1$ instead of $k$.\<close>

lemma binom_prop2: assumes "n\<in>nat" "k \<in> n #+ 1"
  shows "Binom(n #+ 1,k #+ 1) = Binom(n,k #+ 1) #+ Binom(n,k)"
proof -
  from assms have "k\<in>nat" using elem_nat_is_nat(2) by blast
  hence "k #+1 #- 1 = k" by simp
  moreover from assms have 
    "Binom(n #+ 1,k #+ 1) = Binom(n,k #+1 #- 1) #+ Binom(n,k #+ 1)"
    using succ_ineq2 binom_prop by simp
  ultimately show ?thesis by simp
qed

text\<open>A special case of \<open>binom_prop\<close> when $n=k+1$ that helps 
  with the induction step in the proof that the binomial coefficient 
  are 1 on the right boundary of the Pascal's triangle.\<close>

lemma binom_prop1: assumes "n\<in>nat" 
  shows "Binom(n #+ 1,n #+ 1) = Binom(n,n)"
proof -
  let ?B = "Binom"
  from assms have "?B(n,n) \<in> nat"
    using pascal_row_list apply_funtype
    unfolding Binom_def by blast
  from assms have "(PascalTriangle`(n))`(succ(n)) = 0"
    using pascal_val_beyond by simp
  moreover from assms have "succ(n) = n #+ 1"
    using succ_add_one(1) by simp
  ultimately have "?B(n,n #+ 1) = 0"
    unfolding Binom_def by simp
  with assms \<open>?B(n,n) \<in> nat\<close> show ?thesis
    using succ_add_one(2) binom_prop add_subtract add_0 add_commute
    by simp
qed

text\<open>The binomial coefficients are 1 on the right boundary of the Pascal's triangle.\<close> 

theorem binom_right_boundary: assumes "n\<in>nat" shows "Binom(n,n) = 1"
proof -
  from assms have "n\<in>nat" and "Binom(0,0) = 1"
    using binom_zero_zero by auto
  moreover have 
    "\<forall>k\<in>nat. Binom(k,k) = 1 \<longrightarrow> Binom(succ(k),succ(k)) = 1"
    using binom_prop1 by simp
  ultimately show ?thesis by (rule ind_on_nat)  
qed

subsection\<open>Monotonic sequences\<close>

text\<open>In this section we consider monotonic sequences, i.e. sequences $\{x \}_n$ such that
  $x_{n+1} \leq x_n$ for all $n\in\mathbb{N}$ (a decreasing sequence) or $x_n \leq x_{n+1}$
  for all $n\in\mathbb{N}$ (an increasing sequence). We will mostly use the raw set theory
  notation $\langle x_{n+1}, x_n\rangle\in r$ (or $\langle x_n,x_{n+1} \rangle\in r$) instead
  or the $\leq$ sign to have the relevant relation explicit.\<close>

text\<open>A decreasing sequence is a function $s:\mathbb{N}\rightarrow X$ 
  defined on the set natural numbers such that $\langle s_{n+1}, s_n\rangle\in r$ for all
  $n\in \mathbb{N}$.\<close>

definition
  "IsDecreasingSeq(X,r,s) \<equiv> s:nat\<rightarrow>X \<and> (\<forall>n\<in>nat. \<langle>s`(n #+ 1),s`(n)\<rangle> \<in> r)"

text\<open>An increasing sequence is a function $s:\mathbb{N}\rightarrow X$ 
  defined on the set natural numbers such that $\langle s_n, s_{n+1}\rangle\in r$ for all
  $n\in \mathbb{N}$. \<close>

definition
  "IsIncreasingSeq(X,r,s) \<equiv> s:nat\<rightarrow>X \<and> (\<forall>n\<in>nat. \<langle>s`(n),s`(n #+ 1)\<rangle> \<in> r)"

text\<open>If $r$ is a preorder relation and $s$ is a decreasing sequence then 
  all terms that come after $s_n$ are less or equal than $s_n$.\<close>

lemma decreasing_seq_mono: 
  assumes "IsPreorder(X,r)" "IsDecreasingSeq(X,r,s)" "n\<in>nat" "k\<in>nat"
  shows "\<langle>s`(n #+ k),s`(n)\<rangle> \<in> r" 
proof -
  from assms have "k\<in>nat" and "\<langle>s`(n #+ 0),s`(n)\<rangle> \<in> r"
    unfolding IsDecreasingSeq_def IsPreorder_def refl_def 
    using apply_funtype by auto
  moreover from assms(1,2,3) have 
    "\<forall>j\<in>nat. \<langle>s`(n #+ j),s`(n)\<rangle> \<in> r \<longrightarrow> \<langle>s`(n #+ (j #+ 1)),s`(n)\<rangle> \<in> r"
    unfolding IsDecreasingSeq_def IsPreorder_def trans_def by auto
  ultimately show ?thesis by (rule ind_on_nat1)
qed

text\<open>If $r$ is a preorder relation and $s$ is an increasing sequence then 
  all terms that come after $s_n$ are greater or equal than $s_n$.\<close>

lemma increasing_seq_mono: 
  assumes "IsPreorder(X,r)" "IsIncreasingSeq(X,r,s)" "n\<in>nat" "k\<in>nat"
  shows "\<langle>s`(n),s`(n #+ k)\<rangle> \<in> r" 
proof -
  from assms have "k\<in>nat" "\<langle>s`(n),s`(n #+ 0)\<rangle> \<in> r" and
    "\<forall>j\<in>nat. \<langle>s`(n),s`(n #+ j)\<rangle> \<in> r \<longrightarrow> \<langle>s`(n),s`(n #+ (j #+ 1))\<rangle> \<in> r"
    unfolding IsIncreasingSeq_def IsPreorder_def refl_def trans_def
    using apply_funtype by auto
  then show ?thesis by (rule ind_on_nat1)
qed

text\<open>Another formulation of \<open>decreasing_seq_mono\<close>: if a sequence $s$ is decreasing,
  $m$ is a natural number and $n\leq m$ then $s(m)\leq s(n)$.\<close>

lemma decreasing_seq_mono1: 
  assumes "IsPreorder(X,r)" "IsDecreasingSeq(X,r,s)" "m\<in>nat" "n\<le>m"
  shows "\<langle>s`(m),s`(n)\<rangle> \<in> r"
proof -
  from assms(3,4) have "n\<in>nat" "m #- n \<in> nat" and "n #+ (m #- n) = m" 
    using add_diff_inverse le_in_nat by simp_all
  from assms(1,2) \<open>n\<in>nat\<close> \<open>m #- n \<in> nat\<close> have "\<langle>s`(n #+ (m #- n)),s`(n)\<rangle> \<in> r"
    using decreasing_seq_mono by simp
  with \<open>n #+ (m #- n) = m\<close> show ?thesis by simp
qed

text\<open>Another formulation of \<open>increasing_seq_mono\<close>: if a sequence $s$ is increasing,
  $m$ is a natural number and $n\leq m$ then $s(n)\leq s(m)$.\<close>

lemma increasing_seq_mono1: 
  assumes "IsPreorder(X,r)" "IsIncreasingSeq(X,r,s)" "m\<in>nat" "n\<le>m"
  shows "\<langle>s`(n),s`(m)\<rangle> \<in> r"
proof -
  from assms(3,4) have "n\<in>nat" "m #- n \<in> nat" and "n #+ (m #- n) = m" 
    using add_diff_inverse le_in_nat by simp_all
  from assms(1,2) \<open>n\<in>nat\<close> \<open>m #- n \<in> nat\<close> have "\<langle>s`(n),s`(n #+ (m #- n))\<rangle> \<in> r"
    using increasing_seq_mono by simp
  with \<open>n #+ (m #- n) = m\<close> show ?thesis by simp
qed

text\<open>If a sequence is decreasing then the preorder is total on the sequence's image.\<close>

lemma decr_seq_total: 
  assumes "IsPreorder(X,r)" "IsDecreasingSeq(X,r,s)" 
  shows "r {is total on} s``(nat)"
proof -
  { fix x y assume "x\<in>s``(nat)" "y\<in>s``(nat)"
    from assms(2) have "s:nat\<rightarrow>X" unfolding IsDecreasingSeq_def by simp
    with \<open>x\<in>s``(nat)\<close> \<open>y\<in>s``(nat)\<close> obtain n m where 
      "n\<in>nat" "m\<in>nat" "x=s`(n)" "y=s`(m)"
      using func_imagedef by auto
    with assms(1,2) have "\<langle>x,y\<rangle> \<in> r \<or> \<langle>y,x\<rangle> \<in> r" 
      using NatOrder_ZF_1_L1 decreasing_seq_mono1 by blast
  } then show ?thesis unfolding IsTotal_def by simp
qed

text\<open>If a sequence is increasing then the preorder is total on the sequence's image.\<close>

lemma incr_seq_total: 
  assumes "IsPreorder(X,r)" "IsIncreasingSeq(X,r,s)" 
  shows "r {is total on} s``(nat)"
proof -
  { fix x y assume "x\<in>s``(nat)" "y\<in>s``(nat)"
    from assms(2) have "s:nat\<rightarrow>X" unfolding IsIncreasingSeq_def by simp
    with \<open>x\<in>s``(nat)\<close> \<open>y\<in>s``(nat)\<close> obtain n m where 
      "n\<in>nat" "m\<in>nat" "x=s`(n)" "y=s`(m)"
      using func_imagedef by auto
    with assms(1,2) have "\<langle>x,y\<rangle> \<in> r \<or> \<langle>y,x\<rangle> \<in> r" 
      using NatOrder_ZF_1_L1 increasing_seq_mono1 by blast
  } then show ?thesis unfolding IsTotal_def by simp
qed

end
