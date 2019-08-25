(*
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2007  Slawomir Kolodynski

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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open>Finite sequences\<close>

theory FiniteSeq_ZF imports Nat_ZF_IML func1

begin

text\<open>This theory treats finite sequences (i.e. maps $n\rightarrow X$, where
  $n=\{0,1,..,n-1\}$ is a natural number) as lists. It defines and proves
  the properties of basic operations on lists: concatenation, appending
  and element etc.\<close>

subsection\<open>Lists as finite sequences\<close>

text\<open>A natural way of representing (finite) lists in set theory is through 
  (finite) sequences.
  In such view a list of elements of a set $X$ is a 
  function that maps the set $\{0,1,..n-1\}$ into $X$. Since natural numbers 
  in set theory are defined so that $n =\{0,1,..n-1\}$, a list of length $n$
  can be understood as an element of the function space $n\rightarrow X$.
\<close>

text\<open>We define the set of lists with values in set $X$ as \<open>Lists(X)\<close>.\<close>

definition
  "Lists(X) \<equiv> \<Union>n\<in>nat.(n\<rightarrow>X)"

text\<open>The set of nonempty $X$-value listst will be called \<open>NELists(X)\<close>.\<close>

definition
  "NELists(X) \<equiv> \<Union>n\<in>nat.(succ(n)\<rightarrow>X)"

text\<open>We first define the shift that moves the second sequence
  to the domain $\{n,..,n+k-1\}$, where $n,k$ are the lengths of the first 
  and the second sequence, resp.  
  To understand the notation in the definitions below recall that in Isabelle/ZF 
  \<open>pred(n)\<close> is the previous natural number and  
   denotes the difference between natural numbers $n$ and $k$.\<close>

definition
  "ShiftedSeq(b,n) \<equiv> {\<langle>j, b`(j #- n)\<rangle>. j \<in> NatInterval(n,domain(b))}"

text\<open>We define concatenation of two sequences as the union of the first sequence 
  with the shifted second sequence. The result of concatenating lists 
  $a$ and $b$ is called \<open>Concat(a,b)\<close>.\<close>

definition
  "Concat(a,b) \<equiv> a \<union> ShiftedSeq(b,domain(a))"

text\<open>For a finite sequence we define the sequence of all elements 
  except the first one. This corresponds to the "tail" function in Haskell.
  We call it \<open>Tail\<close> here as well.\<close>

definition  
  "Tail(a) \<equiv> {\<langle>k, a`(succ(k))\<rangle>. k \<in> pred(domain(a))}"

text\<open>A dual notion to \<open>Tail\<close> is the list
  of all elements of a list except the last one. Borrowing
  the terminology from Haskell again, we will call this \<open>Init\<close>.\<close>

definition
  "Init(a) \<equiv> restrict(a,pred(domain(a)))"

text\<open>Another obvious operation we can talk about is appending an element
  at the end of a sequence. This is called \<open>Append\<close>.\<close>

definition
  "Append(a,x) \<equiv> a \<union> {\<langle>domain(a),x\<rangle>}"

text\<open>If lists are modeled as finite sequences (i.e. functions on natural 
  intervals $\{0,1,..,n-1\} = n$) it is easy to get the first element
  of a list as the value of the sequence at $0$. The last element is the
  value at $n-1$. To hide this behind a familiar name we define the \<open>Last\<close>
  element of a list.\<close> 

definition
  "Last(a) \<equiv> a`(pred(domain(a)))"

text\<open>Shifted sequence is a function on a the interval of natural numbers.\<close>

lemma shifted_seq_props: 
  assumes A1: "n \<in> nat"  "k \<in> nat" and A2: "b:k\<rightarrow>X"
  shows 
  "ShiftedSeq(b,n): NatInterval(n,k) \<rightarrow> X"
  "\<forall>i \<in> NatInterval(n,k). ShiftedSeq(b,n)`(i) = b`(i #- n)"
  "\<forall>j\<in>k. ShiftedSeq(b,n)`(n #+ j) = b`(j)"   
proof -
  let ?I = "NatInterval(n,domain(b))"
  from A2 have Fact: "?I = NatInterval(n,k)" using func1_1_L1 by simp
  with A1 A2 have "\<forall>j\<in> ?I. b`(j #- n) \<in> X" 
    using inter_diff_in_len apply_funtype by simp
  then have 
    "{\<langle>j, b`(j #- n)\<rangle>. j \<in> ?I} : ?I \<rightarrow> X" by (rule ZF_fun_from_total)
  with Fact show thesis_1: "ShiftedSeq(b,n): NatInterval(n,k) \<rightarrow> X"
    using ShiftedSeq_def by simp
  { fix i 
    from Fact thesis_1 have  "ShiftedSeq(b,n): ?I \<rightarrow> X" by simp
    moreover 
    assume "i \<in> NatInterval(n,k)"
    with Fact have "i \<in> ?I" by simp
    moreover from Fact have 
      "ShiftedSeq(b,n) = {\<langle>i, b`(i #- n)\<rangle>. i \<in> ?I}"
      using ShiftedSeq_def by simp
    ultimately have "ShiftedSeq(b,n)`(i) =  b`(i #- n)"
      by (rule ZF_fun_from_tot_val)
  } then show thesis1: 
      "\<forall>i \<in> NatInterval(n,k). ShiftedSeq(b,n)`(i) = b`(i #- n)"
    by simp
  { fix j 
    let ?i = "n #+ j"
    assume A3: "j\<in>k"
    with A1 have "j \<in> nat" using elem_nat_is_nat by blast
    then have "?i #- n = j" using diff_add_inverse by simp
    with A3 thesis1 have "ShiftedSeq(b,n)`(?i) = b`(j)"
      using NatInterval_def by auto
  } then show "\<forall>j\<in>k. ShiftedSeq(b,n)`(n #+ j) = b`(j)"
    by simp
qed

text\<open>Basis properties of the contatenation of two finite sequences.\<close>

theorem concat_props:
  assumes A1: "n \<in> nat"  "k \<in> nat" and A2: "a:n\<rightarrow>X"   "b:k\<rightarrow>X"
  shows
  "Concat(a,b): n #+ k \<rightarrow> X"
  "\<forall>i\<in>n. Concat(a,b)`(i) = a`(i)"
  "\<forall>i \<in> NatInterval(n,k). Concat(a,b)`(i) =  b`(i #- n)"
  "\<forall>j \<in> k. Concat(a,b)`(n #+ j) = b`(j)"
proof -
  from A1 A2 have
    "a:n\<rightarrow>X"  and I: "ShiftedSeq(b,n): NatInterval(n,k) \<rightarrow> X"
    and "n \<inter> NatInterval(n,k) = 0"
    using shifted_seq_props length_start_decomp by auto
  then have 
    "a \<union> ShiftedSeq(b,n): n \<union> NatInterval(n,k) \<rightarrow> X \<union> X"
    by (rule fun_disjoint_Un)
  with A1 A2 show "Concat(a,b): n #+ k \<rightarrow> X"
    using func1_1_L1 Concat_def length_start_decomp by auto
  { fix i assume "i \<in> n"
    with A1 I have "i \<notin> domain(ShiftedSeq(b,n))"
      using length_start_decomp func1_1_L1 by auto
    with A2 have "Concat(a,b)`(i) = a`(i)"
      using func1_1_L1 fun_disjoint_apply1 Concat_def by simp
  } thus "\<forall>i\<in>n. Concat(a,b)`(i) = a`(i)" by simp
  { fix i assume A3: "i \<in> NatInterval(n,k)"
    with A1 A2 have "i \<notin> domain(a)" 
      using length_start_decomp func1_1_L1 by auto
    with A1 A2 A3 have "Concat(a,b)`(i) =  b`(i #- n)"
      using func1_1_L1 fun_disjoint_apply2 Concat_def shifted_seq_props
      by simp
  } thus II: "\<forall>i \<in> NatInterval(n,k). Concat(a,b)`(i) =  b`(i #- n)"
    by simp
  { fix j
    let ?i = "n #+ j"
    assume A3: "j\<in>k"
    with A1 have "j \<in> nat" using elem_nat_is_nat by blast
    then have "?i #- n = j" using diff_add_inverse by simp
     with A3 II have "Concat(a,b)`(?i) = b`(j)"
      using NatInterval_def by auto
  } thus "\<forall>j \<in> k. Concat(a,b)`(n #+ j) = b`(j)"
    by simp
qed

text\<open>Properties of concatenating three lists.\<close>

lemma concat_concat_list: 
  assumes A1: "n \<in> nat"  "k \<in> nat"  "m \<in> nat" and
  A2: "a:n\<rightarrow>X"   "b:k\<rightarrow>X"  "c:m\<rightarrow>X" and
  A3: "d = Concat(Concat(a,b),c)"
  shows
  "d : n #+k #+ m \<rightarrow> X"
  "\<forall>j \<in> n. d`(j) = a`(j)"
  "\<forall>j \<in> k. d`(n #+ j) = b`(j)"
  "\<forall>j \<in> m. d`(n #+ k #+ j) = c`(j)"
proof -
  from A1 A2 have I:
    "n #+ k \<in> nat"   "m \<in> nat"
    "Concat(a,b): n #+ k \<rightarrow> X"   "c:m\<rightarrow>X"
    using concat_props by auto
  with A3 show "d: n #+k #+ m \<rightarrow> X"
    using concat_props by simp
  from I have II: "\<forall>i \<in> n #+ k. 
    Concat(Concat(a,b),c)`(i) = Concat(a,b)`(i)"
    by (rule concat_props)
  { fix j assume A4: "j \<in> n"
    moreover from A1 have "n \<subseteq> n #+ k" using add_nat_le by simp
    ultimately have "j \<in> n #+ k" by auto
    with A3 II have "d`(j) =  Concat(a,b)`(j)" by simp
    with A1 A2 A4 have "d`(j) = a`(j)"
      using concat_props by simp
  } thus "\<forall>j \<in> n. d`(j) = a`(j)" by simp
  { fix j assume A5: "j \<in> k"
    with A1 A3 II have "d`(n #+ j) = Concat(a,b)`(n #+ j)"
      using add_lt_mono by simp
    also from A1 A2 A5 have "\<dots> = b`(j)"
      using concat_props by simp
    finally have "d`(n #+ j) = b`(j)" by simp
  } thus "\<forall>j \<in> k. d`(n #+ j) = b`(j)" by simp
  from I have "\<forall>j \<in> m. Concat(Concat(a,b),c)`(n #+ k #+ j) = c`(j)"
    by (rule concat_props)
  with A3 show "\<forall>j \<in> m. d`(n #+ k #+ j) = c`(j)"
    by simp
qed

text\<open>Properties of concatenating a list with a concatenation
  of two other lists.\<close>

lemma concat_list_concat: 
  assumes A1: "n \<in> nat"  "k \<in> nat"  "m \<in> nat" and
  A2: "a:n\<rightarrow>X"   "b:k\<rightarrow>X"  "c:m\<rightarrow>X" and
  A3: "e = Concat(a, Concat(b,c))"
  shows 
  "e : n #+k #+ m \<rightarrow> X"
  "\<forall>j \<in> n. e`(j) = a`(j)"
  "\<forall>j \<in> k. e`(n #+ j) = b`(j)"
  "\<forall>j \<in> m. e`(n #+ k #+ j) = c`(j)"
proof -
  from A1 A2 have I: 
    "n \<in> nat"  "k #+ m \<in> nat"
    "a:n\<rightarrow>X"  "Concat(b,c): k #+ m \<rightarrow> X"
    using concat_props by auto
  with A3 show  "e : n #+k #+ m \<rightarrow> X"
    using concat_props add_assoc by simp
  from I have "\<forall>j \<in> n. Concat(a, Concat(b,c))`(j) = a`(j)"
    by (rule concat_props)
  with A3 show "\<forall>j \<in> n. e`(j) = a`(j)" by simp
  from I have II:
    "\<forall>j \<in> k #+ m. Concat(a, Concat(b,c))`(n #+ j) = Concat(b,c)`(j)"
    by (rule concat_props)
  { fix j assume A4: "j \<in> k"
    moreover from A1 have "k \<subseteq> k #+ m" using add_nat_le by simp
    ultimately have "j \<in> k #+ m" by auto
    with A3 II have "e`(n #+ j) =  Concat(b,c)`(j)" by simp
    also from A1 A2 A4 have "\<dots> = b`(j)"
      using concat_props by simp
    finally have "e`(n #+ j) = b`(j)" by simp
  } thus "\<forall>j \<in> k. e`(n #+ j) = b`(j)" by simp
  { fix j assume A5: "j \<in> m"
    with A1 II A3 have "e`(n #+ k #+ j) = Concat(b,c)`(k #+ j)"
      using add_lt_mono add_assoc by simp
    also from A1 A2 A5 have "\<dots> = c`(j)"
      using concat_props by simp
    finally have "e`(n #+ k #+ j) = c`(j)" by simp
  } then show "\<forall>j \<in> m. e`(n #+ k #+ j) = c`(j)"
    by simp
qed

text\<open>Concatenation is associative.\<close>

theorem concat_assoc: 
  assumes A1: "n \<in> nat"  "k \<in> nat"  "m \<in> nat" and
  A2: "a:n\<rightarrow>X"   "b:k\<rightarrow>X"   "c:m\<rightarrow>X"
  shows "Concat(Concat(a,b),c) =  Concat(a, Concat(b,c))"
proof -
  let ?d = "Concat(Concat(a,b),c)"
  let ?e = "Concat(a, Concat(b,c))"
  from A1 A2 have
    "?d : n #+k #+ m \<rightarrow> X" and "?e : n #+k #+ m \<rightarrow> X"
    using concat_concat_list concat_list_concat by auto
  moreover have "\<forall>i \<in>  n #+k #+ m. ?d`(i) = ?e`(i)"
  proof -
    { fix i assume "i \<in> n #+k #+ m"
      moreover from A1 have 
	"n #+k #+ m = n \<union> NatInterval(n,k) \<union> NatInterval(n #+ k,m)"
	using adjacent_intervals3 by simp
      ultimately have 
	"i \<in> n \<or> i \<in> NatInterval(n,k) \<or> i \<in> NatInterval(n #+ k,m)"
	by simp
      moreover
      { assume "i \<in> n"
	with A1 A2 have "?d`(i) = ?e`(i)"
	using concat_concat_list concat_list_concat by simp }
      moreover
      { assume "i \<in> NatInterval(n,k)"
	then obtain j where "j\<in>k" and "i = n #+ j"
	  using NatInterval_def by auto
	with A1 A2 have "?d`(i) = ?e`(i)"
	  using concat_concat_list concat_list_concat by simp }
      moreover
      { assume "i \<in> NatInterval(n #+ k,m)"
	then obtain j where "j \<in> m" and "i = n #+ k #+ j"
	  using NatInterval_def by auto
	with A1 A2 have "?d`(i) = ?e`(i)"
	  using concat_concat_list concat_list_concat by simp }
      ultimately have "?d`(i) = ?e`(i)" by auto
    } thus ?thesis by simp
  qed
  ultimately show "?d = ?e" by (rule func_eq)
qed
    
text\<open>Properties of \<open>Tail\<close>.\<close>

theorem tail_props: 
  assumes A1: "n \<in> nat" and A2: "a: succ(n) \<rightarrow> X"
  shows
  "Tail(a) : n \<rightarrow> X"
  "\<forall>k \<in> n. Tail(a)`(k) = a`(succ(k))"
proof -
  from A1 A2 have "\<forall>k \<in> n. a`(succ(k)) \<in> X"
    using succ_ineq apply_funtype by simp
  then have "{\<langle>k, a`(succ(k))\<rangle>. k \<in> n} : n \<rightarrow> X"
    by (rule ZF_fun_from_total)
  with A2 show I: "Tail(a) : n \<rightarrow> X"
    using func1_1_L1 pred_succ_eq Tail_def by simp
  moreover from A2 have "Tail(a) = {\<langle>k, a`(succ(k))\<rangle>. k \<in> n}"
    using func1_1_L1 pred_succ_eq Tail_def by simp
  ultimately show "\<forall>k \<in> n. Tail(a)`(k) = a`(succ(k))"
    by (rule ZF_fun_from_tot_val0)
qed
  
text\<open>Properties of \<open>Append\<close>. It is a bit surprising that
  the we don't need to assume that $n$ is a natural number.\<close>

theorem append_props:
  assumes A1: "a: n \<rightarrow> X" and A2: "x\<in>X" and A3: "b = Append(a,x)"
  shows 
  "b : succ(n) \<rightarrow> X"
  "\<forall>k\<in>n. b`(k) = a`(k)"
  "b`(n) = x"
proof -
  note A1
  moreover have I: "n \<notin> n" using mem_not_refl by simp
  moreover from A1 A3 have II: "b = a \<union> {\<langle>n,x\<rangle>}"
    using func1_1_L1 Append_def by simp
  ultimately have "b : n \<union> {n} \<rightarrow> X \<union> {x}"
    by (rule func1_1_L11D)
  with A2 show "b : succ(n) \<rightarrow> X"
    using succ_explained set_elem_add by simp
  from A1 I II show "\<forall>k\<in>n. b`(k) = a`(k)" and "b`(n) = x"
    using func1_1_L11D by auto
qed

text\<open>A special case of \<open>append_props\<close>: appending to a nonempty
  list does not change the head (first element) of the list.\<close>

corollary head_of_append: 
  assumes "n\<in> nat" and "a: succ(n) \<rightarrow> X" and "x\<in>X"
  shows "Append(a,x)`(0) = a`(0)"
  using assms append_props empty_in_every_succ by auto

(*text{*A bit technical special case of @{text "append_props"} that tells us
  what is the value of the appended list at the sucessor of some argument.*}

corollary append_val_succ:
  assumes "n \<in> nat" and "a: succ(n) \<rightarrow> X" and "x\<in>X" and "k \<in> n"
  shows "Append(a,x)`(succ(k)) = a`(succ(k))"
  using assms succ_ineq append_props by simp*)

text\<open>\<open>Tail\<close> commutes with \<open>Append\<close>.\<close>

theorem tail_append_commute: 
  assumes A1: "n \<in> nat" and A2: "a: succ(n) \<rightarrow> X" and A3: "x\<in>X"
  shows "Append(Tail(a),x) = Tail(Append(a,x))"
proof -
  let ?b = "Append(Tail(a),x)"
  let ?c = "Tail(Append(a,x))"
  from A1 A2 have I: "Tail(a) : n \<rightarrow> X" using tail_props
    by simp
  from A1 A2 A3 have 
    "succ(n) \<in> nat" and "Append(a,x) : succ(succ(n)) \<rightarrow> X"
    using append_props by auto
  then have II: "\<forall>k \<in> succ(n). ?c`(k) = Append(a,x)`(succ(k))"
    by (rule tail_props)
  from assms have 
    "?b : succ(n) \<rightarrow> X" and "?c : succ(n) \<rightarrow> X"
    using tail_props append_props by auto
  moreover have "\<forall>k \<in> succ(n). ?b`(k) = ?c`(k)"
  proof -
    { fix k assume "k \<in> succ(n)"
      hence "k \<in> n \<or> k = n" by auto
      moreover
      { assume A4: "k \<in> n"
	with assms II have "?c`(k) = a`(succ(k))"
	  using succ_ineq append_props by simp
	moreover
	from A3 I have "\<forall>k\<in>n. ?b`(k) = Tail(a)`(k)"
	  using append_props by simp
	with A1 A2 A4 have "?b`(k) =  a`(succ(k))"
	  using tail_props by simp
	ultimately have "?b`(k) = ?c`(k)" by simp }
      moreover
      { assume A5: "k = n"
	with A2 A3 I II have "?b`(k) = ?c`(k)"
	  using append_props by auto }
      ultimately have "?b`(k) = ?c`(k)" by auto
    } thus ?thesis by simp
  qed
  ultimately show "?b = ?c" by (rule func_eq)
qed  

text\<open>Properties of \<open>Init\<close>.\<close>

theorem init_props: 
  assumes A1: "n \<in> nat" and A2: "a: succ(n) \<rightarrow> X"
  shows 
  "Init(a) : n \<rightarrow> X"
  "\<forall>k\<in>n. Init(a)`(k) = a`(k)"
  "a = Append(Init(a), a`(n))"
proof -
  have "n \<subseteq> succ(n)" by auto
  with A2 have "restrict(a,n): n \<rightarrow> X"
    using restrict_type2 by simp
  moreover from A1 A2 have I: "restrict(a,n) = Init(a)"
    using func1_1_L1 pred_succ_eq Init_def by simp
  ultimately show thesis1: "Init(a) : n \<rightarrow> X" by simp
  { fix k assume "k\<in>n"
    then have "restrict(a,n)`(k) = a`(k)"
      using restrict by simp
    with I have "Init(a)`(k) = a`(k)" by simp
  } then show thesis2: "\<forall>k\<in>n. Init(a)`(k) = a`(k)" by simp
  let ?b = "Append(Init(a), a`(n))"
  from A2 thesis1 have II:
    "Init(a) : n \<rightarrow> X"   "a`(n) \<in> X"
    "?b = Append(Init(a), a`(n))"
    using apply_funtype by auto
  note A2
  moreover from II have "?b : succ(n) \<rightarrow> X"
    by (rule append_props)
  moreover have "\<forall>k \<in> succ(n). a`(k) = ?b`(k)"
  proof -
    { fix k assume A3: "k \<in> n"
      from II have "\<forall>j\<in>n. ?b`(j) = Init(a)`(j)"
	by (rule append_props)
      with thesis2 A3 have "a`(k) = ?b`(k)" by simp }
    moreover 
    from II have "?b`(n) = a`(n)"
      by (rule append_props)
    hence " a`(n) = ?b`(n)" by simp
    ultimately show "\<forall>k \<in> succ(n). a`(k) = ?b`(k)"
      by simp
  qed
  ultimately show "a = ?b" by (rule func_eq)
qed

text\<open>If we take init of the result of append, we get back the same list.\<close> 

lemma init_append: assumes A1: "n \<in> nat" and A2: "a:n\<rightarrow>X" and A3: "x \<in> X"
  shows "Init(Append(a,x)) = a"
proof -
  from A2 A3 have "Append(a,x): succ(n)\<rightarrow>X" using append_props by simp
  with A1 have "Init(Append(a,x)):n\<rightarrow>X" and "\<forall>k\<in>n. Init(Append(a,x))`(k) = Append(a,x)`(k)"  
    using init_props by auto
  with A2 A3 have "\<forall>k\<in>n. Init(Append(a,x))`(k) = a`(k)" using append_props by simp
  with \<open>Init(Append(a,x)):n\<rightarrow>X\<close> A2 show ?thesis by (rule func_eq)
qed

text\<open>A reformulation of definition of  \<open>Init\<close>.\<close>

lemma init_def: assumes "n \<in> nat" and "x:succ(n)\<rightarrow>X"
  shows "Init(x) = restrict(x,n)"
  using assms func1_1_L1 Init_def by simp
    
text\<open>A lemma about extending a finite sequence by one more value. This is 
  just a more explicit version of \<open>append_props\<close>.\<close>

lemma finseq_extend: 
  assumes  "a:n\<rightarrow>X"   "y\<in>X"   "b = a \<union> {\<langle>n,y\<rangle>}"
  shows
  "b: succ(n) \<rightarrow> X"
  "\<forall>k\<in>n. b`(k) = a`(k)"
  "b`(n) = y"
  using assms Append_def func1_1_L1 append_props by auto

text\<open>The next lemma is a bit displaced as it is mainly 
  about finite sets. It is proven here because it uses
  the notion of \<open>Append\<close>.
  Suppose we have a list of element of $A$ is a bijection.
  Then for every element that does not belong to $A$ 
  we can we can construct 
  a bijection for the set $A \cup \{ x\}$ by appending $x$.
  This is just a specialised version of lemma \<open>bij_extend_point\<close>
  from \<open>func1.thy\<close>.
\<close>

lemma bij_append_point: 
  assumes A1: "n \<in> nat" and A2: "b \<in> bij(n,X)" and A3: "x \<notin> X"
  shows "Append(b,x) \<in> bij(succ(n), X \<union> {x})"
proof -
  from A2 A3 have "b \<union> {\<langle>n,x\<rangle>} \<in> bij(n \<union> {n},X \<union> {x})"
    using mem_not_refl bij_extend_point by simp
  moreover have "Append(b,x) = b \<union> {\<langle>n,x\<rangle>}"
  proof -
    from A2 have "b:n\<rightarrow>X"
      using bij_def surj_def by simp
    then have "b : n \<rightarrow> X \<union> {x}" using func1_1_L1B
      by blast
    then show "Append(b,x) = b \<union> {\<langle>n,x\<rangle>}"
      using Append_def func1_1_L1 by simp
  qed
  ultimately show ?thesis using succ_explained by auto
qed


text\<open>The next lemma rephrases the definition of \<open>Last\<close>.
  Recall that in ZF we have $\{0,1,2,..,n\} = n+1=$\<open>succ\<close>$(n)$.\<close>

lemma last_seq_elem: assumes "a: succ(n) \<rightarrow> X" shows "Last(a) = a`(n)"
  using assms func1_1_L1 pred_succ_eq Last_def by simp


text\<open>If two finite sequences are the same when restricted to domain one 
  shorter than the original and have the same value on the last element, 
  then they are equal.\<close>

lemma finseq_restr_eq: assumes A1: "n \<in> nat" and 
  A2: "a: succ(n) \<rightarrow> X"  "b: succ(n) \<rightarrow> X" and
  A3: "restrict(a,n) = restrict(b,n)" and
  A4: "a`(n) = b`(n)"
  shows "a = b"
proof -
  { fix k assume "k \<in> succ(n)"
    then have "k \<in> n \<or> k = n" by auto
    moreover
    { assume "k \<in> n"  
      then have 
	"restrict(a,n)`(k) = a`(k)" and "restrict(b,n)`(k) = b`(k)"
	using restrict by auto
      with A3 have "a`(k) = b`(k)" by simp }
    moreover
    { assume "k = n"
      with A4 have "a`(k) = b`(k)" by simp }
    ultimately have "a`(k) = b`(k)" by auto
  } then have "\<forall> k \<in> succ(n). a`(k) = b`(k)" by simp
  with A2 show "a = b" by (rule func_eq)
qed

text\<open>Concatenating a list of length $1$ is the same as appending its
  first (and only) element. Recall that in ZF set theory 
  $1 = \{ 0 \} $.\<close>

lemma append_1elem: assumes A1: "n \<in> nat" and 
  A2: "a: n \<rightarrow> X"  and A3: "b : 1 \<rightarrow> X"
  shows "Concat(a,b) = Append(a,b`(0))"
proof -
  let ?C = "Concat(a,b)"
  let ?A = "Append(a,b`(0))"
  from A1 A2 A3 have I:
    "n \<in> nat"  "1 \<in> nat"
    "a:n\<rightarrow>X"   "b:1\<rightarrow>X" by auto
  have "?C : succ(n) \<rightarrow> X"
  proof -
    from I have "?C : n #+ 1 \<rightarrow> X"
      by (rule concat_props)
    with A1 show "?C : succ(n) \<rightarrow> X" by simp
  qed
  moreover from A2 A3 have "?A : succ(n) \<rightarrow> X"
    using apply_funtype append_props by simp
  moreover have "\<forall>k \<in> succ(n). ?C`(k) = ?A`(k)"
  proof
    fix k assume "k \<in> succ(n)"
    moreover
    { assume "k \<in> n"
      moreover from I have "\<forall>i \<in> n. ?C`(i) = a`(i)"
	by (rule concat_props)
      moreover from A2 A3 have "\<forall>i\<in>n. ?A`(i) = a`(i)"
	using apply_funtype append_props by simp
      ultimately have "?C`(k) =  ?A`(k)" by simp }
    moreover have "?C`(n) = ?A`(n)"
    proof -
      from I have "\<forall>j \<in> 1. ?C`(n #+ j) = b`(j)"
	by (rule concat_props)
      with A1 A2 A3 show "?C`(n) = ?A`(n)"
	using apply_funtype append_props by simp
    qed
    ultimately show "?C`(k) = ?A`(k)" by auto
  qed
  ultimately show "?C = ?A" by (rule func_eq)
qed

text\<open>A simple lemma about lists of length $1$.\<close>

lemma list_len1_singleton: assumes A1: "x\<in>X" 
  shows "{\<langle>0,x\<rangle>} : 1 \<rightarrow> X"
proof -
  from A1 have "{\<langle>0,x\<rangle>} : {0} \<rightarrow> X" using pair_func_singleton
    by simp
  moreover have "{0} = 1" by auto
  ultimately show ?thesis by simp
qed

text\<open>A singleton list is in fact a singleton set with a pair as the only element.\<close>

lemma list_singleton_pair: assumes A1: "x:1\<rightarrow>X" shows "x = {\<langle>0,x`(0)\<rangle>}"
proof -
  from A1 have "x = {\<langle>t,x`(t)\<rangle>. t\<in>1}" by (rule fun_is_set_of_pairs)
  hence "x = {\<langle>t,x`(t)\<rangle>. t\<in>{0} }" by simp
  thus ?thesis by simp
qed  
 
text\<open>When we append an element to the empty list we get
  a list with length $1$.\<close>

lemma empty_append1: assumes A1: "x\<in>X"
  shows "Append(0,x): 1 \<rightarrow> X" and "Append(0,x)`(0) = x"
proof -
  let ?a = "Append(0,x)"
  have "?a = {\<langle>0,x\<rangle>}" using Append_def by auto
  with A1 show "?a : 1 \<rightarrow> X" and "?a`(0) = x"
    using list_len1_singleton pair_func_singleton
    by auto
qed
  
(*text{*Tail of a list of length 1 is a list of length 0.*}

lemma list_len1_tail: assumes "a:1\<rightarrow>X"
  shows "Tail(a) : 0 \<rightarrow> X"
  using assms tail_props by blast *)

text\<open>Appending an element is the same as concatenating
  with certain pair.\<close>

lemma append_concat_pair: 
  assumes "n \<in> nat" and "a: n \<rightarrow> X" and "x\<in>X"
  shows "Append(a,x) = Concat(a,{\<langle>0,x\<rangle>})"
  using assms list_len1_singleton append_1elem pair_val
  by simp

text\<open>An associativity property involving concatenation 
  and appending. For proof we just convert appending to
  concatenation and use \<open>concat_assoc\<close>.\<close>

lemma concat_append_assoc: assumes A1: "n \<in> nat"  "k \<in> nat" and 
  A2: "a:n\<rightarrow>X"   "b:k\<rightarrow>X" and A3: "x \<in> X"
  shows "Append(Concat(a,b),x) = Concat(a, Append(b,x))"
proof -
  from A1 A2 A3 have 
    "n #+ k \<in> nat"   "Concat(a,b) : n #+ k \<rightarrow> X"   "x \<in> X"
    using concat_props by auto
  then have 
    "Append(Concat(a,b),x) =  Concat(Concat(a,b),{\<langle>0,x\<rangle>})"
    by (rule append_concat_pair)
  moreover
  from A1 A2 A3 have
    "n \<in> nat"  "k \<in> nat"  "1 \<in> nat"
     "a:n\<rightarrow>X"   "b:k\<rightarrow>X"  "{\<langle>0,x\<rangle>} :  1 \<rightarrow> X"
    using list_len1_singleton by auto
  then have
    "Concat(Concat(a,b),{\<langle>0,x\<rangle>}) = Concat(a, Concat(b,{\<langle>0,x\<rangle>}))"
    by (rule concat_assoc)
  moreover from A1 A2 A3 have "Concat(b,{\<langle>0,x\<rangle>}) =  Append(b,x)"
    using list_len1_singleton append_1elem pair_val by simp
  ultimately show "Append(Concat(a,b),x) = Concat(a, Append(b,x))"
    by simp
qed

text\<open>An identity involving concatenating with init
  and appending the last element.\<close>

lemma concat_init_last_elem: 
  assumes "n \<in> nat"  "k \<in> nat" and 
  "a: n \<rightarrow> X"  and "b : succ(k) \<rightarrow> X"
  shows "Append(Concat(a,Init(b)),b`(k)) = Concat(a,b)"
  using assms init_props apply_funtype concat_append_assoc
  by simp

text\<open>A lemma about creating lists by composition and how
  \<open>Append\<close> behaves in such case.\<close>

lemma list_compose_append: 
  assumes A1: "n \<in> nat" and A2: "a : n \<rightarrow> X" and 
  A3: "x \<in> X" and A4: "c : X \<rightarrow> Y"
  shows
  "c O Append(a,x) : succ(n) \<rightarrow> Y"
  "c O Append(a,x) = Append(c O a, c`(x))"
proof -
  let ?b = "Append(a,x)"
  let ?d = "Append(c O a, c`(x))"
  from A2 A4 have "c O a : n \<rightarrow> Y"
    using comp_fun by simp
  from A2 A3 have "?b : succ(n) \<rightarrow> X"
    using append_props by simp
  with A4 show "c O ?b : succ(n) \<rightarrow> Y"
    using comp_fun by simp
  moreover from A3 A4 \<open>c O a : n \<rightarrow> Y\<close> have 
    "?d: succ(n) \<rightarrow> Y"
    using apply_funtype append_props by simp
  moreover have "\<forall>k \<in> succ(n). (c O ?b) `(k) = ?d`(k)"
  proof -
    { fix k assume "k \<in> succ(n)"
      with \<open>?b : succ(n) \<rightarrow> X\<close> have 
	"(c O ?b) `(k) = c`(?b`(k))"
	using comp_fun_apply by simp
      with A2 A3 A4 \<open>c O a : n \<rightarrow> Y\<close> \<open>c O a : n \<rightarrow> Y\<close> \<open>k \<in> succ(n)\<close>
      have "(c O ?b) `(k) = ?d`(k)"
	using append_props comp_fun_apply apply_funtype
	by auto
    } thus ?thesis by simp
  qed
  ultimately show "c O ?b = ?d" by (rule func_eq)
qed

text\<open>A lemma about appending an element to a list defined by set
  comprehension.\<close>

lemma set_list_append:  assumes 
  A1: "\<forall>i \<in> succ(k). b(i) \<in> X" and
  A2: "a = {\<langle>i,b(i)\<rangle>. i \<in> succ(k)}"
  shows 
  "a: succ(k) \<rightarrow> X"
  "{\<langle>i,b(i)\<rangle>. i \<in> k}: k \<rightarrow> X" 
  "a = Append({\<langle>i,b(i)\<rangle>. i \<in> k},b(k))"
proof -
  from A1 have "{\<langle>i,b(i)\<rangle>. i \<in> succ(k)} : succ(k) \<rightarrow> X" 
    by (rule ZF_fun_from_total)
  with A2 show "a: succ(k) \<rightarrow> X" by simp
  from A1 have "\<forall>i \<in> k. b(i) \<in> X"
    by simp
  then show "{\<langle>i,b(i)\<rangle>. i \<in> k}: k \<rightarrow> X"
    by (rule ZF_fun_from_total)
  with A2 show "a = Append({\<langle>i,b(i)\<rangle>. i \<in> k},b(k))"
    using func1_1_L1 Append_def by auto
qed

text\<open>An induction theorem for lists.\<close>

lemma list_induct: assumes A1: "\<forall>b\<in>1\<rightarrow>X. P(b)" and 
  A2: "\<forall>b\<in>NELists(X). P(b) \<longrightarrow> (\<forall>x\<in>X. P(Append(b,x)))" and
  A3: "d \<in> NELists(X)"
  shows "P(d)"
proof -
  { fix n 
    assume "n\<in>nat"
    moreover from A1 have "\<forall>b\<in>succ(0)\<rightarrow>X. P(b)" by simp 
    moreover have "\<forall>k\<in>nat. ((\<forall>b\<in>succ(k)\<rightarrow>X. P(b)) \<longrightarrow> (\<forall>c\<in>succ(succ(k))\<rightarrow>X. P(c)))"
    proof -
      { fix k assume "k \<in> nat" assume "\<forall>b\<in>succ(k)\<rightarrow>X. P(b)"
        have "\<forall>c\<in>succ(succ(k))\<rightarrow>X. P(c)"
        proof
          fix c assume "c: succ(succ(k))\<rightarrow>X"
          let ?b = "Init(c)"
          let ?x = "c`(succ(k))"
          from \<open>k \<in> nat\<close> \<open>c: succ(succ(k))\<rightarrow>X\<close> have "?b:succ(k)\<rightarrow>X"
            using init_props by simp
          with A2 \<open>k \<in> nat\<close> \<open>\<forall>b\<in>succ(k)\<rightarrow>X. P(b)\<close> have "\<forall>x\<in>X. P(Append(?b,x))"
            using NELists_def by auto 
          with \<open>c: succ(succ(k))\<rightarrow>X\<close> have "P(Append(?b,?x))" using apply_funtype by simp 
          with \<open>k \<in> nat\<close> \<open>c: succ(succ(k))\<rightarrow>X\<close> show "P(c)"
            using init_props by simp 
        qed
      } thus ?thesis by simp 
    qed
    ultimately have "\<forall>b\<in>succ(n)\<rightarrow>X. P(b)" by (rule ind_on_nat)
  } with A3 show ?thesis using NELists_def by auto 
qed

subsection\<open>Lists and cartesian products\<close>

text\<open>Lists of length $n$ of elements of some set $X$ can be thought of as a 
model of the cartesian product $X^n$ which is more convenient in many applications.\<close>

text\<open>There is a natural bijection between the space $(n+1)\rightarrow X$ of lists of length 
$n+1$ of elements of $X$ and the cartesian product $(n\rightarrow X)\times X$.\<close>

lemma lists_cart_prod: assumes "n \<in> nat"
  shows "{\<langle>x,\<langle>Init(x),x`(n)\<rangle>\<rangle>. x \<in> succ(n)\<rightarrow>X} \<in> bij(succ(n)\<rightarrow>X,(n\<rightarrow>X)\<times>X)"
proof -
  let ?f = "{\<langle>x,\<langle>Init(x),x`(n)\<rangle>\<rangle>. x \<in> succ(n)\<rightarrow>X}"
  from assms have "\<forall>x \<in> succ(n)\<rightarrow>X. \<langle>Init(x),x`(n)\<rangle> \<in> (n\<rightarrow>X)\<times>X"
    using init_props succ_iff apply_funtype by simp
  then have I: "?f: (succ(n)\<rightarrow>X)\<rightarrow>((n\<rightarrow>X)\<times>X)" by (rule ZF_fun_from_total)
  moreover from assms I have "\<forall>x\<in>succ(n)\<rightarrow>X.\<forall>y\<in>succ(n)\<rightarrow>X. ?f`(x)=?f`(y) \<longrightarrow> x=y"
    using ZF_fun_from_tot_val init_def finseq_restr_eq by auto
  moreover have "\<forall>p\<in>(n\<rightarrow>X)\<times>X.\<exists>x\<in>succ(n)\<rightarrow>X. ?f`(x) = p"
  proof
    fix p assume "p \<in> (n\<rightarrow>X)\<times>X"
    let ?x = "Append(fst(p),snd(p))"
    from assms \<open>p \<in> (n\<rightarrow>X)\<times>X\<close> have "?x:succ(n)\<rightarrow>X" using append_props by simp
    with I have "?f`(?x) = \<langle>Init(?x),?x`(n)\<rangle>" using succ_iff ZF_fun_from_tot_val by simp
    moreover from assms \<open>p \<in> (n\<rightarrow>X)\<times>X\<close> have "Init(?x) = fst(p)" and "?x`(n) = snd(p)"
      using init_append append_props by auto
    ultimately have "?f`(?x) = \<langle>fst(p),snd(p)\<rangle>" by auto
    with \<open>p \<in> (n\<rightarrow>X)\<times>X\<close> \<open>?x:succ(n)\<rightarrow>X\<close> show "\<exists>x\<in>succ(n)\<rightarrow>X. ?f`(x) = p" by auto
  qed
  ultimately show ?thesis using inj_def surj_def bij_def by auto
qed

text\<open>We can identify a set $X$ with lists of length one of elements of $X$.\<close>

lemma singleton_list_bij: shows "{\<langle>x,x`(0)\<rangle>. x\<in>1\<rightarrow>X} \<in> bij(1\<rightarrow>X,X)"
proof -
  let ?f = "{\<langle>x,x`(0)\<rangle>. x\<in>1\<rightarrow>X}"
  have "\<forall>x\<in>1\<rightarrow>X. x`(0) \<in> X" using apply_funtype by simp
  then have I: "?f:(1\<rightarrow>X)\<rightarrow>X" by (rule ZF_fun_from_total)
  moreover have "\<forall>x\<in>1\<rightarrow>X.\<forall>y\<in>1\<rightarrow>X. ?f`(x) = ?f`(y) \<longrightarrow> x=y"
  proof -
    { fix x y
      assume "x:1\<rightarrow>X" "y:1\<rightarrow>X" and "?f`(x) = ?f`(y)"  
      with I have "x`(0) = y`(0)" using ZF_fun_from_tot_val by auto
      moreover from \<open>x:1\<rightarrow>X\<close> \<open>y:1\<rightarrow>X\<close> have "x = {\<langle>0,x`(0)\<rangle>}" and "y = {\<langle>0,y`(0)\<rangle>}" 
        using list_singleton_pair by auto
      ultimately have "x=y" by simp 
    } thus ?thesis by auto 
  qed
  moreover have "\<forall>y\<in>X. \<exists>x\<in>1\<rightarrow>X. ?f`(x)=y"
  proof
    fix y assume "y\<in>X"
    let ?x = "{\<langle>0,y\<rangle>}"
    from I \<open>y\<in>X\<close> have "?x:1\<rightarrow>X" and "?f`(?x) = y" 
      using list_len1_singleton ZF_fun_from_tot_val pair_val by auto 
    thus "\<exists>x\<in>1\<rightarrow>X. ?f`(x)=y" by auto
  qed
  ultimately show ?thesis using inj_def surj_def bij_def by simp 
qed

text\<open>We can identify a set of $X$-valued lists of length with $X$.\<close>

lemma list_singleton_bij: shows 
  "{\<langle>x,{\<langle>0,x\<rangle>}\<rangle>.x\<in>X} \<in> bij(X,1\<rightarrow>X)" and 
  "{\<langle>y,y`(0)\<rangle>. y\<in>1\<rightarrow>X} = converse({\<langle>x,{\<langle>0,x\<rangle>}\<rangle>.x\<in>X})" and
  "{\<langle>x,{\<langle>0,x\<rangle>}\<rangle>.x\<in>X} = converse({\<langle>y,y`(0)\<rangle>. y\<in>1\<rightarrow>X})"
proof -
  let ?f = "{\<langle>y,y`(0)\<rangle>. y\<in>1\<rightarrow>X}"
  let ?g = "{\<langle>x,{\<langle>0,x\<rangle>}\<rangle>.x\<in>X}"
  have "1 = {0}" by auto
  then have "?f \<in> bij(1\<rightarrow>X,X)" and "?g:X\<rightarrow>(1\<rightarrow>X)" 
    using singleton_list_bij pair_func_singleton ZF_fun_from_total  
    by auto
  moreover have "\<forall>y\<in>1\<rightarrow>X.?g`(?f`(y)) = y"
  proof
    fix y assume "y:1\<rightarrow>X"
    have "?f:(1\<rightarrow>X)\<rightarrow>X" using singleton_list_bij bij_def inj_def by simp
    with \<open>1 = {0}\<close> \<open>y:1\<rightarrow>X\<close> \<open>?g:X\<rightarrow>(1\<rightarrow>X)\<close> show "?g`(?f`(y)) = y" 
      using ZF_fun_from_tot_val apply_funtype func_singleton_pair
      by simp 
  qed
  ultimately show "?g \<in> bij(X,1\<rightarrow>X)" and "?f = converse(?g)" and "?g = converse(?f)"
    using comp_conv_id by auto
qed 

text\<open>What is the inverse image of a set by the natural bijection between $X$-valued 
  singleton lists and $X$?\<close>

lemma singleton_vimage: assumes "U\<subseteq>X" shows "{x\<in>1\<rightarrow>X. x`(0) \<in> U} = { {\<langle>0,y\<rangle>}. y\<in>U}"
proof
  have "1 = {0}" by auto 
  { fix x assume "x \<in> {x\<in>1\<rightarrow>X. x`(0) \<in> U}"
    with \<open>1 = {0}\<close> have "x = {\<langle>0, x`(0)\<rangle>}" using func_singleton_pair by auto   
  } thus "{x\<in>1\<rightarrow>X. x`(0) \<in> U} \<subseteq> { {\<langle>0,y\<rangle>}. y\<in>U}" by auto
  { fix x assume "x \<in> { {\<langle>0,y\<rangle>}. y\<in>U}"
    then obtain y where "x = {\<langle>0,y\<rangle>}" and "y\<in>U" by auto
    with \<open>1 = {0}\<close> assms have "x:1\<rightarrow>X" using pair_func_singleton by auto
  } thus "{ {\<langle>0,y\<rangle>}. y\<in>U} \<subseteq> {x\<in>1\<rightarrow>X. x`(0) \<in> U}" by auto
qed

text\<open>A technical lemma about extending a list by values from a set.\<close> 

lemma list_append_from: assumes A1: "n \<in> nat" and A2: "U \<subseteq> n\<rightarrow>X" and A3: "V \<subseteq> X"
  shows 
  "{x \<in> succ(n)\<rightarrow>X. Init(x) \<in> U \<and> x`(n) \<in> V} = (\<Union>y\<in>V.{Append(x,y).x\<in>U})"
proof -
  { fix x assume "x \<in> {x \<in> succ(n)\<rightarrow>X. Init(x) \<in> U \<and> x`(n) \<in> V}"
    then have "x \<in> succ(n)\<rightarrow>X" and "Init(x) \<in> U" and I: "x`(n) \<in> V"
      by auto
    let ?y = "x`(n)"
    from A1 and \<open>x \<in> succ(n)\<rightarrow>X\<close>  have "x = Append(Init(x),?y)"
      using init_props by simp
    with I and \<open>Init(x) \<in> U\<close> have "x \<in> (\<Union>y\<in>V.{Append(a,y).a\<in>U})" by auto
  }
  moreover
  { fix x assume "x \<in> (\<Union>y\<in>V.{Append(a,y).a\<in>U})"
    then obtain a y where "y\<in>V" and "a\<in>U" and "x = Append(a,y)" by auto
    with A2 A3 have "x: succ(n)\<rightarrow>X" using append_props by blast 
    from A2 A3 \<open>y\<in>V\<close> \<open>a\<in>U\<close> have "a:n\<rightarrow>X" and "y\<in>X" by auto
    with A1 \<open>a\<in>U\<close>  \<open>y\<in>V\<close> \<open>x = Append(a,y)\<close> have "Init(x) \<in> U" and  "x`(n) \<in> V"
      using append_props init_append by auto    
    with \<open>x: succ(n)\<rightarrow>X\<close> have "x \<in> {x \<in> succ(n)\<rightarrow>X. Init(x) \<in> U \<and> x`(n) \<in> V}"
      by auto
  }
  ultimately show ?thesis by blast
qed

end