(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open>Natural numbers in IsarMathLib\<close>

theory Nat_ZF_IML imports ZF.Arith

begin

text\<open>The  ZF set theory constructs natural numbers from the empty set
  and the notion of a one-element set. Namely, zero of natural numbers
  is defined as the empty set. For each natural number $n$ the next natural
  number is defined as $n\cup \{n\}$. With this definition for every
  non-zero natural number we get the identity $n = \{0,1,2,..,n-1\}$.
  It is good to remember that when we see an expression like
  $f: n \rightarrow X$. Also, with this definition 
  the relation "less or equal than" becomes "$\subseteq$" and 
  the relation "less than" becomes "$\in$".
\<close>

subsection\<open>Induction\<close>

text\<open>The induction lemmas in the standard Isabelle's Nat.thy file like 
  for example \<open>nat_induct\<close> require the induction step to 
  be a higher order 
  statement (the one that uses the $\Longrightarrow$ sign). I found it 
  difficult to apply from Isar, which is perhaps more of an indication of 
  my Isar skills than anything else. Anyway, here we provide a first order
  version that is easier to reference in Isar declarative style proofs.\<close>

text\<open>The next theorem is a version of induction on natural numbers
  that I was thought in school.\<close>

theorem ind_on_nat: 
  assumes A1: "n\<in>nat" and A2: "P(0)" and A3: "\<forall>k\<in>nat. P(k)\<longrightarrow>P(succ(k))"
  shows "P(n)"
proof -
  note A1 A2
  moreover
  { fix x
    assume "x\<in>nat"  "P(x)"
    with A3 have "P(succ(x))" by simp }
  ultimately show  "P(n)" by (rule nat_induct)
qed

text\<open>A nonzero natural number has a predecessor.\<close>

lemma Nat_ZF_1_L3: assumes A1: "n \<in> nat" and A2: "n\<noteq>0"
  shows "\<exists>k\<in>nat. n = succ(k)"
proof -
  from A1 have "n \<in> {0} \<union> {succ(k). k\<in>nat}"
    using nat_unfold by simp
  with A2 show ?thesis by simp
qed

text\<open>What is \<open>succ\<close>, anyway? It's a union with the singleton of the set.\<close>

lemma succ_explained: shows "succ(n) = n \<union> {n}"
  using succ_iff by auto

text\<open>The singleton containing the empty set is a natural number.\<close>

lemma one_is_nat: shows "{0} \<in> nat" "{0} = succ(0)" "{0} = 1"
proof -
  show "{0} = succ(0)" using succ_explained by simp
  then show "{0} \<in> nat" by simp
  show "{0}=1" by blast
qed

text\<open>If $k$ is a member of $succ(n)$ but is not $n$, then it must be the member of $n$.\<close>

lemma mem_succ_not_eq: assumes "k\<in>succ(n)" "k\<noteq>n"
  shows "k\<in>n" using assms succ_explained by simp

text\<open>Empty set is an element of every natural number which is not zero.\<close>

lemma empty_in_every_succ: assumes A1: "n \<in> nat"
  shows "0 \<in> succ(n)"
proof -
  note A1
  moreover have "0 \<in> succ(0)" by simp
  moreover
  { fix k assume "k \<in> nat" and A2: "0 \<in> succ(k)"
    then have "succ(k) \<subseteq> succ(succ(k))" by auto
    with A2 have "0 \<in> succ(succ(k))" by auto
  } then have "\<forall>k \<in> nat. 0 \<in> succ(k) \<longrightarrow> 0 \<in> succ(succ(k))"
    by simp
  ultimately show "0 \<in> succ(n)" by (rule ind_on_nat)
qed

text\<open>A more direct way of stating that empty set is an element of every non-zero natural number:\<close>

lemma empty_in_non_empty: assumes "n\<in>nat" "n\<noteq>0"
  shows "0\<in>n"
  using assms Nat_ZF_1_L3 empty_in_every_succ by auto

text\<open>If one natural number is less than another then their successors
  are in the same relation.\<close>

lemma succ_ineq: assumes A1: "n \<in> nat"
  shows "\<forall>i \<in> n. succ(i) \<in> succ(n)"
proof -
  note A1
  moreover have "\<forall>k \<in> 0. succ(k) \<in> succ(0)" by simp 
  moreover
  { fix k assume A2: "\<forall>i\<in>k. succ(i) \<in> succ(k)"
    { fix i assume "i \<in> succ(k)"
      then have "i \<in> k \<or> i = k" by auto
      moreover
      { assume "i\<in>k"
	with A2 have "succ(i) \<in> succ(k)" by simp
	hence "succ(i) \<in> succ(succ(k))" by auto }
      moreover
      { assume "i = k"
	then have "succ(i) \<in> succ(succ(k))" by auto }
      ultimately have "succ(i) \<in> succ(succ(k))" by auto
    } then have "\<forall>i \<in> succ(k). succ(i) \<in> succ(succ(k))"
      by simp
  } then have "\<forall>k \<in> nat. 
      ( (\<forall>i\<in>k. succ(i) \<in> succ(k)) \<longrightarrow> (\<forall>i \<in> succ(k). succ(i) \<in> succ(succ(k))) )"
    by simp
  ultimately show "\<forall>i \<in> n. succ(i) \<in> succ(n)" by (rule ind_on_nat)
qed

text\<open>A version of \<open>succ_ineq\<close> without a quantifier.\<close>

lemma succ_ineq1:  assumes A1: "n \<in> nat" "i\<in>n"
  shows "succ(i) \<in> succ(n)" using assms succ_ineq by simp

text\<open>For natural numbers if $k\subseteq n$ the similar holds for 
  their successors.\<close>

lemma succ_subset: assumes A1: "k \<in> nat"  "n \<in> nat" and A2: "k\<subseteq>n" 
  shows "succ(k) \<subseteq> succ(n)"
proof -
  from A1 have T: "Ord(k)" and "Ord(n)"
    using nat_into_Ord by auto
  with A2 have "succ(k) \<le> succ(n)"
    using subset_imp_le by simp
  then show "succ(k) \<subseteq> succ(n)" using le_imp_subset
    by simp
qed

text\<open>For any two natural numbers one of them is contained in the other.\<close>

lemma nat_incl_total: assumes A1: "i \<in> nat"  "j \<in> nat"
  shows "i \<subseteq> j \<or> j \<subseteq> i"
proof -
  from A1 have T: "Ord(i)"   "Ord(j)" 
    using nat_into_Ord by auto
  then have "i\<in>j \<or> i=j \<or> j\<in>i" using Ord_linear
    by simp
  moreover
  { assume "i\<in>j"
    with T have "i\<subseteq>j \<or> j\<subseteq>i"
      using lt_def leI le_imp_subset by simp }
  moreover
  { assume "i=j"
    then have "i\<subseteq>j \<or> j\<subseteq>i" by simp }
  moreover
  { assume "j\<in>i"
    with T have "i\<subseteq>j \<or> j\<subseteq>i" 
      using lt_def leI  le_imp_subset by simp }
  ultimately show "i \<subseteq> j \<or> j \<subseteq> i" by auto
qed

text\<open>The set of natural numbers is the union of all successors of natural
  numbers.\<close>

lemma nat_union_succ: shows "nat = (\<Union>n \<in> nat. succ(n))"
proof
  show "nat \<subseteq> (\<Union>n \<in> nat. succ(n))" by auto
next
  { fix k assume A2: "k \<in> (\<Union>n \<in> nat. succ(n))"
    then obtain n where T: "n \<in> nat" and I: "k \<in> succ(n)"
      by auto
    then have "k \<le> n" using nat_into_Ord lt_def
      by simp
    with T have "k \<in> nat" using le_in_nat by simp
  } then show  "(\<Union>n \<in> nat. succ(n)) \<subseteq> nat" by auto
qed

text\<open>Successors of natural numbers are subsets of the 
  set of natural numbers.\<close>

lemma succnat_subset_nat: assumes A1: "n \<in> nat" shows "succ(n) \<subseteq> nat"
proof -
  from A1 have "succ(n) \<subseteq> (\<Union>n \<in> nat. succ(n))" by auto
  then show "succ(n) \<subseteq> nat" using nat_union_succ by simp
qed

text\<open>Element $k$ of a natural number $n$ is a natural number that is smaller than $n$.\<close>

lemma elem_nat_is_nat: assumes A1: "n \<in> nat"  and A2: "k\<in>n"
  shows "k < n"  "k \<in> nat"  "k \<le> n"  "\<langle>k,n\<rangle> \<in> Le"
proof -
  from A1 A2 show "k < n" using nat_into_Ord lt_def by simp
  with A1 show "k \<in> nat" using lt_nat_in_nat by simp
  from \<open>k < n\<close> show "k \<le> n" using leI by simp
  with A1 \<open>k \<in> nat\<close> show "\<langle>k,n\<rangle> \<in> Le" using Le_def
    by simp
qed

text\<open>For natural numbers membership and inequality are the same
  and $k \leq n$ is the same as $k \in \textrm{succ}(n)$. 
  The proof relies on lemmas in the standard Isabelle's \<open>Nat\<close> and \<open>Ordinal\<close> theories. \<close>

lemma nat_mem_lt: assumes "n\<in>nat" 
  shows "k<n \<longleftrightarrow> k\<in>n" and "k\<le>n \<longleftrightarrow> k \<in> succ(n)"
  using assms nat_into_Ord Ord_mem_iff_lt by auto

text\<open>The term $k \leq n$ is the same as $k < \textrm{succ}(n)$.  \<close>

lemma leq_mem_succ: shows "k\<le>n \<longleftrightarrow> k < succ(n)" by simp

text\<open>If the successor of a natural number $k$ is an element of the successor
  of $n$ then a similar relations holds for the numbers themselves.\<close>

lemma succ_mem: 
  assumes "n \<in> nat" "succ(k) \<in> succ(n)"
  shows "k\<in>n"
  using assms elem_nat_is_nat(1) succ_leE nat_into_Ord 
    unfolding lt_def by blast

text\<open>The set of natural numbers is the union of its elements.\<close>

lemma nat_union_nat: shows "nat = \<Union> nat"
  using elem_nat_is_nat by blast

text\<open>A natural number is a subset of the set of natural numbers.\<close>

lemma nat_subset_nat: assumes A1: "n \<in> nat" shows "n \<subseteq> nat"
proof -
  from A1 have "n \<subseteq> \<Union> nat" by auto
  then show "n \<subseteq> nat" using nat_union_nat by simp
qed

text\<open>Adding natural numbers does not decrease what we add to.\<close>

lemma add_nat_le: assumes A1: "n \<in> nat"  and A2: "k \<in> nat"
  shows 
  "n \<le> n #+ k"
  "n \<subseteq> n #+ k"
  "n \<subseteq> k #+ n"
proof -
  from A1 A2 have "n \<le> n"  "0 \<le> k"  "n \<in> nat"  "k \<in> nat"
    using nat_le_refl nat_0_le by auto
  then have "n #+ 0 \<le> n #+ k" by (rule add_le_mono)
  with A1 show "n \<le> n #+ k" using add_0_right by simp
  then show "n \<subseteq> n #+ k" using le_imp_subset by simp
  then show "n \<subseteq> k #+ n" using add_commute by simp
qed

text\<open>Result of adding an element of $k$ is smaller than of adding $k$.\<close>

lemma add_lt_mono: 
  assumes "k \<in> nat" and "j\<in>k"
  shows 
  "(n #+ j) < (n #+ k)"
  "(n #+ j) \<in> (n #+ k)"
proof -
  from assms have "j < k" using elem_nat_is_nat by blast
  moreover note \<open>k \<in> nat\<close>
  ultimately show "(n #+ j) < (n #+ k)"   "(n #+ j) \<in> (n #+ k)"
    using add_lt_mono2 ltD by auto
qed

text\<open>A technical lemma about a decomposition of a sum of two natural
  numbers: if a number $i$ is from $m + n$ then it is either from $m$
  or can be written as a sum of $m$ and a number from $n$. 
  The proof by induction w.r.t. to $m$ seems to be a bit heavy-handed, but I could
  not figure out how to do this directly from results from standard Isabelle/ZF.\<close>

lemma nat_sum_decomp: assumes A1: "n \<in> nat"  and A2: "m \<in> nat"
  shows "\<forall>i \<in> m #+ n. i \<in> m \<or> (\<exists>j \<in> n. i = m #+ j)" 
proof -
  note A1
  moreover from A2 have "\<forall>i \<in> m #+ 0. i \<in> m \<or> (\<exists>j \<in> 0. i = m #+ j)"
    using add_0_right by simp
  moreover have "\<forall>k\<in>nat.
    (\<forall>i \<in> m #+ k. i \<in> m \<or> (\<exists>j \<in> k. i = m #+ j)) \<longrightarrow>
    (\<forall>i \<in> m #+ succ(k). i \<in> m \<or> (\<exists>j \<in> succ(k). i = m #+ j))"
  proof -
    { fix k assume A3: "k \<in> nat"
      { assume A4: "\<forall>i \<in> m #+ k. i \<in> m \<or> (\<exists>j \<in> k. i = m #+ j)"
	  { fix i assume "i \<in>  m #+ succ(k)"
	    then have "i \<in> m #+ k \<or> i = m #+ k" using add_succ_right
	      by auto
	    moreover from A4 A3 have
	      "i \<in> m #+ k \<longrightarrow> i \<in> m \<or> (\<exists>j \<in> succ(k). i = m #+ j)"
	      by auto
	    ultimately have "i \<in> m \<or> (\<exists>j \<in> succ(k). i = m #+ j)"
	      by auto
	  } then have "\<forall>i \<in> m #+ succ(k). i \<in> m \<or> (\<exists>j \<in> succ(k). i = m #+ j)"
	    by simp
      } then have "(\<forall>i \<in> m #+ k. i \<in> m \<or> (\<exists>j \<in> k. i = m #+ j)) \<longrightarrow>
	  (\<forall>i \<in> m #+ succ(k). i \<in> m \<or> (\<exists>j \<in> succ(k). i = m #+ j))"
	by simp
    } then show ?thesis by simp
  qed
  ultimately show "\<forall>i \<in> m #+ n. i \<in> m \<or> (\<exists>j \<in> n. i = m #+ j)"
    by (rule ind_on_nat)
qed

text\<open>A variant of induction useful for finite sequences.\<close>

lemma fin_nat_ind: assumes A1: "n \<in> nat" and A2: "k \<in> succ(n)"
  and A3: "P(0)" and A4: "\<forall>j\<in>n. P(j)  \<longrightarrow> P(succ(j))"
  shows "P(k)"
proof -
  from A2 have "k \<in> n \<or> k=n" by auto
  with A1 have "k \<in> nat" using elem_nat_is_nat by blast
  moreover from A3 have "0 \<in> succ(n) \<longrightarrow> P(0)" by simp
  moreover from A1 A4 have
    "\<forall>k \<in> nat. (k \<in> succ(n) \<longrightarrow> P(k)) \<longrightarrow> (succ(k) \<in> succ(n) \<longrightarrow> P(succ(k)))"
    using nat_into_Ord Ord_succ_mem_iff by auto
  ultimately have "k \<in> succ(n) \<longrightarrow> P(k)"
    by (rule ind_on_nat)
  with A2 show "P(k)" by simp
qed

text\<open>Some properties of positive natural numbers.\<close>

lemma succ_plus: assumes "n \<in> nat"  "k \<in> nat"
  shows 
  "succ(n #+ j) \<in> nat" 
  "succ(n) #+ succ(j) = succ(succ(n #+ j))"
  using assms by auto

text\<open>If $k$ is in the successor of $n$, then the predecessor of $k$ is in $n$.\<close>

lemma pred_succ_mem: assumes "n\<in>nat" "n\<noteq>0" "k\<in>succ(n)" shows "pred(k)\<in>n"
proof -
  from assms(1,3) have "k\<in>nat" using succnat_subset_nat by blast
  { assume "k\<noteq>0"
    with \<open>k\<in>nat\<close> obtain j where "j\<in>nat" and "k=succ(j)"
      using Nat_ZF_1_L3 by auto
    with assms(1,3) have "pred(k)\<in>n" using succ_mem pred_succ_eq
      by simp
  }
  moreover
  { assume "k=0"
    with assms(1,2) have "pred(k)\<in>n" 
      using pred_0 empty_in_non_empty by simp
  } ultimately show ?thesis by blast
qed

text\<open>For non-zero natural numbers $\textrm{pred}(n) = n-1$.\<close>

lemma pred_minus_one: assumes "n\<in>nat" "n\<noteq>0" 
  shows "n #- 1 = pred(n)"
proof -
  from assms obtain k where "n=succ(k)" 
    using Nat_ZF_1_L3 by blast
  with assms show ?thesis
    using pred_succ_eq eq_succ_imp_eq_m1 by simp
qed

text\<open>Various forms of saying that for natural numbers taking the successor 
  is the same as adding one. \<close>

lemma succ_add_one: assumes "n\<in>nat" 
  shows 
    "n #+ 1 = succ(n)" 
    "n #+ 1 \<in> nat" 
    "{0} #+ n = succ(n)" 
    "n #+ {0} = succ(n)"
    "succ(n) \<in> nat"
proof -
  from assms show "n #+ 1 = succ(n)" "n #+ 1 \<in> nat" "succ(n) \<in> nat" by simp_all
  moreover from assms have "{0} = 1" and "n #+ 1 = 1 #+ n" by auto
  ultimately show "{0} #+ n = succ(n)" and "n #+ {0} = succ(n)"
    by simp_all
qed
  
text\<open>Adding and subtracting a natural number cancel each other.\<close>

lemma add_subctract: assumes "m\<in>nat" shows "(m #+ n) #- n = m"
  using assms diff_add_inverse2 by simp

text\<open>A version of induction on natural numbers that uses the $n+1$ notation
  instead of $succ(n)$.\<close>

lemma ind_on_nat1: 
  assumes "n\<in>nat" and "P(0)" and "\<forall>k\<in>nat. P(k)\<longrightarrow>P(k #+ 1)"
  shows "P(n)" using assms succ_add_one(1) ind_on_nat by simp

subsection\<open>Intervals\<close>

text\<open>In this section we consider intervals of natural numbers i.e. sets
  of the form $\{n+j : j \in 0..k-1\}$.\<close>

text\<open>The interval is determined by two parameters: starting point and length.\<close>

definition

  "NatInterval(n,k) \<equiv> {n #+ j. j\<in>k}"

text\<open>Subtracting the beginning af the interval results in a number from
  the length of the interval. It may sound weird, but note that the length of
  such interval is a natural number, hence a set.\<close>

lemma inter_diff_in_len: 
  assumes A1: "k \<in> nat" and A2: "i \<in> NatInterval(n,k)"
  shows "i #- n \<in> k"
proof -
  from A2 obtain j where I: "i = n #+ j" and II: "j \<in> k"
    using NatInterval_def by auto
  from A1 II have "j \<in> nat" using elem_nat_is_nat by blast
  moreover from I have "i #- n = natify(j)" using diff_add_inverse
    by simp
  ultimately have "i #- n = j" by simp
  with II show ?thesis by simp
qed

text\<open>Intervals don't overlap with their starting point and 
  the union of an interval with its starting point is the sum of the starting
  point and the length of the interval.\<close>

lemma length_start_decomp: assumes  A1: "n \<in> nat"  "k \<in> nat"
  shows 
  "n \<inter> NatInterval(n,k) = 0"
  "n \<union> NatInterval(n,k) = n #+ k"
proof -
  { fix i assume A2: "i \<in> n" and "i \<in> NatInterval(n,k)"
    then obtain j where I: "i = n #+ j" and II: "j \<in> k"
      using NatInterval_def by auto
    from A1 have "k \<in> nat" using elem_nat_is_nat by blast
    with II have "j \<in> nat" using elem_nat_is_nat by blast
    with A1 I have "n \<le> i" using add_nat_le by simp
    moreover from A1 A2 have "i < n" using elem_nat_is_nat by blast
    ultimately have False using le_imp_not_lt by blast
  } thus "n \<inter> NatInterval(n,k) = 0" by auto
  from A1 have "n \<subseteq> n #+ k" using add_nat_le by simp
  moreover
  { fix i assume "i \<in> NatInterval(n,k)"
    then obtain j where III: "i = n #+ j" and IV: "j \<in> k"
      using NatInterval_def by auto
    with A1 have "j < k" using elem_nat_is_nat by blast
    with A1 III have "i \<in> n #+ k" using add_lt_mono2 ltD
      by simp }
  ultimately have "n \<union> NatInterval(n,k) \<subseteq> n #+ k" by auto
  moreover from A1 have "n #+ k \<subseteq> n \<union> NatInterval(n,k)" 
    using nat_sum_decomp NatInterval_def by auto
  ultimately show "n \<union> NatInterval(n,k) = n #+ k" by auto
qed

text\<open>Some properties of three adjacent intervals.\<close>

lemma adjacent_intervals3: assumes "n \<in> nat"  "k \<in> nat"  "m \<in> nat"
  shows 
  "n #+ k #+ m = (n #+ k) \<union> NatInterval(n #+ k,m)"
  "n #+ k #+ m = n \<union> NatInterval(n,k #+  m)"
  "n #+ k #+ m = n \<union> NatInterval(n,k) \<union> NatInterval(n #+ k,m)"
  using assms add_assoc length_start_decomp by auto

end
