(* 
This file is a part of IsarMathLib - 
a library of formalized mathematics for Isabelle/Isar.
Copyright (C) 2023-2026  Slawomir Kolodynski
This program is free software; Redistribution and use in source and binary forms, 
with or without modification, are permitted provided that the 
following conditions are met:
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

section \<open>Summing lists in a monoid\<close>

theory Monoid_ZF_1 imports Monoid_ZF FiniteSeq_ZF

begin

text\<open>This theory consider properties of sums of monoid elements, similar
  to the ones formalized in the \<open>Semigroup_ZF\<close> theory for sums of semigroup elements. The main
  difference is that since each monoid has a neutral element it makes sense to define a sum
  of an empty list of monoid elements. In multiplicative notation the properties considered here
  can be applied to natural powers of elements ($x^n, n\in \mathbb{N}$) in group or ring theory or,
  when written additively, to natural multiplicities $n\cdot x, n\in \mathbb{N}$). \<close>

subsection\<open>Notation and basic properties of sums of lists of monoid elements\<close>

text\<open>In this section we setup a contex (locale) with notation for sums of lists of
  monoid elements and prove basic properties of those sums in terms of that notation. \<close>

text\<open>The locale (context) \<open>monoid1\<close> extends the locale \<open>monoid1\<close>, adding the notation for the 
  neutral element as $0$ and the sum of a list of monoid elements.
  It also defines a notation for natural multiple of an element of a monoid,
  i.e. $n\cdot x = x\oplus x\oplus ... \oplus x$ (n times). \<close>

locale monoid1 = monoid0 +
  fixes mzero ("\<zero>")
  defines mzero_def [simp]: "\<zero> \<equiv> TheNeutralElement(G,f)"

  fixes listsum ("\<Sum> _" 70)
  defines listsum_def [simp]: "\<Sum>s \<equiv> Fold(f,\<zero>,s)"

  fixes nat_mult (infix "\<cdot>" 72)
  defines nat_mult_def [simp]: "n\<cdot>x \<equiv> \<Sum>{\<langle>k,x\<rangle>. k\<in>n}"

text\<open>Let's recall that the neutral element of the monoid is an element of the monoid (carrier) $G$
  and the monoid operation ($f$ in our notation) is a function that maps $G\times G$
  to $G$.\<close>

lemma (in monoid1) zero_monoid_oper: shows "\<zero>\<in>G" and "f:G\<times>G \<rightarrow> G"
  using monoidAssum unit_is_neutral unfolding IsAmonoid_def IsAssociative_def 
  by simp_all

text\<open>The sum of a list of monoid elements is a monoid element.\<close>

lemma (in monoid1) sum_in_mono: assumes "n\<in>nat" "\<forall>k\<in>n. q(k)\<in>G"
  shows "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n}) \<in> G"
proof -
  let ?a = "{\<langle>k,q(k)\<rangle>. k\<in>n}"
  from assms have "n \<in> nat" "f:G\<times>G \<rightarrow> G" "?a:n \<rightarrow> G" "\<zero>\<in>G" "G\<noteq>0"
    using zero_monoid_oper ZF_fun_from_total by auto
  then show ?thesis using fold_props by simp
qed

text\<open>A different expression of the fact the sum of a list valued in monoid 
  is a monoid element.\<close>

lemma (in monoid1) sum_in_mono1: assumes "n\<in>nat" "b:n\<rightarrow>G"
  shows "(\<Sum>b) \<in> G"
proof -
  from assms have "(\<Sum>{\<langle>k,b`(k)\<rangle>. k\<in>n}) \<in> G"
    using apply_funtype sum_in_mono by simp
  with assms(2) show "(\<Sum>b) \<in> G" using fun_is_set_of_pairs
    by simp
qed

text\<open>The reason we start from $0$ in the definition of the summation sign in the \<open>monoid1\<close> locale
  is that we want to be able to sum the empty list. Such sum of the empty list is $0$. \<close>

lemma (in monoid1) sum_empty: assumes "s:0\<rightarrow>G" shows "(\<Sum>s) = \<zero>"
  using assms zero_monoid_oper fold_empty group0_1_L3A by simp

text\<open>For nonempty lists our $\Sigma$ is the same as \<open>Fold1\<close>. \<close>

lemma (in monoid1) sum_nonempty:  assumes "n \<in> nat" "s:succ(n)\<rightarrow>G"
  shows 
    "(\<Sum>s) = Fold(f,s`(0),Tail(s))"
    "(\<Sum>s) = Fold1(f,s)"
proof -
  from assms have "s`(0) \<in> G" using empty_in_every_succ apply_funtype 
    by simp
  with assms have "(\<Sum>s) = Fold(f,\<zero>\<oplus>s`(0),Tail(s))"
    using zero_monoid_oper fold_detach_first by simp
  with \<open>s`(0) \<in> G\<close> show "(\<Sum>s) = Fold(f,s`(0),Tail(s))"
    using unit_is_neutral by simp
  then show "(\<Sum>s) = Fold1(f,s)" unfolding Fold1_def by simp
qed

text\<open>We can pull the first component of a sum of a nonempty list of monoid elements
  before the summation sign. \<close>  

lemma (in monoid1) seq_sum_pull_first0: assumes "n \<in> nat" "s:succ(n)\<rightarrow>G"
  shows "(\<Sum>s) = s`(0) \<oplus> (\<Sum>Tail(s))"
proof -
  from assms have "s`(0) \<in> G" using empty_in_every_succ apply_funtype 
    by simp
  { assume "n=0"
    with assms have "Tail(s):0\<rightarrow>G" using tail_props(1) by blast
    with assms \<open>s`(0) \<in> G\<close> have "(\<Sum>s) = s`(0) \<oplus> (\<Sum>Tail(s))"
      using sum_nonempty(1) sum_empty zero_monoid_oper(2) group0_1_L3A 
        fold_empty unit_is_neutral by simp
  }
  moreover
  { assume "n\<noteq>0"
    with assms(1) obtain m where "m\<in>nat" and "n = succ(m)"
      using Nat_ZF_1_L3 by blast
    with assms have "Tail(s):succ(m)\<rightarrow>G" using tail_props(1) 
      by simp
    let ?a = "{\<langle>0,s`(0)\<rangle>}"
    from \<open>s`(0) \<in> G\<close> have "0\<in>nat" "?a:succ(0)\<rightarrow>G"
      using pair_func_singleton succ_explained by simp_all
    with \<open>m\<in>nat\<close> \<open>Tail(s):succ(m)\<rightarrow>G\<close> 
    have "f`\<langle>Fold1(f,?a),Fold1(f,Tail(s))\<rangle> = Fold1(f,Concat(?a,Tail(s)))"
      using semigr0_valid_in_monoid0 semigr0.prod_conc_distr
      by blast
    with assms \<open>?a:succ(0)\<rightarrow>G\<close> \<open>m\<in>nat\<close> \<open>Tail(s):succ(m)\<rightarrow>G\<close> 
    have "(\<Sum>s) = s`(0) \<oplus> (\<Sum>Tail(s))" 
      using semigr0_valid_in_monoid0 semigr0.prod_of_1elem pair_val 
        sum_nonempty(2) first_concat_tail by simp
  }
  ultimately show ?thesis by auto
qed

text\<open>The first assertion of the next theorem is similar in content to \<open>seq_sum_pull_first0\<close> 
  formulated in terms of the expression defining the list of monoid elements. The second
  one shows the dual statement: the last element of a sequence can be pulled out of the
  sequence and put after the summation sign. So, we are showing here that 
  $\sum_{k=0}^{n} q_k = q_0 \oplus \sum_{k=0}^{n-1} q_{k+1} = (\sum_{k=0}^{n-1} q_k) \oplus q_n. $ \<close>

theorem (in monoid1) seq_sum_pull_one_elem: 
  assumes "n \<in> nat" "\<forall>k\<in>n #+ 1. q(k) \<in> G"
  shows 
    "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n #+ 1}) = q(0) \<oplus> (\<Sum>{\<langle>k,q(k #+ 1)\<rangle>. k\<in>n})"
    "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n #+ 1}) = (\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n}) \<oplus> q(n)"
proof -
  let ?s = "{\<langle>k,q(k)\<rangle>. k\<in>n #+ 1}"
  from assms(1) have "0 \<in> n #+ 1" using empty_in_every_succ succ_add_one(1)
    by simp
  then have "?s`(0) = q(0)" by (rule ZF_fun_from_tot_val1)
  from assms(2) have "?s: n #+ 1 \<rightarrow> G" by (rule ZF_fun_from_total)
  with assms(1) \<open>?s`(0) = q(0)\<close> have "(\<Sum>?s) = q(0) \<oplus> (\<Sum>Tail(?s))"
    using seq_sum_pull_first0 by simp
  moreover from assms have "Tail(?s) = {\<langle>k,q(k #+ 1)\<rangle>. k \<in> n}"
    using tail_formula by simp
  ultimately show "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n #+ 1}) =  q(0) \<oplus> (\<Sum>{\<langle>k,q(k #+ 1)\<rangle>. k\<in>n})" 
    by simp
  from assms show "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n #+ 1}) =  (\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n}) \<oplus> q(n)"
    using zero_monoid_oper fold_detach_last by simp
qed

text\<open>If we append an element to a list then its sum  increases by that element.\<close>

lemma (in monoid1) seq_sum_append:
  assumes "n\<in>nat" "s:n\<rightarrow>G" "x\<in>G"
  shows "(\<Sum>Append(s,x)) = (\<Sum>s)\<oplus>x"
proof -
  let ?q = "Append(s,x)"
  from assms have 
    "?q:n #+ 1 \<rightarrow> G" and I: "\<forall>k\<in>n #+ 1. ?q`(k)\<in>G" 
    and II: "\<forall>k\<in>n. ?q`(k) = s`(k)" "?q`(n) = x"
    using append_props apply_funtype by simp_all
  from \<open>?q:n #+ 1 \<rightarrow> G\<close> have "?q = {\<langle>k,?q`(k)\<rangle>. k\<in>n #+ 1}"
    using fun_is_set_of_pairs by blast
  hence "(\<Sum>?q) = (\<Sum>{\<langle>k,?q`(k)\<rangle>. k\<in>n #+ 1})" by simp
  also from assms(1) I have "... = (\<Sum>{\<langle>k,?q`(k)\<rangle>. k\<in>n}) \<oplus> ?q`(n)"
    using seq_sum_pull_one_elem(2) by simp
  also from assms(2) II have "... = (\<Sum>s) \<oplus> x"
    using fun_is_set_of_pairs by simp
  finally show "(\<Sum>?q) = (\<Sum>s) \<oplus> x" by simp
qed

text\<open>The sum of a nonempty list is the sum of its init plus the last element. \<close>

lemma (in monoid1) seq_sum_init_last:
  assumes "n\<in>nat" "s:(n #+ 1)\<rightarrow>G"
  shows "(\<Sum>s) = (\<Sum>Init(s))\<oplus>(s`(n))"
proof -
    from assms have 
    "Init(s):n\<rightarrow>G" "s=Append(Init(s),s`(n))" "s`(n)\<in>G"
    using init_props(1,3) nat_less_add_one(2) apply_funtype 
      by simp_all
    with assms(1) \<open>Init(s):n\<rightarrow>G\<close> \<open>s`(n)\<in>G\<close> show ?thesis
    using seq_sum_append by force
qed
 
text\<open>Sum of concatenation of two lists is the sum of sums.\<close>

lemma (in monoid1) seq_sum_concat: 
  assumes "n\<in>nat" "s:n\<rightarrow>G" "m\<in>nat" "q:m\<rightarrow>G"
  shows "(\<Sum>Concat(s,q)) = (\<Sum>s)\<oplus>(\<Sum>q)"
proof -
  from assms(1,2) have I: "\<forall>r\<in>0\<rightarrow>G. (\<Sum>Concat(s,r)) = (\<Sum>s)\<oplus>(\<Sum>r)"
    using sum_empty fun_empty_empty concat_empty(1) sum_in_mono1 
      unit_is_neutral by simp
  have "\<forall>k\<in>nat. ((\<forall>r\<in>k\<rightarrow>G. (\<Sum>Concat(s,r)) = (\<Sum>s)\<oplus>(\<Sum>r))
        \<longrightarrow> (\<forall>r\<in>(k #+ 1)\<rightarrow>G. (\<Sum>Concat(s,r)) = (\<Sum>s)\<oplus>(\<Sum>r)))"
  proof -
    { fix k assume "k\<in>nat"
      assume A: "(\<forall>r\<in>k\<rightarrow>G. (\<Sum>Concat(s,r)) = (\<Sum>s)\<oplus>(\<Sum>r))"
      { fix r assume "r:(k #+ 1)\<rightarrow>G"
        with assms(1,2) \<open>k\<in>nat\<close> have "Init(r):k\<rightarrow>G" "r`(k)\<in>G" 
          and T1: "(\<Sum>s)\<in>G" "(\<Sum>Init(r))\<in>G" 
          and T2: "Concat(s,Init(r)):(n #+ k)\<rightarrow>G"
        using init_props(1) nat_less_add_one(2) apply_funtype 
          sum_in_mono1 concat_props(1) by simp_all
        from assms(1,2) \<open>k\<in>nat\<close> \<open>r:(k #+ 1)\<rightarrow>G\<close>
        have "(\<Sum>Concat(s,r)) = \<Sum>Append(Concat(s,Init(r)),r`(k))"
          using concat_init_last_elem by simp
        also from T2 \<open>r`(k)\<in>G\<close> A \<open>Init(r):k\<rightarrow>G\<close>
        have "... = ((\<Sum>s)\<oplus>(\<Sum>Init(r)))\<oplus>(r`(k))"
          using seq_sum_append by force
        also from T1 \<open>r`(k)\<in>G\<close> \<open>k\<in>nat\<close> \<open>r:(k #+ 1)\<rightarrow>G\<close>
        have "... = (\<Sum>s)\<oplus>(\<Sum>r)"
          using sum_associative seq_sum_init_last by simp
        finally have "(\<Sum>Concat(s,r)) = (\<Sum>s)\<oplus>(\<Sum>r)" by simp
      } hence "\<forall>r\<in>(k #+ 1)\<rightarrow>G. (\<Sum>Concat(s,r)) = (\<Sum>s)\<oplus>(\<Sum>r)"
        by simp
    } thus ?thesis by simp
  qed
  with assms(3) I have "(\<forall>r\<in>m\<rightarrow>G. (\<Sum>Concat(s,r)) = (\<Sum>s)\<oplus>(\<Sum>r))"
    by (rule ind_on_nat1)
  with assms(4) show "(\<Sum>Concat(s,q)) = (\<Sum>s)\<oplus>(\<Sum>q)"
    by simp
qed

text\<open>The sum of a singleton list is its only element,\<close>

lemma (in monoid1) seq_sum_singleton: assumes "q(0) \<in> G"
  shows "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>1}) = q(0)"
proof -
  from assms have "0\<in>nat" and "\<forall>k\<in>0 #+ 1. q(k) \<in> G" by simp_all
  then have 
    "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>0 #+ 1}) = q(0) \<oplus> (\<Sum>{\<langle>k,q(k #+ 1)\<rangle>. k\<in>0})"
    by (rule seq_sum_pull_one_elem)
  with assms show ?thesis using sum_empty unit_is_neutral by simp
qed

text\<open>If the monoid operation is commutative, then the sum of a nonempty sequence
  added to another sum of a nonempty sequence of the same length is equal 
  to the sum of pointwise sums of the sequence elements. 
  This is the same as the theorem \<open>prod_comm_distrib\<close> from the 
  \<open>Semigroup_ZF\<close> theory, just written in the notation used in the \<open>monoid1\<close> locale.\<close>

lemma (in monoid1) sum_comm_distrib0:
  assumes  "f {is commutative on} G" "n\<in>nat" and
  "a : n #+ 1 \<rightarrow> G"  "b : n #+ 1 \<rightarrow> G"  "c : n #+ 1 \<rightarrow> G" and
  "\<forall>j\<in>n #+ 1. c`(j) = a`(j) \<oplus> b`(j)"
  shows "(\<Sum> c) = (\<Sum> a) \<oplus> (\<Sum> b)"
  using assms succ_add_one(1) sum_nonempty 
    semigr0_valid_in_monoid0 semigr0.prod_comm_distrib by simp

text\<open>Another version of \<open>sum_comm_distrib0\<close> written in terms of the expressions
  defining the sequences, shows that for commutative monoids we have 
  $\sum_{k=0}^{n-1}q(k) \oplus p(k) = (\sum_{k=0}^{n-1} p(k))\oplus (\sum_{k=0}^{n-1} q(k))$. \<close>

theorem (in monoid1) sum_comm_distrib: 
  assumes  "f {is commutative on} G" "n\<in>nat" and
  "\<forall>k\<in>n. p(k) \<in> G" "\<forall>k\<in>n. q(k) \<in> G"
  shows 
    "(\<Sum>{\<langle>k,p(k)\<oplus>q(k)\<rangle>. k\<in>n}) = (\<Sum>{\<langle>k,p(k)\<rangle>. k\<in>n}) \<oplus> (\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n})" 
proof -
  let ?a = "{\<langle>k,p(k)\<rangle>. k\<in>n}"
  let ?b = "{\<langle>k,q(k)\<rangle>. k\<in>n}"
  let ?c = "{\<langle>k,p(k)\<oplus>q(k)\<rangle>. k\<in>n}"
  { assume "n=0"
    then have "(\<Sum>?c) = (\<Sum>?a) \<oplus> (\<Sum>?b)"
      using sum_empty unit_is_neutral by simp
  }
  moreover
  { assume "n\<noteq>0"
    with assms(2) obtain m where "m\<in>nat" and  "n = m #+ 1"
      using nat_not0_succ by blast
    from assms(3,4) have "?a:n\<rightarrow>G" "?b:n\<rightarrow>G" "?c:n\<rightarrow>G" 
      using group0_1_L1 ZF_fun_from_total by simp_all
    with assms(1) \<open>m\<in>nat\<close> \<open>n = m #+ 1\<close> have 
      "f {is commutative on} G" "m\<in>nat" and
      "?a:m #+ 1\<rightarrow>G" "?b:m #+ 1\<rightarrow>G" "?c:m #+ 1\<rightarrow>G"
      by simp_all
    moreover have "\<forall>k\<in>m #+ 1. ?c`(k) = ?a`(k) \<oplus> ?b`(k)"
    proof -
      { fix k assume "k \<in> m #+ 1"
        with \<open>n = m #+ 1\<close> have "k\<in>n" by simp
        then have "?c`(k) = ?a`(k) \<oplus> ?b`(k)"
          using ZF_fun_from_tot_val1 by simp_all
      } thus ?thesis by simp
    qed
    ultimately have "(\<Sum>?c) = (\<Sum>?a) \<oplus> (\<Sum>?b)"
      using sum_comm_distrib0 by simp
  }
  ultimately show ?thesis by blast
qed

subsection\<open>Multiplying monoid elements by natural numbers\<close>

text\<open>A special case of summing (or, using more notation-neutral term \<open>folding\<close>)
  a list of monoid elements is taking a natural multiple of a single element. 
  This can be applied to various monoids embedded in other algebraic structures.
  For example a ring is a monoid with addition as the operation, so the notion of 
  natural multiple directly transfers there. Another monoid in a ring is formed by its 
  multiplication operation. In that case the natural multiple maps into natural powers of a ring
  element. \<close>

text\<open>Another way of looking at a multiple of a monoid element: it's a sum of the 
  cartesian product of $n$ and the singleton $\{x\}$. This is because
  the expression $\{\langle k,x\rangle : k\in n\}$ in the defintion of the notation for natural 
  multiple i.e. a constant list of the length $n$ is the same as the set $n\times\{ x\}$.\<close>

lemma (in monoid1) monoid_nat_mult_def_alt: shows "n\<cdot>x = \<Sum>n\<times>{x}"
  using const_fun_def_alt const_fun_def_alt1 by simp

text\<open>The zero's multiple of a monoid element is its neutral element.\<close>

lemma (in monoid1) nat_mult_zero: shows "0\<cdot>x = \<zero>" using sum_empty by simp

text\<open>Any multiple of a monoid element is a monoid element.\<close>

lemma (in monoid1) nat_mult_type: assumes "n\<in>nat" "x\<in>G"
  shows "n\<cdot>x \<in> G" using assms sum_in_mono by simp

text\<open>Taking one more multiple of $x$ adds $x$. \<close>

lemma (in monoid1) nat_mult_add_one: assumes "n\<in>nat" "x\<in>G" 
  shows "(n #+ 1)\<cdot>x = n\<cdot>x \<oplus> x" and "(n #+ 1)\<cdot>x = x \<oplus> n\<cdot>x"
proof -
  from assms(2) have I: "\<forall>k\<in>n #+ 1. x \<in> G" by simp
  with assms(1) have "(\<Sum>{\<langle>k,x\<rangle>. k \<in> n #+ 1}) = x \<oplus> (\<Sum>{\<langle>k,x\<rangle>. k\<in>n})"
    by (rule seq_sum_pull_one_elem)
  thus "(n #+ 1)\<cdot>x = x \<oplus> n\<cdot>x" by simp
  from assms(1) I have "(\<Sum>{\<langle>k,x\<rangle>. k\<in>n #+ 1}) =  (\<Sum>{\<langle>k,x\<rangle>. k\<in>n}) \<oplus> x"
    by (rule seq_sum_pull_one_elem)
  thus "(n #+ 1)\<cdot>x = n\<cdot>x \<oplus> x" by simp
qed

text\<open>One element of a monoid is that element.\<close>

lemma (in monoid1) nat_mult_one: assumes "x\<in>G" shows "1\<cdot>x = x"
proof -
  from assms have "(0 #+ 1)\<cdot>x = 0\<cdot>x \<oplus> x" using nat_mult_add_one(1) by blast
  with assms show ?thesis using nat_mult_zero unit_is_neutral by simp
qed

text\<open>Multiplication of $x$ by a natural number induces a homomorphism between natural numbers 
  with addition and and the natural multiples of $x$. \<close>

lemma (in monoid1) nat_mult_add: assumes "n\<in>nat" "m\<in>nat" "x\<in>G"
  shows "(n #+ m)\<cdot>x = n\<cdot>x \<oplus> m\<cdot>x"
proof -
  from assms have "m\<in>nat" and "(n #+ 0)\<cdot>x = n\<cdot>x \<oplus> 0\<cdot>x" 
    using nat_mult_type unit_is_neutral nat_mult_zero by simp_all
  moreover from assms(1,3) have
    "\<forall>k\<in>nat. (n #+ k)\<cdot>x = n\<cdot>x \<oplus> k\<cdot>x \<longrightarrow> (n #+ (k #+ 1))\<cdot>x = n\<cdot>x \<oplus> (k #+ 1)\<cdot>x"
     using nat_mult_type nat_mult_add_one(1) sum_associative by simp
  ultimately show ?thesis by (rule ind_on_nat1)
qed

text\<open>The neutral element is fixed by this operation.\<close>

lemma (in monoid1) nat_mult_neutral: assumes "n\<in>nat" shows "n\<cdot>\<zero> = \<zero>"
proof -
  from assms have "n\<in>nat" and "0\<cdot>\<zero> = \<zero>" using nat_mult_zero by auto
  moreover have
    "\<forall>k\<in>nat. k\<cdot>\<zero> = \<zero> \<longrightarrow> (k #+ 1)\<cdot>\<zero> = \<zero>"
    using nat_mult_add_one nat_mult_one unit_is_neutral by auto
  ultimately show ?thesis by (rule ind_on_nat1)
qed

subsection\<open>Chains weighted in a monoid\<close>

text\<open>In the \<open>FiniteSeq_ZF\<close> theory we define the notions of \<open>chains\<close>, which are essentially 
  lists of points of some set $X$ and their \<open>chain links\<close>, which are lists of 
  elements of $X\times X$.
  Here we consider what happens when the chain intervals are composed with a function valued 
  in a monoid.\<close>

text\<open>For a chain $c$ and a weight function $w:X\times X\rightarrow G$ we define
  the chain weight as the sum of its intervals composed with $w$.\<close>

definition (in monoid1) ChainWeight where
  "ChainWeight(w,c) \<equiv> \<Sum> (w O ChainLinks(c))"

text\<open>If $c$ is a chain in $X$ of a natural length $n$ connecting $x$ and $y$
  and if the weight function $w$ maps $X\times X$ to the monoid $G$, then the weight
  of the chain $c$ is an element of $G$. \<close>

lemma (in monoid1) chain_weight_type: 
  assumes "n\<in>nat" "c\<in>Chains(X,n,x,y)" "w:X\<times>X\<rightarrow>G"
  shows "ChainWeight(w,c) \<in> G"
  using assms chain_links_fun(2) comp_fun sum_in_mono1
  unfolding ChainWeight_def by blast

text\<open>The weight of the concatenation of chains is equal to the weight of the first
  chain plus the the weight of the link connecting the chains plus the weight of the second chain.\<close>

lemma (in monoid1) chain_concat_weight:
  assumes "n\<^sub>1\<in>nat" "c\<^sub>1\<in>Chains(X,n\<^sub>1,x\<^sub>1,y\<^sub>1)" "n\<^sub>2\<in>nat" "c\<^sub>2\<in>Chains(X,n\<^sub>2,x\<^sub>2,y\<^sub>2)" 
    and "w:X\<times>X\<rightarrow>G"
  shows "ChainWeight(w,Concat(c\<^sub>1,c\<^sub>2)) = 
    ChainWeight(w,c\<^sub>1)\<oplus>(w`\<langle>y\<^sub>1,x\<^sub>2\<rangle>)\<oplus>ChainWeight(w,c\<^sub>2)"
proof -
  let ?L\<^sub>1 = "ChainLinks(c\<^sub>1)"
  let ?L\<^sub>2 = "ChainLinks(c\<^sub>2)"
  from assms(1,2) have "y\<^sub>1\<in>X" using chain_props(5) by blast
  from assms(3,4) have "x\<^sub>2\<in>X" using chain_props(4) by blast
  from assms(1,2,3,4) \<open>y\<^sub>1\<in>X\<close> \<open>x\<^sub>2\<in>X\<close> have
    "?L\<^sub>1:n\<^sub>1\<rightarrow>X\<times>X" "?L\<^sub>2:n\<^sub>2\<rightarrow>X\<times>X" "\<langle>y\<^sub>1,x\<^sub>2\<rangle> \<in> X\<times>X" and
    "Append(?L\<^sub>1,\<langle>y\<^sub>1,x\<^sub>2\<rangle>):(n\<^sub>1 #+ 1)\<rightarrow>X\<times>X"
  using chain_links_fun(2) append_props(1) by simp_all
  with assms(1,3,5) \<open>?L\<^sub>2:n\<^sub>2\<rightarrow>X\<times>X\<close> have
    I: "w O Concat(Append(?L\<^sub>1,\<langle>y\<^sub>1,x\<^sub>2\<rangle>),?L\<^sub>2) = 
    Concat(w O Append(?L\<^sub>1,\<langle>y\<^sub>1,x\<^sub>2\<rangle>), w O ?L\<^sub>2)"
    using list_compose_concat by blast
  from assms(1,5) \<open>?L\<^sub>1:n\<^sub>1\<rightarrow>X\<times>X\<close> \<open>?L\<^sub>2:n\<^sub>2\<rightarrow>X\<times>X\<close> \<open>\<langle>y\<^sub>1,x\<^sub>2\<rangle> \<in> X\<times>X\<close>
  have "(w O ?L\<^sub>1):n\<^sub>1\<rightarrow>G" "(w O ?L\<^sub>2): n\<^sub>2\<rightarrow>G" "w`\<langle>y\<^sub>1,x\<^sub>2\<rangle> \<in> G" and
    II: "Append(w O ?L\<^sub>1,w`(\<langle>y\<^sub>1,x\<^sub>2\<rangle>)):(n\<^sub>1 #+ 1)\<rightarrow>G"
    using comp_fun apply_funtype append_props(1) by simp_all
  from assms(1,2,3,4) I have "ChainWeight(w,Concat(c\<^sub>1,c\<^sub>2)) = 
      \<Sum> Concat(w O Append(?L\<^sub>1,\<langle>y\<^sub>1,x\<^sub>2\<rangle>), w O ?L\<^sub>2)"
    unfolding ChainWeight_def using concat_chains(4) by simp
  also from assms(1,5) \<open>?L\<^sub>1:n\<^sub>1\<rightarrow>X\<times>X\<close> \<open>\<langle>y\<^sub>1,x\<^sub>2\<rangle> \<in> X\<times>X\<close>
  have "... = \<Sum> Concat(Append(w O ?L\<^sub>1,w`(\<langle>y\<^sub>1,x\<^sub>2\<rangle>)), w O ?L\<^sub>2)"
    using list_compose_append(2) by simp
  also from assms(1,3) II \<open>(w O ?L\<^sub>2): n\<^sub>2\<rightarrow>G\<close>
  have "... = (\<Sum>Append(w O ?L\<^sub>1,w`\<langle>y\<^sub>1,x\<^sub>2\<rangle>))\<oplus>(\<Sum>(w O ?L\<^sub>2))"
    using seq_sum_concat by blast
  also from assms(1) \<open>(w O ?L\<^sub>1):n\<^sub>1\<rightarrow>G\<close> \<open>w`\<langle>y\<^sub>1,x\<^sub>2\<rangle> \<in> G\<close>
  have "... = ChainWeight(w,c\<^sub>1)\<oplus>(w`\<langle>y\<^sub>1,x\<^sub>2\<rangle>)\<oplus>ChainWeight(w,c\<^sub>2)"
    using seq_sum_append unfolding ChainWeight_def by simp
  finally show ?thesis by simp
qed

text\<open>If, in addition to assumptions of \<open>chain_weight_concat\<close> the weight function
  $w$ vanishes on the diagonal and the first chain ends at the beginning of the second
  one, then the weight of the concatenated chain is the sum of the chain weights.\<close>

lemma (in monoid1) chain_concat_weight1: 
  assumes "n\<^sub>1\<in>nat" "c\<^sub>1\<in>Chains(X,n\<^sub>1,x,y)" "n\<^sub>2\<in>nat" "c\<^sub>2\<in>Chains(X,n\<^sub>2,y,z)"
    and "w:X\<times>X\<rightarrow>G" "\<forall>x\<in>X. w`\<langle>x,x\<rangle> = \<zero>"
  shows "ChainWeight(w,Concat(c\<^sub>1,c\<^sub>2)) = ChainWeight(w,c\<^sub>1)\<oplus>ChainWeight(w,c\<^sub>2)"
proof -
  from assms(1,2) have "y\<in>X" using chain_props(5) by blast
  with assms show ?thesis 
    using chain_weight_type chain_concat_weight unit_is_neutral 
    by simp
qed

end
