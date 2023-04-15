(* 
This file is a part of IsarMathLib - 
a library of formalized mathematics for Isabelle/Isar.
Copyright (C) 2023  Slawomir Kolodynski
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

theory Monoid_ZF_1 imports Monoid_ZF Semigroup_ZF

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

text\<open>Propositions proven in the \<open>semigr0\<close> locale are valid in the \<open>monoid1\<close> locale.\<close>

lemma (in monoid1) semigr0_valid_in_monoid1: shows "semigr0(G,f)"
  using monoidAssum IsAmonoid_def semigr0_def by simp

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
      using semigr0_valid_in_monoid1 semigr0.prod_conc_distr
      by blast
    with assms \<open>?a:succ(0)\<rightarrow>G\<close> \<open>m\<in>nat\<close> \<open>Tail(s):succ(m)\<rightarrow>G\<close> 
    have "(\<Sum>s) = s`(0) \<oplus> (\<Sum>Tail(s))" 
      using semigr0_valid_in_monoid1 semigr0.prod_of_1elem pair_val 
        sum_nonempty(2) first_concat_tail by simp
  }
  ultimately show ?thesis by auto
qed

text\<open>The first assertion of the next theorem is similar in content to \<open>seq_sum_pull_first0\<close> 
  formulated in terms of the expression defining the list of monoid elements. The second
  one shows the dual statement: the last element of a sequence can be pulled out of the
  sequence and put after the summation sign. So, we are showing here that 
  $\sum_{k=0}^{n} q_k = q_0 \oplus \sum_{k=0}^{n-1} q_{k+1} = (\sum_{k=0}^{n-1} q_k)) \oplus q_n. $ \<close>

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
    semigr0_valid_in_monoid1 semigr0.prod_comm_distrib by simp

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
    with assms(2) obtain m where "m\<in>nat" and  "n = m #+1"
      using nat_not0_succ by blast
    from assms(3,4) have "?a:n\<rightarrow>G" "?b:n\<rightarrow>G" "?c:n\<rightarrow>G" 
      using group0_1_L1 ZF_fun_from_total by simp_all
    with assms(1) \<open>m\<in>nat\<close> \<open>n = m #+1\<close> have 
      "f {is commutative on} G" "m\<in>nat" and
      "?a:m #+1\<rightarrow>G" "?b:m #+1\<rightarrow>G" "?c:m #+1\<rightarrow>G"
      by simp_all
    moreover have "\<forall>j\<in>m #+ 1. ?c`(j) = ?a`(j) \<oplus> ?b`(j)"
    proof -
      { fix j assume "j \<in> m #+ 1"
        with \<open>n = m #+1\<close> have "j\<in>n" by simp
        then have "?c`(j) = ?a`(j) \<oplus> ?b`(j)"
          using ZF_fun_from_tot_val1 by simp_all
      } thus ?thesis by simp
    qed
    ultimately have "(\<Sum>?c) = (\<Sum>?a) \<oplus> (\<Sum>?b)"
      using sum_comm_distrib0 by simp
  }
  ultimately show ?thesis by blast
qed

subsection\<open>Multiplying monoid elements by natural numbers\<close>

text\<open>A special case of summing (or, using more notation-neutral term \<open>folding\<close> 
  a list a list of monoid is taking a natural multiple of a single element. 
  This can be applied to various monoids embedded in other algebraic structures.
  For example a ring is a monoid with addition as the operation, so the notion of 
  natural multiple directly transfers there. Another monoid in a ring is formed by its 
  multiplication operation. In that case the natural multiple maps into natural powers of a ring
  element. \<close>

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

text\<open>Multiplication of$x$ by a natural number induces a homomorphism between natural numbers 
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

end
