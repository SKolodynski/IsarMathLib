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

  fixes nat_mult (infix "\<cdot>" 70)
  defines nat_mult_def [simp]: "n\<cdot>x \<equiv> \<Sum>{\<langle>k,x\<rangle>. k\<in>n}"

text\<open>Let's recall that the neutral element of the monoid is an element of the monoid (carrier) $G$
  and the monoid operation ($f$ in our notation) is a function that maps $G\times G$
  to $G$.\<close>

lemma (in monoid1) zero_monoid_oper: shows "\<zero>\<in>G" and "f:G\<times>G \<rightarrow> G"
  using monoidAssum unit_is_neutral unfolding IsAmonoid_def IsAssociative_def 
  by simp_all

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
  but formulated in terms of the expression defining the list of monoid elements. The second
  one shows the dual statement: the last element of a sequence can be pulled out of the
  sequence and put after the summation sign.\<close>

theorem (in monoid1) seq_sum_pull_one_elem: 
  assumes "n \<in> nat" "\<forall>k\<in>n #+ 1. q(k) \<in> G"
  shows 
    "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n #+ 1}) =  q(0) \<oplus> (\<Sum>{\<langle>k,q(k #+ 1)\<rangle>. k\<in>n})"
    "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n #+ 1}) =  (\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n}) \<oplus> q(n)"
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

end
