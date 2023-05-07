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

section \<open>Binomial theorem\<close>

theory Ring_Binomial_ZF imports Monoid_ZF_1 Ring_ZF

begin

text\<open>This theory aims at formalizing sufficient background to be able to state and prove the
  binomial theorem. \<close>

subsection\<open>Sums of multiplicities of powers of ring elements and binomial theorem\<close>

text\<open>The binomial theorem asserts that for any two elements of a commutative ring
  the n-th power of the sum $x+y$ can be written as a sum of certain multiplicities of terms 
  $x^{n-k}y^k$, where $k \in 0..n$. In this section we setup the notation and prove basic properties
  of such multiplicities and powers of ring elements. We show the binomial theorem as 
  an application. \<close>

text\<open>The next locale (context) extends the \<open>ring0\<close> locale with notation for powers, 
  multiplicities and sums and products of finite lists of ring elements.\<close>

locale ring3 = ring0 +
  fixes listsum ("\<Sum> _" 70)
  defines listsum_def [simp]: "\<Sum>s \<equiv> Fold(A,\<zero>,s)"

  fixes listprod ("\<Prod> _" 70)
  defines listprod_def [simp]: "\<Prod>s \<equiv> Fold(M,\<one>,s)"

  fixes nat_mult (infix "\<nm>" 95)
  defines nat_mult_def [simp]: "n\<nm>x \<equiv> \<Sum>{\<langle>k,x\<rangle>. k\<in>n}"

  fixes pow
  defines pow_def [simp]: "pow(n,x) \<equiv> \<Prod>{\<langle>k,x\<rangle>. k\<in>n}"

text\<open>A ring with addition forms a monoid, hence all propositions proven in the \<open>monoid1\<close> locale
  (defined in the \<open>Monoid_ZF_1\<close> theory) can be used in the \<open>ring3\<close> locale, applied to the 
  additive operation. \<close>

sublocale ring3 < add_monoid: monoid1 R A ringa ringzero listsum nat_mult
  using ringAssum 
  unfolding IsAring_def IsAgroup_def monoid1_def monoid0_def 
  by auto

text\<open>A ring with multiplication forms a monoid, hence all propositions proven in the \<open>monoid1\<close> locale
  (defined in the \<open>Monoid_ZF_1\<close> theory) can be used in the \<open>ring3\<close> locale, applied to the
  multiplicative operation. \<close>

sublocale ring3 < mul_monoid: monoid1 R M ringm ringone listprod pow
  using ringAssum 
  unfolding IsAring_def IsAgroup_def monoid1_def monoid0_def 
  by auto

text\<open>$0\cdot x = 0$ and $x^0=1$. It is a bit surprising that we do not need to assume
  that $x\in R$ (i.e. $x$ is an element of the ring). These properties are really proven in the \<open>Monoid_ZF_1\<close> 
  theory where there is no assumption that $x$ is an element of the monoid. \<close>

lemma (in ring3) mult_pow_zero: shows "0\<nm>x = \<zero>" and "pow(0,x) = \<one>"
  using add_monoid.nat_mult_zero mul_monoid.nat_mult_zero by simp_all

text\<open>Natural multiple and power of a ring element is a ring element.\<close>

lemma (in ring3) mult_pow_type: assumes "n\<in>nat" "x\<in>R"
  shows "n\<nm>x \<in> R" and "pow(n,x) \<in> R"
  using assms add_monoid.nat_mult_type mul_monoid.nat_mult_type 
  by simp_all

text\<open>The usual properties of multiples and powers: $(n+1)x = nx+x$ and 
  $x^n+1=x^n x$. These are just versions of \<open>nat_mult_add_one\<close> from \<open>Monoid_ZF_1\<close>
  writtent in the notation defined in the \<open>ring3\<close> locale.\<close>

lemma (in ring3) nat_mult_pow_add_one: assumes  "n\<in>nat" "x\<in>R"
  shows "(n #+ 1)\<nm>x = (n\<nm>x) \<ra> x" and "pow(n #+ 1,x) = pow(n,x)\<cdot>x"
  using assms add_monoid.nat_mult_add_one mul_monoid.nat_mult_add_one 
  by simp_all

text\<open>Associativity for the multiplication by natural number and the ring multiplication:\<close>

lemma (in ring3) nat_mult_assoc: assumes "n\<in>nat" "x\<in>R" "y\<in>R"
  shows "n\<nm>x\<cdot>y = n\<nm>(x\<cdot>y)"
proof -
  from assms(1,3) have "n\<in>nat" and "0\<nm>x\<cdot>y = 0\<nm>(x\<cdot>y)"
    using mult_pow_zero(1) Ring_ZF_1_L6 by simp_all
  moreover from assms(2,3) have "\<forall>k\<in>nat. 
    k\<nm>x\<cdot>y = k\<nm>(x\<cdot>y) \<longrightarrow> (k #+ 1)\<nm>x\<cdot>y = (k #+ 1)\<nm>(x\<cdot>y)"
    using nat_mult_pow_add_one(1) mult_pow_type ring_oper_distr(2) Ring_ZF_1_L4(3)
      by simp
  ultimately show ?thesis by (rule ind_on_nat1)
qed

text\<open>Addition of natural numbers is distributive with respect to natural multiple.
  This is essentially lemma \<open>nat_mult_add\<close> from \<open>Monoid_ZF_1.thy\<close>, just transferred
  to the \<open>ring3\<close> locale.\<close>

lemma (in ring3) nat_add_mult_distrib: assumes "n\<in>nat" "m\<in>nat" "x\<in>R"
  shows "(n #+ m)\<nm>x = n\<nm>x \<ra> m\<nm>x"
  using assms add_monoid.nat_mult_add by simp

text\<open>Associativity for the multiplication by natural number and the ring multiplication
  extended to three elements of the ring:\<close>

lemma (in ring3) nat_mult_assoc1: assumes "n\<in>nat" "x\<in>R" "y\<in>R" "z\<in>R" 
  shows "n\<nm>x\<cdot>y\<cdot>z = n\<nm>(x\<cdot>y\<cdot>z)"
  using assms Ring_ZF_1_L4(3) nat_mult_assoc by simp

text\<open>When we multiply an expression whose value belongs to a ring by a ring element 
  and we get an expression whose value belongs to a ring.\<close>

lemma (in ring3) mult_elem_ring_type: 
  assumes "n\<in>nat" "x\<in>R" and "\<forall>k\<in>n. q(k) \<in> R" 
  shows "\<forall>k\<in>n. q(k)\<cdot>x \<in> R" and "(\<Sum>{\<langle>k,q(k)\<cdot>x\<rangle>. k\<in>n}) \<in> R"
  using assms Ring_ZF_1_L4(3) add_monoid.sum_in_mono by simp_all

text\<open>The sum of expressions whose values belong to a ring is an expression
  whose value belongs to a ring. \<close>

lemma (in ring3) sum_expr_ring_type: 
  assumes "n\<in>nat" "\<forall>k\<in>n. q(k) \<in> R" "\<forall>k\<in>n. p(k) \<in> R"
  shows "\<forall>k\<in>n. q(k)\<ra>p(k) \<in> R" and "(\<Sum>{\<langle>k,q(k)\<ra>p(k)\<rangle>. k\<in>n}) \<in> R"
  using assms Ring_ZF_1_L4(1) add_monoid.sum_in_mono by simp_all

text\<open>Combining \<open>mult_elem_ring_type\<close> and \<open>sum_expr_ring_type\<close> we obtain that
  a (kind of) linear combination of expressions whose values belong to a ring
  belongs to the ring. \<close>

lemma (in ring3) lin_comb_expr_ring_type:
  assumes "n\<in>nat" "x\<in>R"  "y\<in>R" "\<forall>k\<in>n. q(k) \<in> R" "\<forall>k\<in>n. p(k) \<in> R"
  shows "\<forall>k\<in>n. q(k)\<cdot>x\<ra>p(k)\<cdot>y \<in> R" and 
    "(\<Sum>{\<langle>k,q(k)\<cdot>x\<ra>p(k)\<cdot>y\<rangle>. k\<in>n}) \<in> R"
proof -
  from assms have "\<forall>k\<in>n. q(k)\<cdot>x \<in> R" and "\<forall>k\<in>n. p(k)\<cdot>y \<in> R"
    using mult_elem_ring_type(1) by simp_all
  with assms(1) show "\<forall>k\<in>n. q(k)\<cdot>x\<ra>p(k)\<cdot>y \<in> R" 
    using sum_expr_ring_type(1) by simp
  with assms(1) show "(\<Sum>{\<langle>k,q(k)\<cdot>x\<ra>p(k)\<cdot>y\<rangle>. k\<in>n}) \<in> R" 
    using add_monoid.sum_in_mono by simp
qed

text\<open>A \<open>ring3\<close> version of \<open>seq_sum_pull_one_elem\<close> from \<open>Monoid_ZF_1\<close>: \<close>

lemma (in ring3) rng_seq_sum_pull_one_elem:
  assumes "j \<in> nat" "\<forall>k\<in>j #+ 1. q(k) \<in> R"
  shows
    "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1}) = q(0)\<ra>(\<Sum>{\<langle>k,q(k #+ 1)\<rangle>. k\<in>j})"
    "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1}) = (\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j})\<ra> q(j)"
  using assms add_monoid.seq_sum_pull_one_elem by simp_all

text\<open>Distributive laws for finite sums in a ring: 
  $(\sum_{k=0}^{n-1}q(k))\cdot x = \sum_{k=0}^{n-1}q(k)\cdot x$ and 
  $x\cdot (\sum_{k=0}^{n-1}q(k)) = \sum_{k=0}^{n-1}x\cdot q(k)$. \<close>

theorem (in ring3) fin_sum_distrib: 
  assumes "x\<in>R"  "n\<in>nat" "\<forall>k\<in>n. q(k) \<in> R" 
  shows 
    "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n})\<cdot>x = \<Sum>{\<langle>k,q(k)\<cdot>x\<rangle>. k\<in>n}"
    "x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n}) = \<Sum>{\<langle>k,x\<cdot>q(k)\<rangle>. k\<in>n}"
proof -
  from assms(1,2) have "n\<in>nat" and 
    "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>0})\<cdot>x = \<Sum>{\<langle>k,q(k)\<cdot>x\<rangle>. k\<in>0}"
    using add_monoid.sum_empty Ring_ZF_1_L6(1) by simp_all
  moreover have 
    "\<forall>j\<in>n. (\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j})\<cdot>x = (\<Sum>{\<langle>k,q(k)\<cdot>x\<rangle>. k\<in>j})
    \<longrightarrow> (\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1})\<cdot>x = \<Sum>{\<langle>k,q(k)\<cdot>x\<rangle>. k\<in>j #+ 1}"
  proof -
    { fix j assume "j\<in>n" and 
        I: "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j})\<cdot>x = (\<Sum>{\<langle>k,q(k)\<cdot>x\<rangle>. k\<in>j})" 
      from assms(2) \<open>j\<in>n\<close> have "j\<in>nat" using elem_nat_is_nat(2) 
        by simp
      moreover from assms(2,3) \<open>j\<in>n\<close> have II: "\<forall>k\<in>j #+ 1. q(k) \<in> R"
        using mem_add_one_subset by blast
      ultimately have     
        "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1}) =  (\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) \<ra> q(j)"
        using add_monoid.seq_sum_pull_one_elem(2) by simp
      hence 
        "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1})\<cdot>x = ((\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) \<ra> q(j))\<cdot>x"
        by simp
      moreover from assms(1) \<open>j\<in>nat\<close> II have
        "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) \<in> R" "q(j) \<in> R" and "x\<in>R" 
        using add_monoid.sum_in_mono by simp_all
      ultimately have 
        "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1})\<cdot>x = (\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j})\<cdot>x \<ra> q(j)\<cdot>x"
        using ring_oper_distr(2) by simp
      with I have 
        "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1})\<cdot>x = (\<Sum>{\<langle>k,q(k)\<cdot>x\<rangle>. k\<in>j})  \<ra> q(j)\<cdot>x" 
        by simp
      moreover 
      from assms(1) II have "\<forall>k\<in>j #+ 1. q(k)\<cdot>x \<in> R"
        using Ring_ZF_1_L4(3) by simp
      with \<open>j\<in>nat\<close> have 
        "(\<Sum>{\<langle>k,q(k)\<cdot>x\<rangle>. k\<in>j #+ 1}) = (\<Sum>{\<langle>k,q(k)\<cdot>x\<rangle>. k\<in>j}) \<ra> q(j)\<cdot>x"
        using add_monoid.seq_sum_pull_one_elem(2) by simp
      ultimately have 
        "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1})\<cdot>x = (\<Sum>{\<langle>k,q(k)\<cdot>x\<rangle>. k\<in>j #+ 1})"
        by simp
    } thus ?thesis by simp
  qed
  ultimately show "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n})\<cdot>x = \<Sum>{\<langle>k,q(k)\<cdot>x\<rangle>. k\<in>n}"
    by (rule fin_nat_ind1)
  from assms(1,2) have "n\<in>nat" and 
    "x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>0}) = \<Sum>{\<langle>k,x\<cdot>q(k)\<rangle>. k\<in>0}"
    using add_monoid.sum_empty Ring_ZF_1_L6(2) by simp_all
  moreover have 
    "\<forall>j\<in>n. x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) = (\<Sum>{\<langle>k,x\<cdot>q(k)\<rangle>. k\<in>j})
    \<longrightarrow> x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1}) = \<Sum>{\<langle>k,x\<cdot>q(k)\<rangle>. k\<in>j #+ 1}" 
  proof -
    { fix j assume "j\<in>n" and 
        I: "x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) = (\<Sum>{\<langle>k,x\<cdot>q(k)\<rangle>. k\<in>j})"
      from assms(2) \<open>j\<in>n\<close> have "j\<in>nat" using elem_nat_is_nat(2) 
        by simp
      moreover from assms(2,3) \<open>j\<in>n\<close> have II: "\<forall>k\<in>j #+ 1. q(k) \<in> R"
        using mem_add_one_subset by blast
      ultimately have     
        "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1}) =  (\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) \<ra> q(j)"
        using add_monoid.seq_sum_pull_one_elem(2) by simp
      hence 
        "x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1}) = x\<cdot>((\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) \<ra> q(j))"
        by simp
      moreover from assms(1) \<open>j\<in>nat\<close> II have
        "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) \<in> R" "q(j) \<in> R" and "x\<in>R" 
        using add_monoid.sum_in_mono by simp_all
       ultimately have 
        "x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1}) = x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) \<ra> x\<cdot>q(j)"
        using ring_oper_distr(1) by simp
       with I have 
        "x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1}) =  (\<Sum>{\<langle>k,x\<cdot>q(k)\<rangle>. k\<in>j})  \<ra> x\<cdot>q(j)" 
        by simp
      moreover 
      from assms(1) II have "\<forall>k\<in>j #+ 1. x\<cdot>q(k) \<in> R"
        using Ring_ZF_1_L4(3) by simp
      with \<open>j\<in>nat\<close> have 
        "(\<Sum>{\<langle>k,x\<cdot>q(k)\<rangle>. k\<in>j #+ 1}) = (\<Sum>{\<langle>k,x\<cdot>q(k)\<rangle>. k\<in>j}) \<ra> x\<cdot>q(j)"
        using add_monoid.seq_sum_pull_one_elem(2) by simp
      ultimately have 
        "x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1}) = (\<Sum>{\<langle>k,x\<cdot>q(k)\<rangle>. k\<in>j #+ 1})"
        by simp
    } thus ?thesis by simp
  qed
  ultimately show  "x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n}) = \<Sum>{\<langle>k,x\<cdot>q(k)\<rangle>. k\<in>n}"
    by (rule fin_nat_ind1)
qed

text\<open>In rings we have 
  $\sum_{k=0}^{n-1}q(k) + p(k) = (\sum_{k=0}^{n-1} p(k)) + (\sum_{k=0}^{n-1} q(k))$. 
  This is the same as theorem \<open>sum_comm_distrib\<close> in \<open>Monoid_ZF_1.thy\<close>, except that
  we do not need the assumption about commutativity of the operation as addition in rings
  is always commutative. \<close>

lemma (in ring3) sum_ring_distrib: 
  assumes "n\<in>nat" and  "\<forall>k\<in>n. p(k) \<in> R" "\<forall>k\<in>n. q(k) \<in> R"
  shows
    "(\<Sum>{\<langle>k,p(k)\<ra>q(k)\<rangle>. k\<in>n}) = (\<Sum>{\<langle>k,p(k)\<rangle>. k\<in>n}) \<ra> (\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n})"
  using assms Ring_ZF_1_L1(3) add_monoid.sum_comm_distrib by simp

text\<open>To shorten the notation in the proof of the binomial theorem we give a name to the
  binomial term ${n \choose k} x^{n-k} y^k$.\<close>

definition (in ring3) BT where
  "BT(n,k,x,y) \<equiv> Binom(n,k)\<nm>pow(n #- k,x)\<cdot>pow(k,y)"

text\<open>If $n,k$ are natural numbers and $x,y$ are ring elements then the binomial term is 
  an element of the ring. \<close>

lemma (in ring3) bt_type: assumes "n\<in>nat" "k\<in>nat" "x\<in>R" "y\<in>R" 
  shows "BT(n,k,x,y) \<in> R"
  using assms mult_pow_type binom_in_nat Ring_ZF_1_L4(3)
  unfolding BT_def by simp

text\<open>The binomial term is $1$ when the $n=0$ and $k=0$. 
  Somehow we do not need the assumption that $x,y$ are ring elements. \<close>

lemma (in ring3) bt_at_zero: shows "BT(0,0,x,y) = \<one>"
  using binom_zero_zero mult_pow_zero(2) add_monoid.nat_mult_one 
        Ring_ZF_1_L2(2) Ring_ZF_1_L3(5)
  unfolding BT_def by simp

text\<open>The binomial term is $x^n$ when $k=0$. \<close>

lemma (in ring3) bt_at_zero1: assumes "n\<in>nat" "x\<in>R"
  shows "BT(n,0,x,y) = pow(n,x)" 
  unfolding BT_def using assms mult_pow_zero(2) binom_left_boundary
    mult_pow_type(2) add_monoid.nat_mult_one Ring_ZF_1_L3(5) 
    by simp

text\<open>When $k=0$ multiplying the binomial term by $x$ is the same as adding one to $n$. \<close>

lemma (in ring3) bt_at_zero2: assumes "n\<in>nat" "x\<in>R"
  shows "BT(n,0,x,y)\<cdot>x = BT(n #+ 1,0,x,y)"
  using assms bt_at_zero1 nat_mult_pow_add_one(2) by simp

text\<open>The binomial term is $y^n$ when $k=n$.\<close>

lemma (in ring3) bt_at_right: assumes "n\<in>nat" "y\<in>R"
  shows "BT(n,n,x,y) = pow(n,y)" 
  unfolding BT_def using assms binom_right_boundary mult_pow_zero(2)
    add_monoid.nat_mult_one Ring_ZF_1_L2(2) mult_pow_type(2) Ring_ZF_1_L3(6)
  by simp

text\<open>When $k=n$ multiplying the binomial term by $x$ is the same as adding one to $n$. \<close>

lemma (in ring3) bt_at_right1: assumes "n\<in>nat" "y\<in>R"
  shows "BT(n,n,x,y)\<cdot>y = BT(n #+ 1,n #+ 1,x,y)"
  using assms bt_at_right nat_mult_pow_add_one(2) by simp

text\<open>A key identity for binomial terms needed for the proof of the binomial theorem:\<close>

lemma (in ring3) bt_rec_identity: 
  assumes "M {is commutative on} R" "j\<in>nat" "k\<in>j" "x\<in>R" "y\<in>R"
  shows 
    "BT(j,k #+ 1,x,y)\<cdot>x \<ra> BT(j,k,x,y)\<cdot>y = BT(j #+ 1,k #+ 1,x,y)"
proof -
  from assms(2,3,4) have "k\<in>nat" 
    "Binom(j,k #+ 1) \<in> nat" "Binom(j,k) \<in> nat" "Binom(j #+ 1,k #+ 1) \<in> nat" 
    and I: "pow(j #- (k #+ 1),x) \<in> R" and II: "pow(j #- k,x) \<in> R"
    using elem_nat_is_nat(2) binom_in_nat mult_pow_type(2)
    by simp_all
  with assms(5) have III: "pow(k #+ 1,y) \<in> R"
    using mult_pow_type(2) by blast
  let ?L = "BT(j,k #+ 1,x,y)\<cdot>x \<ra> BT(j,k,x,y)\<cdot>y"
  let ?p = "pow(j #- k,x)\<cdot>pow(k #+ 1,y)"
  from assms(2,4) \<open>k\<in>nat\<close> II III have "?p \<in> R"
    using mult_pow_type(2) Ring_ZF_1_L4(3) by simp
  from assms(2,3,4,5) have "BT(j,k,x,y)\<cdot>y = Binom(j,k)\<nm>?p"
    using elem_nat_is_nat(2) binom_in_nat mult_pow_type(2) 
      nat_mult_assoc1 Ring_ZF_1_L11(2) nat_mult_pow_add_one(2)
    unfolding BT_def by simp
  moreover have "BT(j,k #+ 1,x,y)\<cdot>x = Binom(j,k #+ 1)\<nm>?p"
  proof -
    from assms(1,4) \<open>Binom(j,k #+ 1) \<in> nat\<close> I III have
      "Binom(j,k #+ 1)\<nm>pow(j #- (k #+ 1),x)\<cdot>pow(k #+ 1,y)\<cdot>x =
        Binom(j,k #+ 1)\<nm>(pow(j #- (k #+ 1) #+ 1,x)\<cdot>pow(k #+ 1,y))"
      using nat_mult_assoc1 Ring_ZF_2_L4(2) nat_mult_pow_add_one(2)
      by simp
    with assms(2,3) have 
      "Binom(j,k #+ 1)\<nm>pow(j #- (k #+ 1),x)\<cdot>pow(k #+ 1,y)\<cdot>x =
      Binom(j,k #+ 1)\<nm>(pow(j #- (k #+ 1) #+ 1,x)\<cdot>pow(k #+ 1,y))"
      using nat_subtr_simpl0 by blast
    moreover from assms(2,3) have 
      "pow(j #- (k #+ 1) #+ 1,x) = pow(j #- k,x)"
      using nat_subtr_simpl0 by simp
    ultimately show ?thesis unfolding BT_def by simp
  qed
  ultimately have "?L = Binom(j,k #+ 1)\<nm>?p \<ra> Binom(j,k)\<nm>?p"
    by simp
  with assms(2,3) \<open>Binom(j,k #+ 1) \<in> nat\<close> \<open>Binom(j,k) \<in> nat\<close> \<open>?p \<in> R\<close>
  have "?L = Binom(j #+ 1,k #+ 1)\<nm>?p"
    using nat_add_mult_distrib binom_prop2 succ_ineq1(3) by simp
  with assms(2,3) \<open>Binom(j #+ 1,k #+ 1) \<in> nat\<close> II III
  show ?thesis using nat_mult_assoc nat_subtr_simpl0
    unfolding BT_def by simp
qed

text\<open>The binomial theorem $x,y$ are elements of a commutative ring then 
  $(x+y)^n = \sum_{k=0}^{n} {n \choose k} x^{n-k} y^k$.\<close>

theorem (in ring3) binomial_theorem: 
  assumes "M {is commutative on} R" "n\<in>nat" "x\<in>R" "y\<in>R"
  shows "pow(n,x\<ra>y) = \<Sum>{\<langle>k,Binom(n,k)\<nm>pow(n #- k,x) \<cdot> pow(k,y)\<rangle>. k\<in>n #+ 1}"
proof -
  from assms(2) have "n\<in>nat" by simp
  moreover have "pow(0,x\<ra>y) = \<Sum>{\<langle>k,BT(0,k,x,y)\<rangle>. k\<in>0 #+ 1}"
  proof -
    from assms(3,4) have "(\<Sum>{\<langle>k,BT(0,k,x,y)\<rangle>. k\<in>0 #+ 1}) = \<one>"
      using bt_at_zero Ring_ZF_1_L2(2) add_monoid.seq_sum_singleton
      by simp
    then show ?thesis using mult_pow_zero(2) by simp
  qed
  moreover have "\<forall>j\<in>nat. 
    pow(j,x\<ra>y) = (\<Sum>{\<langle>k,BT(j,k,x,y)\<rangle>. k\<in>j #+ 1})  \<longrightarrow> 
    pow(j #+ 1,x\<ra>y) = (\<Sum>{\<langle>k,BT(j #+ 1,k,x,y)\<rangle>. k\<in>j #+ 1 #+ 1})"
  proof -
    { fix j
      let ?s\<^sub>0 = "\<Sum>{\<langle>k,BT(j,k,x,y)\<rangle>. k\<in>j #+ 1}"
      let ?s\<^sub>1 = "\<Sum>{\<langle>k,BT(j,k,x,y)\<cdot>x\<rangle>. k\<in>j #+ 1}"
      let ?s\<^sub>2 = "\<Sum>{\<langle>k,BT(j,k,x,y)\<cdot>y\<rangle>. k\<in>j #+ 1}"
      let ?s\<^sub>3 = "\<Sum>{\<langle>k,BT(j,k #+ 1,x,y)\<cdot>x\<rangle>. k\<in>j}"
      let ?s\<^sub>4 = "\<Sum>{\<langle>k,BT(j,k,x,y)\<cdot>y\<rangle>. k\<in>j}"
      let ?s\<^sub>5 = "\<Sum>{\<langle>k,BT(j,k #+ 1,x,y)\<cdot>x \<ra> BT(j,k,x,y)\<cdot>y\<rangle>. k\<in>j}"
      let ?s\<^sub>6 = "\<Sum>{\<langle>k,BT(j #+ 1,k #+ 1,x,y)\<rangle>. k\<in>j}"
      let ?s\<^sub>7 = "\<Sum>{\<langle>k,BT(j #+ 1,k,x,y)\<rangle>. k\<in>j #+ 1}"
      let ?s\<^sub>8 = "\<Sum>{\<langle>k,BT(j #+ 1,k,x,y)\<rangle>. k\<in>j #+ 1 #+ 1}"
      assume "j\<in>nat" and A: "pow(j,x\<ra>y) = ?s\<^sub>0"
      then have "j #+ 1 \<in> nat" and "j #+ 1 #+ 1 \<in> nat" by simp_all
      have 
        I:  "\<forall>k\<in>j #+ 1. BT(j,k,x,y) \<in> R" and
        II: "\<forall>k\<in>j #+ 1. BT(j,k,x,y)\<cdot>x \<in> R" and
        III: "\<forall>k\<in>j #+ 1. BT(j,k,x,y)\<cdot>y \<in> R" and
        IV:  "\<forall>k\<in>j. BT(j,k #+ 1,x,y)\<cdot>x \<in> R" and
        V:   "\<forall>k\<in>j. BT(j,k,x,y)\<cdot>y \<in> R" and
        VI:  "\<forall>k\<in>j #+ 1. BT(j #+ 1,k,x,y) \<in> R" and
        VII: "\<forall>k\<in>j #+ 1 #+ 1. BT(j #+ 1,k,x,y) \<in> R"
      proof -
        from assms(3,4) \<open>j\<in>nat\<close> show "\<forall>k\<in>j #+ 1. BT(j,k,x,y) \<in> R"
          using elem_nat_is_nat(2) bt_type by blast
        with assms(3,4) \<open>j\<in>nat\<close> show 
          "\<forall>k\<in>j #+ 1. BT(j,k,x,y)\<cdot>x \<in> R" and 
          "\<forall>k\<in>j #+ 1. BT(j,k,x,y)\<cdot>y \<in> R" and
          "\<forall>k\<in>j. BT(j,k,x,y)\<cdot>y \<in> R"
          using Ring_ZF_1_L4(3) by simp_all
        from assms(3,4) \<open>j\<in>nat\<close> have "\<forall>k\<in>j. BT(j,k #+ 1,x,y) \<in> R"
          using elem_nat_is_nat(2) bt_type by simp 
        with \<open>j\<in>nat\<close> assms(3) show "\<forall>k\<in>j. BT(j,k #+ 1,x,y)\<cdot>x \<in> R"
          using mult_elem_ring_type(1) by simp
        from assms(3,4) \<open>j #+ 1 \<in> nat\<close> show 
          "\<forall>k\<in>j #+ 1. BT(j #+ 1,k,x,y) \<in> R"
          using elem_nat_is_nat(2) bt_type by blast
        from assms(3,4) \<open>j #+ 1 #+ 1 \<in> nat\<close> show 
          "\<forall>k\<in>j #+ 1 #+ 1. BT(j #+ 1,k,x,y) \<in> R"
          using elem_nat_is_nat(2) bt_type by blast
      qed
      have "pow(j #+ 1,x\<ra>y) = ?s\<^sub>0\<cdot>x \<ra> ?s\<^sub>0\<cdot>y"
      proof - 
        from assms(3,4) \<open>j\<in>nat\<close> have 
          "pow(j #+ 1,x\<ra>y) = pow(j,x\<ra>y)\<cdot>x \<ra> pow(j,x\<ra>y)\<cdot>y"
          using Ring_ZF_1_L4(1) mult_pow_type nat_mult_pow_add_one(2) 
            ring_oper_distr(1) by simp
        with A show  ?thesis by simp
      qed
      also have "?s\<^sub>0\<cdot>x \<ra> ?s\<^sub>0\<cdot>y = ?s\<^sub>1 \<ra> ?s\<^sub>2"
      proof -
        from assms(3) \<open>j #+ 1 \<in> nat\<close> I have "?s\<^sub>0\<cdot>x = ?s\<^sub>1" 
          by (rule fin_sum_distrib)
        moreover from assms(4) \<open>j #+ 1 \<in> nat\<close> I
        have "?s\<^sub>0\<cdot>y = ?s\<^sub>2" by (rule fin_sum_distrib)
        ultimately show ?thesis by simp
      qed
      also have "?s\<^sub>1 \<ra> ?s\<^sub>2 = 
        (BT(j,0,x,y)\<cdot>x \<ra> ?s\<^sub>3) \<ra> (?s\<^sub>4 \<ra> BT(j,j,x,y)\<cdot>y)"
      proof -
        from \<open>j\<in>nat\<close> II have "?s\<^sub>1 = BT(j,0,x,y)\<cdot>x \<ra> ?s\<^sub>3"
          using rng_seq_sum_pull_one_elem(1) by simp
        moreover from \<open>j\<in>nat\<close> III have "?s\<^sub>2 = ?s\<^sub>4 \<ra> BT(j,j,x,y)\<cdot>y"
          using rng_seq_sum_pull_one_elem(2) by simp
        ultimately show ?thesis by simp
      qed
      also from assms(3,4) IV V \<open>j\<in>nat\<close> have
        "(BT(j,0,x,y)\<cdot>x \<ra> ?s\<^sub>3) \<ra> (?s\<^sub>4 \<ra> BT(j,j,x,y)\<cdot>y) =
        BT(j,0,x,y)\<cdot>x \<ra> (?s\<^sub>3 \<ra> ?s\<^sub>4) \<ra> BT(j,j,x,y)\<cdot>y"
        using bt_type Ring_ZF_1_L4(3) add_monoid.sum_in_mono Ring_ZF_2_L2(3)
        by simp
      also have "BT(j,0,x,y)\<cdot>x \<ra> (?s\<^sub>3 \<ra> ?s\<^sub>4) \<ra> BT(j,j,x,y)\<cdot>y = 
        BT(j,0,x,y)\<cdot>x \<ra> ?s\<^sub>5 \<ra> BT(j,j,x,y)\<cdot>y"
      proof -
        from \<open>j\<in>nat\<close> IV V have "?s\<^sub>3 \<ra> ?s\<^sub>4 = ?s\<^sub>5"
          using sum_ring_distrib by simp
        thus ?thesis by simp
      qed
      also from assms(1,3,4) \<open>j\<in>nat\<close> have 
        "BT(j,0,x,y)\<cdot>x \<ra> ?s\<^sub>5 \<ra> BT(j,j,x,y)\<cdot>y =
        BT(j,0,x,y)\<cdot>x \<ra> ?s\<^sub>6 \<ra> BT(j,j,x,y)\<cdot>y"
        using bt_rec_identity by simp
      also have "BT(j,0,x,y)\<cdot>x \<ra> ?s\<^sub>6 \<ra> BT(j,j,x,y)\<cdot>y =
        ?s\<^sub>7 \<ra> BT(j,j,x,y)\<cdot>y"
      proof -
        from \<open>j\<in>nat\<close> VI have "?s\<^sub>7 = BT(j #+ 1,0,x,y) \<ra> ?s\<^sub>6"
          by (rule rng_seq_sum_pull_one_elem)
        with assms(3) \<open>j\<in>nat\<close> show ?thesis
          using bt_at_zero2 by simp
      qed
      also have "?s\<^sub>7 \<ra> BT(j,j,x,y)\<cdot>y = ?s\<^sub>8"
      proof -
        from \<open>j #+ 1 \<in> nat\<close> VII have 
          "?s\<^sub>8 = ?s\<^sub>7 \<ra> BT(j #+ 1,j #+ 1,x,y)"
          by (rule rng_seq_sum_pull_one_elem)
        with assms(4) \<open>j\<in>nat\<close> show ?thesis 
          using bt_at_right1 by simp
      qed
      finally have "pow(j #+ 1,x\<ra>y) =  ?s\<^sub>8" by simp
    } thus ?thesis by simp
  qed
  ultimately have "pow(n,x\<ra>y) = \<Sum>{\<langle>k,BT(n,k,x,y)\<rangle>. k\<in>n #+ 1}" 
    by (rule ind_on_nat1)
  then show ?thesis unfolding BT_def by simp
qed

end
