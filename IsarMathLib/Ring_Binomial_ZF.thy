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

subsection\<open>Sums of multipliciities of powers of ring elements\<close>

text\<open>The binomial theorem asserts that for any two elements of a commutative ring
  the n-th power of the sum $x+y$ can be written as a sum of certain multiplicities of terms 
  $x^{n-k}y^k$, where $k \in 0..n$. In this section we setup the notation and prove basic properties
  of such multiplicities and powers of ring elements. \<close>

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

text\<open>Distributive laws for finite sums in a ring: 
  $(\sum_{k=0}^{n-1}q(k))\cdot x = \sum_{k=0}^{n-1}q(k)\cdot x$ and 
  $x\cdot (\sum_{k=0}^{n-1}q(k)) = \sum_{k=0}^{n-1}x\cdot q(k)$. \<close>

theorem (in ring3) fin_sum_distrib: 
  assumes "n\<in>nat" "\<forall>k\<in>n. q(k) \<in> R" "x\<in>R"
  shows 
    "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n})\<cdot>x = \<Sum>{\<langle>k,q(k)\<cdot>x\<rangle>. k\<in>n}"
    "x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>n}) = \<Sum>{\<langle>k,x\<cdot>q(k)\<rangle>. k\<in>n}"
proof -
  from assms(1,3) have "n\<in>nat" and 
    "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>0})\<cdot>x = \<Sum>{\<langle>k,q(k)\<cdot>x\<rangle>. k\<in>0}"
    using add_monoid.sum_empty Ring_ZF_1_L6(1) by simp_all
  moreover have 
    "\<forall>j\<in>n. (\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j})\<cdot>x = (\<Sum>{\<langle>k,q(k)\<cdot>x\<rangle>. k\<in>j})
    \<longrightarrow> (\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1})\<cdot>x = \<Sum>{\<langle>k,q(k)\<cdot>x\<rangle>. k\<in>j #+ 1}"
  proof -
    { fix j assume "j\<in>n" and 
        I: "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j})\<cdot>x = (\<Sum>{\<langle>k,q(k)\<cdot>x\<rangle>. k\<in>j})"
      from assms(1) \<open>j\<in>n\<close> have "j\<in>nat" using elem_nat_is_nat(2) 
        by simp
      moreover from assms(1,2) \<open>j\<in>n\<close> have II: "\<forall>k\<in>j #+ 1. q(k) \<in> R"
        using mem_add_one_subset by blast
      ultimately have     
        "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1}) =  (\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) \<ra> q(j)"
        using add_monoid.seq_sum_pull_one_elem(2) by simp
      hence 
        "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1})\<cdot>x = ((\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) \<ra> q(j))\<cdot>x"
        by simp
      moreover from assms(3) \<open>j\<in>nat\<close> II have
        "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) \<in> R" "q(j) \<in> R" and "x\<in>R" 
        using add_monoid.sum_in_mono by simp_all
      ultimately have 
        "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1})\<cdot>x = (\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j})\<cdot>x \<ra> q(j)\<cdot>x"
        using ring_oper_distr(2) by simp
      with I have 
        "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1})\<cdot>x = (\<Sum>{\<langle>k,q(k)\<cdot>x\<rangle>. k\<in>j})  \<ra> q(j)\<cdot>x" 
        by simp
      moreover 
      from assms(3) II have "\<forall>k\<in>j #+ 1. q(k)\<cdot>x \<in> R"
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
  from assms(1,3) have "n\<in>nat" and 
    "x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>0}) = \<Sum>{\<langle>k,x\<cdot>q(k)\<rangle>. k\<in>0}"
    using add_monoid.sum_empty Ring_ZF_1_L6(2) by simp_all
  moreover have 
    "\<forall>j\<in>n. x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) = (\<Sum>{\<langle>k,x\<cdot>q(k)\<rangle>. k\<in>j})
    \<longrightarrow> x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1}) = \<Sum>{\<langle>k,x\<cdot>q(k)\<rangle>. k\<in>j #+ 1}" 
  proof -
    { fix j assume "j\<in>n" and 
        I: "x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) = (\<Sum>{\<langle>k,x\<cdot>q(k)\<rangle>. k\<in>j})"
      from assms(1) \<open>j\<in>n\<close> have "j\<in>nat" using elem_nat_is_nat(2) 
        by simp
      moreover from assms(1,2) \<open>j\<in>n\<close> have II: "\<forall>k\<in>j #+ 1. q(k) \<in> R"
        using mem_add_one_subset by blast
      ultimately have     
        "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1}) =  (\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) \<ra> q(j)"
        using add_monoid.seq_sum_pull_one_elem(2) by simp
      hence 
        "x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1}) = x\<cdot>((\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) \<ra> q(j))"
        by simp
      moreover from assms(3) \<open>j\<in>nat\<close> II have
        "(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) \<in> R" "q(j) \<in> R" and "x\<in>R" 
        using add_monoid.sum_in_mono by simp_all
       ultimately have 
        "x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1}) = x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j}) \<ra> x\<cdot>q(j)"
        using ring_oper_distr(1) by simp
       with I have 
        "x\<cdot>(\<Sum>{\<langle>k,q(k)\<rangle>. k\<in>j #+ 1}) =  (\<Sum>{\<langle>k,x\<cdot>q(k)\<rangle>. k\<in>j})  \<ra> x\<cdot>q(j)" 
        by simp
      moreover 
      from assms(3) II have "\<forall>k\<in>j #+ 1. x\<cdot>q(k) \<in> R"
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
  
end
