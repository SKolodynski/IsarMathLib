(*   This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2008  Seo Sanghyeon

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

section \<open>Order on natural numbers\<close>

theory NatOrder_ZF imports Nat_ZF_IML Order_ZF

begin

text\<open>This theory proves that $\leq$ is a linear order on $\mathbb{N}$.
  $\leq$ is defined in Isabelle's \<open>Nat\<close> theory, and
  linear order is defined in \<open>Order_ZF\<close> theory. 
  Contributed by Seo Sanghyeon.\<close>

subsection\<open>Order on natural numbers\<close>

text\<open>This is the only section in this theory.\<close>

text\<open>If $a,b$ are natural numbers then $a$ is less or equal $b$ or $b$ is
  (strictly) less than $a$. We use a result on ordinals in the proof. \<close>

lemma nat_order_2cases:  assumes "a\<in>nat" and "b\<in>nat"
  shows "a \<le> b \<or> b < a"
proof -
   from assms have I: "Ord(a) \<and> Ord(b)"
    using nat_into_Ord by auto
  then have "a \<in> b \<or> a = b \<or> b \<in> a"
    using Ord_linear by simp
  with I have "a < b \<or> a = b \<or> b < a"
    using ltI by auto
  with I show "a \<le> b \<or> b < a"
    using le_iff by auto
qed

text\<open>A special case of \<open>nat_order_2cases\<close>: If $a,b$ are natural numbers then 
  $a$ is less or equal $b$ or $b$ is less or equal than $a$. \<close>

lemma NatOrder_ZF_1_L1:
  assumes "a\<in>nat" and "b\<in>nat"
  shows "a \<le> b \<or> b \<le> a"
  using assms nat_order_2cases leI by auto

text\<open>$\leq$ is antisymmetric, transitive, total, and linear. Proofs by
  rewrite using definitions.\<close>

lemma NatOrder_ZF_1_L2:
  shows
  "antisym(Le)"
  "trans(Le)"
  "Le {is total on} nat"
  "IsLinOrder(nat,Le)"
proof -
  show "antisym(Le)"
    using antisym_def Le_def le_anti_sym by auto
  moreover show "trans(Le)"
    using trans_def Le_def le_trans by blast
  moreover show "Le {is total on} nat"
    using IsTotal_def Le_def NatOrder_ZF_1_L1 by simp
  ultimately show "IsLinOrder(nat,Le)"
    using IsLinOrder_def by simp
qed

text\<open>The order on natural numbers is linear on every natural number.
  Recall that each natural number is a subset of the set of 
  all natural numbers (as well as a member).\<close>

lemma natord_lin_on_each_nat: 
  assumes A1: "n \<in> nat" shows "IsLinOrder(n,Le)"
proof -
  from A1 have "n \<subseteq> nat" using nat_subset_nat
    by simp
  then show ?thesis using NatOrder_ZF_1_L2 ord_linear_subset
    by blast
qed

end
