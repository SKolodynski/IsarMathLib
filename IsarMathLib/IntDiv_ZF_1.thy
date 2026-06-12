(*
    This file is a part of IsarMathLib -
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2026  Daniel de la Concepcion

    This program is free software; Redistribution and use in source and binary forms,
    with or without modification, are permitted provided that the following conditions are met:

   1. Redistributions of source code must retain the above copyright notice,
   this list of conditions and the following disclaimer.
   2. Redistributions in binary form must reproduce the above copyright notice,
   this list of conditions and the following disclaimer in the documentation and/or
   other materials provided with the distribution.
   3. The name of the author may not be used to endorse or promote products
   derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE AUTHOR `AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES,
INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT,
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

section \<open>Integer division: three as a modulus\<close>

theory IntDiv_ZF_1 imports IntDiv_ZF_IML

begin

text\<open>This theory collects arithmetic facts about integer division and remainders
  that are needed for indexing constructions, in particular the properties of $3$
  as a modulus used to interleave three families of groups into a single
  $\mathbb{Z}$-indexed family (the long exact sequence in homology).\<close>

text\<open>The left summand can be reduced modulo $p$ without changing the remainder
  of the sum: $(n+m) \bmod p = ((n \bmod p) + m) \bmod p$.\<close>

lemma (in int0) zmod_add_left:
  assumes "n\<in>\<int>" "m\<in>\<int>" "p\<in>\<int>"
  shows "(n\<ra>m) zmod p = ((n zmod p)\<ra>m) zmod p"
proof-
  have "(n \<ra> m) zmod p = (n $+ m)zmod p" using Int_ZF_1_L2(1)[OF assms(1,2)]
    by auto
  also have "\<dots> = ((n zmod p) $+ m) zmod p" using zmod_zadd_left_eq[of n m p].
  also have "\<dots> = ((n zmod p) \<ra> m) zmod p" using Int_ZF_1_L2(1)[OF _ assms(2)]
    by auto
  ultimately show ?thesis by auto
qed

subsection\<open>Properties of three as a modulus\<close>

text\<open>Three is a positive integer.\<close>

lemma (in int0) three_pos: shows "\<three> \<in> \<int>\<^sub>+"
  using int_two_three_are_int int_one_two_are_pos Int_ZF_2_L12B Int_ZF_1_5_L7
  by auto

text\<open>Three satisfies the positivity preconditions needed for \<open>zmod\<close> and \<open>zdiv\<close>.\<close>

lemma (in int0) three_zmod_prec: shows "\<zero> \<lsq> \<three>"  "\<three> \<noteq> \<zero>"
  using three_pos Int_ZF_1_5_L3 Int_ZF_2_L16C by auto

text\<open>For any integer $m$, $m \bmod 3$ is either $0$, $1$, or $2$.\<close>

lemma (in int0) zmod_three_cases:
  assumes "m \<in> \<int>"
  shows "m zmod \<three> = \<zero> \<or> m zmod \<three> = \<one> \<or> m zmod \<three> = \<two>"
proof -
  let ?r = "m zmod \<three>"
  have T: "\<zero> \<in> \<int>" "\<one> \<in> \<int>" "\<two> \<in> \<int>" "\<three> \<in> \<int>"
    using int_zero_one_are_int int_two_three_are_int by auto
  have three_rs_one: "\<three>\<rs>\<one> = \<two>"
    using T Int_ZF_1_T2 group0.inv_cancel_two by simp
  have rule:"\<And>m n. m \<in> \<int> \<Longrightarrow>
    \<zero> \<lsq> n \<Longrightarrow> n \<noteq> \<zero> \<Longrightarrow> \<zero> \<lsq> m zmod n"
    and "\<And>m n. m \<in> \<int> \<Longrightarrow>
    \<zero> \<lsq> n \<Longrightarrow> n \<noteq> \<zero> \<Longrightarrow> m zmod n \<lsq> (n\<rs>\<one>)"
    using IntDiv_ZF_1_L2(1,4) by auto
  then have "\<And>m. m:\<int> \<Longrightarrow> \<zero> \<lsq> m zmod \<three>"
    and "\<And>m n. m \<in> \<int> \<Longrightarrow> m zmod \<three> \<lsq> (\<three>\<rs>\<one>)" using three_zmod_prec
    by auto
  then have bnd: "\<zero> \<lsq> ?r" "?r \<lsq> \<two>"
    using assms three_rs_one by auto
  have rT: "?r \<in> \<int>"
    using bnd(1) Int_ZF_2_L1A by simp
  from rT T have "?r = \<zero> \<or> (?r \<lsq> \<zero>\<rs>\<one>) \<or> (\<zero>\<ra>\<one> \<lsq> ?r)"
    using Int_ZF_1_3_L6B by auto
  then show ?thesis
  proof (elim disjE)
    assume "?r = \<zero>" then show ?thesis by simp
  next
    assume A: "?r \<lsq> \<zero>\<rs>\<one>"
    with bnd(1) have "\<zero> \<lsq> \<zero>\<rs>\<one>"
      by (rule Int_order_transitive)
    with T have False using Int_ZF_1_2_L3AA by simp
    then show ?thesis by simp
  next
    assume A: "\<zero>\<ra>\<one> \<lsq> ?r"
    with T have one_le: "\<one> \<lsq> ?r"
      using Int_ZF_1_1_L4 by simp
    from rT T have "?r = \<one> \<or> (?r \<lsq> \<one>\<rs>\<one>) \<or> (\<one>\<ra>\<one> \<lsq> ?r)"
      using Int_ZF_1_3_L6B by auto
    then show ?thesis
    proof (elim disjE)
      assume "?r = \<one>" then show ?thesis by simp
    next
      assume "?r \<lsq> \<one>\<rs>\<one>"
      with one_le have "\<one> \<lsq> \<one>\<rs>\<one>"
        by (rule Int_order_transitive)
      with T have False using Int_ZF_1_2_L3AA by simp
      then show ?thesis by simp
    next
      assume "\<one>\<ra>\<one> \<lsq> ?r"
      with bnd(2) have "?r = \<two>"
        using Int_ZF_2_L3 by simp
      then show ?thesis by simp
    qed
  qed
qed

text\<open>If $m \bmod 3 = 0$ then $(m-1) \bmod 3 = 2$.\<close>

corollary (in int0) zmod_0_minus_one:
  assumes "m \<in> \<int>"
  and "m zmod \<three> = \<zero>"
  shows "(m\<rs>\<one>) zmod \<three> = \<two>"
proof -
  have "(m\<rs>\<one>) zmod \<three> = ((m zmod \<three>)\<rs>\<one>) zmod \<three>"
    using zmod_add_left[OF assms(1) int_neg_type[OF int_zero_one_are_int(2)] 
        int_two_three_are_int(2)] by auto
  also have "\<dots> = (\<zero>\<rs>\<one>)zmod \<three>" using assms(2) by auto
  also have "\<dots> = \<two>"
  proof -
    have T: "\<zero>\<in>\<int>" "\<one>\<in>\<int>" "\<two>\<in>\<int>" "\<three>\<in>\<int>"
      using int_zero_one_are_int int_two_three_are_int by auto
    have zr1: "\<zero>\<rs>\<one> \<in> \<int>"
      by (rule Int_ZF_1_1_L5(2)[OF T(1) T(2)])
    have S1: "(\<zero>\<rs>\<one>)\<ra>\<one> = \<zero>"
      using T Int_ZF_1_T2 group0.inv_cancel_two by simp
    have S2: "((\<zero>\<rs>\<one>)\<ra>\<one>)\<ra>\<two> = \<two>"
      using S1 T(3) Int_ZF_1_1_L4(2) by simp
    have S3: "((\<zero>\<rs>\<one>)\<ra>\<one>)\<ra>\<two> = (\<zero>\<rs>\<one>)\<ra>\<three>"
      using Int_ZF_1_1_L7(1)[OF zr1 T(2) T(3)] Int_ZF_1_1_L5(4)[OF T(2) T(3)] by simp
    have eq: "(\<zero>\<rs>\<one>)\<ra>\<three> = \<two>" using S2 S3 by simp
    have conv: "((\<zero>\<rs>\<one>)\<ra>\<three>) zmod \<three> = (\<zero>\<rs>\<one>) zmod \<three>"
      using Int_ZF_1_L2(1)[OF zr1 T(4)] zmod_zadd_self2 by simp
    have lt23: "\<two> $< \<three>"
    proof -
      have "\<two> \<lsq> \<three>" using T(3) Int_ZF_2_L12B by simp
      moreover have "\<two> \<noteq> \<three>" using Int_ZF_1_L14(1)[OF T(3)] by auto
      ultimately show ?thesis using Int_ZF_2_L9 by auto
    qed
    have le02: "\<zero> \<lsq> \<two>"
    proof -
      have "\<zero> \<lsq> \<one>" using T Int_ZF_2_L12B[of \<zero>] Int_ZF_1_1_L4 by simp
      moreover have "\<one> \<lsq> \<two>" using Int_ZF_2_L16B by simp
      ultimately show ?thesis using Int_order_transitive by auto
    qed
    have h1: "#0 $\<le> \<two>" using le02 Int_ZF_2_L1A Int_ZF_1_L8 by auto
    have two_mod: "\<two> zmod \<three> = \<two>"
      using zmod_pos_pos_trivial[OF h1 lt23] T(3) intify_ident by auto
    from eq conv two_mod show ?thesis by auto
  qed
  finally show ?thesis by auto
qed

text\<open>If $m \bmod 3 = 1$ then $(m-1) \bmod 3 = 0$.\<close>

corollary (in int0) zmod_1_minus_one:
  assumes "m \<in> \<int>"
  and "m zmod \<three> = \<one>"
  shows "(m\<rs>\<one>) zmod \<three> = \<zero>"
proof -
  have "(m\<rs>\<one>) zmod \<three> = ((m zmod \<three>)\<rs>\<one>) zmod \<three>"
    using zmod_add_left[OF assms(1) int_neg_type[OF int_zero_one_are_int(2)] 
        int_two_three_are_int(2)] by auto
  also have "\<dots> = (\<one>\<rs>\<one>)zmod \<three>" using assms(2) by auto
  also have "\<dots> = \<zero> zmod \<three>" using Int_ZF_1_L10[OF int_zero_one_are_int(2) int_zero_one_are_int(2)]
    zadd_zminus_inverse[of \<one>] Int_ZF_1_L8(1) by auto
  finally have "(m\<rs>\<one>) zmod \<three> = \<zero> zmod \<three>" by auto
  then show ?thesis using Int_ZF_1_L8(1) zmod_zero by auto
qed

text\<open>If $m \bmod 3 = 2$ then $(m-1) \bmod 3 = 1$.\<close>

corollary (in int0) zmod_2_minus_one:
  assumes "m \<in> \<int>"
  and "m zmod \<three> = \<two>"
  shows "(m\<rs>\<one>) zmod \<three> = \<one>"
proof -
  have "(m\<rs>\<one>) zmod \<three> = ((m zmod \<three>)\<rs>\<one>) zmod \<three>"
    using zmod_add_left[OF assms(1) int_neg_type[OF int_zero_one_are_int(2)] 
        int_two_three_are_int(2)] by auto
  also have "\<dots> = (\<two>\<rs>\<one>)zmod \<three>" using assms(2) by auto
  also have "\<dots> = \<one> zmod \<three>"
    using int_zero_one_are_int int_two_three_are_int Int_ZF_1_T2 group0.inv_cancel_two by simp
  also have "\<dots> = \<one>"
  proof -
    have T: "\<zero>\<in>\<int>" "\<one>\<in>\<int>" "\<two>\<in>\<int>" "\<three>\<in>\<int>"
      using int_zero_one_are_int int_two_three_are_int by auto
    have h1: "#0 $\<le> \<one>"
    proof -
      have "\<zero> \<lsq> \<one>" using T Int_ZF_2_L12B[of \<zero>] Int_ZF_1_1_L4 by simp
      then show ?thesis using Int_ZF_2_L1A Int_ZF_1_L8 by auto
    qed
    have h2: "\<one> $< \<three>"
    proof -
      have le12: "\<one> \<lsq> \<two>" using Int_ZF_2_L16B by simp
      moreover have "\<one> \<noteq> \<two>" using T(2) Int_ZF_1_L14(1)[of \<one>] by auto
      ultimately have lt12: "\<one> $< \<two>" using Int_ZF_2_L9 by auto
      have "\<two> \<lsq> \<three>" using T(3) Int_ZF_2_L12B by simp
      then have le23: "\<two> $\<le> \<three>" using Int_ZF_2_L1A by auto
      show ?thesis using lt12 le23 zless_zle_trans by auto
    qed
    show ?thesis using zmod_pos_pos_trivial[OF h1 h2] T(2) intify_ident by auto
  qed
  finally show ?thesis by auto
qed

text\<open>If $m \bmod 3 = 2$ then $(m+1) \bmod 3 = 0$.\<close>

corollary (in int0) zmod_2_plus_one:
  assumes "m \<in> \<int>"
  and "m zmod \<three> = \<two>"
  shows "(m \<ra> \<one>) zmod \<three> = \<zero>"
proof -
  have "(m \<ra> \<one>) zmod \<three> = ((m zmod \<three>) \<ra> \<one>) zmod \<three>"
    using zmod_add_left[OF assms(1) Int_ZF_1_L8A(2) int_two_three_are_int(2)] by auto
  also have "\<dots> = (\<two> \<ra> \<one>) zmod \<three>" using assms(2) by auto
  also have "\<dots> = \<three> zmod \<three>" by simp
  also have "\<dots> = \<zero>"
  proof -
    have "\<three> zmod \<three> = $#0" using zmod_self by simp
    then show ?thesis using Int_ZF_1_L8(1) by auto
  qed
  finally show ?thesis by auto
qed

text\<open>If $m \bmod 3 = 0$ then $(m+1) \bmod 3 = 1$.\<close>

corollary (in int0) zmod_0_plus_one:
  assumes "m \<in> \<int>"
  and "m zmod \<three> = \<zero>"
  shows "(m \<ra> \<one>) zmod \<three> = \<one>"
proof -
  have "(m \<ra> \<one>) zmod \<three> = ((m zmod \<three>) \<ra> \<one>) zmod \<three>"
    using zmod_add_left[OF assms(1) Int_ZF_1_L8A(2) int_two_three_are_int(2)] by auto
  also have "\<dots> = (\<zero> \<ra> \<one>) zmod \<three>" using assms(2) by auto
  also have "\<dots> = \<one> zmod \<three>" using Int_ZF_1_1_L4(2) Int_ZF_1_L8A(2) by simp
  also have "\<dots> = \<one>"
  proof -
    have T: "\<zero>\<in>\<int>" "\<one>\<in>\<int>" "\<two>\<in>\<int>" "\<three>\<in>\<int>"
      using int_zero_one_are_int int_two_three_are_int by auto
    have h1: "#0 $\<le> \<one>"
    proof -
      have "\<zero> \<lsq> \<one>" using T Int_ZF_2_L12B[of \<zero>] Int_ZF_1_1_L4 by simp
      then show ?thesis using Int_ZF_2_L1A Int_ZF_1_L8 by auto
    qed
    have h2: "\<one> $< \<three>"
    proof -
      have le12: "\<one> \<lsq> \<two>" using Int_ZF_2_L16B by simp
      moreover have "\<one> \<noteq> \<two>" using T(2) Int_ZF_1_L14(1)[of \<one>] by auto
      ultimately have lt12: "\<one> $< \<two>" using Int_ZF_2_L9 by auto
      have "\<two> \<lsq> \<three>" using T(3) Int_ZF_2_L12B by simp
      then have le23: "\<two> $\<le> \<three>" using Int_ZF_2_L1A by auto
      show ?thesis using lt12 le23 zless_zle_trans by auto
    qed
    show ?thesis using zmod_pos_pos_trivial[OF h1 h2] T(2) intify_ident by auto
  qed
  finally show ?thesis by auto
qed

text\<open>Adding three and dividing by three increments the quotient by one.\<close>

corollary (in int0) zdiv_add_three:
  assumes "m \<in> \<int>"
  shows "(m \<ra> \<three>) zdiv \<three> = m zdiv \<three> \<ra> \<one>"
proof -
  have T3: "\<three> \<in> \<int>" using int_two_three_are_int by auto
  have three_ne: "\<three> \<noteq> $#0"
    using three_zmod_prec(2) Int_ZF_1_L8(1) by auto
  have add_eq: "m \<ra> \<three> = m $+ \<three>"
    using Int_ZF_1_L2(1)[OF assms T3] by simp
  have div_eq: "(m $+ \<three>) zdiv \<three> = m zdiv \<three> $+ $#1"
    using zdiv_zadd_self2 three_ne intify_ident T3 by simp
  have one_eq: "m zdiv \<three> \<ra> \<one> = m zdiv \<three> $+ $#1"
    using Int_ZF_1_L2(1)[OF _ Int_ZF_1_L8A(2)] zdiv_type
      Int_ZF_1_L8(2) by simp
  from add_eq div_eq one_eq show ?thesis by simp
qed

text\<open>Dividing $m+2$ by three and subtracting one gives the same result as
  dividing $m-1$ by three.\<close>

corollary (in int0) zdiv_minus_one:
  assumes "m\<in>\<int>"
  shows "((m\<ra>\<two>) zdiv \<three>) \<rs>\<one> = (m\<rs>\<one>) zdiv \<three>"
proof -
  have T1: "m\<rs>\<one> \<in> \<int>" using assms int_zero_one_are_int Int_ZF_1_1_L5 by auto
  have arith: "m\<rs>\<one>\<ra>\<three> = m\<ra>\<two>"
  proof -
    have h1: "m\<rs>\<one>\<ra>\<one> = m"
      using assms int_zero_one_are_int
        group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3)] by simp
    have h2: "m\<rs>\<one>\<ra>\<one>\<ra>\<two> = m\<rs>\<one>\<ra>\<three>"
      using Int_ZF_1_2_L11(1)[OF T1] by simp
    show ?thesis using h1 h2[symmetric] by simp
  qed
  have main: "(m\<ra>\<two>) zdiv \<three> = (m\<rs>\<one>) zdiv \<three> \<ra> \<one>"
    using arith zdiv_add_three[OF T1] by simp
  show ?thesis
    using main zdiv_type int_zero_one_are_int
      group0.inv_cancel_two(2)[OF Int_ZF_1_T2(3)] by simp
qed

end
