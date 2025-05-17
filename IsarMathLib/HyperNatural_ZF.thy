(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2024 Daniel de la Concepcion

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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. *)

section \<open>Hypernatural numbers\<close>

theory HyperNatural_ZF imports UltraConstruction_ZF ZF.Cardinal Finite1
begin

text\<open>The goal of this file is to show that hyperfinite sets are the sets of
hypernatural numbers internally bijective with an open left ray of hypernatural.\<close>

text\<open>The cardinality of a non-trivial set difference is 
strictly smaller for finite sets\<close>

lemma finite_diff_strict_smaller: assumes "Finite(A)" "A\<noteq>0" "A\<inter>B\<noteq>0"
  shows "|A-B| < |A|"
proof -
  from assms(3) obtain x where x:"x\<in>B" "x\<in>A" by auto
  from x(1) have "x\<notin>A-B" by auto moreover note x(2) moreover
  from assms(1) have "A\<in>FinPow(A)" unfolding FinPow_def by auto
  then have "A-B\<in>FinPow(A)" using subset_finpow[of A A "A-B"] by auto
  ultimately have "|(A-B)\<union>{x}| = succ(|A-B|)" using card_fin_add_one(1)[of "A-B" A x] by auto
  then have A:"|A-B| < |(A-B)\<union>{x}|" using le_refl[OF Ord_cardinal] by auto
  moreover have "(A-B)\<union>{x} \<subseteq> A" using x(2) by auto
  then have "(A-B)\<union>{x} \<lesssim> A" using subset_imp_lepoll by auto
  then have "|(A-B)\<union>{x}| \<le> |A|" using well_ord_lepoll_imp_cardinal_le Finite_imp_well_ord[OF assms(1)]
    by auto
  with A show ?thesis using lt_trans2 by auto
qed

text\<open>This applies to strict subsets\<close>

corollary strict_subset_smaller: assumes "Finite(A)" "B \<subseteq> A" "B\<noteq>A"
  shows "|B| < |A|"
proof-
  {
    assume a0:"A = 0"
    with assms(2) have "B = 0" by auto
    with a0 assms(3) have False by auto
  }
  then have "A\<noteq>0" by auto moreover
  have "A\<inter>(A-B) \<noteq>0" using assms(2,3) by auto moreover
  note assms(1) ultimately
  have "|A-(A-B)| < |A|" using finite_diff_strict_smaller by auto
  moreover have "A-(A-B) = B" using assms(2) by auto
  ultimately show ?thesis by auto
qed

text\<open>It can be further applied to solve the relation between 
injective and bijective functions on finite sets.\<close>

corollary inj_function_same_card_bij: assumes "Finite(B)" "A \<approx> B" "f\<in>inj(A,B)"
  shows "f\<in>bij(A,B)"
proof-
  have "f``A \<subseteq> B" using func1_1_L6(2) inj_is_fun[OF assms(3)] by auto
  with assms(1) have R:"f``A \<noteq> B \<Longrightarrow> |f``A| < |B|" using strict_subset_smaller by auto
  from assms(3) have "f:bij(A,range(f))" using inj_bij_range by auto
  then have "A\<approx>range(f)" unfolding eqpoll_def by auto
  then have "A\<approx>f``A" using range_image_domain[OF inj_is_fun[OF assms(3)]] by auto
  then have "|A| = |f``A|" using cardinal_cong by auto moreover
  have "|A| = |B|" using cardinal_cong assms(2) by auto ultimately
  have "|f``A| = |B|" by auto
  with R have "f``A \<noteq> B \<Longrightarrow> |B| < |B|" by auto
  then have A:"f``A = B" using lt_not_refl by auto
  then show ?thesis using surj_def_alt assms(3) inj_is_fun unfolding bij_def 
    by auto
qed

text\<open>This locale deals with hyper numbers.\<close>

locale hyperNatural = ultra _ nat "\<lambda>_. nat" +
  assumes non_pricipal_filter:"\<Inter>\<FF> = 0"

begin

abbreviation hyperNat ("*\<nat>") where
"*\<nat> \<equiv> hyper_set"

definition seq_class ("[_]") where
"x\<in>nat\<rightarrow>nat \<Longrightarrow> [x] \<equiv> hyper_rel``{x}"

definition omega ("\<omega>") where
"\<omega> = [id(nat)]"

definition incl ("*_" 70) where
"x\<in>nat \<Longrightarrow> *x \<equiv> [ConstantFunction(nat,x)]"

lemma incl_inj_nat:
  shows "{\<langle>x,*x\<rangle>. x\<in>nat} \<in> inj(nat, *\<nat>)" using incl_inj[of nat] 
    seq_class_def[OF func1_3_L1] incl_def
  unfolding incl_def by auto

lemma omega_not_nat:
  shows "x\<in>nat\<longrightarrow>(*x) \<noteq> \<omega>" and "\<omega>:*\<nat>"
proof
  have "id(nat):nat\<rightarrow>nat" using id_def by auto
  then have "[id(nat)]:*\<nat>" using seq_class_def[of "id(nat)"]
    unfolding hyper_set_def quotient_def by auto
  then show "\<omega>:*\<nat>" unfolding omega_def by auto
  {
    assume a:"x\<in>nat" "(*x) = \<omega>"
    from a(2) have "[ConstantFunction(nat,x)] = [id(nat)]"
      unfolding omega_def incl_def[OF a(1)].
    then have "\<langle>ConstantFunction(nat,x),id(nat)\<rangle>\<in>hyper_rel"
      using same_image_equiv[OF hyper_equiv, of "id(nat)"] inj_is_fun[OF id_inj]
      unfolding seq_class_def[OF inj_is_fun[OF id_inj]] seq_class_def[OF func1_3_L1[OF a(1)]] by auto
    then have "{n\<in>nat. ConstantFunction(nat,x)`n = id(nat)`n}:\<FF>" unfolding hyper_rel_def by auto
    then have "{n\<in>nat. x = n}:\<FF>" using apply_equality[of _ _ "id(nat)" nat "\<lambda>_. nat"] inj_is_fun[OF id_inj]
      func1_3_L2[of _ nat x] by auto moreover
    have "{n\<in>nat. x = n} = {x}" using a(1) by auto ultimately
    have f:"{x}:\<FF>" by auto
    {
      fix A assume x:"x\<in>A" "A\<subseteq> nat"
      then have "{x} \<subseteq> A" by auto
      then have "A:\<FF>" using f ultraFilter x(2) unfolding IsFilter_def IsUltrafilter_def by auto
    }
    then have "{A\<in>Pow(nat). x:A} \<subseteq> \<FF>" by auto moreover
    {
      fix A assume a:"A\<in>\<FF>"
      with f have y:"A\<inter>{x}:\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def
          by auto
      {
        assume "x\<notin>A"
        then have "A\<inter>{x} = 0" by auto
        with y have "0:\<FF>" by auto
        then have False using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
      }
      then have "x:A" by auto
      moreover from a have "A\<in>Pow(nat)" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
      ultimately have "A\<in>{A\<in>Pow(nat). x:A}" by auto
    }
    then have "\<FF> \<subseteq> {A\<in>Pow(nat). x:A}" by auto ultimately
    have "\<FF> = {A\<in>Pow(nat). x:A}" by auto
    then have "\<FF>=0 \<or> x\<in>\<Inter>\<FF>" by auto
    with non_pricipal_filter have "\<FF>=0" by auto
    then have False using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  }
  then show "x \<in> nat \<Longrightarrow> (*x) \<noteq> \<omega>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
qed

text\<open>We define the order relation as the internal relation created
by a constant relation of order in natural numbers\<close>

definition rel_star ("*_*" 80) where
"R \<subseteq> nat\<times>nat \<Longrightarrow> *R* \<equiv> internal_rel(ConstantFunction(nat,R))"

definition lessEq_star (infix "*\<le>" 80) where
"x*\<le>y \<equiv> \<langle>x,y\<rangle>\<in>(*Le*)"

definition less_star (infix "*<" 80) where
"x*<y \<equiv> \<langle>x,y\<rangle>\<in>(*Lt*)"

text\<open>Two hypernaturals are ordered iff where their representative sequences are ordered
is a set in the filter\<close>

lemma star_rel_seq:
  assumes "x:nat\<rightarrow>nat" "y:nat\<rightarrow>nat" "R \<subseteq> nat\<times>nat"
  shows "\<langle>[x],[y]\<rangle>\<in>*R* \<longleftrightarrow> {i\<in>nat. \<langle>x`i,y`i\<rangle>\<in>R}\<in>\<FF>"
proof(safe)
have S_fun:"ConstantFunction(nat,R):nat \<rightarrow> Pow(nat\<times>nat)"
    apply (rule func1_3_L1) using assms(3) by auto
  {
    assume "\<langle>[x],[y]\<rangle>\<in>*R*"
    then have "\<langle>[x],[y]\<rangle>\<in>internal_rel(ConstantFunction(nat,R))"
      unfolding rel_star_def[OF assms(3)].
    then obtain z t where zt:"[x] = [z]" "[y] = [t]" "z:nat\<rightarrow>nat " "t:nat\<rightarrow>nat"
"{n \<in> nat . \<langle>z ` n, t ` n\<rangle> \<in> ConstantFunction(nat,R)`n} \<in> \<FF>"
      unfolding internal_rel_def[OF S_fun] using seq_class_def by auto
    from zt(5) have A:"{n \<in> nat . \<langle>z ` n, t ` n\<rangle> \<in> R} \<in> \<FF>"
      using func1_3_L2 by auto
    from zt(1) have "\<langle>x,z\<rangle>\<in>hyper_rel" unfolding seq_class_def[OF zt(3)]
      seq_class_def[OF assms(1)] using eq_equiv_class[OF _ hyper_equiv zt(3)] by auto
    then have "{n:nat. x`n = z`n}\<in>\<FF>" unfolding hyper_rel_def by auto
    with A have A:"{n \<in> nat . \<langle>z ` n,t ` n\<rangle>\<in>R}\<inter>{n:nat. x`n = z`n}\<in>\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    from zt(2) have "\<langle>y,t\<rangle>\<in>hyper_rel" unfolding seq_class_def[OF zt(4)]
      seq_class_def[OF assms(2)] using eq_equiv_class[OF _ hyper_equiv zt(4)] by auto
    then have "{n:nat. y`n = t`n}\<in>\<FF>" unfolding hyper_rel_def by auto
    with A have "{n:nat. y`n = t`n}\<inter>({n \<in> nat . \<langle>z ` n,t ` n\<rangle>\<in>R}\<inter>{n:nat. x`n = z`n})\<in>\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    then have "\<forall>B\<in>Pow(nat). {n:nat. y`n = t`n}\<inter>({n \<in> nat . \<langle>z ` n, t ` n\<rangle>\<in>R}\<inter>{n:nat. x`n = z`n}) \<subseteq> B \<longrightarrow> B\<in>\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    then have "{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R}\<in>Pow(nat) \<Longrightarrow> {n:nat. y`n = t`n}\<inter>({n \<in> nat . \<langle>z ` n, t ` n\<rangle>\<in>R}\<inter>{n:nat. x`n = z`n}) \<subseteq> {n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R} \<Longrightarrow> {n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R}\<in>\<FF>"
      by auto
    then have "{n:nat. y`n = t`n}\<inter>({n \<in> nat . \<langle>z ` n, t ` n\<rangle>\<in>R}\<inter>{n:nat. x`n = z`n}) \<subseteq> {n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R} \<Longrightarrow> {n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R}\<in>\<FF>" by auto moreover
    {
      fix n assume "n\<in>{n:nat. y`n = t`n}\<inter>({n \<in> nat . \<langle>z ` n, t ` n\<rangle>\<in>R}\<inter>{n:nat. x`n = z`n})"
      then have "n\<in>nat" "y`n = t`n" "\<langle>z ` n, t ` n\<rangle>\<in>R" "x`n = z`n" by auto
      then have "n\<in>nat" "\<langle>x`n,y`n\<rangle>\<in>R" by auto
      then have "n\<in>{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R}" by auto
    }
    then have "{n:nat. y`n = t`n}\<inter>({n \<in> nat . \<langle>z ` n, t ` n\<rangle>\<in>R}\<inter>{n:nat. x`n = z`n}) \<subseteq> {n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R}" by auto
    ultimately show "{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R}\<in>\<FF>" by auto
  }
  {
    assume "{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R}\<in>\<FF>" 
    then have "{n \<in> nat . \<langle>x ` n, y ` n\<rangle> \<in> ConstantFunction(nat,R)`n} \<in> \<FF>"
      using func1_3_L2 by auto
    with assms have "\<langle>[x],[y]\<rangle>\<in>internal_rel(ConstantFunction(nat,R))"
      unfolding internal_rel_def[OF S_fun] seq_class_def[OF assms(1)] seq_class_def[OF assms(2)]
      by auto
    then show "\<langle>[x],[y]\<rangle>\<in>*R*" unfolding rel_star_def[OF assms(3)].
  }
qed

corollary star_rel_imp_seq:
  assumes "x:nat\<rightarrow>nat" "y:nat\<rightarrow>nat" "R1 \<subseteq> R2" "R2 \<subseteq> nat\<times>nat"
  shows "\<langle>[x],[y]\<rangle>\<in>*R1* \<longrightarrow> \<langle>[x],[y]\<rangle>\<in>*R2*"
proof(safe)
  assume "\<langle>[x],[y]\<rangle>\<in>*R1*"
  then have "{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R1}\<in>\<FF>" using star_rel_seq[of x y R1] assms by auto
  moreover have "{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R1} \<subseteq> {n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R2}" using assms(3) by auto
  moreover note is_filter_def_split(5)[of \<FF> nat]
  ultimately have "{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R2}\<in>\<FF>" using ultraFilter unfolding IsUltrafilter_def by blast
  then show "\<langle>[x],[y]\<rangle>\<in>*R2*" using star_rel_seq[of x y R2] assms(1,2,4) by auto
qed

corollary star_rel_intersect_seq:
  assumes "x:nat\<rightarrow>nat" "y:nat\<rightarrow>nat" "R1 = R2\<inter>R3" "R2 \<subseteq> nat\<times>nat" "R3 \<subseteq> nat\<times>nat"
  shows "\<langle>[x],[y]\<rangle>\<in>*R1* \<longleftrightarrow> \<langle>[x],[y]\<rangle>\<in>*R2* \<and> \<langle>[x],[y]\<rangle>\<in>*R3*"
proof(safe)
  assume as:"\<langle>[x],[y]\<rangle>\<in>*R1*"
  with assms(1-4) show "\<langle>[x],[y]\<rangle>\<in>*R2*" using star_rel_imp_seq[of x y R1 R2] by auto
  from as assms(1-3,5) show "\<langle>[x],[y]\<rangle>\<in>*R3*" using star_rel_imp_seq[of x y R1 R3] by auto
next
  assume "\<langle>[x],[y]\<rangle>\<in>*R2*" "\<langle>[x],[y]\<rangle>\<in>*R3*"
  then have "{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R2}\<in>\<FF>" "{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R3}\<in>\<FF>"
    using star_rel_seq[of x y] assms(1,2,4,5) by auto
  then have "{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R2}\<inter>{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R3}\<in>\<FF>" using
    is_filter_def_split(4) ultraFilter unfolding IsUltrafilter_def by auto
  moreover have "{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R2}\<inter>{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R3} = {n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R2 \<and> \<langle>x`n,y`n\<rangle>\<in>R3}" by auto
  then have "{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R2}\<inter>{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R3} = {n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R2\<inter>R3}" by auto
  with assms(3) have "{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R2}\<inter>{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R3} = {n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R1}" by auto
  ultimately have "{n\<in>nat. \<langle>x`n,y`n\<rangle>\<in>R1}\<in>\<FF>" by auto
  then show "\<langle>[x],[y]\<rangle>\<in>*R1*" using star_rel_seq[of x y R1] assms(1-4) by auto
qed

corollary less_than_seq:
  assumes "x:nat\<rightarrow>nat" "y:nat\<rightarrow>nat"
  shows "[x] *\<le> [y] \<longleftrightarrow> {i\<in>nat. x`i \<le> y`i}\<in>\<FF>"
proof -
  have "{i \<in> nat. \<langle>x ` i, y ` i\<rangle> \<in> {\<langle>p,q\<rangle> \<in> nat \<times> nat . p \<le> q}} = {i \<in> nat. x`i \<le> y`i}"
    apply simp using assms apply_type by auto
  then have R1:"[x] *\<le> [y] \<longleftrightarrow> {i \<in> nat. \<langle>x ` i, y ` i\<rangle> \<in> {\<langle>p,q\<rangle> \<in> nat \<times> nat . p \<le> q}}\<in>\<FF> \<Longrightarrow> [x] *\<le> [y] \<longleftrightarrow> {i\<in>nat. x`i \<le> y`i}\<in>\<FF>" by auto
  have "[x] *\<le> [y] \<longleftrightarrow> {i \<in> nat. \<langle>x ` i, y ` i\<rangle> \<in> {\<langle>p,q\<rangle> \<in> nat \<times> nat . p \<le> q}}\<in>\<FF> " unfolding lessEq_star_def using star_rel_seq[OF assms, 
  of "{\<langle>p,q\<rangle> \<in> nat \<times> nat . p \<le> q}"] unfolding Le_def by auto
  with R1 show ?thesis by auto
qed

corollary less_seq:
  assumes "x:nat\<rightarrow>nat" "y:nat\<rightarrow>nat"
  shows "[x] *< [y] \<longleftrightarrow> {i\<in>nat. x`i <y`i}\<in>\<FF>"
proof -
  have "{i \<in> nat. \<langle>x ` i, y ` i\<rangle> \<in> {\<langle>p,q\<rangle> \<in> nat \<times> nat . p <q}} = {i \<in> nat. x`i < y`i}"
    apply simp using assms apply_type by auto
  then have R1:"[x] *< [y] \<longleftrightarrow> {i \<in> nat. \<langle>x ` i, y ` i\<rangle> \<in> {\<langle>p,q\<rangle> \<in> nat \<times> nat . p < q}}\<in>\<FF> \<Longrightarrow> [x] *< [y] \<longleftrightarrow> {i\<in>nat. x`i <y`i}\<in>\<FF>" by auto
  have "[x] *< [y] \<longleftrightarrow> {i \<in> nat. \<langle>x ` i, y ` i\<rangle> \<in> {\<langle>p,q\<rangle> \<in> nat \<times> nat . p < q}}\<in>\<FF> " unfolding less_star_def using star_rel_seq[OF assms, 
  of "{\<langle>p,q\<rangle> \<in> nat \<times> nat . p < q}"] unfolding Lt_def by auto
  with R1 show ?thesis by auto
qed

corollary less_imp_less_eq:
  assumes "x:nat\<rightarrow>nat" "y:nat\<rightarrow>nat"
  shows "[x] *< [y] \<longrightarrow> [x] *\<le> [y]"
    unfolding lessEq_star_def less_star_def
    apply (rule star_rel_imp_seq[OF assms]) using leI unfolding Lt_def Le_def by auto 


text\<open>There is a hypernatural bigger than all natural numbers\<close>

lemma omega_bigger_naturals:
  assumes "x:nat"
  shows "(*x) *\<le> \<omega>"
proof-
  from assms have "(*x) = [ConstantFunction(nat,x)]"
    using incl_def by auto
  have "{n\<in>nat. ConstantFunction(nat,x)`n \<le> id(nat)`n} = {n\<in>nat. x \<le> n}"
    using func1_3_L2[of _ nat x] id_iff by auto
  have "nat-{n\<in>nat. x \<le> n}\<in>FinPow(nat)" apply (rule nat_induct[of x "\<lambda>q. nat-{n\<in>nat. q \<le> n}\<in>FinPow(nat)"])
  proof-
    from assms show "x\<in>nat".
    have "{n \<in> nat . 0 \<le> n} = nat" using nat_0_le by auto
    then have "nat-{n \<in> nat . 0 \<le> n} = 0" by auto
    then show "nat-{n \<in> nat . 0 \<le> n}\<in>FinPow(nat)" using Finite_0 unfolding FinPow_def by auto
    {
      fix x assume x:"x\<in>nat" "nat - {n \<in> nat . x \<le> n} \<in> FinPow(nat)"
      {
        fix t assume t:"t\<in>(nat - {n \<in> nat . x \<le> n})\<union>{x}"
        {
          assume e:"t=x"
          then have "t\<in>nat" using x(1) by auto moreover
          {
            assume "succ(x) \<le> x"
            then have "x < x" using succ_leE by auto
            then have False by auto
          } moreover note e
          ultimately have "t\<in>nat-{n \<in> nat. succ(x) \<le> n}" by auto
        } moreover
        {
          assume e:"t\<noteq>x"
          with t have t:"t\<in>nat - {n \<in> nat . x \<le> n}" by auto
          then have tnat:"t\<in>nat" by auto
          {
            assume "succ(x)\<le>t"
            then have "x<t" using succ_leE by auto
            then have "x\<le>t" using leI by auto
            with t have False by auto
          }
          with tnat have "t\<in>nat-{n \<in> nat. succ(x) \<le> n}" by auto
        } ultimately
        have "t\<in>nat-{n \<in> nat. succ(x) \<le> n}" by auto
      }
      then have "nat - {n \<in> nat . x \<le> n} \<union> {x} \<subseteq> nat - {n \<in> nat . succ(x) \<le> n}" by auto moreover
      {
        fix t assume t:"t\<in>nat - {n \<in> nat . succ(x) \<le> n}"
        {
          assume tn:"t\<noteq>x"
          {
            assume tx:"x\<le>t"
            with tn have "x < t" using le_iff by auto
            then have "succ(x)\<le>t" using succ_leI by auto
            with t have False by auto
          }
          with t have "t\<in>nat - {n \<in> nat . x \<le> n}" by auto
        }
        then have "t\<in>nat - {n \<in> nat . x \<le> n} \<union> {x}" by auto
      }
      then have "nat - {n \<in> nat . succ(x) \<le> n} \<subseteq> nat - {n \<in> nat . x \<le> n} \<union> {x}" by auto
      ultimately have "nat - {n \<in> nat . succ(x) \<le> n} = nat - {n \<in> nat . x \<le> n} \<union> {x}" by auto
      then show "nat - {n \<in> nat . succ(x) \<le> n}\<in>FinPow(nat)" 
        using union_finpow[OF x(2) singleton_in_finpow[OF x(1)]] by auto
    }
  qed moreover
  {
    fix x assume as:"x\<in>nat" "{x}:\<FF>"
    {
      fix A assume x:"x\<in>A" "A\<subseteq> nat"
      then have "{x} \<subseteq> A" by auto
      then have "A:\<FF>" using as(2) ultraFilter x(2) unfolding IsFilter_def IsUltrafilter_def by auto
    }
    then have "{A\<in>Pow(nat). x:A} \<subseteq> \<FF>" by auto moreover
    {
      fix A assume a:"A\<in>\<FF>"
      with as(2) have y:"A\<inter>{x}:\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def
          by auto
      {
        assume "x\<notin>A"
        then have "A\<inter>{x} = 0" by auto
        with y have "0:\<FF>" by auto
        then have False using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
      }
      then have "x:A" by auto
      moreover from a have "A\<in>Pow(nat)" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
      ultimately have "A\<in>{A\<in>Pow(nat). x:A}" by auto
    }
    then have "\<FF> \<subseteq> {A\<in>Pow(nat). x:A}" by auto ultimately
    have "\<FF> = {A\<in>Pow(nat). x:A}" by auto
    then have "\<FF>=0 \<or> x\<in>\<Inter>\<FF>" by auto
    with non_pricipal_filter have "\<FF>=0" by auto
    then have False using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
  }
  then have "\<forall>x\<in>nat. {x} \<notin> \<FF>" by auto
  ultimately have "nat - {n \<in> nat . x \<le> n}\<notin>\<FF>" using ultrafilter_finite_set[OF ultraFilter]
    by auto
  then have "{n \<in> nat . x \<le> n}:\<FF>" using ultraFilter set_ultrafilter[of "{n \<in> nat . x \<le> n}"] by auto
  then have "{n\<in>nat. ConstantFunction(nat,x)`n \<le> id(nat)`n}:\<FF>"
    using func1_3_L2[of _ nat x] by auto
  then have "[ConstantFunction(nat,x)]*\<le>[id(nat)]" using less_than_seq[OF func1_3_L1 inj_is_fun[OF id_inj]]
    assms by auto
  then show ?thesis unfolding omega_def incl_def[OF assms] by auto
qed

text\<open>Every function on the natural numbers can be extended to a function on the hypernaturals\<close>

definition hyper_fun ("\<^sup>*_\<^sub>*") where
"f:nat\<rightarrow>nat \<Longrightarrow> \<^sup>*f\<^sub>* \<equiv> internal_fun(ConstantFunction(nat,f))"

lemma hyper_fun_on_nat:
  assumes "f\<in>nat\<rightarrow>nat" "x\<in>nat"
  shows "\<^sup>*f\<^sub>*`(*x) = *(f`x)"
proof-
  have e:"\<^sup>*f\<^sub>*`(*x) = internal_fun(ConstantFunction(nat,f))` (hyper_rel``{ConstantFunction(nat,x)})"
    unfolding hyper_fun_def[OF assms(1)] incl_def[OF assms(2)] seq_class_def[OF func1_3_L1[OF assms(2)]] by auto
  have A:"ConstantFunction(nat,nat):nat\<rightarrow>Pow(nat)" using func1_3_L1 by auto
  have B:"ConstantFunction(nat,f):(\<Prod>i\<in>nat. ConstantFunction(nat, nat) ` i \<rightarrow> ConstantFunction(nat, nat) ` i)"
    unfolding Pi_def function_def Sigma_def apply auto unfolding ConstantFunction_def apply auto
      prefer 2 using assms(1) func1_3_L2[of _ nat nat] unfolding Pi_def ConstantFunction_def apply auto
    unfolding function_def by blast
  have "{\<langle>i,nat\<rangle>. i\<in>nat} = ConstantFunction(nat,nat)" unfolding ConstantFunction_def by auto
  then have "internal_set(ConstantFunction(nat,nat)) = *\<nat>" using internal_total_set by auto
  then have C:"hyper_rel `` {ConstantFunction(nat, x)} \<in>
    internal_set(ConstantFunction(nat, nat))" unfolding hyper_set_def quotient_def
    using func1_3_L1[OF assms(2)] by auto
  from e have "\<^sup>*f\<^sub>*`(*x) =hyper_rel ``
    {{\<langle>i, if ConstantFunction(nat, x) ` i \<in> ConstantFunction(nat, nat) ` i
          then ConstantFunction(nat, f) ` i ` (ConstantFunction(nat, x) ` i)
          else ConstantFunction(nat, x) ` i\<rangle> .
      i \<in> nat}}"
    using internal_fun_apply_2[of "ConstantFunction(nat,nat)" "ConstantFunction(nat,nat)" "ConstantFunction(nat,f)"
        "ConstantFunction(nat,x)", OF A A B C] by auto
  then have "\<^sup>*f\<^sub>*`(*x) =hyper_rel ``
    {{\<langle>i, if x \<in> nat then f ` x else x\<rangle>. i \<in> nat}}"
    using func1_3_L2[of _ nat] by auto
  with assms(2) have "\<^sup>*f\<^sub>*`(*x) =hyper_rel``{{\<langle>i,f`x\<rangle>. i\<in>nat}}" by auto
  then show ?thesis unfolding seq_class_def[OF func1_3_L1[OF apply_type[OF assms]]] incl_def[OF apply_type[OF assms]]
    unfolding ConstantFunction_def by auto
qed

text\<open>Applying a function extended from the natural numbers to the class
of certain sequence gives out the sequence of the composition\<close>

lemma hyper_fun_on_nat_2:
  assumes "f\<in>nat\<rightarrow>nat" "x\<in>nat\<rightarrow>nat"
  shows "\<^sup>*f\<^sub>*`([x]) = [f O x]"
proof-
  have e:"\<^sup>*f\<^sub>*`([x]) = internal_fun(ConstantFunction(nat,f))` (hyper_rel``{x})"
    unfolding hyper_fun_def[OF assms(1)] seq_class_def[OF assms(2)] by auto
  have A:"ConstantFunction(nat,nat):nat\<rightarrow>Pow(nat)" using func1_3_L1 by auto
  have B:"ConstantFunction(nat,f):(\<Prod>i\<in>nat. ConstantFunction(nat, nat) ` i \<rightarrow> ConstantFunction(nat, nat) ` i)"
    unfolding Pi_def function_def Sigma_def apply auto unfolding ConstantFunction_def apply auto
      prefer 2 using assms(1) func1_3_L2[of _ nat nat] unfolding Pi_def ConstantFunction_def apply auto
    unfolding function_def by blast
  have "{\<langle>i,nat\<rangle>. i\<in>nat} = ConstantFunction(nat,nat)" unfolding ConstantFunction_def by auto
  then have "internal_set(ConstantFunction(nat,nat)) = *\<nat>" using internal_total_set by auto
  then have C:"hyper_rel `` {x} \<in>
    internal_set(ConstantFunction(nat, nat))" unfolding hyper_set_def quotient_def
    using assms(2) by auto
  from e have "\<^sup>*f\<^sub>*`([x]) =hyper_rel ``
    {{\<langle>i, if x ` i \<in> ConstantFunction(nat, nat) ` i
          then (ConstantFunction(nat, f) ` i) ` (x ` i)
          else x ` i\<rangle> .
      i \<in> nat}}"
    using internal_fun_apply_2[of "ConstantFunction(nat,nat)" "ConstantFunction(nat,nat)" "ConstantFunction(nat,f)"
        x, OF A A B C] by auto
  then have "\<^sup>*f\<^sub>*`([x]) =hyper_rel ``
    {{\<langle>i, if x ` i \<in> nat then (ConstantFunction(nat, f) ` i) ` (x ` i) else x ` i\<rangle>. i \<in> nat}}"
    using func1_3_L2[of _ nat nat] by auto
  then have "\<^sup>*f\<^sub>*`([x]) =hyper_rel ``
    {{\<langle>i, (ConstantFunction(nat, f) ` i) ` (x ` i)\<rangle>. i \<in> nat}}"
    using apply_type[OF assms(2)] by auto
  then have "\<^sup>*f\<^sub>*`([x]) =hyper_rel ``
    {{\<langle>i, f ` (x ` i)\<rangle>. i \<in> nat}}"
    using func1_3_L2[of _ nat f] by auto
  then have "\<^sup>*f\<^sub>*`([x]) =hyper_rel ``
    {{\<langle>i, (f O x) ` i\<rangle>. i \<in> nat}}" using comp_fun_apply[OF assms(2)] by auto
  then have "\<^sup>*f\<^sub>*`([x]) =hyper_rel `` {f O x}"
    using fun_is_set_of_pairs[OF comp_fun[OF assms(2,1)]] by auto
  then show ?thesis unfolding seq_class_def[OF comp_fun[OF assms(2,1)]].
qed

text\<open>Every subset of an internal set of the natural numbers is internal\<close>

lemma standard_internal_set:
  assumes "isInternal(A)" "A \<subseteq> ({\<langle>x,*x\<rangle>. x\<in>nat}``nat)" "X \<subseteq> A"
  shows "isInternal(X)"
proof-
  let ?X="{\<langle>x,*x\<rangle>. x\<in>nat}-``X"
  let ?SX="ConstantFunction(nat,?X)"
  have X:"?X \<in>Pow(nat)" using vimage_iff by auto
  have s:"?SX:nat\<rightarrow>Pow(nat)" using func1_3_L1[OF X] by auto
  {
    fix t assume t:"t\<in>X"
    with assms(2,3) have "t\<in>({\<langle>x,*x\<rangle>. x\<in>nat}``nat)" by auto
    then obtain q where q:"q\<in>nat" "t=*q" using image_iff by auto
    from t q have "q\<in>?X" using vimage_iff[of q "{\<langle>x,*x\<rangle>. x\<in>nat}" X] by auto
    then have "{n\<in>nat. q\<in>?X}=nat" by auto
    then have "{n\<in>nat. q\<in>?X}:\<FF>" using ultraFilter unfolding IsUltrafilter_def IsFilter_def by auto
    then have "{n\<in>nat. q\<in>?SX`n}:\<FF>" using func1_3_L2 by auto
    then have "{n\<in>nat. ConstantFunction(nat,q)`n\<in>?SX`n}:\<FF>" using func1_3_L2 by auto
    then have "hyper_rel``{ConstantFunction(nat,q)}:internal_set(?SX)"
      unfolding internal_set_def[OF s] using func1_3_L1[OF q(1), of nat] by auto
    then have "(*q):internal_set(?SX)" unfolding incl_def[OF q(1)]
      seq_class_def[OF func1_3_L1[OF q(1), of nat]].
    with q(2) have "t:internal_set(?SX)" by auto
  }
  with assms(3) have "X\<subseteq> A \<inter>internal_set(?SX)" by auto moreover
  {
    fix t assume "t\<in>A \<inter>internal_set(?SX)"
    then have t:"t\<in>A" "t\<in>internal_set(?SX)" by auto
    from t(2) obtain q where q:"q:nat\<rightarrow>nat" "t=hyper_rel``{q}"
      "{n\<in>nat. q`n:?SX`n}:\<FF>" unfolding internal_set_def[OF s] by auto
    from q(3) have A:"{n\<in>nat. q`n:?X}:\<FF>" using func1_3_L2[of _ nat ?X] by auto
    from t(1) assms(2) have "t \<in>{\<langle>x, *x\<rangle> . x \<in> nat} `` nat " by auto
    then obtain s where s:"s\<in>nat" "t=*s" using image_iff by auto
    from q(2) s(2) have "hyper_rel``{q} = *s" by auto
    then have "\<langle>q,ConstantFunction(nat, s)\<rangle>\<in>hyper_rel"
      unfolding incl_def[OF s(1)] seq_class_def[OF func1_3_L1[OF s(1)]]
      using eq_equiv_class[OF _ hyper_equiv func1_3_L1[OF s(1)]] by auto
    then have "{n\<in>nat. q`n = ConstantFunction(nat, s)`n}:\<FF>" unfolding hyper_rel_def by auto
    then have "{n\<in>nat. q`n = s}:\<FF>" using func1_3_L2[of _ nat s] by auto
    with A have "{n\<in>nat. q`n = s}\<inter>{n\<in>nat. q`n:?X}:\<FF>" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    then have "{n\<in>nat. q`n = s}\<inter>{n\<in>nat. q`n:?X} \<noteq>0" using ultraFilter
      unfolding IsFilter_def IsUltrafilter_def by auto
    then obtain n where "n\<in>{n\<in>nat. q`n = s}\<inter>{n\<in>nat. q`n:?X}" by force
    then have "n\<in>nat" "q`n=s" "q`n\<in>?X" by auto
    then have l:"n\<in>nat" "s:?X" by auto
    from l(2) obtain x where "x\<in>X" "x=*s" using vimage_iff by auto
    with s(2) have "t\<in>X" by auto
  }
  then have "A\<inter>internal_set(?SX) \<subseteq> X" by auto
  ultimately have "X= A\<inter>internal_set(?SX)" by auto
  moreover have "isInternal(internal_set(?SX))"
    unfolding isInternal_def using s by auto moreover
  note assms(1) ultimately
  show ?thesis using internal_inter[of A "internal_set(?SX)"] by auto
qed

text\<open>Every non empty internal set has a minimum element\<close>

theorem internal_set_has_minimum:
  assumes "isInternal(A)" "A\<noteq>0"
  shows "\<exists>t\<in>A. \<forall>q\<in>A. t *\<le> q"
proof-
  from assms obtain S where s:"S:nat\<rightarrow>Pow(nat)" "A=internal_set(S)"
    unfolding isInternal_def by auto
  let ?x="{\<langle>i,if S`i\<noteq>0 then \<mu> x. x\<in>S`i else 0\<rangle>. i\<in>nat}"
  have x:"?x\<in>nat\<rightarrow>nat" unfolding Pi_def function_def apply auto
  proof-
    fix i assume i:"i\<in>nat" "S`i\<noteq>0"
    then obtain y where "y\<in>S`i" by auto
    with s(1) i(1) have "y\<in>S`i" "Ord(y)"
      using apply_type[of S nat "\<lambda>_. Pow(nat)" i] nat_into_Ord[of y] by auto
    then have "(\<mu> x. x\<in>S`i)\<in>S`i" using LeastI[of "\<lambda>q. q\<in>S`i"] by auto
    then show "(\<mu> x. x\<in>S`i)\<in>nat" using apply_type[OF s(1) i(1)] by auto
  qed
  {
    assume as:"{n\<in>nat. S`n = 0}:\<FF>"
    {
      fix x assume "x\<in>A"
      with s(2) obtain q where x:"x=[q]" "q:nat\<rightarrow>nat" "{n\<in>nat. q`n\<in>S`n}:\<FF>" unfolding internal_set_def[OF s(1)]
        using seq_class_def by auto
      from as x(3) have "{n\<in>nat. S`n = 0}\<inter>{n\<in>nat. q`n\<in>S`n}:\<FF>" using ultraFilter
        unfolding IsFilter_def IsUltrafilter_def by auto moreover
      have "{n\<in>nat. S`n = 0}\<inter>{n\<in>nat. q`n\<in>S`n} = 0" by auto ultimately
      have "0:\<FF>" by auto
      then have False using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    }
    then have False using assms(2) by auto
  }
  then have "{n\<in>nat. S`n = 0}\<notin>\<FF>" by auto
  then have "nat-{n\<in>nat. S`n = 0}:\<FF>" using ultraFilter
    using set_ultrafilter[of "{n\<in>nat. S`n = 0}" nat \<FF>] by auto moreover
  have "nat-{n\<in>nat. S`n = 0} = {n\<in>nat. S`n \<noteq> 0}" by auto ultimately
  have "{n\<in>nat. S`n \<noteq> 0}:\<FF>" by auto moreover
  {
    fix n assume "n\<in>{n\<in>nat. S`n \<noteq> 0}"
    then have n:"n\<in>nat" "S`n\<noteq>0" by auto
    then obtain y where y:"y\<in>S`n" by auto
    then have "Ord(y)" using apply_type[OF s(1) n(1)] nat_into_Ord by auto
    with y have "(\<mu> x. x:S`n):S`n" using LeastI[of "\<lambda>q. q\<in>S`n" y] by auto
    then have "?x`n\<in>S`n" using n(2) apply_equality[OF _ x] n(1) by auto
    with n(1) have "n\<in>{n\<in>nat. ?x`n\<in>S`n}" by auto
  }
  then have "{n\<in>nat. S`n \<noteq> 0} \<subseteq> {n\<in>nat. ?x`n\<in>S`n}" by auto moreover
  have "{n\<in>nat. ?x`n\<in>S`n} \<in>Pow(nat)" by auto
  ultimately have B:"{n\<in>nat. ?x`n\<in>S`n} :\<FF>" using ultraFilter unfolding IsFilter_def
    IsUltrafilter_def by auto
  with x have Q:"[?x]\<in>internal_set(S)" unfolding internal_set_def[OF s(1)]
    seq_class_def[OF x] by auto
  {
    fix m assume m:"m\<in>A"
    with s(2) obtain p where p:"p:nat\<rightarrow>nat" "m=[p]" "{n\<in>nat. p`n:S`n}:\<FF>"
      unfolding internal_set_def[OF s(1)] using seq_class_def by auto
    from p(3) B have "{n\<in>nat. ?x`n\<in>S`n}\<inter>{n\<in>nat. p`n:S`n}:\<FF>"
      using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
    {
      fix h assume h:"h\<in>{n\<in>nat. ?x`n\<in>S`n}\<inter>{n\<in>nat. p`n:S`n}"
      then have h:"h\<in>nat" "?x`h\<in>S`h" "p`h\<in>S`h" by auto
      from h(2) have "S`h\<noteq>0" by auto
      then have xx:"?x`h=(\<mu> x. x\<in>S`h)" using apply_equality[OF _ x] h(1) by auto
      from h(3) have "p`h\<in>nat" using apply_type[OF s(1)] h(1) by auto
      then have "Ord(p`h)" using nat_into_Ord by auto
      with h(3) xx have "?x`h\<le>p`h" using Least_le[of "\<lambda>q. q\<in>S`h" "p`h"] by auto
      with h(1) have "h\<in>{h\<in>nat. ?x`h\<le>p`h}" by auto
    }
    then have "{n\<in>nat. ?x`n\<in>S`n}\<inter>{n\<in>nat. p`n:S`n} \<subseteq> {h\<in>nat. ?x`h\<le>p`h}" by auto
    moreover have "{h\<in>nat. ?x`h\<le>p`h}\<in>Pow(nat)" by auto ultimately
    have "{h\<in>nat. ?x`h\<le>p`h}:\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
    then have "[?x]*\<le>[p]" using less_than_seq[OF x p(1)] by auto
    with p(2) have "[?x]*\<le>m" by auto
  }
  then have "\<forall>m\<in>A. [?x]*\<le>m" by auto
  with Q s(2) show ?thesis by auto
qed


text\<open>Every hypernatural that is not zero, is a successor\<close>

theorem succ_hyper_nat:
  assumes "n\<in>*\<nat>" "n\<noteq>*0"
  shows "\<exists>t\<in>*\<nat>. \<^sup>*{\<langle>i,succ(i)\<rangle>. i\<in>nat}\<^sub>*`t=n"
proof-
  let ?S1="ConstantFunction(nat,nat)"
  let ?S2="ConstantFunction(nat,nat)"
  let ?S="ConstantFunction(nat,{\<langle>i,succ(i)\<rangle>. i\<in>nat})"
  have A:"?S1:nat\<rightarrow>Pow(nat)" using func1_3_L1 by auto
  have B:"?S2:nat\<rightarrow>Pow(nat)" using func1_3_L1 by auto
  have C:"?S:(\<Prod>i\<in>nat.?S1 ` i \<rightarrow> ?S2 ` i)"
    unfolding Pi_def function_def Sigma_def apply auto unfolding ConstantFunction_def apply auto
    using apply_equality[of _ nat "nat\<times>{nat}" nat "\<lambda>_. Pow(nat)"] A unfolding ConstantFunction_def
    apply simp using apply_equality[of _ nat "nat\<times>{nat}" nat "\<lambda>_. Pow(nat)"] A unfolding ConstantFunction_def
    apply simp using apply_equality[of _ nat "nat\<times>{nat}" nat "\<lambda>_. Pow(nat)"] A unfolding ConstantFunction_def
    by auto
  from assms(1) obtain q where q:"n=[q]" "q:nat\<rightarrow>nat" unfolding hyper_set_def quotient_def
    using seq_class_def by auto
  {
    assume "{n\<in>nat. q`n =0}\<in>\<FF>"
    then have "{n\<in>nat. q`n =ConstantFunction(nat,0)`n}\<in>\<FF>"
      using func1_3_L2 by auto
    then have "\<langle>q,ConstantFunction(nat,0)\<rangle>\<in>hyper_rel"
      unfolding hyper_rel_def using q(2) func1_3_L1[OF nat_0I] by auto
    then have "[q] = *0" using equiv_class_eq[OF hyper_equiv]
      unfolding seq_class_def[OF q(2)] incl_def[OF nat_0I]
      seq_class_def[OF func1_3_L1[OF nat_0I]] by auto
    with q(1) assms(2) have False by auto
  }
  then have "{n\<in>nat. q`n =0}\<notin>\<FF>" by auto
  then have "nat-{n\<in>nat. q`n =0}\<in>\<FF>" using set_ultrafilter[OF _  ultraFilter,
        of "{n\<in>nat. q`n =0}"] by auto
  moreover have "nat-{n\<in>nat. q`n =0} = {n\<in>nat. q`n \<noteq>0}" by auto
  ultimately have L:"{n\<in>nat. q`n \<noteq>0}\<in>\<FF>" by auto
  have suc:"{\<langle>i, succ(i)\<rangle> . i \<in> nat}:nat\<rightarrow>nat"
    unfolding Pi_def function_def by auto
  let ?x="{\<langle>i,pred(q`i)\<rangle>. i\<in>nat}"
  have x:"?x:nat\<rightarrow>nat" unfolding Pi_def function_def apply auto
    using apply_type[OF q(2)] by auto
  then have xN:"[?x]\<in>*\<nat>" unfolding hyper_set_def quotient_def
    seq_class_def[OF x] by auto
  then have "[?x]:internal_set({\<langle>i,nat\<rangle>. i\<in>nat})"
    using internal_total_set by auto moreover
  have "{\<langle>i,nat\<rangle>. i\<in>nat} = nat\<times>{nat}" by auto
  ultimately have "[?x]:internal_set(nat\<times>{nat})" by auto
  then have "[?x]:internal_set(?S1)" unfolding ConstantFunction_def.
  then have D:"hyper_rel `` {?x} \<in> internal_set(ConstantFunction(nat, nat))"
    unfolding seq_class_def[OF x] by auto
  from internal_fun_apply_2[OF A B C D]
  have Q:"\<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` [?x] =
  hyper_rel `` {{\<langle>i, succ(pred(q`i))\<rangle> . i \<in> nat}}" using apply_type[OF x] func1_3_L2[of _ nat nat] 
    func1_3_L2[of _ nat "{\<langle>i, succ(i)\<rangle> . i \<in> nat}"] apply_equality[of _ _ "{\<langle>i, succ(i)\<rangle> . i \<in> nat}", OF _ suc]
    unfolding hyper_fun_def[OF suc] using apply_equality[OF _ x]
    seq_class_def[OF x]  by auto
  {
    fix i assume "i\<in>nat" "q`i=0"
    then have "pred(q`i) = 0" using pred_0 by auto
    then have "succ(pred(q`i)) = 1" by auto
  } 
  then have U:"\<forall>i\<in>nat. q`i= 0 \<longrightarrow> succ(pred(q`i)) = 1" by auto
  {
    fix i assume i:"i\<in>nat" "q`i\<noteq>0"
    then obtain k where k:"k\<in>nat" "q`i = succ(k)" using Nat_ZF_1_L3[OF apply_type[OF q(2)]] i by auto
    then have "pred(q`i) = k" using pred_succ_eq by auto
    then have "succ(pred(q`i)) = q`i" using k(2) by auto
  }
  then have V:"\<forall>i\<in>nat. q`i\<noteq> 0 \<longrightarrow> succ(pred(q`i)) = q`i" by auto
  have f:"{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat} = {\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}} \<union> {\<langle>i,q`i\<rangle>. i\<in>{p\<in>nat. q`p \<noteq> 0}}"
  proof
    {
      fix j assume "j\<in>{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}"
      then obtain i where i:"i\<in>nat" "j=\<langle>i,succ(pred(q`i))\<rangle>" by auto
      {
        assume as:"q`i =0"
        with U i have "j=\<langle>i,1\<rangle>" by auto
        then have "j\<in>{\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}} \<union> {\<langle>i,q`i\<rangle>. i\<in>{p\<in>nat. q`p \<noteq> 0}}"
          using i as by auto
      } moreover
      {
        assume as:"q`i \<noteq>0"
        with V i have "j=\<langle>i,q`i\<rangle>" by auto
        then have "j\<in>{\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}} \<union> {\<langle>i,q`i\<rangle>. i\<in>{p\<in>nat. q`p \<noteq> 0}}"
          using i as by auto
      } ultimately have "j\<in>{\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}} \<union> {\<langle>i,q`i\<rangle>. i\<in>{p\<in>nat. q`p \<noteq> 0}}"
        by auto
    }
    then show "{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat} \<subseteq> {\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}} \<union> {\<langle>i,q`i\<rangle>. i\<in>{p\<in>nat. q`p \<noteq> 0}}"
      by blast
    {
      fix j assume j:"j\<in>{\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}} \<union> {\<langle>i,q`i\<rangle>. i\<in>{p\<in>nat. q`p \<noteq> 0}}"
      {
        assume "j\<in>{\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}}"
        then obtain i where "i\<in>nat" "q`i = 0" "j=\<langle>i,1\<rangle>" by auto
        with U have "i\<in>nat" "j=\<langle>i,succ(pred(q`i))\<rangle>" by auto
        then have "j\<in>{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}" by auto
      } moreover
      {
        assume "j\<notin>{\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}}"
        with j have "j\<in>{\<langle>i,q`i\<rangle>. i\<in>{p\<in>nat. q`p \<noteq> 0}}" by auto
        then obtain i where "i\<in>nat" "q`i \<noteq> 0" "j=\<langle>i,q`i\<rangle>" by auto
        with V have "i\<in>nat" "j=\<langle>i,succ(pred(q`i))\<rangle>" by auto
        then have "j\<in>{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}" by auto
      } ultimately
      have "j\<in>{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}" by auto
    }
    then show "{\<langle>i,1\<rangle>. i\<in>{p\<in>nat. q`p = 0}} \<union> {\<langle>i,q`i\<rangle>. i\<in>{p\<in>nat. q`p \<noteq> 0}} \<subseteq> {\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}"
      by blast
  qed
  have ff:"{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}:nat\<rightarrow>nat" unfolding Pi_def function_def
    apply auto using apply_type[OF q(2)] by auto
  {
    fix i assume "i\<in>{p\<in>nat. q`p \<noteq> 0}"
    then have i:"i\<in>nat" "q`i\<noteq>0" by auto
    with f have "{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}`i = q`i"
      using apply_equality[of i "q`i" _, OF _ ff] by auto
    with i(1) have "i:{p\<in>nat. {\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}`p = q`p}" by auto
  }
  then have "{p\<in>nat. q`p \<noteq> 0} \<subseteq> {p\<in>nat. {\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}`p = q`p}" by auto
  moreover note L moreover have "{p\<in>nat. {\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}`p = q`p}:Pow(nat)" by auto
  ultimately have "{p\<in>nat. {\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}`p = q`p}:\<FF>" using ultraFilter
    unfolding IsFilter_def IsUltrafilter_def by auto
  then have "\<langle>{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat},q\<rangle>\<in>hyper_rel"
    unfolding hyper_rel_def using ff q(2) by auto
  then have "hyper_rel``{{\<langle>i,succ(pred(q`i))\<rangle> . i \<in> nat}} = hyper_rel``{q}"
    using equiv_class_eq[OF hyper_equiv] by auto
  with Q have "\<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` [{\<langle>i, Arith.pred(q ` i)\<rangle> . i \<in> nat}] = [q]"
    using seq_class_def[OF q(2)] by auto
  with q(1) have "\<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` [{\<langle>i, Arith.pred(q ` i)\<rangle> . i \<in> nat}] = n" by auto
  with xN show ?thesis by auto
qed


text\<open>The set of hypernaturals is not well ordered, since
we can only prove that internal sets have minimums. Here is
an example of a set without a minimum:\<close>

corollary not_well_ordered:
  defines "NonNatural \<equiv> *\<nat>-{\<langle>x,*x\<rangle>. x\<in>nat}``nat"
  shows "\<forall>t\<in>NonNatural. \<exists>q\<in>NonNatural. q *< t" 
proof
  fix t assume "t\<in>NonNatural"
  then have t:"t\<in>*\<nat>" "t\<notin>{\<langle>x,*x\<rangle>. x\<in>nat}``nat" unfolding NonNatural_def by auto
  have f:"{\<langle>x,*x\<rangle>. x\<in>nat}:nat \<rightarrow> *\<nat>" using incl_inj_nat unfolding inj_def by auto
  with t(2) have "t\<notin>{{\<langle>x,*x\<rangle>. x\<in>nat}`n. n\<in>nat}" using func_imagedef by auto
  then have R:"t\<notin>{*n. n\<in>nat}" using apply_equality f by auto
  then have "\<forall>n\<in>nat. t\<noteq>*n" by auto
  then have "t\<noteq>*0" by auto
  with t(1) obtain q where q:"q\<in>*\<nat>" "t = \<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` q" using succ_hyper_nat
    by auto
  from q(1) obtain qf where qf:"[qf] = q" "qf:nat \<rightarrow> nat"
    unfolding hyper_set_def quotient_def using seq_class_def by auto
  have suc:"{\<langle>i, succ(i)\<rangle> . i \<in> nat}:nat\<rightarrow>nat"
    unfolding Pi_def function_def by auto
  with q(2) have t:"t = [{\<langle>i, succ(i)\<rangle> . i \<in> nat} O qf]" using
    hyper_fun_on_nat_2[OF _ qf(2), of "{\<langle>i,succ(i)\<rangle>. i\<in>nat}"] qf(1) by auto
  {
    fix n assume "n\<in>nat"
    then have A:"qf`n < succ(qf`n)" using le_refl[OF nat_into_Ord]
      apply_type qf(2) by auto
    moreover have "qf`n \<in> nat" using apply_type qf(2) `n\<in>nat` by auto
    then have "{\<langle>i, succ(i)\<rangle> . i \<in> nat}`(qf`n) = succ(qf`n)" using apply_equality
      suc by auto
    then have "({\<langle>i, succ(i)\<rangle> . i \<in> nat} O qf)`n = succ(qf`n)" using 
      comp_fun_apply qf(2) `n\<in>nat` by auto
    with A have "qf`n < ({\<langle>i, succ(i)\<rangle> . i \<in> nat} O qf)`n" by auto
  }
  then have "{n\<in>nat. qf`n < ({\<langle>i, succ(i)\<rangle> . i \<in> nat} O qf)`n} = nat" by auto
  then have "{n\<in>nat. qf`n < ({\<langle>i, succ(i)\<rangle> . i \<in> nat} O qf)`n} \<in>\<FF>" using
    ultraFilter unfolding IsUltrafilter_def using is_filter_def_split(2) by auto
  then have "[qf] *< [{\<langle>i, succ(i)\<rangle> . i \<in> nat} O qf]"
    using less_seq[OF qf(2) comp_fun[OF qf(2) suc]] by auto
  with qf(1) t have "q *< t" by auto moreover
  {
    assume as:"q\<in>{\<langle>x,*x\<rangle>. x\<in>nat}``nat"
    then have "q\<in>{{\<langle>x,*x\<rangle>. x\<in>nat}`n. n\<in>nat}" using func_imagedef f by auto
    then have "q\<in>{*n. n\<in>nat}" using apply_equality f by auto
    then obtain n where "q=*n" "n\<in>nat" by auto
    then have " \<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` q = *({\<langle>i, succ(i)\<rangle> . i \<in> nat} ` n)"
      using hyper_fun_on_nat[OF suc] by auto
    then have " \<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` q = *(succ(n))"
      using apply_equality[OF _ suc] `n\<in>nat` by auto
    then have " \<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` q\<in>{*p. p\<in>nat}"
      using nat_succI `n\<in>nat` by auto
    with q(2) have "t\<in>{*p. p\<in>nat}" by auto
    with R have False by auto
  }
  with q(1) have "q\<in>NonNatural" unfolding NonNatural_def by auto
  ultimately show "\<exists>q\<in>NonNatural. q *< t" by auto
qed


text\<open>The natural numbers is not an internal set\<close>

corollary nat_not_internal:
  shows "\<not>isInternal({\<langle>x,*x\<rangle>. x\<in>nat}``nat)"
proof
  assume "isInternal({\<langle>x,*x\<rangle>. x\<in>nat}``nat)"
  then have A:"isInternal(*\<nat>-({\<langle>x,*x\<rangle>. x\<in>nat}``nat))"
    using complement_internal by auto
  {
    assume z:"*\<nat>-({\<langle>x,*x\<rangle>. x\<in>nat}``nat) = 0"
    then have "\<omega> \<in> {\<langle>x,*x\<rangle>. x\<in>nat}``nat" using omega_not_nat(2) by auto
    then obtain n where "\<omega> = *n" "n\<in>nat" using image_iff by auto
    then have False using omega_not_nat(1) by auto
  }
  then have B:"*\<nat>-({\<langle>x,*x\<rangle>. x\<in>nat}``nat) \<noteq> 0" by auto
  have C:"\<exists>t\<in>*\<nat>-({\<langle>x,*x\<rangle>. x\<in>nat}``nat). \<forall>q\<in>*\<nat>-({\<langle>x,*x\<rangle>. x\<in>nat}``nat). t *\<le> q"
    using internal_set_has_minimum[OF A B] by auto
  then obtain t where t:"t\<in>*\<nat>-({\<langle>x,*x\<rangle>. x\<in>nat}``nat)" "\<forall>q\<in>*\<nat>-({\<langle>x,*x\<rangle>. x\<in>nat}``nat). t *\<le> q"
    by auto
  from t(1) have A:"t\<in>*\<nat>" by auto
  {
    assume "t=*0"
    then have "t\<in>{\<langle>x,*x\<rangle>. x\<in>nat}``nat" using image_iff by auto
    with t(1) have False by auto
  }
  then have B:"t \<noteq> *0" by auto
  then obtain q where q:"q\<in>*\<nat>" "\<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` q = t" 
    using succ_hyper_nat[OF A B] by auto
  have suc:"{\<langle>i, succ(i)\<rangle> . i \<in> nat}:nat\<rightarrow>nat"
    unfolding Pi_def function_def by auto
  from q(1) obtain qx where qq:"q=[qx]" "qx:nat\<rightarrow>nat" unfolding hyper_set_def quotient_def
    using seq_class_def by auto
  from qq(1) have "\<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` q = [{\<langle>i, succ(i)\<rangle> . i \<in> nat} O qx]"
    using hyper_fun_on_nat_2[OF suc qq(2)] by auto
  then have "t=[{\<langle>i, succ(i)\<rangle> . i \<in> nat} O qx]" using q(2) by auto
  moreover from A obtain tx where tx:"t=[tx]" "tx:nat\<rightarrow>nat" unfolding hyper_set_def quotient_def
    using seq_class_def by auto
  note tx(1) ultimately have "\<langle>tx,{\<langle>i, succ(i)\<rangle> . i \<in> nat} O qx\<rangle>\<in>hyper_rel"
    using eq_equiv_class[OF _ hyper_equiv comp_fun[OF qq(2) suc]] 
    unfolding seq_class_def[OF tx(2)] seq_class_def[OF comp_fun[OF qq(2) suc]] by auto
  then have "{i:nat. tx`i = ({\<langle>i, succ(i)\<rangle> . i \<in> nat} O qx)`i}:\<FF>" unfolding hyper_rel_def by auto
  then have "{i:nat. tx`i = {\<langle>i, succ(i)\<rangle> . i \<in> nat}` (qx`i)}:\<FF>" using comp_fun_apply[OF qq(2)]
    by auto
  then have B:"{i:nat. tx`i = succ (qx`i)}:\<FF>" using apply_equality[OF _ suc]
    apply_type[OF qq(2)] by auto moreover
  have "{i:nat. qx`i \<le> tx`i}:Pow(nat)" by auto moreover
  {
    fix i assume "i\<in>{i:nat. tx`i = succ (qx`i)}"
    then have i:"i\<in>nat" "tx`i = succ(qx`i)" by auto
    have "qx ` i \<le> qx ` i" "Ord(qx ` i)"
      using nat_into_Ord[OF apply_type[OF qq(2) i(1)]] le_refl[OF nat_into_Ord[OF apply_type[OF qq(2) i(1)]]]
      by auto
    then have "(qx ` i \<le> qx ` i \<or> (qx ` i = succ(qx ` i))) \<and> Ord(qx ` i)" by blast
    then have "qx`i \<le> succ(qx`i)" using le_succ_iff by auto
    then have "qx`i \<le> tx`i" by (simp only: subst[OF i(2)[THEN sym], of "\<lambda>z. qx`i \<le> z"])
    with i(1) have "i\<in>{i:nat. qx`i \<le> tx`i}" by auto
  }
  then have "{i:nat. tx`i = succ (qx`i)} \<subseteq> {i:nat. qx`i \<le> tx`i}" by blast
  ultimately have A:"{i:nat. qx`i \<le> tx`i}:\<FF>" using ultraFilter
    unfolding IsFilter_def IsUltrafilter_def by auto
  then have "[qx] *\<le> [tx]" using less_than_seq[OF qq(2) tx(2)] by auto
  then have "q *\<le> t" using qq(1) tx(1) by auto
  {
    assume "q\<in>({\<langle>x,*x\<rangle>. x\<in>nat}``nat)"
    then obtain u where u:"q=*u" "u\<in>nat" using image_iff by auto
    then have "\<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` q = *({\<langle>i, succ(i)\<rangle> . i \<in> nat}`u)"
      using hyper_fun_on_nat[OF suc] by auto
    then have "\<^sup>*{\<langle>i, succ(i)\<rangle> . i \<in> nat}\<^sub>* ` q = *(succ(u))"
      using apply_equality[OF _ suc] u(2) by auto
    then have "t = *(succ(u))" using q(2) by auto
    then have "\<langle>succ(u),t\<rangle>\<in>{\<langle>x,*x\<rangle>. x\<in>nat}" using u(2) by auto
    then have "t: {\<langle>x,*x\<rangle>. x\<in>nat}``nat" using image_iff by auto
    with t(1) have False by auto
  }
  with q(1) have "q\<in>*\<nat>-({\<langle>x,*x\<rangle>. x\<in>nat}``nat)" by auto
  with t(2) have "t *\<le> q" by auto
  then have "{i:nat. tx`i \<le> qx`i}:\<FF>" using less_than_seq[OF tx(2) qq(2)]
    using tx(1) qq(1) by auto
  with B have "{i:nat. tx`i \<le> qx`i}\<inter>{i:nat.  tx ` i = succ(qx ` i)}:\<FF>"
    using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto moreover
  {
    fix i assume "i\<in>{i:nat. tx`i \<le> qx`i}\<inter>{i:nat.  tx ` i = succ(qx ` i)}"
    then have "i:nat" "tx`i \<le> qx`i" "tx ` i = succ(qx ` i)" by auto
    then have "succ(qx`i) \<le> qx`i" by auto
    then have False by auto
  }
  then have "{i:nat. tx`i \<le> qx`i}\<inter>{i:nat.  tx ` i = succ(qx ` i)} = 0" by auto
  ultimately show False using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
qed

lemma bij_finite:
  assumes "Finite(A)" "Finite(B)"
  shows "Finite(A\<rightarrow>B)" apply (rule subset_Finite[of _ "Pow(A\<times>B)"])
  prefer 2 apply (rule Finite_Pow)
proof-
  show "A\<rightarrow>B \<subseteq> Pow(A\<times>B)" unfolding Pi_def by auto
  from assms obtain n m where nm:"A\<approx>n" "B\<approx>m" "n\<in>nat" "m\<in>nat" unfolding Finite_def by auto
  then have "A*B\<approx>n*m" using prod_eqpoll_cong by auto
  then have "A*B\<approx>n\<otimes>m"
    unfolding Card_def cmult_def using nat_implies_well_ord[OF nm(4)] 
      nat_implies_well_ord[OF nm(3)] well_ord_rmult [of n _ m]
      well_ord_cardinal_eqpoll[THEN eqpoll_sym, of "n*m"]
      eqpoll_trans[of "A*B" "n*m" "|n*m|"] by auto
  then have "A*B\<approx>n#*m" using nat_cmult_eq_mult nm(3,4) by auto
  then show "Finite(A*B)" unfolding Finite_def by auto
qed
    
lemma hyperfinite_bijective_left_ray:
  assumes "H\<in>Pow(*\<nat>)" "isHyperFinite(H)"
  shows "\<exists>N\<in>*\<nat>. \<exists>S\<in>nat\<rightarrow>Pow(nat). \<exists>g\<in>Pi(nat, \<lambda>i. S`i \<rightarrow> nat). internal_fun(g):bij(H,{i\<in>*\<nat>. i *< N})"
proof-
  from assms(2) obtain S where S:"S:nat\<rightarrow>FinPow(nat)" "H=internal_set(S)"
    unfolding isHyperFinite_def[OF assms(1)] by auto  
  from S(1) have Y:"S:nat \<rightarrow> Pow(nat)" using func1_1_L1B unfolding FinPow_def by auto
  let ?N="{\<langle>i,|S`i|\<rangle>. i\<in>nat}"
  have n_fun:"?N:nat\<rightarrow>nat" unfolding Pi_def function_def using apply_type[OF S(1)] unfolding FinPow_def
    using Finite_cardinal_in_nat by auto
  then have N:"[?N]:*\<nat>" unfolding hyper_set_def quotient_def using seq_class_def by auto
  {
    fix g assume g:"g\<in>Pi(nat,\<lambda>i. bij(S`i,|S`i|))"
    let ?f="internal_fun(g)"
    have const:"{\<langle>i, nat\<rangle> . i \<in> nat} = ConstantFunction(nat,nat)" 
      unfolding ConstantFunction_def by auto
    have S2:"S:nat \<rightarrow> Pow(nat)" using S(1) unfolding FinPow_def Pi_def by auto moreover
    have gg:"g\<in>Pi(nat,\<lambda>i. S`i \<rightarrow> nat)"
      unfolding Pi_def function_def apply auto
        prefer 3 using g unfolding Pi_def function_def apply blast
       prefer 2 using g unfolding Pi_def apply blast
    proof-
      fix x assume "x\<in>g"
      with g have "x\<in>(\<Sum>i\<in>nat. bij(S ` i, |S ` i|))" unfolding Pi_def by auto
      then obtain i f where x:"x=\<langle>i,f\<rangle>" "i\<in>nat" "f\<in>bij(S ` i, |S ` i|)" by auto
      have f:"f\<in>{f \<in> Pow(S ` i \<times> |S`i|) .
              S ` i \<subseteq> domain(f) \<and> (\<forall>x y. \<langle>x, y\<rangle> \<in> f \<longrightarrow> (\<forall>y'. \<langle>x, y'\<rangle> \<in> f \<longrightarrow> y = y'))}"
        using bij_is_fun[OF x(3)] unfolding Pi_def function_def .
      have "|S`i|\<in>nat" using apply_type[OF S(1) x(2)] unfolding FinPow_def
        using Finite_cardinal_in_nat by auto
      then have "|S`i| \<subseteq> nat" using OrdmemD[OF _ Ord_nat] by auto moreover
      from f have "f\<in> Pow(S ` i \<times> |S`i|)"  by auto
      ultimately have "f:  Pow(S ` i \<times> nat)" by auto
      with f have "f\<in>{f \<in> Pow(S ` i \<times> nat) .
              S ` i \<subseteq> domain(f) \<and> (\<forall>x y. \<langle>x, y\<rangle> \<in> f \<longrightarrow> (\<forall>y'. \<langle>x, y'\<rangle> \<in> f \<longrightarrow> y = y'))}" by blast
      with x(1,2) show "x \<in>
         (\<Sum>i\<in>nat.
             {f \<in> Pow(S ` i \<times> nat) .
              S ` i \<subseteq> domain(f) \<and> (\<forall>x y. \<langle>x, y\<rangle> \<in> f \<longrightarrow> (\<forall>y'. \<langle>x, y'\<rangle> \<in> f \<longrightarrow> y = y'))})" by blast
    qed
    then have g2:"g \<in> (\<Prod>i\<in>nat. S ` i \<rightarrow> ConstantFunction(nat,nat)`i)" using
      func1_3_L2[of _ nat nat] unfolding Pi_def by force
    have n:"nat\<in>Pow(nat)" by auto
    have fun:"?f:H\<rightarrow>*\<nat>" using internal_fun_is_fun[OF S2 func1_3_L1[OF n] g2]
      internal_total_set const S(2) by auto
    {
      fix t assume t:"t\<in>range(?f)"
      then obtain q where "\<langle>q,t\<rangle>\<in>?f" using rangeE by auto
      with fun have f:"q\<in>H" "t\<in>*\<nat>" "\<langle>q,t\<rangle>\<in>?f" unfolding Pi_def by auto
      from f(1,3) have fqt:"?f`q=t" using apply_equality[OF _ fun] by auto
      from f(1) S(2) obtain qx where qx:"qx:nat\<rightarrow>nat" "{i\<in>nat. qx`i\<in>S`i}\<in>\<FF>" "q=[qx]"
        unfolding internal_set_def[OF S2] using seq_class_def by auto
      from f(2) obtain tx where tx:"tx:nat\<rightarrow>nat" "t=[tx]" using seq_class_def
        unfolding hyper_set_def quotient_def by auto
      from fqt qx(3) have "t = hyper_rel `` {{\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}}" using internal_fun_apply_2[OF S2 func1_3_L1[OF n] g2, of qx]
        f(1) S(2) unfolding seq_class_def[OF qx(1)] by auto
      with tx(2) have "[tx] = hyper_rel `` {{\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}}" by auto
      then have "hyper_rel `` {{\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}} = [tx]" by auto
      then have "\<langle>{\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat},tx\<rangle>\<in>hyper_rel"
        using eq_equiv_class[OF _ hyper_equiv, of _ tx] unfolding seq_class_def[OF tx(1)] using tx(1) by auto
      then have "{i\<in>nat. {\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}`i = tx`i}:\<FF>"
  and ff:"{\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}:nat\<rightarrow>nat"
        unfolding hyper_rel_def by auto
      then have "{i\<in>nat. {\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}`i = tx`i}\<inter>{i\<in>nat. qx`i\<in>S`i}\<in>\<FF>"
        using ultraFilter qx(2) unfolding IsFilter_def IsUltrafilter_def by auto moreover
      {
        fix i assume "i\<in>{i\<in>nat. {\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}`i = tx`i}\<inter>{i\<in>nat. qx`i\<in>S`i}"
        then have "i\<in>nat" "{\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}`i = tx`i" "qx`i\<in>S`i" by auto
        then have i:"i\<in>nat" "(g ` i)  ` (qx ` i)  = tx`i" "qx`i\<in>S`i" using apply_equality[OF _ ff] by auto
        from i(1) have "g`i\<in>bij(S`i,|S`i|)" using g apply_type by auto
        with i(3) have "(g`i)`(qx`i)\<in>|S`i|" using apply_type[OF bij_is_fun] by auto
        with i(2) have "tx`i\<in>|S`i|" by auto
        then have "tx`i < |S`i|" unfolding lt_def by auto
        then have "tx`i < ?N`i" using apply_equality[of i "|S`i|" ?N] n_fun i(1) by auto
        then have "i\<in>{i\<in>nat. tx`i < ?N`i }" using i(1) by auto
      }
      then have "{i\<in>nat. {\<langle>i, if qx ` i \<in> S ` i then g ` i ` (qx ` i) else qx ` i\<rangle> . i \<in> nat}`i = tx`i}\<inter>{i\<in>nat. qx`i\<in>S`i} \<subseteq> {i\<in>nat. tx`i < ?N`i }" by auto moreover
      have "{i\<in>nat. tx`i <?N`i }:Pow(nat)" by auto ultimately
      have "{i\<in>nat. tx`i <?N`i }:\<FF>" using ultraFilter unfolding IsFilter_def IsUltrafilter_def by auto
      then have "[tx] *< [?N]" using less_seq[OF tx(1) n_fun] by auto
      then have "t *<[?N]" using tx(2) by auto
      with f(2) have "t:{p:*\<nat>. p *<[?N]}" by auto
    }
    then have "range(?f) \<subseteq> {p:*\<nat>. p *<[?N]}" by auto
    then have fun:"?f:H\<rightarrow>{p:*\<nat>. p *<[?N]}" using range_of_fun[OF fun] func1_1_L1B by auto
    {
      fix h1 h2 assume as:"h1\<in>H" "h2\<in>H" "?f`h1 = ?f`h2"
      from as(1,2) S(2) obtain q1 q2 where q:"q1:nat\<rightarrow>nat" "q2:nat\<rightarrow>nat" "{i\<in>nat. q1`i\<in>S`i}\<in>\<FF>" "{i\<in>nat. q2`i\<in>S`i}\<in>\<FF>" "h1=[q1]" "h2=[q2]"
        unfolding internal_set_def[OF S2] using seq_class_def by auto
      let ?qq1="{\<langle>i, if q1 ` i \<in> S ` i then g ` i ` (q1 ` i) else q1 ` i\<rangle> .
          i \<in> nat}"
      let ?qq2="{\<langle>i, if q2 ` i \<in> S ` i then g ` i ` (q2 ` i) else q2 ` i\<rangle> .
          i \<in> nat}"
      have "?f`h1 = hyper_rel``{?qq1}" using internal_fun_apply(1)[OF S2 func1_3_L1[OF n] g2 q(1,3)] q(5)
        unfolding seq_class_def[OF q(1)] by simp moreover
      have "?f`h2 = hyper_rel``{?qq2}" using internal_fun_apply(1)[OF S2 func1_3_L1[OF n] g2 q(2,4)] q(6)
        unfolding seq_class_def[OF q(2)] by simp ultimately
      have eq:"hyper_rel``{?qq1} = hyper_rel``{?qq2}" using as(3) by auto
      moreover have s1:"?qq1:nat \<rightarrow> nat" using internal_fun_apply(2)[OF S2 func1_3_L1[OF n] g2 q(1,3)] by auto
      have s2:"?qq2:nat \<rightarrow> nat" using internal_fun_apply(2)[OF S2 func1_3_L1[OF n] g2 q(2,4)] by auto
      from eq have "\<langle>?qq1, ?qq2\<rangle>\<in> hyper_rel" using eq_equiv_class[OF _ hyper_equiv, of
          ?qq1 ?qq2] s2 by auto
      then have "{i\<in>nat. ?qq1`i = ?qq2`i}\<in>\<FF>" unfolding hyper_rel_def by auto
      with q(3,4) have "{i:nat. ?qq1`i = ?qq2`i}\<inter>{i:nat. q1`i:S`i}\<inter>{i:nat. q2`i:S`i}:\<FF>"
        using ultraFilter unfolding IsUltrafilter_def IsFilter_def by auto moreover
      have "{i:nat. ?qq1`i = ?qq2`i}\<inter>{i:nat. q1`i:S`i}\<inter>{i:nat. q2`i:S`i} \<subseteq> {i:nat. ?qq1`i = ?qq2`i \<and> q1`i:S`i \<and> q2`i:S`i}"
        by auto moreover
      from ultraFilter have R:"\<And>B C. B:\<FF> \<Longrightarrow> B \<subseteq> C \<Longrightarrow> C \<subseteq> nat \<Longrightarrow> C:\<FF>" using is_filter_def_split(5)[of \<FF> nat]
        unfolding IsUltrafilter_def by auto
      ultimately have A:"{i:nat. ?qq1`i = ?qq2`i \<and> q1`i:S`i \<and> q2`i:S`i}:\<FF>" using ultraFilter
        by auto
      have "\<And>i. i\<in>nat \<Longrightarrow> q1`i \<in> S`i \<Longrightarrow> ?qq1`i = (g`i)`(q1`i)"
        using apply_equality[OF _ s1] by auto moreover
      have "\<And>i. i\<in>nat \<Longrightarrow> q2`i \<in> S`i \<Longrightarrow> ?qq2`i = (g`i)`(q2`i)"
        using apply_equality[OF _ s2] by auto
      ultimately have "{i:nat. ?qq1`i = ?qq2`i \<and> q1`i:S`i \<and> q2`i:S`i} \<subseteq> {i:nat. (g`i)`(q1`i) = (g`i)`(q2`i) \<and> q1`i:S`i \<and> q2`i:S`i}"
        by auto
      with A R have F1:"{i:nat. (g`i)`(q1`i) = (g`i)`(q2`i) \<and> q1`i:S`i \<and> q2`i:S`i}\<in>\<FF>" by auto
      {
        fix j assume as:"j\<in>nat" "(g`j)`(q1`j) = (g`j)`(q2`j)" "q1`j:S`j" "q2`j:S`j"
        from g have "g`j\<in>bij(S`j,|S`j|)" using apply_type as(1) by auto
        then have "g`j\<in>inj(S`j,|S`j|)" unfolding bij_def by auto
        with q(1,2) as have "q1`j=q2`j" unfolding inj_def by auto
      }
      then have "{i:nat. (g`i)`(q1`i) = (g`i)`(q2`i) \<and> q1`i:S`i \<and> q2`i:S`i} \<subseteq> {i:nat. q1`i = q2`i}" by auto
      with F1 R have "{i:nat. q1`i = q2`i}\<in>\<FF>" by auto
      then have "\<langle>q1,q2\<rangle>\<in>hyper_rel" unfolding hyper_rel_def using q(1,2) by auto
      then have "[q1] = [q2]" using equiv_class_eq[OF hyper_equiv] seq_class_def
        q(1,2) by auto
      with q(5,6) have "h1=h2" by auto
    }
    with fun have "?f\<in>inj(H,{p\<in>*\<nat>. p *< [?N]})" unfolding inj_def by auto
    {
      fix p assume as:"p\<in>{p\<in>*\<nat>. p *< [?N]}"
      then have p:"p\<in>*\<nat>" "p *<[?N]" by auto
      from p(1) obtain pf where pf:"pf:nat\<rightarrow>nat" "p =[pf]" unfolding hyper_set_def
        quotient_def seq_class_def by auto
      from pf p(2) n_fun have "{n\<in>nat. pf`n < ?N`n}\<in>\<FF>" using less_seq by auto
      moreover have "\<And>n. n\<in>nat \<Longrightarrow> ?N`n = |S`n|" using apply_equality[OF _ n_fun] by auto
      ultimately have A:"{n\<in>nat. pf`n < |S`n|}\<in>\<FF>" by auto
      let ?h="{\<langle>i,if pf`i\<in>|S`i| then converse(g`i)`(pf`i) else 0\<rangle>. i\<in>nat}"
      {
        fix i assume as:"i\<in>nat" "pf`i \<notin> |S`i|"
        from as(2) have "(if pf`i\<in>|S`i| then converse(g`i)`(pf`i) else 0) = 0" by auto
        then have "\<langle>i,if pf`i\<in>|S`i| then converse(g`i)`(pf`i) else 0\<rangle>\<in>nat\<times>nat" using as(1) by auto
      } moreover
      {
        fix i assume as:"i\<in>nat" "pf`i\<in>|S`i|"
        then have "(if pf`i\<in>|S`i| then converse(g`i)`(pf`i) else 0) = converse(g`i)`(pf`i)" by auto
        moreover note as(1) moreover
        from g have "g`i\<in>bij(S`i,|S`i|)" using apply_type as(1) by auto
        then have "converse(g`i)\<in>bij( |S`i|, S`i)" using bij_converse_bij by auto
        with as(2) have "converse(g`i)`(pf`i)\<in>S`i" using apply_type[OF bij_is_fun] by auto
        moreover have "S`i \<subseteq> nat" using apply_type[OF S2 as(1)] by auto
        ultimately have "(if pf`i\<in>|S`i| then converse(g`i)`(pf`i) else 0)\<in>nat" by auto
      }
      ultimately have "?h \<subseteq> nat\<times>nat" by auto
      then have h_fun:"?h:nat \<rightarrow> nat" unfolding Pi_def function_def by auto
      {
        fix m assume m:"m\<in>nat" "pf`m <|S`m|"
        with m(2) have "pf`m\<in>|S`m|" unfolding lt_def by auto
        then have "(if pf`m\<in>|S`m| then converse(g`m)`(pf`m) else 0) = converse(g`m)`(pf`m)" by auto
        then have "?h`m = converse(g`m)`(pf`m)" using apply_equality m(1) h_fun by auto
        moreover from m(1) g have "g`m\<in>bij(S`m,|S`m|)" using apply_type by auto
        then have "converse(g`m)\<in>bij( |S`m|, S`m)" using bij_converse_bij by auto
        then have "converse(g`m)`(pf`m)\<in>S`m" using apply_type[OF bij_is_fun] m(2) unfolding lt_def by auto
        ultimately have "?h`m\<in>S`m" by auto
      }
      then have B:"{m\<in>nat. pf`m <|S`m| } \<subseteq> {m\<in>nat. ?h`m\<in>S`m}" by auto
      let ?p="{\<langle>i, if ?h ` i \<in> S ` i then g ` i ` (?h ` i) else ?h ` i\<rangle> . i \<in> nat}"
      have "\<FF>{is a filter on}nat" using ultraFilter unfolding IsUltrafilter_def by auto
      then have "\<And>B C. B\<in>\<FF> \<Longrightarrow> C\<in>Pow(nat) \<Longrightarrow> B \<subseteq> C \<Longrightarrow> C \<in> \<FF>" using is_filter_def_split(5) by auto
      with A have CC:"\<And>C. C \<subseteq> nat \<Longrightarrow> {m\<in>nat. pf`m <|S`m| } \<subseteq> C \<Longrightarrow> C\<in>\<FF>" by auto
      then have "{m\<in>nat. ?h`m\<in>S`m} \<subseteq> nat \<Longrightarrow> {m\<in>nat. pf`m <|S`m| } \<subseteq> {m\<in>nat. ?h`m\<in>S`m} \<Longrightarrow> {m\<in>nat. ?h`m\<in>S`m}\<in>\<FF>" by auto
      with B have C:"{m\<in>nat. ?h`m\<in>S`m}\<in> \<FF>" by auto
      with h_fun have T:"[?h]\<in>H" using S(2) unfolding internal_set_def[OF S2] using seq_class_def by auto
      have "nat\<in>Pow(nat)" by auto
      then have Q:"ConstantFunction(nat,nat):nat \<rightarrow> Pow(nat)" using func1_3_L1[of nat "Pow(nat)"] by auto
      have im:"?f`[?h] = hyper_rel``{?p}" 
        unfolding seq_class_def[OF h_fun] using internal_fun_apply(1)[OF S2 Q g2 h_fun C] by auto
      have "?p:nat\<rightarrow>nat" using internal_fun_apply(2)[OF S2 Q g2 h_fun C] by auto
      {
        fix i assume n:"i\<in>nat" and as:"pf`i\<in>|S`i|"
        then have p:"?p`i = (if ?h ` i \<in> S ` i then g ` i ` (?h ` i) else ?h ` i)" using apply_equality
          `?p:nat\<rightarrow>nat` by auto
        have h:"?h`i = (if pf`i\<in>|S`i| then converse(g`i)`(pf`i) else 0)" using h_fun apply_equality n by auto
        with as have A:"?h`i = converse(g`i)`(pf`i)" by auto moreover
        from n g have B:"g`i\<in>bij(S`i,|S`i|)" using apply_type by auto
        then have "converse(g`i)\<in>bij(|S`i|, S`i)" using bij_converse_bij by auto
        then have "converse(g`i)`(pf`i)\<in>S`i" using apply_type[OF bij_is_fun] n as unfolding lt_def by auto
        ultimately have "?h`i\<in>S`i" by auto
        with p have "?p`i = g ` i ` (?h ` i)" by auto
        then have "?p`i = g ` i `(converse(g`i)`(pf`i))" using subst[OF A, of "\<lambda>q. ?p`i = g`i`q"]
          by auto
        then have "?p`i = pf`i" using right_inverse_bij[OF B as] by auto
      }
      then have "{i\<in>nat. pf`i\<in>|S`i|} \<subseteq> {i\<in>nat. ?p`i = pf`i}" by auto
      then have "{i\<in>nat. pf`i<|S`i|} \<subseteq> {i\<in>nat. ?p`i = pf`i}" unfolding lt_def by auto
      moreover from CC have "{i\<in>nat. ?p`i = pf`i} \<subseteq> nat \<Longrightarrow> {m\<in>nat. pf`m <|S`m| } \<subseteq> {i\<in>nat. ?p`i = pf`i}\<Longrightarrow> {i\<in>nat. ?p`i = pf`i}\<in>\<FF>"
        by auto
      ultimately have "{i\<in>nat. ?p`i = pf`i}\<in>\<FF>" by auto
      then have "\<langle>?p,pf\<rangle>\<in>hyper_rel" unfolding hyper_rel_def using `?p:nat\<rightarrow>nat` pf(1) by auto
      then have "[?p] = [pf]" using `?p:nat\<rightarrow>nat` pf(1) using equiv_class_eq[OF hyper_equiv]
        seq_class_def by auto
      with pf(2) have "[?p] = p" by auto
      with im have "?f`[?h] = p" using seq_class_def `?p:nat\<rightarrow>nat` by auto
      with T have "\<exists>h\<in>H. ?f`h = p" by auto
    }
    then have "?f\<in>surj(H,{p\<in>*\<nat>. p *< [?N]})"
      unfolding surj_def using fun by auto
    with `?f\<in>inj(H,{p\<in>*\<nat>. p *< [?N]})` have "?f\<in>bij(H,{p\<in>*\<nat>. p *< [?N]})"
      unfolding bij_def by auto
    then have "\<exists>SS\<in>nat\<rightarrow>Pow(nat). \<exists>g\<in>Pi(nat, \<lambda>i. SS`i \<rightarrow> nat). internal_fun(g)\<in>bij(H,{p\<in>*\<nat>. p *< [?N]})" using gg Y by auto
  }
  then have R1:"\<And>g. g \<in>(\<Prod>i\<in>nat. bij(S ` i, |S ` i|)) \<Longrightarrow> \<exists>SS\<in>nat\<rightarrow>Pow(nat). \<exists>Sa\<in>Pi(nat, \<lambda>i. SS`i \<rightarrow> nat). internal_fun(Sa) \<in> bij(H, {p \<in> *\<nat>. p *< [?N]})" by auto
  let ?g="{\<langle>i,{\<langle>q,|{p\<in>S`i. p < q}|\<rangle>. q\<in>S`i}\<rangle>. i\<in>nat}"
  {
    fix i assume as1:"i\<in>nat"
    let ?u="{\<langle>q,|{p\<in>S`i. p < q}|\<rangle>. q\<in>S`i}"
    {
      fix q assume as2:"q\<in>S`i"
      have sub:"{p\<in>S`i. p < q} \<subseteq> S`i" by auto
      from S(1) as1 have C:"S`i\<in>FinPow(nat)" using apply_type by auto
      with sub have "{p\<in>S`i. p < q}\<in>FinPow(nat)" using subset_finpow by auto
      moreover from as2 C have "q\<in>nat" unfolding FinPow_def by auto moreover
      {
        assume "q\<in>{p\<in>S`i. p < q}"
        then have "q<q" by auto
        then have False unfolding lt_def using mem_irrefl by auto
      }
      ultimately have "{p\<in>S`i. p < q}\<in>FinPow(nat)" "q\<in>nat-{p\<in>S`i. p < q}" by auto
      then have "|{p\<in>S`i. p<q}\<union>{q}| = succ(|{p\<in>S`i. p<q}|)" using card_fin_add_one by auto
      moreover have "{p\<in>S`i. p<q}\<union>{q} \<subseteq> S`i" using as2 sub by auto
      then have l:"{p\<in>S`i. p<q}\<union>{q} \<lesssim> S`i" using subset_imp_lepoll by auto
      have "Finite(S`i)" using C unfolding FinPow_def by auto
      then obtain r where "well_ord(S`i,r)" using Finite_imp_well_ord by auto
      with l have "|{p\<in>S`i. p<q}\<union>{q}| \<le> |S`i|" using well_ord_lepoll_imp_cardinal_le by auto
      ultimately have "succ(|{p\<in>S`i. p<q}|) \<le> |S`i|" using subst[of _ "succ(|{p\<in>S`i. p<q}|)"
        "\<lambda>q. q\<le>|S`i|"] by auto moreover
      have "|{p\<in>S`i. p<q}| < succ(|{p\<in>S`i. p<q}|)" using le_refl[OF Ord_cardinal] by auto
      ultimately have "|{p\<in>S`i. p<q}| < |S`i|" using lt_trans2[of "|{p\<in>S`i. p<q}|" "succ(|{p\<in>S`i. p<q}|)"] by auto
      then have "|{p\<in>S`i. p<q}| \<in> |S`i|" unfolding lt_def by auto
    }
    then have u_fun:"?u:S`i \<rightarrow> |S`i|" unfolding Pi_def function_def by auto
    {
      fix q1 q2 assume as:"q1\<in>S`i" "q2\<in>S`i" "?u`q1 = ?u`q2"
      then have M:"|{p\<in>S`i. p<q1}| = |{p\<in>S`i. p<q2}|" using apply_equality u_fun by auto
      from S(1) as1 have Q:"S`i\<in>FinPow(nat)" using apply_type by auto
      with as(1,2) have nat:"q1\<in>nat" "q2\<in>nat" unfolding FinPow_def by auto
      {
        assume eq:"q1 < q2"
        with as(1) have A:"q1\<in>{p\<in>S`i. p<q2}" by auto
        have B:"q1\<notin>{p\<in>S`i. p<q1}" using mem_irrefl unfolding lt_def by auto
        {
          assume "{p\<in>S`i. p<q1}={p\<in>S`i. p<q2}"
          with A B have False by auto
        }
        then have C:"{p\<in>S`i. p<q1}\<noteq>{p\<in>S`i. p<q2}" by auto
        {
          fix p assume "p\<in>{p\<in>S`i. p<q1}"
          then have "p\<in>S`i" "p<q1" by auto
          then have "p\<in>S`i" "p<q2" using lt_trans eq by auto
          then have "p\<in>{p\<in>S`i. p<q2}" by auto
        }
        then have D:"{p\<in>S`i. p<q1}\<subseteq>{p\<in>S`i. p<q2}" by auto
        from Q have "{p\<in>S`i. p<q2}\<in>FinPow(nat)" using subset_finpow by blast
        then have E:"Finite({p\<in>S`i. p<q2})" unfolding FinPow_def by auto
        from C D E have "|{p\<in>S`i. p<q1}|<|{p\<in>S`i. p<q2}|" using strict_subset_smaller by auto
        with M have False using lt_irrefl by auto
      }
      then have E1:"q2\<le>q1" using not_lt_iff_le[OF nat_into_Ord[OF nat(1)] nat_into_Ord[OF nat(2)]] by blast
      {
        assume eq:"q2 < q1"
        with as(2) have A:"q2\<in>{p\<in>S`i. p<q1}" by auto
        have B:"q2\<notin>{p\<in>S`i. p<q2}" using mem_irrefl unfolding lt_def by auto
        {
          assume "{p\<in>S`i. p<q1}={p\<in>S`i. p<q2}"
          with A B have False by auto
        }
        then have C:"{p\<in>S`i. p<q2}\<noteq>{p\<in>S`i. p<q1}" by auto
        {
          fix p assume "p\<in>{p\<in>S`i. p<q2}"
          then have "p\<in>S`i" "p<q2" by auto
          then have "p\<in>S`i" "p<q1" using lt_trans eq by auto
          then have "p\<in>{p\<in>S`i. p<q1}" by auto
        }
        then have D:"{p\<in>S`i. p<q2}\<subseteq>{p\<in>S`i. p<q1}" by auto
        from Q have "{p\<in>S`i. p<q1}\<in>FinPow(nat)" using subset_finpow by blast
        then have E:"Finite({p\<in>S`i. p<q1})" unfolding FinPow_def by auto
        from C D E have "|{p\<in>S`i. p<q2}|<|{p\<in>S`i. p<q1}|" using strict_subset_smaller by auto
        with M have False using lt_irrefl by auto
      }
      then have E2:"q1\<le>q2" using not_lt_iff_le[OF nat_into_Ord[OF nat(2)] nat_into_Ord[OF nat(1)]] by blast
      with E1 have "q1=q2" using le_anti_sym by auto
    }
    with u_fun have "?u\<in>inj(S`i,|S`i|)" unfolding inj_def by auto moreover
    from S(1) as1 have C:"S`i\<in>FinPow(nat)" using apply_type by auto
    then have S:"S`i \<subseteq> nat" "Finite(S`i)" unfolding FinPow_def by auto
    then have "Finite(|S`i|)" using lepoll_Ord_imp_eqpoll[OF subset_imp_lepoll Ord_nat] eqpoll_imp_Finite_iff by auto
    moreover note S(1)
    ultimately have "?u\<in>bij(S`i,|S`i|)" using inj_function_same_card_bij[OF _ lepoll_Ord_imp_eqpoll[THEN eqpoll_sym, OF subset_imp_lepoll Ord_nat]] by auto
  }
  then have "?g\<in>Pi(nat,\<lambda>i. bij(S`i,|S`i|))" unfolding Pi_def function_def by auto
  with R1 have "\<exists>SS\<in>nat\<rightarrow>Pow(nat). \<exists>g\<in>Pi(nat, \<lambda>i. SS`i \<rightarrow> nat). internal_fun(g) \<in> bij(H, {p \<in> *\<nat>. p *< [?N]})" by auto
  then show ?thesis using N by auto
qed

lemma internal_inj_fun_nat:
  assumes "S1: nat \<rightarrow> Pow(nat)" "S2 \<in> nat \<rightarrow> Pow(nat)" "S \<in> (\<Prod>i\<in>nat. S1 ` i \<rightarrow> S2 ` i)"
    and "internal_fun(S)\<in>inj(internal_set(S1), internal_set(S2))"
  shows "{n\<in>nat. S`n\<in>inj(S1`n,S2`n)}\<in>\<FF>" apply (rule internal_inj_fun)
  using assms(1) apply simp using assms(2) apply simp using assms(3) apply simp using assms(4) apply simp
proof-
  show "nat \<rightarrow> nat \<noteq>0" by auto
  let ?q1 = "\<lambda>n. \<mu> q1. \<exists>q2. (S`n)`q1 = (S`n)`q2 \<and> q1\<noteq>q2 \<and> q1\<in>S1`n \<and> q2\<in>S1`n"
  let ?q2 = "\<lambda>n. \<mu> q2. (S`n)`?q1(n) = (S`n)`q2 \<and> ?q1(n)\<noteq>q2 \<and> q2\<in>S1`n"
  {
    fix n assume as:"n\<in>nat" "S`n\<notin>inj(S1`n,S2`n)"
    from as obtain q1 q2 where q:"(S`n)`q1 = (S`n)`q2" "q1\<noteq>q2" "q1\<in>S1`n" "q2\<in>S1`n" unfolding inj_def using apply_type[OF assms(3)] by auto
    from q(1,2) have "\<exists>q2. (S`n)`?q1(n) = (S`n)`q2 \<and> ?q1(n)\<noteq>q2 \<and> ?q1(n)\<in>S1`n \<and> q2\<in>S1`n" using LeastI[of "\<lambda>t. \<exists>q2. (S`n)`t = (S`n)`q2 \<and> t\<noteq>q2 \<and> t\<in>S1`n \<and> q2\<in>S1`n"]
      nat_into_Ord[of q1] apply_type[OF assms(1) as(1)] q(3,4) by blast
    then obtain q3 where qq:"(S`n)`?q1(n) = (S`n)`q3 \<and> ?q1(n)\<noteq>q3" "?q1(n)\<in>S1`n" "q3\<in>S1`n" by auto
    then have "(S`n)`?q1(n) = (S`n)`?q2(n)" "?q1(n)\<noteq>?q2(n)" "?q2(n)\<in>S1`n" using LeastI[of "\<lambda>t. (S`n)`?q1(n) = (S`n)`t \<and> ?q1(n)\<noteq>t \<and> t\<in>S1`n"]
      nat_into_Ord[of q3] apply_type[OF assms(1) as(1)] by auto
    then have "\<langle>?q1(n),?q2(n)\<rangle>\<in>{\<langle>q1,q2\<rangle> \<in> S1 ` n \<times> S1`n . S ` n ` q1 = S ` n ` q2 \<and> q1 \<noteq> q2}"
      using apply_type[OF assms(1) as(1)] qq(2) by auto
  }
  then have "{\<langle>n,\<langle>?q1(n),?q2(n)\<rangle>\<rangle>. n\<in>{n \<in> nat . S ` n \<notin> inj(S1 ` n, S2`n)}} \<in> Pi({n \<in> nat . S ` n \<notin> inj(S1 ` n, S2`n)},\<lambda>n. {\<langle>q1,q2\<rangle> \<in> S1 ` n \<times> S1`n . S ` n ` q1 = S ` n ` q2 \<and> q1 \<noteq> q2})"
    unfolding Pi_def function_def Sigma_def by auto
  then show "(\<Prod>n\<in>{n \<in> nat . S ` n \<notin> inj(S1 ` n, S2`n)}. {\<langle>q1,q2\<rangle> \<in> S1 ` n \<times> S1`n . S ` n ` q1 = S ` n ` q2 \<and> q1 \<noteq> q2}) \<noteq> 0"
    by auto
qed

lemma hyperfinite_bijective_left_ray_rev:
  assumes "\<exists>N\<in>*\<nat>. \<exists>S\<in>nat\<rightarrow>Pow(nat). \<exists>g\<in>Pi(nat, \<lambda>i. S`i \<rightarrow> nat). internal_fun(g):bij(H,{i\<in>*\<nat>. i *< N})"
  shows "isHyperFinite(H)"
proof-
  from assms obtain N S g where NSG:"N\<in>*\<nat>" "S:nat\<rightarrow>Pow(nat)" "g\<in>Pi(nat,\<lambda>i. S`i \<rightarrow> nat)" "internal_fun(g)\<in>bij(H,{i\<in>*\<nat>. i *< N})" by auto
  have "\<And>i. i\<in>nat \<Longrightarrow> ConstantFunction(nat,nat)`i = nat" using func1_3_L2 by auto
  with NSG(3) have gg:"g\<in>Pi(nat,\<lambda>i. S`i \<rightarrow> ConstantFunction(nat,nat)`i)" unfolding Pi_def by force
  then have internal:"internal_fun(g)\<in>internal_set(S) \<rightarrow> internal_set(ConstantFunction(nat,nat))"
    using internal_fun_is_fun(1)[OF NSG(2) func1_3_L1[of nat], of g] by auto
  then have H:"H=internal_set(S)" using bij_is_fun[OF NSG(4)] unfolding Pi_def domain_def by blast
  then have sub:"H\<in>Pow(*\<nat>)" using internal_subset NSG(2) by auto
  let ?S="{\<langle>n,if Finite(S`n) then S`n else 0\<rangle>. n\<in>nat}"
  from internal NSG(4) have "internal_fun(g)\<in>inj(internal_set(S), internal_set(ConstantFunction(nat,nat)))"
    unfolding bij_def inj_def using H by auto
  then have "{n\<in>nat. g`n\<in>inj(S`n,ConstantFunction(nat,nat)`n)}\<in>\<FF>"
    using internal_inj_fun_nat[of S "ConstantFunction(nat,nat)" g] using gg NSG(2)
    func1_3_L1[of nat "Pow(nat)"] by auto
  then have "{n\<in>nat. g`n\<in>inj(S`n,nat)}\<in>\<FF>" using func1_3_L2 by auto
  from NSG(1) obtain n where n:"n:nat\<rightarrow>nat" "hyper_rel``{n}= N" unfolding hyper_set_def quotient_def by auto
  let ?N="{\<langle>q,{m\<in>nat. m < n`q}\<rangle>. q\<in>nat}"
  {
    fix q assume "q\<in>nat"
    then have q:"n`q\<in>nat" using apply_type n(1) by auto
    then have "Ord(n`q)" "n`q \<subseteq> nat" using nat_into_Ord lt_nat_in_nat[of _ "n`q"] unfolding lt_def by auto
    then have Q:"n`q = {m\<in>nat. m < n`q}" unfolding lt_def by auto
    then have "Finite({m\<in>nat. m < n`q})" using nat_into_Finite q by auto
    with Q have "{m\<in>nat. m < n`q}\<in>FinPow(nat)" unfolding FinPow_def by blast
  }
  then have NF:"?N:nat \<rightarrow> FinPow(nat)" and N:"?N:nat \<rightarrow> Pow(nat)" unfolding Pi_def function_def by auto
  {
    fix t assume t:"t\<in>internal_set(?N)"
    then obtain q where q:"q:nat\<rightarrow>nat" "t=[q]" "{n\<in>nat. q`n\<in>?N`n}\<in>\<FF>"
      unfolding internal_set_def[OF N] seq_class_def by auto
    from q(1,2) have "t\<in>*\<nat>" unfolding hyper_set_def seq_class_def[OF q(1)] by auto
    from q(3) have A:"{s\<in>nat. q`s\<in>{m\<in>nat. m < n`s}}\<in>\<FF>" using apply_equality[OF _ N] by auto
    have "{s\<in>nat. q`s\<in>{m\<in>nat. m < n`s}} \<subseteq> {s\<in>nat. q`s < n`s}" by auto
    moreover have "\<And>C. C\<subseteq>nat \<Longrightarrow> {s\<in>nat. q`s\<in>{m\<in>nat. m < n`s}} \<subseteq> C \<Longrightarrow> C\<in>\<FF>" using ultraFilter
      unfolding IsUltrafilter_def using is_filter_def_split(5) A by auto
    then have "{s\<in>nat. q`s < n`s}\<subseteq>nat \<Longrightarrow> {s\<in>nat. q`s\<in>{m\<in>nat. m < n`s}} \<subseteq> {s\<in>nat. q`s < n`s} \<Longrightarrow> {s\<in>nat. q`s < n`s}\<in>\<FF>" 
      by auto
    ultimately have "{s\<in>nat. q`s < n`s}\<in>\<FF>" by auto
    then have "[q] *< [n]" using less_seq[OF q(1) n(1)] by auto
    with q(2) n(2) have "t *< N" unfolding seq_class_def[OF q(1)] seq_class_def[OF n(1)] by auto
    with `t\<in>*\<nat>` have "t\<in>{p\<in>*\<nat>. p *< N}" by auto
  }
  then have "internal_set(?N) \<subseteq> {p\<in>*\<nat>. p *< N}" by auto moreover
  {
    fix t assume "t\<in>{p\<in>*\<nat>. p *< N}"
    then have t:"t\<in>*\<nat>" "t *< [n]" using n seq_class_def by auto
    from t(1) obtain x where x:"x:nat\<rightarrow>nat" "t=[x]" unfolding hyper_set_def quotient_def using seq_class_def by auto
    with t(2) have "[x] *< [n]" by auto
    then have "{s\<in>nat. x`s < n`s} \<in>\<FF>" using less_seq[OF x(1) n(1)] by auto
    moreover have "\<And>s. s\<in>nat \<Longrightarrow> x`s\<in>nat" using apply_type x(1) by auto
    ultimately have "{s\<in>nat. x`s\<in>{m\<in>nat. m<n`s}}\<in>\<FF>" by auto
    then have "{s\<in>nat. x`s\<in>?N`s}\<in>\<FF>" using apply_equality[OF _ N] by auto
    then have "[x]\<in>internal_set(?N)" unfolding internal_set_def[OF N] using x(1) seq_class_def by auto
    with x(2) have "t\<in>internal_set(?N)" by auto
  }
  ultimately have NN:"internal_set(?N) = {p\<in>*\<nat>. p *< N}" by auto
  let ?Q="{\<langle>i,(g`i)``(S`i)\<rangle>. i\<in>nat}"
  {
    fix q assume "q\<in>nat"
    then have "g`q:S`q \<rightarrow> nat" using NSG(3) apply_type by auto
    then have "(g`q)``(S`q) \<subseteq> nat" using func1_1_L6 by auto
  }
  then have Q:"?Q:nat \<rightarrow> Pow(nat)"unfolding Pi_def function_def by auto
  {
    fix t assume "t\<in>internal_set(?Q)"
    with Q obtain x where x:"x:nat\<rightarrow>nat" "t=[x]" "{q\<in>nat. x`q\<in>?Q`q}\<in>\<FF>"
      unfolding internal_set_def[OF Q] seq_class_def by auto
    from x(3) have "{q\<in>nat. x`q\<in>(g`q)``(S`q)}\<in>\<FF>" using apply_equality[OF _ Q] by auto
    let ?u="\<lambda>i. \<mu> u. u\<in>S`i \<and> (g`i)`u = x`i"
    let ?y="{\<langle>i,if (x`i\<in>(g`i)``(S`i)) then ?u(i) else 0\<rangle>. i\<in>nat}"
    {
      fix i assume i:"i\<in>nat"
      from i have g:"g`i:S`i\<rightarrow> nat" using NSG(3) apply_type by auto
      {
        assume as:"x`i\<in>(g`i)``(S`i)"
        then obtain u where "u\<in>S`i" "(g`i)`u = x`i" using func_imagedef[OF g] by auto
        moreover from `u\<in>S\`i` have "u\<in>nat" using apply_type[OF NSG(2)] i by auto
        then have "Ord(u)" using nat_into_Ord by auto
        ultimately have u:"?u(i)\<in>S`i" "(g`i)`?u(i) = x`i"
          using LeastI[where P="\<lambda>u. u\<in>S`i \<and> (g`i)`u = x`i"] by auto
        from u(1) have "?u(i)\<in>nat" using apply_type[OF NSG(2)] i by auto
      } moreover
      {
        assume as:"x`i\<notin>(g`i)``(S`i)"
        have "0\<in>nat" by auto
      }
      ultimately have "(if (x`i\<in>(g`i)``(S`i)) then ?u(i) else 0)\<in>nat" by auto
    }
    then have "?y \<subseteq> nat\<times>nat" by auto
    then have y:"?y:nat \<rightarrow> nat" unfolding Pi_def function_def by auto
    {
      fix q assume "q\<in>{q\<in>nat. x`q\<in>(g`q)``(S`q)}"
      then have q:"q\<in>nat" "x`q\<in>(g`q)``(S`q)" by auto
      with y have yu:"?y`q = ?u(q)" using apply_equality by auto
      from q(1) have g:"g`q:S`q\<rightarrow> nat" using NSG(3) apply_type by auto
      from q(2) obtain u where "u\<in>S`q" "(g`q)`u = x`q" using func_imagedef[OF g] by auto
      moreover from `u\<in>S\`q` have "u\<in>nat" using apply_type[OF NSG(2)] q(1) by auto
      then have "Ord(u)" using nat_into_Ord by auto
      ultimately have u:"?u(q)\<in>S`q" "(g`q)`?u(q) = x`q"
        using LeastI[where P="\<lambda>u. u\<in>S`q \<and> (g`q)`u = x`q"] by auto
      from u yu have "?y`q\<in>S`q" "(g`q)`?u(q) = x`q" by auto
    }
    then have D1:"{q\<in>nat. x`q\<in>(g`q)``(S`q)} \<subseteq> {q\<in>nat. ?y`q\<in>S`q}" and 
    D2:"{q\<in>nat. x`q\<in>(g`q)``(S`q)} \<subseteq> {q\<in>nat. (g`q)`?u(q) = x`q}" by auto
    note D1 moreover note `{q\<in>nat. x\`q\<in>(g\`q)\`\`(S\`q)}\<in>\<FF>` moreover
    from ultraFilter have "\<And>B C. C\<subseteq> nat \<Longrightarrow> B\<subseteq> C \<Longrightarrow> B\<in>\<FF> \<Longrightarrow> C\<in>\<FF>"
      unfolding IsUltrafilter_def using is_filter_def_split(5) by auto
    then have "{q\<in>nat. ?y`q\<in>S`q}\<subseteq> nat \<Longrightarrow> {q\<in>nat. x`q\<in>(g`q)``(S`q)}\<subseteq> {q\<in>nat. ?y`q\<in>S`q} \<Longrightarrow> {q\<in>nat. x`q\<in>(g`q)``(S`q)}\<in>\<FF> \<Longrightarrow> {q\<in>nat. ?y`q\<in>S`q}\<in>\<FF>"
      by auto
    ultimately have Z:"{q\<in>nat. ?y`q\<in>S`q}\<in>\<FF>" by auto
    then have "?y\<in>{f\<in>nat\<rightarrow>nat. {q\<in>nat. f`q\<in>S`q}\<in>\<FF>}" using y by auto
    then have yS:"[?y]\<in>internal_set(S)" unfolding internal_set_def[OF NSG(2)] seq_class_def[OF y] by auto
    with H have "[?y]\<in>H" by auto
    then have "internal_fun(g)`[?y]\<in>{i\<in>*\<nat>. i *< N}" using apply_type[OF bij_is_fun[OF NSG(4)]] by auto
    with NN have P:"internal_fun(g)`[?y]\<in>internal_set(?N)" by auto
    let ?z="{\<langle>i, if ?y ` i \<in> S ` i
                    then g ` i ` (?y ` i)
                    else ?y ` i\<rangle> .
                    i \<in> nat}"
    from yS have z:"internal_fun(g)`[?y] = hyper_rel `` {?z}" "?z:nat\<rightarrow>nat" using internal_fun_apply_2[OF NSG(2) func1_3_L1[OF _] gg] unfolding seq_class_def[OF y]
      by auto
    {
      fix q assume "q\<in>{q\<in>nat. ?y`q\<in>S`q}\<inter>{q\<in>nat. x`q\<in>(g`q)``(S`q)}"
      then have q:"q\<in>nat" "?y`q\<in>S`q" "x`q\<in>(g`q)``(S`q)" by auto
      from q(1) have "?z`q = (if ?y ` q \<in> S ` q
                    then g ` q ` (?y ` q)
                    else ?y ` q)" using apply_equality z(2) by auto
      with q(2) have "?z`q = g`q`(?y`q)" by auto
      with q(3) have "?z`q = (g`q)`?u(q)" using apply_equality q(1) y by auto
      moreover from q(1,3) D2 have "(g`q)`?u(q) = x`q" by auto
      ultimately have "?z`q = x`q" by auto
    }
    then have "{q\<in>nat. ?y`q\<in>S`q}\<inter>{q\<in>nat. x`q\<in>(g`q)``(S`q)} \<subseteq> {q\<in>nat. ?z`q = x`q}" by auto
    moreover have "{q\<in>nat. ?y`q\<in>S`q}\<inter>{q\<in>nat. x`q\<in>(g`q)``(S`q)}\<in>\<FF>" using 
      `{q\<in>nat. x\`q\<in>(g\`q)\`\`(S\`q)}\<in>\<FF>` Z ultraFilter unfolding IsUltrafilter_def 
      using is_filter_def_split(4) by auto
    moreover have "\<And>C B. C\<subseteq>nat \<Longrightarrow> B\<subseteq>C \<Longrightarrow> B\<in>\<FF> \<Longrightarrow> C\<in>\<FF>" using ultraFilter unfolding IsUltrafilter_def
      using is_filter_def_split(5) by auto
    ultimately have "{q\<in>nat. ?z`q = x`q}\<subseteq>nat \<Longrightarrow> {q\<in>nat. ?z`q = x`q}\<in>\<FF>" by auto
    then have "{q\<in>nat. ?z`q = x`q}\<in>\<FF>" by auto
    then have "\<langle>?z,x\<rangle>\<in>hyper_rel" unfolding hyper_rel_def using z x(1) by auto
    then have "[?z] = [x]" using equiv_class_eq[OF hyper_equiv] seq_class_def z x(1) by auto
    with x(2) have "[?z] = t" by auto
    with z(1) have "internal_fun(g)`[?y] = t" using seq_class_def z(2) by auto
    with P have "t\<in>internal_set(?N)" by auto
  }
  then have "internal_set(?Q) \<subseteq> internal_set(?N)" by auto
  moreover
  have "id(nat)\<in>nat\<rightarrow>nat" using id_bij unfolding bij_def inj_def by auto
  then have "nat\<rightarrow>nat \<noteq>0" by auto moreover note Q N moreover
  let ?qq="{\<langle>j,\<mu> p. p\<in>?Q`j-?N`j\<rangle>. j\<in>{i\<in>nat. \<not>(?Q`i \<subseteq> ?N`i)}}"
  {
    fix j assume "j\<in>{i\<in>nat. \<not>(?Q`i \<subseteq> ?N`i)}"
    then have j:"j\<in>nat" "\<not>(?Q`j \<subseteq> ?N`j)" by auto
    from j(1) have g:"g`j:S`j\<rightarrow> nat" using NSG(3) apply_type by auto
    from j(2) obtain u where u:"u\<in>?Q`j - ?N`j" by auto
    then have "u\<in>?Q`j" by auto
    then have "u\<in>(g`j)``(S`j)" using j(1) Q apply_equality by auto
    then obtain v where "v\<in>S`j" "(g`j)`v = u" using func_imagedef[OF g] by auto
    with g have "u\<in>nat" using apply_type by auto
    then have "Ord(u)" using nat_into_Ord by auto
    with u have "(\<mu> p. p\<in>?Q`j -?N`j)\<in>?Q`j -?N`j" using LeastI[where P="\<lambda>p. p\<in>?Q`j -?N`j"] by auto
  }
  then have "?qq\<in>Pi({i\<in>nat. \<not>(?Q`i \<subseteq> ?N`i)},\<lambda>j. ?Q`j-?N`j)" unfolding Pi_def function_def
    by auto ultimately
  have "{n\<in>nat. ?Q`n \<subseteq> ?N`n}\<in>\<FF>" using internal_sub_rev by auto
  let ?S="{\<langle>i,if Finite(S`i) then S`i else 0\<rangle>. i\<in>nat}"
  {
    fix q assume "q\<in>nat"
    {
      assume "Finite(S`q)"
      then have A:"(if Finite(S`q) then S`q else 0) = S`q" by auto
      with `Finite(S\`q)` have "Finite(if Finite(S`q) then S`q else 0)" by auto
      moreover from A have "(if Finite(S`q) then S`q else 0) \<subseteq> nat" using apply_type[OF NSG(2)]
        `q\<in>nat` by auto
      ultimately have "(if Finite(S`q) then S`q else 0)\<in>FinPow(nat)" unfolding FinPow_def by auto 
    }
    moreover
    {
      assume "\<not>Finite(S`q)"
      then have A:"(if Finite(S`q) then S`q else 0) = 0" by auto
      then have "(if Finite(S`q) then S`q else 0)\<in>FinPow(nat)" unfolding FinPow_def by auto
    }
    ultimately have "(if Finite(S`q) then S`q else 0)\<in>FinPow(nat)" by auto
  }
  then have SS:"?S\<in>nat \<rightarrow> FinPow(nat)" and S:"?S\<in>nat \<rightarrow> Pow(nat)" unfolding Pi_def function_def FinPow_def by auto
  {
    fix q assume "q\<in>{n\<in>nat. ?Q`n \<subseteq> ?N`n}\<inter>{n\<in>nat. g`n\<in>inj(S`n,nat)}"
    then have q:"q\<in>nat" "?Q`q \<subseteq> ?N`q" "g`q\<in>inj(S`q,nat)" by auto
    from NF q(1) have "?N`q\<in>FinPow(nat)" using apply_type by auto
    then have "Finite(?N`q)" unfolding FinPow_def by auto
    with q(2) have "Finite(?Q`q)" using subset_Finite by auto
    then have "Finite((g`q)``(S`q))" using apply_equality Q q(1) by auto
    moreover from q(3) have "g`q\<in>bij(S`q,range(g`q))" using inj_bij_range by auto
    then have "S`q \<approx> range(g`q)" unfolding eqpoll_def by auto
    then have "S`q \<approx> (g`q)``(S`q)" using range_image_domain inj_is_fun[OF q(3)] by auto
    ultimately have "Finite(S`q)" using eqpoll_imp_Finite_iff by auto
    then have "(if Finite(S`q) then S`q else 0) = S`q" by auto
    then have "?S`q = S`q" using apply_equality q(1) SS by auto
  }
  then have "{n\<in>nat. ?Q`n \<subseteq> ?N`n}\<inter>{n\<in>nat. g`n\<in>inj(S`n,nat)} \<subseteq> {q\<in>nat. ?S`q = S`q}" by auto
  moreover have "{q\<in>nat. ?S`q = S`q} \<subseteq> nat" by auto
  moreover have "{n\<in>nat. ?Q`n \<subseteq> ?N`n}\<inter>{n\<in>nat. g`n\<in>inj(S`n,nat)}:\<FF>" using
    `{n\<in>nat. ?Q\`n \<subseteq> ?N\`n}:\<FF>` `{n\<in>nat. g\`n\<in>inj(S\`n,nat)}\<in>\<FF>` ultraFilter
    unfolding IsUltrafilter_def using is_filter_def_split(4) by auto
  ultimately have "{q\<in>nat. ?S`q = S`q}\<in>\<FF>" using ultraFilter
    unfolding IsUltrafilter_def using is_filter_def_split(5) by auto
  then have "internal_set(?S) = internal_set(S)" using internal_eq S NSG(2) by auto
  with H have "H = internal_set(?S)" by auto
  with SS have "\<exists>S\<in>nat \<rightarrow> FinPow(nat). H= internal_set(S)" by auto
  then show ?thesis unfolding isHyperFinite_def[OF sub].
qed

end