(*
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2022  Daniel de la Concepcion

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

section \<open>Rings - Ideals of quotient rings\<close>

theory Ring_ZF_3 imports Ring_ZF_2 Group_ZF_5

begin

text \<open>This section studies the ideals of quotient rings,
and defines ring homomorphisms.\<close>

definition
  ringHomomor ("_{is a ring homomorphism}{_,_,_}\<rightarrow>{_,_,_}" 85)
  where "IsAring(R,A,M) \<Longrightarrow> IsAring(S,U,V) \<Longrightarrow> ringHomomor(f,R,A,M,S,U,V) \<equiv> 
    Homomor(f,R,A,S,U) 
    \<and> (\<forall>x\<in>R. \<forall>y\<in>R. f`(M`\<langle>x,y\<rangle>) = V`\<langle>f`x,f`y\<rangle>) 
    \<and> f`(TheNeutralElement(R,M)) = TheNeutralElement(S,V)"

locale ring_homo =
  fixes T A M S U V f
  assumes origin:"IsAring(T,A,M)" 
    and target:"IsAring(S,U,V)"
    and fun:"f:T\<rightarrow>S"
    and homomorphism:"f{is a ring homomorphism}{T,A,M}\<rightarrow>{S,U,V}"

  fixes ringa (infixl "\<ra>\<^sub>R" 90)
  defines ringa_def [simp]: "x\<ra>\<^sub>Rb \<equiv> A`\<langle>x,b\<rangle>"

  fixes ringminus ("\<rm>\<^sub>R _" 89)
  defines ringminus_def [simp]: "(\<rm>\<^sub>Rx) \<equiv> GroupInv(T,A)`(x)"

  fixes ringsub (infixl "\<rs>\<^sub>R" 90)
  defines ringsub_def [simp]: "x\<rs>\<^sub>Rb \<equiv> x\<ra>\<^sub>R(\<rm>\<^sub>Rb)"

  fixes ringm (infixl "\<cdot>\<^sub>R" 95)
  defines ringm_def [simp]: "x\<cdot>\<^sub>Rb \<equiv> M`\<langle>x,b\<rangle>"

  fixes ringzero ("\<zero>\<^sub>R")
  defines ringzero_def [simp]: "\<zero>\<^sub>R \<equiv> TheNeutralElement(T,A)"

  fixes ringone ("\<one>\<^sub>R")
  defines ringone_def [simp]: "\<one>\<^sub>R \<equiv> TheNeutralElement(T,M)"

  fixes ringtwo ("\<two>\<^sub>R")
  defines ringtwo_def [simp]: "\<two>\<^sub>R \<equiv> \<one>\<^sub>R\<ra>\<^sub>R\<one>\<^sub>R"

  fixes ringsq ("_\<^sup>2\<^sup>R" [96] 97)
  defines ringsq_def [simp]: "x\<^sup>2\<^sup>R \<equiv> x\<cdot>\<^sub>Rx"

  fixes ringas (infixl "\<ra>\<^sub>S" 90)
  defines ringas_def [simp]: "x\<ra>\<^sub>Sb \<equiv> U`\<langle>x,b\<rangle>"

  fixes ringminuss ("\<rm>\<^sub>S _" 89)
  defines ringminuss_def [simp]: "(\<rm>\<^sub>Sx) \<equiv> GroupInv(S,U)`(x)"

  fixes ringsubs (infixl "\<rs>\<^sub>S" 90)
  defines ringsubs_def [simp]: "x\<rs>\<^sub>Sb \<equiv> x\<ra>\<^sub>S(\<rm>\<^sub>Sb)"

  fixes ringms (infixl "\<cdot>\<^sub>S" 95)
  defines ringms_def [simp]: "x\<cdot>\<^sub>Sb \<equiv> V`\<langle> x,b\<rangle>"

  fixes ringzeros ("\<zero>\<^sub>S")
  defines ringzeros_def [simp]: "\<zero>\<^sub>S \<equiv> TheNeutralElement(S,U)"

  fixes ringones ("\<one>\<^sub>S")
  defines ringones_def [simp]: "\<one>\<^sub>S \<equiv> TheNeutralElement(S,V)"

  fixes ringtwos ("\<two>\<^sub>S")
  defines ringtwos_def [simp]: "\<two>\<^sub>S \<equiv> \<one>\<^sub>S\<ra>\<^sub>S\<one>\<^sub>S"

  fixes ringsqs ("_\<^sup>2\<^sup>S" [96] 97)
  defines ringsqs_def [simp]: "x\<^sup>2\<^sup>S \<equiv> x\<cdot>\<^sub>Sx"

abbreviation (in ring_homo) ideal_origin ("_\<triangleleft>R\<^sub>o")
  where "I\<triangleleft>R\<^sub>o \<equiv> ring0.Ideal(T,A,M,I)"

abbreviation (in ring_homo) prime_ideal_target ("_\<triangleleft>\<^sub>pR\<^sub>t")
  where "I\<triangleleft>\<^sub>pR\<^sub>t \<equiv> ring0.primeIdeal(S,U,V,I)"

abbreviation (in ring_homo) prime_ideal_origin ("_\<triangleleft>\<^sub>pR\<^sub>o")
  where "I\<triangleleft>\<^sub>pR\<^sub>o \<equiv> ring0.primeIdeal(T,A,M,I)"

abbreviation (in ring_homo) ideal_target ("_\<triangleleft>R\<^sub>t")
  where "I\<triangleleft>R\<^sub>t \<equiv> ring0.Ideal(S,U,V,I)"

sublocale ring_homo < origin_ring:ring0 T
  using origin unfolding ring0_def by auto

sublocale ring_homo < target_ring:ring0 S U V ringas
  ringminuss ringsubs ringms ringzeros ringones ringtwos
  ringsqs
  using target unfolding ring0_def by auto

lemma (in ring_homo) homomor_dest_mult:
  assumes "x\<in>T" "y\<in>T"
  shows "f`(x\<cdot>\<^sub>Ry) = (f`x)\<cdot>\<^sub>S(f`y)"
  using assms origin target homomorphism ringHomomor_def by auto

lemma (in ring_homo) homomor_dest_add:
  assumes "x\<in>T" "y\<in>T"
  shows "f`(x\<ra>\<^sub>Ry) = (f`x)\<ra>\<^sub>S(f`y)"
  using homomor_eq[of T A S U f x y]
  origin target homomorphism assms
  unfolding IsAring_def ringHomomor_def[OF origin target]
  by auto

lemma (in ring_homo) homomor_dest_minus:
  assumes "x\<in>T"
  shows "f`(\<rm>\<^sub>Rx) = \<rm>\<^sub>S(f`x)"
  using image_inv[of T A S U f x]
  origin target homomorphism assms fun
  unfolding IsAring_def ringHomomor_def[OF origin target]
  by auto

lemma (in ring_homo) homomor_dest_subs:
  assumes "x\<in>T" "y\<in>T"
  shows "f`(x\<rs>\<^sub>Ry) = (f`x)\<rs>\<^sub>S(f`y)"
  using assms homomor_dest_add[of x "\<rm>\<^sub>Ry"]
    homomor_dest_minus[of y]
  using origin_ring.Ring_ZF_1_L3(1) by auto

lemma (in ring_homo) preimage_ideal:
  assumes "J\<triangleleft>R\<^sub>t"
  shows "(f-``J)\<triangleleft>R\<^sub>o"
proof-
  have "IsAnormalSubgroup(T,A,f-``J)"
    using preimage_normal_subgroup[OF _ _ _ fun]
      target_ring.ideal_normal_add_subgroup origin assms
      target homomorphism
    unfolding IsAring_def ring0_def
    ringHomomor_def[OF origin target] by auto
  then have "IsAsubgroup(f-``J,A)" unfolding IsAnormalSubgroup_def
    by auto moreover
  {
    fix x y assume xy:"x\<in>f-``J" "y\<in>T"
    from xy(1) have "f`x \<in> J" "x\<in>T" using func1_1_L15 fun
      by auto
    moreover have "f`y\<in>S" using xy(2) apply_type fun
      by auto
    ultimately have "V`\<langle>f`x,f`y\<rangle>\<in>J" "V`\<langle>f`y,f`x\<rangle>\<in>J"
      using target_ring.ideal_dest_mult assms
      by auto
    then have "f`(M`\<langle>x,y\<rangle>)\<in>J" "f`(M`\<langle>y,x\<rangle>)\<in>J"
      using homomor_dest_mult xy(2) \<open>x\<in>T\<close>
      by auto
    moreover have "M`\<langle>x,y\<rangle>\<in>T" "M`\<langle>y,x\<rangle>\<in>T" using xy(2) \<open>x\<in>T\<close>
      origin_ring.Ring_ZF_1_L4(3) by auto
    ultimately have "M`\<langle>x,y\<rangle>\<in>f-``J" "M`\<langle>y,x\<rangle>\<in>f-``J"
      using func1_1_L15 fun by auto
  }
  ultimately show "(f-``J)\<triangleleft>R\<^sub>o" using origin_ring.Ideal_def by auto
qed

text\<open>Even more, if the target ring of the homomorphism is commutative
or the homomorphism is surjective; we show that if the ideal is prime,
then its preimage is also prime. Note that this is not true in general.\<close>

lemma (in ring_homo) preimage_prime_ideal_comm:
  assumes "J\<triangleleft>\<^sub>pR\<^sub>t" "V{is commutative on}S"
  shows "(f-``J)\<triangleleft>\<^sub>pR\<^sub>o" 
proof(rule origin_ring.equivalent_prime_ideal_2)
  show "(f-``J)\<triangleleft>R\<^sub>o" using preimage_ideal assms unfolding target_ring.primeIdeal_def by auto
  {
    assume "T = f-`` J"
    then have "T = {x\<in>T. f`x \<in>J}"
      using fun func1_1_L15 by auto
    moreover have "\<one>\<^sub>R\<in>T" using origin_ring.Ring_ZF_1_L2(2).
    ultimately have "\<one>\<^sub>R\<in>{x\<in>T. f`x \<in>J}" by auto
    then have "f`(\<one>\<^sub>R) \<in>J" by auto
    moreover have "f`\<one>\<^sub>R = \<one>\<^sub>S" using homomorphism
      unfolding ringHomomor_def[OF origin_ring.ringAssum
          target_ring.ringAssum] by auto
    ultimately have "\<one>\<^sub>S \<in> J" by auto
    then have False using target_ring.ideal_with_one
      assms unfolding target_ring.primeIdeal_def by auto
  }
  then show "f -`` J \<noteq> T" by auto
  show "\<forall>x\<in>T. \<forall>y\<in>T. (\<forall>z\<in>T. x \<cdot>\<^sub>R z \<cdot>\<^sub>R y \<in> f -`` J) \<longrightarrow>
                 x \<in> f -`` J \<or> y \<in> f -`` J"
  proof(safe)
    fix x y assume as:"x\<in>T" "y\<in>T" "\<forall>z\<in>T. x \<cdot>\<^sub>R z \<cdot>\<^sub>R y \<in> f -`` J" "y \<notin> f -`` J"
    {
      fix s assume s:"s\<in>S"
      then have "(f`x)\<cdot>\<^sub>Ss\<cdot>\<^sub>S(f`y) = s\<cdot>\<^sub>S((f`x)\<cdot>\<^sub>S(f`y))"
        using assms(2) unfolding IsCommutative_def
        using apply_type[OF fun as(1)] 
          target_ring.Ring_ZF_1_L11(2) apply_type[OF fun as(2)]
        by auto
      then have "(f`x)\<cdot>\<^sub>Ss\<cdot>\<^sub>S(f`y) = s\<cdot>\<^sub>S(f`(x\<cdot>\<^sub>Ry))"
        using homomor_dest_mult[OF as(1,2)]
        by auto moreover
      from as(3) have "x\<cdot>\<^sub>Ry : f-``J" using origin_ring.Ring_ZF_1_L2(2)
        origin_ring.Ring_ZF_1_L3(5)[OF as(1)] by force
      then have "f`(x\<cdot>\<^sub>Ry) : J" using func1_1_L15 fun by auto
      with s have "s\<cdot>\<^sub>S(f`(x\<cdot>\<^sub>Ry)) :J" using assms(1)
        unfolding target_ring.primeIdeal_def using target_ring.ideal_dest_mult(2)
        by auto
      ultimately have "(f`x)\<cdot>\<^sub>Ss\<cdot>\<^sub>S(f`y):J" by auto
    }
    then have "\<forall>z\<in>S. (f`x) \<cdot>\<^sub>S z \<cdot>\<^sub>S (f`y) \<in> J" by auto
    with target_ring.equivalent_prime_ideal[OF assms(1)]
    apply_type[OF fun] as(1,2) have "f`x:J\<or>f`y:J" by auto
    with as(4,2) have "f`x:J" using func1_1_L15 fun by auto
    then show "x:f-``J" using as(1) func1_1_L15 fun by auto
  qed
qed

lemma (in ring_homo) preimage_prime_ideal_surj:
  assumes "J\<triangleleft>\<^sub>pR\<^sub>t" "f:surj(T,S)"
  shows "(f-``J)\<triangleleft>\<^sub>pR\<^sub>o" 
proof(rule origin_ring.equivalent_prime_ideal_2)
  show "(f-``J)\<triangleleft>R\<^sub>o" using preimage_ideal assms unfolding target_ring.primeIdeal_def by auto
  {
    assume "T = f-`` J"
    then have "T = {x\<in>T. f`x \<in>J}"
      using fun func1_1_L15 by auto
    moreover have "\<one>\<^sub>R\<in>T" using origin_ring.Ring_ZF_1_L2(2).
    ultimately have "\<one>\<^sub>R\<in>{x\<in>T. f`x \<in>J}" by auto
    then have "f`(\<one>\<^sub>R) \<in>J" by auto
    moreover have "f`\<one>\<^sub>R = \<one>\<^sub>S" using homomorphism
      unfolding ringHomomor_def[OF origin_ring.ringAssum
          target_ring.ringAssum] by auto
    ultimately have "\<one>\<^sub>S \<in> J" by auto
    then have False using target_ring.ideal_with_one
      assms unfolding target_ring.primeIdeal_def by auto
  }
  then show "f -`` J \<noteq> T" by auto
  show "\<forall>x\<in>T. \<forall>y\<in>T. (\<forall>z\<in>T. x \<cdot>\<^sub>R z \<cdot>\<^sub>R y \<in> f -`` J) \<longrightarrow>
                 x \<in> f -`` J \<or> y \<in> f -`` J"
  proof(safe)
    fix x y assume as:"x\<in>T" "y\<in>T" "\<forall>z\<in>T. x \<cdot>\<^sub>R z \<cdot>\<^sub>R y \<in> f -`` J" "y \<notin> f -`` J"
    {
      fix s assume s:"s\<in>S"
      with assms(2) obtain t where t:"s=f`t" "t:T"
        unfolding surj_def by auto
      then have "(f`x)\<cdot>\<^sub>S(f`t)\<cdot>\<^sub>S(f`y) = f`(x\<cdot>\<^sub>Rt\<cdot>\<^sub>Ry)"
        using homomor_dest_mult as(1,2) t(2)
        origin_ring.Ring_ZF_1_L4(3) by auto
      moreover have "(x\<cdot>\<^sub>Rt\<cdot>\<^sub>Ry)\<in>f-``J" using as(3) t(2) by auto
      ultimately have "(f`x)\<cdot>\<^sub>S(f`t)\<cdot>\<^sub>S(f`y)\<in>J" 
        using func1_1_L15 fun by auto
      with t(1) have "(f`x)\<cdot>\<^sub>Ss\<cdot>\<^sub>S(f`y)\<in>J" by auto
    }
    then have "\<forall>z\<in>S. (f`x) \<cdot>\<^sub>S z \<cdot>\<^sub>S (f`y) \<in> J" by auto
    with target_ring.equivalent_prime_ideal[OF assms(1)]
    apply_type[OF fun] as(1,2) have "f`x:J\<or>f`y:J" by auto
    with as(4,2) have "f`x:J" using func1_1_L15 fun by auto
    then show "x:f-``J" using as(1) func1_1_L15 fun by auto
  qed
qed

section\<open>Quotient ring with quotient map\<close>

locale ring2 = ring0 +
  fixes I
  assumes idealAssum:"I\<triangleleft>R"

  fixes quot ("R\<^sub>I")
  defines quot_def [simp]: "R\<^sub>I \<equiv> QuotientBy(I)"

  fixes qrel ("r\<^sub>I")
  defines qrel_def [simp]: "r\<^sub>I \<equiv> QuotientGroupRel(R,A,I)"

  fixes qfun ("f\<^sub>I")
  defines qfun_def [simp]: "f\<^sub>I \<equiv> \<lambda>r\<in>R. r\<^sub>I ``{r}"

  fixes qadd ("A\<^sub>I")
  defines qadd_def [simp]: "A\<^sub>I \<equiv> QuotientGroupOp(R, A, I)"

  fixes qmul ("M\<^sub>I")
  defines qmul_def [simp]: "M\<^sub>I \<equiv> ProjFun2(R, qrel, M)"

abbreviation (in ring2) qideal ("_\<triangleleft>R\<^sub>I") where
  "J\<triangleleft>R\<^sub>I \<equiv> ring0.Ideal(R\<^sub>I,A\<^sub>I,M\<^sub>I,J)"

abbreviation (in ring2) qprimeIdeal ("_\<triangleleft>\<^sub>pR\<^sub>I") where
  "J\<triangleleft>\<^sub>pR\<^sub>I \<equiv> ring0.primeIdeal(R\<^sub>I,A\<^sub>I,M\<^sub>I,J)"

lemma (in ring2) image_I_quotient:
  assumes "x\<in>I"
  shows "f\<^sub>I`x = \<zero>\<^sub>I"
proof-
  from assms have xR:"x\<in>R" using idealAssum ideal_dest_subset
    by auto
  with assms show ?thesis unfolding ideal_rzero_def
    using add_group.Group_ZF_2_4_L5E[OF _ xR, of I]
    Group_ZF_2_4_L5B[of R A I "QuotientGroupRel(R, A, I)"
      "TheNeutralElement(R, A)"] add_group.groupAssum
    ideal_normal_add_subgroup[OF idealAssum]
    xR by auto
qed

corollary (in ring2) image_I_quotient_2:
  shows "f\<^sub>I``I = {\<zero>\<^sub>I}"
proof
  show "f\<^sub>I``I \<subseteq> {\<zero>\<^sub>I}" using func_imagedef[OF lam_funtype
    ideal_dest_subset[OF idealAssum], of "\<lambda>u. r\<^sub>I``{u}"]
    image_I_quotient unfolding qfun_def by auto
  from idealAssum have "\<zero>\<in>I"
    using ideal_dest_zero by auto
  then have "f\<^sub>I`\<zero>:f\<^sub>I``I" "f\<^sub>I`\<zero>=\<zero>\<^sub>I"
    using image_I_quotient func_imagedef[OF lam_funtype
    ideal_dest_subset[OF idealAssum], of "\<lambda>u. r\<^sub>I``{u}"]
    by auto
  then show "{\<zero>\<^sub>I} \<subseteq> f\<^sub>I``I" by auto
qed

sublocale ring2 < quotient_ring: ring0 quot qadd qmul
  "\<lambda>x y. ideal_radd(x,I,y)" "\<lambda>y. ideal_rmin(I,y)" 
  "\<lambda>x y. ideal_rsub(x,I,y)" "\<lambda>x y. ideal_rmult(x,I,y)"
  "\<zero>\<^sub>I" "\<one>\<^sub>I" "\<two>\<^sub>I" "\<lambda>x. (x\<^sup>2\<^sup>I)" unfolding ring0_def quot_def
  using quotientBy_is_ring[OF idealAssum] apply simp
  unfolding ideal_radd_def ideal_rmin_def
            ideal_rsub_def ideal_rmult_def
         ideal_rzero_def ideal_rone_def
         ideal_rtwo_def ideal_rsqr_def apply auto
  using neutral_quotient[OF idealAssum] apply simp
  using one_quotient[OF idealAssum] apply simp
  using two_quotient[OF idealAssum] by simp

text\<open>The quotient map is a homomorphism of rings\<close>

theorem (in ring2) quotient_fun_homomor:
  shows "f\<^sub>I{is a ring homomorphism}{R,A,M}\<rightarrow>{R\<^sub>I,A\<^sub>I,M\<^sub>I}"
  unfolding ringHomomor_def[OF ringAssum quotient_ring.ringAssum]
proof(safe)
  from add_group.quotient_map[OF ideal_normal_add_subgroup[OF idealAssum]]
    show "f\<^sub>I{is a homomorphism}{R,A}\<rightarrow>{R\<^sub>I,A\<^sub>I}"
    unfolding qfun_def quot_def qadd_def QuotientBy_def[OF idealAssum] by auto
  {
    fix x y assume as:"x\<in>R" "y\<in>R"
    have "f\<^sub>I ` (x\<cdot>y) = QuotientGroupRel(R,A,I)``{x\<cdot>y}" 
      unfolding qfun_def using as Ring_ZF_1_L4(3)
      lamE lam_funtype by auto
    then have "f\<^sub>I ` (x\<cdot>y) = ((QuotientGroupRel(R,A,I)``{x}){\<cdot>I}(QuotientGroupRel(R,A,I)``{y}))"
      using EquivClass_1_L10[OF equiv_rel[OF idealAssum]
          quotientBy_mul_monoid(1)[OF idealAssum]] as by auto
    then have "f\<^sub>I ` (x\<cdot>y) = ((f\<^sub>I `x){\<cdot>I}(f\<^sub>I `y))" unfolding qfun_def
      using as lamE lam_funtype by auto
    then show "f\<^sub>I ` (M ` \<langle>x, y\<rangle>) =M\<^sub>I `  \<langle>f\<^sub>I ` x, f\<^sub>I ` y\<rangle>" by auto
  }
  have "f\<^sub>I `\<one> = QuotientGroupRel(R,A,I)``{\<one>}"
    unfolding qfun_def using lam_funtype lamE Ring_ZF_1_L2(2)
    by auto
  then have "f\<^sub>I `\<one> = TheNeutralElement(QuotientBy(I),ProjFun2(R, QuotientGroupRel(R,A,I), M))"
    using Group_ZF_2_2_L1[OF _ equiv_rel[OF idealAssum]
          quotientBy_mul_monoid(1)[OF idealAssum]]
          ringAssum unfolding IsAring_def QuotientBy_def[OF idealAssum]
    by auto
  then show "f\<^sub>I ` TheNeutralElement(R, M) = TheNeutralElement(R\<^sub>I, M\<^sub>I)"
    unfolding quot_def by auto
qed

text\<open>The quotient map is surjective\<close>

lemma (in ring2) quot_fun:
  shows "f\<^sub>I\<in>surj(R,R\<^sub>I)" unfolding qfun_def using lam_funtype unfolding quot_def QuotientBy_def[OF idealAssum]
    quotient_def qrel_def surj_def by auto

sublocale ring2 < quot_homomorphism: ring_homo R A M quot qadd qmul qfun
  _ _ _ _ _ _ _ _ "\<lambda>x y. ideal_radd(x,I,y)" "\<lambda>y. ideal_rmin(I,y)" 
  "\<lambda>x y. ideal_rsub(x,I,y)" "\<lambda>x y. ideal_rmult(x,I,y)"
  "\<zero>\<^sub>I" "\<one>\<^sub>I" "\<two>\<^sub>I" "\<lambda>x. (x\<^sup>2\<^sup>I)"
  unfolding ring_homo_def using ringAssum quotient_ring.ringAssum
    quotient_fun_homomor quot_fun unfolding surj_def by auto


theorem (in ring2) quotient_I_image:
  assumes "J\<triangleleft>R"
  shows "f\<^sub>I``(J+\<^sub>II) = f\<^sub>I``J" "f\<^sub>I``(I+\<^sub>IJ) = f\<^sub>I``J"
proof-
  have sub:"J+\<^sub>II \<subseteq> R" using assms idealAssum
    sum_ideals_is_ideal[THEN ideal_dest_subset]
    ideal_dest_subset by auto
  {
    fix t assume "t\<in>f\<^sub>I``(J+\<^sub>II)"
    then obtain q where q:"q\<in>J+\<^sub>II" "t=f\<^sub>I`q"
      using func_imagedef quot_fun unfolding surj_def
      using sub(1) by auto
    from q(1) have "q\<in>A``(J\<times>I)" "J\<times>I \<subseteq> R\<times>R" using sum_ideals_is_sum_elements
      idealAssum assms ideal_dest_subset by auto
    then obtain qj qi where qji:"qj\<in>J" "qi\<in>I"
      "q=qj\<ra>qi" using func_imagedef[of A "R\<times>R" R]
      add_group.groupAssum unfolding IsAgroup_def
      IsAmonoid_def IsAssociative_def by auto
    from qji(3) have "f\<^sub>I`q = f\<^sub>I`(qj\<ra>qi)" by auto
    with qji(1,2) assms have "(f\<^sub>I`q) = ((f\<^sub>I`qj){\<ra>I}(f\<^sub>I`qi))"
      using quot_homomorphism.homomor_dest_add[of qj qi]
      ideal_dest_subset idealAssum by auto
    with qji(2) have "f\<^sub>I ` q = ((f\<^sub>I ` qj){\<ra>I}\<zero>\<^sub>I)" using image_I_quotient
      by auto
    then have "f\<^sub>I ` qj \<in>R\<^sub>I \<Longrightarrow> f\<^sub>I ` q = (f\<^sub>I ` qj)"
      using quotient_ring.Ring_ZF_1_L3(3) by auto
    moreover have "qj\<in>R" using assms qji(1)
      ideal_dest_subset by auto
    then have "f\<^sub>I ` qj \<in>R\<^sub>I" using apply_type[OF quot_fun[THEN surj_is_fun]]
      by auto
    ultimately have "f\<^sub>I ` q = (f\<^sub>I ` qj)" by auto
    with q(2) have "t = f\<^sub>I ` qj" by auto
    then have "t\<in> f\<^sub>I``J" using qji(1) func_imagedef
      quot_fun unfolding surj_def using assms
      ideal_dest_subset by auto
  }
  then have "f\<^sub>I `` (J +\<^sub>I I) \<subseteq> f\<^sub>I `` J" by auto
  moreover
  {
    fix t assume t:"t\<in>f\<^sub>I``J"
    then obtain q where q:"q\<in>J" "t=f\<^sub>I`q"
      using func_imagedef quot_fun[THEN surj_is_fun]
      assms ideal_dest_subset by auto
    from q(1) have "q\<in>J\<union>I" by auto moreover
    have "J\<union>I \<subseteq> R" using assms idealAssum ideal_dest_subset by auto
    ultimately have "q\<in>\<langle>J\<union>I\<rangle>\<^sub>I" using generated_ideal_contains_set by auto
    then have "q\<in>J+\<^sub>II" unfolding sumIdeal_def[OF assms idealAssum].
    with q(2) have "t\<in>f\<^sub>I``(J+\<^sub>II)" using func_imagedef
      quot_fun unfolding surj_def using sub by auto
  }
  then have "f\<^sub>I``J \<subseteq> f\<^sub>I `` (J +\<^sub>I I)" by auto
  ultimately show "f\<^sub>I `` (J +\<^sub>I I) = f\<^sub>I``J" "f\<^sub>I `` (I +\<^sub>I J) = f\<^sub>I``J"
    using sum_ideals_commute assms idealAssum by auto
qed

subsection\<open>Quotient ideals\<close>

text\<open>The preimage of an ideal is an ideal, so it applies to the
quotient map; but the preimage ideal contains the quotient ideal.\<close>

lemma (in ring2) ideal_quot_preimage:
  assumes "J\<triangleleft>R\<^sub>I"
  shows "(f\<^sub>I-``J) \<triangleleft>R" "I \<subseteq> f\<^sub>I-``J"
proof-
  from quot_homomorphism.preimage_ideal[OF assms]
  show "(f\<^sub>I-``J) \<triangleleft>R" by auto
  {
    fix x assume x:"x\<in>I"
    with quot_fun have "f\<^sub>I`x = r\<^sub>I``{x}"
      using lamI[of x R] ideal_dest_subset[OF idealAssum]
      apply_equality[of x "r\<^sub>I``{x}" "f\<^sub>I"] unfolding qfun_def
      by auto
    then have "f\<^sub>I`x = \<zero>\<^sub>I" using add_group.Group_ZF_2_4_L5E[OF
          ideal_normal_add_subgroup[OF idealAssum], of x
          "r\<^sub>I" "\<zero>\<^sub>I"] x ideal_dest_subset[OF idealAssum]
      unfolding qrel_def ideal_rzero_def using
        Group_ZF_2_4_L5B[OF _ ideal_normal_add_subgroup[OF idealAssum]]
      using ringAssum unfolding IsAring_def by auto
    then have "f\<^sub>I`x \<in> J" using quotient_ring.ideal_dest_zero
      assms by auto
    then have "x\<in>f\<^sub>I-``J" using x ideal_dest_subset[OF idealAssum]
      quot_fun func1_1_L15 by auto
  }
  then show "I \<subseteq> f\<^sub>I-``J" by auto
qed

text\<open>Since the map is surjective, the image is also an ideal\<close>

lemma (in ring_homo) image_ideal_surj:
  assumes "J\<triangleleft>R\<^sub>o" "f\<in>surj(T,S)"
  shows "(f``J) \<triangleleft>R\<^sub>t" unfolding target_ring.Ideal_def
proof
  show "IsAsubgroup(f``J,U)"
  proof (rule image_subgroup)
    show "IsAgroup(T,A)" using origin_ring.ringAssum unfolding IsAring_def by auto
    show "f \<in> T \<rightarrow> S" using fun .
    show "IsAsubgroup(J,A)" using assms unfolding origin_ring.Ideal_def by auto
    show "f{is a homomorphism}{T,A}\<rightarrow>{S,U}" using homomorphism
      unfolding ringHomomor_def[OF origin target]
      by auto
    show "IsAgroup(S,U)" using target_ring.ringAssum
      unfolding IsAring_def by auto
  qed
  {
    fix x y assume xy:"x\<in>f``J" "y\<in>S"
    from xy(1) obtain j where x:"x=f`j" "j\<in>J" using func_imagedef
      fun origin_ring.ideal_dest_subset[OF assms(1)] by auto
    from xy(2) have "y\<in>f``T" using assms(2) surj_range_image_domain
      by auto
    then obtain s where y:"y=f`s" "s\<in>T" using func_imagedef
      origin_ring.ideal_dest_subset[OF assms(1)]
      fun by auto
    from x(1) y(1) have "V`\<langle>x,y\<rangle> = V`\<langle>f`j,f`s\<rangle>"
      "V`\<langle>y,x\<rangle> = V`\<langle>f`s,f`j\<rangle>" by auto
    then have "V`\<langle>x,y\<rangle> = f`(M`\<langle>j,s\<rangle>)" "V`\<langle>y,x\<rangle> = f`(M`\<langle>s,j\<rangle>)"
      using homomor_dest_mult[of s j]
        homomor_dest_mult[of j s]
        x(2) y(2) origin_ring.ideal_dest_subset[OF assms(1)] by auto
    moreover have "j\<cdot>\<^sub>Rs\<in>J" "s\<cdot>\<^sub>Rj\<in>J" using origin_ring.ideal_dest_mult[OF assms(1)]
      x(2) y(2) by auto
    ultimately have "(x\<cdot>\<^sub>Sy)\<in>f``J" "(y\<cdot>\<^sub>Sx)\<in>f``J"
      using func_imagedef fun origin_ring.ideal_dest_subset[OF assms(1)]
      by auto
  }
  then show "\<forall>x\<in>f `` J. \<forall>y\<in>S. (y\<cdot>\<^sub>Sx) \<in> f `` J \<and> (x\<cdot>\<^sub>Sy) \<in> f `` J"
    by auto
qed

text\<open>The ideals of the quotient ring are in bijection
with the ideals of the original ring that contain the ideal
by which we made the quotient.\<close>

theorem (in ring2) ideal_quot_bijection:
  defines "idealFun \<equiv> \<lambda>J\<in>quotient_ring.ideals. f\<^sub>I-``J"
  shows "idealFun \<in> bij(quotient_ring.ideals,{K\<in>\<I>. I \<subseteq> K})"
  unfolding bij_def inj_def surj_def
proof(safe)
  have "idealFun \<in> quotient_ring.ideals \<rightarrow> {f\<^sub>I-``J. J\<in>quotient_ring.ideals}"
    unfolding idealFun_def
    using lam_funtype by auto moreover
  {
    fix t assume "t\<in>{f\<^sub>I-``J. J\<in>quotient_ring.ideals}"
    then obtain K where "K\<in>quotient_ring.ideals" "f\<^sub>I-``K = t" by auto
    then have "I \<subseteq> t" "t\<triangleleft>R" "t \<subseteq> R" using ideal_quot_preimage[of K]
      using func1_1_L3[of "f\<^sub>I" R "R\<^sub>I" K]
      quot_fun unfolding surj_def by auto
    then have "t\<in>{K\<in>\<I>. I \<subseteq> K}" by auto
  }
  then have "{f\<^sub>I-``J. J\<in>quotient_ring.ideals} \<subseteq> {K\<in>\<I>. I \<subseteq> K}" by auto
  ultimately show "idealFun \<in> quotient_ring.ideals \<rightarrow> {K\<in>\<I>. I \<subseteq> K}"
    using func1_1_L1B by auto
  then show "idealFun \<in> quotient_ring.ideals \<rightarrow> {K\<in>\<I>. I \<subseteq> K}".
  {
    fix w x assume as:"w\<triangleleft>R\<^sub>I" "x\<triangleleft>R\<^sub>I" "w\<subseteq>R\<^sub>I" "x\<subseteq>R\<^sub>I" "idealFun ` w = idealFun ` x"
    then have "f\<^sub>I-``w = f\<^sub>I-``x" unfolding idealFun_def
      using beta by auto
    then have "f\<^sub>I``(f\<^sub>I-``w) = f\<^sub>I``(f\<^sub>I-``x)" by auto
    then show "w = x" using surj_image_vimage quot_fun as
      by auto
  }
  {
    fix y assume y:"quot_homomorphism.ideal_origin(y)" "y\<subseteq>R" "I \<subseteq> y"
    from y(2) have "y \<subseteq> f\<^sub>I-``(f\<^sub>I``y)" using func1_1_L9 quot_fun unfolding surj_def by auto
    moreover
    {
      fix t assume "t\<in>f\<^sub>I-``(f\<^sub>I``y)"
      then have t:"f\<^sub>I`t\<in>f\<^sub>I``y" "t\<in>R" using func1_1_L15 quot_fun
        unfolding surj_def by auto
      from t(1) y(2) obtain s where s:"s\<in>y" "f\<^sub>I`t = f\<^sub>I`s"
        using func_imagedef[of "f\<^sub>I" R "R\<^sub>I" y] quot_fun unfolding surj_def
        by auto
      from s(1) have "s\<in>R" using y(2) by auto
      with t(2) have E:"f\<^sub>I`t : R\<^sub>I" "f\<^sub>I`s: R\<^sub>I" using apply_type[of "f\<^sub>I" R "\<lambda>u. R\<^sub>I"]
        quot_fun unfolding surj_def by auto
      with s(2) have "ideal_rsub(f\<^sub>I`t,I,f\<^sub>I`s) = \<zero>\<^sub>I"
        using quotient_ring.Ring_ZF_1_L3(7) by auto
      then have "f\<^sub>I`(t\<rs>s) = \<zero>\<^sub>I" using quot_homomorphism.homomor_dest_subs
        t(2) `s:R` by auto
      then have "r\<^sub>I``{t\<rs>s} = TheNeutralElement(R\<^sub>I,A\<^sub>I)"
        using Ring_ZF_1_L4(2) t(2) `s\<in>R` unfolding qfun_def
        using beta by auto
      then have "t\<rs>s \<in>I" using add_group.Group_ZF_2_4_L5E[OF
        ideal_normal_add_subgroup[OF idealAssum] Ring_ZF_1_L4(2)[OF t(2) `s\<in>R`]]
        unfolding quot_def QuotientBy_def[OF idealAssum] by auto
      with y(3) have "t\<rs>s \<in> y" by auto
      then have "(t\<rs>s)\<ra>s \<in>y" using s(1) y(1) ideal_dest_sum
        by auto
      then have "t \<in>y" using Ring_ZF_2_L1A(1) `t:R` `s:R` by auto
    }
    ultimately have "f\<^sub>I-``(f\<^sub>I``y) = y" by blast moreover
    have "f\<^sub>I``y \<subseteq> R\<^sub>I" using func1_1_L6(2)[of "f\<^sub>I" R "R\<^sub>I"] quot_fun
      unfolding surj_def by auto moreover
    have "(f\<^sub>I``y)\<triangleleft>R\<^sub>I" using quot_homomorphism.image_ideal_surj
      quot_fun y(1) by auto
    ultimately show "\<exists>x\<in>quotient_ring.ideals. idealFun ` x = y"
      unfolding idealFun_def
      by auto
  }
qed

theorem (in ring2) quot_converse:
  defines "idealFun \<equiv> \<lambda>J\<in>quotient_ring.ideals. f\<^sub>I-``J"
  assumes "J\<triangleleft>R" "I\<subseteq>J"
  shows "converse(idealFun)`J = f\<^sub>I``J"
proof-
  let ?g="\<lambda>J\<in>{K\<in>\<I>. I\<subseteq>K}. f\<^sub>I``J"
  have "?g\<in>{K\<in>\<I>. I\<subseteq>K} \<rightarrow> {f\<^sub>I``J. J\<in>{K\<in>\<I>. I\<subseteq>K}}"
    using lam_funtype by auto moreover
  have "{f\<^sub>I``J. J\<in>{K\<in>\<I>. I\<subseteq>K}} \<subseteq> quotient_ring.ideals"
    using quot_homomorphism.image_ideal_surj quotient_ring.ideal_dest_subset
    quot_fun by auto
  ultimately have "?g\<in>{K\<in>\<I>. I\<subseteq>K} \<rightarrow> quotient_ring.ideals"
    using func1_1_L1B by auto
  have "converse(idealFun)\<in>bij({K\<in>\<I>. I\<subseteq>K}, quotient_ring.ideals)"
    using bij_converse_bij ideal_quot_bijection
    unfolding idealFun_def by auto
  then have confun:"converse(idealFun):{K\<in>\<I>. I\<subseteq>K} \<rightarrow> quotient_ring.ideals"
    unfolding bij_def inj_def by auto
  moreover have J:"J\<in>{K\<in>\<I>. I\<subseteq>K}" using assms(2,3)
    ideal_dest_subset by auto
  ultimately have ideal:"converse(idealFun)`J \<in> quotient_ring.ideals"
    using apply_type[of "converse(idealFun)" "{K\<in>\<I>. I\<subseteq>K}" "\<lambda>q. quotient_ring.ideals" J]
    by auto
  then have "?g`(idealFun`(converse(idealFun)`J)) = ?g`(f\<^sub>I-``(converse(idealFun)`J))"
    using beta unfolding idealFun_def
    by auto moreover
  from ideal_quot_preimage ideal
    have "(f\<^sub>I-``(converse(idealFun)`J))\<triangleleft>R" "I\<subseteq>(f\<^sub>I-``(converse(idealFun)`J))" by auto
  then have "?g`(f\<^sub>I-``(converse(idealFun)`J)) = f\<^sub>I``(f\<^sub>I-``(converse(idealFun)`J))"
    using beta ideal_dest_subset by auto
  ultimately have "?g`(idealFun`(converse(idealFun)`J)) = f\<^sub>I``(f\<^sub>I-``(converse(idealFun)`J))"
    by auto
  then have "?g`(idealFun`(converse(idealFun)`J)) = converse(idealFun)`J"
    using surj_image_vimage quot_fun ideal by auto
  then have "?g`J = converse(idealFun)`J"
    using right_inverse_lemma[of idealFun quotient_ring.ideals
        "{K \<in> \<I> . I \<subseteq> K}" "{K \<in> \<I> . I \<subseteq> K}" J ] J
    confun bij_is_fun[OF ideal_quot_bijection]
    unfolding idealFun_def by auto
  then show ?thesis using beta J by auto
qed

corollary (in ring2) prime_ideal_quot:
  assumes "J\<triangleleft>R\<^sub>I" "K\<triangleleft>R\<^sub>I"
  shows "f\<^sub>I-``(quotient_ring.productIdeal(J, K)) = ((f\<^sub>I-``J) \<cdot>\<^sub>I (f\<^sub>I-``K)) +\<^sub>I I"
proof
  let ?idealFun = "\<lambda>J \<in> quotient_ring.ideals. f\<^sub>I-``J"
  let ?P = "((?idealFun ` J) \<cdot>\<^sub>I (?idealFun ` K)) +\<^sub>I I"
  have qRI:"quotient_ring.productIdeal(J, K)\<triangleleft>R\<^sub>I"
    using quotient_ring.product_in_intersection(2)
    assms by auto
  then have fun_prd:"?idealFun`(quotient_ring.productIdeal(J, K)) = f\<^sub>I-``(quotient_ring.productIdeal(J, K))"
    using quotient_ring.ideal_dest_subset
    beta by auto
  from assms have ideals:"(?idealFun`J) \<triangleleft>R" "(?idealFun`K) \<triangleleft>R"
    using apply_type[OF bij_is_fun[OF ideal_quot_bijection]]
     quotient_ring.ideal_dest_subset by auto
  then have idealJK:"((?idealFun`J) \<cdot>\<^sub>I (?idealFun`K)) \<triangleleft>R"
    using product_in_intersection(2) by auto
  then have idealSum:"?P \<triangleleft>R"
    using sum_ideals_is_sum_elements sum_elements_is_ideal
    ideal_dest_subset idealAssum by auto
  then have ideal:"(f\<^sub>I``?P) \<triangleleft>R\<^sub>I"
    using quot_homomorphism.image_ideal_surj quot_fun
    by auto
  have preimage:"f\<^sub>I-``J = ?idealFun`J" "f\<^sub>I-``K = ?idealFun`K"
    using assms quotient_ring.ideal_dest_subset
    beta by auto
  {
    fix t assume "t\<in>M\<^sub>I ``(J\<times>K)" moreover
    have "J\<times>K \<subseteq> R\<^sub>I\<times>R\<^sub>I" using assms
      quotient_ring.ideal_dest_subset by auto moreover
    have "M\<^sub>I:R\<^sub>I\<times>R\<^sub>I \<rightarrow> R\<^sub>I" using quotient_ring.ringAssum
      unfolding IsAring_def IsAmonoid_def
      IsAssociative_def by auto
    ultimately obtain j k where jk:"j\<in>J" "k\<in>K" "t=M\<^sub>I`\<langle>j,k\<rangle>"
      using func_imagedef by auto
    from jk(1) have "j\<in>R\<^sub>I" using assms(1)
      quotient_ring.ideal_dest_subset by auto
    then obtain jj where jj:"jj\<in>R" "f\<^sub>I`jj = j" using
      quot_fun unfolding surj_def by auto
    from jk(2) have "k\<in>R\<^sub>I" using assms(2)
      quotient_ring.ideal_dest_subset by auto
    then obtain kk where kk:"kk\<in>R" "f\<^sub>I`kk = k" using
      quot_fun unfolding surj_def by auto
    from jk(3) jj(2) kk(2)
    have "t=M\<^sub>I`\<langle>f\<^sub>I`jj,f\<^sub>I`kk\<rangle>" by auto
    then have t:"t=f\<^sub>I`(M`\<langle>jj,kk\<rangle>)" using
      quot_homomorphism.homomor_dest_mult
      jj(1) kk(1) by auto
    have "f\<^sub>I-``J \<subseteq> R" using quot_fun
      using surj_is_fun func1_1_L6A by auto moreover
    have "f\<^sub>I-``K \<subseteq> R" using quot_fun
      using surj_is_fun func1_1_L6A by auto ultimately
    have sub:"(f\<^sub>I-``J)\<times>(f\<^sub>I-``K) \<subseteq> R\<times>R" by auto moreover
    have "M:R\<times>R \<rightarrow> R" using ringAssum
      unfolding IsAring_def IsAmonoid_def
      IsAssociative_def by auto moreover
    {
      from jj have "jj\<in>f\<^sub>I-``J" using func1_1_L15
        quot_fun jk(1) unfolding surj_def by auto moreover
      from kk have "kk\<in>f\<^sub>I-``K" using func1_1_L15
        quot_fun jk(2) unfolding surj_def by auto ultimately
      have "\<langle>jj,kk\<rangle>\<in>(f\<^sub>I-``J)\<times>(f\<^sub>I-``K)" by auto
    } ultimately
    have "M`\<langle>jj,kk\<rangle> \<in> M``((f\<^sub>I-``J)\<times>(f\<^sub>I-``K))"
      using func_imagedef by auto
    then have "M`\<langle>jj,kk\<rangle> \<in> (f\<^sub>I-``J) \<cdot>\<^sub>I (f\<^sub>I-``K)"
      using quot_homomorphism.preimage_ideal
      assms product_in_intersection(3) by blast
    then have "M`\<langle>jj,kk\<rangle> \<in> ((?idealFun ` J) \<cdot>\<^sub>I (?idealFun ` K))\<union>I"
      using preimage by auto moreover
    have "((?idealFun ` J) \<cdot>\<^sub>I (?idealFun ` K))\<union>I\<subseteq>R" using
        ideal_dest_subset[OF idealAssum]
      ideal_dest_subset[OF idealJK] by blast
    ultimately have "M`\<langle>jj,kk\<rangle> \<in> ?P"
      unfolding sumIdeal_def[OF idealJK idealAssum]
      using generated_ideal_contains_set[of
          "((?idealFun ` J) \<cdot>\<^sub>I (?idealFun ` K)) \<union> I"] by blast
    then have "f\<^sub>I`(M`\<langle>jj,kk\<rangle>) \<in> f\<^sub>I``?P"
      using func1_1_L15D[OF surj_is_fun[OF quot_fun] _
       idealSum[THEN ideal_dest_subset]] by auto
    moreover note t ultimately
    have "t\<in>(f\<^sub>I``?P)"
      by auto
  }
  then have " M\<^sub>I `` (J \<times> K) \<subseteq> f\<^sub>I``?P" by blast
  then have "quotient_ring.generatedIdeal(M\<^sub>I `` (J \<times> K)) \<subseteq> f\<^sub>I``?P"
    using ideal quotient_ring.generated_ideal_small by auto
  then have "quotient_ring.productIdeal(J, K) \<subseteq> f\<^sub>I``(?P)"
    unfolding quotient_ring.productIdeal_def[OF assms].
  then have R:"f\<^sub>I-``quotient_ring.productIdeal(J, K) \<subseteq> f\<^sub>I-``(f\<^sub>I``(?P))"
    unfolding vimage_def by blast
  have "((?idealFun`J) \<cdot>\<^sub>I (?idealFun`K)) \<union> I \<subseteq> R" using idealJK idealAssum
    ideal_dest_subset by blast
  then have "I \<subseteq> ?P"
    unfolding sumIdeal_def[OF idealJK idealAssum]
    using generated_ideal_contains_set by blast
  moreover from idealSum ideal_dest_subset
  have "?P \<subseteq>R" by auto
  moreover note idealSum
  ultimately have P_ideal:"?P \<in> {N\<in>\<I>. I \<subseteq> N}"
    by auto
  then have "?idealFun`(converse(?idealFun)`?P) = ?idealFun`(f\<^sub>I``?P)"
    using quot_converse by auto
  moreover have P:"(f\<^sub>I``?P)\<triangleleft>R\<^sub>I" "f\<^sub>I``?P \<subseteq> R\<^sub>I"
    using quot_homomorphism.image_ideal_surj P_ideal
    quot_fun quotient_ring.ideal_dest_subset by auto
  ultimately have "?idealFun`(converse(?idealFun)`?P) = f\<^sub>I-``(f\<^sub>I``?P)"
    by auto
  then have "f\<^sub>I-``(f\<^sub>I``?P) = ?P" using right_inverse_bij[OF
    ideal_quot_bijection P_ideal] by auto
  with R have "f\<^sub>I-``quotient_ring.productIdeal(J, K) \<subseteq> ?P" by auto
  then show "f\<^sub>I-``quotient_ring.productIdeal(J, K) \<subseteq> ((f\<^sub>I -`` J) \<cdot>\<^sub>I (f\<^sub>I -`` K)) +\<^sub>I I"
    using fun_prd preimage by auto
  {
    fix t assume as:"t\<in>M``((f\<^sub>I-``J)\<times>(f\<^sub>I-``K))"
    moreover have "(f\<^sub>I-``J)\<times>(f\<^sub>I-``K) \<subseteq> R\<times>R" using func1_1_L15[OF surj_is_fun[OF quot_fun]] by auto
    ultimately obtain tj tk where jk:"t=tj\<cdot>tk" "tj\<in>f\<^sub>I-``J" "tk\<in>f\<^sub>I-``K"
      using func_imagedef[of M "R\<times>R" R] ringAssum unfolding IsAring_def IsAmonoid_def
      IsAssociative_def by auto
    from as have tR:"t\<in>R" using func1_1_L6(2)[of M "R\<times>R" R]
      ringAssum unfolding IsAring_def IsAmonoid_def IsAssociative_def
      by auto
    from jk(2) have j:"tj\<in>R" "f\<^sub>I`tj \<in>J" using func1_1_L15 surj_is_fun
      quot_fun by auto
    from jk(3) have k:"tk\<in>R" "f\<^sub>I`tk \<in>K" using func1_1_L15 surj_is_fun
      quot_fun by auto
    from jk(1) have "f\<^sub>I`t = f\<^sub>I`(tj\<cdot>tk)" by auto
    then have ft:"f\<^sub>I`t = ((f\<^sub>I`tj){\<cdot>I}(f\<^sub>I`tk))"  using quot_homomorphism.homomor_dest_mult
      using j(1) k(1) by auto
    from j(2) k(2) have "\<langle>f\<^sub>I`tj,f\<^sub>I`tk\<rangle>\<in>J\<times>K" by auto
    moreover have "M\<^sub>I:R\<^sub>I\<times>R\<^sub>I\<rightarrow>R\<^sub>I" using quotient_ring.ringAssum unfolding IsAring_def
      IsAmonoid_def IsAssociative_def by auto
    moreover have "J\<times>K \<subseteq> R\<^sub>I\<times>R\<^sub>I" using assms using quotient_ring.ideal_dest_subset
      by auto
    ultimately have "M\<^sub>I`\<langle>f\<^sub>I ` tj, f\<^sub>I ` tk\<rangle> \<in>M\<^sub>I``(J\<times>K)"
      using func_imagedef[of M\<^sub>I "R\<^sub>I\<times>R\<^sub>I" R\<^sub>I "J\<times>K"] by force
    with ft have "f\<^sub>I`t\<in>M\<^sub>I``(J\<times>K)" by auto
    then have "f\<^sub>I`t\<in>quotient_ring.productIdeal(J, K)"
      using quotient_ring.product_in_intersection(3) assms
      by blast
    then have "t\<in>f\<^sub>I-``quotient_ring.productIdeal(J, K)"
      using func1_1_L15 surj_is_fun[OF quot_fun] tR
      by auto
  }
  then have "M `` (f\<^sub>I -`` J \<times> f\<^sub>I -`` K) \<subseteq> f\<^sub>I -`` quotient_ring.productIdeal(J, K)" by auto
  moreover have id:"(f\<^sub>I -``quotient_ring.productIdeal(J, K)) \<triangleleft>R"
    using apply_type[OF bij_is_fun[OF ideal_quot_bijection]] using qRI
    quotient_ring.ideal_dest_subset by auto
  ultimately have "(f\<^sub>I -`` J) \<cdot>\<^sub>I (f\<^sub>I -`` K) \<subseteq> f\<^sub>I -``quotient_ring.productIdeal(J, K)"
    using generated_ideal_small productIdeal_def[OF ideals]
    using preimage by auto
  moreover have "I \<subseteq> f\<^sub>I -``quotient_ring.productIdeal(J, K)"
    using ideal_quot_preimage(2) qRI
    beta quotient_ring.ideal_dest_subset by auto
  ultimately have "((f\<^sub>I -`` J) \<cdot>\<^sub>I (f\<^sub>I -`` K))\<union>I \<subseteq>f\<^sub>I -``quotient_ring.productIdeal(J, K)"
    by auto
  then show "((f\<^sub>I -`` J) \<cdot>\<^sub>I (f\<^sub>I -`` K))+\<^sub>II \<subseteq> f\<^sub>I -``quotient_ring.productIdeal(J, K)"
    using generated_ideal_small id
      sumIdeal_def[OF idealJK idealAssum] preimage
    by auto
qed

corollary (in ring2) prime_ideal_quot_2:
  assumes "J\<triangleleft>R\<^sub>I" "K\<triangleleft>R\<^sub>I"
  shows "quotient_ring.productIdeal(J, K) = f\<^sub>I``((f\<^sub>I-`` J) \<cdot>\<^sub>I (f\<^sub>I-`` K))"
proof-
  let ?idealFun = "\<lambda>J \<in> quotient_ring.ideals. f\<^sub>I-``J"
  have "?idealFun` quotient_ring.productIdeal(J, K) =
 ((?idealFun` J) \<cdot>\<^sub>I (?idealFun` K)) +\<^sub>I I" using prime_ideal_quot
  assms beta assms quotient_ring.product_in_intersection(2)
  quotient_ring.ideal_dest_subset by auto
  then have "converse(?idealFun)`(?idealFun ` quotient_ring.productIdeal(J, K))
  = converse(?idealFun)`(((?idealFun ` J) \<cdot>\<^sub>I (?idealFun ` K)) +\<^sub>I I)"
    by auto
  moreover have "quotient_ring.productIdeal(J, K)\<triangleleft>R\<^sub>I"
    using quotient_ring.product_in_intersection(2)
    assms by auto
  then have "quotient_ring.productIdeal(J, K)\<in> quotient_ring.ideals"
    using quotient_ring.ideal_dest_subset by auto
  ultimately have A:"quotient_ring.productIdeal(J, K) =
    converse(?idealFun)`(((?idealFun ` J) \<cdot>\<^sub>I (?idealFun ` K)) +\<^sub>I I)"
    using left_inverse_bij[OF ideal_quot_bijection]
    by auto
  from assms have ideals:"(?idealFun`J) \<triangleleft>R" "(?idealFun`K) \<triangleleft>R"
    using apply_type[OF bij_is_fun[OF ideal_quot_bijection]]
     quotient_ring.ideal_dest_subset by auto
  then have idealJK:"((?idealFun`J) \<cdot>\<^sub>I (?idealFun`K)) \<triangleleft>R"
    using product_in_intersection(2) by auto
  then have "(((?idealFun` J) \<cdot>\<^sub>I (?idealFun` K)) +\<^sub>I I) \<triangleleft>R"
    using idealAssum sum_ideals_is_ideal
    ideal_dest_subset by auto
  moreover
  have prdIdeal:"((?idealFun` J) \<cdot>\<^sub>I (?idealFun` K))\<triangleleft>R"
    using assms
    using apply_type[OF ideal_quot_bijection[THEN bij_is_fun]]
    quotient_ring.ideal_dest_subset
    product_in_intersection(2) by auto
  from idealJK have "((?idealFun` J) \<cdot>\<^sub>I (?idealFun` K)) \<union> I \<subseteq> R"
    using idealAssum ideal_dest_subset by blast
  then have "I \<subseteq> (((?idealFun` J) \<cdot>\<^sub>I (?idealFun` K)) +\<^sub>I I)"
    unfolding sumIdeal_def[OF idealJK idealAssum]
    using generated_ideal_contains_set by blast
  ultimately have B:"converse(?idealFun)`(((?idealFun ` J) \<cdot>\<^sub>I (?idealFun ` K)) +\<^sub>I I) =
    f\<^sub>I``(((?idealFun ` J) \<cdot>\<^sub>I (?idealFun ` K)) +\<^sub>I I)"
    using quot_converse by auto
  with A have "quotient_ring.productIdeal(J, K) =
    f\<^sub>I``((?idealFun ` J) \<cdot>\<^sub>I (?idealFun ` K))"
    using quotient_I_image(1)[OF prdIdeal] by auto
  then show ?thesis using assms beta quotient_ring.ideal_dest_subset
    by auto
qed

text\<open>Since the map is surjective, this bijection
restricts to prime ideals on both sides.\<close>

corollary (in ring2) prime_ideal_quot_3:
  assumes "K\<triangleleft>R\<^sub>I"
  shows "K\<triangleleft>\<^sub>pR\<^sub>I \<longleftrightarrow> ((f\<^sub>I-``K)\<triangleleft>\<^sub>pR)"
proof
  {
    assume as:"K\<triangleleft>\<^sub>pR\<^sub>I"
    then have "(f\<^sub>I-``K)\<triangleleft>\<^sub>pR" using quot_homomorphism.preimage_prime_ideal_surj
      quot_fun by auto
    then show "(f\<^sub>I-``K)\<triangleleft>\<^sub>pR"
      using beta[of K quotient_ring.ideals]
      using quotient_ring.ideal_dest_subset[of K] as
      unfolding quotient_ring.primeIdeal_def by auto
  } moreover
  {
    assume as:"(f\<^sub>I-``K)\<triangleleft>\<^sub>pR"
    from assms(1) have "K\<triangleleft>R\<^sub>I". moreover
    {
      assume "K=R\<^sub>I"
      then have "f\<^sub>I-``K = f\<^sub>I-``R\<^sub>I" by auto
      then have "f\<^sub>I-``K = f\<^sub>I-``(R\<^sub>I)"
        using quotient_ring.R_ideal beta by auto
      then have "f\<^sub>I-``K = R" using func1_1_L4
        quot_fun unfolding surj_def by auto
      with as have False unfolding primeIdeal_def by auto
    }
    then have "K\<noteq>R\<^sub>I" by auto moreover
    {
      fix J P assume jp:"J\<in>quotient_ring.ideals"
        "P\<in>quotient_ring.ideals"
        "quotient_ring.productIdeal(J, P) \<subseteq> K"
      have sub:"((f\<^sub>I -`` J) \<cdot>\<^sub>I (f\<^sub>I -`` P)) \<union> I \<subseteq> R"
        using idealAssum ideal_dest_subset
        product_in_intersection(2) quot_homomorphism.preimage_ideal
        jp by auto
      from jp(3) have "f\<^sub>I -``quotient_ring.productIdeal(J, P) \<subseteq> f\<^sub>I -``K"
        by auto
      with jp(1,2) have "((f\<^sub>I -`` J) \<cdot>\<^sub>I (f\<^sub>I -`` P)) +\<^sub>I I \<subseteq> f\<^sub>I -``K" using prime_ideal_quot
        by auto
      then have "((f\<^sub>I -`` J) \<cdot>\<^sub>I (f\<^sub>I -`` P)) \<subseteq> f\<^sub>I -``K"
        using sumIdeal_def[OF product_in_intersection(2)
            [OF quot_homomorphism.preimage_ideal[of J] quot_homomorphism.preimage_ideal[of P]]
            idealAssum] jp(1,2) generated_ideal_contains_set
            sub by auto
      moreover have "f\<^sub>I -`` J \<in>\<I>" "f\<^sub>I -`` P \<in>\<I>"
        using quot_homomorphism.preimage_ideal
        ideal_dest_subset jp(1,2) by auto
      ultimately have "f\<^sub>I -`` J \<subseteq> f\<^sub>I -`` K \<or> f\<^sub>I -`` P \<subseteq> f\<^sub>I -`` K"
        using as unfolding primeIdeal_def by auto
      then have "f\<^sub>I``(f\<^sub>I -`` J) \<subseteq> f\<^sub>I``(f\<^sub>I -`` K) \<or> f\<^sub>I``(f\<^sub>I -`` P) \<subseteq> f\<^sub>I``(f\<^sub>I -`` K)"
        by blast
      then have "J \<subseteq> K \<or> P \<subseteq> K" using quot_fun
        surj_image_vimage jp(1,2) assms quotient_ring.ideal_dest_subset
        by auto
    }
    ultimately show "K\<triangleleft>\<^sub>pR\<^sub>I"
      unfolding quotient_ring.primeIdeal_def by auto
  }
qed

corollary (in ring2) bij_prime_ideals:
  defines "idealFun \<equiv> \<lambda>J\<in>quotient_ring.ideals. f\<^sub>I-``J"
  shows "restrict(idealFun,{J\<in>Pow(R\<^sub>I). J\<triangleleft>\<^sub>pR\<^sub>I})\<in>bij({J\<in>Pow(R\<^sub>I). J\<triangleleft>\<^sub>pR\<^sub>I}, {J\<in>Pow(R). I\<subseteq>J \<and> (J\<triangleleft>\<^sub>pR)})"
proof-
  have "{J\<in>Pow(R\<^sub>I). J\<triangleleft>\<^sub>pR\<^sub>I} \<subseteq> quotient_ring.ideals"
    unfolding quotient_ring.primeIdeal_def by auto
  then have rest_bij:"restrict(idealFun,{J\<in>Pow(R\<^sub>I). J\<triangleleft>\<^sub>pR\<^sub>I})\<in>bij({J\<in>Pow(R\<^sub>I). J\<triangleleft>\<^sub>pR\<^sub>I}, idealFun``{J\<in>Pow(R\<^sub>I). J\<triangleleft>\<^sub>pR\<^sub>I})" using restrict_bij
    ideal_quot_bijection unfolding bij_def
    idealFun_def by auto
  {
    fix t assume t:"t\<in>idealFun``{J\<in>Pow(R\<^sub>I). J\<triangleleft>\<^sub>pR\<^sub>I}"
    have sub:"{J\<in>Pow(R\<^sub>I). J\<triangleleft>\<^sub>pR\<^sub>I} \<subseteq> quotient_ring.ideals"
      unfolding quotient_ring.primeIdeal_def by auto
    from t obtain q where q:"q\<in>{J\<in>Pow(R\<^sub>I). J\<triangleleft>\<^sub>pR\<^sub>I}" "t=idealFun`q"
      using func_imagedef[OF bij_is_fun[OF ideal_quot_bijection] sub]
      unfolding idealFun_def by auto
    note q(1) moreover
    then have "q\<in>quotient_ring.ideals" unfolding
      quotient_ring.primeIdeal_def by auto moreover
    with q(2) have "t = f\<^sub>I-``q" "I\<subseteq>t" "t\<triangleleft>R" unfolding idealFun_def using beta
      apply_type[OF ideal_quot_bijection[THEN bij_is_fun]] by auto
    ultimately have "t\<triangleleft>R" "t\<triangleleft>\<^sub>pR" "I\<subseteq>t" using prime_ideal_quot_3
      by auto
  }
  then have "idealFun `` Collect(Pow(R\<^sub>I), qprimeIdeal) \<subseteq> {t\<in>Pow(R). I\<subseteq>t \<and> (t\<triangleleft>\<^sub>pR)}"
    using ideal_dest_subset by blast moreover
  {
    fix t assume "t\<in>{t\<in>Pow(R). I\<subseteq>t \<and> (t\<triangleleft>\<^sub>pR)}"
    then have t:"t\<in>Pow(R)" "I\<subseteq>t" "t\<triangleleft>\<^sub>pR" by auto
    then have tSet:"t\<in>{t\<in>\<I>. I \<subseteq> t}" unfolding primeIdeal_def by auto
    have "converse(idealFun)\<in>bij({t\<in>\<I>. I \<subseteq> t}, quotient_ring.ideals)"
      using ideal_quot_bijection bij_converse_bij unfolding idealFun_def
      by auto
    with tSet have cont:"converse(idealFun)`t \<in>quotient_ring.ideals"
      using apply_type[OF bij_is_fun] by blast moreover
    from tSet have eq:"idealFun`(converse(idealFun)`t) = t"
      using ideal_quot_bijection unfolding idealFun_def
      using right_inverse_bij by blast
    ultimately have "f\<^sub>I-``(converse(idealFun)`t) = t"
      using beta unfolding idealFun_def by auto
    with t(3) have "(converse(idealFun)`t) \<triangleleft>\<^sub>pR\<^sub>I"
      using prime_ideal_quot_3 cont by auto
    then have "(converse(idealFun)`t) \<triangleleft>\<^sub>pR\<^sub>I" "(converse(idealFun)`t) \<subseteq> R\<^sub>I"
      unfolding quotient_ring.primeIdeal_def
      using quotient_ring.ideal_dest_subset by auto
    then have elem:"converse(idealFun)`t\<in>{q\<in>Pow(R\<^sub>I). q\<triangleleft>\<^sub>pR\<^sub>I}"
      by auto
    have sub:"{q\<in>Pow(R\<^sub>I). q\<triangleleft>\<^sub>pR\<^sub>I} \<subseteq> quotient_ring.ideals"
      unfolding quotient_ring.primeIdeal_def by auto
    have "t\<in>idealFun``Collect(Pow(R\<^sub>I), qprimeIdeal)"
      using func_imagedef[OF ideal_quot_bijection[THEN bij_is_fun] sub] unfolding idealFun_def
      using eq elem unfolding idealFun_def by auto
  }
  then have "{t\<in>Pow(R). I\<subseteq>t \<and> (t\<triangleleft>\<^sub>pR)} \<subseteq> idealFun``Collect(Pow(R\<^sub>I), qprimeIdeal)" by auto
  ultimately
  have "{t\<in>Pow(R). I\<subseteq>t \<and> (t\<triangleleft>\<^sub>pR)} = idealFun``Collect(Pow(R\<^sub>I), qprimeIdeal)"
    by auto
  with rest_bij show ?thesis by auto
qed

end