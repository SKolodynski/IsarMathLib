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
  fixes R A M S U V f
  assumes origin:"IsAring(R,A,M)" 
    and target:"IsAring(S,U,V)"
    and fun:"f:R\<rightarrow>S"
    and homomorphism:"f{is a ring homomorphism}{R,A,M}\<rightarrow>{S,U,V}"

  fixes ringa (infixl "\<ra>\<^sub>R" 90)
  defines ringa_def [simp]: "x\<ra>\<^sub>Rb \<equiv> A`\<langle>x,b\<rangle>"

  fixes ringminus ("\<rm>\<^sub>R _" 89)
  defines ringminus_def [simp]: "(\<rm>\<^sub>Rx) \<equiv> GroupInv(R,A)`(x)"

  fixes ringsub (infixl "\<rs>\<^sub>R" 90)
  defines ringsub_def [simp]: "x\<rs>\<^sub>Rb \<equiv> x\<ra>\<^sub>R(\<rm>\<^sub>Rb)"

  fixes ringm (infixl "\<cdot>\<^sub>R" 95)
  defines ringm_def [simp]: "x\<cdot>\<^sub>Rb \<equiv> M`\<langle>x,b\<rangle>"

  fixes ringzero ("\<zero>\<^sub>R")
  defines ringzero_def [simp]: "\<zero>\<^sub>R \<equiv> TheNeutralElement(R,A)"

  fixes ringone ("\<one>\<^sub>R")
  defines ringone_def [simp]: "\<one>\<^sub>R \<equiv> TheNeutralElement(R,M)"

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
  where "I\<triangleleft>R\<^sub>o \<equiv> ring0.Ideal(R,A,M,I)"

abbreviation (in ring_homo) prime_ideal_target ("_\<triangleleft>\<^sub>pR\<^sub>t")
  where "I\<triangleleft>\<^sub>pR\<^sub>t \<equiv> ring0.primeIdeal(S,U,V,I)"

abbreviation (in ring_homo) prime_ideal_origin ("_\<triangleleft>\<^sub>pR\<^sub>o")
  where "I\<triangleleft>\<^sub>pR\<^sub>o \<equiv> ring0.primeIdeal(R,A,M,I)"

abbreviation (in ring_homo) ideal_target ("_\<triangleleft>R\<^sub>t")
  where "I\<triangleleft>R\<^sub>t \<equiv> ring0.Ideal(S,U,V,I)"

abbreviation (in ring_homo) kernel ("ker" 90) where
  "ker \<equiv> f-``{\<zero>\<^sub>S}"

sublocale ring_homo < origin_ring:ring0
  using origin unfolding ring0_def by auto

sublocale ring_homo < target_ring:ring0 S U V ringas
  ringminuss ringsubs ringms ringzeros ringones ringtwos
  ringsqs
  using target unfolding ring0_def by auto

lemma (in ring_homo) homomor_dest_mult:
  assumes "x\<in>R" "y\<in>R"
  shows "f`(x\<cdot>\<^sub>Ry) = (f`x)\<cdot>\<^sub>S(f`y)"
  using assms origin target homomorphism ringHomomor_def by auto

lemma (in ring_homo) homomor_dest_add:
  assumes "x\<in>R" "y\<in>R"
  shows "f`(x\<ra>\<^sub>Ry) = (f`x)\<ra>\<^sub>S(f`y)"
  using homomor_eq[of R A S U f x y]
  origin target homomorphism assms
  unfolding IsAring_def ringHomomor_def[OF origin target]
  by auto

lemma (in ring_homo) homomor_dest_minus:
  assumes "x\<in>R"
  shows "f`(\<rm>\<^sub>Rx) = \<rm>\<^sub>S(f`x)"
  using image_inv[of R A S U f x]
  origin target homomorphism assms fun
  unfolding IsAring_def ringHomomor_def[OF origin target]
  by auto

lemma (in ring_homo) homomor_dest_subs:
  assumes "x\<in>R" "y\<in>R"
  shows "f`(x\<rs>\<^sub>Ry) = (f`x)\<rs>\<^sub>S(f`y)"
  using assms homomor_dest_add[of x "\<rm>\<^sub>Ry"]
    homomor_dest_minus[of y]
  using origin_ring.Ring_ZF_1_L3(1) by auto


lemma (in ring_homo) homomor_dest_zero:
  shows "f`(\<zero>\<^sub>R) = \<zero>\<^sub>S"
proof-
  have "f`(\<zero>\<^sub>R) = f`(\<zero>\<^sub>R\<rs>\<^sub>R\<zero>\<^sub>R)"
    using origin_ring.Ring_ZF_1_L3(7) origin_ring.Ring_ZF_1_L2(1)
    by auto
  then have "f`(\<zero>\<^sub>R) = f`(\<zero>\<^sub>R)\<rs>\<^sub>S(f`\<zero>\<^sub>R)"
    using homomor_dest_subs origin_ring.Ring_ZF_1_L2(1)
    by auto
  then show ?thesis using target_ring.Ring_ZF_1_L3(7)
    origin_ring.Ring_ZF_1_L2(1) apply_type[OF fun] by auto
qed
    

lemma (in ring_homo) preimage_ideal:
  assumes "J\<triangleleft>R\<^sub>t"
  shows "(f-``J)\<triangleleft>R\<^sub>o" "ker \<subseteq> f-``J"
proof-
  have "IsAnormalSubgroup(R,A,f-``J)"
    using preimage_normal_subgroup[OF _ _ _ fun]
      target_ring.ideal_normal_add_subgroup origin assms
      target homomorphism
    unfolding IsAring_def ring0_def
    ringHomomor_def[OF origin target] by auto
  then have "IsAsubgroup(f-``J,A)" unfolding IsAnormalSubgroup_def
    by auto moreover
  {
    fix x y assume xy:"x\<in>f-``J" "y\<in>R"
    from xy(1) have "f`x \<in> J" "x\<in>R" using func1_1_L15 fun
      by auto
    moreover have "f`y\<in>S" using xy(2) apply_type fun
      by auto
    ultimately have "V`\<langle>f`x,f`y\<rangle>\<in>J" "V`\<langle>f`y,f`x\<rangle>\<in>J"
      using target_ring.ideal_dest_mult assms
      by auto
    then have "f`(M`\<langle>x,y\<rangle>)\<in>J" "f`(M`\<langle>y,x\<rangle>)\<in>J"
      using homomor_dest_mult xy(2) \<open>x\<in>R\<close>
      by auto
    moreover have "M`\<langle>x,y\<rangle>\<in>R" "M`\<langle>y,x\<rangle>\<in>R" using xy(2) \<open>x\<in>R\<close>
      origin_ring.Ring_ZF_1_L4(3) by auto
    ultimately have "M`\<langle>x,y\<rangle>\<in>f-``J" "M`\<langle>y,x\<rangle>\<in>f-``J"
      using func1_1_L15 fun by auto
  }
  ultimately show "(f-``J)\<triangleleft>R\<^sub>o" using origin_ring.Ideal_def by auto
  have "\<zero>\<^sub>S\<in>J" using assms target_ring.ideal_dest_zero by auto
  then show "ker \<subseteq> f-``J" by auto
qed

text\<open>Even more, if the target ring of the homomorphism is commutative
or the homomorphism is surjective; we show that if the ideal es prime,
then its preimage is also. Note that this is not true in general.\<close>

lemma (in ring_homo) preimage_prime_ideal_comm:
  assumes "J\<triangleleft>\<^sub>pR\<^sub>t" "V{is commutative on}S"
  shows "(f-``J)\<triangleleft>\<^sub>pR\<^sub>o" 
proof(rule origin_ring.equivalent_prime_ideal_2)
  show "(f-``J)\<triangleleft>R\<^sub>o" using preimage_ideal assms unfolding target_ring.primeIdeal_def by auto
  {
    assume "R = f-`` J"
    then have "R = {x\<in>R. f`x \<in>J}"
      using fun func1_1_L15 by auto
    moreover have "\<one>\<^sub>R\<in>R" using origin_ring.Ring_ZF_1_L2(2).
    ultimately have "\<one>\<^sub>R\<in>{x\<in>R. f`x \<in>J}" by auto
    then have "f`(\<one>\<^sub>R) \<in>J" by auto
    moreover have "f`\<one>\<^sub>R = \<one>\<^sub>S" using homomorphism
      unfolding ringHomomor_def[OF origin_ring.ringAssum
          target_ring.ringAssum] by auto
    ultimately have "\<one>\<^sub>S \<in> J" by auto
    then have False using target_ring.ideal_with_one
      assms unfolding target_ring.primeIdeal_def by auto
  }
  then show "f -`` J \<noteq> R" by auto
  show "\<forall>x\<in>R. \<forall>y\<in>R. (\<forall>z\<in>R. x \<cdot>\<^sub>R z \<cdot>\<^sub>R y \<in> f -`` J) \<longrightarrow>
                 x \<in> f -`` J \<or> y \<in> f -`` J"
  proof(safe)
    fix x y assume as:"x\<in>R" "y\<in>R" "\<forall>z\<in>R. x \<cdot>\<^sub>R z \<cdot>\<^sub>R y \<in> f -`` J" "y \<notin> f -`` J"
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
  assumes "J\<triangleleft>\<^sub>pR\<^sub>t" "f:surj(R,S)"
  shows "(f-``J)\<triangleleft>\<^sub>pR\<^sub>o" 
proof(rule origin_ring.equivalent_prime_ideal_2)
  show "(f-``J)\<triangleleft>R\<^sub>o" using preimage_ideal assms unfolding target_ring.primeIdeal_def by auto
  {
    assume "R = f-`` J"
    then have "R = {x\<in>R. f`x \<in>J}"
      using fun func1_1_L15 by auto
    moreover have "\<one>\<^sub>R\<in>R" using origin_ring.Ring_ZF_1_L2(2).
    ultimately have "\<one>\<^sub>R\<in>{x\<in>R. f`x \<in>J}" by auto
    then have "f`(\<one>\<^sub>R) \<in>J" by auto
    moreover have "f`\<one>\<^sub>R = \<one>\<^sub>S" using homomorphism
      unfolding ringHomomor_def[OF origin_ring.ringAssum
          target_ring.ringAssum] by auto
    ultimately have "\<one>\<^sub>S \<in> J" by auto
    then have False using target_ring.ideal_with_one
      assms unfolding target_ring.primeIdeal_def by auto
  }
  then show "f -`` J \<noteq> R" by auto
  show "\<forall>x\<in>R. \<forall>y\<in>R. (\<forall>z\<in>R. x \<cdot>\<^sub>R z \<cdot>\<^sub>R y \<in> f -`` J) \<longrightarrow>
                 x \<in> f -`` J \<or> y \<in> f -`` J"
  proof(safe)
    fix x y assume as:"x\<in>R" "y\<in>R" "\<forall>z\<in>R. x \<cdot>\<^sub>R z \<cdot>\<^sub>R y \<in> f -`` J" "y \<notin> f -`` J"
    {
      fix s assume s:"s\<in>S"
      with assms(2) obtain t where t:"s=f`t" "t:R"
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

lemma (in ring_homo) image_kernel:
  assumes "x\<in>ker"
  shows "f`x = \<zero>\<^sub>S"
  using assms func1_1_L15 fun by auto

corollary (in ring_homo) image_kernel_2:
  shows "f``(ker) = {\<zero>\<^sub>S}"
proof-
  have "\<zero>\<^sub>R \<in>ker" using homomor_dest_zero origin_ring.Ring_ZF_1_L2(1)
    func1_1_L15 fun by auto moreover
  have "ker \<subseteq> R" using func1_1_L15[OF fun, of "{\<zero>\<^sub>S}"] by auto
  then have "f `` (ker) = {f ` x . x \<in> ker}" 
    using func_imagedef[OF fun, of ker] by auto
  ultimately show ?thesis using image_kernel by auto
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

lemma (in ring2) quotient_kernel:
  shows "quot_homomorphism.kernel = I"
proof
  {
    fix t assume t:"t\<in>quot_homomorphism.kernel"
    then have t:"f\<^sub>I`t = \<zero>\<^sub>I" "t\<in>R" using quot_homomorphism.image_kernel
      func1_1_L15[OF surj_is_fun[OF quot_fun]] by auto
    then have "r\<^sub>I``{t} = \<zero>\<^sub>I" using beta by auto
    then have "t\<in>I" using add_group.Group_ZF_2_4_L5E[OF
      ideal_normal_add_subgroup[OF idealAssum] t(2)]
      neutral_quotient[OF idealAssum] unfolding
      ideal_rzero_def QuotientBy_def[OF idealAssum]
      by auto
  }
  then show "quot_homomorphism.kernel \<subseteq> I" by auto
  {
    fix t assume t:"t\<in>I"
    then have tt:"t\<in>R" using ideal_dest_subset idealAssum by auto
    then have "r\<^sub>I``{t} = \<zero>\<^sub>I" using add_group.Group_ZF_2_4_L5E[OF
      ideal_normal_add_subgroup[OF idealAssum] tt] t
      neutral_quotient[OF idealAssum] unfolding
      ideal_rzero_def QuotientBy_def[OF idealAssum]
      by auto
    then have "f\<^sub>I`t = \<zero>\<^sub>I" using beta tt by auto
    with tt have "t\<in>f\<^sub>I-``{\<zero>\<^sub>I}" using func1_1_L15
      surj_is_fun quot_fun by auto
  }
  then show "I \<subseteq> quot_homomorphism.kernel" by auto
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

sublocale ring2 < quot_homomorphism: ring_homo R A M quot qadd qmul qfun
  _ _ _ _ _ _ _ _ "\<lambda>x y. ideal_radd(x,I,y)" "\<lambda>y. ideal_rmin(I,y)" 
  "\<lambda>x y. ideal_rsub(x,I,y)" "\<lambda>x y. ideal_rmult(x,I,y)"
  "\<zero>\<^sub>I" "\<one>\<^sub>I" "\<two>\<^sub>I" "\<lambda>x. (x\<^sup>2\<^sup>I)"
  unfolding ring_homo_def using ringAssum quotient_ring.ringAssum
    quotient_fun_homomor quot_fun unfolding surj_def by auto

theorem (in ring_homo) kernel_empty_image:
  assumes "J\<triangleleft>R" "I \<subseteq> ker" "I\<triangleleft>R"
  shows "f``(J+\<^sub>II) = f``J" "f``(I+\<^sub>IJ) = f``J"
proof-
  have sub:"J+\<^sub>II \<subseteq> R" using assms
    origin_ring.sum_ideals_is_ideal[THEN origin_ring.ideal_dest_subset]
    origin_ring.ideal_dest_subset by auto
  {
    fix t assume "t\<in>f``(J+\<^sub>II)"
    then obtain q where q:"q\<in>J+\<^sub>II" "t=f`q"
      using func_imagedef fun sub(1) by auto
    from q(1) have "q\<in>A``(J\<times>I)" "J\<times>I \<subseteq> R\<times>R" 
      using origin_ring.sum_ideals_is_sum_elements
      assms(1,3) origin_ring.ideal_dest_subset by auto
    then obtain qj qi where qji:"qj\<in>J" "qi\<in>I"
      "q=qj\<ra>\<^sub>Rqi" using func_imagedef[of A "R\<times>R" R]
      origin_ring.add_group.groupAssum unfolding IsAgroup_def
      IsAmonoid_def IsAssociative_def by auto
    from qji(3) have "f`q = f`(qj\<ra>\<^sub>Rqi)" by auto
    with qji(1,2) assms(1,3) have "(f`q) = ((f`qj)\<ra>\<^sub>S(f`qi))"
      using homomor_dest_add[of qj qi] origin_ring.ideal_dest_subset
      by auto
    moreover from qji(2) assms(2) have "qi\<in>ker" by auto
    ultimately have "f ` q = ((f ` qj)\<ra>\<^sub>S\<zero>\<^sub>S)" using image_kernel
      by auto
    then have "f ` qj \<in>S \<Longrightarrow> f ` q = (f ` qj)"
      using target_ring.Ring_ZF_1_L3(3) by auto
    moreover have "qj\<in>R" using assms qji(1)
      origin_ring.ideal_dest_subset by auto
    then have "f ` qj \<in>S" using apply_type[OF fun]
      by auto
    ultimately have "f ` q = (f ` qj)" by auto
    with q(2) have "t = f` qj" by auto
    then have "t\<in> f``J" using qji(1) func_imagedef
      fun assms origin_ring.ideal_dest_subset by auto
  }
  then have "f `` (J +\<^sub>I I) \<subseteq> f `` J" by auto
  moreover
  {
    fix t assume t:"t\<in>f``J"
    then obtain q where q:"q\<in>J" "t=f`q"
      using func_imagedef fun
      assms(1) origin_ring.ideal_dest_subset by auto
    from q(1) have "q\<in>J\<union>I" by auto moreover
    have "J\<union>I \<subseteq> R" using assms(1,3) origin_ring.ideal_dest_subset by auto
    ultimately have "q\<in>\<langle>J\<union>I\<rangle>\<^sub>I" using origin_ring.generated_ideal_contains_set by auto
    then have "q\<in>J+\<^sub>II" unfolding origin_ring.sumIdeal_def[OF assms(1,3)].
    with q(2) have "t\<in>f``(J+\<^sub>II)" using func_imagedef
      fun sub by auto
  }
  then have "f``J \<subseteq> f `` (J +\<^sub>I I)" by auto
  ultimately show "f `` (J +\<^sub>I I) = f``J" "f `` (I +\<^sub>I J) = f``J"
    using origin_ring.sum_ideals_commute assms(1,3) by auto
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
  assumes "J\<triangleleft>R\<^sub>o" "f\<in>surj(R,S)"
  shows "(f``J) \<triangleleft>R\<^sub>t" unfolding target_ring.Ideal_def
proof
  show "IsAsubgroup(f``J,U)"
  proof (rule image_subgroup)
    show "IsAgroup(R,A)" using origin_ring.ringAssum unfolding IsAring_def by auto
    show "f : R \<rightarrow> S" using fun .
    show "IsAsubgroup(J,A)" using assms unfolding origin_ring.Ideal_def by auto
    show "f{is a homomorphism}{R,A}\<rightarrow>{S,U}" using homomorphism
      unfolding ringHomomor_def[OF origin target]
      by auto
    show "IsAgroup(S,U)" using target_ring.ringAssum
      unfolding IsAring_def by auto
  qed
  {
    fix x y assume xy:"x\<in>f``J" "y\<in>S"
    from xy(1) obtain j where x:"x=f`j" "j\<in>J" using func_imagedef
      fun origin_ring.ideal_dest_subset[OF assms(1)] by auto
    from xy(2) have "y\<in>f``R" using assms(2) surj_range_image_domain
      by auto
    then obtain s where y:"y=f`s" "s\<in>R" using func_imagedef
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

corollary (in ring_homo) prime_ideal_quot:
  assumes "J\<triangleleft>R\<^sub>t" "K\<triangleleft>R\<^sub>t" "f:surj(R,S)"
  shows "f-``(target_ring.productIdeal(J, K)) = origin_ring.sumIdeal(origin_ring.productIdeal((f-``J),(f-``K)), ker)"
proof
  let ?P = "origin_ring.sumIdeal(origin_ring.productIdeal((f-``J),(f-``K)), f-``{\<zero>\<^sub>S})"
  have qRI:"target_ring.productIdeal(J, K)\<triangleleft>R\<^sub>t"
    using target_ring.product_in_intersection(2)
    assms by auto
  from assms(1,2) have ideals:"(f-``J) \<triangleleft>R\<^sub>o" "(f-``K) \<triangleleft>R\<^sub>o"
    using preimage_ideal by auto
  then have idealJK:"((f-``J) \<cdot>\<^sub>I (f-``K)) \<triangleleft>R\<^sub>o"
    using origin_ring.product_in_intersection(2) by auto
  have idealSum:"?P \<triangleleft>R"
    using origin_ring.sum_ideals_is_sum_elements[OF idealJK preimage_ideal(1)[OF target_ring.zero_ideal]]
      origin_ring.sum_elements_is_ideal[OF idealJK preimage_ideal(1)[OF target_ring.zero_ideal]]
    by auto
  then have ideal:"(f``?P) \<triangleleft>R\<^sub>t"
    using image_ideal_surj assms(3)
    by auto
  {
    fix t assume "t\<in>V ``(J\<times>K)" moreover
    have "J\<times>K \<subseteq> S\<times>S" using assms
      target_ring.ideal_dest_subset by auto moreover
    have "V:S\<times>S \<rightarrow> S" using target_ring.ringAssum
      unfolding IsAring_def IsAmonoid_def
      IsAssociative_def by auto
    ultimately obtain j k where jk:"j\<in>J" "k\<in>K" "t=V`\<langle>j,k\<rangle>"
      using func_imagedef by auto
    from jk(1) have "j\<in>S" using assms(1)
      target_ring.ideal_dest_subset by auto
    then obtain jj where jj:"jj\<in>R" "f`jj = j" using
      assms(3) unfolding surj_def by auto
    from jk(2) have "k\<in>S" using assms(2)
      target_ring.ideal_dest_subset by auto
    then obtain kk where kk:"kk\<in>R" "f`kk = k" using
      assms(3) unfolding surj_def by auto
    from jk(3) jj(2) kk(2)
    have "t=V`\<langle>f`jj,f`kk\<rangle>" by auto
    then have t:"t=f`(M`\<langle>jj,kk\<rangle>)" using
      homomor_dest_mult[OF jj(1) kk(1)] by auto
    have "f-``J \<subseteq> R" using assms(3)
      using func1_1_L6A[OF surj_is_fun] by auto moreover
    have "f-``K \<subseteq> R" using assms(3)
      using func1_1_L6A[OF surj_is_fun] by auto ultimately
    have sub:"(f-``J)\<times>(f-``K) \<subseteq> R\<times>R" by auto moreover
    have "M:R\<times>R \<rightarrow> R" using origin_ring.ringAssum
      unfolding IsAring_def IsAmonoid_def
      IsAssociative_def by auto moreover
    {
      from jj have "jj\<in>f-``J" using func1_1_L15
        assms(3) jk(1) unfolding surj_def by auto moreover
      from kk have "kk\<in>f-``K" using func1_1_L15
        assms(3) jk(2) unfolding surj_def by auto ultimately
      have "\<langle>jj,kk\<rangle>\<in>(f-``J)\<times>(f-``K)" by auto
    } ultimately
    have "M`\<langle>jj,kk\<rangle> \<in> M``((f-``J)\<times>(f-``K))"
      using func_imagedef by auto
    then have "M`\<langle>jj,kk\<rangle> \<in> (f-``J) \<cdot>\<^sub>I (f-``K)"
      using preimage_ideal
      assms origin_ring.product_in_intersection(3) by blast
    then have "M`\<langle>jj,kk\<rangle> \<in> ((f-``J) \<cdot>\<^sub>I (f-``K))\<union>(f-``{\<zero>\<^sub>S})"
      by auto moreover
    have "((f-``J) \<cdot>\<^sub>I (f -`` K))\<union>(f-``{\<zero>\<^sub>S})\<subseteq>R" using 
      func1_1_L6A[OF surj_is_fun[OF assms(3)]]
      origin_ring.ideal_dest_subset[OF idealJK] by auto
    ultimately have "M`\<langle>jj,kk\<rangle> \<in> ?P"
      unfolding origin_ring.sumIdeal_def[OF idealJK 
          preimage_ideal(1)[OF target_ring.zero_ideal]]
      using origin_ring.generated_ideal_contains_set[of
          "((f-`` J) \<cdot>\<^sub>I (f-`` K)) \<union> (f-``{\<zero>\<^sub>S})"] by blast
    then have "f`(M`\<langle>jj,kk\<rangle>) \<in> f``?P"
      using func1_1_L15D[OF surj_is_fun[OF assms(3)] _
       idealSum[THEN origin_ring.ideal_dest_subset]] by auto
    moreover note t ultimately
    have "t\<in>(f``?P)"
      by auto
  }
  then have "V `` (J \<times> K) \<subseteq> f``?P" by blast
  then have "target_ring.generatedIdeal(V `` (J \<times> K)) \<subseteq> f``?P"
    using ideal target_ring.generated_ideal_small by auto
  then have "target_ring.productIdeal(J, K) \<subseteq> f``(?P)"
    unfolding target_ring.productIdeal_def[OF assms(1,2)].
  then have R:"f-``target_ring.productIdeal(J, K) \<subseteq> f-``(f``?P)"
    unfolding vimage_def by blast
  have "((f-``J) \<cdot>\<^sub>I (f-``K)) \<union> (f -`` {\<zero>\<^sub>S}) \<subseteq> R" using idealJK
    origin_ring.ideal_dest_subset func1_1_L6A[OF surj_is_fun] 
    assms(3) by blast
  then have p:"(f -`` {\<zero>\<^sub>S}) \<subseteq> ?P"
    unfolding origin_ring.sumIdeal_def[OF idealJK 
        preimage_ideal(1)[OF target_ring.zero_ideal]]
    using origin_ring.generated_ideal_contains_set 
      by blast
    moreover 
  from idealSum origin_ring.ideal_dest_subset
    have "?P \<subseteq>R" by auto
  moreover note idealSum
  ultimately have P_ideal:"?P \<in> {N\<in>\<I>. f-``{\<zero>\<^sub>S} \<subseteq> N}"
    by auto
  have P:"f``?P \<subseteq> S"
    using ideal P_ideal
    assms(3) target_ring.ideal_dest_subset by auto
  {
    fix t assume "t\<in>f-``(f``?P)"
    then have t:"f`t\<in>f``?P" "t\<in>R" using func1_1_L15
      surj_is_fun[OF assms(3)] by auto
    then obtain s where s:"f`t = f`s" "s\<in>?P" using
      func_imagedef[OF surj_is_fun[OF assms(3)]] P_ideal by auto
    from s(2) have ss:"s\<in>R" using P_ideal by auto
    from s(1) have "(f`t) \<rs>\<^sub>S (f`s) = \<zero>\<^sub>S" using
      target_ring.Ring_ZF_1_L3(7)[OF apply_type[OF surj_is_fun[OF assms(3)]
      t(2)]] by auto
    then have "f`(t\<rs>\<^sub>Rs) = \<zero>\<^sub>S" using homomor_dest_subs
      t(2) ss by auto moreover
    from t(2) ss have "t\<rs>\<^sub>Rs \<in>R" using origin_ring.Ring_ZF_1_L4(2) by auto
    ultimately have "t\<rs>\<^sub>Rs \<in> f-``{\<zero>\<^sub>S}" using func1_1_L15
      surj_is_fun[OF assms(3)] by auto
    then have "t\<rs>\<^sub>Rs \<in> ?P" using p by auto
    then have "s\<ra>\<^sub>R(t\<rs>\<^sub>Rs) \<in> ?P" using origin_ring.ideal_dest_sum
      P_ideal s(2) by auto
    then have "t\<in>?P" using origin_ring.Ring_ZF_2_L1A(5)
      ss t(2) by auto
  }
  then have "f-``(f``?P) \<subseteq> ?P" by auto
  with R show "f-``target_ring.productIdeal(J, K) \<subseteq> ?P" by auto
  {
    fix t assume as:"t\<in>M``((f-``J)\<times>(f-``K))"
    moreover have "(f-``J)\<times>(f-``K) \<subseteq> R\<times>R" using func1_1_L15[OF surj_is_fun[OF assms(3)]] by auto
    ultimately obtain tj tk where jk:"t=tj\<cdot>\<^sub>Rtk" "tj\<in>f-``J" "tk\<in>f-``K"
      using func_imagedef[of M "R\<times>R" R] origin_ring.ringAssum unfolding IsAring_def IsAmonoid_def
      IsAssociative_def by auto
    from as have tR:"t\<in>R" using func1_1_L6(2)[of M "R\<times>R" R]
      origin_ring.ringAssum unfolding IsAring_def IsAmonoid_def IsAssociative_def
      by auto
    from jk(2) have j:"tj\<in>R" "f`tj \<in>J" using func1_1_L15 surj_is_fun[OF
      assms(3)] by auto
    from jk(3) have k:"tk\<in>R" "f`tk \<in>K" using func1_1_L15 surj_is_fun[OF
      assms(3)] by auto
    from jk(1) have "f`t = f`(tj\<cdot>\<^sub>Rtk)" by auto
    then have ft:"f`t = ((f`tj)\<cdot>\<^sub>S(f`tk))" using homomor_dest_mult
      using j(1) k(1) by auto
    from j(2) k(2) have "\<langle>f`tj,f`tk\<rangle>\<in>J\<times>K" by auto
    moreover have "V:S\<times>S\<rightarrow>S" using target_ring.ringAssum unfolding IsAring_def
      IsAmonoid_def IsAssociative_def by auto
    moreover have "J\<times>K \<subseteq> S\<times>S" using assms using target_ring.ideal_dest_subset
      by auto
    ultimately have "V`\<langle>f ` tj, f ` tk\<rangle> \<in>V``(J\<times>K)"
      using func_imagedef[of V "S\<times>S" S "J\<times>K"] by force
    with ft have "f`t\<in>V``(J\<times>K)" by auto
    then have "f`t\<in>target_ring.productIdeal(J, K)"
      using target_ring.product_in_intersection(3) assms
      by blast
    then have "t\<in>f-``target_ring.productIdeal(J, K)"
      using func1_1_L15 surj_is_fun[OF assms(3)] tR
      by auto
  }
  then have "M `` (f -`` J \<times> f -`` K) \<subseteq> f -`` target_ring.productIdeal(J, K)" by auto
  moreover have id:"(f -``target_ring.productIdeal(J, K)) \<triangleleft>R\<^sub>o"
    apply (rule preimage_ideal) apply (rule target_ring.product_in_intersection(2))
    using assms(1,2) .
  ultimately have "(f -`` J) \<cdot>\<^sub>I (f -`` K) \<subseteq> f -``target_ring.productIdeal(J, K)"
    using origin_ring.generated_ideal_small origin_ring.productIdeal_def[OF ideals]
    by auto
  moreover have "\<zero>\<^sub>S \<in> target_ring.productIdeal(J, K)"
    using target_ring.product_in_intersection(2) assms(1,2)
    target_ring.ideal_dest_zero by auto
  then have "(f -`` {\<zero>\<^sub>S}) \<subseteq> f -``target_ring.productIdeal(J, K)"
     by auto
  ultimately have "((f -`` J) \<cdot>\<^sub>I (f -`` K))\<union>(f -`` {\<zero>\<^sub>S}) \<subseteq> f -``target_ring.productIdeal(J, K)"
    by auto
  then show "((f -`` J) \<cdot>\<^sub>I (f -`` K))+\<^sub>I(f -`` {\<zero>\<^sub>S}) \<subseteq> f -``target_ring.productIdeal(J, K)"
    using origin_ring.generated_ideal_small id 
      origin_ring.sumIdeal_def[OF idealJK preimage_ideal(1)[OF target_ring.zero_ideal]]
    by auto
qed

corollary (in ring_homo) prime_ideal_quot_2:
  assumes "J\<triangleleft>R\<^sub>t" "K\<triangleleft>R\<^sub>t" "f\<in>surj(R,S)"
  shows "target_ring.productIdeal(J, K) = f``origin_ring.productIdeal((f-`` J), (f-`` K))"
proof-
  have "f-`` target_ring.productIdeal(J, K) =
 ((f-`` J) \<cdot>\<^sub>I (f-`` K)) +\<^sub>I (ker)" using prime_ideal_quot assms beta by auto
  then have "f``(f-`` target_ring.productIdeal(J, K))
  = f``(((f -`` J) \<cdot>\<^sub>I (f -`` K)) +\<^sub>I (ker))"
    by auto
  moreover have "target_ring.productIdeal(J, K)\<triangleleft>R\<^sub>t"
    using target_ring.product_in_intersection(2)
    assms(1,2) by auto
  then have "target_ring.productIdeal(J, K) \<subseteq> S" using
    target_ring.ideal_dest_subset by auto
  ultimately have A:"target_ring.productIdeal(J, K) = 
    f``(((f-`` J) \<cdot>\<^sub>I (f-`` K)) +\<^sub>I(f-``{\<zero>\<^sub>S}))"
    using surj_image_vimage assms(3) 
    by auto
  have idealJK:"((f-``J) \<cdot>\<^sub>I (f-``K)) \<triangleleft>R"
    using origin_ring.product_in_intersection(2) 
    preimage_ideal assms(1,2) by auto
  with A show "target_ring.productIdeal(J, K) = 
    f``((f-`` J) \<cdot>\<^sub>I (f-`` K))" using kernel_empty_image(1)
    preimage_ideal[OF target_ring.zero_ideal] by auto
qed

lemma (in ring_homo) preimage_ideal_prime:
  assumes "J\<triangleleft>\<^sub>pR\<^sub>o" "ker \<subseteq> J" "f\<in>surj(R,S)"
  shows "(f``J)\<triangleleft>\<^sub>pR\<^sub>t"
proof-
  from assms(1,3) have "(f``J)\<triangleleft>R\<^sub>t" using image_ideal_surj
    unfolding origin_ring.primeIdeal_def by auto moreover
  from assms(1) have JT:"J \<subseteq> R" "J \<noteq> R" 
    unfolding origin_ring.primeIdeal_def 
    using origin_ring.ideal_dest_subset by auto
  {
    assume full:"f``J = S"
    from JT obtain t where t:"t\<in>R-J" by auto
    with assms(3) have "f`t\<in>S" 
      using apply_type[OF surj_is_fun] by auto
    with full have "f`t\<in>f``J" by auto
    with assms(3) JT(1) obtain j where j:"j\<in>J" "f`t= f`j"
      using func_imagedef[OF surj_is_fun] by auto
    from j(1) have jt:"j\<in>R" using JT(1) by auto
    then have fj:"f`j\<in>S" using apply_type assms(3)
      unfolding surj_def by auto
    from j(2) have "(f`t)\<rs>\<^sub>S(f`j) = \<zero>\<^sub>S" using
      target_ring.Ring_ZF_1_L3(7) fj by auto
    then have "f`(t\<rs>\<^sub>Rj) =\<zero>\<^sub>S" using homomor_dest_subs
      t jt by auto moreover
    have "t\<rs>\<^sub>Rj \<in>R" using origin_ring.Ring_ZF_1_L4(2)
      t jt by auto
    ultimately have "t\<rs>\<^sub>Rj\<in>f-``{\<zero>\<^sub>S}" using func1_1_L15[OF surj_is_fun]
      assms(3) by auto
    with assms(2) have tjJ:"t\<rs>\<^sub>Rj\<in>J" by auto
    with j(1) have "j\<ra>\<^sub>R(t\<rs>\<^sub>Rj) \<in>J" using assms(1)
      unfolding origin_ring.primeIdeal_def
      using origin_ring.ideal_dest_sum by auto
    then have False using origin_ring.Ring_ZF_2_L1A(5)
      using jt t by auto
  }
  then have "f``J \<noteq> S" by auto moreover
  {
    fix I K assume as:"I\<in>target_ring.ideals" "K\<in>target_ring.ideals"
           "target_ring.productIdeal(I, K) \<subseteq> f``J"
    then have "f `` ((f -`` I) \<cdot>\<^sub>I (f -`` K)) \<subseteq> f``J" 
      using prime_ideal_quot_2 assms(3) by auto
    then have "f-``(f `` ((f -`` I) \<cdot>\<^sub>I (f -`` K))) \<subseteq> f-``(f``J)"
      by blast
    moreover have "((f -`` I) \<cdot>\<^sub>I (f -`` K)) \<triangleleft>R"
      using origin_ring.product_in_intersection(2)[OF preimage_ideal(1)
 preimage_ideal(1)]
      as(1,2) by auto
    then have "((f -`` I) \<cdot>\<^sub>I (f -`` K)) \<subseteq> R" using origin_ring.ideal_dest_subset
      by auto
    ultimately have "(f -`` I) \<cdot>\<^sub>I (f -`` K) \<subseteq> f-``(f``J)" 
      using func1_1_L9[OF fun, of "(f -`` I) \<cdot>\<^sub>I (f -`` K)"] by auto
    moreover
    have "J \<subseteq> f-``(f``J)" using func1_1_L9 fun assms(1)
      origin_ring.ideal_dest_subset unfolding origin_ring.primeIdeal_def
      by auto moreover
    {
      fix t assume "t\<in>f-``(f``J)"
      then have t:"f`t\<in>f``J" "t\<in>R" using func1_1_L15 fun by auto
      from t(1) obtain s where s:"f`t = f`s" "s\<in>J"
        using func_imagedef fun assms(1)
        origin_ring.ideal_dest_subset unfolding origin_ring.primeIdeal_def
        by auto
      from s(2) assms(1) have ss:"s\<in>R" unfolding origin_ring.primeIdeal_def
        using origin_ring.ideal_dest_subset by auto
      from s(1) have "f`t \<rs>\<^sub>S (f`s) = \<zero>\<^sub>S" using target_ring.Ring_ZF_1_L3(7)[
        OF apply_type[OF fun t(2)]] by auto
      then have "f`(t\<rs>\<^sub>Rs) = \<zero>\<^sub>S" using homomor_dest_subs
        t(2) ss by auto
      moreover have "t\<rs>\<^sub>Rs \<in>R" using ss t(2)
        origin_ring.Ring_ZF_1_L4(2) by auto
      ultimately have "t\<rs>\<^sub>Rs \<in> f-``{\<zero>\<^sub>S}" using func1_1_L15
        fun by auto
      with assms(2) have "t\<rs>\<^sub>Rs \<in> J" by auto
      with s(2) have "s\<ra>\<^sub>R(t\<rs>\<^sub>Rs)\<in>J"
        using assms(1) origin_ring.ideal_dest_sum
        unfolding origin_ring.primeIdeal_def by auto
      then have "t: J" using origin_ring.Ring_ZF_2_L1A(5)
        ss t(2) by auto
    }
    then have "f-``(f``J) \<subseteq> J" by auto
    ultimately have "(f -`` I) \<cdot>\<^sub>I (f -`` K) \<subseteq> J" by auto
    moreover have "(f -`` I) \<in>\<I>" "(f -`` K) \<in>\<I>"
      using as(1,2) preimage_ideal
        origin_ring.ideal_dest_subset by auto
    ultimately have "(f -`` I) \<subseteq> J \<or> (f -`` K) \<subseteq> J"
      using assms(1) unfolding origin_ring.primeIdeal_def by auto
    then have "f``(f -`` I) \<subseteq> f``J \<or> f``(f -`` K) \<subseteq> f``J"
      by auto
    with assms(3) have "I \<subseteq> f``J \<or> K \<subseteq> f``J"
      using surj_image_vimage as(1,2) by auto
  }
  ultimately show ?thesis unfolding target_ring.primeIdeal_def by auto
qed

text\<open>The ideals of the quotient ring are in bijection
with the ideals of the original ring that contain the ideal
by which we made the quotient.\<close>

theorem (in ring_homo) ideal_quot_bijection:
  assumes "f\<in>surj(R,S)"
  defines "idealFun \<equiv> \<lambda>J\<in>target_ring.ideals. f-``J"
  shows "idealFun \<in> bij(target_ring.ideals,{K\<in>\<I>. ker \<subseteq> K})"
  unfolding bij_def inj_def surj_def
proof(safe)
  have "idealFun \<in> target_ring.ideals \<rightarrow> {f-``J. J\<in>target_ring.ideals}"
    unfolding idealFun_def
    using lam_funtype by auto moreover
  {
    fix t assume "t\<in>{f-``J. J\<in>target_ring.ideals}"
    then obtain K where "K\<in>target_ring.ideals" "f-``K = t" by auto
    then have "ker \<subseteq> t" "t\<triangleleft>R" "t \<subseteq> R" using preimage_ideal[of K]
      using func1_1_L3[OF surj_is_fun[OF assms(1)], of K]
      by auto
    then have "t\<in>{K\<in>\<I>. ker \<subseteq> K}" by auto
  }
  then have "{f-``J. J\<in>target_ring.ideals} \<subseteq> {K\<in>\<I>. ker \<subseteq> K}" by blast
  ultimately show "idealFun \<in> target_ring.ideals \<rightarrow> {K\<in>\<I>. ker \<subseteq> K}"
    using func1_1_L1B by auto
  then show "idealFun \<in> target_ring.ideals \<rightarrow> {K\<in>\<I>. ker \<subseteq> K}".
  {
    fix w x assume as:"w\<triangleleft>R\<^sub>t" "x\<triangleleft>R\<^sub>t" "w\<subseteq>S" "x\<subseteq>S" "idealFun ` w = idealFun ` x"
    then have "f-``w = f-``x" unfolding idealFun_def
      using beta by auto
    then have "f``(f-``w) = f``(f-``x)" by auto
    then show "w = x" using surj_image_vimage assms(1) as
      by auto
  }
  {
    fix y assume y:"y\<triangleleft>R" "y\<subseteq>R" "ker \<subseteq> y"
    from y(2) have "y \<subseteq> f-``(f``y)" using func1_1_L9[OF surj_is_fun] 
        assms(1) by auto
    moreover
    {
      fix t assume "t\<in>f-``(f``y)"
      then have t:"f`t\<in>f``y" "t\<in>R" using func1_1_L15[OF surj_is_fun] 
            assms(1) by auto
      from t(1) y(2) obtain s where s:"s\<in>y" "f`t = f`s" 
        using func_imagedef[of f R S y, OF surj_is_fun] assms(1) 
        by auto
      from s(1) have "s\<in>R" using y(2) by auto
      with t(2) have E:"f`t : S" "f`s: S" using apply_type[of f R "\<lambda>u. S", OF surj_is_fun]
        assms(1) by auto
      from E(1) s(2) have "(f`t)\<rs>\<^sub>S(f`s) = \<zero>\<^sub>S"
        using target_ring.Ring_ZF_1_L3(7) by auto
      then have "f`(t\<rs>\<^sub>Rs) = \<zero>\<^sub>S" using homomor_dest_subs
        t(2) `s:R` by auto
      moreover from \<open>s\<in>R\<close> have "t\<rs>\<^sub>Rs \<in>R" 
        using origin_ring.Ring_ZF_1_L4(2) t(2) by auto
      ultimately have "t\<rs>\<^sub>Rs \<in> f-``{\<zero>\<^sub>S}"
        using func1_1_L15[OF surj_is_fun] assms(1) by auto
      with y(3) have "t\<rs>\<^sub>Rs \<in> y" by auto
      with s(1) have "s\<ra>\<^sub>R(t\<rs>\<^sub>Rs) \<in> y" using 
        origin_ring.ideal_dest_sum y(1) by auto
      then have "t\<in>y" using origin_ring.Ring_ZF_2_L1A(5)
        using `s\<in>R` t(2) by auto
    }
    ultimately have "f-``(f``y) = y" by blast moreover
    have "f``y \<subseteq> S" using func1_1_L6(2)[of f R S] assms(1)
      unfolding surj_def by auto moreover
    have "(f``y)\<triangleleft>R\<^sub>t" using image_ideal_surj
      assms(1) y(1) by auto
    ultimately show "\<exists>x\<in>target_ring.ideals. idealFun ` x = y"
      unfolding idealFun_def
      by auto
  }
qed

theorem (in ring_homo) quot_converse:
  defines "idealFun \<equiv> \<lambda>J\<in>target_ring.ideals. f-``J"
  assumes "J\<triangleleft>R" "ker\<subseteq>J" "f:surj(R,S)"
  shows "converse(idealFun)`J = f``J"
proof-
  let ?g="\<lambda>J\<in>{K\<in>\<I>. ker\<subseteq>K}. f``J"
  have "?g\<in>{K\<in>\<I>. ker\<subseteq>K} \<rightarrow> {f``J. J\<in>{K\<in>\<I>. ker\<subseteq>K}}"
    using lam_funtype by auto moreover
  have "{f``J. J\<in>{K\<in>\<I>. ker\<subseteq>K}} \<subseteq> target_ring.ideals"
    using image_ideal_surj target_ring.ideal_dest_subset
    assms(4) by auto
  ultimately have "?g\<in>{K\<in>\<I>. ker\<subseteq>K} \<rightarrow> target_ring.ideals" 
    using func1_1_L1B by auto
  have "converse(idealFun)\<in>bij({K\<in>\<I>. ker\<subseteq>K}, target_ring.ideals)" 
    using bij_converse_bij ideal_quot_bijection assms(4)
    unfolding idealFun_def by auto
  then have confun:"converse(idealFun):{K\<in>\<I>. ker\<subseteq>K} \<rightarrow> target_ring.ideals"
    unfolding bij_def inj_def by auto
  moreover have J:"J\<in>{K\<in>\<I>. ker\<subseteq>K}" using assms(2,3) 
    origin_ring.ideal_dest_subset by auto
  ultimately have ideal:"converse(idealFun)`J \<in> target_ring.ideals"
    using apply_type[of "converse(idealFun)" "{K\<in>\<I>. ker\<subseteq>K}" "\<lambda>q. target_ring.ideals" J]
    by auto
  then have "?g`(idealFun`(converse(idealFun)`J)) = ?g`(f-``(converse(idealFun)`J))"
    using beta unfolding idealFun_def
    by auto moreover
  from preimage_ideal ideal
    have "(f-``(converse(idealFun)`J))\<triangleleft>R" "ker \<subseteq> (f-``(converse(idealFun)`J))" by auto
  then have "?g`(f-``(converse(idealFun)`J)) = f``(f-``(converse(idealFun)`J))"
    using beta origin_ring.ideal_dest_subset by auto
  ultimately have "?g`(idealFun`(converse(idealFun)`J)) = f``(f-``(converse(idealFun)`J))"
    by auto
  then have "?g`(idealFun`(converse(idealFun)`J)) = converse(idealFun)`J"
    using surj_image_vimage assms(4) ideal by auto
  then have "?g`J = converse(idealFun)`J"
    using right_inverse_lemma[of idealFun target_ring.ideals
        "{K \<in> \<I> . ker \<subseteq> K}" "{K \<in> \<I> . ker \<subseteq> K}" J ] J
    confun bij_is_fun[OF ideal_quot_bijection] assms(4)
    unfolding idealFun_def by auto
  then show ?thesis using beta J by auto
qed
  
text\<open>Since the map is surjective, this bijection
restricts to prime ideals on both sides.\<close>

corollary (in ring_homo) prime_ideal_quot_3:
  assumes "K\<triangleleft>R\<^sub>t" "f:surj(R,S)"
  shows "K\<triangleleft>\<^sub>pR\<^sub>t \<longleftrightarrow> ((f-``K)\<triangleleft>\<^sub>pR\<^sub>o)"
proof
  {
    assume as:"K\<triangleleft>\<^sub>pR\<^sub>t"
    then have "(f-``K)\<triangleleft>\<^sub>pR\<^sub>o" using preimage_prime_ideal_surj
      assms(2) by auto
    then show "(f-``K)\<triangleleft>\<^sub>pR\<^sub>o"
      using beta[of K target_ring.ideals]
      using target_ring.ideal_dest_subset[of K] as
      unfolding target_ring.primeIdeal_def by auto
  } moreover
  {
    assume as:"(f-``K)\<triangleleft>\<^sub>pR\<^sub>o"
    from assms(1) have "K\<triangleleft>R\<^sub>t". moreover
    {
      assume "K=S"
      then have "f-``K = f-``S" by auto
      then have "f-``K = R" using func1_1_L4
        assms(2) unfolding surj_def by auto
      with as have False unfolding origin_ring.primeIdeal_def by auto
    }
    then have "K\<noteq>S" by auto moreover
    {
      fix J P assume jp:"J\<in>target_ring.ideals"
        "P\<in>target_ring.ideals"
        "target_ring.productIdeal(J, P) \<subseteq> K"
      have sub:"((f -`` J) \<cdot>\<^sub>I (f -`` P)) \<union> ker \<subseteq> R"
        using origin_ring.ideal_dest_subset
        origin_ring.product_in_intersection(2) 
        preimage_ideal target_ring.zero_ideal
        jp by auto
      from jp(3) have "f -``target_ring.productIdeal(J, P) \<subseteq> f -``K"
        by auto
      with jp(1,2) have A:"((f -`` J) \<cdot>\<^sub>I (f -`` P)) +\<^sub>I (ker) \<subseteq> f -``K" 
        using prime_ideal_quot assms(2)
        by auto moreover
      have j:"J\<triangleleft>R\<^sub>t" and p:"P\<triangleleft>R\<^sub>t" using jp(1,2) by auto
      then have "(f -`` J) \<cdot>\<^sub>I (f -`` P) \<union> ker \<subseteq> R"
        using origin_ring.ideal_dest_subset[OF origin_ring.product_in_intersection(2)
            [OF preimage_ideal(1) preimage_ideal(1)]]
            origin_ring.ideal_dest_subset[OF preimage_ideal(1)[OF target_ring.zero_ideal]]
        by auto
      with A have "((f -`` J) \<cdot>\<^sub>I (f -`` P)) \<subseteq> f -``K" 
        unfolding origin_ring.sumIdeal_def[OF origin_ring.product_in_intersection(2)
            [OF preimage_ideal(1)[OF j] preimage_ideal(1)[OF p]]   
            preimage_ideal(1)[OF target_ring.zero_ideal]] using
            origin_ring.generated_ideal_contains_set[of "(f -`` J) \<cdot>\<^sub>I (f -`` P) \<union> ker"]
            by auto
      moreover have "f -`` J \<in>\<I>" "f -`` P \<in>\<I>"
        using preimage_ideal
        origin_ring.ideal_dest_subset jp(1,2) by auto
      ultimately have "f -`` J \<subseteq> f -`` K \<or> f -`` P \<subseteq> f -`` K"
        using as unfolding origin_ring.primeIdeal_def by auto
      then have "f``(f -`` J) \<subseteq> f``(f -`` K) \<or> f``(f -`` P) \<subseteq> f``(f -`` K)"
        by blast
      then have "J \<subseteq> K \<or> P \<subseteq> K" using assms(2)
        surj_image_vimage jp(1,2) assms target_ring.ideal_dest_subset
        by auto
    }
    ultimately show "K\<triangleleft>\<^sub>pR\<^sub>t"
      unfolding target_ring.primeIdeal_def by auto
  }
qed

corollary (in ring_homo) bij_prime_ideals:
  defines "idealFun \<equiv> \<lambda>J\<in>target_ring.ideals. f-``J"
  assumes "f:surj(R,S)"
  shows "restrict(idealFun,{J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t})\<in>bij({J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t}, {J\<in>Pow(R). ker\<subseteq>J \<and> (J\<triangleleft>\<^sub>pR)})"
proof-
  have "{J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t} \<subseteq> target_ring.ideals"
    unfolding target_ring.primeIdeal_def by auto
  then have rest_bij:"restrict(idealFun,{J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t})\<in>bij({J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t}, idealFun``{J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t})"
    using restrict_bij assms(2)
    ideal_quot_bijection unfolding bij_def
    idealFun_def by auto
  {
    fix t assume t:"t\<in>idealFun``{J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t}"
    have sub:"{J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t} \<subseteq> target_ring.ideals"
      unfolding target_ring.primeIdeal_def by auto
    from t obtain q where q:"q\<in>{J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t}" "t=idealFun`q"
      using assms(2) func_imagedef[OF bij_is_fun[OF ideal_quot_bijection] sub]
      unfolding idealFun_def by auto
    note q(1) moreover
    then have "q\<in>target_ring.ideals" unfolding
      target_ring.primeIdeal_def by auto moreover
    with q(2) have "t = f-``q" "ker\<subseteq>t" "t\<triangleleft>R" unfolding idealFun_def 
      using beta
      apply_type[OF ideal_quot_bijection[THEN bij_is_fun], of q] assms(2) by auto
    ultimately have "t\<triangleleft>R" "t\<triangleleft>\<^sub>pR" "ker\<subseteq>t" using assms(2) prime_ideal_quot_3
      by auto
  }
  then have "idealFun `` Collect(Pow(S), prime_ideal_target) \<subseteq> {t\<in>Pow(R). ker\<subseteq>t \<and> (t\<triangleleft>\<^sub>pR)}"
    using origin_ring.ideal_dest_subset by blast moreover
  {
    fix t assume "t\<in>{t\<in>Pow(R). ker\<subseteq>t \<and> (t\<triangleleft>\<^sub>pR)}"
    then have t:"t\<in>Pow(R)" "ker\<subseteq>t" "t\<triangleleft>\<^sub>pR" by auto
    then have tSet:"t\<in>{t\<in>\<I>. ker \<subseteq> t}" unfolding origin_ring.primeIdeal_def by auto
    have "converse(idealFun)\<in>bij({t\<in>\<I>. ker \<subseteq> t}, target_ring.ideals)"
      using ideal_quot_bijection[OF assms(2)] bij_converse_bij unfolding idealFun_def
      by auto
    with tSet have cont:"converse(idealFun)`t \<in> target_ring.ideals"
      using apply_type[OF bij_is_fun] by blast moreover
    from tSet have eq:"idealFun`(converse(idealFun)`t) = t"
      using ideal_quot_bijection assms(2) unfolding idealFun_def
      using right_inverse_bij by blast
    ultimately have "f-``(converse(idealFun)`t) = t"
      using beta unfolding idealFun_def by auto
    with t(3) have "(converse(idealFun)`t) \<triangleleft>\<^sub>pR\<^sub>t"
      using prime_ideal_quot_3 cont assms(2) by auto
    then have "(converse(idealFun)`t) \<triangleleft>\<^sub>pR\<^sub>t" "(converse(idealFun)`t) \<subseteq> S"
      unfolding target_ring.primeIdeal_def
      using target_ring.ideal_dest_subset by auto
    then have elem:"converse(idealFun)`t\<in>{q\<in>Pow(S). q\<triangleleft>\<^sub>pR\<^sub>t}"
      by auto
    have sub:"{q\<in>Pow(S). q\<triangleleft>\<^sub>pR\<^sub>t} \<subseteq> target_ring.ideals"
      unfolding target_ring.primeIdeal_def by auto
    have "t\<in>idealFun``Collect(Pow(S), prime_ideal_target)"
      using assms(2) func_imagedef[OF ideal_quot_bijection[THEN bij_is_fun] sub] unfolding idealFun_def
      using eq elem unfolding idealFun_def by auto
  }
  then have "{t\<in>Pow(R). ker\<subseteq>t \<and> (t\<triangleleft>\<^sub>pR)} \<subseteq> idealFun``Collect(Pow(S), prime_ideal_target)" by auto
  ultimately
  have "{t\<in>Pow(R). ker\<subseteq>t \<and> (t\<triangleleft>\<^sub>pR)} = idealFun``Collect(Pow(S), prime_ideal_target)"
    by auto
  with rest_bij show ?thesis by auto
qed
    
end