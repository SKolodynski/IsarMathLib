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

text\<open>This section studies the ideals of quotient rings,
  and defines ring homomorphisms.\<close>

subsection\<open>Ring homomorphisms\<close>

text\<open>Morphisms in general are structure preserving functions between algebraic
  structures. In this section we study ring homomorphisms.\<close>

text\<open>A ring homomorphism is a function between rings which has the
  morphism property with respect to both addition and multiplication operation, 
  and maps one (the neutral element of multiplication) in the first ring to one
  in the second ring. \<close>

definition
  "ringHomomor(f,R,A,M,S,U,V) \<equiv> f:R\<rightarrow>S \<and> IsMorphism(R,A,U,f) \<and> IsMorphism(R,M,V,f) 
  \<and> f`(TheNeutralElement(R,M)) = TheNeutralElement(S,V)"

text\<open>The next locale defines notation which we will use in this theory.
  We assume that we have two rings, one (which we will call the origin ring) 
  defined by the triple $(R,A,M)$  
  and the second one (which we will call the target ring) by the triple $(S,U,V)$, 
  and a homomorphism $f:R\rightarrow S$. \<close>

locale ring_homo =
  fixes R A M S U V f
  assumes origin: "IsAring(R,A,M)" 
    and target: "IsAring(S,U,V)"
    and homomorphism: "ringHomomor(f,R,A,M,S,U,V)"

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

text\<open>We will write \<open>I\<triangleleft>R\<^sub>o\<close> to denote that $I$ is an ideal
  of the ring $R$. Note that in this notation the \<open>R\<^sub>o\<close> part by itself has no meaning,
  only the whole \<open>\<triangleleft>R\<^sub>o\<close> serves as postfix operator. \<close>

abbreviation (in ring_homo) ideal_origin ("_\<triangleleft>R\<^sub>o")
  where "I\<triangleleft>R\<^sub>o \<equiv> ring0.Ideal(R,A,M,I)"

text\<open>\<open>I\<triangleleft>R\<^sub>t\<close> means that $I$ is an ideal of $S$.\<close>

abbreviation (in ring_homo) ideal_target ("_\<triangleleft>R\<^sub>t")
  where "I\<triangleleft>R\<^sub>t \<equiv> ring0.Ideal(S,U,V,I)"

text\<open> \<open>I\<triangleleft>\<^sub>pR\<^sub>o\<close> means that $I$ is a prime ideal of $R$.\<close>

abbreviation (in ring_homo) prime_ideal_origin ("_\<triangleleft>\<^sub>pR\<^sub>o")
  where "I\<triangleleft>\<^sub>pR\<^sub>o \<equiv> ring0.primeIdeal(R,A,M,I)"

text\<open>We will write \<open>I\<triangleleft>\<^sub>pR\<^sub>t\<close> to denote that $I$ is a prime ideal of the ring $S$. \<close>

abbreviation (in ring_homo) prime_ideal_target ("_\<triangleleft>\<^sub>pR\<^sub>t")
  where "I\<triangleleft>\<^sub>pR\<^sub>t \<equiv> ring0.primeIdeal(S,U,V,I)"

text\<open> \<open>ker\<close> denotes the kernel of $f$ (which is assumed to be a homomorphism
  between $R$ and $S$.\<close>

abbreviation (in ring_homo) kernel ("ker" 90) where
  "ker \<equiv> f-``{\<zero>\<^sub>S}"

text\<open>The theorems proven in the \<open>ring0\<close> context are valid in the \<open>ring_homo\<close> 
  context when applied to the ring $R$.\<close>

sublocale ring_homo < origin_ring:ring0
  using origin unfolding ring0_def by auto

text\<open>The theorems proven in the \<open>ring0\<close> context are valid in the \<open>ring_homo\<close> 
  context when applied to the ring $S$.\<close>

sublocale ring_homo < target_ring:ring0 S U V ringas ringminuss 
  ringsubs ringms ringzeros ringones ringtwos ringsqs
  using target unfolding ring0_def by auto

text\<open>A ring homomorphism is a homomorphism both with respect to
  addition and multiplication.\<close>

lemma ringHomHom: assumes "ringHomomor(f,R,A,M,S,U,V)"
  shows "Homomor(f,R,A,S,U)" and "Homomor(f,R,M,S,V)"
  using assms unfolding ringHomomor_def Homomor_def 
  by simp_all

text\<open>Since in the \<open>ring_homo\<close> locale $f$ is a ring homomorphism it implies
  that $f$ is a function from $R$ to $S$. \<close>

lemma (in ring_homo) f_is_fun: shows "f:R\<rightarrow>S"
  using homomorphism unfolding ringHomomor_def by simp

text\<open>In the \<open>ring_homo\<close> context $A$ is the addition in the first (source) ring
   $M$ is the multiplication there and $U,V$ are the addition and multiplication resp.
  in the second (target) ring. The next lemma states the all these are binary
  operations, a trivial, but frequently used fact.\<close>

lemma (in ring_homo) AMUV_are_ops: 
  shows "A:R\<times>R\<rightarrow>R" "M:R\<times>R\<rightarrow>R" "U:S\<times>S\<rightarrow>S" "V:S\<times>S\<rightarrow>S"
  using origin target 
  unfolding IsAring_def IsAgroup_def IsAmonoid_def IsAssociative_def
  by auto

text\<open>The kernel is a subset of $R$ on which the value of $f$ is zero 
  (of the target ring)\<close>

lemma (in ring_homo) kernel_def_alt: shows "ker = {r\<in>R. f`(r) = \<zero>\<^sub>S}"
  using f_is_fun func1_1_L14 by simp  

text\<open> the homomorphism $f$ maps each element of the kernel 
  to zero of the target ring. \<close>

lemma (in ring_homo) image_kernel:
  assumes "x\<in>ker"
  shows "f`(x) = \<zero>\<^sub>S"
  using assms func1_1_L15 f_is_fun by simp

text\<open> As a ring homomorphism $f$ preserves multiplication.\<close>

lemma (in ring_homo) homomor_dest_mult:
  assumes "x\<in>R" "y\<in>R"
  shows "f`(x\<cdot>\<^sub>Ry) = (f`(x))\<cdot>\<^sub>S(f`(y))"
  using assms origin target homomorphism 
  unfolding ringHomomor_def IsMorphism_def by simp

text\<open> As a ring homomorphism $f$ preserves addition. \<close>

lemma (in ring_homo) homomor_dest_add:
  assumes "x\<in>R" "y\<in>R"
  shows "f`(x\<ra>\<^sub>Ry) = (f`(x))\<ra>\<^sub>S(f`(y))"
  using homomor_eq origin target homomorphism assms
  unfolding IsAring_def ringHomomor_def IsMorphism_def
  by simp

text\<open>For $x\in R$ the value of $f$ is in $S$.\<close>

lemma (in ring_homo) homomor_val: assumes "x\<in>R"
  shows "f`(x) \<in> S" 
  using homomorphism assms apply_funtype unfolding ringHomomor_def 
  by blast

text\<open>A ring homomorphism preserves taking negative of an element.\<close>

lemma (in ring_homo) homomor_dest_minus:
  assumes "x\<in>R"
  shows "f`(\<rm>\<^sub>Rx) = \<rm>\<^sub>S(f`(x))"
  using origin target homomorphism assms ringHomHom image_inv
  unfolding IsAring_def by auto

text\<open>A ring homomorphism preserves substraction.\<close> 

lemma (in ring_homo) homomor_dest_subs:
  assumes "x\<in>R" "y\<in>R"
  shows "f`(x\<rs>\<^sub>Ry) = (f`(x))\<rs>\<^sub>S(f`(y))"
  using assms homomor_dest_add homomor_dest_minus
  using origin_ring.Ring_ZF_1_L3(1) by auto

text\<open>A ring homomorphism maps zero to zero.\<close>

lemma (in ring_homo) homomor_dest_zero:
  shows "f`(\<zero>\<^sub>R) = \<zero>\<^sub>S"
  using origin target homomorphism ringHomHom(1) image_neutral
  unfolding IsAring_def by auto

text\<open>The kernel of a homomorphism is never empty.\<close>

lemma (in ring_homo) kernel_non_empty: 
  shows "\<zero>\<^sub>R \<in>ker" and "ker\<noteq>0"
  using homomor_dest_zero origin_ring.Ring_ZF_1_L2(1)
    func1_1_L15 f_is_fun by auto

text\<open>The image of the kernel by $f$ is the singleton $\{ 0_R\}$.\<close>

corollary (in ring_homo) image_kernel_2: shows "f``(ker) = {\<zero>\<^sub>S}"
proof -
  have "f:R\<rightarrow>S" "ker\<subseteq>R" "ker\<noteq>0" "\<forall>x\<in>ker. f`(x) = \<zero>\<^sub>S"
    using f_is_fun kernel_def_alt kernel_non_empty by auto
  then show  "f``(ker) = {\<zero>\<^sub>S}" using image_constant_singleton
    by simp
qed

text\<open>The inverse image of an ideal (in the target ring) is
  a normal subgroup of the addition group and an ideal in the origin ring. 
  The kernel of the homomorphism
  is a subset of the inverse of image of every ideal. \<close>

lemma (in ring_homo) preimage_ideal:
  assumes "J\<triangleleft>R\<^sub>t"
  shows
    "IsAnormalSubgroup(R,A,f-``(J))"
    "(f-``(J))\<triangleleft>R\<^sub>o" "ker \<subseteq> f-``(J)"
proof -
  from origin target homomorphism assms 
    show "IsAnormalSubgroup(R,A,f-``(J))"
      using ringHomHom(1) preimage_normal_subgroup
        target_ring.ideal_normal_add_subgroup
      unfolding IsAring_def by blast
  then have "IsAsubgroup(f-``(J),A)" unfolding IsAnormalSubgroup_def
    by auto 
  moreover
  { fix x y assume "x \<in> f-``(J)" "y\<in>R"
    from homomorphism have "f:R\<rightarrow>S"
      unfolding ringHomomor_def by simp
    with \<open>x \<in> f-``(J)\<close> have "x\<in>R" and "f`(x) \<in> J"
      using func1_1_L15 unfolding ringHomomor_def
      by simp_all
    with assms \<open>y\<in>R\<close> \<open>f:R\<rightarrow>S\<close> have 
      "V`\<langle>f`(x),f`(y)\<rangle> \<in> J" and "V`\<langle>f`(y),f`(x)\<rangle>\<in>J"
      using apply_funtype target_ring.ideal_dest_mult by simp_all
    with \<open>x\<in>R\<close> \<open>y\<in>R\<close> have "f`(M`\<langle>x,y\<rangle>) \<in> J" and "f`(M`\<langle>y,x\<rangle>) \<in> J"
      using homomor_dest_mult by auto
    with \<open>x\<in>R\<close> \<open>y\<in>R\<close> \<open>f:R\<rightarrow>S\<close> have 
      "M`\<langle>x,y\<rangle> \<in> f-``(J)" and "M`\<langle>y,x\<rangle> \<in> f-``(J)"
      using origin_ring.Ring_ZF_1_L4(3) func1_1_L15 by auto 
  }
  ultimately show "(f-``(J))\<triangleleft>R\<^sub>o" using origin_ring.Ideal_def 
    by auto
  from assms show "ker \<subseteq> f-``(J)" using target_ring.ideal_dest_zero
    by auto
qed

text\<open>Kernel of the homomorphism in an ideal.\<close>

lemma (in ring_homo) kernel_ideal: shows "ker \<triangleleft>R\<^sub>o"
  using target_ring.zero_ideal preimage_ideal(2) by simp

text\<open>The inverse image of a prime ideal by a homomorphism is not the whole ring.
  Proof by contradiction.\<close>

lemma (in ring_homo) vimage_prime_ideal_not_all:
  assumes "J\<triangleleft>\<^sub>pR\<^sub>t" shows "f-``(J) \<noteq> R"
proof -
  { assume "R = f-``(J)"
    then have "R = {x\<in>R. f`(x)\<in>J}" using f_is_fun func1_1_L15 
      by simp
    then have "\<one>\<^sub>R \<in> {x\<in>R. f`(x)\<in>J}" using origin_ring.Ring_ZF_1_L2(2)
      by simp
    with origin_ring.ringAssum target_ring.ringAssum homomorphism assms
      have False using target_ring.ideal_with_one
        unfolding target_ring.primeIdeal_def ringHomomor_def by auto
  } thus "f-``(J) \<noteq> R" by blast
qed

text\<open>Even more, if the target ring of the homomorphism is commutative
  and the ideal is prime then its preimage is also. Note that this is 
  not true in general.\<close>

lemma (in ring_homo) preimage_prime_ideal_comm:
  assumes "J\<triangleleft>\<^sub>pR\<^sub>t" "V {is commutative on} S"
  shows "(f-``(J))\<triangleleft>\<^sub>pR\<^sub>o" 
proof -
  have "\<forall>x\<in>R. \<forall>y\<in>R. (\<forall>z\<in>R. x\<cdot>\<^sub>Rz\<cdot>\<^sub>Ry \<in> f-``(J)) \<longrightarrow> x\<in>f-``(J) \<or> y\<in>f-``( J)"
  proof -
    { fix x y assume "x\<in>R" "y\<in>R" and as: "\<forall>z\<in>R. x\<cdot>\<^sub>Rz\<cdot>\<^sub>Ry \<in> f-``(J)" 
        and "y \<notin> f-``(J)"
      { fix s assume "s\<in>S"
        with assms(2) \<open>x\<in>R\<close> \<open>y\<in>R\<close> have 
          "(f`(x))\<cdot>\<^sub>Ss\<cdot>\<^sub>S(f`(y)) = s\<cdot>\<^sub>S((f`(x))\<cdot>\<^sub>S(f`(y)))"
          using f_is_fun apply_funtype target_ring.Ring_ZF_1_L11(2)
          unfolding IsCommutative_def by auto
        with \<open>x\<in>R\<close> \<open>y\<in>R\<close> have "(f`x)\<cdot>\<^sub>Ss\<cdot>\<^sub>S(f`y) = s\<cdot>\<^sub>S(f`(x\<cdot>\<^sub>Ry))"
          using homomor_dest_mult by simp
        with assms(1) \<open>s\<in>S\<close> \<open>x\<in>R\<close> as have "(f`(x))\<cdot>\<^sub>Ss\<cdot>\<^sub>S(f`(y)) \<in> J"
          using origin_ring.Ring_ZF_1_L2(2) origin_ring.Ring_ZF_1_L3(5)
            func1_1_L15 f_is_fun target_ring.ideal_dest_mult(2)
          unfolding target_ring.primeIdeal_def by auto
      } hence "\<forall>z\<in>S. (f`x) \<cdot>\<^sub>S z \<cdot>\<^sub>S (f`y) \<in> J" by simp
      with assms(1) \<open>x\<in>R\<close> \<open>y\<in>R\<close>  have "f`(x)\<in> J \<or> f`(y)\<in>J" 
        using target_ring.equivalent_prime_ideal f_is_fun apply_funtype 
          by simp
      with \<open>x\<in>R\<close> \<open>y\<in>R\<close> \<open>y \<notin> f-``(J)\<close> have "x\<in>f-``(J)"
        using func1_1_L15 f_is_fun by simp
    } thus ?thesis by blast
  qed
  moreover from assms have "(f-``J)\<triangleleft>R\<^sub>o" using preimage_ideal 
    unfolding target_ring.primeIdeal_def by auto
  moreover from assms(1) have "f-``(J) \<noteq> R" using vimage_prime_ideal_not_all 
    by simp
  ultimately show "(f-``(J))\<triangleleft>\<^sub>pR\<^sub>o" 
    by (rule origin_ring.equivalent_prime_ideal_2)
qed

text\<open>We can replace the assumption that the target ring of the homomorphism is commutative
  with the assumption that homomorphism is surjective in \<open>preimage_prime_ideal_comm\<close>
  above and we can show the same assertion that the preimage of a prime ideal prime. \<close>

lemma (in ring_homo) preimage_prime_ideal_surj:
  assumes "J\<triangleleft>\<^sub>pR\<^sub>t" "f \<in> surj(R,S)"
  shows "(f-``(J))\<triangleleft>\<^sub>pR\<^sub>o" 
proof -
  have "\<forall>x\<in>R. \<forall>y\<in>R. (\<forall>z\<in>R. x\<cdot>\<^sub>Rz\<cdot>\<^sub>Ry \<in> f-``(J)) \<longrightarrow> x\<in>f-``(J) \<or> y\<in>f-``(J)"
  proof -
    { fix x y assume "x\<in>R" "y\<in>R" and as: "\<forall>z\<in>R. x\<cdot>\<^sub>Rz\<cdot>\<^sub>Ry \<in> f-``(J)" 
        and "y \<notin> f-``(J)"
      { fix s assume s: "s\<in>S"
        with assms(2) obtain t where "s=f`(t)" "t\<in>R"
          unfolding surj_def by auto
        with \<open>x\<in>R\<close> \<open>y\<in>R\<close> as have "(f`x)\<cdot>\<^sub>Ss\<cdot>\<^sub>S(f`y)\<in>J"
          using homomor_dest_mult origin_ring.Ring_ZF_1_L4(3) 
            func1_1_L15 f_is_fun by simp
      } hence "\<forall>z\<in>S. (f`(x)) \<cdot>\<^sub>S z \<cdot>\<^sub>S (f`(y)) \<in> J" by simp
      with target_ring.equivalent_prime_ideal assms(1) \<open>x\<in>R\<close> \<open>y\<in>R\<close>
      have "f`(x)\<in>J\<or>f`(y)\<in>J" using f_is_fun apply_funtype 
        by auto
      with \<open>x\<in>R\<close> \<open>y\<in>R\<close> \<open>y \<notin> f-``(J)\<close> have "x\<in>f-``(J)" 
        using func1_1_L15 f_is_fun by auto
    } thus ?thesis by blast
  qed
  moreover from assms have "(f-``(J))\<triangleleft>R\<^sub>o" using preimage_ideal 
    unfolding target_ring.primeIdeal_def by auto
  moreover from assms(1) have "f-``(J) \<noteq> R" using vimage_prime_ideal_not_all 
    by simp
  ultimately show "(f-``(J))\<triangleleft>\<^sub>pR\<^sub>o" 
    by (rule origin_ring.equivalent_prime_ideal_2)
qed

subsection\<open>Quotient ring with quotient map\<close>

text\<open>The notion of a quotient ring (a.k.a factor ring, difference ring or residue class) 
  is analogous to the notion of quotient group from the group theory. \<close>

text\<open>The next locale \<open>ring2\<close> extends the \<open>ring0\<close> locale (defined in the \<open>Ring_ZF\<close> theory)
   with the assumption that some fixed set $I$ is an ideal. It also defines some notation
  related to quotient rings, in particular we define the function (projection)
  $f_I$ that maps each element $r$ of the ring $R$ to its class $r_I(\{ r\}$
  where $r_I$ is the quotient group relation defined by $I$ as a (normal) subgroup 
  of $R$ with addition. \<close> 

locale ring2 = ring0 +
  fixes I
  assumes idealAssum: "I\<triangleleft>R"

  fixes quot ("R\<^sub>I")
  defines quot_def [simp]: "R\<^sub>I \<equiv> QuotientBy(I)"

  fixes qrel ("r\<^sub>I")
  defines qrel_def [simp]: "r\<^sub>I \<equiv> QuotientGroupRel(R,A,I)"

  fixes qfun ("f\<^sub>I")
  defines qfun_def [simp]: "f\<^sub>I \<equiv> \<lambda>r\<in>R. r\<^sub>I``{r}"

  fixes qadd ("A\<^sub>I")
  defines qadd_def [simp]: "A\<^sub>I \<equiv> QuotientGroupOp(R, A, I)"

  fixes qmul ("M\<^sub>I")
  defines qmul_def [simp]: "M\<^sub>I \<equiv> ProjFun2(R, qrel, M)"

text\<open>The expression \<open>J\<triangleleft>R\<^sub>I\<close> will mean that $J$ is an ideal of the quotient ring $R_I$
  (with the quotient addition and multiplication).\<close>

abbreviation (in ring2) qideal ("_\<triangleleft>R\<^sub>I") where
  "J\<triangleleft>R\<^sub>I \<equiv> ring0.Ideal(R\<^sub>I,A\<^sub>I,M\<^sub>I,J)"

text\<open>In the \<open>ring2\<close> The expression \<open>J\<triangleleft>\<^sub>pR\<^sub>I\<close> means that $J$ is a prime ideal of the quotient 
  ring $R_I$. \<close>

abbreviation (in ring2) qprimeIdeal ("_\<triangleleft>\<^sub>pR\<^sub>I") where
  "J\<triangleleft>\<^sub>pR\<^sub>I \<equiv> ring0.primeIdeal(R\<^sub>I,A\<^sub>I,M\<^sub>I,J)"

text\<open>Theorems proven in the \<open>ring0\<close> context can be applied
  to the quotient ring in the \<open>ring2\<close> context. \<close>

sublocale ring2 < quotient_ring: ring0 quot qadd qmul
  "\<lambda>x y. ideal_radd(x,I,y)" "\<lambda>y. ideal_rmin(I,y)" 
  "\<lambda>x y. ideal_rsub(x,I,y)" "\<lambda>x y. ideal_rmult(x,I,y)"
  "\<zero>\<^sub>I" "\<one>\<^sub>I" "\<two>\<^sub>I" "\<lambda>x. (x\<^sup>2\<^sup>I)" 
  using quotientBy_is_ring idealAssum neutral_quotient 
    one_quotient two_quotient
  unfolding ring0_def  ideal_radd_def ideal_rmin_def
    ideal_rsub_def ideal_rmult_def ideal_rzero_def 
    ideal_rone_def ideal_rtwo_def ideal_rsqr_def by auto

text\<open>The quotient map is a homomorphism of rings. This is probably one of the
  most sophisticated facts in IsarMathlib that Isabelle's simp method proves  
  from 10 facts and 5 definitions. \<close>

theorem (in ring2) quotient_fun_homomor:
  shows "ringHomomor(f\<^sub>I,R,A,M,R\<^sub>I,A\<^sub>I,M\<^sub>I)"
  using ringAssum idealAssum ideal_normal_add_subgroup add_group.quotient_map 
      Ring_ZF_1_L4(3) EquivClass_1_L10 Ring_ZF_1_L2(2) Group_ZF_2_2_L1 
      ideal_equiv_rel quotientBy_mul_monoid(1) QuotientBy_def
  unfolding IsAring_def Homomor_def IsMorphism_def ringHomomor_def
  by simp

text\<open>The quotient map is surjective\<close>

lemma (in ring2) quot_fun:
  shows "f\<^sub>I\<in>surj(R,R\<^sub>I)" 
  using lam_funtype idealAssum QuotientBy_def 
  unfolding quotient_def surj_def by auto

text\<open>The theorems proven in the  \<open>ring_homo\<close> context are valid in the 
  \<open>ring_homo\<close> context when applied to the quotient ring as the second (target) 
  ring and the quotient map as the ring homomorphism.\<close>

sublocale ring2 < quot_homomorphism: ring_homo R A M quot qadd qmul qfun
  _ _ _ _ _ _ _ _ "\<lambda>x y. ideal_radd(x,I,y)" "\<lambda>y. ideal_rmin(I,y)" 
  "\<lambda>x y. ideal_rsub(x,I,y)" "\<lambda>x y. ideal_rmult(x,I,y)"
  "\<zero>\<^sub>I" "\<one>\<^sub>I" "\<two>\<^sub>I" "\<lambda>x. (x\<^sup>2\<^sup>I)"
  using ringAssum quotient_ring.ringAssum quotient_fun_homomor
  unfolding ring_homo_def by simp_all

text\<open>The ideal we divide by is the kernel of the quotient map.\<close>

lemma (in ring2) quotient_kernel: 
  shows "quot_homomorphism.kernel = I"
proof
  from idealAssum show "quot_homomorphism.kernel \<subseteq> I"
    using add_group.Group_ZF_2_4_L5E ideal_normal_add_subgroup
        neutral_quotient QuotientBy_def 
        quot_homomorphism.image_kernel func1_1_L15
    unfolding  ideal_rzero_def QuotientBy_def by auto  
  { fix t assume "t\<in>I"
    then have "t\<in>R" using ideal_dest_subset idealAssum by auto
    with idealAssum \<open>t\<in>I\<close> have "t \<in> f\<^sub>I-``{\<zero>\<^sub>I}"
      using add_group.Group_ZF_2_4_L5E ideal_normal_add_subgroup
        neutral_quotient QuotientBy_def func1_1_L15 surj_is_fun
      unfolding ideal_rzero_def by auto          
  } thus "I \<subseteq> quot_homomorphism.kernel" by blast
qed

text\<open>The theorems proven in the \<open>ring0\<close> context are valid in the 
  \<open>ring 2\<close> context when applied to the quotient ring.\<close>

sublocale ring2 < quotient_ring: ring0 quot qadd qmul
  "\<lambda>x y. ideal_radd(x,I,y)" "\<lambda>y. ideal_rmin(I,y)" 
  "\<lambda>x y. ideal_rsub(x,I,y)" "\<lambda>x y. ideal_rmult(x,I,y)"
  "\<zero>\<^sub>I" "\<one>\<^sub>I" "\<two>\<^sub>I" "\<lambda>x. (x\<^sup>2\<^sup>I)" 
  using idealAssum quotientBy_is_ring neutral_quotient
    one_quotient two_quotient 
  unfolding ring0_def by simp_all

text\<open>If an ideal $I$ is a subset of the kernel of the homomorphism
  then the image of the ideal generated by $I\cup J$, where $J$ is another ideal,
  is the same as the image of $J$. Note that \<open>J+\<^sub>II\<close> notation means
  the ideal generated by the union of ideals $J$ and $J$, see the definitions
  of \<open>sumIdeal\<close> and \<open>generatedIdeal\<close> in the \<open>Ring_ZF_2\<close> theory, and also
  corollary \<open>sum_ideals_is_sum_elements\<close> for an alternative definition.  \<close>

theorem (in ring_homo) kernel_empty_image:
  assumes "J\<triangleleft>R" "I \<subseteq> ker" "I\<triangleleft>R"
  shows "f``(J+\<^sub>II) = f``(J)" "f``(I+\<^sub>IJ) = f``(J)"
proof-
  from assms(1,3) have "J+\<^sub>II \<subseteq> R" 
    using origin_ring.sum_ideals_is_ideal 
      origin_ring.ideal_dest_subset by auto
  show "f``(J+\<^sub>II) = f``(J)"
  proof
    { fix t assume "t\<in>f``(J+\<^sub>II)"
      with \<open>J+\<^sub>II \<subseteq> R\<close> obtain q where q: "q \<in> J+\<^sub>II" "t=f`(q)"
        using func_imagedef f_is_fun by auto
      with assms(1,3) \<open>q \<in> J+\<^sub>II\<close> have "q\<in>A``(J\<times>I)" "J\<times>I \<subseteq> R\<times>R" 
        using origin_ring.sum_ideals_is_sum_elements
        assms(1,3) origin_ring.ideal_dest_subset by auto
      from origin_ring.add_group.groupAssum \<open>J\<times>I \<subseteq> R\<times>R\<close>
      have "A``(J\<times>I) = {A`(p). p\<in>J\<times>I}"
        unfolding IsAgroup_def IsAmonoid_def IsAssociative_def
        using func_imagedef by auto
      with \<open>q\<in>A``(J\<times>I)\<close> obtain q\<^sub>j q\<^sub>i where "q\<^sub>j\<in>J" "q\<^sub>i\<in>I" "q=q\<^sub>j\<ra>\<^sub>Rq\<^sub>i" 
        by auto
      with assms have "f`(q) = (f`(q\<^sub>j)) \<ra>\<^sub>S \<zero>\<^sub>S"
        using homomor_dest_add origin_ring.ideal_dest_subset image_kernel
        by blast
      moreover from assms(1) \<open>q\<^sub>j\<in>J\<close> have "f`(q\<^sub>j) \<in> S"
        using origin_ring.ideal_dest_subset f_is_fun apply_funtype by blast
      ultimately have "f`(q) = f`(q\<^sub>j)" using target_ring.Ring_ZF_1_L3(3) 
        by auto    
      with assms \<open>t=f`(q)\<close> \<open>q\<^sub>j\<in>J\<close> have "t \<in> f``(J)"
        using func_imagedef f_is_fun origin_ring.ideal_dest_subset by auto    
    } thus "f``(J+\<^sub>II) \<subseteq> f``(J)" by blast
    { fix t assume "t\<in>f``(J)"
      with assms(1) obtain q where q:"q\<in>J" "t=f`(q)"
        using func_imagedef f_is_fun origin_ring.ideal_dest_subset 
        by auto
      from \<open>q\<in>J\<close> have "q\<in>J\<union>I" by auto 
      moreover from assms(1,3) have "J\<union>I \<subseteq> R" 
        using origin_ring.ideal_dest_subset by auto
      ultimately have "q\<in>\<langle>J\<union>I\<rangle>\<^sub>I" using origin_ring.generated_ideal_contains_set 
        by auto
      with assms(1,3) \<open>J+\<^sub>II \<subseteq> R\<close> \<open>t=f`(q)\<close> have "t\<in>f``(J+\<^sub>II)"
        using origin_ring.sumIdeal_def f_is_fun func_imagedef by auto
    } thus "f``(J) \<subseteq> f``(J+\<^sub>II)" by auto
  qed
  with assms(1,3) show "f ``(I+\<^sub>IJ) = f``(J)"
    using origin_ring.sum_ideals_commute by auto
qed

subsection\<open>Quotient ideals\<close>

text\<open>If we have an ideal $J$ in a ring $R$, and another ideal $I$ contained in J, 
  then we can form the quotient ideal J/I whose elements are of the form $a + I$
  where $a$ is an element of $J$.\<close>

text\<open>The preimage of an ideal is an ideal, so it applies to the
  quotient map; but the preimage ideal contains the quotient ideal.\<close>

lemma (in ring2) ideal_quot_preimage:
  assumes "J\<triangleleft>R\<^sub>I"
  shows "(f\<^sub>I-``(J)) \<triangleleft>R" "I \<subseteq> f\<^sub>I-``(J)"
proof -
  from assms quot_homomorphism.preimage_ideal show "(f\<^sub>I-``(J)) \<triangleleft>R" 
    by simp
  { fix x assume x: "x\<in>I"
    with idealAssum have "x\<in>R" using ideal_dest_subset by auto
    from assms \<open>x\<in>I\<close> have "f\<^sub>I`(x) \<in> J"
      using quotient_kernel quot_homomorphism.image_kernel 
        quotient_ring.ideal_dest_zero by simp
    with \<open>x\<in>R\<close> have "x\<in>f\<^sub>I-``(J)" using quot_homomorphism.f_is_fun func1_1_L15 
      by simp
  } thus "I \<subseteq> f\<^sub>I-``(J)" by auto
qed

text\<open>Since the map is surjective, the image is also an ideal\<close>

lemma (in ring_homo) image_ideal_surj:
  assumes "J\<triangleleft>R\<^sub>o" "f\<in>surj(R,S)"
  shows "(f``(J)) \<triangleleft>R\<^sub>t" 
proof -
  from assms homomorphism target_ring.ringAssum origin_ring.ringAssum 
  have "IsAsubgroup(f``(J),U)"
    using ringHomHom(1) image_subgroup f_is_fun
    unfolding IsAring_def origin_ring.Ideal_def by blast
  moreover
  { fix x y assume "x\<in>f``(J)" "y\<in>S"
    from assms(1) \<open>x\<in>f``(J)\<close> obtain j where "x=f`(j)" "j\<in>J" 
      using func_imagedef f_is_fun origin_ring.ideal_dest_subset 
      by auto
    from assms \<open>y\<in>S\<close> \<open>j\<in>J\<close> have "j\<in>R" and "y\<in>f``(R)"
      using origin_ring.ideal_dest_subset surj_range_image_domain
      by auto
    with assms(1) obtain s where "y=f`(s)" "s\<in>R" 
      using func_imagedef origin_ring.ideal_dest_subset f_is_fun 
      by auto
    with assms(1) \<open>j\<in>R\<close> \<open>x=f`(j)\<close> \<open>x\<in>f``(J)\<close> have 
      "V`\<langle>x,y\<rangle> = f`(M`\<langle>j,s\<rangle>)" and "V`\<langle>y,x\<rangle> = f`(M`\<langle>s,j\<rangle>)"
      using homomor_dest_mult origin_ring.ideal_dest_subset by auto
    with assms(1) \<open>j\<in>J\<close> \<open>s\<in>R\<close> have "(x\<cdot>\<^sub>Sy)\<in>f``(J)" and "(y\<cdot>\<^sub>Sx)\<in>f``J"
      using origin_ring.ideal_dest_mult func_imagedef f_is_fun 
        origin_ring.ideal_dest_subset by auto
  } hence "\<forall>x\<in>f``(J). \<forall>y\<in>S. (y\<cdot>\<^sub>Sx) \<in> f``(J) \<and> (x\<cdot>\<^sub>Sy) \<in> f``(J)"
    by auto
  ultimately show ?thesis unfolding target_ring.Ideal_def by simp
qed
  
text\<open>If the homomorphism is a surjection and given two ideals in the target ring 
  the inverse image of their product ideal is the sum ideal of the product
  ideal of their inverse images and the kernel of the homomorphism.\<close>

corollary (in ring_homo) prime_ideal_quot:
  assumes "J\<triangleleft>R\<^sub>t" "K\<triangleleft>R\<^sub>t" "f\<in>surj(R,S)"
  shows "f-``(target_ring.productIdeal(J, K)) = 
  origin_ring.sumIdeal(origin_ring.productIdeal((f-``(J)),(f-``(K))), ker)"
proof
  let ?P = "origin_ring.sumIdeal(origin_ring.productIdeal((f-``(J)),(f-``(K))), f-``{\<zero>\<^sub>S})"
  let ?Q = "target_ring.productIdeal(J, K)"
  from assms(1,2) have ideals: "(f-``(J)) \<triangleleft>R\<^sub>o" "(f-``(K)) \<triangleleft>R\<^sub>o"
    using preimage_ideal by auto
  then have idealJK: "((f-``(J))\<cdot>\<^sub>I(f-``(K))) \<triangleleft>R\<^sub>o"
    using origin_ring.product_in_intersection(2) by auto
  then have "?P \<triangleleft>R\<^sub>o" and "?P\<subseteq>R" 
    using kernel_ideal origin_ring.sum_ideals_is_ideal 
      origin_ring.ideal_dest_subset by simp_all
  with assms(3) have  "(f``(?P)) \<triangleleft>R\<^sub>t" using  image_ideal_surj
    by simp
  let ?X = "((f-``(J)) \<cdot>\<^sub>I (f-``(K)))\<union>(f-``{\<zero>\<^sub>S})"
  from assms(3) idealJK have "?X \<subseteq> R" 
      using func1_1_L6A surj_is_fun origin_ring.ideal_dest_subset 
      by blast
  with idealJK have "?X \<subseteq> ?P"
      using kernel_ideal origin_ring.sumIdeal_def 
        origin_ring.generated_ideal_contains_set by simp
  { fix t assume "t\<in>V ``(J\<times>K)"
    moreover from assms have "J\<times>K \<subseteq> S\<times>S" 
      using target_ring.ideal_dest_subset by blast 
    ultimately obtain j k where "j\<in>J" "k\<in>K" "t=V`\<langle>j,k\<rangle>"
      using func_imagedef AMUV_are_ops(4) by auto
    from assms(1) \<open>j\<in>J\<close> have "j\<in>S" 
      using target_ring.ideal_dest_subset by blast
    with assms(3) obtain j\<^sub>0 where  "j\<^sub>0\<in>R" "f`(j\<^sub>0) = j"
      unfolding surj_def by auto
    with assms(2,3) \<open>k\<in>K\<close> obtain k\<^sub>0 where "k\<^sub>0\<in>R" "f`(k\<^sub>0) = k"
      using target_ring.ideal_dest_subset unfolding surj_def 
      by blast
    with \<open>t=V`\<langle>j,k\<rangle>\<close> \<open>f`(j\<^sub>0) = j\<close>  \<open>j\<^sub>0\<in>R\<close> have "t=f`(M`\<langle>j\<^sub>0,k\<^sub>0\<rangle>)" 
      using homomor_dest_mult by simp
    from assms(3) have "(f-``(J))\<times>(f-``(K)) \<subseteq> R\<times>R"
      using func1_1_L6A  f_is_fun by blast
    moreover from assms(3) \<open>j\<^sub>0\<in>R\<close> \<open>f`(j\<^sub>0) = j\<close> \<open>j\<in>J\<close> \<open>k\<in>K\<close> \<open>k\<^sub>0\<in>R\<close> \<open>f`(k\<^sub>0) = k\<close>
      have "\<langle>j\<^sub>0,k\<^sub>0\<rangle> \<in> (f-``J)\<times>(f-``K)"
      using func1_1_L15 unfolding surj_def by auto
    ultimately have "M`\<langle>j\<^sub>0,k\<^sub>0\<rangle> \<in> M``((f-``(J))\<times>(f-``(K)))"
      using AMUV_are_ops func_imagedef by auto
    with ideals \<open>?X \<subseteq> ?P\<close> have "M`\<langle>j\<^sub>0,k\<^sub>0\<rangle> \<in> ?P"
      using origin_ring.product_in_intersection(3) 
      by blast
    with \<open>?P\<subseteq>R\<close> \<open>t=f`(M`\<langle>j\<^sub>0,k\<^sub>0\<rangle>)\<close> have "t\<in>(f``(?P))"
      using f_is_fun func1_1_L15D by simp
  } hence "V``(J \<times> K) \<subseteq> f``(?P)" by blast
  with assms(1,2) \<open>(f``(?P)) \<triangleleft>R\<^sub>t\<close> have "?Q\<subseteq>f``(?P)"
    using target_ring.generated_ideal_small target_ring.productIdeal_def
    by simp
  then have R: "f-``(?Q) \<subseteq> f-``(f``?P)"
    unfolding vimage_def by blast
  from \<open>?X \<subseteq> ?P\<close> \<open>?P \<triangleleft>R\<^sub>o\<close> \<open>?P\<subseteq>R\<close> have P_ideal: "?P \<in> {N\<in>\<I>. f-``{\<zero>\<^sub>S} \<subseteq> N}" 
    by auto
  { fix t assume "t\<in>f-``(f``(?P))"
    then have "f`(t) \<in> f``(?P)" and "t\<in>R" 
      using func1_1_L15 f_is_fun by simp_all
    with P_ideal obtain s where "f`(t) = f`(s)" "s\<in>?P" 
      using func_imagedef f_is_fun by auto
    from P_ideal \<open>s\<in>?P\<close> have "s\<in>R" by blast
    from \<open>t\<in>R\<close> \<open>s\<in>R\<close> \<open>f`(t) = f`(s)\<close> have "f`(t\<rs>\<^sub>Rs) = \<zero>\<^sub>S"
      using f_is_fun apply_funtype target_ring.Ring_ZF_1_L3(7) 
        homomor_dest_subs by simp
    with \<open>t\<in>R\<close> \<open>s\<in>R\<close> \<open>?X\<subseteq>?P\<close> have "t\<rs>\<^sub>Rs \<in> ?P"
      using origin_ring.Ring_ZF_1_L4(2) func1_1_L15 f_is_fun 
      by auto
    with P_ideal \<open>s\<in>?P\<close> have "s\<ra>\<^sub>R(t\<rs>\<^sub>Rs) \<in> ?P" 
      using origin_ring.ideal_dest_sum by auto
    with \<open>t\<in>R\<close> \<open>s\<in>R\<close> have "t\<in>?P" 
      using origin_ring.Ring_ZF_2_L1A(5) by auto
  } with R show "f-``(?Q) \<subseteq> ?P" 
    by auto
  { fix t assume as: "t \<in> M``((f-``(J))\<times>(f-``(K)))"
    have "(f-``(J))\<times>(f-``(K)) \<subseteq> R\<times>R" 
      using func1_1_L15 f_is_fun by auto
    with as obtain t\<^sub>j t\<^sub>k where 
      jk: "t=t\<^sub>j\<cdot>\<^sub>Rt\<^sub>k" "t\<^sub>j\<in>f-``(J)" "t\<^sub>k\<in>f-``(K)"
      using AMUV_are_ops(2) func_imagedef IsAssociative_def 
      by auto
    from as have "t\<in>R" using AMUV_are_ops(2) func1_1_L6(2) by blast
    from jk(2,3) have "t\<^sub>j\<in>R" "f`(t\<^sub>j)\<in>J" and "t\<^sub>k\<in>R" "f`(t\<^sub>k)\<in>K" 
      using func1_1_L15 f_is_fun by simp_all
    from jk(1) \<open>t\<^sub>j\<in>R\<close> \<open>t\<^sub>k\<in>R\<close> have ft: "f`(t) = ((f`(t\<^sub>j))\<cdot>\<^sub>S(f`(t\<^sub>k)))"
      using homomor_dest_mult by simp
    from \<open>f`(t\<^sub>j)\<in>J\<close> \<open>f`(t\<^sub>k) \<in>K\<close> have "\<langle>f`(t\<^sub>j),f`(t\<^sub>k)\<rangle> \<in> J\<times>K" 
      by simp
    moreover from assms have "V:S\<times>S\<rightarrow>S" and "J\<times>K \<subseteq> S\<times>S" 
      using AMUV_are_ops(4) target_ring.ideal_dest_subset 
      by auto
    ultimately have "V`\<langle>f`(t\<^sub>j), f`(t\<^sub>k)\<rangle> \<in>V``(J\<times>K)"
      using func_imagedef by force
    with assms ft \<open>t\<in>R\<close> have "t \<in> f-``(?Q)"
      using target_ring.product_in_intersection(3) func1_1_L15 f_is_fun 
      by auto  
  } hence "M``(f-``(J)\<times>f-``(K))\<subseteq>f-``(?Q)" 
    by auto
  moreover from assms(1,2) have 
    id: "(f-``(?Q)) \<triangleleft>R\<^sub>o"
    using preimage_ideal target_ring.product_in_intersection(2)
    by simp
  ultimately have "(f -`` J) \<cdot>\<^sub>I (f -`` K)\<subseteq>f-``(?Q)"
    using ideals origin_ring.generated_ideal_small origin_ring.productIdeal_def
    by auto
  with assms(1,2) have "?X \<subseteq> f-``(?Q)"
    using target_ring.product_in_intersection(2) target_ring.ideal_dest_zero 
    by auto
  with idealJK id show 
    "((f-``(J))\<cdot>\<^sub>I(f-``(K)))+\<^sub>I(f-``{\<zero>\<^sub>S}) \<subseteq> f-``(?Q)"
    using origin_ring.generated_ideal_small kernel_ideal origin_ring.sumIdeal_def
    by simp
qed

text\<open>If the homomorphism is surjective then the product ideal of ideals $J,K$ 
  in the target ring is the image of the product ideal (in the source ring) 
  of the inverse images of $J,K$. \<close>

corollary (in ring_homo) prime_ideal_quot_2:
  assumes "J\<triangleleft>R\<^sub>t" "K\<triangleleft>R\<^sub>t" "f\<in>surj(R,S)"
  shows "target_ring.productIdeal(J, K) = 
    f``(origin_ring.productIdeal((f-``(J)), (f-``(K))))"      
proof -
  from assms have "f``(f-``(target_ring.productIdeal(J, K)))
      = f``(((f-``(J)) \<cdot>\<^sub>I (f-``(K))) +\<^sub>I (ker))"
    using prime_ideal_quot by simp
  with assms show ?thesis
    using target_ring.product_in_intersection(2) 
      target_ring.ideal_dest_subset surj_image_vimage
      origin_ring.product_in_intersection(2) preimage_ideal
      kernel_empty_image(1) target_ring.zero_ideal
    by simp
qed

text\<open>If the homomorphism is surjective and an ideal in the source ring
  contains the kernel, then the image of that ideal is a prime ideal in the 
  target ring.\<close>

lemma (in ring_homo) preimage_ideal_prime:
  assumes "J\<triangleleft>\<^sub>pR\<^sub>o" "ker \<subseteq> J" "f\<in>surj(R,S)"
  shows "(f``(J))\<triangleleft>\<^sub>pR\<^sub>t"
proof -
  from assms(1) have "J \<subseteq> R" "J \<noteq> R" 
    unfolding origin_ring.primeIdeal_def 
    using origin_ring.ideal_dest_subset by auto
  from assms(1,3) have "(f``(J))\<triangleleft>R\<^sub>t" 
    using image_ideal_surj  unfolding origin_ring.primeIdeal_def 
    by auto 
  moreover 
  { assume "f``(J) = S"
    from \<open>J \<subseteq> R\<close> \<open>J \<noteq> R\<close> obtain t where "t\<in>R-J" by auto
    with assms(3) have "f`(t)\<in>S" 
      using apply_funtype f_is_fun by auto
    with assms(3) \<open>J \<subseteq> R\<close> \<open>f``(J) = S\<close> obtain j 
      where j: "j\<in>J" "f`(t)= f`(j)"
      using func_imagedef f_is_fun by auto   
    from \<open>j\<in>J\<close> \<open>J \<subseteq> R\<close> have "j\<in>R" by auto
    with assms(3) \<open>f`(t)= f`(j)\<close> \<open>t\<in>R-J\<close> have "t\<rs>\<^sub>Rj\<in>f-``{\<zero>\<^sub>S}"
      using apply_type target_ring.Ring_ZF_1_L3(7) f_is_fun 
        homomor_dest_subs origin_ring.Ring_ZF_1_L4(2) func1_1_L15
        by auto
    with assms(1,2) j(1) have "j\<ra>\<^sub>R(t\<rs>\<^sub>Rj) \<in>J"
      unfolding origin_ring.primeIdeal_def
      using origin_ring.ideal_dest_sum by auto
    with \<open>j\<in>R\<close> \<open>t\<in>R-J\<close> have False using origin_ring.Ring_ZF_2_L1A(5)
      by auto
  } hence "f``(J) \<noteq> S" by auto 
  moreover
  { fix I K assume as: "I\<in>target_ring.ideals" "K\<in>target_ring.ideals"
           "target_ring.productIdeal(I, K) \<subseteq> f``(J)"
    let ?A = "(f-``(I)) \<cdot>\<^sub>I (f-``(K))"
    from as(1,2) have "?A \<subseteq> f-``(f``(?A))"
      using origin_ring.product_in_intersection(2) preimage_ideal(2)
        origin_ring.ideal_dest_subset func1_1_L9 f_is_fun by auto
    with assms(3) as have "?A \<subseteq> f-``(f``(J))"
      using prime_ideal_quot_2 vimage_mono by force
    moreover from assms(1) have "J \<subseteq> f-``(f``(J))" 
      using func1_1_L9 f_is_fun origin_ring.ideal_dest_subset 
      unfolding origin_ring.primeIdeal_def by auto 
    moreover
    { fix t assume "t \<in> f-``(f``(J))"
      then have "f`(t)\<in>f``(J)" "t\<in>R" using func1_1_L15 f_is_fun 
        by auto
      from assms(1) \<open>f`(t)\<in>f``(J)\<close> obtain s where "f`(t)=f`(s)" "s\<in>J"
        using func_imagedef f_is_fun origin_ring.ideal_dest_subset 
        unfolding origin_ring.primeIdeal_def by auto
      from assms(1) \<open>s\<in>J\<close> have "s\<in>R" 
        unfolding origin_ring.primeIdeal_def
        using origin_ring.ideal_dest_subset by auto
      with assms(2) \<open>f`(t)=f`(s)\<close> \<open>t\<in>R\<close> have "t\<rs>\<^sub>Rs \<in> J"
        using target_ring.Ring_ZF_1_L3(7) apply_funtype f_is_fun
          homomor_dest_subs origin_ring.Ring_ZF_1_L4(2) func1_1_L15
        by auto
      with assms(1) \<open>s\<in>J\<close> have "s\<ra>\<^sub>R(t\<rs>\<^sub>Rs)\<in>J"
        using origin_ring.ideal_dest_sum
        unfolding origin_ring.primeIdeal_def by auto
      with \<open>s\<in>R\<close> \<open>t\<in>R\<close> have "t\<in>J" using origin_ring.Ring_ZF_2_L1A(5)
        by auto
    } hence "f-``(f``J) \<subseteq> J" by auto
    ultimately have "?A \<subseteq> J" by auto    
    with assms(1) as(1,2) have "(f-``(I)) \<subseteq> J \<or> (f-``(K)) \<subseteq> J"
      using preimage_ideal origin_ring.ideal_dest_subset
      unfolding origin_ring.primeIdeal_def
      by auto
    hence "f``(f-``(I)) \<subseteq> f``J \<or> f``(f-``(K)) \<subseteq> f``(J)"
      by auto
    with assms(3) as(1,2) have "I \<subseteq> f``(J) \<or> K \<subseteq> f``(J)"
      using surj_image_vimage by auto
  }
  ultimately show ?thesis unfolding target_ring.primeIdeal_def by auto
qed

text\<open>The ideals of the quotient ring are in bijection
  with the ideals of the original ring that contain the ideal
  by which we made the quotient.\<close>

theorem (in ring_homo) ideal_quot_bijection:
  assumes "f\<in>surj(R,S)"
  defines "idealFun \<equiv> \<lambda>J\<in>target_ring.ideals. f-``(J)"
  shows "idealFun \<in> bij(target_ring.ideals,{K\<in>\<I>. ker \<subseteq> K})"
proof -
  let ?\<I>\<^sub>t = "target_ring.ideals"
  have "idealFun : ?\<I>\<^sub>t \<rightarrow> {f-``(J). J\<in>?\<I>\<^sub>t}"
    unfolding idealFun_def using lam_funtype by simp 
  moreover
  { fix t assume "t \<in> {f-``(J). J\<in>?\<I>\<^sub>t}"
    then obtain K where "K \<in> ?\<I>\<^sub>t" "f-``(K) = t" by auto
    then have "K\<triangleleft>R\<^sub>t" by simp
    then have "(f-``(K))\<triangleleft>R" "ker \<subseteq> f-``(K)" using preimage_ideal(2,3)
      by simp_all
    with \<open>f-``(K) = t\<close> have "ker \<subseteq> t" "t\<triangleleft>R" by simp_all
    with \<open>f-``(K) = t\<close> have "t\<in>{K\<in>\<I>. ker \<subseteq> K}" using func1_1_L3 f_is_fun 
      by blast
  } hence "{f-``(J). J\<in>?\<I>\<^sub>t} \<subseteq> {K\<in>\<I>. ker \<subseteq> K}" by blast
  ultimately have I: "idealFun : ?\<I>\<^sub>t \<rightarrow> {K\<in>\<I>. ker \<subseteq> K}"
    using func1_1_L1B by auto
  { fix w x assume 
      as: "w\<triangleleft>R\<^sub>t" "x\<triangleleft>R\<^sub>t" "w\<subseteq>S" "x\<subseteq>S" "idealFun`(w) = idealFun`(x)"
    then have "f``(f-``(w)) = f``(f-``(x))" unfolding idealFun_def by simp
    with assms(1) as have "w = x" using surj_image_vimage
      by simp
  }
  with I have "idealFun \<in>  inj(?\<I>\<^sub>t,{K\<in>\<I>. ker \<subseteq> K})"
    unfolding inj_def by auto
  moreover
  { fix y assume "y\<triangleleft>R" "y\<subseteq>R" "ker \<subseteq> y"
    from \<open>y\<subseteq>R\<close> have "y \<subseteq> f-``(f``y)" using func1_1_L9 f_is_fun 
      by auto
    moreover
    { fix t assume "t\<in>f-``(f``(y))"
      then have "f`(t) \<in> f``(y)" "t\<in>R" using func1_1_L15 f_is_fun 
        by auto
      from \<open>f`(t) \<in> f``(y)\<close> \<open>y\<subseteq>R\<close> obtain s where "s\<in>y" "f`(t) = f`(s)" 
        using func_imagedef f_is_fun by auto
      from \<open>s\<in>y\<close>  \<open>y\<subseteq>R\<close> have "s\<in>R" by auto
      with \<open>t\<in>R\<close> \<open>f`(t) = f`(s)\<close> \<open>ker \<subseteq> y\<close> have "t\<rs>\<^sub>Rs \<in> y"
        using target_ring.Ring_ZF_1_L3(7) homomor_dest_subs 
          origin_ring.Ring_ZF_1_L4(2) func1_1_L15 f_is_fun
        by auto
      with \<open>s\<in>y\<close> \<open>y\<triangleleft>R\<close> \<open>s\<in>R\<close> \<open>t\<in>R\<close> have "t\<in>y"
        using origin_ring.ideal_dest_sum origin_ring.Ring_ZF_2_L1A(5)
        by force
    } 
    ultimately have "f-``(f``(y)) = y" by blast 
    moreover have "f``(y) \<subseteq> S" using func1_1_L6(2) f_is_fun
      unfolding surj_def by auto 
    moreover from assms(1) \<open>y\<triangleleft>R\<close> have "(f``(y))\<triangleleft>R\<^sub>t" using image_ideal_surj
       by auto
    ultimately have "\<exists>x\<in>?\<I>\<^sub>t. idealFun`(x) = y"
      unfolding idealFun_def by auto
  }
  with I have "idealFun \<in> surj(?\<I>\<^sub>t,{K\<in>\<I>. ker \<subseteq> K})"
    unfolding surj_def by auto
  ultimately show ?thesis unfolding bij_def by blast
qed

text\<open>Assume the homomorphism $f$ is surjective and consider the function
  that maps an ideal $J$ in the target ring to its inverse image
  $f^{-1}(J)$ (in the source ring). Then the value of the converse
  of that function on any ideal containing the kernel of $f$ is the image
  of that ideal under the homomorphism $f$.  \<close>

theorem (in ring_homo) quot_converse:
  defines "F \<equiv> \<lambda>J\<in>target_ring.ideals. f-``(J)"
  assumes "J\<triangleleft>R" "ker\<subseteq>J" "f\<in>surj(R,S)"
  shows "converse(F)`(J) = f``(J)"
proof-
  let ?g = "\<lambda>J\<in>{K\<in>\<I>. ker\<subseteq>K}. f``(J)"
  let ?\<I>\<^sub>t = "target_ring.ideals"
  let ?C\<^sub>F = "converse(F)"
  from assms(1,4) have "?C\<^sub>F \<in> bij({K\<in>\<I>. ker\<subseteq>K}, ?\<I>\<^sub>t)" 
    using bij_converse_bij ideal_quot_bijection 
    by auto
  then have I: "?C\<^sub>F:{K\<in>\<I>. ker\<subseteq>K} \<rightarrow> ?\<I>\<^sub>t"
    unfolding bij_def inj_def by auto
  moreover from assms(2,3) have J: "J \<in> {K\<in>\<I>. ker\<subseteq>K}" 
    using origin_ring.ideal_dest_subset by auto
  ultimately have ideal: "?C\<^sub>F`(J) \<in> ?\<I>\<^sub>t"
    using apply_funtype by blast
  with assms(1,4) ideal have "?g`(F`(?C\<^sub>F`(J))) = ?C\<^sub>F`(J)"
    using preimage_ideal origin_ring.ideal_dest_subset
      surj_image_vimage by auto
  moreover
  from assms(1) have "F: ?\<I>\<^sub>t \<rightarrow> {f-``(J). J\<in>?\<I>\<^sub>t}"
    using lam_funtype by simp
  with I J have "F`(?C\<^sub>F`(J)) = J"
    using right_inverse_lemma by simp
  ultimately have "?g`(J) = ?C\<^sub>F`(J)" by simp
  with J show ?thesis by simp
qed
  
text\<open>Since the map is surjective, this bijection
  restricts to prime ideals on both sides.\<close>

corollary (in ring_homo) prime_ideal_quot_3:
  assumes "K\<triangleleft>R\<^sub>t" "f \<in> surj(R,S)"
  shows "K\<triangleleft>\<^sub>pR\<^sub>t \<longleftrightarrow> ((f-``(K))\<triangleleft>\<^sub>pR)"
proof
  { assume "K\<triangleleft>\<^sub>pR\<^sub>t"
    with assms(2) show "(f-``(K))\<triangleleft>\<^sub>pR"
      using preimage_prime_ideal_surj target_ring.ideal_dest_subset
      unfolding target_ring.primeIdeal_def by auto
  }
  { assume "(f-``(K))\<triangleleft>\<^sub>pR"
    with assms(1,2) have "K\<triangleleft>R\<^sub>t" and "K\<noteq>S"
      using func1_1_L4 unfolding origin_ring.primeIdeal_def surj_def 
      by auto    
    moreover
    { fix J P assume jp: "J\<in>target_ring.ideals"
        "P\<in>target_ring.ideals"
        "target_ring.productIdeal(J, P) \<subseteq> K"
      from jp(3) have "f-``(target_ring.productIdeal(J, P)) \<subseteq> f-``(K)"
        by auto
      with assms(2) jp(1,2) have 
        A: "((f-``(J)) \<cdot>\<^sub>I (f-``(P))) +\<^sub>I (ker) \<subseteq> f-``(K)" 
        using prime_ideal_quot by auto 
      from jp(1,2) have 
        "(f-``(J))\<cdot>\<^sub>I(f-``(P)) \<union> ker \<subseteq> ((f-``(J))\<cdot>\<^sub>I(f-``(P))) +\<^sub>I (ker)"
        using preimage_ideal origin_ring.product_in_intersection(2) 
          kernel_ideal origin_ring.comp_in_sum_ideals(3) by simp
      with A have "((f -`` J) \<cdot>\<^sub>I (f -`` P)) \<subseteq> f-``(K)" by auto
      with \<open>(f-``(K))\<triangleleft>\<^sub>pR\<close> jp(1,2) have 
        "f-``(J) \<subseteq> f-``(K) \<or> f-``(P) \<subseteq> f-``(K)"
        using preimage_ideal origin_ring.ideal_dest_subset
        unfolding origin_ring.primeIdeal_def by auto
      then have 
        "f``(f-``(J)) \<subseteq> f``(f-``(K)) \<or> f``(f-``(P)) \<subseteq> f``(f-``(K))"
        by blast
      with assms jp(1,2) have "J \<subseteq> K \<or> P \<subseteq> K" 
        using surj_image_vimage target_ring.ideal_dest_subset
        by auto
    }
    ultimately show "K\<triangleleft>\<^sub>pR\<^sub>t"
      unfolding target_ring.primeIdeal_def by auto
  }
qed

text\<open>If the homomorphism is surjective then the function
  that maps ideals in the target ring to their inverse images (in the source ring)
  is a bijection between prime ideals in the target ring and the prime ideals
  containing the kernel in the source ring. \<close>

corollary (in ring_homo) bij_prime_ideals:
  defines "F \<equiv> \<lambda>J\<in>target_ring.ideals. f-``(J)"
  assumes "f \<in> surj(R,S)"
  shows "restrict(F,{J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t}) \<in> 
    bij({J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t}, {J\<in>Pow(R). ker\<subseteq>J \<and> (J\<triangleleft>\<^sub>pR)})"
proof -
  let ?\<I>\<^sub>t = "target_ring.ideals"
  from assms have I: "F:?\<I>\<^sub>t \<rightarrow> {K\<in>\<I>. ker \<subseteq> K}"
    using ideal_quot_bijection bij_is_fun by simp 
  have II: "{J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t} \<subseteq> ?\<I>\<^sub>t"
    unfolding target_ring.primeIdeal_def by auto
  have III: "{J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t} \<subseteq> ?\<I>\<^sub>t" 
    unfolding target_ring.primeIdeal_def by auto
  with assms have "restrict(F,{J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t}) \<in> 
    bij({J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t}, F``{J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t})"
    using restrict_bij ideal_quot_bijection unfolding bij_def 
    by auto
  moreover have "{t\<in>Pow(R). ker\<subseteq>t \<and> (t\<triangleleft>\<^sub>pR)} = F``{J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t}"
  proof 
    { fix t assume "t \<in> F``{J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t}"
      with I III obtain q where "q\<in>Pow(S)" "q\<triangleleft>\<^sub>pR\<^sub>t" "t=F`(q)"
        using func_imagedef by auto 
      from \<open>q\<in>Pow(S)\<close> \<open>q\<triangleleft>\<^sub>pR\<^sub>t\<close> have "q\<in>?\<I>\<^sub>t" 
        unfolding target_ring.primeIdeal_def by auto
      with I have "F`(q) \<in> {K\<in>\<I>. ker \<subseteq> K}" using apply_funtype 
        by blast
      with assms \<open>q\<triangleleft>\<^sub>pR\<^sub>t\<close> \<open>t=F`(q)\<close> \<open>q\<in>?\<I>\<^sub>t\<close> \<open>t=F`(q)\<close> 
        have "t\<triangleleft>R" "t\<triangleleft>\<^sub>pR" "ker\<subseteq>t"
        using prime_ideal_quot_3 by simp_all
    } then show "F``{J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t} \<subseteq> {t\<in>Pow(R). ker\<subseteq>t \<and> (t\<triangleleft>\<^sub>pR)}"
      using origin_ring.ideal_dest_subset by blast
    { fix t assume "t\<in>{t\<in>Pow(R). ker\<subseteq>t \<and> (t\<triangleleft>\<^sub>pR)}"
      then have "t\<in>Pow(R)" "ker\<subseteq>t" "t\<triangleleft>\<^sub>pR" by auto
      then have tSet: "t \<in> {t\<in>\<I>. ker \<subseteq> t}" 
        unfolding origin_ring.primeIdeal_def by auto
      with assms have cont: "converse(F)`(t) \<in> ?\<I>\<^sub>t"
        using ideal_quot_bijection bij_converse_bij 
          apply_funtype bij_is_fun by blast
      moreover from assms tSet have "F`(converse(F)`(t)) = t"
        using ideal_quot_bijection right_inverse_bij by blast
      ultimately have "f-``(converse(F)`(t)) = t"
        using assms(1) by simp
      with assms II tSet \<open>t\<triangleleft>\<^sub>pR\<close> cont have "t \<in> F``{J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t}"
        using prime_ideal_quot_3 target_ring.ideal_dest_subset
          bij_val_image_vimage ideal_quot_bijection
        unfolding target_ring.primeIdeal_def by auto
    } thus "{t\<in>Pow(R). ker\<subseteq>t \<and> (t\<triangleleft>\<^sub>pR)} \<subseteq> F``{J\<in>Pow(S). J\<triangleleft>\<^sub>pR\<^sub>t}" 
      by auto
  qed
  ultimately show ?thesis by auto
qed
    
end
