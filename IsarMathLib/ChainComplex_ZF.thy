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

section \<open>Chain complexes of abelian groups\<close>

theory ChainComplex_ZF imports Group_ZF_6 IntDiv_ZF_IML

begin

text\<open>A \emph{chain complex} of abelian groups consists of a family of abelian groups
  $(C_n)_{n \in \mathbb{Z}}$ together with group homomorphisms
  $d_n \colon C_n \to C_{n-1}$, satisfying $d_{n-1} \circ d_n = 0$ for every
  $n \in \mathbb{Z}$ (i.e.\ the image of $d_n$ is contained in the kernel of
  $d_{n-1}$).  Here $C$ and $P$ are Isabelle-level functions $\mathbb{Z} \to
  \mathbf{Set}$ giving the carriers and operations, and $d$ is an
  Isabelle-level function giving the boundary maps.\<close>

definition (in int0) IsAchainComplex :: "[i\<Rightarrow>i, i\<Rightarrow>i, i\<Rightarrow>i] \<Rightarrow> o" where
  "IsAchainComplex(C, P, d) \<equiv>
    (\<forall>n \<in> int. IsAgroup(C(n), P(n)) \<and> (P(n)) {is commutative on} (C(n))) \<and>
    (\<forall>n \<in> int. Homomor(d(n), C(n), P(n), C(n \<rs> \<one>), P(n  \<rs> \<one>))) \<and>
    (\<forall>n \<in> int. (d(n))``(C(n)) \<subseteq>
      (d(n \<rs> \<one>))-``{TheNeutralElement(C(n  \<rs> \<one> \<rs> \<one>), P(n  \<rs> \<one> \<rs> \<one>))})"

text\<open>The locale \<open>chain_complex\<close> packages a fixed chain complex.\<close>

locale chain_complex = int0 +
  fixes C :: "i\<Rightarrow>i" and P :: "i\<Rightarrow>i" and d :: "i\<Rightarrow>i"
  assumes cplx: "IsAchainComplex(C, P, d)"

abbreviation (in chain_complex) zero_C
  where "zero_C \<equiv> \<lambda>n. TheNeutralElement(C(n),P(n))"

text\<open>Additive notation for the group operation at degree $n$:
  $x +_n y$ stands for $P_n(x,y)$.\<close>

abbreviation (in chain_complex) cgrp_add :: "[i, i, i] \<Rightarrow> i"
    ("_ \<ra>\<^bsub>_\<^esub> _" [65,65,66] 65) where
  "x \<ra>\<^bsub>n\<^esub> y \<equiv> P(n)`\<langle>x, y\<rangle>"

text\<open>Each $C_n$ is a group.\<close>

lemma (in chain_complex) cplx_group:
  assumes "n \<in> ints"
  shows "IsAgroup(C(n), P(n))"
  using assms cplx unfolding IsAchainComplex_def by auto

text\<open>Each $C_n$ is abelian.\<close>

lemma (in chain_complex) cplx_abelian:
  assumes "n \<in> ints"
  shows "(P(n)) {is commutative on} (C(n))"
  using assms cplx unfolding IsAchainComplex_def by auto

text\<open>The boundary map $d_n$ is a group homomorphism from $C_n$ to $C_{n-1}$.\<close>

lemma (in chain_complex) cplx_hom:
  assumes "n \<in> ints"
  shows "Homomor(d(n), C(n), P(n), C(n \<rs>\<one>), P(n \<rs>\<one>))"
  using assms cplx unfolding IsAchainComplex_def by auto

text\<open>The image of $d_n$ is contained in the kernel of $d_{n-1}$:
  the boundary-squared-zero condition.\<close>

lemma (in chain_complex) bnd_sq_zero:
  assumes "n \<in> ints"
  shows "(d(n))``(C(n)) \<subseteq>
    (d(n\<rs>\<one>))-``{zero_C(n \<rs>\<one>\<rs>\<one>)}"
  using assms cplx unfolding IsAchainComplex_def by auto

text\<open>For any $x \in C_n$, applying $d_{n-1}$ to $d_n(x)$ gives the neutral element
  of $C_{n-2}$.\<close>

lemma (in chain_complex) bnd_sq_zero_elem:
  assumes "n \<in> ints" and "x \<in> C(n)"
  shows "d(n \<rs> \<one>)`(d(n)`x) = zero_C(n \<rs> \<one>\<rs> \<one>)"
proof -
  from assms(1) have pn: "n\<rs> \<one> \<in> int" using Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by simp
  from assms(1) have fn: "d(n) : C(n) \<rightarrow> C(n \<rs> \<one>)"
    using cplx_hom isub_def Int_ZF_1_L10 unfolding Homomor_def by simp
  from fn assms(2) have bx: "d(n)`x \<in> C(n \<rs>\<one>)" using apply_type by simp
  from fn assms(2) have "d(n)`x \<in> (d(n))``(C(n))"
    using func_imagedef by auto
  with bnd_sq_zero[OF assms(1)] have
    mem: "d(n)`x \<in> (d(n \<rs>\<one>))-``{zero_C(n \<rs>\<one>\<rs>\<one>)}"
    by auto
  from pn have fpn: "d(n \<rs>\<one>) : C(n \<rs>\<one>) \<rightarrow> C(n \<rs>\<one>\<rs>\<one>)"
    using cplx_hom unfolding Homomor_def by simp
  from fpn bx mem show ?thesis using func1_1_L15 by auto
qed

text\<open>The composition $d_{n-1} \circ d_n$ is the constant zero map on $C_n$.\<close>

lemma (in chain_complex) bnd_sq_zero_2:
  assumes "n \<in> int"
  shows "d(n \<rs> \<one>) O d(n) =
         ConstantFunction(C(n), zero_C(n \<rs> \<one>\<rs> \<one>))"
proof -
  let ?e = "zero_C(n \<rs> \<one>\<rs> \<one>)"
  from assms have pn: "n \<rs> \<one> \<in> ints"
    using Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by simp
  from pn have ppn: "n \<rs> \<one> \<rs> \<one> \<in> ints"
    using Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by simp
  from assms have fn: "d(n) : C(n) \<rightarrow> C(n \<rs> \<one>)"
    using cplx_hom unfolding Homomor_def by simp
  from pn have fpn: "d(n \<rs> \<one>) : C(n \<rs> \<one>) \<rightarrow> C(n\<rs> \<one>\<rs> \<one>)"
    using cplx_hom unfolding Homomor_def by simp
  from fn fpn have lhs_fun: "d(n\<rs> \<one>) O d(n) : C(n) \<rightarrow> C(n \<rs> \<one>\<rs> \<one>)"
    using comp_fun by simp
  from ppn have grp: "IsAgroup(C(n\<rs> \<one>\<rs> \<one>), P(n \<rs> \<one>\<rs> \<one>))"
    using cplx_group by simp
  from grp have eC: "?e \<in> C(n \<rs> \<one>\<rs> \<one>)"
    using group0.group0_2_L2 unfolding group0_def by auto
  from eC have rhs_fun: "ConstantFunction(C(n), ?e) : C(n) \<rightarrow> C(n \<rs> \<one>\<rs> \<one>)"
    using func1_3_L1 by simp
  show ?thesis
  proof (rule fun_extension[OF lhs_fun rhs_fun])
    fix x assume xn: "x \<in> C(n)"
    have "(d(n \<rs> \<one>) O d(n))`x = d(n \<rs> \<one>)`(d(n)`x)"
      using comp_fun_apply fn fpn xn by simp
    also have "\<dots> = ?e" using bnd_sq_zero_elem assms xn by simp
    also have "\<dots> = ConstantFunction(C(n), ?e)`x"
      using func1_3_L2 xn by simp
    finally show "(d(n \<rs> \<one>) O d(n))`x = ConstantFunction(C(n), ?e)`x" .
  qed
qed

subsection \<open>Chain maps\<close>

text\<open>A \emph{chain map} between two chain complexes is a family of group
  homomorphisms $f_n \colon C_n \to C'_n$ that commute with the boundary
  maps: $d'_n \circ f_n = f_{n-1} \circ d_n$ for every $n \in \mathbb{Z}$.\<close>

definition (in int0) IsAchainMap ::
  "[i\<Rightarrow>i, i\<Rightarrow>i, i\<Rightarrow>i, i\<Rightarrow>i, i\<Rightarrow>i, i\<Rightarrow>i, i\<Rightarrow>i] \<Rightarrow> o" where
  "IsAchainMap(f, C, P, d, C', P', d') \<equiv>
     (\<forall>n \<in> int. Homomor(f(n), C(n), P(n), C'(n), P'(n))) \<and>
     (\<forall>n \<in> int. d'(n) O f(n) = f(n \<rs> \<one>) O d(n))"

text\<open>The locale \<open>chain_map\<close> packages two fixed chain complexes and a chain
  map between them.\<close>

locale chain_map = int0 +
  fixes C  :: "i\<Rightarrow>i" and P  :: "i\<Rightarrow>i" and d  :: "i\<Rightarrow>i"
    and C' :: "i\<Rightarrow>i" and P' :: "i\<Rightarrow>i" and d' :: "i\<Rightarrow>i"
    and f  :: "i\<Rightarrow>i"
  assumes src_cplx: "IsAchainComplex(C, P, d)"
    and   tgt_cplx: "IsAchainComplex(C', P', d')"
    and   cmap:     "IsAchainMap(f, C, P, d, C', P', d')"

sublocale chain_map \<subseteq> src: chain_complex
  using src_cplx by unfold_locales

sublocale chain_map \<subseteq> tgt: chain_complex where C=C' and P=P' and d=d'
  using tgt_cplx by unfold_locales

text\<open>Each component $f_n$ is a group homomorphism.\<close>

lemma (in chain_map) cmap_hom:
  assumes "n \<in> ints"
  shows "Homomor(f(n), C(n), P(n), C'(n), P'(n))"
  using assms cmap unfolding IsAchainMap_def by auto

text\<open>The chain map commutes with the boundary maps.\<close>

lemma (in chain_map) cmap_comm:
  assumes "n \<in> ints"
  shows "d'(n) O f(n) = f(n \<rs> \<one>) O d(n)"
  using assms cmap unfolding IsAchainMap_def by auto


end
