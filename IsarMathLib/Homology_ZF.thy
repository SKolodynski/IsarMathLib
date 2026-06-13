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

section \<open>Homology groups\<close>

theory Homology_ZF imports ChainComplex_ZF

begin

text \<open>The \emph{cycles} at degree $n$ are the kernel of the boundary map $d_n$,
  i.e.\ the elements of $C_n$ that are sent to zero by $d_n$.
  The \emph{boundaries} at degree $n$ are the image of the boundary map $d_{n+1}$,
  i.e.\ elements of $C_n$ of the form $d_{n+1}(x)$ for some $x \in C_{n+1}$.
  The chain complex condition $d_n \circ d_{n+1} = 0$ implies that every boundary
  is a cycle.  The $n$-th \emph{homology group} is the quotient $Z_n / B_n$ of
  cycles by boundaries.\<close>

abbreviation (in chain_complex) Cycles :: "i \<Rightarrow> i" where
  "Cycles(n) \<equiv> (d(n))-``{zero_C(n \<rs> \<one>)}"

abbreviation (in chain_complex) Boundaries :: "i \<Rightarrow> i" where
  "Boundaries(n) \<equiv> (d(n \<ra> \<one>))``(C(n \<ra> \<one>))"

text \<open>We denote the restriction of the group operation $P(n)$ to the cycles by
  \<open>CycleOp(n)\<close>.  This is the operation that makes $Z_n$ a group in its own right.\<close>

abbreviation (in chain_complex) CycleOp :: "i \<Rightarrow> i" where
  "CycleOp(n) \<equiv> restrict(P(n), Cycles(n) \<times> Cycles(n))"

text \<open>The carrier of the $n$-th homology group is the quotient set
  $Z_n / B_n = Z_n / \!\sim$, where $x \sim y$ iff $x - y \in B_n$.\<close>

definition (in chain_complex) Hn :: "i \<Rightarrow> i" where
  "Hn(n) \<equiv> Cycles(n) // QuotientGroupRel(Cycles(n), CycleOp(n), Boundaries(n))"

definition (in chain_complex) HnOp :: "i \<Rightarrow> i" where
  "HnOp(n) \<equiv> QuotientGroupOp(Cycles(n), CycleOp(n), Boundaries(n))"

text \<open>The key structural fact: every boundary is a cycle.  This is a direct
  consequence of the boundary-squared-zero condition in the chain complex.\<close>

lemma (in chain_complex) boundaries_in_cycles:
  assumes "n \<in> \<int>"
  shows "Boundaries(n) \<subseteq> Cycles(n)"
proof -
  have np: "n \<ra> \<one> \<in> \<int>"
    using assms Int_ZF_1_L8A(2) Int_ZF_1_T2(3) group0.group_op_closed by simp
  have arith1: "(n \<ra> \<one>) \<rs> \<one> = n"
    using Int_ZF_1_L8A(2) group0.inv_cancel_two(2)[OF Int_ZF_1_T2(3)] assms by simp
  have arith2: "(n \<ra> \<one>) \<rs> \<one> \<rs> \<one> = n \<rs> \<one>"
    using arith1 by simp
  from bnd_sq_zero[OF np] arith1 arith2 show ?thesis
    by (simp add: Int_ZF_1_L8 Int_ZF_1_L10)
qed

text \<open>Cycles at degree $n$ form a subgroup of $C_n$.\<close>

lemma (in chain_complex) cycles_is_subgroup:
  assumes "n \<in> \<int>"
  shows "IsAsubgroup(Cycles(n), P(n))"
proof -
  have pn: "n \<rs> \<one> \<in> \<int>"
    using assms Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by simp
  interpret dn: group_homo "C(n)" "P(n)" "C(n \<rs> \<one>)" "P(n \<rs> \<one>)" "d(n)"
    "TheNeutralElement(C(n), P(n))" "\<lambda>x y. P(n)`\<langle>x, y\<rangle>"
    "\<lambda>x. GroupInv(C(n), P(n))`x"
    "\<lambda>s. Fold(P(n), TheNeutralElement(C(n), P(n)), s)"
    "\<lambda>m x. Fold(P(n), TheNeutralElement(C(n), P(n)), {\<langle>k, x\<rangle>. k \<in> m})"
    "TheNeutralElement(C(n \<rs> \<one>), P(n \<rs> \<one>))" "\<lambda>x y. P(n \<rs> \<one>)`\<langle>x, y\<rangle>"
    "\<lambda>x. GroupInv(C(n \<rs> \<one>), P(n \<rs> \<one>))`x"
    "\<lambda>s. Fold(P(n \<rs> \<one>), TheNeutralElement(C(n \<rs> \<one>), P(n \<rs> \<one>)), s)"
    "\<lambda>m x. Fold(P(n \<rs> \<one>), TheNeutralElement(C(n \<rs> \<one>), P(n \<rs> \<one>)), {\<langle>k, x\<rangle>. k \<in> m})"
    using cplx_group[OF assms] cplx_group[OF pn] cplx_hom[OF assms]
    unfolding group_homo_def by simp
  from dn.kernel_is_subgroup show ?thesis by simp
qed

text \<open>Cycles at degree $n$ form a group (with the restricted operation).\<close>

lemma (in chain_complex) cycles_is_group:
  assumes "n \<in> \<int>"
  shows "IsAgroup(Cycles(n), CycleOp(n))"
  using cycles_is_subgroup[OF assms] unfolding IsAsubgroup_def by simp

text \<open>The cycle group at degree $n$ is abelian, inheriting commutativity from $C_n$.\<close>

lemma (in chain_complex) cycles_is_abelian:
  assumes "n \<in> \<int>"
  shows "CycleOp(n) {is commutative on} Cycles(n)"
proof -
  have pn_fun: "P(n) : C(n) \<times> C(n) \<rightarrow> C(n)"
    using cplx_group[OF assms]
     group0.group_oper_fun unfolding group0_def by auto
  have sub: "Cycles(n) \<subseteq> C(n)"
    using cycles_is_subgroup[OF assms] cplx_group[OF assms]
    group0.group0_3_L2 unfolding group0_def by auto
  from func_ZF_4_L1[OF pn_fun sub cplx_abelian[OF assms]]
  show ?thesis by simp
qed

text \<open>Boundaries at degree $n$ form a subgroup of the ambient group $C_n$.\<close>

lemma (in chain_complex) boundaries_subgroup_ambient:
  assumes "n \<in> \<int>"
  shows "IsAsubgroup(Boundaries(n), P(n))"
proof -
  have np: "n \<ra> \<one> \<in> \<int>"
    using assms Int_ZF_1_L8A(2) Int_ZF_1_T2(3) group0.group_op_closed by simp
  have arith1: "(n \<ra> \<one>) \<rs> \<one> = n"
    using Int_ZF_1_L8A(2) group0.inv_cancel_two(2)[OF Int_ZF_1_T2(3)] assms by simp
  have ppn: "(n \<ra> \<one>) \<rs> \<one> \<in> \<int>" using arith1 assms by simp
  interpret dn1: group_homo "C(n \<ra> \<one>)" "P(n \<ra> \<one>)"
    "C((n \<ra> \<one>) \<rs> \<one>)" "P((n \<ra> \<one>) \<rs> \<one>)" "d(n \<ra> \<one>)"
    "TheNeutralElement(C(n \<ra> \<one>), P(n \<ra> \<one>))" "\<lambda>x y. P(n \<ra> \<one>)`\<langle>x, y\<rangle>"
    "\<lambda>x. GroupInv(C(n \<ra> \<one>), P(n \<ra> \<one>))`x"
    "\<lambda>s. Fold(P(n \<ra> \<one>), TheNeutralElement(C(n \<ra> \<one>), P(n \<ra> \<one>)), s)"
    "\<lambda>m x. Fold(P(n \<ra> \<one>), TheNeutralElement(C(n \<ra> \<one>), P(n \<ra> \<one>)), {\<langle>k, x\<rangle>. k \<in> m})"
    "TheNeutralElement(C((n \<ra> \<one>) \<rs> \<one>), P((n \<ra> \<one>) \<rs> \<one>))"
    "\<lambda>x y. P((n \<ra> \<one>) \<rs> \<one>)`\<langle>x, y\<rangle>"
    "\<lambda>x. GroupInv(C((n \<ra> \<one>) \<rs> \<one>), P((n \<ra> \<one>) \<rs> \<one>))`x"
    "\<lambda>s. Fold(P((n \<ra> \<one>) \<rs> \<one>), TheNeutralElement(C((n \<ra> \<one>) \<rs> \<one>), P((n \<ra> \<one>) \<rs> \<one>)), s)"
    "\<lambda>m x. Fold(P((n \<ra> \<one>) \<rs> \<one>), TheNeutralElement(C((n \<ra> \<one>) \<rs> \<one>), P((n \<ra> \<one>) \<rs> \<one>)),
             {\<langle>k, x\<rangle>. k \<in> m})"
    using cplx_group[OF np] cplx_group[OF ppn] cplx_hom[OF np]
    unfolding group_homo_def by simp
  from dn1.image_is_group have "IsAsubgroup(Boundaries(n), P((n \<ra> \<one>) \<rs> \<one>))"
    by simp
  with arith1 show ?thesis by simp
qed

text \<open>Boundaries at degree $n$ form a subgroup of the cycle group $Z_n$.\<close>

lemma (in chain_complex) boundaries_subgroup_cycles:
  assumes "n \<in> \<int>"
  shows "IsAsubgroup(Boundaries(n), CycleOp(n))"
proof -
  have bc: "Boundaries(n) \<subseteq> Cycles(n)"
    using boundaries_in_cycles[OF assms] by simp
  have bsub: "IsAsubgroup(Boundaries(n), P(n))"
    using boundaries_subgroup_ambient[OF assms] by simp
  have inter: "Cycles(n) \<times> Cycles(n) \<inter> Boundaries(n) \<times> Boundaries(n) =
               Boundaries(n) \<times> Boundaries(n)"
    using bc by auto
  from bsub inter show ?thesis using restrict_restrict
    unfolding IsAsubgroup_def
    by simp
qed

subsection \<open>The $n$-th homology group\<close>

text \<open>The $n$-th homology group $H_n = Z_n / B_n$ is a group.\<close>

theorem (in chain_complex) Hn_is_group:
  assumes "n \<in> \<int>"
  shows "IsAgroup(Hn(n), HnOp(n))"
proof -
  have normal: "IsAnormalSubgroup(Cycles(n), CycleOp(n), Boundaries(n))"
    using Group_ZF_2_4_L6(1)[OF cycles_is_group[OF assms]
                               cycles_is_abelian[OF assms]
                               boundaries_subgroup_cycles[OF assms]] by simp
  from Group_ZF_2_4_T1[OF cycles_is_group[OF assms] normal]
  show ?thesis unfolding Hn_def HnOp_def by simp
qed

text \<open>The $n$-th homology group is abelian, as a quotient of the abelian cycle group.\<close>

theorem (in chain_complex) Hn_is_abelian:
  assumes "n \<in> \<int>"
  shows "HnOp(n) {is commutative on} Hn(n)"
proof -
  from Group_ZF_2_4_L6(2)[OF cycles_is_group[OF assms]
                             cycles_is_abelian[OF assms]
                             boundaries_subgroup_cycles[OF assms]]
  show ?thesis unfolding HnOp_def Hn_def by simp
qed

subsection \<open>Chain maps induce homomorphisms on homology\<close>

text\<open>A chain map sends cycles to cycles: $d_n(z)=0$ implies $d'_n(f_n(z))=0$.\<close>

lemma (in chain_map) cmap_maps_cycles:
  assumes "n \<in> ints" and "z \<in> src.Cycles(n)"
  shows "f(n)`z \<in> tgt.Cycles(n)"
proof -
  have pn: "n \<rs> \<one> \<in> ints"
    using assms(1) Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by simp
  have fn: "f(n) : C(n) \<rightarrow> C'(n)"
    using cmap_hom[OF assms(1)] unfolding Homomor_def by simp
  have fnp: "f(n \<rs> \<one>) : C(n \<rs> \<one>) \<rightarrow> C'(n \<rs> \<one>)"
    using cmap_hom[OF pn] unfolding Homomor_def by simp
  have dn: "d(n) : C(n) \<rightarrow> C(n \<rs> \<one>)"
    using src.cplx_hom[OF assms(1)] unfolding Homomor_def by simp
  have dn': "d'(n) : C'(n) \<rightarrow> C'(n \<rs> \<one>)"
    using tgt.cplx_hom[OF assms(1)] unfolding Homomor_def by simp
  from assms(2) have zC: "z \<in> C(n)" and dzn: "d(n)`z = src.zero_C(n \<rs> \<one>)"
    using func1_1_L15[OF dn] by auto
  from fn zC have fzC': "f(n)`z \<in> C'(n)" using apply_type by simp
  interpret fn_m1: group_homo
    "C(n \<rs> \<one>)" "P(n \<rs> \<one>)" "C'(n \<rs> \<one>)" "P'(n \<rs> \<one>)" "f(n \<rs> \<one>)"
    "TheNeutralElement(C(n \<rs> \<one>), P(n \<rs> \<one>))"
    "\<lambda>x y. P(n \<rs> \<one>)`\<langle>x, y\<rangle>"
    "\<lambda>x. GroupInv(C(n \<rs> \<one>), P(n \<rs> \<one>))`x"
    "\<lambda>s. Fold(P(n \<rs> \<one>), TheNeutralElement(C(n \<rs> \<one>), P(n \<rs> \<one>)), s)"
    "\<lambda>m x. Fold(P(n \<rs> \<one>), TheNeutralElement(C(n \<rs> \<one>), P(n \<rs> \<one>)), {\<langle>k, x\<rangle>. k \<in> m})"
    "TheNeutralElement(C'(n \<rs> \<one>), P'(n \<rs> \<one>))"
    "\<lambda>x y. P'(n \<rs> \<one>)`\<langle>x, y\<rangle>"
    "\<lambda>x. GroupInv(C'(n \<rs> \<one>), P'(n \<rs> \<one>))`x"
    "\<lambda>s. Fold(P'(n \<rs> \<one>), TheNeutralElement(C'(n \<rs> \<one>), P'(n \<rs> \<one>)), s)"
    "\<lambda>m x. Fold(P'(n \<rs> \<one>), TheNeutralElement(C'(n \<rs> \<one>), P'(n \<rs> \<one>)), {\<langle>k, x\<rangle>. k \<in> m})"
    using src.cplx_group[OF pn] tgt.cplx_group[OF pn] cmap_hom[OF pn]
    unfolding group_homo_def by simp
  have key: "d'(n)`(f(n)`z) = tgt.zero_C(n \<rs> \<one>)"
  proof -
    have eq1: "(d'(n) O f(n))`z = d'(n)`(f(n)`z)"
      using comp_fun_apply fn dn' zC by simp
    have eq2: "(f(n \<rs> \<one>) O d(n))`z = f(n \<rs> \<one>)`(d(n)`z)"
      using comp_fun_apply dn fnp zC by simp
    have eq3: "d'(n) O f(n) = f(n \<rs> \<one>) O d(n)"
      using cmap_comm[OF assms(1)] by simp
    from eq1 eq2 eq3 have "d'(n)`(f(n)`z) = f(n \<rs> \<one>)`(d(n)`z)" by simp
    with dzn fn_m1.f_neutral show ?thesis by simp
  qed
  from fzC' key show ?thesis using func1_1_L15[OF dn'] by auto
qed

text\<open>A chain map sends boundaries to boundaries: the image of $d_{n+1}$
  maps into the image of $d'_{n+1}$.\<close>

lemma (in chain_map) cmap_maps_boundaries:
  assumes "n \<in> ints" and "z \<in> src.Boundaries(n)"
  shows "f(n)`z \<in> tgt.Boundaries(n)"
proof -
  have np: "n \<ra> \<one> \<in> ints"
    using assms(1) Int_ZF_1_L8A(2) Int_ZF_1_T2(3) group0.group_op_closed by simp
  have arith1: "(n \<ra> \<one>) \<rs> \<one> = n"
    using Int_ZF_1_L8A(2) group0.inv_cancel_two(2)[OF Int_ZF_1_T2(3)] assms(1) by simp
  have dnp: "d(n \<ra> \<one>) : C(n \<ra> \<one>) \<rightarrow> C(n)"
    using src.cplx_hom[OF np] arith1 unfolding Homomor_def by simp
  have dnp': "d'(n \<ra> \<one>) : C'(n \<ra> \<one>) \<rightarrow> C'(n)"
    using tgt.cplx_hom[OF np] arith1 unfolding Homomor_def by simp
  have fn: "f(n) : C(n) \<rightarrow> C'(n)"
    using cmap_hom[OF assms(1)] unfolding Homomor_def by simp
  have fnp: "f(n \<ra> \<one>) : C(n \<ra> \<one>) \<rightarrow> C'(n \<ra> \<one>)"
    using cmap_hom[OF np] unfolding Homomor_def by simp
  have comm_np: "d'(n \<ra> \<one>) O f(n \<ra> \<one>) = f(n) O d(n \<ra> \<one>)"
    using cmap_comm[OF np] arith1 by simp
  from assms(2) obtain b where bC: "b \<in> C(n \<ra> \<one>)" and zb: "z = d(n \<ra> \<one>)`b"
    using func_imagedef[OF dnp] by auto
  from bC fnp have fbC': "f(n \<ra> \<one>)`b \<in> C'(n \<ra> \<one>)" using apply_type by simp
  have key: "f(n)`z = d'(n \<ra> \<one>)`(f(n \<ra> \<one>)`b)"
  proof -
    have "f(n)`z = f(n)`(d(n \<ra> \<one>)`b)" using zb by simp
    also have "\<dots> = (f(n) O d(n \<ra> \<one>))`b"
      using comp_fun_apply dnp fn bC by simp
    also have "\<dots> = (d'(n \<ra> \<one>) O f(n \<ra> \<one>))`b"
      using comm_np by simp
    also have "\<dots> = d'(n \<ra> \<one>)`(f(n \<ra> \<one>)`b)"
      using comp_fun_apply fnp dnp' bC by simp
    finally show ?thesis .
  qed
  have img: "(d'(n \<ra> \<one>))``(C'(n \<ra> \<one>)) = {d'(n \<ra> \<one>)`x. x \<in> C'(n \<ra> \<one>)}"
    using func_imagedef[OF dnp' subset_refl] by simp
  from fbC' key img show ?thesis by auto
qed

text\<open>The map on homology induced by a chain map $f$: it sends the class $[z]$
  in $H_n(C)$ to the class $[f_n(z)]$ in $H_n(C')$.\<close>

definition (in chain_map) Hn_map :: "i \<Rightarrow> i" where
  "Hn_map(n) \<equiv>
    {\<langle>QuotientGroupRel(src.Cycles(n), src.CycleOp(n), src.Boundaries(n))``{z},
       QuotientGroupRel(tgt.Cycles(n), tgt.CycleOp(n), tgt.Boundaries(n))``{f(n)`z}\<rangle>.
     z \<in> src.Cycles(n)}"

text\<open>The map induced by a chain map is a group homomorphism $H_n(C) \to H_n(C')$.\<close>

theorem (in chain_map) Hn_map_is_hom:
  assumes "n \<in> ints"
  shows "Homomor(Hn_map(n), src.Hn(n), src.HnOp(n), tgt.Hn(n), tgt.HnOp(n))"
proof -
  let ?Rs = "QuotientGroupRel(src.Cycles(n), src.CycleOp(n), src.Boundaries(n))"
  let ?Rt = "QuotientGroupRel(tgt.Cycles(n), tgt.CycleOp(n), tgt.Boundaries(n))"
  let ?M = "Hn_map(n)"
  have M_eq: "?M = {\<langle>?Rs``{z}, ?Rt``{f(n)`z}\<rangle>. z \<in> src.Cycles(n)}"
    unfolding Hn_map_def by simp
  have normal_s: "IsAnormalSubgroup(src.Cycles(n), src.CycleOp(n), src.Boundaries(n))"
    using Group_ZF_2_4_L6(1)[OF src.cycles_is_group[OF assms]
                                     src.cycles_is_abelian[OF assms]
                                     src.boundaries_subgroup_cycles[OF assms]] by simp
  have normal_t: "IsAnormalSubgroup(tgt.Cycles(n), tgt.CycleOp(n), tgt.Boundaries(n))"
    using Group_ZF_2_4_L6(1)[OF tgt.cycles_is_group[OF assms]
                                     tgt.cycles_is_abelian[OF assms]
                                     tgt.boundaries_subgroup_cycles[OF assms]] by simp
  have equiv_s: "equiv(src.Cycles(n), ?Rs)"
    using src.cycles_is_subgroup[OF assms] group0.Group_ZF_2_4_L3[OF _ src.boundaries_subgroup_cycles[OF assms],
        of "src.Cycles(n)"]
    unfolding IsAsubgroup_def group0_def by auto
  have equiv_t: "equiv(tgt.Cycles(n), ?Rt)"
    using tgt.cycles_is_subgroup[OF assms] group0.Group_ZF_2_4_L3[OF _ tgt.boundaries_subgroup_cycles[OF assms]]
    unfolding IsAsubgroup_def group0_def by simp
  have cong_s: "Congruent2(?Rs, src.CycleOp(n))"
    using Group_ZF_2_4_L5A src.cycles_is_group[OF assms] normal_s by simp
  have cong_t: "Congruent2(?Rt, tgt.CycleOp(n))"
    using Group_ZF_2_4_L5A tgt.cycles_is_group[OF assms] normal_t by simp
  have fn: "f(n) : C(n) \<rightarrow> C'(n)"
    using cmap_hom[OF assms] unfolding Homomor_def by simp
  interpret Cn: group0 "C(n)" "P(n)" "src.zero_C(n)" "\<lambda>x y. P(n)`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(C(n),P(n))`x" "\<lambda>s. Fold(P(n), src.zero_C(n), s)"
    "\<lambda>na x. Fold(P(n), src.zero_C(n), {\<langle>k, x\<rangle>. k \<in> na})"
    using src.cplx_group[OF assms] unfolding group0_def by simp
  interpret Cn': group0 "C'(n)" "P'(n)" "tgt.zero_C(n)" "\<lambda>x y. P'(n)`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(C'(n),P'(n))`x" "\<lambda>s. Fold(P'(n), tgt.zero_C(n), s)"
    "\<lambda>na x. Fold(P'(n), tgt.zero_C(n), {\<langle>k, x\<rangle>. k \<in> na})"
    using tgt.cplx_group[OF assms] unfolding group0_def by simp
  interpret fn_homo: group_homo "C(n)" "P(n)" "C'(n)" "P'(n)" "f(n)"
    "TheNeutralElement(C(n), P(n))"
    "\<lambda>x y. P(n)`\<langle>x, y\<rangle>"
    "\<lambda>x. GroupInv(C(n), P(n))`x"
    "\<lambda>s. Fold(P(n), TheNeutralElement(C(n), P(n)), s)"
    "\<lambda>m x. Fold(P(n), TheNeutralElement(C(n), P(n)), {\<langle>k, x\<rangle>. k \<in> m})"
    "TheNeutralElement(C'(n), P'(n))"
    "\<lambda>x y. P'(n)`\<langle>x, y\<rangle>"
    "\<lambda>x. GroupInv(C'(n), P'(n))`x"
    "\<lambda>s. Fold(P'(n), TheNeutralElement(C'(n), P'(n)), s)"
    "\<lambda>m x. Fold(P'(n), TheNeutralElement(C'(n), P'(n)), {\<langle>k, x\<rangle>. k \<in> m})"
    using src.cplx_group[OF assms] tgt.cplx_group[OF assms] cmap_hom[OF assms]
    unfolding group_homo_def by simp
  have sub_s: "src.Cycles(n) \<subseteq> C(n)"
    using src.cycles_is_subgroup[OF assms] Cn.group0_3_L2 by simp
  have sub_t: "tgt.Cycles(n) \<subseteq> C'(n)"
    using tgt.cycles_is_subgroup[OF assms] Cn'.group0_3_L2 by simp
  have inv_in_cycles_s: "\<forall>h \<in> src.Cycles(n). GroupInv(src.Cycles(n), src.CycleOp(n))`h = GroupInv(C(n), P(n))`h"
    using Cn.group0_3_T2[OF src.cycles_is_subgroup[OF assms]] by blast
  have inv_in_cycles_t: "\<forall>h \<in> tgt.Cycles(n). GroupInv(tgt.Cycles(n), tgt.CycleOp(n))`h = GroupInv(C'(n), P'(n))`h"
    using Cn'.group0_3_T2[OF tgt.cycles_is_subgroup[OF assms]] by blast
  have M_subset: "?M \<in> Pow(src.Hn(n) \<times> tgt.Hn(n))"
  proof(safe)
    fix p assume "p \<in> ?M"
    with M_eq obtain z where zZ: "z \<in> src.Cycles(n)"
      and p_eq: "p = \<langle>?Rs``{z}, ?Rt``{f(n)`z}\<rangle>" by auto
    from zZ equiv_s have Rs_cls: "?Rs``{z} \<in> src.Hn(n)"
      unfolding src.Hn_def quotient_def by auto
    from cmap_maps_cycles[OF assms zZ] equiv_t have Rt_cls: "?Rt``{f(n)`z} \<in> tgt.Hn(n)"
      unfolding tgt.Hn_def quotient_def by auto
    from p_eq Rs_cls Rt_cls show "p \<in> src.Hn(n) \<times> tgt.Hn(n)" by auto
  qed
  have M_dom: "src.Hn(n) \<subseteq> domain(?M)"
    using M_eq unfolding src.Hn_def quotient_def domain_def by auto
  have M_sv: "\<forall>A y t. \<langle>A,y\<rangle> \<in> ?M \<longrightarrow> \<langle>A,t\<rangle> \<in> ?M \<longrightarrow> y = t"
  proof (intro allI impI)
    fix A y t
    assume Ay: "\<langle>A,y\<rangle> \<in> ?M" and At: "\<langle>A,t\<rangle> \<in> ?M"
    from Ay M_eq obtain z\<^sub>y where zy: "z\<^sub>y \<in> src.Cycles(n)"
      and Ay_eq: "\<langle>A,y\<rangle> = \<langle>?Rs``{z\<^sub>y}, ?Rt``{f(n)`z\<^sub>y}\<rangle>" by auto
    from At M_eq obtain z\<^sub>t where zt: "z\<^sub>t \<in> src.Cycles(n)"
      and At_eq: "\<langle>A,t\<rangle> = \<langle>?Rs``{z\<^sub>t}, ?Rt``{f(n)`z\<^sub>t}\<rangle>" by auto
    from Ay_eq At_eq have cls_eq: "?Rs``{z\<^sub>y} = ?Rs``{z\<^sub>t}"
      and y_eq: "y = ?Rt``{f(n)`z\<^sub>y}" and t_eq: "t = ?Rt``{f(n)`z\<^sub>t}" by auto
    from equiv_s zt cls_eq have rel_yz: "\<langle>z\<^sub>y, z\<^sub>t\<rangle> \<in> ?Rs"
      using same_image_equiv by simp
    from rel_yz have diff_B:
      "src.CycleOp(n)`\<langle>z\<^sub>y, GroupInv(src.Cycles(n), src.CycleOp(n))`z\<^sub>t\<rangle> \<in> src.Boundaries(n)"
      unfolding QuotientGroupRel_def by auto
    from zt inv_in_cycles_s have inv_eq:
      "GroupInv(src.Cycles(n), src.CycleOp(n))`z\<^sub>t = GroupInv(C(n), P(n))`z\<^sub>t" by blast
    from zy zt sub_s have zy_C: "z\<^sub>y \<in> C(n)" and zt_C: "z\<^sub>t \<in> C(n)" by auto
    from zt_C have zinv_C: "GroupInv(C(n), P(n))`z\<^sub>t \<in> C(n)" using Cn.inverse_in_group by blast
    have "GroupInv(src.Cycles(n), src.CycleOp(n))`z\<^sub>t \<in> src.Cycles(n)"
      using group0.inverse_in_group[OF _ zt, of "restrict(P(n), src.Cycles(n) \<times> src.Cycles(n))"]
       src.cycles_is_group[OF assms] unfolding group0_def by auto
    with zy have "\<langle>z\<^sub>y,GroupInv(src.Cycles(n), src.CycleOp(n))`z\<^sub>t\<rangle>\<in>src.Cycles(n)\<times>src.Cycles(n)"
      by auto
    then have "(if (\<langle>z\<^sub>y,GroupInv(src.Cycles(n), src.CycleOp(n))`z\<^sub>t\<rangle>\<in>src.Cycles(n)\<times>src.Cycles(n)) then  (P(n) `\<langle>z\<^sub>y,GroupInv(src.Cycles(n), src.CycleOp(n))`z\<^sub>t\<rangle>) else 0) 
      = (P(n)`\<langle>z\<^sub>y,GroupInv(src.Cycles(n), src.CycleOp(n))`z\<^sub>t\<rangle>)"
      apply (simp only:) by (simp only:if_true)
    then have "restrict(P(n), src.Cycles(n) \<times> src.Cycles(n))`\<langle>z\<^sub>y,GroupInv(src.Cycles(n), src.CycleOp(n))`z\<^sub>t\<rangle> = 
      P(n)`\<langle>z\<^sub>y,GroupInv(src.Cycles(n), src.CycleOp(n))`z\<^sub>t\<rangle>"
      using restrict[of "P(n)" " src.Cycles(n) \<times> src.Cycles(n)" "\<langle>z\<^sub>y,GroupInv(src.Cycles(n), src.CycleOp(n))`z\<^sub>t\<rangle>"]
      by (simp only:)
    with inv_eq have cycle_op_eq:
      "src.CycleOp(n)`\<langle>z\<^sub>y, GroupInv(src.Cycles(n), src.CycleOp(n))`z\<^sub>t\<rangle> =
       P(n)`\<langle>z\<^sub>y, GroupInv(C(n), P(n))`z\<^sub>t\<rangle>"
      by (simp only:)
    from diff_B cycle_op_eq have diff_C:
      "P(n)`\<langle>z\<^sub>y, GroupInv(C(n), P(n))`z\<^sub>t\<rangle> \<in> src.Boundaries(n)" by (simp only:)
    from cmap_maps_boundaries[OF assms diff_C] have f_diff:
      "f(n)`(P(n)`\<langle>z\<^sub>y, GroupInv(C(n), P(n))`z\<^sub>t\<rangle>) \<in> tgt.Boundaries(n)" .
    from fn_homo.f_hom zy_C zinv_C have f_hom_step:
      "f(n)`(P(n)`\<langle>z\<^sub>y, GroupInv(C(n), P(n))`z\<^sub>t\<rangle>) = P'(n)`\<langle>f(n)`z\<^sub>y, f(n)`(GroupInv(C(n), P(n))`z\<^sub>t)\<rangle>"
      by (simp only:)
    from fn_homo.f_inv zt_C have f_inv_step:
      "f(n)`(GroupInv(C(n), P(n))`z\<^sub>t) = GroupInv(C'(n), P'(n))`(f(n)`z\<^sub>t)" by (simp only:)
    from f_diff f_hom_step f_inv_step have Rt_mem:
      "P'(n)`\<langle>f(n)`z\<^sub>y, GroupInv(C'(n), P'(n))`(f(n)`z\<^sub>t)\<rangle> \<in> tgt.Boundaries(n)" by (simp only:)
    from cmap_maps_cycles[OF assms zy] have fzy_tC: "f(n)`z\<^sub>y \<in> tgt.Cycles(n)" .
    from cmap_maps_cycles[OF assms zt] have fzt_tC: "f(n)`z\<^sub>t \<in> tgt.Cycles(n)" .
    from fzt_tC inv_in_cycles_t have tgt_inv_eq:
      "GroupInv(tgt.Cycles(n), tgt.CycleOp(n))`(f(n)`z\<^sub>t) = GroupInv(C'(n), P'(n))`(f(n)`z\<^sub>t)" by (simp only:)
    have "GroupInv(tgt.Cycles(n), tgt.CycleOp(n))`(f(n)`z\<^sub>t) \<in> tgt.Cycles(n)"
      using group0.inverse_in_group[OF _ fzt_tC, of "restrict(P'(n), tgt.Cycles(n) \<times> tgt.Cycles(n))"]
       tgt.cycles_is_group[OF assms] unfolding group0_def by (simp only:)
    with fzy_tC have "\<langle>f(n)`z\<^sub>y,GroupInv(tgt.Cycles(n), tgt.CycleOp(n))`(f(n)`z\<^sub>t)\<rangle>\<in>tgt.Cycles(n)\<times>tgt.Cycles(n)"
      by auto
    then have "(if (\<langle>f(n)`z\<^sub>y,GroupInv(tgt.Cycles(n), tgt.CycleOp(n))`(f(n)`z\<^sub>t)\<rangle>\<in>tgt.Cycles(n)\<times>tgt.Cycles(n)) then  (P'(n) `\<langle>f(n)`z\<^sub>y,GroupInv(tgt.Cycles(n), tgt.CycleOp(n))`(f(n)`z\<^sub>t)\<rangle>) else 0) 
      = (P'(n)`\<langle>f(n)`z\<^sub>y,GroupInv(tgt.Cycles(n), tgt.CycleOp(n))`(f(n)`z\<^sub>t)\<rangle>)"
      apply (simp only:) by (simp only:if_true)
    then have "restrict(P'(n), tgt.Cycles(n) \<times> tgt.Cycles(n))`\<langle>f(n)`z\<^sub>y,GroupInv(tgt.Cycles(n), tgt.CycleOp(n))`(f(n)`z\<^sub>t)\<rangle> = 
      P'(n)`\<langle>f(n)`z\<^sub>y,GroupInv(tgt.Cycles(n), tgt.CycleOp(n))`(f(n)`z\<^sub>t)\<rangle>"
      using restrict[of "P'(n)" "tgt.Cycles(n) \<times> tgt.Cycles(n)" "\<langle>f(n)`z\<^sub>y,GroupInv(tgt.Cycles(n), tgt.CycleOp(n))`(f(n)`z\<^sub>t)\<rangle>"]
      by (simp only:)
    with tgt_inv_eq have tgt_op_eq:
      "tgt.CycleOp(n)`\<langle>f(n)`z\<^sub>y, GroupInv(tgt.Cycles(n), tgt.CycleOp(n))`(f(n)`z\<^sub>t)\<rangle> =
       P'(n)`\<langle>f(n)`z\<^sub>y, GroupInv(C'(n), P'(n))`(f(n)`z\<^sub>t)\<rangle>"
      by (simp only:)
    with Rt_mem have "tgt.CycleOp(n)`\<langle>f(n)`z\<^sub>y, GroupInv(tgt.Cycles(n), tgt.CycleOp(n))`(f(n)`z\<^sub>t)\<rangle>\<in>tgt.Boundaries(n)"
      by (simp only:)
    then have Rt_rel: "\<langle>f(n)`z\<^sub>y, f(n)`z\<^sub>t\<rangle> \<in> ?Rt"
      using fzy_tC fzt_tC unfolding QuotientGroupRel_def by auto
    from equiv_t fzt_tC Rt_rel have "?Rt``{f(n)`z\<^sub>y} = ?Rt``{f(n)`z\<^sub>t}"
      using equiv_class_eq by simp
    with y_eq t_eq show "y = t" by simp
  qed
  from M_subset M_dom M_sv have M_fun: "?M : src.Hn(n) \<rightarrow> tgt.Hn(n)"
    unfolding Pi_def function_def by auto
  have morphism: "IsMorphism(src.Hn(n), src.HnOp(n), tgt.HnOp(n), ?M)"
    unfolding IsMorphism_def
  proof (intro ballI)
    fix A\<^sub>1 A\<^sub>2 assume A1: "A\<^sub>1 \<in> src.Hn(n)" and A2: "A\<^sub>2 \<in> src.Hn(n)"
    show "?M`(src.HnOp(n)`\<langle>A\<^sub>1, A\<^sub>2\<rangle>) = tgt.HnOp(n)`\<langle>?M`A\<^sub>1, ?M`A\<^sub>2\<rangle>"
    proof-
      from A1 obtain z\<^sub>1 where z1: "z\<^sub>1 \<in> src.Cycles(n)" and A1_eq: "A\<^sub>1 = ?Rs``{z\<^sub>1}"
        unfolding src.Hn_def quotient_def by auto
      from A2 obtain z\<^sub>2 where z2: "z\<^sub>2 \<in> src.Cycles(n)" and A2_eq: "A\<^sub>2 = ?Rs``{z\<^sub>2}"
        unfolding src.Hn_def quotient_def by auto
      from z1 M_eq A1_eq have pair1: "\<langle>A\<^sub>1, ?Rt``{f(n)`z\<^sub>1}\<rangle> \<in> ?M" by auto
      from z2 M_eq A2_eq have pair2: "\<langle>A\<^sub>2, ?Rt``{f(n)`z\<^sub>2}\<rangle> \<in> ?M" by auto
      from pair1 M_fun have step1: "?M`A\<^sub>1 = ?Rt``{f(n)`z\<^sub>1}"
        using apply_equality by simp
      from pair2 M_fun have step2: "?M`A\<^sub>2 = ?Rt``{f(n)`z\<^sub>2}"
        using apply_equality by simp
      from z1 z2 sub_s have z1C: "z\<^sub>1 \<in> C(n)" and z2C: "z\<^sub>2 \<in> C(n)" by auto
      have cycle_closed: "src.CycleOp(n)`\<langle>z\<^sub>1, z\<^sub>2\<rangle> \<in> src.Cycles(n)"
        using src.cycles_is_group[OF assms] z1 z2
          group0.group_op_closed unfolding group0_def by (simp only:)
      have op_s: "src.HnOp(n)`\<langle>A\<^sub>1, A\<^sub>2\<rangle> = ?Rs``{src.CycleOp(n)`\<langle>z\<^sub>1, z\<^sub>2\<rangle>}"
        using group0.Group_ZF_2_2_L2[OF _ equiv_s cong_s _ z1 z2] A1_eq A2_eq
        src.cycles_is_group[OF assms]
        unfolding src.HnOp_def QuotientGroupOp_def group0_def by auto
      from M_eq have "\<And>z. z\<in>src.Cycles(n) \<Longrightarrow> \<langle>?Rs``{z},?Rt``{f(n)`z}\<rangle>\<in>?M" by auto
      with cycle_closed have pair_prod:
        "\<langle>?Rs``{src.CycleOp(n)`\<langle>z\<^sub>1, z\<^sub>2\<rangle>}, ?Rt``{f(n)`(src.CycleOp(n)`\<langle>z\<^sub>1, z\<^sub>2\<rangle>)}\<rangle> \<in> ?M"
        by auto
      with op_s have "\<langle>src.HnOp(n)`\<langle>A\<^sub>1, A\<^sub>2\<rangle>, ?Rt``{f(n)`(src.CycleOp(n)`\<langle>z\<^sub>1, z\<^sub>2\<rangle>)}\<rangle> \<in> ?M"
        by auto
      with M_fun have step3:
        "?M`(src.HnOp(n)`\<langle>A\<^sub>1, A\<^sub>2\<rangle>) = ?Rt``{f(n)`(src.CycleOp(n)`\<langle>z\<^sub>1, z\<^sub>2\<rangle>)}"
        using apply_equality by (simp only:)
      from z1 z2 have "\<langle>z\<^sub>1,z\<^sub>2\<rangle>\<in>src.Cycles(n)\<times>src.Cycles(n)" by auto
      then have cycleop_eq: "src.CycleOp(n)`\<langle>z\<^sub>1, z\<^sub>2\<rangle> = P(n)`\<langle>z\<^sub>1, z\<^sub>2\<rangle>"
        using restrict[of "P(n)" "src.Cycles(n)\<times>src.Cycles(n)" "\<langle>z\<^sub>1,z\<^sub>2\<rangle>"] by (simp only:if_true)
      from fn_homo.f_hom z1C z2C have f_prod:
        "f(n)`(P(n)`\<langle>z\<^sub>1, z\<^sub>2\<rangle>) = P'(n)`\<langle>f(n)`z\<^sub>1, f(n)`z\<^sub>2\<rangle>" by (simp only:)
      from cmap_maps_cycles[OF assms z1] cmap_maps_cycles[OF assms z2] have
        fz1_tC: "f(n)`z\<^sub>1 \<in> tgt.Cycles(n)" and fz2_tC: "f(n)`z\<^sub>2 \<in> tgt.Cycles(n)" by simp_all
      from fz1_tC fz2_tC have "\<langle>f(n)`z\<^sub>1,f(n)`z\<^sub>2\<rangle>\<in>tgt.Cycles(n)\<times>tgt.Cycles(n)" by auto
      then have tgt_cycleop_eq:
        "tgt.CycleOp(n)`\<langle>f(n)`z\<^sub>1, f(n)`z\<^sub>2\<rangle> = P'(n)`\<langle>f(n)`z\<^sub>1, f(n)`z\<^sub>2\<rangle>"
        using restrict by (simp only:if_true)
      have op_t: "tgt.HnOp(n)`\<langle>?Rt``{f(n)`z\<^sub>1}, ?Rt``{f(n)`z\<^sub>2}\<rangle> =
                  ?Rt``{tgt.CycleOp(n)`\<langle>f(n)`z\<^sub>1, f(n)`z\<^sub>2\<rangle>}"
        using group0.Group_ZF_2_2_L2[OF _ equiv_t cong_t _ fz1_tC fz2_tC]
        tgt.cycles_is_group[OF assms]
        unfolding tgt.HnOp_def QuotientGroupOp_def group0_def by auto
      from step3 cycleop_eq f_prod tgt_cycleop_eq op_t step1 step2
      show "?M`(src.HnOp(n)`\<langle>A\<^sub>1, A\<^sub>2\<rangle>) = tgt.HnOp(n)`\<langle>?M`A\<^sub>1, ?M`A\<^sub>2\<rangle>"
        by (simp only:)
    qed
  qed
  from M_fun morphism show ?thesis unfolding Homomor_def by simp
qed


end
