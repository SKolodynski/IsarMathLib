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

section \<open>Exact sequences\<close>

theory ExactSequence_ZF imports Homology_ZF IntDiv_ZF_1

begin

text \<open>A chain complex is a \emph{long exact sequence} when boundaries equal cycles at
  every degree, i.e.\ $B_n = Z_n$ for all $n$.  Since $B_n \subseteq Z_n$ always holds
  (boundary-squared-zero), this is equivalent to requiring $Z_n \subseteq B_n$, which
  in turn means every cycle is a boundary, i.e.\ $H_n = 0$ for all $n$.\<close>

definition (in chain_complex) IsLongExactSequence :: "o" where
  "IsLongExactSequence \<equiv> \<forall>n \<in> \<int>. Boundaries(n) = Cycles(n)"

subsection \<open>Short exact sequences of chain complexes\<close>

text\<open>A \emph{short exact sequence of chain complexes} is a pair of chain maps
  $f \colon A \to B$ and $g \colon B \to C$ between chain complexes such that
  at each degree $n$ the sequence $0 \to A_n \to B_n \to C_n \to 0$ is
  a short exact sequence of abelian groups.\<close>

definition (in int0) IsASESofChainComplexes ::
  "[i\<Rightarrow>i, i\<Rightarrow>i, i\<Rightarrow>i, i\<Rightarrow>i, i\<Rightarrow>i, i\<Rightarrow>i, i\<Rightarrow>i, i\<Rightarrow>i, i\<Rightarrow>i, i\<Rightarrow>i, i\<Rightarrow>i] \<Rightarrow> o" where
  "IsASESofChainComplexes(A, PA, dA, f, B, PB, dB, g, C, PC, dC) \<equiv>
    IsAchainComplex(A, PA, dA) \<and>
    IsAchainComplex(B, PB, dB) \<and>
    IsAchainComplex(C, PC, dC) \<and>
    IsAchainMap(f, A, PA, dA, B, PB, dB) \<and>
    IsAchainMap(g, B, PB, dB, C, PC, dC) \<and>
    (\<forall>n \<in> int. IsAshortExactSequence(A(n), PA(n), B(n), PB(n), C(n), PC(n), f(n), g(n)))"

text\<open>The locale \<open>ses_chain_complex\<close> packages a short exact sequence of chain
  complexes $A \xrightarrow{f} B \xrightarrow{g} C$.\<close>

locale ses_chain_complex = int0 +
  fixes A  :: "i\<Rightarrow>i" and PA :: "i\<Rightarrow>i" and dA :: "i\<Rightarrow>i"
    and B  :: "i\<Rightarrow>i" and PB :: "i\<Rightarrow>i" and dB :: "i\<Rightarrow>i"
    and C  :: "i\<Rightarrow>i" and PC :: "i\<Rightarrow>i" and dC :: "i\<Rightarrow>i"
    and f  :: "i\<Rightarrow>i" and g  :: "i\<Rightarrow>i"
  assumes ses_cplx_A: "IsAchainComplex(A, PA, dA)"
    and   ses_cplx_B: "IsAchainComplex(B, PB, dB)"
    and   ses_cplx_C: "IsAchainComplex(C, PC, dC)"
    and   ses_map_f:  "IsAchainMap(f, A, PA, dA, B, PB, dB)"
    and   ses_map_g:  "IsAchainMap(g, B, PB, dB, C, PC, dC)"
    and   ses_exact:  "\<forall>n \<in> int. IsAshortExactSequence(A(n), PA(n), B(n), PB(n), C(n), PC(n), f(n), g(n))"

sublocale ses_chain_complex < ab: chain_map
  where C=A and P=PA and d=dA and C'=B and P'=PB and d'=dB and f=f
  using ses_cplx_A ses_cplx_B ses_map_f by unfold_locales

sublocale ses_chain_complex < bc: chain_map
  where C=B and P=PB and d=dB and C'=C and P'=PC and d'=dC and f=g
  using ses_cplx_B ses_cplx_C ses_map_g by unfold_locales

text\<open>At each degree $n$, the groups and maps form a short exact sequence.\<close>

lemma (in ses_chain_complex) deg_ses:
  assumes "n \<in> ints"
  shows "IsAshortExactSequence(A(n), PA(n), B(n), PB(n), C(n), PC(n), f(n), g(n))"
  using assms ses_exact by auto

text\<open>Additive notation for the three complexes: $x +^A_n y$, $x +^B_n y$, $x +^C_n y$.\<close>

abbreviation (in ses_chain_complex) ses_add_A :: "[i, i, i] \<Rightarrow> i"
    ("_ \<ra>\<^sup>A\<^bsub>_\<^esub> _" [65,65,66] 65) where
  "x \<ra>\<^sup>A\<^bsub>n\<^esub> y \<equiv> PA(n)`\<langle>x, y\<rangle>"

abbreviation (in ses_chain_complex) ses_add_B :: "[i, i, i] \<Rightarrow> i"
    ("_ \<ra>\<^sup>B\<^bsub>_\<^esub> _" [65,65,66] 65) where
  "x \<ra>\<^sup>B\<^bsub>n\<^esub> y \<equiv> PB(n)`\<langle>x, y\<rangle>"

abbreviation (in ses_chain_complex) ses_add_C :: "[i, i, i] \<Rightarrow> i"
    ("_ \<ra>\<^sup>C\<^bsub>_\<^esub> _" [65,65,66] 65) where
  "x \<ra>\<^sup>C\<^bsub>n\<^esub> y \<equiv> PC(n)`\<langle>x, y\<rangle>"

text\<open>Additive inverse notation for the three complexes: $-^A_n x$, $-^B_n x$, $-^C_n x$.\<close>

abbreviation (in ses_chain_complex) ses_inv_A :: "[i, i] \<Rightarrow> i"
    ("\<rm>\<^sup>A\<^bsub>_\<^esub> _" [65, 90] 80) where
  "\<rm>\<^sup>A\<^bsub>n\<^esub> x \<equiv> GroupInv(A(n), PA(n))`x"

abbreviation (in ses_chain_complex) ses_inv_B :: "[i, i] \<Rightarrow> i"
    ("\<rm>\<^sup>B\<^bsub>_\<^esub> _" [65, 90] 80) where
  "\<rm>\<^sup>B\<^bsub>n\<^esub> x \<equiv> GroupInv(B(n), PB(n))`x"

abbreviation (in ses_chain_complex) ses_inv_C :: "[i, i] \<Rightarrow> i"
    ("\<rm>\<^sup>C\<^bsub>_\<^esub> _" [65, 90] 80) where
  "\<rm>\<^sup>C\<^bsub>n\<^esub> x \<equiv> GroupInv(C(n), PC(n))`x"

subsection \<open>The connecting homomorphism\<close>

text\<open>For $b \in B_n$ with $g_n(b)$ a cycle in $C_n$, the element
  $d_n^B(b)$ lies in $\ker(g_{n-1}) = \mathrm{im}(f_{n-1})$, so there is a unique
  $a \in A_{n-1}$ with $f_{n-1}(a) = d_n^B(b)$.  This is the \emph{raw lift} $\delta_n^{\mathrm{raw}}(b)$.\<close>

definition (in ses_chain_complex) conn_lift :: "[i, i] \<Rightarrow> i" where
  "conn_lift(n, b) \<equiv> THE x. x \<in> A(n \<rs> \<one>) \<and> f(n \<rs> \<one>)`x = dB(n)`b"

text\<open>Helper: extract the degree-wise exactness and injectivity facts.\<close>

lemma (in ses_chain_complex) ses_hf:
  assumes "n \<in> ints"
  shows "group_homo(A(n), PA(n), B(n), PB(n), f(n))"
  using deg_ses[OF assms] unfolding IsAshortExactSequence_def by auto

lemma (in ses_chain_complex) ses_hg:
  assumes "n \<in> ints"
  shows "group_homo(B(n), PB(n), C(n), PC(n), g(n))"
  using deg_ses[OF assms] unfolding IsAshortExactSequence_def by auto

lemma (in ses_chain_complex) ses_f_inj:
  assumes "n \<in> ints"
  shows "f(n) \<in> inj(A(n), B(n))"
proof -
  have ses: "IsAshortExactSequence(A(n), PA(n), B(n), PB(n), C(n), PC(n), f(n), g(n))"
    using deg_ses[OF assms] .
  have ea: "IsExactAt(ZeroMap(1, A(n), PA(n)), 1, f(n), B(n), PB(n))"
    using ses unfolding IsAshortExactSequence_def by auto
  have grpA: "IsAgroup(A(n), PA(n))"
    using ses_hf[OF assms] unfolding group_homo_def by auto
  from ea 
  have "f(n)-``{TheNeutralElement(B(n), PB(n))} = {TheNeutralElement(A(n), PA(n))}"
    using ZeroMap_image[OF trivial_group grpA] unfolding IsExactAt_def by auto
  with group_homo.kernel_trivial_iff_injective[OF ses_hf[OF assms]]
  show ?thesis by simp
qed

lemma (in ses_chain_complex) ses_im_eq_ker:
  assumes "n \<in> ints"
  shows "f(n)``A(n) = g(n)-``{TheNeutralElement(C(n), PC(n))}"
  using deg_ses[OF assms] unfolding IsAshortExactSequence_def IsExactAt_def by auto

text\<open>The raw lift exists and is unique.\<close>

lemma (in ses_chain_complex) conn_lift_exists:
  assumes n: "n \<in> ints" and bB: "b \<in> B(n)" and cyc: "g(n)`b \<in> bc.tgt.Cycles(n)"
  shows "\<exists>!x. x \<in> A(n \<rs> \<one>) \<and> f(n \<rs> \<one>)`x = dB(n)`b"
proof -
  have pn: "n \<rs> \<one> \<in> ints"
    using n Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  have dBn_fun: "dB(n) : B(n) \<rightarrow> B(n \<rs> \<one>)"
    using ses_cplx_B n unfolding IsAchainComplex_def Homomor_def by auto
  have dBb_B: "dB(n)`b \<in> B(n \<rs> \<one>)"
    using apply_type[OF dBn_fun bB] .
  have gnm1_fun: "g(n \<rs> \<one>) : B(n \<rs> \<one>) \<rightarrow> C(n \<rs> \<one>)"
    using ses_map_g pn unfolding IsAchainMap_def Homomor_def by auto
  have gn_fun: "g(n) : B(n) \<rightarrow> C(n)"
    using ses_map_g n unfolding IsAchainMap_def Homomor_def by auto
  have dCn_fun: "dC(n) : C(n) \<rightarrow> C(n \<rs> \<one>)"
    using ses_cplx_C n unfolding IsAchainComplex_def Homomor_def by auto
  have gnm1_dBb: "g(n \<rs> \<one>)`(dB(n)`b) = bc.tgt.zero_C(n \<rs> \<one>)"
  proof -
    have eq1: "g(n \<rs> \<one>)`(dB(n)`b) = (g(n \<rs> \<one>) O dB(n))`b"
      using comp_fun_apply[OF dBn_fun bB] by simp
    have eq2: "(g(n \<rs> \<one>) O dB(n))`b = (dC(n) O g(n))`b"
      using bc.cmap_comm[OF n] by simp
    have eq3: "(dC(n) O g(n))`b = dC(n)`(g(n)`b)"
      using comp_fun_apply[OF gn_fun bB] by simp
    have eq4: "dC(n)`(g(n)`b) = bc.tgt.zero_C(n \<rs> \<one>)"
      using cyc dCn_fun by (simp add: func1_1_L15)
    from eq1 eq2 eq3 eq4 show ?thesis by simp
  qed
  have dBb_in_ker: "dB(n)`b \<in> g(n \<rs> \<one>)-``{TheNeutralElement(C(n \<rs> \<one>), PC(n \<rs> \<one>))}"
    using func1_1_L15[OF gnm1_fun] dBb_B gnm1_dBb by simp
  have dBb_in_im: "dB(n)`b \<in> f(n \<rs> \<one>)``A(n \<rs> \<one>)"
    using dBb_in_ker ses_im_eq_ker[OF pn] by simp
  have fn_fun: "f(n \<rs> \<one>) : A(n \<rs> \<one>) \<rightarrow> B(n \<rs> \<one>)"
    using ses_map_f pn unfolding IsAchainMap_def Homomor_def by auto
  from dBb_in_im fn_fun obtain x where aA: "x \<in> A(n \<rs> \<one>)"
      and fna: "f(n \<rs> \<one>)`x = dB(n)`b"
    using func_imagedef by auto
  show ?thesis
  proof (rule ex1I[of _ x])
    from aA fna show "x \<in> A(n \<rs> \<one>) \<and> f(n \<rs> \<one>)`x = dB(n)`b" by simp
    fix a' assume "a' \<in> A(n \<rs> \<one>) \<and> f(n \<rs> \<one>)`a' = dB(n)`b"
    then have a'A: "a' \<in> A(n \<rs> \<one>)" and fna': "f(n \<rs> \<one>)`a' = dB(n)`b" by auto
    from fna fna' have eq: "f(n \<rs> \<one>)`x = f(n \<rs> \<one>)`a'" by simp
    from ses_f_inj[OF pn] aA a'A eq show "a' = x" unfolding inj_def by auto
  qed
qed

lemma (in ses_chain_complex) conn_lift_maps:
  assumes "n \<in> ints" "b \<in> B(n)" "g(n)`b \<in> bc.tgt.Cycles(n)"
  shows "f(n \<rs> \<one>)`(conn_lift(n, b)) = dB(n)`b"
  unfolding conn_lift_def
  using theI2[OF conn_lift_exists[OF assms], of "\<lambda>x.  f(n \<rs> 𝟭) ` x = dB(n) ` b"] by blast

lemma (in ses_chain_complex) conn_lift_in_A:
  assumes "n \<in> ints" "b \<in> B(n)" "g(n)`b \<in> bc.tgt.Cycles(n)"
  shows "conn_lift(n, b) \<in> A(n \<rs> \<one>)"
  unfolding conn_lift_def
  using theI2[OF conn_lift_exists[OF assms], of "\<lambda>x. x\<in> A(n \<rs> \<one>)"] by blast

text\<open>The raw lift is a cycle: $d_{n-1}^A(\mathrm{conn\_lift}(n,b)) = 0$.\<close>

lemma (in ses_chain_complex) conn_lift_in_cycles:
  assumes n: "n \<in> ints" and bB: "b \<in> B(n)" and cyc: "g(n)`b \<in> bc.tgt.Cycles(n)"
  shows "conn_lift(n, b) \<in> ab.src.Cycles(n \<rs> \<one>)"
proof -
  have pn: "n \<rs> \<one> \<in> ints"
    using n Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  have ppn: "n \<rs> \<one> \<rs> \<one> \<in> ints"
    using pn Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  let ?cl = "conn_lift(n, b)"
  have clA: "?cl \<in> A(n \<rs> \<one>)" using conn_lift_in_A[OF assms] .
  have fn_maps: "f(n \<rs> \<one>)`?cl = dB(n)`b" using conn_lift_maps[OF assms] .
  have dA_fun: "dA(n \<rs> \<one>) : A(n \<rs> \<one>) \<rightarrow> A(n \<rs> \<one> \<rs> \<one>)"
    using ses_cplx_A pn unfolding IsAchainComplex_def Homomor_def by auto
  have fn2_fun: "f(n \<rs> \<one> \<rs> \<one>) : A(n \<rs> \<one> \<rs> \<one>) \<rightarrow> B(n \<rs> \<one> \<rs> \<one>)"
    using ses_map_f ppn unfolding IsAchainMap_def Homomor_def by auto
  have fn_fun: "f(n \<rs> \<one>) : A(n \<rs> \<one>) \<rightarrow> B(n \<rs> \<one>)"
    using ses_map_f pn unfolding IsAchainMap_def Homomor_def by auto
  have dB_fun: "dB(n \<rs> \<one>) : B(n \<rs> \<one>) \<rightarrow> B(n \<rs> \<one> \<rs> \<one>)"
    using ses_cplx_B pn unfolding IsAchainComplex_def Homomor_def by auto
  have dA_cl: "dA(n \<rs> \<one>)`?cl \<in> A(n \<rs> \<one> \<rs> \<one>)"
    using apply_type[OF dA_fun clA] .
  have key: "f(n \<rs> \<one> \<rs> \<one>)`(dA(n \<rs> \<one>)`?cl) = TheNeutralElement(B(n \<rs> \<one> \<rs> \<one>), PB(n \<rs> \<one> \<rs> \<one>))"
  proof -
    have e1: "f(n \<rs> \<one> \<rs> \<one>)`(dA(n \<rs> \<one>)`?cl) = (f(n \<rs> \<one> \<rs> \<one>) O dA(n \<rs> \<one>))`?cl"
      using comp_fun_apply[OF dA_fun clA] by simp
    have e2: "(f(n \<rs> \<one> \<rs> \<one>) O dA(n \<rs> \<one>))`?cl = (dB(n \<rs> \<one>) O f(n \<rs> \<one>))`?cl"
      using ab.cmap_comm[OF pn] by simp
    have e3: "(dB(n \<rs> \<one>) O f(n \<rs> \<one>))`?cl = dB(n \<rs> \<one>)`(dB(n)`b)"
      using comp_fun_apply[OF fn_fun clA] fn_maps by simp
    have e4: "dB(n \<rs> \<one>)`(dB(n)`b) = TheNeutralElement(B(n \<rs> \<one> \<rs> \<one>), PB(n \<rs> \<one> \<rs> \<one>))"
      using bc.src_cplx chain_complex.bnd_sq_zero_elem n bB unfolding chain_complex_def by simp
    from e1 e2 e3 e4 show ?thesis by simp
  qed
  have ker_eq: "f(n \<rs> \<one> \<rs> \<one>)-``{TheNeutralElement(B(n \<rs> \<one> \<rs> \<one>), PB(n \<rs> \<one> \<rs> \<one>))} =
                {TheNeutralElement(A(n \<rs> \<one> \<rs> \<one>), PA(n \<rs> \<one> \<rs> \<one>))}"
  proof -
    have ses2: "IsAshortExactSequence(A(n \<rs> \<one> \<rs> \<one>), PA(n \<rs> \<one> \<rs> \<one>),
                  B(n \<rs> \<one> \<rs> \<one>), PB(n \<rs> \<one> \<rs> \<one>),
                  C(n \<rs> \<one> \<rs> \<one>), PC(n \<rs> \<one> \<rs> \<one>),
                  f(n \<rs> \<one> \<rs> \<one>), g(n \<rs> \<one> \<rs> \<one>))"
      using deg_ses[OF ppn] .
    have ea: "IsExactAt(ZeroMap(1, A(n \<rs> \<one> \<rs> \<one>), PA(n \<rs> \<one> \<rs> \<one>)), 1,
               f(n \<rs> \<one> \<rs> \<one>), B(n \<rs> \<one> \<rs> \<one>), PB(n \<rs> \<one> \<rs> \<one>))"
      using ses2 unfolding IsAshortExactSequence_def by auto
    have grpA: "IsAgroup(A(n \<rs> \<one> \<rs> \<one>), PA(n \<rs> \<one> \<rs> \<one>))"
      using ses2 unfolding IsAshortExactSequence_def group_homo_def by auto
    from ea 
    show ?thesis using ZeroMap_image[OF trivial_group grpA] unfolding IsExactAt_def by auto
  qed
  have dA_cl_ker: "dA(n \<rs> \<one>)`?cl \<in>
      f(n \<rs> \<one> \<rs> \<one>)-``{TheNeutralElement(B(n \<rs> \<one> \<rs> \<one>), PB(n \<rs> \<one> \<rs> \<one>))}"
    using func1_1_L15[OF fn2_fun] dA_cl key by simp
  have dA_cl_zero: "dA(n \<rs> \<one>)`?cl = TheNeutralElement(A(n \<rs> \<one> \<rs> \<one>), PA(n \<rs> \<one> \<rs> \<one>))"
    using dA_cl_ker ker_eq by auto
  show ?thesis using func1_1_L15[OF dA_fun] clA dA_cl_zero by simp
qed

text\<open>Independence of lift: if two elements of $B_n$ have the same image under $g_n$,
  their raw lifts represent the same homology class.\<close>

lemma (in ses_chain_complex) conn_lift_indep:
  assumes n: "n \<in> ints" and b1: "b1 \<in> B(n)" and b2: "b2 \<in> B(n)"
    and cyc: "g(n)`b1 \<in> bc.tgt.Cycles(n)" and eq: "g(n)`b1 = g(n)`b2"
  shows "\<langle>conn_lift(n, b1), conn_lift(n, b2)\<rangle> \<in>
    QuotientGroupRel(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>), ab.src.Boundaries(n \<rs> \<one>))"
proof -
  have pn: "n \<rs> \<one> \<in> ints"
    using n Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  have cyc2: "g(n)`b2 \<in> bc.tgt.Cycles(n)" using cyc eq by simp
  have cl1_A: "conn_lift(n, b1) \<in> A(n \<rs> \<one>)" using conn_lift_in_A[OF n b1 cyc] .
  have cl2_A: "conn_lift(n, b2) \<in> A(n \<rs> \<one>)" using conn_lift_in_A[OF n b2 cyc2] .
  have cl1_cyc: "conn_lift(n, b1) \<in> ab.src.Cycles(n \<rs> \<one>)"
    using conn_lift_in_cycles[OF n b1 cyc] .
  have cl2_cyc: "conn_lift(n, b2) \<in> ab.src.Cycles(n \<rs> \<one>)"
    using conn_lift_in_cycles[OF n b2 cyc2] .
  have gn_hg: "group_homo(B(n), PB(n), C(n), PC(n), g(n))" using ses_hg[OF n] .
  have gn_fun: "g(n) : B(n) \<rightarrow> C(n)"
    using group_homo.f_is_fun[OF gn_hg] by simp
  have fn_fun: "f(n) : A(n) \<rightarrow> B(n)"
    using group_homo.f_is_fun[OF ses_hf[OF n]] by simp
  have fn_nm1_fun: "f(n \<rs> \<one>) : A(n \<rs> \<one>) \<rightarrow> B(n \<rs> \<one>)"
    using ses_map_f pn unfolding IsAchainMap_def Homomor_def by auto
  have dBn_fun: "dB(n) : B(n) \<rightarrow> B(n \<rs> \<one>)"
    using ses_cplx_B n unfolding IsAchainComplex_def Homomor_def by auto
  have dAn_fun: "dA(n) : A(n) \<rightarrow> A(n \<rs> \<one>)"
    using ses_cplx_A n unfolding IsAchainComplex_def Homomor_def by auto
  have b1B: "b1 \<in> B(n)" using b1 .
  have b2B: "b2 \<in> B(n)" using b2 .
  have inv_b2: "\<rm>\<^sup>B\<^bsub>n\<^esub> b2 \<in> B(n)"
    using group_homo.origin group0.inverse_in_group gn_hg b2 unfolding group0_def by simp
  have diff_B: "b1 \<ra>\<^sup>B\<^bsub>n\<^esub> \<rm>\<^sup>B\<^bsub>n\<^esub> b2 \<in> B(n)"
    using group_homo.origin group0.group_op_closed gn_hg b1 inv_b2 unfolding group0_def by simp
  have g_diff: "g(n)`(b1 \<ra>\<^sup>B\<^bsub>n\<^esub> \<rm>\<^sup>B\<^bsub>n\<^esub> b2) =
                TheNeutralElement(C(n), PC(n))"
  proof -
    have step1: "g(n)`(b1 \<ra>\<^sup>B\<^bsub>n\<^esub> \<rm>\<^sup>B\<^bsub>n\<^esub> b2) =
                 g(n)`b1 \<ra>\<^sup>C\<^bsub>n\<^esub> g(n)`(\<rm>\<^sup>B\<^bsub>n\<^esub> b2)"
      using group_homo.f_hom[OF gn_hg b1 inv_b2] by simp
    have step2: "g(n)`(\<rm>\<^sup>B\<^bsub>n\<^esub> b2) = \<rm>\<^sup>C\<^bsub>n\<^esub> (g(n)`b2)"
      using group_homo.f_inv[OF gn_hg b2] by simp
    have step3: "g(n)`b1 \<ra>\<^sup>C\<^bsub>n\<^esub> \<rm>\<^sup>C\<^bsub>n\<^esub> (g(n)`b1) =
                 TheNeutralElement(C(n), PC(n))"
    proof -
      have gnb1C: "g(n)`b1 \<in> C(n)" using apply_type[OF gn_fun b1] .
      from group_homo.target group0.group0_2_L6 gn_hg gnb1C show ?thesis unfolding group0_def by simp
    qed
    from step1 step2 step3 eq show ?thesis by simp
  qed
  have diff_in_ker: "b1 \<ra>\<^sup>B\<^bsub>n\<^esub> \<rm>\<^sup>B\<^bsub>n\<^esub> b2 \<in>
                     g(n)-``{TheNeutralElement(C(n), PC(n))}"
    using func1_1_L15[OF gn_fun] diff_B g_diff by simp
  have diff_in_im: "b1 \<ra>\<^sup>B\<^bsub>n\<^esub> \<rm>\<^sup>B\<^bsub>n\<^esub> b2 \<in> f(n)``A(n)"
    using diff_in_ker ses_im_eq_ker[OF n] by simp
  from diff_in_im fn_fun obtain a0 where a0A: "a0 \<in> A(n)"
      and fa0: "f(n)`a0 = b1 \<ra>\<^sup>B\<^bsub>n\<^esub> \<rm>\<^sup>B\<^bsub>n\<^esub> b2"
    using func_imagedef by auto
  have dA_a0_Bnd: "dA(n)`a0 \<in> ab.src.Boundaries(n \<rs> \<one>)"
  proof -
    have arith: "(n \<rs> \<one>) \<ra> \<one> = n"
      using Int_ZF_1_L8A(2) group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3)] n by simp
    have "dA(n)`a0 \<in> (dA((n \<rs> \<one>) \<ra> \<one>))``(A((n \<rs> \<one>) \<ra> \<one>))"
      using func_imagedef[OF dAn_fun] a0A arith by auto
    with arith show ?thesis by simp
  qed
  have fn_nm1_hf: "group_homo(A(n \<rs> \<one>), PA(n \<rs> \<one>), B(n \<rs> \<one>), PB(n \<rs> \<one>), f(n \<rs> \<one>))"
    using ses_hf[OF pn] .
  have eq_lhs: "f(n \<rs> \<one>)`(conn_lift(n, b1) \<ra>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub>
                  \<rm>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> (conn_lift(n, b2))) =
                f(n \<rs> \<one>)`(dA(n)`a0)"
  proof -
    have inv_cl2: "\<rm>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> (conn_lift(n, b2)) \<in> A(n \<rs> \<one>)"
      using group_homo.origin group0.inverse_in_group fn_nm1_hf cl2_A unfolding group0_def by simp
    have e1: "f(n \<rs> \<one>)`(conn_lift(n, b1) \<ra>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub>
                \<rm>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> (conn_lift(n, b2))) =
              f(n \<rs> \<one>)`(conn_lift(n, b1)) \<ra>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub>
                f(n \<rs> \<one>)`(\<rm>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> (conn_lift(n, b2)))"
      using group_homo.f_hom[OF fn_nm1_hf cl1_A inv_cl2] by simp
    have e2: "f(n \<rs> \<one>)`(\<rm>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> (conn_lift(n, b2))) =
              \<rm>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> (f(n \<rs> \<one>)`(conn_lift(n, b2)))"
      using group_homo.f_inv[OF fn_nm1_hf cl2_A] by simp
    have e3: "f(n \<rs> \<one>)`(conn_lift(n, b1)) \<ra>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub>
                \<rm>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> (f(n \<rs> \<one>)`(conn_lift(n, b2))) =
              dB(n)`b1 \<ra>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> \<rm>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> (dB(n)`b2)"
      using conn_lift_maps[OF n b1 cyc] conn_lift_maps[OF n b2 cyc2] by simp
    have dBhg: "group_homo(B(n), PB(n), B(n \<rs> \<one>), PB(n \<rs> \<one>), dB(n))"
    proof -
      have hom: "Homomor(dB(n), B(n), PB(n), B(n \<rs> \<one>), PB(n \<rs> \<one>))"
        using ses_cplx_B n unfolding IsAchainComplex_def by auto
      have grpB: "IsAgroup(B(n), PB(n))"
        using ses_cplx_B n unfolding IsAchainComplex_def by auto
      have grpBn: "IsAgroup(B(n \<rs> \<one>), PB(n \<rs> \<one>))"
        using ses_cplx_B pn unfolding IsAchainComplex_def by auto
      from hom grpB grpBn show ?thesis unfolding group_homo_def by simp
    qed
    have e4: "dB(n)`b1 \<ra>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> \<rm>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> (dB(n)`b2) =
              dB(n)`(b1 \<ra>\<^sup>B\<^bsub>n\<^esub> \<rm>\<^sup>B\<^bsub>n\<^esub> b2)"
    proof -
      have inv_b2': "\<rm>\<^sup>B\<^bsub>n\<^esub> b2 \<in> B(n)"
        using group_homo.origin group0.inverse_in_group dBhg b2 unfolding group0_def by simp
      have step_hom: "dB(n)`(b1 \<ra>\<^sup>B\<^bsub>n\<^esub> \<rm>\<^sup>B\<^bsub>n\<^esub> b2) =
                      dB(n)`b1 \<ra>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> dB(n)`(\<rm>\<^sup>B\<^bsub>n\<^esub> b2)"
        using group_homo.f_hom[OF dBhg b1 inv_b2'] by simp
      have step_inv: "dB(n)`(\<rm>\<^sup>B\<^bsub>n\<^esub> b2) = \<rm>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> (dB(n)`b2)"
        using group_homo.f_inv[OF dBhg b2] by simp
      from step_hom step_inv show ?thesis by simp
    qed
    have fn_hf: "group_homo(A(n), PA(n), B(n), PB(n), f(n))" using ses_hf[OF n] .
    have fn_fun': "f(n) : A(n) \<rightarrow> B(n)" using group_homo.f_is_fun[OF fn_hf] .
    have e5: "dB(n)`(b1 \<ra>\<^sup>B\<^bsub>n\<^esub> \<rm>\<^sup>B\<^bsub>n\<^esub> b2) = dB(n)`(f(n)`a0)"
      using fa0 by simp
    have dAn_fun': "dA(n) : A(n) \<rightarrow> A(n \<rs> \<one>)"
      using ses_cplx_A n unfolding IsAchainComplex_def Homomor_def by auto
    have e6: "dB(n)`(f(n)`a0) = f(n \<rs> \<one>)`(dA(n)`a0)"
    proof -
      have step: "(dB(n) O f(n))`a0 = (f(n \<rs> \<one>) O dA(n))`a0"
        using ab.cmap_comm[OF n] by simp
      have lhs: "(dB(n) O f(n))`a0 = dB(n)`(f(n)`a0)"
        using comp_fun_apply[OF fn_fun' a0A] by simp
      have rhs: "(f(n \<rs> \<one>) O dA(n))`a0 = f(n \<rs> \<one>)`(dA(n)`a0)"
        using comp_fun_apply[OF dAn_fun' a0A] by simp
      from step lhs rhs show ?thesis by simp
    qed
    from e1 e2 e3 e4 e5 e6 show ?thesis by simp
  qed
  have f_nm1_inj: "f(n \<rs> \<one>) \<in> inj(A(n \<rs> \<one>), B(n \<rs> \<one>))" using ses_f_inj[OF pn] .
  have inv_cl2_A: "\<rm>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> (conn_lift(n, b2)) \<in> A(n \<rs> \<one>)"
    using group_homo.origin group0.inverse_in_group fn_nm1_hf cl2_A unfolding group0_def by simp
  have diff_cl: "conn_lift(n, b1) \<ra>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub>
                  \<rm>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> (conn_lift(n, b2)) \<in> A(n \<rs> \<one>)"
    using group_homo.origin group0.group_op_closed fn_nm1_hf cl1_A inv_cl2_A unfolding group0_def by simp
  have dA_a0_A: "dA(n)`a0 \<in> A(n \<rs> \<one>)"
    using apply_type[OF dAn_fun a0A] .
  have eq_diff: "conn_lift(n, b1) \<ra>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub>
                  \<rm>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> (conn_lift(n, b2)) = dA(n)`a0"
    using f_nm1_inj diff_cl dA_a0_A eq_lhs unfolding inj_def by auto
  have diff_in_Bnd: "conn_lift(n, b1) \<ra>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub>
                      \<rm>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> (conn_lift(n, b2)) \<in>
                     ab.src.Boundaries(n \<rs> \<one>)"
    using eq_diff dA_a0_Bnd by simp
  have sub_in_cycles: "IsAsubgroup(ab.src.Cycles(n \<rs> \<one>), PA(n \<rs> \<one>))"
    using ab.src.cycles_is_subgroup[OF pn] .
  have inv_eq: "GroupInv(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>))`(conn_lift(n, b2)) =
                \<rm>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> (conn_lift(n, b2))"
  proof -
    have sub_A: "IsAsubgroup(ab.src.Cycles(n \<rs> \<one>), PA(n \<rs> \<one>))"
      using sub_in_cycles .
    from ab.src.cycles_is_group[OF pn]
    have grpCyc: "IsAgroup(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>))" .
    interpret Cn: group0 "A(n \<rs> \<one>)" "PA(n \<rs> \<one>)"
      "TheNeutralElement(A(n \<rs> \<one>), PA(n \<rs> \<one>))"
      "\<lambda>x y. PA(n \<rs> \<one>)`\<langle>x,y\<rangle>"
      "\<lambda>x. GroupInv(A(n \<rs> \<one>), PA(n \<rs> \<one>))`x"
      "\<lambda>s. Fold(PA(n \<rs> \<one>), TheNeutralElement(A(n \<rs> \<one>), PA(n \<rs> \<one>)), s)"
      "\<lambda>m x. Fold(PA(n \<rs> \<one>), TheNeutralElement(A(n \<rs> \<one>), PA(n \<rs> \<one>)), {\<langle>k, x\<rangle>. k \<in> m})"
      using ses_hf[OF pn] unfolding group_homo_def group0_def by simp
    from Cn.group0_3_T2 sub_in_cycles cl2_cyc show ?thesis by simp
  qed
  have cycop_eq: "ab.src.CycleOp(n \<rs> \<one>)`\<langle>conn_lift(n, b1),
                   GroupInv(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>))`(conn_lift(n, b2))\<rangle> =
                  conn_lift(n, b1) \<ra>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub>
                   \<rm>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> (conn_lift(n, b2))"
  proof -
    have inv_cl2_cyc: "GroupInv(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>))`(conn_lift(n, b2)) \<in>
                       ab.src.Cycles(n \<rs> \<one>)"
      using group_homo.origin group0.inverse_in_group fn_nm1_hf cl2_cyc
        ab.src.cycles_is_group[OF pn] unfolding group0_def by simp
    have pair_in: "\<langle>conn_lift(n, b1),
                    GroupInv(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>))`(conn_lift(n, b2))\<rangle>
                   \<in> ab.src.Cycles(n \<rs> \<one>) \<times> ab.src.Cycles(n \<rs> \<one>)"
      using cl1_cyc inv_cl2_cyc by auto
    from restrict[of "PA(n \<rs> \<one>)" "ab.src.Cycles(n \<rs> \<one>) \<times> ab.src.Cycles(n \<rs> \<one>)" _] pair_in inv_eq
    show ?thesis by (simp only: if_true)
  qed
  show ?thesis
    unfolding QuotientGroupRel_def
    using cl1_cyc cl2_cyc diff_in_Bnd cycop_eq inv_eq by auto
qed

text\<open>Boundaries map to boundaries: if $c \in B_n(C)$ and $b$ is a lift of $c$,
  then $\mathrm{conn\_lift}(n,b) \in B_{n-1}(A)$.\<close>

lemma (in ses_chain_complex) conn_lift_bnd_to_bnd:
  assumes n: "n \<in> ints" and bB: "b \<in> B(n)"
    and bnd: "g(n)`b \<in> bc.tgt.Boundaries(n)"
  shows "conn_lift(n, b) \<in> ab.src.Boundaries(n \<rs> \<one>)"
proof -
  have pn: "n \<rs> \<one> \<in> ints"
    using n Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  have np: "n \<ra> \<one> \<in> ints"
    using n Int_ZF_1_L8A(2) Int_ZF_1_T2(3) group0.group_op_closed by simp
  have arith_np: "(n \<ra> \<one>) \<rs> \<one> = n"
    using Int_ZF_1_L8A(2) group0.inv_cancel_two(2)[OF Int_ZF_1_T2(3)] n by simp
  have dc:"dC(n\<ra>\<one>):C(n\<ra>\<one>)\<rightarrow>C(n)"
    using ses_cplx_C np arith_np
    unfolding IsAchainComplex_def IsMorphism_def Homomor_def by auto
  let ?c = "g(n)`b"
  have cyc:"?c\<in>bc.tgt.Cycles(n)" using
    n bnd bc.tgt.boundaries_in_cycles by auto
  from bnd obtain c' where c'C: "c' \<in> C(n \<ra> \<one>)"
      and c'_eq: "?c = dC(n \<ra> \<one>)`c'"
    using func_imagedef[of "dC(n \<ra> \<one>)" "C(n\<ra>\<one>)" "C(n)" "C(n\<ra>\<one>)"]
    dc
    by auto
  have gnp_surj: "g(n \<ra> \<one>)``B(n \<ra> \<one>) = C(n \<ra> \<one>)"
  proof -
    have ses_np: "IsAshortExactSequence(A(n \<ra> \<one>), PA(n \<ra> \<one>), B(n \<ra> \<one>), PB(n \<ra> \<one>),
                   C(n \<ra> \<one>), PC(n \<ra> \<one>), f(n \<ra> \<one>), g(n \<ra> \<one>))"
      using deg_ses[OF np] .
    have ea_C: "IsExactAt(g(n \<ra> \<one>), B(n \<ra> \<one>), ZeroMap(C(n \<ra> \<one>), 1, TrivOp), 1, TrivOp)"
      using ses_np unfolding IsAshortExactSequence_def by auto
    from ea_C 
    have "g(n \<ra> \<one>)``B(n \<ra> \<one>) = ZeroMap(C(n \<ra> \<one>), 1, TrivOp)-``{TheNeutralElement(1, TrivOp)}"
     unfolding IsExactAt_def by simp
    also have "\<dots> = C(n \<ra> \<one>)"
    proof -
      have grpCnp: "IsAgroup(C(n \<ra> \<one>), PC(n \<ra> \<one>))"
        using ses_np unfolding IsAshortExactSequence_def group_homo_def by auto
      show ?thesis
      using ZeroMap_preimage_full[OF grpCnp trivial_group] TrivOp_ne by simp
    qed
    finally show ?thesis .
  qed
  have gnp_fun: "g(n \<ra> \<one>) : B(n \<ra> \<one>) \<rightarrow> C(n \<ra> \<one>)"
    using ses_map_g np unfolding IsAchainMap_def Homomor_def by auto
  from c'C gnp_surj gnp_fun obtain b' where b'B: "b' \<in> B(n \<ra> \<one>)"
      and gnp_b': "g(n \<ra> \<one>)`b' = c'"
    using func_imagedef[of "g(n\<ra>\<one>)" "B(n\<ra>\<one>)" "C(n\<ra>\<one>)" "B(n\<ra>\<one>)"] by auto
  let ?b_spec = "dB(n \<ra> \<one>)`b'"
  have dBnp_fun: "dB(n \<ra> \<one>) : B(n \<ra> \<one>) \<rightarrow> B(n)"
    using ses_cplx_B np unfolding IsAchainComplex_def Homomor_def using arith_np by auto
  have b_spec_B: "?b_spec \<in> B(n)" using apply_type[OF dBnp_fun b'B] .
  have g_b_spec: "g(n)`?b_spec = ?c"
  proof -
    have dCnp_fun': "dC(n \<ra> \<one>) : C(n \<ra> \<one>) \<rightarrow> C((n \<ra> \<one>) \<rs> \<one>)"
      using ses_cplx_C np unfolding IsAchainComplex_def Homomor_def by auto
    have gnp_fun': "g(n \<ra> \<one>) : B(n \<ra> \<one>) \<rightarrow> C(n \<ra> \<one>)"
      using gnp_fun .
    have gn_fun': "g(n) : B(n) \<rightarrow> C(n)"
      using ses_map_g n unfolding IsAchainMap_def Homomor_def by auto
    have bc_comm_np: "dC(n \<ra> \<one>) O g(n \<ra> \<one>) = g((n \<ra> \<one>) \<rs> \<one>) O dB(n \<ra> \<one>)"
      using bc.cmap_comm[OF np] by simp
    have eq1: "g(n)`?b_spec = (g(n) O dB(n \<ra> \<one>))`b'"
      using comp_fun_apply[OF dBnp_fun b'B] by simp
    have eq2: "(g(n) O dB(n \<ra> \<one>))`b' = (dC(n \<ra> \<one>) O g(n \<ra> \<one>))`b'"
      using bc_comm_np arith_np by simp
    have eq3: "(dC(n \<ra> \<one>) O g(n \<ra> \<one>))`b' = dC(n \<ra> \<one>)`c'"
      using comp_fun_apply[OF gnp_fun' b'B] gnp_b' by simp
    from eq1 eq2 eq3 c'_eq arith_np show ?thesis by simp
  qed
  have cyc_spec: "g(n)`?b_spec \<in> bc.tgt.Cycles(n)"
    using g_b_spec cyc by simp
  have cl_spec_zero: "conn_lift(n, ?b_spec) = TheNeutralElement(A(n \<rs> \<one>), PA(n \<rs> \<one>))"
  proof -
    have fn_nm1_fun: "f(n \<rs> \<one>) : A(n \<rs> \<one>) \<rightarrow> B(n \<rs> \<one>)"
      using ses_map_f pn unfolding IsAchainMap_def Homomor_def by auto
    have bnd_zero: "dB(n)`?b_spec = TheNeutralElement(B(n \<rs> \<one>), PB(n \<rs> \<one>))"
    proof -
      have dBn_fun: "dB(n) : B(n) \<rightarrow> B(n \<rs> \<one>)"
        using ses_cplx_B n unfolding IsAchainComplex_def Homomor_def by auto
      have dBnm1_fun: "dB(n \<rs> \<one>) : B(n \<rs> \<one>) \<rightarrow> B(n \<rs> \<one> \<rs> \<one>)"
        using ses_cplx_B pn unfolding IsAchainComplex_def Homomor_def by auto
      have bnd_sub: "(dB(n \<ra> \<one>))``(B(n \<ra> \<one>)) \<subseteq>
          (dB(n))-``{TheNeutralElement(B(n \<rs> \<one>), PB(n \<rs> \<one>))}"
        using ab.tgt.boundaries_in_cycles n by auto
      have b'_im: "?b_spec \<in> (dB(n \<ra> \<one>))``(B(n \<ra> \<one>))"
        using func_imagedef[OF dBnp_fun] b'B by auto
      from b'_im bnd_sub have mem:
        "?b_spec \<in> (dB(n))-``{TheNeutralElement(B(n \<rs> \<one>), PB(n \<rs> \<one>))}"
        by auto
      from func1_1_L15[OF dBn_fun] b_spec_B mem show ?thesis by simp
    qed
    have maps_to_zero: "f(n \<rs> \<one>)`(conn_lift(n, ?b_spec)) =
                        TheNeutralElement(B(n \<rs> \<one>), PB(n \<rs> \<one>))"
      using conn_lift_maps[OF n b_spec_B cyc_spec] bnd_zero by simp
    have f_neutral: "f(n \<rs> \<one>)`(TheNeutralElement(A(n \<rs> \<one>), PA(n \<rs> \<one>))) =
                     TheNeutralElement(B(n \<rs> \<one>), PB(n \<rs> \<one>))"
      using group_homo.f_neutral[OF ses_hf[OF pn]] by simp
    have cl_A: "conn_lift(n, ?b_spec) \<in> A(n \<rs> \<one>)"
      using conn_lift_in_A[OF n b_spec_B cyc_spec] .
    have neu_A: "TheNeutralElement(A(n \<rs> \<one>), PA(n \<rs> \<one>)) \<in> A(n \<rs> \<one>)"
      using group_homo.origin group0.group0_2_L2 ses_hf[OF pn] unfolding group0_def by simp
    from ses_f_inj[OF pn] cl_A neu_A maps_to_zero f_neutral
    show ?thesis unfolding inj_def by auto
  qed
  have same_img: "g(n)`b = g(n)`?b_spec" using g_b_spec by simp
  have rel: "\<langle>conn_lift(n, b), conn_lift(n, ?b_spec)\<rangle> \<in>
    QuotientGroupRel(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>), ab.src.Boundaries(n \<rs> \<one>))"
    using conn_lift_indep[OF n bB b_spec_B cyc same_img] .
  have neu_A: "TheNeutralElement(A(n \<rs> \<one>), PA(n \<rs> \<one>)) \<in> ab.src.Boundaries(n \<rs> \<one>)"
    using ab.src.boundaries_subgroup_ambient[OF pn]
          ab.src_cplx group0.group0_3_L5[of _ "PA(n \<rs> \<one>)"]
    chain_complex.cplx_group pn
    unfolding group0_def chain_complex_def by simp
  have grpCyc: "IsAgroup(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>))"
    using ab.src.cycles_is_group[OF pn] .
  from rel cl_spec_zero
  have " ⟨conn_lift(n, b), ab.src.zero_C(n \<rs> 𝟭)⟩ ∈
    QuotientGroupRel(ab.src.Cycles(n \<rs> 𝟭),
      restrict(PA(n \<rs> 𝟭),
        ab.src.Cycles(n \<rs> 𝟭) ×
        ab.src.Cycles(n \<rs> 𝟭)),
      ab.src.Boundaries(n \<rs> 𝟭))" by auto
  then have rel2: "ab.src.CycleOp(n \<rs> \<one>)`\<langle>conn_lift(n, b),
               GroupInv(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>))`
                 (TheNeutralElement(A(n \<rs> \<one>), PA(n \<rs> \<one>)))\<rangle> \<in>
               ab.src.Boundaries(n \<rs> \<one>)"
    unfolding QuotientGroupRel_def by auto
  have subgCycles:"IsAsubgroup(ab.src.Cycles(n \<rs> 𝟭), PA(n \<rs> 𝟭))"
    using  chain_complex.cycles_is_subgroup[of A PA dA "n\<rs>\<one>"] pn ses_cplx_A
    unfolding chain_complex_def by auto
  then have neu_cyc_eq:"TheNeutralElement(ab.src.Cycles(n \<rs> 𝟭),
      restrict(PA(n \<rs> 𝟭),
        ab.src.Cycles(n \<rs> 𝟭) ×
        ab.src.Cycles(n \<rs> 𝟭))) =
    ab.src.zero_C(n \<rs> 𝟭)" using group0.group0_3_L4[of "A(n\<rs>\<one>)" "PA(n\<rs>\<one>)" "ab.src.Cycles(n \<rs> 𝟭)"]
    unfolding group0_def using ab.src.cplx_group pn by auto
  then have inv_neu: "GroupInv(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>))`
                   (TheNeutralElement(A(n \<rs> \<one>), PA(n \<rs> \<one>))) =
                 TheNeutralElement(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>))"
    using group0.group_inv_of_one[of "ab.src.Cycles(n \<rs> \<one>)" "ab.src.CycleOp(n \<rs> \<one>)"]
          grpCyc
    unfolding group0_def by auto
  have conn_lift_is_cl_b: "conn_lift(n, b) \<in> ab.src.Cycles(n \<rs> \<one>)"
    using conn_lift_in_cycles[OF n bB cyc] .
  from inv_neu have "restrict
     (PA(n \<rs> 𝟭),
      ab.src.Cycles(n \<rs> 𝟭) ×
      ab.src.Cycles(n \<rs> 𝟭)) `
    ⟨conn_lift(n, b),
     GroupInv
      (ab.src.Cycles(n \<rs> 𝟭),
       restrict
        (PA(n \<rs> 𝟭),
         ab.src.Cycles(n \<rs> 𝟭) ×
         ab.src.Cycles(n \<rs> 𝟭))) `
     ab.src.zero_C(n \<rs> 𝟭)⟩ = restrict
     (PA(n \<rs> 𝟭),
      ab.src.Cycles(n \<rs> 𝟭) ×
      ab.src.Cycles(n \<rs> 𝟭)) `
    ⟨conn_lift(n, b),
     TheNeutralElement
     (ab.src.Cycles(n \<rs> 𝟭),
      restrict
       (PA(n \<rs> 𝟭),
        ab.src.Cycles(n \<rs> 𝟭) ×
        ab.src.Cycles(n \<rs> 𝟭)))⟩" by auto
  with rel2 neu_cyc_eq have "ab.src.CycleOp(n \<rs> \<one>)`\<langle>conn_lift(n, b),
         TheNeutralElement(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>))\<rangle> \<in>
        ab.src.Boundaries(n \<rs> \<one>)"
    by auto
  with group0.group0_2_L2[of "ab.src.Cycles(n \<rs> \<one>)" "ab.src.CycleOp(n \<rs> \<one>)"]
       grpCyc conn_lift_is_cl_b
  show ?thesis
    unfolding group0_def by auto
qed

text\<open>The connecting homomorphism $\delta_n \colon H_n(C) \to H_{n-1}(A)$ is defined by
  choosing any lift $b \in B_n$ with $g_n(b) = c$ and mapping $[c]$ to $[\mathrm{conn\_lift}(n,b)]$.
  By independence of lift and the boundary condition, this is well-defined.\<close>

definition (in ses_chain_complex) delta :: "i \<Rightarrow> i" where
  "delta(n) \<equiv>
    {\<langle>QuotientGroupRel(bc.tgt.Cycles(n), bc.tgt.CycleOp(n), bc.tgt.Boundaries(n))``{g(n)`b},
        QuotientGroupRel(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>), ab.src.Boundaries(n \<rs> \<one>))``
        {conn_lift(n, b)}\<rangle>.
     b \<in> {x \<in> B(n). g(n)`x \<in> bc.tgt.Cycles(n)}}"

text\<open>The connecting map is a well-defined function from $H_n(C)$ to $H_{n-1}(A)$.\<close>

lemma (in ses_chain_complex) delta_fun:
  assumes n: "n \<in> ints"
  shows "delta(n) : bc.tgt.Hn(n) \<rightarrow> ab.src.Hn(n \<rs> \<one>)"
proof -
  have pn: "n \<rs> \<one> \<in> ints"
    using n Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  let ?Lft = "{x \<in> B(n). g(n)`x \<in> bc.tgt.Cycles(n)}"
  let ?Rc = "QuotientGroupRel(bc.tgt.Cycles(n), bc.tgt.CycleOp(n), bc.tgt.Boundaries(n))"
  let ?Ra = "QuotientGroupRel(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>), ab.src.Boundaries(n \<rs> \<one>))"
  let ?M = "delta(n)"
  have M_eq: "?M = {\<langle>?Rc``{g(n)`b}, ?Ra``{conn_lift(n, b)}\<rangle>. b \<in> ?Lft}"
    unfolding delta_def by simp
  have equiv_c: "equiv(bc.tgt.Cycles(n), ?Rc)"
    using bc.tgt.cycles_is_subgroup[OF n]
          group0.Group_ZF_2_4_L3[OF _ bc.tgt.boundaries_subgroup_cycles[OF n]]
    unfolding IsAsubgroup_def group0_def by auto
  have equiv_a: "equiv(ab.src.Cycles(n \<rs> \<one>), ?Ra)"
    using ab.src.cycles_is_subgroup[OF pn]
          group0.Group_ZF_2_4_L3[OF _ ab.src.boundaries_subgroup_cycles[OF pn]]
    unfolding IsAsubgroup_def group0_def by simp
  have gn_fun: "g(n) : B(n) \<rightarrow> C(n)"
    using ses_map_g n unfolding IsAchainMap_def Homomor_def by auto
  have gn_surj_Cycles: "\<forall>c \<in> bc.tgt.Cycles(n). \<exists>b \<in> ?Lft. g(n)`b = c"
  proof
    fix c assume cC: "c \<in> bc.tgt.Cycles(n)"
    then have cCn: "c \<in> C(n)"
      using bc.tgt.cycles_is_subgroup[OF n] group0.group0_3_L2[of "C(n)" "PC(n)"]
      bc.tgt.cplx_group[OF n]
      unfolding group0_def by auto
    have gnB_C: "g(n)``B(n) = C(n)"
    proof -
      have ea_C: "IsExactAt(g(n), B(n), ZeroMap(C(n), 1, TrivOp), 1, TrivOp)"
        using deg_ses[OF n] unfolding IsAshortExactSequence_def by auto
      have grpC: "IsAgroup(C(n), PC(n))"
        using deg_ses[OF n] unfolding IsAshortExactSequence_def group_homo_def by auto
      from ea_C 
      show ?thesis using ZeroMap_preimage_full[OF grpC trivial_group] TrivOp_ne unfolding IsExactAt_def by simp
    qed
    from cCn gnB_C have "c\<in> g(n)``B(n)" by auto
    then obtain b where bB: "b \<in> B(n)" and gnb: "g(n)`b = c"
      using func_imagedef[OF gn_fun, of "B(n)"] by auto
    from bB gnb cC show "\<exists>b \<in> ?Lft. g(n)`b = c" by auto
  qed
  have M_subset: "?M \<in> Pow(bc.tgt.Hn(n) \<times> ab.src.Hn(n \<rs> \<one>))"
  proof (safe)
    fix p assume pM: "p \<in> ?M"
    from pM M_eq obtain b where bLft: "b \<in> ?Lft"
        and p_eq: "p = \<langle>?Rc``{g(n)`b}, ?Ra``{conn_lift(n, b)}\<rangle>" by auto
    have bB: "b \<in> B(n)" and b_cyc: "g(n)`b \<in> bc.tgt.Cycles(n)" using bLft by auto
    from b_cyc equiv_c have Rc_cls: "?Rc``{g(n)`b} \<in> bc.tgt.Hn(n)"
      unfolding bc.tgt.Hn_def quotient_def by auto
    have cl_cyc: "conn_lift(n, b) \<in> ab.src.Cycles(n \<rs> \<one>)"
      using conn_lift_in_cycles[OF n bB b_cyc] .
    from cl_cyc equiv_a have Ra_cls: "?Ra``{conn_lift(n, b)} \<in> ab.src.Hn(n \<rs> \<one>)"
      unfolding ab.src.Hn_def quotient_def by auto
    from p_eq Rc_cls Ra_cls show "p \<in> bc.tgt.Hn(n) \<times> ab.src.Hn(n \<rs> \<one>)" by auto
  qed
  have M_dom: "bc.tgt.Hn(n) \<subseteq> domain(?M)"
  proof
    fix X assume X_Hn: "X \<in> bc.tgt.Hn(n)"
    then obtain c where cC: "c \<in> bc.tgt.Cycles(n)" and X_eq: "X = ?Rc``{c}"
      unfolding bc.tgt.Hn_def quotient_def by auto
    from gn_surj_Cycles cC obtain b where bLft: "b \<in> ?Lft" and gnb: "g(n)`b = c" by auto
    have "\<langle>X, ?Ra``{conn_lift(n, b)}\<rangle> \<in> ?M"
      using M_eq bLft X_eq gnb by auto
    then show "X \<in> domain(?M)" unfolding domain_def by auto
  qed
  have M_sv: "\<forall>X y t. \<langle>X,y\<rangle> \<in> ?M \<longrightarrow> \<langle>X,t\<rangle> \<in> ?M \<longrightarrow> y = t"
  proof (intro allI impI)
    fix X y t
    assume Xy: "\<langle>X,y\<rangle> \<in> ?M" and Xt: "\<langle>X,t\<rangle> \<in> ?M"
    from Xy M_eq obtain b1 where b1_Lft: "b1 \<in> ?Lft"
        and Xy_eq: "\<langle>X,y\<rangle> = \<langle>?Rc``{g(n)`b1}, ?Ra``{conn_lift(n, b1)}\<rangle>" by auto
    from Xt M_eq obtain b2 where b2_Lft: "b2 \<in> ?Lft"
        and Xt_eq: "\<langle>X,t\<rangle> = \<langle>?Rc``{g(n)`b2}, ?Ra``{conn_lift(n, b2)}\<rangle>" by auto
    have b1B: "b1 \<in> B(n)" and b1_cyc: "g(n)`b1 \<in> bc.tgt.Cycles(n)" using b1_Lft by auto
    have b2B: "b2 \<in> B(n)" and b2_cyc: "g(n)`b2 \<in> bc.tgt.Cycles(n)" using b2_Lft by auto
    from Xy_eq Xt_eq have X_eq: "X = ?Rc``{g(n)`b1}"
        and cls_eq: "?Rc``{g(n)`b1} = ?Rc``{g(n)`b2}"
        and y_eq: "y = ?Ra``{conn_lift(n, b1)}"
        and t_eq: "t = ?Ra``{conn_lift(n, b2)}" by auto
    from equiv_c b2_cyc cls_eq have rel_12: "\<langle>g(n)`b1, g(n)`b2\<rangle> \<in> ?Rc"
      using same_image_equiv by simp
    have hg: "group_homo(B(n), PB(n), C(n), PC(n), g(n))" using ses_hg[OF n] .
    have hfn: "group_homo(A(n \<rs> \<one>), PA(n \<rs> \<one>), B(n \<rs> \<one>), PB(n \<rs> \<one>), f(n \<rs> \<one>))"
      using ses_hf[OF pn] .
    have fn_fun: "f(n \<rs> \<one>) : A(n \<rs> \<one>) \<rightarrow> B(n \<rs> \<one>)"
      using group_homo.f_is_fun[OF hfn] .
    have dBn_fun: "dB(n) : B(n) \<rightarrow> B(n \<rs> \<one>)"
      using ses_cplx_B n unfolding IsAchainComplex_def Homomor_def by auto
    have dAn_fun: "dA(n) : A(n) \<rightarrow> A(n \<rs> \<one>)"
      using ses_cplx_A n unfolding IsAchainComplex_def Homomor_def by auto
    have inv_b2: "\<rm>\<^sup>B\<^bsub>n\<^esub> b2 \<in> B(n)"
      using group_homo.origin group0.inverse_in_group hg b2B
      unfolding group0_def by auto
    let ?b_diff = "b1 \<ra>\<^sup>B\<^bsub>n\<^esub> \<rm>\<^sup>B\<^bsub>n\<^esub> b2"
    have b_diff_B: "?b_diff \<in> B(n)"
      using group_homo.origin group0.group_op_closed hg b1B inv_b2
      unfolding group0_def by auto
    have g_diff_val: "g(n)`?b_diff =
        g(n)`b1 \<ra>\<^sup>C\<^bsub>n\<^esub> \<rm>\<^sup>C\<^bsub>n\<^esub> (g(n)`b2)"
    proof -
      have step1: "g(n)`?b_diff = g(n)`b1 \<ra>\<^sup>C\<^bsub>n\<^esub> g(n)`(\<rm>\<^sup>B\<^bsub>n\<^esub> b2)"
        using group_homo.f_hom[OF hg b1B inv_b2] by simp
      have step2: "g(n)`(\<rm>\<^sup>B\<^bsub>n\<^esub> b2) = \<rm>\<^sup>C\<^bsub>n\<^esub> (g(n)`b2)"
        using group_homo.f_inv[OF hg b2B] by simp
      from step1 step2 show ?thesis by simp
    qed
    have inv_cyc_eq: "GroupInv(bc.tgt.Cycles(n), bc.tgt.CycleOp(n))`(g(n)`b2) =
                      \<rm>\<^sup>C\<^bsub>n\<^esub> (g(n)`b2)"
    proof -
      interpret Cn: group0 "C(n)" "PC(n)"
        "TheNeutralElement(C(n), PC(n))" "\<lambda>x y. PC(n)`\<langle>x,y\<rangle>"
        "\<lambda>x. GroupInv(C(n), PC(n))`x"
        "\<lambda>s. Fold(PC(n), TheNeutralElement(C(n), PC(n)), s)"
        "\<lambda>m x. Fold(PC(n), TheNeutralElement(C(n), PC(n)), {\<langle>k,x\<rangle>. k \<in> m})"
        using ses_hg[OF n] unfolding group_homo_def group0_def by simp
      from Cn.group0_3_T2[OF bc.tgt.cycles_is_subgroup[OF n]] b2_cyc
      show ?thesis by blast
    qed
    have g_diff_bnd: "g(n)`?b_diff \<in> bc.tgt.Boundaries(n)"
    proof -
      from rel_12 have "bc.tgt.CycleOp(n)`\<langle>g(n)`b1,
            GroupInv(bc.tgt.Cycles(n), bc.tgt.CycleOp(n))`(g(n)`b2)\<rangle> \<in>
            bc.tgt.Boundaries(n)"
        unfolding QuotientGroupRel_def by auto
      with inv_cyc_eq have step1:
        "bc.tgt.CycleOp(n)`\<langle>g(n)`b1, \<rm>\<^sup>C\<^bsub>n\<^esub> (g(n)`b2)\<rangle> \<in>
         bc.tgt.Boundaries(n)" by simp
      have inv_cyc_b2: "GroupInv(bc.tgt.Cycles(n), bc.tgt.CycleOp(n))`(g(n)`b2) \<in>
                        bc.tgt.Cycles(n)"
        using group0.inverse_in_group[OF _ b2_cyc, of "bc.tgt.CycleOp(n)"]
              bc.tgt.cycles_is_group[OF n] unfolding group0_def by auto
      have pair_in: "\<langle>g(n)`b1, \<rm>\<^sup>C\<^bsub>n\<^esub> (g(n)`b2)\<rangle> \<in>
                     bc.tgt.Cycles(n) \<times> bc.tgt.Cycles(n)"
        using b1_cyc inv_cyc_b2 inv_cyc_eq by auto
      from restrict[of "PC(n)" "bc.tgt.Cycles(n) \<times> bc.tgt.Cycles(n)"
                      "\<langle>g(n)`b1, \<rm>\<^sup>C\<^bsub>n\<^esub> (g(n)`b2)\<rangle>"]
           pair_in step1
      have "g(n)`b1 \<ra>\<^sup>C\<^bsub>n\<^esub> \<rm>\<^sup>C\<^bsub>n\<^esub> (g(n)`b2) \<in> bc.tgt.Boundaries(n)"
        by (simp only: if_true)
      with g_diff_val show ?thesis by simp
    qed
    have g_diff_cyc: "g(n)`?b_diff \<in> bc.tgt.Cycles(n)"
      using bc.tgt.boundaries_in_cycles[OF n] g_diff_bnd by auto
    have cl_diff_bnd: "conn_lift(n, ?b_diff) \<in> ab.src.Boundaries(n \<rs> \<one>)"
      using conn_lift_bnd_to_bnd[OF n b_diff_B g_diff_bnd] .
    have cl1_A: "conn_lift(n, b1) \<in> A(n \<rs> \<one>)" using conn_lift_in_A[OF n b1B b1_cyc] .
    have cl2_A: "conn_lift(n, b2) \<in> A(n \<rs> \<one>)" using conn_lift_in_A[OF n b2B b2_cyc] .
    have cl_diff_A: "conn_lift(n, ?b_diff) \<in> A(n \<rs> \<one>)"
      using conn_lift_in_A[OF n b_diff_B g_diff_cyc] .
    have inv_cl2: "\<rm>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> (conn_lift(n, b2)) \<in> A(n \<rs> \<one>)"
      using group_homo.origin group0.inverse_in_group hfn cl2_A
      unfolding group0_def by auto
    let ?diff_cl = "conn_lift(n, b1) \<ra>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> \<rm>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> (conn_lift(n, b2))"
    have diff_cl_A: "?diff_cl \<in> A(n \<rs> \<one>)"
      using group_homo.origin group0.group_op_closed hfn cl1_A inv_cl2
      unfolding group0_def by auto
    have f_eq: "f(n \<rs> \<one>)`?diff_cl = f(n \<rs> \<one>)`(conn_lift(n, ?b_diff))"
    proof -
      have e1: "f(n \<rs> \<one>)`?diff_cl =
                f(n \<rs> \<one>)`(conn_lift(n, b1)) \<ra>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub>
                  f(n \<rs> \<one>)`(\<rm>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> (conn_lift(n, b2)))"
        using group_homo.f_hom[OF hfn cl1_A inv_cl2] by simp
      have e2: "f(n \<rs> \<one>)`(\<rm>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> (conn_lift(n, b2))) =
                \<rm>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> (f(n \<rs> \<one>)`(conn_lift(n, b2)))"
        using group_homo.f_inv[OF hfn cl2_A] by simp
      have e3: "f(n \<rs> \<one>)`(conn_lift(n, b1)) \<ra>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub>
                  \<rm>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> (f(n \<rs> \<one>)`(conn_lift(n, b2))) =
                dB(n)`b1 \<ra>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> \<rm>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> (dB(n)`b2)"
        using conn_lift_maps[OF n b1B b1_cyc] conn_lift_maps[OF n b2B b2_cyc] by simp
      have hg_dB: "group_homo(B(n), PB(n), B(n \<rs> \<one>), PB(n \<rs> \<one>), dB(n))"
      proof -
        have hom: "Homomor(dB(n), B(n), PB(n), B(n \<rs> \<one>), PB(n \<rs> \<one>))"
          using ses_cplx_B n unfolding IsAchainComplex_def by auto
        have g1: "IsAgroup(B(n), PB(n))" using ses_cplx_B n unfolding IsAchainComplex_def by auto
        have g2: "IsAgroup(B(n \<rs> \<one>), PB(n \<rs> \<one>))" using ses_cplx_B pn unfolding IsAchainComplex_def by auto
        from hom g1 g2 show ?thesis unfolding group_homo_def by simp
      qed
      have e4: "dB(n)`b1 \<ra>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> \<rm>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> (dB(n)`b2) =
                dB(n)`?b_diff"
      proof -
        have inv_b2': "\<rm>\<^sup>B\<^bsub>n\<^esub> b2 \<in> B(n)"
          using group_homo.origin group0.inverse_in_group hg_dB b2B
          unfolding group0_def by auto
        have hom_step: "dB(n)`?b_diff =
                        dB(n)`b1 \<ra>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> dB(n)`(\<rm>\<^sup>B\<^bsub>n\<^esub> b2)"
          using group_homo.f_hom[OF hg_dB b1B inv_b2'] by simp
        have inv_step: "dB(n)`(\<rm>\<^sup>B\<^bsub>n\<^esub> b2) =
                        \<rm>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> (dB(n)`b2)"
          using group_homo.f_inv[OF hg_dB b2B] by simp
        from hom_step inv_step show ?thesis by simp
      qed
      have e5: "dB(n)`?b_diff = f(n \<rs> \<one>)`(conn_lift(n, ?b_diff))"
        using conn_lift_maps[OF n b_diff_B g_diff_cyc] by simp
      from e1 e2 e3 e4 e5 show ?thesis by simp
    qed
    have diff_cl_eq: "?diff_cl = conn_lift(n, ?b_diff)"
      using ses_f_inj[OF pn] diff_cl_A cl_diff_A f_eq unfolding inj_def by auto
    have diff_cl_bnd: "?diff_cl \<in> ab.src.Boundaries(n \<rs> \<one>)"
      using diff_cl_eq cl_diff_bnd by simp
    have rel: "\<langle>conn_lift(n, b1), conn_lift(n, b2)\<rangle> \<in> ?Ra"
    proof -
      have cl1_cyc: "conn_lift(n, b1) \<in> ab.src.Cycles(n \<rs> \<one>)"
        using conn_lift_in_cycles[OF n b1B b1_cyc] .
      have cl2_cyc: "conn_lift(n, b2) \<in> ab.src.Cycles(n \<rs> \<one>)"
        using conn_lift_in_cycles[OF n b2B b2_cyc] .
      have inv_eq: "GroupInv(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>))`(conn_lift(n, b2)) =
                    \<rm>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> (conn_lift(n, b2))"
      proof -
        interpret An: group0 "A(n \<rs> \<one>)" "PA(n \<rs> \<one>)"
          "TheNeutralElement(A(n \<rs> \<one>), PA(n \<rs> \<one>))" "\<lambda>x y. PA(n \<rs> \<one>)`\<langle>x,y\<rangle>"
          "\<lambda>x. GroupInv(A(n \<rs> \<one>), PA(n \<rs> \<one>))`x"
          "\<lambda>s. Fold(PA(n \<rs> \<one>), TheNeutralElement(A(n \<rs> \<one>), PA(n \<rs> \<one>)), s)"
          "\<lambda>m x. Fold(PA(n \<rs> \<one>), TheNeutralElement(A(n \<rs> \<one>), PA(n \<rs> \<one>)), {\<langle>k,x\<rangle>. k \<in> m})"
          using hfn unfolding group_homo_def group0_def by simp
        from An.group0_3_T2[OF ab.src.cycles_is_subgroup[OF pn]] cl2_cyc
        show ?thesis by simp
      qed
      have pair_in: "\<langle>conn_lift(n, b1),
            GroupInv(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>))`(conn_lift(n, b2))\<rangle>
            \<in> ab.src.Cycles(n \<rs> \<one>) \<times> ab.src.Cycles(n \<rs> \<one>)"
        using cl1_cyc group0.inverse_in_group[OF _ cl2_cyc, of "ab.src.CycleOp(n \<rs> \<one>)"]
              ab.src.cycles_is_group[OF pn] unfolding group0_def by auto
      from restrict[of "PA(n \<rs> \<one>)" "ab.src.Cycles(n \<rs> \<one>) \<times> ab.src.Cycles(n \<rs> \<one>)"
                      "\<langle>conn_lift(n, b1),
                        GroupInv(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>))`(conn_lift(n, b2))\<rangle>"]
           pair_in inv_eq
      have cycop_eq:
        "ab.src.CycleOp(n \<rs> \<one>)`\<langle>conn_lift(n, b1),
           GroupInv(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>))`(conn_lift(n, b2))\<rangle> =
         ?diff_cl"
        by (simp only: if_true)
      show ?thesis
        unfolding QuotientGroupRel_def
        using cl1_cyc cl2_cyc cycop_eq diff_cl_bnd by auto
    qed
    from rel equiv_a
    have "?Ra``{conn_lift(n, b1)} = ?Ra``{conn_lift(n, b2)}"
      using conn_lift_in_cycles[OF n b1B b1_cyc]
            conn_lift_in_cycles[OF n b2B b2_cyc]
      by (auto simp: equiv_class_eq)
    with y_eq t_eq show "y = t" by simp
  qed
  from M_subset M_dom M_sv show ?thesis
    unfolding Pi_def function_def by auto
qed

text\<open>The connecting homomorphism $\delta_n \colon H_n(C) \to H_{n-1}(A)$ is a group
  homomorphism.\<close>

theorem (in ses_chain_complex) delta_is_hom:
  assumes n: "n \<in> ints"
  shows "Homomor(delta(n), bc.tgt.Hn(n), bc.tgt.HnOp(n),
                 ab.src.Hn(n \<rs> \<one>), ab.src.HnOp(n \<rs> \<one>))"
proof -
  have pn: "n \<rs> \<one> \<in> ints"
    using n Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  let ?Lft = "{x \<in> B(n). g(n)`x \<in> bc.tgt.Cycles(n)}"
  let ?Rc = "QuotientGroupRel(bc.tgt.Cycles(n), bc.tgt.CycleOp(n), bc.tgt.Boundaries(n))"
  let ?Ra = "QuotientGroupRel(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>), ab.src.Boundaries(n \<rs> \<one>))"
  let ?M = "delta(n)"
  have M_eq: "?M = {\<langle>?Rc``{g(n)`b}, ?Ra``{conn_lift(n, b)}\<rangle>. b \<in> ?Lft}"
    unfolding delta_def by simp
  have M_fun: "?M : bc.tgt.Hn(n) \<rightarrow> ab.src.Hn(n \<rs> \<one>)"
    using delta_fun[OF n] .
  have equiv_c: "equiv(bc.tgt.Cycles(n), ?Rc)"
    using bc.tgt.cycles_is_subgroup[OF n]
          group0.Group_ZF_2_4_L3[OF _ bc.tgt.boundaries_subgroup_cycles[OF n]]
    unfolding IsAsubgroup_def group0_def by auto
  have equiv_a: "equiv(ab.src.Cycles(n \<rs> \<one>), ?Ra)"
    using ab.src.cycles_is_subgroup[OF pn]
          group0.Group_ZF_2_4_L3[OF _ ab.src.boundaries_subgroup_cycles[OF pn]]
    unfolding IsAsubgroup_def group0_def by simp
  have normal_c: "IsAnormalSubgroup(bc.tgt.Cycles(n), bc.tgt.CycleOp(n), bc.tgt.Boundaries(n))"
    using Group_ZF_2_4_L6(1)[OF bc.tgt.cycles_is_group[OF n]
                               bc.tgt.cycles_is_abelian[OF n]
                               bc.tgt.boundaries_subgroup_cycles[OF n]] by simp
  have normal_a: "IsAnormalSubgroup(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>), ab.src.Boundaries(n \<rs> \<one>))"
    using Group_ZF_2_4_L6(1)[OF ab.src.cycles_is_group[OF pn]
                               ab.src.cycles_is_abelian[OF pn]
                               ab.src.boundaries_subgroup_cycles[OF pn]] by simp
  have cong_c: "Congruent2(?Rc, bc.tgt.CycleOp(n))"
    using Group_ZF_2_4_L5A bc.tgt.cycles_is_group[OF n] normal_c by simp
  have cong_a: "Congruent2(?Ra, ab.src.CycleOp(n \<rs> \<one>))"
    using Group_ZF_2_4_L5A ab.src.cycles_is_group[OF pn] normal_a by simp
  have gn_fun: "g(n) : B(n) \<rightarrow> C(n)"
    using ses_map_g n unfolding IsAchainMap_def Homomor_def by auto
  have hg: "group_homo(B(n), PB(n), C(n), PC(n), g(n))" using ses_hg[OF n] .
  have hfpn: "group_homo(A(n \<rs> \<one>), PA(n \<rs> \<one>), B(n \<rs> \<one>), PB(n \<rs> \<one>), f(n \<rs> \<one>))"
    using ses_hf[OF pn] .
  have hg_dB: "group_homo(B(n), PB(n), B(n \<rs> \<one>), PB(n \<rs> \<one>), dB(n))"
  proof -
    have hom: "Homomor(dB(n), B(n), PB(n), B(n \<rs> \<one>), PB(n \<rs> \<one>))"
      using ses_cplx_B n unfolding IsAchainComplex_def by auto
    have g1: "IsAgroup(B(n), PB(n))" using ses_cplx_B n unfolding IsAchainComplex_def by auto
    have g2: "IsAgroup(B(n \<rs> \<one>), PB(n \<rs> \<one>))" using ses_cplx_B pn unfolding IsAchainComplex_def by auto
    from hom g1 g2 show ?thesis unfolding group_homo_def by simp
  qed
  have gnB_C: "g(n)``B(n) = C(n)"
  proof -
    have ea_C: "IsExactAt(g(n), B(n), ZeroMap(C(n), 1, TrivOp), 1, TrivOp)"
      using deg_ses[OF n] unfolding IsAshortExactSequence_def by auto
    have grpC: "IsAgroup(C(n), PC(n))"
      using deg_ses[OF n] unfolding IsAshortExactSequence_def group_homo_def by auto
    from ea_C show ?thesis
      using ZeroMap_preimage_full[OF grpC trivial_group] TrivOp_ne unfolding IsExactAt_def by simp
  qed
  have morphism: "IsMorphism(bc.tgt.Hn(n), bc.tgt.HnOp(n), ab.src.HnOp(n \<rs> \<one>), ?M)"
    unfolding IsMorphism_def
  proof (intro ballI)
    fix X1 X2 assume X1: "X1 \<in> bc.tgt.Hn(n)" and X2: "X2 \<in> bc.tgt.Hn(n)"
    show "?M`(bc.tgt.HnOp(n)`\<langle>X1, X2\<rangle>) = ab.src.HnOp(n \<rs> \<one>)`\<langle>?M`X1, ?M`X2\<rangle>"
    proof -
      from X1 obtain c1 where c1: "c1 \<in> bc.tgt.Cycles(n)" and X1_eq: "X1 = ?Rc``{c1}"
        unfolding bc.tgt.Hn_def quotient_def by auto
      from X2 obtain c2 where c2: "c2 \<in> bc.tgt.Cycles(n)" and X2_eq: "X2 = ?Rc``{c2}"
        unfolding bc.tgt.Hn_def quotient_def by auto
      have c1C: "c1 \<in> C(n)"
        using bc.tgt.cycles_is_subgroup[OF n] group0.group0_3_L2 bc.tgt.cplx_group[OF n] c1
        unfolding group0_def by blast
      have c2C: "c2 \<in> C(n)"
        using bc.tgt.cycles_is_subgroup[OF n] group0.group0_3_L2 bc.tgt.cplx_group[OF n] c2
        unfolding group0_def by blast
      from func_imagedef[OF gn_fun] have GB:"g(n)``(B(n)) = {g(n)`b. b\<in>B(n)}"
        by auto
      with gnB_C have CgB: "C(n) = {g(n)`b. b\<in>B(n)}" by auto
      from c1C obtain b1 where b1B: "b1 \<in> B(n)" and gnb1: "g(n)`b1 = c1"
        using CgB by auto
      from c2C obtain b2 where b2B: "b2 \<in> B(n)" and gnb2: "g(n)`b2 = c2"
        using CgB by auto
      have b1_cyc: "g(n)`b1 \<in> bc.tgt.Cycles(n)" using gnb1 c1 by simp
      have b2_cyc: "g(n)`b2 \<in> bc.tgt.Cycles(n)" using gnb2 c2 by simp
      let ?cl1 = "conn_lift(n, b1)"
      let ?cl2 = "conn_lift(n, b2)"
      have cl1_cyc: "?cl1 \<in> ab.src.Cycles(n \<rs> \<one>)"
        using conn_lift_in_cycles[OF n b1B b1_cyc] .
      have cl2_cyc: "?cl2 \<in> ab.src.Cycles(n \<rs> \<one>)"
        using conn_lift_in_cycles[OF n b2B b2_cyc] .
      have cl1_A: "?cl1 \<in> A(n \<rs> \<one>)" using conn_lift_in_A[OF n b1B b1_cyc] .
      have cl2_A: "?cl2 \<in> A(n \<rs> \<one>)" using conn_lift_in_A[OF n b2B b2_cyc] .
      have b_sum_B: "b1 \<ra>\<^sup>B\<^bsub>n\<^esub> b2 \<in> B(n)"
        using group_homo.origin group0.group_op_closed hg b1B b2B unfolding group0_def by auto
      have g_b_sum: "g(n)`(b1 \<ra>\<^sup>B\<^bsub>n\<^esub> b2) = c1 \<ra>\<^sup>C\<^bsub>n\<^esub> c2"
        using group_homo.f_hom[OF hg b1B b2B] gnb1 gnb2 by simp
      from c1 c2 have "\<langle>c1,c2\<rangle>: bc.tgt.Cycles(n) \<times> bc.tgt.Cycles(n)" by auto
      then have cycop_c_eq: "bc.tgt.CycleOp(n)`\<langle>c1, c2\<rangle> = c1 \<ra>\<^sup>C\<^bsub>n\<^esub> c2"
        using restrict[of "PC(n)" "bc.tgt.Cycles(n) \<times> bc.tgt.Cycles(n)" "\<langle>c1, c2\<rangle>"]
        by (simp only: if_true)
      have c_sum_cyc: "bc.tgt.CycleOp(n)`\<langle>c1, c2\<rangle> \<in> bc.tgt.Cycles(n)"
        using bc.tgt.cycles_is_group[OF n] c1 c2 group0.group_op_closed[of "bc.tgt.Cycles(n)"
            "restrict(PC(n),bc.tgt.Cycles(n)\<times>bc.tgt.Cycles(n))"] unfolding group0_def by simp
      have b_sum_cyc: "g(n)`(b1 \<ra>\<^sup>B\<^bsub>n\<^esub> b2) \<in> bc.tgt.Cycles(n)"
        using g_b_sum cycop_c_eq c_sum_cyc by simp
      have b_sum_lft: "b1 \<ra>\<^sup>B\<^bsub>n\<^esub> b2 \<in> ?Lft" using b_sum_B b_sum_cyc by auto
      have cl_sum_eq: "conn_lift(n, b1 \<ra>\<^sup>B\<^bsub>n\<^esub> b2) = ?cl1 \<ra>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> ?cl2"
      proof -
        have cl_sum_A: "?cl1 \<ra>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> ?cl2 \<in> A(n \<rs> \<one>)"
          using group_homo.origin group0.group_op_closed hfpn cl1_A cl2_A
          unfolding group0_def by auto
        have f_cl_sum: "f(n \<rs> \<one>)`(?cl1 \<ra>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> ?cl2) = dB(n)`(b1 \<ra>\<^sup>B\<^bsub>n\<^esub> b2)"
        proof -
          have e1: "f(n \<rs> \<one>)`(?cl1 \<ra>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> ?cl2) =
                    f(n \<rs> \<one>)`?cl1 \<ra>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> f(n \<rs> \<one>)`?cl2"
            using group_homo.f_hom[OF hfpn cl1_A cl2_A] by simp
          have e2: "f(n \<rs> \<one>)`?cl1 = dB(n)`b1" using conn_lift_maps[OF n b1B b1_cyc] by simp
          have e3: "f(n \<rs> \<one>)`?cl2 = dB(n)`b2" using conn_lift_maps[OF n b2B b2_cyc] by simp
          have e4: "dB(n)`b1 \<ra>\<^sup>B\<^bsub>n \<rs> \<one>\<^esub> dB(n)`b2 = dB(n)`(b1 \<ra>\<^sup>B\<^bsub>n\<^esub> b2)"
            using group_homo.f_hom[OF hg_dB b1B b2B] by simp
          from e1 e2 e3 e4 show ?thesis by simp
        qed
        have conn_lift_val: "f(n \<rs> \<one>)`(conn_lift(n, b1 \<ra>\<^sup>B\<^bsub>n\<^esub> b2)) = dB(n)`(b1 \<ra>\<^sup>B\<^bsub>n\<^esub> b2)"
          using conn_lift_maps[OF n b_sum_B b_sum_cyc] by simp
        have conn_lift_in: "conn_lift(n, b1 \<ra>\<^sup>B\<^bsub>n\<^esub> b2) \<in> A(n \<rs> \<one>)"
          using conn_lift_in_A[OF n b_sum_B b_sum_cyc] .
        from ses_f_inj[OF pn] cl_sum_A conn_lift_in f_cl_sum conn_lift_val
        show ?thesis unfolding inj_def by auto
      qed
      have pair1: "\<langle>X1, ?Ra``{?cl1}\<rangle> \<in> ?M"
        using M_eq b1B b1_cyc gnb1 X1_eq by auto
      have pair2: "\<langle>X2, ?Ra``{?cl2}\<rangle> \<in> ?M"
        using M_eq b2B b2_cyc gnb2 X2_eq by auto
      have step1: "?M`X1 = ?Ra``{?cl1}" using apply_equality[OF pair1 M_fun] .
      have step2: "?M`X2 = ?Ra``{?cl2}" using apply_equality[OF pair2 M_fun] .
      have op_c: "bc.tgt.HnOp(n)`\<langle>X1, X2\<rangle> = ?Rc``{bc.tgt.CycleOp(n)`\<langle>c1, c2\<rangle>}"
        using group0.Group_ZF_2_2_L2[OF _ equiv_c cong_c _ c1 c2] X1_eq X2_eq
              bc.tgt.cycles_is_group[OF n]
        unfolding bc.tgt.HnOp_def QuotientGroupOp_def group0_def by auto
      have g_b_sum': "g(n)`(b1 \<ra>\<^sup>B\<^bsub>n\<^esub> b2) = bc.tgt.CycleOp(n)`\<langle>c1, c2\<rangle>"
        using g_b_sum cycop_c_eq by simp
      have prd_m:"⟨QuotientGroupRel
       (bc.tgt.Cycles(n), restrict(PC(n), bc.tgt.Cycles(n) × bc.tgt.Cycles(n)),
        bc.tgt.Boundaries(n)) ``
      {g(n) ` (b1 \<ra>\<^sup>B\<^bsub>n\<^esub> b2)},
      QuotientGroupRel
       (ab.src.Cycles(n \<rs> 𝟭),
        restrict(PA(n \<rs> 𝟭), ab.src.Cycles(n \<rs> 𝟭) × ab.src.Cycles(n \<rs> 𝟭)),
        ab.src.Boundaries(n \<rs> 𝟭)) ``
      {conn_lift(n, b1 \<ra>\<^sup>B\<^bsub>n\<^esub> b2)}⟩\<in>?M" using M_eq b_sum_lft by auto
      then have pair_sum: "\<langle>?Rc``{bc.tgt.CycleOp(n)`\<langle>c1, c2\<rangle>},
                       ?Ra``{conn_lift(n, b1 \<ra>\<^sup>B\<^bsub>n\<^esub> b2)}\<rangle> \<in> ?M"
        using g_b_sum' by auto
      have step3: "?M`(bc.tgt.HnOp(n)`\<langle>X1, X2\<rangle>) = ?Ra``{conn_lift(n, b1 \<ra>\<^sup>B\<^bsub>n\<^esub> b2)}"
        using op_c apply_equality[OF pair_sum M_fun] by simp
      from cl1_cyc cl2_cyc have "\<langle>?cl1,?cl2\<rangle>\<in>ab.src.Cycles(n \<rs> \<one>) \<times> ab.src.Cycles(n \<rs> \<one>)"
        by auto
      then have cycop_a_eq: "ab.src.CycleOp(n \<rs> \<one>)`\<langle>?cl1, ?cl2\<rangle> = ?cl1 \<ra>\<^sup>A\<^bsub>n \<rs> \<one>\<^esub> ?cl2"
        using restrict[of "PA(n \<rs> \<one>)" "ab.src.Cycles(n \<rs> \<one>) \<times> ab.src.Cycles(n \<rs> \<one>)"
                        "\<langle>?cl1, ?cl2\<rangle>"]
        by (simp only: if_true)
      have op_a: "ab.src.HnOp(n \<rs> \<one>)`\<langle>?Ra``{?cl1}, ?Ra``{?cl2}\<rangle> =
                  ?Ra``{ab.src.CycleOp(n \<rs> \<one>)`\<langle>?cl1, ?cl2\<rangle>}"
        using group0.Group_ZF_2_2_L2[OF _ equiv_a cong_a _ cl1_cyc cl2_cyc]
              ab.src.cycles_is_group[OF pn]
        unfolding ab.src.HnOp_def QuotientGroupOp_def group0_def by auto
      from step3 cl_sum_eq cycop_a_eq op_a step1 step2
      show "?M`(bc.tgt.HnOp(n)`\<langle>X1, X2\<rangle>) = ab.src.HnOp(n \<rs> \<one>)`\<langle>?M`X1, ?M`X2\<rangle>"
        by simp
    qed
  qed
  from M_fun morphism show ?thesis unfolding Homomor_def by simp
qed

text\<open>The map induced by $f$ on $H_{n-1}$ evaluates on a coset representative: for
  $z \in Z_{n-1}(A)$ it sends $[z]$ to $[f_{n-1}(z)]$ in $H_{n-1}(B)$.\<close>

lemma (in ses_chain_complex) ab_hn_map_apply:
  assumes n: "n \<in> ints" and z: "z \<in> ab.src.Cycles(n \<rs> \<one>)"
  shows "ab.Hn_map(n \<rs> \<one>)`
    (QuotientGroupRel(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>), ab.src.Boundaries(n \<rs> \<one>))``{z})
    = QuotientGroupRel(ab.tgt.Cycles(n \<rs> \<one>), ab.tgt.CycleOp(n \<rs> \<one>), ab.tgt.Boundaries(n \<rs> \<one>))``{f(n \<rs> \<one>)`z}"
proof -
  let ?Ra = "QuotientGroupRel(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>), ab.src.Boundaries(n \<rs> \<one>))"
  let ?Rb = "QuotientGroupRel(ab.tgt.Cycles(n \<rs> \<one>), ab.tgt.CycleOp(n \<rs> \<one>), ab.tgt.Boundaries(n \<rs> \<one>))"
  have pn: "n \<rs> \<one> \<in> ints"
    using n Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  have M_fun: "ab.Hn_map(n \<rs> \<one>) : ab.src.Hn(n \<rs> \<one>) \<rightarrow> ab.tgt.Hn(n \<rs> \<one>)"
    using ab.Hn_map_is_hom[OF pn] unfolding Homomor_def by simp
  have pair: "\<langle>?Ra``{z}, ?Rb``{f(n \<rs> \<one>)`z}\<rangle> \<in> ab.Hn_map(n \<rs> \<one>)"
    unfolding ab.Hn_map_def using z by auto
  show ?thesis using apply_equality[OF pair M_fun] .
qed

text\<open>The boundary $d_n^B(b)$ represents the zero class in $H_{n-1}(B)$ for any $b \in B_n$.\<close>

lemma (in ses_chain_complex) dBb_class_zero:
  assumes n: "n \<in> ints" and b: "b \<in> B(n)"
  shows "QuotientGroupRel(ab.tgt.Cycles(n \<rs> \<one>), ab.tgt.CycleOp(n \<rs> \<one>), ab.tgt.Boundaries(n \<rs> \<one>))``{dB(n)`b}
    = TheNeutralElement(ab.tgt.Hn(n \<rs> \<one>), ab.tgt.HnOp(n \<rs> \<one>))"
proof -
  let ?Rb = "QuotientGroupRel(ab.tgt.Cycles(n \<rs> \<one>), ab.tgt.CycleOp(n \<rs> \<one>), ab.tgt.Boundaries(n \<rs> \<one>))"
  have pn: "n \<rs> \<one> \<in> ints"
    using n Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  have arith: "(n \<rs> \<one>) \<ra> \<one> = n"
    using Int_ZF_1_L8A(2) group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3)] n by simp
  have dBn_fun: "dB(n) : B(n) \<rightarrow> B(n \<rs> \<one>)"
    using ses_cplx_B n unfolding IsAchainComplex_def Homomor_def by auto
  have dBb_bnd: "dB(n)`b \<in> ab.tgt.Boundaries(n \<rs> \<one>)"
    using arith dBn_fun b func_imagedef[OF dBn_fun subset_refl] by auto
  have dBb_cyc: "dB(n)`b \<in> ab.tgt.Cycles(n \<rs> \<one>)"
    using ab.tgt.boundaries_in_cycles[OF pn] dBb_bnd by auto
  have normal_b: "IsAnormalSubgroup(ab.tgt.Cycles(n \<rs> \<one>), ab.tgt.CycleOp(n \<rs> \<one>), ab.tgt.Boundaries(n \<rs> \<one>))"
    using Group_ZF_2_4_L6(1)[OF ab.tgt.cycles_is_group[OF pn]
                               ab.tgt.cycles_is_abelian[OF pn]
                               ab.tgt.boundaries_subgroup_cycles[OF pn]] by simp
  interpret BnCyc: group0 "ab.tgt.Cycles(n \<rs> \<one>)" "ab.tgt.CycleOp(n \<rs> \<one>)"
    "TheNeutralElement(ab.tgt.Cycles(n \<rs> \<one>), ab.tgt.CycleOp(n \<rs> \<one>))"
    "\<lambda>x y. ab.tgt.CycleOp(n \<rs> \<one>)`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(ab.tgt.Cycles(n \<rs> \<one>), ab.tgt.CycleOp(n \<rs> \<one>))`x"
    "\<lambda>s. Fold(ab.tgt.CycleOp(n \<rs> \<one>), TheNeutralElement(ab.tgt.Cycles(n \<rs> \<one>), ab.tgt.CycleOp(n \<rs> \<one>)), s)"
    "\<lambda>na x. Fold(ab.tgt.CycleOp(n \<rs> \<one>), TheNeutralElement(ab.tgt.Cycles(n \<rs> \<one>), ab.tgt.CycleOp(n \<rs> \<one>)), {\<langle>k, x\<rangle>. k \<in> na})"
    using ab.tgt.cycles_is_group[OF pn] unfolding group0_def by simp
  from BnCyc.Group_ZF_2_4_L5E[OF normal_b dBb_cyc] dBb_bnd
  have cls: "?Rb``{dB(n)`b} = TheNeutralElement(
    ab.tgt.Cycles(n \<rs> \<one>) // ?Rb,
    QuotientGroupOp(ab.tgt.Cycles(n \<rs> \<one>), ab.tgt.CycleOp(n \<rs> \<one>), ab.tgt.Boundaries(n \<rs> \<one>)))"
    by simp
  show ?thesis unfolding ab.tgt.Hn_def ab.tgt.HnOp_def using cls by simp
qed

text\<open>Exactness at $H_{n-1}(A)$: the image of $\delta_n$ equals the kernel of
  $f_* \colon H_{n-1}(A) \to H_{n-1}(B)$.\<close>

theorem (in ses_chain_complex) les_exact_at_HnA:
  assumes n: "n \<in> ints"
  shows "IsExactAt(delta(n), bc.tgt.Hn(n), ab.Hn_map(n \<rs> \<one>),
                   ab.tgt.Hn(n \<rs> \<one>), ab.tgt.HnOp(n \<rs> \<one>))"
proof -
  have pn: "n \<rs> \<one> \<in> ints"
    using n Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  let ?Ra = "QuotientGroupRel(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>), ab.src.Boundaries(n \<rs> \<one>))"
  let ?Rb = "QuotientGroupRel(ab.tgt.Cycles(n \<rs> \<one>), ab.tgt.CycleOp(n \<rs> \<one>), ab.tgt.Boundaries(n \<rs> \<one>))"
  let ?Rc = "QuotientGroupRel(bc.tgt.Cycles(n), bc.tgt.CycleOp(n), bc.tgt.Boundaries(n))"
  let ?Lft = "{x \<in> B(n). g(n)`x \<in> bc.tgt.Cycles(n)}"
  let ?neu_HnB = "TheNeutralElement(ab.tgt.Hn(n \<rs> \<one>), ab.tgt.HnOp(n \<rs> \<one>))"
  have arith: "(n \<rs> \<one>) \<ra> \<one> = n"
    using Int_ZF_1_L8A(2) group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3)] n by simp
  have delta_fun: "delta(n) : bc.tgt.Hn(n) \<rightarrow> ab.src.Hn(n \<rs> \<one>)"
    using delta_fun[OF n] .
  have hn_map_fun: "ab.Hn_map(n \<rs> \<one>) : ab.src.Hn(n \<rs> \<one>) \<rightarrow> ab.tgt.Hn(n \<rs> \<one>)"
    using ab.Hn_map_is_hom[OF pn] unfolding Homomor_def by simp
  have fn_nm1_fun: "f(n \<rs> \<one>) : A(n \<rs> \<one>) \<rightarrow> B(n \<rs> \<one>)"
    using ses_map_f pn unfolding IsAchainMap_def Homomor_def by auto
  have fn_nm1_inj: "f(n \<rs> \<one>) \<in> inj(A(n \<rs> \<one>), B(n \<rs> \<one>))"
    using ses_f_inj[OF pn] .
  have dBn_fun: "dB(n) : B(n) \<rightarrow> B(n \<rs> \<one>)"
    using ses_cplx_B n unfolding IsAchainComplex_def Homomor_def by auto
  have normal_b: "IsAnormalSubgroup(ab.tgt.Cycles(n \<rs> \<one>), ab.tgt.CycleOp(n \<rs> \<one>), ab.tgt.Boundaries(n \<rs> \<one>))"
    using Group_ZF_2_4_L6(1)[OF ab.tgt.cycles_is_group[OF pn]
                               ab.tgt.cycles_is_abelian[OF pn]
                               ab.tgt.boundaries_subgroup_cycles[OF pn]] by simp
  have equiv_c: "equiv(bc.tgt.Cycles(n), ?Rc)"
    using bc.tgt.cycles_is_subgroup[OF n]
          group0.Group_ZF_2_4_L3[OF _ bc.tgt.boundaries_subgroup_cycles[OF n]]
    unfolding IsAsubgroup_def group0_def by auto
  have equiv_a: "equiv(ab.src.Cycles(n \<rs> \<one>), ?Ra)"
    using ab.src.cycles_is_subgroup[OF pn]
          group0.Group_ZF_2_4_L3[OF _ ab.src.boundaries_subgroup_cycles[OF pn]]
    unfolding IsAsubgroup_def group0_def by simp
  have gn_fun: "g(n) : B(n) \<rightarrow> C(n)"
    using ses_map_g n unfolding IsAchainMap_def Homomor_def by auto
  have gnB_C: "g(n)``B(n) = C(n)"
  proof -
    have ea_C: "IsExactAt(g(n), B(n), ZeroMap(C(n), 1, TrivOp), 1, TrivOp)"
      using deg_ses[OF n] unfolding IsAshortExactSequence_def by auto
    have grpC: "IsAgroup(C(n), PC(n))"
      using deg_ses[OF n] unfolding IsAshortExactSequence_def group_homo_def by auto
    from ea_C show ?thesis
      using ZeroMap_preimage_full[OF grpC trivial_group] TrivOp_ne unfolding IsExactAt_def by simp
  qed
  interpret BnCyc: group0 "ab.tgt.Cycles(n \<rs> \<one>)" "ab.tgt.CycleOp(n \<rs> \<one>)"
    "TheNeutralElement(ab.tgt.Cycles(n \<rs> \<one>), ab.tgt.CycleOp(n \<rs> \<one>))"
    "\<lambda>x y. ab.tgt.CycleOp(n \<rs> \<one>)`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(ab.tgt.Cycles(n \<rs> \<one>), ab.tgt.CycleOp(n \<rs> \<one>))`x"
    "\<lambda>s. Fold(ab.tgt.CycleOp(n \<rs> \<one>), TheNeutralElement(ab.tgt.Cycles(n \<rs> \<one>), ab.tgt.CycleOp(n \<rs> \<one>)), s)"
    "\<lambda>na x. Fold(ab.tgt.CycleOp(n \<rs> \<one>), TheNeutralElement(ab.tgt.Cycles(n \<rs> \<one>), ab.tgt.CycleOp(n \<rs> \<one>)), {\<langle>k, x\<rangle>. k \<in> na})"
    using ab.tgt.cycles_is_group[OF pn] unfolding group0_def by simp
  show ?thesis unfolding IsExactAt_def
  proof (rule equalityI)
    show "delta(n)``bc.tgt.Hn(n) \<subseteq> ab.Hn_map(n \<rs> \<one>)-``{?neu_HnB}"
    proof
      fix X assume Xim: "X \<in> delta(n)``bc.tgt.Hn(n)"
      from func_imagedef[OF delta_fun subset_refl] Xim obtain Y where
        Y_Hn: "Y \<in> bc.tgt.Hn(n)" and X_eq: "X = delta(n)`Y" by auto
      from Y_Hn obtain c where c: "c \<in> bc.tgt.Cycles(n)" and Y_eq: "Y = ?Rc``{c}"
        unfolding bc.tgt.Hn_def quotient_def by auto
      have cC: "c \<in> C(n)"
        using bc.tgt.cycles_is_subgroup[OF n] group0.group0_3_L2 bc.tgt.cplx_group[OF n] c
        unfolding group0_def by blast
      from cC gnB_C have "c \<in> g(n)``B(n)" by auto
      then obtain b where bB: "b \<in> B(n)" and gnb: "g(n)`b = c"
        using func_imagedef[OF gn_fun subset_refl] by auto
      have b_cyc: "g(n)`b \<in> bc.tgt.Cycles(n)" using gnb c by simp
      have bLft: "b \<in> ?Lft" using bB b_cyc by auto
      have clb: "conn_lift(n, b) \<in> ab.src.Cycles(n \<rs> \<one>)"
        using conn_lift_in_cycles[OF n bB b_cyc] .
      have delta_Y: "delta(n)`Y = ?Ra``{conn_lift(n, b)}"
      proof -
        have pair: "\<langle>?Rc``{g(n)`b}, ?Ra``{conn_lift(n, b)}\<rangle> \<in> delta(n)"
          unfolding delta_def using bLft by auto
        from Y_eq gnb show ?thesis using apply_equality[OF pair delta_fun] by simp
      qed
      have X_in_Hn: "X \<in> ab.src.Hn(n \<rs> \<one>)"
        using X_eq delta_Y clb equiv_a unfolding ab.src.Hn_def quotient_def by auto
      have X_map: "ab.Hn_map(n \<rs> \<one>)`X = ?neu_HnB"
        using X_eq delta_Y ab_hn_map_apply[OF n clb]
              conn_lift_maps[OF n bB b_cyc] dBb_class_zero[OF n bB] by simp
      show "X \<in> ab.Hn_map(n \<rs> \<one>)-``{?neu_HnB}"
        using func1_1_L15[OF hn_map_fun] X_in_Hn X_map by auto
    qed
    show "ab.Hn_map(n \<rs> \<one>)-``{?neu_HnB} \<subseteq> delta(n)``bc.tgt.Hn(n)"
    proof
      fix X assume Xker: "X \<in> ab.Hn_map(n \<rs> \<one>)-``{?neu_HnB}"
      have X_in_Hn: "X \<in> ab.src.Hn(n \<rs> \<one>)"
        using Xker func1_1_L15[OF hn_map_fun] by auto
      have X_map_neu: "ab.Hn_map(n \<rs> \<one>)`X = ?neu_HnB"
        using Xker func1_1_L15[OF hn_map_fun] by auto
      from X_in_Hn obtain z where z: "z \<in> ab.src.Cycles(n \<rs> \<one>)"
        and X_eq: "X = ?Ra``{z}"
        unfolding ab.src.Hn_def quotient_def by auto
      have zA: "z \<in> A(n \<rs> \<one>)"
        using ab.src.cycles_is_subgroup[OF pn] group0.group0_3_L2 ab.src.cplx_group[OF pn] z
        unfolding group0_def by blast
      have fnz_cyc: "f(n \<rs> \<one>)`z \<in> ab.tgt.Cycles(n \<rs> \<one>)"
        using ab.cmap_maps_cycles[OF pn z] .
      have cls_val: "?Rb``{f(n \<rs> \<one>)`z} = ?neu_HnB"
        using X_eq ab_hn_map_apply[OF n z] X_map_neu by simp
      have fnz_bnd: "f(n \<rs> \<one>)`z \<in> ab.tgt.Boundaries(n \<rs> \<one>)"
        using BnCyc.Group_ZF_2_4_L5E[OF normal_b fnz_cyc] cls_val
        unfolding ab.tgt.Hn_def ab.tgt.HnOp_def by simp
      from fnz_bnd arith have fnz_in_im: "f(n \<rs> \<one>)`z \<in> (dB(n))``(B(n))" by simp
      from func_imagedef[OF dBn_fun subset_refl] fnz_in_im obtain b where
        bB: "b \<in> B(n)" and dBb_eq: "dB(n)`b = f(n \<rs> \<one>)`z" by auto
      have b_cyc: "g(n)`b \<in> bc.tgt.Cycles(n)"
      proof -
        have gnb_C: "g(n)`b \<in> C(n)" using apply_type[OF gn_fun bB] .
        have dCn_fun: "dC(n) : C(n) \<rightarrow> C(n \<rs> \<one>)"
          using ses_cplx_C n unfolding IsAchainComplex_def Homomor_def by auto
        have gn_nm1_fun: "g(n \<rs> \<one>) : B(n \<rs> \<one>) \<rightarrow> C(n \<rs> \<one>)"
          using ses_map_g pn unfolding IsAchainMap_def Homomor_def by auto
        have dCn_gnb: "dC(n)`(g(n)`b) = g(n \<rs> \<one>)`(f(n \<rs> \<one>)`z)"
        proof -
          have e1: "dC(n)`(g(n)`b) = (dC(n) O g(n))`b"
            using comp_fun_apply[OF gn_fun bB] by simp
          have e2: "(g(n \<rs> \<one>) O dB(n))`b = g(n \<rs> \<one>)`(dB(n)`b)"
            using comp_fun_apply[OF dBn_fun bB] by simp
          from e1 e2 bc.cmap_comm[OF n] dBb_eq show ?thesis by simp
        qed
        have gfz_zero: "g(n \<rs> \<one>)`(f(n \<rs> \<one>)`z) = TheNeutralElement(C(n \<rs> \<one>), PC(n \<rs> \<one>))"
        proof -
          have fz_in_im: "f(n \<rs> \<one>)`z \<in> f(n \<rs> \<one>)``A(n \<rs> \<one>)"
            using func_imagedef[OF fn_nm1_fun subset_refl] zA by auto
          have fz_in_ker: "f(n \<rs> \<one>)`z \<in> g(n \<rs> \<one>)-``{TheNeutralElement(C(n \<rs> \<one>), PC(n \<rs> \<one>))}"
            using fz_in_im ses_im_eq_ker[OF pn] by auto
          from func1_1_L15[OF gn_nm1_fun] fz_in_ker
          show ?thesis using apply_type[OF fn_nm1_fun zA] by auto
        qed
        from func1_1_L15[OF dCn_fun] gnb_C dCn_gnb gfz_zero show ?thesis by auto
      qed
      have bLft: "b \<in> ?Lft" using bB b_cyc by auto
      have cl_eq: "conn_lift(n, b) = z"
      proof -
        have clb_A: "conn_lift(n, b) \<in> A(n \<rs> \<one>)"
          using conn_lift_in_A[OF n bB b_cyc] .
        have f_clb: "f(n \<rs> \<one>)`(conn_lift(n, b)) = f(n \<rs> \<one>)`z"
          using conn_lift_maps[OF n bB b_cyc] dBb_eq by simp
        from fn_nm1_inj clb_A zA f_clb show ?thesis unfolding inj_def by auto
      qed
      have Y_in_Hn: "?Rc``{g(n)`b} \<in> bc.tgt.Hn(n)"
        using b_cyc equiv_c unfolding bc.tgt.Hn_def quotient_def by auto
      have "\<langle>?Rc``{g(n)`b},?Ra``{conn_lift(n, b)}\<rangle> \<in> delta(n)"
        using bLft unfolding delta_def by auto
      then have delta_app: "delta(n)`(?Rc``{g(n)`b}) = ?Ra``{conn_lift(n, b)}"
        using apply_equality[OF _ delta_fun] by auto
      have X_is: "X = delta(n)`(?Rc``{g(n)`b})"
        using X_eq cl_eq delta_app by simp
      from func_imagedef[OF delta_fun subset_refl] Y_in_Hn X_is
      show "X \<in> delta(n)``bc.tgt.Hn(n)" by auto
    qed
  qed
qed

text\<open>Exactness at $H_n(B)$: the image of $f_*$ equals the kernel of $g_*$.\<close>

theorem (in ses_chain_complex) les_exact_at_HnB:
  assumes n: "n \<in> ints"
  shows "IsExactAt(ab.Hn_map(n), ab.src.Hn(n), bc.Hn_map(n),
                   bc.tgt.Hn(n), bc.tgt.HnOp(n))"
proof -
  let ?Ra = "QuotientGroupRel(ab.src.Cycles(n), ab.src.CycleOp(n), ab.src.Boundaries(n))"
  let ?Rb = "QuotientGroupRel(ab.tgt.Cycles(n), ab.tgt.CycleOp(n), ab.tgt.Boundaries(n))"
  let ?Rc = "QuotientGroupRel(bc.tgt.Cycles(n), bc.tgt.CycleOp(n), bc.tgt.Boundaries(n))"
  let ?neu_HnC = "TheNeutralElement(bc.tgt.Hn(n), bc.tgt.HnOp(n))"
  have np: "n \<ra> \<one> \<in> ints"
    using n Int_ZF_1_L8A(2) Int_ZF_1_T2(3) group0.group_op_closed by simp
  have arith_np: "(n \<ra> \<one>) \<rs> \<one> = n"
    using Int_ZF_1_L8A(2) group0.inv_cancel_two(2)[OF Int_ZF_1_T2(3)] n by simp
  have ab_map_fun: "ab.Hn_map(n) : ab.src.Hn(n) \<rightarrow> ab.tgt.Hn(n)"
    using ab.Hn_map_is_hom[OF n] unfolding Homomor_def by simp
  have bc_map_fun: "bc.Hn_map(n) : ab.tgt.Hn(n) \<rightarrow> bc.tgt.Hn(n)"
    using bc.Hn_map_is_hom[OF n] unfolding Homomor_def by simp
  have fn_fun: "f(n) : A(n) \<rightarrow> B(n)"
    using ses_map_f n unfolding IsAchainMap_def Homomor_def by auto
  have gn_fun: "g(n) : B(n) \<rightarrow> C(n)"
    using ses_map_g n unfolding IsAchainMap_def Homomor_def by auto
  have dBnp_fun: "dB(n \<ra> \<one>) : B(n \<ra> \<one>) \<rightarrow> B(n)"
    using ses_cplx_B np unfolding IsAchainComplex_def Homomor_def using arith_np by auto
  have grpBn: "IsAgroup(B(n), PB(n))"
    using ses_cplx_B n unfolding IsAchainComplex_def by auto
  have comBn: "PB(n) {is commutative on} B(n)"
    using ses_cplx_B n unfolding IsAchainComplex_def by auto
  have normal_b: "IsAnormalSubgroup(ab.tgt.Cycles(n), ab.tgt.CycleOp(n), ab.tgt.Boundaries(n))"
    using Group_ZF_2_4_L6(1)[OF ab.tgt.cycles_is_group[OF n]
                               ab.tgt.cycles_is_abelian[OF n]
                               ab.tgt.boundaries_subgroup_cycles[OF n]] by simp
  have normal_c: "IsAnormalSubgroup(bc.tgt.Cycles(n), bc.tgt.CycleOp(n), bc.tgt.Boundaries(n))"
    using Group_ZF_2_4_L6(1)[OF bc.tgt.cycles_is_group[OF n]
                               bc.tgt.cycles_is_abelian[OF n]
                               bc.tgt.boundaries_subgroup_cycles[OF n]] by simp
  have equiv_a: "equiv(ab.src.Cycles(n), ?Ra)"
    using ab.src.cycles_is_subgroup[OF n]
          group0.Group_ZF_2_4_L3[OF _ ab.src.boundaries_subgroup_cycles[OF n]]
    unfolding IsAsubgroup_def group0_def by auto
  have equiv_b: "equiv(ab.tgt.Cycles(n), ?Rb)"
    using ab.tgt.cycles_is_subgroup[OF n]
          group0.Group_ZF_2_4_L3[OF _ ab.tgt.boundaries_subgroup_cycles[OF n]]
    unfolding IsAsubgroup_def group0_def by auto
  interpret BnGrp: group0 "B(n)" "PB(n)"
    "TheNeutralElement(B(n), PB(n))" "\<lambda>x y. PB(n)`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(B(n), PB(n))`x"
    "\<lambda>s. Fold(PB(n), TheNeutralElement(B(n), PB(n)), s)"
    "\<lambda>na x. Fold(PB(n), TheNeutralElement(B(n), PB(n)), {\<langle>k, x\<rangle>. k \<in> na})"
    using grpBn unfolding group0_def by simp
  interpret BnCyc: group0 "ab.tgt.Cycles(n)" "ab.tgt.CycleOp(n)"
    "TheNeutralElement(ab.tgt.Cycles(n), ab.tgt.CycleOp(n))"
    "\<lambda>x y. ab.tgt.CycleOp(n)`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(ab.tgt.Cycles(n), ab.tgt.CycleOp(n))`x"
    "\<lambda>s. Fold(ab.tgt.CycleOp(n), TheNeutralElement(ab.tgt.Cycles(n), ab.tgt.CycleOp(n)), s)"
    "\<lambda>na x. Fold(ab.tgt.CycleOp(n), TheNeutralElement(ab.tgt.Cycles(n), ab.tgt.CycleOp(n)),
               {\<langle>k, x\<rangle>. k \<in> na})"
    using ab.tgt.cycles_is_group[OF n] unfolding group0_def by simp
  interpret CnCyc: group0 "bc.tgt.Cycles(n)" "bc.tgt.CycleOp(n)"
    "TheNeutralElement(bc.tgt.Cycles(n), bc.tgt.CycleOp(n))"
    "\<lambda>x y. bc.tgt.CycleOp(n)`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(bc.tgt.Cycles(n), bc.tgt.CycleOp(n))`x"
    "\<lambda>s. Fold(bc.tgt.CycleOp(n), TheNeutralElement(bc.tgt.Cycles(n), bc.tgt.CycleOp(n)), s)"
    "\<lambda>na x. Fold(bc.tgt.CycleOp(n), TheNeutralElement(bc.tgt.Cycles(n), bc.tgt.CycleOp(n)),
               {\<langle>k, x\<rangle>. k \<in> na})"
    using bc.tgt.cycles_is_group[OF n] unfolding group0_def by simp
  have cls_zero_C: "?Rc``{bc.tgt.zero_C(n)} = ?neu_HnC"
  proof -
    have zero_C_cyc: "bc.tgt.zero_C(n) \<in> bc.tgt.Cycles(n)"
      using group0.group0_3_L5[of "C(n)" "PC(n)"] bc.tgt.cplx_group[OF n]
            bc.tgt.cycles_is_subgroup[OF n] unfolding group0_def by simp
    have zero_C_bnd: "bc.tgt.zero_C(n) \<in> bc.tgt.Boundaries(n)"
    proof -
      have neu_eq: "TheNeutralElement(bc.tgt.Cycles(n), bc.tgt.CycleOp(n)) = bc.tgt.zero_C(n)"
        using group0.group0_3_L4[of "C(n)" "PC(n)"] bc.tgt.cycles_is_subgroup[OF n]
              bc.tgt.cplx_group[OF n] unfolding group0_def by simp
      from CnCyc.group0_3_L5[OF bc.tgt.boundaries_subgroup_cycles[OF n]] neu_eq
      show ?thesis by simp
    qed
    from CnCyc.Group_ZF_2_4_L5E[OF normal_c zero_C_cyc] zero_C_bnd
    have cls: "?Rc``{bc.tgt.zero_C(n)} = TheNeutralElement(
      bc.tgt.Cycles(n) // ?Rc,
      QuotientGroupOp(bc.tgt.Cycles(n), bc.tgt.CycleOp(n), bc.tgt.Boundaries(n)))"
      by simp
    show ?thesis unfolding bc.tgt.Hn_def bc.tgt.HnOp_def using cls by simp
  qed
  have gnp_surj: "g(n \<ra> \<one>)``B(n \<ra> \<one>) = C(n \<ra> \<one>)"
  proof -
    have ses_np: "IsAshortExactSequence(A(n \<ra> \<one>), PA(n \<ra> \<one>), B(n \<ra> \<one>), PB(n \<ra> \<one>),
                   C(n \<ra> \<one>), PC(n \<ra> \<one>), f(n \<ra> \<one>), g(n \<ra> \<one>))"
      using deg_ses[OF np] .
    have ea_C: "IsExactAt(g(n \<ra> \<one>), B(n \<ra> \<one>), ZeroMap(C(n \<ra> \<one>), 1, TrivOp), 1, TrivOp)"
      using ses_np unfolding IsAshortExactSequence_def by auto
    have grpCnp: "IsAgroup(C(n \<ra> \<one>), PC(n \<ra> \<one>))"
      using ses_np unfolding IsAshortExactSequence_def group_homo_def by auto
    from ea_C
    have "g(n \<ra> \<one>)``B(n \<ra> \<one>) = ZeroMap(C(n \<ra> \<one>), 1, TrivOp)-``{TheNeutralElement(1, TrivOp)}"
      unfolding IsExactAt_def by simp
    also have "\<dots> = C(n \<ra> \<one>)"
      using ZeroMap_preimage_full[OF grpCnp trivial_group] TrivOp_ne by simp
    finally show ?thesis .
  qed
  have gnp_fun: "g(n \<ra> \<one>) : B(n \<ra> \<one>) \<rightarrow> C(n \<ra> \<one>)"
    using ses_map_g np unfolding IsAchainMap_def Homomor_def by auto
  show ?thesis unfolding IsExactAt_def
  proof (rule equalityI)
    show "ab.Hn_map(n)``ab.src.Hn(n) \<subseteq> bc.Hn_map(n)-``{?neu_HnC}"
    proof
      fix X assume Xim: "X \<in> ab.Hn_map(n)``ab.src.Hn(n)"
      from func_imagedef[OF ab_map_fun subset_refl] Xim obtain Y where
        Y_Hn: "Y \<in> ab.src.Hn(n)" and X_eq: "X = ab.Hn_map(n)`Y" by auto
      from Y_Hn obtain z where z: "z \<in> ab.src.Cycles(n)" and Y_eq: "Y = ?Ra``{z}"
        unfolding ab.src.Hn_def quotient_def by auto
      have zA: "z \<in> A(n)"
        using ab.src.cycles_is_subgroup[OF n] group0.group0_3_L2
              ab.src.cplx_group[OF n] z unfolding group0_def by blast
      have fnz_cyc: "f(n)`z \<in> ab.tgt.Cycles(n)"
        using ab.cmap_maps_cycles[OF n z] .
      have X_val: "X = ?Rb``{f(n)`z}"
      proof -
        have pair: "\<langle>?Ra``{z}, ?Rb``{f(n)`z}\<rangle> \<in> ab.Hn_map(n)"
          unfolding ab.Hn_map_def using z by auto
        from Y_eq show ?thesis using apply_equality[OF pair ab_map_fun] X_eq by simp
      qed
      have X_in_HnB: "X \<in> ab.tgt.Hn(n)"
        using X_val fnz_cyc equiv_b unfolding ab.tgt.Hn_def quotient_def by auto
      have bc_X: "bc.Hn_map(n)`X = ?Rc``{g(n)`(f(n)`z)}"
      proof -
        have pair: "\<langle>?Rb``{f(n)`z}, ?Rc``{g(n)`(f(n)`z)}\<rangle> \<in> bc.Hn_map(n)"
          unfolding bc.Hn_map_def using fnz_cyc by auto
        from X_val show ?thesis using apply_equality[OF pair bc_map_fun] by simp
      qed
      have gnfnz_zero: "g(n)`(f(n)`z) = bc.tgt.zero_C(n)"
      proof -
        have fnz_im: "f(n)`z \<in> f(n)``A(n)"
          using func_imagedef[OF fn_fun subset_refl] zA by auto
        have fnz_ker: "f(n)`z \<in> g(n)-``{bc.tgt.zero_C(n)}"
          using fnz_im ses_im_eq_ker[OF n] by auto
        from func1_1_L15[OF gn_fun] apply_type[OF fn_fun zA] fnz_ker
        show ?thesis by auto
      qed
      show "X \<in> bc.Hn_map(n)-``{?neu_HnC}"
        using func1_1_L15[OF bc_map_fun] X_in_HnB bc_X gnfnz_zero cls_zero_C by auto
    qed
    show "bc.Hn_map(n)-``{?neu_HnC} \<subseteq> ab.Hn_map(n)``ab.src.Hn(n)"
    proof
      fix X assume Xker: "X \<in> bc.Hn_map(n)-``{?neu_HnC}"
      have X_in_HnB: "X \<in> ab.tgt.Hn(n)"
        using Xker func1_1_L15[OF bc_map_fun] by auto
      have X_bc_neu: "bc.Hn_map(n)`X = ?neu_HnC"
        using Xker func1_1_L15[OF bc_map_fun] by auto
      from X_in_HnB obtain b where b: "b \<in> ab.tgt.Cycles(n)"
        and X_eq: "X = ?Rb``{b}"
        unfolding ab.tgt.Hn_def quotient_def by auto
      have bB: "b \<in> B(n)"
        using ab.tgt.cycles_is_subgroup[OF n] group0.group0_3_L2
              ab.tgt.cplx_group[OF n] b unfolding group0_def by blast
      have gnb_cyc: "g(n)`b \<in> bc.tgt.Cycles(n)"
        using bc.cmap_maps_cycles[OF n b] .
      have bc_X_eq: "bc.Hn_map(n)`X = ?Rc``{g(n)`b}"
      proof -
        have pair: "\<langle>?Rb``{b}, ?Rc``{g(n)`b}\<rangle> \<in> bc.Hn_map(n)"
          unfolding bc.Hn_map_def using b by auto
        from X_eq show ?thesis using apply_equality[OF pair bc_map_fun] by simp
      qed
      have gnb_bnd: "g(n)`b \<in> bc.tgt.Boundaries(n)"
      proof -
        have gnb_cls_neu: "?Rc``{g(n)`b} = ?neu_HnC"
          using bc_X_eq X_bc_neu by simp
        from CnCyc.Group_ZF_2_4_L5E[OF normal_c gnb_cyc] gnb_cls_neu
        show ?thesis unfolding bc.tgt.Hn_def bc.tgt.HnOp_def by simp
      qed
      have dc_np_fun: "dC(n \<ra> \<one>) : C(n \<ra> \<one>) \<rightarrow> C(n)"
        using ses_cplx_C np arith_np unfolding IsAchainComplex_def Homomor_def by auto
      from gnb_bnd obtain c' where c'C: "c' \<in> C(n \<ra> \<one>)"
          and c'_eq: "g(n)`b = dC(n \<ra> \<one>)`c'"
        using func_imagedef[of "dC(n\<ra>\<one>)" "C(n\<ra>\<one>)" "C(n)" "C(n\<ra>\<one>)"] dc_np_fun by auto
      from c'C gnp_surj gnp_fun obtain b' where b'B: "b' \<in> B(n \<ra> \<one>)"
          and gnp_b': "g(n \<ra> \<one>)`b' = c'"
        using func_imagedef[of "g(n\<ra>\<one>)" "B(n\<ra>\<one>)" "C(n\<ra>\<one>)" "B(n\<ra>\<one>)"] by auto
      let ?b_spec = "dB(n \<ra> \<one>)`b'"
      have b_spec_B: "?b_spec \<in> B(n)" using apply_type[OF dBnp_fun b'B] .
      have b_spec_bnd: "?b_spec \<in> ab.tgt.Boundaries(n)"
        using func_imagedef[OF dBnp_fun subset_refl] arith_np b'B by auto
      have b_spec_cyc: "?b_spec \<in> ab.tgt.Cycles(n)"
        using ab.tgt.boundaries_in_cycles[OF n] b_spec_bnd by auto
      have g_b_spec: "g(n)`?b_spec = g(n)`b"
      proof -
        have bc_comm_np: "dC(n \<ra> \<one>) O g(n \<ra> \<one>) = g((n \<ra> \<one>) \<rs> \<one>) O dB(n \<ra> \<one>)"
          using bc.cmap_comm[OF np] by simp
        have e1: "g(n)`?b_spec = (g(n) O dB(n \<ra> \<one>))`b'"
          using comp_fun_apply[OF dBnp_fun b'B] by simp
        have e2: "(g(n) O dB(n \<ra> \<one>))`b' = (dC(n \<ra> \<one>) O g(n \<ra> \<one>))`b'"
          using bc_comm_np arith_np by simp
        have e3: "(dC(n \<ra> \<one>) O g(n \<ra> \<one>))`b' = dC(n \<ra> \<one>)`c'"
          using comp_fun_apply[OF gnp_fun b'B] gnp_b' by simp
        from e1 e2 e3 c'_eq show ?thesis by simp
      qed
      have hg: "group_homo(B(n), PB(n), C(n), PC(n), g(n))" using ses_hg[OF n] .
      have inv_bs_B: "GroupInv(B(n),PB(n))`?b_spec \<in> B(n)"
        using BnGrp.inverse_in_group[OF b_spec_B] .
      have g_diff_zero:
        "g(n)`(PB(n)`\<langle>b, GroupInv(B(n),PB(n))`?b_spec\<rangle>) = bc.tgt.zero_C(n)"
      proof -
        have gnb_C: "g(n)`b \<in> C(n)" using apply_type[OF gn_fun bB] .
        have grpC: "IsAgroup(C(n), PC(n))"
          using ses_cplx_C n unfolding IsAchainComplex_def by auto
        have e1: "g(n)`(PB(n)`\<langle>b, GroupInv(B(n),PB(n))`?b_spec\<rangle>) =
                  PC(n)`\<langle>g(n)`b, g(n)`(GroupInv(B(n),PB(n))`?b_spec)\<rangle>"
          using group_homo.f_hom[OF hg bB inv_bs_B] .
        have e2: "g(n)`(GroupInv(B(n),PB(n))`?b_spec) =
                  GroupInv(C(n),PC(n))`(g(n)`?b_spec)"
          using group_homo.f_inv[OF hg b_spec_B] .
        have e3: "PC(n)`\<langle>g(n)`b, GroupInv(C(n),PC(n))`(g(n)`b)\<rangle> = bc.tgt.zero_C(n)"
          using group0.group0_2_L6[of "C(n)" "PC(n)"] gnb_C grpC unfolding group0_def by simp
        have "g(n) ` (\<rm>⇧B⇘n⇙ dB(n \<ra> 𝟭) ` b') = \<rm>⇧C⇘n⇙ (g(n) ` b)" 
          using e2 subst[OF g_b_spec, of "\<lambda>q. g(n) ` (\<rm>⇧B⇘n⇙ dB(n \<ra> 𝟭) ` b') = \<rm>⇧C⇘n⇙ q"]
          by blast
        with e1 e3 show ?thesis by (simp only:)
      qed
      let ?diff = "PB(n)`\<langle>b, GroupInv(B(n),PB(n))`?b_spec\<rangle>"
      have diff_B: "?diff \<in> B(n)"
        using BnGrp.group_op_closed bB inv_bs_B .
      have " b \<ra>⇧B⇘n⇙ \<rm>⇧B⇘n⇙ dB(n \<ra> 𝟭) ` b' ∈
         {x ∈ B(n) . g(n) ` x ∈ {bc.tgt.zero_C(n)}}" using diff_B
        g_diff_zero by blast
      then have diff_ker: "?diff \<in> g(n)-``{bc.tgt.zero_C(n)}"
        using func1_1_L15[OF gn_fun, of "{bc.tgt.zero_C(n)}"] 
        by (simp only:)
      have diff_im: "?diff \<in> f(n)``A(n)"
        using diff_ker ses_im_eq_ker[OF n] by (simp only:)
      from func_imagedef[OF fn_fun subset_refl] diff_im obtain z where
        aA: "z \<in> A(n)" and fa_eq: "f(n)`z = ?diff" by (auto simp only:)
      have a_cyc: "z \<in> ab.src.Cycles(n)"
      proof -
        have pn: "n \<rs> \<one> \<in> ints"
          using n Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
        have fn_nm1_fun: "f(n \<rs> \<one>) : A(n \<rs> \<one>) \<rightarrow> B(n \<rs> \<one>)"
          using ses_map_f pn unfolding IsAchainMap_def Homomor_def by auto
        have fn_nm1_inj: "f(n \<rs> \<one>) \<in> inj(A(n \<rs> \<one>), B(n \<rs> \<one>))"
          using ses_f_inj[OF pn] .
        have dAn_fun: "dA(n) : A(n) \<rightarrow> A(n \<rs> \<one>)"
          using ses_cplx_A n unfolding IsAchainComplex_def Homomor_def by auto
        have dBn_fun: "dB(n) : B(n) \<rightarrow> B(n \<rs> \<one>)"
          using ses_cplx_B n unfolding IsAchainComplex_def Homomor_def by auto
        have grpBpn: "IsAgroup(B(n \<rs> \<one>), PB(n \<rs> \<one>))"
          using ses_cplx_B pn unfolding IsAchainComplex_def by auto
        have hg_dB: "group_homo(B(n), PB(n), B(n \<rs> \<one>), PB(n \<rs> \<one>), dB(n))"
        proof -
          have hom: "Homomor(dB(n), B(n), PB(n), B(n \<rs> \<one>), PB(n \<rs> \<one>))"
            using ses_cplx_B n unfolding IsAchainComplex_def by auto
          from hom grpBn grpBpn show ?thesis unfolding group_homo_def by simp
        qed
        have dBn_b: "dB(n)`b = TheNeutralElement(B(n \<rs> \<one>), PB(n \<rs> \<one>))"
          using b dBn_fun by (simp add: func1_1_L15)
        have dBn_bspec: "dB(n)`?b_spec = TheNeutralElement(B(n \<rs> \<one>), PB(n \<rs> \<one>))"
          using b_spec_cyc dBn_fun by (simp add: func1_1_L15)
        have zero_Bpn: "TheNeutralElement(B(n \<rs> \<one>), PB(n \<rs> \<one>)) \<in> B(n \<rs> \<one>)"
          using group0.group0_2_L2_1[of "B(n \<rs> \<one>)" "PB(n \<rs> \<one>)"] grpBpn
          unfolding group0_def by simp
        have f_dA: "f(n \<rs> \<one>)`(dA(n)`z) = TheNeutralElement(B(n \<rs> \<one>), PB(n \<rs> \<one>))"
        proof -
          have step1: "f(n \<rs> \<one>)`(dA(n)`z) = dB(n)`?diff"
          proof -
            have e1: "(f(n \<rs> \<one>) O dA(n))`z = (dB(n) O f(n))`z"
              using ab.cmap_comm[OF n] by simp
            have e2: "(f(n \<rs> \<one>) O dA(n))`z = f(n \<rs> \<one>)`(dA(n)`z)"
              using comp_fun_apply[OF dAn_fun aA] by simp
            have e3: "(dB(n) O f(n))`z = dB(n)`?diff"
              using comp_fun_apply[OF fn_fun aA] fa_eq by (simp only:)
            from e1 e2 e3 show ?thesis by (simp only:)
          qed
          have step2: "dB(n)`?diff =
                       PB(n \<rs> \<one>)`\<langle>dB(n)`b, dB(n)`(GroupInv(B(n),PB(n))`?b_spec)\<rangle>"
            using group_homo.f_hom[OF hg_dB bB inv_bs_B] by (simp only:)
          have step3: "dB(n)`(GroupInv(B(n),PB(n))`?b_spec) =
                       GroupInv(B(n \<rs> \<one>),PB(n \<rs> \<one>))`(dB(n)`?b_spec)"
            using group_homo.f_inv[OF hg_dB b_spec_B] by (simp only:)
          have step4:
            "GroupInv(B(n \<rs> \<one>),PB(n \<rs> \<one>))`(TheNeutralElement(B(n \<rs> \<one>),PB(n \<rs> \<one>))) =
             TheNeutralElement(B(n \<rs> \<one>),PB(n \<rs> \<one>))"
            using group0.group_inv_of_one[of "B(n \<rs> \<one>)" "PB(n \<rs> \<one>)"] grpBpn
            unfolding group0_def by auto
          have step5:
            "PB(n \<rs> \<one>)`\<langle>TheNeutralElement(B(n \<rs> \<one>),PB(n \<rs> \<one>)),
                        TheNeutralElement(B(n \<rs> \<one>),PB(n \<rs> \<one>))\<rangle> =
             TheNeutralElement(B(n \<rs> \<one>),PB(n \<rs> \<one>))"
            using group0.group0_2_L2[of "B(n \<rs> \<one>)" "PB(n \<rs> \<one>)"] zero_Bpn grpBpn
            unfolding group0_def by simp
          from step1 step2 step3 dBn_b dBn_bspec step4 step5 show ?thesis by (simp only:)
        qed
        have dAn_a: "dA(n)`z \<in> A(n \<rs> \<one>)" using apply_type[OF dAn_fun aA] .
        have neu_A: "TheNeutralElement(A(n \<rs> \<one>), PA(n \<rs> \<one>)) \<in> A(n \<rs> \<one>)"
          using group_homo.origin group0.group0_2_L2 ses_hf[OF pn]
          unfolding group0_def by simp
        have f_neu: "f(n \<rs> \<one>)`(TheNeutralElement(A(n \<rs> \<one>), PA(n \<rs> \<one>))) =
                     TheNeutralElement(B(n \<rs> \<one>), PB(n \<rs> \<one>))"
          using group_homo.f_neutral[OF ses_hf[OF pn]] by simp
        have dA_zero: "dA(n)`z = TheNeutralElement(A(n \<rs> \<one>), PA(n \<rs> \<one>))"
          using fn_nm1_inj dAn_a neu_A f_dA f_neu unfolding inj_def by auto
        from dA_zero aA dAn_fun show ?thesis by (simp add: func1_1_L15)
      qed
      have fnz_cyc: "f(n)`z \<in> ab.tgt.Cycles(n)"
        using ab.cmap_maps_cycles[OF n a_cyc] .
      have inv_b_eq:
        "\<forall>h \<in> ab.tgt.Cycles(n).
           GroupInv(ab.tgt.Cycles(n), ab.tgt.CycleOp(n))`h = GroupInv(B(n),PB(n))`h"
        using BnGrp.group0_3_T2[OF ab.tgt.cycles_is_subgroup[OF n]] by blast
      have inv_b_cyc: "GroupInv(ab.tgt.Cycles(n), ab.tgt.CycleOp(n))`b \<in> ab.tgt.Cycles(n)"
        using group0.inverse_in_group[OF _ b, of "ab.tgt.CycleOp(n)"]
              ab.tgt.cycles_is_group[OF n] unfolding group0_def by auto
      have inv_bspec_bnd: "GroupInv(B(n),PB(n))`?b_spec \<in> ab.tgt.Boundaries(n)"
      proof -
        have inv_bspec_cyc:
          "GroupInv(ab.tgt.Cycles(n), ab.tgt.CycleOp(n))`?b_spec \<in> ab.tgt.Boundaries(n)"
          using BnCyc.group0_3_T3A[OF ab.tgt.boundaries_subgroup_cycles[OF n]] b_spec_bnd by auto
        from inv_b_eq b_spec_cyc have "GroupInv(ab.tgt.Cycles(n), restrict(PB(n),
           ab.tgt.Cycles(n) × ab.tgt.Cycles(n))) ` (dB(n \<ra> 𝟭) ` b') = 
            \<rm>⇧B⇘n⇙ (dB(n \<ra> 𝟭) ` b')"
          by blast
          with inv_bspec_cyc show ?thesis by (simp only:)
      qed
      have fa_inv_b:
        "PB(n)`\<langle>f(n)`z, GroupInv(B(n),PB(n))`b\<rangle> = GroupInv(B(n),PB(n))`?b_spec"
      proof -
        have inv_b: "GroupInv(B(n),PB(n))`b \<in> B(n)"
          using BnGrp.inverse_in_group[OF bB] .
        have e1: "PB(n)`\<langle>f(n)`z, GroupInv(B(n),PB(n))`b\<rangle>
                = PB(n)`\<langle>PB(n)`\<langle>b, GroupInv(B(n),PB(n))`b\<rangle>,
                          GroupInv(B(n),PB(n))`?b_spec\<rangle>"
          using fa_eq BnGrp.group0_4_L4A(5)[OF comBn bB b_spec_B bB] by (simp only:)
        have e2: "PB(n)`\<langle>b, GroupInv(B(n),PB(n))`b\<rangle> = TheNeutralElement(B(n),PB(n))"
          using BnGrp.group0_2_L6[OF bB] by blast
        have e3: "PB(n)`\<langle>TheNeutralElement(B(n),PB(n)), GroupInv(B(n),PB(n))`?b_spec\<rangle> =
                  GroupInv(B(n),PB(n))`?b_spec"
          using BnGrp.group0_2_L2 inv_bs_B by (simp only:)
        from e1 e2 e3 show ?thesis by (simp only:)
      qed
      have rel_fab: "\<langle>f(n)`z, b\<rangle> \<in> ?Rb"
      proof -
        have inv_b_eq_b:
          "GroupInv(ab.tgt.Cycles(n), ab.tgt.CycleOp(n))`b = GroupInv(B(n),PB(n))`b"
          using inv_b_eq b by (simp only:)
        have pair_in: "\<langle>f(n)`z, GroupInv(ab.tgt.Cycles(n), ab.tgt.CycleOp(n))`b\<rangle>
                     \<in> ab.tgt.Cycles(n) \<times> ab.tgt.Cycles(n)"
          using fnz_cyc inv_b_cyc by auto
        from restrict[of "PB(n)" "ab.tgt.Cycles(n) \<times> ab.tgt.Cycles(n)"
                         "\<langle>f(n)`z, GroupInv(ab.tgt.Cycles(n), ab.tgt.CycleOp(n))`b\<rangle>"]
             pair_in inv_b_eq_b
        have cycop_eq:
          "ab.tgt.CycleOp(n)`\<langle>f(n)`z, GroupInv(ab.tgt.Cycles(n), ab.tgt.CycleOp(n))`b\<rangle>
         = PB(n)`\<langle>f(n)`z, GroupInv(B(n),PB(n))`b\<rangle>"
          by (simp only: if_true)
        from cycop_eq fa_inv_b inv_bspec_bnd
        have in_bnd:
          "ab.tgt.CycleOp(n)`\<langle>f(n)`z, GroupInv(ab.tgt.Cycles(n), ab.tgt.CycleOp(n))`b\<rangle>
         \<in> ab.tgt.Boundaries(n)"
          by (simp only:)
        show ?thesis unfolding QuotientGroupRel_def using fnz_cyc b in_bnd by auto
      qed
      have cls_eq: "?Rb``{f(n)`z} = ?Rb``{b}"
        using equiv_b b rel_fab by (auto simp: equiv_class_eq)
      have Y_Hn: "?Ra``{z} \<in> ab.src.Hn(n)"
        using a_cyc equiv_a unfolding ab.src.Hn_def quotient_def by auto
      have pair_a: "\<langle>?Ra``{z}, ?Rb``{f(n)`z}\<rangle> \<in> ab.Hn_map(n)"
        unfolding ab.Hn_map_def using a_cyc by auto
      have map_Y: "ab.Hn_map(n)`(?Ra``{z}) = ?Rb``{f(n)`z}"
        using apply_equality[OF pair_a ab_map_fun] .
      from Y_Hn have "ab.Hn_map(n)`(?Ra``{z}) \<in> ab.Hn_map(n)``ab.src.Hn(n)"
        using func_imagedef[OF ab_map_fun subset_refl] by auto
      with map_Y have "?Rb``{f(n)`z} \<in> ab.Hn_map(n)``ab.src.Hn(n)"
        by auto 
      then show "X \<in> ab.Hn_map(n)``ab.src.Hn(n)"
        using X_eq cls_eq by auto
    qed
  qed
qed

text\<open>Exactness at $H_n(C)$: the image of $g_*$ equals the kernel of $\delta_n$.\<close>

theorem (in ses_chain_complex) les_exact_at_HnC:
  assumes n: "n \<in> ints"
  shows "IsExactAt(bc.Hn_map(n), ab.tgt.Hn(n), delta(n),
                   ab.src.Hn(n \<rs> \<one>), ab.src.HnOp(n \<rs> \<one>))"
proof -
  have pn: "n \<rs> \<one> \<in> ints"
    using n Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  let ?Rb = "QuotientGroupRel(ab.tgt.Cycles(n), ab.tgt.CycleOp(n), ab.tgt.Boundaries(n))"
  let ?Rc = "QuotientGroupRel(bc.tgt.Cycles(n), bc.tgt.CycleOp(n), bc.tgt.Boundaries(n))"
  let ?Ra = "QuotientGroupRel(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>), ab.src.Boundaries(n \<rs> \<one>))"
  let ?neu_HnA = "TheNeutralElement(ab.src.Hn(n \<rs> \<one>), ab.src.HnOp(n \<rs> \<one>))"
  let ?Lft = "{x \<in> B(n). g(n)`x \<in> bc.tgt.Cycles(n)}"
  have arith_pm: "(n \<rs> \<one>) \<ra> \<one> = n"
    using Int_ZF_1_L8A(2) group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3)] n by simp
  have bc_map_fun: "bc.Hn_map(n) : ab.tgt.Hn(n) \<rightarrow> bc.tgt.Hn(n)"
    using bc.Hn_map_is_hom[OF n] unfolding Homomor_def by simp
  have delta_fun: "delta(n) : bc.tgt.Hn(n) \<rightarrow> ab.src.Hn(n \<rs> \<one>)"
    using delta_fun[OF n] .
  have gn_fun: "g(n) : B(n) \<rightarrow> C(n)"
    using ses_map_g n unfolding IsAchainMap_def Homomor_def by auto
  have fn_fun: "f(n) : A(n) \<rightarrow> B(n)"
    using ses_map_f n unfolding IsAchainMap_def Homomor_def by auto
  have fn_nm1_fun: "f(n \<rs> \<one>) : A(n \<rs> \<one>) \<rightarrow> B(n \<rs> \<one>)"
    using ses_map_f pn unfolding IsAchainMap_def Homomor_def by auto
  have fn_nm1_inj: "f(n \<rs> \<one>) \<in> inj(A(n \<rs> \<one>), B(n \<rs> \<one>))"
    using ses_f_inj[OF pn] .
  have dBn_fun: "dB(n) : B(n) \<rightarrow> B(n \<rs> \<one>)"
    using ses_cplx_B n unfolding IsAchainComplex_def Homomor_def by auto
  have dAn_fun: "dA(n) : A(n) \<rightarrow> A(n \<rs> \<one>)"
    using ses_cplx_A n unfolding IsAchainComplex_def Homomor_def by auto
  have equiv_b: "equiv(ab.tgt.Cycles(n), ?Rb)"
    using ab.tgt.cycles_is_subgroup[OF n]
          group0.Group_ZF_2_4_L3[OF _ ab.tgt.boundaries_subgroup_cycles[OF n]]
    unfolding IsAsubgroup_def group0_def by auto
  have equiv_c: "equiv(bc.tgt.Cycles(n), ?Rc)"
    using bc.tgt.cycles_is_subgroup[OF n]
          group0.Group_ZF_2_4_L3[OF _ bc.tgt.boundaries_subgroup_cycles[OF n]]
    unfolding IsAsubgroup_def group0_def by auto
  have normal_a: "IsAnormalSubgroup(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>), ab.src.Boundaries(n \<rs> \<one>))"
    using Group_ZF_2_4_L6(1)[OF ab.src.cycles_is_group[OF pn]
                               ab.src.cycles_is_abelian[OF pn]
                               ab.src.boundaries_subgroup_cycles[OF pn]] by simp
  have gnB_C: "g(n)``B(n) = C(n)"
  proof -
    have ea_C: "IsExactAt(g(n), B(n), ZeroMap(C(n), 1, TrivOp), 1, TrivOp)"
      using deg_ses[OF n] unfolding IsAshortExactSequence_def by auto
    have grpC: "IsAgroup(C(n), PC(n))"
      using deg_ses[OF n] unfolding IsAshortExactSequence_def group_homo_def by auto
    from ea_C show ?thesis
      using ZeroMap_preimage_full[OF grpC trivial_group] TrivOp_ne unfolding IsExactAt_def by simp
  qed
  have hgn: "group_homo(B(n), PB(n), C(n), PC(n), g(n))" using ses_hg[OF n] .
  have grpBn: "IsAgroup(B(n), PB(n))"
    using ses_cplx_B n unfolding IsAchainComplex_def by auto
  have grpBpn: "IsAgroup(B(n \<rs> \<one>), PB(n \<rs> \<one>))"
    using ses_cplx_B pn unfolding IsAchainComplex_def by auto
  have hg_dB: "group_homo(B(n), PB(n), B(n \<rs> \<one>), PB(n \<rs> \<one>), dB(n))"
  proof -
    have hom: "Homomor(dB(n), B(n), PB(n), B(n \<rs> \<one>), PB(n \<rs> \<one>))"
      using ses_cplx_B n unfolding IsAchainComplex_def by auto
    from hom grpBn grpBpn show ?thesis unfolding group_homo_def by simp
  qed
  interpret AnCyc: group0 "ab.src.Cycles(n \<rs> \<one>)" "ab.src.CycleOp(n \<rs> \<one>)"
    "TheNeutralElement(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>))"
    "\<lambda>x y. ab.src.CycleOp(n \<rs> \<one>)`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>))`x"
    "\<lambda>s. Fold(ab.src.CycleOp(n \<rs> \<one>), TheNeutralElement(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>)), s)"
    "\<lambda>na x. Fold(ab.src.CycleOp(n \<rs> \<one>), TheNeutralElement(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>)), {\<langle>k, x\<rangle>. k \<in> na})"
    using ab.src.cycles_is_group[OF pn] unfolding group0_def by simp
  interpret BnGrp: group0 "B(n)" "PB(n)"
    "TheNeutralElement(B(n), PB(n))" "\<lambda>x y. PB(n)`\<langle>x, y\<rangle>"
    "\<lambda>x. GroupInv(B(n), PB(n))`x"
    "\<lambda>s. Fold(PB(n), TheNeutralElement(B(n), PB(n)), s)"
    "\<lambda>na x. Fold(PB(n), TheNeutralElement(B(n), PB(n)), {\<langle>k, x\<rangle>. k \<in> na})"
    using grpBn unfolding group0_def by simp
  have cls_zero_A: "?Ra``{ab.src.zero_C(n \<rs> \<one>)} = ?neu_HnA"
  proof -
    have zero_A_cyc: "ab.src.zero_C(n \<rs> \<one>) \<in> ab.src.Cycles(n \<rs> \<one>)"
      using group0.group0_3_L5[of "A(n \<rs> \<one>)" "PA(n \<rs> \<one>)"] ab.src.cplx_group[OF pn]
            ab.src.cycles_is_subgroup[OF pn] unfolding group0_def by simp
    have zero_A_bnd: "ab.src.zero_C(n \<rs> \<one>) \<in> ab.src.Boundaries(n \<rs> \<one>)"
    proof -
      have neu_eq: "TheNeutralElement(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>)) =
                    ab.src.zero_C(n \<rs> \<one>)"
        using group0.group0_3_L4[of "A(n \<rs> \<one>)" "PA(n \<rs> \<one>)"]
              ab.src.cycles_is_subgroup[OF pn] ab.src.cplx_group[OF pn]
        unfolding group0_def by simp
      from AnCyc.group0_3_L5[OF ab.src.boundaries_subgroup_cycles[OF pn]] neu_eq
      show ?thesis by simp
    qed
    from AnCyc.Group_ZF_2_4_L5E[OF normal_a zero_A_cyc] zero_A_bnd
    have cls: "?Ra``{ab.src.zero_C(n \<rs> \<one>)} = TheNeutralElement(
      ab.src.Cycles(n \<rs> \<one>) // ?Ra,
      QuotientGroupOp(ab.src.Cycles(n \<rs> \<one>), ab.src.CycleOp(n \<rs> \<one>), ab.src.Boundaries(n \<rs> \<one>)))"
      by simp
    show ?thesis unfolding ab.src.Hn_def ab.src.HnOp_def using cls by simp
  qed
  show ?thesis unfolding IsExactAt_def
  proof (rule equalityI)
    show "bc.Hn_map(n)``ab.tgt.Hn(n) \<subseteq> delta(n)-``{?neu_HnA}"
    proof
      fix X assume Xim: "X \<in> bc.Hn_map(n)``ab.tgt.Hn(n)"
      from func_imagedef[OF bc_map_fun subset_refl] Xim obtain Y where
        Y_Hn: "Y \<in> ab.tgt.Hn(n)" and X_eq: "X = bc.Hn_map(n)`Y" by auto
      from Y_Hn obtain b where b: "b \<in> ab.tgt.Cycles(n)" and Y_eq: "Y = ?Rb``{b}"
        unfolding ab.tgt.Hn_def quotient_def by auto
      have bB: "b \<in> B(n)"
        using ab.tgt.cycles_is_subgroup[OF n] group0.group0_3_L2
              ab.tgt.cplx_group[OF n] b unfolding group0_def by blast
      have gnb_cyc: "g(n)`b \<in> bc.tgt.Cycles(n)"
        using bc.cmap_maps_cycles[OF n b] .
      have X_val: "X = ?Rc``{g(n)`b}"
      proof -
        have pair: "\<langle>?Rb``{b}, ?Rc``{g(n)`b}\<rangle> \<in> bc.Hn_map(n)"
          unfolding bc.Hn_map_def using b by auto
        from Y_eq show ?thesis using apply_equality[OF pair bc_map_fun] X_eq by simp
      qed
      have X_Hn: "X \<in> bc.tgt.Hn(n)"
        using X_val gnb_cyc equiv_c unfolding bc.tgt.Hn_def quotient_def by auto
      have dBb_zero: "dB(n)`b = TheNeutralElement(B(n \<rs> \<one>), PB(n \<rs> \<one>))"
        using b dBn_fun by (simp add: func1_1_L15)
      have cl_eq_zero: "conn_lift(n, b) = ab.src.zero_C(n \<rs> \<one>)"
      proof -
        have maps_to_zero: "f(n \<rs> \<one>)`(conn_lift(n, b)) = TheNeutralElement(B(n \<rs> \<one>), PB(n \<rs> \<one>))"
          using conn_lift_maps[OF n bB gnb_cyc] dBb_zero by simp
        have f_neu: "f(n \<rs> \<one>)`(TheNeutralElement(A(n \<rs> \<one>), PA(n \<rs> \<one>))) =
                     TheNeutralElement(B(n \<rs> \<one>), PB(n \<rs> \<one>))"
          using group_homo.f_neutral[OF ses_hf[OF pn]] by simp
        have clb_A: "conn_lift(n, b) \<in> A(n \<rs> \<one>)"
          using conn_lift_in_A[OF n bB gnb_cyc] .
        have neu_A: "TheNeutralElement(A(n \<rs> \<one>), PA(n \<rs> \<one>)) \<in> A(n \<rs> \<one>)"
          using group_homo.origin group0.group0_2_L2 ses_hf[OF pn] unfolding group0_def by simp
        from fn_nm1_inj clb_A neu_A maps_to_zero f_neu
        show ?thesis unfolding inj_def by auto
      qed
      have delta_X: "delta(n)`X = ?Ra``{conn_lift(n, b)}"
      proof -
        have pair: "\<langle>?Rc``{g(n)`b}, ?Ra``{conn_lift(n, b)}\<rangle> \<in> delta(n)"
          unfolding delta_def using bB gnb_cyc by auto
        from X_val show ?thesis using apply_equality[OF pair delta_fun] by simp
      qed
      show "X \<in> delta(n)-``{?neu_HnA}"
        using func1_1_L15[OF delta_fun] X_Hn delta_X cl_eq_zero cls_zero_A by auto
    qed
    show "delta(n)-``{?neu_HnA} \<subseteq> bc.Hn_map(n)``ab.tgt.Hn(n)"
    proof
      fix X assume Xker: "X \<in> delta(n)-``{?neu_HnA}"
      have X_Hn: "X \<in> bc.tgt.Hn(n)"
        using Xker func1_1_L15[OF delta_fun] by auto
      have X_delta_neu: "delta(n)`X = ?neu_HnA"
        using Xker func1_1_L15[OF delta_fun] by auto
      from X_Hn obtain c where c: "c \<in> bc.tgt.Cycles(n)" and X_eq: "X = ?Rc``{c}"
        unfolding bc.tgt.Hn_def quotient_def by auto
      have cC: "c \<in> C(n)"
        using bc.tgt.cycles_is_subgroup[OF n] group0.group0_3_L2 bc.tgt.cplx_group[OF n] c
        unfolding group0_def by blast
      from cC gnB_C have "c \<in> g(n)``B(n)" by auto
      then obtain b where bB: "b \<in> B(n)" and gnb: "g(n)`b = c"
        using func_imagedef[OF gn_fun subset_refl] by auto
      have b_cyc_C: "g(n)`b \<in> bc.tgt.Cycles(n)" using gnb c by simp
      have bLft: "b \<in> ?Lft" using bB b_cyc_C by auto
      have cl_cyc: "conn_lift(n, b) \<in> ab.src.Cycles(n \<rs> \<one>)"
        using conn_lift_in_cycles[OF n bB b_cyc_C] .
      have delta_X_val: "delta(n)`X = ?Ra``{conn_lift(n, b)}"
      proof -
        have pair: "\<langle>?Rc``{g(n)`b}, ?Ra``{conn_lift(n, b)}\<rangle> \<in> delta(n)"
          unfolding delta_def using bLft by auto
        from X_eq gnb show ?thesis using apply_equality[OF pair delta_fun] by simp
      qed
      have cl_bnd: "conn_lift(n, b) \<in> ab.src.Boundaries(n \<rs> \<one>)"
      proof -
        have cls_eq: "?Ra``{conn_lift(n, b)} = ?neu_HnA"
          using delta_X_val X_delta_neu by simp
        from AnCyc.Group_ZF_2_4_L5E[OF normal_a cl_cyc] cls_eq
        show ?thesis unfolding ab.src.Hn_def ab.src.HnOp_def by simp
      qed
      from cl_bnd arith_pm have cl_im: "conn_lift(n, b) \<in> (dA(n))``(A(n))" by simp
      from func_imagedef[OF dAn_fun subset_refl] cl_im obtain a0 where
        a0A: "a0 \<in> A(n)" and cl_eq: "conn_lift(n, b) = dA(n)`a0" by auto
      let ?b' = "PB(n)`\<langle>b, GroupInv(B(n), PB(n))`(f(n)`a0)\<rangle>"
      have fna0_B: "f(n)`a0 \<in> B(n)" using apply_type[OF fn_fun a0A] .
      have inv_fna0_B: "GroupInv(B(n), PB(n))`(f(n)`a0) \<in> B(n)"
        using BnGrp.inverse_in_group[OF fna0_B] .
      have b'_B: "?b' \<in> B(n)" using BnGrp.group_op_closed bB inv_fna0_B .
      have g_b': "g(n)`?b' = c"
      proof -
        have e1: "g(n)`?b' =
                  PC(n)`\<langle>g(n)`b, g(n)`(GroupInv(B(n), PB(n))`(f(n)`a0))\<rangle>"
          using group_homo.f_hom[OF hgn bB inv_fna0_B] .
        have e2: "g(n)`(GroupInv(B(n), PB(n))`(f(n)`a0)) =
                  GroupInv(C(n), PC(n))`(g(n)`(f(n)`a0))"
          using group_homo.f_inv[OF hgn fna0_B] .
        have e3: "g(n)`(f(n)`a0) = bc.tgt.zero_C(n)"
        proof -
          have fna0_im: "f(n)`a0 \<in> f(n)``A(n)"
            using func_imagedef[OF fn_fun subset_refl] a0A by auto
          from fna0_im ses_im_eq_ker[OF n]
          have fna0_ker: "f(n)`a0 \<in> g(n)-``{TheNeutralElement(C(n), PC(n))}" by simp
          from func1_1_L15[OF gn_fun] fna0_B fna0_ker show ?thesis by auto
        qed
        have grpC: "IsAgroup(C(n), PC(n))"
          using ses_cplx_C n unfolding IsAchainComplex_def by auto
        have gnb_C: "g(n)`b \<in> C(n)" using apply_type[OF gn_fun bB] .
        have inv_zero: "GroupInv(C(n), PC(n))`(bc.tgt.zero_C(n)) = bc.tgt.zero_C(n)"
          using group0.group_inv_of_one[of "C(n)" "PC(n)"] grpC unfolding group0_def by auto
        from e1 e2 e3 inv_zero have
          "g(n)`?b' = PC(n)`\<langle>g(n)`b, bc.tgt.zero_C(n)\<rangle>" by (auto simp only:)
        also have "\<dots> = g(n)`b"
          using group0.group0_2_L2[of "C(n)" "PC(n)"] gnb_C grpC unfolding group0_def by simp
        finally show ?thesis using gnb by blast
      qed
      have dBb': "dB(n)`?b' = TheNeutralElement(B(n \<rs> \<one>), PB(n \<rs> \<one>))"
      proof -
        have e1: "dB(n)`?b' =
                  PB(n \<rs> \<one>)`\<langle>dB(n)`b, dB(n)`(GroupInv(B(n), PB(n))`(f(n)`a0))\<rangle>"
          using group_homo.f_hom[OF hg_dB bB inv_fna0_B] .
        have e2: "dB(n)`(GroupInv(B(n), PB(n))`(f(n)`a0)) =
                  GroupInv(B(n \<rs> \<one>), PB(n \<rs> \<one>))`(dB(n)`(f(n)`a0))"
          using group_homo.f_inv[OF hg_dB fna0_B] .
        have e3: "dB(n)`(f(n)`a0) = dB(n)`b"
        proof -
          have step: "(dB(n) O f(n))`a0 = (f(n \<rs> \<one>) O dA(n))`a0"
            using ab.cmap_comm[OF n] by simp
          have lhs: "(dB(n) O f(n))`a0 = dB(n)`(f(n)`a0)"
            using comp_fun_apply[OF fn_fun a0A] by simp
          have rhs: "(f(n \<rs> \<one>) O dA(n))`a0 = f(n \<rs> \<one>)`(dA(n)`a0)"
            using comp_fun_apply[OF dAn_fun a0A] by simp
          have e4: "f(n \<rs> \<one>)`(dA(n)`a0) = dB(n)`b"
            using cl_eq conn_lift_maps[OF n bB b_cyc_C] by simp
          from step lhs rhs e4 show ?thesis by simp
        qed
        have dBb_Bpn: "dB(n)`b \<in> B(n \<rs> \<one>)" using apply_type[OF dBn_fun bB] .
        have e5: "PB(n \<rs> \<one>)`\<langle>dB(n)`b, GroupInv(B(n \<rs> \<one>), PB(n \<rs> \<one>))`(dB(n)`b)\<rangle> =
                  TheNeutralElement(B(n \<rs> \<one>), PB(n \<rs> \<one>))"
          using group0.group0_2_L6[of "B(n \<rs> \<one>)" "PB(n \<rs> \<one>)"] dBb_Bpn grpBpn
          unfolding group0_def by simp
        from e1 e2 e3 e5 show ?thesis by (auto simp only:)
      qed
      have b'_cyc: "?b' \<in> ab.tgt.Cycles(n)"
        using b'_B dBb' func1_1_L15[OF dBn_fun, of "{ab.tgt.zero_C(n \<rs> 𝟭)}"]
        by (auto simp only:)
      have pair: "\<langle>?Rb``{?b'}, ?Rc``{g(n)`?b'}\<rangle> \<in> bc.Hn_map(n)"
        unfolding bc.Hn_map_def using b'_cyc by (auto simp only:)
      have Y_Hn: "?Rb``{?b'} \<in> ab.tgt.Hn(n)"
        using b'_cyc equiv_b unfolding ab.tgt.Hn_def quotient_def by (auto simp only:)
      have bc_Y: "bc.Hn_map(n)`(?Rb``{?b'}) = ?Rc``{c}"
        using apply_equality[OF pair bc_map_fun] g_b' by (auto simp only:)
      from Y_Hn have "bc.Hn_map(n)`(?Rb``{?b'})\<in>{bc.Hn_map(n) ` x . x ∈ ab.tgt.Hn(n)}" by blast
      then have "bc.Hn_map(n)`(?Rb``{?b'})\<in>bc.Hn_map(n)``ab.tgt.Hn(n)"
        using func_imagedef[OF bc_map_fun subset_refl] by (auto simp only:)
      with bc_Y have "?Rc``{c}\<in>bc.Hn_map(n)``ab.tgt.Hn(n)" by (auto simp only:)
      then show "X \<in> bc.Hn_map(n)``ab.tgt.Hn(n)" using X_eq by simp
    qed
  qed
qed

text\<open>The long exact sequence in homology: for each degree $n \in \mathbb{Z}$, the sequence
  $\ldots \to H_n(A) \xrightarrow{f_*} H_n(B) \xrightarrow{g_*} H_n(C) \xrightarrow{\delta_n}
   H_{n-1}(A) \to \ldots$ is exact at every term.\<close>

theorem (in ses_chain_complex) long_exact_sequence:
  assumes n: "n \<in> ints"
  shows
    "IsExactAt(delta(n), bc.tgt.Hn(n), ab.Hn_map(n \<rs> \<one>),
               ab.tgt.Hn(n \<rs> \<one>), ab.tgt.HnOp(n \<rs> \<one>)) \<and>
     IsExactAt(ab.Hn_map(n), ab.src.Hn(n), bc.Hn_map(n),
               bc.tgt.Hn(n), bc.tgt.HnOp(n)) \<and>
     IsExactAt(bc.Hn_map(n), ab.tgt.Hn(n), delta(n),
               ab.src.Hn(n \<rs> \<one>), ab.src.HnOp(n \<rs> \<one>))"
  using les_exact_at_HnA[OF n] les_exact_at_HnB[OF n] les_exact_at_HnC[OF n]
  by auto

subsection \<open>The long exact sequence as a chain complex\<close>

text\<open>We encode the long exact sequence in homology as a single chain complex
  (the \emph{interleaved complex}), indexed by $\mathbb{Z}$ via the identification
  \[
    G(3k) = H_k(A),\quad G(3k-1) = H_k(B),\quad G(3k-2) = H_k(C),
  \]
  with boundary maps $d(3k) = f_{k,*}$, $d(3k-1) = g_{k,*}$,
  $d(3k-2) = \delta_k$.  The three cases are detected by $m \bmod 3$.\<close>

definition (in ses_chain_complex) les_G :: "i \<Rightarrow> i" where
  "les_G(m) \<equiv>
    if m zmod \<three> = \<zero>
    then ab.src.Hn(m zdiv \<three>)
    else if m zmod \<three> = \<two>
    then ab.tgt.Hn((m \<ra> \<one>) zdiv \<three>)
    else bc.tgt.Hn((m \<ra> \<two>) zdiv \<three>)"

definition (in ses_chain_complex) les_opG :: "i \<Rightarrow> i" where
  "les_opG(m) \<equiv>
    if m zmod \<three> = \<zero>
    then ab.src.HnOp(m zdiv \<three>)
    else if m zmod \<three> = \<two>
    then ab.tgt.HnOp((m \<ra> \<one>) zdiv \<three>)
    else bc.tgt.HnOp((m \<ra> \<two>) zdiv \<three>)"

definition (in ses_chain_complex) les_d :: "i \<Rightarrow> i" where
  "les_d(m) \<equiv>
    if m zmod \<three> = \<zero>
    then ab.Hn_map(m zdiv \<three>)
    else if m zmod \<three> = \<two>
    then bc.Hn_map((m \<ra> \<one>) zdiv \<three>)
    else delta((m \<ra> \<two>) zdiv \<three>)"

text\<open>When $m \bmod 3 = 0$ the interleaved boundary satisfies $d_{m-1} \circ d_m = 0$:
  $d_m = f_{k,*}$ and $d_{m-1} = g_{k,*}$ (where $k = m \operatorname{div} 3$), and
  $g_{k,*} \circ f_{k,*} = 0$ by exactness at $H_k(B)$.\<close>

lemma (in ses_chain_complex) les_dd_zero_mod0:
  assumes n: "n \<in> ints"
    and nmod: "n zmod \<three> = \<zero>"
    and X: "X \<in> les_G(n)"
  shows "les_d(n \<rs> \<one>)`(les_d(n)`X) =
         TheNeutralElement(les_G(n \<rs> \<one> \<rs> \<one>), les_opG(n \<rs> \<one> \<rs> \<one>))"
proof -
  let ?k = "n zdiv \<three>"
  have kT: "?k \<in> ints" using zdiv_type by simp
  have nm1T: "n \<rs> \<one> \<in> ints"
    using n Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  have nm2T: "n \<rs> \<one> \<rs> \<one> \<in> ints"
    using nm1T Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  have nm1_mod: "(n \<rs> \<one>) zmod \<three> = \<two>"
    using zmod_0_minus_one[OF n nmod] .
  have nm2_mod: "(n \<rs> \<one> \<rs> \<one>) zmod \<three> = \<one>"
    using zmod_2_minus_one[OF nm1T nm1_mod] .
  have arith1: "(n \<rs> \<one>) \<ra> \<one> = n"
    using n Int_ZF_1_L8A(2) group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3)] by simp
  have arith2: "n \<rs> \<one> \<rs> \<one> \<ra> \<two> = n"
  proof -
    have s1: "n \<rs> \<one> \<rs> \<one> \<ra> \<one> = n \<rs> \<one>"
      using nm1T Int_ZF_1_L8A(2) group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3)] by simp
    have s2: "n \<rs> \<one> \<ra> \<one> = n"
      using n Int_ZF_1_L8A(2) group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3)] by simp
    have s3: "n \<rs> \<one> \<rs> \<one> \<ra> \<two> = n \<rs> \<one> \<rs> \<one> \<ra> \<one> \<ra> \<one>"
      using Int_ZF_1_1_L7(1)[OF nm2T Int_ZF_1_L8A(2) Int_ZF_1_L8A(2), symmetric] by simp
    from s1 s2 s3 show ?thesis by simp
  qed
  have two_neq_zero: "\<two> \<noteq> \<zero>"
    using int_one_two_are_pos(2) Int_ZF_1_5_L3 Int_ZF_2_L16C(2) by auto
  have one_neq_zero: "\<one> \<noteq> \<zero>" using int_zero_not_one by auto
  have one_neq_two: "\<one> \<noteq> \<two>"
    using Int_ZF_1_L14(1)[OF Int_ZF_1_L8A(2)] by auto
  have G_n: "les_G(n) = ab.src.Hn(?k)"
    unfolding les_G_def using nmod by simp
  have d_n: "les_d(n) = ab.Hn_map(?k)"
    unfolding les_d_def using nmod by simp
  have d_nm1: "les_d(n \<rs> \<one>) = bc.Hn_map(((n \<rs> \<one>) \<ra> \<one>) zdiv \<three>)"
    unfolding les_d_def using nm1_mod two_neq_zero by simp
  have d_nm1_k: "les_d(n \<rs> \<one>) = bc.Hn_map(?k)"
    using d_nm1 arith1 by simp
  have G_nm2: "les_G(n \<rs> \<one> \<rs> \<one>) = bc.tgt.Hn(?k)"
    unfolding les_G_def using nm2_mod one_neq_zero one_neq_two arith2 by simp
  have opG_nm2: "les_opG(n \<rs> \<one> \<rs> \<one>) = bc.tgt.HnOp(?k)"
    unfolding les_opG_def using nm2_mod one_neq_zero one_neq_two arith2 by simp
  have X_Hn: "X \<in> ab.src.Hn(?k)" using X G_n by simp
  have ab_map_fun: "ab.Hn_map(?k) : ab.src.Hn(?k) \<rightarrow> ab.tgt.Hn(?k)"
    using ab.Hn_map_is_hom[OF kT] unfolding Homomor_def by simp
  have val_Hn: "ab.Hn_map(?k)`X \<in> ab.tgt.Hn(?k)"
    using apply_type[OF ab_map_fun X_Hn] .
  have bc_map_fun: "bc.Hn_map(?k) : ab.tgt.Hn(?k) \<rightarrow> bc.tgt.Hn(?k)"
    using bc.Hn_map_is_hom[OF kT] unfolding Homomor_def by simp
  have exact_sub: "ab.Hn_map(?k)``ab.src.Hn(?k) \<subseteq>
    bc.Hn_map(?k)-``{TheNeutralElement(bc.tgt.Hn(?k), bc.tgt.HnOp(?k))}"
    using les_exact_at_HnB[OF kT] unfolding IsExactAt_def by auto
  have X_im: "ab.Hn_map(?k)`X \<in> ab.Hn_map(?k)``ab.src.Hn(?k)"
    using func_imagedef[OF ab_map_fun subset_refl] X_Hn by auto
  have mem: "ab.Hn_map(?k)`X \<in> bc.Hn_map(?k)-``{TheNeutralElement(bc.tgt.Hn(?k), bc.tgt.HnOp(?k))}"
    using exact_sub X_im by auto
  have zero: "bc.Hn_map(?k)`(ab.Hn_map(?k)`X) = TheNeutralElement(bc.tgt.Hn(?k), bc.tgt.HnOp(?k))"
    using func1_1_L15[OF bc_map_fun] val_Hn mem by auto
  show ?thesis using d_n d_nm1_k zero G_nm2 opG_nm2 by simp
qed

text\<open>When $m \bmod 3 = 2$ the interleaved boundary satisfies $d_{m-1} \circ d_m = 0$:
  $d_m = g_{k,*}$ and $d_{m-1} = \delta_k$ (where $k = (m+1) \operatorname{div} 3$), and
  $\delta_k \circ g_{k,*} = 0$ by exactness at $H_k(C)$.\<close>

lemma (in ses_chain_complex) les_dd_zero_mod2:
  assumes n: "n \<in> ints"
    and nmod: "n zmod \<three> = \<two>"
    and X: "X \<in> les_G(n)"
  shows "les_d(n \<rs> \<one>)`(les_d(n)`X) =
         TheNeutralElement(les_G(n \<rs> \<one> \<rs> \<one>), les_opG(n \<rs> \<one> \<rs> \<one>))"
proof -
  let ?k = "(n \<ra> \<one>) zdiv \<three>"
  have kT: "?k \<in> ints" using zdiv_type by simp
  have km1T: "?k \<rs> \<one> \<in> ints"
    using kT Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  have nm1T: "n \<rs> \<one> \<in> ints"
    using n Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  have nm2T: "n \<rs> \<one> \<rs> \<one> \<in> ints"
    using nm1T Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  have nm1_mod: "(n \<rs> \<one>) zmod \<three> = \<one>"
    using zmod_2_minus_one[OF n nmod] .
  have nm2_mod: "(n \<rs> \<one> \<rs> \<one>) zmod \<three> = \<zero>"
    using zmod_1_minus_one[OF nm1T nm1_mod] .
  have arith1: "(n \<rs> \<one>) \<ra> \<one> = n"
    using n Int_ZF_1_L8A(2) group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3)] by simp
  have arith2: "n \<rs> \<one> \<rs> \<one> \<ra> \<two> = n"
  proof -
    have s1: "n \<rs> \<one> \<rs> \<one> \<ra> \<one> = n \<rs> \<one>"
      using nm1T Int_ZF_1_L8A(2) group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3)] by simp
    have s2: "n \<rs> \<one> \<ra> \<one> = n"
      using n Int_ZF_1_L8A(2) group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3)] by simp
    have s3: "n \<rs> \<one> \<rs> \<one> \<ra> \<two> = n \<rs> \<one> \<rs> \<one> \<ra> \<one> \<ra> \<one>"
      using Int_ZF_1_1_L7(1)[OF nm2T Int_ZF_1_L8A(2) Int_ZF_1_L8A(2), symmetric] by simp
    from s1 s2 s3 show ?thesis by simp
  qed
  have arith_d: "(n \<rs> \<one>) \<ra> \<two> = n \<ra> \<one>"
  proof -
    have s: "(n \<rs> \<one>) \<ra> \<two> = (n \<rs> \<one>) \<ra> \<one> \<ra> \<one>"
      using Int_ZF_1_1_L7(1)[OF nm1T Int_ZF_1_L8A(2) Int_ZF_1_L8A(2), symmetric] by simp
    from s arith1 show ?thesis by simp
  qed
  have arith3: "n \<rs> \<one> \<rs> \<one> \<ra> \<three> = n \<ra> \<one>"
  proof -
    have s: "n \<rs> \<one> \<rs> \<one> \<ra> \<three> = n \<rs> \<one> \<rs> \<one> \<ra> \<two> \<ra> \<one>"
      using Int_ZF_1_1_L7(1)[OF nm2T int_two_three_are_int(1) Int_ZF_1_L8A(2), symmetric]
      by simp
    from s arith2 show ?thesis by simp
  qed
  have kdiv: "(n \<rs> \<one> \<rs> \<one>) zdiv \<three> = ?k \<rs> \<one>"
  proof -
    have h: "?k = (n \<rs> \<one> \<rs> \<one>) zdiv \<three> \<ra> \<one>"
      using zdiv_add_three[OF nm2T] arith3 by simp
    have hT: "(n \<rs> \<one> \<rs> \<one>) zdiv \<three> \<in> \<int>" using zdiv_type by simp
    from h show ?thesis
      using hT Int_ZF_1_L8A(2)
            group0.inv_cancel_two(2)[OF Int_ZF_1_T2(3)] by simp
  qed
  have two_neq_zero: "\<two> \<noteq> \<zero>"
    using int_one_two_are_pos(2) Int_ZF_1_5_L3 Int_ZF_2_L16C(2) by auto
  have one_neq_zero: "\<one> \<noteq> \<zero>" using int_zero_not_one by auto
  have one_neq_two: "\<one> \<noteq> \<two>"
    using Int_ZF_1_L14(1)[OF Int_ZF_1_L8A(2)] by auto
  have G_n: "les_G(n) = ab.tgt.Hn(?k)"
    unfolding les_G_def using nmod two_neq_zero by simp
  have d_n: "les_d(n) = bc.Hn_map(?k)"
    unfolding les_d_def using nmod two_neq_zero by simp
  have d_nm1: "les_d(n \<rs> \<one>) = delta(((n \<rs> \<one>) \<ra> \<two>) zdiv \<three>)"
    unfolding les_d_def using nm1_mod one_neq_zero one_neq_two by simp
  have d_nm1_k: "les_d(n \<rs> \<one>) = delta(?k)"
    using d_nm1 arith_d by simp
  have G_nm2: "les_G(n \<rs> \<one> \<rs> \<one>) = ab.src.Hn(?k \<rs> \<one>)"
    unfolding les_G_def using nm2_mod kdiv by simp
  have opG_nm2: "les_opG(n \<rs> \<one> \<rs> \<one>) = ab.src.HnOp(?k \<rs> \<one>)"
    unfolding les_opG_def using nm2_mod kdiv by simp
  have X_Hn: "X \<in> ab.tgt.Hn(?k)" using X G_n by simp
  have bc_map_fun: "bc.Hn_map(?k) : ab.tgt.Hn(?k) \<rightarrow> bc.tgt.Hn(?k)"
    using bc.Hn_map_is_hom[OF kT] unfolding Homomor_def by simp
  have val_Hn: "bc.Hn_map(?k)`X \<in> bc.tgt.Hn(?k)"
    using apply_type[OF bc_map_fun X_Hn] .
  have delta_fun: "delta(?k) : bc.tgt.Hn(?k) \<rightarrow> ab.src.Hn(?k \<rs> \<one>)"
    using delta_fun[OF kT] .
  have exact_sub: "bc.Hn_map(?k)``ab.tgt.Hn(?k) \<subseteq>
    delta(?k)-``{TheNeutralElement(ab.src.Hn(?k \<rs> \<one>), ab.src.HnOp(?k \<rs> \<one>))}"
    using les_exact_at_HnC[OF kT] unfolding IsExactAt_def by auto
  have X_im: "bc.Hn_map(?k)`X \<in> bc.Hn_map(?k)``ab.tgt.Hn(?k)"
    using func_imagedef[OF bc_map_fun subset_refl] X_Hn by auto
  have mem: "bc.Hn_map(?k)`X \<in>
    delta(?k)-``{TheNeutralElement(ab.src.Hn(?k \<rs> \<one>), ab.src.HnOp(?k \<rs> \<one>))}"
    using exact_sub X_im by auto
  have zero: "delta(?k)`(bc.Hn_map(?k)`X) =
              TheNeutralElement(ab.src.Hn(?k \<rs> \<one>), ab.src.HnOp(?k \<rs> \<one>))"
    using func1_1_L15[OF delta_fun] val_Hn mem by auto
  show ?thesis using d_n d_nm1_k zero G_nm2 opG_nm2 by simp
qed

text\<open>When $m \bmod 3 = 1$ the interleaved boundary satisfies $d_{m-1} \circ d_m = 0$:
  $d_m = \delta_k$ and $d_{m-1} = f_{k-1,*}$ (where $k = (m+2) \operatorname{div} 3$), and
  $f_{k-1,*} \circ \delta_k = 0$ by exactness at $H_{k-1}(A)$.\<close>

lemma (in ses_chain_complex) les_dd_zero_mod1:
  assumes n: "n \<in> ints"
    and nmod: "n zmod \<three> = \<one>"
    and X: "X \<in> les_G(n)"
  shows "les_d(n \<rs> \<one>)`(les_d(n)`X) =
         TheNeutralElement(les_G(n \<rs> \<one> \<rs> \<one>), les_opG(n \<rs> \<one> \<rs> \<one>))"
proof -
  let ?k = "(n \<ra> \<two>) zdiv \<three>"
  have kT: "?k \<in> ints" using zdiv_type by simp
  have km1T: "?k \<rs> \<one> \<in> ints"
    using kT Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  have nm1T: "n \<rs> \<one> \<in> ints"
    using n Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  have nm2T: "n \<rs> \<one> \<rs> \<one> \<in> ints"
    using nm1T Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  have nm1_mod: "(n \<rs> \<one>) zmod \<three> = \<zero>"
    using zmod_1_minus_one[OF n nmod] .
  have nm2_mod: "(n \<rs> \<one> \<rs> \<one>) zmod \<three> = \<two>"
    using zmod_0_minus_one[OF nm1T nm1_mod] .
  have arith_k: "n \<ra> \<two> = (n \<rs> \<one>) \<ra> \<three>"
  proof -
    have h1: "(n \<rs> \<one>) \<ra> \<one> = n"
      using n Int_ZF_1_L8A(2) group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3)] by simp
    have h2: "(n \<rs> \<one>) \<ra> \<one> \<ra> \<two> = (n \<rs> \<one>) \<ra> \<three>"
      using Int_ZF_1_1_L7(1)[OF nm1T Int_ZF_1_L8A(2) int_two_three_are_int(1)]
            Int_ZF_1_1_L5(4)[OF Int_ZF_1_L8A(2) int_two_three_are_int(1)] by simp
    from h1 h2 show ?thesis by simp
  qed
  have kdiv: "(n \<rs> \<one>) zdiv \<three> = ?k \<rs> \<one>"
  proof -
    have h: "?k = (n \<rs> \<one>) zdiv \<three> \<ra> \<one>"
      using zdiv_add_three[OF nm1T] arith_k by simp
    have hT: "(n \<rs> \<one>) zdiv \<three> \<in> \<int>" using zdiv_type by simp
    from h show ?thesis
      using hT Int_ZF_1_L8A(2)
            group0.inv_cancel_two(2)[OF Int_ZF_1_T2(3)] by simp
  qed
  have arith_nm2: "(n \<rs> \<one> \<rs> \<one>) \<ra> \<one> = n \<rs> \<one>"
    using nm1T Int_ZF_1_L8A(2) group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3)] by simp
  have two_neq_zero: "\<two> \<noteq> \<zero>"
    using int_one_two_are_pos(2) Int_ZF_1_5_L3 Int_ZF_2_L16C(2) by auto
  have one_neq_zero: "\<one> \<noteq> \<zero>" using int_zero_not_one by auto
  have one_neq_two: "\<one> \<noteq> \<two>"
    using Int_ZF_1_L14(1)[OF Int_ZF_1_L8A(2)] by auto
  have G_n: "les_G(n) = bc.tgt.Hn(?k)"
    unfolding les_G_def using nmod one_neq_zero one_neq_two by simp
  have d_n: "les_d(n) = delta(?k)"
    unfolding les_d_def using nmod one_neq_zero one_neq_two by simp
  have d_nm1: "les_d(n \<rs> \<one>) = ab.Hn_map((n \<rs> \<one>) zdiv \<three>)"
    unfolding les_d_def using nm1_mod by simp
  have d_nm1_k: "les_d(n \<rs> \<one>) = ab.Hn_map(?k \<rs> \<one>)"
    using d_nm1 kdiv by simp
  have G_nm2: "les_G(n \<rs> \<one> \<rs> \<one>) = ab.tgt.Hn(?k \<rs> \<one>)"
    unfolding les_G_def using nm2_mod two_neq_zero arith_nm2 kdiv by simp
  have opG_nm2: "les_opG(n \<rs> \<one> \<rs> \<one>) = ab.tgt.HnOp(?k \<rs> \<one>)"
    unfolding les_opG_def using nm2_mod two_neq_zero arith_nm2 kdiv by simp
  have X_Hn: "X \<in> bc.tgt.Hn(?k)" using X G_n by simp
  have delta_fun: "delta(?k) : bc.tgt.Hn(?k) \<rightarrow> ab.src.Hn(?k \<rs> \<one>)"
    using delta_fun[OF kT] .
  have val_Hn: "delta(?k)`X \<in> ab.src.Hn(?k \<rs> \<one>)"
    using apply_type[OF delta_fun X_Hn] .
  have hn_map_fun: "ab.Hn_map(?k \<rs> \<one>) : ab.src.Hn(?k \<rs> \<one>) \<rightarrow> ab.tgt.Hn(?k \<rs> \<one>)"
    using ab.Hn_map_is_hom[OF km1T] unfolding Homomor_def by simp
  have exact_sub: "delta(?k)``bc.tgt.Hn(?k) \<subseteq>
    ab.Hn_map(?k \<rs> \<one>)-``{TheNeutralElement(ab.tgt.Hn(?k \<rs> \<one>), ab.tgt.HnOp(?k \<rs> \<one>))}"
    using les_exact_at_HnA[OF kT] unfolding IsExactAt_def by auto
  have X_im: "delta(?k)`X \<in> delta(?k)``bc.tgt.Hn(?k)"
    using func_imagedef[OF delta_fun subset_refl] X_Hn by auto
  have mem: "delta(?k)`X \<in>
    ab.Hn_map(?k \<rs> \<one>)-``{TheNeutralElement(ab.tgt.Hn(?k \<rs> \<one>), ab.tgt.HnOp(?k \<rs> \<one>))}"
    using exact_sub X_im by auto
  have zero: "ab.Hn_map(?k \<rs> \<one>)`(delta(?k)`X) =
              TheNeutralElement(ab.tgt.Hn(?k \<rs> \<one>), ab.tgt.HnOp(?k \<rs> \<one>))"
    using func1_1_L15[OF hn_map_fun] val_Hn mem by auto
  show ?thesis using d_n d_nm1_k zero G_nm2 opG_nm2 by simp
qed

text\<open>The $n$-th group in the long exact sequence is a group.\<close>

lemma (in ses_chain_complex) les_G_is_group:
  assumes n: "n \<in> ints"
  shows "IsAgroup(les_G(n), les_opG(n))"
proof -
  have two_neq_zero: "\<two> \<noteq> \<zero>"
    using int_one_two_are_pos(2) Int_ZF_1_5_L3 Int_ZF_2_L16C(2) by auto
  have one_neq_zero: "\<one> \<noteq> \<zero>" using int_zero_not_one by auto
  have one_neq_two: "\<one> \<noteq> \<two>"
    using Int_ZF_1_L14(1)[OF Int_ZF_1_L8A(2)] by auto
  show ?thesis using zmod_three_cases[OF n]
  proof (elim disjE)
    assume nmod: "n zmod \<three> = \<zero>"
    have kT: "(n zdiv \<three>) \<in> ints" using zdiv_type by simp
    show ?thesis unfolding les_G_def les_opG_def
      using ab.src.Hn_is_group[OF kT] nmod by simp
  next
    assume nmod: "n zmod \<three> = \<one>"
    have kT: "((n \<ra> \<two>) zdiv \<three>) \<in> ints" using zdiv_type by simp
    show ?thesis unfolding les_G_def les_opG_def
      using bc.tgt.Hn_is_group[OF kT] nmod one_neq_zero one_neq_two by simp
  next
    assume nmod: "n zmod \<three> = \<two>"
    have kT: "((n \<ra> \<one>) zdiv \<three>) \<in> ints" using zdiv_type by simp
    show ?thesis unfolding les_G_def les_opG_def
      using ab.tgt.Hn_is_group[OF kT] nmod two_neq_zero one_neq_zero by simp
  qed
qed

text\<open>The $n$-th group in the long exact sequence is abelian.\<close>

lemma (in ses_chain_complex) les_G_is_abelian:
  assumes n: "n \<in> ints"
  shows "les_opG(n) {is commutative on} les_G(n)"
proof -
  have two_neq_zero: "\<two> \<noteq> \<zero>"
    using int_one_two_are_pos(2) Int_ZF_1_5_L3 Int_ZF_2_L16C(2) by auto
  have one_neq_zero: "\<one> \<noteq> \<zero>" using int_zero_not_one by auto
  have one_neq_two: "\<one> \<noteq> \<two>"
    using Int_ZF_1_L14(1)[OF Int_ZF_1_L8A(2)] by auto
  show ?thesis using zmod_three_cases[OF n]
  proof (elim disjE)
    assume nmod: "n zmod \<three> = \<zero>"
    have kT: "(n zdiv \<three>) \<in> ints" using zdiv_type by simp
    show ?thesis unfolding les_G_def les_opG_def
      using ab.src.Hn_is_abelian[OF kT] nmod by simp
  next
    assume nmod: "n zmod \<three> = \<one>"
    have kT: "((n \<ra> \<two>) zdiv \<three>) \<in> ints" using zdiv_type by simp
    show ?thesis unfolding les_G_def les_opG_def
      using bc.tgt.Hn_is_abelian[OF kT] nmod one_neq_zero one_neq_two by simp
  next
    assume nmod: "n zmod \<three> = \<two>"
    have kT: "((n \<ra> \<one>) zdiv \<three>) \<in> ints" using zdiv_type by simp
    show ?thesis unfolding les_G_def les_opG_def
      using ab.tgt.Hn_is_abelian[OF kT] nmod two_neq_zero one_neq_zero by simp
  qed
qed

text\<open>The $n$-th boundary map in the long exact sequence is a group homomorphism.\<close>

lemma (in ses_chain_complex) les_d_is_hom:
  assumes n: "n \<in> ints"
  shows "Homomor(les_d(n), les_G(n), les_opG(n), les_G(n \<rs> \<one>), les_opG(n \<rs> \<one>))"
proof -
  have nm1T: "n \<rs> \<one> \<in> ints"
    using n Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
  have two_neq_zero: "\<two> \<noteq> \<zero>"
    using int_one_two_are_pos(2) Int_ZF_1_5_L3 Int_ZF_2_L16C(2) by auto
  have one_neq_zero: "\<one> \<noteq> \<zero>" using int_zero_not_one by auto
  have one_neq_two: "\<one> \<noteq> \<two>"
    using Int_ZF_1_L14(1)[OF Int_ZF_1_L8A(2)] by auto
  show ?thesis using zmod_three_cases[OF n]
  proof (elim disjE)
    assume nmod: "n zmod \<three> = \<zero>"
    let ?k = "n zdiv \<three>"
    have kT: "?k \<in> ints" using zdiv_type by simp
    have nm1_mod: "(n \<rs> \<one>) zmod \<three> = \<two>" using zmod_0_minus_one[OF n nmod] .
    have arith1: "(n \<rs> \<one>) \<ra> \<one> = n"
      using n Int_ZF_1_L8A(2) group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3)] by simp
    have G_n: "les_G(n) = ab.src.Hn(?k)"
      unfolding les_G_def using nmod by simp
    have opG_n: "les_opG(n) = ab.src.HnOp(?k)"
      unfolding les_opG_def using nmod by simp
    have d_n: "les_d(n) = ab.Hn_map(?k)"
      unfolding les_d_def using nmod by simp
    have G_nm1: "les_G(n \<rs> \<one>) = ab.tgt.Hn(?k)"
      unfolding les_G_def using nm1_mod arith1 two_neq_zero one_neq_zero by simp
    have opG_nm1: "les_opG(n \<rs> \<one>) = ab.tgt.HnOp(?k)"
      unfolding les_opG_def using nm1_mod arith1 two_neq_zero one_neq_zero by simp
    show ?thesis using d_n G_n opG_n G_nm1 opG_nm1 ab.Hn_map_is_hom[OF kT] by simp
  next
    assume nmod: "n zmod \<three> = \<one>"
    let ?k = "(n \<ra> \<two>) zdiv \<three>"
    have kT: "?k \<in> ints" using zdiv_type by simp
    have nm1_mod: "(n \<rs> \<one>) zmod \<three> = \<zero>" using zmod_1_minus_one[OF n nmod] .
    have arith_k: "n \<ra> \<two> = (n \<rs> \<one>) \<ra> \<three>"
    proof -
      have h1: "(n \<rs> \<one>) \<ra> \<one> = n"
        using n Int_ZF_1_L8A(2) group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3)] by simp
      have h2: "(n \<rs> \<one>) \<ra> \<one> \<ra> \<two> = (n \<rs> \<one>) \<ra> \<three>"
        using Int_ZF_1_1_L7(1)[OF nm1T Int_ZF_1_L8A(2) int_two_three_are_int(1)]
              Int_ZF_1_1_L5(4)[OF Int_ZF_1_L8A(2) int_two_three_are_int(1)] by simp
      from h1 h2 show ?thesis by simp
    qed
    have kdiv: "(n \<rs> \<one>) zdiv \<three> = ?k \<rs> \<one>"
    proof -
      have h: "?k = (n \<rs> \<one>) zdiv \<three> \<ra> \<one>"
        using zdiv_add_three[OF nm1T] arith_k by simp
      have hT: "(n \<rs> \<one>) zdiv \<three> \<in> \<int>" using zdiv_type by simp
      from h show ?thesis
        using hT Int_ZF_1_L8A(2)
              group0.inv_cancel_two(2)[OF Int_ZF_1_T2(3)] by simp
    qed
    have G_n: "les_G(n) = bc.tgt.Hn(?k)"
      unfolding les_G_def using nmod one_neq_zero one_neq_two by simp
    have opG_n: "les_opG(n) = bc.tgt.HnOp(?k)"
      unfolding les_opG_def using nmod one_neq_zero one_neq_two by simp
    have d_n: "les_d(n) = delta(?k)"
      unfolding les_d_def using nmod one_neq_zero one_neq_two by simp
    have G_nm1: "les_G(n \<rs> \<one>) = ab.src.Hn(?k \<rs> \<one>)"
      unfolding les_G_def using nm1_mod kdiv by simp
    have opG_nm1: "les_opG(n \<rs> \<one>) = ab.src.HnOp(?k \<rs> \<one>)"
      unfolding les_opG_def using nm1_mod kdiv by simp
    show ?thesis using d_n G_n opG_n G_nm1 opG_nm1 delta_is_hom[OF kT] by simp
  next
    assume nmod: "n zmod \<three> = \<two>"
    let ?k = "(n \<ra> \<one>) zdiv \<three>"
    have kT: "?k \<in> ints" using zdiv_type by simp
    have nm1_mod: "(n \<rs> \<one>) zmod \<three> = \<one>" using zmod_2_minus_one[OF n nmod] .
    have arith: "(n \<rs> \<one>) \<ra> \<two> = n \<ra> \<one>"
    proof -
      have s1: "(n \<rs> \<one>) \<ra> \<one> = n"
        using n Int_ZF_1_L8A(2) group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3)] by simp
      have s2: "(n \<rs> \<one>) \<ra> \<two> = (n \<rs> \<one>) \<ra> \<one> \<ra> \<one>"
        using Int_ZF_1_1_L7(1)[OF nm1T Int_ZF_1_L8A(2) Int_ZF_1_L8A(2), symmetric] by simp
      from s1 s2 show ?thesis by simp
    qed
    have G_n: "les_G(n) = ab.tgt.Hn(?k)"
      unfolding les_G_def using nmod two_neq_zero one_neq_zero by simp
    have opG_n: "les_opG(n) = ab.tgt.HnOp(?k)"
      unfolding les_opG_def using nmod two_neq_zero one_neq_zero by simp
    have d_n: "les_d(n) = bc.Hn_map(?k)"
      unfolding les_d_def using nmod two_neq_zero one_neq_zero by simp
    have G_nm1: "les_G(n \<rs> \<one>) = bc.tgt.Hn(?k)"
      unfolding les_G_def using nm1_mod arith one_neq_zero one_neq_two by simp
    have opG_nm1: "les_opG(n \<rs> \<one>) = bc.tgt.HnOp(?k)"
      unfolding les_opG_def using nm1_mod arith one_neq_zero one_neq_two by simp
    show ?thesis using d_n G_n opG_n G_nm1 opG_nm1 bc.Hn_map_is_hom[OF kT] by simp
  qed
qed

text\<open>The interleaved long exact sequence data forms a chain complex.\<close>

theorem (in ses_chain_complex) les_is_chain_complex:
  shows "IsAchainComplex(les_G, les_opG, les_d)"
proof -
  have part1: "\<forall>n \<in> int.
      IsAgroup(les_G(n), les_opG(n)) \<and> les_opG(n) {is commutative on} les_G(n)"
    using les_G_is_group les_G_is_abelian by auto
  have part2: "\<forall>n \<in> int.
      Homomor(les_d(n), les_G(n), les_opG(n), les_G(n \<rs> \<one>), les_opG(n \<rs> \<one>))"
    using les_d_is_hom by auto
  have part3: "\<forall>n \<in> int.
      (les_d(n))``(les_G(n)) \<subseteq>
      (les_d(n \<rs> \<one>))-``{TheNeutralElement(les_G(n \<rs> \<one> \<rs> \<one>), les_opG(n \<rs> \<one> \<rs> \<one>))}"
  proof (rule ballI)
    fix n assume n: "n \<in> int"
    have nm1T: "n \<rs> \<one> \<in> ints"
      using n Int_ZF_1_L10(1) Int_ZF_1_L8A(2) by (simp add: zdiff_type)
    have dn_fun: "les_d(n) : les_G(n) \<rightarrow> les_G(n \<rs> \<one>)"
      using les_d_is_hom n unfolding Homomor_def by simp
    have dnm1_fun: "les_d(n \<rs> \<one>) : les_G(n \<rs> \<one>) \<rightarrow> les_G(n \<rs> \<one> \<rs> \<one>)"
      using les_d_is_hom[OF nm1T] unfolding Homomor_def by simp
    show "(les_d(n))``(les_G(n)) \<subseteq>
      (les_d(n \<rs> \<one>))-``{TheNeutralElement(les_G(n \<rs> \<one> \<rs> \<one>), les_opG(n \<rs> \<one> \<rs> \<one>))}"
    proof (rule subsetI)
      fix Y assume Ymem: "Y \<in> (les_d(n))``(les_G(n))"
      obtain X where XG: "X \<in> les_G(n)" and Yeq: "Y = les_d(n)`X"
        using func_imagedef[OF dn_fun subset_refl] Ymem by auto
      have YG: "Y \<in> les_G(n \<rs> \<one>)"
        using apply_type[OF dn_fun XG] Yeq by simp
      have ddX: "les_d(n \<rs> \<one>)`(les_d(n)`X) =
          TheNeutralElement(les_G(n \<rs> \<one> \<rs> \<one>), les_opG(n \<rs> \<one> \<rs> \<one>))"
      proof -
        have "n zmod \<three> = \<zero> \<or> n zmod \<three> = \<one> \<or> n zmod \<three> = \<two>"
          using zmod_three_cases n by auto
        then show ?thesis
        proof (elim disjE)
          assume hn: "n zmod \<three> = \<zero>"
          show ?thesis using les_dd_zero_mod0 n hn XG by auto
        next
          assume hn: "n zmod \<three> = \<one>"
          show ?thesis using les_dd_zero_mod1 n hn XG by auto
        next
          assume hn: "n zmod \<three> = \<two>"
          show ?thesis using les_dd_zero_mod2 n hn XG by auto
        qed
      qed
      have ddY: "les_d(n \<rs> \<one>)`Y =
          TheNeutralElement(les_G(n \<rs> \<one> \<rs> \<one>), les_opG(n \<rs> \<one> \<rs> \<one>))"
        using ddX Yeq by simp
      show "Y \<in> (les_d(n \<rs> \<one>))-``{TheNeutralElement(les_G(n \<rs> \<one> \<rs> \<one>), les_opG(n \<rs> \<one> \<rs> \<one>))}"
        using func1_1_L15[OF dnm1_fun] YG ddY by auto
    qed
  qed
  from part1 part2 part3 show ?thesis unfolding IsAchainComplex_def by auto
qed

sublocale ses_chain_complex \<subseteq> les: chain_complex where C=les_G and P=les_opG and d=les_d
  unfolding chain_complex_def using les_is_chain_complex by auto

corollary (in ses_chain_complex) les_is_long_exact_sequence:
  shows "les.IsLongExactSequence"
  unfolding les.IsLongExactSequence_def
proof(safe)
  fix n assume n:"n:\<int>"
  have df: "les_d(n):les_G(n)\<rightarrow>les_G(n\<rs>\<one>)"
    using les.cplx_hom[OF n] unfolding Homomor_def by auto
  {
    {
      assume nn:"n zmod \<three> = \<two>"
      then have as:"(n\<ra>\<one>) zmod \<three> = \<zero>" using zmod_2_plus_one n by auto
      let ?k = "(n\<ra>\<one>) zdiv \<three>"
      have kT: "?k \<in> ints" using zdiv_type by simp
      have nm1T: "(n\<ra>\<one>) \<rs> \<one> = n"
        using Int_ZF_1_2_L3(3) n int_zero_one_are_int(2) by auto
      have nm2T: "(n\<ra>\<one>) \<rs> \<one> \<rs> \<one> \<in> ints"
        using nm1T Int_ZF_1_L10(1) int_zero_one_are_int(2) n by auto
      have nm1_mod: "((n\<ra>\<one>) \<rs> \<one>) zmod \<three> = \<two>"
        using nm1T nn by auto
      have nm2_mod: "((n\<ra>\<one>) \<rs> \<one> \<rs> \<one>) zmod \<three> = \<one>"
        using zmod_2_minus_one n nm1T nm1_mod by auto
      have arith1: "((n\<ra>\<one>) \<rs> \<one>) \<ra> \<one> = n\<ra>\<one>"
        using nm1T by simp
      have arith2: "(n\<ra>\<one>) \<rs> \<one> \<rs> \<one> \<ra> \<two> = n\<ra>\<one>"
      proof -
        have s1: "(n\<ra>\<one>) \<rs> \<one> \<rs> \<one> \<ra> \<one> = (n\<ra>\<one>) \<rs> \<one>"
          using nm1T Int_ZF_1_L8A(2) group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3), of _ \<one>] n by simp
        have s2: "(n\<ra>\<one>) \<rs> \<one> \<ra> \<one> = (n\<ra>\<one>)"
          using nm1T by simp
        have s3: "(n\<ra>\<one>) \<rs> \<one> \<rs> \<one> \<ra> \<two> = (n\<ra>\<one>) \<rs> \<one> \<rs> \<one> \<ra> \<one> \<ra> \<one>"
          using Int_ZF_1_1_L7(1)[OF nm2T Int_ZF_1_L8A(2) Int_ZF_1_L8A(2), symmetric] by simp
        from s1 s2 s3 show ?thesis by simp
      qed
      have two_neq_zero: "\<two> \<noteq> \<zero>"
        using int_one_two_are_pos(2) Int_ZF_1_5_L3 Int_ZF_2_L16C(2) by auto
      have one_neq_zero: "\<one> \<noteq> \<zero>" using int_zero_not_one by auto
      have one_neq_two: "\<one> \<noteq> \<two>"
        using Int_ZF_1_L14(1)[OF Int_ZF_1_L8A(2)] by auto
      have G_n: "les_G((n\<ra>\<one>)) = ab.src.Hn(?k)"
        unfolding les_G_def using as by simp
      have d_n: "les_d((n\<ra>\<one>)) = ab.Hn_map(?k)"
        unfolding les_d_def using as by simp
      have d_nm1: "les_d((n\<ra>\<one>) \<rs> \<one>) = bc.Hn_map((((n\<ra>\<one>) \<rs> \<one>) \<ra> \<one>) zdiv \<three>)"
        unfolding les_d_def using nm1_mod two_neq_zero by simp
      have d_nm1_k: "les_d((n\<ra>\<one>) \<rs> \<one>) = bc.Hn_map(?k)"
        using d_nm1 arith1 by simp
      have G_nm2: "les_G((n\<ra>\<one>) \<rs> \<one> \<rs> \<one>) = bc.tgt.Hn(?k)"
        unfolding les_G_def using nm2_mod one_neq_zero one_neq_two arith2 by simp
      have opG_nm2: "les_opG((n\<ra>\<one>) \<rs> \<one> \<rs> \<one>) = bc.tgt.HnOp(?k)"
        unfolding les_opG_def using nm2_mod one_neq_zero one_neq_two arith2 by simp
      from G_n d_n d_nm1_k G_nm2 opG_nm2 have "IsExactAt(les_d(n\<ra>\<one>), les_G(n\<ra>\<one>), les_d((n\<ra>\<one>)\<rs>\<one>), 
        les_G((n\<ra>\<one>)\<rs>\<one>\<rs>\<one>), les_opG((n\<ra>\<one>)\<rs>\<one>\<rs>\<one>))"
        using long_exact_sequence[OF kT] by auto
      then have "les.Boundaries(n) = les.Cycles(n)"
        unfolding IsExactAt_def using nm1T by auto
    } moreover
    {
      assume A:"n zmod \<three> = \<one>"
      have "(n\<ra>\<one>) zmod \<three> = ((n zmod \<three>)\<ra>\<one>)zmod \<three>"
        using zmod_add_left[OF n Int_ZF_1_L8A(2)] int_two_three_are_int(2) by auto
      with A have B:"(n\<ra>\<one>) zmod \<three> = \<two> zmod \<three>" by auto
      have T: "𝟬∈ℤ" "𝟭∈ℤ" "𝟮∈ℤ" "𝟯∈ℤ"
        using int_zero_one_are_int int_two_three_are_int by auto
      have lt23: "𝟮 $< 𝟯"
      proof -
        have "𝟮 \<lsq> 𝟯" using T(3) Int_ZF_2_L12B by simp
        moreover have "𝟮 ≠ 𝟯" using Int_ZF_1_L14(1)[OF T(3)] by auto
        ultimately show ?thesis using Int_ZF_2_L9 by auto
      qed
      have le02: "𝟬 \<lsq> 𝟮"
      proof -
        have "𝟬 \<lsq> 𝟭" using T Int_ZF_2_L12B[of 𝟬] Int_ZF_1_1_L4 by simp
        moreover have "𝟭 \<lsq> 𝟮" using Int_ZF_2_L16B by simp
        ultimately show ?thesis using Int_order_transitive by auto
      qed
      have h1: "#0 $≤ 𝟮" using le02 Int_ZF_2_L1A Int_ZF_1_L8 by auto
      have two_mod: "𝟮 zmod 𝟯 = 𝟮"
      using zmod_pos_pos_trivial[OF h1 lt23] T(3) intify_ident by auto
      with B have nn:"(n\<ra>\<one>) zmod \<three> = \<two>" by auto
      have C:"n\<ra>\<one>\<ra>\<one> = n\<ra>\<two>" using Int_ZF_1_1_L7(1)
        n int_zero_one_are_int(2) by auto
      let ?k = "(n\<ra>\<two>) zdiv \<three>"
      have kT: "?k \<in> ints" using zdiv_type by simp
      have nm1T: "(n\<ra>\<one>) \<rs> \<one> = n"
        using Int_ZF_1_2_L3(3) n int_zero_one_are_int(2) by auto
      have nm2T: "(n\<ra>\<one>) \<rs> \<one> \<rs> \<one> \<in> ints"
        using nm1T Int_ZF_1_L10(1) int_zero_one_are_int(2) n by auto
      have nm1_mod: "((n\<ra>\<one>) \<rs> \<one>) zmod \<three> = \<one>"
        using nm1T A by auto
      have nm2_mod: "((n\<ra>\<one>) \<rs> \<one> \<rs> \<one>) zmod \<three> = \<zero>"
        using zmod_1_minus_one n nm1T nm1_mod by auto
      have arith1: "((n\<ra>\<one>) \<rs> \<one>) \<ra> \<one> = n\<ra>\<one>"
        using nm1T by simp
      have arith2: "(n\<ra>\<one>) \<rs> \<one> \<rs> \<one> \<ra> \<two> = n\<ra>\<one>"
      proof -
        have s1: "(n\<ra>\<one>) \<rs> \<one> \<rs> \<one> \<ra> \<one> = (n\<ra>\<one>) \<rs> \<one>"
          using nm1T Int_ZF_1_L8A(2) group0.inv_cancel_two(1)[OF Int_ZF_1_T2(3), of _ \<one>] n by simp
        have s2: "(n\<ra>\<one>) \<rs> \<one> \<ra> \<one> = (n\<ra>\<one>)"
          using nm1T by simp
        have s3: "(n\<ra>\<one>) \<rs> \<one> \<rs> \<one> \<ra> \<two> = (n\<ra>\<one>) \<rs> \<one> \<rs> \<one> \<ra> \<one> \<ra> \<one>"
          using Int_ZF_1_1_L7(1)[OF nm2T Int_ZF_1_L8A(2) Int_ZF_1_L8A(2), symmetric] by simp
        from s1 s2 s3 show ?thesis by simp
      qed
      have two_neq_zero: "\<two> \<noteq> \<zero>"
        using int_one_two_are_pos(2) Int_ZF_1_5_L3 Int_ZF_2_L16C(2) by auto
      have one_neq_zero: "\<one> \<noteq> \<zero>" using int_zero_not_one by auto
      have one_neq_two: "\<one> \<noteq> \<two>"
        using Int_ZF_1_L14(1)[OF Int_ZF_1_L8A(2)] by auto
      have G_n: "les_G(n \<ra> \<one>) = ab.tgt.Hn(?k)"
        unfolding les_G_def using two_neq_zero C nn by simp
      have d_n: "les_d(n \<ra> \<one>) = bc.Hn_map(?k)"
        unfolding les_d_def using two_neq_zero C nn by simp
      have d_nm1: "les_d((n \<ra> \<one>) \<rs> \<one>) = delta(((n \<ra>\<one> \<rs> \<one>) \<ra> \<two>) zdiv \<three>)"
        unfolding les_d_def using nm1_mod one_neq_zero one_neq_two by simp
      have d_nm1_k: "les_d((n \<ra> \<one>) \<rs> \<one>) = delta(?k)"
        using d_nm1 nm1T by simp
      have  "les_G((n \<ra> \<one>) \<rs> \<one> \<rs> \<one>) = ab.src.Hn((n \<rs> 𝟭) zdiv 𝟯)"
        unfolding les_G_def using nm2_mod nn nm1T by simp
      then have G_nm2:"les_G((n \<ra> \<one>) \<rs> \<one> \<rs> \<one>) = ab.src.Hn(?k\<rs>\<one>)" using zdiv_minus_one[OF n] by auto
      have  "les_opG((n \<ra> \<one>) \<rs> \<one> \<rs> \<one>) = ab.src.HnOp((n \<rs> \<one>) zdiv \<three>)"
        unfolding les_opG_def using nm2_mod nm1T by simp
      then have opG_nm2:"les_opG((n \<ra> \<one>) \<rs> \<one> \<rs> \<one>) = ab.src.HnOp(?k\<rs>\<one>)" using zdiv_minus_one[OF n] by auto
      from G_n d_n d_nm1_k G_nm2 opG_nm2 have "IsExactAt(les_d(n\<ra>\<one>), les_G(n\<ra>\<one>), les_d((n\<ra>\<one>)\<rs>\<one>), 
        les_G((n\<ra>\<one>)\<rs>\<one>\<rs>\<one>), les_opG((n\<ra>\<one>)\<rs>\<one>\<rs>\<one>))"
        using long_exact_sequence[OF kT] by auto
      then have "les.Boundaries(n) = les.Cycles(n)"
        unfolding IsExactAt_def using nm1T by auto
    } moreover
    {
      assume as:"n zmod \<three> = \<zero>"
      let ?k="(n zdiv \<three>)\<ra>\<one>"
      have kT: "?k \<in> ints" using zdiv_type Int_ZF_1_L8A(2) Int_ZF_1_1_L5(1) by simp
      have C:"(n\<ra>\<one>) zmod \<three> = \<one>" using zmod_0_plus_one n as by auto
      have eq:"(n \<ra> 𝟭 \<ra> 𝟮) zdiv 𝟯 = ?k" 
        using Int_ZF_1_L8A(2) n int_two_three_are_int(1) Int_ZF_1_1_L7(1) Int_ZF_1_1_L5(4)
          zdiv_add_three by auto
      have nm1T: "(n\<ra>\<one>) \<rs> \<one> = n"
        using Int_ZF_1_2_L3(3) n int_zero_one_are_int(2) by auto
      have ndivT: "((n zdiv \<three>)\<ra>\<one>) \<rs> \<one> = n zdiv \<three>"
        using Int_ZF_1_2_L3(3) n int_zero_one_are_int(2) by auto
      have two_neq_zero: "\<two> \<noteq> \<zero>"
        using int_one_two_are_pos(2) Int_ZF_1_5_L3 Int_ZF_2_L16C(2) by auto
      have one_neq_zero: "\<one> \<noteq> \<zero>" using int_zero_not_one by auto
      have one_neq_two: "\<one> \<noteq> \<two>"
        using Int_ZF_1_L14(1)[OF Int_ZF_1_L8A(2)] by auto
      have "les_G(n \<ra> \<one>) = bc.tgt.Hn((n \<ra> 𝟭 \<ra> 𝟮) zdiv 𝟯)"
        unfolding les_G_def using one_neq_zero one_neq_two C by simp
      then have G_n:"les_G(n \<ra> \<one>) = bc.tgt.Hn(?k)"
        using eq n by auto
      have d_n: "les_d(n \<ra> \<one>) = delta(?k)"
        unfolding les_d_def using eq one_neq_zero one_neq_two C by simp
      have d_nm1_k: "les_d((n \<ra> \<one>) \<rs> \<one>) = ab.Hn_map(?k\<rs>\<one>)"
        unfolding les_d_def using as nm1T ndivT by simp
      have G_nm2:"les_G((n \<ra> \<one>) \<rs> \<one> \<rs> \<one>) = ab.tgt.Hn(?k\<rs>\<one>)"
        unfolding les_G_def using nm1T zmod_0_minus_one[OF n as] two_neq_zero
        Int_ZF_1_2_L3(4)[OF n int_zero_one_are_int(2)] ndivT by simp
      have  opG_nm2:"les_opG((n \<ra> \<one>) \<rs> \<one> \<rs> \<one>) = ab.tgt.HnOp(?k\<rs>\<one>)"
        unfolding les_opG_def using nm1T zmod_0_minus_one[OF n as] two_neq_zero
        Int_ZF_1_2_L3(4)[OF n int_zero_one_are_int(2)] ndivT by simp
      from G_n d_n d_nm1_k G_nm2 opG_nm2 have "IsExactAt(les_d(n\<ra>\<one>), les_G(n\<ra>\<one>), les_d((n\<ra>\<one>)\<rs>\<one>), 
        les_G((n\<ra>\<one>)\<rs>\<one>\<rs>\<one>), les_opG((n\<ra>\<one>)\<rs>\<one>\<rs>\<one>))"
        using long_exact_sequence[OF kT] by auto
      then have "les.Boundaries(n) = les.Cycles(n)"
        unfolding IsExactAt_def using nm1T by auto
    }
    ultimately have "les.Boundaries(n) = les.Cycles(n)" using zmod_three_cases[OF n] by auto
  }
  then show "les.Boundaries(n) = les.Cycles(n)" by auto
qed

subsection \<open>The snake lemma\<close>

text\<open>A \emph{morphism of short exact sequences} is a commutative diagram
  \[
    0 \to A \xrightarrow{f} B \xrightarrow{g} C \to 0
  \]
  on top and
  \[
    0 \to A' \xrightarrow{f'} B' \xrightarrow{g'} C' \to 0
  \]
  on the bottom, connected by vertical group homomorphisms
  $\alpha \colon A \to A'$, $\beta \colon B \to B'$, $\gamma \colon C \to C'$
  such that $f' \circ \alpha = \beta \circ f$ and $g' \circ \beta = \gamma \circ g$.\<close>

locale ses_morphism =
  fixes A  :: i and PA :: i and f  :: i
    and B  :: i and PB :: i and g  :: i
    and C  :: i and PC :: i
    and A' :: i and PA':: i and f' :: i
    and B' :: i and PB':: i and g' :: i
    and C' :: i and PC':: i
    and \<alpha>  :: i and \<beta>  :: i and \<gamma>  :: i
  assumes row1:        "IsAshortExactSequence(A, PA, B, PB, C, PC, f, g)"
    and   row2:        "IsAshortExactSequence(A', PA', B', PB', C', PC', f', g')"
    and   hom_\<alpha>:       "Homomor(\<alpha>, A, PA, A', PA')"
    and   hom_\<beta>:       "Homomor(\<beta>, B, PB, B', PB')"
    and   hom_\<gamma>:       "Homomor(\<gamma>, C, PC, C', PC')"
    and   comm_left:   "f' O \<alpha> = \<beta> O f"
    and   comm_right:  "g' O \<beta> = \<gamma> O g"
    and   comm_A':    "PA' {is commutative on} A'"
    and   comm_B':    "PB' {is commutative on} B'"
    and   comm_C':    "PC' {is commutative on} C'"

text\<open>Kernel of each vertical map.\<close>

abbreviation (in ses_morphism) ker_\<alpha> :: i where
  "ker_\<alpha> \<equiv> \<alpha>-``{TheNeutralElement(A', PA')}"

abbreviation (in ses_morphism) ker_\<beta> :: i where
  "ker_\<beta> \<equiv> \<beta>-``{TheNeutralElement(B', PB')}"

abbreviation (in ses_morphism) ker_\<gamma> :: i where
  "ker_\<gamma> \<equiv> \<gamma>-``{TheNeutralElement(C', PC')}"

text\<open>Cokernel carrier and operation for each vertical map.\<close>

abbreviation (in ses_morphism) coker_\<alpha> :: i where
  "coker_\<alpha> \<equiv> A' // QuotientGroupRel(A', PA', \<alpha>``A)"

abbreviation (in ses_morphism) cokerOp_\<alpha> :: i where
  "cokerOp_\<alpha> \<equiv> QuotientGroupOp(A', PA', \<alpha>``A)"

abbreviation (in ses_morphism) coker_\<beta> :: i where
  "coker_\<beta> \<equiv> B' // QuotientGroupRel(B', PB', \<beta>``B)"

abbreviation (in ses_morphism) cokerOp_\<beta> :: i where
  "cokerOp_\<beta> \<equiv> QuotientGroupOp(B', PB', \<beta>``B)"

abbreviation (in ses_morphism) coker_\<gamma> :: i where
  "coker_\<gamma> \<equiv> C' // QuotientGroupRel(C', PC', \<gamma>``C)"

abbreviation (in ses_morphism) cokerOp_\<gamma> :: i where
  "cokerOp_\<gamma> \<equiv> QuotientGroupOp(C', PC', \<gamma>``C)"

text\<open>Basic structural lemmas: group types extracted from the SES rows.\<close>

lemma (in ses_morphism) grpA:  "IsAgroup(A, PA)"
  using row1 unfolding IsAshortExactSequence_def group_homo_def by auto

lemma (in ses_morphism) grpB:  "IsAgroup(B, PB)"
  using row1 unfolding IsAshortExactSequence_def group_homo_def by auto

lemma (in ses_morphism) grpC:  "IsAgroup(C, PC)"
  using row1 unfolding IsAshortExactSequence_def group_homo_def by auto

lemma (in ses_morphism) grpA': "IsAgroup(A', PA')"
  using row2 unfolding IsAshortExactSequence_def group_homo_def by auto

lemma (in ses_morphism) grpB': "IsAgroup(B', PB')"
  using row2 unfolding IsAshortExactSequence_def group_homo_def by auto

lemma (in ses_morphism) grpC': "IsAgroup(C', PC')"
  using row2 unfolding IsAshortExactSequence_def group_homo_def by auto

text\<open>The maps as typed functions.\<close>

lemma (in ses_morphism) f_fun:  "f  : A  \<rightarrow> B"
  using row1 unfolding IsAshortExactSequence_def group_homo_def Homomor_def by auto

lemma (in ses_morphism) g_fun:  "g  : B  \<rightarrow> C"
  using row1 unfolding IsAshortExactSequence_def group_homo_def Homomor_def by auto

lemma (in ses_morphism) f'_fun: "f' : A' \<rightarrow> B'"
  using row2 unfolding IsAshortExactSequence_def group_homo_def Homomor_def by auto

lemma (in ses_morphism) g'_fun: "g' : B' \<rightarrow> C'"
  using row2 unfolding IsAshortExactSequence_def group_homo_def Homomor_def by auto

lemma (in ses_morphism) \<alpha>_fun: "\<alpha> : A  \<rightarrow> A'"
  using hom_\<alpha> unfolding Homomor_def by auto

lemma (in ses_morphism) \<beta>_fun: "\<beta> : B  \<rightarrow> B'"
  using hom_\<beta> unfolding Homomor_def by auto

lemma (in ses_morphism) \<gamma>_fun: "\<gamma> : C  \<rightarrow> C'"
  using hom_\<gamma> unfolding Homomor_def by auto

text\<open>Image of $f$ equals kernel of $g$ (exactness at $B$).\<close>

lemma (in ses_morphism) row1_im_eq_ker:
  "f``A = g-``{TheNeutralElement(C, PC)}"
  using row1 unfolding IsAshortExactSequence_def IsExactAt_def by auto

text\<open>Image of $f'$ equals kernel of $g'$ (exactness at $B'$).\<close>

lemma (in ses_morphism) row2_im_eq_ker:
  "f'``A' = g'-``{TheNeutralElement(C', PC')}"
  using row2 unfolding IsAshortExactSequence_def IsExactAt_def by auto

text\<open>$f$ is injective.\<close>

lemma (in ses_morphism) f_inj: "f \<in> inj(A, B)"
proof -
  have ea: "IsExactAt(ZeroMap(1, A, PA), 1, f, B, PB)"
    using row1 unfolding IsAshortExactSequence_def by auto
  from ea have "f-``{TheNeutralElement(B, PB)} = {TheNeutralElement(A, PA)}"
    using ZeroMap_image[OF trivial_group grpA] unfolding IsExactAt_def by auto
  with group_homo.kernel_trivial_iff_injective[of A PA B PB f]
       row1 
  show ?thesis unfolding IsAshortExactSequence_def group_homo_def by auto
qed

text\<open>$f'$ is injective.\<close>

lemma (in ses_morphism) f'_inj: "f' \<in> inj(A', B')"
proof -
  have ea: "IsExactAt(ZeroMap(1, A', PA'), 1, f', B', PB')"
    using row2 unfolding IsAshortExactSequence_def by auto
  from ea have "f'-``{TheNeutralElement(B', PB')} = {TheNeutralElement(A', PA')}"
    using ZeroMap_image[OF trivial_group grpA'] unfolding IsExactAt_def by auto
  with group_homo.kernel_trivial_iff_injective[of A' PA' B' PB' f']
       row2
  show ?thesis unfolding IsAshortExactSequence_def group_homo_def by auto
qed

text\<open>$g$ is surjective.\<close>

lemma (in ses_morphism) g_surj: "g``B = C"
proof -
  have ea: "IsExactAt(g, B, ZeroMap(C, 1, TrivOp), 1, TrivOp)"
    using row1 unfolding IsAshortExactSequence_def by auto
  from ea have "g``B = ZeroMap(C, 1, TrivOp)-``{TheNeutralElement(1, TrivOp)}"
    unfolding IsExactAt_def by simp
  also have "\<dots> = C"
    using ZeroMap_preimage_full[OF grpC trivial_group] TrivOp_ne by simp
  finally show ?thesis .
qed

text\<open>$g'$ is surjective.\<close>

lemma (in ses_morphism) g'_surj: "g'``B' = C'"
proof -
  have ea: "IsExactAt(g', B', ZeroMap(C', 1, TrivOp), 1, TrivOp)"
    using row2 unfolding IsAshortExactSequence_def by auto
  from ea have "g'``B' = ZeroMap(C', 1, TrivOp)-``{TheNeutralElement(1, TrivOp)}"
    unfolding IsExactAt_def by simp
  also have "\<dots> = C'"
    using ZeroMap_preimage_full[OF grpC' trivial_group] TrivOp_ne by simp
  finally show ?thesis .
qed

text\<open>Given $b \in B$ such that $\beta(b) \in \mathrm{im}(f')$, the unique preimage
  of $\beta(b)$ under $f'$ in $A'$.\<close>

definition (in ses_morphism) snake_a_of_b :: "i \<Rightarrow> i" where
  "snake_a_of_b(b) \<equiv> THE a'. a' \<in> A' \<and> f'`a' = \<beta>`b"

text\<open>The snake connecting map.  For $c \in \ker(\gamma)$, we lift $c$ to some
  $b \in B$ with $g(b)=c$; then $\beta(b) \in \ker(g')$ by commutativity, so
  $\beta(b) = f'(a')$ for a unique $a' \in A'$, and $\delta(c) = [a']$ in
  $\mathrm{coker}(\alpha)$.  We define it as a replacement indexed by
  $(c, b)$-pairs with $g(b) = c$; we prove below that the cokernel class is
  independent of the choice of lift $b$, so this is a well-defined function.\<close>

definition (in ses_morphism) snake_delta :: "i" where
  "snake_delta \<equiv>
    {\<langle>fst(p), QuotientGroupRel(A', PA', \<alpha>``A)``{snake_a_of_b(snd(p))}\<rangle>.
     p \<in> {p \<in> ker_\<gamma> \<times> B. g`(snd(p)) = fst(p)}}"

subsection \<open>The snake connecting homomorphism\<close>

text\<open>The image of $\alpha$ is a normal subgroup of $(A', PA')$.\<close>

lemma (in ses_morphism) alpha_img_normal:
  shows "IsAnormalSubgroup(A', PA', \<alpha>``A)"
proof -
  interpret alph: group_homo A PA A' PA' \<alpha>
    "TheNeutralElement(A, PA)" "\<lambda>x y. PA`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(A,PA)`x"
    "\<lambda>s. Fold(PA,TheNeutralElement(A,PA),s)"
    "\<lambda>m x. Fold(PA,TheNeutralElement(A,PA),{\<langle>k,x\<rangle>. k \<in> m})"
    "TheNeutralElement(A',PA')" "\<lambda>x y. PA'`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(A',PA')`x"
    "\<lambda>s. Fold(PA',TheNeutralElement(A',PA'),s)"
    "\<lambda>m x. Fold(PA',TheNeutralElement(A',PA'),{\<langle>k,x\<rangle>. k \<in> m})"
    using grpA grpA' hom_\<alpha> unfolding group_homo_def by simp
  from Group_ZF_2_4_L6(1)[OF grpA' comm_A' alph.image_is_group]
  show ?thesis by simp
qed

text\<open>The kernel of $\gamma$ is a subgroup of $(C, PC)$.\<close>

lemma (in ses_morphism) ker_gamma_subgroup:
  shows "IsAsubgroup(ker_\<gamma>, PC)"
proof -
  interpret gam: group_homo C PC C' PC' \<gamma>
    "TheNeutralElement(C,PC)" "\<lambda>x y. PC`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(C,PC)`x"
    "\<lambda>s. Fold(PC,TheNeutralElement(C,PC),s)"
    "\<lambda>m x. Fold(PC,TheNeutralElement(C,PC),{\<langle>k,x\<rangle>. k \<in> m})"
    "TheNeutralElement(C',PC')" "\<lambda>x y. PC'`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(C',PC')`x"
    "\<lambda>s. Fold(PC',TheNeutralElement(C',PC'),s)"
    "\<lambda>m x. Fold(PC',TheNeutralElement(C',PC'),{\<langle>k,x\<rangle>. k \<in> m})"
    using grpC grpC' hom_\<gamma> unfolding group_homo_def by simp
  from gam.kernel_is_subgroup show ?thesis by assumption
qed

text\<open>For $b \in B$ with $g(b) \in \ker(\gamma)$, $\beta(b)$ lies in $\mathrm{im}(f')$.\<close>

lemma (in ses_morphism) beta_b_in_im_f':
  assumes bB: "b \<in> B" and gb_ker: "g`b \<in> ker_\<gamma>"
  shows "\<beta>`b \<in> f'``A'"
proof -
  have \<beta>b_B': "\<beta>`b \<in> B'" using \<beta>_fun bB apply_type by simp
  have gb_C: "g`b \<in> C" using g_fun bB apply_type by simp
  have g'_\<beta>b: "g'`(\<beta>`b) = \<gamma>`(g`b)"
  proof -
    have l: "(g' O \<beta>)`b = g'`(\<beta>`b)"
      using comp_fun_apply \<beta>_fun g'_fun bB by simp
    have r: "(\<gamma> O g)`b = \<gamma>`(g`b)"
      using comp_fun_apply g_fun \<gamma>_fun bB by simp
    from comm_right l r show ?thesis by simp
  qed
  have "\<gamma>`(g`b) = TheNeutralElement(C', PC')"
    using func1_1_L15[OF \<gamma>_fun] gb_ker gb_C by auto
  with g'_\<beta>b have "g'`(\<beta>`b) = TheNeutralElement(C', PC')" by simp
  then have "\<beta>`b \<in> g'-``{TheNeutralElement(C', PC')}"
    using func1_1_L15[OF g'_fun] \<beta>b_B' by simp
  with row2_im_eq_ker show ?thesis by simp
qed

text\<open>The preimage $a'$ of $\beta(b)$ under $f'$ exists uniquely when $g(b) \in \ker(\gamma)$.\<close>

lemma (in ses_morphism) snake_a_of_b_exists_unique:
  assumes bB: "b \<in> B" and gb_ker: "g`b \<in> ker_\<gamma>"
  shows "\<exists>!a'. a' \<in> A' \<and> f'`a' = \<beta>`b"
proof -
  from beta_b_in_im_f'[OF bB gb_ker] obtain a'
    where a'A': "a' \<in> A'" and f'a': "f'`a' = \<beta>`b"
    using func_imagedef[OF f'_fun] by auto
  show "\<exists>!a'. a' \<in> A' \<and> f'`a' = \<beta>`b"
  proof (rule ex1I)
    show "a' \<in> A' \<and> f'`a' = \<beta>`b" using a'A' f'a' by simp
  next
    fix a'' assume H: "a'' \<in> A' \<and> f'`a'' = \<beta>`b"
    then have "f'`a'' = f'`a'" using f'a' by simp
    with H a'A' show "a'' = a'" using f'_inj unfolding inj_def by auto
  qed
qed

text\<open>$\mathrm{snake\_a\_of\_b}(b) \in A'$ when $g(b) \in \ker(\gamma)$.\<close>

lemma (in ses_morphism) snake_a_of_b_in_A':
  assumes bB: "b \<in> B" and gb_ker: "g`b \<in> ker_\<gamma>"
  shows "snake_a_of_b(b) \<in> A'"
  unfolding snake_a_of_b_def
  using theI2[OF snake_a_of_b_exists_unique[OF bB gb_ker],
              of "\<lambda>a'. a' \<in> A'"] by blast

text\<open>$f'(\mathrm{snake\_a\_of\_b}(b)) = \beta(b)$ when $g(b) \in \ker(\gamma)$.\<close>

lemma (in ses_morphism) snake_a_of_b_maps:
  assumes bB: "b \<in> B" and gb_ker: "g`b \<in> ker_\<gamma>"
  shows "f'`(snake_a_of_b(b)) = \<beta>`b"
  unfolding snake_a_of_b_def
  using theI2[OF snake_a_of_b_exists_unique[OF bB gb_ker],
              of "\<lambda>a'. f'`a' = \<beta>`b"] by blast

text\<open>The cokernel class of $\mathrm{snake\_a\_of\_b}$ is independent of the choice of lift $b$:
  if $g(b_1) = g(b_2)$ and both lie in $\ker(\gamma)$, then
  $[\mathrm{snake\_a\_of\_b}(b_1)] = [\mathrm{snake\_a\_of\_b}(b_2)]$ in $\mathrm{coker}(\alpha)$.\<close>

lemma (in ses_morphism) snake_class_independent:
  assumes b1B: "b\<^sub>1 \<in> B" and b2B: "b\<^sub>2 \<in> B"
    and gb_eq: "g`b\<^sub>1 = g`b\<^sub>2" and gb_ker: "g`b\<^sub>1 \<in> ker_\<gamma>"
  shows "QuotientGroupRel(A', PA', \<alpha>``A)``{snake_a_of_b(b\<^sub>1)} =
         QuotientGroupRel(A', PA', \<alpha>``A)``{snake_a_of_b(b\<^sub>2)}"
proof -
  let ?R = "QuotientGroupRel(A', PA', \<alpha>``A)"
  have gb2_ker: "g`b\<^sub>2 \<in> ker_\<gamma>" using gb_eq gb_ker by simp
  interpret \<beta>hom: group_homo B PB B' PB' \<beta>
    "TheNeutralElement(B,PB)" "\<lambda>x y. PB`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(B,PB)`x"
    "\<lambda>s. Fold(PB,TheNeutralElement(B,PB),s)"
    "\<lambda>m x. Fold(PB,TheNeutralElement(B,PB),{\<langle>k,x\<rangle>. k \<in> m})"
    "TheNeutralElement(B',PB')" "\<lambda>x y. PB'`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(B',PB')`x"
    "\<lambda>s. Fold(PB',TheNeutralElement(B',PB'),s)"
    "\<lambda>m x. Fold(PB',TheNeutralElement(B',PB'),{\<langle>k,x\<rangle>. k \<in> m})"
    using grpB grpB' hom_\<beta> unfolding group_homo_def by simp
  interpret f'hom: group_homo A' PA' B' PB' f'
    "TheNeutralElement(A',PA')" "\<lambda>x y. PA'`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(A',PA')`x"
    "\<lambda>s. Fold(PA',TheNeutralElement(A',PA'),s)"
    "\<lambda>m x. Fold(PA',TheNeutralElement(A',PA'),{\<langle>k,x\<rangle>. k \<in> m})"
    "TheNeutralElement(B',PB')" "\<lambda>x y. PB'`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(B',PB')`x"
    "\<lambda>s. Fold(PB',TheNeutralElement(B',PB'),s)"
    "\<lambda>m x. Fold(PB',TheNeutralElement(B',PB'),{\<langle>k,x\<rangle>. k \<in> m})"
    using grpA' grpB' row2 unfolding group_homo_def IsAshortExactSequence_def by simp
  interpret ghom: group_homo B PB C PC g
    "TheNeutralElement(B,PB)" "\<lambda>x y. PB`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(B,PB)`x"
    "\<lambda>s. Fold(PB,TheNeutralElement(B,PB),s)"
    "\<lambda>m x. Fold(PB,TheNeutralElement(B,PB),{\<langle>k,x\<rangle>. k \<in> m})"
    "TheNeutralElement(C,PC)" "\<lambda>x y. PC`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(C,PC)`x"
    "\<lambda>s. Fold(PC,TheNeutralElement(C,PC),s)"
    "\<lambda>m x. Fold(PC,TheNeutralElement(C,PC),{\<langle>k,x\<rangle>. k \<in> m})"
    using grpB grpC row1 unfolding group_homo_def IsAshortExactSequence_def by simp
  let ?a\<^sub>1 = "snake_a_of_b(b\<^sub>1)"
  let ?a\<^sub>2 = "snake_a_of_b(b\<^sub>2)"
  have a1_A': "?a\<^sub>1 \<in> A'" using snake_a_of_b_in_A'[OF b1B gb_ker] by simp
  have a2_A': "?a\<^sub>2 \<in> A'" using snake_a_of_b_in_A'[OF b2B gb2_ker] by simp
  have f'a1: "f'`?a\<^sub>1 = \<beta>`b\<^sub>1" using snake_a_of_b_maps[OF b1B gb_ker] by simp
  have f'a2: "f'`?a\<^sub>2 = \<beta>`b\<^sub>2" using snake_a_of_b_maps[OF b2B gb2_ker] by simp
  let ?diff_b = "PB`\<langle>b\<^sub>1, GroupInv(B,PB)`b\<^sub>2\<rangle>"
  have b2_inv_B: "GroupInv(B,PB)`b\<^sub>2 \<in> B" using b2B ghom.origin
      group0.inverse_in_group[of B PB] unfolding group0_def by (simp only:)
  have diff_b_B: "?diff_b \<in> B"
    using b1B b2_inv_B ghom.origin group0.group_op_closed[of B PB] unfolding group0_def by (simp only:) 
  have g_diff_zero: "g`?diff_b = TheNeutralElement(C, PC)"
  proof -
    have "g`?diff_b = PC`\<langle>g`b\<^sub>1, g`(GroupInv(B,PB)`b\<^sub>2)\<rangle>"
      using ghom.f_hom[OF b1B b2_inv_B] by (simp only:)
    also have "\<dots> = PC`\<langle>g`b\<^sub>1, GroupInv(C,PC)`(g`b\<^sub>2)\<rangle>"
      using ghom.f_inv[OF b2B] by (simp only:)
    also have "\<dots> = PC`\<langle>g`b\<^sub>1, GroupInv(C,PC)`(g`b\<^sub>1)\<rangle>"
      using gb_eq by (simp only:)
    also have "\<dots> = TheNeutralElement(C,PC)"
      using ghom.tgt.group0_2_L6[OF apply_type[OF g_fun b1B]] by (simp only:)
    finally show ?thesis .
  qed
  then have diff_b_ker_g: "?diff_b \<in> f``A"
    using func1_1_L15[OF g_fun, of "{TheNeutralElement(C,PC)}"] 
      diff_b_B row1_im_eq_ker by (auto simp only:)
  have im:"f `` A = {f ` x . x ∈ A}" using func_imagedef[OF f_fun] by auto
  then have "?diff_b\<in>{f ` x . x ∈ A}" using diff_b_ker_g by (auto simp only:)
  then obtain aa where aaA: "aa \<in> A" and f_aa: "?diff_b = f`aa"
    by blast 
  have \<alpha>aa_A': "\<alpha>`aa \<in> A'" using \<alpha>_fun aaA apply_type by (auto simp only:)
  interpret \<alpha>hom: group_homo A PA A' PA' \<alpha>
    "TheNeutralElement(A,PA)" "\<lambda>x y. PA`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(A,PA)`x"
    "\<lambda>s. Fold(PA,TheNeutralElement(A,PA),s)"
    "\<lambda>m x. Fold(PA,TheNeutralElement(A,PA),{\<langle>k,x\<rangle>. k \<in> m})"
    "TheNeutralElement(A',PA')" "\<lambda>x y. PA'`\<langle>x,y\<rangle>"
    "\<lambda>x. GroupInv(A',PA')`x"
    "\<lambda>s. Fold(PA',TheNeutralElement(A',PA'),s)"
    "\<lambda>m x. Fold(PA',TheNeutralElement(A',PA'),{\<langle>k,x\<rangle>. k \<in> m})"
    using grpA grpA' hom_\<alpha> unfolding group_homo_def by simp
  have \<beta>_diff_b: "\<beta>`?diff_b = PB'`\<langle>\<beta>`b\<^sub>1, GroupInv(B',PB')`(\<beta>`b\<^sub>2)\<rangle>"
  proof -
    have "\<beta>`?diff_b = PB'`\<langle>\<beta>`b\<^sub>1, \<beta>`(GroupInv(B,PB)`b\<^sub>2)\<rangle>"
      using \<beta>hom.f_hom[OF b1B b2_inv_B] by (auto simp only:)
    also have "\<dots> = PB'`\<langle>\<beta>`b\<^sub>1, GroupInv(B',PB')`(\<beta>`b\<^sub>2)\<rangle>"
      using \<beta>hom.f_inv[OF b2B] by (auto simp only:)
    finally show ?thesis .
  qed
  have f'_\<alpha>aa: "f'`(\<alpha>`aa) = \<beta>`?diff_b"
  proof -
    have "(f' O \<alpha>)`aa = (\<beta> O f)`aa" using comm_left by simp
    then have "f'`(\<alpha>`aa) = \<beta>`(f`aa)"
      using comp_fun_apply \<alpha>_fun f'_fun aaA comp_fun_apply f_fun \<beta>_fun aaA by simp
    with f_aa show ?thesis by (auto simp only:)
  qed
  have diff_a1_a2: "PA'`\<langle>?a\<^sub>1, GroupInv(A',PA')`?a\<^sub>2\<rangle> = \<alpha>`aa"
  proof -
    have a2_inv_A': "GroupInv(A',PA')`?a\<^sub>2 \<in> A'"
      using a2_A' f'hom.org.inverse_in_group by (auto simp only:)
    have f'_sum: "f'`(PA'`\<langle>?a\<^sub>1, GroupInv(A',PA')`?a\<^sub>2\<rangle>) =
                  PB'`\<langle>f'`?a\<^sub>1, GroupInv(B',PB')`(f'`?a\<^sub>2)\<rangle>"
    proof -
      have "f'`(PA'`\<langle>?a\<^sub>1, GroupInv(A',PA')`?a\<^sub>2\<rangle>) =
            PB'`\<langle>f'`?a\<^sub>1, f'`(GroupInv(A',PA')`?a\<^sub>2)\<rangle>"
        using f'hom.f_hom[OF a1_A' a2_inv_A'] by (auto simp only:)
      also have "\<dots> = PB'`\<langle>f'`?a\<^sub>1, GroupInv(B',PB')`(f'`?a\<^sub>2)\<rangle>"
        using f'hom.f_inv[OF a2_A'] by (auto simp only:)
      finally show ?thesis .
    qed
    have "PB'`\<langle>f'`?a\<^sub>1, GroupInv(B',PB')`(f'`?a\<^sub>2)\<rangle> = \<beta>`?diff_b"
      using f'a1 f'a2 \<beta>_diff_b by (auto simp only:)
    with f'_sum have "f'`(PA'`\<langle>?a\<^sub>1, GroupInv(A',PA')`?a\<^sub>2\<rangle>) = f'`(\<alpha>`aa)"
      using f'_\<alpha>aa by (auto simp only:)
    moreover have "PA'`\<langle>?a\<^sub>1, GroupInv(A',PA')`?a\<^sub>2\<rangle> \<in> A'"
      using a1_A' a2_inv_A' f'hom.org.group_op_closed by (auto simp only:)
    ultimately show ?thesis using f'_inj \<alpha>aa_A' unfolding inj_def by (auto simp only:)
  qed
  have pair_in_R: "\<langle>?a\<^sub>1, ?a\<^sub>2\<rangle> \<in> ?R"
  proof -
    have A:"\<langle>?a\<^sub>1, ?a\<^sub>2\<rangle> \<in> A' \<times> A'" using a1_A' a2_A' by simp
    from diff_a1_a2 have "PA'`\<langle>?a\<^sub>1, GroupInv(A',PA')`?a\<^sub>2\<rangle> = \<alpha>`aa" by (auto simp only:)
    then have E:"PA'`\<langle>snake_a_of_b(b⇩1), GroupInv(A',PA')`snake_a_of_b(b⇩2)\<rangle> \<in> {\<alpha>`x. x\<in>A}"
      using aaA by (auto simp only:)
    have "\<alpha>``A = {\<alpha>`x. x\<in>A}" using func_imagedef[OF \<alpha>_fun, of A] by auto
    with E have "PA'`\<langle>snake_a_of_b(b⇩1), GroupInv(A',PA')`snake_a_of_b(b⇩2)\<rangle> \<in> \<alpha>``A"
      by (auto simp only:)
    with A show ?thesis unfolding QuotientGroupRel_def by (auto simp only: split)
  qed
  have equiv_R: "equiv(A', ?R)"
    using alpha_img_normal grpA'
    using group0.Group_ZF_2_4_L3
    unfolding group0_def IsAnormalSubgroup_def by blast
  from equiv_class_eq[OF equiv_R pair_in_R] a1_A'
  show ?thesis by simp
qed

text\<open>$\mathrm{snake\_delta}$ is a function from $\ker(\gamma)$ to $\mathrm{coker}(\alpha)$.\<close>

lemma (in ses_morphism) snake_delta_is_fun:
  shows "snake_delta : ker_\<gamma> \<rightarrow> coker_\<alpha>"
proof -
  let ?R = "QuotientGroupRel(A', PA', \<alpha>``A)"
  have ker_sub_C: "ker_\<gamma> \<subseteq> C"
    using ker_gamma_subgroup grpC group0.group0_3_L2
    unfolding group0_def IsAsubgroup_def by auto
  have norm: "IsAnormalSubgroup(A', PA', \<alpha>``A)" using alpha_img_normal by simp
  have equiv_R: "equiv(A', ?R)"
    using norm grpA' group0.Group_ZF_2_4_L3
    unfolding group0_def IsAnormalSubgroup_def by auto
  have sub_pow: "snake_delta \<in> Pow(ker_\<gamma> \<times> coker_\<alpha>)"
  proof (safe)
    fix p assume "p \<in> snake_delta"
    then obtain c b where cC: "c \<in> ker_\<gamma>" and bB: "b \<in> B"
      and gbC: "g`b = c" and p_eq: "p = \<langle>c, ?R``{snake_a_of_b(b)}\<rangle>"
      unfolding snake_delta_def by auto
    from cC gbC have gb_ker: "g`b \<in> ker_\<gamma>" by simp
    from snake_a_of_b_in_A'[OF bB gb_ker] equiv_R
    have "?R``{snake_a_of_b(b)} \<in> coker_\<alpha>"
      unfolding quotient_def by auto
    with p_eq cC show "p \<in> ker_\<gamma> \<times> coker_\<alpha>" by auto
  qed
  have dom_sub: "ker_\<gamma> \<subseteq> domain(snake_delta)"
  proof
    fix c assume cC: "c \<in> ker_\<gamma>"
    then have cC': "c \<in> C" using ker_sub_C by auto
    from cC' g_surj obtain b where bB: "b \<in> B" and gbc: "g`b = c"
      using func_imagedef[OF g_fun] by auto
    from cC gbc have gb_ker: "g`b \<in> ker_\<gamma>" by simp
    from snake_a_of_b_in_A'[OF bB gb_ker]
    have "\<langle>c, ?R``{snake_a_of_b(b)}\<rangle> \<in> snake_delta"
      unfolding snake_delta_def using cC bB gbc by auto
    then show "c \<in> domain(snake_delta)" unfolding domain_def by auto
  qed
  have sv: "\<forall>A y t. \<langle>A,y\<rangle> \<in> snake_delta \<longrightarrow> \<langle>A,t\<rangle> \<in> snake_delta \<longrightarrow> y = t"
  proof (intro allI impI)
    fix c y t
    assume Ay: "\<langle>c,y\<rangle> \<in> snake_delta" and At: "\<langle>c,t\<rangle> \<in> snake_delta"
    from Ay obtain b\<^sub>1 where b1B: "b\<^sub>1 \<in> B" and gb1: "g`b\<^sub>1 = c"
      and cK1: "c \<in> ker_\<gamma>"
      and y_eq: "y = ?R``{snake_a_of_b(b\<^sub>1)}"
      unfolding snake_delta_def by auto
    from At obtain b\<^sub>2 where b2B: "b\<^sub>2 \<in> B" and gb2: "g`b\<^sub>2 = c"
      and t_eq: "t = ?R``{snake_a_of_b(b\<^sub>2)}"
      unfolding snake_delta_def by auto
    from gb1 gb2 have gb_eq: "g`b\<^sub>1 = g`b\<^sub>2" by simp
    from gb1 cK1 have gb1_ker: "g`b\<^sub>1 \<in> ker_\<gamma>" by simp
    from snake_class_independent[OF b1B b2B gb_eq gb1_ker]
    show "y = t" using y_eq t_eq by simp
  qed
  from sub_pow dom_sub sv show ?thesis unfolding Pi_def function_def by auto
qed

text\<open>The snake connecting map is a group homomorphism from $\ker(\gamma)$ to $\mathrm{coker}(\alpha)$.\<close>

theorem (in ses_morphism) snake_delta_is_hom:
  shows "Homomor(snake_delta, ker_\<gamma>, restrict(PC, ker_\<gamma> \<times> ker_\<gamma>), coker_\<alpha>, cokerOp_\<alpha>)"
proof -
  let ?R = "QuotientGroupRel(A', PA', \<alpha>``A)"
  have norm: "IsAnormalSubgroup(A', PA', \<alpha>``A)" using alpha_img_normal by simp
  have equiv_R: "equiv(A', ?R)"
    using norm grpA' group0.Group_ZF_2_4_L3
    unfolding group0_def IsAnormalSubgroup_def by auto
  have cong_R: "Congruent2(?R, PA')"
    using Group_ZF_2_4_L5A[OF grpA' norm] by simp
  have ker_sub_C: "ker_\<gamma> \<subseteq> C"
    using ker_gamma_subgroup grpC group0.group0_3_L2
    unfolding group0_def IsAsubgroup_def by auto
  have delta_fun: "snake_delta : ker_\<gamma> \<rightarrow> coker_\<alpha>"
    using snake_delta_is_fun by simp
  have morphism: "IsMorphism(ker_\<gamma>, restrict(PC, ker_\<gamma> \<times> ker_\<gamma>), cokerOp_\<alpha>, snake_delta)"
    unfolding IsMorphism_def
  proof (intro ballI)
    fix c\<^sub>1 c\<^sub>2 assume c1K: "c\<^sub>1 \<in> ker_\<gamma>" and c2K: "c\<^sub>2 \<in> ker_\<gamma>"
    show "snake_delta`(restrict(PC, ker_\<gamma> \<times> ker_\<gamma>)`\<langle>c\<^sub>1, c\<^sub>2\<rangle>) =
          cokerOp_\<alpha>`\<langle>snake_delta`c\<^sub>1, snake_delta`c\<^sub>2\<rangle>"
    proof -
      have c1C: "c\<^sub>1 \<in> C" using c1K ker_sub_C by auto
      have c2C: "c\<^sub>2 \<in> C" using c2K ker_sub_C by auto
      have sum_ker: "PC`\<langle>c\<^sub>1, c\<^sub>2\<rangle> \<in> ker_\<gamma>"
        using ker_gamma_subgroup c1K c2K
        using group0.group_op_closed[of ker_\<gamma> "restrict(PC,ker_\<gamma>\<times>ker_\<gamma>)"] restrict[of PC "ker_\<gamma>\<times>ker_\<gamma>"]
        unfolding group0_def IsAsubgroup_def by auto
      have res_eq: "restrict(PC, ker_\<gamma> \<times> ker_\<gamma>)`\<langle>c\<^sub>1, c\<^sub>2\<rangle> = PC`\<langle>c\<^sub>1, c\<^sub>2\<rangle>"
        using restrict c1K c2K by simp
      from c1C g_surj obtain b\<^sub>1 where b1B: "b\<^sub>1 \<in> B" and gb1: "g`b\<^sub>1 = c\<^sub>1"
        using func_imagedef[OF g_fun] by auto
      from c2C g_surj obtain b\<^sub>2 where b2B: "b\<^sub>2 \<in> B" and gb2: "g`b\<^sub>2 = c\<^sub>2"
        using func_imagedef[OF g_fun] by auto
      from gb1 c1K have gb1_ker: "g`b\<^sub>1 \<in> ker_\<gamma>" by simp
      from gb2 c2K have gb2_ker: "g`b\<^sub>2 \<in> ker_\<gamma>" by simp
      let ?a\<^sub>1 = "snake_a_of_b(b\<^sub>1)"
      let ?a\<^sub>2 = "snake_a_of_b(b\<^sub>2)"
      have a1_A': "?a\<^sub>1 \<in> A'" using snake_a_of_b_in_A'[OF b1B gb1_ker] by simp
      have a2_A': "?a\<^sub>2 \<in> A'" using snake_a_of_b_in_A'[OF b2B gb2_ker] by simp
      have f'a1: "f'`?a\<^sub>1 = \<beta>`b\<^sub>1" using snake_a_of_b_maps[OF b1B gb1_ker] by simp
      have f'a2: "f'`?a\<^sub>2 = \<beta>`b\<^sub>2" using snake_a_of_b_maps[OF b2B gb2_ker] by simp
      interpret ghom: group_homo B PB C PC g
        "TheNeutralElement(B,PB)" "\<lambda>x y. PB`\<langle>x,y\<rangle>"
        "\<lambda>x. GroupInv(B,PB)`x"
        "\<lambda>s. Fold(PB,TheNeutralElement(B,PB),s)"
        "\<lambda>m x. Fold(PB,TheNeutralElement(B,PB),{\<langle>k,x\<rangle>. k \<in> m})"
        "TheNeutralElement(C,PC)" "\<lambda>x y. PC`\<langle>x,y\<rangle>"
        "\<lambda>x. GroupInv(C,PC)`x"
        "\<lambda>s. Fold(PC,TheNeutralElement(C,PC),s)"
        "\<lambda>m x. Fold(PC,TheNeutralElement(C,PC),{\<langle>k,x\<rangle>. k \<in> m})"
        using grpB grpC row1 unfolding group_homo_def IsAshortExactSequence_def by simp
      interpret \<beta>hom: group_homo B PB B' PB' \<beta>
        "TheNeutralElement(B,PB)" "\<lambda>x y. PB`\<langle>x,y\<rangle>"
        "\<lambda>x. GroupInv(B,PB)`x"
        "\<lambda>s. Fold(PB,TheNeutralElement(B,PB),s)"
        "\<lambda>m x. Fold(PB,TheNeutralElement(B,PB),{\<langle>k,x\<rangle>. k \<in> m})"
        "TheNeutralElement(B',PB')" "\<lambda>x y. PB'`\<langle>x,y\<rangle>"
        "\<lambda>x. GroupInv(B',PB')`x"
        "\<lambda>s. Fold(PB',TheNeutralElement(B',PB'),s)"
        "\<lambda>m x. Fold(PB',TheNeutralElement(B',PB'),{\<langle>k,x\<rangle>. k \<in> m})"
        using grpB grpB' hom_\<beta> unfolding group_homo_def by simp
      interpret f'hom: group_homo A' PA' B' PB' f'
        "TheNeutralElement(A',PA')" "\<lambda>x y. PA'`\<langle>x,y\<rangle>"
        "\<lambda>x. GroupInv(A',PA')`x"
        "\<lambda>s. Fold(PA',TheNeutralElement(A',PA'),s)"
        "\<lambda>m x. Fold(PA',TheNeutralElement(A',PA'),{\<langle>k,x\<rangle>. k \<in> m})"
        "TheNeutralElement(B',PB')" "\<lambda>x y. PB'`\<langle>x,y\<rangle>"
        "\<lambda>x. GroupInv(B',PB')`x"
        "\<lambda>s. Fold(PB',TheNeutralElement(B',PB'),s)"
        "\<lambda>m x. Fold(PB',TheNeutralElement(B',PB'),{\<langle>k,x\<rangle>. k \<in> m})"
        using grpA' grpB' row2 unfolding group_homo_def IsAshortExactSequence_def by simp
      let ?b\<^sub>12 = "PB`\<langle>b\<^sub>1, b\<^sub>2\<rangle>"
      have b12B: "?b\<^sub>12 \<in> B" using b1B b2B ghom.org.group_op_closed by (simp only:)
      have g_b12: "g`?b\<^sub>12 = PC`\<langle>c\<^sub>1, c\<^sub>2\<rangle>"
        using ghom.f_hom[OF b1B b2B] gb1 gb2 by (simp only:)
      have gb12_ker: "g`?b\<^sub>12 \<in> ker_\<gamma>" using g_b12 sum_ker by (simp only:)
      let ?a\<^sub>12 = "snake_a_of_b(?b\<^sub>12)"
      have a12_A': "?a\<^sub>12 \<in> A'" using snake_a_of_b_in_A'[OF b12B gb12_ker] by (simp only:)
      have f'a12: "f'`?a\<^sub>12 = \<beta>`?b\<^sub>12" using snake_a_of_b_maps[OF b12B gb12_ker] by (simp only:)
      have beta_add: "\<beta>`?b\<^sub>12 = PB'`\<langle>\<beta>`b\<^sub>1, \<beta>`b\<^sub>2\<rangle>"
        using \<beta>hom.f_hom[OF b1B b2B] by (simp only:)
      have f'_a12_eq: "f'`?a\<^sub>12 = f'`(PA'`\<langle>?a\<^sub>1, ?a\<^sub>2\<rangle>)"
      proof -
        have "f'`(PA'`\<langle>?a\<^sub>1, ?a\<^sub>2\<rangle>) = PB'`\<langle>f'`?a\<^sub>1, f'`?a\<^sub>2\<rangle>"
          using f'hom.f_hom[OF a1_A' a2_A'] by (simp only:)
        also have "\<dots> = PB'`\<langle>\<beta>`b\<^sub>1, \<beta>`b\<^sub>2\<rangle>"
          using f'a1 f'a2 by (simp only:)
        also have "\<dots> = \<beta>`?b\<^sub>12"
          using beta_add by (simp only:)
        also have "\<dots> = f'`?a\<^sub>12"
          using f'a12 by (simp only:)
        finally show ?thesis by (simp only:)
      qed
      have a_sum_A': "PA'`\<langle>?a\<^sub>1, ?a\<^sub>2\<rangle> \<in> A'"
        using a1_A' a2_A' f'hom.org.group_op_closed by (simp only:)
      have a12_eq_sum: "?a\<^sub>12 = PA'`\<langle>?a\<^sub>1, ?a\<^sub>2\<rangle>"
        using f'_inj a12_A' a_sum_A' f'_a12_eq unfolding inj_def by (auto simp only:)
      have pair1: "\<langle>c\<^sub>1, ?R``{?a\<^sub>1}\<rangle> \<in> snake_delta"
        unfolding snake_delta_def using c1K b1B gb1 by auto
      have pair2: "\<langle>c\<^sub>2, ?R``{?a\<^sub>2}\<rangle> \<in> snake_delta"
        unfolding snake_delta_def using c2K b2B gb2 by auto
      have "\<langle>PC ` ⟨c⇩1, c⇩2⟩,PB ` ⟨b⇩1, b⇩2⟩\<rangle>\<in> {p ∈ ker_γ × B .
           g ` snd(p) = fst(p)}" using sum_ker b12B g_b12 by (auto simp only:fst_conv snd_conv)
      then have "⟨fst(\<langle>PC ` ⟨c⇩1, c⇩2⟩,PB ` ⟨b⇩1, b⇩2⟩\<rangle>),
      QuotientGroupRel(A', PA', α `` A) ``
      {snake_a_of_b(snd(\<langle>PC ` ⟨c⇩1, c⇩2⟩,PB ` ⟨b⇩1, b⇩2⟩\<rangle>))}⟩ \<in> snake_delta"
        unfolding snake_delta_def by (auto simp only:)
      then have pair12:"\<langle>PC`\<langle>c⇩1, c⇩2⟩, QuotientGroupRel(A', PA', α `` A) ``
      {snake_a_of_b(PB ` ⟨b⇩1, b⇩2⟩)}⟩ \<in> snake_delta" by (simp only:fst_conv snd_conv)
      from pair1 delta_fun have step1: "snake_delta`c\<^sub>1 = ?R``{?a\<^sub>1}"
        using apply_equality by simp
      from pair2 delta_fun have step2: "snake_delta`c\<^sub>2 = ?R``{?a\<^sub>2}"
        using apply_equality by simp
      from pair12 delta_fun have step12:
        "snake_delta`(PC`\<langle>c\<^sub>1,c\<^sub>2\<rangle>) = ?R``{?a\<^sub>12}"
        using apply_equality by (simp only:)
      have coker_op: "cokerOp_\<alpha>`\<langle>?R``{?a\<^sub>1}, ?R``{?a\<^sub>2}\<rangle> = ?R``{PA'`\<langle>?a\<^sub>1,?a\<^sub>2\<rangle>}"
        using EquivClass_1_L10[OF equiv_R cong_R a1_A' a2_A']
        unfolding QuotientGroupOp_def by (simp only:)
      from step12 a12_eq_sum coker_op step1 step2 res_eq
      show "snake_delta`(restrict(PC, ker_\<gamma> \<times> ker_\<gamma>)`\<langle>c\<^sub>1, c\<^sub>2\<rangle>) =
            cokerOp_\<alpha>`\<langle>snake_delta`c\<^sub>1, snake_delta`c\<^sub>2\<rangle>"
        by  (simp only:)
    qed
  qed
  from delta_fun morphism show ?thesis unfolding Homomor_def by simp
qed


end
