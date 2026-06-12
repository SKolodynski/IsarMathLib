(*
    This file is a part of IsarMathLib -
    a library of formalized mathematics for Isabelle/Isar.

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

section \<open>Rings - Direct Product and Chinese Remainder Theorem\<close>

theory Ring_ZF_5 imports Ring_ZF_4 Ring_ZF_3 DirectProduct_ZF

begin

text\<open>This section develops the direct product of two rings and proves the
  Chinese Remainder Theorem: for comaximal ideals $I$ and $J$ in a commutative
  ring $R$ (meaning $I + J = R$), there is a ring isomorphism
  $R/(I \cap J) \cong R/I \times R/J$.\<close>

subsection\<open>Direct product of rings\<close>

text\<open>The direct product of two rings is a ring with componentwise operations.\<close>

lemma direct_product_ring:
  assumes ringR: "IsAring(R,A,M)" and ringS: "IsAring(S,U,V)"
  shows "IsAring(R\<times>S, DirectProduct(A,U,R,S), DirectProduct(M,V,R,S))"
proof -
  let ?DA = "DirectProduct(A,U,R,S)"
  let ?DM = "DirectProduct(M,V,R,S)"
  interpret r1: ring0 R A M "\<lambda> x y. A`\<langle>x,y\<rangle>" "\<lambda> x. GroupInv(R,A)`x"
    "\<lambda>x y. A`\<langle>x,GroupInv(R,A)`y\<rangle>" "\<lambda>x y. M`\<langle>x,y\<rangle>" "TheNeutralElement(R,A)"
    "TheNeutralElement(R,M)" "A`\<langle>TheNeutralElement(R,M),TheNeutralElement(R,M)\<rangle>"
    "\<lambda>x. M`\<langle>x,x\<rangle>" "\<lambda>s. Fold(A,TheNeutralElement(R,A),s)" "\<lambda>n x. Fold(A,TheNeutralElement(R,A),{\<langle>k,x\<rangle>. k\<in>n})"
    "\<lambda>s. Fold(M,TheNeutralElement(R,M),s)" "\<lambda>n x. Fold(M,TheNeutralElement(R,M),{\<langle>k,x\<rangle>. k\<in>n})"
   using ringR unfolding ring0_def by auto
  interpret r2: ring0 S U V "\<lambda> x y. U`\<langle>x,y\<rangle>" "\<lambda> x. GroupInv(S,U)`x"
    "\<lambda>x y. U`\<langle>x,GroupInv(S,U)`y\<rangle>" "\<lambda>x y. V`\<langle>x,y\<rangle>" "TheNeutralElement(S,U)"
    "TheNeutralElement(S,V)" "U`\<langle>TheNeutralElement(S,V),TheNeutralElement(S,V)\<rangle>"
    "\<lambda>x. V`\<langle>x,x\<rangle>" "\<lambda>s. Fold(U,TheNeutralElement(S,U),s)" "\<lambda>n x. Fold(U,TheNeutralElement(S,U),{\<langle>k,x\<rangle>. k\<in>n})"
    "\<lambda>s. Fold(V,TheNeutralElement(S,V),s)" "\<lambda>n x. Fold(V,TheNeutralElement(S,V),{\<langle>k,x\<rangle>. k\<in>n})"
    using ringS unfolding ring0_def by auto
  have A_fun: "A : R\<times>R\<rightarrow>R" using r1.add_group.group_oper_fun by simp
  have U_fun: "U : S\<times>S\<rightarrow>S" using r2.add_group.group_oper_fun by simp
  have M_fun: "M : R\<times>R\<rightarrow>R" using r1.mult_monoid.monoid_oper_fun by simp
  have V_fun: "V : S\<times>S\<rightarrow>S" using r2.mult_monoid.monoid_oper_fun by simp
  interpret dpA: direct0 A U R S "DirectProduct(A,U,R,S)" using A_fun U_fun unfolding direct0_def by auto
  interpret dpM: direct0 M V R S "DirectProduct(M,V,R,S)" using M_fun V_fun unfolding direct0_def by auto
  have DA_fun: "?DA : (R\<times>S)\<times>(R\<times>S)\<rightarrow>R\<times>S" using dpA.DirectProduct_ZF_1_L1 .
  have DM_fun: "?DM : (R\<times>S)\<times>(R\<times>S)\<rightarrow>R\<times>S" using dpM.DirectProduct_ZF_1_L1 .
  have DA_val: "\<forall>x\<in>R\<times>S. \<forall>y\<in>R\<times>S.
    ?DA`\<langle>x,y\<rangle> = \<langle>A`\<langle>fst(x),fst(y)\<rangle>, U`\<langle>snd(x),snd(y)\<rangle>\<rangle>"
    using dpA.DirectProduct_ZF_1_L2 .
  have DM_val: "\<forall>x\<in>R\<times>S. \<forall>y\<in>R\<times>S.
    ?DM`\<langle>x,y\<rangle> = \<langle>M`\<langle>fst(x),fst(y)\<rangle>, V`\<langle>snd(x),snd(y)\<rangle>\<rangle>"
    using dpM.DirectProduct_ZF_1_L2 .
  have A_assoc: "A {is associative on} R"
    using r1.add_group.groupAssum unfolding IsAgroup_def IsAmonoid_def by blast
  have U_assoc: "U {is associative on} S"
    using r2.add_group.groupAssum unfolding IsAgroup_def IsAmonoid_def by blast
  have M_assoc: "M {is associative on} R"
    using r1.mult_monoid.monoidAssum unfolding IsAmonoid_def by blast
  have V_assoc: "V {is associative on} S"
    using r2.mult_monoid.monoidAssum unfolding IsAmonoid_def by blast
  have DA_assoc: "?DA {is associative on} R\<times>S"
    using dpA.DirectProduct_ZF_2_L2[OF A_assoc U_assoc] by blast
  have DM_assoc: "?DM {is associative on} R\<times>S"
    using dpM.DirectProduct_ZF_2_L2[OF M_assoc V_assoc] by blast
  let ?zRS = "\<langle>TheNeutralElement(R,A), TheNeutralElement(S,U)\<rangle>"
  let ?oRS = "\<langle>TheNeutralElement(R,M), TheNeutralElement(S,V)\<rangle>"
  have fstz:"fst(?zRS) = TheNeutralElement(R,A)" using fst_conv by blast
  have sndz:"snd(?zRS) = TheNeutralElement(S,U)" using snd_conv by blast
  have fsto:"fst(?oRS) = TheNeutralElement(R,M)" using fst_conv by blast
  have sndo:"snd(?oRS) = TheNeutralElement(S,V)" using snd_conv by blast
  have zRS_in: "?zRS \<in> R\<times>S"
    using r1.Ring_ZF_1_L2(1) r2.Ring_ZF_1_L2(1) by blast
  have oRS_in: "?oRS \<in> R\<times>S"
    using r1.Ring_ZF_1_L2(2) r2.Ring_ZF_1_L2(2) by blast
  have DA_neut_prop: "\<forall>p\<in>R\<times>S.
    ?DA`\<langle>?zRS,p\<rangle> = p \<and> ?DA`\<langle>p,?zRS\<rangle> = p"
  proof
    fix p assume p: "p \<in> R\<times>S"
    have pr: "fst(p) \<in> R" and ps: "snd(p) \<in> S" using p by auto
    have "?DA`\<langle>?zRS,p\<rangle> =
      \<langle>A`\<langle>fst(?zRS),fst(p)\<rangle>, U`\<langle>snd(?zRS),snd(p)\<rangle>\<rangle>"
      using DA_val zRS_in p by blast
    also have "\<dots> = \<langle>A`\<langle>TheNeutralElement(R,A),fst(p)\<rangle>,U`\<langle>TheNeutralElement(S,U),snd(p)\<rangle>\<rangle>"
      using fstz sndz by (simp only:)
    also have "\<dots> = \<langle>fst(p), snd(p)\<rangle>"
      using r1.Ring_ZF_1_L3(4)[OF pr] r2.Ring_ZF_1_L3(4)[OF ps] by (simp only:)
    also have "\<dots> = p" using p by auto
    finally have left: "?DA`\<langle>?zRS,p\<rangle> = p" .
    have "?DA`\<langle>p,?zRS\<rangle> =
      \<langle>A`\<langle>fst(p),fst(?zRS)\<rangle>, U`\<langle>snd(p),snd(?zRS)\<rangle>\<rangle>"
      using DA_val zRS_in p by blast
    also have "\<dots> = \<langle>A`\<langle>fst(p),TheNeutralElement(R,A)\<rangle>,U`\<langle>snd(p),TheNeutralElement(S,U)\<rangle>\<rangle>" 
      using sndz fstz by (simp only:)
    also have "\<dots> = \<langle>fst(p), snd(p)\<rangle>"
      using r1.Ring_ZF_1_L3(3)[OF pr] r2.Ring_ZF_1_L3(3)[OF ps] by (simp only:)
    also have "\<dots> = p" using p by auto
    finally have right: "?DA`\<langle>p,?zRS\<rangle> = p" .
    from left right show "?DA`\<langle>?zRS,p\<rangle> = p \<and> ?DA`\<langle>p,?zRS\<rangle> = p" by blast
  qed
  have DM_neut_prop: "\<forall>p\<in>R\<times>S.
    ?DM`\<langle>?oRS,p\<rangle> = p \<and> ?DM`\<langle>p,?oRS\<rangle> = p"
  proof
    fix p assume p: "p \<in> R\<times>S"
    have pr: "fst(p) \<in> R" and ps: "snd(p) \<in> S" using p by auto
    have "?DM`\<langle>p,?oRS\<rangle> =
      \<langle>M`\<langle>fst(p),fst(?oRS)\<rangle>, V`\<langle>snd(p),snd(?oRS)\<rangle>\<rangle>"
      using DM_val oRS_in p by blast
    also have "\<dots> = \<langle>M`\<langle>fst(p),TheNeutralElement(R,M)\<rangle>,V`\<langle>snd(p),TheNeutralElement(S,V)\<rangle>\<rangle>"
      by (simp only:fsto sndo)
    also have "\<dots> = \<langle>fst(p), snd(p)\<rangle>"
      using r1.Ring_ZF_1_L3(5)[OF pr] r2.Ring_ZF_1_L3(5)[OF ps] by (simp only:)
    also have "\<dots> = p" using p by auto
    finally have left: "?DM`\<langle>p,?oRS\<rangle> = p" .
    have "?DM`\<langle>?oRS,p\<rangle> =
      \<langle>M`\<langle>TheNeutralElement(R,M),fst(p)\<rangle>, V`\<langle>TheNeutralElement(S,V),snd(p)\<rangle>\<rangle>"
      using DM_val p oRS_in by (simp only: fsto sndo)
    also have "\<dots> = \<langle>fst(p), snd(p)\<rangle>"
      using r1.Ring_ZF_1_L3(6)[OF pr] r2.Ring_ZF_1_L3(6)[OF ps] by (simp only:)
    also have "\<dots> = p" using p by auto
    finally have right: "?DM`\<langle>?oRS,p\<rangle> = p" .
    from left right show "?DM`\<langle>?oRS,p\<rangle> = p \<and> ?DM`\<langle>p,?oRS\<rangle> = p" by (simp only:)
  qed
  have DA_monoid: "IsAmonoid(R\<times>S, ?DA)"
    using DA_assoc zRS_in DA_neut_prop unfolding IsAmonoid_def by blast
  have DM_monoid: "IsAmonoid(R\<times>S, ?DM)"
    using DM_assoc oRS_in DM_neut_prop unfolding IsAmonoid_def by blast
  have neut_DA: "TheNeutralElement(R\<times>S,?DA) = ?zRS"
  proof -
    interpret DA_mon: monoid0 "R\<times>S" ?DA "\<lambda>x y.  DirectProduct(A, U, R, S) `\<langle>x,y\<rangle>" 
      using DA_monoid unfolding monoid0_def by blast
    show ?thesis apply (rule DA_mon.group0_1_L4[of ?zRS,THEN sym])
      apply (simp only:zRS_in) apply safe
      by (simp only:DA_neut_prop)+
  qed
  have DA_inv: "\<forall>p\<in>R\<times>S. \<exists>b\<in>R\<times>S. ?DA`\<langle>p,b\<rangle> = TheNeutralElement(R\<times>S,?DA)"
  proof
    fix p assume p: "p \<in> R\<times>S"
    have pr: "fst(p) \<in> R" and ps: "snd(p) \<in> S" using p by auto
    let ?b = "\<langle>GroupInv(R,A)`fst(p), GroupInv(S,U)`snd(p)\<rangle>"
    have b_in: "?b \<in> R\<times>S"
      using r1.add_group.inverse_in_group[OF pr]
            r2.add_group.inverse_in_group[OF ps] by blast
    have "?DA`\<langle>p,?b\<rangle> =
      \<langle>A`\<langle>fst(p), GroupInv(R,A)`fst(p)\<rangle>, U`\<langle>snd(p), GroupInv(S,U)`snd(p)\<rangle>\<rangle>"
      using DA_val p b_in by (simp only:fst_conv snd_conv)
    also have "\<dots> = ?zRS"
      using r1.add_group.group0_2_L6[OF pr] r2.add_group.group0_2_L6[OF ps] by (simp only:)
    also have "\<dots> = TheNeutralElement(R\<times>S,?DA)" using neut_DA by (simp only:)
    finally have "?DA`\<langle>p,?b\<rangle> = TheNeutralElement(R\<times>S,?DA)" .
    with b_in show "\<exists>b\<in>R\<times>S. ?DA`\<langle>p,b\<rangle> = TheNeutralElement(R\<times>S,?DA)" by blast
  qed
  have DA_group: "IsAgroup(R\<times>S, ?DA)"
    using definition_of_group DA_monoid DA_inv by blast
  have DA_comm: "?DA {is commutative on} R\<times>S"
  proof -
    from r1.ringAssum have "A {is commutative on} R" unfolding IsAring_def by auto
    from r2.ringAssum have "U {is commutative on} S" unfolding IsAring_def by auto
    with \<open>A {is commutative on} R\<close> show ?thesis
      using dpA.DirectProduct_ZF_2_L1 by blast
  qed
  have distrib: "IsDistributive(R\<times>S, ?DA, ?DM)"
  proof -
    from r1.ringAssum have distR: "IsDistributive(R,A,M)" unfolding IsAring_def by auto
    from r2.ringAssum have distS: "IsDistributive(S,U,V)" unfolding IsAring_def by auto
    {
      fix x y z assume xyz: "x\<in>R\<times>S" "y\<in>R\<times>S" "z\<in>R\<times>S"
      have xr: "fst(x)\<in>R" and xs: "snd(x)\<in>S" using xyz(1) by auto
      have yr: "fst(y)\<in>R" and ys: "snd(y)\<in>S" using xyz(2) by auto
      have zr: "fst(z)\<in>R" and zs: "snd(z)\<in>S" using xyz(3) by auto
      have yz:"?DA`\<langle>y,z\<rangle>\<in>R\<times>S" using DA_group group0.group_op_closed
        unfolding group0_def by (simp only:xyz(2,3))
      have "M`\<langle>fst(x),fst(y)\<rangle>\<in>R" "V`\<langle>snd(x),snd(y)\<rangle>\<in>S" "M`\<langle>fst(x),fst(z)\<rangle>\<in>R"
        "V`\<langle>snd(x),snd(z)\<rangle>\<in>S" using xr xs yr ys zr zs r1.Ring_ZF_1_L4(3) r2.Ring_ZF_1_L4(3)
        by fast+
      then have els:"\<langle>M`\<langle>fst(x),fst(y)\<rangle>,V`\<langle>snd(x),snd(y)\<rangle>\<rangle>\<in>(R\<times>S)"  "\<langle>M`\<langle>fst(x),fst(z)\<rangle>,V`\<langle>snd(x),snd(z)\<rangle>\<rangle>\<in>(R\<times>S)"
        by safe
      have "M`\<langle>fst(y),fst(x)\<rangle>\<in>R" "V`\<langle>snd(y),snd(x)\<rangle>\<in>S" "M`\<langle>fst(z),fst(x)\<rangle>\<in>R"
        "V`\<langle>snd(z),snd(x)\<rangle>\<in>S" using xr xs yr ys zr zs r1.Ring_ZF_1_L4(3) r2.Ring_ZF_1_L4(3)
        by fast+
      then have els2:"\<langle>M`\<langle>fst(y),fst(x)\<rangle>,V`\<langle>snd(y),snd(x)\<rangle>\<rangle>\<in>(R\<times>S)"  "\<langle>M`\<langle>fst(z),fst(x)\<rangle>,V`\<langle>snd(z),snd(x)\<rangle>\<rangle>\<in>(R\<times>S)"
        by safe
      have left: "?DM`\<langle>x,?DA`\<langle>y,z\<rangle>\<rangle> = ?DA`\<langle>?DM`\<langle>x,y\<rangle>,?DM`\<langle>x,z\<rangle>\<rangle>"
      proof -
        have "?DM`\<langle>x,?DA`\<langle>y,z\<rangle>\<rangle> =
          \<langle>M`\<langle>fst(x), fst(?DA`\<langle>y,z\<rangle>)\<rangle>, V`\<langle>snd(x), snd(?DA`\<langle>y,z\<rangle>)\<rangle>\<rangle>"
          using DM_val yz xyz(1) by (simp only:)
        also have "\<dots> = \<langle>M`\<langle>fst(x), A`\<langle>fst(y),fst(z)\<rangle>\<rangle>, V`\<langle>snd(x), U`\<langle>snd(y),snd(z)\<rangle>\<rangle>\<rangle>"
          using DA_val xyz(2,3) by (simp only:fst_conv snd_conv)
        also have "\<dots> =
          \<langle>A`\<langle>M`\<langle>fst(x),fst(y)\<rangle>, M`\<langle>fst(x),fst(z)\<rangle>\<rangle>,
           U`\<langle>V`\<langle>snd(x),snd(y)\<rangle>, V`\<langle>snd(x),snd(z)\<rangle>\<rangle>\<rangle>"
          using distR distS xr yr zr xs ys zs
          unfolding IsDistributive_def by (simp only:)
        also have "\<dots> = ?DA`\<langle>\<langle>M`\<langle>fst(x),fst(y)\<rangle>,V`\<langle>snd(x),snd(y)\<rangle>\<rangle>,\<langle>M`\<langle>fst(x),fst(z)\<rangle>,V`\<langle>snd(x),snd(z)\<rangle>\<rangle>\<rangle>"
          using DA_val els by (simp only:fst_conv snd_conv)
        also have "\<dots> = ?DA`\<langle>?DM`\<langle>x,y\<rangle>,?DM`\<langle>x,z\<rangle>\<rangle>"
          using DA_val DM_val xyz by (simp only:fst_conv snd_conv)
        finally show ?thesis .
      qed
      have right: "?DM`\<langle>?DA`\<langle>y,z\<rangle>,x\<rangle> = ?DA`\<langle>?DM`\<langle>y,x\<rangle>,?DM`\<langle>z,x\<rangle>\<rangle>"
      proof -
        have "?DM`\<langle>?DA`\<langle>y,z\<rangle>,x\<rangle> =
          \<langle>M`\<langle>fst(?DA`\<langle>y,z\<rangle>),fst(x)\<rangle>, V`\<langle>snd(?DA`\<langle>y,z\<rangle>),snd(x)\<rangle>\<rangle>"
          using DM_val DA_val xyz(1) yz by (simp only:)
        also have "\<dots> = \<langle>M`\<langle>A`\<langle>fst(y),fst(z)\<rangle>,fst(x)\<rangle>, V`\<langle>U`\<langle>snd(y),snd(z)\<rangle>,snd(x)\<rangle>\<rangle>"
          using DA_val xyz(2,3) by (simp only:fst_conv snd_conv)
        also have "\<dots> =
          \<langle>A`\<langle>M`\<langle>fst(y),fst(x)\<rangle>, M`\<langle>fst(z),fst(x)\<rangle>\<rangle>,
           U`\<langle>V`\<langle>snd(y),snd(x)\<rangle>, V`\<langle>snd(z),snd(x)\<rangle>\<rangle>\<rangle>"
          using distR distS xr yr zr xs ys zs
          unfolding IsDistributive_def by (simp only:)
        also have "\<dots> = ?DA`\<langle>\<langle>M`\<langle>fst(y),fst(x)\<rangle>,V`\<langle>snd(y),snd(x)\<rangle>\<rangle>,\<langle>M`\<langle>fst(z),fst(x)\<rangle>,V`\<langle>snd(z),snd(x)\<rangle>\<rangle>\<rangle>"
          using DA_val els2 by (simp only:fst_conv snd_conv)
        also have "\<dots> = ?DA`\<langle>?DM`\<langle>y,x\<rangle>,?DM`\<langle>z,x\<rangle>\<rangle>"
          using DA_val DM_val xyz by (simp only:fst_conv snd_conv)
        finally show ?thesis .
      qed
      from left right have
        "?DM`\<langle>x,?DA`\<langle>y,z\<rangle>\<rangle> = ?DA`\<langle>?DM`\<langle>x,y\<rangle>,?DM`\<langle>x,z\<rangle>\<rangle> \<and>
         ?DM`\<langle>?DA`\<langle>y,z\<rangle>,x\<rangle> = ?DA`\<langle>?DM`\<langle>y,x\<rangle>,?DM`\<langle>z,x\<rangle>\<rangle>" by  (simp only:)
    }
    thus ?thesis unfolding IsDistributive_def by blast
  qed
  from DA_group DA_comm DM_monoid distrib show ?thesis
    unfolding IsAring_def by blast
qed

text\<open>The additive neutral element of the direct product ring is the pair
  of additive neutral elements.\<close>

lemma direct_product_neutral:
  assumes ringR: "IsAring(R,A,M)" and ringS: "IsAring(S,U,V)"
  shows "TheNeutralElement(R\<times>S, DirectProduct(A,U,R,S)) =
         \<langle>TheNeutralElement(R,A), TheNeutralElement(S,U)\<rangle>"
proof -
  let ?DA = "DirectProduct(A,U,R,S)"
  interpret r1: ring0 R A M "\<lambda> x y. A`\<langle>x,y\<rangle>" "\<lambda> x. GroupInv(R,A)`x"
    "\<lambda>x y. A`\<langle>x,GroupInv(R,A)`y\<rangle>" "\<lambda>x y. M`\<langle>x,y\<rangle>" "TheNeutralElement(R,A)"
    "TheNeutralElement(R,M)" "A`\<langle>TheNeutralElement(R,M),TheNeutralElement(R,M)\<rangle>"
    "\<lambda>x. M`\<langle>x,x\<rangle>" "\<lambda>s. Fold(A,TheNeutralElement(R,A),s)" "\<lambda>n x. Fold(A,TheNeutralElement(R,A),{\<langle>k,x\<rangle>. k\<in>n})"
    "\<lambda>s. Fold(M,TheNeutralElement(R,M),s)" "\<lambda>n x. Fold(M,TheNeutralElement(R,M),{\<langle>k,x\<rangle>. k\<in>n})"
   using ringR unfolding ring0_def by auto
  interpret r2: ring0 S U V "\<lambda> x y. U`\<langle>x,y\<rangle>" "\<lambda> x. GroupInv(S,U)`x"
    "\<lambda>x y. U`\<langle>x,GroupInv(S,U)`y\<rangle>" "\<lambda>x y. V`\<langle>x,y\<rangle>" "TheNeutralElement(S,U)"
    "TheNeutralElement(S,V)" "U`\<langle>TheNeutralElement(S,V),TheNeutralElement(S,V)\<rangle>"
    "\<lambda>x. V`\<langle>x,x\<rangle>" "\<lambda>s. Fold(U,TheNeutralElement(S,U),s)" "\<lambda>n x. Fold(U,TheNeutralElement(S,U),{\<langle>k,x\<rangle>. k\<in>n})"
    "\<lambda>s. Fold(V,TheNeutralElement(S,V),s)" "\<lambda>n x. Fold(V,TheNeutralElement(S,V),{\<langle>k,x\<rangle>. k\<in>n})"
    using ringS unfolding ring0_def by auto
  have A_fun: "A : R\<times>R\<rightarrow>R" using r1.add_group.group_oper_fun by simp
  have U_fun: "U : S\<times>S\<rightarrow>S" using r2.add_group.group_oper_fun by simp
  interpret dpA: direct0 A U R S "DirectProduct(A,U,R,S)" using A_fun U_fun unfolding direct0_def by auto
  have DA_val: "\<forall>x\<in>R\<times>S. \<forall>y\<in>R\<times>S.
    ?DA`\<langle>x,y\<rangle> = \<langle>A`\<langle>fst(x),fst(y)\<rangle>, U`\<langle>snd(x),snd(y)\<rangle>\<rangle>"
    using dpA.DirectProduct_ZF_1_L2.
  have A_assoc: "A {is associative on} R"
    using r1.add_group.groupAssum unfolding IsAgroup_def IsAmonoid_def by  (simp only:)
  have U_assoc: "U {is associative on} S"
    using r2.add_group.groupAssum unfolding IsAgroup_def IsAmonoid_def by  (simp only:)
  have DA_assoc: "?DA {is associative on} R\<times>S"
    using dpA.DirectProduct_ZF_2_L2[OF A_assoc U_assoc] by  (simp only:)
  let ?zRS = "\<langle>TheNeutralElement(R,A), TheNeutralElement(S,U)\<rangle>"
  have zRS_in: "?zRS \<in> R\<times>S"
    using r1.Ring_ZF_1_L2(1) r2.Ring_ZF_1_L2(1) by (simp only:)
  have DA_neut_prop: "\<forall>p\<in>R\<times>S.
    ?DA`\<langle>?zRS,p\<rangle> = p \<and> ?DA`\<langle>p,?zRS\<rangle> = p"
  proof
    fix p assume p: "p \<in> R\<times>S"
    have pr: "fst(p) \<in> R" and ps: "snd(p) \<in> S" using p by auto
    have "?DA`\<langle>?zRS,p\<rangle> =
      \<langle>A`\<langle>fst(?zRS),fst(p)\<rangle>, U`\<langle>snd(?zRS),snd(p)\<rangle>\<rangle>"
      using DA_val zRS_in p by blast
    also have "\<dots> = \<langle>A`\<langle>TheNeutralElement(R,A),fst(p)\<rangle>,U`\<langle>TheNeutralElement(S,U),snd(p)\<rangle>\<rangle>"
      by (simp only:fst_conv snd_conv)
    also have "\<dots> = \<langle>fst(p), snd(p)\<rangle>"
      using r1.Ring_ZF_1_L3(4)[OF pr] r2.Ring_ZF_1_L3(4)[OF ps] by (simp only:)
    also have "\<dots> = p" using p by auto
    finally have left: "?DA`\<langle>?zRS,p\<rangle> = p" .
    have "?DA`\<langle>p,?zRS\<rangle> =
      \<langle>A`\<langle>fst(p),fst(?zRS)\<rangle>, U`\<langle>snd(p),snd(?zRS)\<rangle>\<rangle>"
      using DA_val zRS_in p by blast
    also have "\<dots> = \<langle>A`\<langle>fst(p),TheNeutralElement(R,A)\<rangle>,U`\<langle>snd(p),TheNeutralElement(S,U)\<rangle>\<rangle>" 
      by (simp only:fst_conv snd_conv)
    also have "\<dots> = \<langle>fst(p), snd(p)\<rangle>"
      using r1.Ring_ZF_1_L3(3)[OF pr] r2.Ring_ZF_1_L3(3)[OF ps] by (simp only:)
    also have "\<dots> = p" using p by auto
    finally have right: "?DA`\<langle>p,?zRS\<rangle> = p" .
    from left right show "?DA`\<langle>?zRS,p\<rangle> = p \<and> ?DA`\<langle>p,?zRS\<rangle> = p" by blast
  qed
  have DA_monoid: "IsAmonoid(R\<times>S, ?DA)"
    using DA_assoc zRS_in DA_neut_prop unfolding IsAmonoid_def by blast
  interpret DA_mon: monoid0 "R\<times>S" ?DA "\<lambda>x y. ?DA`\<langle>x,y\<rangle>" using DA_monoid unfolding monoid0_def by (simp only:)
  from DA_mon.group0_1_L4[of ?zRS] zRS_in DA_neut_prop have "\<langle>TheNeutralElement(R, A),
     TheNeutralElement(S, U)\<rangle> =
    TheNeutralElement
     (R \<times> S,
      DirectProduct(A, U, R, S))" by blast
  then show ?thesis by (simp only:sym)
qed

text\<open>The multiplicative neutral element of the direct product ring is the pair
  of multiplicative neutral elements.\<close>

lemma direct_product_neutral_mult:
  assumes ringR: "IsAring(R,A,M)" and ringS: "IsAring(S,U,V)"
  shows "TheNeutralElement(R\<times>S, DirectProduct(M,V,R,S)) =
         \<langle>TheNeutralElement(R,M), TheNeutralElement(S,V)\<rangle>"
proof -
  let ?DM = "DirectProduct(M,V,R,S)"
  interpret r1: ring0 R A M "\<lambda> x y. A`\<langle>x,y\<rangle>" "\<lambda> x. GroupInv(R,A)`x"
    "\<lambda>x y. A`\<langle>x,GroupInv(R,A)`y\<rangle>" "\<lambda>x y. M`\<langle>x,y\<rangle>" "TheNeutralElement(R,A)"
    "TheNeutralElement(R,M)" "A`\<langle>TheNeutralElement(R,M),TheNeutralElement(R,M)\<rangle>"
    "\<lambda>x. M`\<langle>x,x\<rangle>" "\<lambda>s. Fold(A,TheNeutralElement(R,A),s)" "\<lambda>n x. Fold(A,TheNeutralElement(R,A),{\<langle>k,x\<rangle>. k\<in>n})"
    "\<lambda>s. Fold(M,TheNeutralElement(R,M),s)" "\<lambda>n x. Fold(M,TheNeutralElement(R,M),{\<langle>k,x\<rangle>. k\<in>n})"
   using ringR unfolding ring0_def by auto
  interpret r2: ring0 S U V "\<lambda> x y. U`\<langle>x,y\<rangle>" "\<lambda> x. GroupInv(S,U)`x"
    "\<lambda>x y. U`\<langle>x,GroupInv(S,U)`y\<rangle>" "\<lambda>x y. V`\<langle>x,y\<rangle>" "TheNeutralElement(S,U)"
    "TheNeutralElement(S,V)" "U`\<langle>TheNeutralElement(S,V),TheNeutralElement(S,V)\<rangle>"
    "\<lambda>x. V`\<langle>x,x\<rangle>" "\<lambda>s. Fold(U,TheNeutralElement(S,U),s)" "\<lambda>n x. Fold(U,TheNeutralElement(S,U),{\<langle>k,x\<rangle>. k\<in>n})"
    "\<lambda>s. Fold(V,TheNeutralElement(S,V),s)" "\<lambda>n x. Fold(V,TheNeutralElement(S,V),{\<langle>k,x\<rangle>. k\<in>n})"
    using ringS unfolding ring0_def by auto
  have M_fun: "M : R\<times>R\<rightarrow>R" using r1.mult_monoid.monoid_oper_fun by simp
  have V_fun: "V : S\<times>S\<rightarrow>S" using r2.mult_monoid.monoid_oper_fun by simp
  interpret dpA: direct0 M V R S "DirectProduct(M,V,R,S)" using M_fun V_fun unfolding direct0_def by auto
  have DM_val: "\<forall>x\<in>R\<times>S. \<forall>y\<in>R\<times>S.
    ?DM`\<langle>x,y\<rangle> = \<langle>M`\<langle>fst(x),fst(y)\<rangle>, V`\<langle>snd(x),snd(y)\<rangle>\<rangle>"
    using dpA.DirectProduct_ZF_1_L2.
  have A_assoc: "M {is associative on} R"
    using r1.mult_monoid.monoidAssum unfolding IsAmonoid_def by  (simp only:)
  have U_assoc: "V {is associative on} S"
    using r2.mult_monoid.monoidAssum unfolding IsAmonoid_def by  (simp only:)
  have DA_assoc: "?DM {is associative on} R\<times>S"
    using dpA.DirectProduct_ZF_2_L2[OF A_assoc U_assoc] by  (simp only:)
  let ?zRS = "\<langle>TheNeutralElement(R,M), TheNeutralElement(S,V)\<rangle>"
  have zRS_in: "?zRS \<in> R\<times>S"
    using r1.Ring_ZF_1_L2(2) r2.Ring_ZF_1_L2(2) by (simp only:)
  have DA_neut_prop: "\<forall>p\<in>R\<times>S.
    ?DM`\<langle>?zRS,p\<rangle> = p \<and> ?DM`\<langle>p,?zRS\<rangle> = p"
  proof
    fix p assume p: "p \<in> R\<times>S"
    have pr: "fst(p) \<in> R" and ps: "snd(p) \<in> S" using p by auto
    have "?DM`\<langle>?zRS,p\<rangle> =
      \<langle>M`\<langle>fst(?zRS),fst(p)\<rangle>, V`\<langle>snd(?zRS),snd(p)\<rangle>\<rangle>"
      using DM_val zRS_in p by blast
    also have "\<dots> = \<langle>M`\<langle>TheNeutralElement(R,M),fst(p)\<rangle>,V`\<langle>TheNeutralElement(S,V),snd(p)\<rangle>\<rangle>"
      by (simp only:fst_conv snd_conv)
    also have "\<dots> = \<langle>fst(p), snd(p)\<rangle>"
      using r1.Ring_ZF_1_L3(6)[OF pr] r2.Ring_ZF_1_L3(6)[OF ps] by (simp only:)
    also have "\<dots> = p" using p by auto
    finally have left: "?DM`\<langle>?zRS,p\<rangle> = p" .
    have "?DM`\<langle>p,?zRS\<rangle> =
      \<langle>M`\<langle>fst(p),fst(?zRS)\<rangle>, V`\<langle>snd(p),snd(?zRS)\<rangle>\<rangle>"
      using DM_val zRS_in p by blast
    also have "\<dots> = \<langle>M`\<langle>fst(p),TheNeutralElement(R,M)\<rangle>,V`\<langle>snd(p),TheNeutralElement(S,V)\<rangle>\<rangle>" 
      by (simp only:fst_conv snd_conv)
    also have "\<dots> = \<langle>fst(p), snd(p)\<rangle>"
      using r1.Ring_ZF_1_L3(5)[OF pr] r2.Ring_ZF_1_L3(5)[OF ps] by (simp only:)
    also have "\<dots> = p" using p by auto
    finally have right: "?DM`\<langle>p,?zRS\<rangle> = p" .
    from left right show "?DM`\<langle>?zRS,p\<rangle> = p \<and> ?DM`\<langle>p,?zRS\<rangle> = p" by blast
  qed
  have DA_monoid: "IsAmonoid(R\<times>S, ?DM)"
    using DA_assoc zRS_in DA_neut_prop unfolding IsAmonoid_def by blast
  interpret DA_mon: monoid0 "R\<times>S" ?DM "\<lambda>x y. ?DM`\<langle>x,y\<rangle>" using DA_monoid unfolding monoid0_def by (simp only:)
  from DA_mon.group0_1_L4[of ?zRS] zRS_in DA_neut_prop have "\<langle>TheNeutralElement(R, M),
     TheNeutralElement(S, V)\<rangle> =
    TheNeutralElement
     (R \<times> S,
      DirectProduct(M, V, R, S))" by blast
  then show ?thesis by (simp only:sym)
qed

subsection\<open>Chinese Remainder Theorem\<close>

text\<open>The Chinese Remainder Theorem: if $I$ and $J$ are comaximal ideals of
  a commutative ring $R$ (i.e.\ $I + J = R$), then $R/(I \cap J) \cong R/I \times R/J$
  as rings. The proof constructs the canonical map $\varphi(r) = ([r]_I, [r]_J)$,
  shows it is a surjective ring homomorphism with kernel $I \cap J$, and applies the
  first isomorphism theorem.\<close>

theorem (in commutative_ring) chinese_remainder:
  assumes idealI: "I\<triangleleft>R" and idealJ: "J\<triangleleft>R"
    and comaximal: "I+\<^sub>IJ = R"
  shows "\<exists>\<phi>. IsRingHomomor(\<phi>,
           QuotientBy(I\<inter>J),
           QuotientGroupOp(R,A,I\<inter>J),
           ProjFun2(R,QuotientGroupRel(R,A,I\<inter>J),M),
           QuotientBy(I)\<times>QuotientBy(J),
           DirectProduct(QuotientGroupOp(R,A,I),QuotientGroupOp(R,A,J),
                         QuotientBy(I),QuotientBy(J)),
           DirectProduct(ProjFun2(R,QuotientGroupRel(R,A,I),M),
                         ProjFun2(R,QuotientGroupRel(R,A,J),M),
                         QuotientBy(I),QuotientBy(J)))
           \<and> \<phi> \<in> bij(QuotientBy(I\<inter>J),
                       QuotientBy(I)\<times>QuotientBy(J))"
proof -
  let ?rI = "QuotientGroupRel(R,A,I)"
  let ?rJ = "QuotientGroupRel(R,A,J)"
  let ?qI = "QuotientGroupOp(R,A,I)"
  let ?qJ = "QuotientGroupOp(R,A,J)"
  let ?mI = "ProjFun2(R,?rI,M)"
  let ?mJ = "ProjFun2(R,?rJ,M)"
  let ?QI = "QuotientBy(I)"
  let ?QJ = "QuotientBy(J)"
  let ?DA = "DirectProduct(?qI,?qJ,?QI,?QJ)"
  let ?DM = "DirectProduct(?mI,?mJ,?QI,?QJ)"
  let ?IJ = "I\<inter>J"
  let ?\<phi> = "\<lambda>r\<in>R. \<langle>?rI``{r}, ?rJ``{r}\<rangle>"
  have idealIJ: "?IJ\<triangleleft>R" using intersection_ideals[of "{I,J}"] idealI idealJ by simp
  have QI_ring: "IsAring(?QI,?qI,?mI)" using quotientBy_is_ring[OF idealI] by simp
  have QJ_ring: "IsAring(?QJ,?qJ,?mJ)" using quotientBy_is_ring[OF idealJ] by simp
  have QIJ_ring: "IsAring(?QI\<times>?QJ,?DA,?DM)"
    using direct_product_ring[OF QI_ring QJ_ring] by simp
  have \<phi>_fun: "?\<phi> : R\<rightarrow>?QI\<times>?QJ"
  proof -
    have eqI: "equiv(R,?rI)" using ideal_equiv_rel[OF idealI] by simp
    have eqJ: "equiv(R,?rJ)" using ideal_equiv_rel[OF idealJ] by simp
    {
      fix r assume r: "r\<in>R"
      have "?rI``{r} \<in> ?QI" using eqI r quotientI
        unfolding QuotientBy_def[OF idealI] by auto
      moreover have "?rJ``{r} \<in> ?QJ" using eqJ r quotientI
        unfolding QuotientBy_def[OF idealJ] by auto
      ultimately have "\<langle>?rI``{r},?rJ``{r}\<rangle> \<in> ?QI\<times>?QJ" by auto
    }
    then show ?thesis using ZF_fun_from_total lam_type by auto
  qed
  have \<phi>_val: "\<forall>r\<in>R. ?\<phi>`r = \<langle>?rI``{r},?rJ``{r}\<rangle>"
    using \<phi>_fun ZF_fun_from_tot_val by auto
  have eqI: "equiv(R,?rI)" using ideal_equiv_rel[OF idealI] by simp
  have eqJ: "equiv(R,?rJ)" using ideal_equiv_rel[OF idealJ] by simp
  have congI_A: "Congruent2(?rI,A)"
    using Group_ZF_2_4_L5A[OF add_group.groupAssum ideal_normal_add_subgroup[OF idealI]]
    by simp
  have congJ_A: "Congruent2(?rJ,A)"
    using Group_ZF_2_4_L5A[OF add_group.groupAssum ideal_normal_add_subgroup[OF idealJ]]
    by simp
  have congI_M: "Congruent2(?rI,M)" using quotientBy_mul_monoid(1)[OF idealI] by simp
  have congJ_M: "Congruent2(?rJ,M)" using quotientBy_mul_monoid(1)[OF idealJ] by simp
  have qI_val: "\<forall>r\<^sub>1\<in>R. \<forall>r\<^sub>2\<in>R.
    ?qI`\<langle>?rI``{r\<^sub>1},?rI``{r\<^sub>2}\<rangle> = ?rI``{A`\<langle>r\<^sub>1,r\<^sub>2\<rangle>}"
    using EquivClass_1_L10[OF eqI congI_A]
    unfolding QuotientGroupOp_def by auto
  have qJ_val: "\<forall>r\<^sub>1\<in>R. \<forall>r\<^sub>2\<in>R.
    ?qJ`\<langle>?rJ``{r\<^sub>1},?rJ``{r\<^sub>2}\<rangle> = ?rJ``{A`\<langle>r\<^sub>1,r\<^sub>2\<rangle>}"
    using EquivClass_1_L10[OF eqJ congJ_A]
    unfolding QuotientGroupOp_def by auto
  have mI_val: "\<forall>r\<^sub>1\<in>R. \<forall>r\<^sub>2\<in>R.
    ?mI`\<langle>?rI``{r\<^sub>1},?rI``{r\<^sub>2}\<rangle> = ?rI``{M`\<langle>r\<^sub>1,r\<^sub>2\<rangle>}"
    using EquivClass_1_L10[OF eqI congI_M] by simp
  have mJ_val: "\<forall>r\<^sub>1\<in>R. \<forall>r\<^sub>2\<in>R.
    ?mJ`\<langle>?rJ``{r\<^sub>1},?rJ``{r\<^sub>2}\<rangle> = ?rJ``{M`\<langle>r\<^sub>1,r\<^sub>2\<rangle>}"
    using EquivClass_1_L10[OF eqJ congJ_M] by simp
  have QI_fun: "?qI : ?QI\<times>?QI\<rightarrow>?QI"
    using QI_ring unfolding IsAring_def IsAgroup_def IsAmonoid_def IsAssociative_def by auto
  have QJ_fun: "?qJ : ?QJ\<times>?QJ\<rightarrow>?QJ"
    using QJ_ring unfolding IsAring_def IsAgroup_def IsAmonoid_def IsAssociative_def by auto
  have mI_fun: "?mI : ?QI\<times>?QI\<rightarrow>?QI"
    using QI_ring unfolding IsAring_def IsAmonoid_def IsAssociative_def by auto
  have mJ_fun: "?mJ : ?QJ\<times>?QJ\<rightarrow>?QJ"
    using QJ_ring unfolding IsAring_def IsAmonoid_def IsAssociative_def by auto
  have DA_val: "\<forall>x\<in>?QI\<times>?QJ. \<forall>y\<in>?QI\<times>?QJ.
    ?DA`\<langle>x,y\<rangle> = \<langle>?qI`\<langle>fst(x),fst(y)\<rangle>, ?qJ`\<langle>snd(x),snd(y)\<rangle>\<rangle>"
  proof -
    interpret dpDA: direct0 ?qI ?qJ ?QI ?QJ ?DA
      using QI_fun QJ_fun unfolding direct0_def by auto
    from dpDA.DirectProduct_ZF_1_L2 show ?thesis .
  qed
  have DM_val: "\<forall>x\<in>?QI\<times>?QJ. \<forall>y\<in>?QI\<times>?QJ.
    ?DM`\<langle>x,y\<rangle> = \<langle>?mI`\<langle>fst(x),fst(y)\<rangle>, ?mJ`\<langle>snd(x),snd(y)\<rangle>\<rangle>"
  proof -
    interpret dpDM: direct0 ?mI ?mJ ?QI ?QJ ?DM
      using mI_fun mJ_fun unfolding direct0_def by auto
    from dpDM.DirectProduct_ZF_1_L2 show ?thesis .
  qed
  have \<phi>_add: "IsMorphism(R,A,?DA,?\<phi>)"
    unfolding IsMorphism_def
  proof (intro ballI)
    fix r\<^sub>1 r\<^sub>2 assume r1: "r\<^sub>1\<in>R" and r2: "r\<^sub>2\<in>R"
    have sum_in: "A`\<langle>r\<^sub>1,r\<^sub>2\<rangle>\<in>R" using Ring_ZF_1_L4(1)[OF r1 r2] by simp
    have \<phi>r1_in: "?\<phi>`r\<^sub>1 \<in> ?QI\<times>?QJ" using \<phi>_fun r1 apply_type by (simp only:)
    have \<phi>r2_in: "?\<phi>`r\<^sub>2 \<in> ?QI\<times>?QJ" using \<phi>_fun r2 apply_type by (simp only:)
    have els:"?rI``{r\<^sub>1}\<in>?QI" "?rJ``{r\<^sub>1}\<in>?QJ" "?rI``{r\<^sub>2}\<in>?QI" "?rJ``{r\<^sub>2}\<in>?QJ"
      using eqI r1 r2 quotientI
      unfolding QuotientBy_def[OF idealI] QuotientBy_def[OF idealJ] by auto
    then have elsx:"\<langle>?rI``{r\<^sub>1},?rJ``{r\<^sub>1}\<rangle>\<in>?QI\<times>?QJ" "\<langle>?rI``{r\<^sub>2},?rJ``{r\<^sub>2}\<rangle>\<in>?QI\<times>?QJ"
      by auto
    have "?\<phi>`(A`\<langle>r\<^sub>1,r\<^sub>2\<rangle>) = \<langle>?rI``{A`\<langle>r\<^sub>1,r\<^sub>2\<rangle>}, ?rJ``{A`\<langle>r\<^sub>1,r\<^sub>2\<rangle>}\<rangle>"
      using \<phi>_val sum_in by auto
    also have "\<dots> = \<langle>?qI`\<langle>?rI``{r\<^sub>1},?rI``{r\<^sub>2}\<rangle>, ?qJ`\<langle>?rJ``{r\<^sub>1},?rJ``{r\<^sub>2}\<rangle>\<rangle>"
      using qI_val r1 r2 qJ_val by auto
    also have "\<dots> = ?DA`\<langle>\<langle>?rI``{r\<^sub>1},?rJ``{r\<^sub>1}\<rangle>,\<langle>?rI``{r\<^sub>2},?rJ``{r\<^sub>2}\<rangle>\<rangle>"
      using DA_val elsx by (simp only: sym fst_conv snd_conv)
    also have "\<dots> = ?DA`\<langle>?\<phi>`r\<^sub>1,?\<phi>`r\<^sub>2\<rangle>"
      using \<phi>_val r1 r2 by (simp only:)
    finally show "?\<phi>`(A`\<langle>r\<^sub>1,r\<^sub>2\<rangle>) = ?DA`\<langle>?\<phi>`r\<^sub>1,?\<phi>`r\<^sub>2\<rangle>" .
  qed
  have \<phi>_mult: "IsMorphism(R,M,?DM,?\<phi>)"
    unfolding IsMorphism_def
  proof (intro ballI)
    fix r\<^sub>1 r\<^sub>2 assume r1: "r\<^sub>1\<in>R" and r2: "r\<^sub>2\<in>R"
    have prod_in: "M`\<langle>r\<^sub>1,r\<^sub>2\<rangle>\<in>R" using Ring_ZF_1_L4(3)[OF r1 r2] by simp
    have \<phi>r1_in: "?\<phi>`r\<^sub>1 \<in> ?QI\<times>?QJ" using \<phi>_fun r1 apply_type by (simp only:)
    have \<phi>r2_in: "?\<phi>`r\<^sub>2 \<in> ?QI\<times>?QJ" using \<phi>_fun r2 apply_type by (simp only:)
    have "?\<phi>`(M`\<langle>r\<^sub>1,r\<^sub>2\<rangle>) = \<langle>?rI``{M`\<langle>r\<^sub>1,r\<^sub>2\<rangle>}, ?rJ``{M`\<langle>r\<^sub>1,r\<^sub>2\<rangle>}\<rangle>"
      using \<phi>_val prod_in by auto
    also have "\<dots> = \<langle>?mI`\<langle>?rI``{r\<^sub>1},?rI``{r\<^sub>2}\<rangle>, ?mJ`\<langle>?rJ``{r\<^sub>1},?rJ``{r\<^sub>2}\<rangle>\<rangle>"
      using mI_val r1 r2 mJ_val by auto
    also have "\<dots> = ?DM`\<langle>\<langle>?rI``{r\<^sub>1},?rJ``{r\<^sub>1}\<rangle>,\<langle>?rI``{r\<^sub>2},?rJ``{r\<^sub>2}\<rangle>\<rangle>"
      using DM_val \<phi>r1_in \<phi>r2_in \<phi>_val r1 r2 by auto
    also have "\<dots> = ?DM`\<langle>?\<phi>`r\<^sub>1,?\<phi>`r\<^sub>2\<rangle>"
      using \<phi>_val r1 r2 by auto
    finally show "?\<phi>`(M`\<langle>r\<^sub>1,r\<^sub>2\<rangle>) = ?DM`\<langle>?\<phi>`r\<^sub>1,?\<phi>`r\<^sub>2\<rangle>" .
  qed
  have \<phi>_one: "?\<phi>`\<one> = TheNeutralElement(?QI\<times>?QJ,?DM)"
  proof -
    have "?\<phi>`\<one> = \<langle>?rI``{\<one>},?rJ``{\<one>}\<rangle>"
      using \<phi>_val Ring_ZF_1_L2(2) by auto
    also have "\<dots> = \<langle>TheNeutralElement(?QI,?mI), TheNeutralElement(?QJ,?mJ)\<rangle>"
      using one_quotient[OF idealI] one_quotient[OF idealJ] by auto
    also have "\<dots> = TheNeutralElement(?QI\<times>?QJ,?DM)"
      using direct_product_neutral_mult[OF QI_ring QJ_ring] by simp
    finally show ?thesis .
  qed
  have \<phi>_hom: "IsRingHomomor(?\<phi>,R,A,M,?QI\<times>?QJ,?DA,?DM)"
    using \<phi>_fun \<phi>_add \<phi>_mult \<phi>_one unfolding IsRingHomomor_def by simp
  have neut_DA: "TheNeutralElement(?QI\<times>?QJ,?DA) =
      \<langle>TheNeutralElement(?QI,?qI), TheNeutralElement(?QJ,?qJ)\<rangle>"
    using direct_product_neutral[OF QI_ring QJ_ring] by simp
  have neut_QI: "TheNeutralElement(?QI,?qI) = ?rI``{\<zero>}"
    using neutral_quotient[OF idealI] by simp
  have neut_QJ: "TheNeutralElement(?QJ,?qJ) = ?rJ``{\<zero>}"
    using neutral_quotient[OF idealJ] by simp
  have norm_I: "IsAnormalSubgroup(R,A,I)" using ideal_normal_add_subgroup[OF idealI] by simp
  have norm_J: "IsAnormalSubgroup(R,A,J)" using ideal_normal_add_subgroup[OF idealJ] by simp
  have ker_eq: "?\<phi>-``{TheNeutralElement(?QI\<times>?QJ,?DA)} = ?IJ"
  proof
    show "?\<phi>-``{TheNeutralElement(?QI\<times>?QJ,?DA)} \<subseteq> ?IJ"
    proof
      fix r assume r_in_ker: "r \<in> ?\<phi>-``{TheNeutralElement(?QI\<times>?QJ,?DA)}"
      then have r: "r\<in>R" and \<phi>r: "?\<phi>`r = TheNeutralElement(?QI\<times>?QJ,?DA)"
        using func1_1_L15 by auto
      from \<phi>r have vals: "?rI``{r} = ?rI``{\<zero>} \<and> ?rJ``{r} = ?rJ``{\<zero>}"
        using \<phi>_val r neut_DA neut_QI neut_QJ by auto
      have rI: "r\<in>I"
        using add_group.Group_ZF_2_4_L5E norm_I r neut_QI vals
        unfolding QuotientBy_def[OF idealI] by auto
      have rJ: "r\<in>J"
        using add_group.Group_ZF_2_4_L5E norm_J r neut_QJ vals
        unfolding QuotientBy_def[OF idealJ] by auto
      from rI rJ show "r \<in> ?IJ" by auto
    qed
    show "?IJ \<subseteq> ?\<phi>-``{TheNeutralElement(?QI\<times>?QJ,?DA)}"
    proof
      fix r assume r_in: "r \<in> ?IJ"
      then have rI: "r\<in>I" and rJ: "r\<in>J" and r: "r\<in>R"
        using ideal_dest_subset[OF idealI] by auto
      have "?rI``{r} = ?rI``{\<zero>}"
        using add_group.Group_ZF_2_4_L5E norm_I r neut_QI rI
        unfolding QuotientBy_def[OF idealI] by auto
      moreover have "?rJ``{r} = ?rJ``{\<zero>}"
        using add_group.Group_ZF_2_4_L5E norm_J r neut_QJ rJ
        unfolding QuotientBy_def[OF idealJ] by auto
      ultimately have "?\<phi>`r = TheNeutralElement(?QI\<times>?QJ,?DA)"
        using \<phi>_val r neut_DA neut_QI neut_QJ by auto
      with r \<phi>_fun show "r \<in> ?\<phi>-``{TheNeutralElement(?QI\<times>?QJ,?DA)}"
        using func1_1_L15 by auto
    qed
  qed
  have \<phi>_surj: "?\<phi> \<in> surj(R,?QI\<times>?QJ)"
    unfolding surj_def
  proof (safe)
    from \<phi>_fun show "?\<phi> : R\<rightarrow>?QI\<times>?QJ" .
    fix x y assume pQI: "x \<in> ?QI" and qQJ:"y\<in>?QJ"
    obtain eleA where eA: "x = ?rI``{eleA}" "eleA\<in>R" 
      using pQI unfolding QuotientBy_def[OF idealI] using quotientE[of x R ?rI thesis]
      by blast
    obtain eleB where eB: "eleB\<in>R" "y = ?rJ``{eleB}"
      using qQJ unfolding QuotientBy_def[OF idealJ] using quotientE[of y R ?rJ thesis] by blast
    have one_in_sum: "\<one> \<in> I+\<^sub>IJ"
      using comaximal Ring_ZF_1_L2(2) by auto
    have sum_eq: "I+\<^sub>IJ = A``(I\<times>J)"
      using sum_ideals_is_sum_elements[OF idealI idealJ] by simp
    with one_in_sum have one_in_sum:"\<one>:A``(I\<times>J)" by auto
    have "I\<times>J \<subseteq> R\<times>R" using  ideal_dest_subset[OF idealI]
            ideal_dest_subset[OF idealJ] by auto
    with one_in_sum obtain elemI elemJ where
      ij: "elemI\<in>I" "elemJ\<in>J" "A`\<langle>elemI,elemJ\<rangle>=\<one>"
      using add_group.group_oper_fun func_imagedef[of A "R\<times>R" R "I\<times>J"] by auto
    let ?r = "A`\<langle>M`\<langle>eleA,elemJ\<rangle>, M`\<langle>eleB,elemI\<rangle>\<rangle>"
    have iR: "elemI\<in>R" using ideal_dest_subset[OF idealI] ij(1) by auto
    have jR: "elemJ\<in>R" using ideal_dest_subset[OF idealJ] ij(2) by auto
    have r_in: "?r\<in>R"
      using Ring_ZF_1_L4(1) Ring_ZF_1_L4(3) eA(2) jR
                                Ring_ZF_1_L4(3) eB(1) iR by simp
    have ra_in_I: "A`\<langle>GroupInv(R,A)`eleA,?r\<rangle>\<in>I"
    proof -
      have "A`\<langle>GroupInv(R,A)`eleA, ?r\<rangle>  = A`\<langle>A`\<langle>GroupInv(R,A)`eleA,M`\<langle>eleA,elemJ\<rangle>\<rangle>, M`\<langle>eleB,elemI\<rangle>\<rangle>"
        using Ring_ZF_1_L10(1) add_group.inverse_in_group[OF eA(2)]
              Ring_ZF_1_L4(3)[OF eA(2) jR] Ring_ZF_1_L4(3)[OF eB(1) iR] by auto
      also have "\<dots> = A`\<langle>A`\<langle>M`\<langle>eleA,\<rm>\<one>\<rangle>,M`\<langle>eleA,elemJ\<rangle>\<rangle>, M`\<langle>eleB,elemI\<rangle>\<rangle>"
        using Ring_ZF_1_L3(5)[OF Ring_ZF_1_L3(1)] eA(2) 
          Ring_ZF_1_L7(3)[OF _ Ring_ZF_1_L2(2)] by auto
      also have "\<dots> = A`\<langle>M`\<langle>eleA,A`\<langle>\<rm>\<one>,elemJ\<rangle>\<rangle>, M`\<langle>eleB,elemI\<rangle>\<rangle>"
        using ring_oper_distr(1)[OF eA(2) Ring_ZF_1_L3(1)[OF Ring_ZF_1_L2(2)]]
        jR by simp
      also have "\<dots> = A`\<langle>M`\<langle>eleA,A`\<langle>\<rm>(elemI\<ra>elemJ),elemJ\<rangle>\<rangle>, M`\<langle>eleB,elemI\<rangle>\<rangle>"
        using ij(3) by auto
      also have "\<dots> = A`\<langle>M`\<langle>eleA,A`\<langle>(\<rm>elemI)\<rs>elemJ,elemJ\<rangle>\<rangle>, M`\<langle>eleB,elemI\<rangle>\<rangle>"
        using Ring_ZF_1_L9(2) iR jR by auto
      also have "\<dots> = A`\<langle>M`\<langle>eleA,\<rm>elemI\<rangle>, M`\<langle>eleB,elemI\<rangle>\<rangle>"
        using Ring_ZF_2_L1A(1)[OF Ring_ZF_1_L3(1)] iR jR by auto
      also have "\<dots> = A`\<langle>M`\<langle>\<rm>eleA,elemI\<rangle>, M`\<langle>eleB,elemI\<rangle>\<rangle>"
        using Ring_ZF_1_L7(3) eA(2) iR by auto
      also have "\<dots> = M`\<langle>A`\<langle>\<rm>eleA,eleB\<rangle>,elemI\<rangle>"
        using ring_oper_distr(2)[OF _ Ring_ZF_1_L3(1)] eA(2) eB(1) iR by auto
      finally show ?thesis using ideal_dest_mult(2)[OF idealI ij(1)]
        using Ring_ZF_1_L4(1)[OF Ring_ZF_1_L3(1)[OF eA(2)] eB(1)] by auto
    qed
    then have "\<rm>((\<rm>eleA) \<ra> ?r) \<in>I" using ideal_dest_minus[OF idealI] by auto
    then have "(\<rm>(\<rm>eleA))\<rs>?r :  I" using Ring_ZF_1_L9(2)[OF Ring_ZF_1_L3(1)[OF eA(2)] r_in] by auto
    then have RA:"eleA\<rs>?r: I" using Ring_ZF_1_L3(2) eA(2) by auto
    have rb_in_J: "A`\<langle>GroupInv(R,A)`eleB,?r\<rangle>\<in>J"
    proof -
      have "A`\<langle>GroupInv(R,A)`eleB, ?r\<rangle>  = A`\<langle>A`\<langle>GroupInv(R,A)`eleB,M`\<langle>eleB,elemI\<rangle>\<rangle>, M`\<langle>eleA,elemJ\<rangle>\<rangle>"
        using Ring_ZF_1_L10(1) add_group.inverse_in_group[OF eB(1)]
              Ring_ZF_1_L4(3)[OF eA(2) jR] Ring_ZF_1_L4(3)[OF eB(1) iR]
        Ring_ZF_1_L4(4)[of "M`\<langle>eleA,elemJ\<rangle>" "M`\<langle>eleB,elemI\<rangle>"] by auto
      also have "\<dots> = A`\<langle>A`\<langle>M`\<langle>eleB,\<rm>\<one>\<rangle>,M`\<langle>eleB,elemI\<rangle>\<rangle>, M`\<langle>eleA,elemJ\<rangle>\<rangle>"
        using Ring_ZF_1_L3(5)[OF Ring_ZF_1_L3(1)] eB(1) 
          Ring_ZF_1_L7(3)[OF _ Ring_ZF_1_L2(2)] by auto
      also have "\<dots> = A`\<langle>M`\<langle>eleB,A`\<langle>\<rm>\<one>,elemI\<rangle>\<rangle>, M`\<langle>eleA,elemJ\<rangle>\<rangle>"
        using ring_oper_distr(1)[OF eB(1) Ring_ZF_1_L3(1)[OF Ring_ZF_1_L2(2)]]
        iR by simp
      also have "\<dots> = A`\<langle>M`\<langle>eleB,A`\<langle>\<rm>(elemI\<ra>elemJ),elemI\<rangle>\<rangle>, M`\<langle>eleA,elemJ\<rangle>\<rangle>"
        using ij(3) by auto
      also have "\<dots> = A`\<langle>M`\<langle>eleB,A`\<langle>(\<rm>elemI)\<rs>elemJ,elemI\<rangle>\<rangle>, M`\<langle>eleA,elemJ\<rangle>\<rangle>"
        using Ring_ZF_1_L9(2) iR jR by auto
      also have "\<dots> = A`\<langle>M`\<langle>eleB,\<rm>elemJ\<rangle>, M`\<langle>eleA,elemJ\<rangle>\<rangle>"
        using Ring_ZF_2_L1A(3)[OF _ Ring_ZF_1_L3(1), of elemI elemJ] iR jR unfolding ringsub_def by auto
      also have "\<dots> = A`\<langle>M`\<langle>\<rm>eleB,elemJ\<rangle>, M`\<langle>eleA,elemJ\<rangle>\<rangle>"
        using Ring_ZF_1_L7(3) eB(1) jR by auto
      also have "\<dots> = M`\<langle>A`\<langle>\<rm>eleB,eleA\<rangle>,elemJ\<rangle>"
        using ring_oper_distr(2)[OF _ Ring_ZF_1_L3(1)] eA(2) eB(1) jR by auto
      finally show ?thesis using ideal_dest_mult(2)[OF idealJ ij(2)]
        using Ring_ZF_1_L4(1)[OF Ring_ZF_1_L3(1)[OF eB(1)] eA(2)] by auto
    qed
    then have "\<rm>((\<rm>eleB) \<ra> ?r) \<in>J" using ideal_dest_minus[OF idealJ] by auto
    then have "(\<rm>(\<rm>eleB))\<rs>?r :  J" using Ring_ZF_1_L9(2)[OF Ring_ZF_1_L3(1)[OF eB(1)] r_in] by auto
    then have RB:"eleB\<rs>?r: J" using Ring_ZF_1_L3(2) eB(1) by auto
    have "?rI``{?r} = ?rI``{eleA}"
    proof -
      have "\<langle>eleA,?r\<rangle> \<in> ?rI"
        unfolding QuotientGroupRel_def apply safe
        using eA(2) apply simp using r_in apply simp apply auto using RA by auto
      with eqI show ?thesis using equiv_class_eq by auto
    qed
    moreover have "?rJ``{?r} = ?rJ``{eleB}"
    proof -
      have "\<langle>eleB,?r\<rangle> \<in> ?rJ"
        unfolding QuotientGroupRel_def apply safe
        using eB(1) apply simp using r_in apply simp apply auto using RB by auto
      with eqJ show ?thesis using equiv_class_eq by auto
    qed
    ultimately have "?\<phi>`?r = \<langle>x,y\<rangle>"
      using \<phi>_val r_in eA(1) eB(2) by auto
    with r_in show "\<exists>r\<in>R. ?\<phi>`r = \<langle>x,y\<rangle>" by blast
  qed
  interpret crt: ring_homo R A M "(?QI\<times>?QJ)" ?DA ?DM ?\<phi> _ _ _ _ _ _ _ _  "\<lambda>x b.  DirectProduct
              (QuotientGroupOp(R, A, I),
               QuotientGroupOp(R, A, J),
               QuotientBy(I),
               QuotientBy(J)) `
             \<langle>x, b\<rangle>" "\<lambda>x.  GroupInv
             (QuotientBy(I) \<times> QuotientBy(J),
              DirectProduct
               (QuotientGroupOp(R, A, I),
                QuotientGroupOp(R, A, J),
                QuotientBy(I),
                QuotientBy(J))) `
            x" "\<lambda>x b. DirectProduct
               (QuotientGroupOp(R, A, I),
                QuotientGroupOp(R, A, J),
                QuotientBy(I),
                QuotientBy(J)) `
              \<langle>x, GroupInv
                   (QuotientBy(I) \<times>
                    QuotientBy(J),
                    DirectProduct
                     (QuotientGroupOp
(R, A, I),
                      QuotientGroupOp
(R, A, J),
                      QuotientBy(I),
                      QuotientBy(J))) `
                  b\<rangle>" "\<lambda>x b.  DirectProduct
              (ProjFun2
                (R, QuotientGroupRel
                     (R, A, I),
                 M),
               ProjFun2
                (R, QuotientGroupRel
                     (R, A, J),
                 M),
               QuotientBy(I),
               QuotientBy(J)) `
             \<langle>x, b\<rangle>" " TheNeutralElement
       (QuotientBy(I) \<times> QuotientBy(J),
        DirectProduct
         (QuotientGroupOp(R, A, I),
          QuotientGroupOp(R, A, J),
          QuotientBy(I), QuotientBy(J)))" "TheNeutralElement
      (QuotientBy(I) \<times> QuotientBy(J),
       DirectProduct
        (ProjFun2
          (R, QuotientGroupRel(R, A, I), M),
         ProjFun2
          (R, QuotientGroupRel(R, A, J), M),
         QuotientBy(I), QuotientBy(J)))" "DirectProduct
       (QuotientGroupOp(R, A, I),
        QuotientGroupOp(R, A, J),
        QuotientBy(I), QuotientBy(J)) `
      \<langle>TheNeutralElement
        (QuotientBy(I) \<times> QuotientBy(J),
         DirectProduct
          (ProjFun2
            (R, QuotientGroupRel(R, A, I),
             M),
           ProjFun2
            (R, QuotientGroupRel(R, A, J),
             M),
           QuotientBy(I), QuotientBy(J))),
       TheNeutralElement
        (QuotientBy(I) \<times> QuotientBy(J),
         DirectProduct
          (ProjFun2
            (R, QuotientGroupRel(R, A, I),
             M),
           ProjFun2
            (R, QuotientGroupRel(R, A, J),
             M),
           QuotientBy(I),
           QuotientBy(J)))\<rangle>" "\<lambda>x.  DirectProduct
            (ProjFun2
              (R, QuotientGroupRel(R, A, I),
               M),
             ProjFun2
              (R, QuotientGroupRel(R, A, J),
               M),
             QuotientBy(I), QuotientBy(J)) `
           \<langle>x, x\<rangle>"
        "\<lambda>s.  Fold(A, \<zero>, s)"
      using ringAssum QIJ_ring \<phi>_hom unfolding ring_homo_def by auto
    from crt.first_isomorphism_theorem[OF \<phi>_surj]
    obtain \<psi> where
      \<psi>_hom: "IsRingHomomor(\<psi>, crt.origin_ring.QuotientBy(crt.kernel),
                 QuotientGroupOp(R,A,crt.kernel),
                 ProjFun2(R,QuotientGroupRel(R,A,crt.kernel),M),
                 ?QI\<times>?QJ, ?DA, ?DM)"
      and \<psi>_bij: "\<psi> \<in> bij(crt.origin_ring.QuotientBy(crt.kernel), ?QI\<times>?QJ)"
      by blast
    have ker_is_IJ: "crt.kernel = ?IJ" using ker_eq .
    have quot_eq: "crt.origin_ring.QuotientBy(crt.kernel) = QuotientBy(?IJ)"
      using ker_is_IJ by (simp only:)
    with \<psi>_hom \<psi>_bij have "IsRingHomomor(\<psi>,  QuotientBy(?IJ),
                 QuotientGroupOp(R,A,crt.kernel),
                 ProjFun2(R,QuotientGroupRel(R,A,crt.kernel),M),
                 ?QI\<times>?QJ, ?DA, ?DM) \<and> \<psi> \<in> bij( QuotientBy(?IJ), ?QI\<times>?QJ)" by (simp only:)
    with ker_is_IJ have "IsRingHomomor(\<psi>,  QuotientBy(?IJ),
                 QuotientGroupOp(R,A,?IJ),
                 ProjFun2(R,QuotientGroupRel(R,A,?IJ),M),
                 ?QI\<times>?QJ, ?DA, ?DM) \<and> \<psi> \<in> bij( QuotientBy(?IJ), ?QI\<times>?QJ)" by (simp only:)
    then show ?thesis by auto
qed

end
