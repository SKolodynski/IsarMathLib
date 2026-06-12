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

section \<open>Direct product of groups\<close>

theory DirectProduct_ZF_1 imports DirectProduct_ZF Group_ZF

begin

text\<open>This theory proves that the direct product of two groups is a group.
  The result lives in the \<open>direct0\<close> locale, which already establishes the
  direct product as a binary operation and proves it inherits associativity and
  commutativity.  Here we add the group structure.\<close>

subsection\<open>Neutral element and inverse of the direct product\<close>

text\<open>The neutral element of the direct product is the pair of neutral elements.\<close>

lemma (in direct0) direct_product_neutral:
  assumes GP: "IsAgroup(G,P)" and HQ: "IsAgroup(H,Q)"
  shows "TheNeutralElement(G\<times>H,R) =
    \<langle>TheNeutralElement(G,P), TheNeutralElement(H,Q)\<rangle>"
proof -
  let ?eG = "TheNeutralElement(G,P)"
  let ?eH = "TheNeutralElement(H,Q)"
  interpret gG: group0 G P ?eG "\<lambda>x y. P`\<langle>x,y\<rangle>" "\<lambda>x. GroupInv(G,P)`x"
    "\<lambda>s. Fold(P,?eG,s)" "\<lambda>n x. Fold(P,?eG,{\<langle>k,x\<rangle>. k\<in>n})"
    using GP unfolding group0_def by auto
  interpret gH: group0 H Q ?eH "\<lambda>x y. Q`\<langle>x,y\<rangle>" "\<lambda>x. GroupInv(H,Q)`x"
    "\<lambda>s. Fold(Q,?eH,s)" "\<lambda>n x. Fold(Q,?eH,{\<langle>k,x\<rangle>. k\<in>n})"
    using HQ unfolding group0_def by auto
  from gG.group0_2_L2_1 have eG_in: "?eG \<in> G" by assumption 
  from gG.group0_2_L2_2 gG.group0_2_L2_3 have eG_neut:"\<forall>g\<in>G. P`\<langle>?eG,g\<rangle> = g \<and> P`\<langle>g,?eG\<rangle> = g"
    by blast
  from gH.group0_2_L2_1 have eH_in: "?eH \<in> H" by assumption
    from gH.group0_2_L2_2 gH.group0_2_L2_3 have eH_neut: "\<forall>h\<in>H. Q`\<langle>?eH,h\<rangle> = h \<and> Q`\<langle>h,?eH\<rangle> = h" by blast
  have e_in: "\<langle>?eG,?eH\<rangle> \<in> G\<times>H" using eG_in eH_in by safe
  have neut_prop: "\<forall>p\<in>G\<times>H. R`\<langle>\<langle>?eG,?eH\<rangle>,p\<rangle> = p \<and> R`\<langle>p,\<langle>?eG,?eH\<rangle>\<rangle> = p"
  proof
    fix p assume "p \<in> G\<times>H"
    then obtain g h where gr: "g \<in> G" and hr: "h \<in> H" and peq: "p = \<langle>g,h\<rangle>" by auto
    from gr hr e_in peq show "R`\<langle>\<langle>?eG,?eH\<rangle>,p\<rangle> = p \<and> R`\<langle>p,\<langle>?eG,?eH\<rangle>\<rangle> = p"
      using DirectProduct_ZF_1_L2 eG_neut eH_neut by (simp only:fst_conv snd_conv)
  qed
  have monoidR: "IsAmonoid(G\<times>H,R)"
    using GP HQ e_in neut_prop DirectProduct_ZF_2_L2
    unfolding IsAgroup_def IsAmonoid_def by blast
  interpret pR: monoid0 "G\<times>H" R "\<lambda>a b. R`\<langle>a,b\<rangle>"
    using monoidR unfolding monoid0_def by auto
  have "\<langle>?eG,?eH\<rangle> = TheNeutralElement(G\<times>H,R)"
    using pR.group0_1_L4 e_in neut_prop by blast
  thus ?thesis by (simp only: sym)
qed

subsection\<open>The direct product of groups is a group\<close>

text\<open>The direct product of two groups is a group.\<close>

theorem (in direct0) direct_product_group:
  assumes GP: "IsAgroup(G,P)" and HQ: "IsAgroup(H,Q)"
  shows "IsAgroup(G\<times>H, R)"
proof (rule definition_of_group)
  let ?eG = "TheNeutralElement(G,P)"
  let ?eH = "TheNeutralElement(H,Q)"
  interpret gG: group0 G P ?eG "\<lambda>x y. P`\<langle>x,y\<rangle>" "\<lambda>x. GroupInv(G,P)`x"
    "\<lambda>s. Fold(P,?eG,s)" "\<lambda>n x. Fold(P,?eG,{\<langle>k,x\<rangle>. k\<in>n})"
    using GP unfolding group0_def by auto
  interpret gH: group0 H Q ?eH "\<lambda>x y. Q`\<langle>x,y\<rangle>" "\<lambda>x. GroupInv(H,Q)`x"
    "\<lambda>s. Fold(Q,?eH,s)" "\<lambda>n x. Fold(Q,?eH,{\<langle>k,x\<rangle>. k\<in>n})"
    using HQ unfolding group0_def by auto
  from gG.group0_2_L2_1 have eG_in: "?eG \<in> G" by assumption 
  from gG.group0_2_L2_2 gG.group0_2_L2_3 have eG_neut:"\<forall>g\<in>G. P`\<langle>?eG,g\<rangle> = g \<and> P`\<langle>g,?eG\<rangle> = g"
    by blast
  from gH.group0_2_L2_1 have eH_in: "?eH \<in> H" by assumption
    from gH.group0_2_L2_2 gH.group0_2_L2_3 have eH_neut: "\<forall>h\<in>H. Q`\<langle>?eH,h\<rangle> = h \<and> Q`\<langle>h,?eH\<rangle> = h" by blast
  have e_in: "\<langle>?eG,?eH\<rangle> \<in> G\<times>H" using eG_in eH_in by safe
  have neut_prop: "\<forall>p\<in>G\<times>H. R`\<langle>\<langle>?eG,?eH\<rangle>,p\<rangle> = p \<and> R`\<langle>p,\<langle>?eG,?eH\<rangle>\<rangle> = p"
  proof
    fix p assume "p \<in> G\<times>H"
    then obtain g h where gr: "g \<in> G" and hr: "h \<in> H" and peq: "p = \<langle>g,h\<rangle>" by auto
    from gr hr e_in peq show "R`\<langle>\<langle>?eG,?eH\<rangle>,p\<rangle> = p \<and> R`\<langle>p,\<langle>?eG,?eH\<rangle>\<rangle> = p"
      using DirectProduct_ZF_1_L2 eG_neut eH_neut by (simp only:fst_conv snd_conv)
  qed
  show monoidR: "IsAmonoid(G\<times>H,R)"
    using GP HQ e_in neut_prop DirectProduct_ZF_2_L2
    unfolding IsAgroup_def IsAmonoid_def by blast
  show "\<forall>p\<in>G\<times>H. \<exists>b\<in>G\<times>H. R`\<langle>p,b\<rangle> = TheNeutralElement(G\<times>H,R)"
  proof
    fix p assume "p \<in> G\<times>H"
    then obtain g h where gr: "g \<in> G" and hr: "h \<in> H" and peq: "p = \<langle>g,h\<rangle>" by auto
    from gr have invG: "GroupInv(G,P)`g \<in> G" using gG.inverse_in_group by blast
    from hr have invH: "GroupInv(H,Q)`h \<in> H" using gH.inverse_in_group by blast
    have b_in: "\<langle>GroupInv(G,P)`g, GroupInv(H,Q)`h\<rangle> \<in> G\<times>H" using invG invH by blast
    have "R`\<langle>p, \<langle>GroupInv(G,P)`g, GroupInv(H,Q)`h\<rangle>\<rangle> = TheNeutralElement(G\<times>H,R)"
      using gr invG hr invH peq DirectProduct_ZF_1_L2
        gG.group0_2_L6[OF gr] gH.group0_2_L6[OF hr]
        direct_product_neutral[OF GP HQ] by (simp only:fst_conv snd_conv)
    with b_in show "\<exists>b\<in>G\<times>H. R`\<langle>p,b\<rangle> = TheNeutralElement(G\<times>H,R)" by blast
  qed
qed

text\<open>The group inverse in the direct product is computed componentwise.\<close>

lemma (in direct0) direct_product_inv:
  assumes GP: "IsAgroup(G,P)" and HQ: "IsAgroup(H,Q)"
    and gr: "g \<in> G" and hr: "h \<in> H"
  shows "GroupInv(G\<times>H,R)`\<langle>g,h\<rangle> = \<langle>GroupInv(G,P)`g, GroupInv(H,Q)`h\<rangle>"
proof -
  let ?eG = "TheNeutralElement(G,P)"
  let ?eH = "TheNeutralElement(H,Q)"
  let ?eGH = "TheNeutralElement(G\<times>H,R)"
  interpret gG: group0 G P ?eG "\<lambda>x y. P`\<langle>x,y\<rangle>" "\<lambda>x. GroupInv(G,P)`x"
    "\<lambda>s. Fold(P,?eG,s)" "\<lambda>n x. Fold(P,?eG,{\<langle>k,x\<rangle>. k\<in>n})"
    using GP  unfolding group0_def by auto
  interpret gH: group0 H Q ?eH "\<lambda>x y. Q`\<langle>x,y\<rangle>" "\<lambda>x. GroupInv(H,Q)`x"
    "\<lambda>s. Fold(Q,?eH,s)" "\<lambda>n x. Fold(Q,?eH,{\<langle>k,x\<rangle>. k\<in>n})"
    using HQ unfolding group0_def by auto
  interpret pGH: group0 "G\<times>H" R ?eGH "\<lambda>x y. R`\<langle>x,y\<rangle>" "\<lambda>x. GroupInv(G\<times>H,R)`x"
    "\<lambda>s. Fold(R,?eGH,s)" "\<lambda>n x. Fold(R,?eGH,{\<langle>k,x\<rangle>. k\<in>n})"
    using direct_product_group[OF GP HQ] unfolding group0_def by auto
  from gr have invG: "GroupInv(G,P)`g \<in> G" using gG.inverse_in_group by blast
  from hr have invH: "GroupInv(H,Q)`h \<in> H" using gH.inverse_in_group by blast
  have gh_in: "\<langle>g,h\<rangle> \<in> G\<times>H" using gr hr by simp
  have b_in: "\<langle>GroupInv(G,P)`g, GroupInv(H,Q)`h\<rangle> \<in> G\<times>H" using invG invH by blast
  have step: "R`\<langle>\<langle>g,h\<rangle>, \<langle>GroupInv(G,P)`g, GroupInv(H,Q)`h\<rangle>\<rangle> = ?eGH"
    using gr invG hr invH DirectProduct_ZF_1_L2
      gG.group0_2_L6[OF gr] gH.group0_2_L6[OF hr]
      direct_product_neutral[OF GP HQ] by (simp only:fst_conv snd_conv)
  from gh_in b_in step have
    "\<langle>GroupInv(G,P)`g, GroupInv(H,Q)`h\<rangle> = GroupInv(G\<times>H,R)`\<langle>g,h\<rangle>"
    using pGH.group0_2_L9 by (simp only:)
  thus ?thesis by (simp only:sym)
qed

end
