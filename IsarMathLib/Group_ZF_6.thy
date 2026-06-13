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

section \<open>Group homomorphisms and kernels\<close>

theory Group_ZF_6 imports Group_ZF_4

begin

text\<open>The natural quotient map $q: G \to G/H$ (for a normal subgroup $H$) is a group
  homomorphism. Recall that $\lambda x\in X. p(x)$ is an alternative notation for a
  function defined as a set of pairs, see lemma \<open>lambda_fun_alt\<close> in \<open>func1.thy\<close>.\<close>

lemma (in group0) quotient_map:
  assumes "IsAnormalSubgroup(G,P,H)"
  defines "r \<equiv> QuotientGroupRel(G,P,H)" and "q \<equiv> \<lambda>x\<in>G. QuotientGroupRel(G,P,H)``{x}"
  shows "Homomor(q,G,P,G//r,QuotientGroupOp(G,P,H))"
  using groupAssum assms group_op_closed lam_funtype lamE EquivClass_1_L10
    Group_ZF_2_4_L3 Group_ZF_2_4_L5A Group_ZF_2_4_T1
  unfolding IsAnormalSubgroup_def QuotientGroupOp_def Homomor_def IsMorphism_def
  by simp

subsection\<open>The group homomorphism locale\<close>

text\<open>The next locale packages two groups together with a group homomorphism between them.
  We fix an origin group $(G, P)$ and a target group $(H, F)$ with homomorphism
  $f: G \to H$, and introduce subscripted notation for both groups.\<close>

locale group_homo =
  fixes G P H F f

  assumes origin: "IsAgroup(G, P)"
    and target: "IsAgroup(H, F)"
    and hom: "Homomor(f, G, P, H, F)"

  fixes neut ("\<one>\<^sub>G")
  defines neut_def [simp]: "\<one>\<^sub>G \<equiv> TheNeutralElement(G, P)"

  fixes groper (infixl "\<cdot>\<^sub>G" 70)
  defines groper_def [simp]: "x \<cdot>\<^sub>G y \<equiv> P`\<langle>x, y\<rangle>"

  fixes inv ("_\<inverse>\<^sub>G" [90] 91)
  defines inv_def [simp]: "x\<inverse>\<^sub>G \<equiv> GroupInv(G, P)`x"

  fixes listprod ("\<Prod>\<^sub>G _" 70)
  defines listprod_def [simp]: "\<Prod>\<^sub>G s \<equiv> Fold(P, \<one>\<^sub>G, s)"

  fixes pow
  defines pow_def [simp]: "pow(n, x) \<equiv> \<Prod>\<^sub>G {\<langle>k, x\<rangle>. k \<in> n}"

  fixes neutH ("\<one>\<^sub>H")
  defines neutH_def [simp]: "\<one>\<^sub>H \<equiv> TheNeutralElement(H, F)"

  fixes groperH (infixl "\<cdot>\<^sub>H" 70)
  defines groperH_def [simp]: "x \<cdot>\<^sub>H y \<equiv> F`\<langle>x, y\<rangle>"

  fixes invH ("_\<inverse>\<^sub>H" [90] 91)
  defines invH_def [simp]: "x\<inverse>\<^sub>H \<equiv> GroupInv(H, F)`x"

  fixes listprodH ("\<Prod>\<^sub>H _" 70)
  defines listprodH_def [simp]: "\<Prod>\<^sub>H s \<equiv> Fold(F, \<one>\<^sub>H, s)"

  fixes powH
  defines powH_def [simp]: "powH(n, x) \<equiv> \<Prod>\<^sub>H {\<langle>k, x\<rangle>. k \<in> n}"

text\<open>\<open>ker\<close> denotes the kernel of $f$, i.e. the preimage of the neutral element
  of the target group.\<close>

abbreviation (in group_homo) kernel ("ker" 90) where
  "ker \<equiv> f-``{\<one>\<^sub>H}"

text\<open>The theorems proven in the \<open>group0\<close> context are valid in the \<open>group_homo\<close>
  context when applied to the origin group $G$.\<close>

sublocale group_homo < org: group0 G P neut groper inv listprod pow
  using origin unfolding group0_def groper_def inv_def neut_def by auto

text\<open>The theorems proven in the \<open>group0\<close> context are valid in the \<open>group_homo\<close>
  context when applied to the target group $H$.\<close>

sublocale group_homo < tgt: group0 H F neutH groperH invH listprodH powH
  using target unfolding group0_def groperH_def invH_def neutH_def by auto

text\<open>$f$ is a function from $G$ to $H$.\<close>

lemma (in group_homo) f_is_fun: shows "f: G \<rightarrow> H"
  using hom unfolding Homomor_def by simp

text\<open>$f$ is a group homomorphism: $f(x \cdot_G y) = f(x) \cdot_H f(y)$.\<close>

lemma (in group_homo) f_hom:
  assumes "x \<in> G" "y \<in> G"
  shows "f`(x \<cdot>\<^sub>G y) = f`x \<cdot>\<^sub>H f`y"
  using hom assms homomor_eq by simp

text\<open>$f$ maps the neutral element of $G$ to the neutral element of $H$.\<close>

lemma (in group_homo) f_neutral: shows "f`(\<one>\<^sub>G) = \<one>\<^sub>H"
proof -
  from org.group0_2_L2 have eG: "\<one>\<^sub>G \<in> G" and neut: "\<one>\<^sub>G \<cdot>\<^sub>G \<one>\<^sub>G = \<one>\<^sub>G" by simp_all
  from eG have fval: "f`(\<one>\<^sub>G) \<in> H" using f_is_fun apply_type by simp
  have eq: "f`(\<one>\<^sub>G) = f`(\<one>\<^sub>G) \<cdot>\<^sub>H f`(\<one>\<^sub>G)"
    using f_hom[OF eG eG] neut by auto 
  then have "((f`(\<one>\<^sub>G))¯⇩H)\<cdot>\<^sub>H(f`(\<one>\<^sub>G)) = ((f`(\<one>\<^sub>G))¯⇩H)\<cdot>\<^sub>H(f`(\<one>\<^sub>G) \<cdot>\<^sub>H f`(\<one>\<^sub>G))" by auto
  with fval show ?thesis
    using tgt.group0_2_L6 tgt.group_oper_assoc tgt.inverse_in_group
      tgt.group0_2_L2 by auto
qed

text\<open>$f$ commutes with the group inverse: $f(x^{-1}) = f(x)^{-1}$.\<close>

lemma (in group_homo) f_inv:
  assumes "x \<in> G"
  shows "f`(x\<inverse>\<^sub>G) = (f`x)\<inverse>\<^sub>H"
proof -
  from assms have invxG: "x\<inverse>\<^sub>G \<in> G" using org.inverse_in_group by simp
  from assms have fxH: "f`x \<in> H" using f_is_fun apply_type by simp
  from invxG have finvH: "f`(x\<inverse>\<^sub>G) \<in> H" using f_is_fun apply_type by simp
  have "f`x \<cdot>\<^sub>H f`(x\<inverse>\<^sub>G) = f`(x \<cdot>\<^sub>G x\<inverse>\<^sub>G)"
    using assms invxG f_hom by simp
  also from assms have "\<dots> = f`(\<one>\<^sub>G)"
    using org.group0_2_L6 by simp
  also have "\<dots> = \<one>\<^sub>H" using f_neutral by simp
  finally have "f`x \<cdot>\<^sub>H f`(x\<inverse>\<^sub>G) = \<one>\<^sub>H" .
  with fxH finvH show ?thesis using tgt.group0_2_L9 by simp
qed

text\<open>The preimage of a subgroup of $H$ is a subgroup of $G$.\<close>

lemma (in group_homo) preimage_is_subgroup:
  assumes sub: "IsAsubgroup(K, F)"
  shows "IsAsubgroup(f-``(K), P)"
proof -
  from sub have KH: "K \<subseteq> H" using tgt.group0_3_L2 by simp
  from sub have neutH_K: "\<one>\<^sub>H \<in> K" using tgt.group0_3_L5 by simp
  from org.group0_2_L2 f_neutral neutH_K have ne: "f-``(K) \<noteq> 0"
    using f_is_fun func1_1_L15 by auto
  have subG: "f-``(K) \<subseteq> G" using f_is_fun func1_1_L3 by simp
  have inv_cl: "\<forall>x \<in> f-``(K). x\<inverse>\<^sub>G \<in> f-``(K)"
  proof
    fix x assume "x \<in> f-``(K)"
    with f_is_fun have xG: "x \<in> G" and fxK: "f`x \<in> K" using func1_1_L15 by auto
    from xG have "f`(x\<inverse>\<^sub>G) = (f`x)\<inverse>\<^sub>H" using f_inv by simp
    also from sub fxK have "(f`x)\<inverse>\<^sub>H \<in> K" using tgt.group0_3_T3A by simp
    finally have "f`(x\<inverse>\<^sub>G) \<in> K" .
    with xG show "x\<inverse>\<^sub>G \<in> f-``(K)"
      using f_is_fun org.inverse_in_group func1_1_L15 by simp
  qed
  have op_cl: "f-``(K) {is closed under} P"
    unfolding IsOpClosed_def
  proof (intro ballI)
    fix x y assume "x \<in> f-``(K)" "y \<in> f-``(K)"
    with f_is_fun have xG: "x \<in> G" "f`x \<in> K" and yG: "y \<in> G" "f`y \<in> K"
      using func1_1_L15 by auto
    from xG yG have "f`(x \<cdot>\<^sub>G y) = f`x \<cdot>\<^sub>H f`y" using f_hom by simp
    also from sub xG(2) yG(2) have "f`x \<cdot>\<^sub>H f`y \<in> K"
      using tgt.group0_3_L6 by simp
    finally have "f`(x \<cdot>\<^sub>G y) \<in> K" .
    with xG(1) yG(1) show "P`\<langle>x,y\<rangle> \<in> f-``(K)"
      using f_is_fun org.group_op_closed func1_1_L15 by simp
  qed
  from subG ne op_cl inv_cl show ?thesis using org.group0_3_T3 by simp
qed

text\<open>The image of a subgroup of $G$ is a subgroup of $H$.\<close>

lemma (in group_homo) image_is_subgroup:
  assumes sub: "IsAsubgroup(K, P)"
  shows "IsAsubgroup(f``K, F)"
proof -
  from sub have KG: "K \<subseteq> G" using org.group0_3_L2 by simp
  have subH: "f``K \<subseteq> H" using f_is_fun KG func_imagedef apply_type by auto
  from sub KG have neutK: "\<one>\<^sub>G \<in> K" using org.group0_3_L5 by simp
  from neutK KG have "f`(\<one>\<^sub>G) \<in> f``K"
    using f_is_fun func_imagedef by auto
  hence ne: "f``K \<noteq> 0" by blast
  have inv_cl: "\<forall>x \<in> f``K. x\<inverse>\<^sub>H \<in> f``K"
  proof
    fix x assume "x \<in> f``K"
    with f_is_fun KG obtain k where kK: "k \<in> K" and xfk: "x = f`k"
      using func_imagedef by auto
    from kK KG have kG: "k \<in> G" by auto
    from sub kK have "k\<inverse>\<^sub>G \<in> K" using org.group0_3_T3A by simp
    with KG have "f`(k\<inverse>\<^sub>G) \<in> f``K" using f_is_fun func_imagedef by auto
    with kG xfk show "x\<inverse>\<^sub>H \<in> f``K" using f_inv by simp
  qed
  have op_cl: "f``K {is closed under} F"
    unfolding IsOpClosed_def
  proof (intro ballI)
    fix x y assume "x \<in> f``K" "y \<in> f``K"
    with f_is_fun KG obtain kx ky where
      kx: "kx \<in> K" "x = f`kx" and ky: "ky \<in> K" "y = f`ky"
      using func_imagedef by auto
    from sub kx(1) ky(1) have "kx \<cdot>\<^sub>G ky \<in> K" using org.group0_3_L6 by simp
    with KG have "f`(kx \<cdot>\<^sub>G ky) \<in> f``K" using f_is_fun func_imagedef by auto
    with kx ky KG show "F`\<langle>x,y\<rangle> \<in> f``K" using f_hom[of kx ky] by force
  qed
  from subH ne op_cl inv_cl show ?thesis using tgt.group0_3_T3 by simp
qed

text\<open>The image of $G$ under $f$ is a subgroup of $H$.\<close>

lemma (in group_homo) image_is_group:
  shows "IsAsubgroup(f``G, F)"
proof -
  from origin have "restrict(P, G \<times> G) = P"
    using org.group_oper_fun restrict_domain unfolding group0_def by blast
  with origin have "IsAsubgroup(G, P)"
    unfolding IsAsubgroup_def IsAgroup_def by auto
  thus ?thesis using image_is_subgroup by simp
qed

text\<open>Membership in the kernel: $x \in G$ belongs to $\mathrm{ker}(f)$ iff
  $f(x) = \mathbf{1}_H$.\<close>

lemma (in group_homo) kernel_mem:
  assumes "x \<in> G"
  shows "x \<in> ker \<longleftrightarrow> f`x = \<one>\<^sub>H"
  using f_is_fun assms func1_1_L15 by auto

text\<open>The kernel is a subset of $G$.\<close>

lemma (in group_homo) kernel_in_G: shows "ker \<subseteq> G"
  using f_is_fun func1_1_L3 by simp

text\<open>The neutral element of $G$ belongs to the kernel.\<close>

lemma (in group_homo) neutral_in_kernel: shows "\<one>\<^sub>G \<in> ker"
  using f_is_fun org.group0_2_L2 f_neutral kernel_mem by simp

text\<open>The preimage of a normal subgroup of $H$ is a normal subgroup of $G$.\<close>

theorem (in group_homo) preimage_normal_subgroup:
  assumes "IsAnormalSubgroup(H, F, K)"
  shows "IsAnormalSubgroup(G, P, f-``(K))"
proof -
  from assms have sub: "IsAsubgroup(K, F)"
    unfolding IsAnormalSubgroup_def by simp
  from sub have prsub: "IsAsubgroup(f-``(K), P)"
    using preimage_is_subgroup by simp
  from sub have KH: "K \<subseteq> H" using tgt.group0_3_L2 by simp
  have "\<forall>g\<in>G. {P`\<langle>g, P`\<langle>h, GroupInv(G, P)`g\<rangle>\<rangle>. h \<in> f-``(K)} \<subseteq> f-``(K)"
  proof
    fix g assume gG: "g \<in> G"
    { fix h assume "h \<in> {P`\<langle>g, P`\<langle>h, GroupInv(G, P)`g\<rangle>\<rangle>. h \<in> f-``(K)}"
      then obtain k where
        k: "h = P`\<langle>g, P`\<langle>k, GroupInv(G, P)`g\<rangle>\<rangle>" "k \<in> f-``(K)"
        by auto
      from f_is_fun k(2) have kG: "k \<in> G" using func1_1_L3 by blast
      from f_is_fun k(2) have fkK: "f`k \<in> K" using func1_1_L15 by simp
      from fkK KH have fkH: "f`k \<in> H" by auto
      from gG have fgH: "f`g \<in> H" using f_is_fun apply_type by simp
      from gG have invgG: "GroupInv(G, P)`g \<in> G"
        using org.inverse_in_group by simp
      from kG invgG have pkig: "P`\<langle>k, GroupInv(G, P)`g\<rangle> \<in> G"
        using org.group_op_closed by simp
      from gG pkig have hG: "h \<in> G"
        using org.group_op_closed k(1) by simp
      from gG kG invgG pkig have step1:
        "f`(P`\<langle>g, P`\<langle>k, GroupInv(G, P)`g\<rangle>\<rangle>) =
         F`\<langle>f`g, F`\<langle>f`k, GroupInv(H, F)`(f`g)\<rangle>\<rangle>"
        using f_hom f_inv by simp
      from assms fkK fgH have "F`\<langle>F`\<langle>f`g, f`k\<rangle>, GroupInv(H, F)`(f`g)\<rangle> \<in> K"
        unfolding IsAnormalSubgroup_def by auto
      moreover from fgH fkH have
        "F`\<langle>f`g, F`\<langle>f`k, GroupInv(H, F)`(f`g)\<rangle>\<rangle> =
         F`\<langle>F`\<langle>f`g, f`k\<rangle>, GroupInv(H, F)`(f`g)\<rangle>"
        using tgt.inverse_in_group tgt.group_oper_assoc by simp
      ultimately have "f`h \<in> K" using step1 k(1) by simp
      with f_is_fun hG have "h \<in> f-``(K)" using func1_1_L15 by simp
    }
    thus "{P`\<langle>g, P`\<langle>h, GroupInv(G, P)`g\<rangle>\<rangle>. h \<in> f-``(K)} \<subseteq> f-``(K)"
      by blast
  qed
  with origin prsub show ?thesis using org.cont_conj_is_normal by simp
qed

text\<open>The kernel is a normal subgroup of $G$.\<close>

theorem (in group_homo) kernel_normal_subgroup:
  shows "IsAnormalSubgroup(G, P, ker)"
proof -
  from target have "\<one>\<^sub>H \<in> H" using tgt.group0_2_L2 by simp
  hence "IsAnormalSubgroup(H, F, {\<one>\<^sub>H})"
    using tgt.trivial_normal_subgroup by simp
  thus ?thesis using preimage_normal_subgroup by simp
qed

text\<open>In particular, the kernel is a subgroup of $G$.\<close>

corollary (in group_homo) kernel_is_subgroup:
  shows "IsAsubgroup(ker, P)"
  using kernel_normal_subgroup unfolding IsAnormalSubgroup_def by simp

text\<open>The inverse of a bijective homomorphism is a homomorphism.\<close>

theorem (in group_homo) bijective_hom_inverse:
  assumes bij: "f \<in> bij(G, H)"
  shows "Homomor(converse(f), H, F, G, P)"
proof -
  { fix h\<^sub>1 h\<^sub>2 assume "h\<^sub>1 \<in> H" "h\<^sub>2 \<in> H"
    with bij obtain g\<^sub>1 g\<^sub>2 where
      g1: "g\<^sub>1 \<in> G" "f`g\<^sub>1 = h\<^sub>1" and g2: "g\<^sub>2 \<in> G" "f`g\<^sub>2 = h\<^sub>2"
      unfolding bij_def surj_def by blast
    from g1(1) g2(1) have
      "converse(f)`(f`(g\<^sub>1 \<cdot>\<^sub>G g\<^sub>2)) = converse(f)`(f`g\<^sub>1 \<cdot>\<^sub>H f`g\<^sub>2)"
      using f_hom by simp
    with bij g1 g2 have
      "P`\<langle>converse(f)`h\<^sub>1, converse(f)`h\<^sub>2\<rangle> = converse(f)`(F`\<langle>h\<^sub>1,h\<^sub>2\<rangle>)"
      using left_inverse org.group_op_closed unfolding bij_def by auto
  }
  with bij show ?thesis using bij_converse_bij bij_is_fun
    unfolding Homomor_def IsMorphism_def by simp
qed

text\<open>The first isomorphism theorem: $f$ induces a bijective homomorphism
  $G/\mathrm{ker}(f) \cong f(G)$.\<close>

theorem (in group_homo) first_isomorphism_theorem:
  defines "r \<equiv> QuotientGroupRel(G, P, ker)"
      and "\<P> \<equiv> QuotientGroupOp(G, P, ker)"
  shows "\<exists>\<ff>. Homomor(\<ff>, G//r, \<P>, f``G, restrict(F, f``G \<times> f``G)) \<and>
              \<ff> \<in> bij(G//r, f``G)"
proof -
  let ?\<ff> = "{\<langle>r``{g}, f`g\<rangle>. g \<in> G}"
  from org.Group_ZF_2_4_L3 kernel_normal_subgroup have equiv: "equiv(G, r)"
    unfolding r_def IsAnormalSubgroup_def by simp
  from r_def f_is_fun have "?\<ff> \<in> Pow((G//r) \<times> f``G)"
    unfolding quotient_def using func_imagedef by auto
  moreover have "(G//r) \<subseteq> domain(?\<ff>)" unfolding domain_def quotient_def by auto
  moreover
  { fix x y t assume A: "\<langle>x,y\<rangle> \<in> ?\<ff>" "\<langle>x,t\<rangle> \<in> ?\<ff>"
    then obtain g\<^sub>y g\<^sub>r where
      "\<langle>x,y\<rangle> = \<langle>r``{g\<^sub>y},f`g\<^sub>y\<rangle>" "\<langle>x,t\<rangle> = \<langle>r``{g\<^sub>r},f`g\<^sub>r\<rangle>" "g\<^sub>r \<in> G" "g\<^sub>y \<in> G" by auto
    hence B: "r``{g\<^sub>y} = r``{g\<^sub>r}" "y = f`g\<^sub>y" "t = f`g\<^sub>r" by auto
    from f_is_fun \<open>g\<^sub>y \<in> G\<close> \<open>g\<^sub>r \<in> G\<close> B(2,3) have yH: "y \<in> H" and tH: "t \<in> H"
      using apply_type by simp_all
    with equiv \<open>g\<^sub>r \<in> G\<close> B(1) have "\<langle>g\<^sub>y,g\<^sub>r\<rangle> \<in> r" using same_image_equiv by simp
    with r_def f_is_fun have
      "f`(P`\<langle>g\<^sub>y, GroupInv(G,P)`g\<^sub>r\<rangle>) = TheNeutralElement(H,F)"
      unfolding QuotientGroupRel_def using func1_1_L15 by simp
    with f_hom f_inv[of "g\<^sub>r"]  \<open>g\<^sub>y \<in> G\<close> \<open>g\<^sub>r \<in> G\<close>
    have "F`\<langle>f`(g\<^sub>y),GroupInv(H,F)`(f`(g\<^sub>r))\<rangle> = TheNeutralElement(H,F)"
      using org.inverse_in_group
      by auto
    with B(2,3) yH tH have "y = t"
      using tgt.group0_2_L11A[of y t] by auto
  } hence "\<forall>x y. \<langle>x,y\<rangle> \<in> ?\<ff> \<longrightarrow> (\<forall>z. \<langle>x,z\<rangle> \<in> ?\<ff> \<longrightarrow> y = z)" by auto
  ultimately have ff_fun: "?\<ff>: G//r \<rightarrow> f``G" unfolding Pi_def function_def by auto
  { fix a\<^sub>1 a\<^sub>2 assume AS: "a\<^sub>1 \<in> G//r" "a\<^sub>2 \<in> G//r"
    then obtain g\<^sub>1 g\<^sub>2 where g1: "g\<^sub>1 \<in> G" and g2: "g\<^sub>2 \<in> G"
        and a: "a\<^sub>1 = r``{g\<^sub>1}" "a\<^sub>2 = r``{g\<^sub>2}"
      unfolding quotient_def by auto
    with origin equiv have "\<langle>\<P>`\<langle>a\<^sub>1,a\<^sub>2\<rangle>, f`(P`\<langle>g\<^sub>1,g\<^sub>2\<rangle>)\<rangle> \<in> ?\<ff>"
      using Group_ZF_2_4_L5A kernel_normal_subgroup
        org.Group_ZF_2_2_L2 org.group_op_closed
      unfolding \<P>_def QuotientGroupOp_def r_def by auto
    with ff_fun have eq: "?\<ff>`(\<P>`\<langle>a\<^sub>1,a\<^sub>2\<rangle>) = f`(P`\<langle>g\<^sub>1,g\<^sub>2\<rangle>)" using apply_equality by simp
    from g1 g2 a have p1: "\<langle>a\<^sub>1,f`g\<^sub>1\<rangle> \<in> ?\<ff>" and p2: "\<langle>a\<^sub>2,f`g\<^sub>2\<rangle> \<in> ?\<ff>" by auto
    with ff_fun have "?\<ff>`(a\<^sub>1) = f`(g\<^sub>1)" "?\<ff>`(a\<^sub>2) = f`(g\<^sub>2)"
      using apply_equality by auto
    with g1 g2 eq have "F`\<langle>?\<ff>`a\<^sub>1, ?\<ff>`a\<^sub>2\<rangle> = ?\<ff>`(\<P>`\<langle>a\<^sub>1,a\<^sub>2\<rangle>)"
      using f_hom unfolding Homomor_def IsMorphism_def by simp
    moreover from AS ff_fun have "?\<ff>`a\<^sub>1 \<in> f``G" "?\<ff>`a\<^sub>2 \<in> f``G" using apply_type by auto
    ultimately have "restrict(F,f``G\<times>f``G)`\<langle>?\<ff>`a\<^sub>1,?\<ff>`a\<^sub>2\<rangle> = ?\<ff>`(\<P>`\<langle>a\<^sub>1,a\<^sub>2\<rangle>)" by simp
  } hence rr: "\<forall>a\<^sub>1\<in>G//r. \<forall>a\<^sub>2\<in>G//r.
      restrict(F,f``G\<times>f``G)`\<langle>?\<ff>`a\<^sub>1,?\<ff>`a\<^sub>2\<rangle> = ?\<ff>`(\<P>`\<langle>a\<^sub>1,a\<^sub>2\<rangle>)" by simp
  with ff_fun have HOM: "Homomor(?\<ff>,G//r,\<P>,f``G,restrict(F,f``G\<times>f``G))"
    unfolding Homomor_def IsMorphism_def by simp
  from origin kernel_normal_subgroup have Gq: "IsAgroup(G//r, \<P>)"
    using Group_ZF_2_4_T1 unfolding \<P>_def IsAnormalSubgroup_def r_def by simp
  from image_is_group have fGq: "IsAgroup(f``G, restrict(F,f``G\<times>f``G))"
    unfolding IsAsubgroup_def by simp
  { fix b\<^sub>1 b\<^sub>2 assume AS: "?\<ff>`b\<^sub>1 = ?\<ff>`b\<^sub>2" "b\<^sub>1 \<in> G//r" "b\<^sub>2 \<in> G//r"
    from Gq AS(3) have invb2: "GroupInv(G//r,\<P>)`b\<^sub>2 \<in> G//r"
      using group0.inverse_in_group unfolding group0_def by simp
    with Gq AS(2) have I: "\<P>`\<langle>b\<^sub>1, GroupInv(G//r,\<P>)`b\<^sub>2\<rangle> \<in> G//r"
      using group0.group_op_closed unfolding group0_def by auto
    then obtain g where gG: "g \<in> G"
        and gg: "\<P>`\<langle>b\<^sub>1, GroupInv(G//r,\<P>)`b\<^sub>2\<rangle> = r``{g}"
      unfolding quotient_def by auto
    from gG have "\<langle>r``{g},f`g\<rangle> \<in> ?\<ff>" by blast
    with ff_fun gg have E: "?\<ff>`(\<P>`\<langle>b\<^sub>1,GroupInv(G//r,\<P>)`b\<^sub>2\<rangle>) = f`g"
      using apply_equality by simp
    from ff_fun invb2 have pp: "?\<ff>`(GroupInv(G//r,\<P>)`b\<^sub>2) \<in> f``G" using apply_type by simp
    from ff_fun AS(2,3) have fff: "?\<ff>`b\<^sub>1 \<in> f``G" "?\<ff>`b\<^sub>2 \<in> f``G" using apply_type by simp_all
    from fff(1) pp have EE:
      "F`\<langle>?\<ff>`b\<^sub>1, ?\<ff>`(GroupInv(G//r,\<P>)`b\<^sub>2)\<rangle> =
       restrict(F,f``G\<times>f``G)`\<langle>?\<ff>`b\<^sub>1, ?\<ff>`(GroupInv(G//r,\<P>)`b\<^sub>2)\<rangle>"
      by auto
    from f_is_fun have fGH: "f``G \<subseteq> H" using func1_1_L6(2) by simp
    with fff have fffH: "?\<ff>`b\<^sub>1 \<in> H" "?\<ff>`b\<^sub>2 \<in> H" by auto
    have "?\<ff>`(GroupInv(G//r,\<P>)`b\<^sub>2) = GroupInv(f``G,restrict(F,f``G \<times> f``G))`(?\<ff>`b\<^sub>2)"
      using group_homo.f_inv[of "G//r" \<P> "f``G" "restrict(F,f``G\<times>f``G)"  ?\<ff>] 
        HOM image_is_group Gq AS(3) unfolding group_homo_def IsAsubgroup_def by auto
    moreover from rr AS(2) invb2 have "restrict(F, f `` G × f `` G) `
          ⟨?\<ff> ` b⇩1,
           ?\<ff> ` (GroupInv(G // r, 𝒫) `b⇩2)⟩ =
          ?\<ff> `
          (𝒫 ` ⟨b⇩1, GroupInv(G // r, 𝒫) `b⇩2⟩)" 
      by auto moreover
    note AS(1) ultimately
    have "restrict(F, f `` G × f `` G) `
          ⟨?\<ff> ` b⇩2,
            GroupInv(f``G,restrict(F,f``G \<times> f``G))`(?\<ff>`b⇩2)⟩ =
          f`g" using E by auto
    then have "TheNeutralElement(f``G, restrict(F,f``G\<times>f``G)) = f`g"
      using fff(2) group0.group0_2_L6[of "f``G" "restrict(F,f``G\<times>f``G)" "?\<ff>`b\<^sub>2"] image_is_group unfolding IsAsubgroup_def
      group0_def by auto
    then have "TheNeutralElement(H,F) = f`g" using tgt.group0_3_L4 image_is_group
      by simp
    with f_is_fun gG have "g \<in> ker" using func1_1_L15 by simp
    with origin gG gg have "\<P>`\<langle>b\<^sub>1,GroupInv(G//r,\<P>)`b\<^sub>2\<rangle> = TheNeutralElement(G//r,\<P>)"
      using org.Group_ZF_2_4_L5E[OF kernel_normal_subgroup, of g r " TheNeutralElement(G // r, 𝒫)"]
      unfolding r_def group0_def \<P>_def by auto
    with AS(2,3) Gq have "b\<^sub>1 = b\<^sub>2" using group0.group0_2_L11A unfolding group0_def by auto
  } with ff_fun have "?\<ff> \<in> inj(G//r, f``G)" unfolding inj_def by blast
  moreover
  { fix m assume "m \<in> f``G"
    with f_is_fun obtain g where "g \<in> G" "m = f`g" using func_imagedef by auto
    hence "\<langle>r``{g},m\<rangle> \<in> ?\<ff>" by blast
    with ff_fun have "?\<ff>`(r``{g}) = m" using apply_equality by auto
    with \<open>g \<in> G\<close> have "\<exists>A \<in> G//r. ?\<ff>`A = m" unfolding quotient_def by auto
  }
  ultimately have "?\<ff> \<in> bij(G//r, f``G)" unfolding bij_def surj_def using ff_fun by blast
  with HOM show ?thesis by blast
qed

text\<open>A group homomorphism is injective if and only if its kernel is trivial.\<close>

theorem (in group_homo) kernel_trivial_iff_injective:
  shows "f \<in> inj(G, H) \<longleftrightarrow> ker = {\<one>\<^sub>G}"
proof
  assume inj: "f \<in> inj(G, H)"
  show "ker = {\<one>\<^sub>G}"
  proof
    show "ker \<subseteq> {\<one>\<^sub>G}"
    proof
      fix x assume xker: "x \<in> ker"
      with f_is_fun have xG: "x \<in> G" using kernel_in_G by auto
      from xker xG have fx: "f`x = \<one>\<^sub>H" using kernel_mem by simp
      from xG org.group0_2_L2 f_neutral fx inj
      show "x \<in> {\<one>\<^sub>G}" unfolding inj_def by auto
    qed
    show "{\<one>\<^sub>G} \<subseteq> ker" using neutral_in_kernel by simp
  qed
next
  assume triv: "ker = {\<one>\<^sub>G}"
  { fix x y assume xG: "x \<in> G" and yG: "y \<in> G" and eq: "f`x = f`y"
    from yG have invyG: "y\<inverse>\<^sub>G \<in> G" using org.inverse_in_group by simp
    from xG invyG have prodG: "x \<cdot>\<^sub>G y\<inverse>\<^sub>G \<in> G" using org.group_op_closed by simp
    from xG invyG have step1: "f`(x \<cdot>\<^sub>G y\<inverse>\<^sub>G) = f`x \<cdot>\<^sub>H f`(y\<inverse>\<^sub>G)"
      using f_hom by simp
    from yG have step2: "f`(y\<inverse>\<^sub>G) = (f`y)\<inverse>\<^sub>H" using f_inv by simp
    from f_is_fun yG have fyH: "f`y \<in> H" using apply_type by simp
    from fyH have step3: "f`y \<cdot>\<^sub>H (f`y)\<inverse>\<^sub>H = \<one>\<^sub>H"
      using tgt.group0_2_L6 by simp
    from step1 step2 step3 eq have feq: "f`(x \<cdot>\<^sub>G y\<inverse>\<^sub>G) = \<one>\<^sub>H" by simp
    from prodG feq have "x \<cdot>\<^sub>G y\<inverse>\<^sub>G \<in> ker" using kernel_mem by simp
    with triv have "x \<cdot>\<^sub>G y\<inverse>\<^sub>G = \<one>\<^sub>G" by simp
    with xG yG have "x = y" using org.group0_2_L11A by simp
  }
  with f_is_fun show "f \<in> inj(G, H)" unfolding inj_def by auto
qed

subsection\<open>Exact sequences at a term\<close>

text\<open>A pair of composable group homomorphisms $A \xrightarrow{f} B \xrightarrow{g} C$
  is \emph{exact at $B$} when the image of $f$ equals the kernel of $g$.\<close>

definition IsExactAt :: "[i, i, i, i, i] \<Rightarrow> o" where
  "IsExactAt(f, A, g, C, Q) \<equiv> f``A = g-``{TheNeutralElement(C, Q)}"

text\<open>A locale for two composable group homomorphisms $f\colon A \to B$ and
  $g\colon B \to C$. Lemmas are proved using the two \<open>group_homo\<close> instances
  directly rather than via sublocale inheritance.\<close>

locale two_group_homo =
  fixes A P B F C Q f g
  assumes hf: "group_homo(A, P, B, F, f)"
    and hg: "group_homo(B, F,C, Q, g)"

abbreviation (in two_group_homo) ExactAtB where
  "ExactAtB \<equiv> IsExactAt(f, A, g, C, Q)"


sublocale two_group_homo < second_homo: group_homo B F C Q g
  "TheNeutralElement(B,F)" "\<lambda>x y. F`\<langle>x,y\<rangle>"
  "\<lambda>x. GroupInv(B,F)`x" "\<lambda>s.  Fold(F, TheNeutralElement(B, F), s)"
  "\<lambda>n x.  Fold(F, TheNeutralElement(B, F), {\<langle>k, x\<rangle> . k \<in> n})"
  "TheNeutralElement(C,Q)" "\<lambda>x y. Q`\<langle>x,y\<rangle>"
  "\<lambda>x. GroupInv(C,Q)`x" "\<lambda>s.  Fold(Q, TheNeutralElement(C, Q), s)"
  "\<lambda>n x.  Fold(Q, TheNeutralElement(C, Q), {\<langle>k, x\<rangle> . k \<in> n})"
  apply auto using hg by auto

sublocale two_group_homo < first_homo: group_homo A P B F f
  "TheNeutralElement(A,P)" "\<lambda>x y. P`\<langle>x,y\<rangle>"
  "\<lambda>x. GroupInv(A,P)`x" "\<lambda>s.  Fold(P, TheNeutralElement(A, P), s)"
  "\<lambda>n x.  Fold(P, TheNeutralElement(A, P), {\<langle>k, x\<rangle> . k \<in> n})"
  "TheNeutralElement(B,F)" "\<lambda>x y. F`\<langle>x,y\<rangle>"
  "\<lambda>x. GroupInv(B,F)`x" "\<lambda>s.  Fold(F, TheNeutralElement(B, F), s)"
  "\<lambda>n x.  Fold(F, TheNeutralElement(B, F), {\<langle>k, x\<rangle> . k \<in> n})"
  apply (simp only: hf) apply simp apply simp apply simp apply simp apply simp
  by assumption


text\<open>Exactness at $B$ means the image of $f$ equals the kernel of $g$.\<close>

lemma (in two_group_homo) ExactAtB_unfold:
  shows "ExactAtB \<longleftrightarrow> f``A = g-``{TheNeutralElement(C, Q)}"
  unfolding IsExactAt_def by (simp only:)

text\<open>If the sequence is exact at $B$, the composition $g \circ f$ maps every element
  of $A$ to the neutral element of $C$.\<close>

lemma (in two_group_homo) exact_comp_trivial:
  assumes "ExactAtB" and "x \<in> A"
  shows "g`(f`x) = TheNeutralElement(C, Q)"
proof -
  from assms(2) have "f`x \<in> f``A"
    using first_homo.f_is_fun func_imagedef by auto
  with assms(1) have ker: "f`x \<in> g-``{TheNeutralElement(C, Q)}"
    unfolding IsExactAt_def by (simp only:)
  from assms(2) have "f`x \<in> B" using first_homo.f_is_fun apply_type by simp
  with ker show ?thesis using group_homo.kernel_mem[OF hg] by (simp only:)
qed

text\<open>A sufficient condition for exactness: if $g \circ f$ is trivial and the
  kernel of $g$ is contained in the image of $f$, then the sequence is exact at $B$.\<close>

lemma (in two_group_homo) exact_at_B_intro:
  assumes "\<forall>x \<in> A. g`(f`x) = TheNeutralElement(C, Q)"
    and "g-``{TheNeutralElement(C, Q)} \<subseteq> f``A"
  shows "ExactAtB"
  unfolding IsExactAt_def
proof
  show "f``A \<subseteq> g-``{TheNeutralElement(C, Q)}"
  proof
    fix y assume "y \<in> f``A"
    with first_homo.f_is_fun obtain x where xA: "x \<in> A" and yf: "y = f`x"
      using func_imagedef by auto
    from xA first_homo.f_is_fun yf have yB: "y \<in> B" using apply_type by simp
    from assms(1) xA yf have "g`y = TheNeutralElement(C, Q)" by (simp only:)
    with yB show "y \<in> g-``{TheNeutralElement(C, Q)}"
      using group_homo.kernel_mem[OF hg] by (simp only:)
  qed
  from assms(2) show "g-``{TheNeutralElement(C, Q)} \<subseteq> f``A" .
qed

subsection\<open>The trivial group and zero maps\<close>

text\<open>The \emph{trivial group} has carrier $1 = \{0\}$ and operation
  $\mathbf{0} \colon 1\times 1 \to 1$ defined by $\mathbf{0}(0,0)=0$.\<close>

definition TrivOp :: i where
  "TrivOp \<equiv> ConstantFunction(1\<times>1, 0)"

text\<open>$\mathbf{0}$ is a function $1\times 1 \to 1$.\<close>

lemma TrivOp_type: "TrivOp : 1\<times>1 \<rightarrow> 1"
  unfolding TrivOp_def using func1_3_L1 by simp

text\<open>The value of $\mathbf{0}$ at any pair from $1\times 1$ is $0$.\<close>

lemma TrivOp_val:
  assumes "x \<in> 1" "y \<in> 1"
  shows "TrivOp`\<langle>x,y\<rangle> = 0"
proof -
  from assms have "\<langle>x,y\<rangle> \<in> 1\<times>1" by auto
  then show ?thesis unfolding TrivOp_def using func1_3_L2 by simp
qed

text\<open>The neutral element of $(1, \mathbf{0})$ is $0$.\<close>

lemma TrivOp_ne: "TheNeutralElement(1, TrivOp) = 0"
  unfolding TheNeutralElement_def
proof (rule the_equality)
  show "0 \<in> 1 \<and> (\<forall>g\<in>1. TrivOp`\<langle>0,g\<rangle> = g \<and> TrivOp`\<langle>g,0\<rangle> = g)"
  proof (intro conjI ballI conjI)
    show "0 \<in> 1" by simp
    fix g assume g1: "g \<in> 1"
    then have g0: "g = 0" by auto
    then show "TrivOp`\<langle>0,g\<rangle> = g" using TrivOp_val g1 by auto
    from g0 show "TrivOp`\<langle>g,0\<rangle> = g" using TrivOp_val g1 by auto
  qed
next
  fix e assume "e \<in> 1 \<and> (\<forall>g\<in>1. TrivOp`\<langle>e,g\<rangle> = g \<and> TrivOp`\<langle>g,e\<rangle> = g)"
  then show "e = 0" by auto
qed

text\<open>$(1, \mathbf{0})$ is a group.\<close>

lemma trivial_group: "IsAgroup(1, TrivOp)"
proof -
  have assoc: "TrivOp {is associative on} 1"
    unfolding IsAssociative_def
  proof (intro conjI)
    show "TrivOp : 1\<times>1 \<rightarrow> 1" using TrivOp_type .
    show "\<forall>x\<in>1. \<forall>y\<in>1. \<forall>z\<in>1.
        TrivOp`\<langle>TrivOp`\<langle>x,y\<rangle>,z\<rangle> = TrivOp`\<langle>x,TrivOp`\<langle>y,z\<rangle>\<rangle>"
    proof (intro ballI)
      fix x y z assume H: "x \<in> 1" "y \<in> 1" "z \<in> 1"
      have m1: "TrivOp`\<langle>x,y\<rangle> \<in> 1" using TrivOp_val H by auto
      have m2: "TrivOp`\<langle>y,z\<rangle> \<in> 1" using TrivOp_val H by auto
      have "TrivOp`\<langle>TrivOp`\<langle>x,y\<rangle>,z\<rangle> = 0"
        using TrivOp_val m1 H(3) by simp
      moreover have "TrivOp`\<langle>x,TrivOp`\<langle>y,z\<rangle>\<rangle> = 0"
        using TrivOp_val H(1) m2 by simp
      ultimately show "TrivOp`\<langle>TrivOp`\<langle>x,y\<rangle>,z\<rangle> = TrivOp`\<langle>x,TrivOp`\<langle>y,z\<rangle>\<rangle>" by simp
    qed
  qed
  have neutral: "\<exists>e\<in>1. \<forall>g\<in>1. TrivOp`\<langle>e,g\<rangle> = g \<and> TrivOp`\<langle>g,e\<rangle> = g"
  proof (rule bexI[of _ 0])
    show "\<forall>g\<in>1. TrivOp`\<langle>0,g\<rangle> = g \<and> TrivOp`\<langle>g,0\<rangle> = g"
    proof (intro ballI conjI)
      fix g assume g1: "g \<in> 1"
      then have g0: "g = 0" by auto
      then show "TrivOp`\<langle>0,g\<rangle> = g" using TrivOp_val g1 by auto
      from g0 show "TrivOp`\<langle>g,0\<rangle> = g" using TrivOp_val g1 by auto
    qed
    show "0 \<in> 1" by simp
  qed
  have monoid: "IsAmonoid(1, TrivOp)"
    unfolding IsAmonoid_def using assoc neutral by blast
  have inv: "\<forall>g\<in>1. \<exists>b\<in>1. TrivOp`\<langle>g,b\<rangle> = TheNeutralElement(1,TrivOp)"
  proof (intro ballI)
    fix g assume g1: "g \<in> 1"
    show "\<exists>b\<in>1. TrivOp`\<langle>g,b\<rangle> = TheNeutralElement(1,TrivOp)"
      using TrivOp_val TrivOp_ne g1 by auto
  qed
  from monoid inv show "IsAgroup(1,TrivOp)" unfolding IsAgroup_def by blast
qed

text\<open>$(1, \mathbf{0})$ is abelian.\<close>

lemma trivial_group_abelian: "TrivOp {is commutative on} 1"
  unfolding IsCommutative_def using TrivOp_val by auto

text\<open>The \emph{zero map} from $(G_1,P_1)$ to $(G_2,P_2)$ sends every element
  to the neutral element of $G_2$.\<close>

definition ZeroMap :: "[i, i, i] \<Rightarrow> i" where
  "ZeroMap(G\<^sub>1, G\<^sub>2, P\<^sub>2) \<equiv> ConstantFunction(G\<^sub>1, TheNeutralElement(G\<^sub>2, P\<^sub>2))"

text\<open>The zero map is a group homomorphism.\<close>

lemma ZeroMap_hom:
  assumes grp1: "IsAgroup(G\<^sub>1, P\<^sub>1)" and grp2: "IsAgroup(G\<^sub>2, P\<^sub>2)"
  shows "Homomor(ZeroMap(G\<^sub>1, G\<^sub>2, P\<^sub>2), G\<^sub>1, P\<^sub>1, G\<^sub>2, P\<^sub>2)"
proof -
  let ?e\<^sub>1 = "TheNeutralElement(G\<^sub>1, P\<^sub>1)"
  let ?e\<^sub>2 = "TheNeutralElement(G\<^sub>2, P\<^sub>2)"
  interpret g1: group0 G\<^sub>1 P\<^sub>1 ?e\<^sub>1 "\<lambda>x y. P\<^sub>1`\<langle>x,y\<rangle>" "\<lambda>x. GroupInv(G\<^sub>1,P\<^sub>1)`x"
    "\<lambda>s. Fold(P\<^sub>1,?e\<^sub>1,s)" "\<lambda>n x. Fold(P\<^sub>1,?e\<^sub>1,{\<langle>k,x\<rangle>. k\<in>n})"
    using grp1 unfolding group0_def by auto
  interpret g2: group0 G\<^sub>2 P\<^sub>2 ?e\<^sub>2 "\<lambda>x y. P\<^sub>2`\<langle>x,y\<rangle>" "\<lambda>x. GroupInv(G\<^sub>2,P\<^sub>2)`x"
    "\<lambda>s. Fold(P\<^sub>2,?e\<^sub>2,s)" "\<lambda>n x. Fold(P\<^sub>2,?e\<^sub>2,{\<langle>k,x\<rangle>. k\<in>n})"
    using grp2 unfolding group0_def by auto
  have eG2: "?e\<^sub>2 \<in> G\<^sub>2" using g2.group0_2_L2_1 by assumption
  have ee2: "P\<^sub>2`\<langle>?e\<^sub>2,?e\<^sub>2\<rangle> = ?e\<^sub>2"
    using g2.group0_2_L2_2[OF g2.group0_2_L2_1] by assumption
  have fun_t: "ZeroMap(G\<^sub>1, G\<^sub>2, P\<^sub>2) : G\<^sub>1 \<rightarrow> G\<^sub>2"
    unfolding ZeroMap_def using func1_3_L1 eG2 by blast
  have morph: "IsMorphism(G\<^sub>1, P\<^sub>1, P\<^sub>2, ZeroMap(G\<^sub>1, G\<^sub>2, P\<^sub>2))"
    unfolding IsMorphism_def ZeroMap_def
  proof (intro ballI)
    fix x y assume xy: "x \<in> G\<^sub>1" "y \<in> G\<^sub>1"
    from xy have pxy: "P\<^sub>1`\<langle>x,y\<rangle> \<in> G\<^sub>1" using g1.group_op_closed by blast
    have "ConstantFunction(G\<^sub>1,?e\<^sub>2)`(P\<^sub>1`\<langle>x,y\<rangle>) = ?e\<^sub>2"
      using func1_3_L2 pxy by blast
    also have "\<dots> = P\<^sub>2`\<langle>?e\<^sub>2,?e\<^sub>2\<rangle>" using ee2 by (simp only:sym)
    also have "\<dots> = P\<^sub>2`\<langle>ConstantFunction(G\<^sub>1,?e\<^sub>2)`x,
                         ConstantFunction(G\<^sub>1,?e\<^sub>2)`y\<rangle>"
      using func1_3_L2 xy by (simp only:)
    finally show "ConstantFunction(G\<^sub>1,?e\<^sub>2)`(P\<^sub>1`\<langle>x,y\<rangle>) =
      P\<^sub>2`\<langle>ConstantFunction(G\<^sub>1,?e\<^sub>2)`x,ConstantFunction(G\<^sub>1,?e\<^sub>2)`y\<rangle>" .
  qed
  from fun_t morph show ?thesis unfolding Homomor_def by simp
qed

text\<open>The image of the zero map over its domain is the singleton of the neutral element.\<close>

lemma ZeroMap_image:
  assumes grp1: "IsAgroup(G\<^sub>1, P\<^sub>1)" and grp2: "IsAgroup(G\<^sub>2, P\<^sub>2)"
  shows "ZeroMap(G\<^sub>1, G\<^sub>2, P\<^sub>2)``G\<^sub>1 = {TheNeutralElement(G\<^sub>2, P\<^sub>2)}"
proof -
  let ?e\<^sub>1 = "TheNeutralElement(G\<^sub>1, P\<^sub>1)"
  let ?e\<^sub>2 = "TheNeutralElement(G\<^sub>2, P\<^sub>2)"
  from ZeroMap_hom[OF grp1 grp2] have fun_t: "ZeroMap(G\<^sub>1, G\<^sub>2, P\<^sub>2) : G\<^sub>1 \<rightarrow> G\<^sub>2"
    unfolding Homomor_def by simp
  interpret g1: group0 G\<^sub>1 P\<^sub>1 ?e\<^sub>1 "\<lambda>x y. P\<^sub>1`\<langle>x,y\<rangle>" "\<lambda>x. GroupInv(G\<^sub>1,P\<^sub>1)`x"
    "\<lambda>s. Fold(P\<^sub>1,?e\<^sub>1,s)" "\<lambda>n x. Fold(P\<^sub>1,?e\<^sub>1,{\<langle>k,x\<rangle>. k\<in>n})"
    using grp1 unfolding group0_def by auto
  have e1G: "?e\<^sub>1 \<in> G\<^sub>1" using g1.group0_2_L2_1 by assumption
  have val: "\<forall>x \<in> G\<^sub>1. ZeroMap(G\<^sub>1, G\<^sub>2, P\<^sub>2)`x = ?e\<^sub>2"
    unfolding ZeroMap_def using func1_3_L2 by simp
  then have "{ZeroMap(G\<^sub>1, G\<^sub>2, P\<^sub>2)`x. x\<in>G\<^sub>1} = {?e\<^sub>2}" 
    apply auto using e1G by auto
  with fun_t show ?thesis using func_imagedef by auto
qed

text\<open>The preimage of the neutral element under the zero map is the whole domain.\<close>

lemma ZeroMap_preimage_full:
  assumes grp1: "IsAgroup(G\<^sub>1, P\<^sub>1)" and grp2: "IsAgroup(G\<^sub>2, P\<^sub>2)"
  shows "ZeroMap(G\<^sub>1, G\<^sub>2, P\<^sub>2)-``{TheNeutralElement(G\<^sub>2, P\<^sub>2)} = G\<^sub>1"
proof -
  let ?e\<^sub>2 = "TheNeutralElement(G\<^sub>2, P\<^sub>2)"
  from ZeroMap_hom[OF grp1 grp2] have fun_t: "ZeroMap(G\<^sub>1, G\<^sub>2, P\<^sub>2) : G\<^sub>1 \<rightarrow> G\<^sub>2"
    unfolding Homomor_def by simp
  have val: "\<forall>x \<in> G\<^sub>1. ZeroMap(G\<^sub>1, G\<^sub>2, P\<^sub>2)`x = ?e\<^sub>2"
    unfolding ZeroMap_def using func1_3_L2 by simp
  with fun_t show ?thesis using func1_1_L15 by auto
qed

subsection\<open>Short exact sequences\<close>

text\<open>A \emph{short exact sequence} $0 \to A \xrightarrow{f} B \xrightarrow{g} C \to 0$
  is expressed by exactness at all three terms: the sequence is exact at $A$
  (i.e.\ $f$ is injective), at $B$ (i.e.\ $\mathrm{im}(f) = \ker(g)$), and at $C$
  (i.e.\ $g$ is surjective), each encoded via zero maps to or from the trivial group.\<close>

definition IsAshortExactSequence :: "[i, i, i, i, i, i, i, i] \<Rightarrow> o" where
  "IsAshortExactSequence(A, P, B, F, C, Q, f, g) \<equiv>
    group_homo(A, P, B, F, f) \<and>
    group_homo(B, F, C, Q, g) \<and>
    IsExactAt(ZeroMap(1, A, P), 1, f, B, F) \<and>
    IsExactAt(f, A, g, C, Q) \<and>
    IsExactAt(g, B, ZeroMap(C, 1, TrivOp), 1, TrivOp)"

text\<open>The \<open>short_exact_sequence\<close> locale packages a short exact sequence,
  expressed by exactness at all three terms.\<close>

locale short_exact_sequence = two_group_homo +
  assumes ses_exact_at_A: "IsExactAt(ZeroMap(1, A, P), 1, f, B, F)"
    and ses_exact: "ExactAtB"
    and ses_exact_at_C: "IsExactAt(g, B, ZeroMap(C, 1, TrivOp), 1, TrivOp)"

text\<open>The image of $f$ equals the kernel of $g$.\<close>

lemma (in short_exact_sequence) ses_im_eq_ker:
  shows "f``A = g-``{TheNeutralElement(C, Q)}"
  using ses_exact unfolding IsExactAt_def by (simp only:)

text\<open>$f$ is injective: exactness at $A$ forces the kernel of $f$ to be trivial.\<close>

lemma (in short_exact_sequence) ses_inj:
  shows "f \<in> inj(A, B)"
proof -
  from ses_exact_at_A have "ZeroMap(1, A, P)``1 = f-``{TheNeutralElement(B, F)}"
    unfolding IsExactAt_def by (simp only:)
  moreover have "ZeroMap(1, A, P)``1 = {TheNeutralElement(A, P)}"
    using ZeroMap_image[OF trivial_group first_homo.origin] by (simp only:)
  ultimately have "f-``{TheNeutralElement(B, F)} = {TheNeutralElement(A, P)}" by (simp only:)
  with first_homo.kernel_trivial_iff_injective show ?thesis by (simp only:)
qed

text\<open>$g$ is surjective: exactness at $C$ forces $g$ to hit all of $C$.\<close>

lemma (in short_exact_sequence) ses_surj:
  shows "g``B = C"
proof -
  from ses_exact_at_C have "g``B = ZeroMap(C, 1, TrivOp)-``{TheNeutralElement(1, TrivOp)}"
    unfolding IsExactAt_def by simp
  also have "\<dots> = C"
    using ZeroMap_preimage_full[OF second_homo.target trivial_group] by simp
  finally show ?thesis .
qed

text\<open>The kernel of $f$ is trivial.\<close>

lemma (in short_exact_sequence) ses_ker_trivial:
  shows "f-``{TheNeutralElement(B, F)} = {TheNeutralElement(A, P)}"
  using ses_inj first_homo.kernel_trivial_iff_injective by (simp only:)

text\<open>$g$ maps each element of $B$ to an element of $C$.\<close>

lemma (in short_exact_sequence) ses_g_type:
  assumes "b \<in> B"
  shows "g`b \<in> C"
  using assms second_homo.f_is_fun apply_type by simp

text\<open>An element of $B$ in the kernel of $g$ is in the image of $f$.\<close>

lemma (in short_exact_sequence) ses_ker_in_im:
  assumes "b \<in> B" and "g`b = TheNeutralElement(C, Q)"
  shows "b \<in> f``A"
  using assms second_homo.kernel_mem ses_im_eq_ker by (simp only:)

text\<open>An element in the image of $f$ maps to the neutral element under $g$.\<close>

lemma (in short_exact_sequence) ses_im_to_ker:
  assumes "b \<in> f``A"
  shows "g`b = TheNeutralElement(C, Q)"
proof -
  from assms ses_im_eq_ker have "b \<in> g-``{TheNeutralElement(C, Q)}" by (simp only:)
  with assms first_homo.f_is_fun have "b \<in> B"
    using func1_1_L6(2) by blast
  with \<open>b \<in> g-``{TheNeutralElement(C, Q)}\<close>
  show ?thesis using second_homo.kernel_mem by (simp only:)
qed

text\<open>First isomorphism theorem for a short exact sequence: the quotient $B/f(A)$
  is isomorphic to $C$ via the map induced by $g$.\<close>

theorem (in short_exact_sequence) ses_first_iso:
  defines "r \<equiv> QuotientGroupRel(B, F, f``A)"
      and "\<P> \<equiv> QuotientGroupOp(B, F, f``A)"
  shows "\<exists>\<ff>. Homomor(\<ff>, B//r, \<P>, C, Q) \<and> \<ff> \<in> bij(B//r, C)"
proof -
  have ker_eq: "second_homo.kernel = f``A"
    using ses_im_eq_ker by (simp only:sym)
  have sur: "g``B = C" using ses_surj .
  have restQ: "restrict(Q, C \<times> C) = Q"
    using second_homo.tgt.group_oper_fun restrict_domain by simp
  from second_homo.first_isomorphism_theorem obtain \<ff> where
    HOM: "Homomor(\<ff>, B // QuotientGroupRel(B, F, second_homo.kernel),
                  QuotientGroupOp(B, F, second_homo.kernel),
                  g``B, restrict(Q, g``B \<times> g``B))"
    and BIJ: "\<ff> \<in> bij(B // QuotientGroupRel(B, F, second_homo.kernel), g``B)"
    by blast
  from HOM ker_eq sur restQ have "Homomor(\<ff>, B//r, \<P>, C, Q)"
    unfolding r_def \<P>_def by force
  moreover from BIJ ker_eq sur have "\<ff> \<in> bij(B//r, C)"
    unfolding r_def by force
  ultimately show ?thesis by blast
qed

subsection\<open>The cokernel\<close>

text\<open>A \emph{cokernel} of $f \colon A \to B$ is a group homomorphism
  $q \colon B \to C$ satisfying (i) $q \circ f = 0$, and (ii) the universal
  property: every $h \colon B \to D$ with $h \circ f = 0$ factors uniquely
  through $q$.\<close>

definition IsAcokernel :: "[i, i, i, i, i, i, i] \<Rightarrow> o" where
  "IsAcokernel(f, A, B, F, q, C, Q) \<equiv>
    group_homo(B, F, C, Q, q) \<and>
    (\<forall>x \<in> A. q`(f`x) = TheNeutralElement(C, Q)) \<and>
    (\<forall>D R h. IsAgroup(D, R) \<and> Homomor(h, B, F, D, R) \<and>
             (\<forall>x \<in> A. h`(f`x) = TheNeutralElement(D, R)) \<longrightarrow>
      (\<exists>!hh. Homomor(hh, C, Q, D, R) \<and> (\<forall>b \<in> B. hh`(q`b) = h`b)))"

text\<open>If the target group $H$ is abelian then every subgroup is normal, so
  in particular $f(G)$ is a normal subgroup of $H$.\<close>

lemma (in group_homo) image_normal_if_abelian:
  assumes "F {is commutative on} H"
  shows "IsAnormalSubgroup(H, F, f``G)"
  using target assms image_is_group Group_ZF_2_4_L6(1) by simp

text\<open>The natural quotient map $q \colon H \to H/f(G)$ is a cokernel of $f$
  whenever $H$ is abelian.  The factored map for the universal property is
  $\bar h = \{\langle r``\{b\}, h`b\rangle \mid b \in H\}$, which is exactly the
  construction used in the first isomorphism theorem.\<close>

theorem (in group_homo) quotient_is_cokernel:
  assumes abel: "F {is commutative on} H"
  defines "r \<equiv> QuotientGroupRel(H, F, f``G)"
      and "q \<equiv> \<lambda>h\<in>H. QuotientGroupRel(H, F, f``G)``{h}"
      and "Q \<equiv> QuotientGroupOp(H, F, f``G)"
  shows "IsAcokernel(f, G, H, F, q, H//r, Q)"
  unfolding IsAcokernel_def
proof (intro conjI)
  from image_normal_if_abelian[OF abel]
  have norm: "IsAnormalSubgroup(H, F, f``G)" .
  from norm have equiv_r: "equiv(H, r)"
    unfolding r_def IsAnormalSubgroup_def using tgt.Group_ZF_2_4_L3 by simp
  from norm target have Qgrp: "IsAgroup(H//r, Q)"
    unfolding Q_def r_def using Group_ZF_2_4_T1 by simp
  let ?e\<^sub>Q = "TheNeutralElement(H//r, Q)"
  from norm target have neutQ: "r``{\<one>\<^sub>H} = ?e\<^sub>Q"
    using Group_ZF_2_4_L5B unfolding r_def Q_def by simp
  show "group_homo(H, F, H//r, Q, q)"
  proof -
    have "Homomor(q, H, F, H//r, Q)"
      using tgt.quotient_map[OF norm] unfolding r_def q_def Q_def by simp
    with target Qgrp show ?thesis unfolding group_homo_def by simp
  qed
  show "\<forall>x \<in> G. q`(f`x) = ?e\<^sub>Q"
  proof
    fix x assume aG: "x \<in> G"
    from aG have faH: "f`x \<in> H" using f_is_fun apply_type by simp
    from aG have faim: "f`x \<in> f``G" using f_is_fun func_imagedef by auto
    from faH faim have in_r: "\<langle>f`x, \<one>\<^sub>H\<rangle> \<in> r"
      unfolding r_def using tgt.Group_ZF_2_4_L5C by simp
    from in_r tgt.group0_2_L2 have "r``{f`x} = r``{\<one>\<^sub>H}"
      using equiv_r equiv_class_eq by simp
    also have "\<dots> = ?e\<^sub>Q" using neutQ by simp
    finally have cls: "r``{f`x} = ?e\<^sub>Q" .
    with faH show "q`(f`x) = ?e\<^sub>Q" unfolding q_def r_def by simp
  qed
  show "\<forall>D R h. IsAgroup(D, R) \<and> Homomor(h, H, F, D, R) \<and>
               (\<forall>x \<in> G. h`(f`x) = TheNeutralElement(D, R)) \<longrightarrow>
    (\<exists>!hh. Homomor(hh, H//r, Q, D, R) \<and> (\<forall>b \<in> H. hh`(q`b) = h`b))"
  proof (intro allI)
    fix D R h
    show "IsAgroup(D, R) \<and> Homomor(h, H, F, D, R) \<and>
               (\<forall>x \<in> G. h`(f`x) = TheNeutralElement(D, R)) \<longrightarrow>
      (\<exists>!hh. Homomor(hh, H//r, Q, D, R) \<and> (\<forall>b \<in> H. hh`(q`b) = h`b))"
    proof (intro impI)
    assume conj: "IsAgroup(D, R) \<and> Homomor(h, H, F, D, R) \<and>
                  (\<forall>x \<in> G. h`(f`x) = TheNeutralElement(D, R))"
    from conj have Dgrp: "IsAgroup(D, R)" and hHom: "Homomor(h, H, F, D, R)"
      and hf0: "\<forall>x \<in> G. h`(f`x) = TheNeutralElement(D, R)" by auto
    let ?e\<^sub>D = "TheNeutralElement(D, R)"
    let ?h = "{\<langle>r``{b}, h`b\<rangle>. b \<in> H}"
    interpret h_hom: group_homo H F D R h 
      "TheNeutralElement(H,F)" "\<lambda>x y. F`\<langle>x,y\<rangle>"
      "\<lambda>x. GroupInv(H,F)`x" "\<lambda>s. Fold(F, TheNeutralElement(H, F),s)"
      "\<lambda>n x.  Fold(F, TheNeutralElement(H, F), {⟨k, x⟩ . k ∈ n})"
      "TheNeutralElement(D,R)" "\<lambda>x y. R`\<langle>x,y\<rangle>"
      "\<lambda>x. GroupInv(D,R)`x" "\<lambda>s. Fold(R, TheNeutralElement(D, R),s)"
      "\<lambda>n x.  Fold(R, TheNeutralElement(D, R), {⟨k, x⟩ . k ∈ n})"
      using target Dgrp hHom unfolding group_homo_def by simp
    have hfun: "h: H \<rightarrow> D" using h_hom.f_is_fun .
    have im_in_ker: "\<forall>x \<in> f``G. h`x = ?e\<^sub>D"
    proof
      fix x assume "x \<in> f``G"
      with f_is_fun obtain ga where "ga \<in> G" "x = f`ga"
        using func_imagedef by auto
      with hf0 show "h`x = ?e\<^sub>D" by blast
    qed
    have bhfun: "?h : H//r \<rightarrow> D"
    proof -
      have sub: "?h \<in> Pow((H//r) \<times> D)"
        unfolding quotient_def using hfun apply_type by auto
      have dom: "H//r \<subseteq> domain(?h)"
        unfolding domain_def quotient_def by force
      have sv: "\<forall>c y. \<langle>c,y\<rangle> \<in> ?h \<longrightarrow> (\<forall>z. \<langle>c,z\<rangle> \<in> ?h \<longrightarrow> y = z)"
      proof (intro allI impI)
        fix c y z
        assume H1: "\<langle>c,y\<rangle> \<in> ?h" and H2: "\<langle>c,z\<rangle> \<in> ?h"
        from H1 obtain b\<^sub>1 where b1: "b\<^sub>1 \<in> H" "c = r``{b\<^sub>1}" "y = h`b\<^sub>1" by auto
        from H2 obtain b\<^sub>2 where b2: "b\<^sub>2 \<in> H" "c = r``{b\<^sub>2}" "z = h`b\<^sub>2" by auto
        from b1(2) b2(2) have eq: "r``{b\<^sub>1} = r``{b\<^sub>2}" by simp
        from equiv_r b2(1) eq have rel: "\<langle>b\<^sub>1, b\<^sub>2\<rangle> \<in> r"
          using same_image_equiv by simp
        have R:"\<And>t q X P. \<langle>t,q\<rangle>\<in>{\<langle>x,y\<rangle>\<in>X. P(x,y)} \<Longrightarrow> P(t,q)"
          by auto
        from rel have "\<langle>b\<^sub>1,b\<^sub>2\<rangle> \<in>{\<langle>x,y\<rangle>\<in>H\<times>H. F`\<langle>x, GroupInv(H,F)`y\<rangle> \<in> f``G }"
          unfolding r_def QuotientGroupRel_def by assumption
        then have "F`\<langle>b\<^sub>1, GroupInv(H,F)`b\<^sub>2\<rangle> \<in> f``G"
          using R[of "b\<^sub>1" "b\<^sub>2" "H\<times>H" "\<lambda>x y. F`\<langle>x, GroupInv(H,F)`y\<rangle> \<in> f``G"]
          by (simp only:)
        with im_in_ker have step: "h`(F`\<langle>b\<^sub>1, GroupInv(H,F)`b\<^sub>2\<rangle>) = ?e\<^sub>D" by (simp only:)
        from b2(1) have inv2H: "GroupInv(H,F)`b\<^sub>2 \<in> H"
          using tgt.inverse_in_group tgt.inv_def by (simp only:)
        from b1(1) inv2H have
          "h`(F`\<langle>b\<^sub>1, GroupInv(H,F)`b\<^sub>2\<rangle>) = R`\<langle>h`b\<^sub>1, h`(GroupInv(H,F)`b\<^sub>2)\<rangle>"
          using h_hom.f_hom by (simp only:)
        also from b2(1) have "\<dots> = R`\<langle>h`b\<^sub>1, GroupInv(D,R)`(h`b\<^sub>2)\<rangle>"
          using h_hom.f_inv by (simp only:)
        finally have "R`\<langle>h`b\<^sub>1, GroupInv(D,R)`(h`b\<^sub>2)\<rangle> = ?e\<^sub>D"
          using step by (simp only:)
        with b1(1) b2(1) have "h`b\<^sub>1 = h`b\<^sub>2"
          using h_hom.tgt.group0_2_L11A[OF apply_type[OF hfun] apply_type[OF hfun]] by blast
        with b1(3) b2(3) show "y = z" by simp
      qed
      from sub dom sv show ?thesis unfolding Pi_def function_def by auto
    qed
    have bhHom: "Homomor(?h, H//r, Q, D, R)"
      unfolding Homomor_def IsMorphism_def
    proof (intro conjI bhfun ballI)
      fix c\<^sub>1 c\<^sub>2 assume c1: "c\<^sub>1 \<in> H//r" and c2: "c\<^sub>2 \<in> H//r"
      show "?h`(Q`\<langle>c\<^sub>1,c\<^sub>2\<rangle>) = R`\<langle>?h`c\<^sub>1, ?h`c\<^sub>2\<rangle>"
      proof -
        from c1 obtain b\<^sub>1 where b1: "b\<^sub>1 \<in> H" "c\<^sub>1 = r``{b\<^sub>1}"
          unfolding quotient_def by auto
        from c2 obtain b\<^sub>2 where b2: "b\<^sub>2 \<in> H" "c\<^sub>2 = r``{b\<^sub>2}"
          unfolding quotient_def by auto
        from b1(1) b2(1) have b12H: "F`\<langle>b\<^sub>1,b\<^sub>2\<rangle> \<in> H"
          using tgt.group_op_closed tgt.groper_def by (simp only:)
        have "Q`\<langle>c\<^sub>1,c\<^sub>2\<rangle> = ProjFun2(H, QuotientGroupRel(H, F, f `` G), F) `⟨c⇩1, c⇩2⟩"
          unfolding Q_def QuotientGroupOp_def by auto
        with b1(2) b2(2) have opQ:
          "Q`\<langle>c\<^sub>1,c\<^sub>2\<rangle> = r``{F`\<langle>b\<^sub>1,b\<^sub>2\<rangle>}"
          using Group_ZF_2_4_L5A[OF target norm] tgt.Group_ZF_2_2_L2[OF equiv_r _ _ b1(1) b2(1), of "ProjFun2(H,r,F)"]
          unfolding Q_def r_def tgt.groper_def by (simp only:)
        from b12H have Fh:"\<langle>r ``{F ` ⟨b⇩1, b⇩2⟩},h`(F ` ⟨b⇩1, b⇩2⟩)\<rangle>:?h" by blast
        have lhs: "?h`(Q`\<langle>c\<^sub>1,c\<^sub>2\<rangle>) = h`(F`\<langle>b\<^sub>1,b\<^sub>2\<rangle>)"
          apply (rule apply_equality[OF _ bhfun, of "Q ` ⟨c⇩1, c⇩2⟩"
              "h`(F`\<langle>b\<^sub>1,b\<^sub>2\<rangle>)"]) using opQ Fh by (simp only:sym) 
        from b1(1) b2(1) have hprod: "h`(F`\<langle>b\<^sub>1,b\<^sub>2\<rangle>) = R`\<langle>h`b\<^sub>1, h`b\<^sub>2\<rangle>"
          using h_hom.f_hom by (simp only:)
        have r:"\<And>p. p\<in>H \<Longrightarrow> ?h`(r``{p}) = h`p" using apply_equality[OF _ bhfun] by auto
        from b1(2) b1(1) r have rhs1: "?h`c\<^sub>1 = h`b\<^sub>1" by (simp only:)
        from b2(2) b2(1) r have rhs2: "?h`c\<^sub>2 = h`b\<^sub>2" by (simp only:)
        from lhs hprod rhs1 rhs2 show
          "?h`(Q`\<langle>c\<^sub>1,c\<^sub>2\<rangle>) = R`\<langle>?h`c\<^sub>1, ?h`c\<^sub>2\<rangle>" by (simp only:)
      qed
    qed
    have factor: "\<forall>b \<in> H. ?h`(q`b) = h`b"
    proof
      fix b assume bH: "b \<in> H"
      from bH have "q`b = r``{b}" unfolding q_def r_def by force
      with bH bhfun show "?h`(q`b) = h`b" using apply_equality[OF _ bhfun, of "r``{b}" "h`b"] by force
    qed
    have uniq: "\<And>k. Homomor(k, H//r, Q, D, R) \<and> (\<forall>b \<in> H. k`(q`b) = h`b) \<Longrightarrow> k = ?h"
    proof -
      fix k assume kH: "Homomor(k, H//r, Q, D, R) \<and> (\<forall>b \<in> H. k`(q`b) = h`b)"
      from kH have kHom: "Homomor(k, H//r, Q, D, R)" and kfactor: "\<forall>b \<in> H. k`(q`b) = h`b"
        by auto
      from kHom have kfun: "k: H//r \<rightarrow> D" unfolding Homomor_def by simp
      show "k = ?h"
      proof (rule fun_extension[OF kfun bhfun])
        fix c assume cC: "c \<in> H//r"
        from cC obtain b where bH: "b \<in> H" and cb: "c = r``{b}" unfolding quotient_def by auto
        from bH have "k`c = k`(q`b)" unfolding q_def cb r_def by simp
        also from bH kfactor have "\<dots> = h`b" by simp
        also from bH bhfun cb have "\<dots> = ?h`c" using apply_equality[OF _ bhfun, of c "h`b"] by force
        finally show "k`c = ?h`c" .
      qed
    qed
    from bhHom factor uniq show
      "\<exists>!hh. Homomor(hh, H//r, Q, D, R) \<and> (\<forall>b \<in> H. hh`(q`b) = h`b)"
      by (intro ex1I[of _ "?h"]) auto
    qed
  qed
qed

end

