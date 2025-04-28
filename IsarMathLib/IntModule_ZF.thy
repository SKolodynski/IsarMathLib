(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.
    Copyright (C) 2024  Daniel de la Concepcion
    This program is free software; Redistribution and use in source and binary forms, 
    with or without modification, are permitted provided that the following conditions are met:
   1. Redistributions of source code must retain the above copyright notice, 
   this list of conditions and the following disclaimer.
   2. Redistributions in binary form must reproduce the above copyright notice, 
   this list of conditions and the following disclaimer in the documentation and/or 
   other materials provided with the distribution.
   3. The name of the author may not be used to endorse or promote products 
   derived from this software without specific prior written permission.
THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES,
INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT,
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES LOSS OF USE, DATA, OR PROFITS OR
BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

theory IntModule_ZF imports Module_ZF Int_ZF_1 IntGroup_ZF

begin

section \<open>$\mathbb{Z}$ modules\<close>

text\<open>In this section we show that the integers, as a ring, have only one module structure on 
  each abelian group. We will show that the module structure is unique, but we will also show 
  which action is the one that defines that module structure.\<close>

text \<open>When $\mathbb{Z}$ acts on a group, that action is unique.\<close>

lemma (in int0) action_unique:
  assumes "IsLeftModule(int,IntegerAddition,IntegerMultiplication,G,f,S\<^sub>1)" and  
    "IsLeftModule(int,IntegerAddition,IntegerMultiplication,G,f,S\<^sub>2)"
  shows "S\<^sub>1 = S\<^sub>2"
proof -
  let ?A\<^sub>Z = "IntegerAddition"
  let ?M\<^sub>Z = "IntegerMultiplication"
  from assms have mod0: "module0(\<int>,?A\<^sub>Z,?M\<^sub>Z,G,f,S\<^sub>1)" "module0(\<int>,?A\<^sub>Z,?M\<^sub>Z,G,f,S\<^sub>2)"
      unfolding module0_def IsLeftModule_def ring0_def module0_axioms_def by auto
  { fix r assume rg: "r\<in>\<int>"    
    from mod0(1) have eq: "\<forall>g\<in>G. (S\<^sub>1`(\<zero>))`(g) = TheNeutralElement(G, f)"
      using module0.mult_zero by simp
    with mod0(1) have "S\<^sub>1`(\<zero>) = {\<langle>g,TheNeutralElement(G,f)\<rangle>. g\<in>G}"
      using Int_ZF_1_L8A(1) module0.H_val_type(2) fun_is_set_of_pairs
      by force
    then have s1: "S\<^sub>1`(\<zero>) = ConstantFunction(G,TheNeutralElement(G, f))"
      unfolding ConstantFunction_def by auto
    from mod0(2) have eq: "\<forall>g\<in>G. (S\<^sub>2`(\<zero>))`(g) = TheNeutralElement(G, f)"
      using module0.mult_zero by auto
    with mod0(2) have "(S\<^sub>2`(\<zero>)):G\<rightarrow>G" using Int_ZF_1_L8A(1) module0.H_val_type
      by auto
    with eq s1 have "S\<^sub>1`(\<zero>) = S\<^sub>2`(\<zero>)"
      unfolding ConstantFunction_def using fun_is_set_of_pairs by force
    { assume "r\<lsq>\<zero>"
      then have "r\<in>\<int>" using OrderedGroup_ZF_1_L4(1) by simp
      have "S\<^sub>1`(r) = S\<^sub>2`(r)"
      proof -
        { fix n assume "n\<lsq>\<zero>" "S\<^sub>1`(n) = S\<^sub>2`(n)"
          from \<open>n\<lsq>\<zero>\<close> have "n\<in>\<int>" using OrderedGroup_ZF_1_L4(1) by simp
          have "(\<rm>\<one>) \<in> \<int>" using group0.inverse_in_group Int_ZF_1_T2(3)
              ring0.Ring_ZF_1_L2(2) Int_ZF_1_1_L2(3) by simp
          { fix t assume t: "t\<in>G"
            with mod0(1) \<open>S\<^sub>1`(n) = S\<^sub>2`(n)\<close> \<open>n\<in>\<int>\<close> \<open>(\<rm>\<one>)\<in>\<int>\<close> have 
              "S\<^sub>1`(n\<ra>(\<rm> \<one>))`(t) = (f`\<langle>(S\<^sub>2`(n))`(t),(S\<^sub>1`(\<rm>\<one>))`(t)\<rangle>)"
              using  module0.module_ax2 t by simp
            moreover from mod0(1) have ex: "\<forall>g\<in>G. S\<^sub>1`(\<rm>\<one>)`(g) = GroupInv(G, f)`(g)" 
              using module0.inv_module apply_type module0.H_val_type(2) ring0.Ring_ZF_1_L2(2) 
                Int_ZF_1_1_L2(3) module0.module_ax4 by simp
            moreover from mod0(1) have "S\<^sub>1`(\<rm> \<one>):G\<rightarrow>G"
              using module0.H_val_type(2) ring0.Ring_ZF_1_L2(2) Int_ZF_1_1_L2(3)
                ring0.Ring_ZF_1_L3(1) Int_ZF_1_1_L2(3) by auto
            moreover 
            from assms(1) have "GroupInv(G, f): G\<rightarrow>G"
              using group0_2_T2 unfolding IsLeftModule_def by blast
            with ex \<open>S\<^sub>1`(\<rm> \<one>):G\<rightarrow>G\<close> have "S\<^sub>1`(\<rm> \<one>) =  GroupInv(G, f)" 
              using func_eq by simp
            ultimately have A: "S\<^sub>1`(n\<ra>(\<rm>\<one>))`(t) = f`\<langle>(S\<^sub>2`(n))`(t),GroupInv(G, f) `t\<rangle>" 
              by simp
            from assms(2) \<open>(\<rm>\<one>) \<in> \<int>\<close> \<open>n\<in>\<int>\<close> mod0(2) t \<open>S\<^sub>1`(n) = S\<^sub>2`(n)\<close> have
              "(S\<^sub>2`(n\<ra>\<rm>\<one>))`(t) = f`\<langle>(S\<^sub>2`(n))`(t),(S\<^sub>2`(\<rm>\<one>))`(t)\<rangle>"
              using module0.module_ax2 by simp
            moreover from mod0(2) have ex: "\<forall>g\<in>G. (S\<^sub>2`(\<rm>\<one>))`(g) = GroupInv(G, f)`(g)"
              using module0.inv_module apply_type module0.H_val_type(2) 
                ring0.Ring_ZF_1_L2(2) Int_ZF_1_1_L2(3) module0.module_ax4 by simp
            moreover 
            from mod0(2) have "S\<^sub>2`(\<rm> \<one>): G\<rightarrow>G"
              using module0.H_val_type(2) ring0.Ring_ZF_1_L2(2) Int_ZF_1_1_L2(3)
                ring0.Ring_ZF_1_L3(1) Int_ZF_1_1_L2(3) by auto
            with ex \<open>GroupInv(G, f): G\<rightarrow>G\<close> have "S\<^sub>2`(\<rm>\<one>) = GroupInv(G, f)" 
              using func_eq by blast
            ultimately have "S\<^sub>2`(n\<ra>(\<rm>\<one>))`(t) = f`\<langle>(S\<^sub>2`(n))`(t),GroupInv(G, f)`(t)\<rangle>"
              by simp
            with A have "(S\<^sub>1`(n\<ra>(\<rm> \<one>)))`(t) = S\<^sub>2`(n\<ra>(\<rm>\<one>))`(t)" by simp
          } hence "\<forall>t\<in>G. S\<^sub>1`(n \<ra> \<rm> \<one>)`(t) = S\<^sub>2`(n\<ra>(\<rm>\<one>))`(t)" by simp
          moreover from mod0 \<open>(\<rm>\<one>) \<in> \<int>\<close> \<open>n\<in>\<int>\<close> have 
            "S\<^sub>1`(n\<ra>(\<rm>\<one>)):G\<rightarrow>G" and "S\<^sub>2`(n\<ra>(\<rm>\<one>)):G\<rightarrow>G"
            using group0.group_op_closed Int_ZF_1_T2(3) module0.H_val_type(2) 
            by simp_all
          ultimately have "S\<^sub>1`(n\<ra>(\<rm>\<one>)) = S\<^sub>2`(n\<ra>(\<rm>\<one>))"
            using func_eq by simp
        } hence "\<forall>n. (n\<lsq>\<zero>) \<and> (S\<^sub>1`(n) = S\<^sub>2`(n))\<longrightarrow>S\<^sub>1`(n\<rs>\<one>) = S\<^sub>2`(n\<rs>\<one>)"
          by auto
        with \<open>r\<lsq>\<zero>\<close> \<open>S\<^sub>1`(\<zero>) = S\<^sub>2`(\<zero>)\<close> show "S\<^sub>1`(r) = S\<^sub>2`(r)"
          using Back_induct_on_int by simp
      qed
    }
    moreover
    { assume "\<zero>\<lsq>r"
      then have "r\<in>\<int>" using OrderedGroup_ZF_1_L4(2) by simp
      have "S\<^sub>1`(r) = S\<^sub>2`(r)"
      proof -
        { fix m assume "\<zero>\<lsq>m" "S\<^sub>1`(m) = S\<^sub>2`(m)"
          from \<open>\<zero>\<lsq>m\<close> have "m\<in>\<int>" using OrderedGroup_ZF_1_L4(2) by simp
          have "\<one>\<in>\<int>" using Int_ZF_1_L8A(2) by simp
          { fix t assume  "t\<in>G"
            with assms(1) \<open>m\<in>\<int>\<close> \<open>\<one>\<in>\<int>\<close> mod0(1) \<open>S\<^sub>1`(m) = S\<^sub>2`(m)\<close> have 
              "S\<^sub>1`(m\<ra>\<one>)`t = f`\<langle>(S\<^sub>2`(m))`(t),t\<rangle>"
              using module0.module_ax2 module0.module_ax4 by simp
            moreover from mod0(2) \<open>m\<in>\<int>\<close> \<open>\<one>\<in>\<int>\<close> \<open>t\<in>G\<close> have 
              "(S\<^sub>2`(m\<ra>\<one>))`(t) = f`\<langle>(S\<^sub>2`(m))`(t),t\<rangle>"
              using module0.module_ax2 module0.module_ax4 by simp
            ultimately have "(S\<^sub>1`(m\<ra>\<one>))`(t) = (S\<^sub>2`(m\<ra>\<one>))`(t)" 
              by simp
          } hence "\<forall>t\<in>G. (S\<^sub>1`(m\<ra>\<one>))`(t) = (S\<^sub>2`(m\<ra>\<one>))`(t)" by simp
          moreover from mod0 \<open>\<one>\<in>\<int>\<close> \<open>m\<in>\<int>\<close> have 
            "S\<^sub>1`(m\<ra>\<one>):G\<rightarrow>G" and "S\<^sub>2`(m\<ra>\<one>):G\<rightarrow>G"
            using group0.group_op_closed Int_ZF_1_T2(3) module0.H_val_type(2)
              module0.H_val_type(2) by simp_all
          ultimately have "S\<^sub>1`(m\<ra>\<one>) = S\<^sub>2`(m\<ra>\<one>)"
            using func_eq by simp
        } hence "\<forall>m. (\<zero>\<lsq>m) \<and> S\<^sub>1`(m) = S\<^sub>2`(m) \<longrightarrow> S\<^sub>1`(m\<ra>\<one>) = S\<^sub>2`(m\<ra>\<one>)"
            by simp
          with \<open>\<zero>\<lsq>r\<close> \<open>S\<^sub>1`(\<zero>) = S\<^sub>2`(\<zero>)\<close> show "S\<^sub>1`(r) = S\<^sub>2`(r)" using Induction_on_int 
            by simp
      qed
    }
    moreover have "IntegerOrder {is total on} \<int>" using Int_ZF_2_T1(2) by simp
    ultimately have "S\<^sub>1`(r) = S\<^sub>2`(r)" unfolding IsTotal_def 
      using rg int0.Int_ZF_1_L8(1) ring0.Ring_ZF_1_L2(1) Int_ZF_1_1_L2(3) 
      by auto
  } hence "\<forall>r\<in>\<int>. S\<^sub>1`(r) = S\<^sub>2`(r)" by auto
  moreover from assms have "S\<^sub>1:\<int>\<rightarrow>End(G,f)" "S\<^sub>2:\<int>\<rightarrow>End(G,f)"
    using module_action_type(3) by simp_all
  ultimately show "S\<^sub>1 = S\<^sub>2" using func_eq by simp
qed

sublocale abelian_group < int0_abgroup: abgroup_int0 G P \<one> groper inv
  listprod pow int "\<lambda>x y. IntegerAddition`\<langle>x,y\<rangle>" "\<lambda>x. GroupInv(int,IntegerAddition)`x"
  "\<lambda>x y. IntegerAddition`\<langle>x,GroupInv(int,IntegerAddition)`y\<rangle>"
  "\<lambda>x y. IntegerMultiplication`\<langle>x,y\<rangle>" "\<lambda>A. GroupInv(int,IntegerAddition)``(A)"
  "$# 0" "$# 1" "$# 1 $+ $# 1" "($# 1 $+ $# 1) $+ $# 1" "Nonnegative(int,IntegerAddition,IntegerOrder)" 
  "PositiveSet(int,IntegerAddition,IntegerOrder)" "\<lambda>m. AbsoluteValue(int,IntegerAddition,IntegerOrder)`m" 
  "\<lambda>x y. \<langle>x,y\<rangle>\<in>IntegerOrder" "\<lambda>x y. \<langle>x,y\<rangle>\<in>IntegerOrder \<and> x\<noteq>y" "\<lambda>x y. Interval(IntegerOrder,x,y)"
  "\<lambda>f A. Maximum(IntegerOrder,f``(A))" "\<lambda>f A. Minimum(IntegerOrder,f``(A))"
  "\<lambda>f. OddExtension(int,IntegerAddition,IntegerOrder,f)"
  apply auto
  unfolding abgroup_int0_def group_int0_def abgroup_int0_axioms_def
  apply auto using group0_axioms apply simp using abelian_group_axioms unfolding abelian_group_def abelian_group_axioms_def apply simp
  using int0.Int_ZF_1_L8 apply simp using int0.Int_ZF_1_L8 apply simp
  using int0.Int_ZF_1_L2(1) apply simp
  using int0.Int_ZF_1_L2(1) apply simp done

definition (in abelian_group)
  "powz(z,n) \<equiv> int0_abgroup.powz(z,n)"

text\<open>The action is an group homomorphism between $(\mathbb{Z},+)$ and $(G,P)$\<close>

lemma(in abelian_group) group_action_int_add_morphism:
  defines "S \<equiv> {\<langle>z,{\<langle>x,powz(z,x)\<rangle>. x\<in>G}\<rangle>. z\<in>int}"
  shows "\<forall>r\<in>int. \<forall>s\<in>int. \<forall>g\<in>G. S ` (IntegerAddition` \<langle>r, s\<rangle>) ` g = P ` \<langle>(S ` r) ` g, (S ` s) ` g\<rangle>"
proof(safe)
  have S_fun:"S:int\<rightarrow>End(G,P)" using int0_abgroup.powz_maps_int_End
    unfolding S_def powz_def by blast
  fix r s g assume as:"r:int" "s:int" "g:G"
  from as(1) int_cases obtain n where n:"n\<in>nat" "r=$#n \<or> r=$- $# succ(n)" by blast
  from as(2) int_cases obtain m where m:"m\<in>nat" "s=$#m \<or> s=$- $# succ(m)" by blast
  from as(1,2) have "\<langle>r,s\<rangle>\<in>int\<times>int" unfolding Sigma_def by blast
  then have int:"IntegerAddition`\<langle>r, s\<rangle>\<in>int" 
    using apply_type[of IntegerAddition "int\<times>int" "\<lambda>_. int" "\<langle>r,s\<rangle>"]
    by (simp only: Int_ZF_1_L1(1))
  then have "\<langle>IntegerAddition`\<langle>r,s\<rangle>,{\<langle>x,powz(IntegerAddition`\<langle>r,s\<rangle>,x)\<rangle>. x\<in>G}\<rangle>\<in>S"
    unfolding S_def by blast
  then have Q:"S`(IntegerAddition`\<langle>r,s\<rangle>) = {\<langle>x,powz(IntegerAddition`\<langle>r,s\<rangle>,x)\<rangle>. x\<in>G}"
    using apply_equality[OF _ S_fun] by blast
  have SS_fun:"S`(IntegerAddition`\<langle>r,s\<rangle>):G\<rightarrow>G"
    using apply_type[OF S_fun int] unfolding End_def by (simp only:)
  have SS_r_fun:"S`r:G\<rightarrow>G"
    using apply_type[OF S_fun as(1)] unfolding End_def by (simp only:)
  have SS_s_fun:"S`s:G\<rightarrow>G"
    using apply_type[OF S_fun as(2)] unfolding End_def by (simp only:)
  {
    fix x assume "x\<in>G"
    then have "powz(IntegerAddition`\<langle>r,s\<rangle>,x) = powz(r,x)\<cdot>powz(s,x)"
      using int0_abgroup.powz_hom_prop[of r s x] as(1,2) unfolding powz_def by blast
  }
  then have R:"\<And>y. y\<in>G \<Longrightarrow> powz(IntegerAddition`\<langle>r,s\<rangle>,y) = powz(r,y)\<cdot>powz(s,y)" by blast
  {
    fix t assume as:"t\<in>{\<langle>x,powz(IntegerAddition`\<langle>r,s\<rangle>,x)\<rangle>. x\<in>G}"
    then obtain tx where t:"t=\<langle>tx,powz(IntegerAddition`\<langle>r,s\<rangle>,tx)\<rangle>" "tx\<in>G"
      by blast
    from t(1) have "t=\<langle>tx,powz(r,tx)\<cdot>powz(s,tx)\<rangle>" by (simp only:t(2) R[of tx])
    then have "t\<in>{\<langle>x,powz(r,x)\<cdot>powz(s,x)\<rangle>. x\<in>G}" using t(2) by blast
  }
  then have A1:"{\<langle>x,powz(IntegerAddition`\<langle>r,s\<rangle>,x)\<rangle>. x\<in>G} \<subseteq> {\<langle>x,powz(r,x)\<cdot>powz(s,x)\<rangle>. x\<in>G}" by blast
  {
    fix t assume as:"t\<in>{\<langle>x,powz(r,x)\<cdot>powz(s,x)\<rangle>. x\<in>G}"
    then obtain tx where t:"t=\<langle>tx,powz(r,tx)\<cdot>powz(s,tx)\<rangle>" "tx\<in>G"
      by blast
    from t(1) have "t=\<langle>tx,powz(IntegerAddition`\<langle>r,s\<rangle>,tx)\<rangle>" by (simp only:t(2) R[of tx])
    then have "t\<in>{\<langle>x,powz(IntegerAddition`\<langle>r,s\<rangle>,x)\<rangle>. x\<in>G}" using t(2) by blast
  }
  then have A2:"{\<langle>x,powz(r,x)\<cdot>powz(s,x)\<rangle>. x\<in>G} \<subseteq> {\<langle>x,powz(IntegerAddition`\<langle>r,s\<rangle>,x)\<rangle>. x\<in>G}"
    by blast
  from A1 A2 have A:"{\<langle>x,powz(IntegerAddition`\<langle>r,s\<rangle>,x)\<rangle>. x\<in>G} = {\<langle>x,powz(r,x)\<cdot>powz(s,x)\<rangle>. x\<in>G}"
    by blast
  have E:"S`(IntegerAddition`\<langle>r,s\<rangle>) = {\<langle>x,powz(r,x)\<cdot>powz(s,x)\<rangle>. x\<in>G}"
    using Q by (simp only: A)
  have "\<langle>g,powz(r,g)\<cdot>powz(s,g)\<rangle>\<in>{\<langle>x,powz(r,x)\<cdot>powz(s,x)\<rangle>. x\<in>G}"
    using as(3) by blast
  then have "\<langle>g,powz(r,g)\<cdot>powz(s,g)\<rangle>\<in> S`(IntegerAddition`\<langle>r,s\<rangle>)"
    by (simp only: E)
  from apply_equality[OF this SS_fun] have B:"S`(IntegerAddition`\<langle>r,s\<rangle>)`g = powz(r,g)\<cdot>powz(s,g)"
    by blast
  have "\<langle>r,{\<langle>x,powz(r,x)\<rangle>. x\<in>G}\<rangle>\<in>S"
    unfolding S_def using as(1) by blast
  then have Qr:"S`r = {\<langle>x,powz(r,x)\<rangle>. x\<in>G}"
    using apply_equality[OF _ S_fun] by blast
  have "\<langle>g,powz(r,g)\<rangle>\<in>{\<langle>x,powz(r,x)\<rangle>. x\<in>G}" using as(3) by blast
  then have "\<langle>g,powz(r,g)\<rangle>\<in> S`r"
    by (simp only: Qr)
  from apply_equality[OF this SS_r_fun]
    have C:"S`r`g = powz(r,g)".
  have "\<langle>s,{\<langle>x,powz(s,x)\<rangle>. x\<in>G}\<rangle>\<in>S"
    unfolding S_def using as(2) by blast
  then have Qr:"S`s = {\<langle>x,powz(s,x)\<rangle>. x\<in>G}"
    using apply_equality[OF _ S_fun] by blast
  have "\<langle>g,powz(s,g)\<rangle>\<in>{\<langle>x,powz(s,x)\<rangle>. x\<in>G}" using as(3) by blast
  then have "\<langle>g,powz(s,g)\<rangle>\<in> S`s"
    by (simp only: Qr)
  from apply_equality[OF this SS_s_fun]
    have D:"S`s`g = powz(s,g)".
  from B show "S ` (IntegerAddition` \<langle>r, s\<rangle>) ` g = P ` \<langle>(S ` r) ` g, (S ` s) ` g\<rangle>"
    unfolding groper_def by (simp only:C D)
qed

text\<open>Same as before, but not pointwise\<close>

lemma(in abelian_group) group_action_int_add_morphism_fun:
  defines "S \<equiv> {\<langle>z,{\<langle>x,powz(z,x)\<rangle>. x\<in>G}\<rangle>. z\<in>int}"
  shows "\<forall>r\<in>int. \<forall>s\<in>int. S ` (IntegerAddition` \<langle>r, s\<rangle>) = EndAdd(G,P) ` \<langle>(S ` r), (S ` s)\<rangle>"
proof(safe)
  have S_fun:"S:int\<rightarrow>End(G,P)" using int0_abgroup.powz_maps_int_End
    unfolding S_def powz_def by blast
  fix r s assume as:"r:int" "s:int"
  {
    fix h assume h:"h\<in>G"
    then have "h\<cdot>\<one> = h" using group0_2_L2 by auto
    with h have "h\<in>P``(G\<times>G)" using imageI[of "\<langle>h,\<one>\<rangle>" h P "G\<times>G"]
      using apply_Pair[OF group_oper_fun, of "\<langle>h,\<one>\<rangle>"]
      group0_2_L2(1) by auto
  }
  with range_image_domain[OF group_oper_fun] have "G\<subseteq> range(P)" by auto moreover
  have "range(P) \<subseteq> G" using func1_1_L5B[OF group_oper_fun]. ultimately
  have eq:"range(P) = G" by auto
  from S_fun have endo:"S`r\<in>End(G,P)" "S`s:End(G,P)"
    using apply_type[of S int "\<lambda>_. End(G,P)" r]
    apply (simp only:as) using apply_type[of S int "\<lambda>_. End(G,P)" s] S_fun
    by (simp only:as)
  with eq have SRSS:"S`r:G\<rightarrow>range(P)" "S`s:G\<rightarrow>range(P)" unfolding End_def by auto
  {
    fix g assume g:"g\<in>G"
    with as group_action_int_add_morphism have EE:"S`(IntegerAddition` \<langle>r, s\<rangle>)`g = P ` \<langle>S ` r ` g, S ` s ` g\<rangle>"
      unfolding S_def by blast
    with func_ZF_1_L4[OF group_oper_fun _ _ _ g, of _ "S`r" "S`s"]
     SRSS have "(P {lifted to function space over} G) ` \<langle>S ` r, S ` s\<rangle> ` g = P ` \<langle>S ` r ` g, S ` s ` g\<rangle>"
      by blast
    then have "(P {lifted to function space over} G) ` \<langle>S ` r, S ` s\<rangle> ` g = S`(IntegerAddition` \<langle>r, s\<rangle>)`g"
      by (simp only:EE)
  }
  then have R:"\<And>x. x \<in> G \<Longrightarrow> (P {lifted to function space over} G) ` \<langle>S ` r, S ` s\<rangle> ` x = S`(IntegerAddition` \<langle>r, s\<rangle>) ` x" by blast
  from as have "\<langle>r,s\<rangle>\<in>int\<times>int" unfolding Sigma_def by blast
  then have int:"IntegerAddition`\<langle>r, s\<rangle>\<in>int" 
    using apply_type[of IntegerAddition "int\<times>int" "\<lambda>_. int" "\<langle>r,s\<rangle>"]
    by (simp only: Int_ZF_1_L1(1))
  then have f:"S`(IntegerAddition` \<langle>r, s\<rangle>):G\<rightarrow>G" using S_fun
    apply_type[of S int "\<lambda>_. End(G,P)" "IntegerAddition ` \<langle>r, s\<rangle>"] unfolding End_def S_def
    by blast
  from func_ZF_1_L3[OF group_oper_fun, of _ G] SRSS
  have "(P {lifted to function space over} G) ` \<langle>S ` r, S ` s\<rangle> : G\<rightarrow>range(P)"
    using apply_type by auto
  from fun_extension[OF this f R] have A:"S ` (IntegerAddition ` \<langle>r, s\<rangle>) = (P {lifted to function space over} G) ` \<langle>S ` r, S ` s\<rangle>"
    by (simp only:) 
  have "\<langle>S`r,S`s\<rangle>\<in>End(G,P)\<times>End(G,P)" using endo by blast
  then have "(P {lifted to function space over} G) ` \<langle>S ` r, S ` s\<rangle> = restrict(P {lifted to function space over} G, End(G,P)\<times>End(G,P)) ` \<langle>S ` r, S ` s\<rangle>"
    using restrict[of "P {lifted to function space over} G" "End(G,P)\<times>End(G,P)" "\<langle>S`r,S`s\<rangle>"] apply (simp only:) by simp
  with A show " S ` (IntegerAddition ` \<langle>r, s\<rangle>) = EndAdd(G, P) ` \<langle>S ` r, S ` s\<rangle> " unfolding EndAdd_def by (simp only:)
qed

text\<open>The action is a homomorphism between $(\mathbb{Z},\cdot)$ and $(G\to G, \circ)$\<close>

lemma(in abelian_group) group_action_int_mult_morphism:
  defines "S \<equiv> {\<langle>z,{\<langle>x,powz(z,x)\<rangle>. x\<in>G}\<rangle>. z\<in>int}"
  shows "\<forall>r\<in>int. \<forall>s\<in>int. S ` (IntegerMultiplication` \<langle>r, s\<rangle>) = EndMult(G,P)`\<langle>S`r,S`s\<rangle>"
proof(safe)
  have S_fun:"S:int\<rightarrow>End(G,P)" using int0_abgroup.powz_maps_int_End
    unfolding S_def powz_def by blast
  fix r s assume as:"r:int" "s:int"
  from as have int:"IntegerMultiplication`\<langle>r,s\<rangle>\<in>int" using
    int0_abgroup.ints.Int_ZF_1_1_L5(3) by (simp only:)
  from int have Srs:"S`(IntegerMultiplication`\<langle>r,s\<rangle>):G\<rightarrow>G"
    using apply_type[OF S_fun] unfolding End_def by blast
  from as(1) have Sr:"S`r:G\<rightarrow>G"
    using apply_type[OF S_fun] unfolding End_def by blast
  from as(2) have Ss:"S`s:G\<rightarrow>G"
    using apply_type[OF S_fun] unfolding End_def by blast
  {
    fix g assume g:"g\<in>G"
    from int have "\<langle>IntegerMultiplication`\<langle>r,s\<rangle>,{\<langle>x,powz(IntegerMultiplication`\<langle>r,s\<rangle>,x)\<rangle>. x\<in>G}\<rangle>\<in>S"
      unfolding S_def by blast
    then have "S`(IntegerMultiplication`\<langle>r,s\<rangle>) = {\<langle>x,powz(IntegerMultiplication`\<langle>r,s\<rangle>,x)\<rangle>. x\<in>G}"
      using apply_equality[OF _ S_fun] by (simp only:)
    moreover
    
    have "\<langle>g,powz(IntegerMultiplication`\<langle>r,s\<rangle>,g)\<rangle>\<in>{\<langle>x,powz(IntegerMultiplication`\<langle>r,s\<rangle>,x)\<rangle>. x\<in>G}"
      using g by blast
    ultimately have "\<langle>g,powz(IntegerMultiplication`\<langle>r,s\<rangle>,g)\<rangle>\<in>S`(IntegerMultiplication`\<langle>r,s\<rangle>)"
      by (simp only:)
    then have "S`(IntegerMultiplication`\<langle>r,s\<rangle>)`g = powz(IntegerMultiplication`\<langle>r,s\<rangle>,g)"
      using apply_equality[OF _ Srs] by (simp only:)
    then have "S`(IntegerMultiplication`\<langle>r,s\<rangle>)`g = powz(IntegerMultiplication`\<langle>s,r\<rangle>,g)"
      using int0.Int_ZF_1_1_L5(5) as by (simp only:)
    then have A:"S`(IntegerMultiplication`\<langle>r,s\<rangle>)`g = powz(r,powz(s,g))"
      using int0_abgroup.powz_mult[OF as(2,1) g] unfolding powz_def by (simp only:)
    have "\<langle>s,{\<langle>x,powz(s,x)\<rangle>. x\<in>G}\<rangle>\<in>S" using as(2) unfolding S_def by blast
    then have "S`s = {\<langle>x,powz(s,x)\<rangle>. x\<in>G}" using apply_equality[OF _ S_fun]
      by (simp only:)
    then have "\<langle>g,powz(s,g)\<rangle>\<in>S`s" using g by auto
    then have B:"(S`s)`g = powz(s,g)" using apply_equality Ss by auto
    have "\<langle>r,{\<langle>x,powz(r,x)\<rangle>. x\<in>G}\<rangle>\<in>S" using as(1) unfolding S_def by blast
    then have "S`r = {\<langle>x,powz(r,x)\<rangle>. x\<in>G}" using apply_equality[OF _ S_fun]
      by (simp only:)
    then have "\<langle>powz(s,g),powz(r,powz(s,g))\<rangle>\<in>S`r" using int0_abgroup.powz_type[OF as(2) g]
      unfolding powz_def by auto
    then have C:"(S`r)`powz(s,g) = powz(r,powz(s,g))" using apply_equality Sr by auto
    with A B have "S`(IntegerMultiplication`\<langle>r,s\<rangle>)`g = (S`r)`((S`s)`g)" 
      by (simp only:)
    then have G:"S`(IntegerMultiplication`\<langle>r,s\<rangle>)`g = ((S`r)O(S`s))`g" 
      using comp_fun_apply[OF Ss g] by (simp only:)
    then have "S`(IntegerMultiplication`\<langle>r,s\<rangle>)`g = (Composition(G)`\<langle>S`r,S`s\<rangle>)`g"
      using func_ZF_5_L2 Ss Sr by (simp only:)
  }
  then have R:"\<And>g. g\<in>G \<Longrightarrow> S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = (Composition(G)`\<langle>S`r,S`s\<rangle>)`g" by blast
  have B:"(Composition(G)`\<langle>S`r,S`s\<rangle>):G\<rightarrow>G" using apply_type[OF func_ZF_5_L1] Sr Ss by auto
  have L:"S ` (IntegerMultiplication ` \<langle>r, s\<rangle>) = Composition(G) ` \<langle>S ` r, S ` s\<rangle>"
    using fun_extension[OF Srs B R] by blast
  have "\<langle>S`r,S`s\<rangle>\<in>End(G,P)\<times>End(G,P)" using apply_type[OF S_fun as(1)] apply_type[OF S_fun as(2)] 
    by (simp only:)
  then have "restrict(Composition(G),End(G,P)\<times>End(G,P))`\<langle>S`r,S`s\<rangle> = Composition(G) ` \<langle>S ` r, S ` s\<rangle>"
    using restrict[of "Composition(G)" "End(G,P)\<times>End(G,P)" "\<langle>S`r,S`s\<rangle>"] by auto
  with L show "S ` (IntegerMultiplication ` \<langle>r, s\<rangle>) = EndMult(G, P) ` \<langle>S ` r, S ` s\<rangle>" unfolding EndMult_def S_def
    by (simp only:)
qed

text\<open>The unit is the identity\<close>

lemma (in abelian_group) group_action_int_unit:
  defines "S \<equiv> {\<langle>z,{\<langle>x,powz(z,x)\<rangle>. x\<in>G}\<rangle>. z\<in>int}"
  shows "S ` TheNeutralElement(int, IntegerMultiplication) =
    TheNeutralElement(End(G, P), EndMult(G, P))"
proof-
  have S_fun:"S \<in> int \<rightarrow> End(G, P)" using int0_abgroup.powz_maps_int_End
    unfolding S_def powz_def by blast
  have "TheNeutralElement(int, IntegerMultiplication)\<in>int"
    using int0.int_zero_one_are_int(2).
  then have "\<langle>TheNeutralElement(int, IntegerMultiplication),{\<langle>x,powz(TheNeutralElement(int, IntegerMultiplication),x)\<rangle>. x\<in>G}\<rangle>\<in>S"
    unfolding S_def by blast
  then have "S`TheNeutralElement(int, IntegerMultiplication) = {\<langle>x,powz(TheNeutralElement(int, IntegerMultiplication),x)\<rangle>. x\<in>G}"
    using apply_equality[OF _ S_fun] by blast
  then have "S`TheNeutralElement(int, IntegerMultiplication) = {\<langle>x,int0_abgroup.powz($#1,x)\<rangle>. x\<in>G}"
    using int0.Int_ZF_1_L8(2) unfolding powz_def by (simp only:)
  moreover
  {
    fix t assume "t\<in>{\<langle>x,int0_abgroup.powz($#1,x)\<rangle>. x\<in>G}"
    then obtain tx where "t=\<langle>tx,int0_abgroup.powz($#1,tx)\<rangle>" "tx\<in>G" by blast
    then have "t=\<langle>tx,tx\<rangle>" using int0_abgroup.int_power_zero_one(2)[of tx] by (simp only:)
    then have "t\<in>id(G)" using idI `tx\<in>G` by auto
  }
  then have K:"{\<langle>x,int0_abgroup.powz($#1,x)\<rangle>. x\<in>G} \<subseteq> id(G)" by blast
  {
    fix t assume "t\<in>id(G)"
    {
      fix p assume "p\<in>G" "t=\<langle>p,p\<rangle>"
      then have "t=\<langle>p,int0_abgroup.powz($#1,p)\<rangle>" using int0_abgroup.int_power_zero_one(2)[of p]
        by (simp only:)
      then have "t\<in>{\<langle>x,int0_abgroup.powz($#1,x)\<rangle>. x\<in>G}" using `p\<in>G` by blast
    }
    from idE[OF `t\<in>id(G)` this] have "t\<in>{\<langle>x,int0_abgroup.powz($#1,x)\<rangle>. x\<in>G}" by (simp only:)
  }
  then have "id(G) \<subseteq> {\<langle>x,int0_abgroup.powz($#1,x)\<rangle>. x\<in>G}"
    by blast
  with K have "{\<langle>x,int0_abgroup.powz($#1,x)\<rangle>. x\<in>G} = id(G)" by blast
  ultimately have "S`TheNeutralElement(int, IntegerMultiplication) = id(G)" by (simp only:)
  then show ?thesis using end_comp_monoid(2) unfolding EndMult_def by (simp only:)
qed

text\<open>The action defines a module\<close>

theorem(in abelian_group) group_action_int:
  defines "S \<equiv> {\<langle>z,{\<langle>x,powz(z,x)\<rangle>. x\<in>G}\<rangle>. z\<in>int}"
  shows "IsLeftModule(int,IntegerAddition,IntegerMultiplication,G,P,S)" unfolding IsLeftModule_def IsAction_def ringHomomor_def IsMorphism_def
proof(safe)
  show "IsAgroup(G,P)" using groupAssum.
  show "P{is commutative on}G" using abelian_group_axioms unfolding abelian_group_def abelian_group_axioms_def by auto
  show "S \<in> int \<rightarrow> End(G, P)" using int0_abgroup.powz_maps_int_End
    unfolding S_def powz_def by blast
  show "IsAring(int, IntegerAddition, IntegerMultiplication)" using int0.Int_ZF_1_1_L2(1).
  show "\<And>r s. r \<in> int \<Longrightarrow>
           s \<in> int \<Longrightarrow> S ` (IntegerAddition ` \<langle>r, s\<rangle>) = EndAdd(G, P) ` \<langle>S ` r,S ` s\<rangle>"
    using group_action_int_add_morphism_fun unfolding S_def by blast
  show "\<And>r s. r \<in> int \<Longrightarrow> s \<in> int \<Longrightarrow> S ` (IntegerMultiplication ` \<langle>r, s\<rangle>) =  EndMult(G, P) ` \<langle>S ` r, S ` s\<rangle>"
    using group_action_int_mult_morphism unfolding S_def by blast
  show "S ` TheNeutralElement(int, IntegerMultiplication) =
    TheNeutralElement(End(G, P), EndMult(G, P))" using group_action_int_unit unfolding S_def EndMult_def.
qed

text\<open>If there is a $\mathbb{Z}$-module on an abelian group,
it is the one found in the previous result\<close>

corollary(in abelian_group) group_action_int_rev:
  assumes "IsLeftModule(int,IntegerAddition,IntegerMultiplication,G,P,S)"
  shows "S={\<langle>z,{\<langle>x,powz(z,x)\<rangle>. x\<in>G}\<rangle>. z\<in>int}"
  using group_action_int assms int0.action_unique[of G P S "{\<langle>z,{\<langle>x,powz(z,x)\<rangle>. x\<in>G}\<rangle>. z\<in>int}"]
  by blast

end