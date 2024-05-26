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

theory IntModule_ZF imports Module_ZF Int_ZF_1 Group_ZF

begin

section \<open>$\mathbb{Z}$ modules\<close>

text\<open>In this section we show that the integers, as a ring, have only one module structure on each abelian group.
We will show that the module structure is unique, but we will also show which action is the one that defines
that module structure.\<close>

text \<open>When $\mathbb{Z}$ acts on a group, that action is unique.\<close>

lemma action_unique:
  assumes "IsLeftModule(int,IntegerAddition,IntegerMultiplication,G,f,S1)" and "IsLeftModule(int,IntegerAddition,IntegerMultiplication,G,f,S2)"
  shows "S1 = S2"
proof-
  have mod0:"module0(int,IntegerAddition,IntegerMultiplication,G,f,S1)"
      "module0(int,IntegerAddition,IntegerMultiplication,G,f,S2)"
    using assms unfolding module0_def IsLeftModule_def ring0_def module0_axioms_def by auto
  {
    fix r assume rg:"r:int"
    have "S1`($#0) = S1 ` TheNeutralElement(int, IntegerAddition)"
      using int0.Int_ZF_1_L8(1) by auto
    then have "\<forall>g\<in>G. (S1`($#0))`g = (S1 ` TheNeutralElement(int, IntegerAddition))`g" by auto
    then have eq:"\<forall>g\<in>G. (S1`($#0))`g = TheNeutralElement(G, f)"
      using module0.mult_zero[OF mod0(1)] by auto
    have "(S1`($#0)):G\<rightarrow>G" using module0.H_val_type(2)[OF mod0(1)]
      rg(1) by auto
    from fun_is_set_of_pairs[OF this] eq
    have "S1`($#0) = {\<langle>g,TheNeutralElement(G, f)\<rangle>. g\<in>G}" by auto
    then have "S1`($#0) = G\<times>{TheNeutralElement(G, f)}" by auto
    then have s1:"(S1`($#0)) = ConstantFunction(G,TheNeutralElement(G, f))"
      unfolding ConstantFunction_def.
    have "S2`($#0) = S2 ` TheNeutralElement(int, IntegerAddition)"
      using int0.Int_ZF_1_L8(1) by auto
    then have "\<forall>g\<in>G. (S2`($#0))`g = (S2 ` TheNeutralElement(int, IntegerAddition))`g" by auto
    then have eq:"\<forall>g\<in>G. (S2`($#0))`g = TheNeutralElement(G, f)"
      using module0.mult_zero[OF mod0(2)] by auto
    have "(S2`($#0)):G\<rightarrow>G" using module0.H_val_type[OF mod0(2)]
      rg(1) by auto
    from fun_is_set_of_pairs[OF this] eq
    have "S2`($#0) = {\<langle>g,TheNeutralElement(G, f)\<rangle>. g\<in>G}" by auto
    then have "S2`($#0) = G\<times>{TheNeutralElement(G, f)}" by auto
    then have "(S2`($#0)) = ConstantFunction(G,TheNeutralElement(G, f))"
      unfolding ConstantFunction_def.
    with s1 have ee:"S1`($#0) = S2`($#0)" by auto
    {
      assume k:"\<langle>r,$#0\<rangle>\<in>IntegerOrder"
      then have kint:"r\<in>int" unfolding IntegerOrder_def by auto
      have "S1 ` r = S2 ` r"
      proof (rule int0.Back_induct_on_int[of r "$#0" "\<lambda>q. S1`q = S2`q"])
        from k show "\<langle>r,$#0\<rangle>\<in>IntegerOrder" .
        from ee show "S1`($#0) = S2`($#0)" .
        {
          fix n assume n:"\<langle>n, $# 0\<rangle> \<in> IntegerOrder" "S1 ` n = S2 ` n"
          from n(1) have nint:"n:int" unfolding IntegerOrder_def by auto
          have minone:"GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication):int"
            using group0.inverse_in_group[OF Int_ZF_1_T2(3)]
            ring0.Ring_ZF_1_L2(2)[OF int0.Int_ZF_1_1_L2(3)] by auto
          {
            fix t assume t:"t\<in>G"
            have "S1 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
                 TheNeutralElement(int, IntegerMultiplication)\<rangle>) `t = 
            (f`\<langle>S1`n`t,S1`(GroupInv(int, IntegerAddition) `
                 TheNeutralElement(int, IntegerMultiplication))`t\<rangle>)"
              using minone nint module0.module_ax2[OF mod0(1)] t by auto
            then have "S1 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
                 TheNeutralElement(int, IntegerMultiplication)\<rangle>) `t = 
            (f`\<langle>S2`n`t,S1`(GroupInv(int, IntegerAddition) `
                 TheNeutralElement(int, IntegerMultiplication))`t\<rangle>)" using n(2) by auto moreover
            from module0.inv_module[OF mod0(1) apply_type[OF module0.H_val_type(2)[OF mod0(1) ring0.Ring_ZF_1_L2(2)[OF int0.Int_ZF_1_1_L2(3)]]]] have
           ex:"\<forall>g\<in>G. S1 ` (GroupInv(int, IntegerAddition) ` TheNeutralElement(int, IntegerMultiplication))` g =
             GroupInv(G, f) ` g" using module0.module_ax4[OF mod0(1)] by auto
          have f1:"S1 ` (GroupInv(int, IntegerAddition) ` TheNeutralElement(int, IntegerMultiplication)): G\<rightarrow>G"
            using module0.H_val_type(2)[OF mod0(1)] ring0.Ring_ZF_1_L2(2)[OF int0.Int_ZF_1_1_L2(3)]
            ring0.Ring_ZF_1_L3(1)[OF int0.Int_ZF_1_1_L2(3)] by auto
          have f2:"GroupInv(G, f) : G\<rightarrow>G"
            using group0_2_T2[of G f] using assms(1) unfolding IsLeftModule_def by blast
          from ex f1 f2 have "S1 ` (GroupInv(int, IntegerAddition) ` TheNeutralElement(int, IntegerMultiplication)) =
            GroupInv(G, f)" using func_eq by blast
          ultimately have A:"S1 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>)`t = 
          f`\<langle>S2`n`t,GroupInv(G, f) `t\<rangle>" by auto
          have "S2 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>)`t = 
          f`\<langle>S2`n`t,S2`(GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication))`t\<rangle>"
            using assms(2) minone nint module0.module_ax2[OF mod0(2)] t by auto
          then have "S2 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>)`t = 
          f`\<langle>S2`n`t,S2`(GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication))`t\<rangle>" using n(2) by auto moreover
          from module0.inv_module[OF mod0(2) apply_type[OF module0.H_val_type(2)[OF mod0(2) ring0.Ring_ZF_1_L2(2)[OF int0.Int_ZF_1_1_L2(3)]]]]
          have ex:"\<forall>g\<in>G. S2 ` (GroupInv(int, IntegerAddition) ` TheNeutralElement(int, IntegerMultiplication))` g =
             GroupInv(G, f) ` g" using module0.module_ax4[OF mod0(2)] by auto
          have f1:"S2 ` (GroupInv(int, IntegerAddition) ` TheNeutralElement(int, IntegerMultiplication)): G\<rightarrow>G"
            using module0.H_val_type(2)[OF mod0(2)] ring0.Ring_ZF_1_L2(2)[OF int0.Int_ZF_1_1_L2(3)]
            ring0.Ring_ZF_1_L3(1)[OF int0.Int_ZF_1_1_L2(3)] by auto
          from ex f1 f2 have "S2 ` (GroupInv(int, IntegerAddition) ` TheNeutralElement(int, IntegerMultiplication)) =
            GroupInv(G, f)" using func_eq by blast
          ultimately have "S2 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>)`t = 
          f`\<langle>S2`n`t,GroupInv(G, f)`t\<rangle>"
            by auto
          with A have "S1 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>)`t =S2 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>)`t" by auto
        }
        then have "\<forall>t\<in>G. S1 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>)`t =S2 ` (IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>)`t" by auto
        moreover from minone nint have "IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>:int"
          using group0.group_op_closed[OF Int_ZF_1_T2(3)] by auto
        then have "S1`(IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>):G\<rightarrow>G" "S2`(IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>):G\<rightarrow>G" using module0.H_val_type(2)[OF mod0(1)]
          module0.H_val_type(2)[OF mod0(2)] by auto
        ultimately have "S1`(IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) ` TheNeutralElement(int, IntegerMultiplication)\<rangle>) = S2`(IntegerAddition ` \<langle>n, GroupInv(int, IntegerAddition) ` TheNeutralElement(int, IntegerMultiplication)\<rangle>)"
          using func_eq[of _ G G] by auto
      }
      then show " \<forall>n. \<langle>n, $# 0\<rangle> \<in> IntegerOrder \<and> S1 ` n = S2 ` n \<longrightarrow>
          S1 `
          (IntegerAddition `
           \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>) =
          S2 `
          (IntegerAddition `
           \<langle>n, GroupInv(int, IntegerAddition) `
               TheNeutralElement(int, IntegerMultiplication)\<rangle>)" by auto
      qed
    }
    moreover
    {
      assume k:"\<langle>$#0,r\<rangle>\<in>IntegerOrder"
      then have kint:"r\<in>int" unfolding IntegerOrder_def by auto
      have "S1 ` r = S2 ` r"
      proof (rule int0.Induction_on_int[of "$#0" r "\<lambda>q. S1`q = S2`q"])
        from k show "\<langle>$#0,r\<rangle>\<in>IntegerOrder" .
        from ee show "S1 ` ($# 0) = S2 ` ($# 0)" .
        {
          fix m assume m:"\<langle>$# 0, m\<rangle> \<in> IntegerOrder" "S1 ` m = S2 ` m"
          from m(1) have mint:"m\<in>int" unfolding IntegerOrder_def by auto
          have n:"TheNeutralElement(int, IntegerMultiplication)\<in>int"
            using ring0.Ring_ZF_1_L2(2)[OF int0.Int_ZF_1_1_L2(3)].
          {
            fix t assume t:"t\<in>G"
            have "S1 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>)`t = 
            f`\<langle>S1`m`t,S1`(TheNeutralElement(int, IntegerMultiplication))`t\<rangle>"
              using assms(1) mint n t module0.module_ax2[OF mod0(1)] by auto
            then have "S1 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>)`t = 
            f`\<langle>S2`m`t,t\<rangle>"
              using module0.module_ax4[OF mod0(1)] m(2) t by auto
            moreover
            have "S2 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>)`t = 
            f`\<langle>S2`m`t,S2`(TheNeutralElement(int, IntegerMultiplication))`t\<rangle>"
            using assms(2) mint n t module0.module_ax2[OF mod0(2)] by auto
          then have "S2 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>)`t = 
          f`\<langle>S2`m`t,t\<rangle>"
            using module0.module_ax4[OF mod0(2)] m(2) t by auto
          ultimately
          have "S1 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>)`t = 
            S2 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>)`t" by auto
        }
        then have "\<forall>t\<in>G. S1 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>)`t = 
            S2 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>)`t" by auto
        moreover from n mint have "IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>:int"
          using group0.group_op_closed[OF Int_ZF_1_T2(3)] by auto
        then have "S1`(IntegerAddition ` \<langle>m,
               TheNeutralElement(int, IntegerMultiplication)\<rangle>):G\<rightarrow>G" "S2`(IntegerAddition ` \<langle>m,
               TheNeutralElement(int, IntegerMultiplication)\<rangle>):G\<rightarrow>G" using module0.H_val_type(2)[OF mod0(1)]
          module0.H_val_type(2)[OF mod0(2)] by auto
        ultimately have "S1`(IntegerAddition ` \<langle>m,TheNeutralElement(int, IntegerMultiplication)\<rangle>) = S2`(IntegerAddition ` \<langle>m,TheNeutralElement(int, IntegerMultiplication)\<rangle>)"
          using func_eq[of _ G G] by auto
      }
      then show "\<forall>m. \<langle>$# 0, m\<rangle> \<in> IntegerOrder \<and> S1 ` m = S2 ` m \<longrightarrow>
          S1 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>) =
          S2 ` (IntegerAddition ` \<langle>m, TheNeutralElement(int, IntegerMultiplication)\<rangle>)" by auto
      qed
    } moreover note int0.Int_ZF_2_T1(2)
    ultimately have "S1`r = S2`r" unfolding IsTotal_def using rg(1)
      int0.Int_ZF_1_L8(1) ring0.Ring_ZF_1_L2(1)[OF int0.Int_ZF_1_1_L2(3)] by auto
  }
  then have "\<forall>r\<in>int. S1`r = S2`r" by auto
  from func_eq[OF _ _ this] show "S1 = S2" using 
      module0.mAction[OF mod0(1)] module0.mAction[OF mod0(2)]
      unfolding IsAction_def ringHomomor_def by auto
qed

text \<open>The action we will show works is $n\mapsto (g\mapsto g^n)$.
It is a well-defined function\<close>

lemma(in abelian_group) group_action_int_fun:
  defines "S \<equiv> {\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}\<union> {\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
  shows "S:int \<rightarrow> End(G,P)" unfolding Pi_def apply simp unfolding function_def
proof-
  {
    fix n assume n:"n\<in>nat"
    {
      fix x na assume x:"x\<in>G" "na\<in>nat"
      have "Fold(P,\<one>,na\<times>{x})\<in>G" using fold_props(2)[OF x(2) group_oper_fun,
            of "ConstantFunction(na,x)"] group0_2_L2(1) func1_3_L1[OF x(1)] group0_2_L2 unfolding ConstantFunction_def
        by auto
    }
    then have FG:"\<forall>n\<in>nat. \<forall>x\<in>G. Fold(P,\<one>,n\<times>{x})\<in>G" by auto
    then have fun:"{\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}:G\<rightarrow>G" using ZF_fun_from_total n by auto
    {
      fix x assume x:"x\<in>G"
      then have "{\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}`x = Fold(P,\<one>, n\<times>{x})"
        using ZF_fun_from_tot_val0[OF fun] by auto
    }
    then have rule:"\<forall>x\<in>G. {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}`x = Fold(P,\<one>, n\<times>{x})" by auto
    {
      fix x y assume xy:"x:G" "y:G"
      then have A:"P`\<langle>{\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}`x,{\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}`y\<rangle> = P`\<langle>Fold(P,\<one>, n\<times>{x}),Fold(P,\<one>, n\<times>{y})\<rangle>"
        using rule by auto
      have "P`\<langle>Fold(P,\<one>, n\<times>{x}),Fold(P,\<one>, n\<times>{y})\<rangle> = Fold(P,\<one>, n\<times>{P`\<langle>x,y\<rangle>})"
      proof(rule nat_induct[of n "\<lambda>t. P`\<langle>Fold(P,\<one>, t\<times>{x}),Fold(P,\<one>, t\<times>{y})\<rangle> = Fold(P,\<one>, t\<times>{P`\<langle>x,y\<rangle>})"])
        from n show "n\<in>nat".
        have " Fold(P, \<one>, 0) = \<one>" using fold_empty[OF group_oper_fun] group0_2_L2(1)
          by auto
        then have "\<one>\<cdot>\<one> = \<one> \<Longrightarrow> P ` \<langle>Fold(P, \<one>, 0 \<times> {x}), Fold(P, \<one>, 0 \<times> {y})\<rangle> = Fold(P, \<one>, 0 \<times> {P ` \<langle>x, y\<rangle>})"
          by auto
        then show "P ` \<langle>Fold(P, \<one>, 0 \<times> {x}), Fold(P, \<one>, 0 \<times> {y})\<rangle> = Fold(P, \<one>, 0 \<times> {P ` \<langle>x, y\<rangle>})"
          using group0_2_L2 by auto
        {
          fix xa assume as:"xa\<in>nat" "P ` \<langle>Fold(P, \<one>, xa \<times> {x}), Fold(P, \<one>, xa \<times> {y})\<rangle> =
            Fold(P, \<one>, xa \<times> {P ` \<langle>x, y\<rangle>})"
          have dd:"domain(xa\<times>{x}) = xa" by auto
          then have e:"succ(xa) \<times> {x}= Append(xa\<times>{x},x)"
            unfolding Append_def by auto
          have dd:"domain(xa\<times>{P`\<langle>x,y\<rangle>}) = xa" by auto
          then have u:"succ(xa)\<times>{P`\<langle>x,y\<rangle>} = Append(xa\<times>{P`\<langle>x,y\<rangle>},P`\<langle>x,y\<rangle>)" unfolding Append_def
            by auto
          have "Fold(P, \<one>, succ(xa) \<times> {x}) = Fold(P, \<one>, Append(xa\<times>{x},x))" using subst[OF e, of "\<lambda>t. Fold(P,\<one>,succ(xa) \<times> {x}) = Fold(P,\<one>,t)"]
            by (simp only:refl)
          then have XX:"Fold(P, \<one>, succ(xa) \<times> {x}) =P ` \<langle>Fold(P, \<one>, xa\<times>{x}), x\<rangle>" using fold_append(2)[OF as(1) group_oper_fun
            func1_3_L1[OF xy(1), of xa] _ xy(1)] group0_2_L2 unfolding ConstantFunction_def
            by (simp only:trans)
          have "domain(xa\<times>{y}) = xa" by auto
          then have e:"succ(xa) \<times> {y}= Append(xa\<times>{y},y)"
            unfolding Append_def by auto
          have ff:"(xa \<times> {P ` \<langle>x, y\<rangle>}):xa \<rightarrow> G" using func1_3_L1[OF group_op_closed[OF xy]]
            unfolding ConstantFunction_def by auto
          have g:"x\<cdot>y = P`\<langle>x,y\<rangle>" by auto
          have "Fold(P, \<one>, succ(xa) \<times> {y}) = Fold(P, \<one>, Append(xa\<times>{y},y))" using subst[OF e, of "\<lambda>t. Fold(P,\<one>,succ(xa) \<times> {y}) = Fold(P,\<one>,t)"]
            by (simp only:refl)
          then have YY:"Fold(P, \<one>, succ(xa) \<times> {y}) =P ` \<langle>Fold(P, \<one>, xa\<times>{y}), y\<rangle>" using fold_append(2)[OF as(1) group_oper_fun
            func1_3_L1[OF xy(2), of xa] _ xy(2)] group0_2_L2 unfolding ConstantFunction_def
            by (simp only:trans)
          with XX have "P`\<langle>Fold(P, \<one>, succ(xa) \<times> {x}),Fold(P, \<one>, succ(xa) \<times> {y})\<rangle>= P`\<langle>P ` \<langle>Fold(P, \<one>, xa\<times>{x}), x\<rangle>,P ` \<langle>Fold(P, \<one>, xa\<times>{y}), y\<rangle>\<rangle>"
            by auto
          with FG as(1) xy have "P`\<langle>Fold(P, \<one>, succ(xa) \<times> {x}),Fold(P, \<one>, succ(xa) \<times> {y})\<rangle>= P`\<langle>P ` \<langle>Fold(P, \<one>, xa\<times>{x}), Fold(P, \<one>, xa\<times>{y})\<rangle>,P`\<langle>x, y\<rangle>\<rangle>" 
            using group0_4_L8(3)[OF _ _ xy(1) _ xy(2), of "Fold(P, \<one>, xa\<times>{x})" "Fold(P, \<one>, xa\<times>{y})"] abelian_group_axioms unfolding
            abelian_group_def abelian_group_axioms_def by auto
          with as(2) have "P`\<langle>Fold(P, \<one>, succ(xa) \<times> {x}),Fold(P, \<one>, succ(xa) \<times> {y})\<rangle>= P`\<langle>Fold(P, \<one>, xa \<times> {P ` \<langle>x, y\<rangle>}),P`\<langle>x, y\<rangle>\<rangle>"
            by auto
          then have "P`\<langle>Fold(P, \<one>, succ(xa) \<times> {x}),Fold(P, \<one>, succ(xa) \<times> {y})\<rangle>= Fold(P, \<one>, Append(xa \<times> {P ` \<langle>x, y\<rangle>},P ` \<langle>x, y\<rangle>))"
            using fold_append(2)[OF as(1) group_oper_fun ff, of _ "P`\<langle>x,y\<rangle>", THEN sym] group_op_closed[OF xy]
            g group0_2_L2 by (simp only:trans)
          then show "P ` \<langle>Fold(P, \<one>, succ(xa) \<times> {x}), Fold(P, \<one>, succ(xa) \<times> {y})\<rangle> =
            Fold(P, \<one>, succ(xa) \<times> {P ` \<langle>x, y\<rangle>})" using subst[of _ _ "\<lambda>t. P ` \<langle>Fold(P, \<one>, succ(xa) \<times> {x}), Fold(P, \<one>, succ(xa) \<times> {y})\<rangle> =
            Fold(P, \<one>,t)", OF u[THEN sym]] by blast
        }
      qed
      moreover
      from rule have "{\<langle>x, Fold(P, \<one>, n \<times> {x})\<rangle> . x \<in> G} ` (P ` \<langle>x, y\<rangle>) = Fold(P, \<one>, n \<times> {P ` \<langle>x, y\<rangle>})"
        using group_op_closed xy by auto moreover
      note A ultimately
      have "P ` \<langle>{\<langle>x, Fold(P, \<one>, n \<times> {x})\<rangle> . x \<in> G} ` x, {\<langle>x, Fold(P, \<one>, n \<times> {x})\<rangle> . x \<in> G} ` y\<rangle> =
          {\<langle>x, Fold(P, \<one>, n \<times> {x})\<rangle> . x \<in> G} ` (P ` \<langle>x, y\<rangle>)" by auto
    }
    then have "\<forall>x\<in>G. \<forall>y\<in>G. P ` \<langle>{\<langle>x, Fold(P, \<one>, n \<times> {x})\<rangle> . x \<in> G} ` x, {\<langle>x, Fold(P, \<one>, n \<times> {x})\<rangle> . x \<in> G} ` y\<rangle> =
          {\<langle>x, Fold(P, \<one>, n \<times> {x})\<rangle> . x \<in> G} ` (P ` \<langle>x, y\<rangle>)" by auto
    then have "{\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<in>End(G,P)" unfolding End_def 
      Homomor_def IsMorphism_def
      apply simp using fun by auto moreover
    then have "Composition(G)`\<langle>GroupInv(G,P), {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>\<in>End(G,P)"
      using end_composition[OF end_inverse_group] by auto
    then have "GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<in>End(G,P)"
      using func_ZF_5_L2 fun group0_2_T2 groupAssum by auto
    ultimately have "{\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<in>End(G,P) \<and> GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<in>End(G,P)" by auto
  }
  then have "\<forall>n\<in>nat. {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<in>End(G,P) \<and> GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<in>End(G,P)" by auto
  then have "\<forall>n\<in>nat. \<langle>$# n,{\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>\<in>int\<times>End(G,P) \<and> \<langle>$# $-n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>\<in>int\<times>End(G,P)"
    by auto
  then have A1:"S \<subseteq> int \<times> End(G,P)" unfolding S_def by blast
  have dom:"domain(S) ={$#n. n\<in>nat}\<union>{ $- $# n. n\<in>nat}" unfolding domain_def S_def by auto
  {
    fix z assume z:"z:int"
    {
      assume "znegative(z)"
      then obtain n where n:"z=$- $# succ(n)" "n:nat" using zneg_int_of z by auto
      then have "z\<in>{$- $#n. n\<in>nat}" using nat_succI[of n] by auto
      then have "z\<in>domain(S)" using dom by auto
    } moreover
    {
      assume "\<not>znegative(z)"
      then obtain n where n:"z= $# n" "n:nat" using not_zneg_int_of z by auto
      then have "z\<in>{$#n. n\<in>nat}" using nat_succI[of n] by auto
      then have "z\<in>domain(S)" using dom by auto
    } ultimately
    have "z\<in>domain(S)" by auto
  }
  then have A2:"int \<subseteq> domain(S)" by auto
  {
    fix x y z assume as:"\<langle>x, y\<rangle> \<in> S" "\<langle>x, z\<rangle> \<in> S"
    {
      assume "\<langle>x,y\<rangle>\<in>{\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
      "\<langle>x,z\<rangle>\<in>{\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
      then have "y=z" by auto
    } moreover
    {
      assume "\<langle>x,y\<rangle>\<in>{\<langle>$-$# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
      "\<langle>x,z\<rangle>\<in>{\<langle>$-$# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
      then have "y=z" by auto
    } moreover
    {
      assume "\<langle>x,y\<rangle>\<in>{\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
      "\<langle>x,z\<rangle>\<in>{\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
      then obtain n m where n:"n:nat" "m\<in>nat" "$#n = $- $#m" "$#n=x" "y={\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}"
        "z=GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, m\<times>{x})\<rangle>. x\<in>G}" by auto
      have "\<not>znegative($#n)" using not_znegative_int_of.
      with n(3) have "\<not>znegative($-$#m)" by auto
      then have "$#m = $# 0" using not_znegative_imp_zero by auto
      then have "x=$#0" using n(3,4) int0.Int_ZF_1_L11 int0.Int_ZF_1_L8(1)
        int0.Int_ZF_1_L9A[of "$#0"] int0.Int_ZF_1_L8A(1) by auto
      with n(4) have nz:"n=0" using int_of_inject n(1) by auto
      with n(5) have "y={\<langle>x,Fold(P,\<one>,0)\<rangle>. x\<in>G}" by auto
      then have y:"y=G\<times>{Fold(P,\<one>,0)}" by auto
      from n(3) \<open>n=0\<close> have "$-$#m = $#0" by auto
      then have "$-$-$#m = $-$#0" by auto
      then have "$# m = $-$#0" using zminus_zminus by auto
      then have "$# m = $#0" by auto
      then have mz:"m= 0" using int_of_inject n(2) by auto
      {
        fix u assume u:"u\<in>z"
        with n(6) mz have "u\<in>GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}" by auto
        then obtain u1 u2 u3 where u:"u=\<langle>u1,u3\<rangle>" "\<langle>u1,u2\<rangle>\<in>{\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}"
          "\<langle>u2,u3\<rangle>\<in>GroupInv(G,P)" unfolding comp_def by auto
        from u(2) have "u2=Fold(P,\<one>, 0)" by auto
        then have u2:"u2=\<one>" using fold_empty[OF group_oper_fun]
          group0_2_L2 by auto
        with u(3) have "\<one>\<cdot>u3 = \<one>" "u3:G" unfolding GroupInv_def by auto
        then have "u3=\<one>" using group0_2_L2 by auto
        with u2 have "u2=u3" by auto
        with u(1,2) have "u\<in>{\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}" by auto
      }
      then have "z \<subseteq> {\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}" by auto
      with y have "z \<subseteq> y" by auto moreover
      {
        fix t assume "t:y"
        then have t:"t:G\<times>{Fold(P,\<one>, 0)}" using y by auto
        then have "t:G\<times>{\<one>}" using fold_empty[OF group_oper_fun]
          group0_2_L2 by auto
        then obtain g where g:"g\<in>G" "t=\<langle>g,\<one>\<rangle>" by auto
        moreover have "\<langle>\<one>,\<one>\<rangle>\<in>GroupInv(G,P)"
          unfolding GroupInv_def using group0_2_L2 by auto
        with g have "t\<in>GroupInv(G,P) O (G\<times>{\<one>})" by auto
        then have "t\<in>GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}"
          using fold_empty[OF group_oper_fun]
          group0_2_L2 by force
        then have "t\<in>GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, m\<times>{x})\<rangle>. x\<in>G}" using mz
          by auto
        then have "t:z" using n(6) by auto
      }
      then have "y\<subseteq>z" by auto ultimately
      have "y=z" by auto
    } moreover
    {
      assume "\<langle>x,z\<rangle>\<in>{\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
      "\<langle>x,y\<rangle>\<in>{\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
      then obtain n m where n:"n:nat" "m\<in>nat" "$#n = $- $#m" "$#n=x" "z={\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}"
        "y=GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, m\<times>{x})\<rangle>. x\<in>G}" by auto
      have "\<not>znegative($#n)" using not_znegative_int_of.
      with n(3) have "\<not>znegative($-$#m)" by auto
      then have "$#m = $# 0" using not_znegative_imp_zero by auto
      then have "x=$#0" using n(3,4) int0.Int_ZF_1_L11 int0.Int_ZF_1_L8(1)
        int0.Int_ZF_1_L9A[of "$#0"] int0.Int_ZF_1_L8A(1) by auto
      with n(4) have nz:"n=0" using int_of_inject n(1) by auto
      with n(5) have "z={\<langle>x,Fold(P,\<one>,0)\<rangle>. x\<in>G}" by auto
      then have y:"z=G\<times>{Fold(P,\<one>,0)}" by auto
      from n(3) \<open>n=0\<close> have "$-$#m = $#0" by auto
      then have "$-$-$#m = $-$#0" by auto
      then have "$# m = $-$#0" using zminus_zminus by auto
      then have "$# m = $#0" by auto
      then have mz:"m= 0" using int_of_inject n(2) by auto
      {
        fix u assume u:"u\<in>y"
        with n(6) mz have "u\<in>GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}" by auto
        then obtain u1 u2 u3 where u:"u=\<langle>u1,u3\<rangle>" "\<langle>u1,u2\<rangle>\<in>{\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}"
          "\<langle>u2,u3\<rangle>\<in>GroupInv(G,P)" unfolding comp_def by auto
        from u(2) have "u2=Fold(P,\<one>, 0)" by auto
        then have u2:"u2=\<one>" using fold_empty[OF group_oper_fun]
          group0_2_L2 by auto
        with u(3) have "\<one>\<cdot>u3 = \<one>" "u3:G" unfolding GroupInv_def by auto
        then have "u3=\<one>" using group0_2_L2 by auto
        with u2 have "u2=u3" by auto
        with u(1,2) have "u\<in>{\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}" by auto
      }
      then have "y \<subseteq> {\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}" by auto
      with y have "y \<subseteq> z" by auto moreover
      {
        fix t assume "t:z"
        then have t:"t:G\<times>{Fold(P,\<one>, 0)}" using y by auto
        then have "t:G\<times>{\<one>}" using fold_empty[OF group_oper_fun]
          group0_2_L2 by auto
        then obtain g where g:"g\<in>G" "t=\<langle>g,\<one>\<rangle>" by auto
        moreover have "\<langle>\<one>,\<one>\<rangle>\<in>GroupInv(G,P)"
          unfolding GroupInv_def using group0_2_L2 by auto
        with g have "t\<in>GroupInv(G,P) O (G\<times>{\<one>})" by auto
        then have "t\<in>GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, 0)\<rangle>. x\<in>G}"
          using fold_empty[OF group_oper_fun]
          group0_2_L2 by force
        then have "t\<in>GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, m\<times>{x})\<rangle>. x\<in>G}" using mz
          by auto
        then have "t:y" using n(6) by auto
      }
      then have "z\<subseteq>y" by auto ultimately
      have "y=z" by auto
    } moreover note as
    ultimately have "y=z" unfolding S_def by auto
  }
  then have "\<forall>x y. \<langle>x, y\<rangle> \<in> S \<longrightarrow> (\<forall>z. \<langle>x, z\<rangle> \<in> S \<longrightarrow> y = z)" by auto
  with A1 A2 show "S \<subseteq> int \<times> End(G, P) \<and>
    int \<subseteq> domain(S) \<and> (\<forall>x y. \<langle>x, y\<rangle> \<in> S \<longrightarrow> (\<forall>y'. \<langle>x, y'\<rangle> \<in> S \<longrightarrow> y = y'))" by auto
qed

text\<open>The action is defined on positive and negative numbers by the following
folds:\<close>

lemma(in abelian_group) group_action_int_dest:
  defines "S \<equiv> {\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}\<union> {\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
  assumes "n\<in>nat" "x\<in>G"
  shows "(S`($#n))`x =Fold(P,\<one>,n\<times>{x})" "(S`($- $#n))`x =Fold(P,\<one>,n\<times>{x})\<inverse>"
proof-
  have "S`($#n) = {\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}" unfolding S_def
    apply(rule apply_equality[OF _ group_action_int_fun]) using assms(2) by auto
  then have "(S`($#n))`x = {\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}`x" by auto
  then show "(S`($#n))`x =Fold(P,\<one>,n\<times>{x})" using apply_equality[OF
    lamI[OF assms(3),of "\<lambda>t. Fold(P,\<one>,n\<times>{t})"]] lam_funtype
    lambda_fun_alt[of G "\<lambda>t. Fold(P,\<one>,n\<times>{t})"] by auto
  have "S`($- $#n) =GroupInv(G,P) O {\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}" unfolding S_def
    apply(rule apply_equality[OF _ group_action_int_fun]) using assms(2) by auto
  then have "(S`($- $#n))`x = (GroupInv(G,P) O {\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G})`x" by auto
  then have "(S`($- $#n))`x = GroupInv(G,P)`({\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}`x)"
    using comp_fun_apply[OF lam_funtype assms(3)]
    lambda_fun_alt[of G "\<lambda>t. Fold(P,\<one>,n\<times>{t})"] by auto
  then have "(S`($- $#n))`x = GroupInv(G,P)`(Fold(P,\<one>,n\<times>{x}))"
    using apply_equality[OF lamI[OF assms(3), of "\<lambda>t. Fold(P,\<one>,n\<times>{t})"] lam_funtype[of G "\<lambda>t. Fold(P,\<one>,n\<times>{t})"]
   ] lambda_fun_alt[of G "\<lambda>t. Fold(P,\<one>,n\<times>{t})"] by auto
  then show "(S`($- $#n))`x = (Fold(P,\<one>,n\<times>{x}))\<inverse>"
    by auto
qed

text\<open>The action takes 1 to the identity endomorphism\<close>

lemma(in abelian_group) group_action_int_unit:
  defines "S \<equiv> {\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}\<union> {\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
  shows "S`TheNeutralElement(int,IntegerMultiplication) = TheNeutralElement(End(G, P), Composition(G) {in End} [G,P])"
proof-
  have id:"TheNeutralElement(End(G, P), Composition(G) {in End} [G,P]) = id(G)" using end_comp_monoid(2).
  have S:"S`($# 1) = {\<langle>x,Fold(P,\<one>,1\<times>{x})\<rangle>. x\<in>G}"
    using apply_equality[OF _ group_action_int_fun] unfolding S_def by auto
  {
    fix x assume x:"x\<in>G"
    have tail:"Tail(1\<times>{x}) = 0" using tail_props(1)[OF nat_0I, of "1\<times>{x}" G]
      using func1_3_L1[OF x, of 1] unfolding ConstantFunction_def by auto
    have apf:"(1\<times>{x})`0 = x" using apply_equality[of 0 x "1\<times>{x}"]
      using func1_3_L1[OF x, of 1] unfolding ConstantFunction_def
      by auto
    have "Fold(P,\<one>,1\<times>{x}) = Fold(P,\<one>\<cdot>x,0)" using fold_detach_first[of 0,
          OF nat_0I group_oper_fun, of "1\<times>{x}"] tail group0_2_L2
      func1_3_L1[OF x, of 1] apf unfolding ConstantFunction_def by auto
    then have "Fold(P,\<one>,1\<times>{x}) = x" using fold_empty[OF group_oper_fun
      _ x, of 0] group0_2_L2 x by auto
  }
  with S have "S`($# 1) = {\<langle>x,x\<rangle>. x\<in>G}" by auto
  then have "S`($# 1) = id(G)" unfolding id_def lambda_fun_alt by auto
  then show ?thesis using subst[OF int0.Int_ZF_1_L8(2), of "%t. S`t = id(G)"] subst[OF end_comp_monoid(2)[THEN sym], of "\<lambda>t. S`TheNeutralElement(int,IntegerMultiplication) =t"]
    by blast
qed

subsection\<open>Fold formulas\<close>

text\<open>Folding the sum of 2 numbers is equivalent to doing 2 folds\<close>

lemma(in abelian_group) group_action_int_add:
  assumes "z1\<in>nat" "z2\<in>nat" "g\<in>G"
  shows "Fold(P,\<one>,(z1#+z2)\<times>{g}) = Fold(P,\<one>,(z1)\<times>{g})\<cdot>Fold(P,\<one>,(z2)\<times>{g})"
proof(rule nat_induct[of z2 "\<lambda>t. Fold(P,\<one>,(z1#+t)\<times>{g}) = Fold(P,\<one>,z1\<times>{g})\<cdot>Fold(P,\<one>,t\<times>{g})"])
  {
    fix x na assume x:"x\<in>G" "na\<in>nat"
    have "Fold(P,\<one>,na\<times>{x})\<in>G" using fold_props(2)[OF x(2) group_oper_fun,
          of "ConstantFunction(na,x)"] group0_2_L2 func1_3_L1[OF x(1)] unfolding ConstantFunction_def
      by auto
  }
  then have FG:"\<forall>n\<in>nat. \<forall>x\<in>G. Fold(P,\<one>,n\<times>{x})\<in>G" by auto
  from assms(2) show "z2:nat".
  have "Fold(P, \<one>, (z1 #+ 0) \<times> {g}) =Fold(P, \<one>, z1 \<times> {g})" using add_0_right assms(1) by auto
      moreover
  have "Fold(P,\<one>,0\<times>{g}) = \<one>" using fold_empty[OF group_oper_fun] group0_2_L2
    assms(3) by auto
  then have "Fold(P, \<one>, z1 \<times> {g})\<cdot>Fold(P,\<one>,0\<times>{g}) = Fold(P, \<one>, z1 \<times> {g})"
    using group0_2_L2 FG assms(1,3) by auto
  ultimately
  show "Fold(P, \<one>, (z1 #+ 0) \<times> {g}) =Fold(P, \<one>, z1 \<times> {g})\<cdot>Fold(P,\<one>,0\<times>{g})" by auto
  {
    fix s assume s:"s\<in>nat" "Fold(P, \<one>, (z1 #+ s) \<times> {g}) = Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>, s \<times> {g})"
    have f:"s\<times>{g}:s\<rightarrow>G" using func1_3_L1[OF assms(3)] unfolding ConstantFunction_def.
    have p:"P:G\<times>G\<rightarrow>G" using groupAssum unfolding IsAgroup_def IsAmonoid_def IsAssociative_def by auto
    have "Fold(P, \<one>, Append(s \<times> {g}, g)) = P`\<langle>Fold(P, \<one>,s\<times>{g}),g\<rangle>" using fold_append(2)[OF s(1) p f _ assms(3)]
      group0_2_L2(1) by blast moreover
    have "domain(s \<times> {g}) = s" by auto
    then have "Append(s \<times> {g}, g) = succ(s)\<times> {g}" unfolding Append_def by auto
    ultimately have "Fold(P, \<one>, succ(s) \<times> {g}) = P`\<langle>Fold(P, \<one>,s\<times>{g}),g\<rangle>"
      using subst[of "Append(s \<times> {g}, g)" "succ(s)\<times> {g}" "\<lambda>q. Fold(P, \<one>, q) = P`\<langle>Fold(P, \<one>,s\<times>{g}),g\<rangle>"]
      by blast
    then have H:"Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>, succ(s) \<times> {g}) = Fold(P, \<one>, z1 \<times> {g}) \<cdot> (P`\<langle>Fold(P, \<one>,s\<times>{g}),g\<rangle>)"
      by auto
    let ?S ="{\<langle>$# n, {\<langle>x, Fold(P, \<one>, n \<times> {x})\<rangle> . x \<in> G}\<rangle> . n \<in> nat} \<union>
  {\<langle>$- $# n, GroupInv(G, P) O {\<langle>x, Fold(P, \<one>, n \<times> {x})\<rangle> . x \<in> G}\<rangle> . n \<in> nat}"
    from group_action_int_fun have "?S:int\<rightarrow>End(G,P)" by auto
    then have "(?S`($# z1)) \<in>End(G,P)" using apply_type[of ?S int "\<lambda>_. End(G,P)" "$#z1"] assms(1) by auto
    moreover from group_action_int_dest(1) have "(?S`($# z1))`g = Fold(P, \<one>, z1 \<times> {g})" using assms(1,3) by auto
    ultimately have a:"Fold(P, \<one>, z1 \<times> {g}) \<in> G" unfolding End_def using apply_type[of "?S`($# z1)" G "\<lambda>_. G" g] assms(3)
      by auto
    from group_action_int_fun have "(?S`($# s)) \<in>End(G,P)" using apply_type[of ?S int "\<lambda>_. End(G,P)" "$#s"] by auto
    moreover from group_action_int_dest(1) have "(?S`($# s))`g = Fold(P, \<one>, s \<times> {g})" using assms(3) s(1) by auto
    ultimately have b:"Fold(P, \<one>, s \<times> {g}) \<in> G" unfolding End_def using apply_type[of "?S`($# s)" G "\<lambda>_. G" g] assms(3)
      by auto
    from H a b assms(3) have "Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>, succ(s) \<times> {g}) = (Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>,s\<times>{g})) \<cdot> g"
      using group_oper_assoc by auto
    with s(2) have g:"Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>, succ(s) \<times> {g}) = Fold(P, \<one>, (z1 #+ s) \<times> {g}) \<cdot> g" by auto
    have n:"(z1 #+ s) \<in> nat" using assms(1) s(1) by auto 
    have ff:"(z1 #+ s)\<times>{g}:(z1 #+ s)\<rightarrow>G" using func1_3_L1[OF assms(3)] unfolding ConstantFunction_def.
    from g have "Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>, succ(s) \<times> {g}) = Fold(P, \<one>, Append((z1 #+ s) \<times> {g},g))"
      using subst[OF fold_append(2)[OF n p ff _ assms(3), THEN sym], of _ "\<lambda>q. Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>, succ(s) \<times> {g}) = q"] group0_2_L2
      unfolding groper_def by blast moreover
    have "domain((z1 #+ s) \<times> {g}) = (z1 #+ s)" by auto
    then have "Append((z1 #+ s) \<times> {g}, g) = succ(z1 #+ s)\<times> {g}" unfolding Append_def by auto
    ultimately have "Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>, succ(s) \<times> {g}) = Fold(P, \<one>, succ(z1 #+ s)\<times> {g})"
      using subst[of "Append((z1 #+ s) \<times> {g}, g)" "succ(z1 #+ s)\<times> {g}" "\<lambda>q. Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>, succ(s) \<times> {g}) = Fold(P, \<one>, q)"]
      by blast
    then show "Fold(P, \<one>, (z1 #+ succ(s)) \<times> {g}) =
         Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>, succ(s) \<times> {g})"
      using add_succ_right by auto
  }
qed

text\<open>The element on the fold, can commute with the @{term Fold}\<close>

corollary(in abelian_group) group_action_int_comm:
  assumes "z1\<in>nat" "g\<in>G"
  shows "g\<cdot>Fold(P,\<one>,z1\<times>{g}) = Fold(P,\<one>,z1\<times>{g})\<cdot>g"
proof-
  have  "1\<times>{g} = Append(0,g)" unfolding Append_def by auto
  then have e:"Fold(P,\<one>,1\<times>{g}) = Fold(P,\<one>,Append(0,g))" by (simp only:subst[of "1\<times>{g}" "Append(0,g)"])
  have f:"0:0\<rightarrow>G" unfolding Pi_def function_def by auto
  have A:"Fold(P,\<one>,1\<times>{g}) = Fold(P,\<one>,0) \<cdot> g" using trans[OF e fold_append(2)[OF nat_0I group_oper_fun
    f _ assms(2)]] group0_2_L2 by auto moreover
  have empty:"Fold(P,\<one>,0) = \<one>" using fold_empty[OF group_oper_fun f] group0_2_L2 by auto
  have G:"Fold(P,\<one>,1\<times>{g}) = g" using
    group0_2_L2 assms(2) by (simp only:A empty)
  then have "Fold(P,\<one>,1\<times>{g})\<cdot>Fold(P,\<one>,z1\<times>{g}) = g\<cdot>Fold(P,\<one>,z1\<times>{g})" by auto
  then have "Fold(P,\<one>,(1 #+ z1)\<times>{g}) = g\<cdot>Fold(P,\<one>,z1\<times>{g})"
    using group_action_int_add[OF nat_1I assms(1,2)] by auto
  then have "Fold(P,\<one>,(z1 #+ 1)\<times>{g}) = g\<cdot>Fold(P,\<one>,z1\<times>{g})" using add_commute by auto
  then have "Fold(P,\<one>,z1\<times>{g})\<cdot>Fold(P,\<one>,1\<times>{g}) = g\<cdot>Fold(P,\<one>,z1\<times>{g})"
    using group_action_int_add[OF assms(1) nat_1I assms(2)] by auto
  with G show ?thesis by auto
qed 

text\<open>Folding an inversed element is equivalent of folding and the inverting\<close>

lemma(in abelian_group) group_action_int_inv:
  assumes "z\<in>nat" "g\<in>G"
  shows "Fold(P,\<one>,z\<times>{g\<inverse>}) = Fold(P,\<one>,z\<times>{g})\<inverse>"
proof(rule nat_induct[of z "\<lambda>z. Fold(P,\<one>,z\<times>{g\<inverse>}) = Fold(P,\<one>,z\<times>{g})\<inverse>"])
  show "z\<in>nat" using assms(1).
  {
    fix x na assume x:"x\<in>G" "na\<in>nat"
    have "Fold(P,\<one>,na\<times>{x})\<in>G" using fold_props(2)[OF x(2) group_oper_fun,
          of "ConstantFunction(na,x)"] group0_2_L2(1) func1_3_L1[OF x(1)] unfolding ConstantFunction_def
      by auto
  }
  then have FG:"\<forall>n\<in>nat. \<forall>x\<in>G. Fold(P,\<one>,n\<times>{x})\<in>G" by auto
  have " Fold(P, \<one>, 0 \<times> {g\<inverse> }) =  Fold(P, \<one>, 0 \<times> {g})" by auto
  moreover have "Fold(P, \<one>, 0 \<times> {g}) =\<one>" using fold_empty[OF group_oper_fun] group0_2_L2
    assms(2) by auto
  ultimately show "Fold(P, \<one>, 0 \<times> {g\<inverse> }) =  Fold(P, \<one>, 0 \<times> {g})\<inverse>"
    using group_inv_of_one by auto
  {
    fix x assume x:"x:nat" "Fold(P, \<one>, x \<times> {g\<inverse> }) = Fold(P, \<one>, x \<times> {g})\<inverse>"
    have "domain(x\<times>{g}) = x" by auto
    then have "Append(x\<times>{g},g) = succ(x)\<times>{g}" unfolding Append_def by auto
    then have A:"Fold(P, \<one>, Append(x\<times>{g},g)) = Fold(P, \<one>, succ(x) \<times> {g})"
      by (simp only:subst[where P="\<lambda>t. Fold(P, \<one>, Append(x\<times>{g},g)) = Fold(P, \<one>, t)"])
    have f:"x\<times>{g}:x\<rightarrow>G" unfolding Pi_def function_def using assms(2) by auto
    have "Fold(P, \<one>, x\<times>{g})\<cdot>g = Fold(P, \<one>, succ(x) \<times> {g})"
      using fold_append(2)[OF x(1) group_oper_fun f _ assms(2), of \<one>] group0_2_L2
      apply (simp only:A) by simp
    then have "(Fold(P, \<one>, x\<times>{g})\<cdot>g)\<inverse> = Fold(P, \<one>, succ(x) \<times> {g})\<inverse>" by auto
    then have "g\<inverse>\<cdot>Fold(P, \<one>, x\<times>{g})\<inverse> = Fold(P, \<one>, succ(x) \<times> {g})\<inverse>"
      using group_inv_of_two[OF _ assms(2)] FG x(1) assms(2) by auto
    with x(2) have "g\<inverse>\<cdot>Fold(P, \<one>, x \<times> {g\<inverse> }) = Fold(P, \<one>, succ(x) \<times> {g})\<inverse>"
      by auto moreover
    have "g\<inverse>\<cdot>Fold(P, \<one>, x \<times> {g\<inverse> }) = Fold(P, \<one>, x \<times> {g\<inverse> })\<cdot>g\<inverse>"
      using inverse_in_group[OF assms(2)] group_action_int_comm[OF x(1)]
      by auto
    ultimately have A:"Fold(P, \<one>, x \<times> {g\<inverse> })\<cdot>g\<inverse> = Fold(P, \<one>, succ(x) \<times> {g})\<inverse>" by auto
    have f:"x \<times> {g\<inverse> }:x\<rightarrow>G" unfolding Pi_def function_def using inverse_in_group[OF assms(2)] by auto
    have A:"Fold(P, \<one>, Append(x \<times> {g\<inverse> },g\<inverse>)) = Fold(P, \<one>, succ(x) \<times> {g})\<inverse>"
      using trans[OF fold_append(2)[OF x(1) group_oper_fun f 
          _ inverse_in_group[OF assms(2)]], of _ "Fold(P, \<one>, succ(x) \<times> {g})\<inverse>"] 
      A group0_2_L2 unfolding groper_def by blast
    have "domain(x\<times>{g\<inverse>}) = x" by auto
    then have "Append(x \<times> {g\<inverse> },g\<inverse>) = succ(x)\<times>{g\<inverse>}" unfolding Append_def by auto
    from subst[OF this, of "\<lambda>q. Fold(P, \<one>, q) = Fold(P, \<one>, succ(x) \<times> {g})\<inverse>"]
      A show " Fold(P, \<one>, succ(x) \<times> {g\<inverse> }) = Fold(P, \<one>, succ(x) \<times> {g})\<inverse>"
      by blast
  }
qed

text\<open>Folds when considering a well defined substraction\<close>

lemma(in abelian_group) group_action_int_minus:
  assumes "z1\<in>nat" "z2\<in>nat" "g\<in>G" "z2 \<le> z1"
  shows "Fold(P,\<one>,(z1#-z2)\<times>{g}) = Fold(P,\<one>,(z1)\<times>{g})\<cdot>Fold(P,\<one>,(z2)\<times>{g})\<inverse>"
proof-
  have "z2 \<le> z1 \<longrightarrow> Fold(P,\<one>,(z1#-z2)\<times>{g}) = Fold(P,\<one>,(z1)\<times>{g})\<cdot>Fold(P,\<one>,(z2)\<times>{g})\<inverse>"
  proof(rule nat_induct[of z2 "\<lambda>t. t\<le>z1 \<longrightarrow> (Fold(P,\<one>,(z1#-t)\<times>{g}) = Fold(P,\<one>,z1\<times>{g})\<cdot>Fold(P,\<one>,t\<times>{g})\<inverse>)"])
  {
    fix x na assume x:"x\<in>G" "na\<in>nat"
    have "Fold(P,\<one>,na\<times>{x})\<in>G" using fold_props(2)[OF x(2) group_oper_fun,
          of "ConstantFunction(na,x)"] group0_2_L2 func1_3_L1[OF x(1)] unfolding ConstantFunction_def
      by auto
  }
  then have FG:"\<forall>n\<in>nat. \<forall>x\<in>G. Fold(P,\<one>,n\<times>{x})\<in>G" by auto
  show "z2\<in>nat" using assms(2) by auto
  have "Fold(P,\<one>,0\<times>{g}) = \<one>" using fold_empty[OF group_oper_fun] group0_2_L2
    assms(3) by auto
  then have "Fold(P,\<one>,0\<times>{g})\<inverse> = \<one>" using group_inv_of_one by auto
  moreover
  have "Fold(P, \<one>, (z1 #- 0) \<times> {g}) =Fold(P, \<one>, z1 \<times> {g})" using diff_0 assms(1) by auto
  ultimately show "0 \<le> z1 \<longrightarrow> Fold(P, \<one>, (z1 #- 0) \<times> {g}) = Fold(P, \<one>, z1 \<times> {g})\<cdot>Fold(P,\<one>,0\<times>{g})\<inverse>"
    using group0_2_L2 FG assms(1,3) by auto
  have p:"P:G\<times>G\<rightarrow>G" using groupAssum unfolding IsAgroup_def IsAmonoid_def IsAssociative_def by auto
  {
    fix s assume s:"s\<in>nat" "s \<le> z1 \<longrightarrow> Fold(P, \<one>, (z1 #- s) \<times> {g}) = Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>, s \<times> {g})\<inverse>"
    {
      assume as:"succ(s)\<le>z1"
      have "s\<le>succ(s)" using le_succ_iff[of s s] using le_refl[OF nat_into_Ord] s(1) by auto
      with as have "s\<le>z1" using le_trans by auto
      with s(2) have s2:"Fold(P, \<one>, (z1 #- s) \<times> {g}) = Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>, s \<times> {g})\<inverse>" by auto
      have e:"succ(z1 #- succ(s)) = z1 #- s" using diff_succ[OF as] assms(1) diff_succ_succ by auto
      have "domain((z1 #- succ(s)) \<times> {g}) = (z1 #- succ(s))" by auto
      then have "Append((z1 #- succ(s)) \<times> {g},g) = succ(z1 #- succ(s)) \<times> {g}"
        unfolding Append_def by auto
      then have "Append((z1 #- succ(s)) \<times> {g},g) = (z1 #- s)\<times> {g}" by (simp only:e)
      then have a:"Fold(P, \<one>, Append((z1 #- succ(s)) \<times> {g},g)) =
        Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>, s \<times> {g})\<inverse>" 
        by (simp only:s2)
      have f:"(z1 #- succ(s)) \<times> {g} \<in> z1 #- succ(s) \<rightarrow> G" unfolding Pi_def function_def
        using assms(3) by auto
      have n:"z1 #- succ(s) \<in>nat" by auto
      have one:"\<one>\<in>G" using group0_2_L2 by auto
      have "Fold(P, \<one>, (z1 #- succ(s)) \<times> {g}) \<cdot> g = Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>, s \<times> {g})\<inverse>" 
        using fold_append(2)[of "z1 #- succ(s)", OF _ p _ one assms(3), of "(z1 #- succ(s)) \<times> {g}"]
        apply (simp only:n f a) by simp
      then have "(Fold(P, \<one>, (z1 #- succ(s)) \<times> {g}) \<cdot> g)\<cdot>g\<inverse> = (Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>, s \<times> {g})\<inverse>)\<cdot>g\<inverse>" by auto
      then have "Fold(P, \<one>, (z1 #- succ(s)) \<times> {g})\<cdot> (g\<cdot>g\<inverse>) = (Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>, s \<times> {g})\<inverse>)\<cdot>g\<inverse>"
        using group_oper_assoc[OF _ assms(3) inverse_in_group[OF assms(3)]] FG assms(3)
        by auto
      then have "Fold(P, \<one>, (z1 #- succ(s)) \<times> {g}) = (Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>, s \<times> {g})\<inverse>)\<cdot>g\<inverse>"
        using group0_2_L6[OF assms(3)] group0_2_L2 FG assms(3) by auto
      then have A:"Fold(P, \<one>, (z1 #- succ(s)) \<times> {g}) = Fold(P, \<one>, z1 \<times> {g}) \<cdot> (Fold(P, \<one>, s \<times> {g})\<inverse>\<cdot>g\<inverse>)"
        using group_oper_assoc[OF _ _ inverse_in_group[OF assms(3)]] 
        inverse_in_group[of "Fold(P, \<one>, s \<times> {g})"] FG s(1) assms(1) assms(3) by auto
      then have "Fold(P, \<one>, (z1 #- succ(s)) \<times> {g}) = Fold(P, \<one>, z1 \<times> {g}) \<cdot>(g \<cdot> Fold(P, \<one>, s \<times> {g}))\<inverse>"
        using group_inv_of_two[OF assms(3), of "Fold(P, \<one>, s\<times>{g})"] FG by (simp only: assms(3) s(1))
      then have e:"Fold(P, \<one>, (z1 #- succ(s)) \<times> {g}) = Fold(P, \<one>, z1 \<times> {g}) \<cdot>(Fold(P, \<one>, s \<times> {g}) \<cdot> g)\<inverse>" 
        using group_action_int_comm[OF s(1) assms(3)] by auto
      have f:"s\<times>{g}:s\<rightarrow>G" using assms(3) unfolding Pi_def function_def by auto
      have e:"Fold(P, \<one>, (z1 #- succ(s)) \<times> {g}) = Fold(P, \<one>, z1 \<times> {g}) \<cdot>(Fold(P, \<one>, Append(s \<times> {g},g)))\<inverse>"
        using fold_append(2)[OF s(1) group_oper_fun f _ assms(3)] group0_2_L2 apply (simp only: e)
        unfolding groper_def by (simp only:refl)
      have "domain(s\<times>{g}) = s" by auto
      then have a:"Append(s \<times> {g},g) = succ(s)\<times>{g}" unfolding Append_def by auto
      have "Fold(P, \<one>, (z1 #- succ(s)) \<times> {g}) = Fold(P, \<one>, z1 \<times> {g}) \<cdot>(Fold(P, \<one>,succ(s)\<times>{g}))\<inverse>"
        by (simp only: e a)
    }
    then show "succ(s) \<le> z1 \<longrightarrow> Fold(P, \<one>, (z1 #- succ(s)) \<times> {g}) = Fold(P, \<one>, z1 \<times> {g}) \<cdot> Fold(P, \<one>, succ(s) \<times> {g})\<inverse>"
      by auto
  }
qed
  with assms(4) show ?thesis by auto
qed

text\<open>Fold negative number by substraction\<close>

lemma(in abelian_group) group_action_int_minus_rev:
  assumes "z1\<in>nat" "z2\<in>nat" "g\<in>G" "z1 \<le> z2"
  shows "Fold(P,\<one>,(z2 #- z1)\<times>{g})\<inverse> = Fold(P,\<one>,z1\<times>{g})\<cdot>Fold(P,\<one>,z2\<times>{g})\<inverse>"
proof-
  have "z1 \<le> z2 \<longrightarrow> Fold(P,\<one>,(z2 #- z1)\<times>{g})\<inverse> = Fold(P,\<one>,z1\<times>{g})\<cdot>Fold(P,\<one>,z2\<times>{g})\<inverse>"
  proof(rule nat_induct[of z1 "\<lambda>t. t\<le>z2 \<longrightarrow> (Fold(P,\<one>,(z2#-t)\<times>{g})\<inverse> = Fold(P,\<one>,t\<times>{g})\<cdot>Fold(P,\<one>,z2\<times>{g})\<inverse>)"])
    {
      fix x na assume x:"x\<in>G" "na\<in>nat"
      have "Fold(P,\<one>,na\<times>{x})\<in>G" using fold_props(2)[OF x(2) group_oper_fun,
            of "ConstantFunction(na,x)"] group0_2_L2 func1_3_L1[OF x(1)] unfolding ConstantFunction_def
        by auto
    }
    then have FG:"\<forall>n\<in>nat. \<forall>x\<in>G. Fold(P,\<one>,n\<times>{x})\<in>G" by auto
    show "z1\<in>nat" using assms(1).
    have "Fold(P,\<one>,0\<times>{g}) = \<one>" using fold_empty[OF group_oper_fun] group0_2_L2
      assms(3) by auto
    moreover
    have "Fold(P, \<one>, (z2 #- 0) \<times> {g})\<inverse> =Fold(P, \<one>, z2 \<times> {g})\<inverse>" using diff_0 assms(2) by auto
    ultimately have "Fold(P, \<one>, (z2 #- 0) \<times> {g})\<inverse> =Fold(P,\<one>,0\<times>{g}) \<cdot> Fold(P, \<one>, z2 \<times> {g})\<inverse>"
      using group0_2_L2 FG assms(2,3) inverse_in_group by auto
    then show "0 \<le> z2 \<longrightarrow> Fold(P, \<one>, (z2 #- 0) \<times> {g})\<inverse>  = Fold(P, \<one>, 0 \<times> {g}) \<cdot> Fold(P, \<one>, z2 \<times> {g})\<inverse>" by auto
    {
      fix x assume x:"x\<in>nat" "x \<le> z2 \<longrightarrow>
         Fold(P, \<one>, (z2 #- x) \<times> {g})\<inverse>  = Fold(P, \<one>, x \<times> {g}) \<cdot> Fold(P, \<one>, z2 \<times> {g})\<inverse>"
      {
        assume as:"succ(x) \<le> z2"
        have "x\<le>succ(x)" using le_succ_iff[of x x] using le_refl[OF nat_into_Ord] x(1) by auto
        with as have "x\<le>z2" using le_trans by auto
        with x(2) have A:"Fold(P, \<one>, (z2 #- x) \<times> {g})\<inverse>  = Fold(P, \<one>, x \<times> {g}) \<cdot> Fold(P, \<one>, z2 \<times> {g})\<inverse>"
          by auto
        have "Fold(P, \<one>, (z2 #- succ(x)) \<times> {g}) = Fold(P, \<one>, z2 \<times> {g}) \<cdot> Fold(P, \<one>, succ(x) \<times> {g})\<inverse>"
          using group_action_int_minus[OF assms(2) nat_succI[OF x(1)] assms(3) as].
        then have "Fold(P, \<one>, (z2 #- succ(x)) \<times> {g})\<inverse> = (Fold(P, \<one>, z2 \<times> {g}) \<cdot> Fold(P, \<one>, succ(x) \<times> {g})\<inverse>)\<inverse>"
          by auto
        then have "Fold(P, \<one>, (z2 #- succ(x)) \<times> {g})\<inverse> = (Fold(P, \<one>, succ(x) \<times> {g})\<inverse>)\<inverse> \<cdot> (Fold(P, \<one>, z2 \<times> {g})\<inverse>)"
          using group_inv_of_two[OF _ inverse_in_group] FG assms(2) nat_succI[OF x(1)] assms(3)
          by auto
        then have "Fold(P, \<one>, (z2 #- succ(x)) \<times> {g})\<inverse> = Fold(P, \<one>, succ(x) \<times> {g}) \<cdot> (Fold(P, \<one>, z2 \<times> {g})\<inverse>)"
          using group_inv_of_inv FG assms(3) nat_succI[OF x(1)] by auto
      }
      then show "succ(x) \<le> z2 \<longrightarrow>
         Fold(P, \<one>, (z2 #- succ(x)) \<times> {g})\<inverse>  =
         Fold(P, \<one>, succ(x) \<times> {g}) \<cdot> Fold(P, \<one>, z2 \<times> {g})\<inverse> " by auto
    }
  qed
  with assms(4) show ?thesis by auto
qed

text\<open>The action is an group homomorphism between $(\mathbb{Z},+)$ and $(G,P)$\<close>

lemma(in abelian_group) group_action_int_add_morphism:
  defines "S \<equiv> {\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}\<union> {\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
  shows "\<forall>r\<in>int. \<forall>s\<in>int. \<forall>g\<in>G. S ` (IntegerAddition` \<langle>r, s\<rangle>) ` g = P ` \<langle>(S ` r) ` g, (S ` s) ` g\<rangle>"
proof(safe)
  fix r s g assume as:"r:int" "s:int" "g:G"
  from as(1) int_cases obtain n where n:"n\<in>nat" "r=$#n \<or> r=$- $# succ(n)" by auto
  from as(2) int_cases obtain m where m:"m\<in>nat" "s=$#m \<or> s=$- $# succ(m)" by auto
  have int:"IntegerAddition`\<langle>r, s\<rangle>\<in>int" using int0.Int_ZF_1_L2(1)[OF as(1,2)] by auto
  {
    fix x na assume x:"x\<in>G" "na\<in>nat"
    have "Fold(P,\<one>,na\<times>{x})\<in>G" using fold_props(2)[OF x(2) group_oper_fun,
          of "ConstantFunction(na,x)"] group0_2_L2 func1_3_L1[OF x(1)] unfolding ConstantFunction_def
      by auto
  }
  then have FG:"\<forall>n\<in>nat. \<forall>x\<in>G. Fold(P,\<one>,n\<times>{x})\<in>G" by auto
  {
    assume ass:"r=$#n" "s=$#m"
    then have "IntegerAddition`\<langle>r, s\<rangle> = $#(n#+m)" using int_of_add[of n m]
      int0.Int_ZF_1_L2 as(1,2) by auto
    moreover have "n#+m\<in>nat" by auto
    ultimately have "S ` (IntegerAddition` \<langle>r, s\<rangle>) `g = Fold(P,\<one>,(n#+m)\<times>{g})"
      using group_action_int_dest(1)[of "n#+m", OF _ as(3)] unfolding S_def by auto
    with m(1) n(1) as(3) group_action_int_add have "S ` (IntegerAddition` \<langle>r, s\<rangle>) `g =
      Fold(P,\<one>,n\<times>{g}) \<cdot> Fold(P,\<one>,m\<times>{g})" by auto
    with group_action_int_dest(1)[OF n(1) as(3)] group_action_int_dest(1)[OF m(1) as(3)]
    have "S ` (IntegerAddition` \<langle>r, s\<rangle>) `g = ((S`($#n))`g) \<cdot> ((S`($#m))`g)" 
      unfolding S_def by auto
    with ass have "S ` (IntegerAddition` \<langle>r, s\<rangle>) `g = ((S`r)`g) \<cdot> ((S`s)`g)" by auto
  } moreover
  {
    assume ass:"r=$- $# succ(n)" "s=$#m"
    then have "IntegerAddition`\<langle>r, s\<rangle> = ($- $# succ(n)) $+ $#m" using
      int0.Int_ZF_1_L2(1) as(1,2) by auto
    then have a:"IntegerAddition`\<langle>r, s\<rangle> = $#m $+ ($- $# succ(n))" using zadd_commute by auto
    from int int_cases obtain q where q:"q\<in>nat" "IntegerAddition`\<langle>r, s\<rangle> = $# q \<or> IntegerAddition`\<langle>r, s\<rangle> = $- $# succ(q)"
      by auto
    have SS:"(S`s)`g = Fold(P,\<one>,m\<times>{g})" using group_action_int_dest(1)[OF m(1) as(3)]
        unfolding S_def using ass(2) by auto
    have SR:"(S`r)`g = Fold(P,\<one>,succ(n)\<times>{g})\<inverse>" using group_action_int_dest(2)[OF nat_succI[OF n(1)]
        as(3)] unfolding S_def using ass(1) by auto
    {
      assume assm:"IntegerAddition`\<langle>r, s\<rangle> = $# q"
      then have "S`(IntegerAddition`\<langle>r, s\<rangle>)`g = Fold(P,\<one>,q\<times>{g})"
        using group_action_int_dest(1)[OF q(1) as(3)] unfolding S_def by auto
      have "($#q) $+ ($# succ(n)) = $# (q #+ succ(n))" using int_of_add[of q "succ(n)"] by auto
      moreover have "($#m $+ ($- $# succ(n))) $+ $# succ(n) = $# m"
        using zadd_zminus_inverse2[of "$# succ(n)"] zadd_assoc[of "$# m" "$- $# succ(n)" "$# succ(n)"]
        zadd_int0_right_intify[of "$#m"] by auto moreover
      note a assm ultimately
      have "$# m = $# (q #+ succ(n))" by auto
      then have "m = q #+ succ(n)" using int_of_inject m(1) by auto
      then have "Fold(P,\<one>,m\<times>{g}) = Fold(P,\<one>,(q #+ succ(n))\<times>{g})" by auto
      then have "Fold(P,\<one>,m\<times>{g}) = Fold(P,\<one>,(succ(n) #+ q)\<times>{g})" using add_commute by auto
      then have "Fold(P,\<one>,m\<times>{g}) = Fold(P,\<one>,succ(n)\<times>{g})\<cdot>Fold(P,\<one>,q\<times>{g})"
        using group_action_int_add[OF nat_succI[OF n(1)] q(1) as(3)] by auto
      then have A:"Fold(P,\<one>,(succ(n))\<times>{g})\<inverse>\<cdot>Fold(P,\<one>,m\<times>{g}) = Fold(P,\<one>,q\<times>{g})"
        using group0_2_L18(2) FG nat_succI[OF n(1)] as(3) q(1) by auto
      from SR SS have "((S`r)`g)\<cdot>((S`s)`g) = Fold(P,\<one>,succ(n)\<times>{g})\<inverse> \<cdot> Fold(P,\<one>,m\<times>{g})"
        by auto
      with A have "((S`r)`g)\<cdot>((S`s)`g) = Fold(P,\<one>,q\<times>{g})" by auto
      then have "((S`r)`g)\<cdot>((S`s)`g) = S`($# q)`g" using group_action_int_dest(1)[OF q(1)
        as(3)] unfolding S_def by auto
      with assm have "S ` (IntegerAddition` \<langle>r, s\<rangle>) `g = ((S`r)`g) \<cdot> ((S`s)`g)" by auto
    } moreover
    {
      assume assm:"IntegerAddition`\<langle>r, s\<rangle> = $- $# succ(q)"
      then have E:"S`(IntegerAddition`\<langle>r, s\<rangle>)`g = Fold(P,\<one>,succ(q)\<times>{g})\<inverse>"
        using group_action_int_dest(2)[OF nat_succI[OF q(1)] as(3)] unfolding S_def by auto
      have "($#m $+ ($- $# succ(n))) $+ $# succ(n) = $# m"
        using zadd_zminus_inverse2[of "$# succ(n)"] zadd_assoc[of "$# m" "$- $# succ(n)" "$# succ(n)"]
        zadd_int0_right_intify[of "$#m"] by auto moreover
      note a assm ultimately
      have "$# m = ($- $# succ(q)) $+ ($# succ(n))" by auto
      then have "$# m = ($# succ(n)) $+ ($- $# succ(q))" using zadd_commute by auto
      then have "$# m $+ $# succ(q) = ($# succ(n)) $+ ($- $# succ(q)) $+ $# succ(q)" by auto
      then have "$# m $+ $# succ(q) = ($# succ(n))" using zadd_zminus_inverse2[of "$# succ(q)"] zadd_assoc[of "$# succ(n)" "$- $# succ(q)" "$# succ(q)"]
        zadd_int0_right_intify[of "$#m"] by auto 
      then have "$# (m #+ succ(q)) = $# succ(n)" using int_of_add[of m "succ(q)"] by auto
      then have "m #+ succ(q) = succ(n)" using int_of_inject[OF _ _ nat_succI[OF n(1)]]
        by auto
      then have "Fold(P,\<one>,(m #+ succ(q))\<times>{g}) = Fold(P,\<one>,succ(n)\<times>{g})" by auto
      then have "Fold(P,\<one>,m\<times>{g})\<cdot>Fold(P,\<one>, succ(q)\<times>{g}) = Fold(P,\<one>,succ(n)\<times>{g})"
        using group_action_int_add[OF m(1) nat_succI[OF q(1)] as(3)] by auto
      then have "Fold(P,\<one>,m\<times>{g}) = Fold(P,\<one>,succ(n)\<times>{g})\<cdot>Fold(P,\<one>, succ(q)\<times>{g})\<inverse>"
        using group0_2_L18(1)[of "Fold(P,\<one>,m\<times>{g})" "Fold(P,\<one>,succ(q)\<times>{g})"] FG 
            m(1) nat_succI[OF q(1)] as(3) by auto
      then have "Fold(P,\<one>,succ(n)\<times>{g})\<inverse>\<cdot>Fold(P,\<one>,m\<times>{g}) = Fold(P,\<one>, succ(q)\<times>{g})\<inverse>"
        using group0_2_L18(2)[of "Fold(P,\<one>,succ(n)\<times>{g})" "Fold(P,\<one>,succ(q)\<times>{g})\<inverse>"]
        inverse_in_group[of "Fold(P, \<one>, succ(q) \<times> {g})"] FG as(3) nat_succI[OF n(1)]
        nat_succI[OF q(1)] by auto
      with E have "Fold(P,\<one>,succ(n)\<times>{g})\<inverse>\<cdot>Fold(P,\<one>,m\<times>{g}) = S`(IntegerAddition`\<langle>r, s\<rangle>)`g" by auto
      with SS SR have "S ` (IntegerAddition` \<langle>r, s\<rangle>) `g = ((S`r)`g) \<cdot> ((S`s)`g)" by auto
    } ultimately
    have "S ` (IntegerAddition ` \<langle>r, s\<rangle>) ` g = S ` r ` g \<cdot> S ` s ` g"
      using q(2) by auto
  } moreover
  {
    assume ass:"r = $# n" "s = $- $# succ(m)"
    then have a:"IntegerAddition`\<langle>r, s\<rangle> = $# n $+ ($- $# succ(m))" using
       int0.Int_ZF_1_L2(1) as(1,2) by auto
    from int int_cases obtain q where q:"q\<in>nat" "IntegerAddition`\<langle>r, s\<rangle> = $# q \<or> IntegerAddition`\<langle>r, s\<rangle> = $- $# succ(q)"
      by auto
    have SS:"(S`s)`g = Fold(P,\<one>,succ(m)\<times>{g})\<inverse>" using group_action_int_dest(2)[OF nat_succI[OF m(1)] as(3)]
        unfolding S_def using ass(2) by auto
    have SR:"(S`r)`g = Fold(P,\<one>,n\<times>{g})" using group_action_int_dest(1)[OF n(1)
        as(3)] unfolding S_def using ass(1) by auto
    {
      assume assm:"IntegerAddition`\<langle>r, s\<rangle> = $# q"
      then have "S`(IntegerAddition`\<langle>r, s\<rangle>)`g = Fold(P,\<one>,q\<times>{g})"
        using group_action_int_dest(1)[OF q(1) as(3)] unfolding S_def by auto
      have "($#q) $+ ($# succ(m)) = $# (q #+ succ(m))" using int_of_add[of q "succ(m)"] by auto
      moreover have "($#n $+ ($- $# succ(m))) $+ $# succ(m) = $# n"
        using zadd_zminus_inverse2[of "$# succ(m)"] zadd_assoc[of "$# n" "$- $# succ(m)" "$# succ(m)"]
        zadd_int0_right_intify[of "$#m"] by auto moreover
      note a assm ultimately
      have "$# n = $# (q #+ succ(m))" by auto
      then have "n = q #+ succ(m)" using int_of_inject n(1) by auto
      then have "Fold(P,\<one>,n\<times>{g}) = Fold(P,\<one>,(q #+ succ(m))\<times>{g})" by auto
      then have "Fold(P,\<one>,n\<times>{g}) = Fold(P,\<one>,q\<times>{g})\<cdot>Fold(P,\<one>,succ(m)\<times>{g})"
        using group_action_int_add[OF q(1) nat_succI[OF m(1)] as(3)] by auto
      then have A:"Fold(P,\<one>,n\<times>{g})\<cdot>Fold(P,\<one>,succ(m)\<times>{g})\<inverse> = Fold(P,\<one>,q\<times>{g})"
        using group0_2_L18(1) FG nat_succI[OF m(1)] as(3) q(1) by auto
      from SR SS have "((S`r)`g)\<cdot>((S`s)`g) = Fold(P,\<one>,n\<times>{g}) \<cdot> Fold(P,\<one>,succ(m)\<times>{g})\<inverse>"
        by auto
      with A have "((S`r)`g)\<cdot>((S`s)`g) = Fold(P,\<one>,q\<times>{g})" by auto
      then have "((S`r)`g)\<cdot>((S`s)`g) = S`($# q)`g" using group_action_int_dest(1)[OF q(1)
        as(3)] unfolding S_def by auto
      with assm have "S ` (IntegerAddition` \<langle>r, s\<rangle>) `g = ((S`r)`g) \<cdot> ((S`s)`g)" by auto
    } moreover
    {
      assume assm:"IntegerAddition`\<langle>r, s\<rangle> = $- $# succ(q)"
      then have E:"S`(IntegerAddition`\<langle>r, s\<rangle>)`g = Fold(P,\<one>,succ(q)\<times>{g})\<inverse>"
        using group_action_int_dest(2)[OF nat_succI[OF q(1)] as(3)] unfolding S_def by auto
      have "($#n $+ ($- $# succ(m))) $+ $# succ(m) = $# n"
        using zadd_zminus_inverse2[of "$# succ(m)"] zadd_assoc[of "$# n" "$- $# succ(m)" "$# succ(m)"]
        zadd_int0_right_intify[of "$#m"] by auto moreover
      note a assm ultimately
      have "$# n = ($- $# succ(q)) $+ ($# succ(m))" by auto
      then have "$# n = ($# succ(m)) $+ ($- $# succ(q))" using zadd_commute by auto
      then have "$# n $+ $# succ(q) = ($# succ(m)) $+ ($- $# succ(q)) $+ $# succ(q)" by auto
      then have "$# n $+ $# succ(q) = ($# succ(m))" using zadd_zminus_inverse2[of "$# succ(q)"] zadd_assoc[of "$# succ(m)" "$- $# succ(q)" "$# succ(q)"]
        zadd_int0_right_intify[of "$#m"] by auto 
      then have "$# (n #+ succ(q)) = $# succ(m)" using int_of_add[of n "succ(q)"] by auto
      then have "n #+ succ(q) = succ(m)" using int_of_inject[OF _ _ nat_succI[OF m(1)]]
        by auto
      then have "Fold(P,\<one>,(succ(q) #+ n)\<times>{g}) = Fold(P,\<one>,succ(m)\<times>{g})" 
        using add_commute[of n "succ(q)"] by auto
      then have "Fold(P,\<one>,succ(q)\<times>{g})\<cdot>Fold(P,\<one>, n\<times>{g}) = Fold(P,\<one>,succ(m)\<times>{g})"
        using group_action_int_add[OF nat_succI[OF q(1)] n(1) as(3)] by auto
      then have "Fold(P,\<one>,n\<times>{g}) = Fold(P,\<one>, succ(q)\<times>{g})\<inverse>\<cdot>Fold(P,\<one>,succ(m)\<times>{g})"
        using group0_2_L18(2)[of "Fold(P,\<one>,succ(q)\<times>{g})" "Fold(P,\<one>,n\<times>{g})"] FG 
            n(1) nat_succI[OF q(1)] as(3) by auto
      then have "Fold(P,\<one>,n\<times>{g})\<cdot>Fold(P,\<one>,succ(m)\<times>{g})\<inverse> = Fold(P,\<one>, succ(q)\<times>{g})\<inverse>"
        using group0_2_L18(1)[of "Fold(P,\<one>,succ(q)\<times>{g})\<inverse>" "Fold(P,\<one>,succ(m)\<times>{g})"]
        inverse_in_group[of "Fold(P, \<one>, succ(q) \<times> {g})"] FG as(3) nat_succI[OF m(1)]
        nat_succI[OF q(1)] by auto
      with E have "Fold(P,\<one>,n\<times>{g})\<cdot>Fold(P,\<one>,succ(m)\<times>{g})\<inverse> = S`(IntegerAddition`\<langle>r, s\<rangle>)`g" by auto
      with SS SR have "S ` (IntegerAddition` \<langle>r, s\<rangle>) `g = ((S`r)`g) \<cdot> ((S`s)`g)" by auto
    } ultimately
    have "S ` (IntegerAddition ` \<langle>r, s\<rangle>) ` g = S ` r ` g \<cdot> S ` s ` g"
      using q(2) by auto
  } moreover
  {
    assume ass:"r = $- $# succ(n)" "s = $- $# succ(m)"
    then have "IntegerAddition ` \<langle>r, s\<rangle> = ($- $# succ(n)) $+ ($- $# succ(m))"
      using int0.Int_ZF_1_L2(1) as(1,2) by auto
    then have "IntegerAddition ` \<langle>r, s\<rangle> = $- ($# succ(n) $+ $# succ(m))"
      using zminus_zadd_distrib by auto
    then have "IntegerAddition ` \<langle>r, s\<rangle> = $- $# (succ(n) #+ succ(m))"
      using int_of_add[of "succ(n)" "succ(m)"] by auto
    then have "S`(IntegerAddition ` \<langle>r, s\<rangle>)`g = Fold(P,\<one>,(succ(n) #+ succ(m))\<times>{g})\<inverse>"
      using group_action_int_dest(2)[of "succ(n)#+succ(m)", OF _ as(3)]
      unfolding S_def by auto
    then have "S`(IntegerAddition ` \<langle>r, s\<rangle>)`g = Fold(P,\<one>,(succ(m) #+ succ(n))\<times>{g})\<inverse>"
      using add_commute by auto
    then have "S`(IntegerAddition ` \<langle>r, s\<rangle>)`g = (Fold(P,\<one>,succ(m)\<times>{g})\<cdot> Fold(P,\<one>,succ(n)\<times>{g}))\<inverse>"
      using group_action_int_add[OF nat_succI[OF m(1)] nat_succI[OF n(1)] as(3)] by auto
    then have "S`(IntegerAddition ` \<langle>r, s\<rangle>)`g =Fold(P,\<one>,succ(n)\<times>{g})\<inverse>\<cdot>Fold(P,\<one>,succ(m)\<times>{g})\<inverse>"
      using group_inv_of_two FG as(3) nat_succI[OF n(1)] nat_succI[OF m(1)] by auto
    moreover
    have "S`r`g = Fold(P,\<one>,succ(n)\<times>{g})\<inverse>" using ass(1)
      group_action_int_dest(2)[OF nat_succI[OF n(1)] as(3)] unfolding S_def by auto
    moreover
    have "S`s`g = Fold(P,\<one>,succ(m)\<times>{g})\<inverse>" using ass(2)
      group_action_int_dest(2)[OF nat_succI[OF m(1)] as(3)] unfolding S_def by auto
    ultimately have "S`(IntegerAddition ` \<langle>r, s\<rangle>)`g =(S`r`g)\<cdot>(S`s`g)" by auto
  }
  ultimately show "S`(IntegerAddition ` \<langle>r, s\<rangle>)`g =P ` \<langle>S ` r ` g, S ` s ` g\<rangle>"
    using m(2) n(2) by auto
qed

text\<open>Same as before, but not pointwise\<close>

lemma(in abelian_group) group_action_int_add_morphism_fun:
  defines "S \<equiv> {\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat} \<union> {\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
  shows "\<forall>r\<in>int. \<forall>s\<in>int. S ` (IntegerAddition` \<langle>r, s\<rangle>) = EndAdd(G,P) ` \<langle>(S ` r), (S ` s)\<rangle>"
proof(safe)
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
  from group_action_int_fun as have endo:"S`r\<in>End(G,P)" "S`s:End(G,P)"
    using apply_type unfolding S_def by auto
  with eq have SRSS:"S`r:G\<rightarrow>range(P)" "S`s:G\<rightarrow>range(P)" unfolding End_def by auto
  {
    fix g assume g:"g\<in>G"
    with as group_action_int_add_morphism have EE:"S`(IntegerAddition` \<langle>r, s\<rangle>)`g = P ` \<langle>S ` r ` g, S ` s ` g\<rangle>"
      unfolding S_def by auto
    with func_ZF_1_L4[OF group_oper_fun _ _ _ g, of _ "S`r" "S`s"]
     SRSS have "(P {lifted to function space over} G) ` \<langle>S ` r, S ` s\<rangle> ` g = P ` \<langle>S ` r ` g, S ` s ` g\<rangle>"
      by auto
    with EE have "(P {lifted to function space over} G) ` \<langle>S ` r, S ` s\<rangle> ` g = S`(IntegerAddition` \<langle>r, s\<rangle>)`g"
      by auto
  }
  then have R:"\<And>x. x \<in> G \<Longrightarrow> (P {lifted to function space over} G) ` \<langle>S ` r, S ` s\<rangle> ` x = S`(IntegerAddition` \<langle>r, s\<rangle>) ` x" by auto
  from as have "IntegerAddition` \<langle>r, s\<rangle> \<in>int" using int0.Int_ZF_1_L2(1) by auto
  then have f:"S`(IntegerAddition` \<langle>r, s\<rangle>):G\<rightarrow>G" using group_action_int_fun
    apply_type[of S int "\<lambda>_. End(G,P)" "IntegerAddition ` \<langle>r, s\<rangle>"] unfolding End_def S_def
    by auto
  from func_ZF_1_L3[OF group_oper_fun, of _ G] SRSS
  have "(P {lifted to function space over} G) ` \<langle>S ` r, S ` s\<rangle> : G\<rightarrow>range(P)"
    using apply_type by auto
  with fun_extension[OF _ f R] have "S ` (IntegerAddition ` \<langle>r, s\<rangle>) = (P {lifted to function space over} G) ` \<langle>S ` r, S ` s\<rangle>"
    by auto moreover note endo ultimately
  show " S ` (IntegerAddition ` \<langle>r, s\<rangle>) = EndAdd(G, P) ` \<langle>S ` r, S ` s\<rangle> " unfolding EndAdd_def using restrict by auto
qed

text\<open>Fold of a multiplication\<close>

lemma(in abelian_group) group_action_int_mult:
  assumes "z1\<in>nat" "z2\<in>nat" "g\<in>G"
  shows "Fold(P,\<one>,(z1#*z2)\<times>{g}) = Fold(P,\<one>,z2\<times>{Fold(P,\<one>,z1\<times>{g})})"
proof(rule nat_induct[of z2 "\<lambda>t. Fold(P,\<one>,(z1#*t)\<times>{g}) = Fold(P,\<one>,t\<times>{Fold(P,\<one>,z1\<times>{g})})"])
  show "z2\<in>nat" using assms(2).
  {
    fix x na assume x:"x\<in>G" "na\<in>nat"
    have "Fold(P,\<one>,na\<times>{x})\<in>G" using fold_props(2)[OF x(2) group_oper_fun,
          of "ConstantFunction(na,x)"] group0_2_L2 func1_3_L1[OF x(1)] unfolding ConstantFunction_def
      by auto
  }
  then have FG:"\<forall>n\<in>nat. \<forall>x\<in>G. Fold(P,\<one>,n\<times>{x})\<in>G" by auto
  have "z1#*0 = 0" by auto
  then have "Fold(P, \<one>, (z1 #* 0) \<times> {g}) = Fold(P, \<one>, 0)" by auto
  then show "Fold(P, \<one>, (z1 #* 0) \<times> {g}) = Fold(P, \<one>, 0 \<times> {Fold(P, \<one>, z1 \<times> {g})})" by auto
  {
    fix x assume x:"x\<in>nat" "Fold(P, \<one>, (z1 #* x) \<times> {g}) = Fold(P, \<one>, x \<times> {Fold(P, \<one>, z1 \<times> {g})})"
    have "z1 #* succ(x) = z1#+ (z1#*x)" using mult_succ_right by auto
    then have "Fold(P, \<one>, (z1 #* succ(x)) \<times> {g}) = Fold(P, \<one>, (z1#+ (z1#*x)) \<times> {g})" by auto
    then have "Fold(P, \<one>, (z1 #* succ(x)) \<times> {g}) = Fold(P, \<one>, z1\<times>{g})\<cdot>Fold(P,\<one>, (z1#*x) \<times> {g})"
      using group_action_int_add[OF assms(1) _ assms(3), of "z1#*x"] by auto
    with x(2) have "Fold(P, \<one>, (z1 #* succ(x)) \<times> {g}) = Fold(P, \<one>, z1\<times>{g})\<cdot>Fold(P, \<one>, x \<times> {Fold(P, \<one>, z1 \<times> {g})})"
      by auto
    moreover have "domain(x \<times> {Fold(P, \<one>, z1 \<times> {g})}) = x" by auto
    then have "Append(x \<times> {Fold(P, \<one>, z1 \<times> {g})}, Fold(P, \<one>, z1 \<times> {g})) = succ(x) \<times> {Fold(P, \<one>, z1 \<times> {g})}"
      unfolding Append_def by auto
    from subst[OF this, of "\<lambda>q. Fold(P,\<one>,Append(x \<times> {Fold(P, \<one>, z1 \<times> {g})}, Fold(P, \<one>, z1 \<times> {g}))) = Fold(P,\<one>,q)" ] 
      have A:"Fold(P,\<one>,Append(x \<times> {Fold(P, \<one>, z1 \<times> {g})}, Fold(P, \<one>, z1 \<times> {g}))) = Fold(P,\<one>,succ(x) \<times> {Fold(P, \<one>, z1 \<times> {g})})"
        by (simp only:refl)
    have zg:"Fold(P, \<one>, z1 \<times> {g})\<in>G" using assms(1,3) FG by auto 
    then have f:"x\<times>{Fold(P, \<one>, z1 \<times> {g})}:x\<rightarrow>G" unfolding Pi_def function_def by auto
    from fold_append(2)[OF x(1) group_oper_fun f _ zg]
    have "Fold(P,\<one>,Append(x \<times> {Fold(P, \<one>, z1 \<times> {g})}, Fold(P, \<one>, z1 \<times> {g}))) = 
      Fold(P,\<one>,x \<times> {Fold(P, \<one>, z1 \<times> {g})})\<cdot>Fold(P, \<one>, z1 \<times> {g})" using group0_2_L2 by (simp only:groper_def)
    then have "Fold(P,\<one>,Append(x \<times> {Fold(P, \<one>, z1 \<times> {g})}, Fold(P, \<one>, z1 \<times> {g}))) = 
      Fold(P, \<one>, z1 \<times> {g})\<cdot>Fold(P,\<one>,x \<times> {Fold(P, \<one>, z1 \<times> {g})})" using group_action_int_comm[OF x(1) zg]
      by (simp only: trans[of "Fold(P,\<one>,Append(x \<times> {Fold(P, \<one>, z1 \<times> {g})}, Fold(P, \<one>, z1 \<times> {g})))"
        "Fold(P,\<one>,x \<times> {Fold(P, \<one>, z1 \<times> {g})})\<cdot>Fold(P, \<one>, z1 \<times> {g})" "Fold(P, \<one>, z1 \<times> {g})\<cdot>Fold(P,\<one>,x \<times> {Fold(P, \<one>, z1 \<times> {g})})"])
    ultimately have "Fold(P, \<one>, (z1 #* succ(x)) \<times> {g}) = Fold(P,\<one>,Append(x \<times> {Fold(P, \<one>, z1 \<times> {g})}, Fold(P, \<one>, z1 \<times> {g})))"
      by (simp only:trans)
    with A show "Fold(P, \<one>, (z1 #* succ(x)) \<times> {g}) = Fold(P, \<one>, succ(x) \<times> {Fold(P, \<one>, z1 \<times> {g})})"
      by (simp only:trans)
  }
qed

text\<open>Multiplying 2 int\_of natural numbers, is the same as multiplying the natural
numbers and then applying int\_of\<close>

lemma int_of_mult:
  assumes "nr:nat" "ns:nat"
  shows "($# nr) $* ($# ns) = $# (nr #* ns)"
proof-
  have "($# nr) $* ($# ns) = (intrel``{<nr,0>}) $* (intrel``{<ns,0>})"
    unfolding int_of_def using assms by auto
  then have "($# nr) $* ($# ns) = (intrel``{<(nr #* ns) #+ (0 #* 0),(nr #* 0) #+ (0 #* ns)>})"
    using zmult[OF assms(1) nat_0I assms(2) nat_0I] by auto
  then have "($# nr) $* ($# ns) = intrel``{<(nr #* ns),0>}" using mult_0 mult_0_right
    add_0_right by auto
  then show "($# nr) $* ($# ns) = $#(nr #* ns)" unfolding int_of_def by auto
qed

text\<open>The action is a homomorphism between $(\mathbb{Z},\cdot)$ and $(G\to G, \circ)$\<close>

lemma(in abelian_group) group_action_int_mult_morphism:
  defines "S \<equiv> {\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat} \<union> {\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
  shows "\<forall>r\<in>int. \<forall>s\<in>int. S ` (IntegerMultiplication` \<langle>r, s\<rangle>) = EndMult(G,P)`\<langle>S`r,S`s\<rangle>"
proof(safe)
  {
    fix x na assume x:"x\<in>G" "na\<in>nat"
    have "Fold(P,\<one>,na\<times>{x})\<in>G" using fold_props(2)[OF x(2) group_oper_fun,
          of "ConstantFunction(na,x)"] group0_2_L2 func1_3_L1[OF x(1)] unfolding ConstantFunction_def
      by auto
  }
  then have FG:"\<forall>n\<in>nat. \<forall>x\<in>G. Fold(P,\<one>,n\<times>{x})\<in>G" by auto
  fix r s assume as:"r:int" "s:int"
  {
    fix g assume g:"g\<in>G"
    {
      from int_cases as(1) obtain nr where nr:"nr\<in>nat" "r=$# nr \<or> r= $- $# succ(nr)" by auto
      from int_cases as(2) obtain ns where ns:"ns\<in>nat" "s=$# ns \<or> s= $- $# succ(ns)" by auto
      {
        assume pos:"r=$# nr" "s=$# ns"
        then have A:"IntegerMultiplication` \<langle>r, s\<rangle> = ($# nr) $* ($# ns)"
          using int0.Int_ZF_1_L2(2) by auto
        then have "IntegerMultiplication` \<langle>r, s\<rangle> = $#(nr #* ns)" using int_of_mult nr(1) ns(1) by auto
        then have A:"S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = Fold(P,\<one>,( nr #* ns)\<times>{g})"
          using group_action_int_dest(1)[of "nr #* ns", OF _ g] unfolding S_def by auto
        have "Fold(P,\<one>,( nr #* ns)\<times>{g}) = Fold(P,\<one>,nr\<times>{Fold(P,\<one>,ns\<times>{g})})"
          using group_action_int_mult[OF ns(1) nr(1) g] mult_commute by auto
        then have "Fold(P,\<one>,( nr #* ns)\<times>{g}) = Fold(P,\<one>,nr\<times>{S`s`g})"
          using group_action_int_dest(1)[OF ns(1) g] pos(2) unfolding S_def by auto
        moreover
        have "S`s`g\<in>G" using apply_type[OF group_action_int_fun as(2)]
          apply_type[of "S`s" G "\<lambda>_. G", OF _ g] unfolding S_def End_def by auto
        ultimately have "Fold(P,\<one>,( nr #* ns)\<times>{g}) = (S`r)`(S`s`g)"
          using group_action_int_dest(1)[OF nr(1), of "S`s`g"] pos(1)
          unfolding S_def by auto
        then have "Fold(P,\<one>,( nr #* ns)\<times>{g}) = (Composition(G)`\<langle>S`r,S`s\<rangle>)`g"
          using func_ZF_5_L3[of "S`r" G "S`s", OF _ _ g]
          apply_type[OF group_action_int_fun] as unfolding End_def S_def by auto
        with A have "S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = (Composition(G)`\<langle>S`r,S`s\<rangle>)`g" by auto
      } moreover
      {
        assume pos_neg:"r=$# nr" "s=$- $# succ(ns)"
        then have "IntegerMultiplication` \<langle>r, s\<rangle> = ($# nr) $* ($- $# succ(ns))"
          using int0.Int_ZF_1_L2(2) by auto
        then have "IntegerMultiplication` \<langle>r, s\<rangle> = $- (($# nr) $* ($# succ(ns)))"
          using zmult_zminus_right[of "$#nr" "$# succ(ns)"] by auto
        then have "IntegerMultiplication` \<langle>r, s\<rangle> = $- $# (nr #* succ(ns))"
          using int_of_mult nr(1) nat_succI[OF ns(1)] by auto
        then have "S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = Fold(P,\<one>,(nr #* succ(ns))\<times>{g})\<inverse>"
          using group_action_int_dest(2)[OF _ g]
          unfolding S_def by auto
        then have "S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = Fold(P,\<one>,(succ(ns) #* nr)\<times>{g})\<inverse>"
          using subst[OF mult_commute[of nr "succ(ns)"], of "\<lambda>q. S ` (IntegerMultiplication ` \<langle>r, s\<rangle>) ` g = Fold(P, \<one>,q\<times>{g})\<inverse>"]
          by auto
        then have "S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = Fold(P,\<one>,nr\<times>{Fold(P,\<one>,succ(ns)\<times>{g})})\<inverse>"
          using group_action_int_mult[OF nat_succI[OF ns(1)] nr(1) g] by auto
        then have A:"S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = Fold(P,\<one>,nr\<times>{Fold(P,\<one>,succ(ns)\<times>{g})\<inverse>})"
          using group_action_int_inv[OF nr(1), of "Fold(P,\<one>,succ(ns)\<times>{g})"] FG
          nat_succI[OF ns(1)] g by auto
        have B:"S`s`g = Fold(P,\<one>,succ(ns)\<times>{g})\<inverse>" using pos_neg(2)
          group_action_int_dest(2)[OF nat_succI[OF ns(1)] g] unfolding S_def by auto
        have "S`s \<in> End(G,P)" using apply_type[OF group_action_int_fun as(2)] unfolding S_def by auto
        then have "S`s`g \<in>G" using apply_type[of "S`s" G, OF _ g] unfolding End_def by auto
        then have "S`r`(S`s`g) = Fold(P,\<one>,nr\<times>{S`s`g})"
          using group_action_int_dest(1)[OF nr(1), of "S`s`g"] pos_neg(1) unfolding S_def by auto
        with A B have "S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = S`r`(S`s`g)" by auto
        then have "S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = (Composition(G)`\<langle>S`r,S`s\<rangle>)`g" 
          using func_ZF_5_L3[of "S`r" G "S`s", OF _ _ g] apply_type[OF group_action_int_fun as(2)]
          apply_type[OF group_action_int_fun as(1)] unfolding S_def End_def by auto
      } moreover
      {
        assume pos_neg:"r=$- $# succ(nr)" "s=$# ns"
        then have "IntegerMultiplication` \<langle>r, s\<rangle> = ($- $# succ(nr)) $* ($# ns)"
          using int0.Int_ZF_1_L2(2) by auto
        then have "IntegerMultiplication` \<langle>r, s\<rangle> = $- (($# succ(nr)) $* ($# ns))"
          using zmult_zminus_right[of "$#succ(nr)" "$# ns"] by auto
        then have "IntegerMultiplication` \<langle>r, s\<rangle> = $- $# (succ(nr) #* ns)"
          using int_of_mult nr(1) nat_succI[OF ns(1)] by auto
        then have "S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = Fold(P,\<one>,(succ(nr) #* ns)\<times>{g})\<inverse>"
          using group_action_int_dest(2)[OF _ g]
          unfolding S_def by auto
        then have "S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = Fold(P,\<one>,(ns #* succ(nr))\<times>{g})\<inverse>"
          using subst[OF mult_commute[of "succ(nr)" ns], of "\<lambda>q. S ` (IntegerMultiplication ` \<langle>r, s\<rangle>) ` g = Fold(P, \<one>,q\<times>{g})\<inverse>"]
          by auto
        then have A:"S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = Fold(P,\<one>,succ(nr)\<times>{Fold(P,\<one>,ns\<times>{g})})\<inverse>"
          using group_action_int_mult[OF ns(1) nat_succI[OF nr(1)] g] by auto
        have B:"S`s`g = Fold(P,\<one>,ns\<times>{g})" using pos_neg(2)
          group_action_int_dest(1)[OF ns(1) g] unfolding S_def by auto
        have "S`s \<in> End(G,P)" using apply_type[OF group_action_int_fun as(2)] unfolding S_def by auto
        then have "S`s`g \<in>G" using apply_type[of "S`s" G, OF _ g] unfolding End_def by auto
        then have "S`r`(S`s`g) = Fold(P,\<one>,succ(nr)\<times>{S`s`g})\<inverse>"
          using group_action_int_dest(2)[OF nat_succI[OF nr(1)], of "S`s`g"] pos_neg(1) unfolding S_def by auto
        with A B have "S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = S`r`(S`s`g)" by auto
        then have "S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = (Composition(G)`\<langle>S`r,S`s\<rangle>)`g" 
          using func_ZF_5_L3[of "S`r" G "S`s", OF _ _ g] apply_type[OF group_action_int_fun as(2)]
          apply_type[OF group_action_int_fun as(1)] unfolding S_def End_def by auto
      } moreover
      {
        assume pos:"r=$- $# succ(nr)" "s=$- $# succ(ns)"
        then have A:"IntegerMultiplication` \<langle>r, s\<rangle> = ($- $# succ(nr)) $* ($- $# succ(ns))"
          using int0.Int_ZF_1_L2(2) by auto
        then have "IntegerMultiplication` \<langle>r, s\<rangle> = $#(succ(nr) #* succ(ns))" using int_of_mult
          zmult_zminus zmult_zminus_right nr(1) ns(1) zminus_zminus by auto
        then have A:"S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = Fold(P,\<one>,( succ(nr) #* succ(ns))\<times>{g})"
          using group_action_int_dest(1)[of "succ(nr) #* succ(ns)", OF _ g] unfolding S_def by auto
        have "Fold(P,\<one>,(succ(nr) #* succ(ns))\<times>{g}) = Fold(P,\<one>,succ(nr)\<times>{Fold(P,\<one>,succ(ns)\<times>{g})})"
          using group_action_int_mult[OF nat_succI[OF ns(1)] nat_succI[OF nr(1)] g] mult_commute by auto
        moreover
        have gg:"Fold(P,\<one>,succ(ns)\<times>{g}):G" using FG g nat_succI[OF ns(1)] by auto
        then have "Fold(P,\<one>,succ(nr)\<times>{Fold(P,\<one>,succ(ns)\<times>{g})})\<in>G"
          using FG nat_succI[OF nr(1)] by auto
        ultimately have "Fold(P,\<one>,(succ(nr) #* succ(ns))\<times>{g}) = Fold(P,\<one>,succ(nr)\<times>{Fold(P,\<one>,succ(ns)\<times>{g})})\<inverse>\<inverse>"
          using group_inv_of_inv by auto
        then have "Fold(P,\<one>,(succ(nr) #* succ(ns))\<times>{g}) = Fold(P,\<one>,succ(nr)\<times>{Fold(P,\<one>,succ(ns)\<times>{g})\<inverse>})\<inverse>"
          using group_action_int_inv[OF nat_succI[OF nr(1)] gg] by auto
        then have "Fold(P,\<one>,(succ(nr) #* succ(ns))\<times>{g}) = Fold(P,\<one>,succ(nr)\<times>{S`s`g})\<inverse>"
          using group_action_int_dest(2)[OF nat_succI[OF ns(1)] g] pos(2) unfolding S_def by auto
        moreover
        have "S`s`g\<in>G" using apply_type[OF group_action_int_fun as(2)]
          apply_type[of "S`s" G "\<lambda>_. G", OF _ g] unfolding S_def End_def by auto
        ultimately have "Fold(P,\<one>,(succ(nr) #* succ(ns))\<times>{g}) = (S`r)`(S`s`g)"
          using group_action_int_dest(2)[OF nat_succI[OF nr(1)], of "S`s`g"] pos(1)
          unfolding S_def by auto
        then have "Fold(P,\<one>,(succ(nr) #* succ(ns))\<times>{g}) = (Composition(G)`\<langle>S`r,S`s\<rangle>)`g"
          using func_ZF_5_L3[of "S`r" G "S`s", OF _ _ g]
          apply_type[OF group_action_int_fun] as unfolding End_def S_def by auto
        with A have "S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = (Composition(G)`\<langle>S`r,S`s\<rangle>)`g" by auto
      } moreover note nr(2) ns(2) ultimately
      have "S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = (Composition(G)`\<langle>S`r,S`s\<rangle>)`g" by auto
    }
  }
  then have R:"\<And>g. g\<in>G \<Longrightarrow> S`(IntegerMultiplication` \<langle>r, s\<rangle>)`g = (Composition(G)`\<langle>S`r,S`s\<rangle>)`g" by auto
  have "IntegerMultiplication` \<langle>r, s\<rangle>: int" using int0.Int_ZF_1_L2(2)[OF as] by auto
  then have A:"S`(IntegerMultiplication` \<langle>r, s\<rangle>):G\<rightarrow>G" using apply_type[OF group_action_int_fun]
    unfolding End_def S_def by auto moreover
  have "S`r:G\<rightarrow>G" "S`s:G\<rightarrow>G" using apply_type[OF group_action_int_fun] as unfolding S_def End_def
    by auto
  then have B:"(Composition(G)`\<langle>S`r,S`s\<rangle>):G\<rightarrow>G" using apply_type[OF func_ZF_5_L1] by auto
  have "S ` (IntegerMultiplication ` \<langle>r, s\<rangle>) = Composition(G) ` \<langle>S ` r, S ` s\<rangle>"
    using fun_extension[OF A B R] by auto
  then show "S ` (IntegerMultiplication ` \<langle>r, s\<rangle>) = EndMult(G, P) ` \<langle>S ` r, S ` s\<rangle>" unfolding EndMult_def S_def
    using apply_type[OF group_action_int_fun as(1)] apply_type[OF group_action_int_fun as(2)] by auto
qed

text\<open>The action defines a module\<close>

theorem(in abelian_group) group_action_int:
  defines "S \<equiv> {\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat} \<union> {\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
  shows "IsLeftModule(int,IntegerAddition,IntegerMultiplication,G,P,S)" unfolding IsLeftModule_def IsAction_def ringHomomor_def IsMorphism_def
proof(safe)
  show "IsAgroup(G,P)" using groupAssum.
  show "P{is commutative on}G" using abelian_group_axioms unfolding abelian_group_def abelian_group_axioms_def by auto
  show "S \<in> int \<rightarrow> End(G, P)" using group_action_int_fun unfolding S_def.
  show "S ` TheNeutralElement(int, IntegerMultiplication) =
    TheNeutralElement(End(G, P), EndMult(G, P))" using group_action_int_unit unfolding S_def EndMult_def.
  show "IsAring(int, IntegerAddition, IntegerMultiplication)" using int0.Int_ZF_1_1_L2(1).
  show "\<And>r s. r \<in> int \<Longrightarrow>
           s \<in> int \<Longrightarrow> S ` (IntegerAddition ` \<langle>r, s\<rangle>) = EndAdd(G, P) ` \<langle>S ` r,S ` s\<rangle>"
    using group_action_int_add_morphism_fun unfolding S_def by auto
  show "\<And>r s. r \<in> int \<Longrightarrow> s \<in> int \<Longrightarrow> S ` (IntegerMultiplication ` \<langle>r, s\<rangle>) =  EndMult(G, P) ` \<langle>S ` r, S ` s\<rangle>"
    using group_action_int_mult_morphism unfolding S_def by auto
qed

text\<open>If there is a $\mathbb{Z}$-module on an abelian group,
it is the one found in the previous result\<close>

corollary(in abelian_group) group_action_int_rev:
  assumes "IsLeftModule(int,IntegerAddition,IntegerMultiplication,G,P,S)"
  shows "S={\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat} \<union> {\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
  using group_action_int assms action_unique[of G P S "{\<langle>$# n,{\<langle>x,Fold(P,\<one>,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat} \<union> {\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,\<one>, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"]
  by auto

text\<open>New assumption to consider integers and an abelian group\<close>

locale abelian_group_int_action = abelian_group + int0

text\<open>Under this assumptions, we have an action\<close>

sublocale abelian_group_int_action < int_action:module0 ints IntegerAddition IntegerMultiplication 
  ia iminus isub imult izero ione itwo "\<lambda>q. imult(q,q)" G P "{\<langle>$# n,{\<langle>x,Fold(P,neut,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat} \<union> {\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,neut, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat}"
  neut groper "\<lambda>s g. ({\<langle>$# n,{\<langle>x,Fold(P,neut,n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat} \<union> {\<langle>$- $# n,GroupInv(G,P) O {\<langle>x,Fold(P,neut, n\<times>{x})\<rangle>. x\<in>G}\<rangle>. n\<in>nat})`s`g" inv 
  "\<lambda>g h. groper(g,inv(h))"
  unfolding module0_def module0_axioms_def apply auto using Int_ZF_1_1_L2(3) apply simp
  using groupAssum apply simp using isAbelian apply simp using group_action_int
  unfolding IsLeftModule_def apply simp done

(*
lemma (in abelian_group_int) one_one:
  shows "\<one> = TheNeutralElement(ints,IntegerMultiplication)"

cannot be interpreted. First the unit integer.
\<close>*)

abbreviation (in abelian_group_int_action) zone ("\<one>\<^sub>\<int>") where
"\<one>\<^sub>\<int> \<equiv> ione"

text\<open>Then, the unit in the abelian group\<close>

abbreviation (in abelian_group_int_action) gone ("\<one>\<^sub>G") where
"\<one>\<^sub>G \<equiv> neut"

end