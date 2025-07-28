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

section \<open>$\mathbb{Z}$ modules\<close>

theory IntModule_ZF imports Module_ZF IntGroup_ZF

begin

text\<open>In this section we show that the integers, as a ring, have only one module structure on 
  each abelian group. We will show that the module structure is unique, but we will also show 
  which action is the one that defines that module structure.\<close>

subsection\<open>Integer powers as the only integer actions on abelian groups\<close>

text\<open>As we show in theorem \<open>powz_maps_int_End\<close> in the \<open>IntGroup\<close> theory
  the mapping $\mathbb{Z}\ni n\mapsto (G\ni x\mapsto x^n)$ maps integers to 
  endomorphisms of the abelian group $G$. We will show here that this mapping is the unique 
  action of integers on that group.\<close>

text\<open>When $\mathbb{Z}$ acts on a group, that action is unique.\<close>

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

text\<open>We can use theorems proven in the \<open>abelian_group\<close> locale in the \<open>abgroup_int0\<close>
  locale.\<close>

sublocale abgroup_int0 < abgroup: abelian_group
proof
  from isAbelian show "P {is commutative on} G" by simp
qed

text\<open>The rest of the propositions in this section concern the mapping
  $\mathbb{Z}\ni n\mapsto (G\ni x\mapsto x^n)$. To simplify the statements and 
  proofs we will denote this mapping as $\mathcal{S}$.\<close>

locale abgroup_int1 = abgroup_int0 +
  fixes \<S>
  defines \<S>_def[simp]: "\<S> \<equiv> {\<langle>z,{\<langle>x,powz(z,x)\<rangle>. x\<in>G}\<rangle>. z\<in>\<int>}"

text\<open>The mapping $\mathcal{S}$ is a group homomorphism between $(\mathbb{Z},+)$ and $(G,P)$\<close>

lemma (in abgroup_int1) group_action_int_add_morphism:
  assumes "r\<in>\<int>" "s\<in>\<int>" "g\<in>G"
  shows "(\<S>`(r\<ra>s))`(g) = ((\<S>`(r))`(g))\<cdot>((\<S>`(s))`(g))"
  using assms ints.int_sum_type ZF_fun_from_tot_val1 powz_hom_prop
  by simp
 
text\<open>Same as in lemma \<open>group_action_int_add_morphism\<close> above, but not pointwise:\<close>

lemma (in abgroup_int1) group_action_int_add_morphism_fun:
  assumes "r\<in>\<int>" "s\<in>\<int>"
  shows "\<S>`(r\<ra>s) = EndAdd(G,P)`\<langle>\<S>`(r),\<S>`(s)\<rangle>"
proof -
  let ?F = "EndAdd(G,P)`\<langle>\<S>`(r),\<S>`(s)\<rangle>"
  from assms have 
    "\<S>`(r) \<in> End(G,P)" "\<S>`(s) \<in> End(G,P)" "\<S>`(r\<ra>s) \<in> End(G,P)"
    using powz_maps_int_End ints.int_sum_type apply_funtype 
    by simp_all
  have "EndAdd(G,P):End(G,P)\<times>End(G,P)\<rightarrow>End(G,P)"
    using abgroup.end_addition_group 
    unfolding EndAdd_def IsAgroup_def IsAmonoid_def IsAssociative_def
    by blast
  with \<open>\<S>`(r) \<in> End(G,P)\<close> \<open>\<S>`(s) \<in> End(G,P)\<close> have "?F:G\<rightarrow>G"
    using apply_funtype unfolding End_def by blast
  moreover from \<open>\<S>`(r\<ra>s) \<in> End(G,P)\<close> have "\<S>`(r\<ra>s):G\<rightarrow>G"
    unfolding End_def by simp
  moreover from assms \<open>\<S>`(r) \<in> End(G,P)\<close> \<open>\<S>`(s) \<in> End(G,P)\<close> 
  have "\<forall>g\<in>G. (\<S>`(r\<ra>s))`(g) = ?F`(g)"
    using group_action_int_add_morphism abgroup.end_pointwise_add_val
      unfolding EndAdd_def by simp
  ultimately show "\<S>`(r\<ra>s) = ?F" using func_eq by simp
qed

text\<open>The mapping $\mathcal{S}$ is a homomorphism between $(\mathbb{Z},\cdot)$ and $(G\to G, \circ)$\<close>

lemma (in abgroup_int1) group_action_int_mult_morphism:
  assumes "r\<in>\<int>" "s\<in>\<int>"
  shows "\<S>`(r\<cdot>\<^sub>Zs) = EndMult(G,P)`\<langle>\<S>`(r),\<S>`(s)\<rangle>"
proof -  
  from assms have 
    "\<S>`(r) \<in> End(G,P)" "\<S>`(s) \<in> End(G,P)" "\<S>`(r\<cdot>\<^sub>Zs) \<in> End(G,P)"
    using powz_maps_int_End ints.int_prod_type apply_funtype 
    by simp_all
  from assms have 
    I: "\<S>`(r\<cdot>\<^sub>Zs) = {\<langle>x,powz(s\<cdot>\<^sub>Zr,x)\<rangle>. x\<in>G}" 
    "\<S>`(r) = {\<langle>x,powz(r,x)\<rangle>. x\<in>G}" "\<S>`(s) = {\<langle>x,powz(s,x)\<rangle>. x\<in>G}"
    using ints.int_prod_type ZF_fun_from_tot_val1 ints.Int_ZF_1_L4(2) 
    by simp_all
  from assms(1,2) have "{\<langle>x,powz(s\<cdot>\<^sub>Zr,x)\<rangle>. x\<in>G} = {\<langle>x,powz(r,powz(s,x))\<rangle>. x\<in>G}" 
    using powz_mult by simp
  with assms(1,2) I have "\<S>`(r\<cdot>\<^sub>Zs) = \<S>`(r) O \<S>`(s)"
    using powz_type comp_fun_expr by force
  with \<open>\<S>`(r) \<in> End(G,P)\<close> \<open>\<S>`(s) \<in> End(G,P)\<close> show ?thesis
    unfolding EndMult_def using inend_composition_val by simp
qed

text\<open>The action maps the integer $1$ to the identity, i.e. the neutral element of the
  composition of endomorphisms (which is the multiplication operation of the ring of 
  endomorphisms of the group).\<close>

lemma (in abgroup_int1) group_action_int_unit:
  shows "\<S>`(\<one>\<^sub>Z) = TheNeutralElement(End(G,P),EndMult(G,P))"
proof -
  have "TheNeutralElement(End(G,P),EndMult(G,P)) = id(G)"
    using end_comp_monoid(2) unfolding EndMult_def by blast
  then show ?thesis
    using ints.Int_ZF_1_L8A(2) ZF_fun_from_tot_val1 int_power_zero_one(2) id_diagonal
      by simp
  qed

text\<open>The function from integers to endomorphisms of $G$ defined by $z\mapsto (x\mapsto x^z)$ 
  is a module.\<close>

theorem (in abgroup_int1) group_action_int:
  shows "IsLeftModule(\<int>,IntegerAddition,IntegerMultiplication,G,P,\<S>)"
  using groupAssum isAbelian ints.Int_ZF_1_1_L2 powz_maps_int_End
    group_action_int_add_morphism_fun group_action_int_mult_morphism
    group_action_int_unit
  unfolding IsMorphism_def ringHomomor_def IsAction_def IsLeftModule_def
    by simp

text\<open>If there is a $\mathbb{Z}$-module on an abelian group,
  it is the one found in the previous result.\<close>

theorem (in abgroup_int1) group_action_int_rev0:
  assumes "IsLeftModule(\<int>,IntegerAddition,IntegerMultiplication,G,P,S)"
  shows "S=\<S>"
  using assms group_action_int int0.action_unique by simp

end