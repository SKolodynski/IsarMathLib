(*
    This file is a part of IsarMathLib -
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2024  Daniel de la Concepcion Saez

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

subsection \<open> Linear Combinations on Modules\<close>

theory Module_ZF_1 imports Module_ZF CommutativeSemigroup_ZF

begin

text\<open>Since modules are abelian groups, we can make use of its commutativity to create new elements
by adding acted on elements finitely. Consider two ordered collections of ring elements and of
group elements (indexed by a finite set); then we can add their actions to obtain a new group
element. This is a linear combination.\<close>

definition(in module0)
  LinearComb ("\<Sum>[_;{_,_}]" 88)
  where "fR:C\<rightarrow>R \<Longrightarrow> fG:C\<rightarrow>\<M> \<Longrightarrow> D\<in>FinPow(C) \<Longrightarrow> LinearComb(D,fR,fG) \<equiv> if D\<noteq>0 then CommSetFold(A\<^sub>M,{\<langle>m,(fR`m)\<cdot>\<^sub>S (fG`m)\<rangle>. m\<in>domain(fR)},D)
    else \<Theta>"

text\<open>The function that for each index element gives us the acted element of the 
abelian group is a function from the index to the group.\<close>

lemma(in module0) coordinate_function:
  assumes "AA:C\<rightarrow>R" "B:C\<rightarrow>\<M>"
  shows "{\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>C}:C\<rightarrow>\<M>"
proof-
  {
    fix m assume "m\<in>C"
    then have p:"AA`m\<in>R""B`m\<in>\<M>" using assms(1,2) apply_type by auto
    from p(1) have "H`(AA`m):\<M>\<rightarrow>\<M>" using H_val_type(2) by auto
    then have "(AA`m)\<cdot>\<^sub>S(B`m)\<in>\<M>" using p(2) apply_type by auto
  }
  then have "{\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>C}\<subseteq>C\<times>\<M>" by auto moreover
  {
    fix x y assume "\<langle>x,y\<rangle>\<in>{\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>C}"
    then have xx:"x\<in>C" "y=(AA`x)\<cdot>\<^sub>S (B`x)" by auto
    {
      fix y' assume "\<langle>x,y'\<rangle>\<in>{\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>C}"
      then have "y'=(AA`x)\<cdot>\<^sub>S (B`x)" by auto
      with xx(2) have "y=y'" by auto
    }
    then have "\<forall>y'. \<langle>x,y'\<rangle>\<in>{\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>C} \<longrightarrow> y=y'" by auto
  }
  then have "\<forall>x y. \<langle>x,y\<rangle>\<in>{\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>C} \<longrightarrow> (\<forall>y'. \<langle>x,y'\<rangle>\<in>{\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>C} \<longrightarrow> y=y')"
    by auto 
  moreover have "domain({\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>C})\<subseteq>C" unfolding domain_def by auto ultimately
  show "{\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>C}:C\<rightarrow>\<M>" unfolding Pi_def function_def by auto
qed

text\<open>A linear combination results in a group element where
the functions and the sets are well defined.\<close>

theorem(in module0) linComb_is_in_module:
  assumes "AA:C\<rightarrow>R" "B:C\<rightarrow>\<M>" "D\<in>FinPow(C)"
  shows "(\<Sum>[D;{AA,B}])\<in>\<M>"
proof-
  {
    assume noE:"D\<noteq>0"
    have ffun:"{\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>C}:C\<rightarrow>\<M>" using coordinate_function assms by auto
    note commsemigr.sum_over_set_add_point(1)[OF
      commsemigr.intro[OF _ _ ffun] assms(3) noE]
      mod_ab_gr.abelian_group_axioms abelian_group_def
      group0_def IsAgroup_def IsAmonoid_def abelian_group_axioms_def moreover
    from assms(1) have "domain(AA)=C" unfolding Pi_def by auto
    ultimately have ?thesis unfolding LinearComb_def[OF assms(1-3)] using noE by auto
  }
  then show ?thesis unfolding LinearComb_def[OF assms(1-3)] 
    using mod_ab_gr.group0_2_L2 by auto
qed

text\<open>A linear combination of one element functions is just the action
of one element onto another.\<close>

lemma(in module0) linComb_one_element:
  assumes "x\<in>X" "AA:X\<rightarrow>R" "B:X\<rightarrow>\<M>"
  shows "\<Sum>[{x};{AA,B}]=(AA`x)\<cdot>\<^sub>S(B`x)"
proof-
  have dom:"domain(AA)=X" using assms(2) func1_1_L1 by auto
  have fin:"{x}\<in>FinPow(X)" unfolding FinPow_def using assms(1) by auto
  have A:"\<Sum>[{x};{AA,B}]=CommSetFold(A\<^sub>M,{\<langle>t,(AA`t)\<cdot>\<^sub>S (B`t)\<rangle>. t\<in>X},{x})"
    unfolding LinearComb_def[OF assms(2,3) fin] dom by auto
  have assoc:"A\<^sub>M{is associative on}\<M>" using mod_ab_gr.abelian_group_axioms
    unfolding abelian_group_def group0_def IsAgroup_def IsAmonoid_def by auto
  have comm:"commsemigr(\<M>, A\<^sub>M, X, {\<langle>t,(AA`t)\<cdot>\<^sub>S (B`t)\<rangle>. t\<in>X})"
    unfolding commsemigr_def
    using mod_ab_gr.abelian_group_axioms 
    unfolding abelian_group_def abelian_group_axioms_def
    group0_def IsAgroup_def IsAmonoid_def using coordinate_function[OF assms(2,3)] by auto
  have sing:"1\<approx>{x}" "|{x}|=1" using singleton_eqpoll_1 eqpoll_sym by auto
  then obtain b where b:"b\<in>bij(|{x}|,{x})" "b\<in>bij(1,{x})" unfolding eqpoll_def by auto then
  have "\<Sum>[{x};{AA,B}]=Fold1(A\<^sub>M,{\<langle>t,(AA`t)\<cdot>\<^sub>S (B`t)\<rangle>. t\<in>X} O b)" 
    using commsemigr.sum_over_set_bij[OF comm fin, of b] trans[OF A] by blast
  also have "\<dots>=({\<langle>t,(AA`t)\<cdot>\<^sub>S (B`t)\<rangle>. t\<in>X} O b)`0" using semigr0.prod_of_1elem unfolding semigr0_def using
    comp_fun[OF _ coordinate_function[OF assms(2,3)], of b 1] b(2) assms(1) func1_1_L1B[of b 1 "{x}" X] assoc unfolding bij_def inj_def by blast
  also have "\<dots>=({\<langle>t,(AA`t)\<cdot>\<^sub>S (B`t)\<rangle>. t\<in>X})`(b`0)" using comp_fun_apply b unfolding bij_def inj_def by auto
  also have "\<dots>= {\<langle>t,(AA`t)\<cdot>\<^sub>S (B`t)\<rangle>. t\<in>X}`x" using apply_type[of b 1 "\<lambda>t. {x}" 0] b unfolding bij_def inj_def
    by auto
  ultimately show ?thesis using apply_equality[OF _ coordinate_function[OF assms(2,3)]] assms(1) by auto
qed

text \<open>Since a linear combination is a group element, it makes sense to apply the action onto it.
With this result we simplify it to a linear combination.\<close>

lemma(in module0) linComb_action:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>\<M>" "r\<in>R" "D\<in>FinPow(X)"
  shows "r\<cdot>\<^sub>S(\<Sum>[D;{AA,B}])=\<Sum>[D;{{\<langle>k,r\<cdot>(AA`k)\<rangle>. k\<in>X},B}]" 
    and "{\<langle>m,r \<cdot>(AA`m)\<rangle>. m\<in>X}:X\<rightarrow>R"
proof-
  show f:"{\<langle>m,r \<cdot>(AA`m)\<rangle>. m\<in>X}:X\<rightarrow>R" unfolding Pi_def function_def domain_def
    using apply_type[OF assms(1)] assms(3) Ring_ZF_1_L4(3) by auto
  {
    fix AAt Bt assume as:"AAt:X \<rightarrow> R" "Bt:X \<rightarrow> \<M>"
    have "\<Sum>[0;{AAt,Bt}]=\<Theta>" using LinearComb_def[OF as] unfolding FinPow_def by auto
    then have "r \<cdot>\<^sub>S (\<Sum>[0;{AAt,Bt}])=\<Theta>" using assms(3) zero_fixed by auto moreover
    have mr:"{\<langle>m,r\<cdot>(AAt`m)\<rangle>. m\<in>X}:X\<rightarrow>R" unfolding Pi_def function_def domain_def
      using apply_type[OF as(1)] assms(3) Ring_ZF_1_L4(3) by auto
    then have "\<Sum>[0;{{\<langle>x, r \<cdot> (AAt ` x)\<rangle> . x \<in> X},Bt}]=\<Theta>" using LinearComb_def[OF mr as(2)]
      unfolding FinPow_def by auto
    ultimately have "r \<cdot>\<^sub>S (\<Sum>[0;{AAt,Bt}]) = \<Sum>[0;{{\<langle>x, r \<cdot>(AAt ` x)\<rangle> . x \<in> X},Bt}]" by auto
  }
  then have case0:"(\<forall>AAt\<in>X \<rightarrow> R.
    \<forall>Bt\<in>X \<rightarrow> \<M>. r \<cdot>\<^sub>S (\<Sum>[0;{AAt,Bt}]) = \<Sum>[0;{{\<langle>x, r \<cdot> (AAt ` x)\<rangle> . x \<in> X},Bt}])" by auto
  {
    fix Tk assume A:"Tk\<in>FinPow(X)" "Tk\<noteq>0"
    then obtain t where tt:"t\<in>Tk" by auto
    {
      assume "(\<forall>AAk\<in>X\<rightarrow>R. \<forall>Bk\<in>X\<rightarrow>\<M>. (r\<cdot>\<^sub>S(\<Sum>[Tk-{t};{AAk,Bk}])=\<Sum>[Tk-{t};{{\<langle>k,r\<cdot>(AAk`k)\<rangle>. k\<in>X},Bk}]))"
      with tt obtain t where t:"t\<in>Tk" "(\<forall>AAk\<in>X\<rightarrow>R. \<forall>Bk\<in>X\<rightarrow>\<M>. (r\<cdot>\<^sub>S(\<Sum>[Tk-{t};{AAk,Bk}])=\<Sum>[Tk-{t};{{\<langle>k,r\<cdot>(AAk`k)\<rangle>. k\<in>X},Bk}]))" by auto
      let ?Tk="Tk-{t}"
      have CC:"Tk=?Tk\<union>{t}" using t by auto
      have DD:"?Tk\<in>FinPow(X)" using A(1) unfolding FinPow_def using subset_Finite[of ?Tk Tk]
        by auto
      have tX:"t\<in>X" using t(1) A(1) unfolding FinPow_def by auto
      then have EE:"X-(?Tk)=(X-Tk)\<union>{t}" using t(1) by auto
      {
        assume as:"Tk-{t}\<noteq>0"
        with t have BB:"t\<in>Tk" "Tk-{t}\<noteq>0" "\<forall>AAk\<in>X\<rightarrow>R. \<forall>Bk\<in>X\<rightarrow>\<M>. (r\<cdot>\<^sub>S(\<Sum>[Tk-{t};{AAk,Bk}])=\<Sum>[Tk-{t};{{\<langle>k,r\<cdot>(AAk`k)\<rangle>. k\<in>X},Bk}])" by auto
        from BB(3) have A3:"\<forall>AAk\<in>X\<rightarrow>R. \<forall>Bk\<in>X\<rightarrow>\<M>. (r\<cdot>\<^sub>S(\<Sum>[?Tk;{AAk,Bk}])=\<Sum>[?Tk;{{\<langle>k,r\<cdot>(AAk`k)\<rangle>. k\<in>X},Bk}])" by auto
        {
          fix AAt Bt assume B:"AAt:X\<rightarrow>R" "Bt:X\<rightarrow>\<M>"
          then have af:"{\<langle>k,(AAt`k)\<cdot>\<^sub>S(Bt`k)\<rangle>. k\<in>X}:X\<rightarrow>\<M>" using coordinate_function by auto
          have comm:"commsemigr(\<M>, A\<^sub>M, X, {\<langle>k,(AAt`k)\<cdot>\<^sub>S(Bt`k)\<rangle>. k\<in>X})"
            unfolding commsemigr_def
            using mod_ab_gr.abelian_group_axioms 
            unfolding abelian_group_def abelian_group_axioms_def
            group0_def IsAgroup_def IsAmonoid_def using af by auto
          then have "CommSetFold(A\<^sub>M,{\<langle>k,(AAt`k)\<cdot>\<^sub>S(Bt`k)\<rangle>. k\<in>X},Tk)=CommSetFold(A\<^sub>M,{\<langle>k,(AAt`k)\<cdot>\<^sub>S(Bt`k)\<rangle>. k\<in>X},?Tk)
            +\<^sub>V({\<langle>k,(AAt`k)\<cdot>\<^sub>S(Bt`k)\<rangle>. k\<in>X}`t)" using commsemigr.sum_over_set_add_point(2)[of \<M> A\<^sub>M X "{\<langle>k,(AAt`k)\<cdot>\<^sub>S(Bt`k)\<rangle>. k\<in>X}" "Tk-{t}"] DD BB(2) 
            A(1-2) EE CC by auto
          also have "\<dots>=CommSetFold(A\<^sub>M,{\<langle>k,(AAt`k)\<cdot>\<^sub>S(Bt`k)\<rangle>. k\<in>X},?Tk)
            +\<^sub>V((AAt`t)\<cdot>\<^sub>S(Bt`t))" using apply_equality[OF _ af, of t "(AAt`t)\<cdot>\<^sub>S(Bt`t)"] tX by auto
          ultimately have "CommSetFold(A\<^sub>M,{\<langle>k,(AAt`k)\<cdot>\<^sub>S(Bt`k)\<rangle>. k\<in>X},Tk)=CommSetFold(A\<^sub>M,{\<langle>k,(AAt`k)\<cdot>\<^sub>S(Bt`k)\<rangle>. k\<in>X},?Tk)
            +\<^sub>V((AAt`t)\<cdot>\<^sub>S(Bt`t))" by auto moreover
          have "domain(AAt)=X" using B(1) Pi_def by auto ultimately
          have "(\<Sum>[Tk;{AAt,Bt}])=(\<Sum>[?Tk;{AAt,Bt}])+\<^sub>V((AAt`t)\<cdot>\<^sub>S(Bt`t))" unfolding LinearComb_def[OF B(1,2) A(1)]
            LinearComb_def[OF B(1,2) DD] using as A(2) by auto
          then have eq:"r\<cdot>\<^sub>S(\<Sum>[Tk;{AAt,Bt}])=r\<cdot>\<^sub>S((\<Sum>[?Tk;{AAt,Bt}])+\<^sub>V((AAt`t)\<cdot>\<^sub>S(Bt`t)))" by auto
          moreover have "\<forall>g\<in>\<M>. \<forall>h\<in>\<M>. (H`r)`(g+\<^sub>Vh)=((H`r)`g)+\<^sub>V((H`r)`h)" 
            using module_ax1 assms(3) by auto
          moreover have AR:"AAt`t\<in>R" using B(1) tX apply_type by auto
          then have "H`(AAt`t):\<M>\<rightarrow>\<M>" using H_val_type(2) by auto
          from apply_type[OF this] have "(AAt`t)\<cdot>\<^sub>S(Bt`t)\<in>\<M>" using apply_type[OF B(2)] tX by auto moreover
          have mr:"{\<langle>m,r\<cdot>(AAt`m)\<rangle>. m\<in>X}:X\<rightarrow>R" unfolding Pi_def function_def domain_def
            using apply_type[OF B(1)] assms(3) Ring_ZF_1_L4(3) by auto
          then have fff:"{\<langle>m,({\<langle>m,r\<cdot>(AAt`m)\<rangle>. m\<in>X}`m)\<cdot>\<^sub>S(Bt`m)\<rangle>. m\<in>X}:X\<rightarrow>\<M>" using coordinate_function[OF mr B(2)] apply_equality[OF _ mr] by auto
          with tX have pff:"\<langle>t,({\<langle>m,r\<cdot>(AAt`m)\<rangle>. m\<in>X}`t)\<cdot>\<^sub>S(Bt`t)\<rangle>\<in>{\<langle>m,({\<langle>m,r\<cdot>(AAt`m)\<rangle>. m\<in>X}`m)\<cdot>\<^sub>S(Bt`m)\<rangle>. m\<in>X}"
            by auto
          have dom:"domain({\<langle>m,(r\<cdot>(AAt`m))\<rangle>. m\<in>X})=X" by auto
          have comm2:"commsemigr(\<M>, A\<^sub>M, X, {\<langle>m, ({\<langle>x,r \<cdot>(AAt`x)\<rangle>. x\<in>X}`m)\<cdot>\<^sub>S(Bt`m)\<rangle>. m\<in>X})"
            unfolding commsemigr_def
            using mod_ab_gr.abelian_group_axioms 
            unfolding abelian_group_def abelian_group_axioms_def
            group0_def IsAgroup_def IsAmonoid_def using fff by auto
          have "\<Sum>[?Tk;{AAt,Bt}]\<in>\<M>" using linComb_is_in_module[OF B(1,2) DD].
          ultimately have "r \<cdot>\<^sub>S ((\<Sum>[?Tk;{AAt,Bt}]) +\<^sub>V ((AAt ` t) \<cdot>\<^sub>S (Bt ` t)))=(r\<cdot>\<^sub>S(\<Sum>[?Tk;{AAt,Bt}]))+\<^sub>V(r\<cdot>\<^sub>S((AAt`t)\<cdot>\<^sub>S(Bt`t)))"
            by auto
          also have "\<dots>=(r\<cdot>\<^sub>S(\<Sum>[?Tk;{AAt,Bt}]))+\<^sub>V((r\<cdot>(AAt`t))\<cdot>\<^sub>S(Bt`t))" using module_ax3
            assms(3) AR apply_type[OF B(2)] tX by auto
          also have "\<dots>=(\<Sum>[?Tk;{{\<langle>x,r\<cdot>(AAt`x)\<rangle>. x\<in>X},Bt}])+\<^sub>V((r\<cdot>(AAt`t))\<cdot>\<^sub>S(Bt`t))"
            using A3 B(1,2) by auto
          also have "\<dots>=(\<Sum>[?Tk;{{\<langle>x,r\<cdot>(AAt`x)\<rangle>. x\<in>X},Bt}])+\<^sub>V(({\<langle>m, r \<cdot> (AAt ` m)\<rangle> . m \<in> X} `t)\<cdot>\<^sub>S(Bt`t))"
            using apply_equality[OF _ mr] tX by auto
          also have "\<dots>=(\<Sum>[?Tk;{{\<langle>x,r\<cdot>(AAt`x)\<rangle>. x\<in>X},Bt}])+\<^sub>V({\<langle>m, ({\<langle>x,(r \<cdot>(AAt`x))\<rangle>. x\<in>X}`m)\<cdot>\<^sub>S(Bt`m)\<rangle>. m\<in>X}`t)"
            using apply_equality[OF pff fff] by auto
          also have "\<dots>=CommSetFold(A\<^sub>M,{\<langle>m, ({\<langle>x,r \<cdot>(AAt`x)\<rangle>. x\<in>X}`m)\<cdot>\<^sub>S(Bt`m)\<rangle>. m\<in>X},?Tk)+\<^sub>V({\<langle>m, ({\<langle>x,(r \<cdot>(AAt`x))\<rangle>. x\<in>X}`m)\<cdot>\<^sub>S(Bt`m)\<rangle>. m\<in>X}`t)"
            unfolding LinearComb_def[OF mr B(2) DD] using dom as by auto
          also have "\<dots>=CommSetFold(A\<^sub>M,{\<langle>m, ({\<langle>x,r \<cdot>(AAt`x)\<rangle>. x\<in>X}`m)\<cdot>\<^sub>S(Bt`m)\<rangle>. m\<in>X},Tk)" using 
            commsemigr.sum_over_set_add_point(2)[OF comm2, of "Tk-{t}"] fff DD tX CC BB(2) by auto
          ultimately have "r \<cdot>\<^sub>S ((\<Sum>[?Tk;{AAt,Bt}]) +\<^sub>V ((AAt ` t) \<cdot>\<^sub>S (Bt ` t))) =CommSetFold(A\<^sub>M,{\<langle>m, ({\<langle>x,r \<cdot>(AAt`x)\<rangle>. x\<in>X}`m)\<cdot>\<^sub>S(Bt`m)\<rangle>. m\<in>X},Tk)"
            by auto
          with eq have "r \<cdot>\<^sub>S (\<Sum>[Tk;{AAt,Bt}]) =CommSetFold(A\<^sub>M,{\<langle>m, ({\<langle>x,r \<cdot>(AAt`x)\<rangle>. x\<in>X}`m)\<cdot>\<^sub>S(Bt`m)\<rangle>. m\<in>X},Tk)" by auto
          also have "\<dots>=\<Sum>[Tk;{{\<langle>x,r\<cdot>(AAt`x)\<rangle>. x\<in>X},Bt}]" using A(2) unfolding LinearComb_def[OF mr B(2) A(1)] dom by auto
          ultimately have "r \<cdot>\<^sub>S (\<Sum>[Tk;{AAt,Bt}]) =\<Sum>[Tk;{{\<langle>x,r\<cdot>(AAt`x)\<rangle>. x\<in>X},Bt}]" by auto
        }
        then have "\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>\<M>. r \<cdot>\<^sub>S (\<Sum>[Tk;{AA,B}]) =\<Sum>[Tk;{{\<langle>x,r\<cdot>(AA`x)\<rangle>. x\<in>X},B}]" using BB by auto
      }
      moreover
      {
        assume "Tk-{t}=0"
        then have sing:"Tk={t}" using A(2) by auto
        {
          fix AAt Bt assume B:"AAt:X\<rightarrow>R" "Bt:X\<rightarrow>\<M>"
          have mr:"{\<langle>m,r\<cdot>(AAt`m)\<rangle>. m\<in>X}:X\<rightarrow>R" unfolding Pi_def function_def domain_def
            using apply_type[OF B(1)] assms(3) Ring_ZF_1_L4(3) by auto
          from sing have "\<Sum>[Tk;{AAt,Bt}]=(AAt`t)\<cdot>\<^sub>S(Bt`t)" using linComb_one_element[OF tX B]
            by auto
          then have "r \<cdot>\<^sub>S (\<Sum>[Tk;{AAt,Bt}])=r \<cdot>\<^sub>S ((AAt`t)\<cdot>\<^sub>S(Bt`t))" by auto
          also have "\<dots>=(r \<cdot> (AAt`t))\<cdot>\<^sub>S(Bt`t)" using module_ax3 assms(3) apply_type[OF B(1) tX]
            apply_type[OF B(2) tX] by auto
          also have "\<dots>=({\<langle>m,(r \<cdot> (AAt`m))\<rangle>. m\<in>X}`t)\<cdot>\<^sub>S(Bt`t)" using apply_equality[OF _ mr] tX by auto
          also have "\<dots>=\<Sum>[Tk;{{\<langle>m,(r \<cdot> (AAt`m))\<rangle>. m\<in>X},Bt}]" using sing linComb_one_element[OF tX mr B(2)]
            by auto
          ultimately have "r \<cdot>\<^sub>S (\<Sum>[Tk;{AAt,Bt}])=\<Sum>[Tk;{{\<langle>m,(r \<cdot> (AAt`m))\<rangle>. m\<in>X},Bt}]" by auto
        }
      }
      ultimately have " \<forall>AA\<in>X \<rightarrow> R. \<forall>B\<in>X \<rightarrow> \<M>. r \<cdot>\<^sub>S (\<Sum>[Tk;{AA,B}]) = \<Sum>[Tk;{{\<langle>x, r \<cdot> (AA ` x)\<rangle> . x \<in> X},B}]"
        by auto
    }
    with tt have "\<exists>t\<in>Tk. (\<forall>AAt\<in>X \<rightarrow> R.  \<forall>Bt\<in>X \<rightarrow> \<M>.
                      r \<cdot>\<^sub>S (\<Sum>[Tk - {t};{AAt,Bt}]) =
                      \<Sum>[Tk - {t};{{\<langle>x, r \<cdot> (AAt ` x)\<rangle> . x \<in> X},Bt}]) \<longrightarrow>
               (\<forall>AAt\<in>X \<rightarrow> R. \<forall>Bt\<in>X \<rightarrow> \<M>.
                      r \<cdot>\<^sub>S (\<Sum>[Tk;{AAt,Bt}]) = \<Sum>[Tk;{{\<langle>x, r \<cdot> (AAt ` x)\<rangle> . x \<in> X},Bt}])" by auto
  }
  then have caseStep:"\<forall>A\<in>FinPow(X). A\<noteq>0 \<longrightarrow> (\<exists>t\<in>A. (\<forall>AAt\<in>X \<rightarrow> R.
                   \<forall>Bt\<in>X \<rightarrow> \<M>.
                      r \<cdot>\<^sub>S (\<Sum>[A - {t};{AAt,Bt}]) =
                      \<Sum>[A - {t};{{\<langle>x, r \<cdot> (AAt ` x)\<rangle> . x \<in> X},Bt}]) \<longrightarrow>
               (\<forall>AAt\<in>X \<rightarrow> R.
                   \<forall>Bt\<in>X \<rightarrow> \<M>.
                      r \<cdot>\<^sub>S (\<Sum>[A;{AAt,Bt}]) = \<Sum>[A;{{\<langle>x, r \<cdot> (AAt ` x)\<rangle> . x \<in> X},Bt}]))" by auto
  have "\<forall>AAt\<in>X\<rightarrow>R. \<forall>Bt\<in>X\<rightarrow>\<M>. r \<cdot>\<^sub>S(\<Sum>[D;{AAt,Bt}]) =\<Sum>[D;{{\<langle>x,r\<cdot>(AAt`x)\<rangle>. x\<in>X},Bt}]" using
    FinPow_ind_rem_one[where P="\<lambda>D. (\<forall>AAt\<in>X\<rightarrow>R. \<forall>Bt\<in>X\<rightarrow>\<M>. r \<cdot>\<^sub>S(\<Sum>[D;{AAt,Bt}]) =\<Sum>[D;{{\<langle>x,r\<cdot>(AAt`x)\<rangle>. x\<in>X},Bt}])",
    OF case0 caseStep] assms(4) by auto
  with assms(1,2) show "r \<cdot>\<^sub>S(\<Sum>[D;{AA,B}]) =\<Sum>[D;{{\<langle>x,r\<cdot>(AA`x)\<rangle>. x\<in>X},B}]" by auto
qed

text\<open>A linear combination can always be defined on a cardinal.\<close>

lemma(in module0) linComb_reorder_terms1:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>\<M>" "D\<in>FinPow(X)" "g\<in>bij(|D|,D)"
  shows "(\<Sum>[D;{AA,B}])=\<Sum>[|D|;{AA O g,B O g}]"
proof-
  from assms(3,4) have funf:"g:|D|\<rightarrow>X" unfolding bij_def inj_def FinPow_def using func1_1_L1B by auto
  have ABfun:"AA O g:|D|\<rightarrow>R" "B O g:|D|\<rightarrow>\<M>" using comp_fun[OF funf assms(1)] comp_fun[OF funf assms(2)] by auto
  then have domAg:"domain(AA O g)=|D|" unfolding Pi_def by auto
  from assms(1) have domA:"domain(AA)=X" unfolding Pi_def by auto
  have comm:"commsemigr(\<M>, A\<^sub>M, domain(AA), {\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>domain(AA)})"
    unfolding commsemigr_def using mod_ab_gr.abelian_group_axioms unfolding IsAgroup_def
    IsAmonoid_def abelian_group_def group0_def abelian_group_axioms_def
    using coordinate_function[OF assms(1,2)] domA by auto
  {
    assume A:"D=0"
    then have D:"\<Sum>[D;{AA,B}]=\<Theta>" using LinearComb_def assms(1-3) by auto moreover
    from A assms(4) have "|D|=0" unfolding bij_def inj_def Pi_def by auto
    moreover then have "|D|\<in>FinPow(|D|)" unfolding FinPow_def by auto moreover
    note ABfun
    ultimately have ?thesis using LinearComb_def[of "AA O g" "|D|" "B O g", of "|D|"] by auto
  }
  moreover
  {
    assume A:"D\<noteq>0"
    then have eqD:"\<Sum>[D;{AA,B}]=CommSetFold(A\<^sub>M,{\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>domain(AA)},D)" using LinearComb_def[OF assms(1-3)] by auto
    have eqD1:"CommSetFold(A\<^sub>M,{\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>domain(AA)},D)=Fold1(A\<^sub>M,{\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>domain(AA)} O g)" 
      using commsemigr.sum_over_set_bij[OF comm] assms(3) A
      domA assms(4) by blast
    {
      fix n assume n:"n\<in>|D|"
      then have T:"({\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>domain(AA)} O g)`n={\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>domain(AA)}`( g`n)"
        using comp_fun_apply funf unfolding bij_def inj_def by auto
      have "g`n\<in>D" using assms(4) unfolding bij_def inj_def using apply_type n by auto
      then have "g`n\<in>domain(AA)" using domA assms(3) unfolding FinPow_def by auto
      then have "{\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>domain(AA)}`( g`n)=(AA`(g`n))\<cdot>\<^sub>S (B`( g`n))" using apply_equality[OF _ coordinate_function[OF assms(1,2)]]
        domA by auto
      also have "\<dots>=((AA O g)`n)\<cdot>\<^sub>S ((B O g)`n)" using comp_fun_apply funf n by auto
      also have "\<dots>={\<langle>m,((AA O g)`m)\<cdot>\<^sub>S ((B O g)`m)\<rangle>. m\<in>|D|}`n" using apply_equality[OF _ coordinate_function[OF comp_fun[OF funf assms(1)] comp_fun[OF funf assms(2)]]]
        n by auto
      ultimately have "({\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>domain(AA)} O g)`n={\<langle>m,((AA O g)`m)\<cdot>\<^sub>S ((B O g)`m)\<rangle>. m\<in>|D|}`n" using T by auto
    }
    then have "\<forall>x\<in>|D|. ({\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>domain(AA)} O g)`x={\<langle>m,((AA O g)`m)\<cdot>\<^sub>S ((B O g)`m)\<rangle>. m\<in>|D|}`x" by auto
    then have eq:"{\<langle>m,(AA`m)\<cdot>\<^sub>S (B`m)\<rangle>. m\<in>domain(AA)} O g={\<langle>m,((AA O g)`m)\<cdot>\<^sub>S ((B O g)`m)\<rangle>. m\<in>|D|}" using func_eq[OF comp_fun[OF funf coordinate_function[OF assms(1) assms(2)]]
      coordinate_function[OF comp_fun[OF funf assms(1)] comp_fun[OF funf assms(2)]]] domA by auto
    have R1:"\<Sum>[D;{AA,B}]=Fold1(A\<^sub>M,{\<langle>m,((AA O g)`m)\<cdot>\<^sub>S ((B O g)`m)\<rangle>. m\<in>|D|})"
      using trans[OF eqD eqD1] subst[OF eq, of "\<lambda>t. \<Sum>[D;{AA,B}] = Fold1(A\<^sub>M,t)"] by blast
    from A have Dno:"|D|\<noteq>0" using assms(4) unfolding bij_def surj_def by auto
    have "||D||=|D|" using cardinal_cong assms(4) unfolding eqpoll_def by auto
    then have idf:"id(|D|)\<in>bij(||D||,|D|)" using id_bij by auto
    have comm:"commsemigr(\<M>, A\<^sub>M, |D|, {\<langle>m, ((AA O g) ` m) \<cdot>\<^sub>S ((B O g) ` m)\<rangle> . m \<in> |D|})"
      unfolding commsemigr_def using mod_ab_gr.abelian_group_axioms
      unfolding abelian_group_def group0_def IsAgroup_def IsAmonoid_def
      abelian_group_axioms_def using coordinate_function[OF comp_fun[OF funf assms(1)] comp_fun[OF funf assms(2)]]
      by auto
    have sub:"{\<langle>m, ((AA O g) ` m) \<cdot>\<^sub>S ((B O g) ` m)\<rangle> . m \<in> |D|} \<subseteq> |D|\<times>\<M>" using
      coordinate_function[OF comp_fun[OF funf assms(1)] comp_fun[OF funf assms(2)]]
      unfolding Pi_def by auto
    have finE:"Finite(|D|)" using assms(4,3) eqpoll_imp_Finite_iff unfolding eqpoll_def FinPow_def by auto
    then have EFP:"|D|\<in>FinPow(|D|)" unfolding FinPow_def by auto
    then have eqE:"\<Sum>[|D|;{AA O g,B O g}]=CommSetFold(A\<^sub>M,{\<langle>m,((AA O g)`m)\<cdot>\<^sub>S ((B O g)`m)\<rangle>. m\<in>domain(AA O g)},|D|)" using LinearComb_def[OF comp_fun[OF funf assms(1)]
      comp_fun[OF funf assms(2)]] Dno by auto
    also have "\<dots>=CommSetFold(A\<^sub>M,{\<langle>m,((AA O g)`m)\<cdot>\<^sub>S ((B O g)`m)\<rangle>. m\<in>|D|},|D|)" using domAg by auto
    also have "\<dots>=Fold1(A\<^sub>M,{\<langle>m,((AA O g)`m)\<cdot>\<^sub>S ((B O g)`m)\<rangle>. m\<in>|D|})" using commsemigr.sum_over_set_bij[OF comm
      EFP Dno idf]
      subst[OF right_comp_id[of "{\<langle>m,((AA O g)`m)\<cdot>\<^sub>S ((B O g)`m)\<rangle>. m\<in>|D|}" "|D|" \<M>, OF sub], 
        of "\<lambda>t. CommSetFold(A\<^sub>M,{\<langle>m,((AA O g)`m)\<cdot>\<^sub>S ((B O g)`m)\<rangle>. m\<in>|D|},|D|) = Fold1(A\<^sub>M,t)"]
      by blast
    ultimately have "\<Sum>[|D|;{AA O g,B O g}]=Fold1(A\<^sub>M,{\<langle>m,((AA O g)`m)\<cdot>\<^sub>S ((B O g)`m)\<rangle>. m\<in>|D|})"
      by (simp only:trans)
    with R1 have ?thesis by (simp only:trans sym)
  }
  ultimately show ?thesis by blast
qed

text\<open>Actually a linear combination can be defined over any
bijective set with the original set.\<close>

lemma(in module0) linComb_reorder_terms2:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>\<M>" "D\<in>FinPow(X)" "g\<in>bij(E,D)"
  shows "(\<Sum>[D;{AA,B}])=\<Sum>[E;{AA O g,B O g}]"
proof-
  from assms(3,4) have funf:"g:E\<rightarrow>X" unfolding bij_def inj_def FinPow_def using func1_1_L1B by auto
  have ABfun:"AA O g:E\<rightarrow>R" "B O g:E\<rightarrow>\<M>" using comp_fun[OF funf assms(1)] comp_fun[OF funf assms(2)] by auto
  then have domAg:"domain(AA O g)=E" unfolding Pi_def by auto
  from assms(1) have domA:"domain(AA)=X" unfolding Pi_def by auto
  from assms(3-4) have finE:"Finite(E)" unfolding FinPow_def using eqpoll_imp_Finite_iff unfolding eqpoll_def by auto
  then have "|E|\<approx>E" using well_ord_cardinal_eqpoll Finite_imp_well_ord by blast
  then obtain h where h:"h\<in>bij(|E|,E)" unfolding eqpoll_def by auto
  then have "(g O h)\<in>bij(|E|,D)" using comp_bij assms(4) by auto moreover
  have ED:"|E|=|D|" using cardinal_cong assms(4) unfolding eqpoll_def by auto
  ultimately have "(g O h)\<in>bij(|D|,D)" by auto
  then have "(\<Sum>[D;{AA,B}])=(\<Sum>[|D|;{AA O (g O h),B O (g O h)}])" using linComb_reorder_terms1 assms(1-3) by auto moreover
  from h have "(\<Sum>[E;{AA O g,B O g}])=(\<Sum>[|E|;{(AA O g) O h,(B O g) O h}])" using linComb_reorder_terms1 comp_fun[OF funf assms(1)] comp_fun[OF funf assms(2)] 
    finE unfolding FinPow_def by auto
  moreover note ED ultimately
  show ?thesis using comp_assoc by auto
qed

text\<open>Restricting the defining functions to the domain set does nothing to
the linear combination\<close>

corollary(in module0) linComb_restrict_coord:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>\<M>" "D\<in>FinPow(X)"
  shows "(\<Sum>[D;{AA,B}])=\<Sum>[D;{restrict(AA,D),restrict(B,D)}]"
  using linComb_reorder_terms2[OF assms id_bij] right_comp_id_any by auto

text\<open>A linear combination can by defined with a natural number
and functions with that number as domain.\<close>

corollary(in module0) linComb_nat:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>\<M>" "D\<in>FinPow(X)"
  shows "\<exists>n\<in>nat. \<exists>A1\<in>n\<rightarrow>R. \<exists>B1\<in>n\<rightarrow>\<M>. \<Sum>[D;{AA,B}]=\<Sum>[n;{A1,B1}] \<and> A1``n=AA``D \<and> B1``n=B``D"
proof
  from assms(3) have fin:"Finite(D)" unfolding FinPow_def by auto
  then obtain n where n:"n\<in>nat" "D\<approx>n" unfolding Finite_def by auto moreover
  from fin have "|D|\<approx>D" using well_ord_cardinal_eqpoll Finite_imp_well_ord by blast
  ultimately have "|D|\<approx>n" "n\<in>nat" using eqpoll_trans[of "|D|"] by auto
  then have "n\<in>nat" "||D||=|n|" using cardinal_cong by auto
  then have D:"|D|=n" "n\<in>nat" using Card_cardinal_eq[OF Card_cardinal] Card_cardinal_eq[OF nat_into_Card] by auto
  then show "|D|\<in>nat" by auto
  from n(2) D(1) obtain g where g:"g\<in>bij(|D|,D)" using eqpoll_sym unfolding eqpoll_def by auto
  show "\<exists>A1\<in>|D|\<rightarrow>R. \<exists>B1\<in>|D|\<rightarrow>\<M>. \<Sum>[D;{AA,B}]=\<Sum>[|D|;{A1,B1}] \<and> A1``|D|=AA``D \<and> B1``|D|=B``D"
  proof
    from g have gX:"g:|D|\<rightarrow>X" unfolding bij_def inj_def using assms(3) unfolding FinPow_def using func1_1_L1B by auto
    then show "(AA O g):|D|\<rightarrow>R" using comp_fun assms(1) by auto
    show "\<exists>B1\<in>|D|\<rightarrow>\<M>. \<Sum>[D;{AA,B}]=\<Sum>[|D|;{AA O g,B1}] \<and> (AA O g)``|D|=AA``D \<and> B1``|D|=B``D"
    proof
      show "(B O g):|D|\<rightarrow>\<M>" using comp_fun assms(2) gX by auto
      have "\<Sum>[D;{AA,B}]=\<Sum>[|D|;{AA O g,B O g}]" using g linComb_reorder_terms1 assms func1_1_L1B by auto
      moreover have "(AA O g)``|D|=AA``(g``|D|)" using image_comp by auto
      then have "(AA O g)``|D|=AA``D" using g unfolding bij_def using surj_range_image_domain by auto
      moreover have "(B O g)``|D|=B``(g``|D|)" using image_comp by auto
      then have "(B O g)``|D|=B``D" using g unfolding bij_def using surj_range_image_domain by auto
      ultimately show "\<Sum>[D;{AA,B}]=\<Sum>[|D|;{AA O g,B O g}] \<and> (AA O g)``|D|=AA``D \<and> (B O g)``|D|=B``D" by auto
    qed
  qed
qed

subsubsection\<open>Adding linear combinations\<close>

text \<open>Adding a linear combination defined over $\emptyset$ leaves it as is\<close>

lemma(in module0) linComb_sum_base_induct1:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>\<M>" "D\<in>FinPow(X)" "AA1:Y\<rightarrow>R" "B1:Y\<rightarrow>\<M>"
  shows "(\<Sum>[D;{AA,B}])+\<^sub>V(\<Sum>[0;{AA1,B1}])=\<Sum>[D;{AA,B}]"
proof-
  from assms(1-3) have "\<Sum>[D;{AA,B}]\<in>\<M>" using linComb_is_in_module by auto
  then have eq:"(\<Sum>[D;{AA,B}])+\<^sub>V\<Theta>=\<Sum>[D;{AA,B}]" using zero_neutral(1)
    by auto moreover
  have ff:"0\<in>FinPow(Y)" unfolding FinPow_def by auto
  from eq show ?thesis using LinearComb_def[OF assms(4-5) ff] by auto
qed

text\<open>Applying a product of $1\times$ to the defining set computes the same linear combination; since they are bijective sets\<close>

lemma(in module0) linComb_sum_base_induct2:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>\<M>" "D\<in>FinPow(X)"
  shows "(\<Sum>[D;{AA,B}])=\<Sum>[{0}\<times>D;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}}]" and
  "(\<Sum>[D;{AA,B}])=\<Sum>[{0}\<times>D;{restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D),restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)}]"
proof-
  let ?g="{\<langle>\<langle>0,d\<rangle>,d\<rangle>. d\<in>D}"
  from assms(3) have sub:"D\<subseteq>X" unfolding FinPow_def by auto
  have gfun:"?g:{0}\<times>D\<rightarrow>D" unfolding Pi_def function_def by blast
  then have gfunX:"?g:{0}\<times>D\<rightarrow>X" using sub func1_1_L1B by auto
  from gfun have "?g\<in>surj({0}\<times>D,D)" unfolding surj_def using apply_equality[OF _ gfun] by blast moreover
  {
    fix w y assume "?g`w=?g`y" "w\<in>{0}\<times>D" "y\<in>{0}\<times>D"
    then obtain dw dy where "w=\<langle>0,dw\<rangle>" "y=\<langle>0,dy\<rangle>" "?g`w=?g`y" "dw\<in>D" "dy\<in>D" by auto
    then have "dw=dy" "w=\<langle>0,dw\<rangle>" "y=\<langle>0,dy\<rangle>" using apply_equality[OF _ gfun, of w dw] apply_equality[OF _ gfun, of y dy] by auto
    then have "w=y" by auto
  }
  then have "?g\<in>inj({0}\<times>D,D)" unfolding inj_def using gfun by auto ultimately
  have gbij:"?g\<in>bij({0}\<times>D,D)" unfolding bij_def by auto
  with assms have A1:"(\<Sum>[D;{AA,B}])=\<Sum>[{0}\<times>D;{AA O ?g,B O ?g}]" using linComb_reorder_terms2 by auto
  from gbij have "Finite({0}\<times>D)" using assms(3) eqpoll_imp_Finite_iff unfolding FinPow_def eqpoll_def by auto
  then have fin:"{0}\<times>D\<in>FinPow({0}\<times>X)" unfolding FinPow_def using sub by auto
  have A0:"{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}:{0}\<times>X\<rightarrow>R" unfolding Pi_def function_def using apply_type[OF assms(1)] by auto
  have B0:"{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}:{0}\<times>X\<rightarrow>\<M>" unfolding Pi_def function_def using apply_type[OF assms(2)] by auto
  {
    fix r assume "r\<in>{0}\<times>D"
    then obtain rd where rd:"r=\<langle>0,rd\<rangle>" "rd\<in>D" by auto
    then have "(AA O ?g)`r=AA`rd" using comp_fun_apply gfun apply_equality by auto
    also have "\<dots>={\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}`\<langle>0,rd\<rangle>" using apply_equality[OF _ A0] sub rd(2) by auto
    also have "\<dots>=restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D)`\<langle>0,rd\<rangle>" using restrict rd(2) by auto
    ultimately have "(AA O ?g)`r=restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D)`r" using rd(1) by auto
  }
  then have "\<forall>r\<in>{0}\<times>D. (AA O ?g)`r=restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D)`r" by auto moreover
  have "AA O ?g:{0}\<times>D\<rightarrow>R" using gfunX assms(1) comp_fun by auto moreover
  have "{0}\<times>D\<subseteq>{0}\<times>X" using sub by auto
  then have "restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D):{0}\<times>D\<rightarrow>R" using A0 restrict_fun by auto ultimately
  have f1:"(AA O ?g)=restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D)" using func_eq[of "AA O ?g" "{0}\<times>D" R "restrict({\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X}, {0} \<times> D)"]
    by auto
  {
    fix r assume "r\<in>{0}\<times>D"
    then obtain rd where rd:"r=\<langle>0,rd\<rangle>" "rd\<in>D" by auto
    then have "(B O ?g)`r=B`rd" using comp_fun_apply gfun apply_equality by auto
    also have "\<dots>={\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}`\<langle>0,rd\<rangle>" using apply_equality[OF _ B0] sub rd(2) by auto
    also have "\<dots>=restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)`\<langle>0,rd\<rangle>" using restrict rd(2) by auto
    ultimately have "(B O ?g)`r=restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)`r" using rd(1) by auto
  }
  then have "\<forall>r\<in>{0}\<times>D. (B O ?g)`r=restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)`r" by auto moreover
  have "B O ?g:{0}\<times>D\<rightarrow>\<M>" using gfunX assms(2) comp_fun by auto moreover
  have "{0}\<times>D\<subseteq>{0}\<times>X" using sub by auto
  then have "restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D):{0}\<times>D\<rightarrow>\<M>" using B0 restrict_fun by auto ultimately
  have "(B O ?g)=restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)" using func_eq[of "B O ?g" "{0}\<times>D" \<M> "restrict({\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X}, {0} \<times> D)"]
    by auto
  with A1 f1 show "(\<Sum>[D;{AA,B}])=\<Sum>[{0}\<times>D;{restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D),restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)}]" by auto
  also have "\<dots>=\<Sum>[{0}\<times>D;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}}]" using linComb_restrict_coord[OF A0 B0 fin] by auto
  ultimately show "(\<Sum>[D;{AA,B}])=\<Sum>[{0}\<times>D;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}}]" by auto
qed

text\<open>Then, we can model adding a liner combination on the empty set
as a linear combination of the disjoint union of sets\<close>

lemma(in module0) linComb_sum_base_induct:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>\<M>" "D\<in>FinPow(X)" "AA1:Y\<rightarrow>R" "B1:Y\<rightarrow>\<M>"
  shows "(\<Sum>[D;{AA,B}])+\<^sub>V(\<Sum>[0;{AA1,B1}])=\<Sum>[D+0;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]"
proof-
  from assms(3) have sub:"D\<subseteq>X" unfolding FinPow_def by auto
  then have sub2:"{0}\<times>D\<subseteq>{0}\<times>X" by auto
  then have sub3:"{0}\<times>D\<in>Pow(X+Y)" unfolding sum_def by auto
  let ?g="{\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>D}"
  have gfun:"?g:{0}\<times>D\<rightarrow>D" unfolding Pi_def function_def by blast
  then have "?g\<in>surj({0}\<times>D,D)" unfolding surj_def using apply_equality by auto moreover
  {
    fix w y assume "?g`w=?g`y" "w\<in>{0}\<times>D" "y\<in>{0}\<times>D"
    then obtain dw dy where "w=\<langle>0,dw\<rangle>" "y=\<langle>0,dy\<rangle>" "?g`w=?g`y" "dw\<in>D" "dy\<in>D" by auto
    then have "dw=dy" "w=\<langle>0,dw\<rangle>" "y=\<langle>0,dy\<rangle>" using apply_equality[OF _ gfun, of w dw] apply_equality[OF _ gfun, of y dy] by auto
    then have "w=y" by auto
  }
  then have "?g\<in>inj({0}\<times>D,D)" unfolding inj_def using gfun by auto ultimately
  have gbij:"?g\<in>bij({0}\<times>D,D)" unfolding bij_def by auto
  then have "Finite({0}\<times>D)" using assms(3) eqpoll_imp_Finite_iff unfolding FinPow_def eqpoll_def by auto
  with sub3 have finpow0D:"{0}\<times>D\<in>FinPow(X+Y)" unfolding FinPow_def by auto
  have A0:"{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}:{0}\<times>X\<rightarrow>R" unfolding Pi_def function_def using apply_type[OF assms(1)] by auto
  have A1:"{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}:{1}\<times>Y\<rightarrow>R" unfolding Pi_def function_def using apply_type[OF assms(4)] by auto
  have domA0:"domain({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X})={0}\<times>X" by auto
  have domA1:"domain({\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})={1}\<times>Y" by auto
  have A:"{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}:X+Y\<rightarrow>R" using fun_disjoint_Un[OF A0 A1] unfolding sum_def by auto
  have B0:"{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}:{0}\<times>X\<rightarrow>\<M>" unfolding Pi_def function_def using apply_type[OF assms(2)] by auto
  have B1:"{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}:{1}\<times>Y\<rightarrow>\<M>" unfolding Pi_def function_def using apply_type[OF assms(5)] by auto
  then have domB0:"domain({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X})={0}\<times>X" unfolding Pi_def by auto
  then have domB1:"domain({\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})={1}\<times>Y" unfolding Pi_def by auto
  have B:"{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}:X+Y\<rightarrow>\<M>" using fun_disjoint_Un[OF B0 B1] unfolding sum_def by auto
  have "(\<Sum>[D;{AA,B}])+\<^sub>V(\<Sum>[0;{AA1,B1}])=\<Sum>[D;{AA,B}]" using linComb_sum_base_induct1 assms by auto
  also have "\<dots>=\<Sum>[{0}\<times>D;{restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D),restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)}]" using linComb_sum_base_induct2(2) assms(1-3) by auto
  ultimately have eq1:"(\<Sum>[D;{AA,B}])+\<^sub>V(\<Sum>[0;{AA1,B1}])=\<Sum>[{0}\<times>D;{restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D),restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)}]" by auto
  {
    fix s assume "s\<in>{0}\<times>D"
    then obtain ds where ds:"ds\<in>D" "s=\<langle>0,ds\<rangle>" by auto
    then have "restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D)`s={\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}`s" using restrict by auto
    also have "\<dots>=({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s" using fun_disjoint_apply1 domA1 ds(2) by auto
    also have "\<dots>=restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{0}\<times>D)`s" using restrict ds by auto
    ultimately have "restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D)`s=restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{0}\<times>D)`s" by auto
  }
  then have tot:"\<forall>s\<in>{0}\<times>D. restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D)`s=restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{0}\<times>D)`s" by auto moreover
  have f1:"restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D):{0}\<times>D\<rightarrow>R" using restrict_fun A0 sub2 by auto moreover
  have f2:"restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{0}\<times>D):{0}\<times>D\<rightarrow>R" using restrict_fun[OF fun_disjoint_Un[OF A0 A1]] sub2 by auto
  ultimately have fA:"restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X},{0}\<times>D)=restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{0}\<times>D)" using func_eq[OF f1 f2] by auto
  {
    fix s assume "s\<in>{0}\<times>D"
    then obtain ds where ds:"ds\<in>D" "s=\<langle>0,ds\<rangle>" by auto
    then have "restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)`s={\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}`s" using restrict by auto
    also have "\<dots>=({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s" using fun_disjoint_apply1 domB1 ds(2) by auto
    also have "\<dots>=restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y},{0}\<times>D)`s" using restrict ds by auto
    ultimately have "restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)`s=restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y},{0}\<times>D)`s" by auto
  }
  then have tot:"\<forall>s\<in>{0}\<times>D. restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)`s=restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y},{0}\<times>D)`s" by auto moreover
  have f1:"restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D):{0}\<times>D\<rightarrow>\<M>" using restrict_fun B0 sub2 by auto moreover
  have f2:"restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y},{0}\<times>D):{0}\<times>D\<rightarrow>\<M>" using restrict_fun[OF fun_disjoint_Un[OF B0 B1]] sub2 by auto
  ultimately have fB:"restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X},{0}\<times>D)=restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y},{0}\<times>D)" using func_eq[OF f1 f2] by auto
  with fA eq1 have "(\<Sum>[D;{AA,B}])+\<^sub>V(\<Sum>[0;{AA1,B1}])=\<Sum>[{0}\<times>D;{restrict({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{0}\<times>D),restrict({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y},{0}\<times>D)}]"
    by auto
  also have "\<dots>=\<Sum>[{0}\<times>D;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]" using linComb_restrict_coord[OF A B finpow0D]
    by auto
  also have "\<dots>=\<Sum>[D+0;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]" unfolding sum_def by auto
  ultimately show ?thesis by auto
qed

text\<open>An element of the set for the linear combination
can be removed and add it using group addition.\<close>

lemma(in module0) sum_one_element:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>\<M>" "D\<in>FinPow(X)" "t\<in>D"
  shows "(\<Sum>[D;{AA,B}])=(\<Sum>[D-{t};{AA,B}])+\<^sub>V({\<langle>k,(AA`k)\<cdot>\<^sub>S(B`k)\<rangle>. k\<in>X}`t)"
proof-
  from assms(1,2) have af:"{\<langle>k,(AA`k)\<cdot>\<^sub>S(B`k)\<rangle>. k\<in>X}:X\<rightarrow>\<M>" using coordinate_function by auto  
  from assms(3) have sub:"D\<subseteq>X" unfolding FinPow_def by auto
  then have tX:"t\<in>X" using assms(4) by auto
  have dom:"domain(AA)=X" using assms(1) Pi_def by auto
  {
    assume A:"D-{t}=0"
    with assms(4) have "D={t}" by auto
    then have "(\<Sum>[D;{AA,B}])=\<Sum>[{t};{AA,B}]" by auto
    also have "\<dots>=(AA`t)\<cdot>\<^sub>S(B`t)" using linComb_one_element sub assms(1,2,4) by auto
    also have "\<dots>={\<langle>k,(AA`k)\<cdot>\<^sub>S(B`k)\<rangle>. k\<in>X}`t" using af assms(4) sub apply_equality by auto
    also have "\<dots>=\<Theta> +\<^sub>V({\<langle>k,(AA`k)\<cdot>\<^sub>S(B`k)\<rangle>. k\<in>X}`t)" using zero_neutral(2)
      apply_type[OF af] assms(4) sub by auto
    also have "\<dots>=(\<Sum>[D-{t};{AA,B}])+\<^sub>V({\<langle>k,(AA`k)\<cdot>\<^sub>S(B`k)\<rangle>. k\<in>X}`t)" using A LinearComb_def[OF assms(1,2), of "D-{t}"]
      unfolding FinPow_def by auto
    ultimately have ?thesis by auto
  }
  moreover
  {
    assume A:"D-{t}\<noteq>0"
    then have D:"D\<noteq>0" by auto
    have comm:"commsemigr(\<M>, A\<^sub>M, X, {\<langle>k,(AA`k)\<cdot>\<^sub>S(B`k)\<rangle>. k\<in>X})"
      unfolding commsemigr_def using mod_ab_gr.abelian_group_axioms
      unfolding abelian_group_def abelian_group_axioms_def group0_def
      IsAgroup_def IsAmonoid_def using af by auto
    have fin:"D-{t}\<in>FinPow(X)" using assms(3) unfolding FinPow_def using subset_Finite[of "D-{t}" D] by auto
    have "(D-{t})\<union>{t}=D" "X-(D-{t})=(X-D)\<union>{t}" using assms(4) sub by auto
    then have "CommSetFold(A\<^sub>M,{\<langle>k,(AA`k)\<cdot>\<^sub>S(B`k)\<rangle>. k\<in>X},D)=CommSetFold(A\<^sub>M,{\<langle>k,(AA`k)\<cdot>\<^sub>S(B`k)\<rangle>. k\<in>X},D-{t})
      +\<^sub>V({\<langle>k,(AA`k)\<cdot>\<^sub>S(B`k)\<rangle>. k\<in>X}`t)" using commsemigr.sum_over_set_add_point(2)[OF comm
      fin A] by auto
    also have "\<dots>=(\<Sum>[D-{t};{AA,B}])+\<^sub>V({\<langle>k,(AA`k)\<cdot>\<^sub>S(B`k)\<rangle>. k\<in>X}`t)" using LinearComb_def[OF assms(1,2) fin] A
      dom by auto
    ultimately have "CommSetFold(A\<^sub>M,{\<langle>k,(AA`k)\<cdot>\<^sub>S(B`k)\<rangle>. k\<in>X},D)=(\<Sum>[D-{t};{AA,B}])+\<^sub>V({\<langle>k,(AA`k)\<cdot>\<^sub>S(B`k)\<rangle>. k\<in>X}`t)" by auto moreover
    then have ?thesis unfolding LinearComb_def[OF assms(1-3)] using D dom by auto
  }
  ultimately show ?thesis by blast
qed

text \<open>A small technical lemma to proof by induction on finite sets that the addition of linear combinations
is a linear combination\<close>

lemma(in module0) linComb_sum_ind_step:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>\<M>" "D\<in>FinPow(X)" "E\<in>FinPow(Y)" "AA1:Y\<rightarrow>R" "B1:Y\<rightarrow>\<M>" "t\<in>E" "D\<noteq>0"
    "(\<Sum>[D;{AA,B}])+\<^sub>V(\<Sum>[E-{t};{AA1,B1}])=\<Sum>[D+(E-{t});{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]"
  shows "(\<Sum>[D;{AA,B}])+\<^sub>V(\<Sum>[E;{AA1,B1}])=\<Sum>[D+E;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]"
proof-
  have a1f:"{\<langle>k,(AA1`k)\<cdot>\<^sub>S(B1`k)\<rangle>. k\<in>Y}:Y\<rightarrow>\<M>" using coordinate_function assms(5,6) by auto
  with assms(4,7) have p1:"({\<langle>k,(AA1`k)\<cdot>\<^sub>S(B1`k)\<rangle>. k\<in>Y}`t)\<in>\<M>" unfolding FinPow_def using apply_type by auto
  have p2:"\<Sum>[D;{AA,B}]\<in>\<M>" using linComb_is_in_module assms(1-3) by auto
  have "E-{t}\<in>FinPow(Y)" using assms(4,7) unfolding FinPow_def using subset_Finite[of "E-{t}" E] by auto
  then have p3:"\<Sum>[E-{t};{AA1,B1}]\<in>\<M>" using linComb_is_in_module assms(5,6) by auto
  have "\<Sum>[E;{AA1,B1}]=(\<Sum>[E-{t};{AA1,B1}])+\<^sub>V({\<langle>k,(AA1`k)\<cdot>\<^sub>S(B1`k)\<rangle>. k\<in>Y}`t)" using sum_one_element[OF assms(5,6,4,7)].
  then have "(\<Sum>[D;{AA,B}])+\<^sub>V(\<Sum>[E;{AA1,B1}])=(\<Sum>[D;{AA,B}])+\<^sub>V((\<Sum>[E-{t};{AA1,B1}])+\<^sub>V({\<langle>k,(AA1`k)\<cdot>\<^sub>S(B1`k)\<rangle>. k\<in>Y}`t))" by auto
  also have "\<dots>=((\<Sum>[D;{AA,B}])+\<^sub>V(\<Sum>[E-{t};{AA1,B1}]))+\<^sub>V({\<langle>k,(AA1`k)\<cdot>\<^sub>S(B1`k)\<rangle>. k\<in>Y}`t)"
    using p1 p2 p3 mod_ab_gr.group_oper_assoc by auto
  also have "\<dots>=(\<Sum>[D+(E-{t});{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}])+\<^sub>V({\<langle>k,(AA1`k)\<cdot>\<^sub>S(B1`k)\<rangle>. k\<in>Y}`t)"
    using assms(9) by auto
  ultimately have "(\<Sum>[D;{AA,B}])+\<^sub>V(\<Sum>[E;{AA1,B1}])=(\<Sum>[D+(E-{t});{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}])+\<^sub>V({\<langle>k,(AA1`k)\<cdot>\<^sub>S(B1`k)\<rangle>. k\<in>Y}`t)" by auto
  moreover have "{\<langle>k,(AA1`k)\<cdot>\<^sub>S(B1`k)\<rangle>. k\<in>Y}`t=(AA1`t)\<cdot>\<^sub>S(B1`t)" using apply_equality[OF _ a1f] assms(7,4) unfolding FinPow_def by auto moreover
  {
    have dA:"domain({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X})={\<langle>0,x\<rangle>. x\<in>X}" unfolding domain_def by auto
    have dA1:"domain({\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})={\<langle>1,x\<rangle>. x\<in>Y}" unfolding domain_def by auto
    have "\<langle>1,t\<rangle>\<notin>domain({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X})" by auto
    then have "({\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}\<union>{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X})`\<langle>1,t\<rangle>={\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}`\<langle>1,t\<rangle>" using fun_disjoint_apply1[of "\<langle>1,t\<rangle>" "{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}"] by auto
    moreover have "{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}\<union>{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}={\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}" by auto
    ultimately have "({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>={\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}`\<langle>1,t\<rangle>" by auto moreover
    have "{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}:{1}\<times>Y\<rightarrow>R" unfolding Pi_def function_def using apply_type[OF assms(5)] by auto
    then have "{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}`\<langle>1,t\<rangle>=(AA1`t)" using apply_equality assms(7,4) unfolding FinPow_def by auto
    ultimately have e1:"({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>=(AA1`t)" by auto
    have dB:"domain({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X})={\<langle>0,x\<rangle>. x\<in>X}" unfolding domain_def by auto
    have dB1:"domain({\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})={\<langle>1,x\<rangle>. x\<in>Y}" unfolding domain_def by auto
    have "\<langle>1,t\<rangle>\<notin>domain({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X})" by auto
    then have "({\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}\<union>{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X})`\<langle>1,t\<rangle>={\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}`\<langle>1,t\<rangle>" using fun_disjoint_apply1[of "\<langle>1,t\<rangle>" "{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}"] by auto
    moreover have "{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}\<union>{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}={\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}" by auto
    ultimately have "({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>={\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}`\<langle>1,t\<rangle>" by auto moreover
    have "{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}:{1}\<times>Y\<rightarrow>\<M>" unfolding Pi_def function_def using apply_type[OF assms(6)] by auto
    then have "{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}`\<langle>1,t\<rangle>=(B1`t)" using apply_equality assms(7,4) unfolding FinPow_def by auto
    ultimately have e2:"({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>=(B1`t)" by auto
    with e1 have "(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>)=(AA1`t)\<cdot>\<^sub>S(B1`t)" by auto
    moreover have tXY:"\<langle>1,t\<rangle>\<in>X+Y" unfolding sum_def using assms(7,4) unfolding FinPow_def by auto
    {
      fix s w assume as:"\<langle>s,w\<rangle>\<in>{\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}"
      then have s:"s\<in>X+Y" and w:"w=(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)" by auto
      then have ss:"s\<in>{0}\<times>X \<union> {1}\<times>Y" unfolding sum_def by auto
      {
        assume "s\<in>{0}\<times>X"
        then obtain r where r:"r\<in>X" "s=\<langle>0,r\<rangle>" by auto
        with s have a:"\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>0,r\<rangle>)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>0,r\<rangle>)\<rangle>\<in>
          {\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}" by auto
        have "({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>0,r\<rangle>={\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}`\<langle>0,r\<rangle>" using fun_disjoint_apply1[of "\<langle>0,r\<rangle>"
          "{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}"] by auto
        also have "\<dots>=AA`r" using r(1) apply_equality[of "\<langle>0,r\<rangle>" "AA`r" "{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}" "{0}\<times>X" "\<lambda>p. R"] unfolding Pi_def function_def
          using apply_type[OF assms(1)] by auto
        ultimately have AAr:"({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>0,r\<rangle>=AA`r" by auto
        with a have a1:"\<langle>s,(AA`r)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>0,r\<rangle>)\<rangle>\<in>
          {\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}" by auto
        have "({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>0,r\<rangle>={\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}`\<langle>0,r\<rangle>" using fun_disjoint_apply1[of "\<langle>0,r\<rangle>"
          "{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}"] by auto
        also have "\<dots>=B`r" using r(1) apply_equality[of "\<langle>0,r\<rangle>" "B`r" "{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}" "{0}\<times>X" "\<lambda>p. \<M>"] unfolding Pi_def function_def
          using apply_type[OF assms(2)] by auto
        ultimately have Br:"({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>0,r\<rangle>=B`r" by auto
        with a1 have "\<langle>s,(AA`r)\<cdot>\<^sub>S(B`r)\<rangle>\<in>
          {\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}" by auto moreover
        have "(AA`r)\<cdot>\<^sub>S(B`r)\<in>\<M>" using apply_type[OF coordinate_function[OF assms(1,2)] r(1)] apply_equality[OF _ coordinate_function[OF assms(1,2)]] r(1) by auto
        ultimately have "\<langle>s,(AA`r)\<cdot>\<^sub>S(B`r)\<rangle>\<in>(X+Y)\<times>\<M>" using s by auto moreover
        from w r(2) AAr Br have "w=(AA`r)\<cdot>\<^sub>S(B`r)" by auto
        ultimately have "\<langle>s,w\<rangle>\<in>(X+Y)\<times>\<M>" by auto
      }
      moreover
      {
        assume "s\<notin>{0}\<times>X"
        with ss have "s\<in>{1}\<times>Y" by auto
        then obtain r where r:"r\<in>Y" "s=\<langle>1,r\<rangle>" by auto
        with s have a:"\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>1,r\<rangle>)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,r\<rangle>)\<rangle>\<in>
          {\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}" by auto
        have "({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>1,r\<rangle>={\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}`\<langle>1,r\<rangle>" using fun_disjoint_apply2[of "\<langle>1,r\<rangle>"
          "{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}"] by auto
        also have "\<dots>=AA1`r" using r(1) apply_equality[of "\<langle>1,r\<rangle>" "AA1`r" "{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y}" "{1}\<times>Y" "\<lambda>p. R"] unfolding Pi_def function_def
          using apply_type[OF assms(5)] by auto
        ultimately have AAr:"({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>1,r\<rangle>=AA1`r" by auto
        with a have a1:"\<langle>s,(AA1`r)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,r\<rangle>)\<rangle>\<in>
          {\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}" by auto
        have "({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,r\<rangle>={\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}`\<langle>1,r\<rangle>" using fun_disjoint_apply2[of "\<langle>1,r\<rangle>"
          "{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}"] by auto
        also have "\<dots>=B1`r" using r(1) apply_equality[of "\<langle>1,r\<rangle>" "B1`r" "{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}" "{1}\<times>Y" "\<lambda>p. \<M>"] unfolding Pi_def function_def
          using apply_type[OF assms(6)] by auto
        ultimately have Br:"({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,r\<rangle>=B1`r" by auto
        with a1 have "\<langle>s,(AA1`r)\<cdot>\<^sub>S(B1`r)\<rangle>\<in>
          {\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}" by auto moreover
        have "(AA1`r)\<cdot>\<^sub>S(B1`r)\<in>\<M>" using apply_type[OF coordinate_function[OF assms(5,6)] r(1)] apply_equality[OF _ coordinate_function[OF assms(5,6)]] r(1) by auto
        ultimately have "\<langle>s,(AA1`r)\<cdot>\<^sub>S(B1`r)\<rangle>\<in>(X+Y)\<times>\<M>" using s by auto moreover
        from w r(2) AAr Br have "w=(AA1`r)\<cdot>\<^sub>S(B1`r)" by auto
        ultimately have "\<langle>s,w\<rangle>\<in>(X+Y)\<times>\<M>" by auto
      }
      ultimately have "\<langle>s,w\<rangle>\<in>(X+Y)\<times>\<M>" by auto
    }
    then have "{\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}\<subseteq>(X+Y)\<times>\<M>" by auto
    then have fun:"{\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}:X+Y\<rightarrow>\<M>"
      unfolding Pi_def function_def by auto
    from tXY have pp:"\<langle>\<langle>1,t\<rangle>,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>)\<rangle>\<in>
      {\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}" by auto
    have "{\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}`\<langle>1,t\<rangle>=
      (({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`\<langle>1,t\<rangle>)" using apply_equality[OF pp fun] by auto
    ultimately have "{\<langle>s,(({\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y})`s)\<cdot>\<^sub>S(({\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y})`s)\<rangle>. s\<in>X+Y}`\<langle>1,t\<rangle>=(AA1`t)\<cdot>\<^sub>S(B1`t)"
      by auto
  }
  ultimately have "(\<Sum>[D;{AA,B}]) +\<^sub>V (\<Sum>[E;{AA1,B1}]) =
    (\<Sum>[D+(E-{t});{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]) +\<^sub>V
    (({\<langle>s, ((({\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y}) ` s) \<cdot>\<^sub>S (({\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}) ` s))\<rangle> .
     s \<in> X + Y}) ` \<langle>1, t\<rangle>)" by auto moreover
  have "D+(E-{t})=(D+E)-{\<langle>1,t\<rangle>}" unfolding sum_def by auto ultimately
  have A1:"(\<Sum>[D;{AA,B}]) +\<^sub>V (\<Sum>[E;{AA1,B1}]) =
    (\<Sum>[(D+E)-{\<langle>1,t\<rangle>};{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]) +\<^sub>V
    (({\<langle>s, ((({\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y}) ` s) \<cdot>\<^sub>S (({\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}) ` s))\<rangle> .
     s \<in> X + Y}) ` \<langle>1, t\<rangle>)" by auto
  have f1:"{\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X}:{0}\<times>X\<rightarrow>R" using apply_type[OF assms(1)] unfolding Pi_def function_def by auto
  have f2:"{\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y}:{1}\<times>Y\<rightarrow>R" using apply_type[OF assms(5)] unfolding Pi_def function_def by auto
  have "({0}\<times>X)\<inter>({1}\<times>Y)=0" by auto
  then have ffA:"({\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y}):X+Y\<rightarrow>R" unfolding sum_def using fun_disjoint_Un[OF f1 f2] by auto 
  have f1:"{\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X}:{0}\<times>X\<rightarrow>\<M>" using apply_type[OF assms(2)] unfolding Pi_def function_def by auto
  have f2:"{\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}:{1}\<times>Y\<rightarrow>\<M>" using apply_type[OF assms(6)] unfolding Pi_def function_def by auto
  have "({0}\<times>X)\<inter>({1}\<times>Y)=0" by auto
  then have ffB:"({\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}):X+Y\<rightarrow>\<M>" unfolding sum_def using fun_disjoint_Un[OF f1 f2] by auto
  have "D+E\<subseteq>X+Y" using assms(3,4) unfolding FinPow_def sum_def by auto moreover
  obtain nd ne where "nd\<in>nat" "D\<approx>nd" "ne\<in>nat" "E\<approx>ne" using assms(3,4) unfolding FinPow_def Finite_def by auto
  then have "D+E\<approx>nd+ne" "nd\<in>nat" "ne\<in>nat" using sum_eqpoll_cong by auto
  then have "D+E\<approx>nd #+ ne" using nat_sum_eqpoll_sum eqpoll_trans by auto
  then have "\<exists>n\<in>nat. D+E\<approx>n" using add_type by auto
  then have "Finite(D+E)" unfolding Finite_def by auto
  ultimately have fin:"D+E\<in>FinPow(X+Y)" unfolding FinPow_def by auto
  from assms(7) have "\<langle>1,t\<rangle>\<in>D+E" unfolding sum_def by auto
  with A1 show ?thesis using sum_one_element[OF ffA ffB fin] by auto
qed

text\<open>The addition of two linear combinations is a linear combination\<close>

theorem(in module0) linComb_sum:
  assumes "AA:X\<rightarrow>R" "AA1:Y\<rightarrow>R" "B:X\<rightarrow>\<M>" "B1:Y\<rightarrow>\<M>" "D\<noteq>0" "D\<in>FinPow(X)" "E\<in>FinPow(Y)"
  shows "(\<Sum>[D;{AA,B}])+\<^sub>V(\<Sum>[E;{AA1,B1}])=\<Sum>[D+E;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]"
proof-
  {
    fix \<AA> \<BB> \<AA>1 \<BB>1 assume fun:"\<AA>:X\<rightarrow>R" "\<BB>:X\<rightarrow>\<M>" "\<AA>1:Y\<rightarrow>R" "\<BB>1:Y\<rightarrow>\<M>"
    have "((\<Sum>[D;{\<AA>,\<BB>}]) +\<^sub>V(\<Sum>[0;{\<AA>1,\<BB>1}])=\<Sum>[D+0;{{\<langle>\<langle>0,x\<rangle>,\<AA>`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,\<AA>1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,\<BB>`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,\<BB>1`x\<rangle>. x\<in>Y}}])" using linComb_sum_base_induct[OF fun(1,2) assms(6) fun(3,4)]
      by auto
  }
  then have base:"\<forall>AA\<in>X \<rightarrow> R.
       \<forall>B\<in>X \<rightarrow> \<M>.
          \<forall>AA1\<in>Y \<rightarrow> R.
             \<forall>B1\<in>Y \<rightarrow> \<M>.
                (\<Sum>[D;{AA,B}]) +\<^sub>V (\<Sum>[0;{AA1,B1}]) =
                \<Sum>[D + 0;{{\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y},{\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}}]" by auto
  {
    fix \<RR> assume R:"\<RR>\<in>FinPow(Y)" "\<RR>\<noteq>0"
    then obtain r where r:"r\<in>\<RR>" by auto
    {
      fix \<AA> \<BB> \<AA>1 \<BB>1 assume fun:"\<AA>:X\<rightarrow>R" "\<BB>:X\<rightarrow>\<M>" "\<AA>1:Y\<rightarrow>R" "\<BB>1:Y\<rightarrow>\<M>" and 
        step:"\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>\<M>. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>\<M>. (\<Sum>[D;{AA,B}]) +\<^sub>V (\<Sum>[\<RR> - {r};{AA1,B1}])=(\<Sum>[D+(\<RR> - {r});{{\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y},{\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}}])"
      then have "(\<Sum>[D;{\<AA>,\<BB>}]) +\<^sub>V (\<Sum>[\<RR>;{\<AA>1,\<BB>1}])=(\<Sum>[D+\<RR>;{{\<langle>\<langle>0, x\<rangle>, \<AA> ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, \<AA>1 ` x\<rangle> . x \<in> Y},{\<langle>\<langle>0, x\<rangle>, \<BB> ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, \<BB>1 ` x\<rangle> . x \<in> Y}}])" using linComb_sum_ind_step[OF fun(1,2) assms(6) R(1) fun(3,4) r assms(5)]
        by auto
    }
    then have "(\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>\<M>. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>\<M>. (\<Sum>[D;{AA,B}]) +\<^sub>V (\<Sum>[\<RR> - {r};{AA1,B1}])=(\<Sum>[D+(\<RR> - {r});{{\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y},{\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}}])) \<longrightarrow> 
      (\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>\<M>. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>\<M>. ((\<Sum>[D;{AA,B}]) +\<^sub>V(\<Sum>[\<RR>;{AA1,B1}])=\<Sum>[D+\<RR>;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]))" by auto
    then have "\<exists>r\<in>\<RR>. (\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>\<M>. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>\<M>. (\<Sum>[D;{AA,B}]) +\<^sub>V (\<Sum>[\<RR> - {r};{AA1,B1}])=(\<Sum>[D+(\<RR> - {r});{{\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y},{\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}}])) \<longrightarrow> 
      (\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>\<M>. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>\<M>. ((\<Sum>[D;{AA,B}]) +\<^sub>V(\<Sum>[\<RR>;{AA1,B1}])=\<Sum>[D+\<RR>;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]))" using r by auto
  }
  then have indstep:"\<forall>\<RR>\<in>FinPow(Y). \<RR>\<noteq>0 \<longrightarrow> (\<exists>r\<in>\<RR>. (\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>\<M>. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>\<M>. (\<Sum>[D;{AA,B}]) +\<^sub>V (\<Sum>[\<RR> - {r};{AA1,B1}])=(\<Sum>[D+(\<RR> - {r});{{\<langle>\<langle>0, x\<rangle>, AA ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, AA1 ` x\<rangle> . x \<in> Y},{\<langle>\<langle>0, x\<rangle>, B ` x\<rangle> . x \<in> X} \<union> {\<langle>\<langle>1, x\<rangle>, B1 ` x\<rangle> . x \<in> Y}}])) \<longrightarrow> 
    (\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>\<M>. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>\<M>. ((\<Sum>[D;{AA,B}]) +\<^sub>V(\<Sum>[\<RR>;{AA1,B1}])=\<Sum>[D+\<RR>;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}])))" by auto
  have "\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>\<M>. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>\<M>. ((\<Sum>[D;{AA,B}]) +\<^sub>V(\<Sum>[E;{AA1,B1}])=\<Sum>[D+E;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}])" 
    using FinPow_ind_rem_one[where P="\<lambda>E. (\<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>X\<rightarrow>\<M>. \<forall>AA1\<in>Y\<rightarrow>R. \<forall>B1\<in>Y\<rightarrow>\<M>. ((\<Sum>[D;{AA,B}]) +\<^sub>V(\<Sum>[E;{AA1,B1}])=\<Sum>[D+E;{{\<langle>\<langle>0,x\<rangle>,AA`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,AA1`x\<rangle>. x\<in>Y},{\<langle>\<langle>0,x\<rangle>,B`x\<rangle>. x\<in>X}\<union>{\<langle>\<langle>1,x\<rangle>,B1`x\<rangle>. x\<in>Y}}]))",
    OF base indstep assms(7)].
  with assms(1-4) show ?thesis by auto
qed

subsubsection\<open>Linear dependency\<close>

text \<open>Now, we have the conditions to define what linear independence means:\<close>

definition(in module0)
  LinInde ("_{is linearly independent}" 89)
  where "\<T>\<subseteq>\<M> \<Longrightarrow> \<T>{is linearly independent} \<equiv> (\<forall>X\<in>nat. \<forall>AA\<in>X\<rightarrow>R. \<forall>B\<in>inj(X,\<T>). ((\<Sum>[X;{AA,B}] = \<Theta> ) ) \<longrightarrow> (\<forall>m\<in>X. AA`m=\<zero>))"

text\<open>If a set has the zero element, then it is not linearly independent.\<close>

theorem(in module0) zero_set_dependent:
  assumes "\<Theta>\<in>T" "T\<subseteq>\<M>" "R\<noteq>{\<zero>}"
  shows "\<not>(T{is linearly independent})"
proof
  assume "T{is linearly independent}"
  then have reg:"\<forall>n\<in>nat. \<forall>AA\<in>n\<rightarrow>R. \<forall>B\<in>inj(n,T).(\<Sum>[n;{AA,B}] =\<Theta> ) \<longrightarrow> (\<forall>m\<in>n. AA`m=\<zero>)"
    unfolding LinInde_def[OF assms(2)] by auto
  from assms(3) obtain r where r:"r\<in>R" "r\<noteq>\<zero>" using Ring_ZF_1_L2(1) by auto
  let ?A="{\<langle>0,r\<rangle>}"
  let ?B="{\<langle>0,\<Theta>\<rangle>}"
  have A:"?A:succ(0)\<rightarrow>R" using `r\<in>R` unfolding Pi_def function_def domain_def by auto
  have B:"?B:succ(0)\<rightarrow>T" using assms(1) unfolding Pi_def function_def domain_def by auto
  with assms(2) have B2:"?B:succ(0)\<rightarrow>\<M>" unfolding Pi_def by auto
  have C:"succ(0)\<in>nat" by auto
  have fff:"{\<langle>m, (?A ` m) \<cdot>\<^sub>S (?B ` m)\<rangle> . m \<in> 1}:1\<rightarrow>\<M>" using coordinate_function[OF A B2] by auto
  have "?B\<in>inj(succ(0),T)" unfolding inj_def using apply_equality B by auto
  with A C reg have "\<Sum>[succ(0);{?A,?B}] =\<Theta> \<longrightarrow> (\<forall>m\<in>succ(0). ?A`m=\<zero>)" by blast
  then have "\<Sum>[succ(0);{?A,?B}] =\<Theta> \<longrightarrow> (?A`0=\<zero>)" by blast
  then have "\<Sum>[succ(0);{?A,?B}] =\<Theta> \<longrightarrow> (r=\<zero>)" using apply_equality[OF _ A,of 0 r] by auto
  with r(2) have "\<Sum>[succ(0);{?A,?B}] \<noteq>\<Theta>" by auto
  moreover have "\<Sum>[succ(0);{?A,?B}]=(?A`0) \<cdot>\<^sub>S (?B ` 0)" using linComb_one_element[OF _ A B2] unfolding succ_def by auto
  also have "\<dots>=r\<cdot>\<^sub>S\<Theta>" using apply_equality A B by auto
  also have "\<dots>=\<Theta>" using zero_fixed r(1) by auto
  ultimately show False by auto
qed

subsection\<open>Submodule\<close>

text\<open>A submodule is a subgroup that is invariant by the action\<close>

definition(in module0)
  IsAsubmodule
  where "IsAsubmodule(\<N>) \<equiv> (\<forall>r\<in>R. \<forall>h\<in>\<N>. r\<cdot>\<^sub>S h\<in>\<N>) \<and> IsAsubgroup(\<N>,A\<^sub>M)"

lemma(in module0) sumodule_is_subgroup:
  assumes "IsAsubmodule(\<N>)"
  shows "IsAsubgroup(\<N>,A\<^sub>M)"
  using assms unfolding IsAsubmodule_def by auto

lemma(in module0) sumodule_is_subaction:
  assumes "IsAsubmodule(\<N>)" "r\<in>R" "h\<in>\<N>"
  shows "r\<cdot>\<^sub>S h\<in>\<N>"
  using assms unfolding IsAsubmodule_def by auto

text\<open>For groups, we need to prove that the inverse function
is closed in a set to prove that set to be a subgroup. In module, that is not necessary.\<close>

lemma(in module0) inverse_in_set:
  assumes "\<forall>r\<in>R. \<forall>h\<in>\<N>. r\<cdot>\<^sub>S h\<in>\<N>" "\<N>\<subseteq>\<M>"
  shows "\<forall>h\<in>\<N>. (\<midarrow>h)\<in>\<N>"
proof
  fix h assume "h\<in>\<N>" moreover
  then have "h\<in>\<M>" using assms(2) by auto
  then have "(\<rm>\<one>)\<cdot>\<^sub>S h=(\<midarrow>h)" using inv_module by auto moreover
  have "(\<rm>\<one>)\<in>R" using Ring_ZF_1_L2(2) Ring_ZF_1_L3(1) by auto ultimately
  show "(\<midarrow>h)\<in>\<N>" using assms(1) by force
qed

corollary(in module0) submoduleI:
  assumes "\<N>\<subseteq>\<M>" "\<N>\<noteq>0" "\<N>{is closed under}A\<^sub>M"  "\<forall>r\<in>R. \<forall>h\<in>\<N>. r\<cdot>\<^sub>S h\<in>\<N>"
  shows "IsAsubmodule(\<N>)" unfolding IsAsubmodule_def
  using inverse_in_set[OF assms(4,1)] assms mod_ab_gr.group0_3_T3
    by auto

text\<open>Every module has at least two submodules: the whole module and the trivial module.\<close>

corollary(in module0) trivial_submodules:
  shows "IsAsubmodule(\<M>)" and "IsAsubmodule({\<Theta>})"
  unfolding IsAsubmodule_def
proof(safe)
  have "A\<^sub>M:\<M>\<times>\<M>\<rightarrow>\<M>" using mod_ab_gr.group_oper_fun by auto
  then have "A\<^sub>M\<subseteq>((\<M>\<times>\<M>)\<times>\<M>)" unfolding Pi_def by auto
  then have "restrict(A\<^sub>M,\<M>\<times>\<M>)=A\<^sub>M" unfolding restrict_def by blast
  then show "IsAsubgroup(\<M>,A\<^sub>M)" using mAbGr unfolding IsAsubgroup_def by auto
next
  fix r h assume A:"r\<in>R" "h\<in>\<M>"
  from A(1) have "H`r:\<M>\<rightarrow>\<M>" using H_val_type(2) by auto
  with A(2) show "r\<cdot>\<^sub>Sh\<in>\<M>" using apply_type[of "H`r" \<M> "\<lambda>t. \<M>"] by auto
next
  fix r assume "r\<in>R"
  with zero_fixed show "r \<cdot>\<^sub>S \<Theta> = \<Theta>" by auto
next
  have "{\<Theta>}\<noteq>0" by auto moreover
  have "{\<Theta>}\<subseteq>\<M>" using mod_ab_gr.group0_2_L2 by auto moreover
  {
    fix x y assume "x\<in>{\<Theta>}" "y\<in>{\<Theta>}"
    then have "A\<^sub>M`\<langle>x,y\<rangle>=\<Theta>" using mod_ab_gr.group0_2_L2 by auto
  }
  then have "{\<Theta>}{is closed under}A\<^sub>M" unfolding IsOpClosed_def by auto moreover
  {
    fix x assume "x\<in>{\<Theta>}"
    then have "GroupInv(\<M>, A\<^sub>M) `(x)= \<Theta>" using mod_ab_gr.group_inv_of_one by auto
  }
  then have "\<forall>x\<in>{\<Theta>}. GroupInv(\<M>, A\<^sub>M) `(x)\<in>{\<Theta>}" by auto ultimately
  show "IsAsubgroup({\<Theta>},A\<^sub>M)" using mod_ab_gr.group0_3_T3 by auto
qed

text\<open>The restriction of the action is an action.\<close>

lemma(in module0) action_submodule:
  assumes "IsAsubmodule(\<N>)"
  shows "{\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R}:R\<rightarrow>End(\<N>,restrict(A\<^sub>M,\<N>\<times>\<N>))"
proof-
  have sub:"\<N>\<subseteq>\<M>" using mod_ab_gr.group0_3_L2[OF sumodule_is_subgroup[OF assms]] by auto
  {
    fix t assume "t\<in>{\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R}"
    then obtain r where t:"r\<in>R" "t=\<langle>r,restrict(H`r,\<N>)\<rangle>" by auto
    then have E:"H`r\<in>End(\<M>,A\<^sub>M)" using H_val_type(1) by auto
    from t(1) have "H`r:\<M>\<rightarrow>\<M>" using H_val_type(2) by auto
    then have "restrict(H`r,\<N>):\<N>\<rightarrow>\<M>" using restrict_fun sub by auto moreover
    have "\<forall>h\<in>\<N>. restrict(H`r,\<N>)`h\<in>\<N>" using restrict sumodule_is_subaction[OF assms `r\<in>R`] by auto
    ultimately have HH:"restrict(H`r,\<N>):\<N>\<rightarrow>\<N>" using func1_1_L1A by auto
    {
      fix g1 g2 assume H:"g1\<in>\<N>""g2\<in>\<N>"
      with sub have G:"g1\<in>\<M>""g2\<in>\<M>" by auto
      from H have AA:"A\<^sub>M`\<langle>g1,g2\<rangle>=restrict(A\<^sub>M,\<N>\<times>\<N>)`\<langle>g1,g2\<rangle>" using restrict by auto
      then have "(H`r)`(A\<^sub>M`\<langle>g1,g2\<rangle>)=(H`r)`(restrict(A\<^sub>M,\<N>\<times>\<N>)`\<langle>g1,g2\<rangle>)" by auto
      then have "A\<^sub>M`\<langle>(H`r)`g1,(H`r)`g2\<rangle>=(H`r)`(restrict(A\<^sub>M,\<N>\<times>\<N>)`\<langle>g1,g2\<rangle>)" using E G
        unfolding End_def Homomor_def IsMorphism_def by auto
      with H have "restrict(A\<^sub>M,\<N>\<times>\<N>)`\<langle>(H`r)`g1,(H`r)`g2\<rangle>=(H`r)`(restrict(A\<^sub>M,\<N>\<times>\<N>)`\<langle>g1,g2\<rangle>)" using sumodule_is_subaction[OF assms `r\<in>R`]
        by auto moreover
      from H have "A\<^sub>M`\<langle>g1,g2\<rangle>\<in>\<N>" using sumodule_is_subgroup[OF assms] mod_ab_gr.group0_3_L6 by auto
      then have "restrict(H`r,\<N>)`(A\<^sub>M`\<langle>g1,g2\<rangle>)=(H`r)`(A\<^sub>M`\<langle>g1,g2\<rangle>)" by auto
      with AA have "restrict(H`r,\<N>)`(restrict(A\<^sub>M,\<N>\<times>\<N>)`\<langle>g1,g2\<rangle>)=(H`r)`(restrict(A\<^sub>M,\<N>\<times>\<N>)`\<langle>g1,g2\<rangle>)" by auto moreover
      from H have "(H`r)`g1=restrict(H`r,\<N>)`g1""(H`r)`g2=restrict(H`r,\<N>)`g2" by auto ultimately
      have "restrict(H`r,\<N>)`(restrict(A\<^sub>M,\<N>\<times>\<N>)`\<langle>g1,g2\<rangle>) = restrict(A\<^sub>M,\<N>\<times>\<N>)`\<langle>restrict(H`r,\<N>)`g1,restrict(H`r,\<N>)`g2\<rangle>" by auto
    }
    then have "\<forall>g1\<in>\<N>. \<forall>g2\<in>\<N>. restrict(H`r,\<N>)`(restrict(A\<^sub>M,\<N>\<times>\<N>)`\<langle>g1,g2\<rangle>) = restrict(A\<^sub>M,\<N>\<times>\<N>)`\<langle>restrict(H`r,\<N>)`g1,restrict(H`r,\<N>)`g2\<rangle>" by auto
    then have "Homomor(restrict(H`r,\<N>),\<N>,restrict(A\<^sub>M,\<N>\<times>\<N>),\<N>,restrict(A\<^sub>M,\<N>\<times>\<N>))" using HH
      unfolding Homomor_def IsMorphism_def by auto
    with HH have "restrict(H`r,\<N>)\<in>End(\<N>,restrict(A\<^sub>M,\<N>\<times>\<N>))" unfolding End_def by auto
    then have "t\<in>R\<times>End(\<N>,restrict(A\<^sub>M,\<N>\<times>\<N>))" using t by auto
  }
  then have "{\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R}\<subseteq>R\<times>End(\<N>,restrict(A\<^sub>M,\<N>\<times>\<N>))" by auto moreover
  {
    fix x y assume "\<langle>x,y\<rangle>\<in>{\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R}"
    then have y:"x\<in>R""y=restrict(H`x,\<N>)" by auto
    {
      fix y' assume "\<langle>x,y'\<rangle>\<in>{\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R}"
      then have "y'=restrict(H`x,\<N>)" by auto
      with y(2) have "y=y'" by auto
    }
    then have "\<forall>y'. \<langle>x,y'\<rangle>\<in>{\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R} \<longrightarrow> y=y'" by auto
  }
  then have "\<forall>x y. \<langle>x,y\<rangle>\<in>{\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R} \<longrightarrow> (\<forall>y'. \<langle>x,y'\<rangle>\<in>{\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R} \<longrightarrow> y=y')" by auto
  moreover
  have "domain({\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R})\<subseteq>R" unfolding domain_def by auto
  ultimately show fun:"{\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R}:R\<rightarrow>End(\<N>,restrict(A\<^sub>M,\<N>\<times>\<N>))" unfolding Pi_def function_def by auto
qed

text\<open>A submodule is a module with the restricted action.\<close>

corollary(in module0) submodule: 
  assumes "IsAsubmodule(\<N>)"
  shows "IsLeftModule(R,A,M,\<N>,restrict(A\<^sub>M,\<N>\<times>\<N>),{\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R})"
  unfolding IsLeftModule_def IsAction_def ringHomomor_def IsMorphism_def
proof(safe)
  show "IsAring(R, A, M)" using ringAssum by auto
  show g:"IsAgroup(\<N>, restrict(A\<^sub>M,\<N>\<times>\<N>))" using sumodule_is_subgroup assms unfolding IsAsubgroup_def
    by auto
  have sub:"\<N>\<subseteq>\<M>" using mod_ab_gr.group0_3_L2[OF sumodule_is_subgroup[OF assms]] by auto
  then show "restrict(A\<^sub>M,\<N>\<times>\<N>) {is commutative on} \<N>" using mAbGr
    using func_ZF_4_L1[OF mod_ab_gr.group_oper_fun] by auto
  show fun:"{\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R}:R\<rightarrow>End(\<N>,restrict(A\<^sub>M, \<N> \<times> \<N>))" using action_submodule assms by auto
  then have Q:"{\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R}`\<one>=restrict(H`\<one>,\<N>)" using apply_equality Ring_ZF_1_L2(2)
    by auto
  then have "\<forall>h\<in>\<N>. ({\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R}`\<one>)`h=restrict(H`\<one>,\<N>)`h" by auto
  then have "\<forall>h\<in>\<N>. ({\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R}`\<one>)`h=(H`\<one>)`h" using restrict by auto
  then have "\<forall>h\<in>\<N>. ({\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R}`\<one>)`h=h" using module_ax4
    sub by auto
  then have "\<forall>h\<in>\<N>. ({\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R}`\<one>)`h=id(\<N>)`h" by auto moreover
  have "id(\<N>):\<N>\<rightarrow>\<N>" using id_inj unfolding inj_def by auto moreover
  from Q have "{\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R}`\<one>:\<N>\<rightarrow>\<M>" using restrict_fun[OF H_val_type(2)[OF Ring_ZF_1_L2(2)] sub]
    by auto
  ultimately have "{\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R}`\<one>=id(\<N>)" using fun_extension[of "{\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R}`\<one>" \<N> "\<lambda>_. \<M>" "id(\<N>)"] by auto
  also have "\<dots>=TheNeutralElement(End(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)), restrict(Composition(\<N>), End(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)) \<times> End(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>))))" 
    using group0.end_comp_monoid(2) sumodule_is_subgroup[OF assms] unfolding group0_def IsAsubgroup_def
    by auto
  ultimately show "{\<langle>r,restrict(H`r,\<N>)\<rangle>. r\<in>R}`TheNeutralElement(R, M)=TheNeutralElement(End(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)),   EndMult(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)))"
    unfolding EndMult_def  by auto
  fix r s assume AS:"r\<in>R""s\<in>R"
  then have END:"restrict(H ` r, \<N>)\<in>End(\<N>,restrict(A\<^sub>M, \<N> \<times> \<N>))""restrict(H ` s, \<N>)\<in>End(\<N>,restrict(A\<^sub>M, \<N> \<times> \<N>))" using apply_type[OF fun]
    apply_equality[OF _ fun] by auto
  then have funf:"restrict(H ` r, \<N>):\<N>\<rightarrow>\<N>""restrict(H ` s, \<N>):\<N>\<rightarrow>\<N>" unfolding End_def by auto
  from AS have rs:"r\<ra>s\<in>R""r\<cdot>s\<in>R" using Ring_ZF_1_L4(1,3) by auto
  then have EE:"{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` (r\<ra>s)=restrict(H ` (r\<ra>s), \<N>)" using apply_equality fun by auto
  have m:"monoid0(\<N>,restrict(A\<^sub>M, \<N> \<times> \<N>))" unfolding monoid0_def
    using g unfolding IsAgroup_def by auto
  have f1:"{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` (r\<ra>s):\<N>\<rightarrow>\<N>" using apply_type[OF fun rs(1)] unfolding End_def by auto
  have f:"(restrict(A\<^sub>M, \<N> \<times> \<N>) {lifted to function space over} \<N>) `
          \<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle>:\<N>\<rightarrow>\<N>" using monoid0.Group_ZF_2_1_L0[OF m _ funf]
          AS apply_equality[OF _ fun] by auto
  from END have "\<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle> \<in> End(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)) \<times> End(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>))"
       using apply_equality[OF _ fun] AS by auto
  from apply_type[OF restrict_fun[OF monoid0.Group_ZF_2_1_L0A[OF m, of "restrict(A\<^sub>M,\<N>\<times>\<N>) {lifted to function space over}\<N>" \<N>], of "End(\<N>,restrict(A\<^sub>M, \<N> \<times> \<N>))\<times>End(\<N>,restrict(A\<^sub>M, \<N> \<times> \<N>))"] this] 
     have f2:"(EndAdd(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)) `
          \<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle>):\<N>\<rightarrow>\<N>"
      unfolding EndAdd_def End_def by blast
  {
    fix g assume gh:"g\<in>\<N>"
    have A:"((restrict(A\<^sub>M, \<N> \<times> \<N>)  {lifted to function space over} \<N>) `
          \<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle>)`g=((restrict(A\<^sub>M, \<N> \<times> \<N>) {lifted to function space over} \<N>) `
          \<langle>restrict(H ` r, \<N>), restrict(H ` s, \<N>)\<rangle>)`g" using apply_equality[OF _ fun] AS by auto
    from END have "\<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle> \<in> End(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)) \<times> End(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>))"
       using apply_equality[OF _ fun] AS by auto
     with A have "(EndAdd(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)) `
          \<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle>)`g=((restrict(A\<^sub>M, \<N> \<times> \<N>) {lifted to function space over} \<N>) `
          \<langle>restrict(H ` r, \<N>), restrict(H ` s, \<N>)\<rangle>)`g" unfolding EndAdd_def 
       using restrict[of "(restrict(A\<^sub>M, \<N> \<times> \<N>)  {lifted to function space over} \<N>)" "End(\<N>,restrict(A\<^sub>M, \<N> \<times> \<N>))\<times>End(\<N>,restrict(A\<^sub>M, \<N> \<times> \<N>))" "\<langle>restrict(H ` r, \<N>), restrict(H ` s, \<N>)\<rangle>"]
      by auto
    also have "\<dots>=restrict(A\<^sub>M,\<N> \<times> \<N>)`\<langle>restrict(H ` r, \<N>)`g, restrict(H ` s, \<N>)`g\<rangle>" using group0.Group_ZF_2_1_L3[OF _ _ funf gh] g
      unfolding group0_def by auto
    also have "\<dots>=A\<^sub>M`\<langle>restrict(H ` r, \<N>)`g, restrict(H ` s, \<N>)`g\<rangle>" using apply_type[OF funf(1) gh] apply_type[OF funf(2) gh]
      by auto
    also have "\<dots>=A\<^sub>M`\<langle>(H ` r)`g, (H ` s)`g\<rangle>" using gh by auto
    also have "\<dots>=(H`(r\<ra>s))`g" using module_ax2 AS gh sub by auto
    also have "\<dots>=restrict(H`(r\<ra>s),\<N>)`g" using gh by auto  
    also have "\<dots>=({\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` (r\<ra>s))`g" using EE by auto
    ultimately have "(EndAdd(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)) `
          \<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle>)`g=({\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` (r\<ra>s))`g" by auto
  }
  then have "\<forall>g\<in>\<N>. (EndAdd(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)) `
          \<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle>)`g=({\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` (r\<ra>s))`g" by auto
  then show "{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` (A ` \<langle>r, s\<rangle>) =
          EndAdd(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)) `
          \<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle>" using fun_extension[OF f1 f2] by auto
  have f1:"({\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} `(r\<cdot>s)):\<N>\<rightarrow>\<N>" using apply_type[OF fun rs(2)] unfolding End_def by auto
  have ff1:"{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r:\<N>\<rightarrow>\<N>""{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s:\<N>\<rightarrow>\<N>" using apply_type[OF fun] AS unfolding End_def by auto
  then have "({\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r)O({\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s):\<N>\<rightarrow>\<N>" using comp_fun by auto
  then have f:"(Composition(\<N>) ` \<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle>):\<N>\<rightarrow>\<N>" using func_ZF_5_L2
    [OF ff1] using EndMult_def by auto
  from END have "\<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle> \<in> End(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)) \<times> End(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>))"
       using apply_equality[OF _ fun] AS by auto
  from apply_type[OF restrict_fun[OF func_ZF_5_L1[of \<N>], of "End(\<N>,restrict(A\<^sub>M, \<N> \<times> \<N>))\<times>End(\<N>,restrict(A\<^sub>M, \<N> \<times> \<N>))"] this] 
     have f2:"(EndMult(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)) `
          \<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle>):\<N>\<rightarrow>\<N>"
      unfolding EndMult_def End_def by blast
  {
    fix g assume gh:"g\<in>\<N>"
    have A:"(Composition(\<N>) ` \<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle>)`g=
      (Composition(\<N>) ` \<langle>restrict(H ` r, \<N>), restrict(H ` s,\<N>)\<rangle>)`g" using apply_equality[OF _ fun] AS by auto
    from END have "\<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle> \<in> End(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)) \<times> End(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>))"
       using apply_equality[OF _ fun] AS by auto
     with A have "(EndMult(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)) ` \<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle>)`g=
      (Composition(\<N>) ` \<langle>restrict(H ` r, \<N>), restrict(H ` s,\<N>)\<rangle>)`g" 
       using restrict unfolding EndMult_def by auto
    also have "\<dots>=(restrict(H ` r, \<N>)O restrict(H ` s,\<N>))`g" using func_ZF_5_L2[OF funf] by auto
    also have "\<dots>=restrict(H ` r, \<N>)`( restrict(H` s,\<N>)`g)" using comp_fun_apply[OF funf(2) gh] by auto
    also have "\<dots>=(H ` r)`((H ` s)`g)" using gh apply_type[OF funf(2) gh] by auto
    also have "\<dots>=(H`(r\<cdot>s))`g" using module_ax3 gh sub AS by auto
    also have "\<dots>=restrict(H ` (r\<cdot>s), \<N>)`g" using gh by auto
    also have "\<dots>=({\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} `(r\<cdot>s))`g" using apply_equality[OF _ fun] rs(2) by auto
    ultimately have "({\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} `(r\<cdot>s))`g =(EndMult(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)) ` \<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle>)`g"
      by auto
  }
  then have "\<forall>g\<in>\<N>. ({\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} `(r\<cdot>s))`g =(EndMult(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)) ` \<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle>)`g" by auto
  then show "{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` (M ` \<langle>r, s\<rangle>) =
           EndMult(\<N>, restrict(A\<^sub>M, \<N> \<times> \<N>)) ` \<langle>{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` r, {\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` s\<rangle>" using fun_extension[OF f1 f2] by auto
qed

text\<open>If we consider linear combinations of elements in a submodule, then
the linear combination is also in the submodule.\<close>

lemma(in module0) linear_comb_submod:
  assumes "IsAsubmodule(\<N>)" "D\<in>FinPow(X)" "AA:X\<rightarrow>R" "B:X\<rightarrow>\<N>"
  shows "\<Sum>[D;{AA,B}]\<in>\<N>"
proof-
  have fun:"A\<^sub>M:\<M>\<times>\<M>\<rightarrow>\<M>" using mod_ab_gr.group_oper_fun.
  from assms(4) have BB:"B:X\<rightarrow>\<M>" using mod_ab_gr.group0_3_L2[OF sumodule_is_subgroup[OF assms(1)]] func1_1_L1B by auto
  {
    fix A1 B1 assume fun:"A1:X\<rightarrow>R" "B1:X\<rightarrow>\<N>"
    from fun(2) have fun2:"B1:X\<rightarrow>\<M>" using mod_ab_gr.group0_3_L2[OF sumodule_is_subgroup[OF assms(1)]] func1_1_L1B by auto
    have "0\<in>FinPow(X)" unfolding FinPow_def by auto
    then have "\<Sum>[0;{A1,B1}]=\<Theta>" using LinearComb_def[OF fun(1) fun2] by auto
    then have "\<Sum>[0;{A1,B1}]\<in>\<N>" using assms(1) mod_ab_gr.group0_3_L5 unfolding IsAsubmodule_def by auto
  }
  then have base:"\<forall>A1\<in>X\<rightarrow>R. \<forall>B1\<in>X\<rightarrow>\<N>. \<Sum>[0;{A1,B1}]\<in>\<N>" by auto
  {
    fix RR assume a:"RR\<noteq>0" "RR\<in>FinPow(X)"
    then obtain d where d:"d\<in>RR" by auto
    {
      fix A1 B1 assume fun:"A1:X\<rightarrow>R" "B1:X\<rightarrow>\<N>" and step:"\<forall>A1\<in>X\<rightarrow>R. \<forall>B1\<in>X\<rightarrow>\<N>. \<Sum>[RR-{d};{A1,B1}]\<in>\<N>"
      have F:"{\<langle>m, ({\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` (A1 ` m)) ` (B1 ` m)\<rangle> . m \<in> X} : X \<rightarrow> \<N>" using module0.coordinate_function[OF _ fun]
        submodule[OF assms(1)] unfolding module0_def IsLeftModule_def ring0_def module0_axioms_def by auto
      {
        fix m assume mx:"m\<in>X"
        then have bh:"B1`m\<in>\<N>" using fun(2) apply_type by auto
        from mx have ar:"A1`m\<in>R" using fun(1) apply_type by auto
        then have A:"{\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R}`(A1`m)=restrict(H ` (A1`m), \<N>)" using apply_equality action_submodule[OF assms(1)]
          by auto
        have B:"(restrict(H ` (A1`m), \<N>)) ` (B1 ` m)=(H ` (A1`m))`(B1 ` m)"  using bh restrict by auto
        with A have "({\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` (A1 ` m)) ` (B1 ` m)=(H ` (A1`m))`(B1 ` m)" by auto
      }
      then have eq1:"{\<langle>m, ({\<langle>r, restrict(H ` r, \<N>)\<rangle> . r \<in> R} ` (A1 ` m)) ` (B1 ` m)\<rangle> . m \<in> X} ={\<langle>m, (H ` (A1`m))`(B1 ` m)\<rangle> . m \<in> X} " by auto
      then have pd:"{\<langle>m, (H ` (A1`m))`(B1 ` m)\<rangle> . m \<in> X}`d\<in>\<N>" using d apply_type[OF F] a(2) unfolding FinPow_def by auto
      from fun(2) have fun2:"B1:X\<rightarrow>\<M>" using mod_ab_gr.group0_3_L2[OF sumodule_is_subgroup[OF assms(1)]] func1_1_L1B by auto
      have "\<Sum>[RR;{A1,B1}]=(\<Sum>[RR-{d};{A1,B1}])+\<^sub>V({\<langle>k, (A1 ` k) \<cdot>\<^sub>S (B1 ` k)\<rangle> . k \<in> X} ` d)" using sum_one_element[OF fun(1) fun2 a(2) d].
      also have "\<dots>\<in>\<N>" using pd step fun mod_ab_gr.group0_3_L6[OF sumodule_is_subgroup[OF assms(1)]] by auto
      ultimately have "\<Sum>[RR;{A1,B1}]\<in>\<N>" by auto
    }
    then have "(\<forall>AA1\<in>X\<rightarrow>R. \<forall>BB1\<in>X\<rightarrow>\<N>. \<Sum>[RR-{d};{AA1,BB1}]\<in>\<N>)\<longrightarrow>(\<forall>AA1\<in>X\<rightarrow>R. \<forall>BB1\<in>X\<rightarrow>\<N>. \<Sum>[RR;{AA1,BB1}]\<in>\<N>)" by auto
    with d have "\<exists>d\<in>RR. ((\<forall>AA1\<in>X\<rightarrow>R. \<forall>BB1\<in>X\<rightarrow>\<N>. \<Sum>[RR-{d};{AA1,BB1}]\<in>\<N>)\<longrightarrow>(\<forall>AA1\<in>X\<rightarrow>R. \<forall>BB1\<in>X\<rightarrow>\<N>. \<Sum>[RR;{AA1,BB1}]\<in>\<N>))" by auto
  }
  then have step:"\<forall>RR\<in>FinPow(X). RR\<noteq>0 \<longrightarrow> (\<exists>d\<in>RR. ((\<forall>AA1\<in>X\<rightarrow>R. \<forall>BB1\<in>X\<rightarrow>\<N>. \<Sum>[RR-{d};{AA1,BB1}]\<in>\<N>)\<longrightarrow>(\<forall>AA1\<in>X\<rightarrow>R. \<forall>BB1\<in>X\<rightarrow>\<N>. \<Sum>[RR;{AA1,BB1}]\<in>\<N>)))" by auto
  show ?thesis using FinPow_ind_rem_one[OF base step] assms(2-4) by auto
qed

subsubsection\<open>Spans\<close>

text\<open>Since we know linear combinations, we can define the span of a subset
of a module as the linear combinations of elements in that subset. We have already
proven that the sum can be done only over finite numbers considering a bijection
between a finite number and the original finite set, and that the function can be
restricted to that finite number.\<close>

text\<open>The terms of a linear combination can be reordered so 
that they are indexed by the elements of the module.\<close>

lemma(in module0) index_module:
  assumes "AAA:X\<rightarrow>R" "BB:X\<rightarrow>\<M>" "D\<in>FinPow(X)"
  shows "\<exists>AA\<in>\<M>\<rightarrow>R. \<Sum>[D;{AAA,BB}]=\<Sum>[BB``D;{AA,id(\<M>)}] \<and> (\<forall>x\<in>\<M>-BB``D. AA`x=\<zero>)"
proof-
  let ?F="{\<langle>d,CommSetFold(A,AAA,D\<inter>(BB-``({BB`d})))\<rangle>. d\<in>D}"
  let ?f1="{\<langle>d,D\<inter>(BB-``({BB`d}))\<rangle>. d\<in>D}"
  have "?f1:D\<rightarrow>{D\<inter>(BB-``({BB`d})). d\<in>D}" unfolding Pi_def function_def by auto
  then have "RepFun(D,\<lambda>t. ?f1`t)={D\<inter>(BB-``({BB`d})). d\<in>D}" using apply_equality by auto
  with assms(3) have "Finite({D\<inter>(BB-``({BB`d})). d\<in>D})" using Finite_RepFun unfolding FinPow_def by auto
  then obtain n where "{D\<inter>(BB-``({BB`d})). d\<in>D}\<approx>n" and n:"n\<in>nat" unfolding Finite_def by auto
  then have n2:"{D\<inter>(BB-``({BB`d})). d\<in>D}\<lesssim>n" using eqpoll_imp_lepoll by auto
  {
    fix T assume "T\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}"
    then obtain d where d:"d\<in>D" "T=D\<inter>(BB-``({BB`d}))" by auto
    {
      assume "d\<notin>T"
      with d have "d\<notin>(BB-``({BB`d}))" by auto
      then have "\<langle>d,BB`d\<rangle>\<notin>BB" using vimage_iff by auto
      with d(1) assms(2,3) have "False" unfolding FinPow_def Pi_def using function_apply_Pair[of BB d] by auto
    }
    then have "T\<noteq>0" by auto
  }
  then have n3:"\<forall>t\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}. id({D\<inter>(BB-``({BB`d})). d\<in>D}) ` t \<noteq> 0" using id_def by auto
  from n have "\<forall>M N. M \<lesssim> n \<and> (\<forall>t\<in>M. N ` t \<noteq> 0) \<longrightarrow> (\<exists>f. f \<in> Pi(M,\<lambda>t. N ` t) \<and> (\<forall>t\<in>M. f ` t \<in> N ` t))" using finite_choice[of n] unfolding AxiomCardinalChoiceGen_def
    by auto
  with n2 have "\<forall>N. (\<forall>t\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}. N ` t \<noteq> 0) \<longrightarrow> (\<exists>f. f \<in> Pi({D\<inter>(BB-``({BB`d})). d\<in>D},\<lambda>t. N ` t) \<and> (\<forall>t\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}. f ` t \<in> N ` t))"
    by blast
  with n3 have "\<exists>f. f \<in> Pi({D\<inter>(BB-``({BB`d})). d\<in>D},\<lambda>t. id({D\<inter>(BB-``({BB`d})). d\<in>D}) ` t) \<and> (\<forall>t\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}. f ` t \<in> id({D\<inter>(BB-``({BB`d})). d\<in>D}) ` t)"
    by auto
  then obtain ff where ff:"ff\<in>Pi({D\<inter>(BB-``({BB`d})). d\<in>D},\<lambda>t. id({D\<inter>(BB-``({BB`d})). d\<in>D}) ` t)" "(\<forall>t\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}. ff ` t \<in> id({D\<inter>(BB-``({BB`d})). d\<in>D}) ` t)" by force
  {
    fix t assume as:"t\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}"
    with ff(2) have "ff`t\<in>id({D\<inter>(BB-``({BB`d})). d\<in>D}) ` t" by blast
    with as have "ff`t\<in>t" using id_def by auto
  }
  then have ff2:"\<forall>t\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}. ff ` t \<in>t" by auto
  have "\<forall>x\<in>{D\<inter>(BB-``({BB`d})). d\<in>D}. id({D\<inter>(BB-``({BB`d})). d\<in>D})`x=x" using id_def by auto
  with ff(1) have ff1:"ff\<in>Pi({D\<inter>(BB-``({BB`d})). d\<in>D},\<lambda>t. t)" unfolding Pi_def Sigma_def by auto
  have case0:"\<exists>AA\<in>\<M>\<rightarrow>R. \<Sum>[0;{AAA,BB}]=\<Sum>[BB``0;{AA,id(\<M>)}] \<and> (\<forall>x\<in>\<M>-BB``0. AA`x=\<zero>)"
    proof
      have "\<Sum>[0;{AAA,BB}]=\<Theta>" using LinearComb_def[OF assms(1,2)] unfolding FinPow_def by auto moreover
      let ?A="ConstantFunction(\<M>,\<zero>)"
      have "\<Sum>[0;{?A,id(\<M>)}]=\<Theta>" using LinearComb_def[OF func1_3_L1[OF Ring_ZF_1_L2(1)], of "id(\<M>)" \<M> 0]
        unfolding id_def FinPow_def by auto moreover
      have "BB``0=0" by auto ultimately
      show "\<Sum>[0;{AAA,BB}]=\<Sum>[BB``0;{?A,id(\<M>)}] \<and> (\<forall>x\<in>\<M>-BB``0. ?A`x=\<zero>)" using func1_3_L2 by auto
      then show "?A:\<M>\<rightarrow>R" using func1_3_L1[OF Ring_ZF_1_L2(1), of \<M>] by auto
    qed
  {
    fix E assume E:"E\<in>FinPow(X)" "E\<noteq>0"
    {
      fix d assume d:"d\<in>E"
      {
        assume hyp:"\<exists>AA\<in>\<M>\<rightarrow>R. \<Sum>[E-{d};{AAA,BB}]=\<Sum>[BB``(E-{d});{AA,id(\<M>)}] \<and> (\<forall>x\<in>\<M>-BB``(E-{d}). AA`x=\<zero>)"
        from hyp obtain AA where AA:"AA\<in>\<M>\<rightarrow>R" "\<Sum>[E-{d};{AAA,BB}]=\<Sum>[BB``(E-{d});{AA,id(\<M>)}]" "\<forall>x\<in>\<M>-BB``(E-{d}). AA`x=\<zero>" by auto
        have "\<Sum>[E;{AAA,BB}] = (\<Sum>[E-{d};{AAA,BB}])+\<^sub>V({\<langle>e,(AAA`e)\<cdot>\<^sub>S(BB`e)\<rangle>. e\<in>X}`d)" using sum_one_element[OF assms(1,2) E(1) d].
        with AA(2) also have "\<dots>=(\<Sum>[BB``(E-{d});{AA,id(\<M>)}])+\<^sub>V((AAA`d)\<cdot>\<^sub>S(BB`d))" using d E(1) unfolding FinPow_def using apply_equality[OF _
          coordinate_function[OF assms(1,2)]] by auto
        ultimately have eq:"\<Sum>[E;{AAA,BB}] =(\<Sum>[BB``(E-{d});{AA,id(\<M>)}])+\<^sub>V((AAA`d)\<cdot>\<^sub>S(BB`d))" by auto
        have btype:"BB`d\<in>\<M>" using apply_type assms(2) d E(1) unfolding FinPow_def by auto
        have "(E-{d})\<in>FinPow(X)" using E(1) unfolding FinPow_def using subset_Finite[of "E-{d}" E] by auto moreover
        then have "{BB`x. x\<in>E-{d}}=BB``(E-{d})" using func_imagedef[OF assms(2), of "E-{d}"] unfolding FinPow_def
          by auto
        ultimately have fin:"Finite(BB``(E-{d}))" using Finite_RepFun[of "E-{d}" "\<lambda>t. BB`t"] unfolding FinPow_def by auto
        then have "Finite(BB``(E-{d})\<union>{BB`d})" using Finite_cons[of "BB``(E-{d})" "BB`d"] by auto
        with btype have finpow:"BB``(E-{d})\<union>{BB`d}\<in>FinPow(\<M>)" using func1_1_L6(2)[OF assms(2)] unfolding FinPow_def by auto
        {
          assume as:"BB`d\<notin>BB``(E-{d})"
          then have T_def:"BB``(E-{d})=(BB``(E-{d})\<union>{BB`d})-{BB`d}" by auto
          from as have sub:"BB``(E-{d})\<subseteq>\<M>-{BB`d}" using func1_1_L6(2)[OF assms(2)] by auto
          let ?A="restrict(AA,\<M>-{BB`d})\<union>ConstantFunction({BB`d},AAA`d)"
          have res:"restrict(AA,\<M>-{BB`d}):\<M>-{BB`d}\<rightarrow>R" using restrict_fun[OF AA(1)] by auto
          moreover have "AAA`d\<in>R" using apply_type assms(1) d E(1) unfolding FinPow_def by auto
          then have con:"ConstantFunction({BB`d},AAA`d):{BB`d}\<rightarrow>R" using func1_3_L1 by auto
          moreover have "(G-{BB`d})\<inter>{BB`d}=0" by auto moreover
          have "R\<union>R=R" by auto moreover
          have "(\<M>-{BB`d})\<union>{BB`d}=\<M>" using apply_type[OF assms(2)] d E(1) unfolding FinPow_def by auto ultimately
          have A_fun:"?A:\<M>\<rightarrow>R" using fun_disjoint_Un[of "restrict(AA,\<M>-{BB`d})" "\<M>-{BB`d}" R "ConstantFunction({BB`d},AAA`d)" "{BB`d}" R] by auto
          have "?A`(BB`d)=ConstantFunction({BB`d},AAA`d)`(BB`d)" using as fun_disjoint_apply2 by auto moreover note btype
          ultimately have A_app:"?A`(BB`d)=AAA`d" using as func1_3_L2 by auto
          {
            fix z assume "z\<in>restrict(?A,BB``(E-{d}))"
            then have z:"z\<in>?A" "\<exists>x\<in>BB `` (E - {d}). \<exists>y. z = \<langle>x, y\<rangle>" using restrict_iff by auto
            then have "\<exists>x\<in>BB `` (E - {d}). \<exists>y. z = \<langle>x, y\<rangle>" "z\<in>ConstantFunction({BB`d},AAA`d) \<or> z\<in>restrict(AA,\<M>-{BB`d})" by auto
            then have "\<exists>x\<in>BB `` (E - {d}). \<exists>y. z = \<langle>x, y\<rangle>" "z\<in>{BB`d}\<times>{AAA`d} \<or> z\<in>restrict(AA,\<M>-{BB`d})" using ConstantFunction_def by auto
            then have "fst(z)\<in>BB `` (E - {d})" "z=\<langle>BB`d,AAA`d\<rangle> \<or> z\<in>restrict(AA,\<M>-{BB`d})"  by auto
            with as have "z\<in>restrict(AA,\<M>-{BB`d})" by auto
            with z(2) have "z\<in>AA" "\<exists>x\<in>BB `` (E - {d}). \<exists>y. z = \<langle>x, y\<rangle>" using restrict_iff by auto
            then have "z\<in>restrict(AA,BB``(E-{d}))" using restrict_iff by auto
          }
          then have "restrict(?A,BB``(E-{d}))\<subseteq>restrict(AA,BB``(E-{d}))" by auto moreover
          {
            fix z assume z:"z\<in>restrict(AA,BB``(E-{d}))" "z\<notin>restrict(?A,BB``(E-{d}))"
            then have disj:"z\<notin>?A \<or> (\<forall>x\<in>BB``(E-{d}). \<forall>y. z \<noteq> \<langle>x, y\<rangle>)" using restrict_iff[of z ?A "BB``(E-{d})"] by auto moreover
            with z(1) have z:"z\<in>AA" "\<exists>x\<in>BB``(E-{d}). \<exists>y. z=\<langle>x, y\<rangle>" using restrict_iff[of _ AA "BB``(E-{d})"] by auto moreover
            from z(2) sub have "\<exists>x\<in>\<M>-{BB`d}. \<exists>y. z=\<langle>x, y\<rangle>" by auto
            with z(1) have "z\<in>restrict(AA,\<M>-{BB`d})" using restrict_iff by auto
            then have "z\<in>?A" by auto
            with disj have "\<forall>x\<in>BB``(E-{d}). \<forall>y. z \<noteq> \<langle>x, y\<rangle>" by auto
            with z(2) have "False" by auto
          }
          then have "restrict(AA,BB``(E-{d}))\<subseteq>restrict(?A,BB``(E-{d}))" by auto ultimately
          have resA:"restrict(AA,BB``(E-{d}))=restrict(?A,BB``(E-{d}))" by auto
          have "\<Sum>[BB``(E-{d});{AA,id(\<M>)}]=\<Sum>[BB``(E-{d});{restrict(AA,BB``(E-{d})),restrict(id(\<M>), BB``(E-{d}))}]" using linComb_restrict_coord[OF AA(1) id_type, of "BB``(E-{d})"]
            fin func1_1_L6(2)[OF assms(2)] unfolding FinPow_def by auto
          also have "\<dots>=\<Sum>[BB``(E-{d});{restrict(?A,BB``(E-{d})),restrict(id(\<M>), BB``(E-{d}))}]" using resA by auto
          also have "\<dots>=\<Sum>[BB``(E-{d});{?A,id(\<M>)}]" using linComb_restrict_coord[OF A_fun id_type, of "BB``(E-{d})"] fin func1_1_L6(2)[OF assms(2)] unfolding FinPow_def by auto
          ultimately have "\<Sum>[BB``(E-{d});{AA,id(\<M>)}]=\<Sum>[(BB``(E-{d})\<union>{BB`d})-{BB`d};{?A,id(\<M>)}]" using T_def by auto
          then have "(\<Sum>[BB``(E-{d});{AA,id(\<M>)}])+\<^sub>V((AAA`d)\<cdot>\<^sub>S(BB`d))=(\<Sum>[(BB``(E-{d})\<union>{BB`d})-{BB`d};{?A,id(\<M>)}])+\<^sub>V((?A`(BB`d))\<cdot>\<^sub>S(BB`d))" using A_app by auto
          also have "\<dots>=(\<Sum>[(BB``(E-{d})\<union>{BB`d})-{BB`d};{?A,id(\<M>)}])+\<^sub>V((?A`(BB`d))\<cdot>\<^sub>S(id(\<M>)`(BB`d)))" using id_conv[OF btype] by auto
          also have "\<dots>=(\<Sum>[(BB``(E-{d})\<union>{BB`d})-{BB`d};{?A,id(\<M>)}])+\<^sub>V({\<langle>g,(?A`g)\<cdot>\<^sub>S(id(\<M>)`g)\<rangle>. g\<in>\<M>}`(BB`d))" using apply_equality[OF _ coordinate_function[OF A_fun id_type]
            ,of "BB`d" "(?A`(BB`d))\<cdot>\<^sub>S(id(\<M>)`(BB`d))"] btype by auto
          also have "\<dots>=(\<Sum>[(BB``(E-{d})\<union>{BB`d});{?A,id(\<M>)}])" using sum_one_element[OF A_fun id_type finpow, of "BB`d"] by auto
          ultimately have "(\<Sum>[BB``(E-{d});{AA,id(\<M>)}])+\<^sub>V((AAA`d)\<cdot>\<^sub>S(BB`d))=\<Sum>[(BB``(E-{d})\<union>{BB`d});{?A,id(\<M>)}]" by auto
          with eq have eq:"\<Sum>[E;{AAA,BB}] =\<Sum>[(BB``(E-{d})\<union>{BB`d});{?A,id(\<M>)}]" by auto
          have "BB``(E-{d})\<union>{BB`d}={BB`x. x\<in>E-{d}}\<union>{BB`d}" using func_imagedef[OF assms(2), of "E-{d}"]
            E(1) unfolding FinPow_def by force
          also have "\<dots>={BB`x. x\<in>E}" using d by auto ultimately
          have set:"BB``(E-{d})\<union>{BB`d}=BB``E" using func_imagedef[OF assms(2), of "E"] E(1) unfolding FinPow_def by auto
          {
            fix x assume x:"x\<in>\<M>-BB``E"
            then have x1:"x\<noteq>BB`d" using d func_imagedef[OF assms(2), of E] E(1) unfolding FinPow_def by auto
            then have "?A`x=restrict(AA,\<M>-{BB`d})`x" using fun_disjoint_apply1[of x "ConstantFunction({BB`d},AAA`d)"] unfolding
              ConstantFunction_def by blast
            with x x1 have "?A`x=AA`x" using restrict by auto moreover
            from x set have "x\<in>\<M>-BB``(E-{d})" by auto ultimately
            have "?A`x=\<zero>" using AA(3) by auto
          }
          with set eq A_fun have "\<exists>AA\<in>\<M>\<rightarrow>R. \<Sum>[E;{AAA,BB}]=\<Sum>[BB``E;{AA,id(\<M>)}] \<and> (\<forall>x\<in>\<M>-(BB``E). AA`x=\<zero>)" by auto
        }
        moreover
        {
          assume as:"BB`d\<in>BB``(E-{d})"
          then have "BB``(E-{d})\<union>{BB`d}=BB``(E-{d})" by auto
          then have finpow:"BB``(E-{d})\<in>FinPow(\<M>)" using finpow by auto
          have sub:"E-{d}\<subseteq>X" using E(1) unfolding FinPow_def by force
          with as have "BB`d\<in>{BB`f. f\<in>E-{d}}" using func_imagedef[OF assms(2), of "E-{d}"] by auto
          then have "{BB`f. f\<in>E-{d}}={BB`f. f\<in>E}" by auto
          then have im_eq:"BB``(E-{d})=BB``E" using func_imagedef[OF assms(2),of "E-{d}"] func_imagedef[OF assms(2),of E] sub E(1) unfolding FinPow_def
            by auto
          from as have "\<Sum>[BB``(E-{d});{AA,id(\<M>)}]=(\<Sum>[BB``(E-{d})-{BB`d};{AA,id(\<M>)}])+\<^sub>V({\<langle>g,(AA`g)\<cdot>\<^sub>S(id(\<M>)`g)\<rangle>. g\<in>\<M>}`(BB`d))" using sum_one_element[OF AA(1) id_type]
            finpow by auto
          also have "\<dots>=(\<Sum>[BB``(E-{d})-{BB`d};{AA,id(\<M>)}])+\<^sub>V((AA`(BB`d))\<cdot>\<^sub>S(id(\<M>)`(BB`d)))" using apply_equality[OF _ coordinate_function[OF AA(1) id_type]]
            btype by auto
          also have "\<dots>=(\<Sum>[BB``(E-{d})-{BB`d};{AA,id(\<M>)}])+\<^sub>V((AA`(BB`d))\<cdot>\<^sub>S(BB`d))" using id_conv btype by auto
          ultimately have "\<Sum>[BB``(E-{d});{AA,id(\<M>)}]=(\<Sum>[BB``(E-{d})-{BB`d};{AA,id(\<M>)}])+\<^sub>V((AA`(BB`d))\<cdot>\<^sub>S(BB`d))" by auto
          then have "\<Sum>[E;{AAA,BB}] =((\<Sum>[BB``(E-{d})-{BB`d};{AA,id(\<M>)}])+\<^sub>V((AA`(BB`d))\<cdot>\<^sub>S(BB`d)))+\<^sub>V((AAA ` d)\<cdot>\<^sub>S (BB ` d))" using eq by auto
          moreover have "\<Sum>[BB``(E-{d})-{BB`d};{AA,id(\<M>)}]\<in>\<M>" using linComb_is_in_module[OF AA(1) id_type, of "BB``(E-{d})-{BB`d}"] finpow subset_Finite[of "BB``(E-{d})-{BB`d}" "BB``(E-{d})"] unfolding FinPow_def
            by auto moreover
          have "(AA`(BB`d))\<cdot>\<^sub>S(BB`d)\<in>\<M>" using apply_type[OF AA(1) btype] apply_type[OF H_val_type(2)]
            btype by auto  moreover
          have "(AAA`d)\<cdot>\<^sub>S(BB`d)\<in>\<M>" using apply_type apply_type[OF assms(1), of d] apply_type[OF H_val_type(2)]
             btype d E(1) unfolding FinPow_def by auto ultimately
          have "\<Sum>[E;{AAA,BB}] =(\<Sum>[BB``(E-{d})-{BB`d};{AA,id(\<M>)}])+\<^sub>V(((AA`(BB`d))\<cdot>\<^sub>S(BB`d))+\<^sub>V((AAA ` d) \<cdot>\<^sub>S (BB ` d)))" 
            using mod_ab_gr.group_oper_assoc by auto moreover
          have "((AA`(BB`d))\<cdot>\<^sub>S(BB`d))+\<^sub>V((AAA ` d) \<cdot>\<^sub>S (BB ` d))=((AA`(BB`d))\<ra>(AAA ` d))\<cdot>\<^sub>S(BB`d)" using btype apply_type[OF assms(1), of d]
            apply_type[OF AA(1) btype] d E(1) module_ax2 unfolding FinPow_def by auto
          ultimately have eq:"\<Sum>[E;{AAA,BB}] =(\<Sum>[BB``(E-{d})-{BB`d};{AA,id(\<M>)}])+\<^sub>V(((AA`(BB`d))\<ra>(AAA ` d))\<cdot>\<^sub>S(BB`d))" by auto
          let ?A="restrict(AA,\<M>-{BB`d})\<union>ConstantFunction({BB`d},(AA`(BB`d))\<ra>(AAA ` d))"
          have "(\<M>-{BB`d})\<inter>({BB`d})=0" by auto moreover
          have "(\<M>-{BB`d})\<union>({BB`d})=\<M>" using finpow as unfolding FinPow_def by auto moreover
          have "restrict(AA,\<M>-{BB`d}):(\<M>-{BB`d})\<rightarrow>R" using restrict_fun[OF AA(1), of "\<M>-{BB`d}"] finpow unfolding FinPow_def by auto moreover
          have "AAA`d\<in>R" "AA`(BB`d)\<in>R" using apply_type assms(1) AA(1) btype d E(1) unfolding FinPow_def by auto
          then have "(AA`(BB`d))\<ra>(AAA ` d)\<in>R" using Ring_ZF_1_L4(1) by auto
          then have "ConstantFunction({BB`d},(AA`(BB`d))\<ra>(AAA ` d)):{BB`d}\<rightarrow>R" using func1_3_L1 by auto
          ultimately have A_fun:"?A:\<M>\<rightarrow>R" using fun_disjoint_Un[of "restrict(AA,\<M>-{BB`d})" "\<M>-{BB`d}" R "ConstantFunction({BB`d},(AA`(BB`d))\<ra>(AAA ` d))" "{BB`d}" R] by auto
          have "?A`(BB`d)=ConstantFunction({BB`d},(AA`(BB`d))\<ra>(AAA ` d))`(BB`d)" using as fun_disjoint_apply2 by auto moreover note btype
          ultimately have A_app:"?A`(BB`d)=(AA`(BB`d))\<ra>(AAA ` d)" using as func1_3_L2 by auto
          {
            fix z assume "z\<in>restrict(?A,BB``(E-{d})-{BB`d})"
            then have z:"\<exists>x\<in>BB``(E-{d})-{BB`d}. \<exists>y. z=\<langle>x,y\<rangle>" "z\<in>?A" using restrict_iff by auto
            then have "\<exists>x\<in>BB `` (E - {d})-{BB`d}. \<exists>y. z = \<langle>x, y\<rangle>" "z\<in>ConstantFunction({BB`d},(AA`(BB`d))\<ra>(AAA ` d)) \<or> z\<in>restrict(AA,\<M>-{BB`d})" by auto
            then have "\<exists>x\<in>BB `` (E - {d})-{BB`d}. \<exists>y. z = \<langle>x, y\<rangle>" "z\<in>{BB`d}\<times>{(AA`(BB`d))\<ra>(AAA ` d)} \<or> z\<in>restrict(AA,\<M>-{BB`d})" using ConstantFunction_def by auto
            then have "fst(z)\<in>BB `` (E - {d})-{BB`d}" "z=\<langle>BB`d,AAA`d\<rangle> \<or> z\<in>restrict(AA,\<M>-{BB`d})"  by auto
            then have "z\<in>restrict(AA,\<M>-{BB`d})" by auto
            with z(1) have "z\<in>AA" "\<exists>x\<in>BB `` (E - {d})-{BB`d}. \<exists>y. z = \<langle>x, y\<rangle>" using restrict_iff by auto
            then have "z\<in>restrict(AA,BB``(E-{d})-{BB`d})" using restrict_iff by auto
          }
          then have "restrict(?A,BB``(E-{d})-{BB`d})\<subseteq>restrict(AA,BB``(E-{d})-{BB`d})" by auto moreover
          {
            fix z assume z:"z\<in>restrict(AA,BB``(E-{d})-{BB`d})" "z\<notin>restrict(?A,BB``(E-{d})-{BB`d})"
            then have disj:"z\<notin>?A \<or> (\<forall>x\<in>BB``(E-{d})-{BB`d}. \<forall>y. z \<noteq> \<langle>x, y\<rangle>)" using restrict_iff[of z ?A "BB``(E-{d})-{BB`d}"] by auto moreover
            with z(1) have z:"z\<in>AA" "\<exists>x\<in>BB``(E-{d})-{BB`d}. \<exists>y. z=\<langle>x, y\<rangle>" using restrict_iff[of _ AA "BB``(E-{d})-{BB`d}"] by auto moreover
            from z(2) func1_1_L6(2)[OF assms(2)] have "\<exists>x\<in>\<M>-{BB`d}. \<exists>y. z=\<langle>x, y\<rangle>" by auto
            with z(1) have "z\<in>restrict(AA,\<M>-{BB`d})" using restrict_iff by auto
            then have "z\<in>?A" by auto
            with disj have "\<forall>x\<in>BB``(E-{d})-{BB`d}. \<forall>y. z \<noteq> \<langle>x, y\<rangle>" by auto
            with z(2) have "False" by auto
          }
          then have "restrict(AA,BB``(E-{d})-{BB`d})\<subseteq>restrict(?A,BB``(E-{d})-{BB`d})" by auto ultimately
          have resA:"restrict(AA,BB``(E-{d})-{BB`d})=restrict(?A,BB``(E-{d})-{BB`d})" by auto
          have "Finite(BB``(E-{d})-{BB`d})" using finpow unfolding FinPow_def using subset_Finite[of "BB``(E-{d}) -{BB`d}"] by auto
          with finpow have finpow2:"BB``(E-{d})-{BB`d}\<in>FinPow(\<M>)" unfolding FinPow_def by auto
          have "\<Sum>[BB``(E-{d})-{BB`d};{AA,id(\<M>)}]=\<Sum>[BB``(E-{d})-{BB`d};{restrict(AA,BB``(E-{d})-{BB`d}),restrict(id(\<M>), BB``(E-{d})-{BB`d})}]" using linComb_restrict_coord[OF AA(1) id_type finpow2]
            by auto
          also have "\<dots>=\<Sum>[BB``(E-{d})-{BB`d};{restrict(?A,BB``(E-{d})-{BB`d}),restrict(id(\<M>), BB``(E-{d})-{BB`d})}]" using resA by auto
          also have "\<dots>=\<Sum>[BB``(E-{d})-{BB`d};{?A,id(\<M>)}]" using linComb_restrict_coord[OF A_fun id_type finpow2] by auto
          ultimately have "\<Sum>[BB``(E-{d})-{BB`d};{AA,id(\<M>)}]=\<Sum>[BB``(E-{d})-{BB`d};{?A,id(\<M>)}]" by auto
          then have "(\<Sum>[BB``(E-{d})-{BB`d};{AA,id(\<M>)}])+\<^sub>V(((AA`(BB`d))\<ra>(AAA ` d))\<cdot>\<^sub>S(BB`d))=(\<Sum>[BB``(E-{d})-{BB`d};{?A,id(\<M>)}])+\<^sub>V((?A`(BB`d))\<cdot>\<^sub>S(BB`d))" using A_app by auto
          also have "\<dots>=(\<Sum>[BB``(E-{d})-{BB`d};{?A,id(\<M>)}])+\<^sub>V((?A`(BB`d))\<cdot>\<^sub>S(id(\<M>)`(BB`d)))" using id_conv[OF btype] by auto
          also have "\<dots>=(\<Sum>[BB``(E-{d})-{BB`d};{?A,id(\<M>)}])+\<^sub>V({\<langle>g,(?A`g)\<cdot>\<^sub>S(id(\<M>)`g)\<rangle>. g\<in>\<M>}`(BB`d))" using apply_equality[OF _ coordinate_function[OF A_fun id_type]
            ,of "BB`d" "(?A`(BB`d))\<cdot>\<^sub>S(id(\<M>)`(BB`d))"] btype by auto
          also have "\<dots>=(\<Sum>[BB``(E-{d});{?A,id(\<M>)}])" using sum_one_element[OF A_fun id_type finpow as] by auto
          ultimately have "(\<Sum>[BB``(E-{d})-{BB`d};{AA,id(\<M>)}])+\<^sub>V(((AA`(BB`d))\<ra>(AAA ` d))\<cdot>\<^sub>S(BB`d))=(\<Sum>[BB``(E-{d});{?A,id(\<M>)}])" by auto
          with eq have sol:"\<Sum>[E;{AAA,BB}] =\<Sum>[BB``(E-{d});{?A,id(\<M>)}]" by auto
          {
            fix x assume x:"x\<in>\<M>-BB``E"
            with as have x1:"x\<in>\<M>-{BB`d}" by auto
            then have "?A`x=restrict(AA,\<M>-{BB`d})`x" using fun_disjoint_apply1[of x "ConstantFunction({BB`d},(AA`(BB`d))\<ra>(AAA ` d))"]
              unfolding ConstantFunction_def by blast
            with x1 have "?A`x=AA`x" using restrict by auto
            with x im_eq have "?A`x=\<zero>" using AA(3) by auto
          }
          with sol A_fun im_eq have "\<exists>AA\<in>\<M>\<rightarrow>R. \<Sum>[E;{AAA,BB}]=\<Sum>[BB``(E);{AA,id(\<M>)}] \<and> (\<forall>x\<in>\<M>-BB``E. AA`x=\<zero>)" by auto
        }
        ultimately have "\<exists>AA\<in>\<M>\<rightarrow>R. \<Sum>[E;{AAA,BB}]=\<Sum>[BB``E;{AA,id(\<M>)}] \<and> (\<forall>x\<in>\<M>-BB``E. AA`x=\<zero>)" by auto
      }
      then have "( \<exists>AA\<in>\<M>\<rightarrow>R. (\<Sum>[E-{d};{AAA,BB}])=(\<Sum>[BB``(E-{d});{AA,id(\<M>)}]) \<and> (\<forall>x\<in>\<M>-BB``(E-{d}). AA`x=\<zero>)) \<longrightarrow> (\<exists>AA\<in>\<M>\<rightarrow>R. (\<Sum>[E;{AAA,BB}])=(\<Sum>[BB``E;{AA,id(\<M>)}]) \<and> (\<forall>x\<in>\<M>-BB``E. AA`x=\<zero>))" by auto
    }
    then have "\<exists>d\<in>E. (( \<exists>AA\<in>\<M>\<rightarrow>R. \<Sum>[E-{d};{AAA,BB}]=\<Sum>[BB``(E-{d});{AA,id(\<M>)}] \<and> (\<forall>x\<in>\<M>-BB``(E-{d}). AA`x=\<zero>)) \<longrightarrow> (\<exists>AA\<in>\<M>\<rightarrow>R. \<Sum>[E;{AAA,BB}]=\<Sum>[BB``(E);{AA,id(\<M>)}] \<and> (\<forall>x\<in>\<M>-BB``E. AA`x=\<zero>)))"
      using E(2) by auto
  }
  then have "\<forall>E\<in>FinPow(X). E\<noteq>0 \<longrightarrow> (\<exists>d\<in>E. ((\<exists>AA\<in>\<M>\<rightarrow>R. \<Sum>[E-{d};{AAA,BB}]=\<Sum>[BB``(E-{d});{AA,id(\<M>)}]\<and> (\<forall>x\<in>\<M>-BB``(E-{d}). AA`x=\<zero>)) \<longrightarrow> (\<exists>AA\<in>\<M>\<rightarrow>R. \<Sum>[E;{AAA,BB}]=\<Sum>[BB``(E);{AA,id(\<M>)}]\<and> (\<forall>x\<in>\<M>-BB``E. AA`x=\<zero>))))"
    by auto
  then show ?thesis using FinPow_ind_rem_one[where ?P="\<lambda>E. \<exists>AA\<in>\<M>\<rightarrow>R. \<Sum>[E;{AAA,BB}]=\<Sum>[BB``E;{AA,id(\<M>)}]\<and> (\<forall>x\<in>\<M>-BB``E. AA`x=\<zero>)", OF case0 _ assms(3)] by auto
qed

text\<open>A span over a set is the collection over all linear combinations on those elements.\<close>

definition(in module0)
  Span("{span of}_")
  where "T\<subseteq>\<M> \<Longrightarrow> {span of}T \<equiv> if T=0 then {\<Theta>} else {\<Sum>[F;{AA,id(T)}]. \<langle>F,AA\<rangle>\<in>{\<langle>FF,B\<rangle>\<in>FinPow(T)\<times>(T\<rightarrow>R). \<forall>m\<in>T-FF. B`m=\<zero>}}"

text\<open>The span of a subset is then a submodule and contains the original set.\<close>

theorem(in module0) linear_ind_set_comb_submodule:
  assumes "T\<subseteq>\<M>"
  shows "IsAsubmodule({span of}T)"
  and "T\<subseteq>{span of}T"
proof-
  have "id(T):T\<rightarrow>T" unfolding id_def by auto
  then have idG:"id(T):T\<rightarrow>\<M>" using assms func1_1_L1B by auto
  {
    assume A:"T=0"
    from A assms have eq:"({span of}T)={\<Theta>}" using Span_def by auto
    have "\<forall>r\<in>R. r\<cdot>\<^sub>S\<Theta>=\<Theta>" using zero_fixed by auto
    with eq have "\<forall>r\<in>R. \<forall>g\<in>({span of}T). r\<cdot>\<^sub>Sg\<in>({span of}T)" by auto moreover
    from eq have "IsAsubgroup(({span of}T),A\<^sub>M)" using mod_ab_gr.trivial_normal_subgroup
      unfolding IsAnormalSubgroup_def by auto
    ultimately have "IsAsubmodule({span of}T)" unfolding IsAsubmodule_def by auto
    with A have "IsAsubmodule({span of}T)" "T\<subseteq>{span of}T" by auto
  }
  moreover
  {
    assume A:"T\<noteq>0"
    {
      fix t assume asT:"t\<in>T"
      then have "Finite({t})" by auto
      with asT have FP:"{t}\<in>FinPow(T)" unfolding FinPow_def by auto moreover
      from asT have Af:"{\<langle>t,\<one>\<rangle>}\<union>{\<langle>r,\<zero>\<rangle>. r\<in>T-{t}}:T\<rightarrow>R" unfolding Pi_def function_def using
        Ring_ZF_1_L2(1,2) by auto moreover
      {
        fix m assume "m\<in>T-{t}"
        with Af have "({\<langle>t,\<one>\<rangle>}\<union>{\<langle>r,\<zero>\<rangle>. r\<in>T-{t}})`m=\<zero>" using apply_equality by auto
      }
      ultimately have "\<Sum>[{t};{{\<langle>t,\<one>\<rangle>}\<union>{\<langle>r,\<zero>\<rangle>. r\<in>T-{t}},id(T)}]\<in>{span of}T" unfolding Span_def[OF assms(1)] using A
        by auto
      then have "(({\<langle>t,\<one>\<rangle>}\<union>{\<langle>r,\<zero>\<rangle>. r\<in>T-{t}})`t) \<cdot>\<^sub>S (id(T)`t) \<in>{span of}T" using linComb_one_element[OF asT
        Af idG] by auto
      then have "(({\<langle>t,\<one>\<rangle>}\<union>{\<langle>r,\<zero>\<rangle>. r\<in>T-{t}})`t) \<cdot>\<^sub>S t \<in>{span of}T" using asT by auto
      then have "(\<one>) \<cdot>\<^sub>S t \<in>{span of}T" using apply_equality Af by auto moreover
      have "(\<one>) \<cdot>\<^sub>S t=t" using module_ax4 assms asT by auto ultimately
      have "t\<in>{span of}T" by auto
    }
    then have "T\<subseteq>{span of}T" by auto moreover
    with A have "({span of}T)\<noteq>0" by auto moreover
    {
      fix l assume "l\<in>{span of}T"
      with A obtain S AA where l:"l=\<Sum>[S;{AA,id(T)}]" "S\<in>FinPow(T)" "AA:T\<rightarrow>R" "\<forall>m\<in>T-S. AA`m=\<zero>" unfolding Span_def[OF assms(1)]
        by auto
      from l(1) have "l\<in>\<M>" using linComb_is_in_module[OF l(3) _ l(2), of "id(T)"] idG unfolding FinPow_def by auto
    }
    then have sub:"({span of}T)\<subseteq>\<M>" by force moreover
    {
      fix T1 T2 assume as:"T1\<in>{span of}T"
        "T2\<in>{span of}T"
      with A obtain TT1 AA1 TT2 AA2 where T:"TT1\<in>FinPow(T)" "TT2\<in>FinPow(T)" "AA1:T\<rightarrow>R"
        "AA2:T\<rightarrow>R" "T1=\<Sum>[TT1;{AA1,id(T)}]" "T2=\<Sum>[TT2;{AA2,id(T)}]" "\<forall>m\<in>T-TT1. AA1`m=\<zero>" "\<forall>m\<in>T-TT2. AA2`m=\<zero>" unfolding Span_def[OF assms(1)] by auto
      {
        assume A:"TT1=0"
        then have "T1=\<Sum>[0;{AA1,id(T)}]" using T(5) by auto
        also have "\<dots>=\<Theta>" using LinearComb_def[OF T(3) idG T(1)] A by auto
        ultimately have "T1+\<^sub>VT2=\<Theta>+\<^sub>VT2" by auto
        also have "\<dots>\<in>{span of}T" using sub as(2) mod_ab_gr.group0_2_L2 by auto
        ultimately have "T1+\<^sub>VT2\<in>{span of}T" by auto
      }
      moreover
      {
        assume AA:"TT1\<noteq>0"
        have "T1+\<^sub>VT2=\<Sum>[TT1+TT2;{{\<langle>\<langle>0,x\<rangle>,AA1`x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,AA2`x\<rangle>. x\<in>T},{\<langle>\<langle>0,x\<rangle>,id(T)`x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,id(T)`x\<rangle>. x\<in>T}}]" using linComb_sum[OF T(3,4) idG idG 
          AA T(1,2)] T(5,6) by auto
        also have "\<dots>=\<Sum>[TT1+TT2;{{\<langle>\<langle>0,x\<rangle>,AA1`x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,AA2`x\<rangle>. x\<in>T},{\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T}}]" by auto
        ultimately have eq:"T1+\<^sub>VT2=\<Sum>[TT1+TT2;{{\<langle>\<langle>0,x\<rangle>,AA1`x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,AA2`x\<rangle>. x\<in>T},{\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T}}]" by auto
        from T(1,2) obtain n1 n2 where fin:"TT1\<approx>n1" "n1\<in>nat" "TT2\<approx>n2" "n2\<in>nat" unfolding FinPow_def Finite_def by auto
        then have "n1+n2\<approx>n1#+n2" using nat_sum_eqpoll_sum by auto moreover
        with fin(1,3) have "TT1+TT2\<approx>n1#+n2" using sum_eqpoll_cong[] eqpoll_trans[of "TT1+TT2" "n1+n2" "n1#+n2"] by auto
        then have "Finite(TT1+TT2)" unfolding Finite_def using add_type by auto
        then have fin:"TT1+TT2\<in>FinPow(T+T)" using T(1,2) unfolding FinPow_def by auto moreover
        have f1:"{\<langle>\<langle>0, x\<rangle>, AA1 ` x\<rangle> . x \<in> T}:{0}\<times>T\<rightarrow>R" using apply_type[OF T(3)] unfolding Pi_def function_def by auto
        have f2:"{\<langle>\<langle>1, x\<rangle>, AA2 ` x\<rangle> . x \<in> T}:{1}\<times>T\<rightarrow>R" using apply_type[OF T(4)] unfolding Pi_def function_def by auto
        have "({0}\<times>T)\<inter>({1}\<times>T)=0" by auto
        then have ffA:"({\<langle>\<langle>0, x\<rangle>, AA1 ` x\<rangle> . x \<in> T} \<union> {\<langle>\<langle>1, x\<rangle>, AA2 ` x\<rangle> . x \<in> T}):T+T\<rightarrow>R" unfolding sum_def using fun_disjoint_Un[OF f1 f2] by auto moreover
        have f1:"{\<langle>\<langle>0, x\<rangle>, x\<rangle> . x \<in> T}:{0}\<times>T\<rightarrow>\<M>" using assms unfolding Pi_def function_def by blast
        have f2:"{\<langle>\<langle>1, x\<rangle>, x\<rangle> . x \<in> T}:{1}\<times>T\<rightarrow>\<M>" using assms unfolding Pi_def function_def by blast
        have f1T:"{\<langle>\<langle>0, x\<rangle>, x\<rangle> . x \<in> T}:{0}\<times>T\<rightarrow>T" using assms unfolding Pi_def function_def by blast
        have f2T:"{\<langle>\<langle>1, x\<rangle>, x\<rangle> . x \<in> T}:{1}\<times>T\<rightarrow>T" using assms unfolding Pi_def function_def by blast
        have "({0}\<times>T)\<inter>({1}\<times>T)=0" by auto
        then have ffB:"({\<langle>\<langle>0, x\<rangle>, x\<rangle> . x \<in> T} \<union> {\<langle>\<langle>1, x\<rangle>, x\<rangle> . x \<in>T}):T+T\<rightarrow>\<M>" and ffBT:"({\<langle>\<langle>0, x\<rangle>, x\<rangle> . x \<in> T} \<union> {\<langle>\<langle>1, x\<rangle>, x\<rangle> . x \<in>T}):T+T\<rightarrow>T" unfolding sum_def using fun_disjoint_Un[OF f1 f2]
          using fun_disjoint_Un[OF f1T f2T] by auto
        obtain AA where AA:"\<Sum>[TT1+TT2;{{\<langle>\<langle>0,x\<rangle>,AA1`x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,AA2`x\<rangle>. x\<in>T},{\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T}}]=
          \<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{AA,id(\<M>)}]" "AA:\<M>\<rightarrow>R" "\<forall>x\<in>\<M>-({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2). AA`x=\<zero>" 
          using index_module[OF ffA ffB fin] by auto
        from ffBT have sub:"({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)\<subseteq>T" using func1_1_L6(2) by auto
        then have finpow:"({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)\<in>FinPow(T)" using fin Finite_RepFun[of "TT1+TT2" "\<lambda>t. ({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})`t"] 
          func_imagedef[OF ffBT, of "TT1+TT2"] unfolding FinPow_def by auto
        {
          fix R T assume "R\<in>Pow(T)"
          then have "id(R)\<subseteq>R*T" using func1_1_L1B[OF id_type] by auto
          then have "id(R)=restrict(id(T),R)" using right_comp_id_any[of "id(T)"] using left_comp_id[of "id(R)" R T] by force
        }
        then have reg:"\<forall>T. \<forall>R\<in>Pow(T). id(R)=restrict(id(T),R)" by blast
        then have "\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,T),id(T)}]=
          \<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(restrict(AA,T),({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)),id(({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2))}]"
          using linComb_restrict_coord[OF restrict_fun[OF AA(2) assms] func1_1_L1B[OF id_type assms] finpow] sub by auto moreover
        from sub have " T \<inter> ({\<langle>\<langle>0, x\<rangle>, x\<rangle> . x \<in> T} \<union> {\<langle>\<langle>1, x\<rangle>, x\<rangle> . x \<in> T}) `` (TT1 + TT2)=({\<langle>\<langle>0, x\<rangle>, x\<rangle> . x \<in> T} \<union> {\<langle>\<langle>1, x\<rangle>, x\<rangle> . x \<in> T}) `` (TT1 + TT2)" by auto
        then have "restrict(restrict(AA,T),({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2))=restrict(AA,({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2))"
          using restrict_restrict[of AA T "({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)"] by auto
        ultimately have "\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,T),id(T)}]=
          \<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)),id(({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2))}]" by auto
        moreover have "({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)\<subseteq>\<M>" using sub assms by auto
        with reg have "id(({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2))=restrict(id(\<M>),({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2))" by auto
        ultimately have "\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,T),id(T)}]=
          \<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)),restrict(id(\<M>),({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2))}]"
          by auto
        also have "\<dots>=\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{AA,id(\<M>)}]" using linComb_restrict_coord[OF AA(2) id_type, of "({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)"] 
          finpow unfolding FinPow_def using assms by force
        ultimately have eq1:"\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,T),id(T)}]=
          \<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{AA,id(\<M>)}]" by auto
        have "restrict(AA,T):T\<rightarrow>R" using restrict_fun[OF AA(2) assms]. moreover
        note finpow moreover
        {
          fix x assume x:"x\<in>T-({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)"
          with assms have "x\<in>\<M>-({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)" by auto
          with AA(3) have "AA`x=\<zero>" by auto
          with x have "restrict(AA,T)`x=\<zero>" using restrict by auto
        }
        then have "\<forall>x\<in>T-({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2). restrict(AA,T)`x=\<zero>" by auto ultimately
        have "\<langle>({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2),restrict(AA,T)\<rangle>\<in>{\<langle>F,E\<rangle>\<in>FinPow(T)\<times>(T\<rightarrow>R). \<forall>x\<in>T-F. E`x=\<zero>}" by auto
        then have "\<exists>F\<in>FinPow(T). \<exists>E\<in>T\<rightarrow>R. (\<forall>x\<in>T-F. E`x=\<zero>) \<and> (\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,T),id(T)}]=\<Sum>[F;{E,id(T)}])"
          using exI[of "\<lambda>F. F\<in>FinPow(T) \<and> (\<exists>E\<in>T\<rightarrow>R. (\<forall>x\<in>T-F. E`x=\<zero>) \<and> (\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,T),id(T)}]=\<Sum>[F;{E,id(T)}]))" "({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)"]
          exI[of "\<lambda>E. E\<in>T\<rightarrow>R \<and> ((\<forall>x\<in>T-(({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2)). E`x=\<zero>) \<and> (\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,T),id(T)}]=\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{E,id(T)}]))"
            "restrict(AA,T)"] by auto
        then have "\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{restrict(AA,T),id(T)}]\<in>{\<Sum>[FF;{AA,id(T)}]. 
          \<langle>FF,AA\<rangle> \<in> {\<langle>F,E\<rangle>\<in>FinPow(T)\<times>(T\<rightarrow>R). \<forall>x\<in>T-F. E`x=\<zero>}}" by auto
        with eq1 have "\<Sum>[({\<langle>\<langle>0,x\<rangle>,x\<rangle>. x\<in>T}\<union>{\<langle>\<langle>1,x\<rangle>,x\<rangle>. x\<in>T})``(TT1+TT2);{AA,id(\<M>)}]\<in>{span of}T" using A unfolding Span_def[OF assms]
          by auto
        with AA(1) eq have "T1+\<^sub>VT2\<in>{span of}T" by auto
      }
      ultimately have "T1+\<^sub>VT2\<in>{span of}T" by auto
    }
    then have "\<forall>x\<in>{span of}T. \<forall>y\<in>{span of}T. x+\<^sub>Vy\<in>{span of}T" by blast
    then have "({span of}T){is closed under}A\<^sub>M"  unfolding IsOpClosed_def by auto moreover
    {
      fix r TT assume "r\<in>R" "TT\<in>{span of}T"
      with A obtain n AA where T:"r\<in>R" "TT=\<Sum>[n;{AA,id(T)}]" "n\<in>FinPow(T)" "AA:T\<rightarrow>R" "\<forall>x\<in>T-n. AA`x=\<zero>"
        unfolding Span_def[OF assms(1)] by auto
      have "r\<cdot>\<^sub>S(TT)=\<Sum>[n;{{\<langle>t,r\<cdot>(AA`t)\<rangle>.t\<in>T},id(T)}]" using linComb_action(1)[OF T(4) _ T(1) T(3), of "id(T)"] T(2)
        func1_1_L1B[OF id_type assms] by auto moreover
      have fun:"{\<langle>t,r\<cdot>(AA`t)\<rangle>.t\<in>T}:T\<rightarrow>R" using linComb_action(2)[OF T(4) _ T(1,3)] func1_1_L1B[OF id_type assms] by auto
        moreover
      {
        fix z assume z:"z\<in>T-n"
        then have "{\<langle>t,r\<cdot>(AA`t)\<rangle>.t\<in>T}`z=r\<cdot>(AA`z)" using apply_equality[of z "r\<cdot>(AA`z)"
          "{\<langle>t,r\<cdot>(AA`t)\<rangle>.t\<in>T}" T "\<lambda>t. R"] using fun by auto
        also have "\<dots>=r\<cdot>\<zero>" using T(5) z by auto
        also have "\<dots>=\<zero>" using Ring_ZF_1_L6(2)[OF T(1)] by auto
        ultimately have "{\<langle>t,r\<cdot>(AA`t)\<rangle>.t\<in>T}`z=\<zero>" by auto
      }
      then have "\<forall>z\<in>T-n. {\<langle>t,r\<cdot>(AA`t)\<rangle>.t\<in>T}`z=\<zero>" by auto ultimately
      have "r\<cdot>\<^sub>S(TT)\<in>{span of}T" unfolding Span_def[OF assms(1)] using A T(3) by auto
    }
    then have "\<forall>r\<in>R. \<forall>TT\<in>{span of}T. r\<cdot>\<^sub>S(TT)\<in>{span of}T" by blast
    ultimately have "IsAsubmodule({span of}T)" "T\<subseteq>({span of}T)" using submoduleI by auto
  }
  ultimately show "IsAsubmodule({span of}T)" "T\<subseteq>({span of}T)" by auto
qed


text\<open>Given a linear combination, it is in the span of the image of the second function.\<close>

lemma (in module0) linear_comb_span:
  assumes "AA:X\<rightarrow>R" "B:X\<rightarrow>\<M>" "D\<in>FinPow(X)"
  shows "\<Sum>[D;{AA,B}]\<in>({span of}(B``D))"
proof-
  {
    assume A:"B``D=0"
    {
      assume "D\<noteq>0"
      then obtain d where "d\<in>D" by auto
      then have "B`d\<in>B``D" using image_fun[OF assms(2)] assms(3) unfolding FinPow_def by auto
      with A have "False" by auto
    }
    then have "D=0" by auto
    then have "\<Sum>[D;{AA,B}]=\<Theta>" using LinearComb_def[OF assms] by auto moreover
    with A have ?thesis using Span_def by auto
  }
  moreover
  {
    assume A:"B``D\<noteq>0"
    have sub:"B``D\<subseteq>\<M>" using assms(2) func1_1_L6(2) by auto
    from assms obtain AB where AA:"\<Sum>[D;{AA,B}]=\<Sum>[B``D;{AB,id(\<M>)}]" "AB:\<M>\<rightarrow>R" "\<forall>x\<in>\<M>-B``D. AB`x=\<zero>"
      using index_module by blast
    have fin:"Finite(B``D)" using func_imagedef[OF assms(2)] assms(3) unfolding FinPow_def
      using Finite_RepFun[of D "\<lambda>t. B`t"] by auto
    with sub have finpow:"B``D\<in>FinPow(\<M>)" unfolding FinPow_def by auto
    with AA(1) have "\<Sum>[D;{AA,B}]=\<Sum>[B``D;{restrict(AB,B``D),restrict(id(\<M>),B``D)}]"
      using linComb_restrict_coord AA(2) id_type by auto
    moreover have "restrict(id(\<M>),B``D)=id(\<M>) O id(B``D)" using right_comp_id_any by auto
    then have "restrict(id(\<M>),B``D)=id(B``D)" using left_comp_id[of "id(B``D)"] sub by auto
    ultimately have "\<Sum>[D;{AA,B}]=\<Sum>[B``D;{restrict(AB,B``D),id(B``D)}]" by auto moreover
    have "restrict(AB,B``D):B``D\<rightarrow>R" using AA(2) restrict_fun sub by auto moreover
    have "\<forall>x\<in>B``D-B``D. restrict(AB,B``D)`x=\<zero>\<^sub>R" by auto ultimately
    have "\<Sum>[D;{AA,B}]\<in>{span of}(B``D)" using fin A unfolding Span_def[OF sub] FinPow_def by auto
  }
  ultimately show ?thesis by blast
qed

text\<open>It turns out that the span is the smallest submodule that contains the
original set.\<close>

theorem(in module0) minimal_submodule:
  assumes "T\<subseteq>\<N>" "IsAsubmodule(\<N>)"
  shows "({span of}T)\<subseteq>\<N>"
proof-
  have as:"T\<subseteq>\<M>" using assms(1) mod_ab_gr.group0_3_L2[OF sumodule_is_subgroup[OF assms(2)]] by auto 
  {
    assume A:"T=0"
    {
      fix x assume "x\<in>{span of}T"
      with A have "x=\<Theta>" using Span_def[OF as] by auto
      then have "x\<in>\<N>" using assms(2) unfolding IsAsubmodule_def
        using mod_ab_gr.group0_3_L5 by auto
    }
    then have "({span of}T)\<subseteq>\<N>" by auto
  }
  moreover
  {
    assume A:"T\<noteq>0"
    {
      fix x assume "x\<in>{span of}T"
      with A obtain n AA where "x=\<Sum>[n;{AA,id(T)}]" "n\<in>FinPow(T)" "AA:T\<rightarrow>R"
        unfolding Span_def[OF as] by auto
      then have x:"x=\<Sum>[n;{AA,id(T)}]" "n\<in>FinPow(T)" "AA:T\<rightarrow>R" "id(T):T\<rightarrow>\<N>"
        using assms(1) func1_1_L1B id_type[of T] by auto
      then have "x\<in>\<N>" using linear_comb_submod assms(2) by auto
    }
    then have "({span of}T)\<subseteq>\<N>" by auto
  }
  ultimately show "({span of}T)\<subseteq>\<N>" by auto
qed

end