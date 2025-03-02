(*
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2025  Slawomir Kolodynski

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

section \<open>Finite choice and order relations\<close>

theory FinOrd_ZF_1 imports FinOrd_ZF Cardinal_ZF

begin

text\<open>In this theory we continue the subject of finite sets and order relation 
  from \<open>FinOrd_ZF\<close> with some consequences of finite choice for down-directed sets. \<close>

subsection\<open>Finte choice and preorders\<close>

text\<open>In the \<open>Order_ZF\<close> theory we define what it means that a relation $r$ down-directs a set $X$:
  each two elements of $X$ have a common lower bound in $X$. If the relation is a preorder 
  (i.e. is reflexive and transitive) and it down-directs $X$ we say that $X$ is a down-directed
  set (by the relation $r$). \<close>

text\<open>The next lemma states that each finite subset of a down-directed set 
  has a lower bound in $X$.\<close>

lemma fin_dir_set_bounded: 
  assumes "IsDownDirectedSet(X,r)" and "B\<in>FinPow(X)"
  shows "\<exists>x\<in>X.\<forall>t\<in>B. \<langle>x,t\<rangle>\<in>r"
proof -  
  from assms(1) have "\<exists>x\<in>X.\<forall>t\<in>\<emptyset>. \<langle>x,t\<rangle>\<in>r"
    unfolding IsDownDirectedSet_def DownDirects_def by auto
  moreover have 
    "\<forall>A\<in>FinPow(X). (\<exists>x\<in>X.\<forall>t\<in>A. \<langle>x,t\<rangle>\<in>r)\<longrightarrow>(\<forall>a\<in>X. \<exists>m\<in>X.\<forall>t\<in>A\<union>{a}. \<langle>m,t\<rangle>\<in>r)"
  proof -
    { fix A assume "A\<in>FinPow(X)" and I: "\<exists>x\<in>X.\<forall>t\<in>A. \<langle>x,t\<rangle>\<in>r"
      { fix a assume "a\<in>X"
        from I obtain x where "x\<in>X" and II: "\<forall>t\<in>A. \<langle>x,t\<rangle>\<in>r" by auto
        from assms(1) \<open>a\<in>X\<close> \<open>x\<in>X\<close> obtain m where 
          "m\<in>X" "\<langle>m,a\<rangle>\<in>r" "\<langle>m,x\<rangle>\<in>r"
          unfolding IsDownDirectedSet_def DownDirects_def by auto
        with assms(1) II have "\<exists>m\<in>X.\<forall>t\<in>A\<union>{a}. \<langle>m,t\<rangle>\<in>r"
          unfolding IsDownDirectedSet_def IsPreorder_def trans_def 
            by blast
      } hence "\<forall>a\<in>X. \<exists>x\<in>X.\<forall>t\<in>A\<union>{a}. \<langle>x,t\<rangle>\<in>r" by blast
    } thus ?thesis by simp
  qed
  moreover note assms(2)
  ultimately show ?thesis by (rule FinPow_induct)
qed

text\<open>Suppose $Y$ is a set down-directed by a (preorder) relation $r$
  and $f,g$ are funtions defined on two finite subsets $A,B$, resp., of $X$, valued in Y 
  (i.e.$f:A\rightarrow Y$, $f:B\rightarrow Y$ and $A,B$ are finite subsets of $X$). 
  Then there exist a function $h:A\cup B\rightarrow Y$ that is a lower bound for 
  $f$ on $A$ and for $g$ on $B$.\<close>

lemma two_fun_low_bound: 
  assumes "IsDownDirectedSet(Y,r)" "A\<in>FinPow(X)" "B\<in>FinPow(X)" "f:A\<rightarrow>Y" "g:B\<rightarrow>Y"
  shows "\<exists>h\<in>A\<union>B\<rightarrow>Y. (\<forall>x\<in>A. \<langle>h`(x),f`(x)\<rangle>\<in>r) \<and> (\<forall>x\<in>B. \<langle>h`(x),g`(x)\<rangle>\<in>r)"
proof -
  from assms(2,3) have "Finite(A\<union>B)" using union_finpow 
    unfolding FinPow_def by simp
  { fix x assume "x\<in>A\<union>B"
    from assms(4,5) have "f``{x}\<union>g``{x} \<in> FinPow(Y)"
      using image_singleton_fin union_finpow by simp
    with assms(1) have "\<exists>y\<in>Y.\<forall>t\<in>(f``{x}\<union>g``{x}). \<langle>y,t\<rangle>\<in>r"
      using fin_dir_set_bounded by simp
  } hence "\<forall>x\<in>A\<union>B. \<exists>y\<in>Y.\<forall>t\<in>(f``{x}\<union>g``{x}). \<langle>y,t\<rangle>\<in>r" by auto
  with \<open>Finite(A\<union>B)\<close> have 
    "\<exists>h\<in>A\<union>B\<rightarrow>Y. \<forall>x\<in>A\<union>B. \<forall>t\<in>(f``{x}\<union>g``{x}). \<langle>h`(x),t\<rangle>\<in>r"
    by (rule finite_choice_fun)
  then obtain h where "h\<in>A\<union>B\<rightarrow>Y" and 
    "\<forall>x\<in>A\<union>B. \<forall>t\<in>(f``{x}\<union>g``{x}). \<langle>h`(x),t\<rangle>\<in>r"
    by auto
  with assms(4,5) have 
    "\<forall>x\<in>A. \<langle>h`(x),f`(x)\<rangle>\<in>r" and "\<forall>x\<in>B. \<langle>h`(x),g`(x)\<rangle>\<in>r"
    using func_imagedef by simp_all
  with \<open>h\<in>A\<union>B\<rightarrow>Y\<close> show ?thesis by auto
qed

end