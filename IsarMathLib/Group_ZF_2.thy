(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar (ZF logic).

    Copyright (C) 2005, 2006  Slawomir Kolodynski

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
INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY 
AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. 
IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, 
EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, 
PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; 
OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, 
WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) 
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, 
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)
section \<open>Groups 2\<close>

theory Group_ZF_2 imports AbelianGroup_ZF func_ZF EquivClass1

begin

text\<open>This theory continues Group\_ZF.thy and considers lifting the group 
  structure to function spaces and projecting the group structure to 
  quotient spaces, in particular the quotient qroup.\<close>

subsection\<open>Lifting groups to function spaces\<close>

text\<open>If we have a monoid (group) $G$ than we get a monoid (group) 
  structure on a space of functions valued in 
  in $G$ by defining $(f\cdot g)(x) := f(x)\cdot g(x)$. 
  We call this process ''lifting the monoid (group) to function space''.
  This section formalizes this lifting.\<close>

text\<open>The lifted operation is an operation on the function space.\<close>

lemma (in monoid0) Group_ZF_2_1_L0A:
  assumes A1: "F = f {lifted to function space over} X"
  shows "F : (X\<rightarrow>G)\<times>(X\<rightarrow>G)\<rightarrow>(X\<rightarrow>G)"
proof -
  from monoidAsssum have "f : G\<times>G\<rightarrow>G"
    using IsAmonoid_def IsAssociative_def by simp
  with A1 show ?thesis
    using func_ZF_1_L3 group0_1_L3B by auto
qed

text\<open>The result of the lifted operation is in the function space.\<close>

lemma (in monoid0) Group_ZF_2_1_L0: 
  assumes A1:"F = f {lifted to function space over} X"
  and A2:"s:X\<rightarrow>G" "r:X\<rightarrow>G"
  shows "F`\<langle> s,r\<rangle> : X\<rightarrow>G"
proof -
  from A1 have "F : (X\<rightarrow>G)\<times>(X\<rightarrow>G)\<rightarrow>(X\<rightarrow>G)"
    using Group_ZF_2_1_L0A
    by simp
  with A2 show ?thesis using apply_funtype
    by simp
qed
    
text\<open>The lifted monoid operation has a neutral element, namely
  the constant function with the neutral element as the value.\<close>

lemma (in monoid0) Group_ZF_2_1_L1: 
  assumes A1: "F = f {lifted to function space over} X"
  and A2: "E = ConstantFunction(X,TheNeutralElement(G,f))"
  shows "E : X\<rightarrow>G \<and> (\<forall>s\<in>X\<rightarrow>G. F`\<langle> E,s\<rangle> = s \<and> F`\<langle> s,E\<rangle> = s)"
proof
  from A2 show T1:"E : X\<rightarrow>G"
    using unit_is_neutral func1_3_L1 by simp
  show "\<forall>s\<in>X\<rightarrow>G. F`\<langle> E,s\<rangle> = s \<and> F`\<langle> s,E\<rangle> = s"
  proof
    fix s assume A3:"s:X\<rightarrow>G"
    from monoidAsssum have T2:"f : G\<times>G\<rightarrow>G"
      using IsAmonoid_def IsAssociative_def by simp
    from A3 A1 T1 have 
      "F`\<langle> E,s\<rangle> : X\<rightarrow>G" "F`\<langle> s,E\<rangle> : X\<rightarrow>G" "s : X\<rightarrow>G"
      using Group_ZF_2_1_L0 by auto
    moreover from T2 A1 T1 A2 A3 have
      "\<forall>x\<in>X. (F`\<langle> E,s\<rangle>)`(x) = s`(x)"
      "\<forall>x\<in>X. (F`\<langle> s,E\<rangle>)`(x) = s`(x)"
      using func_ZF_1_L4 group0_1_L3B func1_3_L2 
	apply_type unit_is_neutral by auto
    ultimately show 
      "F`\<langle> E,s\<rangle> = s \<and> F`\<langle> s,E\<rangle> = s"
      using fun_extension_iff by auto
  qed
qed

text\<open>Monoids can be lifted to a function space.\<close>

lemma (in monoid0) Group_ZF_2_1_T1: 
  assumes A1: "F = f {lifted to function space over} X"
  shows "IsAmonoid(X\<rightarrow>G,F)"
proof -
  from monoidAsssum A1 have 
    "F {is associative on} (X\<rightarrow>G)"
    using IsAmonoid_def func_ZF_2_L4 group0_1_L3B
    by auto
  moreover from A1 have 
    "\<exists> E \<in> X\<rightarrow>G. \<forall>s \<in> X\<rightarrow>G. F`\<langle> E,s\<rangle> = s \<and> F`\<langle> s,E\<rangle> = s"
    using Group_ZF_2_1_L1 by blast
  ultimately show ?thesis using IsAmonoid_def
    by simp
qed

text\<open>The constant function with the neutral element as the value is the
  neutral element of the lifted monoid.\<close>

lemma Group_ZF_2_1_L2:
  assumes A1: "IsAmonoid(G,f)"
  and A2: "F = f {lifted to function space over} X"
  and A3: "E = ConstantFunction(X,TheNeutralElement(G,f))"
  shows "E = TheNeutralElement(X\<rightarrow>G,F)"
proof - 
  from A1 A2 have 
     T1:"monoid0(G,f)" and T2:"monoid0(X\<rightarrow>G,F)"
    using monoid0_def monoid0.Group_ZF_2_1_T1
    by auto
  from T1 A2 A3 have 
    "E : X\<rightarrow>G \<and> (\<forall>s\<in>X\<rightarrow>G. F`\<langle> E,s\<rangle> = s \<and> F`\<langle> s,E\<rangle> = s)"
    using monoid0.Group_ZF_2_1_L1 by simp
  with T2 show ?thesis
    using monoid0.group0_1_L4 by auto
qed

text\<open>The lifted operation acts on the functions in a natural way defined
  by the monoid operation.\<close>

lemma (in monoid0) lifted_val:
  assumes "F = f {lifted to function space over} X"
  and "s:X\<rightarrow>G"  "r:X\<rightarrow>G"
  and "x\<in>X"
  shows "(F`\<langle>s,r\<rangle>)`(x) = s`(x) \<oplus> r`(x)"
  using monoidAsssum assms IsAmonoid_def IsAssociative_def
      group0_1_L3B func_ZF_1_L4
  by auto

text\<open>The lifted operation acts on the functions in a natural way defined
  by the group operation. This is the same as \<open>lifted_val\<close>, but
  in the \<open>group0\<close> context.\<close>

lemma (in group0) Group_ZF_2_1_L3:
  assumes "F = P {lifted to function space over} X"
  and "s:X\<rightarrow>G" "r:X\<rightarrow>G"
  and "x\<in>X"
  shows "(F`\<langle>s,r\<rangle>)`(x) = s`(x)\<cdot>r`(x)"
  using assms group0_2_L1 monoid0.lifted_val by simp
    
text\<open>In the group0 context we can apply theorems proven in monoid0 context
  to the lifted monoid.\<close>

lemma (in group0) Group_ZF_2_1_L4:
  assumes A1: "F = P {lifted to function space over} X"
  shows "monoid0(X\<rightarrow>G,F)"
proof -
  from A1 show ?thesis
    using group0_2_L1 monoid0.Group_ZF_2_1_T1 monoid0_def
    by simp
qed

text\<open>The compostion of a function $f:X\rightarrow G$ with the group inverse
  is a right inverse for the lifted group.\<close>

lemma (in group0) Group_ZF_2_1_L5: 
  assumes A1: "F = P {lifted to function space over} X"
  and A2: "s : X\<rightarrow>G"
  and A3: "i = GroupInv(G,P) O s"
  shows "i: X\<rightarrow>G" and "F`\<langle> s,i\<rangle> = TheNeutralElement(X\<rightarrow>G,F)"
proof -
  let ?E = "ConstantFunction(X,\<one>)"
  have "?E : X\<rightarrow>G" 
    using group0_2_L2 func1_3_L1 by simp
  moreover from groupAssum A2 A3 A1 have
    "F`\<langle> s,i\<rangle> :  X\<rightarrow>G" using group0_2_T2 comp_fun 
      Group_ZF_2_1_L4 monoid0.group0_1_L1
    by simp
  moreover from groupAssum A2 A3 A1 have 
    "\<forall>x\<in>X. (F`\<langle> s,i\<rangle>)`(x) = ?E`(x)"
    using group0_2_T2 comp_fun Group_ZF_2_1_L3 
      comp_fun_apply apply_funtype group0_2_L6 func1_3_L2
    by simp
  moreover from groupAssum A1 have
    "?E = TheNeutralElement(X\<rightarrow>G,F)"
    using IsAgroup_def Group_ZF_2_1_L2 by simp
  ultimately show "F`\<langle> s,i\<rangle> = TheNeutralElement(X\<rightarrow>G,F)"
    using fun_extension_iff IsAgroup_def Group_ZF_2_1_L2
    by simp
  from groupAssum A2 A3 show "i: X\<rightarrow>G" 
    using group0_2_T2 comp_fun by simp
qed

text\<open>Groups can be lifted to the function space.\<close>

theorem (in group0) Group_ZF_2_1_T2:
  assumes A1: "F = P {lifted to function space over} X"
  shows "IsAgroup(X\<rightarrow>G,F)"
proof -
  from A1 have "IsAmonoid(X\<rightarrow>G,F)"
    using group0_2_L1 monoid0.Group_ZF_2_1_T1
    by simp
  moreover have 
    "\<forall>s\<in>X\<rightarrow>G. \<exists>i\<in>X\<rightarrow>G. F`\<langle> s,i\<rangle> = TheNeutralElement(X\<rightarrow>G,F)"
  proof
    fix s assume A2: "s : X\<rightarrow>G"
    let ?i = "GroupInv(G,P) O s"
    from groupAssum A2 have "?i:X\<rightarrow>G"
      using group0_2_T2 comp_fun by simp
    moreover from A1 A2 have 
      "F`\<langle> s,?i\<rangle> = TheNeutralElement(X\<rightarrow>G,F)"
      using Group_ZF_2_1_L5 by fast
   ultimately show "\<exists>i\<in>X\<rightarrow>G. F`\<langle> s,i\<rangle> = TheNeutralElement(X\<rightarrow>G,F)" 
      by auto
  qed
  ultimately show ?thesis using IsAgroup_def
    by simp
qed

text\<open>What is the group inverse for the lifted group?\<close>

lemma (in group0) Group_ZF_2_1_L6: 
  assumes A1: "F = P {lifted to function space over} X"
  shows "\<forall>s\<in>(X\<rightarrow>G). GroupInv(X\<rightarrow>G,F)`(s) = GroupInv(G,P) O s"
proof -
  from A1 have  "group0(X\<rightarrow>G,F)"
    using group0_def Group_ZF_2_1_T2 
    by simp
  moreover from A1 have "\<forall>s\<in>X\<rightarrow>G. GroupInv(G,P) O s : X\<rightarrow>G \<and> 
    F`\<langle> s,GroupInv(G,P) O s\<rangle> = TheNeutralElement(X\<rightarrow>G,F)"
    using Group_ZF_2_1_L5 by simp
  ultimately have 
    "\<forall>s\<in>(X\<rightarrow>G).  GroupInv(G,P) O s = GroupInv(X\<rightarrow>G,F)`(s)"
    by (rule group0.group0_2_L9A)
  thus ?thesis by simp
qed

text\<open>What is the value of the group inverse for the lifted group?\<close>

corollary (in group0) lift_gr_inv_val:  
  assumes "F = P {lifted to function space over} X" and
  "s : X\<rightarrow>G" and "x\<in>X"
  shows  "(GroupInv(X\<rightarrow>G,F)`(s))`(x) = (s`(x))\<inverse>"
  using groupAssum assms Group_ZF_2_1_L6 group0_2_T2 comp_fun_apply
  by simp

text\<open>What is the group inverse in a subgroup of the lifted group?\<close>

lemma (in group0) Group_ZF_2_1_L6A:
  assumes A1: "F = P {lifted to function space over} X"
  and A2: "IsAsubgroup(H,F)"
  and A3: "g = restrict(F,H\<times>H)"
  and A4: "s\<in>H"
  shows "GroupInv(H,g)`(s) = GroupInv(G,P) O s"
proof -
  from A1 have T1: "group0(X\<rightarrow>G,F)"
    using group0_def Group_ZF_2_1_T2 
    by simp
  with A2 A3 A4 have "GroupInv(H,g)`(s) = GroupInv(X\<rightarrow>G,F)`(s)"
    using group0.group0_3_T1 restrict by simp
  moreover from T1 A1 A2 A4 have
    "GroupInv(X\<rightarrow>G,F)`(s) = GroupInv(G,P) O s"
    using group0.group0_3_L2 Group_ZF_2_1_L6 by blast
  ultimately show ?thesis by simp
qed

text\<open>If a group is abelian, then its lift to a function space is also 
  abelian.\<close>

lemma (in group0) Group_ZF_2_1_L7: 
  assumes A1: "F = P {lifted to function space over} X"
  and A2: "P {is commutative on} G"
  shows "F {is commutative on} (X\<rightarrow>G)"
proof-
  from A1 A2  have
    "F {is commutative on} (X\<rightarrow>range(P))"
    using group_oper_fun func_ZF_2_L2
    by simp
  moreover from groupAssum have "range(P) = G"
    using group0_2_L1 monoid0.group0_1_L3B
    by simp
  ultimately show ?thesis by simp
qed
    
subsection\<open>Equivalence relations on groups\<close>

text\<open>The goal of this section is to establish that (under some conditions) 
  given an equivalence
  relation on a group or (monoid )we can project the group (monoid)
  structure on the quotient and obtain another group.\<close>

text\<open>The neutral element class is neutral in the projection.\<close>

lemma (in monoid0) Group_ZF_2_2_L1: 
  assumes A1: "equiv(G,r)" and A2:"Congruent2(r,f)"
  and A3: "F = ProjFun2(G,r,f)" 
  and A4: "e = TheNeutralElement(G,f)"
  shows "r``{e} \<in> G//r \<and> 
  (\<forall>c \<in> G//r. F`\<langle> r``{e},c\<rangle> = c \<and>  F`\<langle> c,r``{e}\<rangle> = c)"
proof
  from A4 show T1:"r``{e} \<in> G//r"
    using unit_is_neutral quotientI
    by simp
  show 
    "\<forall>c \<in> G//r. F`\<langle> r``{e},c\<rangle> = c \<and>  F`\<langle> c,r``{e}\<rangle> = c"
  proof
    fix c assume A5:"c \<in> G//r"
    then obtain g where D1:"g\<in>G" "c = r``{g}"
      using quotient_def by auto
    with A1 A2 A3 A4 D1 show 
      "F`\<langle> r``{e},c\<rangle> = c \<and>  F`\<langle> c,r``{e}\<rangle> = c"
      using unit_is_neutral EquivClass_1_L10 (*group0_1_L3*)
      by simp
  qed
qed

text\<open>The projected structure is a monoid.\<close>

theorem (in monoid0) Group_ZF_2_2_T1:
  assumes A1: "equiv(G,r)" and A2: "Congruent2(r,f)"
  and A3: "F = ProjFun2(G,r,f)"
  shows "IsAmonoid(G//r,F)"
proof -
  let ?E = "r``{TheNeutralElement(G,f)}"
  from A1 A2 A3 have 
    "?E \<in> G//r \<and> (\<forall>c\<in>G//r. F`\<langle> ?E,c\<rangle> = c \<and> F`\<langle> c,?E\<rangle> = c)"
    using Group_ZF_2_2_L1 by simp
  hence
    "\<exists>E\<in>G//r. \<forall> c\<in>G//r. F`\<langle> E,c\<rangle> = c \<and> F`\<langle> c,E\<rangle> = c"
    by auto
  with monoidAsssum A1 A2 A3 show ?thesis
    using IsAmonoid_def EquivClass_2_T2
    by simp
qed

text\<open>The class of the neutral element is the neutral element of the
  projected monoid.\<close>

lemma Group_ZF_2_2_L1:
  assumes A1: "IsAmonoid(G,f)"
  and A2: "equiv(G,r)" and A3: "Congruent2(r,f)"
  and A4: "F = ProjFun2(G,r,f)"
  and A5: "e = TheNeutralElement(G,f)"
  shows " r``{e} = TheNeutralElement(G//r,F)"
proof -
  from A1 A2 A3 A4 have 
    T1:"monoid0(G,f)" and T2:"monoid0(G//r,F)"
    using monoid0_def monoid0.Group_ZF_2_2_T1 by auto
  from T1 A2 A3 A4 A5 have "r``{e} \<in> G//r \<and> 
    (\<forall>c \<in> G//r. F`\<langle> r``{e},c\<rangle> = c \<and>  F`\<langle> c,r``{e}\<rangle> = c)"
    using monoid0.Group_ZF_2_2_L1 by simp
  with T2 show ?thesis using monoid0.group0_1_L4
    by auto
qed

text\<open>The projected operation can be defined in terms of the group operation
  on representants in a natural way.\<close>

lemma (in group0) Group_ZF_2_2_L2:
  assumes A1: "equiv(G,r)" and A2: "Congruent2(r,P)"
  and A3: "F = ProjFun2(G,r,P)"
  and A4: "a\<in>G" "b\<in>G"
  shows "F`\<langle> r``{a},r``{b}\<rangle> = r``{a\<cdot>b}"
proof -
  from A1 A2 A3 A4 show ?thesis
    using EquivClass_1_L10 by simp
qed

text\<open>The class of the inverse is a right inverse of the class.\<close>

lemma (in group0) Group_ZF_2_2_L3:
  assumes A1: "equiv(G,r)" and A2: "Congruent2(r,P)"
  and A3: "F = ProjFun2(G,r,P)"
  and A4: "a\<in>G"
  shows "F`\<langle>r``{a},r``{a\<inverse>}\<rangle> = TheNeutralElement(G//r,F)"
proof -
  from A1 A2 A3 A4 have
    "F`\<langle>r``{a},r``{a\<inverse>}\<rangle> = r``{\<one>}"
    using inverse_in_group Group_ZF_2_2_L2 group0_2_L6 
    by simp
  with groupAssum A1 A2 A3 show ?thesis
    using IsAgroup_def Group_ZF_2_2_L1 by simp
qed

text\<open>The group structure can be projected to the quotient space.\<close>

theorem (in group0) Group_ZF_3_T2:
  assumes A1: "equiv(G,r)" and A2: "Congruent2(r,P)"
  shows "IsAgroup(G//r,ProjFun2(G,r,P))"
proof -
  let ?F = "ProjFun2(G,r,P)"
  let ?E = "TheNeutralElement(G//r,?F)"
  from groupAssum A1 A2 have "IsAmonoid(G//r,?F)"
    using IsAgroup_def monoid0_def monoid0.Group_ZF_2_2_T1
    by simp
  moreover have
    "\<forall>c\<in>G//r. \<exists>b\<in>G//r. ?F`\<langle> c,b\<rangle> = ?E"
  proof
    fix c assume A3: "c \<in> G//r"
    then obtain g where D1: "g\<in>G"  "c = r``{g}"
      using quotient_def by auto
    let ?b = "r``{g\<inverse>}"
    from D1 have "?b \<in> G//r"
      using inverse_in_group quotientI
      by simp
    moreover from A1 A2 D1 have 
      "?F`\<langle> c,?b\<rangle> = ?E"
      using Group_ZF_2_2_L3 by simp
    ultimately show "\<exists>b\<in>G//r. ?F`\<langle> c,b\<rangle> = ?E"
      by auto
  qed
  ultimately show ?thesis
    using IsAgroup_def by simp
qed

text\<open>The group inverse (in the projected group) of a class is the class
  of the inverse.\<close>

lemma (in group0) Group_ZF_2_2_L4:
  assumes A1: "equiv(G,r)" and 
  A2: "Congruent2(r,P)" and 
  A3: "F = ProjFun2(G,r,P)" and
  A4: "a\<in>G"
  shows "r``{a\<inverse>} = GroupInv(G//r,F)`(r``{a})"
proof -
  from A1 A2 A3 have "group0(G//r,F)"
    using Group_ZF_3_T2 group0_def by simp
  moreover from A4 have 
    "r``{a} \<in> G//r"  "r``{a\<inverse>} \<in> G//r"
    using inverse_in_group quotientI by auto
  moreover from A1 A2 A3 A4 have
     "F`\<langle>r``{a},r``{a\<inverse>}\<rangle> = TheNeutralElement(G//r,F)"
    using Group_ZF_2_2_L3 by simp
  ultimately show ?thesis
    by (rule group0.group0_2_L9)
qed

subsection\<open>Normal subgroups and quotient groups\<close>

text\<open>If $H$ is a subgroup of $G$, then for every $a\in G$
  we can cosider the sets $\{a\cdot h. h \in H\}$ 
  and $\{ h\cdot a. h \in H\}$ (called a left and right ''coset of H'', resp.)
  These sets sometimes form a group, called the ''quotient group''.
  This section discusses the notion of quotient groups.\<close>

text\<open>A normal subgorup $N$ of a group $G$ is such that $aba^{-1}$ belongs to 
  $N$ if $a\in G, b\in N$.\<close>

definition
  "IsAnormalSubgroup(G,P,N) \<equiv> IsAsubgroup(N,P) \<and> 
  (\<forall>n\<in>N.\<forall>g\<in>G. P`\<langle>  P`\<langle>  g,n \<rangle>,GroupInv(G,P)`(g) \<rangle> \<in> N)"

text\<open>Having a group and a normal subgroup $N$ 
  we can create another group
  consisting of eqivalence classes of the relation 
  $a\sim b \equiv a\cdot b^{-1} \in N$.  We will refer to this relation
  as the quotient group relation. The classes of this relation are in 
  fact cosets of subgroup $H$.\<close>

definition
  "QuotientGroupRel(G,P,H) \<equiv> 
  {\<langle> a,b\<rangle> \<in> G\<times>G. P`\<langle> a, GroupInv(G,P)`(b)\<rangle> \<in> H}"

text\<open>Next we define the operation in the quotient group as the
  projection of the group operation on the classses of the
  quotient group relation.\<close>

definition
  "QuotientGroupOp(G,P,H) \<equiv> ProjFun2(G,QuotientGroupRel(G,P,H ),P)"

text\<open>Definition of a normal subgroup in a more readable notation.\<close>

lemma (in group0) Group_ZF_2_4_L0: 
  assumes "IsAnormalSubgroup(G,P,H)"
  and "g\<in>G" "n\<in>H"
  shows "g\<cdot>n\<cdot>g\<inverse> \<in> H"
  using assms IsAnormalSubgroup_def by simp

text\<open>The quotient group relation is reflexive.\<close>

lemma (in group0) Group_ZF_2_4_L1: 
  assumes "IsAsubgroup(H,P)"
  shows "refl(G,QuotientGroupRel(G,P,H))"
  using assms  group0_2_L6 group0_3_L5 
    QuotientGroupRel_def refl_def by simp

text\<open>The quotient group relation is symmetric.\<close>

lemma (in group0) Group_ZF_2_4_L2:
  assumes A1:"IsAsubgroup(H,P)"
  shows "sym(QuotientGroupRel(G,P,H))"
proof -
  {  
    fix a b assume A2: "\<langle> a,b\<rangle> \<in> QuotientGroupRel(G,P,H)"
    with A1 have "(a\<cdot>b\<inverse>)\<inverse> \<in> H" 
      using QuotientGroupRel_def group0_3_T3A
      by simp
    moreover from A2 have "(a\<cdot>b\<inverse>)\<inverse> =  b\<cdot>a\<inverse>"
      using QuotientGroupRel_def group0_2_L12
      by simp
    ultimately have "b\<cdot>a\<inverse> \<in> H" by simp
    with A2 have "\<langle> b,a\<rangle> \<in> QuotientGroupRel(G,P,H)"
      using QuotientGroupRel_def by simp 
  }
  then show ?thesis using symI by simp
qed

text\<open>The quotient group relation is transistive.\<close>

lemma (in group0) Group_ZF_2_4_L3A:
  assumes A1: "IsAsubgroup(H,P)" and 
  A2: "\<langle> a,b\<rangle> \<in> QuotientGroupRel(G,P,H)" and 
  A3: "\<langle> b,c\<rangle> \<in> QuotientGroupRel(G,P,H)"
  shows "\<langle> a,c\<rangle> \<in> QuotientGroupRel(G,P,H)"
proof -
  let ?r = "QuotientGroupRel(G,P,H)"
  from A2 A3 have T1:"a\<in>G" "b\<in>G" "c\<in>G"
    using QuotientGroupRel_def by auto
  from A1 A2 A3 have "(a\<cdot>b\<inverse>)\<cdot>(b\<cdot>c\<inverse>) \<in> H"
    using  QuotientGroupRel_def group0_3_L6
    by simp
  moreover from T1 have 
    "a\<cdot>c\<inverse> = (a\<cdot>b\<inverse>)\<cdot>(b\<cdot>c\<inverse>)"
    using group0_2_L14A by blast
  ultimately have "a\<cdot>c\<inverse> \<in> H" 
    by simp
  with T1 show ?thesis using QuotientGroupRel_def
    by simp
qed

text\<open>The quotient group relation is an equivalence relation. Note
  we do not need the subgroup to be normal for this to be true.\<close>

lemma (in group0) Group_ZF_2_4_L3: assumes A1:"IsAsubgroup(H,P)"
  shows "equiv(G,QuotientGroupRel(G,P,H))"
proof -
  let ?r = "QuotientGroupRel(G,P,H)"
  from A1 have 
     "\<forall>a b c. (\<langle>a, b\<rangle> \<in> ?r  \<and>  \<langle>b, c\<rangle> \<in> ?r \<longrightarrow> \<langle>a, c\<rangle> \<in> ?r)"
    using Group_ZF_2_4_L3A by blast
  then have "trans(?r)"
    using Fol1_L2 by blast
  with A1 show ?thesis 
    using Group_ZF_2_4_L1 Group_ZF_2_4_L2 
      QuotientGroupRel_def equiv_def
    by auto
qed

text\<open>The next lemma states the essential condition for congruency of 
  the group operation with respect to the quotient group relation.\<close>

lemma (in group0) Group_ZF_2_4_L4: 
  assumes A1: "IsAnormalSubgroup(G,P,H)"
  and A2: "\<langle>a1,a2\<rangle> \<in> QuotientGroupRel(G,P,H)"
  and A3: "\<langle>b1,b2\<rangle> \<in> QuotientGroupRel(G,P,H)"
  shows "\<langle>a1\<cdot>b1, a2\<cdot>b2\<rangle> \<in> QuotientGroupRel(G,P,H)"
proof -
  from A2 A3 have T1:
    "a1\<in>G"  "a2\<in>G"  "b1\<in>G"  "b2\<in>G"
    "a1\<cdot>b1 \<in> G"  "a2\<cdot>b2 \<in> G"
    "b1\<cdot>b2\<inverse> \<in> H"  "a1\<cdot>a2\<inverse> \<in> H"
    using QuotientGroupRel_def group0_2_L1 monoid0.group0_1_L1
    by auto
  with A1 show ?thesis using
    IsAnormalSubgroup_def group0_3_L6 group0_2_L15
    QuotientGroupRel_def by simp
qed

text\<open>If the subgroup is normal, the group operation is congruent 
  with respect to the quotient group relation.\<close>

lemma Group_ZF_2_4_L5A:
  assumes "IsAgroup(G,P)"
  and "IsAnormalSubgroup(G,P,H)" 
  shows "Congruent2(QuotientGroupRel(G,P,H),P)"
  using assms group0_def group0.Group_ZF_2_4_L4 Congruent2_def
  by simp

text\<open>The quotient group is indeed a group.\<close>

theorem Group_ZF_2_4_T1:
  assumes "IsAgroup(G,P)" and "IsAnormalSubgroup(G,P,H)"
  shows   
  "IsAgroup(G//QuotientGroupRel(G,P,H),QuotientGroupOp(G,P,H))"
  using assms group0_def group0.Group_ZF_2_4_L3 IsAnormalSubgroup_def
    Group_ZF_2_4_L5A group0.Group_ZF_3_T2 QuotientGroupOp_def
  by simp

text\<open>The class (coset) of the neutral element is the neutral
  element of the quotient group.\<close>

lemma Group_ZF_2_4_L5B: 
  assumes "IsAgroup(G,P)" and "IsAnormalSubgroup(G,P,H)"
  and "r = QuotientGroupRel(G,P,H)"
  and "e = TheNeutralElement(G,P)"
  shows " r``{e} = TheNeutralElement(G//r,QuotientGroupOp(G,P,H))"
  using assms IsAnormalSubgroup_def group0_def
    IsAgroup_def group0.Group_ZF_2_4_L3 Group_ZF_2_4_L5A
    QuotientGroupOp_def Group_ZF_2_2_L1
  by simp

text\<open>A group element is equivalent to the neutral element iff it is in the
  subgroup we divide the group by.\<close>

lemma (in group0) Group_ZF_2_4_L5C: assumes "a\<in>G"
  shows "\<langle>a,\<one>\<rangle> \<in> QuotientGroupRel(G,P,H) \<longleftrightarrow> a\<in>H"
  using assms QuotientGroupRel_def group_inv_of_one group0_2_L2
  by auto

text\<open>A group element is in $H$ iff its class is the neutral element of
  $G/H$.\<close>

lemma (in group0) Group_ZF_2_4_L5D:
  assumes A1: "IsAnormalSubgroup(G,P,H)" and 
  A2: "a\<in>G" and 
  A3: "r = QuotientGroupRel(G,P,H)" and
  A4: "TheNeutralElement(G//r,QuotientGroupOp(G,P,H)) = e"
  shows "r``{a} = e \<longleftrightarrow> \<langle>a,\<one>\<rangle> \<in> r"
proof
  assume "r``{a} = e"
  with groupAssum assms have 
    "r``{\<one>} = r``{a}" and I: "equiv(G,r)"
    using Group_ZF_2_4_L5B IsAnormalSubgroup_def Group_ZF_2_4_L3
    by auto
  with A2 have "\<langle>\<one>,a\<rangle> \<in> r" using eq_equiv_class 
    by simp
  with I show "\<langle>a,\<one>\<rangle> \<in> r" by (rule equiv_is_sym)
next assume "\<langle>a,\<one>\<rangle> \<in> r"
  moreover from A1 A3 have "equiv(G,r)"
    using IsAnormalSubgroup_def Group_ZF_2_4_L3
    by simp
  ultimately have "r``{a} = r``{\<one>}"
    using equiv_class_eq by simp
  with groupAssum A1 A3 A4 show "r``{a} = e"
    using Group_ZF_2_4_L5B by simp
qed
  
text\<open>The class of $a\in G$ is the neutral 
  element of the quotient $G/H$ iff $a\in H$.\<close>

lemma (in group0) Group_ZF_2_4_L5E: 
  assumes "IsAnormalSubgroup(G,P,H)" and 
  "a\<in>G" and "r = QuotientGroupRel(G,P,H)" and 
  "TheNeutralElement(G//r,QuotientGroupOp(G,P,H)) = e"
  shows "r``{a} = e \<longleftrightarrow> a\<in>H"
  using assms Group_ZF_2_4_L5C  Group_ZF_2_4_L5D
  by simp

text\<open>Essential condition to show that every subgroup of an abelian group 
  is normal.\<close>

lemma (in group0) Group_ZF_2_4_L5:
  assumes A1: "P {is commutative on} G" 
  and A2: "IsAsubgroup(H,P)"
  and A3: "g\<in>G"  "h\<in>H" 
  shows "g\<cdot>h\<cdot>g\<inverse> \<in> H"
proof -
  from A2 A3 have T1:"h\<in>G" "g\<inverse> \<in> G" 
    using group0_3_L2 inverse_in_group by auto
  with A3 A1 have "g\<cdot>h\<cdot>g\<inverse> = g\<inverse>\<cdot>g\<cdot>h"
    using group0_4_L4A by simp
  with A3 T1 show ?thesis using
    group0_2_L6 group0_2_L2
    by simp
qed

text\<open>Every subgroup of an abelian group is normal. Moreover, the quotient
  group is also abelian.\<close>

lemma Group_ZF_2_4_L6:
  assumes A1: "IsAgroup(G,P)"
  and A2: "P {is commutative on} G" 
  and A3: "IsAsubgroup(H,P)"
  shows  "IsAnormalSubgroup(G,P,H)"
  "QuotientGroupOp(G,P,H) {is commutative on} (G//QuotientGroupRel(G,P,H))"
proof -
  from A1 A2 A3 show T1: "IsAnormalSubgroup(G,P,H)" using
    group0_def IsAnormalSubgroup_def group0.Group_ZF_2_4_L5 
    by simp
  let ?r = "QuotientGroupRel(G,P,H)"
  from A1 A3 T1 have "equiv(G,?r)" "Congruent2(?r,P)"
    using group0_def group0.Group_ZF_2_4_L3 Group_ZF_2_4_L5A
    by auto
  with A2 show 
    "QuotientGroupOp(G,P,H) {is commutative on} (G//QuotientGroupRel(G,P,H))"
    using EquivClass_2_T1 QuotientGroupOp_def
    by simp
qed

text\<open>The group inverse (in the quotient group) of a class (coset) is the class
  of the inverse.\<close>

lemma (in group0) Group_ZF_2_4_L7: 
  assumes "IsAnormalSubgroup(G,P,H)" 
  and "a\<in>G" and "r = QuotientGroupRel(G,P,H)" 
  and "F = QuotientGroupOp(G,P,H)"
  shows "r``{a\<inverse>} = GroupInv(G//r,F)`(r``{a})"
  using groupAssum assms IsAnormalSubgroup_def Group_ZF_2_4_L3 
    Group_ZF_2_4_L5A QuotientGroupOp_def Group_ZF_2_2_L4
  by simp

subsection\<open>Function spaces as monoids\<close>

text\<open>On every space of functions $\{f : X\rightarrow X\}$ 
  we can define a natural 
  monoid structure with composition as the operation. This section explores 
  this fact.\<close>

text\<open>The next lemma states that composition has a neutral element, 
  namely the identity function on $X$ 
  (the one that maps $x\in X$ into itself).\<close>
  
lemma Group_ZF_2_5_L1: assumes A1: "F = Composition(X)"
  shows "\<exists>I\<in>(X\<rightarrow>X). \<forall>f\<in>(X\<rightarrow>X). F`\<langle> I,f\<rangle> = f \<and> F`\<langle> f,I\<rangle> = f"
proof-
  let ?I = "id(X)"
  from A1 have 
    "?I \<in> X\<rightarrow>X \<and> (\<forall>f\<in>(X\<rightarrow>X). F`\<langle> ?I,f\<rangle> = f \<and> F`\<langle> f,?I\<rangle> = f)" 
    using id_type func_ZF_6_L1A by simp
  thus ?thesis by auto
qed

text\<open>The space of functions that map a set $X$ into 
  itsef is a monoid with composition as operation and the identity function
  as the neutral element.\<close>

lemma Group_ZF_2_5_L2: shows
  "IsAmonoid(X\<rightarrow>X,Composition(X))"
  "id(X) = TheNeutralElement(X\<rightarrow>X,Composition(X))"
proof -
  let ?I = "id(X)"
  let ?F = "Composition(X)"
  show "IsAmonoid(X\<rightarrow>X,Composition(X))" 
    using func_ZF_5_L5 Group_ZF_2_5_L1 IsAmonoid_def
    by auto  
  then have "monoid0(X\<rightarrow>X,?F)"
    using monoid0_def by simp
  moreover have
    "?I \<in> X\<rightarrow>X \<and> (\<forall>f\<in>(X\<rightarrow>X). ?F`\<langle> ?I,f\<rangle> = f \<and> ?F`\<langle> f,?I\<rangle> = f)"
    using id_type func_ZF_6_L1A by simp
  ultimately show "?I = TheNeutralElement(X\<rightarrow>X,?F)"
    using monoid0.group0_1_L4 by auto
qed

end
