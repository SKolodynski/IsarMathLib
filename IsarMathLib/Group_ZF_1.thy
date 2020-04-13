(* 
This file is a part of IsarMathLib - 
a library of formalized mathematics for Isabelle/Isar.

Copyright (C) 2008  Slawomir Kolodynski

This program is free software; Redistribution and use in source and binary forms, 
with or without modification, are permitted provided that the 
following conditions are met:

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

section \<open>Groups 1\<close>

theory Group_ZF_1 imports Group_ZF

begin

text\<open>In this theory we consider right and left translations and odd 
  functions.\<close>

subsection\<open>Translations\<close>

text\<open>In this section we consider translations. Translations are maps 
  $T: G\rightarrow G$ of the form $T_g (a) = g\cdot a$ or 
  $T_g (a) = a\cdot g$. We also consider two-dimensional translations
  $T_g : G\times G \rightarrow G\times G$, where 
  $T_g(a,b) = (a\cdot g, b\cdot g)$ or $T_g(a,b) = (g\cdot a, g\cdot b)$. 
\<close>

text\<open>For an element $a\in G$ the right translation is defined 
  a function (set of pairs) such that its value (the second element
  of a pair) is the value of the group operation on the first element
  of the pair and $g$. This looks a bit strange in the raw set notation, 
  when we write a function explicitely as a set of pairs and value of 
  the group operation on the pair $\langle a,b \rangle$ 
  as \<open>P`\<langle>a,b\<rangle>\<close> instead of the usual infix $a\cdot b$
  or $a + b$.\<close>

definition
  "RightTranslation(G,P,g) \<equiv> {\<langle> a,b\<rangle> \<in> G\<times>G. P`\<langle>a,g\<rangle> = b}"

text\<open>A similar definition of the left translation.\<close>

definition
  "LeftTranslation(G,P,g) \<equiv> {\<langle>a,b\<rangle> \<in> G\<times>G. P`\<langle>g,a\<rangle> = b}"

text\<open>Translations map $G$ into $G$. Two dimensional translations map
  $G\times G$ into itself.\<close>

lemma (in group0) group0_5_L1: assumes A1: "g\<in>G"
  shows "RightTranslation(G,P,g) : G\<rightarrow>G" and  "LeftTranslation(G,P,g) : G\<rightarrow>G"
proof -
  from A1 have "\<forall>a\<in>G. a\<cdot>g \<in> G" and "\<forall>a\<in>G. g\<cdot>a \<in> G"
    using group_oper_assocA apply_funtype by auto
  then show 
    "RightTranslation(G,P,g) : G\<rightarrow>G" 
    "LeftTranslation(G,P,g) : G\<rightarrow>G"
    using RightTranslation_def LeftTranslation_def func1_1_L11A
    by auto
qed

text\<open>The values of the translations are what we expect.\<close>

lemma (in group0) group0_5_L2: assumes "g\<in>G" "a\<in>G"
  shows 
  "RightTranslation(G,P,g)`(a) = a\<cdot>g"
  "LeftTranslation(G,P,g)`(a) = g\<cdot>a"
  using assms group0_5_L1 RightTranslation_def LeftTranslation_def
    func1_1_L11B by auto

text\<open>Composition of left translations is a left translation by the product.\<close>

lemma (in group0) group0_5_L4: assumes A1: "g\<in>G" "h\<in>G" "a\<in>G" and 
  A2: "T\<^sub>g = LeftTranslation(G,P,g)"  "T\<^sub>h = LeftTranslation(G,P,h)"
  shows 
  "T\<^sub>g`(T\<^sub>h`(a)) = g\<cdot>h\<cdot>a"
  "T\<^sub>g`(T\<^sub>h`(a)) = LeftTranslation(G,P,g\<cdot>h)`(a)"
proof -
  from A1 have I: "h\<cdot>a\<in>G"  "g\<cdot>h\<in>G"
    using group_oper_assocA apply_funtype by auto
  with A1 A2 show "T\<^sub>g`(T\<^sub>h`(a)) = g\<cdot>h\<cdot>a"
    using group0_5_L2 group_oper_assoc by simp
  with A1 A2 I show 
    "T\<^sub>g`(T\<^sub>h`(a)) = LeftTranslation(G,P,g\<cdot>h)`(a)"
    using group0_5_L2 group_oper_assoc by simp
qed


text\<open>Composition of right translations is a right translation by 
  the product.\<close>

lemma (in group0) group0_5_L5: assumes A1: "g\<in>G" "h\<in>G" "a\<in>G" and 
  A2: "T\<^sub>g = RightTranslation(G,P,g)"  "T\<^sub>h = RightTranslation(G,P,h)"
  shows 
 "T\<^sub>g`(T\<^sub>h`(a)) = a\<cdot>h\<cdot>g"
  "T\<^sub>g`(T\<^sub>h`(a)) = RightTranslation(G,P,h\<cdot>g)`(a)"
proof -
  from A1 have I: "a\<cdot>h\<in>G" "h\<cdot>g \<in>G"
    using group_oper_assocA apply_funtype by auto
  with A1 A2 show "T\<^sub>g`(T\<^sub>h`(a)) = a\<cdot>h\<cdot>g" 
    using group0_5_L2 group_oper_assoc by simp
  with A1 A2 I show 
    "T\<^sub>g`(T\<^sub>h`(a)) = RightTranslation(G,P,h\<cdot>g)`(a)"
    using group0_5_L2 group_oper_assoc by simp
qed

text\<open>Point free version of \<open>group0_5_L4\<close> and \<open>group0_5_L5\<close>.\<close>

lemma (in group0) trans_comp: assumes "g\<in>G" "h\<in>G" shows
  "RightTranslation(G,P,g) O RightTranslation(G,P,h) = RightTranslation(G,P,h\<cdot>g)"
  "LeftTranslation(G,P,g) O LeftTranslation(G,P,h) = LeftTranslation(G,P,g\<cdot>h)"
proof -
  let ?T\<^sub>g = "RightTranslation(G,P,g)"
  let ?T\<^sub>h = "RightTranslation(G,P,h)"
  from assms have "?T\<^sub>g:G\<rightarrow>G" and "?T\<^sub>h:G\<rightarrow>G"
    using group0_5_L1 by auto
  then have "?T\<^sub>g O ?T\<^sub>h:G\<rightarrow>G" using comp_fun by simp
  moreover from assms have "RightTranslation(G,P,h\<cdot>g):G\<rightarrow>G"
    using group_op_closed group0_5_L1 by simp
  moreover from assms \<open>?T\<^sub>h:G\<rightarrow>G\<close> have 
    "\<forall>a\<in>G. (?T\<^sub>g O ?T\<^sub>h)`(a) = RightTranslation(G,P,h\<cdot>g)`(a)"
    using comp_fun_apply group0_5_L5 by simp
  ultimately show "?T\<^sub>g O ?T\<^sub>h =  RightTranslation(G,P,h\<cdot>g)"
    by (rule func_eq)
next
  let ?T\<^sub>g = "LeftTranslation(G,P,g)"
  let ?T\<^sub>h = "LeftTranslation(G,P,h)"
  from assms have "?T\<^sub>g:G\<rightarrow>G" and "?T\<^sub>h:G\<rightarrow>G"
    using group0_5_L1 by auto
  then have "?T\<^sub>g O ?T\<^sub>h:G\<rightarrow>G" using comp_fun by simp
  moreover from assms have "LeftTranslation(G,P,g\<cdot>h):G\<rightarrow>G"
    using group_op_closed group0_5_L1 by simp
  moreover from assms \<open>?T\<^sub>h:G\<rightarrow>G\<close> have 
    "\<forall>a\<in>G. (?T\<^sub>g O ?T\<^sub>h)`(a) = LeftTranslation(G,P,g\<cdot>h)`(a)"
    using comp_fun_apply group0_5_L4 by simp
  ultimately show "?T\<^sub>g O ?T\<^sub>h =  LeftTranslation(G,P,g\<cdot>h)"
    by (rule func_eq)
qed

text\<open>The image of a set under a composition of translations is the same as
  the image under translation by a product.\<close>

lemma (in group0) trans_comp_image: assumes A1: "g\<in>G" "h\<in>G" and
  A2: "T\<^sub>g = LeftTranslation(G,P,g)"  "T\<^sub>h = LeftTranslation(G,P,h)"
shows "T\<^sub>g``(T\<^sub>h``(A)) = LeftTranslation(G,P,g\<cdot>h)``(A)"
proof -
  from A2 have "T\<^sub>g``(T\<^sub>h``(A)) = (T\<^sub>g O T\<^sub>h)``(A)"
    using image_comp by simp
  with assms show ?thesis using trans_comp by simp
qed

text\<open>Another form of the image of a set under a composition of translations\<close>

lemma (in group0) group0_5_L6: 
  assumes A1: "g\<in>G" "h\<in>G" and A2: "A\<subseteq>G" and 
  A3: "T\<^sub>g = RightTranslation(G,P,g)"  "T\<^sub>h = RightTranslation(G,P,h)"
  shows "T\<^sub>g``(T\<^sub>h``(A)) = {a\<cdot>h\<cdot>g. a\<in>A}"
proof -
  from A2 have "\<forall>a\<in>A. a\<in>G" by auto
  from A1 A3 have "T\<^sub>g : G\<rightarrow>G"  "T\<^sub>h : G\<rightarrow>G"
    using group0_5_L1 by auto
  with assms \<open>\<forall>a\<in>A. a\<in>G\<close> show 
    "T\<^sub>g``(T\<^sub>h``(A)) = {a\<cdot>h\<cdot>g. a\<in>A}"
    using func1_1_L15C group0_5_L5 by auto
qed

text\<open>The translation by neutral element is the identity on group.\<close>

lemma (in group0) trans_neutral: shows 
  "RightTranslation(G,P,\<one>) = id(G)" and "LeftTranslation(G,P,\<one>) = id(G)"
proof -
  have "RightTranslation(G,P,\<one>):G\<rightarrow>G" and "\<forall>a\<in>G. RightTranslation(G,P,\<one>)`(a) = a"
    using group0_2_L2 group0_5_L1 group0_5_L2  by auto
  then show "RightTranslation(G,P,\<one>) = id(G)" by (rule indentity_fun)
  have "LeftTranslation(G,P,\<one>):G\<rightarrow>G" and "\<forall>a\<in>G. LeftTranslation(G,P,\<one>)`(a) = a"
    using group0_2_L2 group0_5_L1 group0_5_L2  by auto
  then show "LeftTranslation(G,P,\<one>) = id(G)" by (rule indentity_fun)
qed

text\<open>Composition of translations by an element and its inverse is identity.\<close>

lemma (in group0) trans_comp_id: assumes "g\<in>G" shows
  "RightTranslation(G,P,g) O RightTranslation(G,P,g\<inverse>) = id(G)" and
  "RightTranslation(G,P,g\<inverse>) O RightTranslation(G,P,g) = id(G)" and
  "LeftTranslation(G,P,g) O LeftTranslation(G,P,g\<inverse>) = id(G)" and
  "LeftTranslation(G,P,g\<inverse>) O LeftTranslation(G,P,g) = id(G)"
  using assms inverse_in_group trans_comp group0_2_L6 trans_neutral by auto

text\<open>Translations are bijective.\<close>

lemma (in group0) trans_bij: assumes "g\<in>G" shows
  "RightTranslation(G,P,g) \<in> bij(G,G)" and "LeftTranslation(G,P,g) \<in> bij(G,G)"
proof-
  from assms have 
    "RightTranslation(G,P,g):G\<rightarrow>G" and
    "RightTranslation(G,P,g\<inverse>):G\<rightarrow>G" and
    "RightTranslation(G,P,g) O RightTranslation(G,P,g\<inverse>) = id(G)"
    "RightTranslation(G,P,g\<inverse>) O RightTranslation(G,P,g) = id(G)"
  using inverse_in_group group0_5_L1 trans_comp_id by auto
  then show "RightTranslation(G,P,g) \<in> bij(G,G)" using fg_imp_bijective by simp
  from assms have 
    "LeftTranslation(G,P,g):G\<rightarrow>G" and
    "LeftTranslation(G,P,g\<inverse>):G\<rightarrow>G" and
    "LeftTranslation(G,P,g) O LeftTranslation(G,P,g\<inverse>) = id(G)"
    "LeftTranslation(G,P,g\<inverse>) O LeftTranslation(G,P,g) = id(G)"
    using inverse_in_group group0_5_L1 trans_comp_id by auto
  then show "LeftTranslation(G,P,g) \<in> bij(G,G)" using fg_imp_bijective by simp
qed

text\<open>Converse of a translation is translation by the inverse.\<close>

lemma (in group0) trans_conv_inv: assumes "g\<in>G" shows
  "converse(RightTranslation(G,P,g)) = RightTranslation(G,P,g\<inverse>)" and
  "converse(LeftTranslation(G,P,g)) = LeftTranslation(G,P,g\<inverse>)" and
  "LeftTranslation(G,P,g) = converse(LeftTranslation(G,P,g\<inverse>))" and
  "RightTranslation(G,P,g) = converse(RightTranslation(G,P,g\<inverse>))"
proof -
  from assms have
    "RightTranslation(G,P,g) \<in> bij(G,G)"  "RightTranslation(G,P,g\<inverse>) \<in> bij(G,G)" and
    "LeftTranslation(G,P,g) \<in> bij(G,G)"  "LeftTranslation(G,P,g\<inverse>) \<in> bij(G,G)"
    using trans_bij inverse_in_group by auto
  moreover from assms have
    "RightTranslation(G,P,g\<inverse>) O RightTranslation(G,P,g) = id(G)" and
    "LeftTranslation(G,P,g\<inverse>) O LeftTranslation(G,P,g) = id(G)" and
    "LeftTranslation(G,P,g) O LeftTranslation(G,P,g\<inverse>) = id(G)" and
    "LeftTranslation(G,P,g\<inverse>) O LeftTranslation(G,P,g) = id(G)"
    using trans_comp_id by auto
  ultimately show 
    "converse(RightTranslation(G,P,g)) = RightTranslation(G,P,g\<inverse>)" and
    "converse(LeftTranslation(G,P,g)) = LeftTranslation(G,P,g\<inverse>)" and  
    "LeftTranslation(G,P,g) = converse(LeftTranslation(G,P,g\<inverse>))" and
    "RightTranslation(G,P,g) = converse(RightTranslation(G,P,g\<inverse>))"
    using comp_id_conv by auto
qed
  
text\<open>The image of a set by translation is the same as the inverse image by
by the inverse element translation.\<close>

lemma (in group0) trans_image_vimage: assumes "g\<in>G" shows
  "LeftTranslation(G,P,g)``(A) = LeftTranslation(G,P,g\<inverse>)-``(A)" and
  "RightTranslation(G,P,g)``(A) = RightTranslation(G,P,g\<inverse>)-``(A)"
  using assms trans_conv_inv vimage_converse by auto

text\<open>Another way of looking at translations is that they are sections
  of the group operation.\<close>

lemma (in group0) trans_eq_section: assumes "g\<in>G" shows
  "RightTranslation(G,P,g) = Fix2ndVar(P,g)" and
  "LeftTranslation(G,P,g) =  Fix1stVar(P,g)"
proof -
  let ?T = "RightTranslation(G,P,g)"
  let ?F = "Fix2ndVar(P,g)"
  from assms have "?T: G\<rightarrow>G" and "?F: G\<rightarrow>G"
    using group0_5_L1 group_oper_assocA fix_2nd_var_fun by auto
  moreover from assms have "\<forall>a\<in>G. ?T`(a) = ?F`(a)"
    using group0_5_L2 group_oper_assocA fix_var_val by simp
  ultimately show "?T = ?F" by (rule func_eq)
next
  let ?T = "LeftTranslation(G,P,g)"
  let ?F = "Fix1stVar(P,g)"
  from assms have "?T: G\<rightarrow>G" and "?F: G\<rightarrow>G"
    using group0_5_L1 group_oper_assocA fix_1st_var_fun by auto
  moreover from assms have "\<forall>a\<in>G. ?T`(a) = ?F`(a)"
    using group0_5_L2 group_oper_assocA fix_var_val by simp
  ultimately show "?T = ?F" by (rule func_eq)
qed

text\<open>A lemma about translating sets.\<close>

lemma (in group0) ltrans_image: assumes A1: "V\<subseteq>G" and A2: "x\<in>G"
  shows "LeftTranslation(G,P,x)``(V) = {x\<cdot>v. v\<in>V}"
proof -
  from assms have "LeftTranslation(G,P,x)``(V) = {LeftTranslation(G,P,x)`(v). v\<in>V}"
    using group0_5_L1 func_imagedef by blast
  moreover from assms have "\<forall>v\<in>V. LeftTranslation(G,P,x)`(v) = x\<cdot>v"
    using group0_5_L2 by auto
  ultimately show ?thesis by auto
qed

lemma (in group0) rtrans_image: assumes A1: "V\<subseteq>G" and A2: "x\<in>G"
  shows "RightTranslation(G,P,x)``(V) = {v\<cdot>x. v\<in>V}"
proof -
  from assms have "RightTranslation(G,P,x)``(V) = {RightTranslation(G,P,x)`(v). v\<in>V}"
    using group0_5_L1 func_imagedef by blast
  moreover from assms have "\<forall>v\<in>V. RightTranslation(G,P,x)`(v) = v\<cdot>x"
    using group0_5_L2 by auto
  ultimately show ?thesis by auto
qed

text\<open>A technical lemma about solving equations with translations.\<close>

lemma (in group0) ltrans_inv_in: assumes A1: "V\<subseteq>G" and A2: "y\<in>G" and
  A3: "x \<in> LeftTranslation(G,P,y)``(GroupInv(G,P)``(V))"
  shows "y \<in> LeftTranslation(G,P,x)``(V)"
proof -
  have "x\<in>G"
  proof -
    from A2 have "LeftTranslation(G,P,y):G\<rightarrow>G" using group0_5_L1 by simp
    then have "LeftTranslation(G,P,y)``(GroupInv(G,P)``(V)) \<subseteq> G"
      using func1_1_L6 by simp
    with A3 show "x\<in>G" by auto
  qed
  have "\<exists>v\<in>V. x = y\<cdot>v\<inverse>"
  proof -
    have "GroupInv(G,P): G\<rightarrow>G" using groupAssum group0_2_T2
      by simp
    with assms obtain z where "z \<in> GroupInv(G,P)``(V)" and "x = y\<cdot>z"
      using func1_1_L6 ltrans_image by auto
    with A1 \<open>GroupInv(G,P): G\<rightarrow>G\<close> show ?thesis using func_imagedef by auto
  qed
  then obtain v where "v\<in>V" and "x = y\<cdot>v\<inverse>" by auto
  with A1 A2 have "y = x\<cdot>v" using inv_cancel_two by auto
  with assms \<open>x\<in>G\<close> \<open>v\<in>V\<close> show ?thesis using ltrans_image by auto
qed

text\<open>We can look at the result of interval arithmetic operation as union of
  translated sets.\<close>

lemma (in group0) image_ltrans_union: assumes "A\<subseteq>G" "B\<subseteq>G" shows
  "(P {lifted to subsets of} G)`\<langle>A,B\<rangle> = (\<Union>a\<in>A.  LeftTranslation(G,P,a)``(B))"
proof
  from assms have I: "(P {lifted to subsets of} G)`\<langle>A,B\<rangle> = {a\<cdot>b . \<langle>a,b\<rangle> \<in> A\<times>B}"
    using group_oper_assocA lift_subsets_explained by simp
  { fix c assume "c \<in> (P {lifted to subsets of} G)`\<langle>A,B\<rangle>"
    with I obtain a b where "c = a\<cdot>b" and "a\<in>A"  "b\<in>B" by auto
    hence "c \<in> {a\<cdot>b. b\<in>B}" by auto
    moreover from assms \<open>a\<in>A\<close> have 
      "LeftTranslation(G,P,a)``(B) = {a\<cdot>b. b\<in>B}" using ltrans_image by auto
    ultimately have "c \<in> LeftTranslation(G,P,a)``(B)" by simp
    with \<open>a\<in>A\<close> have "c \<in> (\<Union>a\<in>A.  LeftTranslation(G,P,a)``(B))" by auto
  } thus "(P {lifted to subsets of} G)`\<langle>A,B\<rangle> \<subseteq> (\<Union>a\<in>A.  LeftTranslation(G,P,a)``(B))"
    by auto
  { fix c assume "c \<in> (\<Union>a\<in>A.  LeftTranslation(G,P,a)``(B))"
    then obtain a where "a\<in>A" and "c \<in> LeftTranslation(G,P,a)``(B)"
      by auto
    moreover from assms \<open>a\<in>A\<close> have "LeftTranslation(G,P,a)``(B) = {a\<cdot>b. b\<in>B}"
      using ltrans_image by auto
    ultimately obtain b where "b\<in>B" and "c = a\<cdot>b" by auto
    with I \<open>a\<in>A\<close> have "c \<in> (P {lifted to subsets of} G)`\<langle>A,B\<rangle>" by auto
  } thus "(\<Union>a\<in>A. LeftTranslation(G,P,a)``(B)) \<subseteq> (P {lifted to subsets of} G)`\<langle>A,B\<rangle>"
    by auto
qed

text\<open>If the neutral element belongs to a set, then an element of group belongs
  the translation of that set.\<close>

lemma (in group0) neut_trans_elem: 
  assumes A1: "A\<subseteq>G" "g\<in>G" and A2: "\<one>\<in>A" 
  shows "g \<in> LeftTranslation(G,P,g)``(A)" "g \<in> RightTranslation(G,P,g)``(A)"
proof -
  from assms have "g\<cdot>\<one> \<in> LeftTranslation(G,P,g)``(A)"
    using ltrans_image by auto
  with A1 show "g \<in> LeftTranslation(G,P,g)``(A)" using group0_2_L2 by simp
  from assms have "\<one>\<cdot>g \<in> RightTranslation(G,P,g)``(A)"
    using rtrans_image by auto
  with A1 show "g \<in> RightTranslation(G,P,g)``(A)" using group0_2_L2 by simp
qed

text\<open>The neutral element belongs to the translation of a set by the inverse
  of an element that belongs to it.\<close>

lemma (in group0) elem_trans_neut: assumes A1: "A\<subseteq>G" and A2: "g\<in>A"
  shows "\<one> \<in> LeftTranslation(G,P,g\<inverse>)``(A)" "\<one> \<in> RightTranslation(G,P,g\<inverse>)``(A)"
proof -
  from assms have ginv:"g\<inverse> \<in> G" using inverse_in_group by auto
  with assms have "g\<inverse>\<cdot>g \<in> LeftTranslation(G,P,g\<inverse>)``(A)"
    using ltrans_image by auto
  moreover from assms have "g\<inverse>\<cdot>g = \<one>" using group0_2_L6 by auto
  ultimately show "\<one> \<in> LeftTranslation(G,P,g\<inverse>)``(A)" by simp
  from ginv assms have "g\<cdot>g\<inverse> \<in> RightTranslation(G,P,g\<inverse>)``(A)"
    using rtrans_image by auto
  moreover from assms have "g\<cdot>g\<inverse> = \<one>" using group0_2_L6 by auto
  ultimately show "\<one> \<in> RightTranslation(G,P,g\<inverse>)``(A)" by simp
qed

subsection\<open>Odd functions\<close>

text\<open>This section is about odd functions.\<close>

text\<open>Odd functions are those that commute with the group inverse:
  $f(a^{-1}) = (f(a))^{-1}.$\<close>

definition
  "IsOdd(G,P,f) \<equiv> (\<forall>a\<in>G. f`(GroupInv(G,P)`(a)) = GroupInv(G,P)`(f`(a)) )"

text\<open>Let's see the definition of an odd function in a more readable 
  notation.\<close>

lemma (in group0) group0_6_L1: 
  shows "IsOdd(G,P,p) \<longleftrightarrow> ( \<forall>a\<in>G. p`(a\<inverse>) = (p`(a))\<inverse> )"
  using IsOdd_def by simp

text\<open>We can express the definition of an odd function in two ways.\<close>

lemma (in group0) group0_6_L2:
  assumes A1: "p : G\<rightarrow>G" 
  shows 
  "(\<forall>a\<in>G. p`(a\<inverse>) = (p`(a))\<inverse>) \<longleftrightarrow> (\<forall>a\<in>G. (p`(a\<inverse>))\<inverse> = p`(a))"
proof
  assume "\<forall>a\<in>G. p`(a\<inverse>) = (p`(a))\<inverse>"
  with A1 show "\<forall>a\<in>G. (p`(a\<inverse>))\<inverse> = p`(a)"
    using apply_funtype group_inv_of_inv by simp
next assume A2: "\<forall>a\<in>G. (p`(a\<inverse>))\<inverse> = p`(a)"
  { fix a assume "a\<in>G"
    with A1 A2  have 
      "p`(a\<inverse>) \<in> G" and "((p`(a\<inverse>))\<inverse>)\<inverse> =  (p`(a))\<inverse>"
    using apply_funtype inverse_in_group by auto
  then have "p`(a\<inverse>) = (p`(a))\<inverse>"
    using group_inv_of_inv by simp
  } then show "\<forall>a\<in>G. p`(a\<inverse>) = (p`(a))\<inverse>" by simp
qed

end
