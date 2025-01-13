(* 
This file is a part of IsarMathLib - 
a library of formalized mathematics for Isabelle/Isar.

Copyright (C) 2005, 2006  Slawomir Kolodynski

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

section \<open>Abelian Group\<close>

theory AbelianGroup_ZF imports Group_ZF

begin

text\<open>A group is called ``abelian`` if its operation is commutative, i.e.
  $P\langle a,b \rangle  = P\langle a,b \rangle$ for all group 
  elements $a,b$, where $P$ is the group operation. It is customary
  to use the additive notation for abelian groups, so this condition
  is typically written as $a+b = b+a$. We will be using multiplicative 
  notation though (in which the commutativity condition 
  of the operation is written as $a\cdot b = b\cdot a$), just to avoid
  the hassle of changing the notation we used for general groups. 
\<close>

subsection\<open>Rearrangement formulae\<close>

text\<open>This section is not interesting and should not be read.
  Here we will prove formulas is which right hand side uses the same
  factors as the left hand side, just in different order. These facts
  are obvious in informal math sense, but Isabelle prover is not able
  to derive them automatically, so we have to provide explicit proofs. \<close>

text\<open>Proving the facts about associative and commutative operations is 
  quite tedious in formalized mathematics. To a human the thing is simple:
  we can arrange the elements in any order and put parantheses wherever we 
  want, it is all the same. However, formalizing this statement would be 
  rather difficult (I think). The next lemma attempts a quasi-algorithmic
  approach to this type of problem. To prove that two expressions are equal, 
  we first strip one from parantheses, then rearrange the elements in proper 
  order, then put the parantheses where we want them to be. The algorithm for 
  rearrangement is easy to describe: we keep putting the first element 
  (from the right) that is in the wrong place at the left-most position
  until we get the proper arrangement. 
  As far removing parantheses is concerned Isabelle does its job 
  automatically.\<close>

lemma (in group0) group0_4_L2:
  assumes A1:"P {is commutative on} G"
  and A2:"a\<in>G" "b\<in>G" "c\<in>G" "d\<in>G" "E\<in>G" "F\<in>G"
  shows "(a\<cdot>b)\<cdot>(c\<cdot>d)\<cdot>(E\<cdot>F) = (a\<cdot>(d\<cdot>F))\<cdot>(b\<cdot>(c\<cdot>E))"
proof -
  from A2 have "(a\<cdot>b)\<cdot>(c\<cdot>d)\<cdot>(E\<cdot>F) = a\<cdot>b\<cdot>c\<cdot>d\<cdot>E\<cdot>F"
    using group_op_closed group_oper_assoc
    by simp
  also have  "a\<cdot>b\<cdot>c\<cdot>d\<cdot>E\<cdot>F = a\<cdot>d\<cdot>F\<cdot>b\<cdot>c\<cdot>E"
  proof -
    from A1 A2 have "a\<cdot>b\<cdot>c\<cdot>d\<cdot>E\<cdot>F = F\<cdot>(a\<cdot>b\<cdot>c\<cdot>d\<cdot>E)"
      using IsCommutative_def group_op_closed 
      by simp
    also from A2 have "F\<cdot>(a\<cdot>b\<cdot>c\<cdot>d\<cdot>E) = F\<cdot>a\<cdot>b\<cdot>c\<cdot>d\<cdot>E"
      using group_op_closed group_oper_assoc
      by simp
    also from A1 A2 have "F\<cdot>a\<cdot>b\<cdot>c\<cdot>d\<cdot>E = d\<cdot>(F\<cdot>a\<cdot>b\<cdot>c)\<cdot>E"
      using IsCommutative_def group_op_closed
      by simp
    also from A2 have "d\<cdot>(F\<cdot>a\<cdot>b\<cdot>c)\<cdot>E = d\<cdot>F\<cdot>a\<cdot>b\<cdot>c\<cdot>E"
      using group_op_closed group_oper_assoc
      by simp
    also from A1 A2 have " d\<cdot>F\<cdot>a\<cdot>b\<cdot>c\<cdot>E = a\<cdot>(d\<cdot>F)\<cdot>b\<cdot>c\<cdot>E"
      using IsCommutative_def group_op_closed
      by simp
    also from A2 have "a\<cdot>(d\<cdot>F)\<cdot>b\<cdot>c\<cdot>E = a\<cdot>d\<cdot>F\<cdot>b\<cdot>c\<cdot>E" 
      using group_op_closed group_oper_assoc
      by simp
    finally show ?thesis by simp
  qed
  also from A2 have "a\<cdot>d\<cdot>F\<cdot>b\<cdot>c\<cdot>E = (a\<cdot>(d\<cdot>F))\<cdot>(b\<cdot>(c\<cdot>E))"
    using group_op_closed group_oper_assoc
    by simp
  finally show ?thesis by simp
qed
  
text\<open>Another useful rearrangement.\<close>

lemma (in group0) group0_4_L3:
  assumes A1:"P {is commutative on} G" 
  and A2: "a\<in>G"  "b\<in>G" and A3: "c\<in>G"  "d\<in>G"  "E\<in>G"  "F\<in>G"
  shows "a\<cdot>b\<cdot>((c\<cdot>d)\<inverse>\<cdot>(E\<cdot>F)\<inverse>) = (a\<cdot>(E\<cdot>c)\<inverse>)\<cdot>(b\<cdot>(F\<cdot>d)\<inverse>)"
proof -
  from A3 have T1:
    "c\<inverse>\<in>G" "d\<inverse>\<in>G" "E\<inverse>\<in>G" "F\<inverse>\<in>G" "(c\<cdot>d)\<inverse>\<in>G" "(E\<cdot>F)\<inverse>\<in>G"
    using inverse_in_group group_op_closed 
    by auto
  from A2 T1 have 
    "a\<cdot>b\<cdot>((c\<cdot>d)\<inverse>\<cdot>(E\<cdot>F)\<inverse>) = a\<cdot>b\<cdot>(c\<cdot>d)\<inverse>\<cdot>(E\<cdot>F)\<inverse>"
    using group_op_closed group_oper_assoc
    by simp
  also from A2 A3 have 
    "a\<cdot>b\<cdot>(c\<cdot>d)\<inverse>\<cdot>(E\<cdot>F)\<inverse> = (a\<cdot>b)\<cdot>(d\<inverse>\<cdot>c\<inverse>)\<cdot>(F\<inverse>\<cdot>E\<inverse>)"
    using group_inv_of_two by simp
   also from A1 A2 T1 have 
    "(a\<cdot>b)\<cdot>(d\<inverse>\<cdot>c\<inverse>)\<cdot>(F\<inverse>\<cdot>E\<inverse>) = (a\<cdot>(c\<inverse>\<cdot>E\<inverse>))\<cdot>(b\<cdot>(d\<inverse>\<cdot>F\<inverse>))"
    using group0_4_L2 by simp
  also from A2 A3 have 
    "(a\<cdot>(c\<inverse>\<cdot>E\<inverse>))\<cdot>(b\<cdot>(d\<inverse>\<cdot>F\<inverse>)) = (a\<cdot>(E\<cdot>c)\<inverse>)\<cdot>(b\<cdot>(F\<cdot>d)\<inverse>)"
    using group_inv_of_two by simp
  finally show ?thesis by simp
qed

text\<open>Some useful rearrangements for two elements of a group.\<close>

lemma (in group0) group0_4_L4:
  assumes A1:"P {is commutative on} G"
  and A2: "a\<in>G" "b\<in>G"
  shows 
  "b\<inverse>\<cdot>a\<inverse> = a\<inverse>\<cdot>b\<inverse>" 
  "(a\<cdot>b)\<inverse> = a\<inverse>\<cdot>b\<inverse>" 
  "(a\<cdot>b\<inverse>)\<inverse> = a\<inverse>\<cdot>b"
proof -
  from A2 have T1: "b\<inverse>\<in>G" "a\<inverse>\<in>G" using inverse_in_group by auto
  with A1 show "b\<inverse>\<cdot>a\<inverse> = a\<inverse>\<cdot>b\<inverse>" using IsCommutative_def by simp
  with A2 show "(a\<cdot>b)\<inverse> = a\<inverse>\<cdot>b\<inverse>" using group_inv_of_two by simp
  from A2 T1 have "(a\<cdot>b\<inverse>)\<inverse> = (b\<inverse>)\<inverse>\<cdot>a\<inverse>" using group_inv_of_two by simp
  with A1 A2 T1 show "(a\<cdot>b\<inverse>)\<inverse> = a\<inverse>\<cdot>b" 
    using group_inv_of_inv IsCommutative_def by simp
qed
 
text\<open>Another bunch of useful rearrangements with three elements.\<close>

lemma (in group0) group0_4_L4A: 
  assumes A1: "P {is commutative on} G"
  and A2: "a\<in>G"  "b\<in>G"  "c\<in>G"
  shows 
  "a\<cdot>b\<cdot>c = c\<cdot>a\<cdot>b" 
  "a\<inverse>\<cdot>(b\<inverse>\<cdot>c\<inverse>)\<inverse> = (a\<cdot>(b\<cdot>c)\<inverse>)\<inverse>" 
  "a\<cdot>(b\<cdot>c)\<inverse> = a\<cdot>b\<inverse>\<cdot>c\<inverse>" 
  "a\<cdot>(b\<cdot>c\<inverse>)\<inverse> = a\<cdot>b\<inverse>\<cdot>c" 
  "a\<cdot>b\<inverse>\<cdot>c\<inverse> = a\<cdot>c\<inverse>\<cdot>b\<inverse>"
proof -
  from A1 A2 have "a\<cdot>b\<cdot>c = c\<cdot>(a\<cdot>b)"
    using IsCommutative_def group_op_closed
    by simp
  with A2 show "a\<cdot>b\<cdot>c = c\<cdot>a\<cdot>b" using
     group_op_closed group_oper_assoc
    by simp
  from A2 have T: 
    "b\<inverse>\<in>G"  "c\<inverse>\<in>G"  "b\<inverse>\<cdot>c\<inverse> \<in> G"  "a\<cdot>b \<in> G"
    using inverse_in_group group_op_closed
    by auto
  with A1 A2 show "a\<inverse>\<cdot>(b\<inverse>\<cdot>c\<inverse>)\<inverse> = (a\<cdot>(b\<cdot>c)\<inverse>)\<inverse>"
    using group_inv_of_two IsCommutative_def 
    by simp
  from A1 A2 T have "a\<cdot>(b\<cdot>c)\<inverse> = a\<cdot>(b\<inverse>\<cdot>c\<inverse>)"
    using group_inv_of_two IsCommutative_def by simp
  with A2 T show "a\<cdot>(b\<cdot>c)\<inverse> = a\<cdot>b\<inverse>\<cdot>c\<inverse>"
    using group_oper_assoc by simp
  from A1 A2 T have "a\<cdot>(b\<cdot>c\<inverse>)\<inverse> = a\<cdot>(b\<inverse>\<cdot>(c\<inverse>)\<inverse>)"
    using group_inv_of_two IsCommutative_def by simp
  with A2 T show "a\<cdot>(b\<cdot>c\<inverse>)\<inverse> = a\<cdot>b\<inverse>\<cdot>c"
    using group_oper_assoc group_inv_of_inv by simp
  from A1 A2 T have "a\<cdot>b\<inverse>\<cdot>c\<inverse> = a\<cdot>(c\<inverse>\<cdot>b\<inverse>)"
    using group_oper_assoc IsCommutative_def by simp
  with A2 T show "a\<cdot>b\<inverse>\<cdot>c\<inverse> = a\<cdot>c\<inverse>\<cdot>b\<inverse>"
    using group_oper_assoc by simp
qed

text\<open>Another useful rearrangement.\<close>

lemma (in group0) group0_4_L4B: 
  assumes "P {is commutative on} G"
  and "a\<in>G"  "b\<in>G"  "c\<in>G"
  shows "a\<cdot>b\<inverse>\<cdot>(b\<cdot>c\<inverse>) = a\<cdot>c\<inverse>"  
  using assms inverse_in_group group_op_closed 
    group0_4_L4 group_oper_assoc inv_cancel_two by simp

text\<open>A couple of permutations of order for three alements.\<close>

lemma (in group0) group0_4_L4C: 
  assumes A1: "P {is commutative on} G"
  and A2: "a\<in>G" "b\<in>G" "c\<in>G"
  shows
  "a\<cdot>b\<cdot>c = c\<cdot>a\<cdot>b"
  "a\<cdot>b\<cdot>c = a\<cdot>(c\<cdot>b)"
  "a\<cdot>b\<cdot>c = c\<cdot>(a\<cdot>b)"
  "a\<cdot>b\<cdot>c = c\<cdot>b\<cdot>a"
proof -
  from A1 A2 show I: "a\<cdot>b\<cdot>c = c\<cdot>a\<cdot>b"
    using group0_4_L4A by simp
  also from A1 A2 have "c\<cdot>a\<cdot>b = a\<cdot>c\<cdot>b"
    using IsCommutative_def by simp
  also from A2 have "a\<cdot>c\<cdot>b = a\<cdot>(c\<cdot>b)"
    using group_oper_assoc by simp
  finally show "a\<cdot>b\<cdot>c = a\<cdot>(c\<cdot>b)" by simp
  from A2 I show "a\<cdot>b\<cdot>c = c\<cdot>(a\<cdot>b)"
    using group_oper_assoc by simp
  also from A1 A2 have "c\<cdot>(a\<cdot>b) = c\<cdot>(b\<cdot>a)"
    using IsCommutative_def by simp
  also from A2 have "c\<cdot>(b\<cdot>a) = c\<cdot>b\<cdot>a"
    using group_oper_assoc by simp
  finally show "a\<cdot>b\<cdot>c = c\<cdot>b\<cdot>a" by simp
qed

text\<open>Some rearangement with three elements and inverse.\<close>

lemma (in group0) group0_4_L4D:
  assumes A1: "P {is commutative on} G"
  and A2: "a\<in>G"  "b\<in>G"  "c\<in>G"
  shows 
  "a\<inverse>\<cdot>b\<inverse>\<cdot>c = c\<cdot>a\<inverse>\<cdot>b\<inverse>"
  "b\<inverse>\<cdot>a\<inverse>\<cdot>c = c\<cdot>a\<inverse>\<cdot>b\<inverse>"
  "(a\<inverse>\<cdot>b\<cdot>c)\<inverse> = a\<cdot>b\<inverse>\<cdot>c\<inverse>"
proof -
  from A2 have T: 
    "a\<inverse> \<in> G"  "b\<inverse> \<in> G"  "c\<inverse>\<in>G"
    using inverse_in_group by auto
  with A1 A2 show 
    "a\<inverse>\<cdot>b\<inverse>\<cdot>c = c\<cdot>a\<inverse>\<cdot>b\<inverse>"
    "b\<inverse>\<cdot>a\<inverse>\<cdot>c = c\<cdot>a\<inverse>\<cdot>b\<inverse>"
    using  group0_4_L4A by auto
  from A1 A2 T show "(a\<inverse>\<cdot>b\<cdot>c)\<inverse> = a\<cdot>b\<inverse>\<cdot>c\<inverse>"
    using group_inv_of_three group_inv_of_inv group0_4_L4C
    by simp
qed

text\<open>Another rearrangement lemma with three elements and equation.\<close>

lemma (in group0) group0_4_L5: assumes A1:"P {is commutative on} G" 
  and A2: "a\<in>G"  "b\<in>G"  "c\<in>G"
  and A3: "c = a\<cdot>b\<inverse>"
  shows "a = b\<cdot>c"
proof - 
  from A2 A3 have "c\<cdot>(b\<inverse>)\<inverse> = a"
    using inverse_in_group group0_2_L18
    by simp
  with A1 A2 show ?thesis using 
     group_inv_of_inv IsCommutative_def by simp
qed

text\<open>In abelian groups we can cancel an element with its inverse
  even if separated by another element.\<close>

lemma (in group0) group0_4_L6A: assumes A1: "P {is commutative on} G"
  and A2: "a\<in>G"  "b\<in>G"
  shows 
  "a\<cdot>b\<cdot>a\<inverse> = b"
  "a\<inverse>\<cdot>b\<cdot>a = b"
  "a\<inverse>\<cdot>(b\<cdot>a) = b"
  "a\<cdot>(b\<cdot>a\<inverse>) = b"
proof -
  from A1 A2 have 
    "a\<cdot>b\<cdot>a\<inverse> = a\<inverse>\<cdot>a\<cdot>b"
    using inverse_in_group group0_4_L4A by blast
  also from A2 have "\<dots> = b"
    using group0_2_L6 group0_2_L2 by simp
  finally show "a\<cdot>b\<cdot>a\<inverse> = b" by simp
  from A1 A2 have 
    "a\<inverse>\<cdot>b\<cdot>a = a\<cdot>a\<inverse>\<cdot>b"
    using inverse_in_group group0_4_L4A by blast
  also from A2 have "\<dots> = b"
    using group0_2_L6 group0_2_L2 by simp
  finally show "a\<inverse>\<cdot>b\<cdot>a = b" by simp
  moreover from A2 have "a\<inverse>\<cdot>b\<cdot>a = a\<inverse>\<cdot>(b\<cdot>a)"
    using inverse_in_group group_oper_assoc by simp
  ultimately show "a\<inverse>\<cdot>(b\<cdot>a) = b" by simp
  from A1 A2 show "a\<cdot>(b\<cdot>a\<inverse>) = b"
     using inverse_in_group IsCommutative_def inv_cancel_two
     by simp
qed

text\<open>Another lemma about cancelling with two elements.\<close>

lemma (in group0) group0_4_L6AA: 
  assumes A1: "P {is commutative on} G" and A2: "a\<in>G"  "b\<in>G"
  shows "a\<cdot>b\<inverse>\<cdot>a\<inverse> = b\<inverse>"
  using assms inverse_in_group group0_4_L6A
  by auto

text\<open>Another lemma about cancelling with two elements.\<close>

lemma (in group0) group0_4_L6AB: 
  assumes A1: "P {is commutative on} G" and A2: "a\<in>G"  "b\<in>G"
  shows 
  "a\<cdot>(a\<cdot>b)\<inverse> = b\<inverse>"
  "a\<cdot>(b\<cdot>a\<inverse>) = b"
proof -
    from A2 have "a\<cdot>(a\<cdot>b)\<inverse> = a\<cdot>(b\<inverse>\<cdot>a\<inverse>)"
      using group_inv_of_two by simp
    also from A2 have "\<dots> = a\<cdot>b\<inverse>\<cdot>a\<inverse>"
      using inverse_in_group group_oper_assoc by simp
    also from A1 A2 have "\<dots> =  b\<inverse>"
      using group0_4_L6AA by simp
    finally show "a\<cdot>(a\<cdot>b)\<inverse> = b\<inverse>" by simp
    from A1 A2 have "a\<cdot>(b\<cdot>a\<inverse>) = a\<cdot>(a\<inverse>\<cdot>b)"
      using inverse_in_group IsCommutative_def by simp
    also from A2 have "\<dots> = b"
      using inverse_in_group group_oper_assoc group0_2_L6 group0_2_L2
      by simp
    finally show "a\<cdot>(b\<cdot>a\<inverse>) = b" by simp
qed

text\<open>Another lemma about cancelling with two elements.\<close>

lemma (in group0) group0_4_L6AC: 
  assumes "P {is commutative on} G" and "a\<in>G"  "b\<in>G"
  shows "a\<cdot>(a\<cdot>b\<inverse>)\<inverse> = b"
  using assms inverse_in_group group0_4_L6AB group_inv_of_inv
  by simp


text\<open>In abelian groups we can cancel an element with its inverse
  even if separated by two other elements.\<close>

lemma (in group0) group0_4_L6B: assumes A1: "P {is commutative on} G"
  and A2: "a\<in>G"  "b\<in>G"  "c\<in>G" 
  shows 
  "a\<cdot>b\<cdot>c\<cdot>a\<inverse> = b\<cdot>c"
  "a\<inverse>\<cdot>b\<cdot>c\<cdot>a = b\<cdot>c"
proof -
   from A2 have 
     "a\<cdot>b\<cdot>c\<cdot>a\<inverse> = a\<cdot>(b\<cdot>c)\<cdot>a\<inverse>"
     "a\<inverse>\<cdot>b\<cdot>c\<cdot>a = a\<inverse>\<cdot>(b\<cdot>c)\<cdot>a"
    using group_op_closed group_oper_assoc inverse_in_group
    by auto
  with A1 A2 show
    "a\<cdot>b\<cdot>c\<cdot>a\<inverse> = b\<cdot>c"
    "a\<inverse>\<cdot>b\<cdot>c\<cdot>a = b\<cdot>c"
    using group_op_closed group0_4_L6A
    by auto
qed

text\<open>In abelian groups we can cancel an element with its inverse
  even if separated by three other elements.\<close>

lemma (in group0) group0_4_L6C: assumes A1: "P {is commutative on} G"
  and A2: "a\<in>G" "b\<in>G" "c\<in>G" "d\<in>G"
  shows "a\<cdot>b\<cdot>c\<cdot>d\<cdot>a\<inverse> = b\<cdot>c\<cdot>d" 
proof -
  from A2 have "a\<cdot>b\<cdot>c\<cdot>d\<cdot>a\<inverse> = a\<cdot>(b\<cdot>c\<cdot>d)\<cdot>a\<inverse>"
    using group_op_closed group_oper_assoc
    by simp
  with A1 A2 show ?thesis 
    using group_op_closed group0_4_L6A 
    by simp
qed

text\<open>Another couple of useful rearrangements of three elements
  and cancelling.\<close>

lemma (in group0) group0_4_L6D: 
  assumes A1: "P {is commutative on} G"
  and A2: "a\<in>G"  "b\<in>G"  "c\<in>G"
  shows 
  "a\<cdot>b\<inverse>\<cdot>(a\<cdot>c\<inverse>)\<inverse> = c\<cdot>b\<inverse>"
  "(a\<cdot>c)\<inverse>\<cdot>(b\<cdot>c) = a\<inverse>\<cdot>b"
  "a\<cdot>(b\<cdot>(c\<cdot>a\<inverse>\<cdot>b\<inverse>)) = c"
  "a\<cdot>b\<cdot>c\<inverse>\<cdot>(c\<cdot>a\<inverse>) = b"
proof -
  from A2 have T: 
    "a\<inverse> \<in> G"  "b\<inverse> \<in> G"  "c\<inverse> \<in> G" 
    "a\<cdot>b \<in> G"  "a\<cdot>b\<inverse> \<in> G"  "c\<inverse>\<cdot>a\<inverse> \<in> G"  "c\<cdot>a\<inverse> \<in> G"
    using inverse_in_group group_op_closed by auto
  with A1 A2 show "a\<cdot>b\<inverse>\<cdot>(a\<cdot>c\<inverse>)\<inverse> = c\<cdot>b\<inverse>"
    using group0_2_L12 group_oper_assoc group0_4_L6B
    IsCommutative_def by simp
  from A2 T have "(a\<cdot>c)\<inverse>\<cdot>(b\<cdot>c) = c\<inverse>\<cdot>a\<inverse>\<cdot>b\<cdot>c"
    using group_inv_of_two group_oper_assoc by simp
  also from A1 A2 T have "\<dots> = a\<inverse>\<cdot>b"
    using group0_4_L6B by simp
  finally show "(a\<cdot>c)\<inverse>\<cdot>(b\<cdot>c) = a\<inverse>\<cdot>b"
    by simp
  from A1 A2 T show "a\<cdot>(b\<cdot>(c\<cdot>a\<inverse>\<cdot>b\<inverse>)) = c"
    using group_oper_assoc group0_4_L6B group0_4_L6A
    by simp
  from T have "a\<cdot>b\<cdot>c\<inverse>\<cdot>(c\<cdot>a\<inverse>) = a\<cdot>b\<cdot>(c\<inverse>\<cdot>(c\<cdot>a\<inverse>))"
    using group_oper_assoc by simp
  also from A1 A2 T have "\<dots> = b"
    using group_oper_assoc group0_2_L6 group0_2_L2 group0_4_L6A
    by simp
  finally show "a\<cdot>b\<cdot>c\<inverse>\<cdot>(c\<cdot>a\<inverse>) = b" by simp
qed

text\<open>Another useful rearrangement of three elements
  and cancelling.\<close>

lemma (in group0) group0_4_L6E: 
  assumes A1: "P {is commutative on} G"
  and A2: "a\<in>G"  "b\<in>G"  "c\<in>G"
  shows 
  "a\<cdot>b\<cdot>(a\<cdot>c)\<inverse> = b\<cdot>c\<inverse>"
proof -
  from A2 have T: "b\<inverse> \<in> G"  "c\<inverse> \<in> G"
    using inverse_in_group by auto
  with A1 A2 have
    "a\<cdot>(b\<inverse>)\<inverse>\<cdot>(a\<cdot>(c\<inverse>)\<inverse>)\<inverse> = c\<inverse>\<cdot>(b\<inverse>)\<inverse>"
    using group0_4_L6D by simp
  with A1 A2 T show "a\<cdot>b\<cdot>(a\<cdot>c)\<inverse> = b\<cdot>c\<inverse>"
    using group_inv_of_inv IsCommutative_def
    by simp
qed

text\<open>A rearrangement with two elements and canceelling,
  special case of \<open>group0_4_L6D\<close> when $c=b^{-1}$.\<close>

lemma (in group0) group0_4_L6F: 
  assumes A1: "P {is commutative on} G"
  and A2: "a\<in>G"  "b\<in>G"
  shows "a\<cdot>b\<inverse>\<cdot>(a\<cdot>b)\<inverse> = b\<inverse>\<cdot>b\<inverse>"
proof -
  from A2 have "b\<inverse> \<in> G" 
    using inverse_in_group by simp
  with A1 A2 have "a\<cdot>b\<inverse>\<cdot>(a\<cdot>(b\<inverse>)\<inverse>)\<inverse> = b\<inverse>\<cdot>b\<inverse>"
    using group0_4_L6D by simp
  with A2 show "a\<cdot>b\<inverse>\<cdot>(a\<cdot>b)\<inverse> = b\<inverse>\<cdot>b\<inverse>"
    using group_inv_of_inv by simp
qed

text\<open>Some other rearrangements with four elements.
  The algorithm for proof as in \<open>group0_4_L2\<close>
  works very well here.\<close>

lemma (in group0) rearr_ab_gr_4_elemA:
  assumes A1: "P {is commutative on} G"
  and A2: "a\<in>G"  "b\<in>G"  "c\<in>G"  "d\<in>G"
  shows 
  "a\<cdot>b\<cdot>c\<cdot>d = a\<cdot>d\<cdot>b\<cdot>c"
  "a\<cdot>b\<cdot>c\<cdot>d = a\<cdot>c\<cdot>(b\<cdot>d)"
proof -
  from A1 A2 have "a\<cdot>b\<cdot>c\<cdot>d = d\<cdot>(a\<cdot>b\<cdot>c)"
    using  IsCommutative_def group_op_closed
    by simp
  also from A2 have "\<dots> = d\<cdot>a\<cdot>b\<cdot>c"
    using group_op_closed group_oper_assoc
    by simp
  also from A1 A2 have "\<dots> = a\<cdot>d\<cdot>b\<cdot>c"
    using IsCommutative_def group_op_closed
    by simp
  finally show "a\<cdot>b\<cdot>c\<cdot>d = a\<cdot>d\<cdot>b\<cdot>c"
    by simp
  from A1 A2 have "a\<cdot>b\<cdot>c\<cdot>d = c\<cdot>(a\<cdot>b)\<cdot>d"
    using IsCommutative_def group_op_closed
    by simp
  also from A2 have "\<dots> = c\<cdot>a\<cdot>b\<cdot>d"
    using group_op_closed group_oper_assoc
    by simp
  also from A1 A2 have "\<dots> = a\<cdot>c\<cdot>b\<cdot>d"
    using IsCommutative_def group_op_closed
    by simp
  also from A2 have "\<dots> = a\<cdot>c\<cdot>(b\<cdot>d)"
    using group_op_closed group_oper_assoc
    by simp
  finally show "a\<cdot>b\<cdot>c\<cdot>d = a\<cdot>c\<cdot>(b\<cdot>d)"
    by simp
qed

text\<open>Some rearrangements with four elements and inverse
  that are applications of \<open>rearr_ab_gr_4_elem\<close> 
\<close>

lemma (in group0) rearr_ab_gr_4_elemB:
  assumes A1: "P {is commutative on} G"
  and A2: "a\<in>G"  "b\<in>G"  "c\<in>G"  "d\<in>G"
  shows 
  "a\<cdot>b\<inverse>\<cdot>c\<inverse>\<cdot>d\<inverse> = a\<cdot>d\<inverse>\<cdot>b\<inverse>\<cdot>c\<inverse>"
  "a\<cdot>b\<cdot>c\<cdot>d\<inverse> = a\<cdot>d\<inverse>\<cdot>b\<cdot>c"
  "a\<cdot>b\<cdot>c\<inverse>\<cdot>d\<inverse> =  a\<cdot>c\<inverse>\<cdot>(b\<cdot>d\<inverse>)"
proof -
  from A2 have T: "b\<inverse> \<in> G"  "c\<inverse> \<in> G"  "d\<inverse> \<in> G"
    using inverse_in_group by auto
  with A1 A2 show 
    "a\<cdot>b\<inverse>\<cdot>c\<inverse>\<cdot>d\<inverse> = a\<cdot>d\<inverse>\<cdot>b\<inverse>\<cdot>c\<inverse>"
    "a\<cdot>b\<cdot>c\<cdot>d\<inverse> = a\<cdot>d\<inverse>\<cdot>b\<cdot>c"
    "a\<cdot>b\<cdot>c\<inverse>\<cdot>d\<inverse> =  a\<cdot>c\<inverse>\<cdot>(b\<cdot>d\<inverse>)"
    using rearr_ab_gr_4_elemA by auto
qed
  
text\<open>Some rearrangement lemmas with four elements.\<close>
 
lemma (in group0) group0_4_L7: 
  assumes A1: "P {is commutative on} G"
  and A2: "a\<in>G"  "b\<in>G"  "c\<in>G"  "d\<in>G"
  shows 
  "a\<cdot>b\<cdot>c\<cdot>d\<inverse> = a\<cdot>d\<inverse>\<cdot> b\<cdot>c" 
  "a\<cdot>d\<cdot>(b\<cdot>d\<cdot>(c\<cdot>d))\<inverse> = a\<cdot>(b\<cdot>c)\<inverse>\<cdot>d\<inverse>"
  "a\<cdot>(b\<cdot>c)\<cdot>d = a\<cdot>b\<cdot>d\<cdot>c"
proof -
  from A2 have T:
    "b\<cdot>c \<in> G" "d\<inverse> \<in> G" "b\<inverse>\<in>G" "c\<inverse>\<in>G" 
    "d\<inverse>\<cdot>b \<in> G" "c\<inverse>\<cdot>d \<in> G" "(b\<cdot>c)\<inverse> \<in> G"
    "b\<cdot>d \<in> G"  "b\<cdot>d\<cdot>c \<in> G"  "(b\<cdot>d\<cdot>c)\<inverse> \<in> G"
    "a\<cdot>d \<in> G"  "b\<cdot>c \<in> G"
    using group_op_closed inverse_in_group 
    by auto
  with A1 A2 have "a\<cdot>b\<cdot>c\<cdot>d\<inverse> = a\<cdot>(d\<inverse>\<cdot>b\<cdot>c)"
    using group_oper_assoc group0_4_L4A by simp
  also from A2 T have "a\<cdot>(d\<inverse>\<cdot>b\<cdot>c) = a\<cdot>d\<inverse>\<cdot>b\<cdot>c"
    using group_oper_assoc by simp 
  finally show "a\<cdot>b\<cdot>c\<cdot>d\<inverse> = a\<cdot>d\<inverse>\<cdot> b\<cdot>c" by simp
  from A2 T have "a\<cdot>d\<cdot>(b\<cdot>d\<cdot>(c\<cdot>d))\<inverse> = a\<cdot>d\<cdot>(d\<inverse>\<cdot>(b\<cdot>d\<cdot>c)\<inverse>)"
    using group_oper_assoc group_inv_of_two by simp
  also from A2 T have "\<dots> = a\<cdot>(b\<cdot>d\<cdot>c)\<inverse>"
    using group_oper_assoc inv_cancel_two by simp
  also from A1 A2 have "\<dots> =  a\<cdot>(d\<cdot>(b\<cdot>c))\<inverse>"
    using IsCommutative_def group_oper_assoc by simp
  also from A2 T have "\<dots> = a\<cdot>((b\<cdot>c)\<inverse>\<cdot>d\<inverse>)"
    using group_inv_of_two by simp
  also from A2 T have "\<dots> =  a\<cdot>(b\<cdot>c)\<inverse>\<cdot>d\<inverse>"
    using group_oper_assoc by simp
  finally show "a\<cdot>d\<cdot>(b\<cdot>d\<cdot>(c\<cdot>d))\<inverse> = a\<cdot>(b\<cdot>c)\<inverse>\<cdot>d\<inverse>"
    by simp
  from A2 have "a\<cdot>(b\<cdot>c)\<cdot>d = a\<cdot>(b\<cdot>(c\<cdot>d))"
    using group_op_closed group_oper_assoc by simp
  also from A1 A2 have "\<dots> =  a\<cdot>(b\<cdot>(d\<cdot>c))"
    using IsCommutative_def group_op_closed by simp
  also from A2 have "\<dots> =  a\<cdot>b\<cdot>d\<cdot>c"
    using group_op_closed group_oper_assoc by simp
  finally show "a\<cdot>(b\<cdot>c)\<cdot>d = a\<cdot>b\<cdot>d\<cdot>c" by simp
qed

text\<open>Some other rearrangements with four elements.\<close>

lemma (in group0) group0_4_L8: 
  assumes A1: "P {is commutative on} G"
  and A2: "a\<in>G"  "b\<in>G"  "c\<in>G"  "d\<in>G"
  shows 
  "a\<cdot>(b\<cdot>c)\<inverse> = (a\<cdot>d\<inverse>\<cdot>c\<inverse>)\<cdot>(d\<cdot>b\<inverse>)"
  "a\<cdot>b\<cdot>(c\<cdot>d) = c\<cdot>a\<cdot>(b\<cdot>d)"
  "a\<cdot>b\<cdot>(c\<cdot>d) = a\<cdot>c\<cdot>(b\<cdot>d)"
  "a\<cdot>(b\<cdot>c\<inverse>)\<cdot>d = a\<cdot>b\<cdot>d\<cdot>c\<inverse>"
  "(a\<cdot>b)\<cdot>(c\<cdot>d)\<inverse>\<cdot>(b\<cdot>d\<inverse>)\<inverse> = a\<cdot>c\<inverse>"
proof -
  from A2 have T:
    "b\<cdot>c \<in> G" "a\<cdot>b \<in> G" "d\<inverse> \<in> G" "b\<inverse>\<in>G" "c\<inverse>\<in>G" 
    "d\<inverse>\<cdot>b \<in> G" "c\<inverse>\<cdot>d \<in> G" "(b\<cdot>c)\<inverse> \<in> G"
    "a\<cdot>b \<in> G"  "(c\<cdot>d)\<inverse> \<in> G"  "(b\<cdot>d\<inverse>)\<inverse> \<in> G"  "d\<cdot>b\<inverse> \<in> G"
    using group_op_closed inverse_in_group 
    by auto
  from A2 have "a\<cdot>(b\<cdot>c)\<inverse> = a\<cdot>c\<inverse>\<cdot>b\<inverse>" using group0_2_L14A by blast
  moreover from A2 have "a\<cdot>c\<inverse> = (a\<cdot>d\<inverse>)\<cdot>(d\<cdot>c\<inverse>)" using group0_2_L14A
    by blast
  ultimately have "a\<cdot>(b\<cdot>c)\<inverse> = (a\<cdot>d\<inverse>)\<cdot>(d\<cdot>c\<inverse>)\<cdot>b\<inverse>" by simp
  with A1 A2 T have "a\<cdot>(b\<cdot>c)\<inverse>= a\<cdot>d\<inverse>\<cdot>(c\<inverse>\<cdot>d)\<cdot>b\<inverse>"
    using IsCommutative_def by simp
  with A2 T show "a\<cdot>(b\<cdot>c)\<inverse> = (a\<cdot>d\<inverse>\<cdot>c\<inverse>)\<cdot>(d\<cdot>b\<inverse>)"
    using group_op_closed group_oper_assoc by simp
  from A2 T have "a\<cdot>b\<cdot>(c\<cdot>d) = a\<cdot>b\<cdot>c\<cdot>d"
    using group_oper_assoc by simp
  also have "a\<cdot>b\<cdot>c\<cdot>d = c\<cdot>a\<cdot>b\<cdot>d"
  proof -
    from A1 A2 have "a\<cdot>b\<cdot>c\<cdot>d = c\<cdot>(a\<cdot>b)\<cdot>d"
      using IsCommutative_def group_op_closed
      by simp
    also from A2 have "\<dots> = c\<cdot>a\<cdot>b\<cdot>d"
      using group_op_closed group_oper_assoc
      by simp
    finally show ?thesis by simp
  qed
  also from A2 have "c\<cdot>a\<cdot>b\<cdot>d =  c\<cdot>a\<cdot>(b\<cdot>d)"
    using group_op_closed group_oper_assoc
    by simp
  finally show "a\<cdot>b\<cdot>(c\<cdot>d) = c\<cdot>a\<cdot>(b\<cdot>d)" by simp
  with A1 A2 show "a\<cdot>b\<cdot>(c\<cdot>d) = a\<cdot>c\<cdot>(b\<cdot>d)"
    using IsCommutative_def by simp
  from A1 A2 T show "a\<cdot>(b\<cdot>c\<inverse>)\<cdot>d = a\<cdot>b\<cdot>d\<cdot>c\<inverse>"
    using group0_4_L7 by simp
  from T have "(a\<cdot>b)\<cdot>(c\<cdot>d)\<inverse>\<cdot>(b\<cdot>d\<inverse>)\<inverse> = (a\<cdot>b)\<cdot>((c\<cdot>d)\<inverse>\<cdot>(b\<cdot>d\<inverse>)\<inverse>)"
    using group_oper_assoc by simp
  also from A1 A2 T have "\<dots> = (a\<cdot>b)\<cdot>(c\<inverse>\<cdot>d\<inverse>\<cdot>(d\<cdot>b\<inverse>))"
    using group_inv_of_two group0_2_L12 IsCommutative_def
    by simp
  also from T have "\<dots> = (a\<cdot>b)\<cdot>(c\<inverse>\<cdot>(d\<inverse>\<cdot>(d\<cdot>b\<inverse>)))"
    using group_oper_assoc by simp
  also from A1 A2 T have "\<dots> = a\<cdot>c\<inverse>"
    using group_oper_assoc group0_2_L6 group0_2_L2 IsCommutative_def
    inv_cancel_two by simp
  finally show "(a\<cdot>b)\<cdot>(c\<cdot>d)\<inverse>\<cdot>(b\<cdot>d\<inverse>)\<inverse> = a\<cdot>c\<inverse>"
    by simp
qed


text\<open>Some other rearrangements with four elements.\<close>

lemma (in group0) group0_4_L8A: 
  assumes A1: "P {is commutative on} G"
  and A2: "a\<in>G"  "b\<in>G"  "c\<in>G"  "d\<in>G"
  shows 
  "a\<cdot>b\<inverse>\<cdot>(c\<cdot>d\<inverse>) = a\<cdot>c\<cdot>(b\<inverse>\<cdot>d\<inverse>)"
  "a\<cdot>b\<inverse>\<cdot>(c\<cdot>d\<inverse>) = a\<cdot>c\<cdot>b\<inverse>\<cdot>d\<inverse>"
proof -
  from A2 have 
    T: "a\<in>G"  "b\<inverse> \<in> G"  "c\<in>G"  "d\<inverse> \<in> G"
    using inverse_in_group by auto
  with A1 show "a\<cdot>b\<inverse>\<cdot>(c\<cdot>d\<inverse>) = a\<cdot>c\<cdot>(b\<inverse>\<cdot>d\<inverse>)"
    by (rule group0_4_L8)
  with A2 T show  "a\<cdot>b\<inverse>\<cdot>(c\<cdot>d\<inverse>) = a\<cdot>c\<cdot>b\<inverse>\<cdot>d\<inverse>"
    using group_op_closed group_oper_assoc
    by simp
qed

text\<open>Some rearrangements with an equation.\<close>

lemma (in group0) group0_4_L9:
  assumes A1: "P {is commutative on} G"
  and A2: "a\<in>G"  "b\<in>G"  "c\<in>G"  "d\<in>G"
  and A3: "a = b\<cdot>c\<inverse>\<cdot>d\<inverse>"
  shows 
  "d = b\<cdot>a\<inverse>\<cdot>c\<inverse>"
  "d = a\<inverse>\<cdot>b\<cdot>c\<inverse>"
  "b = a\<cdot>d\<cdot>c"
proof -
  from A2 have T: 
    "a\<inverse> \<in> G"  "c\<inverse> \<in> G"  "d\<inverse> \<in> G"  "b\<cdot>c\<inverse> \<in> G"
    using group_op_closed inverse_in_group 
    by auto
  with A2 A3 have "a\<cdot>(d\<inverse>)\<inverse> =  b\<cdot>c\<inverse>"
    using group0_2_L18 by simp
  with A2 have "b\<cdot>c\<inverse> = a\<cdot>d"
    using group_inv_of_inv by simp
  with A2 T have I: "a\<inverse>\<cdot>(b\<cdot>c\<inverse>) = d"
    using group0_2_L18 by simp
  with A1 A2 T show 
    "d = b\<cdot>a\<inverse>\<cdot>c\<inverse>"
    "d = a\<inverse>\<cdot>b\<cdot>c\<inverse>"
    using group_oper_assoc IsCommutative_def by auto
  from A3 have "a\<cdot>d\<cdot>c = (b\<cdot>c\<inverse>\<cdot>d\<inverse>)\<cdot>d\<cdot>c" by simp
  also from A2 T have "\<dots> = b\<cdot>c\<inverse>\<cdot>(d\<inverse>\<cdot>d)\<cdot>c"
    using group_oper_assoc by simp
  also from A2 T have "\<dots> =  b\<cdot>c\<inverse>\<cdot>c"
    using group0_2_L6 group0_2_L2 by simp
  also from A2 T have "\<dots> =  b\<cdot>(c\<inverse>\<cdot>c)"
    using group_oper_assoc by simp
  also from A2 have "\<dots> = b"
    using group0_2_L6 group0_2_L2 by simp
  finally have "a\<cdot>d\<cdot>c = b" by simp
  thus "b = a\<cdot>d\<cdot>c" by simp
qed

end
