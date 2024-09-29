(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

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

section \<open>Groups - an alternative definition\<close>

theory Group_ZF_1b imports Group_ZF

begin

text\<open>In a typical textbook a group is defined as a set $G$ with an 
  associative operation such that two conditions hold:

  A: there is an element $e\in G$ such that for all 
  $g\in G$ we have $e\cdot g = g$ and $g\cdot e =g$. We call this element a 
  "unit" or a "neutral element" of the group.
  
  B: for every $a\in G$ there exists a $b\in G$ such that $a\cdot b = e$, 
  where $e$ is the element of $G$ whose existence is guaranteed by A.

  The validity of this definition is rather dubious to me, as condition 
  A does not define any specific element $e$ that can be referred to in 
  condition B - it merely states that a set of such units
  $e$ is not empty. Of course it does work in the end as we can prove that
  the set of such neutral elements has exactly one element, but still the definition
  by itself is not valid. You just can't reference a variable bound by a quantifier
  outside of the scope of that quantifier.
  
  One way around this is to first use condition A to define
  the notion of a monoid, then prove the uniqueness of $e$ and then use the 
  condition B to define groups. 

  Another way is to write conditions A and B together as follows:
  
  $\exists_{e \in G} \ (\forall_{g \in G} \ e\cdot g = g \wedge g\cdot e = g) 
  \wedge (\forall_{a\in G}\exists_{b\in G}\  a\cdot b = e).$

  This is rather ugly.

  What I want to talk about is an amusing way to define groups directly 
  without any reference to the neutral elements. Namely, we can define 
  a group as a non-empty set $G$ with an associative operation "$\cdot $" 
  such that 
  
  C: for every $a,b\in G$ the equations $a\cdot x = b$ and 
  $y\cdot a = b$ can be solved in $G$.
  
  This theory file aims at proving the equivalence of this 
  alternative definition with the usual definition of the group, as 
  formulated in \<open>Group_ZF.thy\<close>. The informal proofs come from an Aug. 14, 2005
  post by buli on the matematyka.org forum.\<close>

subsection\<open>An alternative definition of group\<close>

text\<open>First we will define notation for writing about groups.\<close>

text\<open>We will use the multiplicative notation for the group operation. To do this, we
  define a context (locale) that tells Isabelle
  to interpret $a\cdot b$ as the value of function $P$ on the pair 
  $\langle a,b \rangle$.\<close>

locale group2 =
  fixes P 
  fixes dot (infixl "\<cdot>" 70)
  defines dot_def [simp]: "a \<cdot> b \<equiv> P`\<langle>a,b\<rangle>"

text\<open>The next theorem states that a set $G$ with an associative operation 
  that satisfies condition C is a group, as defined in IsarMathLib
  \<open>Group_ZF\<close> theory.\<close>

theorem (in group2) altgroup_is_group: 
  assumes A1: "G\<noteq>0" and A2: "P {is associative on} G"
  and A3: "\<forall>a\<in>G.\<forall>b\<in>G. \<exists>x\<in>G. a\<cdot>x = b"
  and A4: "\<forall>a\<in>G.\<forall>b\<in>G. \<exists>y\<in>G. y\<cdot>a = b"
  shows "IsAgroup(G,P)"
proof -
  from A1 obtain a where "a\<in>G" by auto
  with A3 obtain x where "x\<in>G" and "a\<cdot>x = a" 
    by auto
  from A4 \<open>a\<in>G\<close> obtain y where "y\<in>G" and "y\<cdot>a = a"
    by auto
  have I: "\<forall>b\<in>G. b = b\<cdot>x \<and> b = y\<cdot>b"
  proof
    fix b assume "b\<in>G"
     with A4 \<open>a\<in>G\<close> obtain y\<^sub>b where "y\<^sub>b\<in>G"  
      and "y\<^sub>b\<cdot>a = b" by auto
    from A3 \<open>a\<in>G\<close> \<open>b\<in>G\<close> obtain x\<^sub>b where "x\<^sub>b\<in>G"  
      and "a\<cdot>x\<^sub>b = b" by auto
    from \<open>a\<cdot>x = a\<close> \<open>y\<cdot>a = a\<close> \<open>y\<^sub>b\<cdot>a = b\<close> \<open>a\<cdot>x\<^sub>b = b\<close> 
    have "b = y\<^sub>b\<cdot>(a\<cdot>x)" and "b = (y\<cdot>a)\<cdot>x\<^sub>b" 
      by auto
    moreover from A2 \<open>a\<in>G\<close> \<open>x\<in>G\<close> \<open>y\<in>G\<close> \<open>x\<^sub>b\<in>G\<close> \<open>y\<^sub>b\<in>G\<close> have 
      "(y\<cdot>a)\<cdot>x\<^sub>b = y\<cdot>(a\<cdot>x\<^sub>b)"  "y\<^sub>b\<cdot>(a\<cdot>x) = (y\<^sub>b\<cdot>a)\<cdot>x"
      using IsAssociative_def by auto
    moreover from \<open>y\<^sub>b\<cdot>a = b\<close> \<open>a\<cdot>x\<^sub>b = b\<close> have 
      "(y\<^sub>b\<cdot>a)\<cdot>x = b\<cdot>x"  "y\<cdot>(a\<cdot>x\<^sub>b) = y\<cdot>b"
      by auto
    ultimately show "b = b\<cdot>x \<and> b = y\<cdot>b" by simp
  qed
  moreover have "x = y"
  proof -
    from \<open>x\<in>G\<close> I have "x = y\<cdot>x" by simp  
    also from \<open>y\<in>G\<close> I have "y\<cdot>x = y" by simp
    finally show "x = y" by simp
  qed
  ultimately have "\<forall>b\<in>G. b\<cdot>x = b \<and> x\<cdot>b = b" by simp
  with A2 \<open>x\<in>G\<close> have "IsAmonoid(G,P)" using IsAmonoid_def by auto
  with A3 show "IsAgroup(G,P)"
    using monoid0_def monoid0.unit_is_neutral IsAgroup_def
    by simp
qed

text\<open>The converse of \<open>altgroup_is_group\<close>: 
  in every (classically defined) group condition C holds.  
  In informal mathematics we can say "Obviously
  condition C holds in any group." In formalized mathematics the word "obviously" 
  is not in the language. The next theorem is proven in the context called
  \<open>group0\<close> defined in the theory \<open>Group_ZF.thy\<close>. Similarly to the
  \<open>group2\<close> that context defines $a\cdot b$ as $P\langle a,b\rangle$ 
  It also defines notation related to the group inverse and 
  adds an assumption that the pair $(G,P)$ is a group 
  to all its theorems. This is why in the next theorem we don't 
  explicitely assume that $(G,P)$ is a group - this assumption 
  is implicit in the context.\<close>

theorem (in group0) group_is_altgroup: shows 
  "\<forall>a\<in>G.\<forall>b\<in>G. \<exists>x\<in>G. a\<cdot>x = b" and "\<forall>a\<in>G.\<forall>b\<in>G. \<exists>y\<in>G. y\<cdot>a = b"
proof -
  { fix a b assume "a\<in>G"  "b\<in>G"
    let ?x = "a\<inverse>\<cdot> b"
    let ?y = "b\<cdot>a\<inverse>"
    from \<open>a\<in>G\<close>  \<open>b\<in>G\<close>  have 
      "?x \<in> G"  "?y \<in> G"  and  "a\<cdot>?x = b"  "?y\<cdot>a = b"
      using inverse_in_group group_op_closed inv_cancel_two
      by auto
    hence "\<exists>x\<in>G. a\<cdot>x = b" and "\<exists>y\<in>G. y\<cdot>a = b" by auto
  } thus 
      "\<forall>a\<in>G.\<forall>b\<in>G. \<exists>x\<in>G. a\<cdot>x = b" and
      "\<forall>a\<in>G.\<forall>b\<in>G. \<exists>y\<in>G. y\<cdot>a = b"
    by auto
qed

text\<open>An associative quasigroup is a group. This is a bit weaker than \<open>altgroup_is_group\<close> 
  as the definition of quasigroup requires uniqueness of solutions of $a\cdot x = b$ and 
  $y\cdot a = b$ equations. \<close>

lemma assoc_quasigroup_group: 
  assumes "IsAquasigroup(G,P)" and "P {is associative on} G" "G\<noteq>\<emptyset>" 
  shows "IsAgroup(G,P)"
proof -
  from assms(1) have 
    "\<forall>a\<in>G.\<forall>b\<in>G. \<exists>y\<in>G. P`\<langle>a,y\<rangle> = b" and "\<forall>a\<in>G.\<forall>b\<in>G. \<exists>x\<in>G. P`\<langle>x,a\<rangle> = b"
    unfolding IsAquasigroup_def HasLatinSquareProp_def HasLeftDiv_def HasRightDiv_def
    using ZF1_1_L9(4) by simp_all
  with assms(2,3) show ?thesis using group2.altgroup_is_group by auto
qed
 
end
  
