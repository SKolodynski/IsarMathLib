(* 
This file is a part of IsarMathLib - 
a library of formalized mathematics for Isabelle/Isar.

Copyright (C) 2005 - 2008  Slawomir Kolodynski

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

section \<open>Monoids\<close>

theory Monoid_ZF imports func_ZF

begin

text\<open>This theory provides basic facts about monoids.\<close>

subsection\<open>Definition and basic properties\<close>

text\<open>In this section we talk about monoids. 
  The notion of a monoid is similar to the notion of a semigroup 
  except that we require the existence of a neutral element.
  It is also similar to the notion of group except that
  we don't require existence of the inverse.\<close>

text\<open>Monoid is a set $G$ with an associative operation and a neutral element.
  The operation is a function on $G\times G$ with values in $G$. 
  In the context of ZF set theory this means that it is a set of pairs
  $\langle x,y \rangle$, where $x\in G\times G$ and $y\in G$. In other words 
  the operation is a certain subset of $(G\times G)\times G$. We express
  all this by defing a predicate \<open>IsAmonoid(G,f)\<close>. Here $G$ is the 
 ''carrier'' of the group and $f$ is the binary operation on it.
\<close>

definition
  "IsAmonoid(G,f) \<equiv>
  f {is associative on} G \<and> 
  (\<exists>e\<in>G. (\<forall> g\<in>G. ( (f`(\<langle>e,g\<rangle>) = g) \<and> (f`(\<langle>g,e\<rangle>) = g))))"

text\<open>The next locale called ''monoid0'' defines a context for theorems
  that concern monoids. In this contex we assume that the pair $(G,f)$
  is a monoid.  We will use
  the \<open>\<oplus>\<close> symbol to denote the monoid operation (for 
  no particular reason).\<close>

locale monoid0 =
  fixes G 
  fixes f
  assumes monoidAsssum: "IsAmonoid(G,f)"
  
  fixes monoper (infixl "\<oplus>" 70)
  defines monoper_def [simp]: "a \<oplus> b \<equiv> f`\<langle>a,b\<rangle>"

text\<open>The result of the monoid operation is in the monoid (carrier).\<close>

lemma (in monoid0) group0_1_L1: 
  assumes "a\<in>G"  "b\<in>G" shows "a\<oplus>b \<in> G" 
  using assms monoidAsssum IsAmonoid_def IsAssociative_def apply_funtype
  by auto

text\<open>There is only one neutral element in a monoid.\<close>

lemma (in monoid0) group0_1_L2: shows
  "\<exists>!e. e\<in>G \<and> (\<forall> g\<in>G. ( (e\<oplus>g = g) \<and> g\<oplus>e = g))"
proof
  fix e y
  assume "e \<in> G \<and> (\<forall>g\<in>G. e \<oplus> g = g \<and> g \<oplus> e = g)"
    and "y \<in> G \<and> (\<forall>g\<in>G. y \<oplus> g = g \<and> g \<oplus> y = g)"
  then have "y\<oplus>e = y" "y\<oplus>e = e" by auto
  thus "e = y" by simp
next from monoidAsssum show 
    "\<exists>e. e\<in> G \<and> (\<forall> g\<in>G. e\<oplus>g = g \<and> g\<oplus>e = g)"
    using IsAmonoid_def by auto
qed

text\<open>We could put the definition of neutral element anywhere, 
  but it is only usable in conjuction  with the above lemma.\<close>

definition 
 "TheNeutralElement(G,f) \<equiv> 
  ( THE e. e\<in>G \<and> (\<forall> g\<in>G. f`\<langle>e,g\<rangle> = g \<and> f`\<langle>g,e\<rangle> = g))"

text\<open>The neutral element is neutral.\<close>

lemma (in monoid0) unit_is_neutral:
  assumes A1: "e = TheNeutralElement(G,f)"
  shows "e \<in> G \<and> (\<forall>g\<in>G. e \<oplus> g = g \<and> g \<oplus> e = g)"
proof -
  let ?n = "THE b. b\<in> G \<and> (\<forall> g\<in>G. b\<oplus>g = g \<and> g\<oplus>b = g)"
  have "\<exists>!b. b\<in> G \<and> (\<forall> g\<in>G. b\<oplus>g = g \<and> g\<oplus>b = g)"
    using group0_1_L2 by simp
  then have "?n\<in> G \<and> (\<forall> g\<in>G. ?n\<oplus>g = g \<and> g\<oplus>?n = g)"
    by (rule theI)
  with A1 show ?thesis 
    using TheNeutralElement_def by simp
qed

text\<open>The monoid carrier is not empty.\<close>

lemma (in monoid0) group0_1_L3A: shows "G\<noteq>0"
proof -
  have "TheNeutralElement(G,f) \<in> G" using unit_is_neutral
    by simp
  thus ?thesis by auto
qed

text\<open>The range of the monoid operation is the whole monoid carrier.\<close>

lemma (in monoid0) group0_1_L3B: shows "range(f) = G"
proof
  from monoidAsssum have "f : G\<times>G\<rightarrow>G"
     using IsAmonoid_def IsAssociative_def by simp
  then show "range(f) \<subseteq> G" 
    using func1_1_L5B by simp
  show "G \<subseteq> range(f)"
  proof
    fix g assume A1: "g\<in>G"
    let ?e = "TheNeutralElement(G,f)"
    from A1 have "\<langle>?e,g\<rangle> \<in> G\<times>G" "g = f`\<langle>?e,g\<rangle>"
      using unit_is_neutral by auto
    with \<open>f : G\<times>G\<rightarrow>G\<close> show "g \<in> range(f)"
      using func1_1_L5A by blast
  qed
qed

text\<open>Another way to state that the range of the monoid operation
  is the whole monoid carrier.\<close>

lemma (in monoid0) range_carr: shows "f``(G\<times>G) = G"
  using monoidAsssum IsAmonoid_def IsAssociative_def
    group0_1_L3B range_image_domain by auto
      
text\<open>In a monoid any neutral element is the neutral element.\<close>

lemma (in monoid0) group0_1_L4: 
  assumes A1: "e \<in> G \<and> (\<forall>g\<in>G. e \<oplus> g = g \<and> g \<oplus> e = g)"
  shows "e = TheNeutralElement(G,f)"
proof -
  let ?n = "THE b. b\<in> G \<and> (\<forall> g\<in>G. b\<oplus>g = g \<and> g\<oplus>b = g)"
  have "\<exists>!b. b\<in> G \<and> (\<forall> g\<in>G. b\<oplus>g = g \<and> g\<oplus>b = g)"
    using group0_1_L2 by simp
  moreover note A1
  ultimately have "?n = e" by (rule the_equality2)
  then show ?thesis using TheNeutralElement_def by simp
qed

text\<open>The next lemma shows that if the if we restrict the monoid operation to
  a subset of $G$ that contains the neutral element, then the 
  neutral element of the monoid operation is also neutral with the 
  restricted operation.
\<close>

lemma (in monoid0) group0_1_L5:
  assumes A1: "\<forall>x\<in>H.\<forall>y\<in>H. x\<oplus>y \<in> H"
  and A2: "H\<subseteq>G"
  and A3: "e = TheNeutralElement(G,f)"
  and A4: "g = restrict(f,H\<times>H)"
  and A5: "e\<in>H"
  and A6: "h\<in>H"
  shows "g`\<langle>e,h\<rangle> = h \<and> g`\<langle>h,e\<rangle> = h"
proof -
  from A4 A6 A5 have 
    "g`\<langle>e,h\<rangle> = e\<oplus>h \<and> g`\<langle>h,e\<rangle> = h\<oplus>e"
    using restrict_if by simp
  with A3 A4 A6 A2 show 
    "g`\<langle>e,h\<rangle> = h \<and> g`\<langle>h,e\<rangle> = h"
    using  unit_is_neutral by auto
qed

text\<open>The next theorem shows that if the monoid operation is closed
  on a subset of $G$ then this set is a (sub)monoid (although 
  we do not define this notion). This fact will be 
  useful when we study subgroups.\<close>

theorem (in monoid0) group0_1_T1: 
  assumes A1: "H {is closed under} f"
  and A2: "H\<subseteq>G"
  and A3: "TheNeutralElement(G,f) \<in> H"
  shows  "IsAmonoid(H,restrict(f,H\<times>H))"
proof -
  let ?g = "restrict(f,H\<times>H)"
  let ?e = "TheNeutralElement(G,f)"
  from monoidAsssum have "f \<in> G\<times>G\<rightarrow>G" 
    using IsAmonoid_def IsAssociative_def by simp
  moreover from A2 have "H\<times>H \<subseteq> G\<times>G" by auto
  moreover from A1 have "\<forall>p \<in> H\<times>H. f`(p) \<in> H"
    using IsOpClosed_def by auto
  ultimately have "?g \<in> H\<times>H\<rightarrow>H"
    using func1_2_L4 by simp
  moreover have "\<forall>x\<in>H.\<forall>y\<in>H.\<forall>z\<in>H. 
    ?g`\<langle>?g`\<langle>x,y\<rangle> ,z\<rangle> = ?g`\<langle>x,?g`\<langle>y,z\<rangle>\<rangle>"
  proof -
    from A1 have "\<forall>x\<in>H.\<forall>y\<in>H.\<forall>z\<in>H.
      ?g`\<langle>?g`\<langle>x,y\<rangle>,z\<rangle> = x\<oplus>y\<oplus>z"
      using IsOpClosed_def restrict_if by simp
    moreover have "\<forall>x\<in>H.\<forall>y\<in>H.\<forall>z\<in>H. x\<oplus>y\<oplus>z = x\<oplus>(y\<oplus>z)"
    proof -
      from monoidAsssum have 
	"\<forall>x\<in>G.\<forall>y\<in>G.\<forall>z\<in>G. x\<oplus>y\<oplus>z = x\<oplus>(y\<oplus>z)"
	using IsAmonoid_def IsAssociative_def 
	by simp
      with A2 show ?thesis by auto
    qed
    moreover from A1 have 
      "\<forall>x\<in>H.\<forall>y\<in>H.\<forall>z\<in>H. x\<oplus>(y\<oplus>z) = ?g`\<langle> x,?g`\<langle>y,z\<rangle> \<rangle>"
      using IsOpClosed_def restrict_if by simp
    ultimately show ?thesis by simp 
  qed
  moreover have 
    "\<exists>n\<in>H. (\<forall>h\<in>H. ?g`\<langle>n,h\<rangle> = h \<and> ?g`\<langle>h,n\<rangle> = h)"
  proof -
    from A1 have "\<forall>x\<in>H.\<forall>y\<in>H. x\<oplus>y \<in> H"
      using IsOpClosed_def by simp
    with A2 A3 have 
      "\<forall> h\<in>H. ?g`\<langle>?e,h\<rangle> = h \<and> ?g`\<langle>h,?e\<rangle> = h"
      using group0_1_L5 by blast
    with A3 show ?thesis by auto
  qed
  ultimately show ?thesis using IsAmonoid_def IsAssociative_def 
    by simp
qed
    
text\<open>Under the assumptions of \<open> group0_1_T1\<close>
  the neutral element of a 
  submonoid is the same as that of the monoid.\<close>

lemma group0_1_L6: 
  assumes A1: "IsAmonoid(G,f)"
  and A2: "H {is closed under} f"
  and A3: "H\<subseteq>G"
  and A4: "TheNeutralElement(G,f) \<in> H"
  shows "TheNeutralElement(H,restrict(f,H\<times>H)) = TheNeutralElement(G,f)"
proof -
  let ?e = "TheNeutralElement(G,f)"
  let ?g = "restrict(f,H\<times>H)"
  from assms have "monoid0(H,?g)"
    using monoid0_def monoid0.group0_1_T1 
    by simp
  moreover have 
    "?e \<in> H \<and> (\<forall>h\<in>H. ?g`\<langle>?e,h\<rangle> = h \<and> ?g`\<langle>h,?e\<rangle> = h)"
  proof -
    { fix h assume "h \<in> H"
      with assms have
	"monoid0(G,f)"  "\<forall>x\<in>H.\<forall>y\<in>H. f`\<langle>x,y\<rangle> \<in> H" 
	"H\<subseteq>G"  "?e = TheNeutralElement(G,f)"  "?g = restrict(f,H\<times>H)"
	"?e \<in> H"  "h \<in> H" 
	using monoid0_def IsOpClosed_def by auto
      then have "?g`\<langle>?e,h\<rangle> = h \<and> ?g`\<langle>h,?e\<rangle> = h"
	by (rule monoid0.group0_1_L5)
    } hence "\<forall>h\<in>H. ?g`\<langle>?e,h\<rangle> = h \<and> ?g`\<langle>h,?e\<rangle> = h" by simp
    with A4 show ?thesis by simp
  qed
  ultimately have "?e =  TheNeutralElement(H,?g)"
    by (rule monoid0.group0_1_L4)
  thus ?thesis by simp
qed

text\<open>If a sum of two elements is not zero, 
  then at least one has to be nonzero.\<close>

lemma (in monoid0) sum_nonzero_elmnt_nonzero: 
  assumes "a \<oplus> b \<noteq> TheNeutralElement(G,f)"
  shows "a \<noteq> TheNeutralElement(G,f) \<or> b \<noteq> TheNeutralElement(G,f)"
  using assms unit_is_neutral by auto

end
