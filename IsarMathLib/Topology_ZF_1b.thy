(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

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
INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT,
INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open>Topology 1b\<close>

theory Topology_ZF_1b imports Topology_ZF_1

begin

text\<open>One of the facts demonstrated in every class on General Topology is that
  in a $T_2$ (Hausdorff) topological space compact sets are closed. 
  Formalizing the proof of this fact gave me an interesting insight 
  into the role of the Axiom of Choice (AC) in many informal proofs.

  A typical informal proof of this fact goes like this: we want to show 
  that the complement of $K$ is open. To do this, 
  choose an arbitrary point $y\in K^c$.
  Since $X$ is $T_2$, for every point $x\in K$ we can find an 
  open set $U_x$ such that $y\notin \overline{U_x}$. 
  Obviously $\{U_x\}_{x\in K}$ covers $K$, so select a finite subcollection
  that covers $K$, and so on. I had never realized that 
  such reasoning requires the Axiom of Choice. 
  Namely, suppose we have a lemma that states "In $T_2$ spaces, 
  if $x\neq y$, then there is an open set 
  $U$ such that $x\in U$ and $y\notin \overline{U}$" (like our 
  lemma \<open>T2_cl_open_sep\<close> below). This only states that
  the set of such open sets $U$ is not empty. To get the collection 
  $\{U_x \}_{x\in K}$ in this proof we have to select one such set 
  among many for every $x\in K$ and this is where we use the Axiom of Choice. 
  Probably in 99/100 cases when an informal calculus proof states something like
  $\forall \varepsilon \exists \delta_\varepsilon \cdots$ the proof uses AC.
  Most of the time the use of AC in such proofs can be avoided. This is also 
  the case for the fact that in a $T_2$ space compact sets are closed.
\<close>

subsection\<open>Compact sets are closed - no need for AC\<close>

text\<open>In this section we show that in a $T_2$ topological 
  space compact sets are closed.\<close>

text\<open>First we prove a lemma that in a $T_2$ space two points 
  can be separated by the closure of an open set.\<close>

lemma (in topology0) T2_cl_open_sep:
  assumes "T {is T\<^sub>2}"  and "x \<in> \<Union>T"  "y \<in> \<Union>T"   "x\<noteq>y"
  shows "\<exists>U\<in>T. (x\<in>U \<and> y \<notin> cl(U))"
proof -
  from assms have "\<exists>U\<in>T. \<exists>V\<in>T. x\<in>U \<and> y\<in>V \<and> U\<inter>V=0"
    using isT2_def by simp
  then obtain U V where "U\<in>T"  "V\<in>T"  "x\<in>U"  "y\<in>V"  "U\<inter>V=0"
    by auto
  then have "U\<in>T \<and> x\<in>U \<and> y\<in> V \<and> cl(U) \<inter> V = 0"
    using  disj_open_cl_disj by auto
  thus "\<exists>U\<in>T. (x\<in>U \<and> y \<notin> cl(U))" by auto
qed

text\<open>AC-free proof that in a Hausdorff space compact sets 
  are closed. To understand the notation recall that in Isabelle/ZF
  \<open>Pow(A)\<close> is the powerset (the set of subsets) of $A$ 
  and \<open>FinPow(A)\<close> denotes the set of finite subsets of $A$ 
  in IsarMathLib.\<close>

theorem (in topology0) in_t2_compact_is_cl:
  assumes A1: "T {is T\<^sub>2}" and A2: "K {is compact in} T"
  shows "K {is closed in} T"
proof -
  let ?X = "\<Union>T"
  have "\<forall>y \<in> ?X - K. \<exists>U\<in>T. y\<in>U \<and> U \<subseteq> ?X - K"
  proof -
    { fix y assume "y \<in> ?X"  "y\<notin>K"
      have "\<exists>U\<in>T. y\<in>U \<and> U \<subseteq> ?X - K"
      proof -
	let ?B = "\<Union>x\<in>K. {V\<in>T. x\<in>V \<and> y \<notin> cl(V)}"
	have I: "?B \<in> Pow(T)"  "FinPow(?B) \<subseteq> Pow(?B)" 
	  using FinPow_def by auto
	from \<open>K {is compact in} T\<close> \<open>y \<in> ?X\<close>  \<open>y\<notin>K\<close> have 
	  "\<forall>x\<in>K. x \<in> ?X \<and> y \<in> ?X \<and> x\<noteq>y"
	  using IsCompact_def by auto
	with \<open>T {is T\<^sub>2}\<close> have "\<forall>x\<in>K. {V\<in>T. x\<in>V \<and> y \<notin> cl(V)} \<noteq> 0"
	  using T2_cl_open_sep by auto
	hence "K \<subseteq> \<Union>?B" by blast
	with \<open>K {is compact in} T\<close> I have 
	  "\<exists>N \<in> FinPow(?B). K \<subseteq> \<Union>N" 
	  using IsCompact_def by auto
	then obtain N where "N \<in> FinPow(?B)"  "K \<subseteq> \<Union>N" 
	  by auto
	with I have "N \<subseteq> ?B" by auto
	hence "\<forall>V\<in>N. V\<in>?B" by auto
	let ?M = "{cl(V). V\<in>N}"
	let ?C = "{D \<in> Pow(?X). D {is closed in} T}"
	from \<open>N \<in> FinPow(?B)\<close> have "\<forall>V\<in>?B. cl(V) \<in> ?C"  "N \<in> FinPow(?B)"
	  using cl_is_closed IsClosed_def by auto
	then have "?M \<in> FinPow(?C)" by (rule fin_image_fin)
	then have "?X - \<Union>?M \<in> T" using fin_union_cl_is_cl IsClosed_def 
	  by simp
	moreover from \<open>y \<in> ?X\<close>  \<open>y\<notin>K\<close>  \<open>\<forall>V\<in>N. V\<in>?B\<close> have 
	  "y \<in> ?X - \<Union>?M" by simp
	moreover have "?X - \<Union>?M \<subseteq> ?X - K"
	proof -
	  from \<open>\<forall>V\<in>N. V\<in>?B\<close> have "\<Union>N \<subseteq> \<Union>?M" using cl_contains_set by auto
	  with \<open>K \<subseteq> \<Union>N\<close> show "?X - \<Union>?M \<subseteq> ?X - K" by auto
	qed
	ultimately have "\<exists>U. U\<in>T \<and> y \<in> U \<and> U \<subseteq> ?X - K"
	  by auto
	thus "\<exists>U\<in>T. y\<in>U \<and> U \<subseteq> ?X - K" by auto
      qed
    } thus "\<forall>y \<in> ?X - K. \<exists>U\<in>T. y\<in>U \<and> U \<subseteq> ?X - K"
      by auto
  qed
  with A2 show "K {is closed in} T" 
    using open_neigh_open IsCompact_def IsClosed_def by auto
qed


end
