(*    This file is a part of IsarMathLib - 
    a library of formalized mathematics for Isabelle/Isar.

    Copyright (C) 2020  Slawomir Kolodynski

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

section \<open>Semilattices and Lattices \<close>

theory Lattice_ZF imports Order_ZF_1a func1

begin


text\<open> Lattices can be introduced in algebraic way as commutative idempotent ($x\cdot x =x$) 
  semigroups or as partial orders with some additional properties. These two approaches are
  equivalent. In this theory we will use the order-theoretic approach. \<close>

subsection\<open>Semilattices\<close>

text\<open> We start with a relation $r$ which is a partial order on a set $L$. Such situation is defined
 in \<open>Order_ZF\<close> as the predicate \<open>IsPartOrder(L,r)\<close>. \<close>

text\<open> A partially ordered $(L,r)$ set is a join-semilattice if each two-element subset of $L$
  has a supremum (i.e. the least upper bound). The definition is written in terms of 
  images of singletons $\{ x\}$ under relation. To understand this formulation note
  that the set of upper bounds of a set $A\subseteq X$ is 
  $\bigcap_{x\in A}\{ y\in X | \langle x,y\rangle \in r \}$, which is the same
  as $\bigcap_{x\in A} r(\{ x \})$, where $r(\{ x \})$ is the image of the singleton $\{ x\}$ under
  relation $r$. \<close>

definition
  "IsJoinSemilattice(L,r) \<equiv> 
    r\<subseteq>L\<times>L \<and> IsPartOrder(L,r) \<and> (\<forall>x\<in>L. \<forall>y\<in>L. HasAsupremum(r,{x,y}))"

text\<open> A partially ordered $(L,r)$ set is a meet-semilattice if each two-element subset of $L$
  has an infimum (i.e. the greatest lower bound). \<close>

definition
  "IsMeetSemilattice(L,r) \<equiv> 
    r\<subseteq>L\<times>L \<and> IsPartOrder(L,r) \<and> (\<forall>x\<in>L. \<forall>y\<in>L. HasAnInfimum(r,{x,y}))"

text\<open> A partially ordered $(L,r)$ set is a lattice if it is both join and meet-semilattice, i.e. if 
  every two element set has a supremum (least upper bound) and infimum (greatest lower bound). \<close>

definition
  IsAlattice (infixl "{is a lattice on}" 90) where
  "r {is a lattice on} L \<equiv> IsJoinSemilattice(L,r) \<and> IsMeetSemilattice(L,r)"

text\<open> Join is a binary operation whose value on a pair $\langle x,y\rangle$ is def\{ x,y\}$ 
  is defined as the supremum of the set $\{ x,y\}$. \<close>

definition
  "Join(L,r) \<equiv> {\<langle>p,Supremum(r,{fst(p),snd(p)})\<rangle> . p \<in> L\<times>L}"

text\<open> Meet is a binary operation whose value on a pair $\langle x,y\rangle$ is def\{ x,y\}$ 
  is defined as the infimum of the set $\{ x,y\}$.\<close>


definition
  "Meet(L,r) \<equiv> {\<langle>p,Infimum(r,{fst(p),snd(p)})\<rangle> . p \<in> L\<times>L}"

text\<open> In a join-semilattice join is indeed a binary operation. \<close>

lemma join_is_binop: assumes "IsJoinSemilattice(L,r)" 
  shows "Join(L,r) :  L\<times>L \<rightarrow> L"
proof -
  from assms have "\<forall>p \<in> L\<times>L. Supremum(r,{fst(p),snd(p)}) \<in> L"
    unfolding IsJoinSemilattice_def IsPartOrder_def HasAsupremum_def using sup_in_space 
    by auto
  then show ?thesis unfolding Join_def using ZF_fun_from_total by simp
qed

text\<open> The value of \<open>Join(L,r)\<close> on a pair $\langle x,y\rangle$ is the supremum
  of the set $\{ x,y\}$. \<close>

lemma join_val: assumes "IsJoinSemilattice(L,r)" "x\<in>L" "y\<in>L"
  shows "Join(L,r)`\<langle>x,y\<rangle> = Supremum(r,{x,y})"
proof -
  from assms(1) have "Join(L,r) :  L\<times>L \<rightarrow> L" using join_is_binop by simp
  with assms(2,3) show ?thesis unfolding Join_def using ZF_fun_from_tot_val by auto
qed

text\<open> In a meet-semilattice meet is indeed a binary operation. \<close>

lemma meet_is_binop: assumes "IsMeetSemilattice(L,r)" 
  shows "Meet(L,r) :  L\<times>L \<rightarrow> L"
proof -
  from assms have "\<forall>p \<in> L\<times>L. Infimum(r,{fst(p),snd(p)}) \<in> L"
    unfolding IsMeetSemilattice_def IsPartOrder_def HasAnInfimum_def using inf_in_space 
    by auto
  then show ?thesis unfolding Meet_def using ZF_fun_from_total by simp
qed

text\<open> The value of \<open>Meet(L,r)\<close> on a pair $\langle x,y\rangle$ is the infimum
  of the set $\{ x,y\}$. \<close>

lemma meet_val: assumes "IsMeetSemilattice(L,r)" "x\<in>L" "y\<in>L"
  shows "Meet(L,r)`\<langle>x,y\<rangle> = Infimum(r,{x,y})"
proof -
  from assms(1) have "Meet(L,r) :  L\<times>L \<rightarrow> L" using meet_is_binop by simp
  with assms(2,3) show ?thesis unfolding Meet_def using ZF_fun_from_tot_val by auto
qed

text\<open> The next locale defines a a notation for join-semilattice. We will use the $\sqcup$ symbol
  rather than more common $\vee$ to avoid confusion with logical "or". \<close>

locale join_semilatt =
  fixes L
  fixes r
  assumes joinLatt: "IsJoinSemilattice(L,r)"
  fixes join (infixl "\<squnion>" 71)
  defines join_def [simp]: "x \<squnion> y \<equiv> Join(L,r)`\<langle>x,y\<rangle>"
  fixes sup ("sup _" ) 
  defines sup_def [simp]: "sup A  \<equiv> Supremum(r,A)"

text\<open> Join of the elements of the lattice is in the lattice. \<close>

lemma (in join_semilatt) join_props: assumes "x\<in>L" "y\<in>L" 
  shows "x\<squnion>y \<in> L" and "x\<squnion>y = sup {x,y}"
proof -
  from joinLatt assms have "Join(L,r)`\<langle>x,y\<rangle> \<in> L" using join_is_binop apply_funtype 
    by blast
  thus "x\<squnion>y \<in> L" by simp
  from joinLatt assms have "Join(L,r)`\<langle>x,y\<rangle> = Supremum(r,{x,y})" using join_val by simp
  thus "x\<squnion>y = sup {x,y}" by simp
qed

text\<open> Join is associative. \<close>

lemma (in join_semilatt) join_assoc: assumes "x\<in>L" "y\<in>L" "z\<in>L"
  shows "x\<squnion>(y\<squnion>z) = x\<squnion>y\<squnion>z"
proof -
  from joinLatt assms(2,3) have "x\<squnion>(y\<squnion>z) = x\<squnion>(sup {y,z})" using join_val by simp
  also from assms joinLatt have "... = sup {sup {x}, sup {y,z}}"
    unfolding IsJoinSemilattice_def IsPartOrder_def using join_props sup_inf_singl(2) 
    by auto
  also have "... = sup {x,y,z}"
  proof -
    let ?\<T> = "{{x},{y,z}}"
    from joinLatt have "r \<subseteq> L\<times>L" "antisym(r)" "trans(r)" 
      unfolding IsJoinSemilattice_def IsPartOrder_def by auto
    moreover from joinLatt assms have "\<forall>T\<in>?\<T>. HasAsupremum(r,T)"
      unfolding IsJoinSemilattice_def IsPartOrder_def using sup_inf_singl(1) by blast
    moreover from joinLatt assms have "HasAsupremum(r,{Supremum(r,T).T\<in>?\<T>})"
      unfolding IsJoinSemilattice_def IsPartOrder_def  HasAsupremum_def 
      using sup_in_space(1) sup_inf_singl(2) by auto
    ultimately have "Supremum(r,{Supremum(r,T).T\<in>?\<T>}) = Supremum(r,\<Union>?\<T>)" by (rule sup_sup)
    moreover have "{Supremum(r,T).T\<in>?\<T>} = {sup {x}, sup {y,z}}" and "\<Union>?\<T> = {x,y,z}"
      by auto
    ultimately show "(sup {sup {x}, sup {y,z}}) =  sup {x,y,z}" by simp
  qed
  also have "... = sup {sup {x,y}, sup {z}}"
  proof -
    let ?\<T> = "{{x,y},{z}}"
    from joinLatt have "r \<subseteq> L\<times>L" "antisym(r)" "trans(r)" 
      unfolding IsJoinSemilattice_def IsPartOrder_def by auto
    moreover from joinLatt assms have "\<forall>T\<in>?\<T>. HasAsupremum(r,T)"
      unfolding IsJoinSemilattice_def IsPartOrder_def using sup_inf_singl(1) by blast
    moreover from joinLatt assms have "HasAsupremum(r,{Supremum(r,T).T\<in>?\<T>})"
      unfolding IsJoinSemilattice_def IsPartOrder_def  HasAsupremum_def 
      using sup_in_space(1) sup_inf_singl(2) by auto
    ultimately have "Supremum(r,{Supremum(r,T).T\<in>?\<T>}) = Supremum(r,\<Union>?\<T>)" by (rule sup_sup)
    moreover have "{Supremum(r,T).T\<in>?\<T>} = {sup {x,y}, sup {z}}" and "\<Union>?\<T> = {x,y,z}"
      by auto
    ultimately show "(sup {x,y,z}) = sup {sup {x,y}, sup {z}}" by auto
  qed
  also from assms joinLatt have "... = sup {sup {x,y}, z}"
    unfolding IsJoinSemilattice_def IsPartOrder_def using join_props sup_inf_singl(2) 
    by auto
  also from assms joinLatt have "... = (sup {x,y}) \<squnion> z "
    unfolding IsJoinSemilattice_def IsPartOrder_def using join_props sup_inf_singl(2) 
    by auto
  also from joinLatt assms(1,2) have "... = x\<squnion>y\<squnion>z" using join_val by simp
  finally show "x\<squnion>(y\<squnion>z) = x\<squnion>y\<squnion>z" by simp
qed

text\<open> Join is idempotent. \<close>

lemma (in join_semilatt) join_idempotent: assumes "x\<in>L" shows "x\<squnion>x = x" 
  using joinLatt assms join_val IsJoinSemilattice_def IsPartOrder_def sup_inf_singl(2)
  by auto

end
