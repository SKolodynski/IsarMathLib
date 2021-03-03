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
  has a supremum (i.e. the least upper bound). \<close>

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

text\<open> Join is a binary operation whose value on a pair $\langle x,y\rangle$
  is defined as the supremum of the set $\{ x,y\}$. \<close>

definition
  "Join(L,r) \<equiv> {\<langle>p,Supremum(r,{fst(p),snd(p)})\<rangle> . p \<in> L\<times>L}"

text\<open> Meet is a binary operation whose value on a pair $\langle x,y\rangle$
  is defined as the infimum of the set $\{ x,y\}$.\<close>


definition
  "Meet(L,r) \<equiv> {\<langle>p,Infimum(r,{fst(p),snd(p)})\<rangle> . p \<in> L\<times>L}"

text\<open>Linear order is a lattice.\<close>

lemma lin_is_latt: assumes "r\<subseteq>L\<times>L" and "IsLinOrder(L,r)"
  shows "r {is a lattice on} L"
proof -
  from assms(2) have "IsPartOrder(L,r)" using Order_ZF_1_L2 by simp
  with assms have "IsMeetSemilattice(L,r)" unfolding IsLinOrder_def IsMeetSemilattice_def
    using inf_sup_two_el(1) by auto
  moreover from assms \<open>IsPartOrder(L,r)\<close> have "IsJoinSemilattice(L,r)"
    unfolding IsLinOrder_def IsJoinSemilattice_def using inf_sup_two_el(3) by auto
  ultimately show ?thesis unfolding IsAlattice_def by simp
qed

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
  of the set $\{ x,y\}$, hence its is greater or equal than both. \<close>

lemma join_val: 
  assumes "IsJoinSemilattice(L,r)" "x\<in>L" "y\<in>L"
  defines "j \<equiv> Join(L,r)`\<langle>x,y\<rangle>"
  shows "j\<in>L" "j = Supremum(r,{x,y})" "\<langle>x,j\<rangle> \<in> r" "\<langle>y,j\<rangle> \<in> r"
proof -
  from assms(1) have "Join(L,r) :  L\<times>L \<rightarrow> L" using join_is_binop by simp
  with assms(2,3,4) show "j = Supremum(r,{x,y})" unfolding Join_def using ZF_fun_from_tot_val 
    by auto
  from assms(2,3,4) \<open>Join(L,r) : L\<times>L \<rightarrow> L\<close>  show "j\<in>L" using apply_funtype by simp
  from assms(1,2,3) have "r \<subseteq> L\<times>L" "antisym(r)" "HasAminimum(r,\<Inter>z\<in>{x,y}. r``{z})"
    unfolding IsJoinSemilattice_def IsPartOrder_def HasAsupremum_def by auto
  with \<open>j = Supremum(r,{x,y})\<close> show "\<langle>x,j\<rangle> \<in> r" and "\<langle>y,j\<rangle> \<in> r"
    using sup_in_space(2) by auto
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
  of the set $\{ x,y\}$, hence is less or equal than both. \<close>

lemma meet_val: 
  assumes "IsMeetSemilattice(L,r)" "x\<in>L" "y\<in>L"
  defines "m \<equiv> Meet(L,r)`\<langle>x,y\<rangle>"
  shows "m\<in>L" "m = Infimum(r,{x,y})" "\<langle>m,x\<rangle> \<in> r" "\<langle>m,y\<rangle> \<in> r"
proof -
  from assms(1) have "Meet(L,r) : L\<times>L \<rightarrow> L" using meet_is_binop by simp
  with assms(2,3,4) show  "m = Infimum(r,{x,y})" unfolding Meet_def using ZF_fun_from_tot_val 
    by auto
  from assms(2,3,4) \<open>Meet(L,r) : L\<times>L \<rightarrow> L\<close>  show "m\<in>L" using apply_funtype by simp
  from assms(1,2,3) have "r \<subseteq> L\<times>L" "antisym(r)" "HasAmaximum(r,\<Inter>z\<in>{x,y}. r-``{z})"
    unfolding IsMeetSemilattice_def IsPartOrder_def HasAnInfimum_def by auto
  with \<open>m = Infimum(r,{x,y})\<close> show "\<langle>m,x\<rangle> \<in> r" and "\<langle>m,y\<rangle> \<in> r"
    using inf_in_space(2) by auto
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
  from joinLatt assms have "Join(L,r)`\<langle>x,y\<rangle> = Supremum(r,{x,y})" using join_val(2) 
    by simp
  thus "x\<squnion>y = sup {x,y}" by simp
qed

text\<open> Join is associative. \<close>

lemma (in join_semilatt) join_assoc: assumes "x\<in>L" "y\<in>L" "z\<in>L"
  shows "x\<squnion>(y\<squnion>z) = x\<squnion>y\<squnion>z"
proof -
  from joinLatt assms(2,3) have "x\<squnion>(y\<squnion>z) = x\<squnion>(sup {y,z})" using join_val(2) by simp
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
    unfolding IsJoinSemilattice_def IsPartOrder_def using join_props by auto
  also from joinLatt assms(1,2) have "... = x\<squnion>y\<squnion>z" using join_val(2) by simp
  finally show "x\<squnion>(y\<squnion>z) = x\<squnion>y\<squnion>z" by simp
qed

text\<open> Join is idempotent. \<close>

lemma (in join_semilatt) join_idempotent: assumes "x\<in>L" shows "x\<squnion>x = x" 
  using joinLatt assms join_val(2) IsJoinSemilattice_def IsPartOrder_def sup_inf_singl(2)
  by auto

text\<open> The \<open>meet_semilatt\<close> locale is the dual of the join-semilattice locale defined above.
  We will use the $\sqcap$ symbol to denote join, giving it ab bit higher precedence.\<close>

locale meet_semilatt =
  fixes L
  fixes r
  assumes meetLatt: "IsMeetSemilattice(L,r)"
  fixes join (infixl "\<sqinter>" 72)
  defines join_def [simp]: "x \<sqinter> y \<equiv> Meet(L,r)`\<langle>x,y\<rangle>"
  fixes sup ("inf _" ) 
  defines sup_def [simp]: "inf A  \<equiv> Infimum(r,A)"

text\<open> Meet of the elements of the lattice is in the lattice. \<close>

lemma (in meet_semilatt) meet_props: assumes "x\<in>L" "y\<in>L" 
  shows "x\<sqinter>y \<in> L" and "x\<sqinter>y = inf {x,y}"
proof -
  from meetLatt assms have "Meet(L,r)`\<langle>x,y\<rangle> \<in> L" using meet_is_binop apply_funtype 
    by blast
  thus "x\<sqinter>y \<in> L" by simp
  from meetLatt assms have "Meet(L,r)`\<langle>x,y\<rangle> = Infimum(r,{x,y})" using meet_val(2) by blast
  thus "x\<sqinter>y = inf {x,y}" by simp
qed

text\<open> Meet is associative. \<close>

lemma (in meet_semilatt) meet_assoc: assumes "x\<in>L" "y\<in>L" "z\<in>L"
  shows "x\<sqinter>(y\<sqinter>z) = x\<sqinter>y\<sqinter>z"
proof -
  from meetLatt assms(2,3) have "x\<sqinter>(y\<sqinter>z) = x\<sqinter>(inf {y,z})" using meet_val by simp
  also from assms meetLatt have "... = inf {inf {x}, inf {y,z}}"
    unfolding IsMeetSemilattice_def IsPartOrder_def using meet_props sup_inf_singl(4) 
    by auto
  also have "... = inf {x,y,z}"
  proof -
    let ?\<T> = "{{x},{y,z}}"
    from meetLatt have "r \<subseteq> L\<times>L" "antisym(r)" "trans(r)" 
      unfolding IsMeetSemilattice_def IsPartOrder_def by auto
    moreover from meetLatt assms have "\<forall>T\<in>?\<T>. HasAnInfimum(r,T)"
      unfolding IsMeetSemilattice_def IsPartOrder_def using sup_inf_singl(3) by blast
    moreover from meetLatt assms have "HasAnInfimum(r,{Infimum(r,T).T\<in>?\<T>})"
      unfolding IsMeetSemilattice_def IsPartOrder_def  HasAnInfimum_def 
      using inf_in_space(1) sup_inf_singl(4) by auto
    ultimately have "Infimum(r,{Infimum(r,T).T\<in>?\<T>}) = Infimum(r,\<Union>?\<T>)" by (rule inf_inf)
    moreover have "{Infimum(r,T).T\<in>?\<T>} = {inf {x}, inf {y,z}}" and "\<Union>?\<T> = {x,y,z}"
      by auto
    ultimately show "(inf {inf {x}, inf {y,z}}) =  inf {x,y,z}" by simp
  qed
  also have "... = inf {inf {x,y}, inf {z}}"
  proof -
    let ?\<T> = "{{x,y},{z}}"
    from meetLatt have "r \<subseteq> L\<times>L" "antisym(r)" "trans(r)" 
      unfolding IsMeetSemilattice_def IsPartOrder_def by auto
    moreover from meetLatt assms have "\<forall>T\<in>?\<T>. HasAnInfimum(r,T)"
      unfolding IsMeetSemilattice_def IsPartOrder_def using sup_inf_singl(3) by blast
    moreover from meetLatt assms have "HasAnInfimum(r,{Infimum(r,T).T\<in>?\<T>})"
      unfolding IsMeetSemilattice_def IsPartOrder_def HasAnInfimum_def 
      using inf_in_space(1) sup_inf_singl(4) by auto
    ultimately have "Infimum(r,{Infimum(r,T).T\<in>?\<T>}) = Infimum(r,\<Union>?\<T>)" by (rule inf_inf)
    moreover have "{Infimum(r,T).T\<in>?\<T>} = {inf {x,y}, inf {z}}" and "\<Union>?\<T> = {x,y,z}"
      by auto
    ultimately show "(inf {x,y,z}) = inf {inf {x,y}, inf {z}}" by auto
  qed
  also from assms meetLatt have "... = inf {inf {x,y}, z}"
    unfolding IsMeetSemilattice_def IsPartOrder_def using meet_props sup_inf_singl(4) 
    by auto
  also from assms meetLatt have "... = (inf {x,y}) \<sqinter> z "
    unfolding IsMeetSemilattice_def IsPartOrder_def using meet_props by auto
  also from meetLatt assms(1,2) have "... = x\<sqinter>y\<sqinter>z" using meet_val by simp
  finally show "x\<sqinter>(y\<sqinter>z) = x\<sqinter>y\<sqinter>z" by simp
qed

text\<open> Meet is idempotent. \<close>

lemma (in meet_semilatt) meet_idempotent: assumes "x\<in>L" shows "x\<sqinter>x = x" 
  using meetLatt assms meet_val IsMeetSemilattice_def IsPartOrder_def sup_inf_singl(4)
  by auto

end
