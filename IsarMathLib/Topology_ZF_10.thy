(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2013 Daniel de la Concepcion

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
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. *)

section \<open>Topology 10\<close>

theory Topology_ZF_10
imports Topology_ZF_7
begin

text\<open>This file deals with properties of product spaces. We only consider
product of two spaces, and most of this proofs, can be used to prove
the results in product of a finite number of spaces.\<close>

subsection\<open>Closure and closed sets in product space\<close>

text\<open>The closure of a product, is the product of the closures.\<close>

lemma cl_product:
  assumes "T{is a topology}" "S{is a topology}" "A\<subseteq>\<Union>T" "B\<subseteq>\<Union>S"
  shows "Closure(A\<times>B,ProductTopology(T,S))=Closure(A,T)\<times>Closure(B,S)"
proof
  have "A\<times>B\<subseteq>\<Union>T\<times>\<Union>S" using assms(3,4) by auto
  then have sub:"A\<times>B\<subseteq>\<Union>ProductTopology(T,S)" using Top_1_4_T1(3) assms(1,2) by auto
  have top:"ProductTopology(T,S){is a topology}" using Top_1_4_T1(1) assms(1,2) by auto
  {
    fix x assume asx:"x\<in>Closure(A\<times>B,ProductTopology(T,S))"
    then have reg:"\<forall>U\<in>ProductTopology(T,S). x\<in>U \<longrightarrow> U\<inter>(A\<times>B)\<noteq>0" using topology0.cl_inter_neigh
      sub top unfolding topology0_def by blast
    from asx have "x\<in>\<Union>ProductTopology(T,S)" using topology0.Top_3_L11(1) top unfolding topology0_def
      using sub by blast
    then have xSigma:"x\<in>\<Union>T\<times>\<Union>S" using Top_1_4_T1(3) assms(1,2) by auto
    then have "\<langle>fst(x),snd(x)\<rangle>\<in>\<Union>T\<times>\<Union>S" using Pair_fst_snd_eq by auto
    then have xT:"fst(x)\<in>\<Union>T" and xS:"snd(x)\<in>\<Union>S" by auto
    {
      fix U V assume as:"U\<in>T"  "fst(x)\<in>U"
      have "\<Union>S\<in>S" using assms(2) unfolding IsATopology_def by auto
      with as have "U\<times>(\<Union>S)\<in>ProductCollection(T,S)" unfolding ProductCollection_def
        by auto
      then have P:"U\<times>(\<Union>S)\<in>ProductTopology(T,S)" using Top_1_4_T1(2) assms(1,2) base_sets_open by blast
      with xS as(2) have "\<langle>fst(x),snd(x)\<rangle>\<in>U\<times>(\<Union>S)" by auto
      then have "x\<in>U\<times>(\<Union>S)" using Pair_fst_snd_eq xSigma by auto
      with P reg have "U\<times>(\<Union>S)\<inter>A\<times>B\<noteq>0" by auto
      then have noEm:"U\<inter>A\<noteq>0" by auto
    }
    then have "\<forall>U\<in>T. fst(x)\<in>U \<longrightarrow> U\<inter>A\<noteq>0" by auto moreover
    {
      fix U V assume as:"U\<in>S"  "snd(x)\<in>U"
      have "\<Union>T\<in>T" using assms(1) unfolding IsATopology_def by auto
      with as have "(\<Union>T)\<times>U\<in>ProductCollection(T,S)" unfolding ProductCollection_def
        by auto
      then have P:"(\<Union>T)\<times>U\<in>ProductTopology(T,S)" using Top_1_4_T1(2) assms(1,2) base_sets_open by blast
      with xT as(2) have "\<langle>fst(x),snd(x)\<rangle>\<in>(\<Union>T)\<times>U" by auto
      then have "x\<in>(\<Union>T)\<times>U" using Pair_fst_snd_eq xSigma by auto
      with P reg have "(\<Union>T)\<times>U\<inter>A\<times>B\<noteq>0" by auto
      then have noEm:"U\<inter>B\<noteq>0" by auto
    }
    then have "\<forall>U\<in>S. snd(x)\<in>U \<longrightarrow> U\<inter>B\<noteq>0" by auto
    ultimately have "fst(x)\<in>Closure(A,T)" "snd(x)\<in>Closure(B,S)" using 
      topology0.inter_neigh_cl assms(3,4) unfolding topology0_def
      using assms(1,2) xT xS by auto
    then have "\<langle>fst(x),snd(x)\<rangle>\<in>Closure(A,T)\<times>Closure(B,S)" by auto
    with xSigma have "x\<in>Closure(A,T)\<times>Closure(B,S)" by auto
  }
  then show "Closure(A\<times>B,ProductTopology(T,S))\<subseteq>Closure(A,T)\<times>Closure(B,S)" by auto
  {
    fix x assume x:"x\<in>Closure(A,T)\<times>Closure(B,S)"
    then have xcl:"fst(x)\<in>Closure(A,T)" "snd(x)\<in>Closure(B,S)" by auto
    from xcl(1) have regT:"\<forall>U\<in>T. fst(x)\<in>U \<longrightarrow> U\<inter>A\<noteq>0" using topology0.cl_inter_neigh
      unfolding topology0_def using assms(1,3) by blast
    from xcl(2) have regS:"\<forall>U\<in>S. snd(x)\<in>U \<longrightarrow> U\<inter>B\<noteq>0" using topology0.cl_inter_neigh
      unfolding topology0_def using assms(2,4) by blast
    from x assms(3,4) have "x\<in>\<Union>T\<times>\<Union>S" using topology0.Top_3_L11(1) unfolding topology0_def
      using assms(1,2) by blast
    then have xtot:"x\<in>\<Union>ProductTopology(T,S)" using Top_1_4_T1(3) assms(1,2) by auto
    {
      fix PO assume as:"PO\<in>ProductTopology(T,S)" "x\<in>PO"
      then obtain POB where base:"POB\<in>ProductCollection(T,S)" "x\<in>POB""POB\<subseteq>PO" using point_open_base_neigh
        Top_1_4_T1(2) assms(1,2) base_sets_open by blast
      then obtain VT VS where V:"VT\<in>T" "VS\<in>S" "x\<in>VT\<times>VS" "POB=VT\<times>VS" unfolding ProductCollection_def
        by auto
      from V(3) have x:"fst(x)\<in>VT" "snd(x)\<in>VS" by auto
      from V(1) regT x(1) have "VT\<inter>A\<noteq>0" by auto moreover
      from V(2) regS x(2) have "VS\<inter>B\<noteq>0" by auto ultimately
      have "VT\<times>VS\<inter>A\<times>B\<noteq>0" by auto
      with V(4) base(3) have "PO\<inter>A\<times>B\<noteq>0" by blast
    }
    then have "\<forall>P\<in>ProductTopology(T,S). x\<in>P \<longrightarrow> P\<inter>A\<times>B\<noteq>0" by auto
    then have "x\<in>Closure(A\<times>B,ProductTopology(T,S))" using topology0.inter_neigh_cl
      unfolding topology0_def using top sub xtot by auto
  }
  then show "Closure(A,T)\<times>Closure(B,S)\<subseteq>Closure(A\<times>B,ProductTopology(T,S))" by auto
qed

text\<open>The product of closed sets, is closed in the product topology.\<close>

corollary closed_product:
  assumes "T{is a topology}" "S{is a topology}" "A{is closed in}T""B{is closed in}S"
  shows "(A\<times>B) {is closed in}ProductTopology(T,S)"
proof-
  from assms(3,4) have sub:"A\<subseteq>\<Union>T""B\<subseteq>\<Union>S" unfolding IsClosed_def by auto
  then have "A\<times>B\<subseteq>\<Union>T\<times>\<Union>S" by auto
  then have sub1:"A\<times>B\<subseteq>\<Union>ProductTopology(T,S)" using Top_1_4_T1(3) assms(1,2) by auto
  from sub assms have "Closure(A,T)=A""Closure(B,S)=B" using topology0.Top_3_L8
    unfolding topology0_def by auto
  then have "Closure(A\<times>B,ProductTopology(T,S))=A\<times>B" using cl_product
    assms(1,2) sub by auto
  then show ?thesis using topology0.Top_3_L8 unfolding topology0_def
    using sub1 Top_1_4_T1(1) assms(1,2) by auto
qed

subsection\<open>Separation properties in product space\<close>

text\<open>The product of $T_0$ spaces is $T_0$.\<close>

theorem T0_product:
  assumes "T{is a topology}""S{is a topology}""T{is T\<^sub>0}""S{is T\<^sub>0}"
  shows "ProductTopology(T,S){is T\<^sub>0}"
proof-
  {
    fix x y assume "x\<in>\<Union>ProductTopology(T,S)""y\<in>\<Union>ProductTopology(T,S)""x\<noteq>y"
    then have tot:"x\<in>\<Union>T\<times>\<Union>S""y\<in>\<Union>T\<times>\<Union>S""x\<noteq>y" using Top_1_4_T1(3) assms(1,2) by auto
    then have "\<langle>fst(x),snd(x)\<rangle>\<in>\<Union>T\<times>\<Union>S""\<langle>fst(y),snd(y)\<rangle>\<in>\<Union>T\<times>\<Union>S" and disj:"fst(x)\<noteq>fst(y)\<or>snd(x)\<noteq>snd(y)" 
      using Pair_fst_snd_eq by auto
    then have T:"fst(x)\<in>\<Union>T""fst(y)\<in>\<Union>T" and S:"snd(y)\<in>\<Union>S""snd(x)\<in>\<Union>S" and p:"fst(x)\<noteq>fst(y)\<or>snd(x)\<noteq>snd(y)"
      by auto
    {
      assume "fst(x)\<noteq>fst(y)"
      with T assms(3) have "(\<exists>U\<in>T. (fst(x)\<in>U\<and>fst(y)\<notin>U)\<or>(fst(y)\<in>U\<and>fst(x)\<notin>U))" unfolding
        isT0_def by auto
      then obtain U where "U\<in>T" "(fst(x)\<in>U\<and>fst(y)\<notin>U)\<or>(fst(y)\<in>U\<and>fst(x)\<notin>U)" by auto
      with S have "(\<langle>fst(x),snd(x)\<rangle>\<in>U\<times>(\<Union>S) \<and> \<langle>fst(y),snd(y)\<rangle>\<notin>U\<times>(\<Union>S))\<or>(\<langle>fst(y),snd(y)\<rangle>\<in>U\<times>(\<Union>S) \<and> \<langle>fst(x),snd(x)\<rangle>\<notin>U\<times>(\<Union>S))"
        by auto
      then have "(x\<in>U\<times>(\<Union>S) \<and> y\<notin>U\<times>(\<Union>S))\<or>(y\<in>U\<times>(\<Union>S) \<and> x\<notin>U\<times>(\<Union>S))" using Pair_fst_snd_eq tot(1,2) by auto
      moreover have "(\<Union>S)\<in>S" using assms(2) unfolding IsATopology_def by auto
      with \<open>U\<in>T\<close> have "U\<times>(\<Union>S)\<in>ProductTopology(T,S)" using prod_open_open_prod assms(1,2) by auto
      ultimately
      have "\<exists>V\<in>ProductTopology(T,S). (x\<in>V \<and> y\<notin>V)\<or>(y\<in>V \<and> x\<notin>V)" proof qed
    } moreover
    {
      assume "snd(x)\<noteq>snd(y)"
      with S assms(4) have "(\<exists>U\<in>S. (snd(x)\<in>U\<and>snd(y)\<notin>U)\<or>(snd(y)\<in>U\<and>snd(x)\<notin>U))" unfolding
        isT0_def by auto
      then obtain U where "U\<in>S" "(snd(x)\<in>U\<and>snd(y)\<notin>U)\<or>(snd(y)\<in>U\<and>snd(x)\<notin>U)" by auto
      with T have "(\<langle>fst(x),snd(x)\<rangle>\<in>(\<Union>T)\<times>U \<and> \<langle>fst(y),snd(y)\<rangle>\<notin>(\<Union>T)\<times>U)\<or>(\<langle>fst(y),snd(y)\<rangle>\<in>(\<Union>T)\<times>U \<and> \<langle>fst(x),snd(x)\<rangle>\<notin>(\<Union>T)\<times>U)"
        by auto
      then have "(x\<in>(\<Union>T)\<times>U \<and> y\<notin>(\<Union>T)\<times>U)\<or>(y\<in>(\<Union>T)\<times>U \<and> x\<notin>(\<Union>T)\<times>U)" using Pair_fst_snd_eq tot(1,2) by auto
      moreover have "(\<Union>T)\<in>T" using assms(1) unfolding IsATopology_def by auto
      with \<open>U\<in>S\<close> have "(\<Union>T)\<times>U\<in>ProductTopology(T,S)" using prod_open_open_prod assms(1,2) by auto
      ultimately
      have "\<exists>V\<in>ProductTopology(T,S). (x\<in>V \<and> y\<notin>V)\<or>(y\<in>V \<and> x\<notin>V)" proof qed
    }moreover
    note disj
    ultimately have "\<exists>V\<in>ProductTopology(T,S). (x\<in>V \<and> y\<notin>V)\<or>(y\<in>V \<and> x\<notin>V)" by auto
  }
  then show ?thesis unfolding isT0_def by auto
qed

text\<open>The product of $T_1$ spaces is $T_1$.\<close>

theorem T1_product:
  assumes "T{is a topology}""S{is a topology}""T{is T\<^sub>1}""S{is T\<^sub>1}"
  shows "ProductTopology(T,S){is T\<^sub>1}"
proof-
  {
    fix x y assume "x\<in>\<Union>ProductTopology(T,S)""y\<in>\<Union>ProductTopology(T,S)""x\<noteq>y"
    then have tot:"x\<in>\<Union>T\<times>\<Union>S""y\<in>\<Union>T\<times>\<Union>S""x\<noteq>y" using Top_1_4_T1(3) assms(1,2) by auto
    then have "\<langle>fst(x),snd(x)\<rangle>\<in>\<Union>T\<times>\<Union>S""\<langle>fst(y),snd(y)\<rangle>\<in>\<Union>T\<times>\<Union>S" and disj:"fst(x)\<noteq>fst(y)\<or>snd(x)\<noteq>snd(y)" 
      using Pair_fst_snd_eq by auto
    then have T:"fst(x)\<in>\<Union>T""fst(y)\<in>\<Union>T" and S:"snd(y)\<in>\<Union>S""snd(x)\<in>\<Union>S" and p:"fst(x)\<noteq>fst(y)\<or>snd(x)\<noteq>snd(y)"
      by auto
    {
      assume "fst(x)\<noteq>fst(y)"
      with T assms(3) have "(\<exists>U\<in>T. (fst(x)\<in>U\<and>fst(y)\<notin>U))" unfolding
        isT1_def by auto
      then obtain U where "U\<in>T" "(fst(x)\<in>U\<and>fst(y)\<notin>U)" by auto
      with S have "(\<langle>fst(x),snd(x)\<rangle>\<in>U\<times>(\<Union>S) \<and> \<langle>fst(y),snd(y)\<rangle>\<notin>U\<times>(\<Union>S))" by auto
      then have "(x\<in>U\<times>(\<Union>S) \<and> y\<notin>U\<times>(\<Union>S))" using Pair_fst_snd_eq tot(1,2) by auto
      moreover have "(\<Union>S)\<in>S" using assms(2) unfolding IsATopology_def by auto
      with \<open>U\<in>T\<close> have "U\<times>(\<Union>S)\<in>ProductTopology(T,S)" using prod_open_open_prod assms(1,2) by auto
      ultimately
      have "\<exists>V\<in>ProductTopology(T,S). (x\<in>V \<and> y\<notin>V)" proof qed
    } moreover
    {
      assume "snd(x)\<noteq>snd(y)"
      with S assms(4) have "(\<exists>U\<in>S. (snd(x)\<in>U\<and>snd(y)\<notin>U))" unfolding
        isT1_def by auto
      then obtain U where "U\<in>S" "(snd(x)\<in>U\<and>snd(y)\<notin>U)" by auto
      with T have "(\<langle>fst(x),snd(x)\<rangle>\<in>(\<Union>T)\<times>U \<and> \<langle>fst(y),snd(y)\<rangle>\<notin>(\<Union>T)\<times>U)" by auto
      then have "(x\<in>(\<Union>T)\<times>U \<and> y\<notin>(\<Union>T)\<times>U)" using Pair_fst_snd_eq tot(1,2) by auto
      moreover have "(\<Union>T)\<in>T" using assms(1) unfolding IsATopology_def by auto
      with \<open>U\<in>S\<close> have "(\<Union>T)\<times>U\<in>ProductTopology(T,S)" using prod_open_open_prod assms(1,2) by auto
      ultimately
      have "\<exists>V\<in>ProductTopology(T,S). (x\<in>V \<and> y\<notin>V)" proof qed
    }moreover
    note disj
    ultimately have "\<exists>V\<in>ProductTopology(T,S). (x\<in>V \<and> y\<notin>V)" by auto
  }
  then show ?thesis unfolding isT1_def by auto
qed

text\<open>The product of $T_2$ spaces is $T_2$.\<close>

theorem T2_product:
  assumes "T{is a topology}""S{is a topology}""T{is T\<^sub>2}""S{is T\<^sub>2}"
  shows "ProductTopology(T,S){is T\<^sub>2}"
proof-
  {
    fix x y assume "x\<in>\<Union>ProductTopology(T,S)""y\<in>\<Union>ProductTopology(T,S)""x\<noteq>y"
    then have tot:"x\<in>\<Union>T\<times>\<Union>S""y\<in>\<Union>T\<times>\<Union>S""x\<noteq>y" using Top_1_4_T1(3) assms(1,2) by auto
    then have "\<langle>fst(x),snd(x)\<rangle>\<in>\<Union>T\<times>\<Union>S""\<langle>fst(y),snd(y)\<rangle>\<in>\<Union>T\<times>\<Union>S" and disj:"fst(x)\<noteq>fst(y)\<or>snd(x)\<noteq>snd(y)" 
      using Pair_fst_snd_eq by auto
    then have T:"fst(x)\<in>\<Union>T""fst(y)\<in>\<Union>T" and S:"snd(y)\<in>\<Union>S""snd(x)\<in>\<Union>S" and p:"fst(x)\<noteq>fst(y)\<or>snd(x)\<noteq>snd(y)"
      by auto
    {
      assume "fst(x)\<noteq>fst(y)"
      with T assms(3) have "(\<exists>U\<in>T. \<exists>V\<in>T. (fst(x)\<in>U\<and>fst(y)\<in>V) \<and> U\<inter>V=0)" unfolding
        isT2_def by auto
      then obtain U V where "U\<in>T" "V\<in>T" "fst(x)\<in>U" "fst(y)\<in>V" "U\<inter>V=0" by auto
      with S have "\<langle>fst(x),snd(x)\<rangle>\<in>U\<times>(\<Union>S)" "\<langle>fst(y),snd(y)\<rangle>\<in>V\<times>(\<Union>S)" and disjoint:"(U\<times>\<Union>S)\<inter>(V\<times>\<Union>S)=0" by auto
      then have "x\<in>U\<times>(\<Union>S)""y\<in>V\<times>(\<Union>S)" using Pair_fst_snd_eq tot(1,2) by auto
      moreover have "(\<Union>S)\<in>S" using assms(2) unfolding IsATopology_def by auto
      with \<open>U\<in>T\<close>\<open>V\<in>T\<close> have P:"U\<times>(\<Union>S)\<in>ProductTopology(T,S)" "V\<times>(\<Union>S)\<in>ProductTopology(T,S)" 
        using prod_open_open_prod assms(1,2) by auto
      note disjoint ultimately 
      have "x\<in>U\<times>(\<Union>S) \<and> y\<in>V\<times>(\<Union>S) \<and> (U\<times>(\<Union>S))\<inter>(V\<times>(\<Union>S))=0" by auto
      with P(2) have "\<exists>UU\<in>ProductTopology(T,S). (x\<in>U\<times>(\<Union>S) \<and> y\<in>UU \<and> (U\<times>(\<Union>S))\<inter>UU=0)"
        using exI[where x="V\<times>(\<Union>S)" and P="\<lambda>t. t\<in>ProductTopology(T,S) \<and> (x\<in>U\<times>(\<Union>S) \<and> y\<in>t \<and> (U\<times>(\<Union>S))\<inter>t=0)"] by auto
      with P(1) have "\<exists>VV\<in>ProductTopology(T,S). \<exists>UU\<in>ProductTopology(T,S). (x\<in>VV \<and> y\<in>UU \<and> VV\<inter>UU=0)" 
        using exI[where x="U\<times>(\<Union>S)" and P="\<lambda>t. t\<in>ProductTopology(T,S) \<and> (\<exists>UU\<in>ProductTopology(T,S). (x\<in>t \<and> y\<in>UU \<and> (t)\<inter>UU=0))"] by auto
    } moreover
    {
      assume "snd(x)\<noteq>snd(y)"
      with S assms(4) have "(\<exists>U\<in>S. \<exists>V\<in>S. (snd(x)\<in>U\<and>snd(y)\<in>V) \<and> U\<inter>V=0)" unfolding
        isT2_def by auto
      then obtain U V where "U\<in>S" "V\<in>S" "snd(x)\<in>U" "snd(y)\<in>V" "U\<inter>V=0" by auto
      with T have "\<langle>fst(x),snd(x)\<rangle>\<in>(\<Union>T)\<times>U" "\<langle>fst(y),snd(y)\<rangle>\<in>(\<Union>T)\<times>V" and disjoint:"((\<Union>T)\<times>U)\<inter>((\<Union>T)\<times>V)=0" by auto
      then have "x\<in>(\<Union>T)\<times>U""y\<in>(\<Union>T)\<times>V" using Pair_fst_snd_eq tot(1,2) by auto
      moreover have "(\<Union>T)\<in>T" using assms(1) unfolding IsATopology_def by auto
      with \<open>U\<in>S\<close>\<open>V\<in>S\<close> have P:"(\<Union>T)\<times>U\<in>ProductTopology(T,S)" "(\<Union>T)\<times>V\<in>ProductTopology(T,S)" 
        using prod_open_open_prod assms(1,2) by auto
      note disjoint ultimately 
      have "x\<in>(\<Union>T)\<times>U \<and> y\<in>(\<Union>T)\<times>V \<and> ((\<Union>T)\<times>U)\<inter>((\<Union>T)\<times>V)=0" by auto
      with P(2) have "\<exists>UU\<in>ProductTopology(T,S). (x\<in>(\<Union>T)\<times>U \<and> y\<in>UU \<and> ((\<Union>T)\<times>U)\<inter>UU=0)"
        using exI[where x="(\<Union>T)\<times>V" and P="\<lambda>t. t\<in>ProductTopology(T,S) \<and> (x\<in>(\<Union>T)\<times>U \<and> y\<in>t \<and> ((\<Union>T)\<times>U)\<inter>t=0)"] by auto
      with P(1) have "\<exists>VV\<in>ProductTopology(T,S). \<exists>UU\<in>ProductTopology(T,S). (x\<in>VV \<and> y\<in>UU \<and> VV\<inter>UU=0)" 
        using exI[where x="(\<Union>T)\<times>U" and P="\<lambda>t. t\<in>ProductTopology(T,S) \<and> (\<exists>UU\<in>ProductTopology(T,S). (x\<in>t \<and> y\<in>UU \<and> (t)\<inter>UU=0))"] by auto
    } moreover
    note disj
    ultimately have "\<exists>VV\<in>ProductTopology(T, S). \<exists>UU\<in>ProductTopology(T, S). x \<in> VV \<and> y \<in> UU \<and> VV \<inter> UU = 0" by auto
  }
  then show ?thesis unfolding isT2_def by auto
qed

text\<open>The product of regular spaces is regular.\<close>

theorem regular_product:
  assumes "T{is a topology}" "S{is a topology}" "T{is regular}" "S{is regular}"
  shows "ProductTopology(T,S){is regular}"
proof-
  {
    fix x U assume "x\<in>\<Union>ProductTopology(T,S)" "U\<in>ProductTopology(T,S)" "x\<in>U"
    then obtain V W where VW:"V\<in>T""W\<in>S" "V\<times>W\<subseteq>U" and x:"x\<in>V\<times>W" using prod_top_point_neighb 
      assms(1,2) by blast
    then have p:"fst(x)\<in>V""snd(x)\<in>W" by auto
    from p(1) \<open>V\<in>T\<close> obtain VV where VV:"fst(x)\<in>VV" "Closure(VV,T)\<subseteq>V" "VV\<in>T" using 
      assms(1,3) topology0.regular_imp_exist_clos_neig unfolding topology0_def
      by force moreover
    from p(2) \<open>W\<in>S\<close> obtain WW where WW:"snd(x)\<in>WW" "Closure(WW,S)\<subseteq>W" "WW\<in>S" using 
      assms(2,4) topology0.regular_imp_exist_clos_neig unfolding topology0_def
      by force ultimately
    have  "x\<in>VV\<times>WW" using x by auto
    moreover from  \<open>Closure(VV,T)\<subseteq>V\<close> \<open>Closure(WW,S)\<subseteq>W\<close> have "Closure(VV,T)\<times>Closure(WW,S) \<subseteq> V\<times>W"
      by auto 
    moreover from VV(3) WW(3) have "VV\<subseteq>\<Union>T""WW\<subseteq>\<Union>S" by auto
    ultimately have "x\<in>VV\<times>WW" "Closure(VV\<times>WW,ProductTopology(T,S)) \<subseteq> V\<times>W" using cl_product assms(1,2)
      by auto
    moreover have "VV\<times>WW\<in>ProductTopology(T,S)" using prod_open_open_prod assms(1,2)
      VV(3) WW(3) by auto
    ultimately have "\<exists>Z\<in>ProductTopology(T,S). x\<in>Z \<and> Closure(Z,ProductTopology(T,S))\<subseteq>V\<times>W" by auto
    with VW(3) have "\<exists>Z\<in>ProductTopology(T,S). x\<in>Z \<and> Closure(Z,ProductTopology(T,S))\<subseteq>U" by auto
  }
  then have "\<forall>x\<in>\<Union>ProductTopology(T,S). \<forall>U\<in>ProductTopology(T,S).x\<in>U \<longrightarrow> (\<exists>Z\<in>ProductTopology(T,S). x\<in>Z \<and> Closure(Z,ProductTopology(T,S))\<subseteq>U)"
    by auto
  then show ?thesis using topology0.exist_clos_neig_imp_regular unfolding topology0_def
    using assms(1,2) Top_1_4_T1(1) by auto
qed

subsection\<open>Connection properties in product space\<close>

text\<open>First, we prove that the projection functions are open.\<close>

lemma projection_open:
  assumes "T{is a topology}""S{is a topology}""B\<in>ProductTopology(T,S)"
  shows "{y\<in>\<Union>T. \<exists>x\<in>\<Union>S. \<langle>y,x\<rangle>\<in>B}\<in>T"
proof-
  {
    fix z assume "z\<in>{y\<in>\<Union>T. \<exists>x\<in>\<Union>S. \<langle>y,x\<rangle>\<in>B}"
    then obtain x where x:"x\<in>\<Union>S" and z:"z\<in>\<Union>T" and p:"\<langle>z,x\<rangle>\<in>B" by auto
    then have "z\<in>{y\<in>\<Union>T. \<langle>y,x\<rangle>\<in>B}" "{y\<in>\<Union>T. \<langle>y,x\<rangle>\<in>B}\<subseteq>{y\<in>\<Union>T. \<exists>x\<in>\<Union>S. \<langle>y,x\<rangle>\<in>B}" by auto moreover
    from x have "{y\<in>\<Union>T. \<langle>y,x\<rangle>\<in>B}\<in>T" using prod_sec_open2 assms by auto
    ultimately have "\<exists>V\<in>T. z\<in>V \<and> V\<subseteq>{y\<in>\<Union>T. \<exists>x\<in>\<Union>S. \<langle>y,x\<rangle>\<in>B}" unfolding Bex_def by auto
  }   
  then show "{y\<in>\<Union>T. \<exists>x\<in>\<Union>S. \<langle>y,x\<rangle>\<in>B}\<in>T" using topology0.open_neigh_open unfolding topology0_def
    using assms(1) by blast
qed

lemma projection_open2:
  assumes "T{is a topology}""S{is a topology}""B\<in>ProductTopology(T,S)"
  shows "{y\<in>\<Union>S. \<exists>x\<in>\<Union>T. \<langle>x,y\<rangle>\<in>B}\<in>S"
proof-
  {
    fix z assume "z\<in>{y\<in>\<Union>S. \<exists>x\<in>\<Union>T. \<langle>x,y\<rangle>\<in>B}"
    then obtain x where x:"x\<in>\<Union>T" and z:"z\<in>\<Union>S" and p:"\<langle>x,z\<rangle>\<in>B" by auto
    then have "z\<in>{y\<in>\<Union>S. \<langle>x,y\<rangle>\<in>B}" "{y\<in>\<Union>S. \<langle>x,y\<rangle>\<in>B}\<subseteq>{y\<in>\<Union>S. \<exists>x\<in>\<Union>T. \<langle>x,y\<rangle>\<in>B}" by auto moreover
    from x have "{y\<in>\<Union>S. \<langle>x,y\<rangle>\<in>B}\<in>S" using prod_sec_open1 assms by auto
    ultimately have "\<exists>V\<in>S. z\<in>V \<and> V\<subseteq>{y\<in>\<Union>S. \<exists>x\<in>\<Union>T. \<langle>x,y\<rangle>\<in>B}" unfolding Bex_def by auto
  }   
  then show "{y\<in>\<Union>S. \<exists>x\<in>\<Union>T. \<langle>x,y\<rangle>\<in>B}\<in>S" using topology0.open_neigh_open unfolding topology0_def
    using assms(2) by blast
qed

text\<open>The product of connected spaces is connected.\<close>

theorem compact_product:
  assumes "T{is a topology}""S{is a topology}""T{is connected}""S{is connected}"
  shows "ProductTopology(T,S){is connected}"
proof-
  {
    fix U assume U:"U\<in>ProductTopology(T,S)" "U{is closed in}ProductTopology(T,S)"
    then have P:"U\<in>ProductTopology(T,S)" "\<Union>ProductTopology(T,S)-U\<in>ProductTopology(T,S)"
      unfolding IsClosed_def by auto
    {
      fix s assume s:"s\<in>\<Union>S" 
      with P(1) have p:"{x\<in>\<Union>T. \<langle>x,s\<rangle>\<in>U}\<in>T" using prod_sec_open2 assms(1,2) by auto
      from s P(2) have oop:"{y\<in>\<Union>T. \<langle>y,s\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)}\<in>T" using prod_sec_open2
        assms(1,2) by blast
      then have "\<Union>T-(\<Union>T-{y\<in>\<Union>T. \<langle>y,s\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)})={y\<in>\<Union>T. \<langle>y,s\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)}" by auto
      with oop have cl:"(\<Union>T-{y\<in>\<Union>T. \<langle>y,s\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)}) {is closed in}T" unfolding IsClosed_def by auto
      {
        fix t assume "t\<in>\<Union>T-{y\<in>\<Union>T. \<langle>y,s\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)}"
        then have tt:"t\<in>\<Union>T" "t\<notin>{y\<in>\<Union>T. \<langle>y,s\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)}" by auto
        then have "\<langle>t,s\<rangle>\<notin>(\<Union>ProductTopology(T,S)-U)" by auto
        then have "\<langle>t,s\<rangle>\<in>U \<or> \<langle>t,s\<rangle>\<notin>\<Union>ProductTopology(T,S)" by auto
        then have "\<langle>t,s\<rangle>\<in>U \<or> \<langle>t,s\<rangle>\<notin>\<Union>T\<times>\<Union>S" using Top_1_4_T1(3) assms(1,2) by auto
        with tt(1) s have "\<langle>t,s\<rangle>\<in>U" by auto
        with tt(1) have "t\<in>{x\<in>\<Union>T. \<langle>x,s\<rangle>\<in>U}" by auto
      } moreover
      {
        fix t assume "t\<in>{x\<in>\<Union>T. \<langle>x,s\<rangle>\<in>U}"
        then have tt:"t\<in>\<Union>T" "\<langle>t,s\<rangle>\<in>U" by auto
        then have "\<langle>t,s\<rangle>\<notin>\<Union>ProductTopology(T,S)-U" by auto
        then have "t\<notin>{y\<in>\<Union>T. \<langle>y,s\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)}" by auto
        with tt(1) have "t\<in>\<Union>T-{y\<in>\<Union>T. \<langle>y,s\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)}" by auto
      }
      ultimately have "{x\<in>\<Union>T. \<langle>x,s\<rangle>\<in>U}=\<Union>T-{y\<in>\<Union>T. \<langle>y,s\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)}" by blast
      with cl have "{x\<in>\<Union>T. \<langle>x,s\<rangle>\<in>U}{is closed in}T" by auto
      with p assms(3) have "{x\<in>\<Union>T. \<langle>x,s\<rangle>\<in>U}=0 \<or> {x\<in>\<Union>T. \<langle>x,s\<rangle>\<in>U}=\<Union>T" unfolding IsConnected_def
        by auto moreover
      {
        assume "{x\<in>\<Union>T. \<langle>x,s\<rangle>\<in>U}=0"
        then have "\<forall>x\<in>\<Union>T. \<langle>x,s\<rangle>\<notin>U" by auto
      }
      moreover
      {
        assume AA:"{x\<in>\<Union>T. \<langle>x,s\<rangle>\<in>U}=\<Union>T"
        {
          fix x assume "x\<in>\<Union>T"
          with AA have "x\<in>{x\<in>\<Union>T. \<langle>x,s\<rangle>\<in>U}" by auto
          then have "\<langle>x,s\<rangle>\<in>U" by auto
        }
        then have "\<forall>x\<in>\<Union>T. \<langle>x,s\<rangle>\<in>U" by auto
      }
      ultimately have "(\<forall>x\<in>\<Union>T. \<langle>x,s\<rangle>\<notin>U) \<or> (\<forall>x\<in>\<Union>T. \<langle>x,s\<rangle>\<in>U)" by blast
    }
    then have reg:"\<forall>s\<in>\<Union>S. (\<forall>x\<in>\<Union>T. \<langle>x,s\<rangle>\<notin>U) \<or> (\<forall>x\<in>\<Union>T. \<langle>x,s\<rangle>\<in>U)" by auto
    {
      fix q assume qU:"q\<in>\<Union>T\<times>{snd(qq). qq\<in>U}"
      then obtain t u where t:"t\<in>\<Union>T" "u\<in>U" "q=\<langle>t,snd(u)\<rangle>" by auto
      with U(1) have "u\<in>\<Union>ProductTopology(T,S)" by auto
      then have "u\<in>\<Union>T\<times>\<Union>S" using Top_1_4_T1(3) assms(1,2) by auto moreover
      then have uu:"u=\<langle>fst(u),snd(u)\<rangle>" using Pair_fst_snd_eq by auto ultimately
      have fu:"fst(u)\<in>\<Union>T""snd(u)\<in>\<Union>S" by (safe,auto)
      with reg have "(\<forall>tt\<in>\<Union>T. \<langle>tt,snd(u)\<rangle>\<notin>U)\<or>(\<forall>tt\<in>\<Union>T. \<langle>tt,snd(u)\<rangle>\<in>U)" by auto
      with \<open>u\<in>U\<close> uu fu(1) have "\<forall>tt\<in>\<Union>T. \<langle>tt,snd(u)\<rangle>\<in>U" by force
      with t(1,3) have "q\<in>U" by auto
    }
    then have U1:"\<Union>T\<times>{snd(qq). qq\<in>U}\<subseteq>U" by auto
    {
      fix t assume t:"t\<in>\<Union>T" 
      with P(1) have p:"{x\<in>\<Union>S. \<langle>t,x\<rangle>\<in>U}\<in>S" using prod_sec_open1 assms(1,2) by auto
      from t P(2) have oop:"{x\<in>\<Union>S. \<langle>t,x\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)}\<in>S" using prod_sec_open1
        assms(1,2) by blast
      then have "\<Union>S-(\<Union>S-{x\<in>\<Union>S. \<langle>t,x\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)})={y\<in>\<Union>S. \<langle>t,y\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)}" by auto
      with oop have cl:"(\<Union>S-{y\<in>\<Union>S. \<langle>t,y\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)}) {is closed in}S" unfolding IsClosed_def by auto
      {
        fix s assume "s\<in>\<Union>S-{y\<in>\<Union>S. \<langle>t,y\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)}"
        then have tt:"s\<in>\<Union>S" "s\<notin>{y\<in>\<Union>S. \<langle>t,y\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)}" by auto
        then have "\<langle>t,s\<rangle>\<notin>(\<Union>ProductTopology(T,S)-U)" by auto
        then have "\<langle>t,s\<rangle>\<in>U \<or> \<langle>t,s\<rangle>\<notin>\<Union>ProductTopology(T,S)" by auto
        then have "\<langle>t,s\<rangle>\<in>U \<or> \<langle>t,s\<rangle>\<notin>\<Union>T\<times>\<Union>S" using Top_1_4_T1(3) assms(1,2) by auto
        with tt(1) t have "\<langle>t,s\<rangle>\<in>U" by auto
        with tt(1) have "s\<in>{x\<in>\<Union>S. \<langle>t,x\<rangle>\<in>U}" by auto
      } moreover
      {
        fix s assume "s\<in>{x\<in>\<Union>S. \<langle>t,x\<rangle>\<in>U}"
        then have tt:"s\<in>\<Union>S" "\<langle>t,s\<rangle>\<in>U" by auto
        then have "\<langle>t,s\<rangle>\<notin>\<Union>ProductTopology(T,S)-U" by auto
        then have "s\<notin>{y\<in>\<Union>S. \<langle>t,y\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)}" by auto
        with tt(1) have "s\<in>\<Union>S-{y\<in>\<Union>S. \<langle>t,y\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)}" by auto
      }
      ultimately have "{x\<in>\<Union>S. \<langle>t,x\<rangle>\<in>U}=\<Union>S-{y\<in>\<Union>S. \<langle>t,y\<rangle>\<in>(\<Union>ProductTopology(T,S)-U)}" by blast
      with cl have "{x\<in>\<Union>S. \<langle>t,x\<rangle>\<in>U}{is closed in}S" by auto
      with p assms(4) have "{x\<in>\<Union>S. \<langle>t,x\<rangle>\<in>U}=0 \<or> {x\<in>\<Union>S. \<langle>t,x\<rangle>\<in>U}=\<Union>S" unfolding IsConnected_def
        by auto moreover
      {
        assume "{x\<in>\<Union>S. \<langle>t,x\<rangle>\<in>U}=0"
        then have "\<forall>x\<in>\<Union>S. \<langle>t,x\<rangle>\<notin>U" by auto
      }
      moreover
      {
        assume AA:"{x\<in>\<Union>S. \<langle>t,x\<rangle>\<in>U}=\<Union>S"
        {
          fix x assume "x\<in>\<Union>S"
          with AA have "x\<in>{x\<in>\<Union>S. \<langle>t,x\<rangle>\<in>U}" by auto
          then have "\<langle>t,x\<rangle>\<in>U" by auto
        }
        then have "\<forall>x\<in>\<Union>S. \<langle>t,x\<rangle>\<in>U" by auto
      }
      ultimately have "(\<forall>x\<in>\<Union>S. \<langle>t,x\<rangle>\<notin>U) \<or> (\<forall>x\<in>\<Union>S. \<langle>t,x\<rangle>\<in>U)" by blast
    }
    then have reg:"\<forall>s\<in>\<Union>T. (\<forall>x\<in>\<Union>S. \<langle>s,x\<rangle>\<notin>U) \<or> (\<forall>x\<in>\<Union>S. \<langle>s,x\<rangle>\<in>U)" by auto
    {
      fix q assume qU:"q\<in>{fst(qq). qq\<in>U}\<times>\<Union>S"
      then obtain qq s where t:"q=\<langle>fst(qq),s\<rangle>" "qq\<in>U" "s\<in>\<Union>S" by auto
      with U(1) have "qq\<in>\<Union>ProductTopology(T,S)" by auto
      then have "qq\<in>\<Union>T\<times>\<Union>S" using Top_1_4_T1(3) assms(1,2) by auto moreover
      then have qq:"qq=\<langle>fst(qq),snd(qq)\<rangle>" using Pair_fst_snd_eq by auto ultimately
      have fq:"fst(qq)\<in>\<Union>T""snd(qq)\<in>\<Union>S" by (safe,auto)
      from fq(1) reg have "(\<forall>tt\<in>\<Union>S. \<langle>fst(qq),tt\<rangle>\<notin>U)\<or>(\<forall>tt\<in>\<Union>S. \<langle>fst(qq),tt\<rangle>\<in>U)" by auto moreover
      with \<open>qq\<in>U\<close> qq fq(2) have "\<forall>tt\<in>\<Union>S. \<langle>fst(qq),tt\<rangle>\<in>U" by force
      with t(1,3) have "q\<in>U" by auto
    }
    then have U2:"{fst(qq). qq\<in>U}\<times>\<Union>S\<subseteq>U" by blast
    {
      assume "U\<noteq>0"
      then obtain u where u:"u\<in>U" by auto
      {
        fix aa assume "aa\<in>\<Union>T\<times>\<Union>S"
        then obtain t s where "t\<in>\<Union>T""s\<in>\<Union>S""aa=\<langle>t,s\<rangle>" by auto
        with u have "\<langle>t,snd(u)\<rangle>\<in>\<Union>T\<times>{snd(qq). qq\<in>U}" by auto
        with U1 have "\<langle>t,snd(u)\<rangle>\<in>U" by auto
        moreover have "t=fst(\<langle>t,snd(u)\<rangle>)" by auto moreover note \<open>s\<in>\<Union>S\<close> ultimately
        have "\<langle>t,s\<rangle>\<in>{fst(qq). qq\<in>U}\<times>\<Union>S" by blast
        with U2 have "\<langle>t,s\<rangle>\<in>U" by auto
        with \<open>aa=\<langle>t,s\<rangle>\<close> have "aa\<in>U" by auto
      }
      then have "\<Union>T\<times>\<Union>S\<subseteq>U" by auto moreover
      with U(1) have "U\<subseteq>\<Union>ProductTopology(T,S)" by auto ultimately
      have "\<Union>T\<times>\<Union>S=U" using Top_1_4_T1(3) assms(1,2) by auto
    }
    then have "(U=0)\<or>(U=\<Union>T\<times>\<Union>S)" by auto
  }
  then show ?thesis unfolding IsConnected_def using Top_1_4_T1(3) assms(1,2) by auto
qed

end
