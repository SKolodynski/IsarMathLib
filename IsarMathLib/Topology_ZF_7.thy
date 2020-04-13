(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2012 Daniel de la Concepcion

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

section \<open>Topology 7\<close>

theory Topology_ZF_7 imports Topology_ZF_5
begin

subsection\<open>Connection Properties\<close>

text\<open>Another type of topological properties are the connection properties.
These properties establish if the space is formed of several pieces or just one.\<close>

text\<open>A space is connected iff there is no clopen set other that the empty set
and the total set.\<close>

definition IsConnected ("_{is connected}" 70)
  where "T {is connected} \<equiv> \<forall>U. (U\<in>T \<and> (U {is closed in}T)) \<longrightarrow> U=0\<or>U=\<Union>T"

lemma indiscrete_connected:
  shows "{0,X} {is connected}"
  unfolding IsConnected_def IsClosed_def by auto

text\<open>The anti-property of connectedness is called total-diconnectedness.\<close>

definition IsTotDis ("_ {is totally-disconnected}" 70)
  where "IsTotDis \<equiv> ANTI(IsConnected)"

lemma conn_spectrum:
  shows "(A{is in the spectrum of}IsConnected) \<longleftrightarrow> A\<lesssim>1"
proof
  assume "A{is in the spectrum of}IsConnected"
  then have "\<forall>T. (T{is a topology}\<and>\<Union>T\<approx>A) \<longrightarrow> (T{is connected})" using Spec_def by auto
  moreover
  have "Pow(A){is a topology}" using Pow_is_top by auto
  moreover
  have "\<Union>(Pow(A))=A" by auto
  then have "\<Union>(Pow(A))\<approx>A" by auto
  ultimately have "Pow(A) {is connected}" by auto
  {
    assume "A\<noteq>0"
    then obtain E where "E\<in>A" by blast
    then have "{E}\<in>Pow(A)" by auto
    moreover
    have "A-{E}\<in>Pow(A)" by auto
    ultimately have "{E}\<in>Pow(A)\<and>{E}{is closed in}Pow(A)" unfolding IsClosed_def by auto
    with \<open>Pow(A) {is connected}\<close> have "{E}=A" unfolding IsConnected_def by auto
    then have "A\<approx>1" using singleton_eqpoll_1 by auto
    then have "A\<lesssim>1" using eqpoll_imp_lepoll by auto
  }
  moreover
  {
    assume "A=0"
    then have "A\<lesssim>1" using empty_lepollI[of "1"] by auto
  }
  ultimately show "A\<lesssim>1" by auto
next
  assume "A\<lesssim>1"
  {
    fix T
    assume "T{is a topology}""\<Union>T\<approx>A"
    {
      assume "\<Union>T=0"
      with \<open>T{is a topology}\<close> have "T={0}" using empty_open by auto
      then have "T{is connected}" unfolding IsConnected_def by auto
    }
    moreover
    {
      assume "\<Union>T\<noteq>0"
      moreover
      from \<open>A\<lesssim>1\<close>\<open>\<Union>T\<approx>A\<close> have "\<Union>T\<lesssim>1" using eq_lepoll_trans by auto
      ultimately
      obtain E where "\<Union>T={E}" using lepoll_1_is_sing by blast
      moreover
      have "T\<subseteq>Pow(\<Union>T)" by auto
      ultimately have "T\<subseteq>Pow({E})" by auto
      then have "T\<subseteq>{0,{E}}" by blast
      with \<open>T{is a topology}\<close> have "{0}\<subseteq>T" "T\<subseteq>{0,{E}}" using empty_open by auto
      then have "T{is connected}" unfolding IsConnected_def by auto
    }
    ultimately have "T{is connected}" by auto
  }
  then show "A{is in the spectrum of}IsConnected" unfolding Spec_def by auto
qed

text\<open>The discrete space is a first example of totally-disconnected space.\<close>

lemma discrete_tot_dis:
  shows "Pow(X) {is totally-disconnected}"
proof-
  {
    fix A assume "A\<in>Pow(X)" and con:"(Pow(X){restricted to}A){is connected}"
    have res:"(Pow(X){restricted to}A)=Pow(A)" unfolding RestrictedTo_def using \<open>A\<in>Pow(X)\<close>
      by blast
    {
      assume "A=0"
      then have "A\<lesssim>1" using empty_lepollI[of "1"] by auto
      then have "A{is in the spectrum of}IsConnected" using conn_spectrum by auto
    }
    moreover
    {
      assume "A\<noteq>0"
      then obtain E where "E\<in>A" by blast
      then have "{E}\<in>Pow(A)" by auto
      moreover
      have "A-{E}\<in>Pow(A)" by auto
      ultimately have "{E}\<in>Pow(A)\<and>{E}{is closed in}Pow(A)" unfolding IsClosed_def by auto
      with con res have "{E}=A" unfolding IsConnected_def by auto
      then have "A\<approx>1" using singleton_eqpoll_1 by auto
      then have "A\<lesssim>1" using eqpoll_imp_lepoll by auto
      then have "A{is in the spectrum of}IsConnected" using conn_spectrum by auto
    }
    ultimately have "A{is in the spectrum of}IsConnected" by auto
  }
  then show ?thesis unfolding IsTotDis_def antiProperty_def by auto
qed

text\<open>An space is hyperconnected iff every two non-empty open sets meet.\<close>

definition IsHConnected ("_{is hyperconnected}"90)
  where "T{is hyperconnected} \<equiv>\<forall>U V. U\<in>T \<and> V\<in>T \<and> U\<inter>V=0 \<longrightarrow> U=0\<or>V=0"

text\<open>Every hyperconnected space is connected.\<close>
  
lemma HConn_imp_Conn:
  assumes "T{is hyperconnected}"
  shows "T{is connected}"
proof-
  {
    fix U
    assume "U\<in>T""U {is closed in}T"
    then have "\<Union>T-U\<in>T""U\<in>T" using IsClosed_def by auto
    moreover
    have "(\<Union>T-U)\<inter>U=0" by auto
    moreover
    note assms
    ultimately
    have "U=0\<or>(\<Union>T-U)=0" using IsHConnected_def by auto
    with \<open>U\<in>T\<close> have "U=0\<or>U=\<Union>T" by auto
  }
  then show ?thesis using IsConnected_def by auto
qed

lemma Indiscrete_HConn:
  shows "{0,X}{is hyperconnected}"
  unfolding IsHConnected_def by auto

text\<open>A first example of an hyperconnected space but not indiscrete, is the cofinite topology on 
the natural numbers.\<close>

lemma Cofinite_nat_HConn:
  assumes "\<not>(X\<prec>nat)"
  shows "(CoFinite X){is hyperconnected}"
proof-
  {
    fix U V
    assume "U\<in>(CoFinite X)""V\<in>(CoFinite X)""U\<inter>V=0"
    then have eq:"(X-U)\<prec>nat\<or>U=0""(X-V)\<prec>nat\<or>V=0" unfolding Cofinite_def
      CoCardinal_def by auto
    from \<open>U\<inter>V=0\<close> have un:"(X-U)\<union>(X-V)=X" by auto
    {
      assume AS:"(X-U)\<prec>nat""(X-V)\<prec>nat"
      from un have "X\<prec>nat" using less_less_imp_un_less[OF AS InfCard_nat] by auto
      then have "False" using assms by auto
    }
    with eq(1,2) have "U=0\<or>V=0" by auto
  }
  then show "(CoFinite X){is hyperconnected}" using IsHConnected_def by auto
qed

lemma HConn_spectrum:
  shows "(A{is in the spectrum of}IsHConnected) \<longleftrightarrow> A\<lesssim>1"
proof
  assume "A{is in the spectrum of}IsHConnected"
  then have "\<forall>T. (T{is a topology}\<and>\<Union>T\<approx>A) \<longrightarrow> (T{is hyperconnected})" using Spec_def by auto
  moreover
  have "Pow(A){is a topology}" using Pow_is_top by auto
  moreover
  have "\<Union>(Pow(A))=A" by auto
  then have "\<Union>(Pow(A))\<approx>A" by auto
  ultimately
  have HC_Pow:"Pow(A){is hyperconnected}" by auto
  {
    assume "A=0"
    then have "A\<lesssim>1" using empty_lepollI by auto
  }
  moreover
  {
    assume "A\<noteq>0"
    then obtain e where "e\<in>A" by blast
    then have "{e}\<in>Pow(A)" by auto
    moreover
    have "A-{e}\<in>Pow(A)" by auto
    moreover
    have "{e}\<inter>(A-{e})=0" by auto
    moreover
    note HC_Pow
    ultimately have "A-{e}=0" unfolding IsHConnected_def by blast
    with \<open>e\<in>A\<close> have "A={e}" by auto
    then have "A\<approx>1" using singleton_eqpoll_1 by auto
    then have "A\<lesssim>1" using eqpoll_imp_lepoll by auto
  }
  ultimately show "A\<lesssim>1" by auto
next
  assume "A\<lesssim>1"
  {
    fix T
    assume "T{is a topology}""\<Union>T\<approx>A"
    {
      assume "\<Union>T=0"
      with \<open>T{is a topology}\<close> have "T={0}" using empty_open by auto
      then have "T{is hyperconnected}" unfolding IsHConnected_def by auto
    }
    moreover
    {
      assume "\<Union>T\<noteq>0"
      moreover
      from \<open>A\<lesssim>1\<close>\<open>\<Union>T\<approx>A\<close> have "\<Union>T\<lesssim>1" using eq_lepoll_trans by auto
      ultimately
      obtain E where "\<Union>T={E}" using lepoll_1_is_sing by blast
      moreover
      have "T\<subseteq>Pow(\<Union>T)" by auto
      ultimately have "T\<subseteq>Pow({E})" by auto
      then have "T\<subseteq>{0,{E}}" by blast
      with \<open>T{is a topology}\<close> have "{0}\<subseteq>T" "T\<subseteq>{0,{E}}" using empty_open by auto
      then have "T{is hyperconnected}" unfolding IsHConnected_def by auto
    }
    ultimately have "T{is hyperconnected}" by auto
  }
  then show "A{is in the spectrum of}IsHConnected" unfolding Spec_def by auto
qed

text\<open>In the following results we will show that anti-hyperconnectedness is a separation
property between $T_1$ and $T_2$. We will show also that both implications are proper.\<close>

text\<open>First, the closure of a point in every topological space is always hyperconnected.
This is the reason why every anti-hyperconnected space must be $T_1$: every singleton
must be closed.\<close>

lemma (in topology0)cl_point_imp_HConn:
  assumes "x\<in>\<Union>T"
  shows "(T{restricted to}Closure({x},T)){is hyperconnected}"
proof-
  from assms have sub:"Closure({x},T)\<subseteq>\<Union>T" using Top_3_L11 by auto
  then have tot:"\<Union>(T{restricted to}Closure({x},T))=Closure({x},T)" unfolding RestrictedTo_def by auto
  {
    fix A B
    assume AS:"A\<in>(T{restricted to}Closure({x},T))""B\<in>(T{restricted to}Closure({x},T))""A\<inter>B=0"
    then have "B\<subseteq>\<Union>((T{restricted to}Closure({x},T)))""A\<subseteq>\<Union>((T{restricted to}Closure({x},T)))"
      by auto
    with tot have "B\<subseteq>Closure({x},T)""A\<subseteq>Closure({x},T)" by auto
    from AS(1,2) obtain UA UB where UAUB:"UA\<in>T""UB\<in>T""A=UA\<inter>Closure({x},T)""B=UB\<inter>Closure({x},T)"
      unfolding RestrictedTo_def by auto
    then have "Closure({x},T)-A=Closure({x},T)-(UA\<inter>Closure({x},T))" "Closure({x},T)-B=Closure({x},T)-(UB\<inter>Closure({x},T))"
      by auto
    then have "Closure({x},T)-A=Closure({x},T)-(UA)" "Closure({x},T)-B=Closure({x},T)-(UB)"
      by auto
    with sub have "Closure({x},T)-A=Closure({x},T)\<inter>(\<Union>T-UA)" "Closure({x},T)-B=Closure({x},T)\<inter>(\<Union>T-UB)" by auto
    moreover
    from UAUB have "(\<Union>T-UA){is closed in}T""(\<Union>T-UB){is closed in}T" using Top_3_L9 by auto
    moreover
    have "Closure({x},T){is closed in}T" using cl_is_closed assms by auto
    ultimately have "(Closure({x},T)-A){is closed in}T""(Closure({x},T)-B){is closed in}T"
      using Top_3_L5(1) by auto
    moreover
    {
      have "x\<in>Closure({x},T)" using cl_contains_set assms by auto
      moreover
      from AS(3) have "x\<notin>A\<or>x\<notin>B" by auto
      ultimately have "x\<in>(Closure({x},T)-A)\<or>x\<in>(Closure({x},T)-B)" by auto
    }
    ultimately have "Closure({x},T)\<subseteq>(Closure({x},T)-A) \<or> Closure({x},T)\<subseteq>(Closure({x},T)-B)"
      using Top_3_L13 by auto
    then have "A\<inter>Closure({x},T)=0 \<or> B\<inter>Closure({x},T)=0" by auto
    with \<open>B\<subseteq>Closure({x},T)\<close>\<open>A\<subseteq>Closure({x},T)\<close> have "A=0\<or>B=0" using cl_contains_set assms by blast
  }
  then show ?thesis unfolding IsHConnected_def by auto
qed

text\<open>A consequence is that every totally-disconnected space is $T_1$.\<close>

lemma (in topology0) tot_dis_imp_T1:
  assumes "T{is totally-disconnected}"
  shows "T{is T\<^sub>1}"
proof-
  {
    fix x y
    assume "y\<in>\<Union>T""x\<in>\<Union>T""y\<noteq>x"
    then have "(T{restricted to}Closure({x},T)){is hyperconnected}" using cl_point_imp_HConn by auto
    then have "(T{restricted to}Closure({x},T)){is connected}" using HConn_imp_Conn by auto
    moreover
    from \<open>x\<in>\<Union>T\<close> have "Closure({x},T)\<subseteq>\<Union>T" using Top_3_L11(1) by auto
    moreover
    note assms 
    ultimately have "Closure({x},T){is in the spectrum of}IsConnected" unfolding IsTotDis_def antiProperty_def
      by auto
    then have "Closure({x},T)\<lesssim>1" using conn_spectrum by auto
    moreover
    from \<open>x\<in>\<Union>T\<close> have "x\<in>Closure({x},T)" using cl_contains_set by auto
    ultimately have "Closure({x},T)={x}" using lepoll_1_is_sing[of "Closure({x},T)" "x"] by auto
    then have "{x}{is closed in}T" using Top_3_L8 \<open>x\<in>\<Union>T\<close> by auto
    then have "\<Union>T-{x}\<in>T" unfolding IsClosed_def by auto
    moreover
    from \<open>y\<in>\<Union>T\<close>\<open>y\<noteq>x\<close> have "y\<in>\<Union>T-{x}\<and>x\<notin>\<Union>T-{x}" by auto
    ultimately have "\<exists>U\<in>T. y\<in>U\<and>x\<notin>U" by force
  }
  then show ?thesis unfolding isT1_def by auto
qed

text\<open>In the literature, there exists a class of spaces called sober spaces; where the only non-empty closed
hyperconnected subspaces are the closures of points and closures of different singletons
are different.\<close>

definition IsSober ("_{is sober}"90)
  where "T{is sober} \<equiv> \<forall>A\<in>Pow(\<Union>T)-{0}. (A{is closed in}T \<and> ((T{restricted to}A){is hyperconnected})) \<longrightarrow> (\<exists>x\<in>\<Union>T. A=Closure({x},T) \<and> (\<forall>y\<in>\<Union>T. A=Closure({y},T) \<longrightarrow> y=x) )"

text\<open>Being sober is weaker than being anti-hyperconnected.\<close>

theorem (in topology0) anti_HConn_imp_sober:
  assumes "T{is anti-}IsHConnected"
  shows "T{is sober}"
proof-
  {
    fix A assume "A\<in>Pow(\<Union>T)-{0}""A{is closed in}T""(T{restricted to}A){is hyperconnected}"
    with assms have "A{is in the spectrum of}IsHConnected" unfolding antiProperty_def by auto
    then have "A\<lesssim>1" using HConn_spectrum by auto
    moreover
    with \<open>A\<in>Pow(\<Union>T)-{0}\<close> have "A\<noteq>0" by auto
    then obtain x where "x\<in>A" by auto
    ultimately have "A={x}" using lepoll_1_is_sing by auto
    with \<open>A{is closed in}T\<close> have "{x}{is closed in}T" by auto
    moreover from \<open>x\<in>A\<close> \<open>A\<in>Pow(\<Union>T)-{0}\<close> have "{x}\<in>Pow(\<Union>T)" by auto
    ultimately
    have "Closure({x},T)={x}" unfolding Closure_def ClosedCovers_def by auto
    with \<open>A={x}\<close> have "A=Closure({x},T)" by auto
    moreover
    {
      fix y assume "y\<in>\<Union>T""A=Closure({y},T)"
      then have "{y}\<subseteq>Closure({y},T)" using cl_contains_set by auto
      with \<open>A=Closure({y},T)\<close> have "y\<in>A" by auto
      with \<open>A={x}\<close> have "y=x" by auto
    }
    then have "\<forall>y\<in>\<Union>T. A=Closure({y},T) \<longrightarrow> y=x" by auto
    moreover note \<open>{x}\<in>Pow(\<Union>T)\<close> 
    ultimately have "\<exists>x\<in>\<Union>T. A=Closure({x},T)\<and>(\<forall>y\<in>\<Union>T. A=Closure({y},T) \<longrightarrow> y=x)" by auto
  }
  then show ?thesis using IsSober_def by auto
qed
  
text\<open>Every sober space is $T_0$.\<close>

lemma (in topology0) sober_imp_T0:
  assumes "T{is sober}"
  shows "T{is T\<^sub>0}"
proof-
  {
    fix x y
    assume AS:"x\<in>\<Union>T""y\<in>\<Union>T""x\<noteq>y""\<forall>U\<in>T. x\<in>U \<longleftrightarrow> y\<in>U"
    from \<open>x\<in>\<Union>T\<close> have clx:"Closure({x},T) {is closed in}T" using cl_is_closed by auto
    with \<open>x\<in>\<Union>T\<close> have "(\<Union>T-Closure({x},T))\<in>T" using Top_3_L11(1) unfolding IsClosed_def by auto
    moreover
    from \<open>x\<in>\<Union>T\<close> have "x\<in>Closure({x},T)" using cl_contains_set by auto
    moreover
    note AS(1,4)
    ultimately have "y\<notin>(\<Union>T-Closure({x},T))" by auto
    with AS(2) have "y\<in>Closure({x},T)" by auto
    with clx have ineq1:"Closure({y},T)\<subseteq>Closure({x},T)" using Top_3_L13 by auto
    from \<open>y\<in>\<Union>T\<close> have cly:"Closure({y},T) {is closed in}T" using cl_is_closed by auto
    with \<open>y\<in>\<Union>T\<close> have "(\<Union>T-Closure({y},T))\<in>T" using Top_3_L11(1) unfolding IsClosed_def by auto
    moreover
    from \<open>y\<in>\<Union>T\<close> have "y\<in>Closure({y},T)" using cl_contains_set by auto
    moreover
    note AS(2,4)
    ultimately have "x\<notin>(\<Union>T-Closure({y},T))" by auto
    with AS(1) have "x\<in>Closure({y},T)" by auto
    with cly have "Closure({x},T)\<subseteq>Closure({y},T)" using Top_3_L13 by auto
    with ineq1 have eq:"Closure({x},T)=Closure({y},T)" by auto
    have "Closure({x},T)\<in>Pow(\<Union>T)-{0}" using Top_3_L11(1) \<open>x\<in>\<Union>T\<close> \<open>x\<in>Closure({x},T)\<close> by auto
    moreover note assms clx
    ultimately have "\<exists>t\<in>\<Union>T.( Closure({x},T) = Closure({t}, T) \<and> (\<forall>y\<in>\<Union>T. Closure({x},T) = Closure({y}, T) \<longrightarrow> y = t))" 
      unfolding IsSober_def using cl_point_imp_HConn[OF \<open>x\<in>\<Union>T\<close>] by auto
    then obtain t where t_def:"t\<in>\<Union>T""Closure({x},T) = Closure({t}, T)""\<forall>y\<in>\<Union>T. Closure({x},T) = Closure({y}, T) \<longrightarrow> y = t"
      by blast
    with eq have "y=t" using \<open>y\<in>\<Union>T\<close> by auto
    moreover from t_def \<open>x\<in>\<Union>T\<close> have "x=t" by blast
    ultimately have "y=x" by auto
    with \<open>x\<noteq>y\<close> have "False" by auto
  }
  then have "\<forall>x y. x\<in>\<Union>T\<and>y\<in>\<Union>T\<and>x\<noteq>y \<longrightarrow> (\<exists>U\<in>T. (x\<in>U\<and>y\<notin>U)\<or>(y\<in>U\<and>x\<notin>U))" by auto
  then show ?thesis using isT0_def by auto
qed

text\<open>Every $T_2$ space is anti-hyperconnected.\<close>

theorem (in topology0) T2_imp_anti_HConn:
  assumes "T{is T\<^sub>2}"
  shows "T{is anti-}IsHConnected"
proof-
  {
    fix TT
    assume "TT{is a topology}" "TT{is hyperconnected}""TT{is T\<^sub>2}"
    {
      assume "\<Union>TT=0"
      then have "\<Union>TT\<lesssim>1" using empty_lepollI by auto
      then have "(\<Union>TT){is in the spectrum of}IsHConnected" using HConn_spectrum by auto
    }
    moreover
    {
      assume "\<Union>TT\<noteq>0"
      then obtain x where "x\<in>\<Union>TT" by blast
      {
        fix y
        assume "y\<in>\<Union>TT""x\<noteq>y"
        with \<open>TT{is T\<^sub>2}\<close>\<open>x\<in>\<Union>TT\<close> obtain U V where "U\<in>TT""V\<in>TT""x\<in>U""y\<in>V""U\<inter>V=0" unfolding isT2_def by blast
        with \<open>TT{is hyperconnected}\<close> have "False" using IsHConnected_def by auto
      }
      with \<open>x\<in>\<Union>TT\<close> have "\<Union>TT={x}" by auto
      then have "\<Union>TT\<approx>1" using singleton_eqpoll_1 by auto
      then have "\<Union>TT\<lesssim>1" using eqpoll_imp_lepoll by auto
      then have "(\<Union>TT){is in the spectrum of}IsHConnected" using HConn_spectrum by auto
    }
    ultimately have "(\<Union>TT){is in the spectrum of}IsHConnected" by blast
  }
  then have "\<forall>T. ((T{is a topology}\<and>(T{is hyperconnected})\<and>(T{is T\<^sub>2}))\<longrightarrow> ((\<Union>T){is in the spectrum of}IsHConnected))"
    by auto
  moreover
  note here_T2
  ultimately
  have "\<forall>T.  T{is a topology} \<longrightarrow> ((T{is T\<^sub>2})\<longrightarrow>(T{is anti-}IsHConnected))" using Q_P_imp_Spec[where P=IsHConnected and Q=isT2]
    by auto
  then show ?thesis using assms topSpaceAssum by auto
qed

text\<open>Every anti-hyperconnected space is $T_1$.\<close>

theorem anti_HConn_imp_T1:
  assumes "T{is anti-}IsHConnected"
  shows "T{is T\<^sub>1}"
proof-
  {
    fix x y
    assume "x\<in>\<Union>T""y\<in>\<Union>T""x\<noteq>y"
    {
      assume AS:"\<forall>U\<in>T. x\<notin>U\<or>y\<in>U"
      from \<open>x\<in>\<Union>T\<close>\<open>y\<in>\<Union>T\<close> have "{x,y}\<in>Pow(\<Union>T)" by auto
      then have sub:"(T{restricted to}{x,y})\<subseteq>Pow({x,y})" using RestrictedTo_def by auto
      {
        fix U V
        assume H:"U\<in>T{restricted to}{x,y}" "V\<in>(T{restricted to}{x,y})""U\<inter>V=0"
        with AS have "x\<in>U\<longrightarrow>y\<in>U""x\<in>V\<longrightarrow>y\<in>V" unfolding RestrictedTo_def by auto
        with H(1,2) sub have "x\<in>U\<longrightarrow>U={x,y}""x\<in>V\<longrightarrow>V={x,y}" by auto
        with H sub have "x\<in>U\<longrightarrow>(U={x,y}\<and>V=0)""x\<in>V\<longrightarrow>(V={x,y}\<and>U=0)" by auto
        then have "(x\<in>U\<or>x\<in>V)\<longrightarrow>(U=0\<or>V=0)" by auto
        moreover
        from sub H have "(x\<notin>U\<and>x\<notin>V)\<longrightarrow> (U=0\<or>V=0)" by blast
        ultimately have "U=0\<or>V=0" by auto
      }
      then have "(T{restricted to}{x,y}){is hyperconnected}" unfolding IsHConnected_def by auto
      with assms\<open>{x,y}\<in>Pow(\<Union>T)\<close> have "{x,y}{is in the spectrum of}IsHConnected" unfolding antiProperty_def
        by auto
      then have "{x,y}\<lesssim>1" using HConn_spectrum by auto
      moreover
      have "x\<in>{x,y}" by auto
      ultimately have "{x,y}={x}" using lepoll_1_is_sing[of "{x,y}""x"] by auto
      moreover
      have "y\<in>{x,y}" by auto
      ultimately have "y\<in>{x}" by auto
      then have "y=x" by auto
      with \<open>x\<noteq>y\<close> have "False" by auto
    }
    then have "\<exists>U\<in>T. x\<in>U\<and>y\<notin>U" by auto
  }
  then show ?thesis using isT1_def by auto
qed

text\<open>There is at least one topological space that is $T_1$, but not anti-hyperconnected.
This space is the cofinite topology on the natural numbers.\<close>

lemma Cofinite_not_anti_HConn:
  shows "\<not>((CoFinite nat){is anti-}IsHConnected)" and "(CoFinite nat){is T\<^sub>1}"
proof-
  {
    assume "(CoFinite nat){is anti-}IsHConnected"
    moreover
    have "\<Union>(CoFinite nat)=nat" unfolding Cofinite_def using union_cocardinal by auto
    moreover
    have "(CoFinite nat){restricted to}nat=(CoFinite nat)" using subspace_cocardinal unfolding Cofinite_def
      by auto
    moreover
    have "\<not>(nat\<prec>nat)" by auto
    then have "(CoFinite nat){is hyperconnected}" using Cofinite_nat_HConn[of "nat"] by auto
    ultimately have "nat{is in the spectrum of}IsHConnected" unfolding antiProperty_def by auto
    then have "nat\<lesssim>1" using HConn_spectrum by auto
    moreover
    have "1\<in>nat" by auto
    then have "1\<prec>nat" using n_lesspoll_nat by auto
    ultimately have "nat\<prec>nat" using lesspoll_trans1 by auto
    then have "False" by auto
  }
  then show "\<not>((CoFinite nat){is anti-}IsHConnected)" by auto
next
  show "(CoFinite nat){is T\<^sub>1}" using cocardinal_is_T1 InfCard_nat unfolding Cofinite_def by auto
qed

text\<open>The join-topology build from the cofinite topology on the natural numbers,
and the excluded set topology on the natural numbers excluding \<open>{0,1}\<close>;
is just the union of both.\<close>

lemma join_top_cofinite_excluded_set:
  shows "(joinT {CoFinite nat,ExcludedSet(nat,{0,1})})=(CoFinite nat)\<union> ExcludedSet(nat,{0,1})"
proof-
  have coftop:"(CoFinite nat){is a topology}" unfolding Cofinite_def using CoCar_is_topology InfCard_nat by auto
  moreover
  have "ExcludedSet(nat,{0,1}){is a topology}" using excludedset_is_topology by auto
  moreover
  have exuni:"\<Union>ExcludedSet(nat,{0,1})=nat" using union_excludedset by auto
  moreover
  have cofuni:"\<Union>(CoFinite nat)=nat" using union_cocardinal unfolding Cofinite_def by auto
  ultimately have "(joinT {CoFinite nat,ExcludedSet(nat,{0,1})}) = (THE T. (CoFinite nat)\<union>ExcludedSet(nat,{0,1}) {is a subbase for} T)"
    using joinT_def by auto
  moreover
  have "\<Union>(CoFinite nat)\<in>CoFinite nat" using CoCar_is_topology[OF InfCard_nat] unfolding Cofinite_def IsATopology_def
    by auto
  with cofuni have n:"nat\<in>CoFinite nat" by auto
  have Pa:"(CoFinite nat)\<union>ExcludedSet(nat,{0,1}) {is a subbase for}{\<Union>A. A\<in>Pow({\<Inter>B. B\<in>FinPow((CoFinite nat)\<union>ExcludedSet(nat,{0,1}))})}"
    using Top_subbase(2) by auto
  have "{\<Union>A. A\<in>Pow({\<Inter>B. B\<in>FinPow((CoFinite nat)\<union>ExcludedSet(nat,{0,1}))})}=(THE T. (CoFinite nat)\<union>ExcludedSet(nat,{0,1}) {is a subbase for} T)"
    using same_subbase_same_top[where B="(CoFinite nat)\<union>ExcludedSet(nat,{0,1})", OF _ Pa] the_equality[where a="{\<Union>A. A\<in>Pow({\<Inter>B. B\<in>FinPow((CoFinite nat)\<union>ExcludedSet(nat,{0,1}))})}" and P="\<lambda>T. ((CoFinite nat)\<union>ExcludedSet(nat,{0,1})){is a subbase for}T",
      OF Pa] by auto
  ultimately have equal:"(joinT {CoFinite nat,ExcludedSet(nat,{0,1})}) ={\<Union>A. A\<in>Pow({\<Inter>B. B\<in>FinPow((CoFinite nat)\<union>ExcludedSet(nat,{0,1}))})}"
    by auto
  {
    fix U assume "U\<in>{\<Union>A. A\<in>Pow({\<Inter>B. B\<in>FinPow((CoFinite nat)\<union>ExcludedSet(nat,{0,1}))})}"
    then obtain AU where "U=\<Union>AU" and base:"AU\<in>Pow({\<Inter>B. B\<in>FinPow((CoFinite nat)\<union>ExcludedSet(nat,{0,1}))})"
      by auto
    have "(CoFinite nat)\<subseteq>Pow(\<Union>(CoFinite nat))" by auto
    moreover
    have "ExcludedSet(nat,{0,1})\<subseteq>Pow(\<Union>ExcludedSet(nat,{0,1}))" by auto
    moreover
    note cofuni exuni
    ultimately have sub:"(CoFinite nat)\<union>ExcludedSet(nat,{0,1})\<subseteq>Pow(nat)" by auto
    from base have "\<forall>S\<in>AU. S\<in>{\<Inter>B. B\<in>FinPow((CoFinite nat)\<union>ExcludedSet(nat,{0,1}))}" by blast
    then have "\<forall>S\<in>AU. \<exists>B\<in>FinPow((CoFinite nat)\<union>ExcludedSet(nat,{0,1})). S=\<Inter>B" by blast
    then have eq:"\<forall>S\<in>AU. \<exists>B\<in>Pow((CoFinite nat)\<union>ExcludedSet(nat,{0,1})). S=\<Inter>B" unfolding FinPow_def by blast
    { 
      fix S assume "S\<in>AU"
      with eq obtain B where "B\<in>Pow((CoFinite nat)\<union>ExcludedSet(nat,{0,1}))""S=\<Inter>B" by auto
      with sub have "B\<in>Pow(Pow(nat))" by auto
      {
        fix x assume "x\<in>\<Inter>B"
        then have "\<forall>N\<in>B. x\<in>N""B\<noteq>0" by auto
        with \<open>B\<in>Pow(Pow(nat))\<close> have "x\<in>nat" by blast
      }
      with \<open>S=\<Inter>B\<close> have "S\<in>Pow(nat)" by auto
    }
    then have "\<forall>S\<in>AU. S\<in>Pow(nat)" by blast
    with \<open>U=\<Union>AU\<close> have "U\<in>Pow(nat)" by auto
    {
      assume "0\<in>U\<or>1\<in>U"
      with \<open>U=\<Union>AU\<close> obtain S where "S\<in>AU""0\<in>S\<or>1\<in>S" by auto
      with base obtain BS where "S=\<Inter>BS" and bsbase:"BS\<in>FinPow((CoFinite nat)\<union>ExcludedSet(nat,{0,1}))" by auto
      with \<open>0\<in>S\<or>1\<in>S\<close> have "\<forall>M\<in>BS. 0\<in>M\<or>1\<in>M" by auto
      then have "\<forall>M\<in>BS. M\<notin>ExcludedSet(nat,{0,1})-{nat}" unfolding ExcludedPoint_def ExcludedSet_def by auto
      moreover
      note bsbase n
      ultimately have "BS\<in>FinPow(CoFinite nat)" unfolding FinPow_def by auto
      moreover
      from \<open>0\<in>S\<or>1\<in>S\<close> have "S\<noteq>0" by auto
      with \<open>S=\<Inter>BS\<close> have "BS\<noteq>0" by auto
      moreover
      note coftop 
      ultimately have "\<Inter>BS\<in>CoFinite nat" using topology0.fin_inter_open_open[OF topology0_CoCardinal[OF InfCard_nat]]
        unfolding Cofinite_def by auto
      with \<open>S=\<Inter>BS\<close> have "S\<in>CoFinite nat" by auto
      with \<open>0\<in>S\<or>1\<in>S\<close> have "nat-S\<prec>nat" unfolding Cofinite_def CoCardinal_def by auto
      moreover
      from \<open>U=\<Union>AU\<close>\<open>S\<in>AU\<close> have "S\<subseteq>U" by auto
      then have "nat-U\<subseteq>nat-S" by auto
      then have "nat-U\<lesssim>nat-S" using subset_imp_lepoll by auto
      ultimately
      have "nat-U\<prec>nat" using lesspoll_trans1 by auto
      with \<open>U\<in>Pow(nat)\<close> have "U\<in>CoFinite nat" unfolding Cofinite_def CoCardinal_def by auto
      with \<open>U\<in>Pow(nat)\<close> have "U\<in> (CoFinite nat)\<union> ExcludedSet(nat,{0,1})" by auto
    }
    with \<open>U\<in>Pow(nat)\<close> have "U\<in>(CoFinite nat)\<union> ExcludedSet(nat,{0,1})" unfolding ExcludedSet_def by blast
  }
  then have "({\<Union>A . A \<in> Pow({\<Inter>B . B \<in> FinPow((CoFinite nat) \<union> ExcludedSet(nat,{0,1}))})}) \<subseteq> (CoFinite nat)\<union> ExcludedSet(nat,{0,1})"
    by blast
  moreover
  {
    fix U
    assume "U\<in>(CoFinite nat)\<union> ExcludedSet(nat,{0,1})"
    then have "{U}\<in>FinPow((CoFinite nat) \<union> ExcludedSet(nat,{0,1}))" unfolding FinPow_def by auto
    then have "{U}\<in>Pow({\<Inter>B . B \<in> FinPow((CoFinite nat) \<union> ExcludedSet(nat,{0,1}))})" by blast
    moreover
    have "U=\<Union>{U}" by auto
    ultimately have "U\<in>{\<Union>A . A \<in> Pow({\<Inter>B . B \<in> FinPow((CoFinite nat) \<union> ExcludedSet(nat,{0,1}))})}" by blast
  }
  then have "(CoFinite nat)\<union> ExcludedSet(nat,{0,1})\<subseteq>{\<Union>A . A \<in> Pow({\<Inter>B . B \<in> FinPow((CoFinite nat) \<union> ExcludedSet(nat,{0,1}))})}"
    by auto
  ultimately have "(CoFinite nat)\<union> ExcludedSet(nat,{0,1})={\<Union>A . A \<in> Pow({\<Inter>B . B \<in> FinPow((CoFinite nat) \<union> ExcludedSet(nat,{0,1}))})}"
    by auto
  with equal show ?thesis by auto
qed

text\<open>The previous topology in not $T_2$, but is anti-hyperconnected.\<close>

theorem join_Cofinite_ExclPoint_not_T2:
  shows 
    "\<not>((joinT {CoFinite nat, ExcludedSet(nat,{0,1})}){is T\<^sub>2})" and 
    "(joinT {CoFinite nat,ExcludedSet(nat,{0,1})}){is anti-} IsHConnected"
proof-
  have "(CoFinite nat) \<subseteq> (CoFinite nat) \<union> ExcludedSet(nat,{0,1})" by auto
  have "\<Union>((CoFinite nat)\<union> ExcludedSet(nat,{0,1}))=(\<Union>(CoFinite nat))\<union> (\<Union>ExcludedSet(nat,{0,1}))"
    by auto
  moreover
  have "\<dots>=nat "unfolding Cofinite_def using union_cocardinal union_excludedset by auto
  ultimately have tot:"\<Union>((CoFinite nat)\<union> ExcludedSet(nat,{0,1}))=nat" by auto
  { 
    assume "(joinT {CoFinite nat,ExcludedSet(nat,{0,1})}) {is T\<^sub>2}"
    then have t2:"((CoFinite nat)\<union> ExcludedSet(nat,{0,1})){is T\<^sub>2}" using join_top_cofinite_excluded_set
      by auto
    with tot have "\<exists>U\<in>((CoFinite nat)\<union> ExcludedSet(nat,{0,1})). \<exists>V\<in>((CoFinite nat)\<union> ExcludedSet(nat,{0,1})). 0\<in>U\<and>1\<in>V\<and>U\<inter>V=0" using isT2_def by auto
    then obtain U V where "U \<in> (CoFinite nat) \<or> (0 \<notin> U\<and>1\<notin>U)""V \<in> (CoFinite nat) \<or> (0 \<notin> V\<and>1\<notin>V)""0\<in>U""1\<in>V""U\<inter>V=0" 
      unfolding ExcludedSet_def by auto
    then have "U\<in>(CoFinite nat)""V\<in>(CoFinite nat)" by auto
    with \<open>0\<in>U\<close>\<open>1\<in>V\<close> have "U\<inter>V\<noteq>0" using Cofinite_nat_HConn IsHConnected_def by auto
    with \<open>U\<inter>V=0\<close> have "False" by auto
  }
  then show "\<not>((joinT {CoFinite nat,ExcludedSet(nat,{0,1})}){is T\<^sub>2})" by auto
  {
    fix A assume AS:"A\<in>Pow(\<Union>((CoFinite nat)\<union> ExcludedSet(nat,{0,1})))""(((CoFinite nat)\<union> ExcludedSet(nat,{0,1})){restricted to}A){is hyperconnected}"
    with tot have "A\<in>Pow(nat)" by auto
    then have sub:"A\<inter>nat=A" by auto
    have "((CoFinite nat)\<union> ExcludedSet(nat,{0,1})){restricted to}A=((CoFinite nat){restricted to}A)\<union> (ExcludedSet(nat,{0,1}){restricted to}A)"
      unfolding RestrictedTo_def by auto
    also from sub have "\<dots>=(CoFinite A)\<union>ExcludedSet(A,{0,1})" using subspace_excludedset[of"nat""{0,1}""A"] subspace_cocardinal[of "nat""nat""A"] unfolding Cofinite_def
      by auto
    finally have "((CoFinite nat)\<union> ExcludedSet(nat,{0,1})){restricted to}A=(CoFinite A)\<union>ExcludedSet(A,{0,1})" by auto
    with AS(2) have eq:"((CoFinite A)\<union>ExcludedSet(A,{0,1})){is hyperconnected}" by auto
    {
      assume "{0,1}\<inter>A=0"
      then have "(CoFinite A)\<union>ExcludedSet(A,{0,1})=Pow(A)" using empty_excludedset[of "{0,1}""A"] unfolding Cofinite_def CoCardinal_def
        by auto
      with eq have "Pow(A){is hyperconnected}" by auto
      then have "Pow(A){is connected}" using HConn_imp_Conn by auto
      moreover
      have "Pow(A){is anti-}IsConnected" using discrete_tot_dis unfolding IsTotDis_def by auto
      moreover
      have "\<Union>(Pow(A))\<in>Pow(\<Union>(Pow(A)))" by auto
      moreover
      have "Pow(A){restricted to}\<Union>(Pow(A))=Pow(A)" unfolding RestrictedTo_def by blast
      ultimately have "(\<Union>(Pow(A))){is in the spectrum of}IsConnected" unfolding antiProperty_def
        by auto
      then have "A{is in the spectrum of}IsConnected" by auto
      then have "A\<lesssim>1" using conn_spectrum  by auto
      then have "A{is in the spectrum of}IsHConnected" using HConn_spectrum by auto
    }
    moreover
    {
      assume AS:"{0,1}\<inter>A\<noteq>0"
      {
        assume "A={0}\<or>A={1}"
        then have "A\<approx>1" using singleton_eqpoll_1 by auto
        then have "A\<lesssim>1" using eqpoll_imp_lepoll by auto
        then have "A{is in the spectrum of}IsHConnected" using HConn_spectrum by auto
      }
      moreover
      {  
        assume AS2:"\<not>(A={0}\<or>A={1})"
        {
          assume AS3:"A\<subseteq>{0,1}"
          with AS AS2 have A_def:"A={0,1}" by blast
          then have "ExcludedSet(A,{0,1})=ExcludedSet(A,A)" by auto
          moreover have "ExcludedSet(A,A)={0,A}" unfolding ExcludedSet_def by blast
          ultimately have "ExcludedSet(A,{0,1})={0,A}" by auto
          moreover
          have "0\<in>(CoFinite A)" using empty_open[of "CoFinite A"]
            CoCar_is_topology[OF InfCard_nat,of "A"] unfolding Cofinite_def by auto
          moreover
          have "\<Union>(CoFinite A)=A" using union_cocardinal unfolding Cofinite_def by auto
          then have "A\<in>(CoFinite A)" using CoCar_is_topology[OF InfCard_nat,of "A"] unfolding Cofinite_def
            IsATopology_def by auto
          ultimately have "(CoFinite A)\<union>ExcludedSet(A,{0,1})=(CoFinite A)" by auto
          with eq have"(CoFinite A){is hyperconnected}" by auto
          with A_def have  hyp:"(CoFinite {0,1}){is hyperconnected}" by auto
          have "{0}\<approx>1""{1}\<approx>1" using singleton_eqpoll_1 by auto
          moreover
          have "1\<prec>nat" using n_lesspoll_nat by auto
          ultimately have "{0}\<prec>nat""{1}\<prec>nat" using eq_lesspoll_trans by auto
          moreover
          have "{0,1}-{1}={0}""{0,1}-{0}={1}" by auto
          ultimately have "{1}\<in>(CoFinite {0,1})""{0}\<in>(CoFinite {0,1})" "{1}\<inter>{0}=0" unfolding Cofinite_def CoCardinal_def
            by auto
          with hyp have "False" unfolding IsHConnected_def by auto
        }
        then obtain t where "t\<in>A" "t\<noteq>0" "t\<noteq>1" by auto
        then have "{t}\<in>ExcludedSet(A,{0,1})" unfolding ExcludedSet_def by auto
        moreover
        {
          have "{t}\<approx>1" using singleton_eqpoll_1 by auto
          moreover
          have "1\<prec>nat" using n_lesspoll_nat by auto
          ultimately have "{t}\<prec>nat" using eq_lesspoll_trans by auto
          moreover
          with \<open>t\<in>A\<close> have "A-(A-{t})={t}" by auto
          ultimately have "A-{t}\<in>(CoFinite A)" unfolding Cofinite_def CoCardinal_def
            by auto
        }
        ultimately have "{t}\<in>((CoFinite A)\<union>ExcludedSet(A,{0,1}))""A-{t}\<in>((CoFinite A)\<union>ExcludedSet(A,{0,1}))"
          "{t}\<inter>(A-{t})=0" by auto
        with eq have "A-{t}=0" unfolding IsHConnected_def by auto
        with \<open>t\<in>A\<close> have "A={t}" by auto
        then have "A\<approx>1" using singleton_eqpoll_1 by auto
        then have "A\<lesssim>1" using eqpoll_imp_lepoll by auto
        then have "A{is in the spectrum of}IsHConnected" using HConn_spectrum by auto
      }
      ultimately have "A{is in the spectrum of}IsHConnected" by auto
    }
    ultimately have "A{is in the spectrum of}IsHConnected" by auto
  }
  then have "((CoFinite nat)\<union>ExcludedSet(nat,{0,1})){is anti-}IsHConnected" unfolding antiProperty_def
    by auto
  then show "(joinT {CoFinite nat, ExcludedSet(nat,{0,1})}){is anti-}IsHConnected" using join_top_cofinite_excluded_set
    by auto
qed

text\<open>Let's show that anti-hyperconnected is in fact $T_1$ and sober. The trick of the proof lies
in the fact that if a subset is hyperconnected, its closure is so too (the closure of a point
is then always hyperconnected because singletons are in the spectrum); since the closure
is closed, we can apply the sober property on it.\<close>

theorem (in topology0) T1_sober_imp_anti_HConn:
  assumes "T{is T\<^sub>1}" and "T{is sober}"
  shows "T{is anti-}IsHConnected"
proof-
  {
    fix A assume AS:"A\<in>Pow(\<Union>T)""(T{restricted to}A){is hyperconnected}"
    {
      assume "A=0"
      then have "A\<lesssim>1" using empty_lepollI by auto
      then have "A{is in the spectrum of}IsHConnected" using HConn_spectrum by auto
    }
    moreover
    {
      assume "A\<noteq>0"
      then obtain x where "x\<in>A" by blast
      {
        assume "\<not>((T{restricted to}Closure(A,T)){is hyperconnected})"
        then obtain U V where UV_def:"U\<in>(T{restricted to}Closure(A,T))""V\<in>(T{restricted to}Closure(A,T))"
          "U\<inter>V=0""U\<noteq>0""V\<noteq>0" using IsHConnected_def by auto
        then obtain UCA VCA where "UCA\<in>T""VCA\<in>T""U=UCA\<inter>Closure(A,T)""V=VCA\<inter>Closure(A,T)"
          unfolding RestrictedTo_def by auto
        from \<open>A\<in>Pow(\<Union>T)\<close> have "A\<subseteq>Closure(A,T)" using cl_contains_set by auto
        then have "UCA\<inter>A\<subseteq>UCA\<inter>Closure(A,T)""VCA\<inter>A\<subseteq>VCA\<inter>Closure(A,T)" by auto
        with \<open>U=UCA\<inter>Closure(A,T)\<close>\<open>V=VCA\<inter>Closure(A,T)\<close>\<open>U\<inter>V=0\<close> have "(UCA\<inter>A)\<inter>(VCA\<inter>A)=0" by auto
        moreover
        from \<open>UCA\<in>T\<close>\<open>VCA\<in>T\<close> have "UCA\<inter>A\<in>(T{restricted to}A)""VCA\<inter>A\<in>(T{restricted to}A)"
          unfolding RestrictedTo_def by auto
        moreover
        note AS(2)
        ultimately have "UCA\<inter>A=0\<or>VCA\<inter>A=0" using IsHConnected_def by auto
        with \<open>A\<subseteq>Closure(A,T)\<close> have "A\<subseteq>Closure(A,T)-UCA\<or>A\<subseteq>Closure(A,T)-VCA" by auto
        moreover
        {
          have "Closure(A,T)-UCA=Closure(A,T)\<inter>(\<Union>T-UCA)""Closure(A,T)-VCA=Closure(A,T)\<inter>(\<Union>T-VCA)"
            using Top_3_L11(1) AS(1) by auto
          moreover 
          with \<open>UCA\<in>T\<close>\<open>VCA\<in>T\<close> have "(\<Union>T-UCA){is closed in}T""(\<Union>T-VCA){is closed in}T""Closure(A,T){is closed in}T"
            using Top_3_L9 cl_is_closed AS(1) by auto
          ultimately have "(Closure(A,T)-UCA){is closed in}T""(Closure(A,T)-VCA){is closed in}T"
            using Top_3_L5(1) by auto
        }
        ultimately
        have "Closure(A,T)\<subseteq>Closure(A,T)-UCA\<or>Closure(A,T)\<subseteq>Closure(A,T)-VCA" using Top_3_L13
          by auto
        then have "UCA\<inter>Closure(A,T)=0\<or>VCA\<inter>Closure(A,T)=0" by auto
        with \<open>U=UCA\<inter>Closure(A,T)\<close>\<open>V=VCA\<inter>Closure(A,T)\<close> have "U=0\<or>V=0" by auto
        with \<open>U\<noteq>0\<close>\<open>V\<noteq>0\<close> have "False" by auto
      }
      then have "(T{restricted to}Closure(A,T)){is hyperconnected}" by auto
      moreover
      have "Closure(A,T){is closed in}T" using cl_is_closed AS(1) by auto
      moreover
      from \<open>x\<in>A\<close> have "Closure(A,T)\<noteq>0" using cl_contains_set AS(1) by auto
      moreover
      from AS(1) have "Closure(A,T)\<subseteq>\<Union>T" using Top_3_L11(1) by auto
      ultimately have "Closure(A,T)\<in>Pow(\<Union>T)-{0}""(T {restricted to} Closure(A, T)){is hyperconnected}" "Closure(A, T) {is closed in} T"
        by auto
      moreover note assms(2) 
      ultimately have "\<exists>x\<in>\<Union>T. (Closure(A,T)=Closure({x},T)\<and> (\<forall>y\<in>\<Union>T. Closure(A,T) = Closure({y}, T) \<longrightarrow> y = x))" unfolding IsSober_def
        by auto
      then obtain y where "y\<in>\<Union>T""Closure(A,T)=Closure({y},T)" by auto
      moreover
      {
        fix z assume "z\<in>(\<Union>T)-{y}"
        with assms(1) \<open>y\<in>\<Union>T\<close> obtain U where "U\<in>T" "z\<in>U" "y\<notin>U" using isT1_def by blast
        then have "U\<in>T" "z\<in>U" "U\<subseteq>(\<Union>T)-{y}" by auto
        then have "\<exists>U\<in>T. z\<in>U \<and> U\<subseteq>(\<Union>T)-{y}" by auto
      }
      then have "\<forall>z\<in>(\<Union>T)-{y}. \<exists>U\<in>T. z\<in>U \<and> U\<subseteq>(\<Union>T)-{y}" by auto
      then have "\<Union>T-{y}\<in>T" using open_neigh_open by auto
      with \<open>y\<in>\<Union>T\<close> have "{y} {is closed in}T" using IsClosed_def by auto
      with \<open>y\<in>\<Union>T\<close> have "Closure({y},T)={y}" using Top_3_L8 by auto
      with \<open>Closure(A,T)=Closure({y},T)\<close> have "Closure(A,T)={y}" by auto
      with AS(1) have "A\<subseteq>{y}" using cl_contains_set[of "A"] by auto
      with \<open>A\<noteq>0\<close> have "A={y}" by auto
      then have "A\<approx>1" using singleton_eqpoll_1 by auto
      then have "A\<lesssim>1" using eqpoll_imp_lepoll by auto
      then have "A{is in the spectrum of}IsHConnected" using HConn_spectrum by auto
    }
    ultimately have "A{is in the spectrum of}IsHConnected" by blast
  }
  then show ?thesis using antiProperty_def by auto
qed

theorem (in topology0) anti_HConn_iff_T1_sober:
  shows "(T{is anti-}IsHConnected) \<longleftrightarrow> (T{is sober}\<and>T{is T\<^sub>1})"
  using T1_sober_imp_anti_HConn anti_HConn_imp_T1 anti_HConn_imp_sober by auto


text\<open>A space is ultraconnected iff every two non-empty closed sets meet.\<close>

definition IsUConnected ("_{is ultraconnected}"80)
  where "T{is ultraconnected}\<equiv> \<forall>A B. A{is closed in}T\<and>B{is closed in}T\<and>A\<inter>B=0 \<longrightarrow> A=0\<or>B=0"

text\<open>Every ultraconnected space is trivially normal.\<close>

lemma (in topology0)UConn_imp_normal:
  assumes "T{is ultraconnected}"
  shows "T{is normal}"
proof-
  {
    fix A B
    assume AS:"A{is closed in}T" "B{is closed in}T""A\<inter>B=0"
    with assms have "A=0\<or>B=0" using IsUConnected_def by auto
    with AS(1,2) have "(A\<subseteq>0\<and>B\<subseteq>\<Union>T)\<or>(A\<subseteq>\<Union>T\<and>B\<subseteq>0)" unfolding IsClosed_def by auto
    moreover
    have "0\<in>T" using empty_open topSpaceAssum by auto
    moreover
    have "\<Union>T\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
    ultimately have "\<exists>U\<in>T. \<exists>V\<in>T. A\<subseteq>U\<and>B\<subseteq>V\<and>U\<inter>V=0" by auto
  }
  then show ?thesis unfolding IsNormal_def by auto
qed

text\<open>Every ultraconnected space is connected.\<close>

lemma UConn_imp_Conn:
  assumes "T{is ultraconnected}"
  shows "T{is connected}"
proof-
  {
    fix U V
    assume "U\<in>T""U{is closed in}T"
    then have "\<Union>T-(\<Union>T-U)=U" by auto
    with \<open>U\<in>T\<close> have "(\<Union>T-U){is closed in}T" unfolding IsClosed_def by auto
    with \<open>U{is closed in}T\<close> assms have "U=0\<or>\<Union>T-U=0" unfolding IsUConnected_def by auto
    with \<open>U\<in>T\<close> have "U=0\<or>U=\<Union>T" by auto
  }
  then show ?thesis unfolding IsConnected_def by auto
qed

lemma UConn_spectrum:
  shows "(A{is in the spectrum of}IsUConnected) \<longleftrightarrow> A\<lesssim>1"
proof
  assume A_spec:"(A{is in the spectrum of}IsUConnected)"
  {
    assume "A=0"
    then have "A\<lesssim>1" using empty_lepollI by auto
  }
  moreover
  {
    assume "A\<noteq>0"
    from A_spec have "\<forall>T. (T{is a topology}\<and>\<Union>T\<approx>A) \<longrightarrow> (T{is ultraconnected})" unfolding Spec_def by auto
    moreover
    have "Pow(A){is a topology}" using Pow_is_top by auto
    moreover
    have "\<Union>Pow(A)=A" by auto
    then have "\<Union>Pow(A)\<approx>A" by auto
    ultimately have ult:"Pow(A){is ultraconnected}" by auto
    moreover
    from \<open>A\<noteq>0\<close> obtain b where "b\<in>A" by auto
    then have "{b}{is closed in}Pow(A)" unfolding IsClosed_def by auto
    {
      fix c
      assume "c\<in>A""c\<noteq>b"
      then have "{c}{is closed in}Pow(A)""{c}\<inter>{b}=0" unfolding IsClosed_def by auto
      with ult \<open>{b}{is closed in}Pow(A)\<close> have "False" using IsUConnected_def by auto
    }
    with \<open>b\<in>A\<close> have "A={b}" by auto
    then have "A\<approx>1" using singleton_eqpoll_1 by auto
    then have "A\<lesssim>1" using eqpoll_imp_lepoll by auto
  }
  ultimately show "A\<lesssim>1" by auto
next
  assume "A\<lesssim>1"
  {
    fix T
    assume "T{is a topology}""\<Union>T\<approx>A"
    {
      assume "\<Union>T=0"
      with \<open>T{is a topology}\<close> have "T={0}" using empty_open by auto
      then have "T{is ultraconnected}" unfolding IsUConnected_def IsClosed_def by auto
    }
    moreover
    {
      assume "\<Union>T\<noteq>0"
      moreover
      from \<open>A\<lesssim>1\<close>\<open>\<Union>T\<approx>A\<close> have "\<Union>T\<lesssim>1" using eq_lepoll_trans by auto
      ultimately
      obtain E where eq:"\<Union>T={E}" using lepoll_1_is_sing by blast
      moreover
      have "T\<subseteq>Pow(\<Union>T)" by auto
      ultimately have "T\<subseteq>Pow({E})" by auto
      then have "T\<subseteq>{0,{E}}" by blast
      with \<open>T{is a topology}\<close> have "{0}\<subseteq>T" "T\<subseteq>{0,{E}}" using empty_open by auto
      then have "T{is ultraconnected}" unfolding IsUConnected_def IsClosed_def by (simp only: eq, safe, force)
    }
    ultimately have "T{is ultraconnected}" by auto
  }
  then show "A{is in the spectrum of}IsUConnected" unfolding Spec_def by auto
qed

text\<open>This time, anti-ultraconnected is an old property.\<close>

theorem (in topology0) anti_UConn:
  shows "(T{is anti-}IsUConnected) \<longleftrightarrow> T{is T\<^sub>1}"
proof
  assume "T{is T\<^sub>1}"
  {
    fix TT
    {
      assume "TT{is a topology}""TT{is T\<^sub>1}""TT{is ultraconnected}"
      {
        assume "\<Union>TT=0"
        then have "\<Union>TT\<lesssim>1" using empty_lepollI by auto
        then have "((\<Union>TT){is in the spectrum of}IsUConnected)" using UConn_spectrum by auto
      }
      moreover
      {
        assume "\<Union>TT\<noteq>0"
        then obtain t where "t\<in>\<Union>TT" by blast
        {
          fix x
          assume p:"x\<in>\<Union>TT"
          {
            fix y assume "y\<in>(\<Union>TT)-{x}"
            with \<open>TT{is T\<^sub>1}\<close> p obtain U where "U\<in>TT" "y\<in>U" "x\<notin>U" using isT1_def by blast
            then have "U\<in>TT" "y\<in>U" "U\<subseteq>(\<Union>TT)-{x}" by auto
            then have "\<exists>U\<in>TT. y\<in>U \<and> U\<subseteq>(\<Union>TT)-{x}" by auto
          }
          then have "\<forall>y\<in>(\<Union>TT)-{x}. \<exists>U\<in>TT. y\<in>U \<and> U\<subseteq>(\<Union>TT)-{x}" by auto
          with \<open>TT{is a topology}\<close> have "\<Union>TT-{x}\<in>TT" using topology0.open_neigh_open unfolding topology0_def by auto
          with p have "{x} {is closed in}TT" using IsClosed_def by auto
        }
        then have reg:"\<forall>x\<in>\<Union>TT. {x}{is closed in}TT" by auto
        with \<open>t\<in>\<Union>TT\<close> have t_cl:"{t}{is closed in}TT" by auto
        {
          fix y
          assume "y\<in>\<Union>TT"
          with reg have "{y}{is closed in}TT" by auto
          with \<open>TT{is ultraconnected}\<close> t_cl have "y=t" unfolding IsUConnected_def by auto
        }
        with \<open>t\<in>\<Union>TT\<close> have "\<Union>TT={t}" by blast
        then have "\<Union>TT\<approx>1" using singleton_eqpoll_1 by auto
        then have "\<Union>TT\<lesssim>1" using eqpoll_imp_lepoll by auto
        then have "(\<Union>TT){is in the spectrum of}IsUConnected" using UConn_spectrum by auto
      }
      ultimately have "(\<Union>TT){is in the spectrum of}IsUConnected" by blast
    }
    then have "(TT{is a topology}\<and>TT{is T\<^sub>1}\<and>(TT{is ultraconnected}))\<longrightarrow> ((\<Union>TT){is in the spectrum of}IsUConnected)"
      by auto
  }
  then have "\<forall>TT. (TT{is a topology}\<and>TT{is T\<^sub>1}\<and>(TT{is ultraconnected}))\<longrightarrow> ((\<Union>TT){is in the spectrum of}IsUConnected)"
    by auto
  moreover
  note here_T1
  ultimately have "\<forall>T. T{is a topology} \<longrightarrow> ((T{is T\<^sub>1})\<longrightarrow>(T{is anti-}IsUConnected))" using Q_P_imp_Spec[where Q=isT1 and P=IsUConnected]
    by auto
  with topSpaceAssum have "(T{is T\<^sub>1})\<longrightarrow>(T{is anti-}IsUConnected)" by auto
  with \<open>T{is T\<^sub>1}\<close> show "T{is anti-}IsUConnected" by auto
next
  assume ASS:"T{is anti-}IsUConnected"
  {
    fix x y
    assume "x\<in>\<Union>T""y\<in>\<Union>T""x\<noteq>y"
    then have tot:"\<Union>(T{restricted to}{x,y})={x,y}" unfolding RestrictedTo_def by auto
    {
      assume AS:"\<forall>U\<in>T. x\<in>U\<longrightarrow>y\<in>U"
      {
        assume "{y}{is closed in}(T{restricted to}{x,y})"
        moreover
        from \<open>x\<noteq>y\<close> have "{x,y}-{y}={x}" by auto
        ultimately have "{x}\<in>(T{restricted to}{x,y})" unfolding IsClosed_def by (simp only:tot)
        then obtain U where "U\<in>T""{x}={x,y}\<inter>U" unfolding RestrictedTo_def by auto
        moreover
        with \<open>x\<noteq>y\<close> have "y\<notin>{x}" "y\<in>{x,y}" by (blast+)
        with \<open>{x}={x,y}\<inter>U\<close> have "y\<notin>U" by auto
        moreover have "x\<in>{x}" by auto
        with \<open>{x}={x,y}\<inter>U\<close> have "x\<in>U" by auto
        ultimately have "x\<in>U""y\<notin>U""U\<in>T" by auto
        with AS have "False" by auto
      }
      then have y_no_cl:"\<not>({y}{is closed in}(T{restricted to}{x,y}))" by auto
      {
        fix A B 
        assume cl:"A{is closed in}(T{restricted to}{x,y})""B{is closed in}(T{restricted to}{x,y})""A\<inter>B=0"
        with tot have "A\<subseteq>{x,y}""B\<subseteq>{x,y}""A\<inter>B=0" unfolding IsClosed_def by auto
        then have "x\<in>A\<longrightarrow>x\<notin>B""y\<in>A\<longrightarrow>y\<notin>B""A\<subseteq>{x,y}""B\<subseteq>{x,y}" by auto
        {
          assume "x\<in>A"
          with \<open>x\<in>A\<longrightarrow>x\<notin>B\<close>\<open>B\<subseteq>{x,y}\<close> have "B\<subseteq>{y}" by auto
          then have "B=0\<or>B={y}" by auto
          with y_no_cl cl(2) have "B=0" by auto
        }
        moreover
        {
          assume "x\<notin>A"
          with \<open>A\<subseteq>{x,y}\<close> have "A\<subseteq>{y}" by auto
          then have "A=0\<or>A={y}" by auto
          with y_no_cl cl(1) have "A=0" by auto
        }
        ultimately have "A=0\<or>B=0" by auto
      }
      then have "(T{restricted to}{x,y}){is ultraconnected}" unfolding IsUConnected_def by auto
      with ASS \<open>x\<in>\<Union>T\<close>\<open>y\<in>\<Union>T\<close> have "{x,y}{is in the spectrum of}IsUConnected" unfolding antiProperty_def
        by auto
      then have "{x,y}\<lesssim>1" using UConn_spectrum by auto
      moreover have "x\<in>{x,y}" by auto
      ultimately have "{x}={x,y}" using lepoll_1_is_sing[of "{x,y}""x"] by auto
      moreover
      have "y\<in>{x,y}" by auto
      ultimately have "y\<in>{x}" by auto
      then have "y=x" by auto
      then have "False" using \<open>x\<noteq>y\<close> by auto
    }
    then have "\<exists>U\<in>T. x\<in>U\<and>y\<notin>U" by auto
  }
  then show "T{is T\<^sub>1}" unfolding isT1_def by auto
qed

text\<open>Is is natural that separation axioms and connection axioms are anti-properties of each other;
as the concepts of connectedness and separation are opposite.\<close>

text\<open>To end this section, let's try to charaterize anti-sober spaces.\<close>

lemma sober_spectrum:
  shows "(A{is in the spectrum of}IsSober) \<longleftrightarrow> A\<lesssim>1"
proof
  assume AS:"A{is in the spectrum of}IsSober"
  {
    assume "A=0"
    then have "A\<lesssim>1" using empty_lepollI by auto
  }
  moreover
  { 
    assume "A\<noteq>0"
    note AS
    moreover
    have top:"{0,A}{is a topology}" unfolding IsATopology_def by auto
    moreover
    have "\<Union>{0,A}=A" by auto
    then have "\<Union>{0,A}\<approx>A" by auto
    ultimately have "{0,A}{is sober}" using Spec_def by auto
    moreover
    have "{0,A}{is hyperconnected}" using Indiscrete_HConn by auto
    moreover
    have "{0,A}{restricted to}A={0,A}" unfolding RestrictedTo_def by auto
    moreover
    have "A{is closed in}{0,A}" unfolding IsClosed_def by auto
    moreover
    note \<open>A\<noteq>0\<close>
    ultimately have "\<exists>x\<in>A. A=Closure({x},{0,A})\<and> (\<forall>y\<in>\<Union>{0, A}. A = Closure({y}, {0, A}) \<longrightarrow> y = x)" unfolding IsSober_def by auto
    then obtain x where "x\<in>A" "A=Closure({x},{0,A})" and reg:"\<forall>y\<in>A. A = Closure({y}, {0, A}) \<longrightarrow> y = x" by auto
    {
      fix y assume "y\<in>A"
      with top have "Closure({y},{0,A}){is closed in}{0,A}" using topology0.cl_is_closed
        topology0_def by auto
      moreover
      from \<open>y\<in>A\<close> top have "y\<in>Closure({y},{0,A})" using topology0.cl_contains_set
        topology0_def by auto
      ultimately have "A-Closure({y},{0,A})\<in>{0,A}""Closure({y},{0,A})\<inter>A\<noteq>0" unfolding IsClosed_def
        by auto
      then have "A-Closure({y},{0,A})=A\<or>A-Closure({y},{0,A})=0"
        by auto
      moreover
      from \<open>y\<in>A\<close>\<open>y\<in>Closure({y},{0,A})\<close> have "y\<in>A""y\<notin>A-Closure({y},{0,A})" by auto
      ultimately have "A-Closure({y},{0,A})=0" by (cases "A-Closure({y},{0,A})=A", simp, auto)
      moreover
      from \<open>y\<in>A\<close> top have "Closure({y},{0,A})\<subseteq>A" using topology0_def topology0.Top_3_L11(1) by blast
      then have "A-(A-Closure({y},{0,A}))=Closure({y},{0,A})" by auto
      ultimately have "A=Closure({y},{0,A})" by auto
    }
    with reg have "\<forall>y\<in>A. x=y" by auto
    with \<open>x\<in>A\<close> have "A={x}" by blast
    then have "A\<approx>1" using singleton_eqpoll_1 by auto
    then have "A\<lesssim>1" using eqpoll_imp_lepoll by auto
  }
  ultimately show "A\<lesssim>1" by auto
next
  assume "A\<lesssim>1"
  {
    fix T assume "T{is a topology}""\<Union>T\<approx>A"
    {
      assume "\<Union>T=0"
      then have "T{is sober}" unfolding IsSober_def by auto
    }
    moreover
    {
      assume "\<Union>T\<noteq>0"
      then obtain x where "x\<in>\<Union>T" by blast
      moreover
      from \<open>\<Union>T\<approx>A\<close> \<open>A\<lesssim>1\<close> have "\<Union>T\<lesssim>1" using eq_lepoll_trans by auto
      ultimately have "\<Union>T={x}" using lepoll_1_is_sing by auto
      moreover
      have "T\<subseteq>Pow(\<Union>T)" by auto
      ultimately have "T\<subseteq>Pow({x})" by auto
      then have "T\<subseteq>{0,{x}}" by blast
      moreover
      from \<open>T{is a topology}\<close> have "0\<in>T" using empty_open by auto
      moreover
      from \<open>T{is a topology}\<close> have "\<Union>T\<in>T" unfolding IsATopology_def by auto
      with \<open>\<Union>T={x}\<close> have "{x}\<in>T" by auto
      ultimately have T_def:"T={0,{x}}" by auto
      then have dd:"Pow(\<Union>T)-{0}={{x}}" by auto
      {
        fix B assume "B\<in>Pow(\<Union>T)-{0}"
        with dd have B_def:"B={x}" by auto
        from \<open>T{is a topology}\<close> have "(\<Union>T){is closed in}T" using topology0_def topology0.Top_3_L1
          by auto
        with \<open>\<Union>T={x}\<close> \<open>T{is a topology}\<close> have "Closure({x},T)={x}" using topology0.Top_3_L8
          unfolding topology0_def by auto
        with B_def have "B=Closure({x},T)" by auto
        moreover
        {
          fix y assume "y\<in>\<Union>T"
          with \<open>\<Union>T={x}\<close> have "y=x" by auto
          }
        then have "(\<forall>y\<in>\<Union>T. B = Closure({y}, T) \<longrightarrow> y = x)" by auto
        moreover note \<open>x\<in>\<Union>T\<close>
        ultimately have "(\<exists>x\<in>\<Union>T. B = Closure({x}, T) \<and> (\<forall>y\<in>\<Union>T. B = Closure({y}, T) \<longrightarrow> y = x))"
          by auto
      }
      then have "T{is sober}" unfolding IsSober_def by auto
    }
    ultimately have "T{is sober}" by blast
  }
  then show "A {is in the spectrum of} IsSober" unfolding Spec_def by auto
qed

theorem (in topology0)anti_sober:
  shows "(T{is anti-}IsSober) \<longleftrightarrow> T={0,\<Union>T}"
proof
  assume "T={0,\<Union>T}"
  {
    fix A assume "A\<in>Pow(\<Union>T)""(T{restricted to}A){is sober}"
    {
      assume "A=0"
      then have "A\<lesssim>1" using empty_lepollI by auto
      then have "A{is in the spectrum of}IsSober" using sober_spectrum by auto
    }
    moreover
    {
      assume "A\<noteq>0"
      have "\<Union>T\<in>{0,\<Union>T}""0\<in>{0,\<Union>T}" by auto
      with \<open>T={0,\<Union>T}\<close> have "(\<Union>T)\<in>T" "0\<in>T" by auto
      with \<open>A\<in>Pow(\<Union>T)\<close> have "{0,A}\<subseteq>(T{restricted to}A)" unfolding RestrictedTo_def by auto
      moreover
      have "\<forall>B\<in>{0,\<Union>T}. B=0\<or>B=\<Union>T" by auto
      with \<open>T={0,\<Union>T}\<close> have "\<forall>B\<in>T. B=0\<or>B=\<Union>T" by auto
      with \<open>A\<in>Pow(\<Union>T)\<close> have "T{restricted to}A\<subseteq>{0,A}" unfolding RestrictedTo_def by auto
      ultimately have top_def:"T{restricted to}A={0,A}" by auto
      moreover
      have "A{is closed in}{0,A}" unfolding IsClosed_def by auto
      moreover
      have "{0,A}{is hyperconnected}" using Indiscrete_HConn by auto
      moreover
      from \<open>A\<in>Pow(\<Union>T)\<close> have "(T{restricted to}A){restricted to}A=T{restricted to}A" using subspace_of_subspace[of "A""A""T"]
        by auto
      moreover
      note \<open>A\<noteq>0\<close> \<open>A\<in>Pow(\<Union>T)\<close>
      ultimately have "A\<in>Pow(\<Union>(T{restricted to}A))-{0}""A{is closed in}(T{restricted to}A)""((T{restricted to}A){restricted to}A){is hyperconnected}"
        by auto
      with \<open>(T{restricted to}A){is sober}\<close> have "\<exists>x\<in>\<Union>(T{restricted to}A). A=Closure({x},T{restricted to}A)\<and>(\<forall>y\<in>\<Union>(T{restricted to}A). A=Closure({y},T{restricted to}A) \<longrightarrow> y=x)"
        unfolding IsSober_def by auto
      with top_def have "\<exists>x\<in>A. A=Closure({x},{0,A})\<and>(\<forall>y\<in>A. A=Closure({y},{0,A}) \<longrightarrow> y=x)" by auto
      then obtain x where "x\<in>A""A=Closure({x},{0,A})"and reg:"\<forall>y\<in>A. A=Closure({y},{0,A}) \<longrightarrow> y=x" by auto
      {
        fix y assume "y\<in>A"
        from \<open>A\<noteq>0\<close> have top:"{0,A}{is a topology}" using indiscrete_ptopology[of "A"] indiscrete_partition[of "A"] Ptopology_is_a_topology(1)[of "{A}""A"]
          by auto
        with \<open>y\<in>A\<close> have "Closure({y},{0,A}){is closed in}{0,A}" using topology0.cl_is_closed
          topology0_def by auto
        moreover
        from \<open>y\<in>A\<close> top have "y\<in>Closure({y},{0,A})" using topology0.cl_contains_set
          topology0_def by auto
        ultimately have "A-Closure({y},{0,A})\<in>{0,A}""Closure({y},{0,A})\<inter>A\<noteq>0" unfolding IsClosed_def
          by auto
        then have "A-Closure({y},{0,A})=A\<or>A-Closure({y},{0,A})=0"
          by auto
        moreover
        from \<open>y\<in>A\<close>\<open>y\<in>Closure({y},{0,A})\<close> have "y\<in>A""y\<notin>A-Closure({y},{0,A})" by auto
        ultimately have "A-Closure({y},{0,A})=0" by (cases "A-Closure({y},{0,A})=A", simp, auto)
        moreover
        from \<open>y\<in>A\<close> top have "Closure({y},{0,A})\<subseteq>A" using topology0_def topology0.Top_3_L11(1) by blast
        then have "A-(A-Closure({y},{0,A}))=Closure({y},{0,A})" by auto
        ultimately have "A=Closure({y},{0,A})" by auto
      }
      with reg \<open>x\<in>A\<close> have "A={x}" by blast
      then have "A\<approx>1" using singleton_eqpoll_1 by auto
      then have "A\<lesssim>1" using eqpoll_imp_lepoll by auto
      then have "A{is in the spectrum of}IsSober" using sober_spectrum by auto
    }
    ultimately have "A{is in the spectrum of}IsSober" by auto
  }
  then show "T{is anti-}IsSober" using antiProperty_def by auto
next
  assume "T{is anti-}IsSober"
  {
    fix A
    assume "A\<in>T""A\<noteq>0""A\<noteq>\<Union>T"
    then obtain x y where "x\<in>A""y\<in>\<Union>T-A" "x\<noteq>y"by blast
    then have "{x}={x,y}\<inter>A" by auto
    with \<open>A\<in>T\<close> have "{x}\<in>T{restricted to}{x,y}" unfolding RestrictedTo_def by auto
    {
      assume "{y}\<in>T{restricted to}{x,y}"
      from \<open>y\<in>\<Union>T-A\<close> \<open>x\<in>A\<close>\<open>A\<in>T\<close> have "\<Union>(T{restricted to}{x,y})={x,y}" unfolding RestrictedTo_def
        by auto
      with \<open>x\<noteq>y\<close>\<open>{y}\<in>T{restricted to}{x,y}\<close>\<open>{x}\<in>T{restricted to}{x,y}\<close> have "(T{restricted to}{x,y}){is T\<^sub>2}"
        unfolding isT2_def by auto
      then have "(T{restricted to}{x,y}){is sober}" using topology0.T2_imp_anti_HConn[of "T{restricted to}{x,y}"]
        Top_1_L4 topology0_def topology0.anti_HConn_iff_T1_sober[of "T{restricted to}{x,y}"] by auto
    }
    moreover
    {
      assume "{y}\<notin>T{restricted to}{x,y}"
      moreover
      from \<open>y\<in>\<Union>T-A\<close> \<open>x\<in>A\<close>\<open>A\<in>T\<close> have "T{restricted to}{x,y}\<subseteq>Pow({x,y})" unfolding RestrictedTo_def by auto
      then have "T{restricted to}{x,y}\<subseteq>{0,{x},{y},{x,y}}" by blast
      moreover
      note \<open>{x}\<in>T{restricted to}{x,y}\<close> empty_open[OF Top_1_L4[of "{x,y}"]]
      moreover
      from \<open>y\<in>\<Union>T-A\<close> \<open>x\<in>A\<close>\<open>A\<in>T\<close> have tot:"\<Union>(T{restricted to}{x,y})={x,y}" unfolding RestrictedTo_def
        by auto
      from Top_1_L4[of "{x,y}"] have "\<Union>(T{restricted to}{x,y})\<in>T{restricted to}{x,y}" unfolding IsATopology_def
        by auto
      with tot have "{x,y}\<in>T{restricted to}{x,y}" by auto
      ultimately have top_d_def:"T{restricted to}{x,y}={0,{x},{x,y}}" by auto
      {
        fix B assume "B\<in>Pow({x,y})-{0}""B{is closed in}(T{restricted to}{x,y})"
        with top_d_def have "(\<Union>(T{restricted to}{x,y}))-B\<in>{0,{x},{x,y}}" unfolding IsClosed_def by simp
        moreover have "B\<in>{{x},{y},{x,y}}" using \<open>B\<in>Pow({x,y})-{0}\<close> by blast
        moreover note tot 
        ultimately have "{x,y}-B\<in>{0,{x},{x,y}}" by auto
        have xin:"x\<in>Closure({x},T{restricted to}{x,y})" using topology0.cl_contains_set[of "T{restricted to}{x,y}""{x}"]
          Top_1_L4[of "{x,y}"] unfolding topology0_def[of "(T {restricted to} {x, y})"] using tot by auto
        {
          assume "{x}{is closed in}(T{restricted to}{x,y})"
          then have "{x,y}-{x}\<in>(T{restricted to}{x,y})" unfolding IsClosed_def using tot
            by auto
          moreover
          from \<open>x\<noteq>y\<close> have "{x,y}-{x}={y}" by auto
          ultimately have "{y}\<in>(T{restricted to}{x,y})" by auto
          then have "False" using \<open>{y}\<notin>(T{restricted to}{x,y})\<close> by auto
        }
        then have "\<not>({x}{is closed in}(T{restricted to}{x,y}))" by auto
        moreover
        from tot have "(Closure({x},T{restricted to}{x,y})){is closed in}(T{restricted to}{x,y})"
          using topology0.cl_is_closed unfolding topology0_def using Top_1_L4[of "{x,y}"]
          tot by auto
        ultimately have "\<not>(Closure({x},T{restricted to}{x,y})={x})" by auto
        moreover note xin topology0.Top_3_L11(1)[of "T{restricted to}{x,y}""{x}"] tot
        ultimately have cl_x:"Closure({x},T{restricted to}{x,y})={x,y}" unfolding topology0_def
          using Top_1_L4[of "{x,y}"] by auto
        have "{y}{is closed in}(T{restricted to}{x,y})" unfolding IsClosed_def using tot
          top_d_def \<open>x\<noteq>y\<close> by auto
        then have cl_y:"Closure({y},T{restricted to}{x,y})={y}" using topology0.Top_3_L8[of "T{restricted to}{x,y}"]
          unfolding topology0_def using Top_1_L4[of "{x,y}"] tot by auto
        {
          assume "{x,y}-B=0"
          with \<open>B\<in>Pow({x,y})-{0}\<close> have B:"{x,y}=B" by auto
          {
            fix m
            assume dis:"m\<in>{x,y}" and B_def:"B=Closure({m},T{restricted to}{x,y})"
            {
              assume "m=y"
              with B_def have "B=Closure({y},T{restricted to}{x,y})" by auto
              with cl_y have "B={y}" by auto
              with B have "{x,y}={y}" by auto
              moreover have "x\<in>{x,y}" by auto
              ultimately
              have "x\<in>{y}" by auto
              with \<open>x\<noteq>y\<close> have "False" by auto
            }
            with dis have "m=x" by auto
          }
          then have "(\<forall>m\<in>{x,y}. B=Closure({m},T{restricted to}{x,y})\<longrightarrow>m=x )" by auto
          moreover
          have "B=Closure({x},T{restricted to}{x,y})" using cl_x B by auto
          ultimately have "\<exists>t\<in>{x,y}. B=Closure({t},T{restricted to}{x,y}) \<and> (\<forall>m\<in>{x,y}. B=Closure({m},T{restricted to}{x,y})\<longrightarrow>m=t )"
            by auto
        }
        moreover
        {
          assume "{x,y}-B\<noteq>0"
          with \<open>{x,y}-B\<in>{0,{x},{x,y}}\<close> have or:"{x,y}-B={x}\<or>{x,y}-B={x,y}" by auto
          {
            assume "{x,y}-B={x}"
            then have "x\<in>{x,y}-B" by auto
            with \<open>B\<in>{{x},{y},{x,y}}\<close> \<open>x\<noteq>y\<close> have B:"B={y}" by blast
            {
              fix m
              assume dis:"m\<in>{x,y}" and B_def:"B=Closure({m},T{restricted to}{x,y})"
              {
                assume "m=x"
                with B_def have "B=Closure({x},T{restricted to}{x,y})" by auto
                with cl_x have "B={x,y}" by auto
                with B have "{x,y}={y}" by auto
                moreover have "x\<in>{x,y}" by auto
                ultimately
                have "x\<in>{y}" by auto
                with \<open>x\<noteq>y\<close> have "False" by auto
              }
              with dis have "m=y" by auto
            }
            moreover
            have "B=Closure({y},T{restricted to}{x,y})" using cl_y B by auto
            ultimately have "\<exists>t\<in>{x,y}. B=Closure({t},T{restricted to}{x,y}) \<and> (\<forall>m\<in>{x,y}. B=Closure({m},T{restricted to}{x,y})\<longrightarrow>m=t )"
              by auto
          }
          moreover
          {
            assume "{x,y}-B\<noteq>{x}"
            with or have "{x,y}-B={x,y}" by auto
            then have "x\<in>{x,y}-B""y\<in>{x,y}-B" by auto
            with \<open>B\<in>{{x},{y},{x,y}}\<close> \<open>x\<noteq>y\<close> have "False" by auto
          }
          ultimately have "\<exists>t\<in>{x,y}. B=Closure({t},T{restricted to}{x,y}) \<and> (\<forall>m\<in>{x,y}. B=Closure({m},T{restricted to}{x,y})\<longrightarrow>m=t )"
            by auto
        }
        ultimately have "\<exists>t\<in>{x,y}. B=Closure({t},T{restricted to}{x,y}) \<and> (\<forall>m\<in>{x,y}. B=Closure({m},T{restricted to}{x,y})\<longrightarrow>m=t )"
          by auto
      }
      then have "(T{restricted to}{x,y}){is sober}" unfolding IsSober_def using tot by auto
    }
    ultimately have "(T{restricted to}{x,y}){is sober}" by auto
    with \<open>T{is anti-}IsSober\<close> have "{x,y}{is in the spectrum of}IsSober" unfolding antiProperty_def
      using \<open>x\<in>A\<close>\<open>A\<in>T\<close>\<open>y\<in>\<Union>T-A\<close> by auto
    then have "{x,y}\<lesssim>1" using sober_spectrum by auto
    moreover
    have "x\<in>{x,y}" by auto
    ultimately have "{x,y}={x}" using lepoll_1_is_sing[of "{x,y}""x"] by auto
    moreover have "y\<in>{x,y}" by auto
    ultimately have "y\<in>{x}" by auto
    then have "False" using \<open>x\<noteq>y\<close> by auto
  }
  then have "T\<subseteq>{0,\<Union>T}" by auto
  with empty_open[OF topSpaceAssum] topSpaceAssum show "T={0,\<Union>T}" unfolding IsATopology_def
    by auto
qed

      
end
