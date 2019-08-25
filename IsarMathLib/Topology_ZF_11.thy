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

section \<open>Topology 11\<close>

theory Topology_ZF_11 imports Topology_ZF_7 Finite_ZF_1

begin

text\<open>This file deals with order topologies. The order topology
is already defined in @{file "Topology_ZF_examples_1.thy"}.\<close>

subsection\<open>Order topologies\<close>

text\<open>We will assume
most of the time that the ordered set has more than one point.
It is natural to think that the topological properties
can be translated to properties of the order; since every
order rises one and only one topology in a set.\<close>

subsection\<open>Separation properties\<close>

text\<open>Order topologies have a lot of separation properties.\<close>

text\<open>Every order topology is Hausdorff.\<close>

theorem order_top_T2:
  assumes "IsLinOrder(X,r)" "\<exists>x y. x\<noteq>y\<and>x\<in>X\<and>y\<in>X"
  shows "(OrdTopology X r){is T\<^sub>2}"
proof-
  {
    fix x y assume A1:"x\<in>\<Union>(OrdTopology X r)""y\<in>\<Union>(OrdTopology X r)""x\<noteq>y"
    then have AS:"x\<in>X""y\<in>X""x\<noteq>y" using union_ordtopology[OF assms(1) assms(2)] by auto
    {
      assume A2:"\<exists>z\<in>X-{x,y}. (\<langle>x,y\<rangle>\<in>r\<longrightarrow>\<langle>x,z\<rangle>\<in>r\<and>\<langle>z,y\<rangle>\<in>r)\<and>(\<langle>y,x\<rangle>\<in>r\<longrightarrow>\<langle>y,z\<rangle>\<in>r\<and>\<langle>z,x\<rangle>\<in>r)"
      from AS(1,2) assms(1) have "\<langle>x,y\<rangle>\<in>r\<or>\<langle>y,x\<rangle>\<in>r" unfolding IsLinOrder_def IsTotal_def by auto moreover
      {
        assume "\<langle>x,y\<rangle>\<in>r"
        with AS A2 obtain z where z:"\<langle>x,z\<rangle>\<in>r""\<langle>z,y\<rangle>\<in>r""z\<in>X""z\<noteq>x""z\<noteq>y" by auto
        with AS(1,2) have "x\<in>LeftRayX(X,r,z)""y\<in>RightRayX(X,r,z)" unfolding LeftRayX_def RightRayX_def
          by auto moreover
        have "LeftRayX(X,r,z)\<inter>RightRayX(X,r,z)=0" using inter_lray_rray[OF z(3) z(3) assms(1)]
          unfolding IntervalX_def using Order_ZF_2_L4[OF total_is_refl _ z(3)] assms(1) unfolding IsLinOrder_def
          by auto moreover
        have "LeftRayX(X,r,z)\<in>(OrdTopology X r)""RightRayX(X,r,z)\<in>(OrdTopology X r)"
          using z(3) base_sets_open[OF Ordtopology_is_a_topology(2)[OF assms(1)]] by auto
        ultimately have "\<exists>U\<in>(OrdTopology X r). \<exists>V\<in>(OrdTopology X r). x\<in>U \<and> y\<in>V \<and> U\<inter>V=0" by auto
      }
      moreover
      {
        assume "\<langle>y,x\<rangle>\<in>r"
        with AS A2 obtain z where z:"\<langle>y,z\<rangle>\<in>r""\<langle>z,x\<rangle>\<in>r""z\<in>X""z\<noteq>x""z\<noteq>y" by auto
        with AS(1,2) have "y\<in>LeftRayX(X,r,z)""x\<in>RightRayX(X,r,z)" unfolding LeftRayX_def RightRayX_def
          by auto moreover
        have "LeftRayX(X,r,z)\<inter>RightRayX(X,r,z)=0" using inter_lray_rray[OF z(3) z(3) assms(1)]
          unfolding IntervalX_def using Order_ZF_2_L4[OF total_is_refl _ z(3)] assms(1) unfolding IsLinOrder_def
          by auto moreover
        have "LeftRayX(X,r,z)\<in>(OrdTopology X r)""RightRayX(X,r,z)\<in>(OrdTopology X r)"
          using z(3) base_sets_open[OF Ordtopology_is_a_topology(2)[OF assms(1)]] by auto
        ultimately have "\<exists>U\<in>(OrdTopology X r). \<exists>V\<in>(OrdTopology X r). x\<in>U \<and> y\<in>V \<and> U\<inter>V=0" by auto
      }
      ultimately have "\<exists>U\<in>(OrdTopology X r). \<exists>V\<in>(OrdTopology X r). x\<in>U \<and> y\<in>V \<and> U\<inter>V=0" by auto
    }
    moreover
    {
      assume A2:"\<forall>z\<in>X - {x, y}. (\<langle>x, y\<rangle> \<in> r \<and> (\<langle>x, z\<rangle> \<notin> r \<or> \<langle>z, y\<rangle> \<notin> r)) \<or> (\<langle>y, x\<rangle> \<in> r \<and> (\<langle>y, z\<rangle> \<notin> r \<or> \<langle>z, x\<rangle> \<notin> r))"
      from AS(1,2) assms(1) have disj:"\<langle>x,y\<rangle>\<in>r\<or>\<langle>y,x\<rangle>\<in>r" unfolding IsLinOrder_def IsTotal_def by auto moreover
      {
        assume TT:"\<langle>x,y\<rangle>\<in>r"
        with AS assms(1) have T:"\<langle>y,x\<rangle>\<notin>r" unfolding IsLinOrder_def antisym_def by auto
        from TT AS(1-3) have "x\<in>LeftRayX(X,r,y)""y\<in>RightRayX(X,r,x)" unfolding LeftRayX_def RightRayX_def
          by auto moreover
        {
          fix z assume "z\<in>LeftRayX(X,r,y)\<inter>RightRayX(X,r,x)"
          then have "\<langle>z,y\<rangle>\<in>r""\<langle>x,z\<rangle>\<in>r""z\<in>X-{x,y}" unfolding RightRayX_def LeftRayX_def by auto
          with A2 T have "False" by auto
        }
        then have "LeftRayX(X,r,y)\<inter>RightRayX(X,r,x)=0" by auto moreover
        have "LeftRayX(X,r,y)\<in>(OrdTopology X r)""RightRayX(X,r,x)\<in>(OrdTopology X r)"
          using base_sets_open[OF Ordtopology_is_a_topology(2)[OF assms(1)]] AS by auto
        ultimately have "\<exists>U\<in>(OrdTopology X r). \<exists>V\<in>(OrdTopology X r). x\<in>U \<and> y\<in>V \<and> U\<inter>V=0" by auto
      }
      moreover
      {
        assume TT:"\<langle>y,x\<rangle>\<in>r"
        with AS assms(1) have T:"\<langle>x,y\<rangle>\<notin>r" unfolding IsLinOrder_def antisym_def by auto
        from TT AS(1-3) have "y\<in>LeftRayX(X,r,x)""x\<in>RightRayX(X,r,y)" unfolding LeftRayX_def RightRayX_def
          by auto moreover
        {
          fix z assume "z\<in>LeftRayX(X,r,x)\<inter>RightRayX(X,r,y)"
          then have "\<langle>z,x\<rangle>\<in>r""\<langle>y,z\<rangle>\<in>r""z\<in>X-{x,y}" unfolding RightRayX_def LeftRayX_def by auto
          with A2 T have "False" by auto
        }
        then have "LeftRayX(X,r,x)\<inter>RightRayX(X,r,y)=0" by auto moreover
        have "LeftRayX(X,r,x)\<in>(OrdTopology X r)""RightRayX(X,r,y)\<in>(OrdTopology X r)"
          using base_sets_open[OF Ordtopology_is_a_topology(2)[OF assms(1)]] AS by auto
        ultimately have "\<exists>U\<in>(OrdTopology X r). \<exists>V\<in>(OrdTopology X r). x\<in>U \<and> y\<in>V \<and> U\<inter>V=0" by auto
      }
      ultimately have "\<exists>U\<in>(OrdTopology X r). \<exists>V\<in>(OrdTopology X r). x\<in>U \<and> y\<in>V \<and> U\<inter>V=0" by auto
    }
    ultimately have "\<exists>U\<in>(OrdTopology X r). \<exists>V\<in>(OrdTopology X r). x\<in>U \<and> y\<in>V \<and> U\<inter>V=0" by auto
  }
  then show ?thesis unfolding isT2_def by auto
qed

text\<open>Every order topology is $T_4$, but the proof needs lots of machinery.
At the end of the file, we will prove that every order topology is normal; sooner
or later.\<close>

subsection\<open>Connectedness properties\<close>

text\<open>Connectedness is related to two properties of orders: completeness and density\<close>

text\<open>Some order-dense properties:\<close>

definition
  IsDenseSub ("_ {is dense in}_{with respect to}_") where
  "A {is dense in}X{with respect to}r \<equiv> 
  \<forall>x\<in>X. \<forall>y\<in>X. \<langle>x,y\<rangle>\<in>r \<and> x\<noteq>y  \<longrightarrow> (\<exists>z\<in>A-{x,y}. \<langle>x,z\<rangle>\<in>r\<and>\<langle>z,y\<rangle>\<in>r)"

definition
  IsDenseUnp ("_ {is not-properly dense in}_{with respect to}_") where
  "A {is not-properly dense in}X{with respect to}r \<equiv> 
  \<forall>x\<in>X. \<forall>y\<in>X. \<langle>x,y\<rangle>\<in>r \<and> x\<noteq>y  \<longrightarrow> (\<exists>z\<in>A. \<langle>x,z\<rangle>\<in>r\<and>\<langle>z,y\<rangle>\<in>r)"

definition
  IsWeaklyDenseSub ("_ {is weakly dense in}_{with respect to}_") where
  "A {is weakly dense in}X{with respect to}r \<equiv> 
  \<forall>x\<in>X. \<forall>y\<in>X. \<langle>x,y\<rangle>\<in>r \<and> x\<noteq>y  \<longrightarrow> ((\<exists>z\<in>A-{x,y}. \<langle>x,z\<rangle>\<in>r\<and>\<langle>z,y\<rangle>\<in>r)\<or> IntervalX(X,r,x,y)=0)"

definition
  IsDense ("_ {is dense with respect to}_") where
  "X {is dense with respect to}r \<equiv> 
  \<forall>x\<in>X. \<forall>y\<in>X. \<langle>x,y\<rangle>\<in>r \<and> x\<noteq>y  \<longrightarrow> (\<exists>z\<in>X-{x,y}. \<langle>x,z\<rangle>\<in>r\<and>\<langle>z,y\<rangle>\<in>r)"

lemma dense_sub:
  shows "(X {is dense with respect to}r) \<longleftrightarrow> (X {is dense in}X{with respect to}r)"
  unfolding IsDenseSub_def IsDense_def by auto

lemma not_prop_dense_sub:
  shows "(A {is dense in}X{with respect to}r) \<longrightarrow> (A {is not-properly dense in}X{with respect to}r)"
  unfolding IsDenseSub_def IsDenseUnp_def by auto

text\<open>In densely ordered sets, intervals are infinite.\<close>

theorem dense_order_inf_intervals:
  assumes "IsLinOrder(X,r)" "IntervalX(X, r, b, c)\<noteq>0""b\<in>X""c\<in>X" "X{is dense with respect to}r"
  shows "\<not>Finite(IntervalX(X, r, b, c))"
proof
  assume fin:"Finite(IntervalX(X, r, b, c))"
  have sub:"IntervalX(X, r, b, c)\<subseteq>X" unfolding IntervalX_def by auto
  have p:"Minimum(r,IntervalX(X, r, b, c))\<in>IntervalX(X, r, b, c)" using Finite_ZF_1_T2(2)[OF assms(1) Finite_Fin[OF fin sub] assms(2)]
    by auto
  then have "\<langle>b,Minimum(r,IntervalX(X, r, b, c))\<rangle>\<in>r""b\<noteq>Minimum(r,IntervalX(X, r, b, c))"
    unfolding IntervalX_def using Order_ZF_2_L1 by auto
  with assms(3,5) sub p obtain z1 where z1:"z1\<in>X""z1\<noteq>b""z1\<noteq>Minimum(r,IntervalX(X, r, b, c))""\<langle>b,z1\<rangle>\<in>r""\<langle>z1,Minimum(r,IntervalX(X, r, b, c))\<rangle>\<in>r"
    unfolding IsDense_def by blast
  from p have B:"\<langle>Minimum(r,IntervalX(X, r, b, c)),c\<rangle>\<in>r" unfolding IntervalX_def using Order_ZF_2_L1 by auto moreover
  have "trans(r)" using assms(1) unfolding IsLinOrder_def by auto moreover
  note z1(5) ultimately have z1a:"\<langle>z1,c\<rangle>\<in>r" unfolding trans_def by fast
  {
    assume "z1=c"
    with B have "\<langle>Minimum(r,IntervalX(X, r, b, c)),z1\<rangle>\<in>r" by auto
    with z1(5) have "z1=Minimum(r,IntervalX(X, r, b, c))" using assms(1) unfolding IsLinOrder_def antisym_def by auto
    then have "False" using z1(3) by auto
  }
  then have "z1\<noteq>c" by auto
  with z1(1,2,4) z1a have "z1\<in>IntervalX(X, r, b, c)" unfolding IntervalX_def using Order_ZF_2_L1 by auto
  then have "\<langle>Minimum(r,IntervalX(X, r, b, c)),z1\<rangle>\<in>r" using Finite_ZF_1_T2(4)[OF assms(1) Finite_Fin[OF fin sub] assms(2)] by auto
  with z1(5) have "z1=Minimum(r,IntervalX(X, r, b, c))" using assms(1) unfolding IsLinOrder_def antisym_def by auto
  with z1(3) show "False" by auto
qed

text\<open>Left rays are infinite.\<close>

theorem dense_order_inf_lrays:
  assumes "IsLinOrder(X,r)" "LeftRayX(X,r,c)\<noteq>0""c\<in>X"  "X{is dense with respect to}r"
  shows "\<not>Finite(LeftRayX(X,r,c))"
proof-
  from assms(2) obtain b where "b\<in>X""\<langle>b,c\<rangle>\<in>r""b\<noteq>c" unfolding LeftRayX_def by auto
  with assms(3) obtain z where "z\<in>X-{b,c}""\<langle>b,z\<rangle>\<in>r""\<langle>z,c\<rangle>\<in>r" using assms(4) unfolding IsDense_def by auto
  then have "IntervalX(X, r, b, c)\<noteq>0" unfolding IntervalX_def using Order_ZF_2_L1 by auto
  then have nFIN:"\<not>Finite(IntervalX(X, r, b, c))" using dense_order_inf_intervals[OF assms(1) _ _ assms(3,4)]
    \<open>b\<in>X\<close> by auto
  {
    fix d assume "d\<in>IntervalX(X, r, b, c)"
    then have "\<langle>b,d\<rangle>\<in>r""\<langle>d,c\<rangle>\<in>r""d\<in>X""d\<noteq>b""d\<noteq>c" unfolding IntervalX_def using Order_ZF_2_L1 by auto
    then have "d\<in>LeftRayX(X,r,c)" unfolding LeftRayX_def by auto
  }
  then have "IntervalX(X, r, b, c)\<subseteq>LeftRayX(X,r,c)" by auto
  with nFIN show ?thesis using subset_Finite by auto
qed

text\<open>Right rays are infinite.\<close>

theorem dense_order_inf_rrays:
  assumes "IsLinOrder(X,r)" "RightRayX(X,r,b)\<noteq>0""b\<in>X"  "X{is dense with respect to}r"
  shows "\<not>Finite(RightRayX(X,r,b))"
proof-
  from assms(2) obtain c where "c\<in>X""\<langle>b,c\<rangle>\<in>r""b\<noteq>c" unfolding RightRayX_def by auto
  with assms(3) obtain z where "z\<in>X-{b,c}""\<langle>b,z\<rangle>\<in>r""\<langle>z,c\<rangle>\<in>r" using assms(4) unfolding IsDense_def by auto
  then have "IntervalX(X, r, b, c)\<noteq>0" unfolding IntervalX_def using Order_ZF_2_L1 by auto
  then have nFIN:"\<not>Finite(IntervalX(X, r, b, c))" using dense_order_inf_intervals[OF assms(1) _ assms(3) _ assms(4)]
    \<open>c\<in>X\<close> by auto
  {
    fix d assume "d\<in>IntervalX(X, r, b, c)"
    then have "\<langle>b,d\<rangle>\<in>r""\<langle>d,c\<rangle>\<in>r""d\<in>X""d\<noteq>b""d\<noteq>c" unfolding IntervalX_def using Order_ZF_2_L1 by auto
    then have "d\<in>RightRayX(X,r,b)" unfolding RightRayX_def by auto
  }
  then have "IntervalX(X, r, b, c)\<subseteq>RightRayX(X,r,b)" by auto
  with nFIN show ?thesis using subset_Finite by auto
qed

text\<open>The whole space in a densely ordered set is infinite.\<close>

corollary dense_order_infinite:
  assumes "IsLinOrder(X,r)"  "X{is dense with respect to}r"
    "\<exists>x y. x\<noteq>y\<and>x\<in>X\<and>y\<in>X"
  shows "\<not>(X\<prec>nat)"
proof-
  from assms(3) obtain b c where B:"b\<in>X""c\<in>X""b\<noteq>c" by auto
  {
    assume "\<langle>b,c\<rangle>\<notin>r"
    with assms(1) have "\<langle>c,b\<rangle>\<in>r" unfolding IsLinOrder_def IsTotal_def using \<open>b\<in>X\<close>\<open>c\<in>X\<close> by auto
    with assms(2) B obtain z where "z\<in>X-{b,c}""\<langle>c,z\<rangle>\<in>r""\<langle>z,b\<rangle>\<in>r" unfolding IsDense_def by auto
    then have "IntervalX(X,r,c,b)\<noteq>0" unfolding IntervalX_def using Order_ZF_2_L1 by auto
    then have "\<not>(Finite(IntervalX(X,r,c,b)))" using dense_order_inf_intervals[OF assms(1) _ \<open>c\<in>X\<close>\<open>b\<in>X\<close> assms(2)]
      by auto moreover
    have "IntervalX(X,r,c,b)\<subseteq>X" unfolding IntervalX_def by auto
    ultimately have "\<not>(Finite(X))" using subset_Finite by auto
    then have "\<not>(X\<prec>nat)" using lesspoll_nat_is_Finite by auto
  }
  moreover
  {
    assume "\<langle>b,c\<rangle>\<in>r"
    with assms(2) B obtain z where "z\<in>X-{b,c}""\<langle>b,z\<rangle>\<in>r""\<langle>z,c\<rangle>\<in>r" unfolding IsDense_def by auto
    then have "IntervalX(X,r,b,c)\<noteq>0" unfolding IntervalX_def using Order_ZF_2_L1 by auto
    then have "\<not>(Finite(IntervalX(X,r,b,c)))" using dense_order_inf_intervals[OF assms(1) _ \<open>b\<in>X\<close>\<open>c\<in>X\<close> assms(2)]
      by auto moreover
    have "IntervalX(X,r,b,c)\<subseteq>X" unfolding IntervalX_def by auto
    ultimately have "\<not>(Finite(X))" using subset_Finite by auto
    then have "\<not>(X\<prec>nat)" using lesspoll_nat_is_Finite by auto
  }
  ultimately show ?thesis by auto
qed

text\<open>If an order topology is connected, then the order is complete.
It is equivalent to assume that $r\subseteq X\times X$ or prove that
$r\cap X\times X$ is complete.\<close>

theorem conn_imp_complete:
  assumes "IsLinOrder(X,r)" "\<exists>x y. x\<noteq>y\<and>x\<in>X\<and>y\<in>X" "r\<subseteq>X\<times>X"
     "(OrdTopology X r){is connected}"
  shows "r{is complete}"
proof-
  {
    assume "\<not>(r{is complete})"
    then obtain A where A:"A\<noteq>0""IsBoundedAbove(A,r)""\<not>(HasAminimum(r, \<Inter>b\<in>A. r `` {b}))" unfolding
      IsComplete_def by auto
    from A(3) have r1:"\<forall>m\<in>\<Inter>b\<in>A. r `` {b}. \<exists>x\<in>\<Inter>b\<in>A. r `` {b}. \<langle>m,x\<rangle>\<notin>r" unfolding HasAminimum_def
      by force
    from A(1,2) obtain b where r2:"\<forall>x\<in>A. \<langle>x, b\<rangle> \<in> r" unfolding IsBoundedAbove_def by auto
    with assms(3) A(1) have "A\<subseteq>X""b\<in>X" by auto
    with assms(3) have r3:"\<forall>c\<in>A. r `` {c}\<subseteq>X" using image_iff by auto
    from r2 have "\<forall>x\<in>A. b\<in>r``{x}" using image_iff by auto
    then have noE:"b\<in>(\<Inter>b\<in>A. r `` {b})" using A(1) by auto
    {
      fix x assume "x\<in>(\<Inter>b\<in>A. r `` {b})"
      then have "\<forall>c\<in>A. x\<in>r``{c}" by auto
      with A(1) obtain c where "c\<in>A" "x\<in>r``{c}" by auto
      with r3 have "x\<in>X" by auto
    }
    then have sub:"(\<Inter>b\<in>A. r `` {b})\<subseteq>X" by auto
    {
      fix x assume x:"x\<in>(\<Inter>b\<in>A. r `` {b})"
      with r1 have "\<exists>z\<in>\<Inter>b\<in>A. r `` {b}. \<langle>x,z\<rangle>\<notin>r" by auto
      then obtain z where z:"z\<in>(\<Inter>b\<in>A. r `` {b})""\<langle>x,z\<rangle>\<notin>r" by auto
      from x z(1) sub have "x\<in>X""z\<in>X" by auto
      with z(2) have "\<langle>z,x\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def IsTotal_def by auto
      then have xx:"x\<in>RightRayX(X,r,z)" unfolding RightRayX_def using \<open>x\<in>X\<close>\<open>\<langle>x,z\<rangle>\<notin>r\<close>
        assms(1) unfolding IsLinOrder_def using total_is_refl unfolding refl_def by auto
      {
        fix m assume "m\<in>RightRayX(X,r,z)"
        then have m:"m\<in>X-{z}""\<langle>z,m\<rangle>\<in>r" unfolding RightRayX_def by auto
        {
          fix c assume "c\<in>A"
          with z(1) have "\<langle>c,z\<rangle>\<in>r" using image_iff by auto
          with m(2) have "\<langle>c,m\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def trans_def by fast
          then have "m\<in>r``{c}" using image_iff by auto
        }
        with A(1) have "m\<in>(\<Inter>b\<in>A. r `` {b})" by auto
      }
      then have sub1:"RightRayX(X,r,z)\<subseteq>(\<Inter>b\<in>A. r `` {b})" by auto
      have "RightRayX(X,r,z)\<in>(OrdTopology X r)" using 
        base_sets_open[OF Ordtopology_is_a_topology(2)[OF assms(1)]] \<open>z\<in>X\<close> by auto
      with sub1 xx have "\<exists>U\<in>(OrdTopology X r). x\<in>U \<and> U\<subseteq>(\<Inter>b\<in>A. r `` {b})" by auto
    }
    then have "(\<Inter>b\<in>A. r `` {b})\<in>(OrdTopology X r)" using topology0.open_neigh_open[OF topology0_ordtopology[OF assms(1)]]
      by auto moreover
    {
      fix x assume "x\<in>X-(\<Inter>b\<in>A. r `` {b})"
      then have "x\<in>X""x\<notin>(\<Inter>b\<in>A. r `` {b})" by auto
      with A(1) obtain b where "x\<notin>r``{b}""b\<in>A" by auto
      then have "\<langle>b,x\<rangle>\<notin>r" using image_iff by auto
      with \<open>A\<subseteq>X\<close> \<open>b\<in>A\<close>\<open>x\<in>X\<close> have "\<langle>x,b\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def
        IsTotal_def by auto
      then have xx:"x\<in>LeftRayX(X,r,b)" unfolding LeftRayX_def using \<open>x\<in>X\<close> \<open>\<langle>b,x\<rangle>\<notin>r\<close>
        assms(1) unfolding IsLinOrder_def using total_is_refl unfolding refl_def by auto
      {
        fix y assume "y\<in>LeftRayX(X,r,b)\<inter>(\<Inter>b\<in>A. r `` {b})"
        then have "y\<in>X-{b}""\<langle>y,b\<rangle>\<in>r""\<forall>c\<in>A. y\<in>r``{c}" unfolding LeftRayX_def by auto
        then have "y\<in>X""\<langle>y,b\<rangle>\<in>r""\<forall>c\<in>A. \<langle>c,y\<rangle>\<in>r" using image_iff by auto
        with \<open>b\<in>A\<close> have "y=b" using assms(1) unfolding IsLinOrder_def antisym_def by auto
        then have "False" using \<open>y\<in>X-{b}\<close> by auto
      }
      then have sub1:"LeftRayX(X,r,b)\<subseteq>X-(\<Inter>b\<in>A. r `` {b})" unfolding LeftRayX_def by auto
      have "LeftRayX(X,r,b)\<in>(OrdTopology X r)" using 
        base_sets_open[OF Ordtopology_is_a_topology(2)[OF assms(1)]] \<open>b\<in>A\<close>\<open>A\<subseteq>X\<close> by blast
      with sub1 xx have "\<exists>U\<in>(OrdTopology X r). x\<in>U\<and>U\<subseteq>X-(\<Inter>b\<in>A. r `` {b})" by auto
    }
    then have "X - (\<Inter>b\<in>A. r `` {b})\<in>(OrdTopology X r)" using topology0.open_neigh_open[OF topology0_ordtopology[OF assms(1)]]
      by auto
    then have "\<Union>(OrdTopology X r)-(\<Inter>b\<in>A. r `` {b})\<in>(OrdTopology X r)" using union_ordtopology[OF assms(1,2)] by auto
    then have "(\<Inter>b\<in>A. r `` {b}){is closed in}(OrdTopology X r)" unfolding IsClosed_def using union_ordtopology[OF assms(1,2)]
      sub by auto
    moreover note assms(4) ultimately
    have "(\<Inter>b\<in>A. r `` {b})=0\<or>(\<Inter>b\<in>A. r `` {b})=X" using union_ordtopology[OF assms(1,2)] unfolding IsConnected_def
      by auto
    then have e1:"(\<Inter>b\<in>A. r `` {b})=X" using noE by auto
    then have "\<forall>x\<in>X. \<forall>b\<in>A. x\<in>r``{b}" by auto
    then have r4:"\<forall>x\<in>X. \<forall>b\<in>A. \<langle>b,x\<rangle>\<in>r" using image_iff by auto
    {
      fix a1 a2 assume aA:"a1\<in>A""a2\<in>A""a1\<noteq>a2"
      with \<open>A\<subseteq>X\<close> have aX:"a1\<in>X""a2\<in>X" by auto
      with r4 aA(1,2) have "\<langle>a1,a2\<rangle>\<in>r""\<langle>a2,a1\<rangle>\<in>r" by auto
      then have "a1=a2" using assms(1) unfolding IsLinOrder_def antisym_def by auto
      with aA(3) have "False" by auto
    }
    moreover
    from A(1) obtain t where "t\<in>A" by auto
    ultimately have "A={t}" by auto
    with r4 have "\<forall>x\<in>X. \<langle>t,x\<rangle>\<in>r""t\<in>X" using \<open>A\<subseteq>X\<close> by auto
    then have "HasAminimum(r,X)" unfolding HasAminimum_def by auto
    with e1 have "HasAminimum(r,\<Inter>b\<in>A. r `` {b})" by auto
    with A(3) have "False" by auto
  }
  then show ?thesis by auto
qed

text\<open>If an order topology is connected, then the order is dense.\<close>

theorem conn_imp_dense:
  assumes "IsLinOrder(X,r)" "\<exists>x y. x\<noteq>y\<and>x\<in>X\<and>y\<in>X"
     "(OrdTopology X r){is connected}"
  shows "X {is dense with respect to}r"
proof-
  {
    assume "\<not>(X {is dense with respect to}r)"
    then have "\<exists>x1\<in>X. \<exists>x2\<in>X. \<langle>x1,x2\<rangle>\<in>r\<and>x1\<noteq>x2\<and>(\<forall>z\<in>X-{x1,x2}. \<langle>x1,z\<rangle>\<notin>r\<or>\<langle>z,x2\<rangle>\<notin>r)"
      unfolding IsDense_def by auto
    then obtain x1 x2 where x:"x1\<in>X""x2\<in>X""\<langle>x1,x2\<rangle>\<in>r""x1\<noteq>x2""(\<forall>z\<in>X-{x1,x2}. \<langle>x1,z\<rangle>\<notin>r\<or>\<langle>z,x2\<rangle>\<notin>r)" by auto
    from x(1,2) have P:"LeftRayX(X,r,x2)\<in>(OrdTopology X r)""RightRayX(X,r,x1)\<in>(OrdTopology X r)"
      using  base_sets_open[OF Ordtopology_is_a_topology(2)[OF assms(1)]] by auto
    {
      fix x assume "x\<in>X-LeftRayX(X,r,x2)"
      then have "x\<in>X" "x\<notin>LeftRayX(X,r,x2)" by auto
      then have "\<langle>x,x2\<rangle>\<notin>r\<or>x=x2" unfolding LeftRayX_def by auto
      then have "\<langle>x2,x\<rangle>\<in>r\<or>x=x2" using assms(1) \<open>x\<in>X\<close> \<open>x2\<in>X\<close> unfolding IsLinOrder_def
        IsTotal_def by auto
      then have s:"\<langle>x2,x\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def using total_is_refl \<open>x2\<in>X\<close>
        unfolding refl_def by auto
      with x(3) have "\<langle>x1,x\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def trans_def by fast
      then have "x=x1\<or>x\<in>RightRayX(X,r,x1)" unfolding RightRayX_def using \<open>x\<in>X\<close> by auto
      with s have "\<langle>x2,x1\<rangle>\<in>r\<or>x\<in>RightRayX(X,r,x1)" by auto
      with x(3) have "x1=x2 \<or> x\<in>RightRayX(X,r,x1)" using assms(1) unfolding IsLinOrder_def
        antisym_def by auto
      with x(4) have "x\<in>RightRayX(X,r,x1)" by auto
    }
    then have "X-LeftRayX(X,r,x2)\<subseteq>RightRayX(X,r,x1)" by auto moreover
    {
      fix x assume "x\<in>RightRayX(X,r,x1)"
      then have xr:"x\<in>X-{x1}""\<langle>x1,x\<rangle>\<in>r" unfolding RightRayX_def by auto
      {
        assume "x\<in>LeftRayX(X,r,x2)"
        then have xl:"x\<in>X-{x2}""\<langle>x,x2\<rangle>\<in>r" unfolding LeftRayX_def by auto
        from xl xr x(5) have "False" by auto
      }
      with xr(1) have "x\<in>X-LeftRayX(X,r,x2)" by auto
    }
    ultimately have "RightRayX(X,r,x1)=X-LeftRayX(X,r,x2)" by auto
    then have "LeftRayX(X,r,x2){is closed in}(OrdTopology X r)" using P(2) union_ordtopology[
      OF assms(1,2)] unfolding IsClosed_def LeftRayX_def by auto
    with P(1) have "LeftRayX(X,r,x2)=0\<or>LeftRayX(X,r,x2)=X" using union_ordtopology[
      OF assms(1,2)] assms(3) unfolding IsConnected_def by auto
    with x(1,3,4) have "LeftRayX(X,r,x2)=X" unfolding LeftRayX_def by auto
    then have "x2\<in>LeftRayX(X,r,x2)" using x(2) by auto
    then have "False" unfolding LeftRayX_def by auto
  }
  then show ?thesis by auto
qed

text\<open>Actually a connected order topology is one that comes from a dense
and complete order.\<close>

text\<open>First a lemma. In a complete ordered set, every non-empty set bounded from below has
a maximum lower bound.\<close>

lemma complete_order_bounded_below:
  assumes "r{is complete}" "IsBoundedBelow(A,r)" "A\<noteq>0" "r\<subseteq>X\<times>X"
  shows "HasAmaximum(r,\<Inter>c\<in>A. r-``{c})"
proof-
  let ?M="\<Inter>c\<in>A. r-``{c}"
  from assms(3) obtain t where A:"t\<in>A" by auto
  {
    fix m assume "m\<in>?M"
    with A have "m\<in>r-``{t}" by auto
    then have "\<langle>m,t\<rangle>\<in>r" by auto
  }
  then have "(\<forall>x\<in>\<Inter>c\<in>A. r -`` {c}. \<langle>x, t\<rangle> \<in> r)" by auto
  then have "IsBoundedAbove(?M,r)" unfolding IsBoundedAbove_def by auto
  moreover
  from assms(2,3) obtain l where " \<forall>x\<in>A. \<langle>l, x\<rangle> \<in> r" unfolding IsBoundedBelow_def by auto
  then have "\<forall>x\<in>A. l \<in> r-``{x}" using vimage_iff by auto
  with assms(3) have "l\<in>?M" by auto
  then have "?M\<noteq>0" by auto moreover note assms(1)
  ultimately have "HasAminimum(r,\<Inter>c\<in>?M. r `` {c})" unfolding IsComplete_def by auto
  then obtain rr where rr:"rr\<in>(\<Inter>c\<in>?M. r `` {c})" "\<forall>s\<in>(\<Inter>c\<in>?M. r `` {c}). \<langle>rr,s\<rangle>\<in>r" unfolding HasAminimum_def
    by auto
  {
    fix aa assume A:"aa\<in>A"
    {
      fix c assume M:"c\<in>?M"
      with A have "\<langle>c,aa\<rangle>\<in>r" by auto
      then have "aa\<in>r``{c}" by auto
    }
    then have "aa\<in>(\<Inter>c\<in>?M. r `` {c})" using rr(1) by auto
  }
  then have "A\<subseteq>(\<Inter>c\<in>?M. r `` {c})" by auto
  with rr(2) have "\<forall>s\<in>A. \<langle>rr,s\<rangle>\<in>r" by auto
  then have "rr\<in>?M" using assms(3) by auto
  moreover
  {
    fix m assume "m\<in>?M"
    then have "rr\<in>r``{m}" using rr(1) by auto
    then have "\<langle>m,rr\<rangle>\<in>r" by auto
  }
  then have "\<forall>m\<in>?M. \<langle>m,rr\<rangle>\<in>r" by auto
  ultimately show ?thesis unfolding HasAmaximum_def by auto
qed 

theorem comp_dense_imp_conn:
  assumes "IsLinOrder(X,r)" "\<exists>x y. x\<noteq>y\<and>x\<in>X\<and>y\<in>X" "r\<subseteq>X\<times>X"
     "X {is dense with respect to}r" "r{is complete}"
  shows "(OrdTopology X r){is connected}"
proof-
  {
    assume "\<not>((OrdTopology X r){is connected})"
    then obtain U where U:"U\<noteq>0""U\<noteq>X""U\<in>(OrdTopology X r)""U{is closed in}(OrdTopology X r)"
      unfolding IsConnected_def using union_ordtopology[OF assms(1,2)] by auto
    from U(4) have A:"X-U\<in>(OrdTopology X r)""U\<subseteq>X" unfolding IsClosed_def using union_ordtopology[OF assms(1,2)] by auto
    from U(1) obtain u where "u\<in>U" by auto
    from A(2) U(1,2) have "X-U\<noteq>0" by auto
    then obtain v where "v\<in>X-U" by auto
    with \<open>u\<in>U\<close> \<open>U\<subseteq>X\<close> have "\<langle>u,v\<rangle>\<in>r\<or>\<langle>v,u\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def IsTotal_def
      by auto
    {
      assume "\<langle>u,v\<rangle>\<in>r"
      have "LeftRayX(X,r,v)\<in>(OrdTopology X r)" using base_sets_open[OF Ordtopology_is_a_topology(2)[OF assms(1)]]
        \<open>v\<in>X-U\<close> by auto
      then have "U\<inter>LeftRayX(X,r,v)\<in>(OrdTopology X r)" using U(3) using Ordtopology_is_a_topology(1)
        [OF assms(1)] unfolding IsATopology_def by auto
      {
        fix b assume "b\<in>(U)\<inter>LeftRayX(X,r,v)"
        then have "\<langle>b,v\<rangle>\<in>r" unfolding LeftRayX_def by auto
      }
      then have bound:"IsBoundedAbove(U\<inter>LeftRayX(X,r,v),r)" unfolding IsBoundedAbove_def by auto moreover
      with \<open>\<langle>u,v\<rangle>\<in>r\<close>\<open>u\<in>U\<close>\<open>U\<subseteq>X\<close>\<open>v\<in>X-U\<close> have nE:"U\<inter>LeftRayX(X,r,v)\<noteq>0" unfolding LeftRayX_def by auto
      ultimately have Hmin:"HasAminimum(r,\<Inter>c\<in>U\<inter>LeftRayX(X,r,v). r``{c})" using assms(5) unfolding IsComplete_def
        by auto
      let ?min="Supremum(r,U\<inter>LeftRayX(X,r,v))"
      {
        fix c assume "c\<in>U\<inter>LeftRayX(X,r,v)"
        then have "\<langle>c,v\<rangle>\<in>r" unfolding LeftRayX_def by auto
      }
      then have a1:"\<langle>?min,v\<rangle>\<in>r" using Order_ZF_5_L3[OF _ nE Hmin] assms(1) unfolding IsLinOrder_def
        by auto
      {
        assume ass:"?min\<in>U"
        then obtain V where V:"?min\<in>V""V\<subseteq>U"
          "V\<in>{IntervalX(X,r,b,c). \<langle>b,c\<rangle>\<in>X\<times>X}\<union>{LeftRayX(X,r,b). b\<in>X}\<union>{RightRayX(X,r,b). b\<in>X}" using point_open_base_neigh
          [OF Ordtopology_is_a_topology(2)[OF assms(1)] \<open>U\<in>(OrdTopology X r)\<close> ass] by blast
        {
          assume "V\<in>{RightRayX(X,r,b). b\<in>X}"
          then obtain b where b:"b\<in>X" "V=RightRayX(X,r,b)" by auto
          note a1 moreover
          from V(1) b(2) have a2:"\<langle>b,?min\<rangle>\<in>r""?min\<noteq>b" unfolding RightRayX_def by auto
          ultimately have "\<langle>b,v\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def trans_def by blast moreover
          {
            assume "b=v"
            with a1 a2(1) have "b=?min" using assms(1) unfolding IsLinOrder_def antisym_def by auto
            with a2(2) have "False" by auto
          }
          ultimately have "False" using V(2) b(2) unfolding RightRayX_def using \<open>v\<in>X-U\<close> by auto
        }
        moreover
        {
          assume "V\<in>{LeftRayX(X,r,b). b\<in>X}"
          then obtain b where b:"V=LeftRayX(X,r,b)" "b\<in>X" by auto
          {
            assume "\<langle>v,b\<rangle>\<in>r"
            then have "b=v\<or>v\<in>LeftRayX(X,r,b)" unfolding LeftRayX_def using \<open>v\<in>X-U\<close> by auto
            then have "b=v" using b(1) V(2) \<open>v\<in>X-U\<close> by auto
          }
          then have bv:"\<langle>b,v\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def IsTotal_def using b(2)
            \<open>v\<in>X-U\<close> by auto
          from b(1) V(1) have "\<langle>?min,b\<rangle>\<in>r""?min\<noteq>b" unfolding LeftRayX_def by auto
          with assms(4) obtain z where z:"\<langle>?min,z\<rangle>\<in>r""\<langle>z,b\<rangle>\<in>r""z\<in>X-{b,?min}" unfolding IsDense_def
            using b(2) V(1,2) \<open>U\<subseteq>X\<close> by blast
          then have rayb:"z\<in>LeftRayX(X,r,b)" unfolding LeftRayX_def by auto
          from z(2) bv have "\<langle>z,v\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def trans_def by fast
          moreover
          {
            assume "z=v"
            with bv have "\<langle>b,z\<rangle>\<in>r" by auto
            with z(2) have "b=z" using assms(1) unfolding IsLinOrder_def antisym_def by auto
            then have "False" using z(3) by auto
          }
          ultimately have "z\<in>LeftRayX(X,r,v)" unfolding LeftRayX_def using z(3) by auto
          with rayb have "z\<in>U\<inter>LeftRayX(X,r,v)" using V(2) b(1) by auto
          then have "?min\<in>r``{z}" using Order_ZF_4_L4(1)[OF _ Hmin] assms(1) unfolding Supremum_def IsLinOrder_def
            by auto
          then have "\<langle>z,?min\<rangle>\<in>r" by auto
          with z(1,3) have "False" using assms(1) unfolding IsLinOrder_def antisym_def by auto
        }
        moreover
        {
          assume "V\<in>{IntervalX(X,r,b,c). \<langle>b,c\<rangle>\<in>X\<times>X}"
          then obtain b c where b:"V=IntervalX(X,r,b,c)" "b\<in>X""c\<in>X" by auto
          from b V(1) have m:"\<langle>?min,c\<rangle>\<in>r""\<langle>b,?min\<rangle>\<in>r""?min\<noteq>b" "?min\<noteq>c" unfolding IntervalX_def Interval_def by auto  
          {
            assume A:"\<langle>c,v\<rangle>\<in>r"
            from m obtain z where z:"\<langle>z,c\<rangle>\<in>r" "\<langle>?min,z\<rangle>\<in>r""z\<in>X-{c,?min}" using assms(4) unfolding IsDense_def
              using b(3) V(1,2) \<open>U\<subseteq>X\<close> by blast
            from z(2) have "\<langle>b,z\<rangle>\<in>r" using m(2) assms(1) unfolding IsLinOrder_def trans_def
              by fast
            with z(1) have "z\<in>IntervalX(X,r,b,c)\<or>z=b" using z(3) unfolding IntervalX_def
              Interval_def by auto
            then have "z\<in>IntervalX(X,r,b,c)" using m(2) z(2,3) using assms(1) unfolding IsLinOrder_def
              antisym_def by auto
            with b(1) V(2) have "z\<in>U" by auto moreover
            from A z(1) have "\<langle>z,v\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def trans_def by fast
            moreover have "z\<noteq>v" using A z(1,3) assms(1) unfolding IsLinOrder_def antisym_def by auto
            ultimately have "z\<in>U\<inter>LeftRayX(X,r,v)" unfolding LeftRayX_def using z(3) by auto
            then have "?min\<in>r``{z}" using Order_ZF_4_L4(1)[OF _ Hmin] assms(1) unfolding Supremum_def IsLinOrder_def
              by auto
            then have "\<langle>z,?min\<rangle>\<in>r" by auto
            with z(2,3) have "False" using assms(1) unfolding IsLinOrder_def antisym_def by auto
          }
          then have vc:"\<langle>v,c\<rangle>\<in>r""v\<noteq>c" using assms(1) unfolding IsLinOrder_def IsTotal_def using \<open>v\<in>X-U\<close>
            b(3) by auto
          {
            assume "?min=v"
            with V(2,1) \<open>v\<in>X-U\<close> have "False" by auto
          }
          then have "?min\<noteq>v" by auto
          with a1 obtain z where z:"\<langle>?min,z\<rangle>\<in>r""\<langle>z,v\<rangle>\<in>r""z\<in>X-{?min,v}" using assms(4) unfolding IsDense_def
            using V(1,2) \<open>U\<subseteq>X\<close>\<open>v\<in>X-U\<close> by blast
          from z(2) vc(1) have zc:"\<langle>z,c\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def trans_def
            by fast moreover
          from m(2) z(1) have "\<langle>b,z\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def trans_def
            by fast ultimately
          have "z\<in>Interval(r,b,c)" using Order_ZF_2_L1B by auto moreover
          {
            assume "z=c"
            then have "False" using z(2) vc using assms(1) unfolding IsLinOrder_def antisym_def
              by fast
          }
          then have "z\<noteq>c" by auto moreover
          {
            assume "z=b"
            then have "z=?min" using m(2) z(1) using assms(1) unfolding IsLinOrder_def
              antisym_def by auto
            with z(3) have "False" by auto
          }
          then have "z\<noteq>b" by auto moreover
          have "z\<in>X" using z(3) by auto ultimately
          have "z\<in>IntervalX(X,r,b,c)" unfolding IntervalX_def by auto
          then have "z\<in>V" using b(1) by auto
          then have "z\<in>U" using V(2) by auto moreover
          from z(2,3) have "z\<in>LeftRayX(X,r,v)" unfolding LeftRayX_def by auto ultimately
          have "z\<in>U\<inter>LeftRayX(X,r,v)" by auto
          then have "?min\<in>r``{z}" using Order_ZF_4_L4(1)[OF _ Hmin] assms(1) unfolding Supremum_def IsLinOrder_def
            by auto
          then have "\<langle>z,?min\<rangle>\<in>r" by auto
          with z(1,3) have "False" using assms(1) unfolding IsLinOrder_def antisym_def by auto
        }
        ultimately have "False" using V(3) by auto
      }
      then have ass:"?min\<in>X-U" using a1 assms(3) by auto
      then obtain V where V:"?min\<in>V""V\<subseteq>X-U"
        "V\<in>{IntervalX(X,r,b,c). \<langle>b,c\<rangle>\<in>X\<times>X}\<union>{LeftRayX(X,r,b). b\<in>X}\<union>{RightRayX(X,r,b). b\<in>X}" using point_open_base_neigh
        [OF Ordtopology_is_a_topology(2)[OF assms(1)] \<open>X-U\<in>(OrdTopology X r)\<close> ass] by blast
      {
        assume "V\<in>{IntervalX(X,r,b,c). \<langle>b,c\<rangle>\<in>X\<times>X}"
        then obtain b c where b:"V=IntervalX(X,r,b,c)""b\<in>X""c\<in>X" by auto
        from b V(1) have m:"\<langle>?min,c\<rangle>\<in>r""\<langle>b,?min\<rangle>\<in>r""?min\<noteq>b" "?min\<noteq>c" unfolding IntervalX_def Interval_def by auto  
        {
          fix x assume A:"x\<in>U\<inter>LeftRayX(X,r,v)"
          then have "\<langle>x,v\<rangle>\<in>r""x\<in>U" unfolding LeftRayX_def by auto
          then have "x\<notin>V" using V(2) by auto
          then have "x\<notin>Interval(r, b, c) \<inter> X\<or>x=b\<or>x=c" using b(1) unfolding IntervalX_def by auto
          then have "(\<langle>b,x\<rangle>\<notin>r\<or>\<langle>x,c\<rangle>\<notin>r)\<or>x=b\<or>x=c""x\<in>X" using Order_ZF_2_L1B \<open>x\<in>U\<close>\<open>U\<subseteq>X\<close> by auto
          then have "(\<langle>x,b\<rangle>\<in>r\<or>\<langle>c,x\<rangle>\<in>r)\<or>x=b\<or>x=c" using assms(1) unfolding IsLinOrder_def IsTotal_def
            using b(2,3) by auto
          then have "(\<langle>x,b\<rangle>\<in>r\<or>\<langle>c,x\<rangle>\<in>r)" using assms(1) unfolding IsLinOrder_def using total_is_refl
            unfolding refl_def using b(2,3) by auto moreover
          from A have "\<langle>x,?min\<rangle>\<in>r" using Order_ZF_4_L4(1)[OF _ Hmin] assms(1) unfolding Supremum_def IsLinOrder_def
            by auto
          ultimately have "(\<langle>x,b\<rangle>\<in>r\<or>\<langle>c,?min\<rangle>\<in>r)" using assms(1) unfolding IsLinOrder_def trans_def
            by fast
          with m(1) have "(\<langle>x,b\<rangle>\<in>r\<or>c=?min)" using assms(1) unfolding IsLinOrder_def antisym_def by auto
          with m(4) have "\<langle>x,b\<rangle>\<in>r" by auto
        }
        then have "\<langle>?min,b\<rangle>\<in>r" using Order_ZF_5_L3[OF _ nE Hmin] assms(1) unfolding IsLinOrder_def by auto
        with m(2,3) have "False" using assms(1) unfolding IsLinOrder_def antisym_def by auto
      }
      moreover
      {
        assume "V\<in>{RightRayX(X,r,b). b\<in>X}"
        then obtain b where b:"V=RightRayX(X,r,b)" "b\<in>X" by auto
        from b V(1) have m:"\<langle>b,?min\<rangle>\<in>r""?min\<noteq>b" unfolding RightRayX_def by auto
        {
          fix x assume A:"x\<in>U\<inter>LeftRayX(X,r,v)"
          then have "\<langle>x,v\<rangle>\<in>r""x\<in>U" unfolding LeftRayX_def by auto
          then have "x\<notin>V" using V(2) by auto
          then have "x\<notin>RightRayX(X,r, b)" using b(1) by auto
          then have "(\<langle>b,x\<rangle>\<notin>r\<or>x=b)""x\<in>X" unfolding RightRayX_def using \<open>x\<in>U\<close>\<open>U\<subseteq>X\<close> by auto
          then have "\<langle>x,b\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def using total_is_refl unfolding
            refl_def unfolding IsTotal_def using b(2) by auto
        }
        then have "\<langle>?min,b\<rangle>\<in>r" using Order_ZF_5_L3[OF _ nE Hmin] assms(1) unfolding IsLinOrder_def by auto
        with m(2,1) have "False" using assms(1) unfolding IsLinOrder_def antisym_def by auto
      } moreover
      {
         assume "V\<in>{LeftRayX(X,r,b). b\<in>X}"
        then obtain b where b:"V=LeftRayX(X,r,b)" "b\<in>X" by auto
        from b V(1) have m:"\<langle>?min,b\<rangle>\<in>r""?min\<noteq>b" unfolding LeftRayX_def by auto
        {
          fix x assume A:"x\<in>U\<inter>LeftRayX(X,r,v)"
          then have "\<langle>x,v\<rangle>\<in>r""x\<in>U" unfolding LeftRayX_def by auto
          then have "x\<notin>V" using V(2) by auto
          then have "x\<notin>LeftRayX(X,r, b)" using b(1) by auto
          then have "(\<langle>x,b\<rangle>\<notin>r\<or>x=b)""x\<in>X" unfolding LeftRayX_def using \<open>x\<in>U\<close>\<open>U\<subseteq>X\<close> by auto
          then have "\<langle>b,x\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def using total_is_refl unfolding
            refl_def unfolding IsTotal_def using b(2) by auto
          with m(1) have "\<langle>?min,x\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def trans_def by fast
          moreover 
          from bound A have "\<exists>g. \<forall>y\<in>U\<inter>LeftRayX(X,r,v). \<langle>y,g\<rangle>\<in>r" using nE
            unfolding IsBoundedAbove_def by auto
          then obtain g where g:"\<forall>y\<in>U\<inter>LeftRayX(X,r,v). \<langle>y,g\<rangle>\<in>r" by auto
          with nE obtain t where "t\<in>U\<inter>LeftRayX(X,r,v)" by auto
          with g have "\<langle>t,g\<rangle>\<in>r" by auto
          with assms(3) have "g\<in>X" by auto
          with g have boundX:"\<exists>g\<in>X. \<forall>y\<in>U\<inter>LeftRayX(X,r,v). \<langle>y,g\<rangle>\<in>r" by auto
          have "\<langle>x,?min\<rangle>\<in>r" using Order_ZF_5_L7(2)[OF assms(3) _ assms(5) _ nE boundX]
            assms(1) \<open>U\<subseteq>X\<close> A unfolding LeftRayX_def IsLinOrder_def by auto
          ultimately have "x=?min" using assms(1) unfolding IsLinOrder_def antisym_def by auto
        }
        then have "U\<inter>LeftRayX(X,r,v)\<subseteq>{?min}" by auto moreover
        {
          assume "?min\<in>U\<inter>LeftRayX(X,r,v)"
          then have "?min\<in>U" by auto
          then have "False" using V(1,2) by auto
        }
        ultimately have "False" using nE by auto
      }
      moreover note V(3)
      ultimately have "False" by auto
    }
    with assms(1) have "\<langle>v,u\<rangle>\<in>r" unfolding IsLinOrder_def IsTotal_def using \<open>u\<in>U\<close>\<open>U\<subseteq>X\<close>
      \<open>v\<in>X-U\<close> by auto
    have "RightRayX(X,r,v)\<in>(OrdTopology X r)" using base_sets_open[OF Ordtopology_is_a_topology(2)[OF assms(1)]]
      \<open>v\<in>X-U\<close> by auto
    then have "U\<inter>RightRayX(X,r,v)\<in>(OrdTopology X r)" using U(3) using Ordtopology_is_a_topology(1)
      [OF assms(1)] unfolding IsATopology_def by auto
    {
      fix b assume "b\<in>(U)\<inter>RightRayX(X,r,v)"
      then have "\<langle>v,b\<rangle>\<in>r" unfolding RightRayX_def by auto
    }
    then have bound:"IsBoundedBelow(U\<inter>RightRayX(X,r,v),r)" unfolding IsBoundedBelow_def by auto
    with \<open>\<langle>v,u\<rangle>\<in>r\<close>\<open>u\<in>U\<close>\<open>U\<subseteq>X\<close>\<open>v\<in>X-U\<close> have nE:"U\<inter>RightRayX(X,r,v)\<noteq>0" unfolding RightRayX_def by auto
    have Hmax:"HasAmaximum(r,\<Inter>c\<in>U\<inter>RightRayX(X,r,v). r-``{c})" using complete_order_bounded_below[OF assms(5) bound nE assms(3)].
    let ?max="Infimum(r,U\<inter>RightRayX(X,r,v))"
    {
      fix c assume "c\<in>U\<inter>RightRayX(X,r,v)"
      then have "\<langle>v,c\<rangle>\<in>r" unfolding RightRayX_def by auto
    }
    then have a1:"\<langle>v,?max\<rangle>\<in>r" using Order_ZF_5_L4[OF _ nE Hmax] assms(1) unfolding IsLinOrder_def
      by auto
    {
      assume ass:"?max\<in>U"
      then obtain V where V:"?max\<in>V""V\<subseteq>U"
        "V\<in>{IntervalX(X,r,b,c). \<langle>b,c\<rangle>\<in>X\<times>X}\<union>{LeftRayX(X,r,b). b\<in>X}\<union>{RightRayX(X,r,b). b\<in>X}" using point_open_base_neigh
        [OF Ordtopology_is_a_topology(2)[OF assms(1)] \<open>U\<in>(OrdTopology X r)\<close> ass] by blast
      {
        assume "V\<in>{RightRayX(X,r,b). b\<in>X}"
        then obtain b where b:"b\<in>X" "V=RightRayX(X,r,b)" by auto
        from V(1) b(2) have a2:"\<langle>b,?max\<rangle>\<in>r""?max\<noteq>b" unfolding RightRayX_def by auto
        {
          assume "\<langle>b,v\<rangle>\<in>r"
          then have "b=v\<or>v\<in>RightRayX(X,r,b)" unfolding RightRayX_def using \<open>v\<in>X-U\<close> by auto
          then have "b=v" using b(2) V(2) \<open>v\<in>X-U\<close> by auto
        }
        then have bv:"\<langle>v,b\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def IsTotal_def using b(1)
          \<open>v\<in>X-U\<close> by auto
        from a2 assms(4) obtain z where z:"\<langle>b,z\<rangle>\<in>r""\<langle>z,?max\<rangle>\<in>r""z\<in>X-{b,?max}" unfolding IsDense_def
          using b(1) V(1,2) \<open>U\<subseteq>X\<close> by blast
        then have rayb:"z\<in>RightRayX(X,r,b)" unfolding RightRayX_def by auto
        from z(1) bv have "\<langle>v,z\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def trans_def by fast moreover
        {
          assume "z=v"
          with bv have "\<langle>z,b\<rangle>\<in>r" by auto
          with z(1) have "b=z" using assms(1) unfolding IsLinOrder_def antisym_def by auto
          then have "False" using z(3) by auto
        }
        ultimately have "z\<in>RightRayX(X,r,v)" unfolding RightRayX_def using z(3) by auto
        with rayb have "z\<in>U\<inter>RightRayX(X,r,v)" using V(2) b(2) by auto
        then have "?max\<in>r-``{z}" using Order_ZF_4_L3(1)[OF _ Hmax] assms(1) unfolding Infimum_def IsLinOrder_def
          by auto
        then have "\<langle>?max,z\<rangle>\<in>r" by auto
        with z(2,3) have "False" using assms(1) unfolding IsLinOrder_def antisym_def by auto
      }
      moreover
      {
        assume "V\<in>{LeftRayX(X,r,b). b\<in>X}"
        then obtain b where b:"V=LeftRayX(X,r,b)" "b\<in>X" by auto
        note a1 moreover
        from V(1) b(1) have a2:"\<langle>?max,b\<rangle>\<in>r""?max\<noteq>b" unfolding LeftRayX_def by auto
        ultimately have "\<langle>v,b\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def trans_def by blast moreover
        {
          assume "b=v"
          with a1 a2(1) have "b=?max" using assms(1) unfolding IsLinOrder_def antisym_def by auto
          with a2(2) have "False" by auto
        }
        ultimately have "False" using V(2) b(1) unfolding LeftRayX_def using \<open>v\<in>X-U\<close> by auto
      }
      moreover
      {
        assume "V\<in>{IntervalX(X,r,b,c). \<langle>b,c\<rangle>\<in>X\<times>X}"
        then obtain b c where b:"V=IntervalX(X,r,b,c)" "b\<in>X""c\<in>X" by auto
        from b V(1) have m:"\<langle>?max,c\<rangle>\<in>r""\<langle>b,?max\<rangle>\<in>r""?max\<noteq>b" "?max\<noteq>c" unfolding IntervalX_def Interval_def by auto  
        {
          assume A:"\<langle>v,b\<rangle>\<in>r"
          from m obtain z where z:"\<langle>z,?max\<rangle>\<in>r" "\<langle>b,z\<rangle>\<in>r""z\<in>X-{b,?max}" using assms(4) unfolding IsDense_def
            using b(2) V(1,2) \<open>U\<subseteq>X\<close> by blast
          from z(1) have "\<langle>z,c\<rangle>\<in>r" using m(1) assms(1) unfolding IsLinOrder_def trans_def
            by fast
          with z(2) have "z\<in>IntervalX(X,r,b,c)\<or>z=c" using z(3) unfolding IntervalX_def
            Interval_def by auto
          then have "z\<in>IntervalX(X,r,b,c)" using m(1) z(1,3) using assms(1) unfolding IsLinOrder_def
            antisym_def by auto
          with b(1) V(2) have "z\<in>U" by auto moreover
          from A z(2) have "\<langle>v,z\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def trans_def by fast
          moreover have "z\<noteq>v" using A z(2,3) assms(1) unfolding IsLinOrder_def antisym_def by auto
          ultimately have "z\<in>U\<inter>RightRayX(X,r,v)" unfolding RightRayX_def using z(3) by auto
          then have "?max\<in>r-``{z}" using Order_ZF_4_L3(1)[OF _ Hmax] assms(1) unfolding Infimum_def IsLinOrder_def
            by auto
          then have "\<langle>?max,z\<rangle>\<in>r" by auto
          with z(1,3) have "False" using assms(1) unfolding IsLinOrder_def antisym_def by auto
        }
        then have vc:"\<langle>b,v\<rangle>\<in>r""v\<noteq>b" using assms(1) unfolding IsLinOrder_def IsTotal_def using \<open>v\<in>X-U\<close>
          b(2) by auto
        {
          assume "?max=v"
          with V(2,1) \<open>v\<in>X-U\<close> have "False" by auto
        }
        then have "v\<noteq>?max" by auto moreover
        note a1 moreover
        have "?max\<in>X" using V(1,2) \<open>U\<subseteq>X\<close> by auto
        moreover have "v\<in>X" using \<open>v\<in>X-U\<close> by auto
        ultimately obtain z where z:"\<langle>v,z\<rangle>\<in>r""\<langle>z,?max\<rangle>\<in>r""z\<in>X-{v,?max}" using assms(4) unfolding IsDense_def
          by auto
        from z(1) vc(1) have zc:"\<langle>b,z\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def trans_def
          by fast moreover
        from m(1) z(2) have "\<langle>z,c\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def trans_def
          by fast ultimately
        have "z\<in>Interval(r,b,c)" using Order_ZF_2_L1B by auto moreover
        {
          assume "z=b"
          then have "False" using z(1) vc using assms(1) unfolding IsLinOrder_def antisym_def
            by fast
        }
        then have "z\<noteq>b" by auto moreover
        {
          assume "z=c"
          then have "z=?max" using m(1) z(2) using assms(1) unfolding IsLinOrder_def
            antisym_def by auto
          with z(3) have "False" by auto
        }
        then have "z\<noteq>c" by auto moreover
        have "z\<in>X" using z(3) by auto ultimately
        have "z\<in>IntervalX(X,r,b,c)" unfolding IntervalX_def by auto
        then have "z\<in>V" using b(1) by auto
        then have "z\<in>U" using V(2) by auto moreover
        from z(1,3) have "z\<in>RightRayX(X,r,v)" unfolding RightRayX_def by auto ultimately
        have "z\<in>U\<inter>RightRayX(X,r,v)" by auto
        then have "?max\<in>r-``{z}" using Order_ZF_4_L3(1)[OF _ Hmax] assms(1) unfolding Infimum_def IsLinOrder_def
          by auto
        then have "\<langle>?max,z\<rangle>\<in>r" by auto
        with z(2,3) have "False" using assms(1) unfolding IsLinOrder_def antisym_def by auto
      }
      ultimately have "False" using V(3) by auto
    }
    then have ass:"?max\<in>X-U" using a1 assms(3) by auto
    then obtain V where V:"?max\<in>V""V\<subseteq>X-U"
      "V\<in>{IntervalX(X,r,b,c). \<langle>b,c\<rangle>\<in>X\<times>X}\<union>{LeftRayX(X,r,b). b\<in>X}\<union>{RightRayX(X,r,b). b\<in>X}" using point_open_base_neigh
      [OF Ordtopology_is_a_topology(2)[OF assms(1)] \<open>X-U\<in>(OrdTopology X r)\<close> ass] by blast
    {
      assume "V\<in>{IntervalX(X,r,b,c). \<langle>b,c\<rangle>\<in>X\<times>X}"
      then obtain b c where b:"V=IntervalX(X,r,b,c)""b\<in>X""c\<in>X" by auto
      from b V(1) have m:"\<langle>?max,c\<rangle>\<in>r""\<langle>b,?max\<rangle>\<in>r""?max\<noteq>b" "?max\<noteq>c" unfolding IntervalX_def Interval_def by auto  
      {
        fix x assume A:"x\<in>U\<inter>RightRayX(X,r,v)"
        then have "\<langle>v,x\<rangle>\<in>r""x\<in>U" unfolding RightRayX_def by auto
        then have "x\<notin>V" using V(2) by auto
        then have "x\<notin>Interval(r, b, c) \<inter> X\<or>x=b\<or>x=c" using b(1) unfolding IntervalX_def by auto
        then have "(\<langle>b,x\<rangle>\<notin>r\<or>\<langle>x,c\<rangle>\<notin>r)\<or>x=b\<or>x=c""x\<in>X" using Order_ZF_2_L1B \<open>x\<in>U\<close>\<open>U\<subseteq>X\<close> by auto
        then have "(\<langle>x,b\<rangle>\<in>r\<or>\<langle>c,x\<rangle>\<in>r)\<or>x=b\<or>x=c" using assms(1) unfolding IsLinOrder_def IsTotal_def
          using b(2,3) by auto
        then have "(\<langle>x,b\<rangle>\<in>r\<or>\<langle>c,x\<rangle>\<in>r)" using assms(1) unfolding IsLinOrder_def using total_is_refl
          unfolding refl_def using b(2,3) by auto moreover
        from A have "\<langle>?max,x\<rangle>\<in>r" using Order_ZF_4_L3(1)[OF _ Hmax] assms(1) unfolding Infimum_def IsLinOrder_def
          by auto
        ultimately have "(\<langle>?max,b\<rangle>\<in>r\<or>\<langle>c,x\<rangle>\<in>r)" using assms(1) unfolding IsLinOrder_def trans_def
          by fast
        with m(2) have "(?max=b\<or>\<langle>c,x\<rangle>\<in>r)" using assms(1) unfolding IsLinOrder_def antisym_def by auto
        with m(3) have "\<langle>c,x\<rangle>\<in>r" by auto
      }
      then have "\<langle>c,?max\<rangle>\<in>r" using Order_ZF_5_L4[OF _ nE Hmax] assms(1) unfolding IsLinOrder_def by auto
      with m(1,4) have "False" using assms(1) unfolding IsLinOrder_def antisym_def by auto
    }
    moreover
    {
      assume "V\<in>{RightRayX(X,r,b). b\<in>X}"
      then obtain b where b:"V=RightRayX(X,r,b)" "b\<in>X" by auto
      from b V(1) have m:"\<langle>b,?max\<rangle>\<in>r""?max\<noteq>b" unfolding RightRayX_def by auto
      {
        fix x assume A:"x\<in>U\<inter>RightRayX(X,r,v)"
        then have "\<langle>v,x\<rangle>\<in>r""x\<in>U" unfolding RightRayX_def by auto
        then have "x\<notin>V" using V(2) by auto
        then have "x\<notin>RightRayX(X,r, b)" using b(1) by auto
        then have "(\<langle>b,x\<rangle>\<notin>r\<or>x=b)""x\<in>X" unfolding RightRayX_def using \<open>x\<in>U\<close>\<open>U\<subseteq>X\<close> by auto
        then have "\<langle>x,b\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def using total_is_refl unfolding
          refl_def unfolding IsTotal_def using b(2) by auto moreover
        from A have "\<langle>?max,x\<rangle>\<in>r" using Order_ZF_4_L3(1)[OF _ Hmax] assms(1) unfolding Infimum_def IsLinOrder_def
          by auto ultimately
        have "\<langle>?max,b\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def trans_def by fast
        with m have "False" using assms(1) unfolding IsLinOrder_def antisym_def by auto
      }
      then have "False" using nE by auto
    } moreover
    {
       assume "V\<in>{LeftRayX(X,r,b). b\<in>X}"
      then obtain b where b:"V=LeftRayX(X,r,b)" "b\<in>X" by auto
      from b V(1) have m:"\<langle>?max,b\<rangle>\<in>r""?max\<noteq>b" unfolding LeftRayX_def by auto
      {
        fix x assume A:"x\<in>U\<inter>RightRayX(X,r,v)"
        then have "\<langle>v,x\<rangle>\<in>r""x\<in>U" unfolding RightRayX_def by auto
        then have "x\<notin>V" using V(2) by auto
        then have "x\<notin>LeftRayX(X,r, b)" using b(1) by auto
        then have "(\<langle>x,b\<rangle>\<notin>r\<or>x=b)""x\<in>X" unfolding LeftRayX_def using \<open>x\<in>U\<close>\<open>U\<subseteq>X\<close> by auto
        then have "\<langle>b,x\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def using total_is_refl unfolding
          refl_def unfolding IsTotal_def using b(2) by auto
        then have "b\<in>r-``{x}" by auto
      }
      with nE have "b\<in>(\<Inter>c\<in>U\<inter>RightRayX(X,r,v). r-``{c})" by auto
      then have "\<langle>b,?max\<rangle>\<in>r" unfolding Infimum_def using Order_ZF_4_L3(2)[OF _ Hmax] assms(1)
        unfolding IsLinOrder_def by auto
      with m have "False" using assms(1) unfolding IsLinOrder_def antisym_def by auto
    }
    moreover note V(3)
    ultimately have "False" by auto
  } 
  then show ?thesis by auto
qed

subsection\<open>Numerability axioms\<close>

text\<open>A $\kappa$-separable order topology is in relation with order density.\<close>

text\<open>If an order topology has a subset $A$ which is topologically
dense, then that subset is weakly order-dense in $X$.\<close>

lemma dense_top_imp_Wdense_ord:
  assumes "IsLinOrder(X,r)" "Closure(A,OrdTopology X r)=X" "A\<subseteq>X" "\<exists>x y. x \<noteq> y \<and> x \<in> X \<and> y \<in> X"
  shows "A{is weakly dense in}X{with respect to}r"
proof-
  {
    fix r1 r2 assume "r1\<in>X""r2\<in>X""r1\<noteq>r2" "\<langle>r1,r2\<rangle>\<in>r"
    then have "IntervalX(X,r,r1,r2)\<in>{IntervalX(X, r, b, c) . \<langle>b,c\<rangle> \<in> X \<times> X} \<union> {LeftRayX(X, r, b) . b \<in> X} \<union>
      {RightRayX(X, r, b) . b \<in> X}" by auto
    then have P:"IntervalX(X,r,r1,r2)\<in>(OrdTopology X r)" using base_sets_open[OF Ordtopology_is_a_topology(2)[OF assms(1)]]
      by auto
    have "IntervalX(X,r,r1,r2)\<subseteq>X" unfolding IntervalX_def by auto
    then have int:"Closure(A,OrdTopology X r)\<inter>IntervalX(X,r,r1,r2)=IntervalX(X,r,r1,r2)" using assms(2) by auto
    {
      assume "IntervalX(X,r,r1,r2)\<noteq>0"
      then have "A\<inter>(IntervalX(X,r,r1,r2))\<noteq>0" using topology0.cl_inter_neigh[OF topology0_ordtopology[OF assms(1)] _ P , of "A"]
        using assms(3) union_ordtopology[OF assms(1,4)] int by auto
    }
    then have "(\<exists>z\<in>A-{r1,r2}. \<langle>r1,z\<rangle>\<in>r\<and>\<langle>z,r2\<rangle>\<in>r)\<or>IntervalX(X,r,r1,r2)=0" unfolding IntervalX_def
      Interval_def by auto
  }
  then show ?thesis unfolding IsWeaklyDenseSub_def by auto
qed

text\<open>Conversely, a weakly order-dense set is topologically dense if it is also considered
that: if there is a maximum or a minimum elements whose singletons are open, this points
have to be in $A$. In conclusion, weakly order-density is a property closed to topological density.\<close>

text\<open>Another way to see this: Consider a weakly order-dense set $A$:
\begin{itemize}
\item If $X$ has a maximum and a minimum and $\{min,max\}$ is open: $A$ is topologically dense in $X\setminus\{min,max\}$, where $min$ is the minimum in $X$ and $max$ is the maximum in $X$.
\item If $X$ has a maximum, $\{max\}$ is open and $X$ has no minimum
  or $\{min\}$ isn't open: $A$ is topologically dense in $X\setminus\{max\}$, where $max$ is the maximum in $X$.
\item If $X$ has a minimum, $\{min\}$ is open and $X$ has no maximum
  or $\{max\}$ isn't open $A$ is topologically dense in $X\setminus\{min\}$, where $min$ is the minimum in $X$.
\item If $X$ has no minimum or maximum, or $\{min,max\}$ has no proper open sets: $A$ is topologically dense in $X$.
\end{itemize}
\<close>

lemma Wdense_ord_imp_dense_top:
  assumes "IsLinOrder(X,r)" "A{is weakly dense in}X{with respect to}r" "A\<subseteq>X" "\<exists>x y. x \<noteq> y \<and> x \<in> X \<and> y \<in> X"
    "HasAminimum(r,X)\<longrightarrow>{Minimum(r,X)}\<in>(OrdTopology X r)\<longrightarrow>Minimum(r,X)\<in>A"
    "HasAmaximum(r,X)\<longrightarrow>{Maximum(r,X)}\<in>(OrdTopology X r)\<longrightarrow>Maximum(r,X)\<in>A"
  shows "Closure(A,OrdTopology X r)=X"
proof-
  {
    fix x assume "x\<in>X"
  {
    fix U assume ass:"x\<in>U""U\<in>(OrdTopology X r)"
    then have "\<exists>V\<in>{IntervalX(X, r, b, c) . \<langle>b,c\<rangle> \<in> X \<times> X} \<union> {LeftRayX(X, r, b) . b \<in> X} \<union> {RightRayX(X, r, b) . b \<in> X} . V\<subseteq>U\<and>x\<in>V"
      using point_open_base_neigh[OF Ordtopology_is_a_topology(2)[OF assms(1)]] by auto
    then obtain V where V:"V\<in>{IntervalX(X, r, b, c) . \<langle>b,c\<rangle> \<in> X \<times> X} \<union> {LeftRayX(X, r, b) . b \<in> X} \<union> {RightRayX(X, r, b) . b \<in> X}" "V\<subseteq>U" "x\<in>V"
      by blast
    note V(1) moreover
    {
      assume "V\<in>{IntervalX(X, r, b, c) . \<langle>b,c\<rangle> \<in> X \<times> X}"
      then obtain b c where b:"b\<in>X""c\<in>X""V=IntervalX(X, r, b, c)" by auto
      with V(3) have x:"\<langle>b,x\<rangle>\<in>r" "\<langle>x,c\<rangle>\<in>r" "x\<noteq>b" "x\<noteq>c" unfolding IntervalX_def Interval_def by auto
      then have "\<langle>b,c\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def trans_def by fast
      moreover from x(1-3) have "b\<noteq>c" using assms(1) unfolding IsLinOrder_def antisym_def by fast
      moreover note assms(2) b V(3)
      ultimately have "\<exists>z\<in>A-{b,c}. \<langle>b,z\<rangle>\<in>r\<and>\<langle>z,c\<rangle>\<in>r" unfolding IsWeaklyDenseSub_def by auto
      then obtain z where "z\<in>A""z\<noteq>b""z\<noteq>c""\<langle>b,z\<rangle>\<in>r""\<langle>z,c\<rangle>\<in>r" by auto
      with assms(3) have "z\<in>A""z\<in>IntervalX(X, r, b, c)" unfolding IntervalX_def Interval_def by auto
      then have "A\<inter>U\<noteq>0" using V(2) b(3) by auto
    }
    moreover
    {
      assume "V\<in>{RightRayX(X, r, b) . b \<in> X}"
      then obtain b where b:"b\<in>X""V=RightRayX(X, r, b)" by auto
      with V(3) have x:"\<langle>b,x\<rangle>\<in>r" "b\<noteq>x" unfolding RightRayX_def by auto moreover
      note b(1) moreover
      have "U\<subseteq>\<Union>(OrdTopology X r)" using ass(2) by auto
      then have "U\<subseteq>X" using union_ordtopology[OF assms(1,4)] by auto
      then have "x\<in>X" using ass(1) by auto moreover
      note assms(2) ultimately
      have disj:"(\<exists>z\<in>A-{b,x}. \<langle>b,z\<rangle>\<in>r\<and>\<langle>z,x\<rangle>\<in>r)\<or> IntervalX(X, r, b, x) = 0" unfolding IsWeaklyDenseSub_def by auto
      {
        assume B:"IntervalX(X, r, b, x) = 0"
        {
          assume "\<exists>y\<in>X. \<langle>x,y\<rangle>\<in>r \<and> x\<noteq>y"
          then obtain y where y:"y\<in>X""\<langle>x,y\<rangle>\<in>r" "x\<noteq>y" by auto
          with x have "x\<in>IntervalX(X,r,b,y)" unfolding IntervalX_def Interval_def
            using \<open>x\<in>X\<close> by auto moreover
          have "\<langle>b,y\<rangle>\<in>r" using y(2) x(1) assms(1) unfolding IsLinOrder_def trans_def by fast
          moreover have "b\<noteq>y" using y(2,3) x(1) assms(1) unfolding IsLinOrder_def antisym_def by fast
          ultimately
          have "(\<exists>z\<in>A-{b,y}. \<langle>b,z\<rangle>\<in>r\<and>\<langle>z,y\<rangle>\<in>r)" using assms(2) unfolding IsWeaklyDenseSub_def
            using y(1) b(1) by auto
          then obtain z where "z\<in>A""\<langle>b,z\<rangle>\<in>r""b\<noteq>z" by auto
          then have "z\<in>A\<inter>V" using b(2) unfolding RightRayX_def using assms(3) by auto
          then have "z\<in>A\<inter>U" using V(2) by auto
          then have "A\<inter>U\<noteq>0" by auto
        }
        moreover
        {
          assume R:"\<forall>y\<in>X. \<langle>x,y\<rangle>\<in>r\<longrightarrow>x=y"
          {
            fix y assume "y\<in>RightRayX(X,r,b)"
            then have y:"\<langle>b,y\<rangle>\<in>r" "y\<in>X-{b}" unfolding RightRayX_def by auto
            {
              assume A:"y\<noteq>x"
              then have "\<langle>x,y\<rangle>\<notin>r" using R y(2) by auto
              then have "\<langle>y,x\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def IsTotal_def
                using \<open>x\<in>X\<close> y(2) by auto
              with A y have "y\<in>IntervalX(X,r,b,x)" unfolding IntervalX_def Interval_def
                by auto
              then have "False" using B by auto
            }
            then have "y=x" by auto
          }
          then have "RightRayX(X,r,b)={x}" using V(3) b(2) by blast
          moreover
          {
            fix t assume T:"t\<in>X"
            {
              assume "t=x"
              then have "\<langle>t,x\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def
                using Order_ZF_1_L1 T by auto
            }
            moreover
            {
              assume "t\<noteq>x"
              then have "\<langle>x,t\<rangle>\<notin>r" using R T by auto
              then have "\<langle>t,x\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def IsTotal_def
                using T \<open>x\<in>X\<close> by auto
            }
            ultimately have "\<langle>t,x\<rangle>\<in>r" by auto
          }
          with \<open>x\<in>X\<close> have HM:"HasAmaximum(r,X)" unfolding HasAmaximum_def by auto
          then have "Maximum(r,X)\<in>X""\<forall>t\<in>X. \<langle>t,Maximum(r,X)\<rangle>\<in>r" using Order_ZF_4_L3 assms(1) unfolding IsLinOrder_def
            by auto
          with R \<open>x\<in>X\<close> have xm:"x=Maximum(r,X)" by auto
          moreover note b(2)
          ultimately have "V={Maximum(r,X)}" by auto
          then have "{Maximum(r,X)}\<in>(OrdTopology X r)" using base_sets_open[OF Ordtopology_is_a_topology(2)[OF assms(1)]]
            V(1) by auto
          with HM have "Maximum(r,X)\<in>A" using assms(6) by auto
          with xm have "x\<in>A" by auto
          with V(2,3) have "A\<inter>U\<noteq>0" by auto
        }
        ultimately have "A\<inter>U\<noteq>0" by auto
      }
      moreover
      {
        assume "IntervalX(X, r, b, x) \<noteq> 0"
        with disj have "\<exists>z\<in>A-{b,x}. \<langle>b,z\<rangle>\<in>r\<and>\<langle>z,x\<rangle>\<in>r" by auto
        then obtain z where "z\<in>A""z\<noteq>b""\<langle>b,z\<rangle>\<in>r" by auto
        then have "z\<in>A""z\<in>RightRayX(X,r,b)" unfolding RightRayX_def using assms(3) by auto
        then have "z\<in>A\<inter>U" using V(2) b(2) by auto
        then have "A\<inter>U\<noteq>0" by auto
      }
      ultimately have "A\<inter>U\<noteq>0" by auto
    }
    moreover
    {
      assume "V\<in>{LeftRayX(X, r, b) . b \<in> X}"
      then obtain b where b:"b\<in>X""V=LeftRayX(X, r, b)" by auto
      with V(3) have x:"\<langle>x,b\<rangle>\<in>r" "b\<noteq>x" unfolding LeftRayX_def by auto moreover
      note b(1) moreover
      have "U\<subseteq>\<Union>(OrdTopology X r)" using ass(2) by auto
      then have "U\<subseteq>X" using union_ordtopology[OF assms(1,4)] by auto
      then have "x\<in>X" using ass(1) by auto moreover
      note assms(2) ultimately
      have disj:"(\<exists>z\<in>A-{b,x}. \<langle>x,z\<rangle>\<in>r\<and>\<langle>z,b\<rangle>\<in>r)\<or> IntervalX(X, r, x, b) = 0" unfolding IsWeaklyDenseSub_def by auto
      {
        assume B:"IntervalX(X, r, x, b) = 0"
        {
          assume "\<exists>y\<in>X. \<langle>y,x\<rangle>\<in>r \<and> x\<noteq>y"
          then obtain y where y:"y\<in>X""\<langle>y,x\<rangle>\<in>r" "x\<noteq>y" by auto
          with x have "x\<in>IntervalX(X,r,y,b)" unfolding IntervalX_def Interval_def
            using \<open>x\<in>X\<close> by auto moreover
          have "\<langle>y,b\<rangle>\<in>r" using y(2) x(1) assms(1) unfolding IsLinOrder_def trans_def by fast
          moreover have "b\<noteq>y" using y(2,3) x(1) assms(1) unfolding IsLinOrder_def antisym_def by fast
          ultimately
          have "(\<exists>z\<in>A-{b,y}. \<langle>y,z\<rangle>\<in>r\<and>\<langle>z,b\<rangle>\<in>r)" using assms(2) unfolding IsWeaklyDenseSub_def
            using y(1) b(1) by auto
          then obtain z where "z\<in>A""\<langle>z,b\<rangle>\<in>r""b\<noteq>z" by auto
          then have "z\<in>A\<inter>V" using b(2) unfolding LeftRayX_def using assms(3) by auto
          then have "z\<in>A\<inter>U" using V(2) by auto
          then have "A\<inter>U\<noteq>0" by auto
        }
        moreover
        {
          assume R:"\<forall>y\<in>X. \<langle>y,x\<rangle>\<in>r\<longrightarrow>x=y"
          {
            fix y assume "y\<in>LeftRayX(X,r,b)"
            then have y:"\<langle>y,b\<rangle>\<in>r" "y\<in>X-{b}" unfolding LeftRayX_def by auto
            {
              assume A:"y\<noteq>x"
              then have "\<langle>y,x\<rangle>\<notin>r" using R y(2) by auto
              then have "\<langle>x,y\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def IsTotal_def
                using \<open>x\<in>X\<close> y(2) by auto
              with A y have "y\<in>IntervalX(X,r,x,b)" unfolding IntervalX_def Interval_def
                by auto
              then have "False" using B by auto
            }
            then have "y=x" by auto
          }
          then have "LeftRayX(X,r,b)={x}" using V(3) b(2) by blast
          moreover
          {
            fix t assume T:"t\<in>X"
            {
              assume "t=x"
              then have "\<langle>x,t\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def
                using Order_ZF_1_L1 T by auto
            }
            moreover
            {
              assume "t\<noteq>x"
              then have "\<langle>t,x\<rangle>\<notin>r" using R T by auto
              then have "\<langle>x,t\<rangle>\<in>r" using assms(1) unfolding IsLinOrder_def IsTotal_def
                using T \<open>x\<in>X\<close> by auto
            }
            ultimately have "\<langle>x,t\<rangle>\<in>r" by auto
          }
          with \<open>x\<in>X\<close> have HM:"HasAminimum(r,X)" unfolding HasAminimum_def by auto
          then have "Minimum(r,X)\<in>X""\<forall>t\<in>X. \<langle>Minimum(r,X),t\<rangle>\<in>r" using Order_ZF_4_L4 assms(1) unfolding IsLinOrder_def
            by auto
          with R \<open>x\<in>X\<close> have xm:"x=Minimum(r,X)" by auto
          moreover note b(2)
          ultimately have "V={Minimum(r,X)}" by auto
          then have "{Minimum(r,X)}\<in>(OrdTopology X r)" using base_sets_open[OF Ordtopology_is_a_topology(2)[OF assms(1)]]
            V(1) by auto
          with HM have "Minimum(r,X)\<in>A" using assms(5) by auto
          with xm have "x\<in>A" by auto
          with V(2,3) have "A\<inter>U\<noteq>0" by auto
        }
        ultimately have "A\<inter>U\<noteq>0" by auto
      }
      moreover
      {
        assume "IntervalX(X, r, x, b) \<noteq> 0"
        with disj have "\<exists>z\<in>A-{b,x}. \<langle>x,z\<rangle>\<in>r\<and>\<langle>z,b\<rangle>\<in>r" by auto
        then obtain z where "z\<in>A""z\<noteq>b""\<langle>z,b\<rangle>\<in>r" by auto
        then have "z\<in>A""z\<in>LeftRayX(X,r,b)" unfolding LeftRayX_def using assms(3) by auto
        then have "z\<in>A\<inter>U" using V(2) b(2) by auto
        then have "A\<inter>U\<noteq>0" by auto
      }
      ultimately have "A\<inter>U\<noteq>0" by auto
    }
    ultimately have "A\<inter>U\<noteq>0" by auto
  }
  then have "\<forall>U\<in>(OrdTopology X r). x\<in>U \<longrightarrow> U\<inter>A\<noteq>0" by auto
  moreover note \<open>x\<in>X\<close> moreover
  note assms(3) topology0.inter_neigh_cl[OF topology0_ordtopology[OF assms(1)]]
  union_ordtopology[OF assms(1,4)] ultimately have "x\<in>Closure(A,OrdTopology X r)"
    by auto
  }
  then have "X\<subseteq>Closure(A,OrdTopology X r)" by auto
  with topology0.Top_3_L11(1)[OF topology0_ordtopology[OF assms(1)]]
    assms(3) union_ordtopology[OF assms(1,4)] show ?thesis by auto
qed

text\<open>The conclusion is that an order topology is $\kappa$-separable
iff there is a set $A$ with cardinality strictly less than $\kappa$
which is weakly-dense in $X$.\<close>

theorem separable_imp_wdense:
  assumes "(OrdTopology X r){is separable of cardinal}Q" "\<exists>x y. x \<noteq> y \<and> x \<in> X \<and> y \<in> X"
    "IsLinOrder(X,r)"
  shows "\<exists>A\<in>Pow(X). A\<prec>Q \<and> (A{is weakly dense in}X{with respect to}r)"
proof-
  from assms obtain U where "U\<in>Pow(\<Union>(OrdTopology X r))" "Closure(U,OrdTopology X r)=\<Union>(OrdTopology X r)" "U\<prec>Q"
    unfolding IsSeparableOfCard_def by auto
  then have "U\<in>Pow(X)" "Closure(U,OrdTopology X r)=X" "U\<prec>Q" using union_ordtopology[OF assms(3,2)]
    by auto
  with dense_top_imp_Wdense_ord[OF assms(3) _ _ assms(2)] show ?thesis by auto
qed

theorem wdense_imp_separable:
  assumes "\<exists>x y. x \<noteq> y \<and> x \<in> X \<and> y \<in> X" "(A{is weakly dense in}X{with respect to}r)"
    "IsLinOrder(X,r)" "A\<prec>Q" "InfCard(Q)" "A\<subseteq>X"
  shows "(OrdTopology X r){is separable of cardinal}Q"
proof-
  {
    assume Hmin:"HasAmaximum(r,X)"
    then have MaxX:"Maximum(r,X)\<in>X" using Order_ZF_4_L3(1) assms(3) unfolding IsLinOrder_def
      by auto
    {
      assume HMax:"HasAminimum(r,X)"
      then have MinX:"Minimum(r,X)\<in>X" using Order_ZF_4_L4(1) assms(3) unfolding IsLinOrder_def
        by auto
      let ?A="A \<union>{Maximum(r,X),Minimum(r,X)}"
      have "Finite({Maximum(r,X),Minimum(r,X)})" by auto
      then have "{Maximum(r,X),Minimum(r,X)}\<prec>nat" using n_lesspoll_nat
        unfolding Finite_def using eq_lesspoll_trans by auto
      moreover
      from assms(5) have "nat\<prec>Q\<or>nat=Q" unfolding InfCard_def
        using lt_Card_imp_lesspoll[of "Q""nat"] unfolding lt_def succ_def
        using Card_is_Ord[of "Q"] by auto
      ultimately have "{Maximum(r,X),Minimum(r,X)}\<prec>Q" using lesspoll_trans by auto
      with assms(4,5) have C:"?A\<prec>Q" using less_less_imp_un_less
        by auto
      have WeakDense:"?A{is weakly dense in}X{with respect to}r" using assms(2) unfolding
        IsWeaklyDenseSub_def by auto
      from MaxX MinX assms(6) have S:"?A\<subseteq>X" by auto
      then have "Closure(?A,OrdTopology X r)=X" using Wdense_ord_imp_dense_top
        [OF assms(3) WeakDense _ assms(1)] by auto
      then have ?thesis unfolding IsSeparableOfCard_def using union_ordtopology[OF assms(3,1)]
        S C by auto
    }
    moreover
    {
      assume nmin:"\<not>HasAminimum(r,X)"
       let ?A="A \<union>{Maximum(r,X)}"
      have "Finite({Maximum(r,X)})" by auto
      then have "{Maximum(r,X)}\<prec>nat" using n_lesspoll_nat
        unfolding Finite_def using eq_lesspoll_trans by auto
      moreover
      from assms(5) have "nat\<prec>Q\<or>nat=Q" unfolding InfCard_def
        using lt_Card_imp_lesspoll[of "Q""nat"] unfolding lt_def succ_def
        using Card_is_Ord[of "Q"] by auto
      ultimately have "{Maximum(r,X)}\<prec>Q" using lesspoll_trans by auto
      with assms(4,5) have C:"?A\<prec>Q" using less_less_imp_un_less
        by auto
      have WeakDense:"?A{is weakly dense in}X{with respect to}r" using assms(2) unfolding
        IsWeaklyDenseSub_def by auto
      from MaxX assms(6) have S:"?A\<subseteq>X" by auto
      then have "Closure(?A,OrdTopology X r)=X" using Wdense_ord_imp_dense_top
        [OF assms(3) WeakDense _ assms(1)] nmin by auto
      then have ?thesis unfolding IsSeparableOfCard_def using union_ordtopology[OF assms(3,1)]
        S C by auto
    }
    ultimately have ?thesis by auto
  }
  moreover
  {
    assume nmax:"\<not>HasAmaximum(r,X)"
    {
      assume HMin:"HasAminimum(r,X)"
      then have MinX:"Minimum(r,X)\<in>X" using Order_ZF_4_L4(1) assms(3) unfolding IsLinOrder_def
        by auto
      let ?A="A \<union>{Minimum(r,X)}"
      have "Finite({Minimum(r,X)})" by auto
      then have "{Minimum(r,X)}\<prec>nat" using n_lesspoll_nat
        unfolding Finite_def using eq_lesspoll_trans by auto
      moreover
      from assms(5) have "nat\<prec>Q\<or>nat=Q" unfolding InfCard_def
        using lt_Card_imp_lesspoll[of "Q""nat"] unfolding lt_def succ_def
        using Card_is_Ord[of "Q"] by auto
      ultimately have "{Minimum(r,X)}\<prec>Q" using lesspoll_trans by auto
      with assms(4,5) have C:"?A\<prec>Q" using less_less_imp_un_less
        by auto
      have WeakDense:"?A{is weakly dense in}X{with respect to}r" using assms(2) unfolding
        IsWeaklyDenseSub_def by auto
      from MinX assms(6) have S:"?A\<subseteq>X" by auto
      then have "Closure(?A,OrdTopology X r)=X" using Wdense_ord_imp_dense_top
        [OF assms(3) WeakDense _ assms(1)] nmax by auto
      then have ?thesis unfolding IsSeparableOfCard_def using union_ordtopology[OF assms(3,1)]
        S C by auto
    }
    moreover
    {
      assume nmin:"\<not>HasAminimum(r,X)"
      let ?A="A"
      from assms(4,5) have C:"?A\<prec>Q" by auto
      have WeakDense:"?A{is weakly dense in}X{with respect to}r" using assms(2) unfolding
        IsWeaklyDenseSub_def by auto
      from assms(6) have S:"?A\<subseteq>X" by auto
      then have "Closure(?A,OrdTopology X r)=X" using Wdense_ord_imp_dense_top
        [OF assms(3) WeakDense _ assms(1)] nmin nmax by auto
      then have ?thesis unfolding IsSeparableOfCard_def using union_ordtopology[OF assms(3,1)]
        S C by auto
    }
    ultimately have ?thesis by auto
  }
  ultimately show ?thesis by auto
qed


end

