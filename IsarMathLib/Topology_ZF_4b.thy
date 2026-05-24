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

section \<open>Relation between nets and filters\<close>

theory Topology_ZF_4b imports Topology_ZF_4
begin

text\<open>This theory continues \<open>Topology_ZF_4\<close> with results relating the net and filter convergence notions introduced there.\<close>

subsection\<open>Relation between nets and filters\<close>

text\<open>In this section we show that filters do not generalize nets, but still nets and filters
  are in a way equivalent as far as convergence is considered.\<close>

text\<open>Let's build now a net from a filter, such that both converge to the same points.\<close>

definition
  NetOfFilter ("Net(_)" 40) where
  "\<FF> {is a filter on} \<Union>\<FF> \<Longrightarrow> Net(\<FF>) \<equiv> 
    \<langle>{\<langle>A,fst(A)\<rangle>. A\<in>{\<langle>x,F\<rangle>\<in>(\<Union>\<FF>)\<times>\<FF>. x\<in>F}},{\<langle>A,B\<rangle>\<in>{\<langle>x,F\<rangle>\<in>(\<Union>\<FF>)\<times>\<FF>. x\<in>F}\<times>{\<langle>x,F\<rangle>\<in>(\<Union>\<FF>)\<times>\<FF>. x\<in>F}. snd(B)\<subseteq>snd(A)}\<rangle>"

text\<open>Net of a filter is indeed a net.\<close>

theorem net_of_filter_is_net:
  assumes "\<FF> {is a filter on} X"
  shows "(Net(\<FF>)) {is a net on} X"
proof-
  from assms have "X\<in>\<FF>" "\<FF>\<subseteq>Pow(X)" using IsFilter_def by auto
  then have uu:"\<Union>\<FF>=X" by blast
  let ?f = "{\<langle>A,fst(A)\<rangle>. A\<in>{\<langle>x,F\<rangle>\<in>(\<Union>\<FF>)\<times>\<FF>. x\<in>F}}"
  let ?r = "{\<langle>A,B\<rangle>\<in>{\<langle>x,F\<rangle>\<in>(\<Union>\<FF>)\<times>\<FF>. x\<in>F}\<times>{\<langle>x,F\<rangle>\<in>(\<Union>\<FF>)\<times>\<FF>. x\<in>F}. snd(B)\<subseteq>snd(A)}"
  have "function(?f)" using function_def by auto
  moreover have "relation(?f)" using relation_def by auto
  ultimately  have "?f:domain(?f)\<rightarrow>range(?f)" using function_imp_Pi 
    by auto
  have dom:"domain(?f)={\<langle>x,F\<rangle>\<in>(\<Union>\<FF>)\<times>\<FF>. x\<in>F}" by auto
  have "range(?f)\<subseteq>\<Union>\<FF>" by auto
  with \<open>?f:domain(?f)\<rightarrow>range(?f)\<close> have "?f:domain(?f)\<rightarrow>\<Union>\<FF>" using fun_weaken_type by auto
  moreover
  {
    {
      fix t
      assume pp:"t\<in>domain(?f)"
      then have "snd(t)\<subseteq>snd(t)" by auto
      with dom pp have "\<langle>t,t\<rangle>\<in>?r" by auto
    }
    then have "refl(domain(?f),?r)" using refl_def by auto
    moreover
    {
      fix t1 t2 t3
      assume "\<langle>t1,t2\<rangle>\<in>?r" "\<langle>t2,t3\<rangle>\<in>?r"
      then have "snd(t3)\<subseteq>snd(t1)" "t1\<in>domain(?f)" "t3\<in>domain(?f)" using dom by auto
      then have "\<langle>t1,t3\<rangle>\<in>?r" by auto
    }
    then have "trans(?r)" using trans_def by auto
    moreover
    {
      fix x y
      assume as:"x\<in>domain(?f)""y\<in>domain(?f)"
      then have "snd(x)\<in>\<FF>" "snd(y)\<in>\<FF>" by auto
      then have p:"snd(x)\<inter>snd(y)\<in>\<FF>" using assms IsFilter_def by auto
      {
        assume "snd(x)\<inter>snd(y)=0"
        with p have "0\<in>\<FF>" by auto
        then have "False" using assms IsFilter_def by auto
      }
      then have "snd(x)\<inter>snd(y)\<noteq>0" by auto
      then obtain xy where "xy\<in>snd(x)\<inter>snd(y)" by auto
      then have "xy\<in>snd(x)\<inter>snd(y)" "\<langle>xy,snd(x)\<inter>snd(y)\<rangle>\<in>(\<Union>\<FF>)\<times>\<FF>" using p by auto
      then have "\<langle>xy,snd(x)\<inter>snd(y)\<rangle>\<in>{\<langle>x,F\<rangle>\<in>(\<Union>\<FF>)\<times>\<FF>. x\<in>F}" by auto
      with dom have d:"\<langle>xy,snd(x)\<inter>snd(y)\<rangle>\<in>domain(?f)" by auto
      with as have "\<langle>x,\<langle>xy,snd(x)\<inter>snd(y)\<rangle>\<rangle>\<in>?r \<and> \<langle>y,\<langle>xy,snd(x)\<inter>snd(y)\<rangle>\<rangle>\<in>?r" by auto
      with d have "\<exists>z\<in>domain(?f). \<langle>x,z\<rangle>\<in>?r \<and> \<langle>y,z\<rangle>\<in>?r"  by blast
    }
    then have "\<forall>x\<in>domain(?f). \<forall>y\<in>domain(?f). \<exists>z\<in>domain(?f). \<langle>x,z\<rangle>\<in>?r \<and> \<langle>y,z\<rangle>\<in>?r" by blast
    ultimately have "?r directs domain(?f)" using IsDirectedSet_def by blast
  }
  moreover
  {
    have p:"X\<in>\<FF>" and "0\<notin>\<FF>" using assms IsFilter_def by auto
    then have "X\<noteq>0" by auto
    then obtain q where "q\<in>X" by auto
    with p dom have "\<langle>q,X\<rangle>\<in>domain(?f)" by auto
    then have "domain(?f)\<noteq>0" by blast
  }
  ultimately have "\<langle>?f,?r\<rangle> {is a net on}\<Union>\<FF>" using IsNet_def by auto
  then show "(Net(\<FF>)) {is a net on} X" using NetOfFilter_def assms uu by auto
qed

text\<open>If a filter converges to some point then its net converges to the same point.\<close>
    
theorem (in topology0) filter_conver_net_of_filter_conver:
  assumes "\<FF> {is a filter on} \<Union>T" and "\<FF> \<rightarrow>\<^sub>F x"
  shows "(Net(\<FF>)) \<rightarrow>\<^sub>N x"
proof-
  from assms have "\<Union>T\<in>\<FF>" "\<FF>\<subseteq>Pow(\<Union>T)" using IsFilter_def by auto
  then have uu: "\<Union>\<FF>=\<Union>T" by blast
  from assms(1) have func: "fst(Net(\<FF>))={\<langle>A,fst(A)\<rangle>. A\<in>{\<langle>x,F\<rangle>\<in>(\<Union>\<FF>)\<times>\<FF>. x\<in>F}}"
    and dir: "snd(Net(\<FF>))={\<langle>A,B\<rangle>\<in>{\<langle>x,F\<rangle>\<in>(\<Union>\<FF>)\<times>\<FF>. x\<in>F}\<times>{\<langle>x,F\<rangle>\<in>(\<Union>\<FF>)\<times>\<FF>. x\<in>F}. snd(B)\<subseteq>snd(A)}"
    using NetOfFilter_def uu by auto
  then have dom_def: "domain(fst(Net(\<FF>)))={\<langle>x,F\<rangle>\<in>(\<Union>\<FF>)\<times>\<FF>. x\<in>F}" by auto
  from func have fun: "fst(Net(\<FF>)): {\<langle>x,F\<rangle>\<in>(\<Union>\<FF>)\<times>\<FF>. x\<in>F} \<rightarrow> (\<Union>\<FF>)"
    using ZF_fun_from_total by simp
  from assms(1) have NN: "(Net(\<FF>)) {is a net on}\<Union>T" using net_of_filter_is_net 
    by auto
  moreover from assms have "x\<in>\<Union>T" using FilterConverges_def 
    by auto
  moreover
  {
    fix U
    assume AS: "U\<in>Pow(\<Union>T)" "x\<in>int(U)"
    with assms have "U\<in>\<FF>" "x\<in>U" using Top_2_L1 FilterConverges_def by auto
    then have pp: "\<langle>x,U\<rangle>\<in>domain(fst(Net(\<FF>)))" using dom_def by auto
    {
      fix m
      assume ASS: "m\<in>domain(fst(Net(\<FF>)))" "\<langle>\<langle>x,U\<rangle>,m\<rangle>\<in>snd(Net(\<FF>))"
      from ASS(1) fun func have "fst(Net(\<FF>))`(m) = fst(m)" 
        using func1_1_L1 ZF_fun_from_tot_val by simp 
      with dir ASS have "fst(Net(\<FF>))`(m) \<in> U" using dom_def by auto    
    }
    then have "\<forall>m\<in>domain(fst(Net(\<FF>))). (\<langle>\<langle>x,U\<rangle>,m\<rangle>\<in>snd(Net(\<FF>)) \<longrightarrow> fst(Net(\<FF>))`m\<in>U)" by auto
    with pp have "\<exists>t\<in>domain(fst(Net(\<FF>))). \<forall>m\<in>domain(fst(Net(\<FF>))). (\<langle>t,m\<rangle>\<in>snd(Net(\<FF>)) \<longrightarrow> fst(Net(\<FF>))`m\<in>U)"
      by auto
  }
  then have "\<forall>U\<in>Pow(\<Union>T). 
      (x\<in>int(U) \<longrightarrow> (\<exists>t\<in>domain(fst(Net(\<FF>))). \<forall>m\<in>domain(fst(Net(\<FF>))). (\<langle>t,m\<rangle>\<in>snd(Net(\<FF>)) \<longrightarrow> fst(Net(\<FF>))`m\<in>U)))"
      by auto
  ultimately show ?thesis using NetConverges_def by auto
qed

text\<open>If a net converges to a point, then a filter also converges to a point.\<close>

theorem (in topology0) net_of_filter_conver_filter_conver:
  assumes "\<FF> {is a filter on}\<Union>T" and "(Net(\<FF>)) \<rightarrow>\<^sub>N x"
  shows "\<FF> \<rightarrow>\<^sub>F x"
proof-
  from assms have "\<Union>T\<in>\<FF>" "\<FF>\<subseteq>Pow(\<Union>T)" using IsFilter_def by auto
  then have uu: "\<Union>\<FF>=\<Union>T" by blast
  have "x\<in>\<Union>T" using assms NetConverges_def net_of_filter_is_net by auto
  moreover
  {
    fix U
    assume "U\<in>Pow(\<Union>T)" "x\<in>int(U)"
    then obtain t where t: "t\<in>domain(fst(Net(\<FF>)))" and 
      reg: "\<forall>m\<in>domain(fst(Net(\<FF>))). \<langle>t,m\<rangle>\<in>snd(Net(\<FF>)) \<longrightarrow> fst(Net(\<FF>))`m\<in>U"
        using assms net_of_filter_is_net NetConverges_def by blast
    with assms(1) uu obtain t1 t2 where t_def: "t=\<langle>t1,t2\<rangle>" and "t1\<in>t2" and tFF: "t2\<in>\<FF>" 
      using NetOfFilter_def by auto
    {
      fix s
      assume "s\<in>t2"
      then have "\<langle>s,t2\<rangle>\<in>{\<langle>q1,q2\<rangle>\<in>\<Union>\<FF>\<times>\<FF>. q1\<in>q2}" using tFF by auto
      moreover
      from assms(1) uu have "domain(fst(Net(\<FF>)))={\<langle>q1,q2\<rangle>\<in>\<Union>\<FF>\<times>\<FF>. q1\<in>q2}" using NetOfFilter_def
        by auto
      ultimately
      have tt: "\<langle>s,t2\<rangle>\<in>domain(fst(Net(\<FF>)))" by auto
      moreover
      from assms(1) uu t t_def tt have "\<langle>\<langle>t1,t2\<rangle>,\<langle>s,t2\<rangle>\<rangle>\<in>snd(Net(\<FF>))" using NetOfFilter_def
        by auto
      ultimately
      have "fst(Net(\<FF>))`\<langle>s,t2\<rangle>\<in>U" using reg t_def by auto
      moreover
      from assms(1) uu have "function(fst(Net(\<FF>)))" using NetOfFilter_def function_def
        by auto
      moreover
      from tt assms(1) uu have "\<langle>\<langle>s,t2\<rangle>,s\<rangle>\<in>fst(Net(\<FF>))" using NetOfFilter_def by auto
      ultimately
      have "s\<in>U" using NetOfFilter_def function_apply_equality by auto
    }
    then have "t2\<subseteq>U" by auto
    with tFF assms(1) \<open>U\<in>Pow(\<Union>T)\<close> have "U\<in>\<FF>" using IsFilter_def by auto
  }
  then have "{U\<in>Pow(\<Union>T). x\<in>int(U)} \<subseteq> \<FF>" by auto
  ultimately
  show ?thesis using FilterConverges_def assms(1) by auto
qed

text\<open>A filter converges to a point if and only if its net converges to the point.\<close>

theorem (in topology0) filter_conver_iff_net_of_filter_conver:
  assumes "\<FF> {is a filter on}\<Union>T"
  shows "(\<FF> \<rightarrow>\<^sub>F x) \<longleftrightarrow> ((Net(\<FF>)) \<rightarrow>\<^sub>N x)"
  using filter_conver_net_of_filter_conver net_of_filter_conver_filter_conver assms 
    by auto

text\<open>The previous result states that, when considering convergence, the filters
do not generalize nets. When considering a filter, there is always a net that
converges to the same points of the original filter.

Now we see that with nets, results come naturally applying the axiom
of choice; but with filters, the results come, may be less natural, but
with no choice. The reason is that \<open>Net(\<FF>)\<close> is a net
that doesn't come into our attention as a first choice; maybe because
we restrict ourselves to the anti-symmetry property of orders without realizing that
a directed set is not an order.

The following results will state that filters are not just a subclass of nets,
but that nets and filters are equivalent on convergence: for every filter there is a net
converging to the same points, and also, for every net there is a filter converging
to the same points.\<close>

definition
  FilterOfNet ("Filter (_ .. _)" 40) where
  "(N {is a net on} X) \<Longrightarrow> Filter N..X \<equiv> {A\<in>Pow(X). \<exists>D\<in>{{fst(N)`snd(s). s\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=t0}}. t0\<in>domain(fst(N))}. D\<subseteq>A}"

text\<open>Filter of a net is indeed a filter\<close>

theorem filter_of_net_is_filter:
  assumes "N {is a net on} X"
  shows "(Filter N..X) {is a filter on} X" and 
    "{{fst(N)`snd(s). s\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=t0}}. t0\<in>domain(fst(N))} {is a base filter} (Filter N..X)"
proof -
  let ?C = "{{fst(N)`(snd(s)). s\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=t0}}. t0\<in>domain(fst(N))}"
  have "?C\<subseteq>Pow(X)"
  proof -
    {
      fix t
      assume "t\<in>?C"
      then obtain t1 where "t1\<in>domain(fst(N))" and 
        t_Def: "t={fst(N)`snd(s). s\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=t1}}" 
        by auto
      {
        fix x
        assume "x\<in>t" 
        with t_Def obtain ss where "ss\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=t1}" and 
          x_def: "x = fst(N)`(snd(ss))" by blast 
        then have "snd(ss) \<in> domain(fst(N))" by auto
        from assms have "fst(N):domain(fst(N))\<rightarrow>X" unfolding IsNet_def by simp
          with \<open>snd(ss) \<in> domain(fst(N))\<close> have "x\<in>X" using apply_funtype x_def 
        by auto 
      }
      hence "t\<subseteq>X" by auto
    }
    thus ?thesis by blast
  qed
  have sat: "?C {satisfies the filter base condition}"
  proof -
    from assms obtain t1 where "t1\<in>domain(fst(N))" using IsNet_def by blast
    hence "{fst(N)`snd(s). s\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=t1}}\<in>?C" 
      by auto
    hence "?C\<noteq>0" by auto
    moreover
    {
      fix U
      assume "U\<in>?C"
      then obtain q where q_dom: "q\<in>domain(fst(N))" and 
        U_def: "U={fst(N)`snd(s). s\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=q}}" 
        by blast
      with assms have "\<langle>q,q\<rangle>\<in>snd(N) \<and> fst(\<langle>q,q\<rangle>)=q" unfolding IsNet_def IsDirectedSet_def refl_def 
        by auto
      with q_dom have "\<langle>q,q\<rangle>\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=q}" 
        by auto
      with U_def have "fst(N)`(snd(\<langle>q,q\<rangle>)) \<in> U" by blast
      hence "U\<noteq>0" by auto 
    }
    then have "0\<notin>?C" by auto
    moreover
    have "\<forall>A\<in>?C. \<forall>B\<in>?C. (\<exists>D\<in>?C. D\<subseteq>A\<inter>B)"
    proof
      fix A
      assume pA: "A\<in>?C"
      show "\<forall>B\<in>?C. \<exists>D\<in>?C. D\<subseteq>A\<inter>B"
      proof
        {
          fix B
          assume "B\<in>?C"
          with pA obtain qA qB where per: "qA\<in>domain(fst(N))" "qB\<in>domain(fst(N))" and 
            A_def: "A={fst(N)`snd(s). s\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=qA}}" and
            B_def: "B={fst(N)`snd(s). s\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=qB}}" 
              by blast
          have dir: "snd(N) directs domain(fst(N))" using assms IsNet_def by auto
          with per obtain qD where ine: "\<langle>qA,qD\<rangle>\<in>snd(N)" "\<langle>qB,qD\<rangle>\<in>snd(N)" and 
          perD: "qD\<in>domain(fst(N))" unfolding IsDirectedSet_def
            by blast
          let ?D = "{fst(N)`snd(s). s\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=qD}}"
          from perD have "?D\<in>?C" by auto
          moreover
          {
            fix d
            assume "d\<in>?D"
            then obtain sd where "sd\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=qD}" and 
              d_def: "d=fst(N)`snd(sd)" by blast
            then have sdN: "sd\<in>snd(N)" and qdd: "fst(sd)=qD" and "sd\<in>domain(fst(N))\<times>domain(fst(N))" 
              by auto
            then obtain qI aa where "sd = \<langle>aa,qI\<rangle>" "qI \<in> domain(fst(N))" "aa \<in> domain(fst(N))" 
              by auto
            with qdd have sd_def: "sd=\<langle>qD,qI\<rangle>" and qIdom: "qI\<in>domain(fst(N))" by auto
            with sdN have "\<langle>qD,qI\<rangle>\<in>snd(N)" by auto
            from dir have "trans(snd(N))" unfolding IsDirectedSet_def by auto
            then have "\<langle>qA,qD\<rangle>\<in>snd(N) \<and> \<langle>qD,qI\<rangle>\<in>snd(N) \<longrightarrow> \<langle>qA,qI\<rangle>\<in>snd(N)" and 
              "\<langle>qB,qD\<rangle>\<in>snd(N) \<and> \<langle>qD,qI\<rangle>\<in>snd(N)\<longrightarrow>\<langle>qB,qI\<rangle>\<in>snd(N)"
              using trans_def by auto 
            with ine \<open>\<langle>qD,qI\<rangle>\<in>snd(N)\<close> have "\<langle>qA,qI\<rangle>\<in>snd(N)" "\<langle>qB,qI\<rangle>\<in>snd(N)" by auto
            with qIdom per have "\<langle>qA,qI\<rangle>\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=qA}"
              "\<langle>qB,qI\<rangle>\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=qB}" 
              by auto
            then have "fst(N)`(qI) \<in> A\<inter>B" using A_def B_def by auto
            then have "fst(N)`(snd(sd)) \<in> A\<inter>B" using sd_def by auto
            then have "d \<in> A\<inter>B" using d_def by auto
          }
          then have "?D \<subseteq> A\<inter>B" by blast
          ultimately show "\<exists>D\<in>?C. D\<subseteq>A\<inter>B" by blast
        }
      qed
    qed
    ultimately
    show ?thesis unfolding SatisfiesFilterBase_def by blast
  qed
  have 
    Base: "?C {is a base filter} {A\<in>Pow(X). \<exists>D\<in>?C. D\<subseteq>A}" "\<Union>{A\<in>Pow(X). \<exists>D\<in>?C. D\<subseteq>A}=X"
  proof -
    from \<open>?C\<subseteq>Pow(X)\<close> sat show "?C {is a base filter} {A\<in>Pow(X). \<exists>D\<in>?C. D\<subseteq>A}" 
      by (rule base_unique_filter_set3)
    from \<open>?C\<subseteq>Pow(X)\<close> sat show "\<Union>{A\<in>Pow(X). \<exists>D\<in>?C. D\<subseteq>A}=X"
      by (rule base_unique_filter_set3)
  qed 
  with sat show "(Filter N..X) {is a filter on} X" 
    using sat basic_filter FilterOfNet_def assms by auto
  from Base(1) show "?C {is a base filter} (Filter N..X)" 
    using FilterOfNet_def assms by auto
qed

text\<open>Convergence of a net implies the convergence of the corresponding filter.\<close>

theorem (in topology0) net_conver_filter_of_net_conver:
  assumes "N {is a net on} \<Union>T" and "N \<rightarrow>\<^sub>N x"
  shows "(Filter N..(\<Union>T)) \<rightarrow>\<^sub>F x"
proof -
  let ?C = "{{fst(N)`snd(s). s\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=t}}. 
      t\<in>domain(fst(N))}"
  from assms(1) have  
    "(Filter N..(\<Union>T)) {is a filter on} (\<Union>T)" and "?C {is a base filter} Filter N..(\<Union>T)"
    using filter_of_net_is_filter by auto 
  moreover have "\<forall>U\<in>Pow(\<Union>T). x\<in>int(U) \<longrightarrow> (\<exists>D\<in>?C. D\<subseteq>U)"
  proof -
    {
      fix U
      assume "U\<in>Pow(\<Union>T)" "x\<in>int(U)"
      with assms have "\<exists>t\<in>domain(fst(N)). (\<forall>m\<in>domain(fst(N)). (\<langle>t,m\<rangle>\<in>snd(N) \<longrightarrow> fst(N)`m\<in>U))"
        using NetConverges_def by auto
        then obtain t where "t\<in>domain(fst(N))" and 
          reg: "\<forall>m\<in>domain(fst(N)). (\<langle>t,m\<rangle>\<in>snd(N) \<longrightarrow> fst(N)`m\<in>U)" by auto
      {
        fix f
        assume "f\<in>{fst(N)`snd(s). s\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=t}}"
        then obtain s where "s\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=t}" and 
          f_def: "f=fst(N)`snd(s)" by blast
        hence "s\<in>domain(fst(N))\<times>domain(fst(N))" and "s\<in>snd(N)" and "fst(s)=t" 
          by auto
        hence "s=\<langle>t,snd(s)\<rangle>" and "snd(s)\<in>domain(fst(N))" by auto
        with \<open>s\<in>snd(N)\<close> reg have "fst(N)`snd(s)\<in>U" by auto
        with f_def have "f\<in>U" by auto
      }
      hence "{fst(N)`snd(s). s\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=t}} \<subseteq> U" 
        by blast
      with \<open>t\<in>domain(fst(N))\<close> have "\<exists>D\<in>?C. D\<subseteq>U"
        by auto
    } thus "\<forall>U\<in>Pow(\<Union>T). x\<in>int(U) \<longrightarrow> (\<exists>D\<in>?C. D\<subseteq>U)"  by auto
  qed
  moreover from assms have "x\<in>\<Union>T" using NetConverges_def by auto
  ultimately show "(Filter N..(\<Union>T)) \<rightarrow>\<^sub>F x" by (rule convergence_filter_base2)
qed

text\<open>Convergence of a filter corresponding to a net implies convergence of the net.\<close>

 theorem (in topology0) filter_of_net_conver_net_conver:
  assumes "N {is a net on} \<Union>T" and "(Filter N..(\<Union>T)) \<rightarrow>\<^sub>F x"
  shows "N \<rightarrow>\<^sub>N x"
proof -
  let ?C = "{{fst(N)`snd(s). s\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=t}}. 
      t\<in>domain(fst(N))}"
  from assms have I: "(Filter N..(\<Union>T)) {is a filter on} (\<Union>T)"
    "?C {is a base filter} (Filter N..(\<Union>T))" "(Filter N..(\<Union>T)) \<rightarrow>\<^sub>F x"
    using filter_of_net_is_filter by auto
  then have reg: "\<forall>U\<in>Pow(\<Union>T). x\<in>int(U) \<longrightarrow> (\<exists>D\<in>?C. D\<subseteq>U)"
    by (rule convergence_filter_base1)
  from I have "x\<in>\<Union>T" by (rule convergence_filter_base1)
  moreover
  {
    fix U
    assume "U\<in>Pow(\<Union>T)" "x\<in>int(U)"
    with reg have "\<exists>D\<in>?C. D\<subseteq>U" by auto
    then obtain D where "D\<in>?C" "D\<subseteq>U"
      by auto
    then obtain td where "td\<in>domain(fst(N))" and 
      D_def: "D={fst(N)`snd(s). s\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=td}}"
      by auto
    {
      fix m
      assume "m\<in>domain(fst(N))" "\<langle>td,m\<rangle>\<in>snd(N)"
      with \<open>td\<in>domain(fst(N))\<close> have 
        "\<langle>td,m\<rangle>\<in>{s\<in>domain(fst(N))\<times>domain(fst(N)). s\<in>snd(N) \<and> fst(s)=td}"
        by auto
      with D_def have "fst(N)`m\<in>D" by auto
      with \<open>D\<subseteq>U\<close> have "fst(N)`m\<in>U" by auto
    }
    then have "\<forall>m\<in>domain(fst(N)). \<langle>td,m\<rangle>\<in>snd(N) \<longrightarrow> fst(N)`m\<in>U" by auto
    with \<open>td\<in>domain(fst(N))\<close> have 
      "\<exists>t\<in>domain(fst(N)). \<forall>m\<in>domain(fst(N)). \<langle>t,m\<rangle>\<in>snd(N) \<longrightarrow> fst(N)`m\<in>U"
      by auto
  }
  then have 
    "\<forall>U\<in>Pow(\<Union>T). x\<in>int(U) \<longrightarrow> 
      (\<exists>t\<in>domain(fst(N)). \<forall>m\<in>domain(fst(N)). \<langle>t,m\<rangle>\<in>snd(N) \<longrightarrow> fst(N)`m\<in>U)"
      by auto
  ultimately show "?thesis" using NetConverges_def assms(1) by auto
qed

text\<open>Filter of net converges to a point $x$ if and only the net converges to $x$.\<close>
theorem (in topology0) filter_of_net_conv_iff_net_conv:
  assumes "N {is a net on} \<Union>T"
  shows "((Filter N..(\<Union>T)) \<rightarrow>\<^sub>F x) \<longleftrightarrow> (N \<rightarrow>\<^sub>N x)"
  using assms filter_of_net_conver_net_conver net_conver_filter_of_net_conver 
    by auto

text\<open>We know now that filters and nets are the same thing, when working convergence
of topological spaces. Sometimes, the nature of filters makes it easier to generalized
them as follows.

Instead of considering all subsets of some set $X$, we can consider only open sets (we
get an open filter) or closed sets (we get a closed filter). There are many more
useful examples that characterize topological properties.

This type of generalization cannot be done with nets.

Also a filter can give us a topology in the following way:\<close>

theorem top_of_filter:
  assumes "\<FF> {is a filter on} \<Union>\<FF>"
  shows "(\<FF> \<union> {0}) {is a topology}"
proof -
  {
    fix A B
    assume "A\<in>(\<FF> \<union> {0})""B\<in>(\<FF> \<union> {0})"
    then have "(A\<in>\<FF> \<and> B\<in>\<FF>) \<or> (A\<inter>B=0)" by auto
    with assms have "A\<inter>B\<in>(\<FF> \<union> {0})" unfolding IsFilter_def 
      by blast 
  }
  then have "\<forall>A\<in>(\<FF> \<union> {0}). \<forall>B\<in>(\<FF> \<union> {0}). A\<inter>B\<in>(\<FF> \<union> {0})" by auto
  moreover
  {
    fix M
    assume A:"M\<in>Pow(\<FF> \<union> {0})"
    then have "M=0\<or>M={0}\<or>(\<exists>T\<in>M. T\<in>\<FF>)" by blast
    then have "\<Union>M=0\<or>(\<exists>T\<in>M. T\<in>\<FF>)" by auto
    then obtain T where "\<Union>M=0\<or>(T\<in>\<FF> \<and> T\<in>M)" by auto
    then have "\<Union>M=0\<or>(T\<in>\<FF> \<and> T\<subseteq>\<Union>M)" by auto
    moreover from this A have "\<Union>M\<subseteq>\<Union>\<FF>" by auto
    ultimately have "\<Union>M\<in>(\<FF>\<union>{0})" using IsFilter_def assms by auto
    }
  then have "\<forall>M\<in>Pow(\<FF>\<union>{0}). \<Union>M\<in>(\<FF>\<union>{0})" by auto
  ultimately show ?thesis using IsATopology_def by auto
qed

text\<open>We can use  \<open>topology0\<close> locale with filters.\<close>

lemma topology0_filter:
  assumes "\<FF> {is a filter on} \<Union>\<FF>"
  shows "topology0(\<FF> \<union> {0})"
  using top_of_filter topology0_def assms by auto

text\<open>The next abbreviation introduces notation where we want to specify the space where
  the filter convergence takes place.\<close>

abbreviation FilConvTop("_ \<rightarrow>\<^sub>F _ {in} _")
  where "\<FF> \<rightarrow>\<^sub>F x {in} T \<equiv> topology0.FilterConverges(T,\<FF>,x)"

text\<open>The next abbreviation introduces notation where we want to specify the space where
  the net convergence takes place.\<close>

abbreviation NetConvTop("_ \<rightarrow>\<^sub>N _ {in} _")
  where "N \<rightarrow>\<^sub>N x {in} T \<equiv> topology0.NetConverges(T,N,x)"

text\<open>Each point of a the union of a filter is a limit of that filter.\<close>

lemma lim_filter_top_of_filter:
  assumes "\<FF> {is a filter on} \<Union>\<FF>" and "x\<in>\<Union>\<FF>"
  shows "\<FF> \<rightarrow>\<^sub>F x {in} (\<FF>\<union>{0})"
proof-
  have "\<Union>\<FF>=\<Union>(\<FF>\<union>{0})" by auto
  with assms(1) have assms1: "\<FF> {is a filter on} \<Union>(\<FF>\<union>{0})" by auto
  {
    fix U
    assume "U\<in>Pow(\<Union>(\<FF>\<union>{0}))" "x\<in>Interior(U,(\<FF>\<union>{0}))"
    with assms(1) have "Interior(U,(\<FF>\<union>{0}))\<in>\<FF>" using topology0_def top_of_filter
      topology0.Top_2_L2 by blast
    moreover
    from assms(1) have "Interior(U,(\<FF>\<union>{0}))\<subseteq>U" using topology0_def top_of_filter
      topology0.Top_2_L1 by auto
    moreover
    from \<open>U\<in>Pow(\<Union>(\<FF>\<union>{0}))\<close> have "U\<in>Pow(\<Union>\<FF>)" by auto
    ultimately have "U\<in>\<FF>" using assms(1) IsFilter_def by auto
  }
  with assms assms1 show ?thesis using topology0.FilterConverges_def top_of_filter
    topology0_def by auto
qed

end
