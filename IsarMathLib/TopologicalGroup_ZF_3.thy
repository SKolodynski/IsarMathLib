(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2013  Daniel de la Concepcion

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
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES LOSS OF USE, DATA, OR PROFITS OR
BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open>Topological groups 3\<close>

theory TopologicalGroup_ZF_3 imports Topology_ZF_10 TopologicalGroup_ZF_2 TopologicalGroup_ZF_1
  Group_ZF_4

begin

text\<open>This theory deals with topological properties of subgroups, quotient groups
and relations between group theorical properties and topological properties.\<close>

subsection\<open>Subgroups topologies\<close>

text\<open>The closure of a subgroup is a subgroup.\<close>

theorem (in topgroup) closure_subgroup:
  assumes "IsAsubgroup(H,f)"
  shows "IsAsubgroup(cl(H),f)"
proof-
  have two:"two_top_spaces0(ProductTopology(T,T),T,f)" unfolding two_top_spaces0_def using
    topSpaceAssum Top_1_4_T1(1,3) topgroup_f_binop by auto
  from fcon have cont:"IsContinuous(ProductTopology(T,T),T,f)" by auto
  then have closed:"\<forall>D. D{is closed in}T \<longrightarrow> f-``D{is closed in}\<tau>" using two_top_spaces0.TopZF_2_1_L1
    two by auto
  then have closure:"\<forall>A\<in>Pow(\<Union>\<tau>). f``(Closure(A,\<tau>))\<subseteq>cl(f``A)" using two_top_spaces0.Top_ZF_2_1_L2
    two by force
  have sub1:"H\<subseteq>G" using group0.group0_3_L2 group0_valid_in_tgroup assms by force
  then have sub:"(H)\<times>(H)\<subseteq>\<Union>\<tau>" using prod_top_on_G(2) by auto
  from sub1 have clHG:"cl(H)\<subseteq>G" using Top_3_L11(1) by auto
  then have clHsub1:"cl(H)\<times>cl(H)\<subseteq>G\<times>G" by auto
  have "Closure(H\<times>H,ProductTopology(T,T))=cl(H)\<times>cl(H)" using cl_product
    topSpaceAssum group0.group0_3_L2 group0_valid_in_tgroup assms by auto
  then have "f``(Closure(H\<times>H,ProductTopology(T,T)))=f``(cl(H)\<times>cl(H))" by auto
  with closure sub have clcl:"f``(cl(H)\<times>cl(H))\<subseteq>cl(f``(H\<times>H))" by force
  from assms have fun:"restrict(f,H\<times>H):H\<times>H\<rightarrow>H" unfolding IsAsubgroup_def using
    group0.group_oper_assocA unfolding group0_def by auto
  then have "restrict(f,H\<times>H)``(H\<times>H)=f``(H\<times>H)" using restrict_image by auto
  moreover from fun have "restrict(f,H\<times>H)``(H\<times>H)\<subseteq>H" using func1_1_L6(2) by blast
  ultimately have "f``(H\<times>H)\<subseteq>H" by auto
  with sub1 have "f``(H\<times>H)\<subseteq>H""f``(H\<times>H)\<subseteq>G""H\<subseteq>G" by auto
  then have "cl(f``(H\<times>H))\<subseteq>cl(H)" using top_closure_mono by auto
  with clcl have img:"f``(cl(H)\<times>cl(H))\<subseteq>cl(H)" by auto
  {
    fix x y assume "x\<in>cl(H)""y\<in>cl(H)"
    then have "\<langle>x,y\<rangle>\<in>cl(H)\<times>cl(H)" by auto moreover
    have "f``(cl(H)\<times>cl(H))={f`t. t\<in>cl(H)\<times>cl(H)}" using func_imagedef topgroup_f_binop 
      clHsub1 by auto ultimately
    have "f`\<langle>x,y\<rangle>\<in>f``(cl(H)\<times>cl(H))" by auto
    with img have "f`\<langle>x,y\<rangle>\<in>cl(H)" by auto
  }
  then have A1:"cl(H){is closed under} f" unfolding IsOpClosed_def by auto
  have two:"two_top_spaces0(T,T,GroupInv(G,f))" unfolding two_top_spaces0_def using
    topSpaceAssum Ggroup group0_2_T2 by auto
  from inv_cont have cont:"IsContinuous(T,T,GroupInv(G,f))" by auto
  then have closed:"\<forall>D. D{is closed in}T \<longrightarrow> GroupInv(G,f)-``D{is closed in}T" using two_top_spaces0.TopZF_2_1_L1
    two by auto
  then have closure:"\<forall>A\<in>Pow(\<Union>T). GroupInv(G,f)``(cl(A))\<subseteq>cl(GroupInv(G,f)``A)" using two_top_spaces0.Top_ZF_2_1_L2
    two by force
  with sub1 have Inv:"GroupInv(G,f)``(cl(H))\<subseteq>cl(GroupInv(G,f)``H)" by auto moreover
  have "GroupInv(H,restrict(f,H\<times>H)):H\<rightarrow>H" using assms unfolding IsAsubgroup_def using group0_2_T2 by auto then
  have "GroupInv(H,restrict(f,H\<times>H))``H\<subseteq>H" using func1_1_L6(2) by auto
  then have "restrict(GroupInv(G,f),H)``H\<subseteq>H" using group0.group0_3_T1 assms group0_valid_in_tgroup by auto
  then have sss:"GroupInv(G,f)``H\<subseteq>H" using restrict_image by auto
  then have "H\<subseteq>G" "GroupInv(G,f)``H\<subseteq>G" using sub1 by auto
  with sub1 sss have "cl(GroupInv(G,f)``H)\<subseteq>cl(H)" using top_closure_mono by auto ultimately
  have img:"GroupInv(G,f)``(cl(H))\<subseteq>cl(H)" by auto
  {
    fix x assume "x\<in>cl(H)" moreover
    have "GroupInv(G,f)``(cl(H))={GroupInv(G,f)`t. t\<in>cl(H)}" using func_imagedef Ggroup group0_2_T2
      clHG by force ultimately
    have "GroupInv(G,f)`x\<in>GroupInv(G,f)``(cl(H))" by auto
    with img have "GroupInv(G,f)`x\<in>cl(H)" by auto
  }
  then have A2:"\<forall>x\<in>cl(H). GroupInv(G,f)`x\<in>cl(H)" by auto
  from assms have "H\<noteq>0" using group0.group0_3_L5 group0_valid_in_tgroup by auto moreover
  have "H\<subseteq>cl(H)" using cl_contains_set sub1 by auto ultimately
  have "cl(H)\<noteq>0" by auto
  with clHG A2 A1 show ?thesis using group0.group0_3_T3 group0_valid_in_tgroup by auto
qed

text\<open>The closure of a normal subgroup is normal.\<close>

theorem (in topgroup) normal_subg:
  assumes "IsAnormalSubgroup(G,f,H)"
  shows "IsAnormalSubgroup(G,f,cl(H))"
proof-
  have A:"IsAsubgroup(cl(H),f)" using closure_subgroup assms unfolding IsAnormalSubgroup_def by auto
  have sub1:"H\<subseteq>G" using group0.group0_3_L2 group0_valid_in_tgroup assms unfolding IsAnormalSubgroup_def by auto
  then have sub2:"cl(H)\<subseteq>G" using Top_3_L11(1) by auto
  {
    fix g assume g:"g\<in>G"
    then have cl1:"cl(g\<ltr>H)=g\<ltr>cl(H)" using trans_closure sub1 by auto
    have ss:"g\<ltr>cl(H)\<subseteq>G" unfolding ltrans_def LeftTranslation_def by auto
    have "g\<ltr>H\<subseteq>G" unfolding ltrans_def LeftTranslation_def by auto
    moreover from g have "(\<rm>g)\<in>G" using neg_in_tgroup by auto
    ultimately have cl2:"cl((g\<ltr>H)\<rtr>(\<rm>g))=cl(g\<ltr>H)\<rtr>(\<rm>g)" using trans_closure2
      by auto
    with cl1 have clcon:"cl((g\<ltr>H)\<rtr>(\<rm>g))=(g\<ltr>(cl(H)))\<rtr>(\<rm>g)" by auto
    {
      fix r assume "r\<in>(g\<ltr>H)\<rtr>(\<rm>g)"
      then obtain q where q:"q\<in>g\<ltr>H" "r=q\<ra>(\<rm>g)" unfolding rtrans_def RightTranslation_def
        by force
      from q(1) obtain h where "h\<in>H" "q=g\<ra>h" unfolding ltrans_def LeftTranslation_def by auto
      with q(2) have "r=(g\<ra>h)\<ra>(\<rm>g)" by auto
      with \<open>h\<in>H\<close> \<open>g\<in>G\<close> \<open>(\<rm>g)\<in>G\<close> have "r\<in>H" using assms unfolding IsAnormalSubgroup_def
        grinv_def grop_def by auto
    }
    then have "(g\<ltr>H)\<rtr>(\<rm>g)\<subseteq>H" by auto
    moreover then have "(g\<ltr>H)\<rtr>(\<rm>g)\<subseteq>G""H\<subseteq>G" using sub1 by auto ultimately
    have "cl((g\<ltr>H)\<rtr>(\<rm>g))\<subseteq>cl(H)" using top_closure_mono by auto
    with clcon have "(g\<ltr>(cl(H)))\<rtr>(\<rm>g)\<subseteq>cl(H)" by auto moreover
    {
      fix b assume "b\<in>{g\<ra>(d\<rs>g). d\<in>cl(H)}"
      then obtain d where d:"d\<in>cl(H)" "b=g\<ra>(d\<rs>g)" by auto moreover
      then have "d\<in>G" using sub2 by auto 
      then have "g\<ra>d\<in>G" using group0.group_op_closed[OF group0_valid_in_tgroup \<open>g\<in>G\<close>] by auto
      from d(2) have b:"b=(g\<ra>d)\<rs>g" using group0.group_oper_assoc[OF group0_valid_in_tgroup \<open>g\<in>G\<close> \<open>d\<in>G\<close>\<open>(\<rm>g)\<in>G\<close>] 
        unfolding grsub_def grop_def grinv_def by blast
      have "(g\<ra>d)=LeftTranslation(G,f,g)`d" using group0.group0_5_L2(2)[OF group0_valid_in_tgroup]
        \<open>g\<in>G\<close>\<open>d\<in>G\<close> by auto
      with \<open>d\<in>cl(H)\<close> have "g\<ra>d\<in>g\<ltr>cl(H)" unfolding ltrans_def using func_imagedef[OF group0.group0_5_L1(2)[
        OF group0_valid_in_tgroup \<open>g\<in>G\<close>] sub2] by auto
      moreover from b have "b=RightTranslation(G,f,\<rm>g)`(g\<ra>d)" using group0.group0_5_L2(1)[OF group0_valid_in_tgroup]
        \<open>(\<rm>g)\<in>G\<close>\<open>g\<ra>d\<in>G\<close> by auto
      ultimately have "b\<in>(g\<ltr>cl(H))\<rtr>(\<rm>g)" unfolding rtrans_def using func_imagedef[OF group0.group0_5_L1(1)[
        OF group0_valid_in_tgroup \<open>(\<rm>g)\<in>G\<close>] ss] by force
    }
    ultimately have "{g\<ra>(d\<rs>g). d\<in>cl(H)}\<subseteq>cl(H)" by force
  }
  then show ?thesis using A group0.cont_conj_is_normal[OF group0_valid_in_tgroup, of "cl(H)"]
    unfolding grsub_def grinv_def grop_def by auto
qed

text\<open>Every open subgroup is also closed.\<close>

theorem (in topgroup) open_subgroup_closed:
  assumes "IsAsubgroup(H,f)" "H\<in>T"
  shows "H{is closed in}T"
proof-
  from assms(1) have sub:"H\<subseteq>G" using group0.group0_3_L2 group0_valid_in_tgroup by force
  {
    fix t assume "t\<in>G-H"
    then have tnH:"t\<notin>H" and tG:"t\<in>G" by auto
    from assms(1) have sub:"H\<subseteq>G" using group0.group0_3_L2 group0_valid_in_tgroup by force
    from assms(1) have nSubG:"\<zero>\<in>H" using group0.group0_3_L5 group0_valid_in_tgroup by auto
    from assms(2) tG have P:"t\<ltr>H\<in>T" using open_tr_open(1) by auto
    from nSubG sub tG have tp:"t\<in>t\<ltr>H" using group0_valid_in_tgroup group0.neut_trans_elem
      by auto
    {
      fix x assume "x\<in>(t\<ltr>H)\<inter>H"
      then obtain u where "x=t\<ra>u" "u\<in>H" "x\<in>H" unfolding ltrans_def LeftTranslation_def by auto
      then have "u\<in>G""x\<in>G""t\<in>G" using sub tG by auto
      with \<open>x=t\<ra>u\<close> have "x\<ra>(\<rm>u)=t" using group0.group0_2_L18(1) group0_valid_in_tgroup
        unfolding grop_def grinv_def by auto
      from \<open>u\<in>H\<close> have "(\<rm>u)\<in>H" unfolding grinv_def using assms(1) group0.group0_3_T3A group0_valid_in_tgroup
        by auto
      with \<open>x\<in>H\<close> have "x\<ra>(\<rm>u)\<in>H" unfolding grop_def using assms(1) group0.group0_3_L6 group0_valid_in_tgroup
        by auto
      with \<open>x\<ra>(\<rm>u)=t\<close> have "False" using tnH by auto
    }
    then have "(t\<ltr>H)\<inter>H=0" by auto moreover
    have "t\<ltr>H\<subseteq>G" unfolding ltrans_def LeftTranslation_def by auto ultimately
    have "(t\<ltr>H)\<subseteq>G-H" by auto
    with tp P have "\<exists>V\<in>T. t\<in>V \<and> V\<subseteq>G-H" unfolding Bex_def by auto
  }
  then have "\<forall>t\<in>G-H. \<exists>V\<in>T. t\<in>V \<and> V\<subseteq>G-H" by auto
  then have "G-H\<in>T" using open_neigh_open by auto
  then show ?thesis unfolding IsClosed_def using sub by auto
qed

text\<open>Any subgroup with non-empty interior is open.\<close>

theorem (in topgroup) clopen_or_emptyInt:
  assumes "IsAsubgroup(H,f)" "int(H)\<noteq>0"
  shows "H\<in>T"
proof-
  from assms(1) have sub:"H\<subseteq>G" using group0.group0_3_L2 group0_valid_in_tgroup by force
  {
    fix h assume "h\<in>H"
    have intsub:"int(H)\<subseteq>H" using Top_2_L1 by auto
    from assms(2) obtain u where "u\<in>int(H)" by auto
    with intsub have "u\<in>H" by auto
    then have "(\<rm>u)\<in>H" unfolding grinv_def using assms(1) group0.group0_3_T3A group0_valid_in_tgroup
      by auto
    with \<open>h\<in>H\<close> have "h\<rs>u\<in>H" unfolding grop_def using assms(1) group0.group0_3_L6 group0_valid_in_tgroup
      by auto
    {
      fix t assume "t\<in>(h\<rs>u)\<ltr>(int(H))"
      then obtain r where "r\<in>int(H)""t=(h\<rs>u)\<ra>r" unfolding grsub_def grinv_def grop_def
        ltrans_def LeftTranslation_def by auto
      then have "r\<in>H" using intsub by auto
      with \<open>h\<rs>u\<in>H\<close> have "(h\<rs>u)\<ra>r\<in>H" unfolding grop_def using assms(1) group0.group0_3_L6 group0_valid_in_tgroup
        by auto
      with \<open>t=(h\<rs>u)\<ra>r\<close> have "t\<in>H" by auto
    }
    then have ss:"(h\<rs>u)\<ltr>(int(H))\<subseteq>H" by auto
    have P:"(h\<rs>u)\<ltr>(int(H))\<in>T" using open_tr_open(1) \<open>h\<rs>u\<in>H\<close> Top_2_L2 sub by blast
    from \<open>h\<rs>u\<in>H\<close>\<open>u\<in>H\<close>\<open>h\<in>H\<close> sub have "(h\<rs>u)\<in>G" "u\<in>G""h\<in>G" by auto
    have "int(H)\<subseteq>G" using sub intsub by auto moreover
    have "LeftTranslation(G,f,(h\<rs>u))\<in>G\<rightarrow>G" using group0.group0_5_L1(2) group0_valid_in_tgroup \<open>(h\<rs>u)\<in>G\<close>
      by auto ultimately
    have "LeftTranslation(G,f,(h\<rs>u))``(int(H))={LeftTranslation(G,f,(h\<rs>u))`r. r\<in>int(H)}" 
      using func_imagedef by auto moreover
    from \<open>(h\<rs>u)\<in>G\<close> \<open>u\<in>G\<close> have "LeftTranslation(G,f,(h\<rs>u))`u=(h\<rs>u)\<ra>u" using group0.group0_5_L2(2) group0_valid_in_tgroup
      by auto
    with \<open>u\<in>int(H)\<close> have "(h\<rs>u)\<ra>u\<in>{LeftTranslation(G,f,(h\<rs>u))`r. r\<in>int(H)}" by force ultimately
    have "(h\<rs>u)\<ra>u\<in>(h\<rs>u)\<ltr>(int(H))" unfolding ltrans_def by auto moreover
    have "(h\<rs>u)\<ra>u=h" using group0.inv_cancel_two(1) group0_valid_in_tgroup
      \<open>u\<in>G\<close>\<open>h\<in>G\<close> by auto ultimately
    have "h\<in>(h\<rs>u)\<ltr>(int(H))" by auto
    with P ss have "\<exists>V\<in>T. h\<in>V\<and> V\<subseteq>H" unfolding Bex_def by auto
  }
  then show ?thesis using open_neigh_open by auto
qed

text\<open>In conclusion, a subgroup is either open or has empty interior.\<close>

corollary(in topgroup) emptyInterior_xor_op:
  assumes "IsAsubgroup(H,f)"
  shows "(int(H)=0) Xor (H\<in>T)"
  unfolding Xor_def using clopen_or_emptyInt assms Top_2_L3 
  group0.group0_3_L5 group0_valid_in_tgroup by force

text\<open>Then no connected topological groups has proper subgroups with non-empty interior.\<close>

corollary(in topgroup) connected_emptyInterior:
  assumes "IsAsubgroup(H,f)" "T{is connected}"
  shows "(int(H)=0) Xor (H=G)"
proof-
  have "(int(H)=0) Xor (H\<in>T)" using emptyInterior_xor_op assms(1) by auto moreover
  {
    assume "H\<in>T" moreover
    then have "H{is closed in}T" using open_subgroup_closed assms(1) by auto ultimately
    have "H=0\<or>H=G" using assms(2) unfolding IsConnected_def by auto
    then have "H=G" using group0.group0_3_L5 group0_valid_in_tgroup assms(1) by auto
  } moreover
  have "G\<in>T" using topSpaceAssum unfolding IsATopology_def G_def by auto
  ultimately show ?thesis unfolding Xor_def by auto
qed

text\<open>Every locally-compact subgroup of a $T_0$ group is closed.\<close>

theorem (in topgroup) loc_compact_T0_closed:
  assumes "IsAsubgroup(H,f)" "(T{restricted to}H){is locally-compact}" "T{is T\<^sub>0}"
  shows "H{is closed in}T"
proof-
  from assms(1) have clsub:"IsAsubgroup(cl(H),f)" using closure_subgroup by auto
  then have subcl:"cl(H)\<subseteq>G" using group0.group0_3_L2 group0_valid_in_tgroup by force
  from assms(1) have sub:"H\<subseteq>G" using group0.group0_3_L2 group0_valid_in_tgroup by force
  from assms(3) have "T{is T\<^sub>2}" using T1_imp_T2 neu_closed_imp_T1 T0_imp_neu_closed by auto
  then have "(T{restricted to}H){is T\<^sub>2}" using T2_here sub by auto
  have tot:"\<Union>(T{restricted to}H)=H" using sub unfolding RestrictedTo_def by auto
  with assms(2) have "\<forall>x\<in>H. \<exists>A\<in>Pow(H). A {is compact in} (T{restricted to}H) \<and> x \<in> Interior(A, (T{restricted to}H))" using 
    topology0.locally_compact_exist_compact_neig[of "T{restricted to}H"] Top_1_L4 unfolding topology0_def
    by auto
  then obtain K where K:"K\<subseteq>H" "K{is compact in} (T{restricted to}H)""\<zero>\<in>Interior(K,(T{restricted to}H))"
    using group0.group0_3_L5 group0_valid_in_tgroup assms(1) unfolding gzero_def by force
  from K(1,2) have "K{is compact in} T" using compact_subspace_imp_compact by auto
  with \<open>T{is T\<^sub>2}\<close> have Kcl:"K{is closed in}T" using in_t2_compact_is_cl by auto
  have "Interior(K,(T{restricted to}H))\<in>(T{restricted to}H)" using topology0.Top_2_L2 unfolding topology0_def
    using Top_1_L4 by auto
  then obtain U where U:"U\<in>T""Interior(K,(T{restricted to}H))=H\<inter>U" unfolding RestrictedTo_def by auto
  then have "H\<inter>U\<subseteq>K" using topology0.Top_2_L1[of "T{restricted to}H"] unfolding topology0_def using Top_1_L4 by force
  moreover have U2:"U\<subseteq>U\<union>K" by auto
  have ksub:"K\<subseteq>H" using tot K(2) unfolding IsCompact_def by auto
  ultimately have int:"H\<inter>(U\<union>K)=K" by auto
  from U(2) K(3) have "\<zero>\<in>U" by auto
  with U(1) U2 have "\<zero>\<in>int(U \<union> K)" using Top_2_L6 by auto
  then have "U\<union>K\<in>\<N>\<^sub>0" unfolding zerohoods_def using U(1) ksub sub by auto
  then obtain V where V:"V\<subseteq>U\<union>K" "V\<in>\<N>\<^sub>0" "V\<sad>V\<subseteq>U\<union>K""(\<sm> V) = V" using exists_procls_zerohood[of "U\<union>K"]
    by auto
  {
    fix h assume AS:"h\<in>cl(H)"
    with clsub have "(\<rm>h)\<in>cl(H)" using group0.group0_3_T3A group0_valid_in_tgroup by auto moreover
    then have "(\<rm>h)\<in>G" using subcl by auto
    with V(2) have "(\<rm>h)\<in>int((\<rm>h)\<ltr>V)" using elem_in_int_trans by auto ultimately
    have "(\<rm>h)\<in>(cl(H))\<inter>(int((\<rm>h)\<ltr>V))" by auto moreover
    have "int((\<rm>h)\<ltr>V)\<in>T" using Top_2_L2 by auto moreover
    note sub ultimately
    have "H\<inter>(int((\<rm>h)\<ltr>V))\<noteq>0" using cl_inter_neigh by auto moreover
    from \<open>(\<rm>h)\<in>G\<close> V(2) have "int((\<rm>h)\<ltr>V)=(\<rm>h)\<ltr>int(V)" unfolding zerohoods_def using trans_interior by force
    ultimately have "H\<inter>((\<rm>h)\<ltr>int(V))\<noteq>0" by auto
    then obtain y where y:"y\<in>H" "y\<in>(\<rm>h)\<ltr>int(V)" by blast
    then obtain v where v:"v\<in>int(V)" "y=(\<rm>h)\<ra>v" unfolding ltrans_def LeftTranslation_def by auto
    with \<open>(\<rm>h)\<in>G\<close> V(2) y(1) sub have "v\<in>G""(\<rm>h)\<in>G""y\<in>G" using Top_2_L1[of "V"] unfolding zerohoods_def by auto
    with v(2) have "(\<rm>(\<rm>h))\<ra>y=v" using group0.group0_2_L18(2) group0_valid_in_tgroup
      unfolding grop_def grinv_def by auto moreover
    have "h\<in>G" using AS subcl by auto
    then have "(\<rm>(\<rm>h))=h" using group0.group_inv_of_inv group0_valid_in_tgroup by auto ultimately
    have "h\<ra>y=v" by auto
    with v(1) have hyV:"h\<ra>y\<in>int(V)" by auto
    have "y\<in>cl(H)" using y(1) cl_contains_set sub by auto
    with AS have hycl:"h\<ra> y\<in>cl(H)" using clsub group0.group0_3_L6 group0_valid_in_tgroup by auto
    {
      fix W assume W:"W\<in>T""h\<ra>y\<in>W"
      with hyV have "h\<ra>y\<in>int(V)\<inter>W" by auto moreover
      from W(1) have "int(V)\<inter>W\<in>T" using Top_2_L2 topSpaceAssum unfolding IsATopology_def by auto moreover
      note hycl sub
      ultimately have "(int(V)\<inter>W)\<inter>H\<noteq>0" using cl_inter_neigh[of "H""int(V)\<inter>W""h\<ra>y"] by auto
      then have "V\<inter>W\<inter>H\<noteq>0" using Top_2_L1 by auto
      with V(1) have "(U\<union>K)\<inter>W\<inter>H\<noteq>0" by auto
      then have "(H\<inter>(U\<union>K))\<inter>W\<noteq>0" by auto
      with int have "K\<inter>W\<noteq>0" by auto
    }
    then have "\<forall>W\<in>T. h\<ra>y\<in>W \<longrightarrow> K\<inter>W\<noteq>0" by auto moreover
    have "K\<subseteq>G" "h\<ra>y\<in>G" using ksub sub hycl subcl by auto ultimately
    have "h\<ra>y\<in>cl(K)" using inter_neigh_cl[of "K""h\<ra>y"] unfolding G_def by force
    then have "h\<ra>y\<in>K" using Kcl Top_3_L8 \<open>K\<subseteq>G\<close> by auto
    with ksub have "h\<ra>y\<in>H" by auto
    moreover from y(1) have "(\<rm>y)\<in>H" using group0.group0_3_T3A assms(1) group0_valid_in_tgroup
      by auto
    ultimately have "(h\<ra>y)\<rs>y\<in>H" unfolding grsub_def using group0.group0_3_L6 group0_valid_in_tgroup
      assms(1) by auto
    moreover 
    have "(\<rm>y)\<in>G" using \<open>(\<rm>y)\<in>H\<close> sub by auto
    then have "h\<ra>(y\<rs>y)=(h\<ra>y)\<rs>y" using \<open>y\<in>G\<close>\<open>h\<in>G\<close> group0.group_oper_assoc
      group0_valid_in_tgroup unfolding grsub_def by auto
    then have "h\<ra>\<zero>=(h\<ra>y)\<rs>y" using group0.group0_2_L6 group0_valid_in_tgroup \<open>y\<in>G\<close>
      unfolding grsub_def grinv_def grop_def gzero_def by auto
    then have "h=(h\<ra>y)\<rs>y" using group0.group0_2_L2 group0_valid_in_tgroup
      \<open>h\<in>G\<close> unfolding gzero_def by auto
    ultimately have "h\<in>H" by auto
  }
  then have "cl(H)\<subseteq>H" by auto
  then have "H=cl(H)" using cl_contains_set sub by auto
  then show ?thesis using Top_3_L8 sub by auto
qed

text\<open>We can always consider a factor group which is $T_2$.\<close>

theorem(in topgroup) factor_haus:
  shows "(T{quotient by}QuotientGroupRel(G,f,cl({\<zero>}))){is T\<^sub>2}"
proof-
  let ?r="QuotientGroupRel(G,f,cl({\<zero>}))"
  let ?f="QuotientGroupOp(G,f,cl({\<zero>}))"
  let ?i="GroupInv(G//?r,?f)"
  have "IsAnormalSubgroup(G,f,{\<zero>})" using group0.trivial_normal_subgroup Ggroup unfolding group0_def
    by auto
  then have normal:"IsAnormalSubgroup(G,f,cl({\<zero>}))" using normal_subg by auto
  then have eq:"equiv(\<Union>T,?r)" using group0.Group_ZF_2_4_L3[OF group0_valid_in_tgroup]
    unfolding IsAnormalSubgroup_def by auto
  then have tot:"\<Union>(T{quotient by}?r)=G//?r" using total_quo_equi by auto
  have neu:"?r``{\<zero>}=TheNeutralElement(G//?r,?f)" using Group_ZF_2_4_L5B[OF Ggroup normal] by auto
  then have "?r``{\<zero>}\<in>G//?r" using group0.group0_2_L2 Group_ZF_2_4_T1[OF Ggroup normal] unfolding group0_def by auto
  then have sub1:"{?r``{\<zero>}}\<subseteq>G//?r" by auto
  then have sub:"{?r``{\<zero>}}\<subseteq>\<Union>(T{quotient by}?r)" using tot by auto
  have zG:"\<zero>\<in>\<Union>T" using group0.group0_2_L2[OF group0_valid_in_tgroup] by auto
  from zG have cla:"?r``{\<zero>}\<in>G//?r" unfolding quotient_def by auto
  let ?x="G//?r-{?r``{\<zero>}}"
  {
    fix s assume A:"s\<in>\<Union>(G//?r-{?r``{\<zero>}})"
    then obtain U where "s\<in>U" "U\<in>G//?r-{?r``{\<zero>}}" by auto
    then have "U\<in>G//?r" "U\<noteq>?r``{\<zero>}" "s\<in>U" by auto
    then have "U\<in>G//?r" "s\<in>U" "s\<notin>?r``{\<zero>}" using cla quotient_disj[OF eq] by auto
    then have "s\<in>\<Union>(G//?r)-?r``{\<zero>}" by auto
  }
  moreover
  {
    fix s assume A:"s\<in>\<Union>(G//?r)-?r``{\<zero>}"
    then obtain U where "s\<in>U" "U\<in>G//?r" "s\<notin>?r``{\<zero>}" by auto
    then have "s\<in>U" "U\<in>G//?r-{?r``{\<zero>}}" by auto
    then have "s\<in>\<Union>(G//?r-{?r``{\<zero>}})" by auto
  }
  ultimately have "\<Union>(G//?r-{?r``{\<zero>}})=\<Union>(G//?r)-?r``{\<zero>}" by auto
  then have A:"\<Union>(G//?r-{?r``{\<zero>}})=G-?r``{\<zero>}" using Union_quotient eq by auto
  {
    fix s assume A:"s\<in>?r``{\<zero>}"
    then have "\<langle>\<zero>,s\<rangle>\<in>?r" by auto
    then have "\<langle>s,\<zero>\<rangle>\<in>?r" using eq unfolding equiv_def sym_def by auto
    then have "s\<in>cl({\<zero>})" using group0.Group_ZF_2_4_L5C[OF group0_valid_in_tgroup] unfolding QuotientGroupRel_def by auto
  }
  moreover
  {
    fix s assume A:"s\<in>cl({\<zero>})"
    then have "s\<in>G" using Top_3_L11(1) zG by auto
    then have "\<langle>s,\<zero>\<rangle>\<in>?r" using group0.Group_ZF_2_4_L5C[OF group0_valid_in_tgroup] A by auto
    then have "\<langle>\<zero>,s\<rangle>\<in>?r" using eq unfolding equiv_def sym_def by auto
    then have "s\<in>?r``{\<zero>}" by auto
  }
  ultimately have "?r``{\<zero>}=cl({\<zero>})" by blast
  with A have "\<Union>(G//?r-{?r``{\<zero>}})=G-cl({\<zero>})" by auto
  moreover have "cl({\<zero>}){is closed in}T" using cl_is_closed zG by auto
  ultimately have "\<Union>(G//?r-{?r``{\<zero>}})\<in>T" unfolding IsClosed_def by auto
  then have "(G//?r-{?r``{\<zero>}})\<in>{quotient by}?r" using quotient_equiv_rel eq by auto
  then have "(\<Union>(T{quotient by}?r)-{?r``{\<zero>}})\<in>{quotient by}?r" using total_quo_equi[OF eq] by auto
  moreover from sub1 have "{?r``{\<zero>}}\<subseteq>(\<Union>(T{quotient by}?r))" using total_quo_equi[OF eq] by auto
  ultimately have "{?r``{\<zero>}}{is closed in}(T{quotient by}?r)" unfolding IsClosed_def by auto
  then have "{TheNeutralElement(G//?r,?f)}{is closed in}(T{quotient by}?r)" using neu by auto
  then have "(T{quotient by}?r){is T\<^sub>1}" using topgroup.neu_closed_imp_T1[OF topGroupLocale[OF quotient_top_group[OF normal]]]
    total_quo_equi[OF eq] by auto
  then show ?thesis using topgroup.T1_imp_T2[OF topGroupLocale[OF quotient_top_group[OF normal]]] by auto
qed 
      

end
