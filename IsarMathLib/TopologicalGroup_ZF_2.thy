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

section \<open>Topological groups 2\<close>

theory TopologicalGroup_ZF_2 imports Topology_ZF_8 TopologicalGroup_ZF Group_ZF_2
begin

text\<open>This theory deals with quotient topological groups.\<close>

subsection\<open>Quotients of topological groups\<close>

text\<open>The quotient topology given by the quotient group equivalent relation, has
an open quotient map.\<close>

theorem(in topgroup) quotient_map_topgroup_open:
  assumes "IsAsubgroup(H,f)" "A\<in>T"
  defines "r \<equiv> QuotientGroupRel(G,f,H)"
  shows "{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``A\<in>(T{quotient by}r)"
proof-
  have eqT:"equiv(\<Union>T,r)" and eqG:"equiv(G,r)" using group0.Group_ZF_2_4_L3 assms(1) unfolding r_def IsAnormalSubgroup_def
    using group0_valid_in_tgroup by auto
  have subA:"A\<subseteq>G" using assms(2) by auto
  have subH:"H\<subseteq>G" using group0.group0_3_L2[OF group0_valid_in_tgroup assms(1)].
  have A1:"{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}-``({\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``A)=H\<sad>A"
  proof
    {
      fix t assume "t\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}-``({\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``A)"
      then have "\<exists>m\<in>({\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``A). \<langle>t,m\<rangle>\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}" using vimage_iff by auto
      then obtain m where "m\<in>({\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``A)""\<langle>t,m\<rangle>\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}" by auto
      then obtain b where "b\<in>A""\<langle>b,m\<rangle>\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}""t\<in>G" and rel:"r``{t}=m" using image_iff by auto
      then have "r``{b}=m" by auto
      then have "r``{t}=r``{b}" using rel by auto
      with \<open>b\<in>A\<close>subA have "\<langle>t,b\<rangle>\<in>r" using eq_equiv_class[OF _ eqT] by auto
      then have "f`\<langle>t,GroupInv(G,f)`b\<rangle>\<in>H" unfolding r_def QuotientGroupRel_def by auto
      then obtain h where "h\<in>H" and prd:"f`\<langle>t,GroupInv(G,f)`b\<rangle>=h" by auto
      then have "h\<in>G" using subH by auto
      have "b\<in>G" using \<open>b\<in>A\<close>\<open>A\<in>T\<close> by auto
      then have "(\<rm>b)\<in>G" using neg_in_tgroup by auto
      from prd have "h=t\<ra>(\<rm>b)" by simp
      with \<open>t\<in>G\<close> \<open>b\<in>G\<close> have "t = h\<ra>b" using inv_cancel_two_add(1) by simp 
      then have "\<langle>\<langle>h,b\<rangle>,t\<rangle>\<in>f" using apply_Pair[OF topgroup_f_binop] \<open>h\<in>G\<close>\<open>b\<in>G\<close> by auto 
      moreover from \<open>h\<in>H\<close>\<open>b\<in>A\<close> have "\<langle>h,b\<rangle>\<in>H\<times>A" by auto
      ultimately have "t\<in>f``(H\<times>A)" using image_iff by auto
      with subA subH have "t\<in>H\<sad>A" using interval_add(2) by auto
    }
    then show "({\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}-``({\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``A))\<subseteq>H\<sad>A" by force
    {
      fix t assume "t\<in>H\<sad>A"
      with subA subH have "t \<in> f``(H\<times>A)" using interval_add(2) by auto
      then obtain ha where "ha\<in>H\<times>A" "\<langle>ha,t\<rangle>\<in>f" using image_iff by auto
      then obtain h aa where "ha=\<langle>h,aa\<rangle>""h\<in>H""aa\<in>A" by auto
      then have "h\<in>G""aa\<in>G" using subH subA by auto
      from \<open>\<langle>ha,t\<rangle>\<in>f\<close> have "t\<in>G" using topgroup_f_binop unfolding Pi_def by auto
      from \<open>ha=\<langle>h,aa\<rangle>\<close> \<open>\<langle>ha,t\<rangle>\<in>f\<close> have "t=h\<ra>aa" using apply_equality topgroup_f_binop 
        by auto 
      with \<open>h\<in>G\<close> \<open>aa\<in>G\<close> have "t\<ra>(\<rm>aa) = h" using inv_cancel_two_add(2) by simp
      with \<open>h\<in>H\<close>\<open>t\<in>G\<close>\<open>aa\<in>G\<close> have "\<langle>t,aa\<rangle>\<in>r" unfolding r_def QuotientGroupRel_def by auto
      then have "r``{t}=r``{aa}" using eqT equiv_class_eq by auto
      with \<open>aa\<in>G\<close> have "\<langle>aa,r``{t}\<rangle>\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}" by auto
      with \<open>aa\<in>A\<close> have A1:"r``{t}\<in>({\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``A)" using image_iff by auto
      from \<open>t\<in>G\<close> have "\<langle>t,r``{t}\<rangle>\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}" by auto
      with A1 have "t\<in>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}-``({\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``A)" using vimage_iff by auto
    }
    then show "H\<sad>A\<subseteq>{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}-``({\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``A)" by auto
  qed
  have "H\<sad>A=(\<Union>x\<in>H. x \<ltr> A)" using interval_add(3) subH subA by auto moreover
  have "\<forall>x\<in>H. x \<ltr> A\<in>T" using open_tr_open(1) assms(2) subH by blast
  then have "{x \<ltr> A. x\<in>H}\<subseteq>T" by auto
  then have "(\<Union>x\<in>H. x \<ltr> A)\<in>T" using topSpaceAssum unfolding IsATopology_def by auto
  ultimately have "H\<sad>A\<in>T" by auto
  with A1 have "{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}-``({\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``A)\<in>T" by auto
  then have "({\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``A)\<in>{quotient topology in}((\<Union>T)//r){by}{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}{from}T"
    using QuotientTop_def topSpaceAssum quotient_proj_surj using 
    func1_1_L6(2)[OF quotient_proj_fun] by auto
  then show "({\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}``A)\<in>(T{quotient by}r)" using EquivQuo_def[OF eqT] by auto
qed 
      

text\<open>A quotient of a topological group is just a quotient group with an appropiate
 topology that makes product and inverse continuous.\<close>

theorem (in topgroup) quotient_top_group_F_cont:
  assumes "IsAnormalSubgroup(G,f,H)"
  defines "r \<equiv> QuotientGroupRel(G,f,H)"
  defines "F \<equiv> QuotientGroupOp(G,f,H)"
  shows "IsContinuous(ProductTopology(T{quotient by}r,T{quotient by}r),T{quotient by}r,F)"
proof-
  have eqT:"equiv(\<Union>T,r)" and eqG:"equiv(G,r)" using group0.Group_ZF_2_4_L3 assms(1) unfolding r_def IsAnormalSubgroup_def
    using group0_valid_in_tgroup by auto
  have fun:"{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}:G\<times>G\<rightarrow>(G//r)\<times>(G//r)" using product_equiv_rel_fun unfolding G_def by auto 
  have C:"Congruent2(r,f)" using Group_ZF_2_4_L5A[OF Ggroup assms(1)] unfolding r_def.
  with eqT have "IsContinuous(ProductTopology(T,T),ProductTopology(T{quotient by}r,T{quotient by}r),{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T})"
    using product_quo_fun by auto
  have tprod:"topology0(ProductTopology(T,T))" unfolding topology0_def using Top_1_4_T1(1)[OF topSpaceAssum topSpaceAssum].
  have Hfun:"{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}\<in>surj(\<Union>ProductTopology(T,T),\<Union>(({quotient topology in}(((\<Union>T)//r)\<times>((\<Union>T)//r)){by}{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}{from}(ProductTopology(T,T)))))" using prod_equiv_rel_surj
    total_quo_equi[OF eqT] topology0.total_quo_func[OF tprod prod_equiv_rel_surj] unfolding F_def QuotientGroupOp_def r_def
    by auto
  have Ffun:"F:\<Union>(({quotient topology in}(((\<Union>T)//r)\<times>((\<Union>T)//r)){by}{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}{from}(ProductTopology(T,T))))\<rightarrow>\<Union>(T{quotient by}r)"
    using EquivClass_1_T1[OF eqG C] using total_quo_equi[OF eqT] topology0.total_quo_func[OF tprod prod_equiv_rel_surj] unfolding F_def QuotientGroupOp_def r_def
    by auto
  have cc:"(F O {\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}):G\<times>G\<rightarrow>G//r" using comp_fun[OF fun EquivClass_1_T1[OF eqG C]]
    unfolding F_def QuotientGroupOp_def r_def by auto
  then have "(F O {\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}):\<Union>(ProductTopology(T,T))\<rightarrow>\<Union>(T{quotient by}r)" using Top_1_4_T1(3)[OF topSpaceAssum topSpaceAssum]
    total_quo_equi[OF eqT] by auto
  then have two:"two_top_spaces0(ProductTopology(T,T),T{quotient by}r,(F O {\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}))" unfolding two_top_spaces0_def
    using Top_1_4_T1(1)[OF topSpaceAssum topSpaceAssum] equiv_quo_is_top[OF eqT] by auto
  have "IsContinuous(ProductTopology(T,T),T,f)" using fcon prodtop_def by auto moreover
  have "IsContinuous(T,T{quotient by}r,{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T})" using quotient_func_cont[OF quotient_proj_surj]
    unfolding EquivQuo_def[OF eqT] by auto
  ultimately have cont:"IsContinuous(ProductTopology(T,T),T{quotient by}r,{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T} O f)"
    using comp_cont by auto
  {
    fix A assume A:"A\<in>G\<times>G"
    then obtain g1 g2 where A_def:"A=\<langle>g1,g2\<rangle>" "g1\<in>G""g2\<in>G" by auto
    then have "f`A=g1\<ra>g2" and p:"g1\<ra>g2\<in>\<Union>T" unfolding grop_def using 
      apply_type[OF topgroup_f_binop] by auto
    then have "{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}`(f`A)={\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}`(g1\<ra>g2)" by auto
    with p have "{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}`(f`A)=r``{g1\<ra>g2}" using apply_equality[OF _ quotient_proj_fun]
      by auto
    then have Pr1:"({\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T} O f)`A=r``{g1\<ra>g2}" using comp_fun_apply[OF topgroup_f_binop A] by auto
    from A_def(2,3) have "\<langle>g1,g2\<rangle>\<in>\<Union>T\<times>\<Union>T" by auto
    then have "\<langle>\<langle>g1,g2\<rangle>,\<langle>r``{g1},r``{g2}\<rangle>\<rangle>\<in>{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}" by auto
    then have "{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}`A=\<langle>r``{g1},r``{g2}\<rangle>" using A_def(1) apply_equality[OF _ product_equiv_rel_fun]
      by auto
    then have "F`({\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}`A)=F`\<langle>r``{g1},r``{g2}\<rangle>" by auto
    then have "F`({\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}`A)=r``({g1\<ra>g2})" using group0.Group_ZF_2_2_L2[OF group0_valid_in_tgroup eqG C
      _ A_def(2,3)] unfolding F_def QuotientGroupOp_def r_def by auto moreover
    note fun ultimately have "(F O {\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T})`A=r``({g1\<ra>g2})" using comp_fun_apply[OF _ A] by auto
    then have "(F O {\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T})`A=({\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T} O f)`A" using Pr1 by auto
  }
  then have "(F O {\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T})=({\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T} O f)" using fun_extension[OF cc comp_fun[OF topgroup_f_binop quotient_proj_fun]]
    unfolding F_def QuotientGroupOp_def r_def by auto
  then have A:"IsContinuous(ProductTopology(T,T),T{quotient by}r,F O {\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T})" using cont by auto
  have "IsAsubgroup(H,f)" using assms(1) unfolding IsAnormalSubgroup_def by auto
  then have "\<forall>A\<in>T. {\<langle>b, r `` {b}\<rangle> . b \<in> \<Union>T} `` A \<in> ({quotient by}r)" using quotient_map_topgroup_open unfolding r_def by auto
  with eqT have "ProductTopology({quotient by}r,{quotient by}r)=({quotient topology in}(((\<Union>T)//r)\<times>((\<Union>T)//r)){by}{\<langle>\<langle>b,c\<rangle>,\<langle>r``{b},r``{c}\<rangle>\<rangle>. \<langle>b,c\<rangle>\<in>\<Union>T\<times>\<Union>T}{from}(ProductTopology(T,T)))" using prod_quotient
    by auto
  with A show "IsContinuous(ProductTopology(T{quotient by}r,T{quotient by}r),T{quotient by}r,F)"
    using two_top_spaces0.cont_quotient_top[OF two Hfun Ffun] topology0.total_quo_func[OF tprod prod_equiv_rel_surj] unfolding F_def QuotientGroupOp_def r_def
    by auto
qed

lemma (in group0) Group_ZF_2_4_L8: 
  assumes "IsAnormalSubgroup(G,P,H)" 
  defines "r \<equiv> QuotientGroupRel(G,P,H)" 
  and "F \<equiv> QuotientGroupOp(G,P,H)"
  shows "GroupInv(G//r,F):G//r\<rightarrow>G//r"
  using group0_2_T2[OF Group_ZF_2_4_T1[OF _ assms(1)]] groupAssum using assms(2,3)
    by auto

theorem (in topgroup) quotient_top_group_INV_cont:
  assumes "IsAnormalSubgroup(G,f,H)"
  defines "r \<equiv> QuotientGroupRel(G,f,H)"
  defines "F \<equiv> QuotientGroupOp(G,f,H)"
  shows "IsContinuous(T{quotient by}r,T{quotient by}r,GroupInv(G//r,F))"
proof-
  have eqT:"equiv(\<Union>T,r)" and eqG:"equiv(G,r)" using group0.Group_ZF_2_4_L3 assms(1) unfolding r_def IsAnormalSubgroup_def
    using group0_valid_in_tgroup by auto
  have two:"two_top_spaces0(T,T{quotient by}r,{\<langle>b,r``{b}\<rangle>. b\<in>G})" unfolding two_top_spaces0_def
    using topSpaceAssum equiv_quo_is_top[OF eqT] quotient_proj_fun total_quo_equi[OF eqT] by auto
  have "IsContinuous(T,T,GroupInv(G,f))" using inv_cont. moreover
  {
    fix g assume G:"g\<in>G"
    then have "GroupInv(G,f)`g=\<rm>g" using grinv_def by auto
    then have "r``({GroupInv(G,f)`g})=GroupInv(G//r,F)`(r``{g})" using group0.Group_ZF_2_4_L7
      [OF group0_valid_in_tgroup assms(1) G] unfolding r_def F_def by auto
    then have "{\<langle>b,r``{b}\<rangle>. b\<in>G}`(GroupInv(G,f)`g)=GroupInv(G//r,F)`({\<langle>b,r``{b}\<rangle>. b\<in>G}`g)"
      using apply_equality[OF _ quotient_proj_fun] G neg_in_tgroup unfolding grinv_def
      by auto
    then have "({\<langle>b,r``{b}\<rangle>. b\<in>G}O GroupInv(G,f))`g=(GroupInv(G//r,F)O {\<langle>b,r``{b}\<rangle>. b\<in>G})`g"
      using comp_fun_apply[OF quotient_proj_fun G] comp_fun_apply[OF group0_2_T2[OF Ggroup] G] by auto
  }
  then have A1:"{\<langle>b,r``{b}\<rangle>. b\<in>G}O GroupInv(G,f)=GroupInv(G//r,F)O {\<langle>b,r``{b}\<rangle>. b\<in>G}" using fun_extension[
    OF comp_fun[OF quotient_proj_fun group0.Group_ZF_2_4_L8[OF group0_valid_in_tgroup assms(1)]] 
    comp_fun[OF group0_2_T2[OF Ggroup] quotient_proj_fun[of "G""r"]]] unfolding r_def F_def by auto
  have "IsContinuous(T,T{quotient by}r,{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T})" using quotient_func_cont[OF quotient_proj_surj]
    unfolding EquivQuo_def[OF eqT] by auto
  ultimately have "IsContinuous(T,T{quotient by}r,{\<langle>b,r``{b}\<rangle>. b\<in>\<Union>T}O GroupInv(G,f))"
    using comp_cont by auto
  with A1 have "IsContinuous(T,T{quotient by}r,GroupInv(G//r,F)O {\<langle>b,r``{b}\<rangle>. b\<in>G})" by auto
  then have "IsContinuous({quotient topology in}(\<Union>T) // r{by}{\<langle>b, r `` {b}\<rangle> . b \<in> \<Union>T}{from}T,T{quotient by}r,GroupInv(G//r,F))"
    using two_top_spaces0.cont_quotient_top[OF two quotient_proj_surj, of "GroupInv(G//r,F)""r"] group0.Group_ZF_2_4_L8[OF group0_valid_in_tgroup assms(1)]
    using total_quo_equi[OF eqT] unfolding r_def F_def by auto
  then show ?thesis unfolding EquivQuo_def[OF eqT].
qed

text\<open>Finally we can prove that quotient groups of topological groups
 are topological groups.\<close>

theorem(in topgroup) quotient_top_group:
  assumes "IsAnormalSubgroup(G,f,H)"
  defines "r \<equiv> QuotientGroupRel(G,f,H)"
  defines "F \<equiv> QuotientGroupOp(G,f,H)"
  shows "IsAtopologicalGroup({quotient by}r,F)"
    unfolding IsAtopologicalGroup_def using total_quo_equi equiv_quo_is_top
    Group_ZF_2_4_T1 Ggroup assms(1) quotient_top_group_INV_cont quotient_top_group_F_cont
    group0.Group_ZF_2_4_L3 group0_valid_in_tgroup assms(1) unfolding r_def F_def IsAnormalSubgroup_def
    by auto


end
