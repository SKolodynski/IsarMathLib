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

section \<open>Topological groups 1\<close>

theory TopologicalGroup_ZF_1 imports TopologicalGroup_ZF Topology_ZF_properties_2
begin

text\<open>This theory deals with some topological properties of topological groups.\<close>

subsection\<open>Separation properties of topological groups\<close>
text\<open>The topological groups have very specific properties. For instance, $G$ is \<open>T\<^sub>0\<close>
iff it is \<open>T\<^sub>3\<close>.\<close>

theorem(in topgroup) cl_point:
  assumes "x\<in>G"
  shows "cl({x}) = (\<Inter>H\<in>\<N>\<^sub>0. x\<ltr>H)"
proof-
  {
    have c:"cl({x}) = (\<Inter>H\<in>\<N>\<^sub>0. {x}\<sad>H)" using cl_topgroup assms by auto
    {
      fix H
      assume "H\<in>\<N>\<^sub>0"
      then have "{x}\<sad>H=x\<ltr> H" using interval_add(3) assms
        by auto
      with \<open>H\<in>\<N>\<^sub>0\<close> have "{x}\<sad>H\<in>{x\<ltr>H. H\<in>\<N>\<^sub>0}" by auto
    }
    then have "{{x}\<sad>H. H\<in>\<N>\<^sub>0}\<subseteq>{x\<ltr>H. H\<in>\<N>\<^sub>0}" by auto
    moreover
    {
      fix H
      assume "H\<in>\<N>\<^sub>0"
      then have "{x}\<sad>H=x\<ltr> H" using interval_add(3) assms
        by auto
      with \<open>H\<in>\<N>\<^sub>0\<close> have "x\<ltr> H\<in>{{x}\<sad>H. H\<in>\<N>\<^sub>0}" by auto
    }
    then have "{x\<ltr>H. H\<in>\<N>\<^sub>0}\<subseteq>{{x}\<sad>H. H\<in>\<N>\<^sub>0}" by auto
    ultimately have "{{x}\<sad>H. H\<in>\<N>\<^sub>0}={x\<ltr>H. H\<in>\<N>\<^sub>0}" by auto
    then have "(\<Inter>H\<in>\<N>\<^sub>0. {x}\<sad>H) = (\<Inter>H\<in>\<N>\<^sub>0. x\<ltr>H)" by auto
    with c show "cl({x})=(\<Inter>H\<in>\<N>\<^sub>0. x\<ltr>H)" by auto
  }
qed

text\<open>We prove the equivalence between $T_0$ and $T_1$ first.\<close>

theorem (in topgroup) neu_closed_imp_T1:
  assumes "{\<zero>}{is closed in}T"
  shows "T{is T\<^sub>1}"
proof-
  {
    fix x z assume xG:"x\<in>G" and zG:"z\<in>G" and dis:"x\<noteq>z"
    then have clx:"cl({x})=(\<Inter>H\<in>\<N>\<^sub>0. x\<ltr>H)" using cl_point by auto
    {
      fix y
      assume "y\<in>cl({x})"
      with clx have "y\<in>(\<Inter>H\<in>\<N>\<^sub>0. x\<ltr>H)" by auto
      then have t:"\<forall>H\<in>\<N>\<^sub>0. y\<in>x\<ltr>H" by auto
      from \<open>y\<in>cl({x})\<close> xG have yG:"y\<in>G" using Top_3_L11(1) G_def by auto
      {
        fix H
        assume HNeig:"H\<in>\<N>\<^sub>0"
        with t have "y\<in>x\<ltr>H" by auto
        then obtain n where "y=x\<ra>n" and "n\<in>H" unfolding ltrans_def grop_def LeftTranslation_def by auto
        with HNeig have nG:"n\<in>G" unfolding zerohoods_def by auto
        from \<open>y=x\<ra>n\<close> and \<open>n\<in>H\<close> have "(\<rm>x)\<ra>y\<in>H" using group0.group0_2_L18(2) group0_valid_in_tgroup xG nG yG unfolding grinv_def grop_def
          by auto
      }
      then have el:"(\<rm>x)\<ra>y\<in>(\<Inter>\<N>\<^sub>0)" using zneigh_not_empty by auto
      have "cl({\<zero>})=(\<Inter>H\<in>\<N>\<^sub>0. \<zero>\<ltr>H)" using cl_point zero_in_tgroup by auto
      moreover
      {
        fix H  assume "H\<in>\<N>\<^sub>0"
        then have "H\<subseteq>G" unfolding zerohoods_def by auto
        then have "\<zero>\<ltr>H=H" using image_id_same  group0.trans_neutral(2) group0_valid_in_tgroup unfolding gzero_def ltrans_def
          by auto
        with \<open>H\<in>\<N>\<^sub>0\<close> have "\<zero>\<ltr>H\<in>\<N>\<^sub>0" "H\<in>{\<zero>\<ltr>H. H\<in>\<N>\<^sub>0}" by auto
      }
      then have "{\<zero>\<ltr>H. H\<in>\<N>\<^sub>0}=\<N>\<^sub>0" by blast
      ultimately have "cl({\<zero>})=(\<Inter>\<N>\<^sub>0)" by auto
      with el have "(\<rm>x)\<ra>y\<in>cl({\<zero>})" by auto
      then have "(\<rm>x)\<ra>y\<in>{\<zero>}" using assms Top_3_L8 G_def zero_in_tgroup by auto
      then have "(\<rm>x)\<ra>y=\<zero>" by auto
      then have "y=\<rm>(\<rm>x)" using group0.group0_2_L9(2) group0_valid_in_tgroup neg_in_tgroup xG yG unfolding grop_def grinv_def by auto
      then have "y=x" using group0.group_inv_of_inv group0_valid_in_tgroup xG unfolding grinv_def by auto
    }
    then have "cl({x})\<subseteq>{x}" by auto
    then have "cl({x})={x}" using xG cl_contains_set G_def by blast
    then have "{x}{is closed in}T" using Top_3_L8 xG G_def by auto
    then have "(\<Union>T)-{x}\<in>T" using IsClosed_def by auto moreover
    from dis zG G_def have "z\<in>((\<Union>T)-{x}) \<and> x\<notin>((\<Union>T)-{x})" by auto
    ultimately have "\<exists>V\<in>T. z\<in>V\<and>x\<notin>V" by(safe,auto)
  }
  then show "T{is T\<^sub>1}" using isT1_def by auto
qed

theorem (in topgroup) T0_imp_neu_closed:
  assumes "T{is T\<^sub>0}"
  shows "{\<zero>}{is closed in}T"
proof-
  {
    fix x assume "x\<in>cl({\<zero>})" and "x\<noteq>\<zero>"
    have "cl({\<zero>})=(\<Inter>H\<in>\<N>\<^sub>0. \<zero>\<ltr>H)" using cl_point zero_in_tgroup by auto
    moreover
    {
      fix H  assume "H\<in>\<N>\<^sub>0"
      then have "H\<subseteq>G" unfolding zerohoods_def by auto
      then have "\<zero>\<ltr>H=H" using image_id_same  group0.trans_neutral(2) group0_valid_in_tgroup unfolding gzero_def ltrans_def
        by auto
      with \<open>H\<in>\<N>\<^sub>0\<close> have "\<zero>\<ltr>H\<in>\<N>\<^sub>0" "H\<in>{\<zero>\<ltr>H. H\<in>\<N>\<^sub>0}" by auto
    }
    then have "{\<zero>\<ltr>H. H\<in>\<N>\<^sub>0}=\<N>\<^sub>0" by blast
    ultimately have "cl({\<zero>})=(\<Inter>\<N>\<^sub>0)" by auto
    from \<open>x\<noteq>\<zero>\<close> and \<open>x\<in>cl({\<zero>})\<close> obtain U where "U\<in>T" and "(x\<notin>U\<and>\<zero>\<in>U)\<or>(\<zero>\<notin>U\<and>x\<in>U)" using assms Top_3_L11(1)
      zero_in_tgroup unfolding isT0_def G_def by blast moreover
    {
      assume "\<zero>\<in>U"
      with \<open>U\<in>T\<close> have "U\<in>\<N>\<^sub>0" using zerohoods_def G_def Top_2_L3 by auto
      with \<open>x\<in>cl({\<zero>})\<close> and \<open>cl({\<zero>})=(\<Inter>\<N>\<^sub>0)\<close> have "x\<in>U" by auto
    }
    ultimately have "\<zero>\<notin>U" and "x\<in>U" by auto
    with \<open>U\<in>T\<close> \<open>x\<in>cl({\<zero>})\<close> have "False" using cl_inter_neigh zero_in_tgroup unfolding G_def by blast
  }
  then have "cl({\<zero>})\<subseteq>{\<zero>}" by auto
  then have "cl({\<zero>})={\<zero>}" using zero_in_tgroup cl_contains_set G_def by blast
  then show ?thesis using Top_3_L8 zero_in_tgroup unfolding G_def by auto
qed

subsection\<open>Existence of nice neighbourhoods.\<close>

theorem(in topgroup) exists_sym_zerohood:
  assumes "U\<in>\<N>\<^sub>0"
  shows "\<exists>V\<in>\<N>\<^sub>0. (V\<subseteq>U\<and> (\<sm>V)=V)"
proof
  let ?V="U\<inter>(\<sm>U)"
  have "U\<subseteq>G" using assms unfolding zerohoods_def by auto
  then have "?V\<subseteq>G" by auto
  have invg:" GroupInv(G, f) \<in> G \<rightarrow> G" using group0_2_T2 Ggroup by auto
  have invb:"GroupInv(G, f) \<in>bij(G,G)" using group0.group_inv_bij(2) group0_valid_in_tgroup by auto
  have "(\<sm>?V)=GroupInv(G,f)-``?V" unfolding setninv_def using group0.inv_image_vimage group0_valid_in_tgroup by auto
  also have "\<dots>=(GroupInv(G,f)-``U)\<inter>(GroupInv(G,f)-``(\<sm>U))" using invim_inter_inter_invim invg by auto
  also have "\<dots>=(\<sm>U)\<inter>(GroupInv(G,f)-``(GroupInv(G,f)``U))" unfolding setninv_def using group0.inv_image_vimage group0_valid_in_tgroup by auto
  also with \<open>U\<subseteq>G\<close> have "\<dots>=(\<sm>U)\<inter>U" using inj_vimage_image invb unfolding bij_def
    by auto
  finally have "(\<sm>?V)=?V" by auto
  then show "?V \<subseteq> U \<and> (\<sm> ?V) = ?V" by auto
  from assms have "(\<sm>U)\<in>\<N>\<^sub>0" using neg_neigh_neigh by auto
  with assms have "\<zero>\<in>int(U)\<inter>int(\<sm>U)" unfolding zerohoods_def by auto
  moreover 
  have "int(U)\<inter>int(\<sm>U)\<in>T" using Top_2_L3 IsATopology_def topSpaceAssum Top_2_L4 by auto
  then have int:"int(int(U)\<inter>int(\<sm>U))=int(U)\<inter>int(\<sm>U)" using Top_2_L3 by auto
  have "int(U)\<inter>int(\<sm>U)\<subseteq>?V" using Top_2_L1 by auto
  from interior_mono[OF this] int have "int(U)\<inter>int(\<sm>U)\<subseteq>int(?V)" by auto
  ultimately have "\<zero>\<in>int(?V)" by auto
  with \<open>?V\<subseteq>G\<close> show "?V\<in>\<N>\<^sub>0" using zerohoods_def by auto
qed 

theorem(in topgroup) exists_procls_zerohood:
  assumes "U\<in>\<N>\<^sub>0"
  shows "\<exists>V\<in>\<N>\<^sub>0. (V\<subseteq>U\<and> (V\<sad>V)\<subseteq>U \<and> (\<sm>V)=V)"
proof-
  have "int(U)\<in>T" using Top_2_L2 by auto
  then have "f-``(int(U))\<in>\<tau>" using fcon IsContinuous_def by auto
  moreover 
  have fne:"f ` \<langle>\<zero>, \<zero>\<rangle> = \<zero>" using group0.group0_2_L2 group0_valid_in_tgroup by auto
  have "\<zero>\<in>int(U)" using assms unfolding zerohoods_def by auto
  then have "f -`` {\<zero>}\<subseteq>f-``(int(U))" using func1_1_L8 vimage_def by auto
  then have "GroupInv(G,f)\<subseteq>f-``(int(U))" using group0.group0_2_T3 group0_valid_in_tgroup by auto
  then have "\<langle>\<zero>,\<zero>\<rangle>\<in>f-``(int(U))" using fne zero_in_tgroup unfolding GroupInv_def
    by auto
  ultimately obtain W V where wop:"W\<in>T" and vop:"V\<in>T" and cartsub:"W\<times>V\<subseteq>f-``(int(U))" and zerhood:"\<langle>\<zero>,\<zero>\<rangle>\<in>W\<times>V" using prod_top_point_neighb topSpaceAssum
    unfolding prodtop_def by force
  then have "\<zero>\<in>W" and "\<zero>\<in>V" by auto
  then have "\<zero>\<in>W\<inter>V" by auto
  have sub:"W\<inter>V\<subseteq>G" using wop vop G_def by auto
  have assoc:"f\<in>G\<times>G\<rightarrow>G" using group0.group_oper_assocA group0_valid_in_tgroup by auto
  {
    fix t s assume "t\<in>W\<inter>V" and "s\<in>W\<inter>V"
    then have "t\<in>W" and "s\<in>V" by auto
    then have "\<langle>t,s\<rangle>\<in>W\<times>V" by auto
    then have "\<langle>t,s\<rangle>\<in>f-``(int(U))" using cartsub by auto
    then have "f`\<langle>t,s\<rangle>\<in>int(U)" using func1_1_L15 assoc by auto
  }
  then have "{f`\<langle>t,s\<rangle>. \<langle>t,s\<rangle>\<in>(W\<inter>V)\<times>(W\<inter>V)}\<subseteq>int(U)" by auto
  then have "(W\<inter>V)\<sad>(W\<inter>V)\<subseteq>int(U)" unfolding setadd_def using lift_subsets_explained(4) assoc sub
    by auto
  then have "(W\<inter>V)\<sad>(W\<inter>V)\<subseteq>U" using Top_2_L1 by auto
  from topSpaceAssum have "W\<inter>V\<in>T" using vop wop unfolding IsATopology_def by auto
  then have "int(W\<inter>V)=W\<inter>V" using Top_2_L3 by auto
  with sub \<open>\<zero>\<in>W\<inter>V\<close> have "W\<inter>V\<in>\<N>\<^sub>0" unfolding zerohoods_def by auto
  then obtain Q where "Q\<in>\<N>\<^sub>0" and "Q\<subseteq>W\<inter>V" and "(\<sm>Q)=Q" using exists_sym_zerohood by blast
  then have "Q\<times>Q\<subseteq>(W\<inter>V)\<times>(W\<inter>V)" by auto 
  moreover from \<open>Q\<subseteq>W\<inter>V\<close> have "W\<inter>V\<subseteq>G" and "Q\<subseteq>G" using vop wop unfolding G_def by auto
  ultimately have "Q\<sad>Q\<subseteq>(W\<inter>V)\<sad>(W\<inter>V)" using interval_add(2) func1_1_L8 by auto
  with \<open>(W\<inter>V)\<sad>(W\<inter>V)\<subseteq>U\<close> have "Q\<sad>Q\<subseteq>U" by auto
  from \<open>Q\<in>\<N>\<^sub>0\<close> have "\<zero>\<in>Q" unfolding zerohoods_def using Top_2_L1 by auto
  with \<open>Q\<sad>Q\<subseteq>U\<close> \<open>Q\<subseteq>G\<close> have "\<zero>\<ltr>Q\<subseteq>U" using interval_add(3) by auto
  with \<open>Q\<subseteq>G\<close> have "Q\<subseteq>U" unfolding ltrans_def using group0.trans_neutral(2) group0_valid_in_tgroup
    unfolding gzero_def using image_id_same by auto
  with \<open>Q\<in>\<N>\<^sub>0\<close> \<open>Q\<sad>Q\<subseteq>U\<close> \<open>(\<sm>Q)=Q\<close> show ?thesis by auto
qed


lemma (in topgroup) exist_basehoods_closed:
  assumes "U\<in>\<N>\<^sub>0"
  shows "\<exists>V\<in>\<N>\<^sub>0. cl(V)\<subseteq>U"
proof-
  from assms obtain V where "V\<in>\<N>\<^sub>0" "V\<subseteq>U" "(V\<sad>V)\<subseteq>U" "(\<sm>V)=V" using exists_procls_zerohood by blast
  have inv_fun:"GroupInv(G,f)\<in>G\<rightarrow>G" using group0_2_T2 Ggroup by auto
  have f_fun:"f\<in>G\<times>G\<rightarrow>G" using group0.group_oper_assocA group0_valid_in_tgroup by auto
  {
    fix x assume "x\<in>cl(V)"
    with \<open>V\<in>\<N>\<^sub>0\<close> have "x\<in>\<Union>T" "V\<subseteq>\<Union>T" using Top_3_L11(1) unfolding zerohoods_def G_def by blast+
    with \<open>V\<in>\<N>\<^sub>0\<close> have "x\<in>int(x\<ltr>V)" using elem_in_int_trans G_def by auto
    with \<open>V\<subseteq>\<Union>T\<close>\<open>x\<in>cl(V)\<close> have "int(x\<ltr>V)\<inter>V\<noteq>0" using cl_inter_neigh Top_2_L2 by blast
    then have "(x\<ltr>V)\<inter>V\<noteq>0" using Top_2_L1 by blast
    then obtain q where "q\<in>(x\<ltr>V)" and "q\<in>V" by blast
    with \<open>V\<subseteq>\<Union>T\<close>\<open>x\<in>\<Union>T\<close> obtain v where "q=x\<ra>v" "v\<in>V" unfolding ltrans_def grop_def using group0.ltrans_image
      group0_valid_in_tgroup unfolding G_def by auto
    from \<open>V\<subseteq>\<Union>T\<close> \<open>v\<in>V\<close>\<open>q\<in>V\<close> have "v\<in>\<Union>T" "q\<in>\<Union>T" by auto
    with \<open>q=x\<ra>v\<close>\<open>x\<in>\<Union>T\<close> have "q\<rs>v=x" using group0.group0_2_L18(1) group0_valid_in_tgroup unfolding G_def
        unfolding grsub_def grinv_def grop_def by auto moreover
    from \<open>v\<in>V\<close> have "(\<rm>v)\<in>(\<sm>V)" unfolding setninv_def grinv_def using func_imagedef inv_fun \<open>V\<subseteq>\<Union>T\<close> G_def by auto
    then have "(\<rm>v)\<in>V" using \<open>(\<sm>V)=V\<close> by auto
    with \<open>q\<in>V\<close> have "\<langle>q,\<rm>v\<rangle>\<in>V\<times>V" by auto
    then have "f`\<langle>q,\<rm>v\<rangle>\<in>V\<sad>V" using lift_subset_suff f_fun \<open>V\<subseteq>\<Union>T\<close> unfolding setadd_def by auto
    with \<open>V\<sad>V\<subseteq>U\<close> have "q\<rs>v\<in>U" unfolding grsub_def grop_def by auto
    with \<open>q\<rs>v=x\<close> have "x\<in>U" by auto
  }
  then have "cl(V)\<subseteq>U" by auto
  with \<open>V\<in>\<N>\<^sub>0\<close> show ?thesis by auto
qed

subsection\<open>Rest of separation axioms\<close>

theorem(in topgroup) T1_imp_T2:
  assumes "T{is T\<^sub>1}"
  shows "T{is T\<^sub>2}"
proof-
  {
    fix x y assume ass:"x\<in>\<Union>T" "y\<in>\<Union>T" "x\<noteq>y"
    {
      assume "(\<rm>y)\<ra>x=\<zero>"
      with ass(1,2) have "y=x" using group0.group0_2_L11[where a="y" and b="x"] group0_valid_in_tgroup by auto (*cannot be erased.*)
      with ass(3) have "False" by auto
    }
    then have "(\<rm>y)\<ra>x\<noteq>\<zero>" by auto
    then have "\<zero>\<noteq>(\<rm>y)\<ra>x" by auto
    from \<open>y\<in>\<Union>T\<close> have "(\<rm>y)\<in>\<Union>T" using neg_in_tgroup G_def by auto
    with \<open>x\<in>\<Union>T\<close> have "(\<rm>y)\<ra>x\<in>\<Union>T" using group0.group_op_closed[where a="\<rm>y" and b="x"] group0_valid_in_tgroup unfolding (*cannot be erased.*)
      G_def by auto
    with assms \<open>\<zero>\<noteq>(\<rm>y)\<ra>x\<close> obtain U where "U\<in>T" and "(\<rm>y)\<ra>x\<notin>U" and "\<zero>\<in>U" unfolding isT1_def using zero_in_tgroup
      by auto
    then have "U\<in>\<N>\<^sub>0" unfolding zerohoods_def G_def using Top_2_L3 by auto
    then obtain Q where "Q\<in>\<N>\<^sub>0" "Q\<subseteq>U" "(Q\<sad>Q)\<subseteq>U" "(\<sm>Q)=Q" using exists_procls_zerohood by blast
    with \<open>(\<rm>y)\<ra>x\<notin>U\<close> have "(\<rm>y)\<ra>x\<notin>Q" by auto
    from \<open>Q\<in>\<N>\<^sub>0\<close> have "Q\<subseteq>G" unfolding zerohoods_def by auto
    {
      assume "x\<in>y\<ltr>Q"
      with \<open>Q\<subseteq>G\<close> \<open>y\<in>\<Union>T\<close> obtain u where "u\<in>Q" and "x=y\<ra>u" unfolding ltrans_def grop_def using group0.ltrans_image group0_valid_in_tgroup
        unfolding G_def by auto
      with \<open>Q\<subseteq>G\<close> have "u\<in>\<Union>T" unfolding G_def by auto
      with \<open>x=y\<ra>u\<close> \<open>y\<in>\<Union>T\<close> \<open>x\<in>\<Union>T\<close> \<open>Q\<subseteq>G\<close> have "(\<rm>y)\<ra>x=u" using group0.group0_2_L18(2) group0_valid_in_tgroup unfolding G_def
        unfolding grsub_def grinv_def grop_def by auto
      with \<open>u\<in>Q\<close> have "(\<rm>y)\<ra>x\<in>Q" by auto
      then have "False" using \<open>(\<rm>y)\<ra>x\<notin>Q\<close> by auto
    }
    then have "x\<notin>y\<ltr>Q" by auto moreover
    {
      assume "y\<in>x\<ltr>Q"
      with \<open>Q\<subseteq>G\<close> \<open>x\<in>\<Union>T\<close> obtain u where "u\<in>Q" and "y=x\<ra>u" unfolding ltrans_def grop_def using group0.ltrans_image group0_valid_in_tgroup
        unfolding G_def by auto
      with \<open>Q\<subseteq>G\<close> have "u\<in>\<Union>T" unfolding G_def by auto
      with \<open>y=x\<ra>u\<close> \<open>y\<in>\<Union>T\<close> \<open>x\<in>\<Union>T\<close> \<open>Q\<subseteq>G\<close> have "(\<rm>x)\<ra>y=u" using group0.group0_2_L18(2) group0_valid_in_tgroup unfolding G_def
        unfolding grsub_def grinv_def grop_def by auto
      with \<open>u\<in>Q\<close> have "(\<rm>y)\<ra>x=\<rm>u" using group0.group_inv_of_two[OF group0_valid_in_tgroup group0.inverse_in_group[OF group0_valid_in_tgroup,of x],of y] (*From here no checked*)
        using \<open>x\<in>\<Union>T\<close> \<open>y\<in>\<Union>T\<close> using group0.group_inv_of_inv[OF group0_valid_in_tgroup] unfolding G_def grinv_def grop_def by auto
      moreover from \<open>u\<in>Q\<close> have "(\<rm>u)\<in>(\<sm>Q)" unfolding setninv_def grinv_def using func_imagedef[OF group0_2_T2[OF Ggroup] \<open>Q\<subseteq>G\<close>] by auto
      ultimately have "(\<rm>y)\<ra>x\<in>Q" using \<open>(\<rm>y)\<ra>x\<notin>Q\<close> \<open>(\<sm>Q)=Q\<close> unfolding setninv_def grinv_def by auto
      then have "False" using \<open>(\<rm>y)\<ra>x\<notin>Q\<close> by auto
    }
    then have "y\<notin>x\<ltr>Q" by auto moreover
    {
      fix t
      assume "t\<in>(x\<ltr>Q)\<inter>(y\<ltr>Q)"
      then have "t\<in>(x\<ltr>Q)" "t\<in>(y\<ltr>Q)" by auto
      with \<open>Q\<subseteq>G\<close> \<open>x\<in>\<Union>T\<close> \<open>y\<in>\<Union>T\<close> obtain u v where "u\<in>Q" "v\<in>Q" and "t=x\<ra>u" "t=y\<ra>v" unfolding ltrans_def grop_def using group0.ltrans_image[OF group0_valid_in_tgroup]
        unfolding G_def by auto
      then have "x\<ra>u=y\<ra>v" by auto
      moreover from \<open>u\<in>Q\<close> \<open>v\<in>Q\<close> \<open>Q\<subseteq>G\<close> have "u\<in>\<Union>T" "v\<in>\<Union>T" unfolding G_def by auto
      moreover note \<open>x\<in>\<Union>T\<close> \<open>y\<in>\<Union>T\<close>
      ultimately have "(\<rm>y)\<ra>(x\<ra>u)=v" using group0.group0_2_L18(2)[OF group0_valid_in_tgroup, of y v "x\<ra>u"] group0.group_op_closed[OF group0_valid_in_tgroup, of x u] unfolding G_def
        unfolding grsub_def grinv_def grop_def by auto
      then have "((\<rm>y)\<ra>x)\<ra>u=v" using group0.group_oper_assoc[OF group0_valid_in_tgroup]
        unfolding grop_def using \<open>x\<in>\<Union>T\<close> \<open>y\<in>\<Union>T\<close> \<open>u\<in>\<Union>T\<close> using group0.inverse_in_group[OF group0_valid_in_tgroup] unfolding G_def
        by auto
      then have "((\<rm>y)\<ra>x)=v\<rs>u" using group0.group0_2_L18(1)[OF group0_valid_in_tgroup,of "(\<rm>y)\<ra>x" u v]
        using \<open>(\<rm>y)\<ra>x\<in>\<Union>T\<close> \<open>u\<in>\<Union>T\<close> \<open>v\<in>\<Union>T\<close> unfolding G_def grsub_def grinv_def grop_def by force
      moreover 
      from \<open>u\<in>Q\<close> have "(\<rm>u)\<in>(\<sm>Q)" unfolding setninv_def grinv_def using func_imagedef[OF group0_2_T2[OF Ggroup] \<open>Q\<subseteq>G\<close>] by auto
      then have "(\<rm>u)\<in>Q" using \<open>(\<sm>Q)=Q\<close> by auto
      with \<open>v\<in>Q\<close> have "\<langle>v,\<rm>u\<rangle>\<in>Q\<times>Q" by auto
      then have "f`\<langle>v,\<rm>u\<rangle>\<in>Q\<sad>Q" using lift_subset_suff[OF group0.group_oper_assocA[OF group0_valid_in_tgroup] \<open>Q\<subseteq>G\<close> \<open>Q\<subseteq>G\<close>]
        unfolding setadd_def by auto
      with \<open>Q\<sad>Q\<subseteq>U\<close> have "v\<rs>u\<in>U" unfolding grsub_def grop_def by auto
      ultimately have "(\<rm>y)\<ra>x\<in>U" by auto
      with \<open>(\<rm>y)\<ra>x\<notin>U\<close> have "False" by auto
    }
    then have "(x\<ltr>Q)\<inter>(y\<ltr>Q)=0" by auto
    moreover have "x\<in>int(x\<ltr>Q)""y\<in>int(y\<ltr>Q)" using elem_in_int_trans \<open>Q\<in>\<N>\<^sub>0\<close>
      \<open>x\<in>\<Union>T\<close> \<open>y\<in>\<Union>T\<close> unfolding G_def by auto moreover
    have "int(x\<ltr>Q)\<subseteq>(x\<ltr>Q)""int(y\<ltr>Q)\<subseteq>(y\<ltr>Q)" using Top_2_L1 by auto
    moreover have "int(x\<ltr>Q)\<in>T" "int(y\<ltr>Q)\<in>T" using Top_2_L2 by auto
    ultimately have "int(x\<ltr>Q)\<in>T \<and> int(y\<ltr>Q)\<in>T \<and> x \<in> int(x\<ltr>Q) \<and> y \<in> int(y\<ltr>Q) \<and> int(x\<ltr>Q) \<inter> int(y\<ltr>Q) = 0"
      by blast
    then have "\<exists>U\<in>T. \<exists>V\<in>T. x\<in>U\<and>y\<in>V\<and>U\<inter>V=0" by auto
  }
  then show ?thesis using isT2_def by auto
qed

text\<open>Here follow some auxiliary lemmas.\<close>

lemma (in topgroup) trans_closure:
  assumes "x\<in>G" "A\<subseteq>G"
  shows "cl(x\<ltr>A)=x\<ltr>cl(A)"
proof-
  have "\<Union>T-(\<Union>T-(x\<ltr>A))=(x\<ltr>A)" unfolding ltrans_def using group0.group0_5_L1(2)[OF group0_valid_in_tgroup assms(1)]
    unfolding image_def range_def domain_def converse_def Pi_def by auto
  then have "cl(x\<ltr>A)=\<Union>T-int(\<Union>T-(x\<ltr>A))" using Top_3_L11(2)[of "\<Union>T-(x\<ltr>A)"] by auto moreover
  have "x\<ltr>G=G" using surj_image_eq group0.trans_bij(2)[OF group0_valid_in_tgroup assms(1)] bij_def by auto
  then have "\<Union>T-(x\<ltr>A)=x\<ltr>(\<Union>T-A)" using inj_image_dif[of "LeftTranslation(G, f, x)""G""G", OF _ assms(2)]
    unfolding ltrans_def G_def using group0.trans_bij(2)[OF group0_valid_in_tgroup assms(1)] bij_def by auto
  then have "int(\<Union>T-(x\<ltr>A))=int(x\<ltr>(\<Union>T-A))" by auto
  then have "int(\<Union>T-(x\<ltr>A))=x\<ltr>int(\<Union>T-A)" using trans_interior[OF assms(1),of "\<Union>T-A"] unfolding G_def by force
  have "\<Union>T-int(\<Union>T-A)=cl(\<Union>T-(\<Union>T-A))" using Top_3_L11(2)[of "\<Union>T-A"] by force
  have "\<Union>T-(\<Union>T-A)=A" using assms(2) G_def by auto
  with \<open>\<Union>T-int(\<Union>T-A)=cl(\<Union>T-(\<Union>T-A))\<close> have "\<Union>T-int(\<Union>T-A)=cl(A)" by auto
  have "\<Union>T-(\<Union>T-int(\<Union>T-A))=int(\<Union>T-A)" using Top_2_L2 by auto
  with \<open>\<Union>T-int(\<Union>T-A)=cl(A)\<close> have "int(\<Union>T-A)=\<Union>T-cl(A)" by auto
  with \<open>int(\<Union>T-(x\<ltr>A))=x\<ltr>int(\<Union>T-A)\<close> have "int(\<Union>T-(x\<ltr>A))=x\<ltr>(\<Union>T-cl(A))" by auto
  with \<open>x\<ltr>G=G\<close> have "int(\<Union>T-(x\<ltr>A))=\<Union>T-(x\<ltr>cl(A))" using inj_image_dif[of "LeftTranslation(G, f, x)""G""G""cl(A)"]
    unfolding ltrans_def using group0.trans_bij(2)[OF group0_valid_in_tgroup assms(1)] Top_3_L11(1) assms(2) unfolding bij_def G_def
    by auto
  then have "\<Union>T-int(\<Union>T-(x\<ltr>A))=\<Union>T-(\<Union>T-(x\<ltr>cl(A)))" by auto
  then have "\<Union>T-int(\<Union>T-(x\<ltr>A))=x\<ltr>cl(A)" unfolding ltrans_def using group0.group0_5_L1(2)[OF group0_valid_in_tgroup assms(1)]
    unfolding image_def range_def domain_def converse_def Pi_def by auto
  with \<open>cl(x\<ltr>A)=\<Union>T-int(\<Union>T-(x\<ltr>A))\<close> show ?thesis by auto
qed

lemma (in topgroup) trans_interior2: assumes A1: "g\<in>G" and A2: "A\<subseteq>G" 
  shows "int(A)\<rtr>g = int(A\<rtr>g)"
proof -
  from assms have "A \<subseteq> \<Union>T" and "IsAhomeomorphism(T,T,RightTranslation(G,f,g))"
    using tr_homeo by auto
  then show ?thesis using int_top_invariant by simp
qed

lemma (in topgroup) trans_closure2:
  assumes "x\<in>G" "A\<subseteq>G"
  shows "cl(A\<rtr>x)=cl(A)\<rtr>x"
proof-
  have "\<Union>T-(\<Union>T-(A\<rtr>x))=(A\<rtr>x)" unfolding ltrans_def using group0.group0_5_L1(1)[OF group0_valid_in_tgroup assms(1)]
    unfolding image_def range_def domain_def converse_def Pi_def by auto
  then have "cl(A\<rtr>x)=\<Union>T-int(\<Union>T-(A\<rtr>x))" using Top_3_L11(2)[of "\<Union>T-(A\<rtr>x)"] by auto moreover
  have "G\<rtr>x=G" using surj_image_eq group0.trans_bij(1)[OF group0_valid_in_tgroup assms(1)] bij_def by auto
  then have "\<Union>T-(A\<rtr>x)=(\<Union>T-A)\<rtr>x" using inj_image_dif[of "RightTranslation(G, f, x)""G""G", OF _ assms(2)]
    unfolding rtrans_def G_def using group0.trans_bij(1)[OF group0_valid_in_tgroup assms(1)] bij_def by auto
  then have "int(\<Union>T-(A\<rtr>x))=int((\<Union>T-A)\<rtr>x)" by auto
  then have "int(\<Union>T-(A\<rtr>x))=int(\<Union>T-A)\<rtr>x" using trans_interior2[OF assms(1),of "\<Union>T-A"] unfolding G_def by force
  have "\<Union>T-int(\<Union>T-A)=cl(\<Union>T-(\<Union>T-A))" using Top_3_L11(2)[of "\<Union>T-A"] by force
  have "\<Union>T-(\<Union>T-A)=A" using assms(2) G_def by auto
  with \<open>\<Union>T-int(\<Union>T-A)=cl(\<Union>T-(\<Union>T-A))\<close> have "\<Union>T-int(\<Union>T-A)=cl(A)" by auto
  have "\<Union>T-(\<Union>T-int(\<Union>T-A))=int(\<Union>T-A)" using Top_2_L2 by auto
  with \<open>\<Union>T-int(\<Union>T-A)=cl(A)\<close> have "int(\<Union>T-A)=\<Union>T-cl(A)" by auto
  with \<open>int(\<Union>T-(A\<rtr>x))=int(\<Union>T-A)\<rtr>x\<close> have "int(\<Union>T-(A\<rtr>x))=(\<Union>T-cl(A))\<rtr>x" by auto
  with \<open>G\<rtr>x=G\<close> have "int(\<Union>T-(A\<rtr>x))=\<Union>T-(cl(A)\<rtr>x)" using inj_image_dif[of "RightTranslation(G, f, x)""G""G""cl(A)"]
    unfolding rtrans_def using group0.trans_bij(1)[OF group0_valid_in_tgroup assms(1)] Top_3_L11(1) assms(2) unfolding bij_def G_def
    by auto
  then have "\<Union>T-int(\<Union>T-(A\<rtr>x))=\<Union>T-(\<Union>T-(cl(A)\<rtr>x))" by auto
  then have "\<Union>T-int(\<Union>T-(A\<rtr>x))=cl(A)\<rtr>x" unfolding ltrans_def using group0.group0_5_L1(1)[OF group0_valid_in_tgroup assms(1)]
    unfolding image_def range_def domain_def converse_def Pi_def by auto
  with \<open>cl(A\<rtr>x)=\<Union>T-int(\<Union>T-(A\<rtr>x))\<close> show ?thesis by auto
qed

lemma (in topgroup) trans_subset:
  assumes "A\<subseteq>((\<rm>x)\<ltr>B)""x\<in>G""A\<subseteq>G""B\<subseteq>G"
  shows "x\<ltr>A\<subseteq>B"
proof-
  {
   fix t assume "t\<in>x\<ltr>A"
    with \<open>x\<in>G\<close> \<open>A\<subseteq>G\<close> obtain u where "u\<in>A" "t=x\<ra>u" unfolding ltrans_def grop_def using group0.ltrans_image[OF group0_valid_in_tgroup]
      unfolding G_def by auto
    with \<open>x\<in>G\<close> \<open>A\<subseteq>G\<close> \<open>u\<in>A\<close> have "(\<rm>x)\<ra>t=u" using group0.group0_2_L18(2)[OF group0_valid_in_tgroup, of "x""u""t"]
      group0.group_op_closed[OF group0_valid_in_tgroup,of x u] unfolding grop_def grinv_def by auto
    with \<open>u\<in>A\<close> have "(\<rm>x)\<ra>t\<in>A" by auto
    with \<open>A\<subseteq>(\<rm>x)\<ltr>B\<close> have "(\<rm>x)\<ra>t\<in>(\<rm>x)\<ltr>B" by auto
    with \<open>B\<subseteq>G\<close> obtain v where "(\<rm>x)\<ra>t=(\<rm>x)\<ra>v" "v\<in>B" unfolding ltrans_def grop_def using neg_in_tgroup[OF \<open>x\<in>G\<close>] group0.ltrans_image[OF group0_valid_in_tgroup]
      unfolding G_def by auto
    have "LeftTranslation(G,f,\<rm>x)\<in>inj(G,G)" using group0.trans_bij(2)[OF group0_valid_in_tgroup neg_in_tgroup[OF \<open>x\<in>G\<close>]] bij_def by auto
    then have eq:"\<forall>A\<in>G. \<forall>B\<in>G. LeftTranslation(G,f,\<rm>x)`A=LeftTranslation(G,f,\<rm>x)`B \<longrightarrow> A=B" unfolding inj_def by auto
    {
      fix A B assume "A\<in>G""B\<in>G"
      assume "f`\<langle>\<rm>x,A\<rangle>=f`\<langle>\<rm>x,B\<rangle>"
      then have "LeftTranslation(G,f,\<rm>x)`A=LeftTranslation(G,f,\<rm>x)`B" using group0.group0_5_L2(2)[OF group0_valid_in_tgroup neg_in_tgroup[OF \<open>x\<in>G\<close>]]
        \<open>A\<in>G\<close>\<open>B\<in>G\<close> by auto
      with eq \<open>A\<in>G\<close>\<open>B\<in>G\<close> have "A=B" by auto
    }
    then have eq1:"\<forall>A\<in>G. \<forall>B\<in>G. f`\<langle>\<rm>x,A\<rangle>=f`\<langle>\<rm>x,B\<rangle> \<longrightarrow> A=B" by auto
    from \<open>A\<subseteq>G\<close> \<open>u\<in>A\<close> have "u\<in>G" by auto
    with \<open>v\<in>B\<close> \<open>B\<subseteq>G\<close> \<open>t=x\<ra>u\<close> have "t\<in>G" "v\<in>G" using group0.group_op_closed[OF group0_valid_in_tgroup \<open>x\<in>G\<close>,of u] unfolding grop_def
      by auto
    with eq1 \<open>(\<rm>x)\<ra>t=(\<rm>x)\<ra>v\<close> have "t=v" unfolding grop_def by auto
    with \<open>v\<in>B\<close> have "t\<in>B" by auto
  }
  then show ?thesis by auto
qed

text\<open>Every topological group is regular, and hence $T_3$. The proof is in the next
section, since it uses local properties.\<close>

subsection\<open>Local properties\<close>

text\<open>In a topological group, all local properties depend only on the neighbourhoods
of the neutral element; when considering topological properties. The next result
of regularity, will use this idea, since translations preserve closed sets.\<close>

lemma (in topgroup) local_iff_neutral:
  assumes "\<forall>U\<in>T\<inter>\<N>\<^sub>0. \<exists>N\<in>\<N>\<^sub>0. N\<subseteq>U\<and> P(N,T)" "\<forall>N\<in>Pow(G). \<forall>x\<in>G. P(N,T) \<longrightarrow> P(x\<ltr>N,T)"
  shows "T{is locally}P"
proof-
  {
    fix x U assume "x\<in>\<Union>T""U\<in>T""x\<in>U"
    then have "(\<rm>x)\<ltr>U\<in>T\<inter>\<N>\<^sub>0" using open_tr_open(1) open_trans_neigh neg_in_tgroup unfolding G_def
      by auto
    with assms(1) obtain N where "N\<subseteq>((\<rm>x)\<ltr>U)""P(N,T)""N\<in>\<N>\<^sub>0" by auto
    note \<open>x\<in>\<Union>T\<close>\<open>N\<subseteq>((\<rm>x)\<ltr>U)\<close> moreover
    from \<open>U\<in>T\<close> have "U\<subseteq>\<Union>T" by auto moreover
    from \<open>N\<in>\<N>\<^sub>0\<close> have "N\<subseteq>G" unfolding zerohoods_def by auto
    ultimately have "(x\<ltr>N)\<subseteq>U" using trans_subset unfolding G_def by auto moreover
    from \<open>N\<subseteq>G\<close>\<open>x\<in>\<Union>T\<close> assms(2) \<open>P(N,T)\<close> have "P((x\<ltr>N),T)" unfolding G_def by auto moreover
    from \<open>N\<in>\<N>\<^sub>0\<close>\<open>x\<in>\<Union>T\<close> have "x\<in>int(x\<ltr>N)" using elem_in_int_trans unfolding G_def by auto
    ultimately have "\<exists>N\<in>Pow(U). x\<in>int(N)\<and>P(N,T)" by auto
  }
  then show ?thesis unfolding IsLocally_def[OF topSpaceAssum] by auto
qed

lemma (in topgroup) trans_closed:
  assumes "A{is closed in}T""x\<in>G"
  shows "(x\<ltr>A){is closed in}T"
proof-
  from assms(1) have "cl(A)=A" using Top_3_L8 unfolding IsClosed_def by auto
  then have "x\<ltr>cl(A)=x\<ltr>A" by auto
  then have "cl(x\<ltr>A)=x\<ltr>A" using trans_closure assms unfolding IsClosed_def by auto
  moreover have "x\<ltr>A\<subseteq>G" unfolding ltrans_def using group0.group0_5_L1(2)[OF group0_valid_in_tgroup \<open>x\<in>G\<close>]
      unfolding image_def range_def domain_def converse_def Pi_def by auto
  ultimately show ?thesis using Top_3_L8 unfolding G_def by auto
qed

text\<open>As it is written in the previous section, every topological group is regular.\<close>

theorem (in topgroup) topgroup_reg:
  shows "T{is regular}"
proof-
  {
    fix U assume "U\<in>T\<inter>\<N>\<^sub>0"
    then obtain V where "cl(V)\<subseteq>U""V\<in>\<N>\<^sub>0" using exist_basehoods_closed by blast
    then have "V\<subseteq>cl(V)" using cl_contains_set unfolding zerohoods_def G_def by auto
    then have "int(V)\<subseteq>int(cl(V))" using interior_mono by auto
    with \<open>V\<in>\<N>\<^sub>0\<close> have "cl(V)\<in>\<N>\<^sub>0" unfolding zerohoods_def G_def using Top_3_L11(1) by auto
    from \<open>V\<in>\<N>\<^sub>0\<close> have "cl(V){is closed in}T" using cl_is_closed unfolding zerohoods_def G_def by auto
    with \<open>cl(V)\<in>\<N>\<^sub>0\<close>\<open>cl(V)\<subseteq>U\<close> have "\<exists>N\<in>\<N>\<^sub>0. N\<subseteq>U\<and>N{is closed in}T" by auto
  }
  then have "\<forall>U\<in>T\<inter>\<N>\<^sub>0. \<exists>N\<in>\<N>\<^sub>0. N\<subseteq>U\<and>N{is closed in}T" by auto moreover
  have "\<forall>N\<in>Pow(G).( \<forall>x\<in>G. (N{is closed in}T\<longrightarrow>(x\<ltr>N){is closed in}T))" using trans_closed by auto
  ultimately have "T{is locally-closed}" using local_iff_neutral unfolding IsLocallyClosed_def by auto
  then show "T{is regular}" using regular_locally_closed by auto
qed

text\<open>The promised corollary follows:\<close>
    
corollary (in topgroup) T2_imp_T3:
  assumes "T{is T\<^sub>2}"
  shows "T{is T\<^sub>3}" using T2_is_T1 topgroup_reg isT3_def assms by auto

end
