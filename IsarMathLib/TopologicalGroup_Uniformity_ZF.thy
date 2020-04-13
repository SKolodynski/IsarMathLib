(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2020  Daniel de la Concepcion

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

section \<open>Topological groups - uniformity\<close>

theory TopologicalGroup_Uniformity_ZF imports TopologicalGroup_ZF_1 UniformSpace_ZF

begin
text\<open>This theory is about the unifomities comming from topological groups.\<close>

subsection\<open>Topological group: definition and notation\<close>

text\<open>A topological group can have 2 basic uniformties, the left and the right uniformities\<close>

definition (in topgroup) leftUniformity
 where "leftUniformity \<equiv> {V\<in>Pow(G\<times>G).\<exists>U\<in> \<N>\<^sub>0. {\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>U}\<subseteq> V}"

definition (in topgroup) rightUniformity
 where "rightUniformity \<equiv> {V\<in>Pow(G\<times>G).\<exists>U\<in> \<N>\<^sub>0. {\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>U}\<subseteq> V}"

lemma (in topgroup) side_uniformities:
    shows "leftUniformity {is a uniformity on} G" and "rightUniformity {is a uniformity on} G"
proof-
  {
    assume "0\<in>leftUniformity"
    then obtain U where U:"U\<in>\<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>U}\<subseteq>0" unfolding leftUniformity_def by auto
    have "\<langle>\<zero>,\<zero>\<rangle>:G\<times>G" using zero_in_tgroup by auto
    moreover have "(\<rm>\<zero>)\<ra>\<zero> = \<zero>" using group0.group_inv_of_one[OF group0_valid_in_tgroup]
      group0.group0_2_L2[OF group0_valid_in_tgroup] zero_in_tgroup by auto
    moreover have "\<zero>\<in>int(U)" using U(1) by auto
    then have "\<zero>\<in>U" using Top_2_L1 by auto
    ultimately have "\<langle>\<zero>,\<zero>\<rangle>\<in>{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>U}" by auto
    then have "\<langle>\<zero>,\<zero>\<rangle>\<in>0" using U(2) by blast
    then have False by auto
  }
  then have "0\<notin>leftUniformity" by auto moreover
  have "leftUniformity \<subseteq> Pow(G\<times>G)" unfolding leftUniformity_def by auto moreover
  {
    have "G\<times>G\<in>Pow(G\<times>G)" by auto moreover
    have "{\<langle>s,t\<rangle>:G\<times>G. (\<rm>s)\<ra>t:G} \<subseteq> G\<times>G" by auto moreover
    note zneigh_not_empty
    ultimately have "G\<times>G\<in>leftUniformity" unfolding leftUniformity_def by auto
  } moreover
  {
    fix A B assume as:"A\<in>leftUniformity" "B\<in>leftUniformity"
    from as(1) obtain AU where AU:"AU\<in> \<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>AU}\<subseteq> A" "A\<in>Pow(G\<times>G)" unfolding leftUniformity_def by auto
    from as(2) obtain BU where BU:"BU\<in> \<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>BU}\<subseteq> B" "B\<in>Pow(G\<times>G)" unfolding leftUniformity_def by auto
    from AU(1) BU(1) have "\<zero>\<in>int(AU)\<inter>int(BU)" by auto
    moreover have op:"int(AU)\<inter>int(BU)\<in>T" using Top_2_L2[of AU] Top_2_L2[of BU]
      using topSpaceAssum unfolding IsATopology_def by auto
    have "int(AU)\<inter>int(BU) \<subseteq> AU\<inter>BU" using Top_2_L1 by auto
    with op have "int(AU)\<inter>int(BU)\<subseteq>int(AU\<inter>BU)" using Top_2_L5[of "int(AU)\<inter>int(BU)"]
      by auto moreover note AU(1) BU(1)
    ultimately have "AU\<inter>BU: \<N>\<^sub>0" unfolding zerohoods_def by auto
    moreover have "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>AU\<inter>BU}\<subseteq>{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>AU}"
      "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>AU\<inter>BU}\<subseteq>{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>AU}" by auto
    with AU(2) BU(2) have "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>AU\<inter>BU}\<subseteq>A\<inter>B" by auto
    ultimately have "A\<inter>B\<in>leftUniformity" using AU(3) BU(3) unfolding leftUniformity_def by blast
  }
  then have "\<forall>A\<in>leftUniformity. \<forall>B\<in>leftUniformity. A \<inter> B \<in> leftUniformity" by auto
  moreover
  {
    fix B C assume as:"B\<in>leftUniformity" "C\<in>Pow(G \<times> G)" "B \<subseteq> C"
    from as(1) obtain BU where BU:"BU\<in>\<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> BU}\<subseteq>B" unfolding leftUniformity_def by blast
    from as(3) BU(2) have "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> BU}\<subseteq>C" by auto
    then have "C \<in> leftUniformity" using as(2) BU(1) unfolding leftUniformity_def by auto
  }
  then have "\<forall>B\<in>leftUniformity. \<forall>C\<in>Pow(G\<times>G). B\<subseteq>C \<longrightarrow> C\<in>leftUniformity" by auto
  ultimately have leftFilter:"leftUniformity {is a filter on} (G\<times>G)" unfolding IsFilter_def by auto
  {
    assume "0\<in>rightUniformity"
    then obtain U where U:"U\<in>\<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>U}\<subseteq>0" unfolding rightUniformity_def by auto
    have "\<langle>\<zero>,\<zero>\<rangle>:G\<times>G" using zero_in_tgroup by auto
    moreover have "\<zero>\<ra>(\<rm>\<zero>) = \<zero>" using group0.group_inv_of_one[OF group0_valid_in_tgroup]
      group0.group0_2_L2[OF group0_valid_in_tgroup] zero_in_tgroup by auto
    moreover have "\<zero>\<in>int(U)" using U(1) by auto
    then have "\<zero>\<in>U" using Top_2_L1 by auto
    ultimately have "\<langle>\<zero>,\<zero>\<rangle>\<in>{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>U}" by auto
    then have "\<langle>\<zero>,\<zero>\<rangle>\<in>0" using U(2) by blast
    then have False by auto
  }
  then have "0\<notin>rightUniformity" by auto moreover
  have "rightUniformity \<subseteq> Pow(G\<times>G)" unfolding rightUniformity_def by auto moreover
  {
    have "G\<times>G\<in>Pow(G\<times>G)" by auto moreover
    have "{\<langle>s,t\<rangle>:G\<times>G. (\<rm>s)\<ra>t:G} \<subseteq> G\<times>G" by auto moreover
    note zneigh_not_empty
    ultimately have "G\<times>G\<in>rightUniformity" unfolding rightUniformity_def by auto
  } moreover
  {
    fix A B assume as:"A\<in>rightUniformity" "B\<in>rightUniformity"
    from as(1) obtain AU where AU:"AU\<in> \<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>AU}\<subseteq> A" "A\<in>Pow(G\<times>G)" unfolding rightUniformity_def by auto
    from as(2) obtain BU where BU:"BU\<in> \<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>BU}\<subseteq> B" "B\<in>Pow(G\<times>G)" unfolding rightUniformity_def by auto
    from AU(1) BU(1) have "\<zero>\<in>int(AU)\<inter>int(BU)" by auto
    moreover have op:"int(AU)\<inter>int(BU)\<in>T" using Top_2_L2[of AU] Top_2_L2[of BU]
      using topSpaceAssum unfolding IsATopology_def by auto
    have "int(AU)\<inter>int(BU) \<subseteq> AU\<inter>BU" using Top_2_L1 by auto
    with op have "int(AU)\<inter>int(BU)\<subseteq>int(AU\<inter>BU)" using Top_2_L5[of "int(AU)\<inter>int(BU)"]
      by auto moreover note AU(1) BU(1)
    ultimately have "AU\<inter>BU: \<N>\<^sub>0" unfolding zerohoods_def by auto
    moreover have "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>AU\<inter>BU}\<subseteq>{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>AU}"
      "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>AU\<inter>BU}\<subseteq>{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>AU}" by auto
    with AU(2) BU(2) have "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>AU\<inter>BU}\<subseteq>A\<inter>B" by auto
    ultimately have "A\<inter>B\<in>rightUniformity" using AU(3) BU(3) unfolding rightUniformity_def by blast
  }
  then have "\<forall>A\<in>rightUniformity. \<forall>B\<in>rightUniformity. A \<inter> B \<in> rightUniformity" by auto
  moreover
  {
    fix B C assume as:"B\<in>rightUniformity" "C\<in>Pow(G \<times> G)" "B \<subseteq> C"
    from as(1) obtain BU where BU:"BU\<in>\<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in> BU}\<subseteq>B" unfolding rightUniformity_def by blast
    from as(3) BU(2) have "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in> BU}\<subseteq>C" by auto
    then have "C \<in> rightUniformity" using as(2) BU(1) unfolding rightUniformity_def by auto
  }
  then have "\<forall>B\<in>rightUniformity. \<forall>C\<in>Pow(G\<times>G). B\<subseteq>C \<longrightarrow> C\<in>rightUniformity" by auto
  ultimately have rightFilter:"rightUniformity {is a filter on} (G\<times>G)" unfolding IsFilter_def by auto
  {
    fix U assume as:"U\<in>leftUniformity"
    from as obtain V where V:"V\<in>\<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> V} \<subseteq> U" 
      unfolding leftUniformity_def by auto
    {
      fix x assume as2:"x\<in>id(G)"
      from as obtain V where V:"V\<in>\<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> V} \<subseteq> U" 
        unfolding leftUniformity_def by auto
      from V(1) have "\<zero>\<in>int(V)" by auto
      then have V0:"\<zero>\<in>V" using Top_2_L1 by auto
      from as2 obtain t where t:"x=\<langle>t,t\<rangle>" "t:G" by auto
      from t(2) have "(\<rm>t)\<ra>t =\<zero>" using group0.group0_2_L6[OF group0_valid_in_tgroup] by auto
      with V0 t V(2) have "x\<in>U" by auto
    }
    then have "id(G)\<subseteq>U" by auto moreover
    {
      {
        fix x assume ass:"x\<in>{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> \<sm>V}"
        then obtain s t where as:"s:G" "t:G" "(\<rm>s)\<ra>t \<in> \<sm>V" "x=\<langle>s,t\<rangle>" by force
        from as(3) have "(\<rm>s)\<ra>t:{\<rm>q. q:V}" 
          using func_imagedef[OF group0_2_T2[OF Ggroup], of V] V(1) unfolding zerohoods_def
          by auto
        then obtain q where q:"q:V" "(\<rm>s)\<ra>t = \<rm>q" by auto
        then have "(\<rm>(\<rm>q)) = (\<rm>((\<rm>s)\<ra>t))" by auto
        then have "q=(\<rm>((\<rm>s)\<ra>t))" using group0.group_inv_of_inv[OF group0_valid_in_tgroup, of q]
          using q(1) V(1) unfolding zerohoods_def by auto
        then have "q=(\<rm>t)\<ra>(\<rm>(\<rm>s))" using group0.group_inv_of_two[OF group0_valid_in_tgroup, of "\<rm>s" t]
          as(1) group0.inverse_in_group[OF group0_valid_in_tgroup, of s] as(2) by auto
        then have "q=(\<rm>t)\<ra>s" using group0.group_inv_of_inv[OF group0_valid_in_tgroup as(1)] by auto
        with q(1) have "(\<rm>t)\<ra>s:V" by auto
        with as(1,2) have "\<langle>t,s\<rangle>:U" using V(2) by auto
        then have "\<langle>s,t\<rangle>:converse(U)" by auto
        with as(4) have "x:converse(U)" by auto
      }
      then have "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> \<sm>V} \<subseteq> converse(U)" by auto
      moreover have "(\<sm>V):\<N>\<^sub>0" using neg_neigh_neigh V(1) by auto
      ultimately have "converse(U):leftUniformity" using as unfolding leftUniformity_def by auto
    }
    moreover
    {
      from V(1) obtain W where W:"W:\<N>\<^sub>0" "W \<sad> W \<subseteq>V" using exists_procls_zerohood by blast
      {
        fix x assume as:"x:{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> W} O {\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> W}"
        then obtain x1 x2 x3 where x:"x1:G" "x2:G" "x3:G" "(\<rm>x1)\<ra>x2 \<in> W" "(\<rm>x2)\<ra>x3 \<in> W" "x=\<langle>x1,x3\<rangle>"
          unfolding comp_def by auto
        from W(1) have "W\<sad>W = f``(W\<times>W)" using interval_add(2) by auto moreover
        from W(1) have WW:"W\<times>W\<subseteq>G\<times>G" by auto
        from x(4,5) have "\<langle>(\<rm>x1)\<ra>x2,(\<rm>x2)\<ra>x3\<rangle>:W\<times>W" by auto
        with WW have "f`(\<langle>(\<rm>x1)\<ra>x2,(\<rm>x2)\<ra>x3\<rangle>):f``(W\<times>W)"
          using func_imagedef[OF topgroup_f_binop, of "W\<times>W"] by auto
        ultimately have "((\<rm>x1)\<ra>x2)\<ra>((\<rm>x2)\<ra>x3) :W\<sad>W" by auto
        moreover have "((\<rm>x1)\<ra>x2)\<ra>((\<rm>x2)\<ra>x3) = (\<rm>x1)\<ra>(x2\<ra>((\<rm>x2)\<ra>x3))"
          using group0.group_oper_assoc[OF group0_valid_in_tgroup group0.inverse_in_group[OF group0_valid_in_tgroup x(1)] x(2)]
          using group0.group_op_closed[OF group0_valid_in_tgroup group0.inverse_in_group[OF group0_valid_in_tgroup x(2)] x(3)] by auto
        then have "((\<rm>x1)\<ra>x2)\<ra>((\<rm>x2)\<ra>x3) = (\<rm>x1)\<ra>((x2\<ra>(\<rm>x2))\<ra>x3)"
          using group0.group_oper_assoc[OF group0_valid_in_tgroup x(2) group0.inverse_in_group[OF group0_valid_in_tgroup x(2)] x(3)]
          by auto
        then have "((\<rm>x1)\<ra>x2)\<ra>((\<rm>x2)\<ra>x3) = (\<rm>x1)\<ra>(\<zero>\<ra>x3)" using group0.group0_2_L6[OF group0_valid_in_tgroup x(2)] by auto
        then have "((\<rm>x1)\<ra>x2)\<ra>((\<rm>x2)\<ra>x3) = (\<rm>x1)\<ra> x3" using group0.group0_2_L2[OF group0_valid_in_tgroup] x(3) by auto
        ultimately have "(\<rm>x1)\<ra> x3\<in>W\<sad>W" by auto
        with W(2) have "(\<rm>x1)\<ra> x3\<in>V" by auto
        then have "x:{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> V}" using x(1,3,6) by auto
      }
      then have "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> W} O {\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> W} \<subseteq> U"
        using V(2) by auto moreover
      have "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> W}\<in>leftUniformity" unfolding leftUniformity_def using W(1) by auto
      ultimately have "\<exists>Z\<in>leftUniformity. Z O Z\<subseteq>U" by auto
    }
    ultimately have "id(G)\<subseteq>U \<and> (\<exists>Z\<in>leftUniformity. Z O Z\<subseteq>U) \<and> converse(U)\<in>leftUniformity" by blast
  }
  then have "\<forall>U\<in>leftUniformity. id(G)\<subseteq>U \<and> (\<exists>Z\<in>leftUniformity. Z O Z\<subseteq>U) \<and> converse(U)\<in>leftUniformity" by auto
  with leftFilter show "leftUniformity {is a uniformity on} G" unfolding IsUniformity_def by auto
  {
    fix U assume as:"U\<in>rightUniformity"
    from as obtain V where V:"V\<in>\<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in> V} \<subseteq> U" 
      unfolding rightUniformity_def by auto
    {
      fix x assume as2:"x\<in>id(G)"
      from as obtain V where V:"V\<in>\<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in> V} \<subseteq> U" 
        unfolding rightUniformity_def by auto
      from V(1) have "\<zero>\<in>int(V)" by auto
      then have V0:"\<zero>\<in>V" using Top_2_L1 by auto
      from as2 obtain t where t:"x=\<langle>t,t\<rangle>" "t:G" by auto
      from t(2) have "t\<ra>(\<rm>t) =\<zero>" using group0.group0_2_L6[OF group0_valid_in_tgroup] by auto
      with V0 t V(2) have "x\<in>U" by auto
    }
    then have "id(G)\<subseteq>U" by auto moreover
    {
      {
        fix x assume ass:"x\<in>{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in> \<sm>V}"
        then obtain s t where as:"s:G" "t:G" "s\<ra>(\<rm>t) \<in> \<sm>V" "x=\<langle>s,t\<rangle>" by force
        from as(3) have "s\<ra>(\<rm>t):{\<rm>q. q:V}" 
          using func_imagedef[OF group0_2_T2[OF Ggroup], of V] V(1) unfolding zerohoods_def
          by auto
        then obtain q where q:"q:V" "s\<ra>(\<rm>t) = \<rm>q" by auto
        then have "(\<rm>(\<rm>q)) = (\<rm>(s\<ra>(\<rm>t)))" by auto
        then have "q=(\<rm>(s\<ra>(\<rm>t)))" using group0.group_inv_of_inv[OF group0_valid_in_tgroup, of q]
          using q(1) V(1) unfolding zerohoods_def by auto
        then have "q=(\<rm>(\<rm>t))\<ra>(\<rm>s)" using group0.group_inv_of_two[OF group0_valid_in_tgroup, of s "\<rm>t"]
          as(1) group0.inverse_in_group[OF group0_valid_in_tgroup, of t] as(2) by auto
        then have "q=t\<ra>(\<rm>s)" using group0.group_inv_of_inv[OF group0_valid_in_tgroup as(2)] by auto
        with q(1) have "t\<ra>(\<rm>s):V" by auto
        with as(1,2) have "\<langle>t,s\<rangle>:U" using V(2) by auto
        then have "\<langle>s,t\<rangle>:converse(U)" by auto
        with as(4) have "x:converse(U)" by auto
      }
      then have "{\<langle>s,t\<rangle>\<in>G\<times>G.  s\<ra>(\<rm>t) \<in> \<sm>V} \<subseteq> converse(U)" by auto
      moreover have "(\<sm>V):\<N>\<^sub>0" using neg_neigh_neigh V(1) by auto
      ultimately have "converse(U):rightUniformity" using as unfolding rightUniformity_def by auto
    }
    moreover
    {
      from V(1) obtain W where W:"W:\<N>\<^sub>0" "W \<sad> W \<subseteq>V" using exists_procls_zerohood by blast
      {
        fix x assume as:"x:{\<langle>s,t\<rangle>\<in>G\<times>G.  s\<ra>(\<rm>t) \<in> W} O {\<langle>s,t\<rangle>\<in>G\<times>G.  s\<ra>(\<rm>t) \<in> W}"
        then obtain x1 x2 x3 where x:"x1:G" "x2:G" "x3:G" "x1\<ra>(\<rm>x2) \<in> W" "x2\<ra>(\<rm>x3) \<in> W" "x=\<langle>x1,x3\<rangle>"
          unfolding comp_def by auto
        from W(1) have "W\<sad>W = f``(W\<times>W)" using interval_add(2) by auto moreover
        from W(1) have WW:"W\<times>W\<subseteq>G\<times>G" by auto
        from x(4,5) have "\<langle>x1\<ra>(\<rm>x2),x2\<ra>(\<rm>x3)\<rangle>:W\<times>W" by auto
        with WW have "f`(\<langle>x1\<ra>(\<rm>x2),x2\<ra>(\<rm>x3)\<rangle>):f``(W\<times>W)"
          using func_imagedef[OF topgroup_f_binop, of "W\<times>W"] by auto
        ultimately have "(x1\<ra>(\<rm>x2))\<ra>(x2\<ra>(\<rm>x3)) :W\<sad>W" by auto
        moreover have "(x1\<ra>(\<rm>x2))\<ra>(x2\<ra>(\<rm>x3)) = x1\<ra>((\<rm>x2)\<ra>(x2\<ra>(\<rm>x3)))"
          using group0.group_oper_assoc[OF group0_valid_in_tgroup x(1) group0.inverse_in_group[OF group0_valid_in_tgroup x(2)]]
          using group0.group_op_closed[OF group0_valid_in_tgroup x(2) group0.inverse_in_group[OF group0_valid_in_tgroup x(3)]] by auto
        then have "(x1\<ra>(\<rm>x2))\<ra>(x2\<ra>(\<rm>x3)) = x1\<ra>(((\<rm>x2)\<ra>x2)\<ra>(\<rm>x3))"
          using group0.group_oper_assoc[OF group0_valid_in_tgroup group0.inverse_in_group[OF group0_valid_in_tgroup x(2)] x(2) 
              group0.inverse_in_group[OF group0_valid_in_tgroup x(3)]]
          by auto
        then have "(x1\<ra>(\<rm>x2))\<ra>(x2\<ra>(\<rm>x3)) = x1\<ra>(\<zero>\<ra>(\<rm>x3))" using group0.group0_2_L6[OF group0_valid_in_tgroup x(2)] by auto
        then have "(x1\<ra>(\<rm>x2))\<ra>(x2\<ra>(\<rm>x3)) = x1\<ra> (\<rm>x3)" using group0.group0_2_L2[OF group0_valid_in_tgroup]
          group0.inverse_in_group[OF group0_valid_in_tgroup x(3)] by auto
        ultimately have "x1\<ra> (\<rm>x3)\<in>W\<sad>W" by auto
        with W(2) have "x1\<ra> (\<rm>x3)\<in>V" by auto
        then have "x:{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in> V}" using x(1,3,6) by auto
      }
      then have "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in> W} O {\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in> W} \<subseteq> U"
        using V(2) by auto moreover
      have "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in> W}\<in>rightUniformity" unfolding rightUniformity_def using W(1) by auto
      ultimately have "\<exists>Z\<in>rightUniformity. Z O Z\<subseteq>U" by auto
    }
    ultimately have "id(G)\<subseteq>U \<and> (\<exists>Z\<in>rightUniformity. Z O Z\<subseteq>U) \<and> converse(U)\<in>rightUniformity" by blast
  }
  then have "\<forall>U\<in>rightUniformity. id(G)\<subseteq>U \<and> (\<exists>Z\<in>rightUniformity. Z O Z\<subseteq>U) \<and> converse(U)\<in>rightUniformity" by auto
  with rightFilter show "rightUniformity {is a uniformity on} G" unfolding IsUniformity_def by auto
qed

lemma (in topgroup) top_generated_side_uniformities:
  shows "UniformTopology(leftUniformity,G) =T"  "UniformTopology(rightUniformity,G) =T"
  unfolding UniformTopology_def
proof-
  let ?M = "{\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G}"
  from neigh_from_uniformity[OF side_uniformities(1)] have fun:"?M:G\<rightarrow>Pow(Pow(G))" unfolding IsNeighSystem_def by auto
  let ?N = "{\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle> . t \<in> G}"
  from neigh_from_uniformity[OF side_uniformities(2)] have funN:"?N:G\<rightarrow>Pow(Pow(G))" unfolding IsNeighSystem_def by auto
  {
    fix U assume op:"U\<in>T"
    {
      fix x assume x:"x\<in>U"
      then have xg:"x:G" using op by auto
      then have "\<langle>x, {V `` {x} . V \<in> leftUniformity}\<rangle> \<in>  {\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G}" by auto
      with fun have app:"?M ` x = {V `` {x} . V \<in> leftUniformity}"
        using apply_iff[of ?M G "\<lambda>x. Pow(Pow(G))" x "{V `` {x} . V \<in> leftUniformity}"] by auto
      have "(\<rm>x)\<ltr>U : \<N>\<^sub>0" using open_trans_neigh op x by auto
      then have V:"{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t\<in>((\<rm>x)\<ltr>U)}:leftUniformity"
        unfolding leftUniformity_def by auto
      then have N:"\<forall>t\<in>G. t:{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t\<in>((\<rm>x)\<ltr>U)}``{x} \<longleftrightarrow> (\<rm>x)\<ra>t\<in>((\<rm>x)\<ltr>U)"
        using xg image_iff[of _ "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t\<in>((\<rm>x)\<ltr>U)}" "{x}"] by auto
      {
        fix t assume t:"t:G" 
        {
          assume as:"(\<rm>x)\<ra>t\<in>((\<rm>x)\<ltr>U)"
          then have "(\<rm>x)\<ra>t\<in>LeftTranslation(G,f,\<rm>x)``U" by auto
          then obtain q where q:"q:U" "\<langle>q,(\<rm>x)\<ra>t\<rangle>\<in>LeftTranslation(G,f,\<rm>x)"
            using image_iff[of "(\<rm>x)\<ra>t" "LeftTranslation(G,f,\<rm>x)" U] by auto
          from q(2) have "(\<rm>x)\<ra>q = (\<rm>x)\<ra>t" unfolding LeftTranslation_def by auto
          then have "q = t" using group0.group0_2_L19(2)[OF group0_valid_in_tgroup _ t(1) 
            group0.inverse_in_group[OF group0_valid_in_tgroup xg], of q] q(1) op by auto
          with q(1) have "t:U" by auto
        } moreover
        {
          assume t:"t:U"
          have "\<langle>t,(\<rm>x)\<ra>t\<rangle>\<in>LeftTranslation(G,f,\<rm>x)" unfolding LeftTranslation_def
            using t op group0.inverse_in_group[OF group0_valid_in_tgroup xg] group0.group_op_closed[OF group0_valid_in_tgroup, of "\<rm>x" t]
            by auto
          with t have "(\<rm>x)\<ra>t\<in>((\<rm>x)\<ltr>U)" by auto
        } ultimately have "(\<rm>x)\<ra>t\<in>((\<rm>x)\<ltr>U) \<longleftrightarrow> t:U" by blast
      } with N have "\<forall>t\<in>G. t:{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t\<in>((\<rm>x)\<ltr>U)}``{x} \<longleftrightarrow> t:U" by blast
      then have "\<forall>t. t:{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t\<in>((\<rm>x)\<ltr>U)}``{x} \<longleftrightarrow> t:U" using op by auto
      then have "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t\<in>((\<rm>x)\<ltr>U)}``{x} = U" by auto
      with V have "\<exists>V\<in>leftUniformity. U=V``{x}" using exI[of "\<lambda>V. V\<in>leftUniformity \<and> U=V``{x}" "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t\<in>((\<rm>x)\<ltr>U)}"]
        by auto
      then have " U \<in> {\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G} ` x" using app by auto
      moreover
      from xg have "\<langle>x, {V `` {x} . V \<in> rightUniformity}\<rangle> \<in>  {\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle> . t \<in> G}" by auto
      with funN have app:"?N `  x = {V `` {x} . V \<in> rightUniformity}"
        using apply_iff[of ?N G "\<lambda>x. Pow(Pow(G))" x "{V `` {x} . V \<in> rightUniformity}"] by auto
      from x op have openTrans:"U\<rtr>(\<rm>x): \<N>\<^sub>0" using open_trans_neigh_2 by auto
      then have V:"{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t)\<in>(U\<rtr>(\<rm>x))}:rightUniformity"
        unfolding rightUniformity_def by auto
      then have N:"\<forall>t\<in>G. t:{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t)\<in>(U\<rtr>(\<rm>x))}-``{x} \<longleftrightarrow> t\<ra>(\<rm>x)\<in>(U\<rtr>(\<rm>x))"
        using xg vimage_iff[of _ "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t)\<in>(U\<rtr>(\<rm>x))}" "{x}"] by auto
      {
        fix t assume t:"t:G" 
        {
          assume as:"t\<ra>(\<rm>x)\<in>(U\<rtr>(\<rm>x))"
          then have "t\<ra>(\<rm>x)\<in>RightTranslation(G,f,\<rm>x)``U" by auto
          then obtain q where q:"q:U" "\<langle>q,t\<ra>(\<rm>x)\<rangle>\<in>RightTranslation(G,f,\<rm>x)"
            using image_iff[of "t\<ra>(\<rm>x)" "RightTranslation(G,f,\<rm>x)" U] by auto
          from q(2) have "q\<ra>(\<rm>x) = t\<ra>(\<rm>x)" unfolding RightTranslation_def by auto
          then have "q = t" using group0.group0_2_L19(1)[OF group0_valid_in_tgroup _ t(1) 
            group0.inverse_in_group[OF group0_valid_in_tgroup xg], of q] q(1) op by auto
          with q(1) have "t:U" by auto
        } moreover
        {
          assume t:"t:U"
          have "\<langle>t,t\<ra>(\<rm>x)\<rangle>\<in>RightTranslation(G,f,\<rm>x)" unfolding RightTranslation_def
            using t op group0.inverse_in_group[OF group0_valid_in_tgroup xg] group0.group_op_closed[OF group0_valid_in_tgroup, of t "\<rm>x"]
            by auto
          with t have "t\<ra>(\<rm>x)\<in>(U\<rtr>(\<rm>x))" by auto
        } ultimately have "t\<ra>(\<rm>x)\<in>(U\<rtr>(\<rm>x)) \<longleftrightarrow> t:U" by blast
      } with N have "\<forall>t\<in>G. t:{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t)\<in>(U\<rtr>(\<rm>x))}-``{x} \<longleftrightarrow> t:U" by blast
      then have "\<forall>t. t:{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t)\<in>(U\<rtr>(\<rm>x))}-``{x} \<longleftrightarrow> t:U" using op by auto
      then have "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t)\<in>(U\<rtr>(\<rm>x))}-``{x} = U" by auto
      then have "converse({\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t)\<in>(U\<rtr>(\<rm>x))})``{x} =U" unfolding vimage_def.
      with V have "\<exists>V\<in>rightUniformity. U=V``{x}" using exI[of "\<lambda>V. V\<in>rightUniformity \<and> U=V``{x}" "converse({\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t)\<in>(U\<rtr>(\<rm>x))})"]
        using side_uniformities(2) unfolding IsUniformity_def by auto
      then have " U \<in> {\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle> . t \<in> G} ` x" using app by auto
      ultimately have "U \<in> {\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G} ` x" "U \<in> {\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle> . t \<in> G} ` x" by auto
    }
    then have "\<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G} ` x" "\<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle> . t \<in> G} ` x"
      by auto
  }
  then have "T\<subseteq>{U \<in> Pow(G) . \<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G} ` x}" "T\<subseteq>{U \<in> Pow(G) . \<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle> . t \<in> G} ` x}" by auto
  moreover
  {
    fix U assume as:"U \<in> Pow(G)" "\<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G} ` x"
    {
      fix x assume x:"x\<in>U"
      with as(1) have xg:"x\<in>G" by auto
      from x as(2) have "U\<in>{\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G} ` x" by auto
      with xg have "U\<in>{V `` {x} . V \<in> leftUniformity}" using apply_equality[of x "{V `` {x} . V \<in> leftUniformity}", OF _ fun] by auto
      then obtain V where V:"U=V``{x}" "V\<in>leftUniformity" by auto
      from V(2) obtain W where W:"W\<in> \<N>\<^sub>0" "{\<langle>s,t\<rangle>:G\<times>G. (\<rm>s)\<ra>t:W}\<subseteq>V" unfolding leftUniformity_def
        by auto
      from W(2) have A:"{\<langle>s,t\<rangle>:G\<times>G. (\<rm>s)\<ra>t:W}``{x}\<subseteq>V``{x}" by auto
      from xg have "\<forall>q\<in>G. q\<in>({\<langle>s,t\<rangle>:G\<times>G. (\<rm>s)\<ra>t:W}``{x}) \<longleftrightarrow> (\<rm>x)\<ra>q:W"
        using image_iff[of _ "{\<langle>s,t\<rangle>:G\<times>G. (\<rm>s)\<ra>t:W}" "{x}"] by auto
      then have B:"{\<langle>s,t\<rangle>:G\<times>G. (\<rm>s)\<ra>t:W}``{x} = {t\<in>G. (\<rm>x)\<ra>t:W}" by auto
      from W(1) have WG:"W\<subseteq>G" by auto
      {
        fix t assume t:"t:x\<ltr>W"
        then have "t:LeftTranslation(G,f,x)``W" by auto
        then obtain s where s:"s:W" "\<langle>s,t\<rangle>\<in>LeftTranslation(G,f,x)" using image_iff by auto
        from s(2) have "t=x\<ra>s" "t:G" unfolding LeftTranslation_def by auto
        then have "(\<rm>x)\<ra>t = (\<rm>x)\<ra>(x\<ra>s)" by auto
        with xg s(1) WG have "(\<rm>x)\<ra>t = ((\<rm>x)\<ra>x)\<ra>s" using group0.group_oper_assoc[OF group0_valid_in_tgroup, of "\<rm>x" x s]
          group0.inverse_in_group[OF group0_valid_in_tgroup, of x] by auto
        with xg have "(\<rm>x)\<ra>t =\<zero>\<ra>s" using group0.group0_2_L6[OF group0_valid_in_tgroup] by auto
        with s(1) WG have "(\<rm>x)\<ra>t = s" using group0.group0_2_L2[OF group0_valid_in_tgroup] by auto
        with s(1) have "(\<rm>x)\<ra>t:W" by auto
        with `t:G` have "t:{s:G. (\<rm>x)\<ra>s:W}" by auto
      }
      then have "x\<ltr>W \<subseteq> {t:G. (\<rm>x)\<ra>t:W}" by auto
      with B have "x \<ltr> W \<subseteq> {\<langle>s,t\<rangle> \<in> G \<times> G . (\<rm> s) \<ra> t \<in> W} `` {x}" by auto
      with A have "x \<ltr> W \<subseteq> V`` {x}" by blast
      with V(1) have "x \<ltr> W \<subseteq> U" by auto
      then have "int(x \<ltr> W) \<subseteq> U" using Top_2_L1 by blast
      moreover from xg W(1) have "x\<in>int(x \<ltr> W)" using elem_in_int_trans by auto
      moreover have "int(x \<ltr> W)\<in>T" using Top_2_L2 by auto
      ultimately have "\<exists>Y\<in>T. x\<in>Y \<and> Y\<subseteq>U" by auto
    }
    then have "U\<in>T" using open_neigh_open by auto
  }
  then have "{U \<in> Pow(G) . \<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G} ` x} \<subseteq> T" by auto
  moreover
  {
    fix U assume as:"U \<in> Pow(G)" "\<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle> . t \<in> G} ` x"
    {
      fix x assume x:"x\<in>U"
      with as(1) have xg:"x\<in>G" by auto
      from x as(2) have "U\<in>{\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle> . t \<in> G} ` x" by auto
      with xg have "U\<in>{V `` {x} . V \<in> rightUniformity}" using apply_equality[of x "{V `` {x} . V \<in> rightUniformity}", OF _ funN] by auto
      then obtain V where V:"U=V``{x}" "V\<in>rightUniformity" by auto
      then have "converse(V)\<in>rightUniformity" using side_uniformities(2) unfolding IsUniformity_def by auto
      then obtain W where W:"W\<in> \<N>\<^sub>0" "{\<langle>s,t\<rangle>:G\<times>G. s\<ra>(\<rm>t):W}\<subseteq>converse(V)" unfolding rightUniformity_def
        by auto
      from W(2) have A:"{\<langle>s,t\<rangle>:G\<times>G. s\<ra>(\<rm>t):W}-``{x}\<subseteq>V``{x}" by auto
      from xg have "\<forall>q\<in>G. q\<in>({\<langle>s,t\<rangle>:G\<times>G. s\<ra>(\<rm>t):W}-``{x}) \<longleftrightarrow> q\<ra>(\<rm>x):W"
        using image_iff[of _ "{\<langle>s,t\<rangle>:G\<times>G. s\<ra>(\<rm>t):W}" "{x}"] by auto
      then have B:"{\<langle>s,t\<rangle>:G\<times>G. s\<ra>(\<rm>t):W}-``{x} = {t\<in>G. t\<ra>(\<rm>x):W}" by auto
      from W(1) have WG:"W\<subseteq>G" by auto
      {
        fix t assume t:"t:W\<rtr>x"
        then have "t:RightTranslation(G,f,x)``W" by auto
        then obtain s where s:"s:W" "\<langle>s,t\<rangle>\<in>RightTranslation(G,f,x)" using image_iff by auto
        from s(2) have "t=s\<ra>x" "t:G" unfolding RightTranslation_def by auto
        then have "t\<ra>(\<rm>x) = (s\<ra>x)\<ra>(\<rm>x)" by auto
        with xg s(1) WG have "t\<ra>(\<rm>x) = s\<ra>(x\<ra>(\<rm>x))" using group0.group_oper_assoc[OF group0_valid_in_tgroup, of s x "\<rm>x", THEN sym]
          group0.inverse_in_group[OF group0_valid_in_tgroup, of x] by auto
        with xg have "t\<ra>(\<rm>x) = s\<ra>\<zero>" using group0.group0_2_L6[OF group0_valid_in_tgroup] by auto
        with s(1) WG have "t\<ra>(\<rm>x) = s" using group0.group0_2_L2[OF group0_valid_in_tgroup] by auto
        with s(1) have "t\<ra>(\<rm>x):W" by auto
        with `t:G` have "t:{s:G. s\<ra>(\<rm>x):W}" by auto
      }
      then have "W\<rtr>x \<subseteq> {t:G. t\<ra>(\<rm>x):W}" by auto
      with B have "W \<rtr> x \<subseteq> {\<langle>s,t\<rangle> \<in> G \<times> G . s \<ra> (\<rm> t) \<in> W} -`` {x}" by auto
      with A have "W \<rtr> x \<subseteq> V`` {x}" by blast
      with V(1) have "W \<rtr> x \<subseteq> U" by auto
      then have "int(W \<rtr> x) \<subseteq> U" using Top_2_L1 by blast
      moreover from xg W(1) have "x\<in>int(W \<rtr> x)" using elem_in_int_trans_2 by auto
      moreover have "int(W \<rtr> x)\<in>T" using Top_2_L2 by auto
      ultimately have "\<exists>Y\<in>T. x\<in>Y \<and> Y\<subseteq>U" by auto
    }
    then have "U\<in>T" using open_neigh_open by auto
  }
  ultimately show " {U \<in> Pow(G) . \<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G} ` x} =
    T" " {U \<in> Pow(G) . \<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle> . t \<in> G} ` x} =
    T" by auto
qed


end