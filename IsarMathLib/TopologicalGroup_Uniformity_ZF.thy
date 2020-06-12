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
text\<open> Each topological group is a uniform space.
  This theory is about the unifomities that are naturally defined by a topological group structure. \<close>

subsection\<open>Topological group: definition and notation\<close>

text\<open>There are two basic uniformities that can be defined on a topological group. \<close>

text\<open>Definition of left uniformity\<close>

definition (in topgroup) leftUniformity
 where "leftUniformity \<equiv> {V\<in>Pow(G\<times>G).\<exists>U\<in> \<N>\<^sub>0. {\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>U} \<subseteq> V}"

text\<open>Definition of right uniformity\<close>

definition (in topgroup) rightUniformity
 where "rightUniformity \<equiv> {V\<in>Pow(G\<times>G).\<exists>U\<in> \<N>\<^sub>0. {\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>U}\<subseteq> V}"

text\<open>Right and left uniformities are indeed uniformities. \<close>

lemma (in topgroup) side_uniformities:
    shows "leftUniformity {is a uniformity on} G" and "rightUniformity {is a uniformity on} G"
proof-
  {
    assume "0 \<in> leftUniformity"
    then obtain U where U:"U\<in>\<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>U}\<subseteq>0" unfolding leftUniformity_def 
      by auto
    have "\<langle>\<zero>,\<zero>\<rangle>:G\<times>G" using zero_in_tgroup by auto
    moreover have "(\<rm>\<zero>)\<ra>\<zero> = \<zero>" 
      using group0_valid_in_tgroup group0.group_inv_of_one group0.group0_2_L2 zero_in_tgroup 
      by auto
    moreover have "\<zero>\<in>int(U)" using U(1) by auto
    then have "\<zero>\<in>U" using Top_2_L1 by auto
    ultimately have "\<langle>\<zero>,\<zero>\<rangle>\<in>{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>U}" by auto
    with U(2) have "\<langle>\<zero>,\<zero>\<rangle>\<in>0" by blast
    hence False by auto
  }
  hence "0\<notin>leftUniformity" by auto 
  moreover  have "leftUniformity \<subseteq> Pow(G\<times>G)" unfolding leftUniformity_def by auto 
  moreover
  {
    have "G\<times>G\<in>Pow(G\<times>G)" by auto moreover
    have "{\<langle>s,t\<rangle>:G\<times>G. (\<rm>s)\<ra>t:G} \<subseteq> G\<times>G" by auto moreover
    note zneigh_not_empty
    ultimately have "G\<times>G\<in>leftUniformity" unfolding leftUniformity_def by auto
  } 
  moreover
  {
    fix A B assume as:"A\<in>leftUniformity" "B\<in>leftUniformity"
    from as(1) obtain AU where AU:"AU\<in> \<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>AU}\<subseteq> A" "A\<in>Pow(G\<times>G)" 
      unfolding leftUniformity_def by auto
    from as(2) obtain BU where BU:"BU\<in> \<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>BU}\<subseteq> B" "B\<in>Pow(G\<times>G)" 
      unfolding leftUniformity_def by auto
    from AU(1) BU(1) have "\<zero>\<in>int(AU)\<inter>int(BU)" by auto
    moreover from AU BU have op:"int(AU)\<inter>int(BU)\<in>T" using Top_2_L2 topSpaceAssum IsATopology_def 
      by auto  
    moreover 
    have "int(AU)\<inter>int(BU) \<subseteq> AU\<inter>BU" using Top_2_L1 by auto
    with op have "int(AU)\<inter>int(BU)\<subseteq>int(AU\<inter>BU)" using Top_2_L5 by auto 
    moreover note AU(1) BU(1)
    ultimately have "AU\<inter>BU \<in> \<N>\<^sub>0" unfolding zerohoods_def by auto
    moreover 
    have "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>AU\<inter>BU}\<subseteq>{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>AU}"
      "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>AU\<inter>BU}\<subseteq>{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>AU}" by auto
    with AU(2) BU(2) have "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>AU\<inter>BU}\<subseteq>A\<inter>B" by auto
    ultimately have "A\<inter>B \<in> {V\<in>Pow(G\<times>G).\<exists>U\<in> \<N>\<^sub>0. {\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>U} \<subseteq> V}"
      using AU(3) BU(3) by blast
    then have "A\<inter>B\<in>leftUniformity" unfolding leftUniformity_def by simp 
  }
  hence "\<forall>A\<in>leftUniformity. \<forall>B\<in>leftUniformity. A \<inter> B \<in> leftUniformity" by auto
  moreover
  {
    fix B C assume as:"B\<in>leftUniformity" "C\<in>Pow(G \<times> G)" "B \<subseteq> C"
    from as(1) obtain BU where BU:"BU\<in>\<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> BU}\<subseteq>B" 
      unfolding leftUniformity_def by blast
    from as(3) BU(2) have "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> BU}\<subseteq>C" by auto
    with as(2) BU(1) have "C \<in> {V\<in>Pow(G\<times>G).\<exists>U\<in> \<N>\<^sub>0. {\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>U} \<subseteq> V}"
      by auto 
    then have "C \<in> leftUniformity"  unfolding leftUniformity_def by auto
  }
  then have "\<forall>B\<in>leftUniformity. \<forall>C\<in>Pow(G\<times>G). B\<subseteq>C \<longrightarrow> C\<in>leftUniformity" by auto
  ultimately have leftFilter:"leftUniformity {is a filter on} (G\<times>G)" unfolding IsFilter_def 
    by auto
  {
    assume "0\<in>rightUniformity"
    then obtain U where U:"U\<in>\<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>U}\<subseteq>0" unfolding rightUniformity_def 
      by auto
    have "\<langle>\<zero>,\<zero>\<rangle>:G\<times>G" using zero_in_tgroup by auto
    moreover have "\<zero>\<ra>(\<rm>\<zero>) = \<zero>" 
      using group0_valid_in_tgroup group0.group_inv_of_one group0.group0_2_L2 zero_in_tgroup 
      by auto
    moreover 
    have "\<zero>\<in>int(U)" using U(1) by auto
    then have "\<zero>\<in>U" using Top_2_L1 by auto
    ultimately have "\<langle>\<zero>,\<zero>\<rangle>\<in>{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>U}" by auto
    with U(2) have "\<langle>\<zero>,\<zero>\<rangle>\<in>0" by blast
    hence False by auto
  }
  then have "0\<notin>rightUniformity" by auto 
  moreover  have "rightUniformity \<subseteq> Pow(G\<times>G)" unfolding rightUniformity_def by auto 
  moreover
  {
    have "G\<times>G\<in>Pow(G\<times>G)" by auto 
    moreover have "{\<langle>s,t\<rangle>:G\<times>G. (\<rm>s)\<ra>t:G} \<subseteq> G\<times>G" by auto 
    moreover note zneigh_not_empty
    ultimately have "G\<times>G \<in> rightUniformity" unfolding rightUniformity_def by auto
  } 
  moreover
  {
    fix A B assume as:"A\<in>rightUniformity" "B\<in>rightUniformity"
    from as(1) obtain AU where AU:"AU\<in> \<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>AU}\<subseteq> A" "A\<in>Pow(G\<times>G)" 
      unfolding rightUniformity_def by auto
    from as(2) obtain BU where BU:"BU\<in> \<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>BU}\<subseteq> B" "B\<in>Pow(G\<times>G)" 
      unfolding rightUniformity_def by auto
    from AU(1) BU(1) have "\<zero>\<in>int(AU)\<inter>int(BU)" by auto
    moreover from AU BU have op:"int(AU)\<inter>int(BU)\<in>T" 
      using Top_2_L2 topSpaceAssum IsATopology_def by auto 
    moreover 
    have "int(AU)\<inter>int(BU) \<subseteq> AU\<inter>BU" using Top_2_L1 by auto
    with op have "int(AU)\<inter>int(BU)\<subseteq>int(AU\<inter>BU)" using Top_2_L5 by blast 
    moreover note AU(1) BU(1)
    ultimately have "AU\<inter>BU \<in> \<N>\<^sub>0" unfolding zerohoods_def by auto
    moreover have "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>AU\<inter>BU}\<subseteq>{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>AU}"
      "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>AU\<inter>BU}\<subseteq>{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>AU}" by auto
    with AU(2) BU(2) have "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>AU\<inter>BU}\<subseteq>A\<inter>B" by auto
    ultimately have "A\<inter>B \<in> {V\<in>Pow(G\<times>G).\<exists>U\<in> \<N>\<^sub>0. {\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>U}\<subseteq> V}"
      using AU(3) BU(3) by blast 
    then have "A\<inter>B \<in> rightUniformity" unfolding rightUniformity_def by simp
  }
  hence "\<forall>A\<in>rightUniformity. \<forall>B\<in>rightUniformity. A\<inter>B \<in> rightUniformity" by auto
  moreover
  {
    fix B C assume as:"B\<in>rightUniformity" "C\<in>Pow(G \<times> G)" "B \<subseteq> C"
    from as(1) obtain BU where BU:"BU\<in>\<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in> BU}\<subseteq>B" 
      unfolding rightUniformity_def by blast
    from as(3) BU(2) have "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in> BU}\<subseteq>C" by auto
    then have "C \<in> rightUniformity" using as(2) BU(1) unfolding rightUniformity_def by auto
  }
  then have "\<forall>B\<in>rightUniformity. \<forall>C\<in>Pow(G\<times>G). B\<subseteq>C \<longrightarrow> C\<in>rightUniformity" by auto
  ultimately have rightFilter:"rightUniformity {is a filter on} (G\<times>G)" unfolding IsFilter_def 
    by auto
  {
    fix U assume as:"U\<in>leftUniformity"
    from as obtain V where V:"V\<in>\<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> V} \<subseteq> U" 
      unfolding leftUniformity_def by auto
    then have "V\<subseteq>G" by auto
    {
      fix x assume as2:"x\<in>id(G)"
      from as obtain V where V:"V\<in>\<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> V} \<subseteq> U" 
        unfolding leftUniformity_def by auto
      from V(1) have "\<zero>\<in>int(V)" by auto
      then have V0:"\<zero>\<in>V" using Top_2_L1 by auto
      from as2 obtain t where t:"x=\<langle>t,t\<rangle>" "t:G" by auto
      from t(2) have "(\<rm>t)\<ra>t =\<zero>" using group0_valid_in_tgroup group0.group0_2_L6
        by auto
      with V0 t V(2) have "x\<in>U" by auto
    }
    then have "id(G)\<subseteq>U" by auto 
    moreover
    {
      {
        fix x assume ass:"x\<in>{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> \<sm>V}"
        then obtain s t where as:"s\<in>G" "t\<in>G" "(\<rm>s)\<ra>t \<in> \<sm>V" "x=\<langle>s,t\<rangle>" by force
        from as(3) \<open>V\<subseteq>G\<close> have "(\<rm>s)\<ra>t\<in>{\<rm>q. q\<in>V}" using ginv_image_add by simp 
        then obtain q where q: "q\<in>V" "(\<rm>s)\<ra>t = \<rm>q" by auto
        with \<open>V\<subseteq>G\<close> have "q\<in>G" by auto
        with \<open>s\<in>G\<close> \<open>t\<in>G\<close> \<open>(\<rm>s)\<ra>t = \<rm>q\<close> have "q=(\<rm>t)\<ra>s" 
          using simple_equation1_add by blast  
        with q(1) have "(\<rm>t)\<ra>s \<in> V" by auto
        with as(1,2) have "\<langle>t,s\<rangle> \<in> U" using V(2) by auto
        then have "\<langle>s,t\<rangle> \<in> converse(U)" by auto
        with as(4) have "x \<in> converse(U)" by auto
      }
      then have "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> \<sm>V} \<subseteq> converse(U)" by auto
      moreover have "(\<sm>V):\<N>\<^sub>0" using neg_neigh_neigh V(1) by auto
      moreover note as 
      ultimately have "converse(U) \<in> leftUniformity" unfolding leftUniformity_def by auto
    }
    moreover
    {
      from V(1) obtain W where W:"W:\<N>\<^sub>0" "W \<sad> W \<subseteq>V" using exists_procls_zerohood by blast
      {
        fix x assume as:"x \<in> {\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> W} O {\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> W}"
        then obtain x1 x2 x3 where x:"x1\<in>G" "x2\<in>G" "x3\<in>G" "(\<rm>x1)\<ra>x2 \<in> W" "(\<rm>x2)\<ra>x3 \<in> W" "x=\<langle>x1,x3\<rangle>"
          unfolding comp_def by auto
        from W(1) have "W\<sad>W = f``(W\<times>W)" using interval_add(2) by auto 
        moreover from W(1) have WW:"W\<times>W\<subseteq>G\<times>G" by auto
        moreover 
        from x(4,5) have "\<langle>(\<rm>x1)\<ra>x2,(\<rm>x2)\<ra>x3\<rangle>:W\<times>W" by auto
        with WW have "f`(\<langle>(\<rm>x1)\<ra>x2,(\<rm>x2)\<ra>x3\<rangle>):f``(W\<times>W)"
          using func_imagedef topgroup_f_binop by auto
        ultimately have "((\<rm>x1)\<ra>x2)\<ra>((\<rm>x2)\<ra>x3) :W\<sad>W" by auto
        moreover from x(1,2,3) have "((\<rm>x1)\<ra>x2)\<ra>((\<rm>x2)\<ra>x3) = (\<rm>x1)\<ra> x3"
          using cancel_middle(2) by simp     
        ultimately have "(\<rm>x1)\<ra> x3\<in>W\<sad>W" by auto
        with W(2) have "(\<rm>x1)\<ra> x3\<in>V" by auto
        with x(1,3,6) have "x:{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> V}" by auto
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
      from t(2) have "t\<ra>(\<rm>t) =\<zero>" using group0_valid_in_tgroup group0.group0_2_L6 
        by auto 
      with V0 t V(2) have "x\<in>U" by auto
    }
    then have "id(G)\<subseteq>U" by auto 
    moreover
    {
      {
        fix x assume ass:"x\<in>{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in> \<sm>V}"
        then obtain s t where as:"s\<in>G" "t\<in>G" "s\<ra>(\<rm>t) \<in> \<sm>V" "x=\<langle>s,t\<rangle>" 
          by force
        from as(3) V(1) have "s\<ra>(\<rm>t) \<in> {\<rm>q. q\<in>V}"
          using ginv_image_add by simp 
        then obtain q where q:"q\<in>V" "s\<ra>(\<rm>t) = \<rm>q" by auto 
        with \<open>V\<in>\<N>\<^sub>0\<close> have "q\<in>G" by auto  
        with as(1,2) q(1,2) have "t\<ra>(\<rm>s) \<in> V" using simple_equation0_add 
          by blast 
        with as(1,2,4) V(2) have "x \<in> converse(U)" by auto 
      }
      then have "{\<langle>s,t\<rangle>\<in>G\<times>G.  s\<ra>(\<rm>t) \<in> \<sm>V} \<subseteq> converse(U)" by auto
      moreover from V(1) have "(\<sm>V) \<in> \<N>\<^sub>0" using neg_neigh_neigh by auto
      ultimately have "converse(U) \<in> rightUniformity" using as rightUniformity_def 
        by auto
    }
    moreover
    {
      from V(1) obtain W where W:"W:\<N>\<^sub>0" "W \<sad> W \<subseteq>V" using exists_procls_zerohood by blast
      {
        fix x assume as:"x:{\<langle>s,t\<rangle>\<in>G\<times>G.  s\<ra>(\<rm>t) \<in> W} O {\<langle>s,t\<rangle>\<in>G\<times>G.  s\<ra>(\<rm>t) \<in> W}"
        then obtain x1 x2 x3 where x:"x1:G" "x2:G" "x3:G" "x1\<ra>(\<rm>x2) \<in> W" "x2\<ra>(\<rm>x3) \<in> W" "x=\<langle>x1,x3\<rangle>"
          unfolding comp_def by auto
        from W(1) have "W\<sad>W = f``(W\<times>W)" using interval_add(2) by auto
        moreover from W(1) have WW:"W\<times>W\<subseteq>G\<times>G" by auto
        moreover 
        from x(4,5) have "\<langle>x1\<ra>(\<rm>x2),x2\<ra>(\<rm>x3)\<rangle> \<in> W\<times>W" by auto
        with WW have "f`(\<langle>x1\<ra>(\<rm>x2),x2\<ra>(\<rm>x3)\<rangle>) \<in> f``(W\<times>W)"
          using func_imagedef topgroup_f_binop  by auto
        ultimately have "(x1\<ra>(\<rm>x2))\<ra>(x2\<ra>(\<rm>x3)) \<in> W\<sad>W" by auto
        moreover from x(1,2,3) have "(x1\<ra>(\<rm>x2))\<ra>(x2\<ra>(\<rm>x3)) = x1\<ra> (\<rm>x3)"
          using cancel_middle(1) by simp 
        ultimately have "x1\<ra>(\<rm>x3) \<in> W\<sad>W" by auto
        with W(2) have "x1\<ra>(\<rm>x3) \<in> V" by auto
        then have "x \<in> {\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in> V}" using x(1,3,6) by auto
      }
      with V(2) have "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in> W} O {\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in> W} \<subseteq> U"
        by auto 
      moreover from W(1) have "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in> W} \<in> rightUniformity" 
        unfolding rightUniformity_def  by auto
      ultimately have "\<exists>Z\<in>rightUniformity. Z O Z\<subseteq>U" by auto
    }
    ultimately have "id(G)\<subseteq>U \<and> (\<exists>Z\<in>rightUniformity. Z O Z\<subseteq>U) \<and> converse(U)\<in>rightUniformity" 
      by blast
  }
  then have "\<forall>U\<in>rightUniformity. id(G)\<subseteq>U \<and> (\<exists>Z\<in>rightUniformity. Z O Z\<subseteq>U) \<and> converse(U)\<in>rightUniformity" 
    by auto
  with rightFilter show "rightUniformity {is a uniformity on} G" unfolding IsUniformity_def 
    by auto
qed

text\<open> The topologies generated by the right and left uniformities are the original group topology. \<close>

lemma (in topgroup) top_generated_side_uniformities:
  shows "UniformTopology(leftUniformity,G) = T" and "UniformTopology(rightUniformity,G) = T"
proof-
  let ?M = "{\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle>. t\<in>G}"
  have fun:"?M:G\<rightarrow>Pow(Pow(G))" using neigh_from_uniformity side_uniformities(1) IsNeighSystem_def
    by auto 
  let ?N = "{\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle>. t\<in>G}"
  have funN:"?N:G\<rightarrow>Pow(Pow(G))" using neigh_from_uniformity side_uniformities(2) IsNeighSystem_def
    by auto 
  {
    fix U assume op:"U\<in>T"
    hence "U\<subseteq>G" by auto 
    {
      fix x assume x:"x\<in>U"
      with op have xg:"x\<in>G" and "(\<rm>x) \<in> G" using neg_in_tgroup by auto
      then have "\<langle>x, {V``{x}. V \<in> leftUniformity}\<rangle> \<in> {\<langle>t, {V``{t}. V \<in> leftUniformity}\<rangle>. t\<in>G}" 
        by auto
      with fun have app:"?M`(x) = {V``{x}. V \<in> leftUniformity}" using ZF_fun_from_tot_val 
        by auto 
      have "(\<rm>x)\<ltr>U : \<N>\<^sub>0" using open_trans_neigh op x by auto
      then have V:"{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t\<in>((\<rm>x)\<ltr>U)} \<in> leftUniformity"
        unfolding leftUniformity_def by auto
      with xg have 
        N:"\<forall>t\<in>G. t:{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t\<in>((\<rm>x)\<ltr>U)}``{x} \<longleftrightarrow> (\<rm>x)\<ra>t\<in>((\<rm>x)\<ltr>U)"
        using image_iff by auto 
      {
        fix t assume t:"t\<in>G" 
        {
          assume as:"(\<rm>x)\<ra>t\<in>((\<rm>x)\<ltr>U)"
          then have "(\<rm>x)\<ra>t\<in>LeftTranslation(G,f,\<rm>x)``U" by auto
          then obtain q where q:"q\<in>U" "\<langle>q,(\<rm>x)\<ra>t\<rangle>\<in>LeftTranslation(G,f,\<rm>x)"
            using image_iff by auto 
          with op have "q\<in>G" by auto
          from q(2) have "(\<rm>x)\<ra>q = (\<rm>x)\<ra>t" unfolding LeftTranslation_def 
            by auto
          with \<open>(\<rm>x) \<in> G\<close> \<open>q\<in>G\<close> \<open>t\<in>G\<close> have "q = t" using neg_in_tgroup cancel_left_add 
            by blast 
          with q(1) have "t\<in>U" by auto
        } 
        moreover
        {
          assume t:"t\<in>U"
          with \<open>U\<subseteq>G\<close> \<open>(\<rm>x)\<in>G\<close> have "(\<rm>x)\<ra>t \<in> ((\<rm>x)\<ltr>U)"
            using ltrans_image_add by auto 
        } 
        ultimately have "(\<rm>x)\<ra>t\<in>((\<rm>x)\<ltr>U) \<longleftrightarrow> t:U" by blast
      } 
      with N have "\<forall>t\<in>G. t:{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in> ((\<rm>x)\<ltr>U)}``{x} \<longleftrightarrow> t\<in>U" 
        by blast
      with op have "\<forall>t. t:{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t\<in>((\<rm>x)\<ltr>U)}``{x} \<longleftrightarrow> t:U" 
        by auto
      hence "U = {\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t\<in>((\<rm>x)\<ltr>U)}``{x}" by auto
      with V have "\<exists>V\<in>leftUniformity. U=V``{x}" by blast 
      with app have "U \<in> {\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G}`(x)" by auto
      moreover from \<open>x\<in>G\<close> funN have app:"?N`(x) = {V``{x}. V \<in> rightUniformity}" 
        using ZF_fun_from_tot_val by simp 
      moreover 
      from x op have openTrans:"U\<rtr>(\<rm>x): \<N>\<^sub>0" using open_trans_neigh_2 by auto
      then have V:"{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t)\<in>(U\<rtr>(\<rm>x))} \<in> rightUniformity"
        unfolding rightUniformity_def by auto
      with xg have 
        N:"\<forall>t\<in>G. t:{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t)\<in>(U\<rtr>(\<rm>x))}-``{x} \<longleftrightarrow> t\<ra>(\<rm>x)\<in>(U\<rtr>(\<rm>x))"
        using vimage_iff by auto
      moreover 
      {
        fix t assume t:"t\<in>G" 
        {
          assume as:"t\<ra>(\<rm>x)\<in>(U\<rtr>(\<rm>x))"
          hence "t\<ra>(\<rm>x)\<in>RightTranslation(G,f,\<rm>x)``U" by auto
          then obtain q where q:"q\<in>U" "\<langle>q,t\<ra>(\<rm>x)\<rangle>\<in>RightTranslation(G,f,\<rm>x)"
            using image_iff by auto
          with op have "q\<in>G" by auto
          from q(2) have "q\<ra>(\<rm>x) = t\<ra>(\<rm>x)" unfolding RightTranslation_def by auto
          with \<open>q\<in>G\<close> \<open>(\<rm>x) \<in> G\<close> \<open>t\<in>G\<close> have "q = t" using cancel_right_add by simp 
          with q(1) have "t\<in>U" by auto
        } 
        moreover
        {
          assume "t\<in>U"
          with \<open>(\<rm>x)\<in>G\<close> \<open>U\<subseteq>G\<close> have "t\<ra>(\<rm>x)\<in>(U\<rtr>(\<rm>x))" using rtrans_image_add
            by auto 
        } ultimately have "t\<ra>(\<rm>x)\<in>(U\<rtr>(\<rm>x)) \<longleftrightarrow> t:U" by blast
      } with N have "\<forall>t\<in>G. t:{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t)\<in>(U\<rtr>(\<rm>x))}-``{x} \<longleftrightarrow> t:U" 
        by blast
      with op have "\<forall>t. t:{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t)\<in>(U\<rtr>(\<rm>x))}-``{x} \<longleftrightarrow> t:U" 
        by auto
      hence "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t)\<in>(U\<rtr>(\<rm>x))}-``{x} = U" by auto
      then have "U = converse({\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t)\<in>(U\<rtr>(\<rm>x))})``{x}" 
        unfolding vimage_def by simp
      with V app have "U \<in> {\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle> . t \<in> G}`(x)"
        using side_uniformities(2) IsUniformity_def by auto 
      ultimately have 
        "U \<in> {\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G}`(x)" and 
        "U \<in> {\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle> . t \<in> G}`(x)" 
        by auto
    }
    hence 
      "\<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G} ` x" and 
      "\<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle> . t \<in> G} ` x"
      by auto
  }
  hence 
    "T\<subseteq>{U \<in> Pow(G) . \<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G} ` x}" and 
    "T\<subseteq>{U \<in> Pow(G) . \<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle> . t \<in> G} ` x}" 
    by auto
  moreover
  {
    fix U assume as:"U \<in> Pow(G)" "\<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G}`(x)"
    {
      fix x assume x:"x\<in>U"
      with as(1) have xg:"x\<in>G" by auto
      from x as(2) have "U\<in>{\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G}`(x)" by auto
      with xg fun have "U\<in>{V `` {x} . V \<in> leftUniformity}" using apply_equality by auto 
      then obtain V where V:"U=V``{x}" "V\<in>leftUniformity" by auto
      from V(2) obtain W where W:"W\<in> \<N>\<^sub>0" "{\<langle>s,t\<rangle>:G\<times>G. (\<rm>s)\<ra>t:W}\<subseteq>V" 
        unfolding leftUniformity_def by auto
      from W(2) have A:"{\<langle>s,t\<rangle>:G\<times>G. (\<rm>s)\<ra>t:W}``{x}\<subseteq>V``{x}" by auto
      from xg have "\<forall>q\<in>G. q\<in>({\<langle>s,t\<rangle>:G\<times>G. (\<rm>s)\<ra>t:W}``{x}) \<longleftrightarrow> (\<rm>x)\<ra>q:W"
        using image_iff by auto 
      hence B:"{\<langle>s,t\<rangle>:G\<times>G. (\<rm>s)\<ra>t:W}``{x} = {t\<in>G. (\<rm>x)\<ra>t:W}" by auto
      from W(1) have WG:"W\<subseteq>G" by auto
      {
        fix t assume t:"t \<in> x\<ltr>W"
        then have "t \<in> LeftTranslation(G,f,x)``W" by auto
        then obtain s where s:"s\<in>W" "\<langle>s,t\<rangle>\<in>LeftTranslation(G,f,x)" using image_iff by auto
        with \<open>W\<subseteq>G\<close> have "s\<in>G" by auto 
        from s(2) have "t=x\<ra>s" "t\<in>G" unfolding LeftTranslation_def by auto
        with \<open>x\<in>G\<close> \<open>s\<in>G\<close> have "(\<rm>x)\<ra>t = s" using put_on_the_other_side(2) by simp 
        with s(1) have "(\<rm>x)\<ra>t\<in>W" by auto
        with \<open>t\<in>G\<close> have "t \<in> {s\<in>G. (\<rm>x)\<ra>s:W}" by auto
      }
      then have "x\<ltr>W \<subseteq> {t\<in>G. (\<rm>x)\<ra>t\<in>W}" by auto
      with B have "x \<ltr> W \<subseteq> {\<langle>s,t\<rangle> \<in> G \<times> G . (\<rm> s) \<ra> t \<in> W} `` {x}" by auto
      with A have "x \<ltr> W \<subseteq> V`` {x}" by blast
      with V(1) have "x \<ltr> W \<subseteq> U" by auto
      then have "int(x \<ltr> W) \<subseteq> U" using Top_2_L1 by blast
      moreover from xg W(1) have "x\<in>int(x \<ltr> W)" using elem_in_int_trans by auto
      moreover have "int(x \<ltr> W)\<in>T" using Top_2_L2 by auto
      ultimately have "\<exists>Y\<in>T. x\<in>Y \<and> Y\<subseteq>U" by auto
    }
    then have "U\<in>T" using open_neigh_open by auto
  } hence  "{U \<in> Pow(G) . \<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G} ` x} \<subseteq> T" 
    by auto
  moreover
  {
    fix U assume as:"U \<in> Pow(G)" "\<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle> . t \<in> G} ` x"
    {
      fix x assume x:"x\<in>U"
      with as(1) have xg:"x\<in>G" by auto
      from x as(2) have "U\<in>{\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle> . t \<in> G} ` x" by auto
      with xg funN have "U\<in>{V `` {x} . V \<in> rightUniformity}" using apply_equality 
        by auto 
      then obtain V where V:"U=V``{x}" "V \<in> rightUniformity" by auto
      then have "converse(V) \<in> rightUniformity" using side_uniformities(2) IsUniformity_def 
        by auto
      then obtain W where W:"W\<in> \<N>\<^sub>0" "{\<langle>s,t\<rangle>:G\<times>G. s\<ra>(\<rm>t):W}\<subseteq>converse(V)" 
        unfolding rightUniformity_def by auto
      from W(2) have A:"{\<langle>s,t\<rangle>:G\<times>G. s\<ra>(\<rm>t):W}-``{x}\<subseteq>V``{x}" by auto
      from xg have "\<forall>q\<in>G. q\<in>({\<langle>s,t\<rangle>:G\<times>G. s\<ra>(\<rm>t):W}-``{x}) \<longleftrightarrow> q\<ra>(\<rm>x):W"
        using image_iff by auto 
      hence B:"{\<langle>s,t\<rangle>:G\<times>G. s\<ra>(\<rm>t):W}-``{x} = {t\<in>G. t\<ra>(\<rm>x):W}" by auto
      from W(1) have WG:"W\<subseteq>G" by auto
      {
        fix t assume "t \<in> W\<rtr>x"
        with \<open>x\<in>G\<close> \<open>W\<subseteq>G\<close> obtain s where "s\<in>W" and "t=s\<ra>x" using rtrans_image_add 
          by auto
        with \<open>W\<subseteq>G\<close> have "s\<in>G" by auto 
        with \<open>x\<in>G\<close> \<open>t=s\<ra>x\<close> have "t\<in>G" using group_op_closed_add by simp 
        from \<open>x\<in>G\<close> \<open>s\<in>G\<close> \<open>t=s\<ra>x\<close> have "t\<ra>(\<rm>x) = s" using put_on_the_other_side 
          by simp
        with \<open>s\<in>W\<close> \<open>t\<in>G\<close> have "t \<in> {s\<in>G. s\<ra>(\<rm>x) \<in> W}" by auto
      }
      then have "W\<rtr>x \<subseteq> {t:G. t\<ra>(\<rm>x):W}" by auto
      with B have "W \<rtr> x \<subseteq> {\<langle>s,t\<rangle> \<in> G \<times> G . s \<ra> (\<rm> t) \<in> W}-``{x}" by auto
      with A have "W \<rtr> x \<subseteq> V`` {x}" by blast
      with V(1) have "W \<rtr> x \<subseteq> U" by auto
      then have "int(W \<rtr> x) \<subseteq> U" using Top_2_L1 by blast
      moreover 
      from xg W(1) have "x\<in>int(W \<rtr> x)" using elem_in_int_trans_2 by auto
      moreover have "int(W \<rtr> x)\<in>T" using Top_2_L2 by auto
      ultimately have "\<exists>Y\<in>T. x\<in>Y \<and> Y\<subseteq>U" by auto
    }
    then have "U\<in>T" using open_neigh_open by auto
  }
  ultimately have 
    "{U \<in> Pow(G) . \<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G} ` x} = T" and 
    " {U \<in> Pow(G) . \<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle> . t \<in> G} ` x} = T" 
    by auto
  then show "UniformTopology(leftUniformity,G) =T"  and "UniformTopology(rightUniformity,G) =T" 
    unfolding UniformTopology_def by auto 
qed

end
