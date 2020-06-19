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

theory TopologicalGroup_Uniformity_ZF imports TopologicalGroup_ZF_1 UniformSpace_ZF_1

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
    with op have "int(AU)\<inter>int(BU)\<subseteq>int(AU\<inter>BU)" using Top_2_L5[of "int(AU)\<inter>int(BU)"]
      by auto moreover note AU(1) BU(1)
    ultimately have "AU\<inter>BU: \<N>\<^sub>0" unfolding zerohoods_def by auto
    moreover have "{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>AU\<inter>BU}\<subseteq>{\<langle>s,t\<rangle>\<in>G\<times>G. (\<rm>s)\<ra>t \<in>AU}" by auto
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
    with op have "int(AU)\<inter>int(BU)\<subseteq>int(AU\<inter>BU)" using Top_2_L5[of "int(AU)\<inter>int(BU)"]
      by auto moreover note AU(1) BU(1)
    ultimately have "AU\<inter>BU: \<N>\<^sub>0" unfolding zerohoods_def by auto
    moreover have "{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>AU\<inter>BU}\<subseteq>{\<langle>s,t\<rangle>\<in>G\<times>G. s\<ra>(\<rm>t) \<in>AU}" by auto
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
  ultimately show "{U \<in> Pow(G) . \<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> leftUniformity}\<rangle> . t \<in> G} ` x} = T" 
  "{U \<in> Pow(G) . \<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> rightUniformity}\<rangle> . t \<in> G} ` x} = T" by auto
qed

text\<open> The side uniformities are called this way because of how they affect left and right translations \<close>

lemma (in topgroup) left_mult_uniformity:
  assumes "x:G"
  shows "LeftTranslation(G,f,x) {is uniformly continuous between} leftUniformity {and} leftUniformity" 
    unfolding IsUniformlyCont_def[OF group0.group0_5_L1(2)[OF group0_valid_in_tgroup assms] side_uniformities(1) side_uniformities(1)]
    unfolding leftUniformity_def
proof(safe)
  fix xa xaa assume as:"\<langle>xa, xaa\<rangle> \<in> ProdFunction(LeftTranslation(G, f, x), LeftTranslation(G, f, x))"
  then show "xa : G\<times>G" using prodFunction[OF group0.group0_5_L1(2)[OF group0_valid_in_tgroup assms] group0.group0_5_L1(2)[OF group0_valid_in_tgroup assms]]
    unfolding Pi_def by auto
next
  fix V U assume as:"V \<subseteq> G \<times> G" "U \<in> \<N>\<^sub>0" "{\<langle>s,t\<rangle> \<in> G \<times> G . (\<rm> s) \<ra> t \<in> U} \<subseteq> V"
  {
    fix z assume z:"z:{\<langle>s,t\<rangle> \<in> G \<times> G . (\<rm> s) \<ra> t \<in> U}"
    then obtain s t where st:"z=\<langle>s,t\<rangle>" "s:G" "t:G" by auto
    from st(1) z have st2:"(\<rm> s) \<ra> t \<in> U" by auto
    from st(1) have "ProdFunction(LeftTranslation(G, f, x), LeftTranslation(G, f, x))`z = \<langle>LeftTranslation(G, f, x)`s, LeftTranslation(G, f, x)`t\<rangle>"
      using prodFunctionApp[OF group0.group0_5_L1(2)[OF group0_valid_in_tgroup assms] group0.group0_5_L1(2)[OF group0_valid_in_tgroup assms] st(2,3)]
      by auto
    then have "ProdFunction(LeftTranslation(G, f, x), LeftTranslation(G, f, x))`z = \<langle>x\<ra>s,x\<ra>t\<rangle>" 
      using group0.group0_5_L2(2)[OF group0_valid_in_tgroup assms] st(2,3) by auto
    moreover
    have "(\<rm> (x\<ra>s)) \<ra> (x\<ra>t) = (\<rm>s)\<ra>(\<rm>x)\<ra>(x\<ra>t)" using group0.group_inv_of_two[OF group0_valid_in_tgroup]
      assms st(2) by auto
    then have "(\<rm> (x\<ra>s)) \<ra> (x\<ra>t) = (\<rm>s)\<ra>((\<rm>x)\<ra>(x\<ra>t))" using group0.group_oper_assoc[OF group0_valid_in_tgroup
      group0.inverse_in_group[OF group0_valid_in_tgroup st(2)] group0.inverse_in_group[OF group0_valid_in_tgroup assms] group0.group_op_closed[OF group0_valid_in_tgroup assms st(3)]]
      by auto
    then have "(\<rm> (x\<ra>s)) \<ra> (x\<ra>t) = (\<rm>s)\<ra>((\<rm>x)\<ra>x\<ra>t)" using group0.group_oper_assoc[OF group0_valid_in_tgroup
      group0.inverse_in_group[OF group0_valid_in_tgroup assms] assms st(3)] by auto
    then have "(\<rm> (x\<ra>s)) \<ra> (x\<ra>t) = (\<rm>s)\<ra>(\<zero> \<ra>t)" using group0.group0_2_L6[OF group0_valid_in_tgroup assms] by auto
    then have "(\<rm> (x\<ra>s)) \<ra> (x\<ra>t) = (\<rm>s)\<ra>t" using group0.group0_2_L2[OF group0_valid_in_tgroup] st(3) by auto
    with st2 have "(\<rm> (x\<ra>s)) \<ra> (x\<ra>t) :U" by auto
    ultimately have "ProdFunction(LeftTranslation(G, f, x), LeftTranslation(G, f, x))`z : {\<langle>s,t\<rangle> \<in> G \<times> G . (\<rm> s) \<ra> t \<in> U}"
      using group0.group_op_closed[OF group0_valid_in_tgroup assms] st(2,3) by auto
    with as(3) have "ProdFunction(LeftTranslation(G, f, x), LeftTranslation(G, f, x))`z : V" by force moreover
    have "\<langle>z,ProdFunction(LeftTranslation(G, f, x), LeftTranslation(G, f, x))`z\<rangle>: ProdFunction(LeftTranslation(G, f, x), LeftTranslation(G, f, x))"
      using apply_iff[OF prodFunction[OF group0.group0_5_L1(2)[OF group0_valid_in_tgroup assms] group0.group0_5_L1(2)[OF group0_valid_in_tgroup assms]]]
      st by auto
    ultimately have "z: ProdFunction(LeftTranslation(G, f, x), LeftTranslation(G, f, x))-`` V" using vimage_iff by auto
  }
  with as(2) show "\<exists>U\<in>\<N>\<^sub>0. {\<langle>s,t\<rangle> \<in> G \<times> G . (\<rm> s) \<ra> t \<in> U} \<subseteq>  ProdFunction(LeftTranslation(G, f, x), LeftTranslation(G, f, x)) -``V" by blast
qed

lemma (in topgroup) right_mult_uniformity:
  assumes "x:G"
  shows "RightTranslation(G,f,x) {is uniformly continuous between} rightUniformity {and} rightUniformity" 
    unfolding IsUniformlyCont_def[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup assms] side_uniformities(2) side_uniformities(2)]
    unfolding rightUniformity_def
proof(safe)
  fix xa xaa assume as:"\<langle>xa, xaa\<rangle> \<in> ProdFunction(RightTranslation(G, f, x), RightTranslation(G, f, x))"
  then show "xa : G\<times>G" using prodFunction[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup assms] 
    group0.group0_5_L1(1)[OF group0_valid_in_tgroup assms]] unfolding Pi_def by auto
next
  fix V U assume as:"V \<subseteq> G \<times> G" "U \<in> \<N>\<^sub>0" "{\<langle>s,t\<rangle> \<in> G \<times> G . s \<ra> (\<rm> t) \<in> U} \<subseteq> V"
  {
    fix z assume z:"z:{\<langle>s,t\<rangle> \<in> G \<times> G . s \<ra> (\<rm> t) \<in> U}"
    then obtain s t where st:"z=\<langle>s,t\<rangle>" "s:G" "t:G" by auto
    from st(1) z have st2:"s \<ra> (\<rm> t) \<in> U" by auto
    from st(1) have "ProdFunction(RightTranslation(G, f, x), RightTranslation(G, f, x))`z = \<langle>RightTranslation(G, f, x)`s, RightTranslation(G, f, x)`t\<rangle>"
      using prodFunctionApp[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup assms] group0.group0_5_L1(1)[OF group0_valid_in_tgroup assms] 
      st(2,3)] by auto
    then have "ProdFunction(RightTranslation(G, f, x), RightTranslation(G, f, x))`z = \<langle>s\<ra>x,t\<ra>x\<rangle>" 
      using group0.group0_5_L2(1)[OF group0_valid_in_tgroup assms] st(2,3) by auto
    moreover
    have "(s\<ra>x) \<ra> (\<rm>(t\<ra>x)) = (s\<ra>x)\<ra>((\<rm>x)\<ra>(\<rm>t))" using group0.group_inv_of_two[OF group0_valid_in_tgroup]
      assms st(3) by auto
    then have "(s\<ra>x) \<ra> (\<rm>(t\<ra>x)) = s\<ra>(x\<ra>((\<rm>x)\<ra>(\<rm>t)))" using group0.group_oper_assoc[OF group0_valid_in_tgroup
      st(2) assms group0.group_op_closed[OF group0_valid_in_tgroup group0.inverse_in_group[OF group0_valid_in_tgroup assms]  group0.inverse_in_group[OF group0_valid_in_tgroup st(3)]]]
      by auto
    then have "(s\<ra>x) \<ra> (\<rm>(t\<ra>x)) = s\<ra>(x\<ra>(\<rm>x)\<ra>(\<rm>t))" using group0.group_oper_assoc[OF group0_valid_in_tgroup
      assms group0.inverse_in_group[OF group0_valid_in_tgroup assms] group0.inverse_in_group[OF group0_valid_in_tgroup st(3)]] by auto
    then have "(s\<ra>x) \<ra> (\<rm>(t\<ra>x)) = s\<ra>(\<zero> \<ra>(\<rm>t))" using group0.group0_2_L6[OF group0_valid_in_tgroup assms] by auto
    then have "(s\<ra>x) \<ra> (\<rm>(t\<ra>x)) = s\<ra>(\<rm>t)" using group0.group0_2_L2[OF group0_valid_in_tgroup] group0.inverse_in_group[OF group0_valid_in_tgroup st(3)] by auto
    with st2 have "(s\<ra>x) \<ra> (\<rm>(t\<ra>x)) :U" by auto
    ultimately have "ProdFunction(RightTranslation(G, f, x), RightTranslation(G, f, x))`z : {\<langle>s,t\<rangle> \<in> G \<times> G . s\<ra>(\<rm>t) \<in> U}"
      using group0.group_op_closed[OF group0_valid_in_tgroup _ assms] st(2,3) by auto
    with as(3) have "ProdFunction(RightTranslation(G, f, x), RightTranslation(G, f, x))`z : V" by force moreover
    have "\<langle>z,ProdFunction(RightTranslation(G, f, x), RightTranslation(G, f, x))`z\<rangle>: ProdFunction(RightTranslation(G, f, x), RightTranslation(G, f, x))"
      using apply_iff[OF prodFunction[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup assms] group0.group0_5_L1(1)[OF group0_valid_in_tgroup assms]]]
      st by auto
    ultimately have "z: ProdFunction(RightTranslation(G, f, x), RightTranslation(G, f, x))-`` V" using vimage_iff by auto
  }
  with as(2) show "\<exists>U\<in>\<N>\<^sub>0. {\<langle>s,t\<rangle> \<in> G \<times> G . s \<ra> (\<rm> t) \<in> U} \<subseteq>  ProdFunction(RightTranslation(G, f, x), RightTranslation(G, f, x)) -``V" by blast
qed

text\<open> The third uniformity important on topological groups is called the uniformity of Roelcke. \<close> 

definition(in topgroup) roelckeUniformity
 where "roelckeUniformity \<equiv> {V\<in>Pow(G\<times>G). \<exists>U\<in> \<N>\<^sub>0. {\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(U\<rtr>s)\<sad>U}\<subseteq> V}"

lemma (in topgroup) roelcke_uniformity:
  shows "roelckeUniformity {is a uniformity on} G" unfolding IsUniformity_def
proof(safe)
  fix U assume U:"U:roelckeUniformity"
  from U obtain V where V:"{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(V\<rtr>s)\<sad>V} \<subseteq> U" "V\<in> \<N>\<^sub>0" "U:Pow(G\<times>G)" unfolding roelckeUniformity_def by auto
  from V(2) have VG:"V\<subseteq>G" by auto
  from V(2) have "\<zero>\<in>int(V)" by auto
  then have V0:"\<zero>\<in>V" using Top_2_L1 by auto
  {
    fix x assume x:"x:G"
    with V0 have "RightTranslation(G, f, x) `\<zero> : V\<rtr>x" using func_imagedef[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup x] VG] by auto
    then have "x : V\<rtr>x" using apply_equality[OF _ group0.group0_5_L1(1)[OF group0_valid_in_tgroup x], of "\<zero>" x] unfolding RightTranslation_def
      using group0.group0_2_L2[OF group0_valid_in_tgroup] x by auto moreover
    from VG x have VxG:"V\<rtr>x \<subseteq> G" using func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup x]] by auto moreover
    note V0 ultimately have "x\<ra>\<zero> : (V\<rtr>x)\<sad>V" using interval_add(4)[OF _ VG] by auto
    then have "x: (V\<rtr>x)\<sad>V" using group0.group0_2_L2[OF group0_valid_in_tgroup] x by auto
    with x have "\<langle>x,x\<rangle>:{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(V\<rtr>s)\<sad>V}" by auto
    with V(1) show "\<langle>x,x\<rangle>:U" by auto
  }
  {
    fix l assume "l:{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>((\<sm>V)\<rtr>s)\<sad>(\<sm>V)}"
    then obtain s t where st:"s:G" "t:G" "t \<in>((\<sm>V)\<rtr>s)\<sad>(\<sm>V)" "l=\<langle>s,t\<rangle>" by force
    from st(3) VG have smV:"(\<sm>V) = {\<rm>q. q:V}" 
      using func_imagedef[OF group0_2_T2[OF Ggroup], of V] unfolding zerohoods_def
      by auto
    have smG:"(\<sm>V) \<subseteq> G" using func1_1_L6(2)[OF group0_2_T2[OF Ggroup]] by auto
    from st(1) have VxG:"(\<sm>V)\<rtr>s \<subseteq> G" using func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup]] by auto
    from st(2) have VsG:"V\<rtr>t \<subseteq> G" using func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup]] by auto
    from st(3) obtain x y where xy:"t = x\<ra>y" "x:(\<sm>V)\<rtr>s" "y:(\<sm>V)" using elements_in_set_sum[OF VxG smG, of t] by blast
    from xy(2) smG st(1) obtain z where z:"x = z\<ra>s" "z:(\<sm>V)" using elements_in_rtrans by blast
    from xy(2,3) VxG smG z(2) have xyzG:"x:G" "y:G" "z:G" by auto
    from xyzG(1,2) st(2) xy(1) have "t\<ra>(\<rm>y) = x" using group0.group0_2_L18(1)[OF group0_valid_in_tgroup, of x y t] by auto
    with z(1) have "t\<ra>(\<rm>y) = z\<ra>s" by auto
    with xyzG(3) st(1) have "(\<rm>z)\<ra>(t\<ra>(\<rm>y)) = s" using group0.group0_2_L18(2)[OF group0_valid_in_tgroup, of z s "t\<ra>(\<rm>y)"]
      group0.group_op_closed[OF group0_valid_in_tgroup xyzG(3) st(1)] by auto
    then have ts:"(\<rm>z)\<ra>t\<ra>(\<rm>y) = s" using group0.group_oper_assoc[OF group0_valid_in_tgroup group0.inverse_in_group[OF group0_valid_in_tgroup xyzG(3)]]
      st(2) group0.inverse_in_group[OF group0_valid_in_tgroup xyzG(2)] by auto
    {
      fix u assume u:"u:(\<sm>V)"
      with smV obtain qz where "qz:V" "u=\<rm>qz" by auto 
      with VG have "qz:V" "qz:G" "(\<rm>u)=\<rm>(\<rm>qz)" by auto
      then have "qz:V" "(\<rm>u)=qz" using group0.group_inv_of_inv[OF group0_valid_in_tgroup, of qz] by auto
      then have "(\<rm>u) : V" by auto
    }
    then have R:"!!u. u:(\<sm>V) ==> (\<rm>u) : V" by auto
    with z(2) xy(3) have zy:"(\<rm>z):V" "(\<rm>y):V" by auto
    from zy(1) VG st(2) have "(\<rm>z)\<ra>t : V\<rtr>t" using rtrans_image_add by auto
    with zy(2) VG VsG have "(\<rm>z)\<ra>t\<ra>(\<rm>y) : (V\<rtr>t)\<sad>V" using interval_add(4) by auto
    with ts have "s:(V\<rtr>t)\<sad>V" by auto
    with st(1,2) have "\<langle>s,t\<rangle> :converse({\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(V\<rtr>s)\<sad>V})" using converse_iff[of s t "{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(V\<rtr>s)\<sad>V}"] by auto
    with V(1) have "\<langle>s,t\<rangle> : converse(U)" by auto
    with st(4) have "l:converse(U)" by auto
  }
  then have "{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>((\<sm>V)\<rtr>s)\<sad>(\<sm>V)} \<subseteq> converse(U)" by auto
  moreover from V(2) have "(\<sm>V): \<N>\<^sub>0" using neg_neigh_neigh by auto
  ultimately have "\<exists>V\<in> \<N>\<^sub>0. {\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(V\<rtr>s)\<sad>V} \<subseteq> converse(U)" by auto moreover
  from V(3) have "converse(U) \<subseteq> G\<times>G" unfolding converse_def by auto
  ultimately show "converse(U) : roelckeUniformity" unfolding roelckeUniformity_def by auto
  from V(2) obtain W where W:"W:\<N>\<^sub>0" "W \<sad> W \<subseteq>V" using exists_procls_zerohood by blast
  then have WG:"W\<subseteq>G" by auto
  {
    fix k assume as:"k:{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(W\<rtr>s)\<sad>W} O {\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(W\<rtr>s)\<sad>W}"
    then obtain x1 x2 x3 where x:"x1:G" "x2:G" "x3:G" "x2 : (W\<rtr>x1)\<sad>W" "x3: (W\<rtr>x2)\<sad>W" "k=\<langle>x1,x3\<rangle>"
      unfolding comp_def by auto
    from x(1) have VsG:"W\<rtr>x1 \<subseteq> G" using func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup]] by auto
    from x(1) have Vx1G:"V\<rtr>x1 \<subseteq> G" using func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup]] by auto
    from x(4) VsG WG obtain x y where xy:"x2 = x\<ra>y" "x:W\<rtr>x1" "y:W" using elements_in_set_sum by blast
    from xy(2) WG x(1) obtain z where z:"x = z\<ra>x1" "z:W" using elements_in_rtrans by blast
    from z(2) xy(3) WG have yzG:"y:G" "z:G" by auto
    from x(2) have VsG:"W\<rtr>x2 \<subseteq> G" using func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup]] by auto
    from x(5) VsG WG obtain x' y' where xy2:"x3 = x'\<ra>y'" "x':W\<rtr>x2" "y':W" using elements_in_set_sum by blast
    from xy2(2) WG x(2) obtain z' where z2:"x' = z'\<ra>x2" "z':W" using elements_in_rtrans by blast
    from z2(2) xy2(3) WG have yzG2:"y':G" "z':G" by auto
    from xy(1) z(1) xy2(1) z2(1) have "x3 = (z'\<ra>(z\<ra>x1\<ra>y))\<ra>y'" by auto
    with yzG yzG2 x(1) have x3:"x3 = ((z'\<ra>z)\<ra>x1)\<ra>(y\<ra>y')" using group0.group_oper_assoc[OF group0_valid_in_tgroup]
      group0.group_op_closed[OF group0_valid_in_tgroup] by auto
    moreover
    from xy(3) z(2) xy2(3) z2(2) WG have "z'\<ra>z : W\<sad>W" "y\<ra>y' :W\<sad>W" using interval_add(4) by auto
    with W(2) have yzV:"z'\<ra>z : V" "y\<ra>y' : V" by auto
    from yzV(1) VG x(1) have "(z'\<ra>z)\<ra>x1 : V\<rtr>x1" using rtrans_image_add by auto
    with yzV(2) Vx1G VG have "((z'\<ra>z)\<ra>x1)\<ra>(y\<ra>y') : (V\<rtr>x1)\<sad>V" using interval_add(4) by auto
    with x3 have "x3:(V\<rtr>x1)\<sad>V" by auto
    with x(1,3,6) have "k:{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(V\<rtr>s)\<sad>V}" by auto
  }
  with V(1) have "{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(W\<rtr>s)\<sad>W} O {\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(W\<rtr>s)\<sad>W}\<subseteq> U" by auto moreover
  have "{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(W\<rtr>s)\<sad>W}\<in>roelckeUniformity" unfolding roelckeUniformity_def using W(1) by auto
  ultimately show "\<exists>Z\<in>roelckeUniformity. Z O Z\<subseteq>U" by auto
next
  show "roelckeUniformity {is a filter on} (G \<times> G)" unfolding IsFilter_def
  proof (safe)
    {
      assume "0\<in>roelckeUniformity"
      then obtain W where U:"W\<in>\<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(W\<rtr>s)\<sad>W}\<subseteq>0" unfolding roelckeUniformity_def by auto
      have "\<langle> \<zero>,\<zero>\<rangle>:G\<times>G"using zero_in_tgroup by auto
      moreover have "\<zero> = f`\<langle>f`\<langle>\<zero>,\<zero>\<rangle>,\<zero>\<rangle>" using group0.group0_2_L2[OF group0_valid_in_tgroup] zero_in_tgroup by auto
      moreover have "\<zero>\<in>int(W)" using U(1) by auto
      then have nW:"\<zero>\<in>W" using Top_2_L1 by auto
      with U(1) have "\<zero>\<ra>\<zero> : W\<rtr>\<zero>" using rtrans_image_add[of W "\<zero>"] group0.group0_2_L2[OF group0_valid_in_tgroup] by auto
      with nW U(1) have "f`\<langle>f`\<langle>\<zero>,\<zero>\<rangle>,\<zero>\<rangle> :(W\<rtr>\<zero>)\<sad>W" using interval_add(4) func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup]]
        group0.group0_2_L2[OF group0_valid_in_tgroup] by auto 
      ultimately have "\<langle>\<zero>,\<zero>\<rangle>\<in>{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(W\<rtr>s)\<sad>W}" by auto
      then have "\<langle>\<zero>,\<zero>\<rangle>\<in>0" using U(2) by blast
      then show False by auto
    }
    {
      fix x xa assume as:"x:roelckeUniformity" "xa:x"
      have "roelckeUniformity \<subseteq> Pow(G\<times>G)" unfolding roelckeUniformity_def by auto
      with as show "xa:G\<times>G" by auto
    }
    {
      have "G\<times>G\<in>Pow(G\<times>G)" by auto moreover
      have "{\<langle>s,t\<rangle>:G\<times>G.  t \<in>(G\<rtr>s)\<sad>G} \<subseteq> G\<times>G" by auto moreover
      note zneigh_not_empty
      ultimately show "G\<times>G\<in>roelckeUniformity" unfolding roelckeUniformity_def by auto
    }
    {
      fix A B assume as:"A\<in>roelckeUniformity" "B\<in>roelckeUniformity"
      from as(1) obtain AU where AU:"AU\<in> \<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(AU\<rtr>s)\<sad>AU}\<subseteq> A" "A\<in>Pow(G\<times>G)" unfolding roelckeUniformity_def by auto
      from as(2) obtain BU where BU:"BU\<in> \<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(BU\<rtr>s)\<sad>BU}\<subseteq> B" "B\<in>Pow(G\<times>G)" unfolding roelckeUniformity_def by auto
      from AU(1) BU(1) have "\<zero>\<in>int(AU)\<inter>int(BU)" by auto
      moreover have op:"int(AU)\<inter>int(BU)\<in>T" using Top_2_L2[of AU] Top_2_L2[of BU]
        using topSpaceAssum unfolding IsATopology_def by auto
      have "int(AU)\<inter>int(BU) \<subseteq> AU\<inter>BU" using Top_2_L1 by auto
      with op have "int(AU)\<inter>int(BU)\<subseteq>int(AU\<inter>BU)" using Top_2_L5[of "int(AU)\<inter>int(BU)"]
        by auto moreover note AU(1) BU(1)
      ultimately have interNeigh:"AU\<inter>BU: \<N>\<^sub>0" unfolding zerohoods_def by auto moreover
      {
        fix z assume "z:{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>((AU\<inter>BU)\<rtr>s)\<sad>(AU\<inter>BU)}"
        then obtain s t where z:"z=\<langle>s,t\<rangle>" "s:G" "t:G" "t \<in>((AU\<inter>BU)\<rtr>s)\<sad>(AU\<inter>BU)" by force
        from z(2,4) interNeigh obtain x y where t:"t=x\<ra>y" "x:(AU\<inter>BU)\<rtr>s" "y:AU\<inter>BU" using interval_add(4) 
          func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup]] by auto
        from t(2) z(2) interNeigh obtain q where x:"x=q\<ra>s" "q:AU\<inter>BU" using rtrans_image_add by auto
        with AU(1) BU(1) z(2) have "x:AU\<rtr>s" "x:BU\<rtr>s" using rtrans_image_add by auto
        with t(1,3) z(2) AU(1) BU(1) have "t:(AU\<rtr>s)\<sad>AU" "t:(BU\<rtr>s)\<sad>BU" using interval_add(4) func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup]]
          by auto
        with z(1-3) have "z:{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(AU\<rtr>s)\<sad>AU}" "z:{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(BU\<rtr>s)\<sad>BU}" by auto
      }
      then have "{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>((AU\<inter>BU)\<rtr>s)\<sad>(AU\<inter>BU)}\<subseteq>{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(AU\<rtr>s)\<sad>AU}\<inter>{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(BU\<rtr>s)\<sad>BU}" by auto
      with AU(2) BU(2) have "{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>((AU\<inter>BU)\<rtr>s)\<sad>(AU\<inter>BU)}\<subseteq>A\<inter>B" by blast
      ultimately show "A\<inter>B\<in>roelckeUniformity" using AU(3) BU(3) unfolding roelckeUniformity_def by blast
    }
    {
      fix B C assume as:"B\<in>roelckeUniformity" "C\<subseteq>(G \<times> G)" "B \<subseteq> C"
      from as(1) obtain BU where BU:"BU\<in>\<N>\<^sub>0" "{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(BU\<rtr>s)\<sad>BU}\<subseteq>B" unfolding roelckeUniformity_def by blast
      from as(3) BU(2) have "{\<langle>s,t\<rangle>\<in>G\<times>G. t \<in>(BU\<rtr>s)\<sad>BU}\<subseteq>C" by auto
      then show "C \<in> roelckeUniformity" using as(2) BU(1) unfolding roelckeUniformity_def by auto
    }
  qed
qed

text\<open> The topology given by the roelcke uniformity is the original topology \<close>

lemma (in topgroup) top_generated_roelcke_uniformity:
  shows "UniformTopology(roelckeUniformity,G) = T" unfolding UniformTopology_def
proof-
  let ?M = "{\<langle>t, {V `` {t} . V \<in> roelckeUniformity}\<rangle> . t \<in> G}"
  from neigh_from_uniformity[OF roelcke_uniformity] have fun:"?M:G\<rightarrow>Pow(Pow(G))" unfolding IsNeighSystem_def by auto
  {
    fix U assume as:"U:{U \<in> Pow(G). \<forall>x\<in>U. U \<in> ?M`x}"
    {
      fix x assume x:"x\<in>U"
      with as have xg:"x\<in>G" by auto
      from x as have "U\<in>{\<langle>t, {V `` {t} . V \<in> roelckeUniformity}\<rangle> . t \<in> G} ` x" by auto
      with xg have "U\<in>{V `` {x} . V \<in> roelckeUniformity}" using apply_equality[of x "{V `` {x} . V \<in> roelckeUniformity}", OF _ fun] by auto
      then obtain V where V:"U=V``{x}" "V\<in>roelckeUniformity" by auto
      from V(2) obtain W where W:"W\<in> \<N>\<^sub>0" "{\<langle>s,t\<rangle>:G\<times>G. t:(W\<rtr>s)\<sad>W}\<subseteq>V" unfolding roelckeUniformity_def by auto
      from W(1) have WG:"W\<subseteq>G" by auto
      from W(2) have A:"{\<langle>s,t\<rangle>:G\<times>G. t:(W\<rtr>s)\<sad>W}``{x}\<subseteq>V``{x}" by auto
      from xg have "\<forall>q. q\<in>({\<langle>s,t\<rangle>:G\<times>G. t:(W\<rtr>s)\<sad>W}``{x}) \<longleftrightarrow> q:(W\<rtr>x)\<sad>W"
        using WG func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup xg], of W]
        interval_add(1)[of "W\<rtr>x" W] by auto
      then have B:"{\<langle>s,t\<rangle>:G\<times>G. t:(W\<rtr>s)\<sad>W}``{x} = (W\<rtr>x)\<sad>W" by force
      with A have "(W\<rtr>x)\<sad>W \<subseteq> V``{x}" by auto
      with V(1) have WU:"(W\<rtr>x)\<sad>W \<subseteq> U" by auto
      have "int(W)\<rtr>x \<subseteq> W\<rtr>x" using image_mono[of "RightTranslation(G,f,x)" "RightTranslation(G,f,x)", OF _
        Top_2_L1[of W]] by auto
      then have "(int(W)\<rtr>x)\<times>(int(W)) \<subseteq> (W\<rtr>x)\<times>W" using Top_2_L1[of W] by auto
      then have "f``((int(W)\<rtr>x)\<times>(int(W))) \<subseteq> f``((W\<rtr>x)\<times>W)" using image_mono[of f f "(int(W)\<rtr>x)\<times>(int(W))" "(W\<rtr>x)\<times>W"] by auto
      moreover have "\<langle>(int(W)\<rtr>x),(int(W))\<rangle>:Pow(G)\<times>Pow(G)" "\<langle>(W\<rtr>x),W\<rangle> :Pow(G)\<times>Pow(G)" using
        func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup xg], of W] WG
        func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup xg], of "int(W)"] Top_2_L2[of W] by auto
      then have "(int(W)\<rtr>x)\<sad>(int(W)) = f``((int(W)\<rtr>x)\<times>(int(W)))" "(W\<rtr>x)\<sad>W = f``((W\<rtr>x)\<times>W)" using
        apply_equality[OF _ lift_subsets_binop[OF group0.group_oper_assocA[OF group0_valid_in_tgroup]]]
        unfolding setadd_def Lift2Subsets_def by auto
      ultimately have "(int(W)\<rtr>x)\<sad>(int(W)) \<subseteq> (W\<rtr>x)\<sad>W" by auto
      with xg WG have "int(W\<rtr>x)\<sad>(int(W)) \<subseteq> (W\<rtr>x)\<sad>W" using trans_interior_2 by auto moreover
      {
        have "int(W\<rtr>x)\<sad>(int(W)) = (\<Union>t\<in>int(W\<rtr>x). t\<ltr>(int(W)))" using interval_add(3)
          Top_2_L2 by auto moreover
        have "!!t. t:int(W\<rtr>x) ==> t\<ltr>(int(W)) = int(t\<ltr>W)" using trans_interior[of _ W]
          WG func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup], of _ "int(W)"] Top_2_L2[of "W\<rtr>x"] by auto
        ultimately have "int(W\<rtr>x)\<sad>(int(W)) = (\<Union>t\<in>int(W\<rtr>x). int(t\<ltr>W))" by auto
        then have "int(W\<rtr>x)\<sad>(int(W)) : T" using Top_2_L2 union_open[OF topSpaceAssum] by auto
      } moreover
      have "x:int(W\<rtr>x)" using elem_in_int_trans_2[OF xg W(1)].
      then have "x\<ra>\<zero> : int(W\<rtr>x)\<sad>(int(W))" using W(1) elements_in_set_sum_inv[of "int(W\<rtr>x)" "int(W)" _ x \<zero>] Top_2_L2
        by auto
      then have "x:int(W\<rtr>x)\<sad>(int(W))" using group0.group0_2_L2[OF group0_valid_in_tgroup] xg by auto moreover
      note WU
      ultimately have "\<exists>Y\<in>T. x\<in>Y \<and> Y\<subseteq>U" by auto
    }
    then have "U\<in>T" using open_neigh_open by auto
  } 
  then have "{U \<in> Pow(G). \<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> roelckeUniformity}\<rangle> . t \<in> G} ` x} \<subseteq> T" by auto moreover
  {
    fix U assume op:"U:T"
    {
      fix x assume x:"x:U"
      with op have xg:"x:G" by auto
      have "(\<rm>x)\<ltr>U : \<N>\<^sub>0" using open_trans_neigh op x by auto
      then obtain W where W:"W:\<N>\<^sub>0" "W \<sad> W \<subseteq>(\<rm>x)\<ltr>U" using exists_procls_zerohood by blast
      let ?V = "x\<ltr>(W\<rtr>(\<rm>x)) \<inter> W"
      from W(1) have WG:"W\<subseteq>G" by auto
      from xg have "int(x\<ltr>(W\<rtr>(\<rm>x))) = x\<ltr>int(W\<rtr>(\<rm>x))" using trans_interior
        func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup]]
        group0.inverse_in_group[OF group0_valid_in_tgroup] by auto
      with xg WG have "int(x\<ltr>(W\<rtr>(\<rm>x))) = x\<ltr>(int(W)\<rtr>(\<rm>x))" using trans_interior_2
        group0.inverse_in_group[OF group0_valid_in_tgroup] by auto
      moreover from W(1) have "\<zero>: int(W)" by auto
      then have "\<zero>\<ra>(\<rm>x) :int(W)\<rtr>(\<rm>x)" using elements_in_rtrans_inv[of "int(W)" "\<rm>x"]
        Top_2_L2[of W] group0.inverse_in_group[OF group0_valid_in_tgroup xg] by auto
      then have "(\<rm>x) :int(W)\<rtr>(\<rm>x)" using group0.group0_2_L2[OF group0_valid_in_tgroup]
        group0.inverse_in_group[OF group0_valid_in_tgroup xg] by auto
      with xg have "x\<ra>(\<rm>x) :x\<ltr>(int(W)\<rtr>(\<rm>x))" using elements_in_ltrans_inv[of "int(W)\<rtr>(\<rm>x)" "x"]
        func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup group0.inverse_in_group[OF group0_valid_in_tgroup]]]
        by auto
      with xg have "\<zero> : x\<ltr>(int(W)\<rtr>(\<rm>x))" using group0.group0_2_L6[OF group0_valid_in_tgroup] by auto
      ultimately have "\<zero> :int(x\<ltr>(W\<rtr>(\<rm>x)))" by auto
      with xg have xWx:"x\<ltr>(W\<rtr>(\<rm>x)) :\<N>\<^sub>0" using func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup]]
       func1_1_L6(2)[OF group0.group0_5_L1(2)[OF group0_valid_in_tgroup]] group0.inverse_in_group[OF group0_valid_in_tgroup]
       by auto
      from xWx W(1) have "\<zero>\<in>int(x\<ltr>(W\<rtr>(\<rm>x)))\<inter>int(W)" by auto
      moreover have int:"int(x\<ltr>(W\<rtr>(\<rm>x)))\<inter>int(W)\<in>T" using Top_2_L2
        using topSpaceAssum unfolding IsATopology_def by auto
      have "int(x\<ltr>(W\<rtr>(\<rm>x)))\<inter>int(W) \<subseteq> (x\<ltr>(W\<rtr>(\<rm>x)))\<inter>W" using Top_2_L1 by auto
      with int have "int(x\<ltr>(W\<rtr>(\<rm>x)))\<inter>int(W)\<subseteq>int((x\<ltr>(W\<rtr>(\<rm>x)))\<inter>W)" using Top_2_L5[of "int(x\<ltr>(W\<rtr>(\<rm>x)))\<inter>int(W)"]
        by auto moreover note xWx W(1)
      ultimately have V_NEIG:"?V: \<N>\<^sub>0" unfolding zerohoods_def by auto  
      {
        fix z assume z:"z:(?V\<rtr>x)\<sad>?V"
        from W(1) have VG:"?V \<subseteq> G" by auto
        then have VxG:"?V\<rtr>x \<subseteq> G" using func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup xg]] by auto
        from z VG VxG W(1) obtain a1 b1 where ab:"z=a1\<ra>b1" "a1:?V\<rtr>x" "b1:?V" using elements_in_set_sum[of "?V\<rtr>x" ?V z] by blast
        from ab(2) xg VG obtain c1 where c:"a1=c1\<ra>x" "c1:?V" using elements_in_rtrans by blast
        from ab(3) c(2) have bc:"b1:W" "c1:x\<ltr>(W\<rtr>(\<rm>x))" by auto
        from bc(2) xg W(1) obtain d where d:"c1=x\<ra>d" "d:W\<rtr>(\<rm>x)" using elements_in_ltrans[OF _ xg, of "W\<rtr>(\<rm>x)"] 
          func1_1_L6(2)[OF group0.group0_5_L1(1)[OF group0_valid_in_tgroup group0.inverse_in_group[OF group0_valid_in_tgroup]]] by auto
        from W(1) xg d(2) obtain e where e:"d=e\<ra>(\<rm>x)" "e:W" using elements_in_rtrans[of W "\<rm>x"] group0.inverse_in_group[OF group0_valid_in_tgroup]
          by auto
        from e(2) WG have eG:"e:G" by auto
        from e(1) d(1) have "c1=x\<ra>(e\<ra>(\<rm>x))" by auto
        with c(1) have "a1=(x\<ra>(e\<ra>(\<rm>x)))\<ra>x" by auto
        with xg eG have "a1=(x\<ra>e)\<ra>((\<rm>x)\<ra>x)" using 
          group0.group_oper_assoc[OF group0_valid_in_tgroup]
          group0.group_op_closed[OF group0_valid_in_tgroup]
          group0.inverse_in_group[OF group0_valid_in_tgroup] by auto
        then have "a1 = x\<ra>e" using group0.group0_2_L6[OF group0_valid_in_tgroup xg]
          group0.group0_2_L2[OF group0_valid_in_tgroup] group0.group_op_closed[OF group0_valid_in_tgroup xg eG]
          by auto
        with ab(1) have "z=(x\<ra>e)\<ra>b1" by auto moreover
        from ab(3) WG have bG:"b1:G" by auto
        ultimately have "z=x\<ra>(e\<ra>b1)" using group0.group_oper_assoc[OF group0_valid_in_tgroup xg eG, of b1] by auto moreover
        from e(2) ab(3) WG have "e\<ra>b1 :W\<sad>W" using elements_in_set_sum_inv by auto
        moreover note xg WG
        ultimately have "z:x\<ltr>(W\<sad>W)" using elements_in_ltrans_inv interval_add(1) by auto moreover
        from W(2) WG xg op have "x\<ltr>(W\<sad>W) \<subseteq> U" using trans_subset[of "W\<sad>W" x U] interval_add(1)[of W W] by auto
        ultimately have "z:U" by auto
      }
      then have sub:"(?V\<rtr>x)\<sad>?V \<subseteq> U" by auto moreover
      from V_NEIG have unif:"{\<langle>s,t\<rangle> \<in> G\<times>G. t : (?V\<rtr>s)\<sad>?V} : roelckeUniformity" unfolding roelckeUniformity_def by auto moreover
      from xg have "!!q. q:{\<langle>s,t\<rangle> \<in> G\<times>G. t : (?V\<rtr>s)\<sad>?V}``{x} <-> q:((?V\<rtr>x)\<sad>?V)\<inter>G" by auto
      then have "{\<langle>s,t\<rangle> \<in> G\<times>G. t : (?V\<rtr>s)\<sad>?V}``{x} = ((?V\<rtr>x)\<sad>?V)\<inter>G" by auto
      ultimately have basic:"{\<langle>s,t\<rangle> \<in> G\<times>G. t : (?V\<rtr>s)\<sad>?V}``{x} \<subseteq> U" using op by auto
      have add:"({x}\<times>U)``{x} =U" by auto
      from basic add have "({\<langle>s,t\<rangle> \<in> G\<times>G. t : (?V\<rtr>s)\<sad>?V}\<union>({x}\<times>U))``{x} = U" by auto
      moreover
      have R:"!!B C. B\<in>roelckeUniformity ==> C\<in>Pow(G \<times> G) ==> B \<subseteq> C ==> C \<in> roelckeUniformity" using roelcke_uniformity unfolding IsUniformity_def IsFilter_def by auto
      from op xg have GG:"({\<langle>s,t\<rangle> \<in> G\<times>G. t : (?V\<rtr>s)\<sad>?V}\<union>({x}\<times>U)):Pow(G\<times>G)" by auto
      have sub:"{\<langle>s,t\<rangle> \<in> G\<times>G. t : (?V\<rtr>s)\<sad>?V}\<subseteq>({\<langle>s,t\<rangle> \<in> G\<times>G. t : (?V\<rtr>s)\<sad>?V}\<union>({x}\<times>U))" by auto
      from R[OF unif GG] have "({\<langle>s,t\<rangle> \<in> G\<times>G. t : (?V\<rtr>s)\<sad>?V}\<union>({x}\<times>U)) : roelckeUniformity" by auto
      ultimately have "\<exists>V\<in>roelckeUniformity. V``{x} = U" by auto
      then have "U:{V `` {x} . V \<in> roelckeUniformity}" by auto
      with xg have "U \<in> {\<langle>t, {V `` {t} . V \<in> roelckeUniformity}\<rangle> . t \<in> G} ` x" using apply_equality[OF _ fun] by auto
    }
    then have "\<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> roelckeUniformity}\<rangle> . t \<in> G} ` x" by auto
    with op have "U:{U \<in> Pow(G). \<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> roelckeUniformity}\<rangle> . t \<in> G} ` x}" by auto
  }
  then have "T \<subseteq> {U \<in> Pow(G). \<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> roelckeUniformity}\<rangle> . t \<in> G} ` x}" by auto
  ultimately show "{U \<in> Pow(G). \<forall>x\<in>U. U \<in> {\<langle>t, {V `` {t} . V \<in> roelckeUniformity}\<rangle> . t \<in> G} ` x} = T" by auto
qed

end
