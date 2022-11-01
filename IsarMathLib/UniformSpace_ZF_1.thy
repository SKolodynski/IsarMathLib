(* 
    This file is a part of IsarMathLib - 
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2020 Daniel de la Concepcion

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

section \<open> More on uniform spaces \<close>

theory UniformSpace_ZF_1 imports func_ZF_1 UniformSpace_ZF Topology_ZF_2
begin

text\<open> This theory defines the maps to study in uniform spaces and proves their basic properties. \<close>

subsection\<open> Uniformly continuous functions \<close>

text\<open> Just as the the most general setting for continuity of functions is that of topological spaces, uniform spaces 
  are the most general setting for the study of uniform continuity. \<close>

text\<open> A map between 2 uniformities is uniformly continuous if it preserves
the entourages: \<close>

definition
  IsUniformlyCont ("_ {is uniformly continuous between} _ {and} _" 90) where
  "f:X->Y ==> \<Phi> {is a uniformity on}X  ==> \<Gamma> {is a uniformity on}Y  ==> 
  f {is uniformly continuous between} \<Phi> {and} \<Gamma> \<equiv> \<forall>V\<in>\<Gamma>. (ProdFunction(f,f)-``V)\<in>\<Phi>"

text\<open> Any uniformly continuous function is continuous when considering the topologies on the uniformities. \<close>

lemma uniformly_cont_is_cont:
  assumes "f:X->Y" "\<Phi> {is a uniformity on}X " "\<Gamma> {is a uniformity on}Y" 
    "f {is uniformly continuous between} \<Phi> {and} \<Gamma>"
  shows "IsContinuous(UniformTopology(\<Phi>,X),UniformTopology(\<Gamma>,Y),f)"
proof -
  {  fix U assume op: "U \<in> UniformTopology(\<Gamma>,Y)"
    have "f-``(U) \<in> UniformTopology(\<Phi>,X)"
    proof -
      from assms(1) have "f-``(U) \<subseteq> X" using func1_1_L3 by simp
      moreover 
      { fix x xa assume as:"\<langle>x,xa\<rangle> \<in> f" "xa \<in> U"
        with assms(1) have x:"x\<in>X" unfolding Pi_def by auto
        from as(2) op have U:"U \<in> {\<langle>t,{V``{t}.V\<in>\<Gamma>}\<rangle>.t\<in>Y}`(xa)" using uniftop_def_alt by auto
        from as(1) assms(1) have xa:"xa \<in> Y" unfolding Pi_def by auto
        have "{\<langle>t,{V``{t}.V\<in>\<Gamma>}\<rangle>.t\<in>Y} \<in> Pi(Y,%t. {{V``{t}.V\<in>\<Gamma>}})" unfolding Pi_def function_def 
          by auto
        with U xa have "U \<in>{V``{xa}.V\<in>\<Gamma>}" using apply_equality by auto
        then obtain V where V:"U = V``{xa}" "V\<in>\<Gamma>" by auto
        with assms have ent:"(ProdFunction(f,f)-``(V))\<in>\<Phi>" using IsUniformlyCont_def by simp
        have "\<forall>t. t \<in> (ProdFunction(f,f)-``V)``{x} <-> \<langle>x,t\<rangle> \<in> ProdFunction(f,f)-``(V)" 
          using image_def by auto
        with assms(1) x have "\<forall>t. t: (ProdFunction(f,f)-``V)``{x} \<longleftrightarrow> (t\<in>X \<and> \<langle>f`x,f`t\<rangle> \<in> V)" 
          using prodFunVimage by auto
        with assms(1) as(1) have "\<forall>t. t \<in> (ProdFunction(f,f)-``V)``{x} \<longleftrightarrow> (t\<in>X \<and> \<langle>xa,f`t\<rangle>: V)" 
          using apply_equality by auto
        with V(1) have "\<forall>t. t \<in> (ProdFunction(f,f)-``V)``{x} \<longleftrightarrow> (t\<in>X \<and> f`(t) \<in> U)" by auto
        with assms(1) U have "\<forall>t. t \<in> (ProdFunction(f,f)-``V)``{x} \<longleftrightarrow> t \<in> f-``U"
          using func1_1_L15 by simp
        hence "f-``U = (ProdFunction(f,f)-``V)``{x}" by blast
        with ent have "f-``(U) \<in> {V``{x} . V \<in> \<Phi>}" by auto 
        moreover
        have "{\<langle>t,{V``{t}.V\<in>\<Phi>}\<rangle>.t\<in>X} \<in> Pi(X,%t. {{V``{t}.V\<in>\<Phi>}})" unfolding Pi_def function_def 
          by auto
        ultimately have "f-``(U) \<in> {\<langle>t, {V `` {t} . V \<in> \<Phi>}\<rangle> . t \<in> X}`(x)" using x apply_equality 
          by auto
      } 
      ultimately show "f-``(U) \<in> UniformTopology(\<Phi>,X)" using uniftop_def_alt by auto
    qed
  } then show ?thesis unfolding IsContinuous_def by simp
qed

end
