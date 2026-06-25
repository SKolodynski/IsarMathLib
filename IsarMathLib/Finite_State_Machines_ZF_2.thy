(*
    This file is a part of IsarMathLib -
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2026 Daniel de la Concepcion

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

section \<open>Kleene's Star\<close>

theory Finite_State_Machines_ZF_2 imports Finite_State_Machines_ZF_1

begin

definition R_lang
  where "Finite(\<Sigma>) \<Longrightarrow> L {is a language with alphabet}\<Sigma> \<Longrightarrow> R_lang(L,\<Sigma>) ={\<langle>v,w\<rangle>\<in>Lists(\<Sigma>)\<times>Lists(\<Sigma>). \<exists>x\<in>L\<union>{0}. w = Concat(x,v)}"

definition star ("_*\<^sup>_" 90)       
  where "Finite(\<Sigma>) \<Longrightarrow> L {is a language with alphabet}\<Sigma> \<Longrightarrow> L*\<^sup>\<Sigma> \<equiv> {v\<in>Lists(\<Sigma>). \<langle>0,v\<rangle>\<in>R_lang(L,\<Sigma>)^*}"

lemma r_lang_refl:
  assumes "Finite(\<Sigma>)" "L {is a language with alphabet}\<Sigma>"
  shows "refl(Lists(\<Sigma>),R_lang(L,\<Sigma>))"
  unfolding refl_def
proof
  fix v assume v:"v\<in>Lists(\<Sigma>)"
  from v have "\<langle>v,v\<rangle>\<in>Lists(\<Sigma>)\<times>Lists(\<Sigma>)" by auto
  moreover have "v = Concat(0,v)" using concat_empty(2) v unfolding Lists_def by auto
  then have "\<exists>x\<in>L\<union>{0}. v = Concat(x,v)" by auto
  ultimately have "\<langle>v,v\<rangle> \<in> {\<langle>v,w\<rangle>\<in>Lists(\<Sigma>)\<times>Lists(\<Sigma>). \<exists>x\<in>L\<union>{0}. w = Concat(x,v)}" by auto
  then show "\<langle>v,v\<rangle> \<in> R_lang(L,\<Sigma>)" using R_lang_def assms(1,2) by auto
qed

lemma concat_r_lang:
  assumes "Finite(\<Sigma>)" "L {is a language with alphabet}\<Sigma>" "\<langle>u,v\<rangle>\<in>R_lang(L,\<Sigma>)" "w\<in>Lists(\<Sigma>)"
  shows "\<langle>Concat(u,w),Concat(v,w)\<rangle>\<in>R_lang(L,\<Sigma>)"
proof-
  from assms(1-3) have uv:"u\<in>Lists(\<Sigma>)" "v\<in>Lists(\<Sigma>)" using R_lang_def by auto
  then have I:"Concat(u,w)\<in>Lists(\<Sigma>)" "Concat(v,w)\<in>Lists(\<Sigma>)" using concat_type assms(4) by auto
  from assms(1-3) obtain x where x:"x\<in>L\<union>{0}" "Concat(x,u) = v" using R_lang_def by auto
  from x(2) have A:"Concat(Concat(x,u),w) = Concat(v,w)" by auto
  {
    assume as:"x=0"
    have "0:0\<rightarrow>\<Sigma>" unfolding Pi_def function_def by auto
    then have l0:"0\<in>Lists(\<Sigma>)" unfolding Lists_def by blast
    with as have "x\<in>Lists(\<Sigma>)" by auto
  }
  moreover
  {
    assume as:"x\<noteq>0"
    with x(1) have "x:L" by auto
    with assms(1,2) have "x\<in>Lists(\<Sigma>)" using IsALanguage_def by auto
  } ultimately
  have "x\<in>Lists(\<Sigma>)" by auto
  with uv(1) assms(4) have "Concat(Concat(x,u),w) =Concat(x,Concat(u,w)) " using concat_assoc_lists by auto
  with A have "Concat(v,w) = Concat(x,Concat(u,w))"  by auto
  with x(1) have "\<exists>x\<in>L\<union>{0}. Concat(v,w) = Concat(x,Concat(u,w))" by auto
  with I show ?thesis using R_lang_def assms(1,2) by auto
qed

lemma concat_r_lang_2:
  assumes "Finite(\<Sigma>)" "L {is a language with alphabet}\<Sigma>" "\<langle>u,v\<rangle>\<in>R_lang(L,\<Sigma>)^*" "w\<in>Lists(\<Sigma>)"
  shows "\<langle>Concat(u,w),Concat(v,w)\<rangle>\<in>R_lang(L,\<Sigma>)^*"
proof-
  from assms(3) show ?thesis
  proof(rule rtrancl_induct)
    have "field(R_lang(L,\<Sigma>)^*) = field(R_lang(L,\<Sigma>))" using rtrancl_field by auto
    then have "field(R_lang(L,\<Sigma>)^*) \<subseteq> Lists(\<Sigma>)" using R_lang_def assms(1,2) unfolding field_def by auto
    then have u:"u\<in>Lists(\<Sigma>)" using assms(3) by auto
    with assms(4) have "Concat(u,w)\<in>Lists(\<Sigma>)" using concat_type by auto
    then show "\<langle>Concat(u,w),Concat(u,w)\<rangle>\<in>R_lang(L,\<Sigma>)^*"
      using r_into_rtrancl r_lang_refl assms(1,2) unfolding refl_def by auto
  next
    fix y z assume as:"\<langle>u,y\<rangle>\<in>R_lang(L,\<Sigma>)^*"
      "\<langle>y, z\<rangle> \<in> R_lang(L, \<Sigma>)" "\<langle>Concat(u, w), Concat(y, w)\<rangle> \<in> R_lang(L, \<Sigma>)^*"
    from as(2) assms(1,2,4) have "\<langle>Concat(y,w),Concat(z,w)\<rangle>\<in>R_lang(L,\<Sigma>)"
      using concat_r_lang by auto
    with as(3) show "\<langle>Concat(u,w),Concat(z,w)\<rangle>\<in>R_lang(L,\<Sigma>)^*"
      using rtrancl_into_rtrancl by auto
  qed
qed


lemma r_lang_L:
  assumes "Finite(\<Sigma>)" "L {is a language with alphabet}\<Sigma>" "v\<in>L"
  shows "\<langle>0,v\<rangle>\<in>R_lang(L,\<Sigma>)"
proof-
  have "0:0\<rightarrow>\<Sigma>" unfolding Pi_def function_def by auto
  then have l0:"0\<in>Lists(\<Sigma>)" unfolding Lists_def by blast
  moreover from assms have v:"v\<in>Lists(\<Sigma>)" using IsALanguage_def by auto
  ultimately have "\<langle>0,v\<rangle>\<in>Lists(\<Sigma>)\<times>Lists(\<Sigma>)" by auto
  moreover have "v = Concat(v,0)" using concat_empty(1) v unfolding Lists_def by auto
  with assms(3) have "\<exists>x\<in>L. v = Concat(x,0)" by auto
  ultimately have "\<langle>0,v\<rangle> \<in> {\<langle>v,w\<rangle>\<in>Lists(\<Sigma>)\<times>Lists(\<Sigma>). \<exists>x\<in>L\<union>{0}. w = Concat(x,v)}" by auto
  then show "\<langle>0,v\<rangle> \<in> R_lang(L,\<Sigma>)" using R_lang_def assms(1,2) by auto
qed

corollary L_star_lang:
  assumes "Finite(\<Sigma>)" "L {is a language with alphabet}\<Sigma>"
  shows "(L*\<^sup>\<Sigma>) {is a language with alphabet}\<Sigma>"
  using star_def IsALanguage_def assms by auto

corollary L_in_L_star:
  assumes "Finite(\<Sigma>)" "L {is a language with alphabet}\<Sigma>"
  shows "L \<subseteq> (L*\<^sup>\<Sigma>)"
proof
  fix x assume "x\<in>L"
  with assms have "\<langle>0,x\<rangle>\<in>R_lang(L,\<Sigma>)" using r_lang_L by auto
  then have "\<langle>0,x\<rangle>\<in>R_lang(L,\<Sigma>)^*" using r_into_rtrancl by auto moreover
  from `x\<in>L` have "x\<in>Lists(\<Sigma>)" using assms IsALanguage_def by auto
  ultimately show "x\<in>(L*\<^sup>\<Sigma>)" using star_def assms by auto
qed

lemma empty_star:
  assumes "Finite(\<Sigma>)" "L {is a language with alphabet} \<Sigma>"
  shows "0\<in>(L*\<^sup>\<Sigma>)"
proof-
  have "0:0\<rightarrow>\<Sigma>" unfolding Pi_def function_def by auto
  then have l0:"0\<in>Lists(\<Sigma>)" unfolding Lists_def by blast
  then have "\<langle>0,0\<rangle>\<in>R_lang(L,\<Sigma>)" using r_lang_refl assms unfolding refl_def by auto
  then have "\<langle>0,0\<rangle>\<in>R_lang(L,\<Sigma>)^*" using r_into_rtrancl by auto 
  with l0 have "0\<in> {v\<in>Lists(\<Sigma>). \<langle>0,v\<rangle>\<in>R_lang(L,\<Sigma>)^*}" by auto moreover
  have "(L*\<^sup>\<Sigma>) = {v\<in>Lists(\<Sigma>). \<langle>0,v\<rangle>\<in>R_lang(L,\<Sigma>)^*}" using star_def
    assms by auto ultimately
  show ?thesis by auto
qed

lemma concat_star:
  assumes "Finite(\<Sigma>)" "L {is a language with alphabet} \<Sigma>"
  shows "concat(L*\<^sup>\<Sigma>,L*\<^sup>\<Sigma>)\<subseteq>(L*\<^sup>\<Sigma>)"
proof
  have lang:"(L*\<^sup>\<Sigma>) {is a language with alphabet}\<Sigma>" using assms L_star_lang by auto
  fix x assume "x\<in>concat(L*\<^sup>\<Sigma>,L*\<^sup>\<Sigma>)"
  then obtain u v where uv:"u\<in>L*\<^sup>\<Sigma>" "v\<in>L*\<^sup>\<Sigma>" "x=Concat(u,v)" using concat_def lang by auto
  from uv(2) have vv:"\<langle>0,v\<rangle>\<in>R_lang(L,\<Sigma>)^*" using star_def assms by auto
  have v:"v\<in>Lists(\<Sigma>)" using uv(2) L_star_lang assms IsALanguage_def by auto
  from uv(1) have uu:"\<langle>0,u\<rangle>\<in>R_lang(L,\<Sigma>)^*" using star_def assms by auto
  with v have "\<langle>Concat(0,v),Concat(u,v)\<rangle>\<in>R_lang(L,\<Sigma>)^*" using concat_r_lang_2 assms by auto
  moreover have "Concat(0,v) = v" using v concat_empty(2) unfolding Lists_def by auto
  ultimately have "\<langle>v,Concat(u,v)\<rangle>\<in>R_lang(L,\<Sigma>)^*" by auto
  with uv(3) have "\<langle>v,x\<rangle>\<in>R_lang(L,\<Sigma>)^*" by auto
  with vv have I:"\<langle>0,x\<rangle>\<in>R_lang(L,\<Sigma>)^*" using trans_rtrancl unfolding trans_def by auto
  have u:"u\<in>Lists(\<Sigma>)" using uv(1) L_star_lang assms IsALanguage_def by auto
  with v have "Concat(u,v)\<in>Lists(\<Sigma>)" using concat_type by auto
  with uv(3) have "x\<in>Lists(\<Sigma>)" by auto
  with I show "x\<in>(L*\<^sup>\<Sigma>)" using star_def assms by auto
qed
    
  
lemma star_minimal:
  assumes "Finite(\<Sigma>)" "L {is a language with alphabet} \<Sigma>"
  and "L \<subseteq> M" "M {is a language with alphabet} \<Sigma>" "0\<in>M" "concat(M,M) \<subseteq> M"
  shows "(L*\<^sup>\<Sigma>) \<subseteq> M"
proof
  have lang:"(L*\<^sup>\<Sigma>) {is a language with alphabet}\<Sigma>" using assms L_star_lang by auto
  fix x assume x:"x\<in>(L*\<^sup>\<Sigma>)"
  show "x\<in>M"
  proof (rule rtrancl_induct[where P="\<lambda>x. x\<in>M"])
    from assms(5) show "0\<in>M" by auto
    from x have x:"x\<in>Lists(\<Sigma>)" "\<langle>0,x\<rangle>\<in>R_lang(L,\<Sigma>)^*" using star_def assms(1,2) by auto
    from x(2) show "\<langle>0,x\<rangle>\<in>R_lang(L,\<Sigma>)^*" by auto
    fix y z assume as:"\<langle>0,y\<rangle>:R_lang(L,\<Sigma>)^*" "\<langle>y,z\<rangle>\<in>R_lang(L,\<Sigma>)" "y\<in>M"
    from as(2) obtain q where q:"z=Concat(q,y)" "q\<in>L\<union>{0}" "y\<in>Lists(\<Sigma>)" "z\<in>Lists(\<Sigma>)" using R_lang_def assms(1,2) by auto
    {
      assume "q=0"
      then have "Concat(q,y) = Concat(0,y)" by auto
      then have "Concat(q,y) = y" using concat_empty(2) q(3)
        unfolding Lists_def by auto
      with q(1) have "z=y" by auto
      with as(3) have "z\<in>M" by auto
    } moreover
    {
      assume "q\<noteq>0"
      with q(2) have "q:L" by auto
      with assms(3) have "q\<in>M" by auto
      with as(3) have "Concat(q,y)\<in>concat(M,M)" using concat_def assms(4) by auto
      with assms(6) have "Concat(q,y)\<in>M" by auto
      with q(1) have "z\<in>M" by auto
    }
    ultimately show "z:M" by auto
  qed
qed

corollary star_star_is_star:
  assumes "Finite(\<Sigma>)" "L {is a language with alphabet} \<Sigma>"
  shows "(L*\<^sup>\<Sigma>)*\<^sup>\<Sigma> = (L*\<^sup>\<Sigma>)"
proof
  from assms have II:"L*\<^sup>\<Sigma> {is a language with alphabet} \<Sigma>" using L_star_lang by auto
  from assms(1) II show "(L*\<^sup>\<Sigma>) \<subseteq> (L*\<^sup>\<Sigma>)*\<^sup>\<Sigma>" using L_in_L_star by auto
  have I:"L*\<^sup>\<Sigma> \<subseteq> (L*\<^sup>\<Sigma>)" by auto
  from assms have III:"0\<in> (L*\<^sup>\<Sigma>)" using empty_star by auto
  from assms have IV:"concat((L*\<^sup>\<Sigma>),(L*\<^sup>\<Sigma>)) \<subseteq> (L*\<^sup>\<Sigma>)" using concat_star by auto
  from I II III IV assms(1) show "(L*\<^sup>\<Sigma>)*\<^sup>\<Sigma> \<subseteq> (L*\<^sup>\<Sigma>)" using star_minimal by auto
qed
    
  

end
