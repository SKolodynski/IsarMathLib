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
  then obtain u v where uv:"u\<in>(L*\<^sup>\<Sigma>)" "v\<in>(L*\<^sup>\<Sigma>)" "x=Concat(u,v)" using concat_def lang by auto
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
  shows "((L*\<^sup>\<Sigma>)*\<^sup>\<Sigma>) = (L*\<^sup>\<Sigma>)"
proof
  from assms have II:"(L*\<^sup>\<Sigma>) {is a language with alphabet} \<Sigma>" using L_star_lang by auto
  from assms(1) II show "(L*\<^sup>\<Sigma>) \<subseteq> ((L*\<^sup>\<Sigma>)*\<^sup>\<Sigma>)" using L_in_L_star by auto
  have I:"(L*\<^sup>\<Sigma>) \<subseteq> (L*\<^sup>\<Sigma>)" by auto
  from assms have III:"0\<in> (L*\<^sup>\<Sigma>)" using empty_star by auto
  from assms have IV:"concat((L*\<^sup>\<Sigma>),(L*\<^sup>\<Sigma>)) \<subseteq> (L*\<^sup>\<Sigma>)" using concat_star by auto
  from I II III IV assms(1) show "((L*\<^sup>\<Sigma>)*\<^sup>\<Sigma>) \<subseteq> (L*\<^sup>\<Sigma>)" using star_minimal by auto
qed
   

definition start_eNFSA_states where
  "start_eNFSA_states(S) \<equiv> succ(S)"

definition start_eNFSA_trans where
  "Finite(\<Sigma>) \<Longrightarrow>
   (S,s0,t,F){is an DFSA for alphabet}\<Sigma> \<Longrightarrow>
   start_eNFSA_trans(S,s0,t,F,\<Sigma>) \<equiv>
     {\<langle>\<langle>s,\<sigma>\<rangle>,{t`\<langle>s,\<sigma>\<rangle>}\<rangle>. \<langle>s,\<sigma>\<rangle>\<in>S\<times>\<Sigma>} \<union> {\<langle>\<langle>S,\<Sigma>\<rangle>, F\<union>{s0}\<rangle>} 
   \<union> {\<langle>\<langle>f,\<Sigma>\<rangle>, {s0}\<rangle>. f\<in>F} \<union> {\<langle>\<langle>f,\<Sigma>\<rangle>, 0\<rangle>. f\<in>S-F} 
   \<union> {\<langle>\<langle>S,q\<rangle>, 0\<rangle>. q\<in>\<Sigma>}"

lemma start_eNFSA_valid:
  assumes fin:"Finite(\<Sigma>)"
  and A:"(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  shows "(start_eNFSA_states(S), S,
  start_eNFSA_trans(S,s0,t,F,\<Sigma>), F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
proof-
have Sfin:"Finite(S)"
    and s0S:"s0\<in>S"
    and FS:"F\<subseteq>S"
    and t:"t:S\<times>\<Sigma> \<rightarrow> S"
    using A unfolding DFSA_def[OF fin] by auto
  let ?SS = "start_eNFSA_states(S)"
  let ?tc = "start_eNFSA_trans(S,s0,t,F,\<Sigma>)"
  have finSuccS:"Finite(start_eNFSA_states(S))" using Finite_cons Sfin
    unfolding succ_def start_eNFSA_states_def by auto
  have s0SS:"S\<in>?SS" unfolding start_eNFSA_states_def by auto
  have FSS:"F \<subseteq> ?SS" unfolding start_eNFSA_states_def using FS by auto
  have tc_type:"?tc : ?SS\<times>succ(\<Sigma>) \<rightarrow> Pow(?SS)"
  proof-
    have ran:"?tc \<in> Pow((?SS\<times>succ(\<Sigma>))\<times>Pow(?SS))"
    proof-
      {
        fix m assume mt:"m\<in>?tc"
        then obtain x y where tt:"\<langle>x,y\<rangle> = m" using t unfolding Pi_def start_eNFSA_trans_def[OF fin A] by auto
        with mt have xy:"\<langle>x,y\<rangle>\<in>?tc" by auto
        have xy_dom:"x\<in>?SS\<times>succ(\<Sigma>)"
          using xy t FSS unfolding start_eNFSA_trans_def[OF fin A]
                             start_eNFSA_states_def Pi_def 
          by auto
        have xy_img:"y\<subseteq>?SS"
        proof-
          from xy consider
            (a) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S\<times>\<Sigma> \<and> x=\<langle>s,aa\<rangle> \<and> y={t`\<langle>s,aa\<rangle>}" |
            (b) "\<exists>s. s\<in>F \<and> x=\<langle>s,\<Sigma>\<rangle> \<and> y={s0}" |
            (c) "x=\<langle>S,\<Sigma>\<rangle> \<and> y=F\<union>{s0}" |
            (d) "\<exists>s. s\<in>S-F \<and> x=\<langle>s,\<Sigma>\<rangle> \<and> y=0" |
            (e) "\<exists>s. s\<in>\<Sigma> \<and> x=\<langle>S,s\<rangle> \<and> y=0"
            unfolding start_eNFSA_trans_def[OF fin A] by auto
          then show "y\<subseteq>?SS"
          proof cases
            case a
            then obtain s aa where sa:"\<langle>s,aa\<rangle>\<in>S\<times>\<Sigma>" "y={t`\<langle>s,aa\<rangle>}" by auto
            from sa(1) have "t`\<langle>s,aa\<rangle>\<in>S" using apply_type[OF t] by auto
            with sa(2) show ?thesis unfolding start_eNFSA_states_def by auto
          next
            case b
            then obtain s where sb:"s\<in>F" "y={s0}" by auto
            then show ?thesis using s0S unfolding start_eNFSA_states_def by auto
          next
            case c
            then have sa:"y=F\<union>{s0}" by auto
            then show ?thesis using FS s0S unfolding start_eNFSA_states_def by auto
          next
            case d
            then have sa:"y=0" by auto
            then show ?thesis by auto
          next
            case e
            then have "y=0" by auto
            then show ?thesis by auto
          qed
        qed
        from xy_dom xy_img have "\<langle>x,y\<rangle>\<in>(?SS\<times>succ(\<Sigma>))\<times>Pow(?SS)" by auto
        with tt have "m\<in>(?SS\<times>succ(\<Sigma>))\<times>Pow(?SS)" by auto
      }
      then show ?thesis by auto
    qed
    moreover have "function(?tc)"
    proof -
      {
        fix x y z
        assume h1:"\<langle>x,y\<rangle>\<in>?tc" and h2:"\<langle>x,z\<rangle>\<in>?tc"
        from h1 consider
            (a1) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S\<times>\<Sigma> \<and> x=\<langle>s,aa\<rangle> \<and> y={t`\<langle>s,aa\<rangle>}" |
            (b1) "\<exists>s. s\<in>F \<and> x=\<langle>s,\<Sigma>\<rangle> \<and> y={s0}" |
            (c1) "x=\<langle>S,\<Sigma>\<rangle> \<and> y=F\<union>{s0}" |
            (d1) "\<exists>s. s\<in>S-F \<and> x=\<langle>s,\<Sigma>\<rangle> \<and> y=0" |
            (e1) "\<exists>s. s\<in>\<Sigma> \<and> x=\<langle>S,s\<rangle> \<and> y=0"
          unfolding start_eNFSA_trans_def[OF fin A] by auto
        then have "y=z"
        proof cases
          case a1
          then obtain s aa where sa:"\<langle>s,aa\<rangle>\<in>S\<times>\<Sigma>" "x=\<langle>s,aa\<rangle>" "y={t`\<langle>s,aa\<rangle>}" by auto
          from h2 consider
            (a2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S\<times>\<Sigma> \<and> x=\<langle>s,aa\<rangle> \<and> z={t`\<langle>s,aa\<rangle>}" |
            (b2) "\<exists>s. s\<in>F \<and> x=\<langle>s,\<Sigma>\<rangle> \<and> z={s0}" |
            (c2) "x=\<langle>S,\<Sigma>\<rangle> \<and> z=F\<union>{s0}" |
            (d2) "\<exists>s. s\<in>S-F \<and> x=\<langle>s,\<Sigma>\<rangle> \<and> z=0" |
            (e2) "\<exists>s. s\<in>\<Sigma> \<and> x=\<langle>S,s\<rangle> \<and> z=0"
          unfolding start_eNFSA_trans_def[OF fin A] by auto
          then show ?thesis
          proof cases
            case a2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S\<times>\<Sigma>" "x=\<langle>p,q\<rangle>" "z={t`\<langle>p,q\<rangle>}" by auto
            from pq(2) sa(2) have "p=s" "q=aa" by auto
            with sa(3) pq(3) show ?thesis by auto
            next
            case b2
            then obtain p where pq:"p\<in>F" "x=\<langle>p,\<Sigma>\<rangle>" "z={s0}" by auto
            from pq(2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case c2
            then have pq:"x=\<langle>S,\<Sigma>\<rangle>" "z=F\<union>{s0}" by auto
            from pq(1) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case d2
            then obtain p where pq:"p\<in>S-F" "x=\<langle>p,\<Sigma>\<rangle>" "z=0" by auto
            from pq(1,2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
          next
            case e2
            then obtain s where "s\<in>\<Sigma>" "x=\<langle>S,s\<rangle>" by auto
            with sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
          qed
        next
          case b1
          then obtain s where sa:"s\<in>F" "x=\<langle>s,\<Sigma>\<rangle>" "y={s0}" by auto
          from h2 consider
            (a2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S\<times>\<Sigma> \<and> x=\<langle>s,aa\<rangle> \<and> z={t`\<langle>s,aa\<rangle>}" |
            (b2) "\<exists>s. s\<in>F \<and> x=\<langle>s,\<Sigma>\<rangle> \<and> z={s0}" |
            (c2) "x=\<langle>S,\<Sigma>\<rangle> \<and> z=F\<union>{s0}" |
            (d2) "\<exists>s. s\<in>S-F \<and> x=\<langle>s,\<Sigma>\<rangle> \<and> z=0" |
            (e2) "\<exists>s. s\<in>\<Sigma> \<and> x=\<langle>S,s\<rangle> \<and> z=0"
          unfolding start_eNFSA_trans_def[OF fin A] by auto
          then show ?thesis
          proof cases
            case a2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S\<times>\<Sigma>" "x=\<langle>p,q\<rangle>" "z={t`\<langle>p,q\<rangle>}" by auto
            from pq(1,2) sa(2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case b2
            then obtain p where pq:"p\<in>F" "x=\<langle>p,\<Sigma>\<rangle>" "z={s0}" by auto
            from pq(2) sa(1,2) have "p=s" by auto
            with sa(3) pq(3) show ?thesis by auto
            next
            case c2
            then have pq:"x=\<langle>S,\<Sigma>\<rangle>" "z=F\<union>{s0}" by auto
            from FS sa(1) have "s\<in>S" by auto
            with pq(1) sa(2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case d2
            then obtain p where pq:"p\<in>S-F" "x=\<langle>p,\<Sigma>\<rangle>" "z=0" by auto
            from pq(1,2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case e2
            then obtain p where pq:"p\<in>\<Sigma>" "x=\<langle>S,p\<rangle>" "z=0" by auto
            from pq(1,2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
          qed
        next
          case c1
          then have sa: "x=\<langle>S,\<Sigma>\<rangle>" "y=F\<union>{s0}" by auto
          from h2 consider
            (a2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S\<times>\<Sigma> \<and> x=\<langle>s,aa\<rangle> \<and> z={t`\<langle>s,aa\<rangle>}" |
            (b2) "\<exists>s. s\<in>F \<and> x=\<langle>s,\<Sigma>\<rangle> \<and> z={s0}" |
            (c2) "x=\<langle>S,\<Sigma>\<rangle> \<and> z=F\<union>{s0}" |
            (d2) "\<exists>s. s\<in>S-F \<and> x=\<langle>s,\<Sigma>\<rangle> \<and> z=0" |
            (e2) "\<exists>s. s\<in>\<Sigma> \<and> x=\<langle>S,s\<rangle> \<and> z=0"
          unfolding start_eNFSA_trans_def[OF fin A] by auto
          then show ?thesis
          proof cases
            case a2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S\<times>\<Sigma>" "x=\<langle>p,q\<rangle>" "z={t`\<langle>p,q\<rangle>}" by auto
            from pq(1,2) sa(1) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case b2
            then obtain p where pq:"p\<in>F" "x=\<langle>p,\<Sigma>\<rangle>" "z={s0}" by auto
            from pq(1) FS have "p:S" by auto
            with pq(2) sa(1) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case c2
            then have pq:"x=\<langle>S,\<Sigma>\<rangle>" "z=F\<union>{s0}" by auto
            with sa show ?thesis by auto
            next
            case d2
            then obtain p where pq:"p\<in>S-F" "x=\<langle>p,\<Sigma>\<rangle>" "z=0" by auto
            from pq(1,2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case e2
            then obtain p where pq:"p\<in>\<Sigma>" "x=\<langle>S,p\<rangle>" "z=0" by auto
            from pq(1,2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
          qed
        next
          case d1
          then obtain p where sa: "x=\<langle>p,\<Sigma>\<rangle>" "y=0" "p\<in>S-F" by auto
          from h2 consider
            (a2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S\<times>\<Sigma> \<and> x=\<langle>s,aa\<rangle> \<and> z={t`\<langle>s,aa\<rangle>}" |
            (b2) "\<exists>s. s\<in>F \<and> x=\<langle>s,\<Sigma>\<rangle> \<and> z={s0}" |
            (c2) "x=\<langle>S,\<Sigma>\<rangle> \<and> z=F\<union>{s0}" |
            (d2) "\<exists>s. s\<in>S-F \<and> x=\<langle>s,\<Sigma>\<rangle> \<and> z=0" |
            (e2) "\<exists>s. s\<in>\<Sigma> \<and> x=\<langle>S,s\<rangle> \<and> z=0"
          unfolding start_eNFSA_trans_def[OF fin A] by auto
          then show ?thesis
          proof cases
            case a2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S\<times>\<Sigma>" "x=\<langle>p,q\<rangle>" "z={t`\<langle>p,q\<rangle>}" by auto
            from pq(1,2) sa(1) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case b2
            then obtain q where pq:"q\<in>F" "x=\<langle>q,\<Sigma>\<rangle>" "z={s0}" by auto
            from pq(1,2) sa(1,3) have False by auto
            then show ?thesis by auto
            next
            case c2
            then have pq:"x=\<langle>S,\<Sigma>\<rangle>" "z=F\<union>{s0}" by auto
            from sa(1) pq(1) have "p=S" by auto
            with sa(3) have False using mem_irrefl by auto
            with sa show ?thesis by auto
            next
            case d2
            then obtain q where pq:"q\<in>S-F" "x=\<langle>q,\<Sigma>\<rangle>" "z=0" by auto
            from sa(2) pq(3) show ?thesis by auto
            next
            case e2
            then obtain p where pq:"p\<in>\<Sigma>" "x=\<langle>S,p\<rangle>" "z=0" by auto
            from pq(1,2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
          qed
        next
          case e1
          then obtain p where sa:"p:\<Sigma>" "x=\<langle>S,p\<rangle>" "y=0" by auto
          from h2 consider
            (a2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S\<times>\<Sigma> \<and> x=\<langle>s,aa\<rangle> \<and> z={t`\<langle>s,aa\<rangle>}" |
            (b2) "\<exists>s. s\<in>F \<and> x=\<langle>s,\<Sigma>\<rangle> \<and> z={s0}" |
            (c2) "x=\<langle>S,\<Sigma>\<rangle> \<and> z=F\<union>{s0}" |
            (d2) "\<exists>s. s\<in>S-F \<and> x=\<langle>s,\<Sigma>\<rangle> \<and> z=0" |
            (e2) "\<exists>s. s\<in>\<Sigma> \<and> x=\<langle>S,s\<rangle> \<and> z=0"
          unfolding start_eNFSA_trans_def[OF fin A] by auto
          then show ?thesis
          proof cases
            case a2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S\<times>\<Sigma>" "x=\<langle>p,q\<rangle>" "z={t`\<langle>p,q\<rangle>}" by auto
            from pq(1,2) sa(2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case b2
            then obtain q where pq:"q\<in>F" "x=\<langle>q,\<Sigma>\<rangle>" "z={s0}" by auto
            from pq(1,2) sa(1,2) have False  using mem_irrefl by auto
            then show ?thesis by auto
            next
            case c2
            then have pq:"x=\<langle>S,\<Sigma>\<rangle>" "z=F\<union>{s0}" by auto
            with sa(1,2) have False using mem_irrefl by auto
            with sa show ?thesis by auto
            next
            case d2
            then obtain q where pq:"q\<in>S-F" "x=\<langle>q,\<Sigma>\<rangle>" "z=0" by auto
            from sa(3) pq(3) show ?thesis by auto
            next
            case e2
            then obtain p where pq:"p\<in>\<Sigma>" "x=\<langle>S,p\<rangle>" "z=0" by auto
            from sa(3) pq(3) show ?thesis by auto
          qed
        qed
      }
      then show ?thesis unfolding function_def by auto
    qed
    moreover have "?SS\<times>succ(\<Sigma>) \<subseteq> domain(?tc)"
    proof
      fix x assume hx:"x\<in>?SS\<times>succ(\<Sigma>)"
      then obtain p aa where pa:"p\<in>?SS" "aa\<in>succ(\<Sigma>)" "x=\<langle>p,aa\<rangle>" by auto
      from pa(1) have ps:"p:S\<or> p=S"
        unfolding start_eNFSA_states_def by auto
      from pa(2) have acase:"aa\<in>\<Sigma> \<or> aa=\<Sigma>" using succ_iff by auto
      from ps show "x\<in>domain(?tc)"
      proof (elim disjE conjE)
        assume hs1:"p\<in>S"
        from acase show ?thesis
        proof (elim disjE)
          assume "aa\<in>\<Sigma>"
          with hs1 pa(3) have "\<langle>x,{t`\<langle>p,aa\<rangle>}\<rangle>\<in>?tc"
            unfolding start_eNFSA_trans_def[OF fin A] by auto
          then show ?thesis unfolding domain_def by auto
        next
          assume as:"aa=\<Sigma>"
          {
            assume "p\<in>F"
            with pa(3) as have "\<langle>x,{s0}\<rangle>\<in>?tc"
              unfolding start_eNFSA_trans_def[OF fin A] by auto
            then have ?thesis unfolding domain_def by auto
          } moreover
          {
            assume "p\<notin>F"
            with hs1 have "p\<in>S-F" by auto
            with pa(3) as have "\<langle>x,0\<rangle>\<in>?tc"
              unfolding start_eNFSA_trans_def[OF fin A] by auto
            then have ?thesis unfolding domain_def by auto
          } ultimately
          show ?thesis by auto
        qed
      next
        assume hs2:"p=S"
        from acase show ?thesis
        proof (elim disjE)
          assume "aa\<in>\<Sigma>"
          with hs2 pa(3) have "\<langle>x,0\<rangle>\<in>?tc"
            unfolding start_eNFSA_trans_def[OF fin A] by auto
          then show ?thesis unfolding domain_def by auto
        next
          assume "aa=\<Sigma>"
          with hs2 pa(3) have "\<langle>x,F\<union>{s0}\<rangle>\<in>?tc"
            unfolding start_eNFSA_trans_def[OF fin A] by auto
          then show ?thesis unfolding domain_def by auto
        qed
      qed
    qed
    ultimately show ?thesis unfolding Pi_def by auto
  qed
  show ?thesis unfolding FullNFSA_def[OF fin]
    using tc_type finSuccS FSS s0SS by auto 
qed

subsection\<open>Computing epsilon-closure for start_eNFSA\<close>

text\<open>Using the general epsilon-closure lemmas, we compute what epsilon-closure
looks like for the specific state sets in start_eNFSA.\<close>

lemma epsilon_cl_F_in_cl_S:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  shows "\<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {S}) = F\<union>{S,s0}"
proof
  {
    fix y assume "y\<in>F\<union>{S,s0}"
    {
      assume "y=S"
      then have "y\<in>\<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {S})"
        using
  from assms(2) have "F\<subseteq>S" using DFSA_def[OF assms(1)] by auto
  then have "F \<subseteq> start_eNFSA_states(S)" unfolding start_eNFSA_states_def by auto
  have valid:"(start_eNFSA_states(S), S, start_eNFSA_trans(S,s0,t,F,\<Sigma>), F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using start_eNFSA_valid[OF assms(1,2)] by auto
  have S_in_states:"S \<in> start_eNFSA_states(S)" unfolding start_eNFSA_states_def by auto
  from epsilon_cl_refl_sub[OF assms(1) valid, of "{S}"] S_in_states
    have "{S} \<subseteq> \<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {S})" by auto
  then show ?thesis
    sorry
qed

lemma epsilon_cl_s0_result:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>" "s0\<notin>F"
  shows "\<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {s0}) = {s0}"
proof-
  from assms(2) have s:"s0\<in>S" using DFSA_def[OF assms(1)] by auto
  have valid:"(start_eNFSA_states(S), S, start_eNFSA_trans(S,s0,t,F,\<Sigma>), F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using start_eNFSA_valid[OF assms(1,2)] by auto
  from s have "{s0} \<subseteq> start_eNFSA_states(S)" unfolding start_eNFSA_states_def  by auto
  from epsilon_cl_refl_sub[OF assms(1) valid] `{s0} \<subseteq> start_eNFSA_states(S)`
    have "{s0} \<subseteq> \<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {s0})" by auto
  then show ?thesis
    sorry
qed

lemma epsilon_cl_from_accepting_state:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>" "f\<in>F"
  shows "s0 \<in> \<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {f})"
proof-
  from assms(2,3) have f:"f\<in>S" using DFSA_def[OF assms(1)] by auto
  from assms(2) have "s0\<in>S" using DFSA_def[OF assms(1)] by auto
  have valid:"(start_eNFSA_states(S), S, start_eNFSA_trans(S,s0,t,F,\<Sigma>), F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using start_eNFSA_valid[OF assms(1,2)] by auto
  from f have "{f} \<subseteq> start_eNFSA_states(S)" unfolding start_eNFSA_states_def by auto
  then show ?thesis
    sorry
qed

lemma epsilon_cl_S_accepts:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>" "F \<noteq> 0"
  shows "\<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {S}) \<inter> F \<noteq> 0"
proof-
  from epsilon_cl_F_in_cl_S[OF assms(1,2)]
    have "F \<subseteq> \<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {S})" by auto
  with assms(3) show ?thesis by auto
qed

lemma eNFSA_lang_is_language:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  shows "{w \<in> Lists(\<Sigma>). w <-\<epsilon>-N (start_eNFSA_states(S), S,
  start_eNFSA_trans(S,s0,t,F,\<Sigma>), F){in alphabet}\<Sigma>}
         {is a language with alphabet}\<Sigma>"
proof-
  have "{w \<in> Lists(\<Sigma>). w <-\<epsilon>-N (start_eNFSA_states(S), S,
  start_eNFSA_trans(S,s0,t,F,\<Sigma>), F){in alphabet}\<Sigma>} \<subseteq> Lists(\<Sigma>)"
    by (auto simp: Collect_subset)
  thus "{w \<in> Lists(\<Sigma>). w <-\<epsilon>-N (start_eNFSA_states(S), S,
  start_eNFSA_trans(S,s0,t,F,\<Sigma>), F){in alphabet}\<Sigma>}
        {is a language with alphabet}\<Sigma>"
    using assms(1) IsALanguage_def by simp
qed

lemma L_subset_eNFSA_lang:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  shows "{w \<in> Lists(\<Sigma>). w <-D (S,s0,t,F){in alphabet}\<Sigma>}
         \<subseteq> {w \<in> Lists(\<Sigma>). w <-\<epsilon>-N (start_eNFSA_states(S), S,
                                start_eNFSA_trans(S,s0,t,F,\<Sigma>), F){in alphabet}\<Sigma>}"
proof
  fix w assume w_in_L:"w \<in> {w \<in> Lists(\<Sigma>). w <-D (S,s0,t,F){in alphabet}\<Sigma>}"
  then have w_type:"w \<in> Lists(\<Sigma>)" "w <-D (S,s0,t,F){in alphabet}\<Sigma>" by auto
  from assms(2) have DFSA_props:"Finite(S)" "s0\<in>S" "F\<subseteq>S" "t:S\<times>\<Sigma> \<rightarrow> S"
    using DFSA_def[OF assms(1)] by auto
  have valid_eNFSA:"(start_eNFSA_states(S), S, start_eNFSA_trans(S,s0,t,F,\<Sigma>), F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using start_eNFSA_valid[OF assms(1,2)] by auto
  show "w \<in> {w \<in> Lists(\<Sigma>). w <-\<epsilon>-N (start_eNFSA_states(S), S,
    start_eNFSA_trans(S,s0,t,F,\<Sigma>), F){in alphabet}\<Sigma>}"
  proof
    show "w \<in> Lists(\<Sigma>)" using w_type(1) by auto
    show "w <-\<epsilon>-N (start_eNFSA_states(S), S, start_eNFSA_trans(S,s0,t,F,\<Sigma>), F){in alphabet}\<Sigma>"
    proof-
      from w_type(2) w_type(1) have "\<exists>q\<in>F. \<langle>\<langle>w,s0\<rangle>,\<langle>0,q\<rangle>\<rangle> \<in> ({reduce D-relation}(S,t){in alphabet}\<Sigma>)^* \<or> (w = 0 \<and> s0\<in>F)"
        using DFSASatisfy_def[OF assms(1) assms(2) w_type(1)] by auto
      then show ?thesis
        unfolding FullNFSASatisfy_def[OF assms(1) valid_eNFSA w_type(1)]
        sorry
    qed
  qed
qed


end
