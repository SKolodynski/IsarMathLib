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

text\<open>This theory defines the Kleene star $L^*$ of a language $L$ over a finite alphabet $\Sigma$
  and proves its basic properties, including that $L^*$ is the smallest language containing $L$
  and the empty word and closed under concatenation. We then construct an $\epsilon$-NFSA
  that is meant to recognize $L^*$ when $L$ is recognized by a DFSA.\<close>

subsection\<open>Definition and properties of the Kleene star\<close>

text\<open>The Kleene star of a language is defined by means of a relation on words. In this section
  we define that relation, define the star as the set of words reachable from the empty word
  by its reflexive-transitive closure, and show that the star is the smallest language that
  contains $L$, contains the empty word and is closed under concatenation.\<close>

text\<open>For a language $L$ over alphabet $\Sigma$ the relation $R_L$ relates a word $v$
  to every word of the form $x\cdot v$, where $x$ is either a word from $L$ or the empty word.\<close>

definition R_lang
  where "Finite(\<Sigma>) \<Longrightarrow> L {is a language with alphabet}\<Sigma> \<Longrightarrow> R_lang(L,\<Sigma>) ={\<langle>v,w\<rangle>\<in>Lists(\<Sigma>)\<times>Lists(\<Sigma>). \<exists>x\<in>L\<union>{0}. w = Concat(x,v)}"

text\<open>The Kleene star $L^*$ of a language $L$ consists of those words $v$ for which
  the pair $(\emptyset, v)$ is in the reflexive-transitive closure of $R_L$,
  i.e. words that can be built from the empty word by repeatedly prepending words from $L$.\<close>

definition star ("_*\<^sup>_" 90)       
  where "Finite(\<Sigma>) \<Longrightarrow> L {is a language with alphabet}\<Sigma> \<Longrightarrow> L*\<^sup>\<Sigma> \<equiv> {v\<in>Lists(\<Sigma>). \<langle>0,v\<rangle>\<in>R_lang(L,\<Sigma>)^*}"

text\<open>The relation $R_L$ is reflexive on the set of all words over $\Sigma$,
  because $v = \emptyset\cdot v$.\<close>

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

text\<open>The relation $R_L$ is preserved by appending a word on the right: if $u R_L v$
  then $u\cdot w\ R_L\ v\cdot w$. This follows from associativity of concatenation.\<close>

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

text\<open>Appending a word on the right is also preserved by the reflexive-transitive closure
  of $R_L$. The proof is by induction on the closure.\<close>

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


text\<open>Every word $v\in L$ is related to the empty word: $\emptyset\ R_L\ v$.\<close>

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

text\<open>The Kleene star of a language over $\Sigma$ is a language over $\Sigma$.\<close>

corollary L_star_lang:
  assumes "Finite(\<Sigma>)" "L {is a language with alphabet}\<Sigma>"
  shows "(L*\<^sup>\<Sigma>) {is a language with alphabet}\<Sigma>"
  using star_def IsALanguage_def assms by auto

text\<open>A language $L$ is contained in its Kleene star $L^*$.\<close>

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

text\<open>The empty word is in the Kleene star of any language.\<close>

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

text\<open>The Kleene star $L^*$ is closed under concatenation.\<close>

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
    
  
text\<open>Minimality of the Kleene star: if a language $M$ contains $L$ and the empty word
  and is closed under concatenation, then $L^*\subseteq M$.\<close>

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

text\<open>The Kleene star is idempotent: $(L^*)^* = L^*$.\<close>

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
   

subsection\<open>The automaton start_eNFSA\<close>

text\<open>Given a DFSA $(S,s_0,t,F)$ we build an $\epsilon$-NFSA that adds a new initial state
  (the set $S$ itself, as $succ(S) = S\cup\{S\}$) and $\epsilon$-transitions that restart the
  computation from $s_0$. The goal is to show that it recognizes the Kleene star of the
  language of the DFSA.\<close>

text\<open>The state set of start-eNFSA consists of the states of the DFSA and one new state, $S$.\<close>

definition start_eNFSA_states where
  "start_eNFSA_states(S) \<equiv> succ(S)"

text\<open>The transition function of start-eNFSA keeps the transitions of the DFSA, adds
  $\epsilon$-transitions (reading the extra symbol $\Sigma$) from the new state $S$ and from
  each accepting state to $s_0$, and makes all other $\epsilon$-transitions empty.\<close>

definition start_eNFSA_trans where
  "Finite(\<Sigma>) \<Longrightarrow>
   (S,s0,t,F){is an DFSA for alphabet}\<Sigma> \<Longrightarrow>
   start_eNFSA_trans(S,s0,t,F,\<Sigma>) \<equiv>
     {\<langle>\<langle>s,\<sigma>\<rangle>,{t`\<langle>s,\<sigma>\<rangle>}\<rangle>. \<langle>s,\<sigma>\<rangle>\<in>S\<times>\<Sigma>} 
\<union> {\<langle>\<langle>S,\<Sigma>\<rangle>, {s0}\<rangle>} 
   \<union> {\<langle>\<langle>f,\<Sigma>\<rangle>, {s0}\<rangle>. f\<in>F} 
\<union> {\<langle>\<langle>f,\<Sigma>\<rangle>, 0\<rangle>. f\<in>S-F} 
   \<union> {\<langle>\<langle>S,q\<rangle>, 0\<rangle>. q\<in>\<Sigma>}"

text\<open>If $(S,s_0,t,F)$ is a DFSA then start-eNFSA, with accepting states $F\cup\{S\}$,
  is an $\epsilon$-NFSA.\<close>

lemma start_eNFSA_valid:
  assumes fin:"Finite(\<Sigma>)"
  and A:"(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  shows "(start_eNFSA_states(S), S,
  start_eNFSA_trans(S,s0,t,F,\<Sigma>), F\<union>{S}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
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
            (c) "x=\<langle>S,\<Sigma>\<rangle> \<and> y={s0}" |
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
            then have sa:"y={s0}" by auto
            then show ?thesis using s0S unfolding start_eNFSA_states_def by auto
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
            (c1) "x=\<langle>S,\<Sigma>\<rangle> \<and> y={s0}" |
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
            (c2) "x=\<langle>S,\<Sigma>\<rangle> \<and> z={s0}" |
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
            then have pq:"x=\<langle>S,\<Sigma>\<rangle>" "z={s0}" by auto
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
            (c2) "x=\<langle>S,\<Sigma>\<rangle> \<and> z={s0}" |
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
            then have pq:"x=\<langle>S,\<Sigma>\<rangle>" "z={s0}" by auto
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
          then have sa: "x=\<langle>S,\<Sigma>\<rangle>" "y={s0}" by auto
          from h2 consider
            (a2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S\<times>\<Sigma> \<and> x=\<langle>s,aa\<rangle> \<and> z={t`\<langle>s,aa\<rangle>}" |
            (b2) "\<exists>s. s\<in>F \<and> x=\<langle>s,\<Sigma>\<rangle> \<and> z={s0}" |
            (c2) "x=\<langle>S,\<Sigma>\<rangle> \<and> z={s0}" |
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
            then have pq:"x=\<langle>S,\<Sigma>\<rangle>" "z={s0}" by auto
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
            (c2) "x=\<langle>S,\<Sigma>\<rangle> \<and> z={s0}" |
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
            then have pq:"x=\<langle>S,\<Sigma>\<rangle>" "z={s0}" by auto
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
            (c2) "x=\<langle>S,\<Sigma>\<rangle> \<and> z={s0}" |
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
            then have pq:"x=\<langle>S,\<Sigma>\<rangle>" "z={s0}" by auto
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
          with hs2 pa(3) have "\<langle>x,{s0}\<rangle>\<in>?tc"
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

text\<open>In this section we compute the $\epsilon$-transitions of start-eNFSA and the
  $\epsilon$-closures of the sets of states we need.\<close>

text\<open>The $\epsilon$-transition from the new state $S$ leads to $\{s_0\}$.\<close>

lemma epsilon_trans_fun_S:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  shows "start_eNFSA_trans(S,s0,t,F,\<Sigma>)`\<langle>S,\<Sigma>\<rangle> = {s0}"
proof-
  from assms have "(start_eNFSA_states(S),S,start_eNFSA_trans
               (S, s0, t, F, \<Sigma>),F\<union>{S}){is an \<epsilon>-NFSA for alphabet}\<Sigma>" using start_eNFSA_valid
    by auto
  then have f:"start_eNFSA_trans(S, s0, t, F, \<Sigma>):succ(S)\<times>succ(\<Sigma>)\<rightarrow>Pow(succ(S))"
    using FullNFSA_def[OF assms(1)] unfolding start_eNFSA_states_def by auto
  have "\<langle>\<langle>S,\<Sigma>\<rangle>,{s0}\<rangle>\<in>start_eNFSA_trans(S, s0, t, F, \<Sigma>)"
    using start_eNFSA_trans_def[OF assms] by auto
  with f show ?thesis using apply_equality by auto
qed

text\<open>The $\epsilon$-transition from an accepting state $u\in F$ leads to $\{s_0\}$.
  This is the restart that allows concatenating words.\<close>

lemma epsilon_trans_fun_F:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>" and "u\<in>F"
  shows "start_eNFSA_trans(S,s0,t,F,\<Sigma>)`\<langle>u,\<Sigma>\<rangle> = {s0}"
proof-
  from assms have "(start_eNFSA_states(S),S,start_eNFSA_trans
               (S, s0, t, F, \<Sigma>),F\<union>{S}){is an \<epsilon>-NFSA for alphabet}\<Sigma>" using start_eNFSA_valid
    by auto
  then have f:"start_eNFSA_trans(S, s0, t, F, \<Sigma>):succ(S)\<times>succ(\<Sigma>)\<rightarrow>Pow(succ(S))"
    using FullNFSA_def[OF assms(1)] unfolding start_eNFSA_states_def by auto
  have "\<langle>\<langle>u,\<Sigma>\<rangle>,{s0}\<rangle>\<in>start_eNFSA_trans(S, s0, t, F, \<Sigma>)"
    using start_eNFSA_trans_def[OF assms(1,2)] assms(3) by auto
  with f show ?thesis using apply_equality by auto
qed


text\<open>A non-accepting state $u\in S\setminus F$ has no $\epsilon$-transitions.\<close>

lemma epsilon_trans_fun_s:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>" and "u\<in>S-F"
  shows "start_eNFSA_trans(S,s0,t,F,\<Sigma>)`\<langle>u,\<Sigma>\<rangle> = 0"
proof-
  from assms have "(start_eNFSA_states(S),S,start_eNFSA_trans
               (S, s0, t, F, \<Sigma>),F\<union>{S}){is an \<epsilon>-NFSA for alphabet}\<Sigma>" using start_eNFSA_valid
    by auto
  then have f:"start_eNFSA_trans(S, s0, t, F, \<Sigma>):succ(S)\<times>succ(\<Sigma>)\<rightarrow>Pow(succ(S))"
    using FullNFSA_def[OF assms(1)] unfolding start_eNFSA_states_def by auto
  have "\<langle>\<langle>u,\<Sigma>\<rangle>,0\<rangle>\<in>start_eNFSA_trans(S, s0, t, F, \<Sigma>)"
    using start_eNFSA_trans_def[OF assms(1,2)] assms(3) by auto
  with f show ?thesis using apply_equality by auto
qed

text\<open>Using the general epsilon-closure lemmas, we compute what epsilon-closure
looks like for the specific state sets in start-eNFSA.\<close>

lemma epsilon_cl_F_in_cl_S:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  shows "\<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {S}) = {S,s0}"
proof
  let ?r = "{\<langle>Q,{s\<in>succ(S). \<exists>q\<in>Q. s \<in> start_eNFSA_trans(S,s0,t,F,\<Sigma>)`\<langle>q,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(succ(S))}"
  {
    fix y assume y:"y\<in>{S,s0}"
    let ?B="{s\<in>succ(S). \<exists>m\<in>{S}. s\<in>start_eNFSA_trans(S, s0, t, F, \<Sigma>)`\<langle>m,\<Sigma>\<rangle>}"
    {
      assume "y=S"
      then have "y\<in>\<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {S})"
        using epsilon_cl_refl_sub[OF assms(1) start_eNFSA_valid[OF assms]]
        unfolding start_eNFSA_states_def by auto
    } moreover
    {
      assume "y\<noteq>S"
      with y have "y\<in>{s0}" by auto moreover
      from this have "y\<in>S" using assms(2) DFSA_def[OF assms(1)] by auto
      then have "y\<in>succ(S)" by auto
      moreover
      have "?B = succ(S)\<inter>({s0})"
        using epsilon_trans_fun_S[OF assms] by auto
      ultimately have y:"y\<in>?B" by auto
      have "\<langle>{S},{s\<in>succ(S). \<exists>m\<in>{S}. s\<in>start_eNFSA_trans(S, s0, t, F, \<Sigma>)`\<langle>m,\<Sigma>\<rangle>}\<rangle>\<in>?r"  by auto
      then have "\<langle>{S},{s\<in>succ(S). \<exists>m\<in>{S}. s\<in>start_eNFSA_trans(S, s0, t, F, \<Sigma>)`\<langle>m,\<Sigma>\<rangle>}\<rangle>\<in>?r^*" 
        using r_into_rtrancl by auto
      moreover have "{S} \<subseteq> succ(S)" by auto
      ultimately have "{s\<in>succ(S). \<exists>m\<in>{S}. s\<in>start_eNFSA_trans(S, s0, t, F, \<Sigma>)`\<langle>m,\<Sigma>\<rangle>} \<subseteq> \<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {S})"
        using EpsilonClosure_def[OF assms(1) start_eNFSA_valid[OF assms], of "{S}"]
        unfolding start_eNFSA_states_def by force
      with y have "y\<in> \<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {S})"
        by auto
    } ultimately
    have "y\<in> \<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {S})"
      by auto
  }
  then show "{S,s0} \<subseteq> \<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {S})"
    by auto
  {
    fix y assume "y\<in>\<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {S})"
    then obtain P where P:"P\<in>Pow(succ(S))" "y\<in>P" "\<langle>{S},P\<rangle>\<in>({\<langle>Q,{s\<in>succ(S). \<exists>q\<in>Q. 
      s \<in> start_eNFSA_trans(S, s0, t, F, \<Sigma>)`\<langle>q,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(succ(S))}^*)"
      using EpsilonClosure_def[OF assms(1) start_eNFSA_valid[OF assms], of "{S}"]
      unfolding start_eNFSA_states_def by auto
    let ?r = "{\<langle>Q,{s\<in>succ(S). \<exists>q\<in>Q. s \<in> start_eNFSA_trans(S, s0, t, F, \<Sigma>)`\<langle>q,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(succ(S))}"
    {
      assume "\<langle>{S},P\<rangle>\<in>id(field(?r))"
      then have "P={S}" by auto
      with P(2) have "y:{S}" by auto
      then have "y = S" by auto
      then have "y\<in>{S,s0}" by auto
    } moreover
    {
      assume "\<langle>{S},P\<rangle>\<notin>id(field(?r))"
      moreover from P(3) have "\<langle>{S},P\<rangle>\<in>id(field(?r))\<union>(?r O ?r^*)" using rtrancl_unfold by auto
      ultimately have "\<langle>{S},P\<rangle>\<in>(?r O ?r^*)" by auto
      then obtain Q where q:"\<langle>{S},Q\<rangle>\<in>?r^*" "\<langle>Q,P\<rangle>\<in>?r" using compE by auto
      from q(2) have p:"P={s\<in>succ(S). \<exists>u\<in>Q. s\<in>start_eNFSA_trans(S,s0,t,F,\<Sigma>)`\<langle>u,\<Sigma>\<rangle>}" "Q\<in>Pow(succ(S))" by auto
      from P(2) p(1) obtain u where u:"u\<in>Q" "y\<in>start_eNFSA_trans(S,s0,t,F,\<Sigma>)`\<langle>u,\<Sigma>\<rangle>" by auto
      {
        assume "u=S"
        then have "start_eNFSA_trans(S,s0,t,F,\<Sigma>)`\<langle>u,\<Sigma>\<rangle> = {s0}"
          using epsilon_trans_fun_S[OF assms] by auto
        with u(2) have "y\<in>{s0}" by auto
        then have "y\<in>{S,s0}" by auto
      }
      moreover
      {
        assume "u\<noteq>S"
        with u(1) p(2) have uS:"u\<in>S" by auto
        {
          assume "u\<in>F"
          then have "start_eNFSA_trans(S,s0,t,F,\<Sigma>)`\<langle>u,\<Sigma>\<rangle> = {s0}"
            using epsilon_trans_fun_F[OF assms] by auto
          with u(2) have "y=s0" by auto
          then have "y\<in> {S,s0}" by auto
        } moreover
        {
          assume "u\<notin>F"
          then have "start_eNFSA_trans(S,s0,t,F,\<Sigma>)`\<langle>u,\<Sigma>\<rangle> = 0"
            using epsilon_trans_fun_s[OF assms] uS by auto
          with u(2) have "False" by auto
          then have "y\<in> {S,s0}" by auto
        } ultimately
        have "y\<in> {S,s0}" by auto
      }
      ultimately have "y\<in> {S,s0}" by auto
    }
    ultimately have "y\<in> {S,s0}" by auto
  }
  then show " \<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S, s0, t, F, \<Sigma>), \<Sigma>, {S}) \<subseteq>
   {S,s0}" by auto
qed

text\<open>The $\epsilon$-closure of a non-accepting state $q\in S\setminus F$ is just $\{q\}$.\<close>

lemma epsilon_cl_s0_result:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>" "q\<in>S-F"
  shows "\<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {q}) = {q}"
proof
  from assms(2) have s:"s0\<in>S" using DFSA_def[OF assms(1)] by auto
  have valid:"(start_eNFSA_states(S), S, start_eNFSA_trans(S,s0,t,F,\<Sigma>), F\<union>{S}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using start_eNFSA_valid[OF assms(1,2)] by auto
  from s have A:"{q} \<subseteq> start_eNFSA_states(S)" unfolding start_eNFSA_states_def using assms(3) by auto
  from epsilon_cl_refl_sub[OF assms(1) valid] `{q} \<subseteq> start_eNFSA_states(S)`
  show "{q} \<subseteq> \<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {q})" by auto
  {
    fix y assume y:"y\<in> \<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {q})"
    from A y obtain P where P:"P\<in>Pow(succ(S))" "y\<in>P" "\<langle>{q},P\<rangle>\<in>({\<langle>Q,{s\<in>succ(S). \<exists>q\<in>Q.
      s \<in> start_eNFSA_trans(S, s0, t, F, \<Sigma>)`\<langle>q,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(succ(S))}^*)"
      using EpsilonClosure_def[OF assms(1) start_eNFSA_valid[OF assms(1,2)], of "{q}"]
      unfolding start_eNFSA_states_def by auto
    let ?r = "{\<langle>Q,{s\<in>succ(S). \<exists>q\<in>Q. s \<in> start_eNFSA_trans(S, s0, t, F, \<Sigma>)`\<langle>q,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(succ(S))}"
    {
      assume "\<langle>{q},P\<rangle>\<in>id(field(?r))"
      then have "P={q}" by auto
      with P(2) have "y:{q}" by auto
      then have "y = q" by auto
      then have "y\<in>{q}" by auto
    } moreover
    {
      assume "\<langle>{q},P\<rangle>\<notin>id(field(?r))"
      moreover from P(3) have "\<langle>{q},P\<rangle>\<in>id(field(?r))\<union>(?r O ?r^*)" using rtrancl_unfold by auto
      ultimately have "\<langle>{q},P\<rangle>\<in>(?r O ?r^*)" by auto
      then obtain Q where q:"\<langle>{q},Q\<rangle>\<in>?r^*" "\<langle>Q,P\<rangle>\<in>?r" using compE by auto
      {
        fix x z assume as:"\<langle>{q},x\<rangle>\<in>?r^*"
          "\<langle>x,z\<rangle>\<in>?r" "x\<subseteq>{q}"
        {
          assume "x\<noteq>0"
          with as(3) have xq:"x={q}" by auto
          from as(2) have "z={s \<in> succ(S) .
          \<exists>q\<in>x. s \<in> start_eNFSA_trans(S, s0, t, F, \<Sigma>) ` \<langle>q, \<Sigma>\<rangle>}" by auto
          with xq have "z={s \<in> succ(S) .
          \<exists>q\<in>{q}. s \<in> start_eNFSA_trans(S, s0, t, F, \<Sigma>) ` \<langle>q, \<Sigma>\<rangle>}" by auto
          then have "z=succ(S)\<inter>(start_eNFSA_trans(S, s0, t, F, \<Sigma>) ` \<langle>q, \<Sigma>\<rangle>)" by auto
          then have "z=succ(S)\<inter>0" using epsilon_trans_fun_s[OF assms] by auto
          then have "z\<subseteq>{q}" by auto
        } moreover
        {
          assume "x=0"
          with as(2) have "z=0" by auto
          then have "z\<subseteq>{q}" by auto
        }
        ultimately have "z\<subseteq>{q}" by auto
      }  
      with rtrancl_induct[OF P(3), where P="\<lambda>t. t\<subseteq>{q}"]
      have "P\<subseteq>{q}" by auto
      with P(2) have "y=q" by auto
    } ultimately have "y\<in>{q}" by auto
  }
  then show " \<epsilon>-cl(start_eNFSA_states(S), start_eNFSA_trans(S,s0,t,F,\<Sigma>), \<Sigma>, {q})\<subseteq>{q}" by auto
qed

subsection\<open>start_eNFSA recognizes the Kleene star\<close>

text\<open>We show that the language accepted by start-eNFSA contains $L$ and the empty word,
  which are the first ingredients needed to apply minimality of the Kleene star.\<close>

text\<open>The set of words accepted by start-eNFSA is a language over $\Sigma$,
  as it is a subset of the set of all words over $\Sigma$.\<close>

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

text\<open>The empty word is accepted by start-eNFSA, because the $\epsilon$-closure of the
  initial state $S$ contains $S$, which is an accepting state.\<close>

lemma empty_in_eNFSA_lang:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  shows "0\<in> {w \<in> Lists(\<Sigma>). w <-\<epsilon>-N (start_eNFSA_states(S), S,
                                start_eNFSA_trans(S,s0,t,F,\<Sigma>), F\<union>{S}){in alphabet}\<Sigma>}"
proof
  show ol:"0\<in>Lists(\<Sigma>)" unfolding Lists_def Pi_def function_def by auto
  have "s0\<in>S" using assms(2) DFSA_def[OF assms(1)] by auto
  then have "\<epsilon>-cl(start_eNFSA_states(S),start_eNFSA_trans(S,s0,t,F,\<Sigma>),\<Sigma>,{S}) = {S,s0}"
    using epsilon_cl_F_in_cl_S assms by auto
  then show "0 <-\<epsilon>-N (start_eNFSA_states(S),S,start_eNFSA_trans(S, s0, t, F, \<Sigma>),F \<union> {S}){in alphabet}\<Sigma>"
    using FullNFSASatisfy_def[OF assms(1)] start_eNFSA_valid[OF assms] ol by auto
qed


text\<open>On a symbol of the alphabet, the transition function of start-eNFSA from a state of the DFSA
  agrees with the transition function of the DFSA.\<close>

lemma start_eNFSA_trans_symbol:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>" "u\<in>S" "\<sigma>\<in>\<Sigma>"
  shows "start_eNFSA_trans(S,s0,t,F,\<Sigma>)`\<langle>u,\<sigma>\<rangle> = {t`\<langle>u,\<sigma>\<rangle>}"
proof-
  from assms(1,2) have "(start_eNFSA_states(S),S,start_eNFSA_trans
               (S, s0, t, F, \<Sigma>),F\<union>{S}){is an \<epsilon>-NFSA for alphabet}\<Sigma>" using start_eNFSA_valid
    by auto
  then have f:"start_eNFSA_trans(S, s0, t, F, \<Sigma>):succ(S)\<times>succ(\<Sigma>)\<rightarrow>Pow(succ(S))"
    using FullNFSA_def[OF assms(1)] unfolding start_eNFSA_states_def by auto
  have "\<langle>\<langle>u,\<sigma>\<rangle>,{t`\<langle>u,\<sigma>\<rangle>}\<rangle>\<in>start_eNFSA_trans(S, s0, t, F, \<Sigma>)"
    using start_eNFSA_trans_def[OF assms(1,2)] assms(3,4) by auto
  with f show ?thesis using apply_equality by auto
qed

text\<open>On symbols of the alphabet there are no transitions from the new state $S$.\<close>

lemma start_eNFSA_trans_symbol_S:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>" "\<sigma>\<in>\<Sigma>"
  shows "start_eNFSA_trans(S,s0,t,F,\<Sigma>)`\<langle>S,\<sigma>\<rangle> = 0"
proof-
  from assms(1,2) have "(start_eNFSA_states(S),S,start_eNFSA_trans
               (S,s0,t,F,\<Sigma>),F\<union>{S}){is an \<epsilon>-NFSA for alphabet}\<Sigma>" using start_eNFSA_valid
    by auto
  then have f:"start_eNFSA_trans(S,s0,t,F,\<Sigma>):succ(S)\<times>succ(\<Sigma>)\<rightarrow>Pow(succ(S))"
    using FullNFSA_def[OF assms(1)] unfolding start_eNFSA_states_def by auto
  have "\<langle>\<langle>S,\<sigma>\<rangle>,0\<rangle>\<in>start_eNFSA_trans(S,s0,t,F,\<Sigma>)"
    using start_eNFSA_trans_def[OF assms(1,2)] assms(3) by auto
  with f show ?thesis using apply_equality by auto
qed

text\<open>On a symbol of the alphabet, start-eNFSA moves every state only to states of the DFSA.\<close>

lemma start_eNFSA_trans_symbol_sub:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>" "u\<in>succ(S)" "\<sigma>\<in>\<Sigma>"
  shows "start_eNFSA_trans(S,s0,t,F,\<Sigma>)`\<langle>u,\<sigma>\<rangle> \<subseteq> S"
proof-
  from assms(1,2) have tT:"t:S\<times>\<Sigma>\<rightarrow>S" using DFSA_def[OF assms(1)] by auto
  from assms(3) have "u=S \<or> u\<in>S" by auto
  then show ?thesis
  proof
    assume "u=S"
    then show ?thesis using start_eNFSA_trans_symbol_S assms(1,2,4) by auto
  next
    assume uS:"u\<in>S"
    then have "start_eNFSA_trans(S,s0,t,F,\<Sigma>)`\<langle>u,\<sigma>\<rangle> = {t`\<langle>u,\<sigma>\<rangle>}"
      using start_eNFSA_trans_symbol assms(1,2,4) by auto
    moreover from tT uS assms(4) have "t`\<langle>u,\<sigma>\<rangle>\<in>S" using apply_type by auto
    ultimately show ?thesis by auto
  qed
qed

text\<open>The $\epsilon$-closure of a set of states of start-eNFSA is a set of states of start-eNFSA.\<close>

lemma start_eNFSA_cl_subset:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>" "E\<subseteq>start_eNFSA_states(S)"
  shows "\<epsilon>-cl(start_eNFSA_states(S),start_eNFSA_trans(S,s0,t,F,\<Sigma>),\<Sigma>,E) \<subseteq> start_eNFSA_states(S)"
proof-
  have valid:"(start_eNFSA_states(S),S,start_eNFSA_trans(S,s0,t,F,\<Sigma>),F\<union>{S}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using start_eNFSA_valid[OF assms(1,2)] by auto
  show ?thesis using EpsilonClosure_def[OF assms(1) valid assms(3)] by auto
qed

text\<open>If $U$ is a set of states of the DFSA, then the $\epsilon$-closure of $U$ in start-eNFSA
  consists of the elements of $U$ and possibly of $s_0$, which is added only when $U$
  contains an accepting state of the DFSA.\<close>

lemma start_eNFSA_cl_upper:
  assumes fin:"Finite(\<Sigma>)" and A:"(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  and US:"U\<subseteq>S"
  and x:"x\<in>\<epsilon>-cl(start_eNFSA_states(S),start_eNFSA_trans(S,s0,t,F,\<Sigma>),\<Sigma>,U)"
  shows "x\<in>U \<or> (x=s0 \<and> U\<inter>F\<noteq>0)"
proof-
  let ?SS = "start_eNFSA_states(S)"
  let ?tc = "start_eNFSA_trans(S,s0,t,F,\<Sigma>)"
  have valid:"(?SS,S,?tc,F\<union>{S}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using start_eNFSA_valid[OF fin A] by auto
  from A have s0S:"s0\<in>S" using DFSA_def[OF fin] by auto
  have USS:"U\<subseteq>?SS" using US unfolding start_eNFSA_states_def by auto
  let ?r = "{\<langle>Q,{s\<in>?SS. \<exists>q\<in>Q. s\<in>?tc`\<langle>q,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(?SS)}"
  from x obtain P where P:"P\<in>Pow(?SS)" "x\<in>P" "\<langle>U,P\<rangle>\<in>?r^*"
    using EpsilonClosure_def[OF fin valid USS] by auto
  have inv:"P\<subseteq>U\<union>{s0} \<and> (s0\<in>P \<longrightarrow> s0\<in>U \<or> U\<inter>F\<noteq>0)"
  proof(rule rtrancl_induct[OF P(3), where P="\<lambda>y. y\<subseteq>U\<union>{s0} \<and> (s0\<in>y \<longrightarrow> s0\<in>U \<or> U\<inter>F\<noteq>0)"])
    show "U\<subseteq>U\<union>{s0} \<and> (s0\<in>U \<longrightarrow> s0\<in>U \<or> U\<inter>F\<noteq>0)" by auto
  next
    fix y z assume as:"\<langle>U,y\<rangle>\<in>?r^*" "\<langle>y,z\<rangle>\<in>?r"
      "y\<subseteq>U\<union>{s0} \<and> (s0\<in>y \<longrightarrow> s0\<in>U \<or> U\<inter>F\<noteq>0)"
    from as(2) have zdef:"z={s\<in>?SS. \<exists>q\<in>y. s\<in>?tc`\<langle>q,\<Sigma>\<rangle>}" by auto
    have key:"\<forall>e\<in>z. e=s0 \<and> (\<exists>q\<in>y. q\<in>F)"
    proof(rule ballI)
      fix e assume ez:"e\<in>z"
      with zdef obtain q where q:"q\<in>y" "e\<in>?tc`\<langle>q,\<Sigma>\<rangle>" by auto
      from q(1) as(3) have "q\<in>U \<or> q=s0" by auto
      with US s0S have qS:"q\<in>S" by auto
      show "e=s0 \<and> (\<exists>q\<in>y. q\<in>F)"
      proof(cases "q\<in>F")
        case True
        then have "?tc`\<langle>q,\<Sigma>\<rangle> = {s0}" using epsilon_trans_fun_F[OF fin A True] by auto
        with q True show ?thesis by auto
      next
        case False
        with qS have qSF:"q\<in>S-F" by auto
        then have "?tc`\<langle>q,\<Sigma>\<rangle> = 0" using epsilon_trans_fun_s[OF fin A qSF] by auto
        with q(2) show ?thesis by auto
      qed
    qed
    then have "z\<subseteq>U\<union>{s0}" by auto
    moreover
    {
      assume s0z:"s0\<in>z"
      with key obtain q where q:"q\<in>y" "q\<in>F" by auto
      from q(1) as(3) have "q\<in>U \<or> q=s0" by auto
      then have "s0\<in>U \<or> U\<inter>F\<noteq>0"
      proof
        assume "q\<in>U"
        with q(2) show ?thesis by auto
      next
        assume "q=s0"
        with q(1) as(3) show ?thesis by auto
      qed
    }
    ultimately show "z\<subseteq>U\<union>{s0} \<and> (s0\<in>z \<longrightarrow> s0\<in>U \<or> U\<inter>F\<noteq>0)" by auto
  qed
  show ?thesis
  proof(cases "x\<in>U")
    case True
    then show ?thesis by auto
  next
    case False
    with P(2) inv have xs:"x=s0" by auto
    with P(2) inv have "s0\<in>U \<or> U\<inter>F\<noteq>0" by auto
    with False xs show ?thesis by auto
  qed
qed

text\<open>If the $\epsilon$-closure computed in start-eNFSA from the set $E$ is going to be iterated, we need
  to know that $s_0$ is in the closure whenever $E$ contains an accepting state or the new state $S$.\<close>

lemma start_eNFSA_s0_in_cl:
  assumes fin:"Finite(\<Sigma>)" and A:"(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  and E:"E\<subseteq>start_eNFSA_states(S)" and e:"e\<in>E" "e\<in>F\<union>{S}"
  shows "s0\<in>\<epsilon>-cl(start_eNFSA_states(S),start_eNFSA_trans(S,s0,t,F,\<Sigma>),\<Sigma>,E)"
proof-
  let ?SS = "start_eNFSA_states(S)"
  let ?tc = "start_eNFSA_trans(S,s0,t,F,\<Sigma>)"
  have valid:"(?SS,S,?tc,F\<union>{S}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using start_eNFSA_valid[OF fin A] by auto
  from A have s0S:"s0\<in>S" using DFSA_def[OF fin] by auto
  have tce:"?tc`\<langle>e,\<Sigma>\<rangle> = {s0}"
  proof-
    from e(2) have "e\<in>F \<or> e=S" by auto
    then show ?thesis
    proof
      assume eF:"e\<in>F"
      then show ?thesis using epsilon_trans_fun_F[OF fin A eF] by auto
    next
      assume "e=S"
      then show ?thesis using epsilon_trans_fun_S[OF fin A] by auto
    qed
  qed
  let ?r = "{\<langle>Q,{s\<in>?SS. \<exists>q\<in>Q. s\<in>?tc`\<langle>q,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(?SS)}"
  let ?B = "{s\<in>?SS. \<exists>q\<in>E. s\<in>?tc`\<langle>q,\<Sigma>\<rangle>}"
  have EP:"E\<in>Pow(?SS)" using E by auto
  have B:"?B\<in>Pow(?SS)" by auto
  have "s0\<in> start_eNFSA_states(S)" using s0S unfolding start_eNFSA_states_def by auto moreover
  have "s0\<in>start_eNFSA_trans(S, s0, t, F, \<Sigma>) `\<langle>e, \<Sigma>\<rangle>" using tce by auto
  ultimately have s0B:"s0\<in>?B" using e(1) by auto
  from EP have "\<langle>E,?B\<rangle>\<in>?r" by auto
  then have "\<langle>E,?B\<rangle>\<in>?r^*" using r_into_rtrancl by auto
  with B have "?B \<subseteq> \<epsilon>-cl(?SS,?tc,\<Sigma>,E)"
    using EpsilonClosure_def[OF fin valid E] by force
  with s0B show ?thesis by auto
qed

text\<open>If an execution of an $\epsilon$-NFSA reduces the word $j$ to the word $r$, then the same execution,
  started at the same set of states, reduces $s\cdot j$ to $s\cdot r$ for any word $s$.\<close>

lemma eps_nfsa_run_prefix:
  assumes fin:"Finite(\<Sigma>)" and fsa:"(X,x0,tt,Acc){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
  and run:"\<langle>\<langle>j,P0\<rangle>,\<langle>r,Q1\<rangle>\<rangle>\<in>({reduce \<epsilon>-N-relation}(X,tt){in alphabet}\<Sigma>)^*"
  and jNE:"j\<in>NELists(\<Sigma>)" and PX:"P0\<in>Pow(X)" and sL:"s\<in>Lists(\<Sigma>)"
  shows "\<langle>\<langle>Concat(s,j),P0\<rangle>,\<langle>Concat(s,r),Q1\<rangle>\<rangle>\<in>({reduce \<epsilon>-N-relation}(X,tt){in alphabet}\<Sigma>)^*"
proof-
  let ?R = "{reduce \<epsilon>-N-relation}(X,tt){in alphabet}\<Sigma>"
  have Csj:"Concat(s,j)\<in>NELists(\<Sigma>)" using concat_is_NElist[OF sL jNE] by auto
  from Csj PX have "\<langle>Concat(s,j),P0\<rangle>\<in>field(?R)" using eps_nfsa_field(2)[OF fin fsa] by auto
  then have base:"\<langle>\<langle>Concat(s,j),P0\<rangle>,\<langle>Concat(s,j),P0\<rangle>\<rangle>\<in>?R^*" using rtrancl_refl by auto
  have "\<langle>\<langle>Concat(s,j),P0\<rangle>,\<langle>Concat(s,fst(\<langle>r,Q1\<rangle>)),snd(\<langle>r,Q1\<rangle>)\<rangle>\<rangle>\<in>?R^*"
  proof(rule rtrancl_induct[OF run, where P="\<lambda>y. \<langle>\<langle>Concat(s,j),P0\<rangle>,\<langle>Concat(s,fst(y)),snd(y)\<rangle>\<rangle>\<in>?R^*"])
    show "\<langle>\<langle>Concat(s,j),P0\<rangle>,\<langle>Concat(s,fst(\<langle>j,P0\<rangle>)),snd(\<langle>j,P0\<rangle>)\<rangle>\<rangle>\<in>?R^*"
      using base by auto
  next
    fix y z assume as:"\<langle>\<langle>j,P0\<rangle>,y\<rangle>\<in>?R^*" "\<langle>y,z\<rangle>\<in>?R"
      "\<langle>\<langle>Concat(s,j),P0\<rangle>,\<langle>Concat(s,fst(y)),snd(y)\<rangle>\<rangle>\<in>?R^*"
    from as(2) obtain yl Qy where yz:"yl\<in>NELists(\<Sigma>)" "Qy\<in>Pow(X)" "y=\<langle>yl,Qy\<rangle>"
      "z=\<langle>Init(yl),\<epsilon>-cl(X,tt,\<Sigma>,\<Union>{tt`\<langle>u,Last(yl)\<rangle>. u\<in>\<epsilon>-cl(X,tt,\<Sigma>,Qy)})\<rangle>"
      unfolding FullNFSAExecutionRelation_def[OF fin fsa] by auto
    have Csyl:"Concat(s,yl)\<in>NELists(\<Sigma>)" using concat_is_NElist[OF sL yz(1)] by auto
    have lastEq:"Last(Concat(s,yl)) = Last(yl)" using concat_last_NElist[OF sL yz(1)] by auto
    have initEq:"Init(Concat(s,yl)) = Concat(s,Init(yl))" using concat_init_NElist[OF sL yz(1)] by auto
    from as(3) yz(3) have A1:"\<langle>\<langle>Concat(s,j),P0\<rangle>,\<langle>Concat(s,yl),Qy\<rangle>\<rangle>\<in>?R^*" by auto
    have "\<langle>\<langle>Concat(s,yl),Qy\<rangle>,\<langle>Init(Concat(s,yl)),\<epsilon>-cl(X,tt,\<Sigma>,\<Union>{tt`\<langle>u,Last(Concat(s,yl))\<rangle>. u\<in>\<epsilon>-cl(X,tt,\<Sigma>,Qy)})\<rangle>\<rangle>\<in>?R"
      unfolding FullNFSAExecutionRelation_def[OF fin fsa] using Csyl yz(2) by auto
    with lastEq initEq have step:"\<langle>\<langle>Concat(s,yl),Qy\<rangle>,\<langle>Concat(s,Init(yl)),\<epsilon>-cl(X,tt,\<Sigma>,\<Union>{tt`\<langle>u,Last(yl)\<rangle>. u\<in>\<epsilon>-cl(X,tt,\<Sigma>,Qy)})\<rangle>\<rangle>\<in>?R"
      by auto
    with A1 have "\<langle>\<langle>Concat(s,j),P0\<rangle>,\<langle>Concat(s,Init(yl)),\<epsilon>-cl(X,tt,\<Sigma>,\<Union>{tt`\<langle>u,Last(yl)\<rangle>. u\<in>\<epsilon>-cl(X,tt,\<Sigma>,Qy)})\<rangle>\<rangle>\<in>?R^*"
      using rtrancl_into_rtrancl by auto
    with yz(4) show "\<langle>\<langle>Concat(s,j),P0\<rangle>,\<langle>Concat(s,fst(z)),snd(z)\<rangle>\<rangle>\<in>?R^*" by auto
  qed
  then show ?thesis by auto
qed

text\<open>Every execution of the DFSA on a nonempty word, starting at $s_0$, is simulated by
  an execution of start-eNFSA that starts at any set $P_0$ of states whose $\epsilon$-closure contains
  $s_0$: if the DFSA reaches the state $q$ then $q$ belongs to the $\epsilon$-closure of the set of
  states reached by start-eNFSA.\<close>

lemma start_eNFSA_simulates_DFSA_from:
  assumes fin:"Finite(\<Sigma>)" and A:"(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  and run:"\<langle>\<langle>w,s0\<rangle>,\<langle>r,q\<rangle>\<rangle>\<in>({reduce D-relation}(S,t){in alphabet}\<Sigma>)^*"
  and wne:"w\<in>NELists(\<Sigma>)"
  and P0:"P0\<in>Pow(start_eNFSA_states(S))"
  and s0P:"s0\<in>\<epsilon>-cl(start_eNFSA_states(S),start_eNFSA_trans(S,s0,t,F,\<Sigma>),\<Sigma>,P0)"
  shows "\<exists>Q\<in>Pow(start_eNFSA_states(S)). q\<in>\<epsilon>-cl(start_eNFSA_states(S),start_eNFSA_trans(S,s0,t,F,\<Sigma>),\<Sigma>,Q) \<and>
    \<langle>\<langle>w,P0\<rangle>,\<langle>r,Q\<rangle>\<rangle>\<in>({reduce \<epsilon>-N-relation}(start_eNFSA_states(S),start_eNFSA_trans(S,s0,t,F,\<Sigma>)){in alphabet}\<Sigma>)^*"
proof-
  let ?SS = "start_eNFSA_states(S)"
  let ?tc = "start_eNFSA_trans(S,s0,t,F,\<Sigma>)"
  let ?r = "{reduce \<epsilon>-N-relation}(?SS,?tc){in alphabet}\<Sigma>"
  have valid:"(?SS,S,?tc,F\<union>{S}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using start_eNFSA_valid[OF fin A] by auto
  have tT:"?tc:?SS\<times>succ(\<Sigma>)\<rightarrow>Pow(?SS)" using valid unfolding FullNFSA_def[OF fin] by auto
  have cl_sub:"\<And>E. E\<subseteq>?SS \<Longrightarrow> \<epsilon>-cl(?SS,?tc,\<Sigma>,E) \<subseteq> ?SS"
  proof-
    fix E assume E:"E\<subseteq>?SS"
    show "\<epsilon>-cl(?SS,?tc,\<Sigma>,E) \<subseteq> ?SS" using start_eNFSA_cl_subset[OF fin A E] by auto
  qed
  have key:"\<exists>Q\<in>Pow(?SS). snd(\<langle>r,q\<rangle>)\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Q) \<and> \<langle>\<langle>w,P0\<rangle>,\<langle>fst(\<langle>r,q\<rangle>),Q\<rangle>\<rangle>\<in>?r^*"
  proof(rule rtrancl_induct[OF run, where P="\<lambda>y. \<exists>Q\<in>Pow(?SS). snd(y)\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Q) \<and> \<langle>\<langle>w,P0\<rangle>,\<langle>fst(y),Q\<rangle>\<rangle>\<in>?r^*"])
    from wne P0 have "\<langle>w,P0\<rangle>\<in>field(?r)" using eps_nfsa_field(2)[OF fin valid] by auto
    then have "\<langle>\<langle>w,P0\<rangle>,\<langle>w,P0\<rangle>\<rangle>\<in>?r^*" using rtrancl_refl by auto
    with s0P P0 show "\<exists>Q\<in>Pow(?SS). snd(\<langle>w,s0\<rangle>)\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Q) \<and> \<langle>\<langle>w,P0\<rangle>,\<langle>fst(\<langle>w,s0\<rangle>),Q\<rangle>\<rangle>\<in>?r^*"
      by auto
  next
    fix y z assume as:"\<langle>\<langle>w,s0\<rangle>,y\<rangle>\<in>({reduce D-relation}(S,t){in alphabet}\<Sigma>)^*"
      "\<langle>y,z\<rangle>\<in>({reduce D-relation}(S,t){in alphabet}\<Sigma>)"
      "\<exists>Q\<in>Pow(?SS). snd(y)\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Q) \<and> \<langle>\<langle>w,P0\<rangle>,\<langle>fst(y),Q\<rangle>\<rangle>\<in>?r^*"
    from as(2) obtain yl ys where yz:"yl\<in>NELists(\<Sigma>)" "ys\<in>S" "y=\<langle>yl,ys\<rangle>" "z=\<langle>Init(yl),t`\<langle>ys,Last(yl)\<rangle>\<rangle>"
      unfolding DFSAExecutionRelation_def[OF fin A] by auto
    from yz(3) as(3) obtain Qy where Q:"Qy\<in>Pow(?SS)" "ys\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Qy)" "\<langle>\<langle>w,P0\<rangle>,\<langle>yl,Qy\<rangle>\<rangle>\<in>?r^*" by auto
    let ?U = "\<Union>{?tc`\<langle>u,Last(yl)\<rangle>. u\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Qy)}"
    have step:"\<langle>\<langle>yl,Qy\<rangle>,\<langle>Init(yl),\<epsilon>-cl(?SS,?tc,\<Sigma>,?U)\<rangle>\<rangle>\<in>?r"
      unfolding FullNFSAExecutionRelation_def[OF fin valid] using yz(1) Q(1) by auto
    with Q(3) have A1:"\<langle>\<langle>w,P0\<rangle>,\<langle>Init(yl),\<epsilon>-cl(?SS,?tc,\<Sigma>,?U)\<rangle>\<rangle>\<in>?r^*" using rtrancl_into_rtrancl by auto
    from yz(1) have lastSig:"Last(yl)\<in>\<Sigma>" using last_type by auto
    from fin A yz(2) lastSig have tys:"?tc`\<langle>ys,Last(yl)\<rangle> = {t`\<langle>ys,Last(yl)\<rangle>}"
      using start_eNFSA_trans_symbol by auto
    from Q(1) have QyS:"Qy\<subseteq>?SS" by auto
    have unionSS:"?U \<subseteq> ?SS"
    proof
      fix x assume "x\<in>?U"
      then obtain ss where ss:"ss\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Qy)" "x\<in>?tc`\<langle>ss,Last(yl)\<rangle>" by auto
      from ss(1) cl_sub[OF QyS] have ssS:"ss\<in>?SS" by auto
      from lastSig have "Last(yl)\<in>succ(\<Sigma>)" by auto
      with ssS have "\<langle>ss,Last(yl)\<rangle>\<in>?SS\<times>succ(\<Sigma>)" by auto
      from apply_type[OF tT this] ss(2) show "x\<in>?SS" by auto
    qed
    have "t`\<langle>ys,Last(yl)\<rangle>\<in>{t`\<langle>ys,Last(yl)\<rangle>}" by auto
    moreover from Q(2) have
      "(?tc`\<langle>ys,Last(yl)\<rangle>) \<subseteq> ?U" by auto
    moreover note tys
    ultimately have xU:"t`\<langle>ys,Last(yl)\<rangle>\<in>?U" by auto
    have refl1:"?U \<subseteq> \<epsilon>-cl(?SS,?tc,\<Sigma>,?U)" using epsilon_cl_refl_sub[OF fin valid unionSS] by auto
    from unionSS have QSS:"\<epsilon>-cl(?SS,?tc,\<Sigma>,?U) \<subseteq> ?SS" using cl_sub by auto
    then have refl2:"\<epsilon>-cl(?SS,?tc,\<Sigma>,?U) \<subseteq> \<epsilon>-cl(?SS,?tc,\<Sigma>,\<epsilon>-cl(?SS,?tc,\<Sigma>,?U))"
      using epsilon_cl_refl_sub[OF fin valid] by auto
    from xU refl1 refl2 have mem:"t`\<langle>ys,Last(yl)\<rangle>\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,\<epsilon>-cl(?SS,?tc,\<Sigma>,?U))" by auto
    from QSS have Qnew:"\<epsilon>-cl(?SS,?tc,\<Sigma>,?U)\<in>Pow(?SS)" by auto
    from Qnew mem A1 yz(4) show "\<exists>Q\<in>Pow(?SS). snd(z)\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Q) \<and> \<langle>\<langle>w,P0\<rangle>,\<langle>fst(z),Q\<rangle>\<rangle>\<in>?r^*"
      by auto
  qed
  then show ?thesis by auto
qed

text\<open>In particular, an execution of the DFSA on a nonempty word is simulated by start-eNFSA
  started at the new state $S$.\<close>

lemma start_eNFSA_simulates_DFSA:
  assumes fin:"Finite(\<Sigma>)" and A:"(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  and run:"\<langle>\<langle>w,s0\<rangle>,\<langle>r,q\<rangle>\<rangle>\<in>({reduce D-relation}(S,t){in alphabet}\<Sigma>)^*"
  and wne:"w\<in>NELists(\<Sigma>)"
  shows "\<exists>Q\<in>Pow(start_eNFSA_states(S)). q\<in>\<epsilon>-cl(start_eNFSA_states(S),start_eNFSA_trans(S,s0,t,F,\<Sigma>),\<Sigma>,Q) \<and>
    \<langle>\<langle>w,{S}\<rangle>,\<langle>r,Q\<rangle>\<rangle>\<in>({reduce \<epsilon>-N-relation}(start_eNFSA_states(S),start_eNFSA_trans(S,s0,t,F,\<Sigma>)){in alphabet}\<Sigma>)^*"
proof-
  have SPow:"{S}\<in>Pow(start_eNFSA_states(S))" unfolding start_eNFSA_states_def by auto
  have "\<epsilon>-cl(start_eNFSA_states(S),start_eNFSA_trans(S,s0,t,F,\<Sigma>),\<Sigma>,{S}) = {S,s0}"
    using epsilon_cl_F_in_cl_S[OF fin A] by auto
  then have s0P:"s0\<in>\<epsilon>-cl(start_eNFSA_states(S),start_eNFSA_trans(S,s0,t,F,\<Sigma>),\<Sigma>,{S})" by auto
  show ?thesis using start_eNFSA_simulates_DFSA_from[OF fin A run wne SPow s0P] by auto
qed


text\<open>Every word accepted by the original DFSA is accepted by start-eNFSA: the empty word
  is accepted because the $\epsilon$-closure of the initial state $S$ contains $S$, and for a
  nonempty word the DFSA execution is simulated by start-eNFSA, after the initial
  $\epsilon$-move to $s_0$.\<close>

lemma L_subset_eNFSA_lang:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  shows "{w \<in> Lists(\<Sigma>). w <-D (S,s0,t,F){in alphabet}\<Sigma>}
         \<subseteq> {w \<in> Lists(\<Sigma>). w <-\<epsilon>-N (start_eNFSA_states(S), S,
                                start_eNFSA_trans(S,s0,t,F,\<Sigma>), F\<union>{S}){in alphabet}\<Sigma>}"
proof
  fix w assume w_in_L:"w \<in> {w \<in> Lists(\<Sigma>). w <-D (S,s0,t,F){in alphabet}\<Sigma>}"
  then have w_type:"w \<in> Lists(\<Sigma>)" "w <-D (S,s0,t,F){in alphabet}\<Sigma>" by auto
  have valid_eNFSA:"(start_eNFSA_states(S), S, start_eNFSA_trans(S,s0,t,F,\<Sigma>), F\<union>{S}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using start_eNFSA_valid[OF assms(1,2)] by auto
  show "w \<in> {w \<in> Lists(\<Sigma>). w <-\<epsilon>-N (start_eNFSA_states(S), S,
    start_eNFSA_trans(S,s0,t,F,\<Sigma>), F\<union>{S}){in alphabet}\<Sigma>}"
  proof(cases "w=0")
    case True
    then show ?thesis using empty_in_eNFSA_lang assms by auto
  next
    case False
    with w_type(1) have wne:"w\<in>NELists(\<Sigma>)" using non_zero_List_func_is_NEList by auto
    from w_type(2) w_type(1) have "(\<exists>q\<in>F. \<langle>\<langle>w,s0\<rangle>,\<langle>0,q\<rangle>\<rangle> \<in> ({reduce D-relation}(S,t){in alphabet}\<Sigma>)^*) \<or> (w = 0 \<and> s0\<in>F)"
      using DFSASatisfy_def[OF assms(1) assms(2) w_type(1)] by auto
    with False obtain q where q:"q\<in>F" "\<langle>\<langle>w,s0\<rangle>,\<langle>0,q\<rangle>\<rangle> \<in> ({reduce D-relation}(S,t){in alphabet}\<Sigma>)^*" by auto
    obtain Q where Q:"Q\<in>Pow(start_eNFSA_states(S))"
      "q\<in>\<epsilon>-cl(start_eNFSA_states(S),start_eNFSA_trans(S,s0,t,F,\<Sigma>),\<Sigma>,Q)"
      "\<langle>\<langle>w,{S}\<rangle>,\<langle>0,Q\<rangle>\<rangle>\<in>({reduce \<epsilon>-N-relation}(start_eNFSA_states(S),start_eNFSA_trans(S,s0,t,F,\<Sigma>)){in alphabet}\<Sigma>)^*"
      using start_eNFSA_simulates_DFSA[OF assms(1,2) q(2) wne] by blast
    from q(1) Q(2) have "\<epsilon>-cl(start_eNFSA_states(S),start_eNFSA_trans(S,s0,t,F,\<Sigma>),\<Sigma>,Q)\<inter>(F\<union>{S}) \<noteq> 0" by auto
    then have "w <-\<epsilon>-N (start_eNFSA_states(S), S, start_eNFSA_trans(S,s0,t,F,\<Sigma>), F\<union>{S}){in alphabet}\<Sigma>"
      unfolding FullNFSASatisfy_def[OF assms(1) valid_eNFSA w_type(1)] using Q by blast
    with w_type(1) show ?thesis by auto
  qed
qed


text\<open>Prepending a word of $L$, or the empty word, to a word of $L^*$ gives a word of $L^*$.\<close>

lemma star_prepend:
  assumes "Finite(\<Sigma>)" "L {is a language with alphabet}\<Sigma>" "x\<in>L\<union>{0}" "c\<in>(L*\<^sup>\<Sigma>)"
  shows "Concat(x,c)\<in>(L*\<^sup>\<Sigma>)"
proof-
  have "0:0\<rightarrow>\<Sigma>" unfolding Pi_def function_def by auto
  then have l0:"0\<in>Lists(\<Sigma>)" unfolding Lists_def by blast
  from assms(4) have c:"c\<in>Lists(\<Sigma>)" "\<langle>0,c\<rangle>\<in>R_lang(L,\<Sigma>)^*" using star_def assms(1,2) by auto
  have xL:"x\<in>Lists(\<Sigma>)"
  proof(cases "x=0")
    case True
    with l0 show ?thesis by auto
  next
    case False
    with assms(3) have "x\<in>L" by auto
    with assms(1,2) show ?thesis using IsALanguage_def by auto
  qed
  have cc:"Concat(x,c)\<in>Lists(\<Sigma>)" using concat_type xL c(1) by auto
  from c(1) cc have "\<langle>c,Concat(x,c)\<rangle>\<in>Lists(\<Sigma>)\<times>Lists(\<Sigma>)" by auto
  moreover from assms(3) have "\<exists>y\<in>L\<union>{0}. Concat(x,c) = Concat(y,c)" by auto
  ultimately have "\<langle>c,Concat(x,c)\<rangle> \<in> {\<langle>v,w\<rangle>\<in>Lists(\<Sigma>)\<times>Lists(\<Sigma>). \<exists>y\<in>L\<union>{0}. w = Concat(y,v)}" by auto
  then have "\<langle>c,Concat(x,c)\<rangle>\<in>R_lang(L,\<Sigma>)" using R_lang_def assms(1,2) by auto
  with c(2) have "\<langle>0,Concat(x,c)\<rangle>\<in>R_lang(L,\<Sigma>)^*" using rtrancl_into_rtrancl by auto
  with cc show ?thesis using star_def assms(1,2) by auto
qed

text\<open>If $x$ is a word accepted by the DFSA and $v$ is a word accepted by start-eNFSA,
  then the concatenation $x\cdot v$ is accepted by start-eNFSA. The automaton reads $v$ first,
  then restarts at $s_0$ thanks to the $\epsilon$-transition from an accepting state, and then reads $x$.\<close>

lemma concat_L_eNFSA_lang:
  assumes fin:"Finite(\<Sigma>)" and A:"(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  and x:"x\<in>Lists(\<Sigma>)" "x <-D (S,s0,t,F){in alphabet}\<Sigma>"
  and v:"v\<in>Lists(\<Sigma>)"
    "v <-\<epsilon>-N (start_eNFSA_states(S),S,start_eNFSA_trans(S,s0,t,F,\<Sigma>),F\<union>{S}){in alphabet}\<Sigma>"
  shows "Concat(x,v) <-\<epsilon>-N (start_eNFSA_states(S),S,start_eNFSA_trans(S,s0,t,F,\<Sigma>),F\<union>{S}){in alphabet}\<Sigma>"
proof-
  let ?SS = "start_eNFSA_states(S)"
  let ?tc = "start_eNFSA_trans(S,s0,t,F,\<Sigma>)"
  let ?R = "{reduce \<epsilon>-N-relation}(?SS,?tc){in alphabet}\<Sigma>"
  let ?rD = "{reduce D-relation}(S,t){in alphabet}\<Sigma>"
  have valid:"(?SS,S,?tc,F\<union>{S}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using start_eNFSA_valid[OF fin A] by auto
  have CL:"Concat(x,v)\<in>Lists(\<Sigma>)" using concat_type x(1) v(1) by auto
  have SPow:"{S}\<in>Pow(?SS)" unfolding start_eNFSA_states_def by auto
  show ?thesis
  proof(cases "x=0")
    case True
    have "Concat(0,v) = v" using concat_empty(2) v(1) unfolding Lists_def by auto
    with True v(2) show ?thesis by auto
  next
    case xne:False
    show ?thesis
    proof(cases "v=0")
      case True
      have e1:"Concat(x,0) = x" using concat_empty(1) x(1) unfolding Lists_def by auto
      have e2:"x\<in>{w\<in>Lists(\<Sigma>). w <-D (S,s0,t,F){in alphabet}\<Sigma>}" using x by auto
      have e3:"x\<in>{w\<in>Lists(\<Sigma>). w <-\<epsilon>-N (?SS,S,?tc,F\<union>{S}){in alphabet}\<Sigma>}"
        using L_subset_eNFSA_lang[OF fin A] e2 by auto
      from e3 have "x <-\<epsilon>-N (?SS,S,?tc,F\<union>{S}){in alphabet}\<Sigma>" by auto
      with e1 True show ?thesis by auto
    next
      case vne:False
      from v(2) have acc:"(\<exists>Q\<in>Pow(?SS). \<epsilon>-cl(?SS,?tc,\<Sigma>,Q)\<inter>(F\<union>{S})\<noteq>0 \<and> \<langle>\<langle>v,{S}\<rangle>,\<langle>0,Q\<rangle>\<rangle>\<in>?R^*)
        \<or> (v=0 \<and> \<epsilon>-cl(?SS,?tc,\<Sigma>,{S})\<inter>(F\<union>{S})\<noteq>0)"
        using FullNFSASatisfy_def[OF fin valid v(1)] by auto
      with vne obtain Q where Q:"Q\<in>Pow(?SS)" "\<epsilon>-cl(?SS,?tc,\<Sigma>,Q)\<inter>(F\<union>{S})\<noteq>0"
        "\<langle>\<langle>v,{S}\<rangle>,\<langle>0,Q\<rangle>\<rangle>\<in>?R^*" by auto
      have vNE:"v\<in>NELists(\<Sigma>)" using non_zero_List_func_is_NEList v(1) vne by auto
      have xNE:"x\<in>NELists(\<Sigma>)" using non_zero_List_func_is_NEList x(1) xne by auto
      have lift:"\<langle>\<langle>Concat(x,v),{S}\<rangle>,\<langle>Concat(x,0),Q\<rangle>\<rangle>\<in>?R^*"
        using eps_nfsa_run_prefix[OF fin valid Q(3) vNE SPow x(1)] by auto
      have c0:"Concat(x,0) = x" using concat_empty(1) x(1) unfolding Lists_def by auto
      with lift have lift2:"\<langle>\<langle>Concat(x,v),{S}\<rangle>,\<langle>x,Q\<rangle>\<rangle>\<in>?R^*" by auto
      from x(2) have dacc:"(\<exists>f\<in>F. \<langle>\<langle>x,s0\<rangle>,\<langle>0,f\<rangle>\<rangle>\<in>?rD^*) \<or> (x=0 \<and> s0\<in>F)"
        using DFSASatisfy_def[OF fin A x(1)] by auto
      with xne obtain f where f:"f\<in>F" "\<langle>\<langle>x,s0\<rangle>,\<langle>0,f\<rangle>\<rangle>\<in>?rD^*" by auto
      from Q(2) have "\<exists>e. e\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Q)\<inter>(F\<union>{S})" by auto
      then obtain e where e:"e\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Q)" "e\<in>F\<union>{S}" by auto
      from Q(1) have QS:"Q\<subseteq>?SS" by auto
      have clQS:"\<epsilon>-cl(?SS,?tc,\<Sigma>,Q)\<subseteq>?SS" using start_eNFSA_cl_subset[OF fin A QS] by auto
      have "s0\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,\<epsilon>-cl(?SS,?tc,\<Sigma>,Q))"
        using start_eNFSA_s0_in_cl[OF fin A clQS e(1) e(2)] by auto
      moreover have "\<epsilon>-cl(?SS,?tc,\<Sigma>,\<epsilon>-cl(?SS,?tc,\<Sigma>,Q)) = \<epsilon>-cl(?SS,?tc,\<Sigma>,Q)"
        using epsilon_cl_idem[OF fin valid Q(1)] by auto
      ultimately have s0cl:"s0\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Q)" by auto
      obtain Q2 where Q2:"Q2\<in>Pow(?SS)" "f\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Q2)" "\<langle>\<langle>x,Q\<rangle>,\<langle>0,Q2\<rangle>\<rangle>\<in>?R^*"
        using start_eNFSA_simulates_DFSA_from[OF fin A f(2) xNE Q(1) s0cl] by blast
      from lift2 Q2(3) have comp:"\<langle>\<langle>Concat(x,v),{S}\<rangle>,\<langle>0,Q2\<rangle>\<rangle>\<in>?R^*"
        using trans_rtrancl unfolding trans_def by auto
      from Q2(2) f(1) have clne:"\<epsilon>-cl(?SS,?tc,\<Sigma>,Q2)\<inter>(F\<union>{S})\<noteq>0" by auto
      show ?thesis unfolding FullNFSASatisfy_def[OF fin valid CL] using Q2(1) clne comp by blast
    qed
  qed
qed

text\<open>The Kleene star of the language of the DFSA is contained in the language
  accepted by start-eNFSA. We follow the construction of $L^*$: the empty word is accepted and
  prepending a word of $L$ to an accepted word gives an accepted word.\<close>

lemma star_subset_eNFSA_lang:
  assumes fin:"Finite(\<Sigma>)" and A:"(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  shows "({u\<in>Lists(\<Sigma>). u <-D (S,s0,t,F){in alphabet}\<Sigma>}*\<^sup>\<Sigma>) \<subseteq>
    {w\<in>Lists(\<Sigma>). w <-\<epsilon>-N (start_eNFSA_states(S),S,start_eNFSA_trans(S,s0,t,F,\<Sigma>),F\<union>{S}){in alphabet}\<Sigma>}"
proof
  let ?L = "{u\<in>Lists(\<Sigma>). u <-D (S,s0,t,F){in alphabet}\<Sigma>}"
  let ?M = "{w\<in>Lists(\<Sigma>). w <-\<epsilon>-N (start_eNFSA_states(S),S,start_eNFSA_trans(S,s0,t,F,\<Sigma>),F\<union>{S}){in alphabet}\<Sigma>}"
  have langL:"?L {is a language with alphabet}\<Sigma>" unfolding IsALanguage_def[OF fin] by auto
  fix x assume x:"x\<in>(?L*\<^sup>\<Sigma>)"
  from x have xx:"x\<in>Lists(\<Sigma>)" "\<langle>0,x\<rangle>\<in>R_lang(?L,\<Sigma>)^*" using star_def fin langL by auto
  show "x\<in>?M"
  proof(rule rtrancl_induct[OF xx(2), where P="\<lambda>y. y\<in>?M"])
    show "0\<in>?M" using empty_in_eNFSA_lang[OF fin A] by auto
  next
    fix y z assume as:"\<langle>0,y\<rangle>\<in>R_lang(?L,\<Sigma>)^*" "\<langle>y,z\<rangle>\<in>R_lang(?L,\<Sigma>)" "y\<in>?M"
    from as(2) obtain q where q:"z=Concat(q,y)" "q\<in>?L\<union>{0}" "y\<in>Lists(\<Sigma>)" "z\<in>Lists(\<Sigma>)"
      using R_lang_def fin langL by auto
    from as(3) have yM:"y <-\<epsilon>-N (start_eNFSA_states(S),S,start_eNFSA_trans(S,s0,t,F,\<Sigma>),F\<union>{S}){in alphabet}\<Sigma>"
      by auto
    show "z\<in>?M"
    proof(cases "q=0")
      case True
      have "Concat(0,y) = y" using concat_empty(2) q(3) unfolding Lists_def by auto
      with True q(1) as(3) show ?thesis by auto
    next
      case False
      with q(2) have qL:"q\<in>?L" by auto
      then have qq1:"q\<in>Lists(\<Sigma>)" and qq2:"q <-D (S,s0,t,F){in alphabet}\<Sigma>" by auto
      have "Concat(q,y) <-\<epsilon>-N (start_eNFSA_states(S),S,start_eNFSA_trans(S,s0,t,F,\<Sigma>),F\<union>{S}){in alphabet}\<Sigma>"
        using concat_L_eNFSA_lang[OF fin A qq1 qq2 q(3) yM] by auto
      with q(1,4) show ?thesis by auto
    qed
  qed
qed

text\<open>To show the converse inclusion we follow an execution of start-eNFSA on a word $w$. The predicate
  start-eNFSA-wit says that, after reading a suffix of $w$ and leaving $r$ unread, the state $x$ was reached
  as follows: $w=rr\cdot c$ where $c\in L^*$ is the part of the word that was read before the last restart
  at $s_0$, and the DFSA run on $rr$ from $s_0$ has reached the state $x$ with $r$ unread.\<close>

definition start_eNFSA_wit where
  "start_eNFSA_wit(S,s0,t,F,\<Sigma>,w,r,x) \<equiv>
   \<exists>rr\<in>Lists(\<Sigma>). \<exists>c\<in>({u\<in>Lists(\<Sigma>). u <-D (S,s0,t,F){in alphabet}\<Sigma>}*\<^sup>\<Sigma>).
     w=Concat(rr,c) \<and> ((rr=r \<and> x=s0) \<or> \<langle>\<langle>rr,s0\<rangle>,\<langle>r,x\<rangle>\<rangle>\<in>({reduce D-relation}(S,t){in alphabet}\<Sigma>)^*)"

text\<open>The invariant of an execution of start-eNFSA: every state in the $\epsilon$-closure of the current
  set of states $Q$ is either the new state $S$ (before anything was read) or a state of the DFSA
  reached in the way described by start-eNFSA-wit.\<close>

definition start_eNFSA_inv where
  "start_eNFSA_inv(S,s0,t,F,\<Sigma>,w,r,Q) \<equiv> Q\<in>Pow(start_eNFSA_states(S)) \<and>
   (\<forall>x\<in>\<epsilon>-cl(start_eNFSA_states(S),start_eNFSA_trans(S,s0,t,F,\<Sigma>),\<Sigma>,Q).
     (x=S \<and> r=w) \<or> (x\<in>S \<and> start_eNFSA_wit(S,s0,t,F,\<Sigma>,w,r,x)))"

text\<open>Introduction rule for start-eNFSA-wit.\<close>

lemma start_eNFSA_wit_intro:
  assumes "rr\<in>Lists(\<Sigma>)" "c\<in>({u\<in>Lists(\<Sigma>). u <-D (S,s0,t,F){in alphabet}\<Sigma>}*\<^sup>\<Sigma>)" "w=Concat(rr,c)"
    "(rr=r \<and> x=s0) \<or> \<langle>\<langle>rr,s0\<rangle>,\<langle>r,x\<rangle>\<rangle>\<in>({reduce D-relation}(S,t){in alphabet}\<Sigma>)^*"
  shows "start_eNFSA_wit(S,s0,t,F,\<Sigma>,w,r,x)"
  unfolding start_eNFSA_wit_def using assms by blast

text\<open>Every word accepted by start-eNFSA belongs to the Kleene star of the language of the DFSA.\<close>

lemma eNFSA_lang_subset_star:
  assumes fin:"Finite(\<Sigma>)" and A:"(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  shows "{w\<in>Lists(\<Sigma>). w <-\<epsilon>-N (start_eNFSA_states(S),S,start_eNFSA_trans(S,s0,t,F,\<Sigma>),F\<union>{S}){in alphabet}\<Sigma>}
    \<subseteq> ({u\<in>Lists(\<Sigma>). u <-D (S,s0,t,F){in alphabet}\<Sigma>}*\<^sup>\<Sigma>)"
proof
  let ?SS = "start_eNFSA_states(S)"
  let ?tc = "start_eNFSA_trans(S,s0,t,F,\<Sigma>)"
  let ?R = "{reduce \<epsilon>-N-relation}(?SS,?tc){in alphabet}\<Sigma>"
  let ?rD = "{reduce D-relation}(S,t){in alphabet}\<Sigma>"
  let ?L = "{u\<in>Lists(\<Sigma>). u <-D (S,s0,t,F){in alphabet}\<Sigma>}"
  let ?Ls = "(?L)*\<^sup>\<Sigma>"
  have valid:"(?SS,S,?tc,F\<union>{S}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using start_eNFSA_valid[OF fin A] by auto
  have SSdef:"?SS = succ(S)" by (simp add: start_eNFSA_states_def)
  from A have s0S:"s0\<in>S" using DFSA_def[OF fin] by auto
  have langL:"?L {is a language with alphabet}\<Sigma>" unfolding IsALanguage_def[OF fin] by auto
  have D:"DetFinStateAuto(S,s0,t,F,\<Sigma>)" unfolding DetFinStateAuto_def using fin A by auto
  have empty0:"0\<in>?Ls" using empty_star fin langL by auto
  have SnotS:"S\<notin>S" using mem_not_refl by auto
  have SPow:"{S}\<in>Pow(?SS)" using SSdef by auto
  fix w assume wM:"w\<in>{u\<in>Lists(\<Sigma>). u <-\<epsilon>-N (?SS,S,?tc,F\<union>{S}){in alphabet}\<Sigma>}"
  then have wL:"w\<in>Lists(\<Sigma>)" and wacc:"w <-\<epsilon>-N (?SS,S,?tc,F\<union>{S}){in alphabet}\<Sigma>" by auto
  show "w\<in>?Ls"
  proof(cases "w=0")
    case True
    with empty0 show ?thesis by auto
  next
    case wne:False
    from wacc have acc:"(\<exists>Q\<in>Pow(?SS). \<epsilon>-cl(?SS,?tc,\<Sigma>,Q)\<inter>(F\<union>{S})\<noteq>0 \<and> \<langle>\<langle>w,{S}\<rangle>,\<langle>0,Q\<rangle>\<rangle>\<in>?R^*)
      \<or> (w=0 \<and> \<epsilon>-cl(?SS,?tc,\<Sigma>,{S})\<inter>(F\<union>{S})\<noteq>0)"
      using FullNFSASatisfy_def[OF fin valid wL] by auto
    with wne obtain Q where Q:"Q\<in>Pow(?SS)" "\<epsilon>-cl(?SS,?tc,\<Sigma>,Q)\<inter>(F\<union>{S})\<noteq>0"
      "\<langle>\<langle>w,{S}\<rangle>,\<langle>0,Q\<rangle>\<rangle>\<in>?R^*" by auto
    have claim:"\<forall>r' Q'. \<langle>0,Q\<rangle>=\<langle>r',Q'\<rangle> \<longrightarrow> start_eNFSA_inv(S,s0,t,F,\<Sigma>,w,r',Q')"
    proof(rule rtrancl_induct[OF Q(3), where P="\<lambda>y. \<forall>r' Q'. y=\<langle>r',Q'\<rangle> \<longrightarrow> start_eNFSA_inv(S,s0,t,F,\<Sigma>,w,r',Q')"])
      show "\<forall>r' Q'. \<langle>w,{S}\<rangle>=\<langle>r',Q'\<rangle> \<longrightarrow> start_eNFSA_inv(S,s0,t,F,\<Sigma>,w,r',Q')"
      proof(intro allI impI)
        fix r' Q' assume eq:"\<langle>w,{S}\<rangle>=\<langle>r',Q'\<rangle>"
        then have e:"r'=w" "Q'={S}" by auto
        have clS:"\<epsilon>-cl(?SS,?tc,\<Sigma>,{S}) = {S,s0}" using epsilon_cl_F_in_cl_S[OF fin A] by auto
        have "\<forall>x\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Q'). (x=S \<and> r'=w) \<or> (x\<in>S \<and> start_eNFSA_wit(S,s0,t,F,\<Sigma>,w,r',x))"
        proof(rule ballI)
          fix x assume x:"x\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Q')"
          with e(2) clS have "x=S \<or> x=s0" by auto
          then show "(x=S \<and> r'=w) \<or> (x\<in>S \<and> start_eNFSA_wit(S,s0,t,F,\<Sigma>,w,r',x))"
          proof
            assume "x=S"
            with e(1) show ?thesis by auto
          next
            assume xs:"x=s0"
            have c3:"w = Concat(w,0)" using concat_empty(1) wL unfolding Lists_def by auto
            have d4:"(w=r' \<and> x=s0) \<or> \<langle>\<langle>w,s0\<rangle>,\<langle>r',x\<rangle>\<rangle>\<in>?rD^*" using e(1) xs by auto
            have "start_eNFSA_wit(S,s0,t,F,\<Sigma>,w,r',x)"
              using start_eNFSA_wit_intro[OF wL empty0 c3 d4] by auto
            moreover from xs s0S have "x\<in>S" by auto
            ultimately show ?thesis by auto
          qed
        qed
        moreover from e(2) SPow have "Q'\<in>Pow(?SS)" by auto
        ultimately show "start_eNFSA_inv(S,s0,t,F,\<Sigma>,w,r',Q')" unfolding start_eNFSA_inv_def by auto
      qed
    next
      fix y z assume as:"\<langle>\<langle>w,{S}\<rangle>,y\<rangle>\<in>?R^*" "\<langle>y,z\<rangle>\<in>?R"
        "\<forall>r' Q'. y=\<langle>r',Q'\<rangle> \<longrightarrow> start_eNFSA_inv(S,s0,t,F,\<Sigma>,w,r',Q')"
      from as(2) obtain yl Qy where yz:"yl\<in>NELists(\<Sigma>)" "Qy\<in>Pow(?SS)" "y=\<langle>yl,Qy\<rangle>"
        "z=\<langle>Init(yl),\<epsilon>-cl(?SS,?tc,\<Sigma>,\<Union>{?tc`\<langle>u,Last(yl)\<rangle>. u\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Qy)})\<rangle>"
        unfolding FullNFSAExecutionRelation_def[OF fin valid] by auto
      let ?U = "\<Union>{?tc`\<langle>u,Last(yl)\<rangle>. u\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Qy)}"
      have I:"start_eNFSA_inv(S,s0,t,F,\<Sigma>,w,yl,Qy)" using as(3) yz(3) by auto
      have Ic:"\<forall>s\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Qy). (s=S \<and> yl=w) \<or> (s\<in>S \<and> start_eNFSA_wit(S,s0,t,F,\<Sigma>,w,yl,s))"
        using I unfolding start_eNFSA_inv_def by auto
      have lastSig:"Last(yl)\<in>\<Sigma>" using last_type yz(1) by auto
      have InitL:"Init(yl)\<in>Lists(\<Sigma>)" using init_NElist(1)[OF yz(1)] by auto
      from yz(2) have QyS:"Qy\<subseteq>?SS" by auto
      have clQy:"\<epsilon>-cl(?SS,?tc,\<Sigma>,Qy)\<subseteq>?SS" using start_eNFSA_cl_subset[OF fin A QyS] by auto
      have US:"?U\<subseteq>S"
      proof
        fix x assume "x\<in>?U"
        then obtain s where s:"s\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Qy)" "x\<in>?tc`\<langle>s,Last(yl)\<rangle>" by auto
        from s(1) clQy have "s\<in>?SS" by auto
        with SSdef have sSucc:"s\<in>succ(S)" by auto
        from start_eNFSA_trans_symbol_sub[OF fin A sSucc lastSig] s(2) show "x\<in>S" by auto
      qed
      have USS:"?U\<subseteq>?SS" using US SSdef by auto
      then have USP:"?U\<in>Pow(?SS)" by auto
      have idem:"\<epsilon>-cl(?SS,?tc,\<Sigma>,\<epsilon>-cl(?SS,?tc,\<Sigma>,?U)) = \<epsilon>-cl(?SS,?tc,\<Sigma>,?U)"
        using epsilon_cl_idem[OF fin valid USP] by auto
      have clU:"\<epsilon>-cl(?SS,?tc,\<Sigma>,?U)\<in>Pow(?SS)" using start_eNFSA_cl_subset[OF fin A USS] by auto
      have ext:"\<forall>s\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Qy). \<forall>x\<in>?tc`\<langle>s,Last(yl)\<rangle>.
        \<exists>rr\<in>Lists(\<Sigma>). \<exists>c\<in>?Ls. w=Concat(rr,c) \<and> \<langle>\<langle>rr,s0\<rangle>,\<langle>Init(yl),x\<rangle>\<rangle>\<in>?rD^*"
      proof(intro ballI)
        fix s x assume s:"s\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Qy)" and x:"x\<in>?tc`\<langle>s,Last(yl)\<rangle>"
        from s clQy have "s\<in>?SS" by auto
        with SSdef have sSucc:"s\<in>succ(S)" by auto
        then have "s=S \<or> s\<in>S" by auto
        then show "\<exists>rr\<in>Lists(\<Sigma>). \<exists>c\<in>?Ls. w=Concat(rr,c) \<and> \<langle>\<langle>rr,s0\<rangle>,\<langle>Init(yl),x\<rangle>\<rangle>\<in>?rD^*"
        proof
          assume sS:"s=S"
          then have "?tc`\<langle>s,Last(yl)\<rangle> = 0" using start_eNFSA_trans_symbol_S[OF fin A lastSig] by auto
          with x show ?thesis by auto
        next
          assume sS:"s\<in>S"
          have tcs:"?tc`\<langle>s,Last(yl)\<rangle> = {t`\<langle>s,Last(yl)\<rangle>}"
            using start_eNFSA_trans_symbol[OF fin A sS lastSig] by auto
          with x have xe:"x=t`\<langle>s,Last(yl)\<rangle>" by auto
          from Ic s have "(s=S \<and> yl=w) \<or> (s\<in>S \<and> start_eNFSA_wit(S,s0,t,F,\<Sigma>,w,yl,s))" by auto
          with sS SnotS have W:"start_eNFSA_wit(S,s0,t,F,\<Sigma>,w,yl,s)" by auto
          from W obtain rr c where rc:"rr\<in>Lists(\<Sigma>)" "c\<in>?Ls" "w=Concat(rr,c)"
            "(rr=yl \<and> s=s0) \<or> \<langle>\<langle>rr,s0\<rangle>,\<langle>yl,s\<rangle>\<rangle>\<in>?rD^*"
            unfolding start_eNFSA_wit_def by auto
          have stepD:"\<langle>\<langle>yl,s\<rangle>,\<langle>Init(yl),t`\<langle>s,Last(yl)\<rangle>\<rangle>\<rangle>\<in>?rD"
            unfolding DFSAExecutionRelation_def[OF fin A] using yz(1) sS by auto
          have run2:"\<langle>\<langle>rr,s0\<rangle>,\<langle>Init(yl),t`\<langle>s,Last(yl)\<rangle>\<rangle>\<rangle>\<in>?rD^*"
          proof(cases "rr=yl \<and> s=s0")
            case True
            with stepD show ?thesis using r_into_rtrancl by auto
          next
            case False
            with rc(4) have "\<langle>\<langle>rr,s0\<rangle>,\<langle>yl,s\<rangle>\<rangle>\<in>?rD^*" by auto
            with stepD show ?thesis using rtrancl_into_rtrancl by auto
          qed
          from rc(1,2,3) run2 xe show ?thesis by blast
        qed
      qed
      show "\<forall>r' Q'. z=\<langle>r',Q'\<rangle> \<longrightarrow> start_eNFSA_inv(S,s0,t,F,\<Sigma>,w,r',Q')"
      proof(intro allI impI)
        fix r' Q' assume zz:"z=\<langle>r',Q'\<rangle>"
        with yz(4) have e:"r'=Init(yl)" "Q'=\<epsilon>-cl(?SS,?tc,\<Sigma>,?U)" by auto
        have "\<forall>x\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Q'). (x=S \<and> r'=w) \<or> (x\<in>S \<and> start_eNFSA_wit(S,s0,t,F,\<Sigma>,w,r',x))"
        proof(rule ballI)
          fix x assume x:"x\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Q')"
          with e(2) idem have xU:"x\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,?U)" by auto
          from start_eNFSA_cl_upper[OF fin A US xU] have xcases:"x\<in>?U \<or> (x=s0 \<and> ?U\<inter>F\<noteq>0)" by auto
          then show "(x=S \<and> r'=w) \<or> (x\<in>S \<and> start_eNFSA_wit(S,s0,t,F,\<Sigma>,w,r',x))"
          proof
            assume xu:"x\<in>?U"
            then obtain s where s:"s\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Qy)" "x\<in>?tc`\<langle>s,Last(yl)\<rangle>" by auto
            have exx:"\<exists>rr\<in>Lists(\<Sigma>). \<exists>c\<in>?Ls. w=Concat(rr,c) \<and> \<langle>\<langle>rr,s0\<rangle>,\<langle>Init(yl),x\<rangle>\<rangle>\<in>?rD^*"
              using bspec[OF bspec[OF ext s(1)] s(2)] by auto
            then obtain rr c where rc:"rr\<in>Lists(\<Sigma>)" "c\<in>?Ls" "w=Concat(rr,c)"
              "\<langle>\<langle>rr,s0\<rangle>,\<langle>Init(yl),x\<rangle>\<rangle>\<in>?rD^*" by auto
            have d4:"(rr=r' \<and> x=s0) \<or> \<langle>\<langle>rr,s0\<rangle>,\<langle>r',x\<rangle>\<rangle>\<in>?rD^*" using rc(4) e(1) by auto
            have "start_eNFSA_wit(S,s0,t,F,\<Sigma>,w,r',x)"
              using start_eNFSA_wit_intro[OF rc(1,2,3) d4] by auto
            moreover from xu US have "x\<in>S" by auto
            ultimately show ?thesis by auto
          next
            assume xs:"x=s0 \<and> ?U\<inter>F\<noteq>0"
            then have "\<exists>f. f\<in>(?U\<inter>F)" by blast
            then obtain f where f:"f\<in>?U" "f\<in>F" by auto
            then obtain s where s:"s\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Qy)" "f\<in>?tc`\<langle>s,Last(yl)\<rangle>" by auto
            have exx:"\<exists>rr\<in>Lists(\<Sigma>). \<exists>c\<in>?Ls. w=Concat(rr,c) \<and> \<langle>\<langle>rr,s0\<rangle>,\<langle>Init(yl),f\<rangle>\<rangle>\<in>?rD^*"
              using bspec[OF bspec[OF ext s(1)] s(2)] by auto
            then obtain rr c where rc:"rr\<in>Lists(\<Sigma>)" "c\<in>?Ls" "w=Concat(rr,c)"
              "\<langle>\<langle>rr,s0\<rangle>,\<langle>Init(yl),f\<rangle>\<rangle>\<in>?rD^*" by auto
            have cL:"c\<in>Lists(\<Sigma>)" using rc(2) star_def fin langL by auto
            have "\<exists>j\<in>Lists(\<Sigma>). rr=Concat(Init(yl),j)"
              using DetFinStateAuto.list_prefix_split[OF D rc(4)] by auto
            then obtain j where j:"j\<in>Lists(\<Sigma>)" "rr=Concat(Init(yl),j)" by auto
            have jL:"j\<in>?L\<union>{0}"
            proof(cases "j=0")
              case True
              then show ?thesis by auto
            next
              case False
              from j(1) False have jNE:"j\<in>NELists(\<Sigma>)" using non_zero_List_func_is_NEList by auto
              from rc(4) j(2) have rj:"\<langle>\<langle>Concat(Init(yl),j),s0\<rangle>,\<langle>Init(yl),f\<rangle>\<rangle>\<in>?rD^*" by auto
              from DetFinStateAuto.dfa_run_suffix[OF D InitL jNE rj]
              have "\<langle>\<langle>j,s0\<rangle>,\<langle>0,f\<rangle>\<rangle>\<in>?rD^*" by auto
              then have "j <-D (S,s0,t,F){in alphabet}\<Sigma>"
                unfolding DFSASatisfy_def[OF fin A j(1)] using f(2) by auto
              with j(1) show ?thesis by auto
            qed
            have c':"Concat(j,c)\<in>?Ls" using star_prepend[OF fin langL jL rc(2)] by auto
            have assoc:"Concat(Concat(Init(yl),j),c) = Concat(Init(yl),Concat(j,c))"
              using concat_assoc_lists[OF InitL j(1) cL] by auto
            from rc(3) j(2) assoc have wsplit:"w=Concat(Init(yl),Concat(j,c))" by auto
            have d4:"(Init(yl)=r' \<and> x=s0) \<or> \<langle>\<langle>Init(yl),s0\<rangle>,\<langle>r',x\<rangle>\<rangle>\<in>?rD^*" using e(1) xs by auto
            have "start_eNFSA_wit(S,s0,t,F,\<Sigma>,w,r',x)"
              using start_eNFSA_wit_intro[OF InitL c' wsplit d4] by auto
            moreover from xs s0S have "x\<in>S" by auto
            ultimately show ?thesis by auto
          qed
        qed
        moreover from e(2) clU have "Q'\<in>Pow(?SS)" by auto
        ultimately show "start_eNFSA_inv(S,s0,t,F,\<Sigma>,w,r',Q')" unfolding start_eNFSA_inv_def by auto
      qed
    qed
    from claim have finInv:"start_eNFSA_inv(S,s0,t,F,\<Sigma>,w,0,Q)" by auto
    from Q(2) have "\<exists>e. e\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Q)\<inter>(F\<union>{S})" by auto
    then obtain e where e:"e\<in>\<epsilon>-cl(?SS,?tc,\<Sigma>,Q)" "e\<in>F\<union>{S}" by auto
    from finInv e(1) have "(e=S \<and> 0=w) \<or> (e\<in>S \<and> start_eNFSA_wit(S,s0,t,F,\<Sigma>,w,0,e))"
      unfolding start_eNFSA_inv_def by auto
    with wne SnotS e(2) have W:"start_eNFSA_wit(S,s0,t,F,\<Sigma>,w,0,e)" and eF:"e\<in>F" by auto
    from W obtain rr c where rc:"rr\<in>Lists(\<Sigma>)" "c\<in>?Ls" "w=Concat(rr,c)"
      "(rr=0 \<and> e=s0) \<or> \<langle>\<langle>rr,s0\<rangle>,\<langle>0,e\<rangle>\<rangle>\<in>?rD^*"
      unfolding start_eNFSA_wit_def by auto
    have rrL:"rr\<in>?L\<union>{0}"
    proof(cases "rr=0")
      case True
      then show ?thesis by auto
    next
      case False
      with rc(4) have "\<langle>\<langle>rr,s0\<rangle>,\<langle>0,e\<rangle>\<rangle>\<in>?rD^*" by auto
      then have "rr <-D (S,s0,t,F){in alphabet}\<Sigma>"
        unfolding DFSASatisfy_def[OF fin A rc(1)] using eF by auto
      with rc(1) show ?thesis by auto
    qed
    show ?thesis using star_prepend[OF fin langL rrL rc(2)] rc(3) by auto
  qed
qed

text\<open>The main result: the language accepted by start-eNFSA is the Kleene star of the language
  accepted by the DFSA.\<close>

theorem start_eNFSA_lang_eq_star:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  shows "{w\<in>Lists(\<Sigma>). w <-\<epsilon>-N (start_eNFSA_states(S),S,start_eNFSA_trans(S,s0,t,F,\<Sigma>),F\<union>{S}){in alphabet}\<Sigma>}
    = ({u\<in>Lists(\<Sigma>). u <-D (S,s0,t,F){in alphabet}\<Sigma>}*\<^sup>\<Sigma>)"
proof
  show "{w\<in>Lists(\<Sigma>). w <-\<epsilon>-N (start_eNFSA_states(S),S,start_eNFSA_trans(S,s0,t,F,\<Sigma>),F\<union>{S}){in alphabet}\<Sigma>}
    \<subseteq> ({u\<in>Lists(\<Sigma>). u <-D (S,s0,t,F){in alphabet}\<Sigma>}*\<^sup>\<Sigma>)"
    using eNFSA_lang_subset_star[OF assms] by auto
  show "({u\<in>Lists(\<Sigma>). u <-D (S,s0,t,F){in alphabet}\<Sigma>}*\<^sup>\<Sigma>) \<subseteq>
    {w\<in>Lists(\<Sigma>). w <-\<epsilon>-N (start_eNFSA_states(S),S,start_eNFSA_trans(S,s0,t,F,\<Sigma>),F\<union>{S}){in alphabet}\<Sigma>}"
    using star_subset_eNFSA_lang[OF assms] by auto
qed

text\<open>As a consequence, the Kleene star of the language of a DFSA is a regular language.\<close>

corollary star_language_is_regular:
  assumes "Finite(\<Sigma>)" "(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
  shows "({u\<in>Lists(\<Sigma>). u <-D (S,s0,t,F){in alphabet}\<Sigma>}*\<^sup>\<Sigma>) {is a regular language on}\<Sigma>"
proof-
  have valid:"(start_eNFSA_states(S),S,start_eNFSA_trans(S,s0,t,F,\<Sigma>),F\<union>{S}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using start_eNFSA_valid[OF assms] by auto
  have "{w\<in>Lists(\<Sigma>). w <-\<epsilon>-N (start_eNFSA_states(S),S,start_eNFSA_trans(S,s0,t,F,\<Sigma>),F\<union>{S}){in alphabet}\<Sigma>}
    {is a regular language on}\<Sigma>"
    using epsilonNFSA_lang_is_regular[OF assms(1) valid] by auto
  then show ?thesis using start_eNFSA_lang_eq_star[OF assms] by auto
qed

text\<open>The Kleene star of a regular language is regular.\<close>

corollary regular_star:
  assumes "Finite(\<Sigma>)" "L{is a regular language on}\<Sigma>"
  shows "(L*\<^sup>\<Sigma>) {is a regular language on}\<Sigma>"
proof-
  from assms obtain S s0 t F where A:"(S,s0,t,F){is an DFSA for alphabet}\<Sigma>"
    and "L=DetFinStateAuto.LanguageDFSA(S,s0,t,F,\<Sigma>)"
    using IsRegularLanguage_def[OF assms(1)] by auto
  then have "L={u\<in>Lists(\<Sigma>). u <-D (S,s0,t,F){in alphabet}\<Sigma>}" by auto
  moreover have "({u\<in>Lists(\<Sigma>). u <-D (S,s0,t,F){in alphabet}\<Sigma>}*\<^sup>\<Sigma>) {is a regular language on}\<Sigma>"
    using star_language_is_regular[OF assms(1) A] by auto
  ultimately show ?thesis by auto
qed

end
