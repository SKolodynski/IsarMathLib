(*
    This file is a part of IsarMathLib -
    a library of formalized mathematics written for Isabelle/Isar.

    Copyright (C) 2023 Daniel de la Concepcion

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

section \<open>Formal languages\<close>

theory Finite_State_Machines_ZF imports FiniteSeq_ZF Finite1 ZF.CardinalArith

begin

subsection\<open>Introduction\<close>

text\<open>This file deals with finite state machines. The goal
is to define regular languages and show that they are closed
by finite union, finite intersection, complements and
concatenation.

We show that the languages defined by deterministic, non-deterministic
and non-deterministic with $\epsilon$ moves are equivalent.\<close>

text\<open>First, a transitive closure variation on @{thm rtrancl_unfold}.\<close>

theorem rtrancl_rev:
  shows "r^* = id(field(r)) \<union> (r^* O r)"
proof-
  have "converse(r)^* = id(field(converse(r))) \<union> (converse(r) O converse(r)^*)"
    using rtrancl_unfold[of "converse(r)"] by auto
  then have "converse(r^*) = id(field(r)) \<union> (converse(r) O converse(r^*))"
    using rtrancl_converse by auto
  then have "converse(r^*) = id(field(r)) \<union> (converse(r^* O r))"
    using converse_comp by auto moreover
  {
    fix t assume t:"t\<in>id(field(r)) \<union> (converse(r^* O r))"
    {
      assume "t\<in>id(field(r))"
      then have "t\<in>converse(id(field(r)) \<union> (r^* O r))" by auto
    } moreover
    {
      assume "t\<notin>id(field(r))"
      with t have "t\<in>converse(r^* O r)" by auto
      then have "t\<in>converse(id(field(r)) \<union> (r^* O r))" by auto
    }
    ultimately have "t\<in>converse(id(field(r)) \<union> (r^* O r))" by auto
  }
  moreover
  {
    fix t assume t:"t\<in>converse(id(field(r)) \<union> (r^* O r))"
    then obtain t1 t2 where t12:"t=\<langle>t1,t2\<rangle>" "\<langle>t2,t1\<rangle>\<in>id(field(r)) \<union> (r^* O r)"
      by auto
    {
      assume "\<langle>t2,t1\<rangle>\<in>id(field(r))"
      with t12(1) have "t\<in>id(field(r))" by auto
      then have "t\<in>id(field(r)) \<union> converse(r^* O r)" by auto
    } moreover
    {
      assume "\<langle>t2,t1\<rangle>\<notin>id(field(r))"
      with t12(2) have "\<langle>t2,t1\<rangle>\<in>(r^* O r)" by auto
      with t12(1) have "t\<in>converse(r^* O r)" by auto
      then have "t\<in>id(field(r)) \<union> converse(r^* O r)" by auto
    }
    ultimately have "t\<in>id(field(r)) \<union> converse(r^* O r)" by auto
  }
  ultimately have "converse(id(field(r)) \<union> (r^* O r)) = converse(r^*)" by auto
  then have "converse(converse(id(field(r)) \<union> (r^* O r))) = r^*" using converse_converse[OF rtrancl_type]
    by auto moreover
  {
    fix t assume t:"t\<in>id(field(r)) \<union> (r^* O r)"
    {
      assume "t\<in>id(field(r))"
      then have "t:field(r)*field(r)" by auto
    } moreover
    {
      assume "t\<notin>id(field(r))"
      with t have "t\<in>r^* O r" by auto
      then have "t:field(r)*field(r)" using rtrancl_type unfolding comp_def by auto
    } ultimately
    have "t\<in>field(r)*field(r)" by auto
  }
  ultimately show ?thesis using converse_converse[of "id(field(r))\<union>(r^* O r)" "field(r)" "\<lambda>_. field(r)"] by auto
qed

text\<open>A language is a subset of words.\<close>

definition
  IsALanguage ("_{is a language with alphabet}_") where
  "Finite(\<Sigma>) \<Longrightarrow> L {is a language with alphabet} \<Sigma> \<equiv> L \<subseteq> Lists(\<Sigma>)"

text\<open>The set of all words, and the set of no words are languages.\<close>

lemma full_empty_language:
  assumes "Finite(\<Sigma>)"
  shows "Lists(\<Sigma>) {is a language with alphabet} \<Sigma>"
  and "0 {is a language with alphabet} \<Sigma>"
  unfolding IsALanguage_def[OF assms] by auto

subsection\<open>Deterministic Finite Automata\<close>

text\<open>A deterministic finite state automaton is defined
as a finite set of states, an initial state,
a transition function from state to state based on
the word and a set of final states.\<close>

definition
  DFSA ("'(_,_,_,_'){is an DFSA for alphabet}_") where
  "Finite(\<Sigma>) \<Longrightarrow> (S,s\<^sub>0,t,F){is an DFSA for alphabet}\<Sigma> \<equiv> Finite(S) \<and> s\<^sub>0 \<in> S \<and> F \<subseteq> S \<and> t:S\<times>\<Sigma> \<rightarrow> S"

text\<open>A finite automaton defines transitions on pairs of
words and states. Two pairs are transition related
if the second word is equal to the first except it is
missing the last symbol, and the second state is
generated by this symbol and the first state by way
of the transition function.\<close>

definition
  DFSAExecutionRelation ("{reduce D-relation}'(_,_'){in alphabet}_") where
  "Finite(\<Sigma>) \<Longrightarrow> (S,s\<^sub>0,t,F){is an DFSA for alphabet}\<Sigma> \<Longrightarrow>
  {reduce D-relation}(S,t){in alphabet}\<Sigma> \<equiv> {\<langle>\<langle>w,s\<rangle>,\<langle>Init(w),t`\<langle>s,Last(w)\<rangle>\<rangle>\<rangle>. \<langle>w,s\<rangle>\<in>NELists(\<Sigma>)\<times>S}"

text\<open>We define a word to be fully reducible by a finite
state automaton if in the transitive closure of the previous
relation it is related to the pair of the empty word and a final state.

Since the empty word with the initial state need not be in
@{term "field({reduce D-relation}(S,t){in alphabet}\<Sigma>)"},
we add the extra condition that @{term "\<langle>\<langle>0,s\<^sub>0\<rangle>,\<langle>0,s\<^sub>0\<rangle>\<rangle>"}
is also a valid transition.\<close>

definition
  DFSASatisfy ("_ <-D '(_,_,_,_'){in alphabet}_") where
  "Finite(\<Sigma>) \<Longrightarrow> (S,s\<^sub>0,t,F){is an DFSA for alphabet}\<Sigma> \<Longrightarrow> i\<in>Lists(\<Sigma>) \<Longrightarrow>
  i <-D (S,s\<^sub>0,t,F){in alphabet}\<Sigma> \<equiv> (\<exists>q\<in>F. \<langle>\<langle>i,s\<^sub>0\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in> ({reduce D-relation}(S,t){in alphabet}\<Sigma>)^*) \<or> (i = 0 \<and> s\<^sub>0\<in>F)"

text\<open>We define a locale for better notation\<close>

locale DetFinStateAuto =
  fixes S and s\<^sub>0 and t and F and \<Sigma>
  assumes finite_alphabet: "Finite(\<Sigma>)"

  assumes DFSA: "(S,s\<^sub>0,t,F){is an DFSA for alphabet}\<Sigma>"

text\<open>We abbreviate the reduce relation to a single symbol
within this locale.\<close>

abbreviation (in DetFinStateAuto) "r\<^sub>D" where
 "r\<^sub>D \<equiv> {reduce D-relation}(S,t){in alphabet}\<Sigma>"

text\<open>We abbreviate the full reduction condition to a single symbol
within this locale.\<close>

abbreviation (in DetFinStateAuto) reduce ("_{reduces}") where
  "i{reduces} \<equiv> i <-D (S,s\<^sub>0,t,F){in alphabet}\<Sigma>"

text\<open>Destruction lemma about deterministic finite
state automata.\<close>

lemma (in DetFinStateAuto) DFSA_dest:
  shows "s\<^sub>0\<in>S" "F\<subseteq>S" "t:S\<times>\<Sigma> \<rightarrow> S" "Finite(S)" using DFSA unfolding DFSA_def[OF finite_alphabet] by auto

text\<open>The set of words that reduce to final states forms a language.
This is by definition.\<close>

lemma (in DetFinStateAuto) DFSA_language:
  shows "{i\<in>Lists(\<Sigma>). i <-D (S,s\<^sub>0,t,F){in alphabet}\<Sigma>} {is a language with alphabet}\<Sigma>"
  unfolding IsALanguage_def[OF finite_alphabet] by auto

text\<open>Define this language as an abbreviation
to reduce terms\<close>

abbreviation (in DetFinStateAuto) LanguageDFSA
  where "LanguageDFSA \<equiv> {i\<in>Lists(\<Sigma>). i <-D (S,s\<^sub>0,t,F){in alphabet}\<Sigma>}"

text\<open>The relation is an actual relation, but even
more it is a function (hence the adjective deterministic).\<close>

lemma (in DetFinStateAuto) reduce_is_relation_function:
  shows "relation(r\<^sub>D)" "function(r\<^sub>D)" unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA]
   relation_def function_def by auto

text\<open>The relation, that is actually a function
has the following domain and range:\<close>

lemma (in DetFinStateAuto) reduce_function:
shows "r\<^sub>D:NELists(\<Sigma>)\<times>S\<rightarrow>Lists(\<Sigma>)\<times>S"
proof-
  from DFSA have T:"t:S\<times>\<Sigma> \<rightarrow> S" unfolding DFSA_def[OF finite_alphabet] by auto
  {
    fix x assume "x\<in>r\<^sub>D"
    then obtain l s where x:"l \<in> NELists(\<Sigma>)" "s \<in> S" "x = \<langle>\<langle>l,s\<rangle>,\<langle>Init(l),t`\<langle>s,Last(l)\<rangle>\<rangle>\<rangle>" unfolding
      DFSAExecutionRelation_def[OF finite_alphabet DFSA] by auto
    from x(1) have "Init(l) \<in> Lists(\<Sigma>)" using init_NElist(1) by auto moreover
    from x(1) have "Last(l) \<in> \<Sigma>" using last_type by auto
    with x(2) have "t`\<langle>s,Last(l)\<rangle> \<in> S" using apply_type[OF T] by auto
    moreover note x
    ultimately have "x\<in>(NELists(\<Sigma>)\<times>S)\<times>(Lists(\<Sigma>)\<times>S)" by auto
  }
  then have r:"r\<^sub>D\<in>Pow((NELists(\<Sigma>)\<times>S)\<times>(Lists(\<Sigma>)\<times>S))" by auto moreover
  {
    fix x assume "x\<in>NELists(\<Sigma>)\<times>S"
    then obtain l s where x:"l\<in>NELists(\<Sigma>)" "s\<in>S" "x=\<langle>l,s\<rangle>" by auto
    then have "\<langle>\<langle>l,s\<rangle>,\<langle>Init(l),t`\<langle>s,Last(l)\<rangle>\<rangle>\<rangle>\<in>r\<^sub>D" unfolding
      DFSAExecutionRelation_def[OF finite_alphabet DFSA] by auto
    with x(3) have "x\<in>domain(r\<^sub>D)" unfolding domain_def by auto
  }
  then have "NELists(\<Sigma>)\<times>S \<subseteq> domain(r\<^sub>D)" by auto moreover
  note reduce_is_relation_function(2)
  ultimately show ?thesis unfolding Pi_def by auto
qed

text\<open>The field of the relation contains all pairs
with non-empty
words, but we cannot assume that it contains all pairs.\<close>

corollary (in DetFinStateAuto) reduce_field:
shows "field(r\<^sub>D) \<subseteq> Lists(\<Sigma>)\<times>S" "NELists(\<Sigma>)\<times>S \<subseteq> field(r\<^sub>D)"
proof-
  from DFSA have T:"t:S\<times>\<Sigma> \<rightarrow> S" unfolding DFSA_def[OF finite_alphabet] by auto
  {
    fix x assume "x\<in>field(r\<^sub>D)"
    then have E:"\<exists>y. \<langle>x,y\<rangle>\<in>r\<^sub>D \<or> \<langle>y,x\<rangle>\<in>r\<^sub>D" unfolding domain_def range_def field_def by auto
    {
      assume "\<exists>y. \<langle>x,y\<rangle>\<in>r\<^sub>D"
      then have "x\<in>NELists(\<Sigma>)\<times>S" unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA]
        by auto
      then have "x\<in>Lists(\<Sigma>)\<times>S" unfolding Lists_def NELists_def by auto
    } moreover
    {
      assume "\<not>(\<exists>y. \<langle>x,y\<rangle>\<in>r\<^sub>D)"
      with E have "\<exists>y.\<langle>y,x\<rangle>\<in>r\<^sub>D" by auto
      then obtain u v where y:"u\<in>NELists(\<Sigma>)" "v\<in>S" "x=\<langle>Init(u),t`\<langle>v,Last(u)\<rangle>\<rangle>"
        unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA] by auto
      from y(1) have "Init(u) \<in> Lists(\<Sigma>)" using init_NElist(1) by auto moreover
      from y(1) have "Last(u) \<in> \<Sigma>" using last_type by auto
      with y(2) have "t`\<langle>v,Last(u)\<rangle> \<in> S" using apply_type[OF T] by auto
      moreover note y(3) ultimately have "x\<in>Lists(\<Sigma>)\<times>S" by auto
    }
    ultimately have "x\<in>Lists(\<Sigma>)\<times>S" by auto
  }
  then show "field(r\<^sub>D) \<subseteq> Lists(\<Sigma>)\<times>S" by auto
  show "NELists(\<Sigma>)\<times>S \<subseteq> field(r\<^sub>D)"
    using domain_of_fun[OF reduce_function] unfolding field_def by auto
qed

text\<open>If a word is a reduced version of an other,
then it can be encoded as a restriction.\<close>

lemma (in DetFinStateAuto) seq_is_restriction:
  fixes w s u v
  assumes "\<langle>\<langle>w,s\<rangle>,\<langle>u,v\<rangle>\<rangle>\<in>r\<^sub>D^*"
  shows "restrict(w,domain(u)) = u"
proof-
  from assms have "\<langle>w,s\<rangle>\<in>field(r\<^sub>D)" using rtrancl_field[of r\<^sub>D] relation_field_times_field[OF relation_rtrancl[of r\<^sub>D]] by auto
  then have "w\<in>Lists(\<Sigma>)" using reduce_field(1) by auto
  then obtain n where "w:n\<rightarrow>\<Sigma>" unfolding Lists_def by auto
  then have "restrict(w,n) = w" "w:n\<rightarrow>\<Sigma>" using restrict_idem unfolding Pi_def by auto
  then have base:"restrict(w,domain(w)) = w" using domain_of_fun by auto
  {
    fix y z
    assume as:"\<langle>\<langle>w, s\<rangle>, y\<rangle> \<in> r\<^sub>D^*" "\<langle>y, z\<rangle> \<in> r\<^sub>D" "restrict(w, domain(fst(y))) = fst(y)"
    from as(1) have "y:field(r\<^sub>D)"  using rtrancl_field[of r\<^sub>D] relation_field_times_field[OF relation_rtrancl[of r\<^sub>D]] by auto
    then obtain y1 y2 where y:"y=\<langle>y1,y2\<rangle>" "y1\<in>Lists(\<Sigma>)" "y2\<in>S" using reduce_field(1)
      by auto
    with as(2) have z:"z=\<langle>Init(y1),t`\<langle>y2,Last(y1)\<rangle>\<rangle>" "y1\<in>NELists(\<Sigma>)" unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA]
      by auto
    then have "fst(z) = Init(y1)" by auto
    with z(2) have S:"succ(domain(fst(z))) = domain(y1)" using init_NElist(2) by auto
    from as(3) y(1) have "restrict(w,domain(y1)) = y1" by auto
    then have "restrict(restrict(w,domain(y1)),pred(domain(y1))) = Init(y1)" unfolding Init_def by auto
    then have w:"restrict(w,domain(y1)\<inter>pred(domain(y1))) = Init(y1)" using restrict_restrict by auto
    from z(2) obtain q where q:"domain(y1) = succ(q)" "q\<in>nat" using domain_of_fun unfolding NELists_def by auto
    then have "pred(domain(y1)) \<subseteq> domain(y1)" using pred_succ_eq by auto
    then have "domain(y1) \<inter> pred(domain(y1)) = pred(domain(y1))" by auto
    with w have "restrict(w,pred(domain(y1))) = Init(y1)" by auto moreover
    from q z(2) init_props(1)[of _ y1 \<Sigma>] have "domain(Init(y1)) = pred(domain(y1))"
      using domain_of_fun[of y1 _ "\<lambda>_. \<Sigma>"] domain_of_fun[of "Init(y1)" _ "\<lambda>_. \<Sigma>"]
      unfolding NELists_def by auto ultimately
    have "restrict(w,domain(Init(y1))) = Init(y1)" by auto
    with z(1) have "restrict(w,domain(fst(z))) = fst(z)" by auto
  }
  then have reg:"\<forall>y z. \<langle>\<langle>w, s\<rangle>, y\<rangle> \<in> r\<^sub>D^* \<longrightarrow>
             (\<langle>y, z\<rangle> \<in> r\<^sub>D \<longrightarrow>
             (restrict(w, domain(fst(y))) = fst(y) \<longrightarrow>
             restrict(w, domain(fst(z))) = fst(z)))" by auto
  have "restrict(w, domain(fst(\<langle>u, v\<rangle>))) = fst(\<langle>u, v\<rangle>)"
  proof(rule rtrancl_induct[of "\<langle>w,s\<rangle>" "\<langle>u,v\<rangle>" r\<^sub>D "\<lambda>q. restrict(w,domain(fst(q))) = fst(q)"])
    from base show "restrict(w,domain(fst(\<langle>w,s\<rangle>))) = fst(\<langle>w,s\<rangle>)" by auto
    from assms show "\<langle>\<langle>w, s\<rangle>, u, v\<rangle> \<in> r\<^sub>D^*" by auto
    {
      fix y z
      assume as:"\<langle>\<langle>w, s\<rangle>, y\<rangle> \<in> r\<^sub>D^*" "\<langle>y, z\<rangle> \<in> r\<^sub>D" "restrict(w, domain(fst(y))) = fst(y)"
      from as(1) have "y:field(r\<^sub>D)"  using rtrancl_field[of r\<^sub>D] relation_field_times_field[OF relation_rtrancl[of r\<^sub>D]] by auto
      then obtain y1 y2 where y:"y=\<langle>y1,y2\<rangle>" "y1\<in>Lists(\<Sigma>)" "y2\<in>S" using reduce_field(1)
        by auto
      with as(2) have z:"z=\<langle>Init(y1),t`\<langle>y2,Last(y1)\<rangle>\<rangle>" "y1\<in>NELists(\<Sigma>)" unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA]
        by auto
      then have "fst(z) = Init(y1)" by auto
      with z(2) have S:"succ(domain(fst(z))) = domain(y1)" using init_NElist(2) by auto
      from as(3) y(1) have "restrict(w,domain(y1)) = y1" by auto
      then have "restrict(restrict(w,domain(y1)),pred(domain(y1))) = Init(y1)" unfolding Init_def by auto
      then have w:"restrict(w,domain(y1)\<inter>pred(domain(y1))) = Init(y1)" using restrict_restrict by auto
      from z(2) obtain q where q:"domain(y1) = succ(q)" "q\<in>nat" using domain_of_fun unfolding NELists_def by auto
      then have "pred(domain(y1)) \<subseteq> domain(y1)" using pred_succ_eq by auto
      then have "domain(y1) \<inter> pred(domain(y1)) = pred(domain(y1))" by auto
      with w have "restrict(w,pred(domain(y1))) = Init(y1)" by auto moreover
      from q z(2) init_props(1)[of _ y1 \<Sigma>] have "domain(Init(y1)) = pred(domain(y1))"
        using domain_of_fun[of y1 _ "\<lambda>_. \<Sigma>"] domain_of_fun[of "Init(y1)" _ "\<lambda>_. \<Sigma>"]
        unfolding NELists_def by auto ultimately
      have "restrict(w,domain(Init(y1))) = Init(y1)" by auto
      with z(1) show "restrict(w,domain(fst(z))) = fst(z)" by auto
    }
  qed
  then show ?thesis by auto
qed

lemma (in DetFinStateAuto) relation_deteministic:
  assumes "\<langle>\<langle>w,s\<rangle>,\<langle>u,v\<rangle>\<rangle>\<in>r\<^sub>D^*" "\<langle>\<langle>w,s\<rangle>,\<langle>u,m\<rangle>\<rangle>\<in>r\<^sub>D^*"
  shows "v=m"
proof-
  let ?P="\<lambda>y. \<forall>q1 q2. \<langle>\<langle>w,s\<rangle>,\<langle>q1,q2\<rangle>\<rangle>\<in>r\<^sub>D^* \<longrightarrow> fst(y) = q1 \<longrightarrow> snd(y) = q2"
  {
    fix q1 q2 assume "\<langle>\<langle>w, s\<rangle>, q1, q2\<rangle> \<in> r\<^sub>D^*" "fst(\<langle>w, ss\<rangle>) = q1"
    then have "\<langle>\<langle>w, s\<rangle>, w, q2\<rangle> \<in> r\<^sub>D^*" by auto
    then have "\<langle>\<langle>w, s\<rangle>, w, q2\<rangle> \<in> id(field(r\<^sub>D)) \<union> (r\<^sub>D^* O r\<^sub>D)" using rtrancl_rev by auto
    then have A:"s=q2 \<or> \<langle>\<langle>w, s\<rangle>, w, q2\<rangle>:(r\<^sub>D^* O r\<^sub>D)" by auto
    {
      assume "s\<noteq>q2"
      with A have "\<langle>\<langle>w, s\<rangle>, w, q2\<rangle>:(r\<^sub>D^* O r\<^sub>D)" by auto
      then obtain b where b:"\<langle>\<langle>w,s\<rangle>,b\<rangle>:r\<^sub>D" "\<langle>b,w,q2\<rangle>:r\<^sub>D^*" unfolding compE by auto
      from b(1) have "b=\<langle>Init(w),t`\<langle>s,Last(w)\<rangle>\<rangle>" and w:"w:NELists(\<Sigma>)" unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA] by auto
      with b(2) have "restrict(Init(w),domain(w)) = w" using seq_is_restriction by auto
      then have "domain(Init(w))\<inter>domain(w) = domain(w)" using domain_restrict[of "Init(w)" "domain(w)"] by auto
      with w have e:"domain(Init(w))\<inter>domain(w) = succ(domain(Init(w)))" using init_NElist(2)[of w] by auto
      {
        fix tt assume t:"tt:succ(domain(Init(w)))"
        with e have "tt:domain(Init(w))\<inter>domain(w)" by auto
        then have "tt:domain(Init(w))" by auto
      }
      then have "succ(domain(Init(w)))\<subseteq>domain(Init(w))" by auto
      then have "domain(Init(w)) \<in> domain(Init(w))" by auto
      then have False using mem_irrefl[of "domain(Init(w))"] by auto
    }
    then have "s=q2" by auto
    then have "snd(\<langle>w,s\<rangle>) = q2" by auto
  }
  then have P0:"?P(\<langle>w,s\<rangle>)" by auto
  {
    fix y z assume y:"\<langle>\<langle>w,s\<rangle>,y\<rangle>:r\<^sub>D^*" "\<langle>y,z\<rangle>:r\<^sub>D" "?P(y)"
    {
      fix q1 q2 assume z:"\<langle>\<langle>w, s\<rangle>, q1, q2\<rangle> \<in> r\<^sub>D^*" "fst(z) = q1"
      from this(1) have "\<langle>\<langle>w, s\<rangle>, q1, q2\<rangle> \<in> id(field(r\<^sub>D)) \<union> (r\<^sub>D O r\<^sub>D^*)" using rtrancl_unfold by auto
      then have A:"(s=q2 \<and> w=q1) \<or> \<langle>\<langle>w, s\<rangle>, q1, q2\<rangle>:(r\<^sub>D O r\<^sub>D^*)" by auto
      from y(2) obtain y1 y2 where zz:"y=\<langle>y1,y2\<rangle>" "y1:NELists(\<Sigma>)" "y2\<in>S" "z=\<langle>Init(y1),t`\<langle>y2,Last(y1)\<rangle>\<rangle>"
        unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA] by auto
      {
        assume w:"w=q1"
        with z(2) zz(4) have "w=Init(y1)" by auto
        with y(1) zz(1) have "restrict(Init(y1),domain(y1)) = y1" using seq_is_restriction
          by auto
        then have "domain(Init(y1))\<inter>domain(y1) = domain(y1)" using domain_restrict[of "Init(y1)" "domain(y1)"] by auto
        with zz(2) have e:"domain(Init(y1))\<inter>domain(y1) = succ(domain(Init(y1)))" using init_NElist(2)[of y1] by auto
        {
          fix tt assume t:"tt:succ(domain(Init(y1)))"
          with e have "tt:domain(Init(y1))\<inter>domain(y1)" by auto
          then have "tt:domain(Init(y1))" by auto
        }
        then have "succ(domain(Init(y1)))\<subseteq> domain(Init(y1))" by auto
        then have "domain(Init(y1)) \<in> domain(Init(y1))" by auto
        then have False using mem_irrefl[of "domain(Init(y1))"] by auto
      }
      with A have "\<langle>\<langle>w, s\<rangle>, q1, q2\<rangle>:(r\<^sub>D O r\<^sub>D^*)" by auto
      then obtain pp where pp:"\<langle>\<langle>w, s\<rangle>, pp\<rangle>:r\<^sub>D^*" "\<langle>pp, q1, q2\<rangle>:r\<^sub>D" unfolding compE by auto
      from this(2) obtain ppL ppS where ppl:"ppL:NELists(\<Sigma>)" "ppS\<in>S" "pp=\<langle>ppL,ppS\<rangle>"
        "q1=Init(ppL)" "q2=t`\<langle>ppS,Last(ppL)\<rangle>" unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA] by auto
      from this(3) pp(1) have rr:"restrict(w,domain(ppL)) = ppL" using seq_is_restriction by auto
      then have r:"restrict(w,domain(ppL))`pred(domain(ppL)) = Last(ppL)" unfolding Last_def by auto
      from ppl(1) obtain q where q:"ppL:succ(q) \<rightarrow> \<Sigma>" "q\<in>nat" unfolding NELists_def by blast
      from q(1) have D:"domain(ppL) = succ(q)" using func1_1_L1[of ppL] by auto moreover
      from D have "pred(domain(ppL)) = q" using pred_succ_eq by auto
      then have "pred(domain(ppL)) \<in> succ(q)" by auto
      ultimately have "pred(domain(ppL)) \<in> domain(ppL)" by auto
      with restrict r have W:"w`pred(domain(ppL)) = Last(ppL)" by auto
      from y(1) zz(1) have "restrict(w,domain(y1)) = y1" using seq_is_restriction by auto
      moreover note rr moreover
      from q have "Init(ppL):q \<rightarrow> \<Sigma>" using init_props(1) by auto
      then have DInit:"domain(Init(ppL)) = q" using func1_1_L1 by auto
      from zz(4) z(2) have "q1=Init(y1)" by auto
      with ppl(4) have "Init(ppL) = Init(y1)" by auto
      with DInit have Dy1:"domain(Init(y1)) = q" by auto
      from zz(2) obtain o where o:"o\<in>nat" "y1:succ(o) \<rightarrow> \<Sigma>" unfolding NELists_def by auto
      then have "Init(y1):o\<rightarrow>\<Sigma>" using init_props(1) by auto
      with Dy1 have "q=o" using func1_1_L1 by auto
      with o(2) have "y1:succ(q)\<rightarrow>\<Sigma>" by auto moreover
      note q(1) ultimately have "y1=ppL" using func1_1_L1 by auto moreover
      then have "fst(y) = ppL" using zz(1) by auto
      with y(3) pp(1) ppl(3) have "snd(y) = ppS" by auto
      with zz(1) have "y2= ppS" by auto moreover
      note zz(4) ultimately have "z=\<langle>Init(ppL),t`\<langle>ppS,Last(ppL)\<rangle>\<rangle>" by auto
      then have "snd(z) = t`\<langle>ppS,Last(ppL)\<rangle>" by auto
      with ppl(5) have "snd(z) = q2" by auto
    }
    then have "?P(z)" by auto
  }
  then have R:"\<And>y z. \<langle>\<langle>w,s\<rangle>,y\<rangle>\<in>r\<^sub>D^* \<Longrightarrow> \<langle>y,z\<rangle>\<in>r\<^sub>D \<Longrightarrow> ?P(y) \<Longrightarrow> ?P(z)" by auto
  then have "?P(\<langle>u,v\<rangle>)" using rtrancl_induct[of "\<langle>w,s\<rangle>" "\<langle>u,v\<rangle>" r\<^sub>D "\<lambda>y. \<forall>q1 q2. \<langle>\<langle>w,s\<rangle>,\<langle>q1,q2\<rangle>\<rangle>:r\<^sub>D^* \<longrightarrow> fst(y) = q1 \<longrightarrow> snd(y) = q2"]
    P0 assms(1) by auto
  then show ?thesis using assms(2) by auto
qed

text\<open>Any non-empty word can be reduced to the empty
string, but it does not always end in a final state.\<close>

lemma (in DetFinStateAuto) endpoint_exists:
  assumes "w\<in>NELists(\<Sigma>)"
  shows "\<exists>q \<in> S. \<langle>\<langle>w,s\<^sub>0\<rangle>,\<langle>0,q\<rangle>\<rangle> \<in> r\<^sub>D^*"
proof-
  let ?P="\<lambda>k. \<forall>y\<in>Lists(\<Sigma>). domain(y) = k \<longrightarrow> y=0 \<or> (\<forall>ss\<in>S. (\<exists>q\<in>S. \<langle>\<langle>y,ss\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>r\<^sub>D^*))"
  {
    fix y assume "y\<in>Lists(\<Sigma>)" "domain(y) = 0"
    with assms have "y=0" unfolding Lists_def using domain_of_fun by auto
    then have "y=0 \<or> (\<forall>ss\<in>S. (\<exists>q\<in>S. \<langle>\<langle>y,ss\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>r\<^sub>D^*))" by auto
  }
  then have base:"?P(0)" by auto
  {
    fix k assume hyp:"?P(k)" "k\<in>nat"
    {
      fix y assume as:"y\<in>Lists(\<Sigma>)" "domain(y) = succ(k)"
      from as have "y:succ(k)\<rightarrow>\<Sigma>" unfolding Lists_def using domain_of_fun by auto
      with hyp(2) have y:"y:NELists(\<Sigma>)" unfolding NELists_def by auto
      then have "Init(y):Lists(\<Sigma>)" "succ(domain(Init(y))) = domain(y)" using init_NElist by auto
      with as(2) have D:"Init(y):Lists(\<Sigma>)" "domain(Init(y)) = k" using pred_succ_eq by auto
      with hyp(1) have d:"Init(y) = 0 \<or> (\<forall>ss\<in>S. (\<exists>q\<in>S. \<langle>\<langle>Init(y),ss\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>r\<^sub>D^*))" by auto
      {
        assume iy0:"Init(y) = 0"
        {
          fix ss assume "ss\<in>S"
          with iy0 y have "\<langle>\<langle>y,ss\<rangle>,0,t`\<langle>ss,Last(y)\<rangle>\<rangle>\<in>r\<^sub>D" unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA]
            by auto
          then have "\<langle>\<langle>y,ss\<rangle>,0,t`\<langle>ss,Last(y)\<rangle>\<rangle>\<in>r\<^sub>D^*" using r_into_rtrancl by auto
          moreover from `ss\<in>S` have "t`\<langle>ss,Last(y)\<rangle> \<in>S" using apply_type[OF DFSA_dest(3)]
            last_type[OF y] by auto
          ultimately have "\<exists>q\<in>S. \<langle>\<langle>y,ss\<rangle>,0,q\<rangle>:r\<^sub>D^*" by auto
        }
        then have "\<forall>ss\<in>S. \<exists>q\<in>S. \<langle>\<langle>y,ss\<rangle>,0,q\<rangle>:r\<^sub>D^*" by auto
        then have "y = 0 \<or> (\<forall>ss\<in>S. \<exists>q\<in>S. \<langle>\<langle>y,ss\<rangle>,0,q\<rangle>:r\<^sub>D^*)" by auto
      } moreover
      {
        assume qS:"\<forall>ss\<in>S. \<exists>q\<in>S. \<langle>\<langle>Init(y),ss\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>r\<^sub>D^*"
        {
          fix ss assume "ss\<in>S"
          with y have "\<langle>\<langle>y,ss\<rangle>,Init(y),t`\<langle>ss,Last(y)\<rangle>\<rangle>\<in>r\<^sub>D" unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA]
            by auto
          moreover from `ss\<in>S` y have "t`\<langle>ss,Last(y)\<rangle> \<in>S" using apply_type[OF DFSA_dest(3)]
            last_type by auto
          with qS have "\<exists>q\<in>S. \<langle>\<langle>Init(y),t`\<langle>ss,Last(y)\<rangle>\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>r\<^sub>D^*" by auto
          then obtain q where "q\<in>S" "\<langle>\<langle>Init(y),t`\<langle>ss,Last(y)\<rangle>\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>r\<^sub>D^*" by auto
          ultimately have "\<langle>\<langle>y,ss\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>r\<^sub>D^*" "q\<in>S" using rtrancl_into_trancl2
            trancl_into_rtrancl by auto
          then have "\<exists>q\<in>S. \<langle>\<langle>y,ss\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>r\<^sub>D^*" by auto
        }
        then have "y = 0 \<or> (\<forall>ss\<in>S. \<exists>q\<in>S. \<langle>\<langle>y,ss\<rangle>,0,q\<rangle>:r\<^sub>D^*)"  by auto
      } ultimately
      have "y = 0 \<or> (\<forall>ss\<in>S. \<exists>q\<in>S. \<langle>\<langle>y,ss\<rangle>,0,q\<rangle>:r\<^sub>D^*)" using d by auto
    }
    then have "?P(succ(k))" by auto
  }
  then have ind:"\<And>k. k\<in>nat \<Longrightarrow> ?P(k) \<Longrightarrow> ?P(succ(k))" by blast
  have dom:"domain(w) \<in> nat" using assms unfolding NELists_def using domain_of_fun by auto
  from ind have "?P(domain(w))" using nat_induct[of _ ?P, OF dom base] by auto
  with assms have "(\<forall>ss\<in>S. \<exists>q\<in>S. \<langle>\<langle>w, ss\<rangle>, 0, q\<rangle> \<in> r\<^sub>D^*)"
    using non_zero_List_func_is_NEList by auto
  then show ?thesis using DFSA_dest(1) by auto
qed


text\<open>Example of Finite Automaton of binary lists
starting with $0$ and ending with $1$\<close>

locale ListFrom0To1
begin

text\<open>Empty state\<close>

definition empty where
  "empty \<equiv> 2"

text\<open>The string starts with $0$ state\<close>

definition ends0 where
  "ends0 \<equiv> succ(2)"

text\<open>The string ends with $1$ state\<close>

definition starts1 where
  "starts1 \<equiv> 1"

text\<open>The string ends with $0$ state\<close>

definition starts0 where
  "starts0 \<equiv> 0"

text\<open>The states are the previous 4 states.
They are encoded as natural numbers to make
it easier to reason about them, and as human
readable variable names to make it easier to
understand.\<close>

definition states where
  "states \<equiv> {empty, starts0, starts1, ends0}"

text\<open>The final state is @{term starts0}\<close>

definition finalStates where
"finalStates \<equiv> {starts0}"

text\<open>The transition function is defined as follows:

From the @{term empty} state,
we transition to state @{term starts1} in case there is a $1$
and to state @{term ends0} in case there is a $0$.

From the state @{term ends0} we stay in it.

From the states @{term starts1} and @{term starts0}
we transition to @{term starts0} in case there is a $0$,
 and to @{term starts1} in case there is a $1$.\<close>

definition transFun where
"transFun \<equiv> {\<langle>\<langle>empty,1\<rangle>,starts1\<rangle>,\<langle>\<langle>empty,0\<rangle>,ends0\<rangle>}\<union>
               {\<langle>\<langle>ends0,x\<rangle>,ends0\<rangle>. x\<in>2}\<union>
               {\<langle>\<langle>starts1,0\<rangle>,starts0\<rangle>,\<langle>\<langle>starts1,1\<rangle>,starts1\<rangle>,
                \<langle>\<langle>starts0,0\<rangle>,starts0\<rangle>,\<langle>\<langle>starts0,1\<rangle>,starts1\<rangle>}"

text\<open>Add lemmas to simplify\<close>

lemmas from0To1[simp] = states_def empty_def transFun_def finalStates_def
ends0_def starts1_def starts0_def

text\<open>Interpret the example as a deterministic finite state automaton\<close>

interpretation dfsaFrom0To1: DetFinStateAuto states empty transFun finalStates 2 unfolding DetFinStateAuto_def apply safe
  using Finite_0 apply simp
proof-
  have finA:"Finite(2)" using nat_into_Finite[of 2] by auto
  have finS:"Finite(states)" using nat_into_Finite by auto
  moreover have funT:"transFun:states\<times>2 \<rightarrow> states" unfolding Pi_def function_def by auto
  moreover have "finalStates \<subseteq> states" by auto
  moreover have "empty\<in> states" by auto
  ultimately show "(states,empty,transFun,finalStates){is an DFSA for alphabet}2"
    unfolding DFSA_def[OF finA] by auto
qed

text\<open>Abbreviate the relation to something
readable.\<close>

abbreviation r0to1 ("r{0.*1}") where
  "r{0.*1} \<equiv> dfsaFrom0To1.r\<^sub>D"

text\<open>If a word reaches the state @{term starts0},
it does not move from it.\<close>

lemma invariant_state_3:
  fixes w u y
  assumes "\<langle>\<langle>w,ends0\<rangle>,\<langle>u,y\<rangle>\<rangle>\<in>r{0.*1}^*"
  shows "y = ends0"
proof-
  have finA:"Finite(2)" by auto
  have funT:"transFun:states\<times>2\<rightarrow> states"
    using dfsaFrom0To1.DFSA_dest(3) .
  have "snd(\<langle>u,y\<rangle>) = ends0"
  proof(rule rtrancl_induct[of "\<langle>w,ends0\<rangle>"
        "\<langle>u,y\<rangle>" "r{0.*1}" "\<lambda>t. snd(t) = ends0"])
    show "snd(\<langle>w, ends0\<rangle>) = ends0" by auto
    from assms show "\<langle>\<langle>w, ends0\<rangle>, u, y\<rangle> \<in> r{0.*1}^*" .
    {
      fix y z assume as:"\<langle>\<langle>w, ends0\<rangle>, y\<rangle> \<in> r{0.*1}^*" "\<langle>y, z\<rangle> \<in> r{0.*1}" "snd(y) = ends0"
      from as(3,2) obtain y1 where yy:"y=\<langle>y1,ends0\<rangle>" "y1\<in>NELists(2)"
        "z=\<langle>Init(y1),transFun`\<langle>ends0,Last(y1)\<rangle>\<rangle>"
        unfolding DFSAExecutionRelation_def[OF finA dfsaFrom0To1.DFSA]
        by auto
      from yy(2) have "Last(y1)\<in>2" using last_type by auto
      then have "\<langle>\<langle>ends0,Last(y1)\<rangle>,ends0\<rangle>\<in>transFun" by auto
      then have "transFun`\<langle>ends0,Last(y1)\<rangle> = ends0"
        using apply_equality[OF _ funT, of _ ends0] by auto
      with yy(3) have "z=\<langle>Init(y1),ends0\<rangle>" by auto
      then show "snd(z) = ends0" by auto
    }
  qed
  then show ?thesis by auto
qed

text\<open>If the string starts in $0$ and has
reached states @{term starts0} or @{term starts1};
then it reduces to @{term starts0}.\<close>

lemma invariant_state_0_1:
  fixes w
  assumes "w\<in>NELists(2)" "w`0 = 0"
  shows "\<langle>\<langle>w,starts0\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*" "\<langle>\<langle>w,starts1\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*"
proof-
  from assms(1) obtain n where w:"n:nat" "w:succ(n)\<rightarrow>2" unfolding NELists_def by auto
  then have dom:"domain(w)\<in>nat" using domain_of_fun by auto
  {
    fix q assume "q\<in>NELists(2)"
    then obtain m where "m\<in>nat" "q:succ(m)\<rightarrow>2" unfolding NELists_def by auto
    then have "domain(q)\<noteq>0" using domain_of_fun by auto
  }
  then have base:"\<forall>w. w \<in> NELists(2) \<and> w`0 = 0 \<and> domain(w) = 0 \<longrightarrow>
        \<langle>\<langle>w, starts0\<rangle>, 0, starts0\<rangle> \<in> r{0.*1}^* \<and> \<langle>\<langle>w, starts1\<rangle>, 0, starts0\<rangle> \<in> r{0.*1}^*" by auto
  from w(2) have domN0:"domain(w)\<noteq> 0" using domain_of_fun by auto
  have finA:"Finite(2)" using nat_into_Finite[of 2] by auto
  have funT:"transFun:states\<times>2\<rightarrow>states" unfolding Pi_def function_def by auto
  have t00:"transFun`\<langle>starts0,0\<rangle> = starts0" using funT apply_equality[of "\<langle>starts0,0\<rangle>" starts0 transFun "states\<times>2" "\<lambda>_. states"] by auto
  have t01:"transFun`\<langle>starts1,0\<rangle> = starts0" using funT apply_equality[of "\<langle>starts1,0\<rangle>" starts0 transFun "states\<times>2" "\<lambda>_. states"] by auto
  have t10:"transFun`\<langle>starts0,1\<rangle> = starts1" using funT apply_equality[of "\<langle>starts0,1\<rangle>" starts1 transFun "states\<times>2" "\<lambda>_. states"] by auto
  have t11:"transFun`\<langle>starts1,1\<rangle> = starts1" using funT apply_equality[of "\<langle>starts1,1\<rangle>" starts1 transFun "states\<times>2" "\<lambda>_. states"] by auto
  {
    fix ka assume kaNat:"ka:nat"
    assume k:"\<forall>w. w \<in> NELists(2) \<and> w`0 = 0 \<and> domain(w) = ka \<longrightarrow> (\<langle>\<langle>w,starts0\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^* \<and> \<langle>\<langle>w,starts1\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*)"
    {
      fix y assume y:"y\<in>NELists(2)" "y`0 = 0" "domain(y) = succ(ka)"
      from y(1) obtain s where s:"y:succ(s)\<rightarrow>2" "s\<in>nat" unfolding NELists_def by auto
      then have L:"Last(y) = y`s" using last_seq_elem by auto
      then have last_2:"Last(y) \<in> 2" using apply_type[OF s(1), of s] by auto
      {
        assume ka:"ka =0"
        with y(3) have "pred(domain(y)) = 0" using pred_succ_eq by auto
        then have y00:"y`0 = 0" using y(2) unfolding Last_def by auto
        then have "\<langle>\<langle>y,starts0\<rangle>,\<langle>Init(y),transFun`\<langle>starts0,Last(y)\<rangle>\<rangle>\<rangle>\<in>r{0.*1}" unfolding
          DFSAExecutionRelation_def[OF finA dfsaFrom0To1.DFSA]
          using y(1) by auto
        with last_2 t00 t10 have "\<langle>\<langle>y,starts0\<rangle>,\<langle>Init(y),Last(y)\<rangle>\<rangle>\<in>r{0.*1}" by auto moreover
        from ka y(3) s(1) have "Init(y):0\<rightarrow>2" using init_props(1)[OF s(2,1)]
          domain_of_fun[OF s(1)] by auto
        then have y0:"Init(y) = 0" unfolding Pi_def by auto moreover
        from ka s(1) y(3) have "s=0" using domain_of_fun by auto
        with L have LL:"y`0 = Last(y)" by auto moreover note y(2)
        ultimately have "\<langle>\<langle>y,starts0\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}" by auto
        then have A:"\<langle>\<langle>y,starts0\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*" using r_into_rtrancl by auto
        note t01 moreover have "\<langle>\<langle>y,starts1\<rangle>,\<langle>Init(y),transFun`\<langle>starts1,Last(y)\<rangle>\<rangle>\<rangle> \<in> r{0.*1}"
          unfolding DFSAExecutionRelation_def[OF finA dfsaFrom0To1.DFSA] using y(1,2) by auto
        moreover note t11 last_2 y0 LL y(2) ultimately have "\<langle>\<langle>y,starts1\<rangle>,\<langle>0,starts0\<rangle>\<rangle> \<in> r{0.*1}" by auto
        then have B:"\<langle>\<langle>y,starts1\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*" using r_into_rtrancl by auto
        with A have "\<langle>\<langle>y,starts0\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^* \<and> \<langle>\<langle>y,starts1\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*" by auto
      } moreover
      {
        assume ka:"ka\<noteq>0"
        with kaNat obtain u where u:"ka=succ(u)" "u\<in>nat" using Nat_ZF_1_L3 by auto
        from y(3) s(1) kaNat s(2) have "s=ka" using domain_of_fun succ_inject by auto
        with u(1) have "s=succ(u)" by auto moreover
        have "Init(y):s\<rightarrow>2" using init_props(1)[OF s(2,1)].
        ultimately have yu:"Init(y):succ(u)\<rightarrow>2" by auto
        with u have "Init(y)\<in>NELists(2)" "domain(Init(y)) = ka"
          using domain_of_fun unfolding NELists_def by auto
        moreover from yu have "Init(y)`0 = 0" using init_props(2)[OF nat_succI[OF u(2)], of y 2]
          s(1) `s=succ(u)` empty_in_every_succ[OF u(2)] y(2) by auto
        moreover note k ultimately have "\<langle>\<langle>Init(y),starts0\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*"
          "\<langle>\<langle>Init(y),starts1\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*" by auto
        then have A:"\<forall>x\<in>{starts0, starts1}. \<langle>\<langle>Init(y),x\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*" by auto
        have Q:"\<langle>\<langle>y,starts0\<rangle>,\<langle>Init(y),transFun`\<langle>starts0,Last(y)\<rangle>\<rangle>\<rangle>\<in>r{0.*1}" using y(2)
          unfolding DFSAExecutionRelation_def[OF finA dfsaFrom0To1.DFSA] using y(1) by auto
        {
          assume as:"Last(y) = 0"
          with Q t00 have "\<langle>\<langle>y,starts0\<rangle>,\<langle>Init(y),starts0\<rangle>\<rangle>\<in>r{0.*1}" by auto
        } moreover
        {
          assume as:"Last(y) = 1"
          with Q t10 have "\<langle>\<langle>y,starts0\<rangle>,\<langle>Init(y),starts1\<rangle>\<rangle>\<in>r{0.*1}" by auto
        }
        moreover note last_2 ultimately have
        "(\<langle>\<langle>y,starts0\<rangle>,\<langle>Init(y),starts0\<rangle>\<rangle>\<in>r{0.*1}) \<or> (\<langle>\<langle>y,starts0\<rangle>,\<langle>Init(y),starts1\<rangle>\<rangle>\<in>r{0.*1})" by auto
        with A have B:"\<langle>\<langle>y,starts0\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*" using rtrancl_into_trancl2 trancl_into_rtrancl by auto
        have Q:"\<langle>\<langle>y,starts1\<rangle>,\<langle>Init(y),transFun`\<langle>starts1,Last(y)\<rangle>\<rangle>\<rangle>\<in>r{0.*1}" using y(2)
          unfolding DFSAExecutionRelation_def[OF finA dfsaFrom0To1.DFSA] using y(1) by auto
        {
          assume as:"Last(y) = 0"
          with Q t01 have "\<langle>\<langle>y,starts1\<rangle>,\<langle>Init(y),starts0\<rangle>\<rangle>\<in>r{0.*1}" by auto
        } moreover
        {
          assume as:"Last(y) = 1"
          with Q t11 have "\<langle>\<langle>y,starts1\<rangle>,\<langle>Init(y),starts1\<rangle>\<rangle>\<in>r{0.*1}" by auto
        }
        moreover note last_2 ultimately have
        "(\<langle>\<langle>y,starts1\<rangle>,\<langle>Init(y),starts0\<rangle>\<rangle>\<in>r{0.*1}) \<or> (\<langle>\<langle>y,starts1\<rangle>,\<langle>Init(y),starts1\<rangle>\<rangle>\<in>r{0.*1})" by auto
        with A have "\<langle>\<langle>y,starts1\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*" using rtrancl_into_trancl2 trancl_into_rtrancl by auto
        with B have rr:"\<langle>\<langle>y,starts0\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^* \<and> \<langle>\<langle>y,starts1\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*" by auto
      }
      ultimately have "\<langle>\<langle>y,starts0\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^* \<and> \<langle>\<langle>y,starts1\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*" by auto
    }
    then have "\<forall>w. w \<in> NELists(2) \<and> w`0 = 0 \<and> domain(w) = succ(ka) \<longrightarrow> (\<langle>\<langle>w,starts0\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^* \<and> \<langle>\<langle>w,starts1\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*)" by auto
  }
  then have rule:"\<forall>k\<in>nat.
       (\<forall>w. w \<in> NELists(2) \<and> w`0 = 0 \<and> domain(w) = k \<longrightarrow>
            \<langle>\<langle>w, starts0\<rangle>, 0, starts0\<rangle> \<in> r{0.*1}^* \<and> \<langle>\<langle>w, starts1\<rangle>, 0, starts0\<rangle> \<in> r{0.*1}^*) \<longrightarrow>
       (\<forall>w. w \<in> NELists(2) \<and> w`0 = 0 \<and> domain(w) = succ(k) \<longrightarrow>
            \<langle>\<langle>w, starts0\<rangle>, 0, starts0\<rangle> \<in> r{0.*1}^* \<and> \<langle>\<langle>w, starts1\<rangle>, 0, starts0\<rangle> \<in> r{0.*1}^*)" by blast
  from ind_on_nat[of "domain(w)" "\<lambda>t . \<forall>w. w\<in>NELists(2) \<and> w`0 =0 \<and> domain(w) = t \<longrightarrow> (\<langle>\<langle>w,starts0\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^* \<and> \<langle>\<langle>w,starts1\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*)", OF dom base rule]
  show R:"\<langle>\<langle>w,starts0\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*" "\<langle>\<langle>w,starts1\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*" using assms(2,1) by auto
qed

text\<open>A more readable reduction statement\<close>

abbreviation red ("_{reduces in 0.*1}") where
  "i{reduces in 0.*1} \<equiv> dfsaFrom0To1.reduce(i)"

text\<open>Any list starting with $0$ and ending in $1$
reduces.\<close>

theorem starts1ends0_DFSA_reduce:
  fixes i
  assumes "i\<in>Lists(2)" and "i`0=0" and "Last(i) = 1"
  shows "i{reduces in 0.*1}"
proof-
  from assms(1) obtain tt where t:"tt\<in>nat" "i:tt\<rightarrow>2" unfolding Lists_def by auto
  then have domNat:"domain(i) = tt" using domain_of_fun by auto
  {
    assume "domain(i) = 0" moreover
    from assms(3) have "\<Union>(i``{Arith.pred(domain(i))})=1" unfolding Last_def apply_def by auto
    then have "i\<noteq>0" by auto
    ultimately have False using t domain_of_fun by auto
  }
  with domNat t(1) obtain y where y:"domain(i) = succ(y)" "y\<in>nat" using Nat_ZF_1_L3 by auto
  with domNat t(2) have iList:"i\<in>NELists(2)" unfolding NELists_def by auto
  have finA:"Finite(2)" using nat_into_Finite[of 2] by auto
  have funT:"transFun:states\<times>2\<rightarrow>states" unfolding Pi_def function_def by auto
  have "\<langle>\<langle>i,empty\<rangle>,\<langle>Init(i),transFun`\<langle>empty,Last(i)\<rangle>\<rangle>\<rangle>:r{0.*1}" using iList unfolding
      DFSAExecutionRelation_def[OF finA dfsaFrom0To1.DFSA] by auto
  moreover have "transFun`\<langle>empty,Last(i)\<rangle> = 1" using apply_equality[OF _ funT] assms(3)
    by auto
  ultimately have U:"\<langle>\<langle>i,empty\<rangle>,\<langle>Init(i),starts1\<rangle>\<rangle>:r{0.*1}" by auto
  {
    assume "y = 0"
    with y(1) t(2) have iFun:"i:1\<rightarrow>2" using domain_of_fun by auto
    then have "i = {\<langle>0,i`0\<rangle>}" using fun_is_set_of_pairs[of i 1 2] by auto
    with assms(2) have ii:"i={\<langle>0,0\<rangle>}" by auto
    then have "\<forall>y. \<exists>x\<in>{Arith.pred(domain(i))}. \<langle>x, y\<rangle> \<in> i \<longrightarrow> y=0" by auto
    moreover from assms(3) have eq:"1 = i`pred(domain(i))" unfolding Last_def by auto
    from iFun have "domain(i) = 1" using domain_of_fun by auto
    then have "pred(domain(i)) = 0" using pred_succ_eq by auto
    then have "i`pred(domain(i)) = i`0" by auto
    with eq have "1 = i`0" by auto
    then have False using assms(2) by auto
  }
  then have "y\<noteq>0" by auto
  then obtain k where yy:"y= succ(k)" "k\<in>nat" using Nat_ZF_1_L3 y(2) by auto
  with iList y(1) have iss:"i:succ(succ(k)) \<rightarrow> 2" unfolding NELists_def using domain_of_fun by auto
  then have "Init(i):succ(k) \<rightarrow> 2" using init_props(1) nat_succI[OF yy(2)] by auto
  then have "Init(i)\<in>NELists(2)" unfolding NELists_def using yy(2) by auto moreover
  have "0\<in>succ(k)" using empty_in_every_succ yy(2) by auto
  with iss assms(2) have "Init(i)`0 = 0" using init_props(2)[of "succ(k)" i 2] nat_succI[OF yy(2)]
    by auto
  ultimately have "\<langle>\<langle>Init(i),starts1\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*" using invariant_state_0_1
    by auto
  with U have "\<langle>\<langle>i,empty\<rangle>,\<langle>0,starts0\<rangle>\<rangle>\<in>r{0.*1}^*" using rtrancl_into_trancl2[THEN trancl_into_rtrancl] by auto
  then have "\<exists>q\<in>finalStates. \<langle>\<langle>i,empty\<rangle>,\<langle>0,q\<rangle>\<rangle> \<in> r{0.*1}^*" by auto
  then show ?thesis using DFSASatisfy_def[OF finA dfsaFrom0To1.DFSA assms(1)] by auto
qed

text\<open>Any list that reduces starts with 0 and ends in 1\<close>

theorem starts1ends0_DFSA_reduce_rev:
  fixes i
  assumes "i\<in>Lists(2)" and "i {reduces in 0.*1}"
  shows "i`0=0" and "Last(i) = 1"
proof-
  have finA:"Finite(2)" using nat_into_Finite[of 2] by auto
  have funT:"transFun:states\<times>2\<rightarrow>states" unfolding Pi_def function_def by auto
  from assms(2) have "\<langle>\<langle>i,empty\<rangle>,\<langle>0,starts0\<rangle>\<rangle> \<in> r{0.*1}^*"
    unfolding DFSASatisfy_def[OF finA dfsaFrom0To1.DFSA assms(1)]
    by auto
  then have "\<langle>\<langle>i,empty\<rangle>,\<langle>0,starts0\<rangle>\<rangle> \<in> id(field(r{0.*1})) \<union> (r{0.*1} O r{0.*1}^*)" using rtrancl_unfold[of "r{0.*1}"] by auto
  then have k:"\<langle>\<langle>i,empty\<rangle>,\<langle>0,starts0\<rangle>\<rangle> \<in> id(field(r{0.*1})) \<or> \<langle>\<langle>i,empty\<rangle>,\<langle>0,starts0\<rangle>\<rangle> \<in> (r{0.*1} O r{0.*1}^*)" by auto
  have d:"domain(r{0.*1}) = NELists(2)\<times>states"
    using domainI[of _ _ "r{0.*1}"]
    unfolding DFSAExecutionRelation_def[OF finA dfsaFrom0To1.DFSA]
    by auto
  from k have "\<langle>i,empty\<rangle> = \<langle>0,starts0\<rangle> \<or> \<langle>\<langle>i,empty\<rangle>,\<langle>0,starts0\<rangle>\<rangle> \<in> (r{0.*1} O r{0.*1}^*)" using id_iff by auto
  then have "(i=0 \<and> empty=starts0) \<or> (\<langle>\<langle>i,empty\<rangle>,\<langle>0,starts0\<rangle>\<rangle> \<in> r{0.*1} O r{0.*1}^*)" by auto
  then have "\<langle>\<langle>i,empty\<rangle>,\<langle>0,starts0\<rangle>\<rangle> \<in> r{0.*1} O r{0.*1}^*" by auto
  then obtain q where q:"\<langle>q,\<langle>0,starts0\<rangle>\<rangle> \<in> r{0.*1}" "\<langle>\<langle>i,empty\<rangle>,q\<rangle>\<in>r{0.*1}^*" unfolding comp_def by auto
  from q(1) have "q \<in> domain(r{0.*1})" unfolding domain_def by auto
  with d have "q \<in> NELists(2)\<times>states" by auto
  then obtain q1 q2 where qq:"q=\<langle>q1,q2\<rangle>" "q1\<in>NELists(2)" "q2\<in>states" by auto
  from q(1) qq(1) have A:"0 = Init(q1)" "0 = transFun`\<langle>q2,Last(q1)\<rangle>"
    unfolding DFSAExecutionRelation_def[OF finA dfsaFrom0To1.DFSA] by auto
  from qq(1) q(2) have "restrict(i,domain(q1)) = q1"
    using dfsaFrom0To1.seq_is_restriction
    by auto
  then have iRes:"restrict(i,domain(q1))`0 = q1`0" by auto
  from qq(2) obtain k where k:"q1:succ(k)\<rightarrow>2" "k\<in>nat" unfolding NELists_def by auto
  then have "Init(q1):k\<rightarrow>2" using init_props(1) by auto
  with A(1) have "k=0" unfolding Pi_def by auto
  with k(1) have qfun:"q1:1\<rightarrow>2" by auto
  from qfun have q10:"Last(q1) = q1`0" unfolding Last_def using domain_of_fun by auto
  from k have "0\<in>domain(q1)" using domain_of_fun empty_in_every_succ by auto
  with iRes have "i`0 = q1`0" using restrict by auto
  from qfun have "q1`0\<in>2" using apply_type[of q1 1 "\<lambda>_. 2"] empty_in_every_succ[OF nat_0I] by auto
  with qq(3) A(2) have "\<langle>\<langle>q2,Last(q1)\<rangle>,0\<rangle> \<in> transFun" using apply_Pair[OF funT, of "\<langle>q2,Last(q1)\<rangle>"] q10 by auto
  then have "q2\<in>2" "Last(q1) = 0" by auto
  with `0\<in>domain(q1)` iRes q10 show "i`0 = 0" using restrict by auto
  from q(2) qq(1) have "\<langle>\<langle>i,empty\<rangle>,\<langle>q1,q2\<rangle>\<rangle> \<in> r{0.*1}^*" by auto
  then have "\<langle>\<langle>i,2\<rangle>,\<langle>q1,q2\<rangle>\<rangle> \<in> id(field(r{0.*1})) \<union> (r{0.*1}^* O r{0.*1})" using rtrancl_rev by auto
  moreover
  {
    assume "\<langle>\<langle>i,2\<rangle>,\<langle>q1,q2\<rangle>\<rangle> \<in> id(field(r{0.*1}))"
    then have "i=q1 \<and> q2=2" by auto
    with `q2\<in>2` have False by auto
  } ultimately
  have "\<langle>\<langle>i,2\<rangle>,\<langle>q1,q2\<rangle>\<rangle> \<in> (r{0.*1}^* O r{0.*1})" by auto
  then obtain z where z:"\<langle>\<langle>i,2\<rangle>,z\<rangle> :r{0.*1}" "\<langle>z,\<langle>q1,q2\<rangle>\<rangle>:r{0.*1}^*" unfolding comp_def by auto
  from z(2) have "z\<in>field(r{0.*1})" using rtrancl_type[of "r{0.*1}"] by auto
  then obtain z1 z2 where zz:"z=\<langle>z1,z2\<rangle>" "z1\<in>Lists(2)" "z2\<in>states" using dfsaFrom0To1.reduce_field(1)
    by blast
  from zz(1) z(1) have zzz:"z1=Init(i)" "z2=transFun`\<langle>2,Last(i)\<rangle>"
    unfolding DFSAExecutionRelation_def[OF finA dfsaFrom0To1.DFSA] by auto
  {
    assume "Last(i) = 0"
    with zzz(2) have "z2 = succ(2)" using apply_equality[OF _ funT] by auto
    with zz(1) z(2) have "q2= succ(2)" using invariant_state_3 by auto
    with `q2\<in>2` have False by auto
  }
  with z(1) show "Last(i) = 1" using last_type[of i 2]
    unfolding DFSAExecutionRelation_def[OF finA dfsaFrom0To1.DFSA]
    by auto
qed

text\<open>We conclude that this example constitutes
the language of binary strings starting in $0$
and ending in $1$\<close>

theorem determine_strings:
  shows "dfsaFrom0To1.LanguageDFSA = {i\<in>Lists(2). i`0 = 0 \<and> Last(i) = 1}"
  using starts1ends0_DFSA_reduce_rev
  starts1ends0_DFSA_reduce by blast

end

text\<open>We define the languages determined by a deterministic
finite state automaton as \textbf{regular}.\<close>

definition
  IsRegularLanguage ("_{is a regular language on}_") where
  "Finite(\<Sigma>) \<Longrightarrow> L{is a regular language on}\<Sigma> \<equiv> \<exists>S s t F. ((S,s,t,F){is an DFSA for alphabet}\<Sigma>) \<and> L=DetFinStateAuto.LanguageDFSA(S,s,t,F,\<Sigma>)"

text\<open>By definition, the language in the locale
is regular.\<close>

corollary (in DetFinStateAuto) regular_intersect:
  shows "LanguageDFSA{is a regular language on}\<Sigma>"
  using IsRegularLanguage_def finite_alphabet DFSA by auto

text\<open>A regular language is a language.\<close>

lemma regular_is_language:
  assumes "Finite(\<Sigma>)"
  and "L{is a regular language on}\<Sigma>"
  shows "L{is a language with alphabet}\<Sigma>" unfolding IsALanguage_def[OF assms(1)]
proof-
  from assms(2) obtain S s t F where "(S,s,t,F){is an DFSA for alphabet}\<Sigma>" "L=DetFinStateAuto.LanguageDFSA(S,s,t,F,\<Sigma>)"
    unfolding IsRegularLanguage_def[OF assms(1)] by auto
  then show "L\<subseteq> Lists(\<Sigma>)"
    unfolding DetFinStateAuto_def using assms(1) by auto
qed

subsection\<open>Operations on regular languages\<close>

text\<open>The intersection of two regular languages
is a regular language.\<close>

theorem regular_intersect:
  assumes "Finite(\<Sigma>)"
  and "L1{is a regular language on}\<Sigma>"
  and "L2{is a regular language on}\<Sigma>"
shows "(L1\<inter>L2) {is a regular language on}\<Sigma>"
proof-
  from assms(1,2) obtain S1 s1 t1 F1 where l1:"(S1,s1,t1,F1){is an DFSA for alphabet}\<Sigma>"
    "L1 = DetFinStateAuto.LanguageDFSA(S1,s1,t1,F1,\<Sigma>)"
    using IsRegularLanguage_def by auto
  then have l1:"(S1,s1,t1,F1){is an DFSA for alphabet}\<Sigma>"
    "L1 = {i\<in>Lists(\<Sigma>). i <-D (S1,s1,t1,F1){in alphabet}\<Sigma>}"
    using DetFinStateAuto_def assms(1) l1(1) by auto
  from assms(1,3) obtain S2 s2 t2 F2 where l2:"(S2,s2,t2,F2){is an DFSA for alphabet}\<Sigma>"
    "L2= DetFinStateAuto.LanguageDFSA(S2,s2,t2,F2,\<Sigma>)"
    using IsRegularLanguage_def by auto
  then have l2:"(S2,s2,t2,F2){is an DFSA for alphabet}\<Sigma>"
    "L2 = {i\<in>Lists(\<Sigma>). i <-D (S2,s2,t2,F2){in alphabet}\<Sigma>}"
    using DetFinStateAuto_def assms(1) l2(1) by auto
  let ?S = "S1\<times>S2"
  let ?s = "\<langle>s1,s2\<rangle>"
  let ?t = "{\<langle>\<langle>\<langle>x1,x2\<rangle>,y\<rangle>,\<langle>t1`\<langle>x1,y\<rangle>,t2`\<langle>x2,y\<rangle>\<rangle>\<rangle>. \<langle>\<langle>x1,x2\<rangle>,y\<rangle> \<in> ?S\<times>\<Sigma>}"
  let ?F = "F1\<times>F2"
  let ?r = "DetFinStateAuto.r\<^sub>D(?S,?t,\<Sigma>)"
  let ?r1 = "DetFinStateAuto.r\<^sub>D(S1,t1,\<Sigma>)"
  let ?r2 = "DetFinStateAuto.r\<^sub>D(S2,t2,\<Sigma>)"
  have D:"(?S,?s,?t,?F){is an DFSA for alphabet}\<Sigma>"
  proof-
    have A:"?s\<in>?S" using l1(1) l2(1) unfolding DFSA_def[OF assms(1)] by auto
    have B:"?F \<subseteq> ?S" using l1(1) l2(1) unfolding DFSA_def[OF assms(1)] by auto
    have "function(?t)" unfolding function_def by auto
    moreover have "?S\<times>\<Sigma> \<subseteq> domain(?t)" by auto
    moreover
    {
      fix x1 x2 y assume as:"\<langle>\<langle>x1,x2\<rangle>,y\<rangle> \<in> ?S \<times> \<Sigma>"
      then have "t1`\<langle>x1,y\<rangle>\<in>S1" "t2`\<langle>x2,y\<rangle>\<in>S2" using apply_type
        l1(1) l2(1) unfolding DFSA_def[OF assms(1)] by auto
      then have "\<langle>t1`\<langle>x1,y\<rangle>,t2`\<langle>x2,y\<rangle>\<rangle>\<in>?S" by auto
    }
    then have "{\<langle>\<langle>\<langle>x1,x2\<rangle>,y\<rangle>,\<langle>t1`\<langle>x1,y\<rangle>,t2`\<langle>x2,y\<rangle>\<rangle>\<rangle>. \<langle>\<langle>x1,x2\<rangle>,y\<rangle> \<in> (S1 \<times> S2) \<times> \<Sigma>} \<in> Pow((?S\<times>\<Sigma>)\<times>?S)" by auto
    ultimately have C:"?t:?S\<times>\<Sigma> \<rightarrow> ?S" unfolding Pi_def by auto
    have "Finite(?S)" using Finite1_L12[of S1 S2] Fin_into_Finite Finite_into_Fin
      l1(1) l2(1) unfolding DFSA_def[OF assms(1)] by auto
    with A B C show ?thesis unfolding DFSA_def[OF assms(1)] by auto
  qed
  then have DFSA0:"DetFinStateAuto(?S,?s,?t,?F,\<Sigma>)" unfolding DetFinStateAuto_def using assms(1) by auto
  have RR:"\<And>m yy zz. m\<in>NELists(\<Sigma>) \<Longrightarrow> \<langle>\<langle>m,s1,s2\<rangle>,\<langle>0,yy,zz\<rangle>\<rangle>:?r^* \<Longrightarrow> \<langle>\<langle>m,s1\<rangle>,\<langle>0,yy\<rangle>\<rangle>:?r1^* \<and> \<langle>\<langle>m,s2\<rangle>,\<langle>0,zz\<rangle>\<rangle>:?r2^*"
    proof
      fix m yy zz
      assume as:"\<langle>\<langle>m,s1,s2\<rangle>,\<langle>0,yy,zz\<rangle>\<rangle>:?r^*" "m\<in>NELists(\<Sigma>)"
      note as(2)
      moreover have "s1\<in>S1" "s2\<in>S2" using l1(1) l2(1) unfolding DFSA_def[OF assms(1)] by auto
      ultimately have "\<langle>m,s1\<rangle> : field(?r1)" "\<langle>m,s2\<rangle> : field(?r2)" using DetFinStateAuto.reduce_field(2)[of S1 s1 t1 F1 \<Sigma>] assms(1) l1(1) l2(1)
        DetFinStateAuto.reduce_field(2)[of S2 s2 t2 F2 \<Sigma>] unfolding DetFinStateAuto_def by auto
      then have "\<langle>\<langle>m,s1\<rangle>,\<langle>m,s1\<rangle>\<rangle>:?r1^*" "\<langle>\<langle>m,s2\<rangle>,\<langle>m,s2\<rangle>\<rangle>:?r2^*" using rtrancl_refl by auto moreover
      {
        fix bb cc assume as:"\<langle>\<langle>m,s1,s2\<rangle>,bb\<rangle>:?r^*" "\<langle>bb,cc\<rangle>:?r" "\<langle>\<langle>m,s1\<rangle>,fst(bb),fst(snd(bb))\<rangle>:?r1^* \<and> \<langle>\<langle>m,s2\<rangle>,fst(bb),snd(snd(bb))\<rangle>:?r2^*"
        from this(2) have "bb\<in>field(?r)" "cc\<in>field(?r)" using
            fieldI1[of bb cc ?r] fieldI2[of bb cc ?r] by auto
        then obtain bbL bb1 bb2 ccL cc1 cc2 where bbcc:"bb=\<langle>bbL,bb1,bb2\<rangle>" "cc=\<langle>ccL,cc1,cc2\<rangle>"
          "bbL\<in>Lists(\<Sigma>)" "ccL\<in>Lists(\<Sigma>)" "cc1\<in>S1" "cc2\<in>S2" "bb1\<in>S1" "bb2\<in>S2"
          using DetFinStateAuto.reduce_field(1)[OF DFSA0] by blast
        with as(3) have "\<langle>\<langle>m,s1\<rangle>,bbL,bb1\<rangle>:?r1^*" by auto
        from as(2) bbcc have C:"ccL=Init(bbL)" "\<langle>cc1,cc2\<rangle>=?t`\<langle>\<langle>bb1,bb2\<rangle>,Last(bbL)\<rangle>" "bbL:NELists(\<Sigma>)"
          unfolding DFSAExecutionRelation_def[OF assms(1) D] by auto
        from this(2,3) bbcc(8,7) have "\<langle>cc1,cc2\<rangle>=\<langle>t1`\<langle>bb1,Last(bbL)\<rangle>,t2`\<langle>bb2,Last(bbL)\<rangle>\<rangle>" using last_type[of bbL \<Sigma>]
          apply_equality[of "\<langle>\<langle>bb1,bb2\<rangle>,Last(bbL)\<rangle>" _ ?t] D
          unfolding DFSA_def[OF assms(1)] by auto
        then have "cc1=t1`\<langle>bb1,Last(bbL)\<rangle>" "cc2=t2`\<langle>bb2,Last(bbL)\<rangle>" by auto
        with C(1,3) bbcc(8,7) have "\<langle>\<langle>bbL,bb1\<rangle>,\<langle>ccL,cc1\<rangle>\<rangle>:?r1" "\<langle>\<langle>bbL,bb2\<rangle>,\<langle>ccL,cc2\<rangle>\<rangle>:?r2"
          unfolding DFSAExecutionRelation_def[OF assms(1) l1(1)]
              DFSAExecutionRelation_def[OF assms(1) l2(1)] by auto
        with as(3) bbcc(1,2) have "\<langle>\<langle>m,s1\<rangle>,\<langle>ccL,cc1\<rangle>\<rangle>\<in>?r1^*" "\<langle>\<langle>m,s2\<rangle>,\<langle>ccL,cc2\<rangle>\<rangle>\<in>?r2^*"
          using rtrancl_into_trancl1[of _ _ ?r2, THEN trancl_into_rtrancl]
          rtrancl_into_trancl1[of _ _ ?r1, THEN trancl_into_rtrancl]
          by auto
        then have "\<langle>\<langle>m,s1\<rangle>,\<langle>fst(cc),fst(snd(cc))\<rangle>\<rangle>:?r1^* \<and> \<langle>\<langle>m,s2\<rangle>,\<langle>fst(cc),snd(snd(cc))\<rangle>\<rangle>:?r2^*"
          using bbcc(2) by auto
      } moreover note as
      rtrancl_induct[of "\<langle>m,s1,s2\<rangle>" "\<langle>0,yy,zz\<rangle>" "?r" "\<lambda>b. \<langle>\<langle>m,s1\<rangle>,\<langle>fst(b),fst(snd(b))\<rangle>\<rangle>:?r1^* \<and> \<langle>\<langle>m,s2\<rangle>,\<langle>fst(b),snd(snd(b))\<rangle>\<rangle>:?r2^*"]
      ultimately show "\<langle>\<langle>m, s1\<rangle>, 0, yy\<rangle> \<in> ?r1^*" "\<langle>\<langle>m, s2\<rangle>, 0, zz\<rangle> \<in> ?r2^*" by auto
    qed
  {
    fix m assume "m\<in>{i\<in>Lists(\<Sigma>). i <-D (?S,?s,?t,?F){in alphabet}\<Sigma>}"
    then have M:"m\<in>Lists(\<Sigma>)" "m <-D (?S,?s,?t,?F){in alphabet}\<Sigma>" by auto
    {
      assume m0:"m=0"
      from m0 M have "0 <-D (?S,?s,?t,?F){in alphabet}\<Sigma>" by auto
      then obtain yy zz where "\<langle>\<langle>0,s1,s2\<rangle>,\<langle>0,yy,zz\<rangle>\<rangle>:?r^* \<or> ?s:?F" "\<langle>yy,zz\<rangle>:?F" using m0
        DFSASatisfy_def[OF assms(1) D M(1)] by auto moreover
      {
        fix y z
        assume "\<langle>\<langle>0,s1,s2\<rangle>,y\<rangle> \<in> ?r^*" "\<langle>y,z\<rangle> \<in> ?r" "y = \<langle>0,s1,s2\<rangle>"
        from this(2,3) have "0\<in>NELists(\<Sigma>)" unfolding DFSAExecutionRelation_def[OF assms(1) D]
          by auto
        then have False unfolding NELists_def Pi_def by auto
        then have "z=\<langle>0,s1,s2\<rangle>" by auto
      }
      ultimately have "?s:?F" using rtrancl_induct[of "\<langle>0,?s\<rangle>" "\<langle>0,yy,zz\<rangle>" ?r
        "\<lambda>q. q=\<langle>0,?s\<rangle>"] by auto
      then have "m <-D (S1,s1,t1,F1){in alphabet}\<Sigma>" "m <-D (S2,s2,t2,F2){in alphabet}\<Sigma>"
        using DFSASatisfy_def[OF assms(1) l1(1) M(1)] DFSASatisfy_def[OF assms(1) l2(1) M(1)]
        using m0 by auto
    } moreover
    {
      assume m0:"m\<noteq>0"
      with M(2) obtain yy zz where F:"\<langle>\<langle>m,s1,s2\<rangle>,\<langle>0,yy,zz\<rangle>\<rangle>:?r^*" "\<langle>yy,zz\<rangle>:?F" using
        DFSASatisfy_def[OF assms(1) D M(1)] by auto
      from m0 M(1) have "m\<in>NELists(\<Sigma>)" using non_zero_List_func_is_NEList by auto
      then have RR:"\<And>yy zz. \<langle>\<langle>m,s1,s2\<rangle>,\<langle>0,yy,zz\<rangle>\<rangle>:?r^* \<Longrightarrow> \<langle>\<langle>m,s1\<rangle>,\<langle>0,yy\<rangle>\<rangle>:?r1^* \<and> \<langle>\<langle>m,s2\<rangle>,\<langle>0,zz\<rangle>\<rangle>:?r2^*"
        using RR by auto
      with F have "\<exists>q\<in>F1.  \<langle>\<langle>m, s1\<rangle>, 0,q\<rangle>\<in>?r1^*" "\<exists>q\<in>F2.  \<langle>\<langle>m, s2\<rangle>, 0,q\<rangle>\<in>?r2^*" by auto
      then have "m <-D (S1,s1,t1,F1){in alphabet}\<Sigma>" "m <-D (S2,s2,t2,F2){in alphabet}\<Sigma>"
        using DFSASatisfy_def[OF assms(1) l1(1) M(1)] DFSASatisfy_def[OF assms(1) l2(1) M(1)]
        using m0 by auto
    }
    ultimately have "m <-D (S1,s1,t1,F1){in alphabet}\<Sigma>" "m <-D (S2,s2,t2,F2){in alphabet}\<Sigma>" by auto
  }
  then have S1:"{i \<in> Lists(\<Sigma>). i <-D (?S,?s,?t,?F){in alphabet}\<Sigma>} \<subseteq> L1\<inter>L2" using l1(2) l2(2) by auto
  {
    fix m assume "m\<in>L1\<inter>L2"
    with l1(2) l2(2) have M:"m\<in>Lists(\<Sigma>)" "m <-D (S1,s1,t1,F1){in alphabet}\<Sigma>" "m <-D (S2,s2,t2,F2){in alphabet}\<Sigma>"
      by auto
    then obtain f1 f2 where ff:"f1\<in>F1" "f2\<in>F2" "\<langle>\<langle>m,s1\<rangle>,0,f1\<rangle>\<in>?r1^* \<or> (m=0 \<and> s1\<in>F1)" "\<langle>\<langle>m,s2\<rangle>,0,f2\<rangle>\<in>?r2^* \<or> (m=0 \<and> s2\<in>F2)"
      unfolding DFSASatisfy_def[OF assms(1) l1(1) M(1)] DFSASatisfy_def[OF assms(1) l2(1) M(1)] by auto
    {
      fix y z
      assume "\<langle>\<langle>0,s1\<rangle>,y\<rangle> \<in> ?r1^*" "\<langle>y,z\<rangle> \<in> ?r1" "y = \<langle>0,s1\<rangle>"
      from this(2,3) have "0\<in>NELists(\<Sigma>)" unfolding DFSAExecutionRelation_def[OF assms(1) l1(1)]
        by auto
      then have False unfolding NELists_def Pi_def by auto
      then have "z=\<langle>0,s1\<rangle>" by auto
    }
    with ff(1,3) have "m=0 \<longrightarrow> s1\<in>F1" using rtrancl_induct[of "\<langle>m,s1\<rangle>" "\<langle>0,f1\<rangle>" ?r1 "\<lambda>q. q=\<langle>0,s1\<rangle>"] by auto
    moreover
    {
      fix y z
      assume "\<langle>\<langle>0,s2\<rangle>,y\<rangle> \<in> ?r2^*" "\<langle>y,z\<rangle> \<in> ?r2" "y = \<langle>0,s2\<rangle>"
      from this(2,3) have "0\<in>NELists(\<Sigma>)" unfolding DFSAExecutionRelation_def[OF assms(1) l2(1)]
        by auto
      then have False unfolding NELists_def Pi_def by auto
      then have "z=\<langle>0,s2\<rangle>" by auto
    }
    with ff(2,4) have "m=0 \<longrightarrow> s2\<in>F2" using rtrancl_induct[of "\<langle>m,s2\<rangle>" "\<langle>0,f2\<rangle>" ?r2 "\<lambda>q. q=\<langle>0,s2\<rangle>"] by auto
    moreover
    {
      assume m0:"m\<noteq>0"
      with ff(3,4) have A:"\<langle>\<langle>m,s1\<rangle>,0,f1\<rangle>:?r1^*" "\<langle>\<langle>m,s2\<rangle>,0,f2\<rangle>:?r2^*" by auto
      from this(1) have "\<langle>m,s1\<rangle>:field(?r1)" using rtrancl_type by auto
      then have "\<langle>m,s1\<rangle>:Lists(\<Sigma>)\<times>S1" using DetFinStateAuto.reduce_field(1)[of S1 s1 t1 F1 \<Sigma>] l1(1) unfolding DetFinStateAuto_def
        using assms(1) by auto
      with m0 have "m\<in>NELists(\<Sigma>)" "s1\<in>S1" "s2\<in>S2" using l1(1) l2(1) non_zero_List_func_is_NEList
        unfolding DFSA_def[OF assms(1)] by auto
      then have "\<langle>m,s1,s2\<rangle>:NELists(\<Sigma>)\<times>?S" by auto
      then have "\<langle>m,s1,s2\<rangle>:field(?r)" using DetFinStateAuto.reduce_field(2)[OF DFSA0] by auto
      then have K:"\<langle>\<langle>m,s1,s2\<rangle>,\<langle>m,s1,s2\<rangle>\<rangle>:?r^*" using rtrancl_refl by auto
      with `s2\<in>S2` have "\<exists>f2\<in>S2. \<langle>\<langle>m,s1,s2\<rangle>,\<langle>m,s1,f2\<rangle>\<rangle>:?r^*" by auto moreover
      {
        fix y z
        assume as:"\<langle>\<langle>m,s1\<rangle>,y\<rangle>:?r1^*" "\<langle>y,z\<rangle>:?r1" "\<exists>f2\<in>S2. \<langle>\<langle>m,s1,s2\<rangle>,\<langle>fst(y),snd(y),f2\<rangle>\<rangle>:?r^*"
        from as(2) obtain yL y1 where y:"y=\<langle>yL,y1\<rangle>" "z=\<langle>Init(yL),t1`\<langle>y1,Last(yL)\<rangle>\<rangle>"
          "yL\<in>NELists(\<Sigma>)" "y1:S1" unfolding DFSAExecutionRelation_def[OF assms(1) l1(1)] by auto
        with as(3) obtain ff2 where sf:"ff2\<in>S2" "\<langle>\<langle>m,s1,s2\<rangle>,\<langle>yL,y1,ff2\<rangle>\<rangle>:?r^*" by auto
        from this(1) y(3,4) have "\<langle>\<langle>yL,y1,ff2\<rangle>,\<langle>Init(yL),?t`\<langle>\<langle>y1,ff2\<rangle>,Last(yL)\<rangle>\<rangle>\<rangle> \<in> ?r"
          unfolding DFSAExecutionRelation_def[OF assms(1) D] by auto moreover
        have funT:"?t:?S\<times>\<Sigma> \<rightarrow> ?S" using D unfolding DFSA_def[OF assms(1)] by auto
        with y(3,4) sf(1) have "?t`\<langle>\<langle>y1,ff2\<rangle>,Last(yL)\<rangle> =\<langle>t1`\<langle>y1,Last(yL)\<rangle>,t2`\<langle>ff2,Last(yL)\<rangle>\<rangle>"
          using apply_equality[of "\<langle>\<langle>y1,ff2\<rangle>,Last(yL)\<rangle>" _ ?t "?S\<times>\<Sigma>" "\<lambda>_. ?S"] last_type by auto
        ultimately have "\<langle>\<langle>yL,y1,ff2\<rangle>,\<langle>Init(yL),\<langle>t1`\<langle>y1,Last(yL)\<rangle>,t2`\<langle>ff2,Last(yL)\<rangle>\<rangle>\<rangle>\<rangle> \<in> ?r" by auto
        with y(2) have "\<langle>\<langle>yL,y1,ff2\<rangle>,\<langle>fst(z),\<langle>snd(z),t2`\<langle>ff2,Last(yL)\<rangle>\<rangle>\<rangle>\<rangle> \<in> ?r" by auto
        with sf(2) have "\<langle>\<langle>m,s1,s2\<rangle>,\<langle>fst(z),\<langle>snd(z),t2`\<langle>ff2,Last(yL)\<rangle>\<rangle>\<rangle>\<rangle>:?r^*" using
          rtrancl_into_rtrancl by auto
        moreover from sf(1) have "t2`\<langle>ff2,Last(yL)\<rangle> \<in> S2" using l2(1)
          apply_type[of t2 "S2\<times>\<Sigma>" "\<lambda>_. S2"] last_type[OF y(3)] unfolding DFSA_def[OF assms(1)]
          by auto
        ultimately have "\<exists>f2\<in>S2. \<langle>\<langle>m,s1,s2\<rangle>,\<langle>fst(z),\<langle>snd(z),f2\<rangle>\<rangle>\<rangle>:?r^*"
          using sf(1) by auto
      } moreover note A(1)
      ultimately have "\<exists>f2\<in>S2. \<langle>\<langle>m,s1,s2\<rangle>,\<langle>0,\<langle>f1,f2\<rangle>\<rangle>\<rangle>:?r^*"
        using rtrancl_induct[of "\<langle>m,s1\<rangle>" "\<langle>0,f1\<rangle>" ?r1 "\<lambda>q. \<exists>f2\<in>S2. \<langle>\<langle>m,s1,s2\<rangle>,\<langle>fst(q),snd(q),f2\<rangle>\<rangle>:?r^*"]
        by auto
      then obtain uu where uu:"uu\<in>S2" "\<langle>\<langle>m,s1,s2\<rangle>,\<langle>0,\<langle>f1,uu\<rangle>\<rangle>\<rangle>:?r^*" by auto
      from K `s1\<in>S1` have "\<exists>f1\<in>S1. \<langle>\<langle>m,s1,s2\<rangle>,\<langle>m,f1,s2\<rangle>\<rangle>:?r^*" by auto moreover
      {
        fix y z
        assume as:"\<langle>\<langle>m,s2\<rangle>,y\<rangle>:?r2^*" "\<langle>y,z\<rangle>:?r2" "\<exists>f1\<in>S1. \<langle>\<langle>m,s1,s2\<rangle>,\<langle>fst(y),f1,snd(y)\<rangle>\<rangle>:?r^*"
        from as(2) obtain yL y1 where y:"y=\<langle>yL,y1\<rangle>" "z=\<langle>Init(yL),t2`\<langle>y1,Last(yL)\<rangle>\<rangle>"
          "yL\<in>NELists(\<Sigma>)" "y1:S2" unfolding DFSAExecutionRelation_def[OF assms(1) l2(1)] by auto
        with as(3) obtain ff2 where sf:"ff2\<in>S1" "\<langle>\<langle>m,s1,s2\<rangle>,\<langle>yL,ff2,y1\<rangle>\<rangle>:?r^*" by auto
        from this(1) y(3,4) have "\<langle>\<langle>yL,ff2,y1\<rangle>,\<langle>Init(yL),?t`\<langle>\<langle>ff2,y1\<rangle>,Last(yL)\<rangle>\<rangle>\<rangle> \<in> ?r"
          unfolding DFSAExecutionRelation_def[OF assms(1) D] by auto moreover
        have funT:"?t:?S\<times>\<Sigma> \<rightarrow> ?S" using D unfolding DFSA_def[OF assms(1)] by auto
        with y(3,4) sf(1) have "?t`\<langle>\<langle>ff2,y1\<rangle>,Last(yL)\<rangle> =\<langle>t1`\<langle>ff2,Last(yL)\<rangle>,t2`\<langle>y1,Last(yL)\<rangle>\<rangle>"
          using apply_equality[of "\<langle>\<langle>ff2,y1\<rangle>,Last(yL)\<rangle>" _ ?t "?S\<times>\<Sigma>" "\<lambda>_. ?S"] last_type by auto
        ultimately have "\<langle>\<langle>yL,ff2,y1\<rangle>,\<langle>Init(yL),\<langle>t1`\<langle>ff2,Last(yL)\<rangle>,t2`\<langle>y1,Last(yL)\<rangle>\<rangle>\<rangle>\<rangle> \<in> ?r" by auto
        with y(2) have "\<langle>\<langle>yL,ff2,y1\<rangle>,\<langle>fst(z),\<langle>t1`\<langle>ff2,Last(yL)\<rangle>,snd(z)\<rangle>\<rangle>\<rangle> \<in> ?r" by auto
        with sf(2) have "\<langle>\<langle>m,s1,s2\<rangle>,\<langle>fst(z),\<langle>t1`\<langle>ff2,Last(yL)\<rangle>,snd(z)\<rangle>\<rangle>\<rangle>:?r^*" using
          rtrancl_into_rtrancl by auto
        moreover from sf(1) have "t1`\<langle>ff2,Last(yL)\<rangle> \<in> S1" using l1(1)
          apply_type[of t1 "S1\<times>\<Sigma>" "\<lambda>_. S1"] last_type[OF y(3)] unfolding DFSA_def[OF assms(1)]
          by auto
        ultimately have "\<exists>f2\<in>S1. \<langle>\<langle>m,s1,s2\<rangle>,\<langle>fst(z),\<langle>f2,snd(z)\<rangle>\<rangle>\<rangle>:?r^*"
          using sf(1) by auto
      } moreover note A(2)
      ultimately have "\<exists>f1\<in>S1. \<langle>\<langle>m,s1,s2\<rangle>,\<langle>0,\<langle>f1,f2\<rangle>\<rangle>\<rangle>:?r^*"
        using rtrancl_induct[of "\<langle>m,s2\<rangle>" "\<langle>0,f2\<rangle>" ?r2 "\<lambda>q. \<exists>f1\<in>S1. \<langle>\<langle>m,s1,s2\<rangle>,\<langle>fst(q),f1,snd(q)\<rangle>\<rangle>:?r^*"]
        by auto
      then obtain vv where vv:"vv\<in>S1" "\<langle>\<langle>m,s1,s2\<rangle>,\<langle>0,\<langle>vv,f2\<rangle>\<rangle>\<rangle>:?r^*" by auto
      from uu(2) vv(2) have "f1=vv" "uu=f2" using DetFinStateAuto.relation_deteministic[OF DFSA0,
            of m ?s 0 ] by auto
      from this(1) vv(2) ff(1,2) have "m <-D (?S,?s,?t,?F){in alphabet}\<Sigma>"
        unfolding DFSASatisfy_def[OF assms(1) D M(1)] by auto
    }
    ultimately have "m <-D (?S,?s,?t,?F){in alphabet}\<Sigma>"
      unfolding DFSASatisfy_def[OF assms(1) D M(1)] by auto
  }
  with l1(2) l2(2) have "L1\<inter>L2 \<subseteq> {i \<in> Lists(\<Sigma>). i <-D (?S,?s,?t,?F){in alphabet}\<Sigma>}" by auto
  with S1 have "{i \<in> Lists(\<Sigma>). i <-D (?S,?s,?t,?F){in alphabet}\<Sigma>} = L1\<inter>L2" by auto
  then have "L1\<inter>L2 = DetFinStateAuto.LanguageDFSA(?S,?s,?t,?F,\<Sigma>)" by auto
  with D have "\<exists>S s t F. ((S,s,t,F){is an DFSA for alphabet}\<Sigma>) \<and> L1\<inter>L2 = DetFinStateAuto.LanguageDFSA(S,s,t,F,\<Sigma>)"
    using exI[of "\<lambda>h. ((?S,?s,?t,h){is an DFSA for alphabet}\<Sigma>) \<and> L1\<inter>L2 = DetFinStateAuto.LanguageDFSA(?S,?s,?t,h,\<Sigma>)" ?F]
    using exI[of "\<lambda>m. \<exists>h. ((?S,?s,m,h){is an DFSA for alphabet}\<Sigma>) \<and> L1\<inter>L2 = DetFinStateAuto.LanguageDFSA(?S,?s,m,h,\<Sigma>)" ?t]
    using exI[of "\<lambda>n. \<exists>m h. ((?S,n,m,h){is an DFSA for alphabet}\<Sigma>) \<and> L1\<inter>L2 = DetFinStateAuto.LanguageDFSA(?S,n,m,h,\<Sigma>)" ?s]
    using exI[of "\<lambda>p. \<exists>n m h. ((p,n,m,h){is an DFSA for alphabet}\<Sigma>) \<and> L1\<inter>L2 = DetFinStateAuto.LanguageDFSA(p,n,m,h,\<Sigma>)" ?S]
    by auto
  with assms(2,3) show ?thesis unfolding IsRegularLanguage_def[OF assms(1)] IsALanguage_def[OF assms(1)] by auto
qed

text\<open>The complement of a regular language
is a regular language.\<close>

theorem regular_opp:
  assumes "Finite(\<Sigma>)"
  and "L{is a regular language on}\<Sigma>"
  shows "(Lists(\<Sigma>)-L) {is a regular language on}\<Sigma>"
proof-
  from assms(1,2) obtain S s t F where l:"(S,s,t,F){is an DFSA for alphabet}\<Sigma>"
    "L=DetFinStateAuto.LanguageDFSA(S,s,t,F,\<Sigma>)" unfolding IsRegularLanguage_def[OF assms(1)] by auto
  then have l:"(S,s,t,F){is an DFSA for alphabet}\<Sigma>"
    "L={i\<in>Lists(\<Sigma>). i <-D (S,s,t,F){in alphabet}\<Sigma>}"
    using DetFinStateAuto_def assms(1) l(1) by auto
  have "Lists(\<Sigma>)-L \<subseteq> Lists(\<Sigma>)" by auto
  then have "(Lists(\<Sigma>)-L) {is a language with alphabet} \<Sigma>"
    unfolding IsALanguage_def[OF assms(1)] by auto
  let ?F = "S-F"
  let ?r = "DetFinStateAuto.r\<^sub>D(S,t,\<Sigma>)"
  from l(1) have D:"(S,s,t,?F){is an DFSA for alphabet}\<Sigma>" unfolding DFSA_def[OF assms(1)]
    by auto
  with assms(1) have D0:"DetFinStateAuto(S,s,t,?F,\<Sigma>)" unfolding DetFinStateAuto_def by auto
  {
    fix m assume "m\<in>{i\<in>Lists(\<Sigma>). i <-D (S,s,t,?F){in alphabet}\<Sigma>}"
    then have M:"m\<in>Lists(\<Sigma>)" "m <-D (S,s,t,?F){in alphabet}\<Sigma>" by auto
    {
      assume "m\<in>L"
      with l(2) have MM:"m <-D (S,s,t,F){in alphabet}\<Sigma>" by auto
      {
        assume as:"m=0"
        from MM(1) as(1) obtain yy where "\<langle>\<langle>0,s\<rangle>,\<langle>0,yy\<rangle>\<rangle>:?r^* \<or> s:F" "yy\<in>F" unfolding
          DFSASatisfy_def[OF assms(1) l(1) M(1)] by auto moreover
        {
          fix y z
          assume "\<langle>\<langle>0,s\<rangle>,y\<rangle> \<in> ?r^*" "\<langle>y,z\<rangle> \<in> ?r" "y = \<langle>0,s\<rangle>"
          from this(2,3) have "0\<in>NELists(\<Sigma>)" unfolding DFSAExecutionRelation_def[OF assms(1) l(1)]
            by auto
          then have False unfolding NELists_def Pi_def by auto
          then have "z=\<langle>0,s\<rangle>" by auto
        }
        ultimately have sf:"s:F" using rtrancl_induct[of "\<langle>0,s\<rangle>" "\<langle>0,yy\<rangle>" ?r "\<lambda>q. q=\<langle>0,s\<rangle>"] by auto
        from M(2) as(1) obtain yy where "\<langle>\<langle>0,s\<rangle>,\<langle>0,yy\<rangle>\<rangle>:?r^* \<or> s:S-F" "yy\<in>S-F" unfolding
          DFSASatisfy_def[OF assms(1) D M(1)] by auto moreover
        {
          fix y z
          assume "\<langle>\<langle>0,s\<rangle>,y\<rangle> \<in> ?r^*" "\<langle>y,z\<rangle> \<in> ?r" "y = \<langle>0,s\<rangle>"
          from this(2,3) have "0\<in>NELists(\<Sigma>)" unfolding DFSAExecutionRelation_def[OF assms(1) D]
            by auto
          then have False unfolding NELists_def Pi_def by auto
          then have "z=\<langle>0,s\<rangle>" by auto
        }
        ultimately have "s:S-F" using rtrancl_induct[of "\<langle>0,s\<rangle>" "\<langle>0,yy\<rangle>" ?r "\<lambda>q. q=\<langle>0,s\<rangle>"] by auto
        with sf have False by auto
      }
      then have m0:"m\<noteq>0" by auto
      with MM obtain q1 where q1:"q1\<in>F" "\<langle>\<langle>m, s\<rangle>, 0, q1\<rangle> \<in> ?r^*"
        unfolding DFSASatisfy_def[OF assms(1) l(1) M(1)] by auto
      from m0 M(2) obtain q2 where q2:"q2\<in>S-F" "\<langle>\<langle>m, s\<rangle>, 0, q2\<rangle> \<in> ?r^*"
        unfolding DFSASatisfy_def[OF assms(1) D M(1)] by auto
      from q1(2) q2(2) have "q1=q2" using DetFinStateAuto.relation_deteministic[OF D0,
            of m s 0] by auto
      with q1(1) q2(1) have False by auto
    }
    then have "m\<in>Lists(\<Sigma>) - L" using M(1) by auto
  }
  then have S:"{i \<in> Lists(\<Sigma>) . i <-D (S,s,t,S - F){in alphabet}\<Sigma>} \<subseteq> Lists(\<Sigma>) - L" by auto
  {
    fix m assume "m\<in>Lists(\<Sigma>)-L"
    then have m:"m\<in>Lists(\<Sigma>)" "m <-D (S,s,t,F){in alphabet}\<Sigma> \<Longrightarrow> False" using l(2)
      by auto
    from this(1) have R:"m = 0 \<or> (\<exists>q\<in>S. \<langle>\<langle>m,s\<rangle>,0,q\<rangle> \<in> ?r^*)"
      using non_zero_List_func_is_NEList
        DetFinStateAuto.endpoint_exists[OF D0] by auto
    {
      assume as:"m=0" "s\<in>F"
      with m(1) have "m <-D (S,s,t,F){in alphabet}\<Sigma>" unfolding
        DFSASatisfy_def[OF assms(1) l(1) m(1)] by auto
      with m(2) have False by auto
      then have "m\<in>{i \<in> Lists(\<Sigma>) . i <-D (S,s,t,S - F){in alphabet}\<Sigma>}" by auto
    } moreover
    {
      assume as:"m=0" "s\<notin>F"
      then have "m=0" "s\<in>S-F" using DetFinStateAuto.DFSA_dest(1)[OF D0] by auto
      then have "m <-D (S,s,t,S - F){in alphabet}\<Sigma>" unfolding DFSASatisfy_def[OF assms(1) D m(1)] by auto
      with m(1) have "m\<in>{i \<in> Lists(\<Sigma>) . i <-D (S,s,t,S - F){in alphabet}\<Sigma>}" by auto
    } ultimately
    have "m =0 \<longrightarrow> m\<in>{i \<in> Lists(\<Sigma>) . i <-D (S,s,t,S - F){in alphabet}\<Sigma>}" by auto moreover
    {
      assume "\<exists>q\<in>S. \<langle>\<langle>m,s\<rangle>,0,q\<rangle> \<in> ?r^*"
      then obtain q where q:"\<langle>\<langle>m,s\<rangle>,0,q\<rangle> \<in> ?r^*" "q\<in>S" by auto
      {
        assume "q\<in>F"
        with q(1) have "m <-D (S,s,t,F){in alphabet}\<Sigma>" unfolding DFSASatisfy_def[OF assms(1) l(1) m(1)] by auto
        with m(2) have False by auto
      }
      with q have "\<exists>q\<in>S-F. \<langle>\<langle>m,s\<rangle>,0,q\<rangle> \<in> ?r^*" by auto
      then have "m <-D (S,s,t,S-F){in alphabet}\<Sigma>" unfolding DFSASatisfy_def[OF assms(1) D m(1)] by auto
      with m(1) have "m\<in>{i \<in> Lists(\<Sigma>) . i <-D (S,s,t,S - F){in alphabet}\<Sigma>}" by auto
    } moreover note R
    ultimately have "m\<in>{i \<in> Lists(\<Sigma>) . i <-D (S,s,t,S - F){in alphabet}\<Sigma>}" by auto
  }
  then have "Lists(\<Sigma>) -L \<subseteq> {i \<in> Lists(\<Sigma>) . i <-D (S,s,t,S - F){in alphabet}\<Sigma>}" by auto
  with S have "Lists(\<Sigma>) -L = {i \<in> Lists(\<Sigma>) . i <-D (S,s,t,S - F){in alphabet}\<Sigma>}" by auto
  then have "Lists(\<Sigma>) -L = DetFinStateAuto.LanguageDFSA(S,s,t,S-F,\<Sigma>)" .
  then show ?thesis unfolding IsRegularLanguage_def[OF assms(1)] using D by auto
qed

text\<open>The union of two regular languages
is a regular language.\<close>

theorem regular_union:
  assumes "Finite(\<Sigma>)"
  and "L1{is a regular language on}\<Sigma>"
  and "L2{is a regular language on}\<Sigma>"
shows "(L1\<union>L2) {is a regular language on}\<Sigma>"
proof-
  have "L1\<union>L2 = Lists(\<Sigma>)-((Lists(\<Sigma>)-L1)\<inter>(Lists(\<Sigma>)-L2))" using regular_is_language[OF assms(1)]
    assms(2,3) unfolding IsALanguage_def[OF assms(1)] by auto
  moreover
  have A:"(Lists(\<Sigma>)-L1) {is a regular language on}\<Sigma>" using regular_opp[OF assms(1,2)].
  have B:"(Lists(\<Sigma>)-L2) {is a regular language on}\<Sigma>" using regular_opp[OF assms(1,3)].
  from A B have "((Lists(\<Sigma>)-L1)\<inter>(Lists(\<Sigma>)-L2)) {is a regular language on}\<Sigma>" using regular_intersect[OF assms(1)] by auto
  then have "(Lists(\<Sigma>)-((Lists(\<Sigma>)-L1)\<inter>(Lists(\<Sigma>)-L2))) {is a regular language on}\<Sigma>" using regular_opp[OF assms(1)] by auto
  ultimately show ?thesis by auto
qed

text\<open>Another natural operation on words is concatenation,
hence we can defined the concatenated language as
the set of concatenations of words of one language
with words of another.\<close>

definition concat where
  "L1 {is a language with alphabet}\<Sigma> \<Longrightarrow> L2 {is a language with alphabet}\<Sigma>
    \<Longrightarrow> concat(L1,L2) = {Concat(w2,w1). \<langle>w1,w2\<rangle>\<in>L1\<times>L2}"

text\<open>The result of concatenating two languages is a language.\<close>

lemma concat_language:
  assumes "Finite(\<Sigma>)"
  and "L1 {is a language with alphabet}\<Sigma>"
  and "L2 {is a language with alphabet}\<Sigma>"
shows "concat(L1,L2) {is a language with alphabet}\<Sigma>"
proof-
  {
    fix w assume "w\<in>concat(L1,L2)"
    then obtain w1 w2 where w:"w=Concat(w2,w1)" "w1\<in>L1" "w2\<in>L2" unfolding concat_def[OF assms(2,3)]
      by auto
    from this(2,3) assms(2,3) obtain n1 n2 where "n1\<in>nat" "n2\<in>nat" "w1:n1\<rightarrow>\<Sigma>" "w2:n2\<rightarrow>\<Sigma>"
      unfolding IsALanguage_def[OF assms(1)] Lists_def by blast
    then have "Concat(w2,w1):n2#+n1 \<rightarrow> \<Sigma>" "n2#+n1 \<in>nat" using concat_props(1) by auto
    with w(1) have "w\<in>Lists(\<Sigma>)" unfolding Lists_def by auto
  }
  then show ?thesis unfolding IsALanguage_def[OF assms(1)] by auto
qed

subsection\<open>Non-deterministic finite state automata\<close>

text\<open>We have reached a point where it is not easy
to realize a concatenated language of two regular
languages as a regular language. Nevertheless,
if we extend our instruments to allow non-determinism
it is much easier.

The cost, a priori, is that our class of languages
would be larger since our automata are more generic.\<close>

text\<open>The non-determinism is introduced by allowing
the transition function to return not just a state,
but more than one or even none.\<close>

definition
  NFSA ("'(_,_,_,_'){is an NFSA for alphabet}_") where
  "Finite(\<Sigma>) \<Longrightarrow> (S,s\<^sub>0,t,F){is an NFSA for alphabet}\<Sigma> \<equiv> Finite(S) \<and> s\<^sub>0\<in>S \<and> F\<subseteq>S \<and> t:S\<times>\<Sigma>\<rightarrow>Pow(S)"

text\<open>The transition relation is then realized by considering
all possible steps the transition function returns.\<close>

definition
  NFSAExecutionRelation ("{reduce N-relation} '(_,_'){in alphabet}_") where
  "Finite(\<Sigma>) \<Longrightarrow> (S,s\<^sub>0,t,F){is an NFSA for alphabet}\<Sigma> \<Longrightarrow>
  {reduce N-relation}(S,t){in alphabet}\<Sigma> \<equiv> {\<langle>\<langle>w,Q\<rangle>,\<langle>Init(w),\<Union>{t`\<langle>s,Last(w)\<rangle>. s\<in>Q}\<rangle>\<rangle>. \<langle>w,Q\<rangle>\<in>NELists(\<Sigma>)\<times>Pow(S)}"

text\<open>The full reduction is conceived as one of those possible
paths reaching a final state.\<close>

definition
  NFSASatisfy ("_ <-N '(_,_,_,_'){in alphabet}_") where
  "Finite(\<Sigma>) \<Longrightarrow> (S,s\<^sub>0,t,F){is an NFSA for alphabet}\<Sigma> \<Longrightarrow> i\<in>Lists(\<Sigma>) \<Longrightarrow>
  i <-N (S,s\<^sub>0,t,F){in alphabet}\<Sigma> \<equiv> (\<exists>q\<in>Pow(S). (q\<inter>F\<noteq>0 \<and> \<langle>\<langle>i,{s\<^sub>0}\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in> ({reduce N-relation}(S,t){in alphabet}\<Sigma>)^*)) \<or> (i = 0 \<and> s\<^sub>0\<in>F)"

text\<open>An extra generalization can be consider
if we allow the transition relation to go forward
without consuming elements from the word. This
is implemented as allowing @{term \<Sigma>} to symbolize
an step without the word being touched. We might
call it a @{term \<Sigma>} transition or a $\varepsilon$-transition.\<close>

definition
  FullNFSA ("'(_,_,_,_'){is an \<epsilon>-NFSA for alphabet}_") where
  "Finite(\<Sigma>) \<Longrightarrow> (S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma> \<equiv> Finite(S) \<and> s\<^sub>0\<in>S \<and> F\<subseteq>S \<and> t:S\<times>succ(\<Sigma>)\<rightarrow>Pow(S)"

text\<open>The closure of a set of states can then be
viewed as all the states reachable from that set
with a transition of type @{term \<Sigma>}.\<close>

definition
  EpsilonClosure ("\<epsilon>-cl") where
  "Finite(\<Sigma>) \<Longrightarrow> (S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma> \<Longrightarrow> E\<subseteq>S
    \<Longrightarrow> \<epsilon>-cl(S,t,\<Sigma>,E) \<equiv> \<Union>{P\<in>Pow(S). \<langle>E,P\<rangle>\<in>({\<langle>Q,{s\<in>S. \<exists>q\<in>Q. s \<in> t`\<langle>q,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(S)}^*)}"

text\<open>The reduction relation is then extended
by considering any such transitions.\<close>

definition
  FullNFSAExecutionRelation ("{reduce \<epsilon>-N-relation} '(_,_'){in alphabet}_") where
  "Finite(\<Sigma>) \<Longrightarrow> (S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma> \<Longrightarrow>
  {reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma> \<equiv> {\<langle>\<langle>w,Q\<rangle>,\<langle>Init(w),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(w)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)})\<rangle>\<rangle>. \<langle>w,Q\<rangle>\<in>NELists(\<Sigma>)\<times>Pow(S)}"

text\<open>The full reduction of a word is similar to that
of the automata without $\varepsilon$-transitions.\<close>

definition
  FullNFSASatisfy ("_ <-\<epsilon>-N '(_,_,_,_'){in alphabet}_") where
  "Finite(\<Sigma>) \<Longrightarrow> (S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma> \<Longrightarrow> i\<in>Lists(\<Sigma>) \<Longrightarrow>
  i <-\<epsilon>-N (S,s\<^sub>0,t,F){in alphabet}\<Sigma> \<equiv> (\<exists>q\<in>Pow(S). (\<epsilon>-cl(S,t,\<Sigma>,q)\<inter>F\<noteq>0 \<and> \<langle>\<langle>i,{s\<^sub>0}\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in> ({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*)) \<or> (i = 0 \<and> \<epsilon>-cl(S,t,\<Sigma>,{s\<^sub>0})\<inter>F\<noteq>0)"

text\<open>We define a locale to create some notation\<close>

locale NonDetFinStateAuto =
  fixes S and s\<^sub>0 and t and F and \<Sigma>
  assumes finite_alphabet: "Finite(\<Sigma>)"

  assumes NFSA: "(S,s\<^sub>0,t,F){is an NFSA for alphabet}\<Sigma>"

text\<open>Notation for the transition relation\<close>

abbreviation (in NonDetFinStateAuto) nd_rel ("r\<^sub>N")
  where "r\<^sub>N \<equiv> {reduce N-relation}(S,t){in alphabet}\<Sigma>"

text\<open>Notation for the language generated by the
non-deterministic automaton\<close>

abbreviation (in NonDetFinStateAuto) LanguageNFSA
  where "LanguageNFSA \<equiv> {i\<in>Lists(\<Sigma>). i<-N (S,s\<^sub>0,t,F){in alphabet}\<Sigma>}"

subsection\<open>Equivalence of Non-deterministic and Deterministic
Finite State Automata\<close>

text\<open>We will show that the non-deterministic
automata generate languages that are regular
in the sense that there is a deterministic automaton
that generates the same language.\<close>

text\<open>The transition function of the deterministic
automata we will construct\<close>

definition (in NonDetFinStateAuto) tPow where
  "tPow \<equiv> {\<langle>\<langle>U,u\<rangle>,(\<Union>v\<in>U. t ` \<langle>v, u\<rangle>)\<rangle>. \<langle>U,u\<rangle>\<in>Pow(S)\<times>\<Sigma>}"

text\<open>The transition relation of the deterministic
automata we will construct\<close>

definition (in NonDetFinStateAuto) rPow where
  "rPow \<equiv> DetFinStateAuto.r\<^sub>D(Pow(S),tPow,\<Sigma>)"

text\<open>We show that we do have a deterministic automaton\<close>

sublocale NonDetFinStateAuto < dfsa:DetFinStateAuto "Pow(S)" "{s\<^sub>0}" tPow "{Q\<in>Pow(S). Q\<inter>F \<noteq> 0}" \<Sigma>
  unfolding DetFinStateAuto_def DFSA_def[OF finite_alphabet] unfolding tPow_def
  apply safe using finite_alphabet apply simp
  using NFSA unfolding NFSA_def[OF finite_alphabet]
  apply simp using NFSA unfolding NFSA_def[OF finite_alphabet]
   apply simp unfolding Pi_def function_def apply auto
proof-
  fix b y x v assume as:"y \<in> \<Sigma>" "b \<subseteq> S" "v \<in> b" "x \<in> t ` \<langle>v, y\<rangle>"
  from as(2,3) have v:"v\<in>S" by auto
  have "t \<in> S \<times> \<Sigma> \<rightarrow> Pow(S)" using NFSA
    unfolding NFSA_def[OF finite_alphabet] by auto
  with as(1,4) v show "x\<in>S" using apply_type[of t "S\<times>\<Sigma>" "\<lambda>_. Pow(S)" "\<langle>v,y\<rangle>"]
    by auto
qed

text\<open>The two automata have the same relations
associated with them. \<close>

text\<open>First, we show that if the non-deterministic
automaton produces a reduction step to a word, then the deterministic one
we constructed does the same reduction step.\<close>

lemma (in NonDetFinStateAuto) nd_impl_det:
  assumes "\<langle>\<langle>w,Q\<rangle>,\<langle>u,G\<rangle>\<rangle>\<in>r\<^sub>N"
  shows "\<langle>\<langle>w,Q\<rangle>,\<langle>u,G\<rangle>\<rangle>\<in>rPow"
proof-
  from assms have w:"w\<in>NELists(\<Sigma>)" "u=Init(w)" "Q\<in>Pow(S)" "G=(\<Union>s\<in>Q. t`\<langle>s,Last(w)\<rangle>)"
    unfolding NFSAExecutionRelation_def[OF finite_alphabet NFSA] by auto
  then have "tPow`\<langle>Q,Last(w)\<rangle> = (\<Union>s\<in>Q. t`\<langle>s,Last(w)\<rangle>) \<Longrightarrow> ?thesis"
    unfolding DFSAExecutionRelation_def[OF finite_alphabet dfsa.DFSA] rPow_def
    by auto
  moreover have "\<langle>\<langle>Q,Last(w)\<rangle>,\<Union>s\<in>Q. t`\<langle>s,Last(w)\<rangle>\<rangle>:tPow" using last_type[OF w(1)] w(3)
    unfolding tPow_def by auto
  ultimately show ?thesis using apply_equality[OF _ dfsa.DFSA_dest(3), of "\<langle>Q,Last(w)\<rangle>" "\<Union>s\<in>Q. t`\<langle>s,Last(w)\<rangle>"]
    by blast
qed

text\<open>Next, we show that if the deterministic
automaton produces a reduction step to a word, then the non-deterministic one
we constructed does the same reduction step.\<close>

lemma (in NonDetFinStateAuto) det_impl_nd:
  assumes "\<langle>\<langle>w,Q\<rangle>,\<langle>u,G\<rangle>\<rangle>\<in>rPow"
  shows "\<langle>\<langle>w,Q\<rangle>,\<langle>u,G\<rangle>\<rangle>\<in>r\<^sub>N"
proof-
  from assms have w:"w\<in>NELists(\<Sigma>)" "u=Init(w)" "Q\<in>Pow(S)" "G=tPow ` \<langle>Q, Last(w)\<rangle>"
    unfolding DFSAExecutionRelation_def[OF finite_alphabet dfsa.DFSA] rPow_def by auto
  then have "tPow`\<langle>Q,Last(w)\<rangle> = (\<Union>s\<in>Q. t`\<langle>s,Last(w)\<rangle>) \<Longrightarrow> ?thesis"
    unfolding NFSAExecutionRelation_def[OF finite_alphabet NFSA] by auto
  moreover have "\<langle>\<langle>Q,Last(w)\<rangle>,\<Union>s\<in>Q. t`\<langle>s,Last(w)\<rangle>\<rangle>:tPow" unfolding tPow_def using last_type[OF w(1)] w(3) by auto
  ultimately show ?thesis using apply_equality[OF _ dfsa.DFSA_dest(3), of "\<langle>Q,Last(w)\<rangle>" "\<Union>s\<in>Q. t`\<langle>s,Last(w)\<rangle>"]
    by blast
qed

text\<open>Since both are relations, they are equal\<close>

corollary (in NonDetFinStateAuto) relation_NFSA_to_DFSA:
  shows "r\<^sub>N = rPow" using nd_impl_det det_impl_nd
  unfolding DFSAExecutionRelation_def[OF finite_alphabet dfsa.DFSA]
  NFSAExecutionRelation_def[OF finite_alphabet NFSA] rPow_def
  by auto

text\<open>As a consequence, by the definition of a language
generated by an automaton, both languages are equal.\<close>

theorem (in NonDetFinStateAuto) language_nfsa:
  shows "dfsa.LanguageDFSA = LanguageNFSA"
proof-
  let ?S = "Pow(S)"
  let ?s = "{s\<^sub>0}"
  let ?f = "{\<langle>\<langle>U, u\<rangle>, \<Union>v\<in>U. t ` \<langle>v, u\<rangle>\<rangle> . \<langle>U, u\<rangle> \<in> Pow(S) \<times> \<Sigma>}"
  let ?F = "{Q \<in> Pow(S) . Q \<inter> F \<noteq> 0}"
  {
    fix i assume i:"i\<in>Lists(\<Sigma>)" "i <-D (?S,?s,?f,?F){in alphabet}\<Sigma>"
    {
      assume "i=0" "?s\<in>?F"
      then have "i=0" "s\<^sub>0\<in>F" by auto
      then have "i <-N (S,s\<^sub>0,t,F){in alphabet}\<Sigma>"
        unfolding NFSASatisfy_def[OF finite_alphabet NFSA i(1)] by auto
    } moreover
    {
      assume "\<not>(i=0 \<and> ?s\<in>?F)"
      with i(2) obtain q where q:"q\<in>?F" "\<langle>\<langle>i,?s\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>rPow^*"
        using DFSASatisfy_def[OF finite_alphabet dfsa.DFSA i(1)]
        unfolding rPow_def tPow_def by auto
      then have "\<langle>\<langle>i,?s\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>r\<^sub>N^*" using relation_NFSA_to_DFSA
        by auto
      with q(1) have "i <-N (S,s\<^sub>0,t,F){in alphabet}\<Sigma>"
      unfolding NFSASatisfy_def[OF finite_alphabet NFSA i(1)] by auto
    } ultimately
    have "i <-N (S,s\<^sub>0,t,F){in alphabet}\<Sigma>" by auto
  }
  then have A:"{i \<in> Lists(\<Sigma>) . dfsa.reduce(i)} \<subseteq> {i \<in> Lists(\<Sigma>) . i <-N (S,s\<^sub>0,t,F){in alphabet}\<Sigma>}"
    unfolding rPow_def tPow_def by auto
  {
    fix i assume i:"i\<in>Lists(\<Sigma>)" "i <-N (S,s\<^sub>0,t,F){in alphabet}\<Sigma>"
    {
      assume "i=0" "s\<^sub>0\<in>F"
      then have "i=0" "?s\<in>?F" using NFSA
        unfolding NFSA_def[OF finite_alphabet] by auto
      then have "i <-D (?S,?s,?f,?F){in alphabet}\<Sigma>"
        using DFSASatisfy_def[OF finite_alphabet dfsa.DFSA i(1)]
        unfolding tPow_def rPow_def by auto
    } moreover
    {
      assume "\<not>(i=0 \<and> s\<^sub>0\<in>F)"
      with i(2) obtain q where q:"q\<in>Pow(S)" "q\<inter>F\<noteq>0" "\<langle>\<langle>i,?s\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>r\<^sub>N^*"
        unfolding NFSASatisfy_def[OF finite_alphabet NFSA i(1)] by auto
      then have "\<langle>\<langle>i,?s\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>rPow^*" using relation_NFSA_to_DFSA
        by auto
      with q(1,2) have "i <-D (?S,?s,?f,?F){in alphabet}\<Sigma>"
        using DFSASatisfy_def[OF finite_alphabet dfsa.DFSA i(1)]
      unfolding tPow_def rPow_def by auto
    } ultimately
    have "i <-D (?S,?s,?f,?F){in alphabet}\<Sigma>" by auto
  }
  then have B:"{i \<in> Lists(\<Sigma>) . i <-N (S,s\<^sub>0,t,F){in alphabet}\<Sigma>}\<subseteq>
    {i \<in> Lists(\<Sigma>) . dfsa.reduce(i)}" unfolding tPow_def rPow_def by auto
  with A show "dfsa.LanguageDFSA = LanguageNFSA" by auto
qed

text\<open>The language of a non-deterministic finite
state automaton is regular.\<close>

corollary (in NonDetFinStateAuto) lang_is_regular:
  shows "LanguageNFSA{is a regular language on}\<Sigma>"
  unfolding IsRegularLanguage_def[OF finite_alphabet]
  apply (rule exI[of _ "Pow(S)"],
         rule exI[of _ "{s\<^sub>0}"],
         rule exI[of _ tPow],
         rule exI[of _ "{Q \<in> Pow(S). Q \<inter> F \<noteq> 0}"])
  using language_nfsa dfsa.DFSA by auto

subsection\<open>Epsilon-NFSA languages are regular\<close>

text\<open>We now show that every language recognised by an \<open>\<epsilon>\<close>-NFSA
is regular.  The strategy mirrors the NFSA-to-DFSA construction already
in the file: we absorb the \<open>\<epsilon>\<close>-transitions into the transition
function so as to obtain an ordinary NFSA, and then appeal to
@{thm NonDetFinStateAuto.lang_is_regular}.\<close>

text\<open>Given an \<open>\<epsilon>\<close>-NFSA \<open>(S,s\<^sub>0,t,F)\<close> over \<open>\<Sigma>\<close>, define
the \<open>\<epsilon>\<close>-free transition function by following every ordinary
transition with the \<open>\<epsilon>\<close>-closure of the resulting set of states.\<close>

definition EpsilonFreeTransition where
  "Finite(\<Sigma>) \<Longrightarrow> (S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma> \<Longrightarrow>
   EpsilonFreeTransition(S,t,\<Sigma>) \<equiv>
     {\<langle>\<langle>s,x\<rangle>, \<Union>{\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,x\<rangle>). p\<in>\<epsilon>-cl(S,t,\<Sigma>,{s})}\<rangle>. \<langle>s,x\<rangle>\<in>S\<times>\<Sigma>}"

text\<open>The \<open>\<epsilon>\<close>-free transition function is a function
\<open>S\<times>\<Sigma>\<rightarrow>Pow(S)\<close>.\<close>

lemma EpsilonFreeTransition_type:
  assumes fin:"Finite(\<Sigma>)"
  and fsa:"(S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
  shows "EpsilonFreeTransition(S,t,\<Sigma>) : S\<times>\<Sigma> \<rightarrow> Pow(S)"
proof-
  have tT:"t:S\<times>succ(\<Sigma>)\<rightarrow>Pow(S)"
    using fsa unfolding FullNFSA_def[OF fin] by auto
  have subS:"\<And>s x. \<langle>s,x\<rangle>\<in>S\<times>\<Sigma> \<Longrightarrow> \<Union>{\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,x\<rangle>). p\<in>\<epsilon>-cl(S,t,\<Sigma>,{s})} \<subseteq> S"
  proof-
    fix s x assume sa:"\<langle>s,x\<rangle>\<in>S\<times>\<Sigma>"
    have e:"\<epsilon>-cl(S,t,\<Sigma>,{s}) \<subseteq> S" using EpsilonClosure_def[OF fin fsa]
      sa by auto
    {
      fix p assume p:"p\<in>\<epsilon>-cl(S,t,\<Sigma>,{s})"
      have imgS:"t`\<langle>p,x\<rangle> \<subseteq> S"
      proof-
        have "\<langle>p,x\<rangle>\<in>S\<times>succ(\<Sigma>)" using sa p e by (auto intro: succI2)
        with tT have "t`\<langle>p,x\<rangle>\<in>Pow(S)" using apply_type[of t "S\<times>succ(\<Sigma>)" "\<lambda>_. Pow(S)"] by auto
        then show ?thesis by auto
      qed
      then have "\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,x\<rangle>) \<subseteq> S"
        unfolding EpsilonClosure_def[OF fin fsa imgS] by auto
    }
    then show "\<Union>{\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,x\<rangle>). p\<in>\<epsilon>-cl(S,t,\<Sigma>,{s})} \<subseteq> S" by auto
  qed
  have pow:"EpsilonFreeTransition(S,t,\<Sigma>) \<in> Pow((S\<times>\<Sigma>)\<times>Pow(S))"
  proof-
    {
      fix x assume "x\<in>EpsilonFreeTransition(S,t,\<Sigma>)"
      then obtain s y where sa:"\<langle>s,y\<rangle>\<in>S\<times>\<Sigma>" "x=\<langle>\<langle>s,y\<rangle>,\<Union>{\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,y\<rangle>). p\<in>\<epsilon>-cl(S,t,\<Sigma>,{s})}\<rangle>"
        unfolding EpsilonFreeTransition_def[OF fin fsa] by auto
      from subS[OF sa(1)] sa(1) sa(2) have "x\<in>(S\<times>\<Sigma>)\<times>Pow(S)" by auto
    }
    then show ?thesis by auto
  qed
  moreover have "function(EpsilonFreeTransition(S,t,\<Sigma>))"
  proof -
    {
      fix x y z
      assume h1:"\<langle>x,y\<rangle>\<in>EpsilonFreeTransition(S,t,\<Sigma>)"
         and h2:"\<langle>x,z\<rangle>\<in>EpsilonFreeTransition(S,t,\<Sigma>)"
      from h1 obtain s q where sa:"\<langle>s,q\<rangle>\<in>S\<times>\<Sigma>" "x=\<langle>s,q\<rangle>" "y=(\<Union>p\<in>\<epsilon>-cl(S, t, \<Sigma>,{s}). \<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,q\<rangle>))"
        unfolding EpsilonFreeTransition_def[OF fin fsa] by auto
      from h2 sa(2) have "z=(\<Union>p\<in>\<epsilon>-cl(S, t, \<Sigma>,{s}). \<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,q\<rangle>))"
        unfolding EpsilonFreeTransition_def[OF fin fsa] by auto
      with sa(3) have "y=z" by auto
    }
    then show ?thesis unfolding function_def by auto
  qed
  moreover have "S\<times>\<Sigma> \<subseteq> domain(EpsilonFreeTransition(S,t,\<Sigma>))"
    unfolding EpsilonFreeTransition_def[OF fin fsa] domain_def by auto
  ultimately show ?thesis unfolding Pi_def by auto
qed

text\<open>The \<open>\<epsilon>\<close>-free automaton, where the new final states collect all
states whose \<open>\<epsilon>\<close>-closure meets \<open>F\<close>, is an NFSA over \<open>\<Sigma>\<close>.\<close>

lemma EpsilonFree_is_NFSA:
  assumes fin:"Finite(\<Sigma>)"
  and fsa:"(S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
  shows "(S, s\<^sub>0, EpsilonFreeTransition(S,t,\<Sigma>), {q\<in>S. \<epsilon>-cl(S,t,\<Sigma>,{q})\<inter>F \<noteq> 0}){is an NFSA for alphabet}\<Sigma>"
proof-
  have finS:"Finite(S)" and s0S:"s\<^sub>0\<in>S"
    using fsa unfolding FullNFSA_def[OF fin] by auto
  have "EpsilonFreeTransition(S,t,\<Sigma>) : S\<times>\<Sigma> \<rightarrow> Pow(S)"
    using EpsilonFreeTransition_type[OF fin fsa] .
  moreover have "{q\<in>S. \<epsilon>-cl(S,t,\<Sigma>,{q})\<inter>F \<noteq> 0} \<subseteq> S" by auto
  ultimately show ?thesis unfolding NFSA_def[OF fin]
    using finS s0S by auto
qed

text\<open>Every set $B \subseteq S$ is contained in its own $\varepsilon$-closure.\<close>

lemma epsilon_cl_refl_sub:
  assumes fin:"Finite(\<Sigma>)"
  and fsa:"(S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
  and bS:"B\<subseteq>S"
  shows "B \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,B)"
proof-
  let ?R = "{\<langle>Q,{s\<in>S. \<exists>q\<in>Q. s \<in> t`\<langle>q,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(S)}"
  have fieldR:"Pow(S) \<subseteq> field(?R)"
  proof-
    {
      fix Q assume "Q\<in>Pow(S)"
      then have "\<langle>Q,{s\<in>S. \<exists>q\<in>Q. s \<in> t`\<langle>q,\<Sigma>\<rangle>}\<rangle>\<in>?R" by auto
      then have "Q\<in>domain(?R)" by auto
      then have "Q\<in>field(?R)" unfolding field_def by auto
    }
    then show ?thesis by auto
  qed
  from bS have Bin:"B\<in>Pow(S)" by auto
  then have Brefl:"\<langle>B,B\<rangle>\<in>?R^*" using fieldR rtrancl_refl[of B ?R] by auto
  then have "B\<in>{P\<in>Pow(S). \<langle>B,P\<rangle>\<in>?R^*}" using Bin by auto
  then have "B\<subseteq>\<Union>{P\<in>Pow(S). \<langle>B,P\<rangle>\<in>?R^*}" by auto
  then show ?thesis unfolding EpsilonClosure_def[OF fin fsa bS] by simp
qed

text\<open>The $\varepsilon$-closure is monotone: if $A \subseteq B \subseteq S$
then $\varepsilon$-cl$(S,t,\Sigma,A) \subseteq \varepsilon$-cl$(S,t,\Sigma,B)$.\<close>

lemma epsilon_cl_mono:
  assumes fin:"Finite(\<Sigma>)"
  and fsa:"(S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
  and bS:"B\<subseteq>S" and sub:"A\<subseteq>B"
  shows "\<epsilon>-cl(S,t,\<Sigma>,A) \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,B)"
proof-
  let ?R = "{\<langle>Q,{s\<in>S. \<exists>q\<in>Q. s \<in> t`\<langle>q,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(S)}"
  from bS sub have aS:"A\<subseteq>S" by auto
  have Adef:"\<epsilon>-cl(S,t,\<Sigma>,A) = \<Union>{P\<in>Pow(S). \<langle>A,P\<rangle>\<in>?R^*}"
    unfolding EpsilonClosure_def[OF fin fsa aS] by auto
  have Bdef:"\<epsilon>-cl(S,t,\<Sigma>,B) = \<Union>{P\<in>Pow(S). \<langle>B,P\<rangle>\<in>?R^*}"
    unfolding EpsilonClosure_def[OF fin fsa bS] by simp
  have fieldR:"Pow(S) \<subseteq> field(?R)"
  proof-
    {
      fix Q assume "Q\<in>Pow(S)"
      then have "\<langle>Q,{s\<in>S. \<exists>q\<in>Q. s \<in> t`\<langle>q,\<Sigma>\<rangle>}\<rangle>\<in>?R" by auto
      then have "Q\<in>domain(?R)" by auto
      then have "Q\<in>field(?R)" unfolding field_def by auto
    }
    then show ?thesis by auto
  qed
  from bS have Bin:"B\<in>Pow(S)" by auto
  have Brefl:"\<langle>B,B\<rangle>\<in>?R^*" using Bin fieldR rtrancl_refl[of B ?R] by auto
  {
    fix p assume "p \<in> \<epsilon>-cl(S,t,\<Sigma>,A)"
    then obtain PA where PA:"PA\<in>Pow(S)" "\<langle>A,PA\<rangle>\<in>?R^*" "p\<in>PA"
      using Adef by auto
    have "\<forall>pp\<in>PA. pp\<in>\<epsilon>-cl(S,t,\<Sigma>,B)"
    proof(rule rtrancl_induct[of A PA ?R "\<lambda>Q. \<forall>pp\<in>Q. pp\<in>\<epsilon>-cl(S,t,\<Sigma>,B)"])
      show "\<langle>A,PA\<rangle>\<in>?R^*" using PA(2) .
      show "\<forall>pp\<in>A. pp\<in>\<epsilon>-cl(S,t,\<Sigma>,B)"
      proof
        fix pp assume "pp\<in>A"
        with sub have "pp\<in>B" by auto
        with Brefl Bin have "pp\<in>\<Union>{P\<in>Pow(S). \<langle>B,P\<rangle>\<in>?R^*}" by auto
        then show "pp\<in>\<epsilon>-cl(S,t,\<Sigma>,B)" using Bdef by simp
      qed
      fix Q P'
      assume IH:"\<forall>pp\<in>Q. pp\<in>\<epsilon>-cl(S,t,\<Sigma>,B)" and step:"\<langle>Q,P'\<rangle>\<in>?R"
      show "\<forall>pp\<in>P'. pp\<in>\<epsilon>-cl(S,t,\<Sigma>,B)"
      proof
        fix pp assume "pp\<in>P'"
        from step obtain Q0 where Q0:"Q0\<in>Pow(S)" "Q=Q0"
          "P'={s\<in>S. \<exists>q\<in>Q0. s \<in> t`\<langle>q,\<Sigma>\<rangle>}" by auto
        with \<open>pp\<in>P'\<close> obtain q where q:"q\<in>Q" "pp \<in> t`\<langle>q,\<Sigma>\<rangle>" "pp\<in>S" by auto
        from q(1) IH obtain PB where PB:"PB\<in>Pow(S)" "\<langle>B,PB\<rangle>\<in>?R^*" "q\<in>PB"
          using Bdef by auto
        let ?P1 = "{s\<in>S. \<exists>r\<in>PB. s \<in> t`\<langle>r,\<Sigma>\<rangle>}"
        have "\<langle>PB,?P1\<rangle>\<in>?R" using PB(1) by auto
        with PB(2) have step1:"\<langle>B,?P1\<rangle>\<in>?R^*" using rtrancl_into_rtrancl by auto
        have "?P1\<in>Pow(S)" by auto
        from q(2,3) PB(3) have "pp\<in>?P1" by auto
        with step1 \<open>?P1\<in>Pow(S)\<close> have "pp\<in>\<Union>{P\<in>Pow(S). \<langle>B,P\<rangle>\<in>?R^*}" by auto
        then show "pp\<in>\<epsilon>-cl(S,t,\<Sigma>,B)" using Bdef by simp
      qed
    qed
    then have goal:"p \<in> \<epsilon>-cl(S,t,\<Sigma>,B)" using PA(3) by auto
  }
  then show ?thesis by auto
qed

text\<open>The $\varepsilon$-closure distributes over arbitrary unions:
for $C \subseteq \mathrm{Pow}(S)$ we have
$\varepsilon$-cl$(S,t,\Sigma,\bigcup C) = \bigcup\{\varepsilon$-cl$(S,t,\Sigma,E) \mid E\in C\}$.\<close>

lemma epsilon_cl_union:
  assumes fin:"Finite(\<Sigma>)"
  and fsa:"(S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
  and cS:"C\<subseteq>Pow(S)"
  shows "\<epsilon>-cl(S,t,\<Sigma>,\<Union>C) = \<Union>{\<epsilon>-cl(S,t,\<Sigma>,E). E\<in>C}"
proof-
  let ?R = "{\<langle>Q,{s\<in>S. \<exists>q\<in>Q. s \<in> t`\<langle>q,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(S)}"
  have UC:"(\<Union>C)\<subseteq>S" using cS by auto
  have UCdef:"\<epsilon>-cl(S,t,\<Sigma>,\<Union>C) = \<Union>{P\<in>Pow(S). \<langle>\<Union>C,P\<rangle>\<in>?R^*}"
    unfolding EpsilonClosure_def[OF fin fsa UC] by simp
  show ?thesis
  proof(rule equalityI)
    show "\<epsilon>-cl(S,t,\<Sigma>,\<Union>C) \<subseteq> \<Union>{\<epsilon>-cl(S,t,\<Sigma>,E). E\<in>C}"
    proof
      fix p assume "p\<in>\<epsilon>-cl(S,t,\<Sigma>,\<Union>C)"
      then obtain P where P:"P\<in>Pow(S)" "\<langle>\<Union>C,P\<rangle>\<in>?R^*" "p\<in>P" using UCdef by auto
      have "\<forall>pp\<in>P. pp\<in>\<Union>{\<epsilon>-cl(S,t,\<Sigma>,E). E\<in>C}"
      proof(rule rtrancl_induct[of "\<Union>C" P ?R "\<lambda>Q. \<forall>pp\<in>Q. pp\<in>\<Union>{\<epsilon>-cl(S,t,\<Sigma>,E). E\<in>C}"])
        show "\<langle>\<Union>C,P\<rangle>\<in>?R^*" using P(2) .
        show "\<forall>pp\<in>\<Union>C. pp\<in>\<Union>{\<epsilon>-cl(S,t,\<Sigma>,E). E\<in>C}"
        proof
          fix pp assume "pp\<in>\<Union>C"
          then obtain E0 where E0:"E0\<in>C" "pp\<in>E0" by auto
          from E0(1) cS have E0S:"E0\<subseteq>S" by auto
          from epsilon_cl_refl_sub[OF fin fsa E0S] E0(2) have "pp\<in>\<epsilon>-cl(S,t,\<Sigma>,E0)" by auto
          with E0(1) show "pp\<in>\<Union>{\<epsilon>-cl(S,t,\<Sigma>,E). E\<in>C}" by auto
        qed
        fix Q P'
        assume IH:"\<forall>pp\<in>Q. pp\<in>\<Union>{\<epsilon>-cl(S,t,\<Sigma>,E). E\<in>C}" and step:"\<langle>Q,P'\<rangle>\<in>?R"
        show "\<forall>pp\<in>P'. pp\<in>\<Union>{\<epsilon>-cl(S,t,\<Sigma>,E). E\<in>C}"
        proof
          fix pp assume "pp\<in>P'"
          from step obtain Q0 where Q0:"Q0\<in>Pow(S)" "Q=Q0"
            "P'={s\<in>S. \<exists>q\<in>Q0. s \<in> t`\<langle>q,\<Sigma>\<rangle>}" by auto
          with \<open>pp\<in>P'\<close> obtain q where q:"q\<in>Q" "pp \<in> t`\<langle>q,\<Sigma>\<rangle>" "pp\<in>S" by auto
          from q(1) IH obtain E1 where E1:"E1\<in>C" "q\<in>\<epsilon>-cl(S,t,\<Sigma>,E1)" by auto
          from E1(1) cS have E1S:"E1\<subseteq>S" by auto
          from E1(2) obtain P0 where P0:"P0\<in>Pow(S)" "\<langle>E1,P0\<rangle>\<in>?R^*" "q\<in>P0"
            unfolding EpsilonClosure_def[OF fin fsa E1S] by auto
          let ?P1 = "{s\<in>S. \<exists>r\<in>P0. s \<in> t`\<langle>r,\<Sigma>\<rangle>}"
          have "\<langle>P0,?P1\<rangle>\<in>?R" using P0(1) by auto
          with P0(2) have "\<langle>E1,?P1\<rangle>\<in>?R^*" using rtrancl_into_rtrancl by auto
          moreover have "?P1\<in>Pow(S)" by auto
          moreover from q(2,3) P0(3) have "pp\<in>?P1" by auto
          ultimately have "pp\<in>\<epsilon>-cl(S,t,\<Sigma>,E1)"
            unfolding EpsilonClosure_def[OF fin fsa E1S] by auto
          with E1(1) show "pp\<in>\<Union>{\<epsilon>-cl(S,t,\<Sigma>,E). E\<in>C}" by auto
        qed
      qed
      with P(3) show "p\<in>\<Union>{\<epsilon>-cl(S,t,\<Sigma>,E). E\<in>C}" by auto
    qed
    show "\<Union>{\<epsilon>-cl(S,t,\<Sigma>,E). E\<in>C} \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,\<Union>C)"
    proof
      fix p assume "p\<in>\<Union>{\<epsilon>-cl(S,t,\<Sigma>,E). E\<in>C}"
      then obtain E0 where E0:"E0\<in>C" "p\<in>\<epsilon>-cl(S,t,\<Sigma>,E0)" by auto
      from E0(1) cS have E0S:"E0\<subseteq>S" by auto
      have "E0\<subseteq>\<Union>C" using E0(1) by auto
      from epsilon_cl_mono[OF fin fsa UC this] E0(2)
      show "p\<in>\<epsilon>-cl(S,t,\<Sigma>,\<Union>C)" by auto
    qed
  qed
qed

text\<open>The $\varepsilon$-closure is idempotent:
for $C \in \mathrm{Pow}(S)$ we have
$\varepsilon$-cl$(S,t,\Sigma,\varepsilon$-cl$(S,t,\Sigma, C) = \varepsilon$-cl$(S,t,\Sigma,C)$.\<close>

lemma epsilon_cl_idem:
  assumes fin:"Finite(\<Sigma>)"
  and fsa:"(S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
  and cS:"q\<in>Pow(S)"
  shows "\<epsilon>-cl(S,t,\<Sigma>,\<epsilon>-cl(S,t,\<Sigma>,q)) = \<epsilon>-cl(S,t,\<Sigma>,q)"
proof(rule equalityI)
  have qS:"q\<subseteq>S" using cS by auto
  have clS:"\<epsilon>-cl(S,t,\<Sigma>,q)\<subseteq>S"
    unfolding EpsilonClosure_def[OF fin fsa qS] by auto
  from epsilon_cl_refl_sub[OF fin fsa clS]
  show "\<epsilon>-cl(S,t,\<Sigma>,q) \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,\<epsilon>-cl(S,t,\<Sigma>,q))" .
  show "\<epsilon>-cl(S,t,\<Sigma>,\<epsilon>-cl(S,t,\<Sigma>,q)) \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,q)"
  proof
    fix p assume "p \<in> \<epsilon>-cl(S,t,\<Sigma>,\<epsilon>-cl(S,t,\<Sigma>,q))"
    let ?R = "{\<langle>Q,{s\<in>S. \<exists>r\<in>Q. s \<in> t`\<langle>r,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(S)}"
    have cldef:"\<epsilon>-cl(S,t,\<Sigma>,q) = \<Union>{P\<in>Pow(S). \<langle>q,P\<rangle>\<in>?R^*}"
      unfolding EpsilonClosure_def[OF fin fsa qS] by simp
    have icldef:"\<epsilon>-cl(S,t,\<Sigma>,\<epsilon>-cl(S,t,\<Sigma>,q)) = \<Union>{P\<in>Pow(S). \<langle>\<epsilon>-cl(S,t,\<Sigma>,q),P\<rangle>\<in>?R^*}"
      unfolding EpsilonClosure_def[OF fin fsa clS] by simp
    from \<open>p \<in> \<epsilon>-cl(S,t,\<Sigma>,\<epsilon>-cl(S,t,\<Sigma>,q))\<close>
    obtain P where P:"P\<in>Pow(S)" "\<langle>\<epsilon>-cl(S,t,\<Sigma>,q),P\<rangle>\<in>?R^*" "p\<in>P"
      using icldef by auto
    have "P \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,q)"
    proof(rule rtrancl_induct[of "\<epsilon>-cl(S,t,\<Sigma>,q)" P ?R "\<lambda>Q. Q \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,q)"])
      show "\<langle>\<epsilon>-cl(S,t,\<Sigma>,q),P\<rangle>\<in>?R^*" using P(2) .
      show "\<epsilon>-cl(S,t,\<Sigma>,q) \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,q)" by auto
      fix V W
      assume IH:"V \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,q)" and step:"\<langle>V,W\<rangle>\<in>?R"
      show "W \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,q)"
      proof
        fix pp assume "pp\<in>W"
        from step obtain V0 where V0:"V0\<in>Pow(S)" "V=V0"
          "W={s\<in>S. \<exists>r\<in>V0. s \<in> t`\<langle>r,\<Sigma>\<rangle>}" by auto
        with \<open>pp\<in>W\<close> obtain v where v:"v\<in>V" "pp \<in> t`\<langle>v,\<Sigma>\<rangle>" "pp\<in>S" by auto
        from v(1) IH obtain P0 where P0:"P0\<in>Pow(S)" "\<langle>q,P0\<rangle>\<in>?R^*" "v\<in>P0"
          using cldef by auto
        let ?P1 = "{s\<in>S. \<exists>r\<in>P0. s \<in> t`\<langle>r,\<Sigma>\<rangle>}"
        have "\<langle>P0,?P1\<rangle>\<in>?R" using P0(1) by auto
        with P0(2) have "\<langle>q,?P1\<rangle>\<in>?R^*" using rtrancl_into_rtrancl by auto
        moreover have "?P1\<in>Pow(S)" by auto
        moreover from v(2,3) P0(3) have "pp\<in>?P1" by auto
        ultimately show "pp\<in>\<epsilon>-cl(S,t,\<Sigma>,q)" using cldef by auto
      qed
    qed
    with P(3) show "p \<in> \<epsilon>-cl(S,t,\<Sigma>,q)" by auto
  qed
qed

text\<open>The value of @{term EpsilonFreeTransition} at $\langle s,x\rangle$ is the
$\varepsilon$-closure of $t\,`\langle s,x\rangle$.\<close>

lemma EpsilonFreeTransition_val:
  assumes fin:"Finite(\<Sigma>)"
  and fsa:"(S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
  and sS:"s\<in>S" and xSig:"x\<in>\<Sigma>"
  shows "EpsilonFreeTransition(S,t,\<Sigma>)`\<langle>s,x\<rangle> = (\<Union>p\<in>\<epsilon>-cl(S,t,\<Sigma>,{s}). \<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,x\<rangle>))"
proof-
  have "\<langle>\<langle>s,x\<rangle>, (\<Union>p\<in>\<epsilon>-cl(S,t,\<Sigma>,{s}). \<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,x\<rangle>))\<rangle> \<in> EpsilonFreeTransition(S,t,\<Sigma>)"
    unfolding EpsilonFreeTransition_def[OF fin fsa] using sS xSig by auto
  then show ?thesis using apply_equality[OF _ EpsilonFreeTransition_type[OF fin fsa]] by auto
qed

text\<open>The $\varepsilon$-N execution relation coincides with the N execution relation
of the $\varepsilon$-free transition function.\<close>

lemma epsilon_free_rel_eq:
  assumes fin:"Finite(\<Sigma>)"
  and fsa:"(S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
  shows "({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>) =
         ({reduce N-relation}(S,EpsilonFreeTransition(S,t,\<Sigma>)){in alphabet}\<Sigma>)"
proof-
  have tT:"t:S\<times>succ(\<Sigma>)\<rightarrow>Pow(S)"
    using fsa unfolding FullNFSA_def[OF fin] by auto
  have nfsa:"(S,s\<^sub>0,EpsilonFreeTransition(S,t,\<Sigma>),{q\<in>S. \<epsilon>-cl(S,t,\<Sigma>,{q})\<inter>F\<noteq>0}){is an NFSA for alphabet}\<Sigma>" using EpsilonFree_is_NFSA[OF fin fsa] .
  {
    fix w Q assume wQ:"\<langle>w,Q\<rangle>\<in>NELists(\<Sigma>)\<times>Pow(S)"
    then have wNE:"w\<in>NELists(\<Sigma>)" and QS:"Q\<in>Pow(S)" by auto
    have lT:"Last(w)\<in>\<Sigma>" using last_type[OF wNE] by auto
    have C_sub:"{t`\<langle>s,Last(w)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)}\<subseteq>Pow(S)"
    proof-
      {
        fix E assume "E\<in>{t`\<langle>s,Last(w)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)}"
        then obtain s where s:"s\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)" "E=t`\<langle>s,Last(w)\<rangle>" by auto
        have "\<langle>s,Last(w)\<rangle>\<in>S\<times>succ(\<Sigma>)" using QS s(1) lT
          EpsilonClosure_def[OF fin fsa] by (auto intro: succI2)
        with tT have "t`\<langle>s,Last(w)\<rangle>\<in>Pow(S)"
          using apply_type[of t "S\<times>succ(\<Sigma>)" "\<lambda>_. Pow(S)"] by auto
        with s(2) have "E\<in>Pow(S)" by auto
      }
      then show ?thesis by auto
    qed
    have "\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(w)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)}) =
          \<Union>{EpsilonFreeTransition(S,t,\<Sigma>)`\<langle>s,Last(w)\<rangle>. s\<in>Q}"
    proof-
      have "\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(w)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)}) =
            \<Union>{\<epsilon>-cl(S,t,\<Sigma>,E). E\<in>{t`\<langle>s,Last(w)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)}}"
        using epsilon_cl_union[OF fin fsa C_sub] by auto
      also have "... = \<Union>{\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>s,Last(w)\<rangle>). s\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)}" by auto
      also have "... = \<Union>{EpsilonFreeTransition(S,t,\<Sigma>)`\<langle>s,Last(w)\<rangle>. s\<in>Q}"
      proof-
        {
          fix s assume sQ:"s\<in>Q"
          with QS have sS:"s\<in>S" using EpsilonClosure_def[OF fin fsa] by auto
          from EpsilonFreeTransition_val[OF fin fsa sS lT]
          have "(\<Union>p\<in>\<epsilon>-cl(S,t,\<Sigma>,{s}). \<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,Last(w)\<rangle>)) = EpsilonFreeTransition(S,t,\<Sigma>)`\<langle>s,Last(w)\<rangle>" by auto
        }
        then have "\<Union>{(\<Union>p\<in>\<epsilon>-cl(S,t,\<Sigma>,{s}). \<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,Last(w)\<rangle>)). s\<in>Q} =
          \<Union>{EpsilonFreeTransition(S,t,\<Sigma>)`\<langle>s,Last(w)\<rangle>. s\<in>Q}" by auto
        moreover have "\<Union>{(\<Union>p\<in>\<epsilon>-cl(S,t,\<Sigma>,{s}). \<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,Last(w)\<rangle>)). s\<in>Q} =
          \<Union>{\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>s,Last(w)\<rangle>). s\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)}"
        proof 
          {
            fix q assume "q\<in>\<Union>{(\<Union>p\<in>\<epsilon>-cl(S,t,\<Sigma>,{s}). \<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,Last(w)\<rangle>)). s\<in>Q}"
            then obtain s where s:"s\<in>Q" "q\<in>(\<Union>p\<in>\<epsilon>-cl(S,t,\<Sigma>,{s}). \<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,Last(w)\<rangle>))"
              by auto
            from s(2) obtain p where p:"p\<in>\<epsilon>-cl(S,t,\<Sigma>,{s})" "q\<in>\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,Last(w)\<rangle>)" by auto
            from QS have "\<epsilon>-cl(S,t,\<Sigma>,{s}) \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,Q)" using s(1) epsilon_cl_mono[OF fin fsa] by auto
            with p(1) have "p\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)" by auto
            with p(2) have "q\<in>\<Union>{\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>s,Last(w)\<rangle>). s\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)}" by auto
          }
          then show "\<Union>{(\<Union>p\<in>\<epsilon>-cl(S,t,\<Sigma>,{s}). \<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,Last(w)\<rangle>)). s\<in>Q} \<subseteq>
            \<Union>{\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>s,Last(w)\<rangle>). s\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)}" by blast
          {
            fix q assume "q\<in>\<Union>{\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>s,Last(w)\<rangle>). s\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)}"
            then obtain p where p:"p\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)" "q\<in>\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,Last(w)\<rangle>)" by auto
            have "\<epsilon>-cl(S,t,\<Sigma>,\<Union>{{s}. s\<in>Q}) = \<Union>{\<epsilon>-cl(S,t,\<Sigma>,{s}). s\<in>Q}"
              using epsilon_cl_union[OF fin fsa, of "{{s}. s\<in>Q}"] QS by auto
            moreover have "\<Union>{{s}. s\<in>Q} = Q" by auto
            ultimately have "\<epsilon>-cl(S,t,\<Sigma>,Q) = \<Union>{\<epsilon>-cl(S,t,\<Sigma>,{s}). s\<in>Q}" by auto
            with p(1) obtain p1 where p1:"p\<in>\<epsilon>-cl(S,t,\<Sigma>,{p1})" "p1\<in>Q" by auto
            then have "q\<in>(\<Union>p\<in>\<epsilon>-cl(S,t,\<Sigma>,{p1}). \<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,Last(w)\<rangle>))"
              using p(2) by auto
            then have "q\<in>\<Union>{(\<Union>p\<in>\<epsilon>-cl(S,t,\<Sigma>,{s}). \<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,Last(w)\<rangle>)). s\<in>Q}"
              using p1(2) by auto
          }
          then show "\<Union>{\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>s,Last(w)\<rangle>). s\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)} \<subseteq>
            \<Union>{(\<Union>p\<in>\<epsilon>-cl(S,t,\<Sigma>,{s}). \<epsilon>-cl(S,t,\<Sigma>,t`\<langle>p,Last(w)\<rangle>)). s\<in>Q}" by blast
        qed
        ultimately show ?thesis by auto
      qed
      finally show ?thesis .
    qed
  }
  then show ?thesis
    unfolding FullNFSAExecutionRelation_def[OF fin fsa]
            NFSAExecutionRelation_def[OF fin nfsa]
    by auto
qed


text\<open>The @{term field} of the NFSA relation is equal to its DFSA construction\<close>

lemma (in NonDetFinStateAuto) eps_nfsa_field:
  shows "field({reduce N-relation}(S,t){in alphabet}\<Sigma>) \<subseteq> Lists(\<Sigma>)\<times>Pow(S)"
    "NELists(\<Sigma>)\<times>Pow(S) \<subseteq> field({reduce N-relation}(S,t){in alphabet}\<Sigma>)"
  using dfsa.reduce_field relation_NFSA_to_DFSA unfolding rPow_def by auto

text\<open>The @{term field} of the \<open>\<epsilon>\<close> relation is equal to its NDFSA construction\<close>

lemma eps_nfsa_field:
  assumes fin:"Finite(\<Sigma>)"
  and fsa:"(S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
  shows "field({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>) \<subseteq> Lists(\<Sigma>)\<times>Pow(S)"
    "NELists(\<Sigma>)\<times>Pow(S) \<subseteq> field({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)"
  using epsilon_free_rel_eq[OF fin fsa] NonDetFinStateAuto.eps_nfsa_field[of S "s\<^sub>0" "EpsilonFreeTransition
   (S, t, \<Sigma>)" "{q\<in>S. \<epsilon>-cl(S,t,\<Sigma>,{q})\<inter>F \<noteq> 0}" \<Sigma>]
  unfolding NonDetFinStateAuto_def using assms(1) EpsilonFree_is_NFSA[OF assms] by auto

text\<open>The language accepted by the \<open>\<epsilon>\<close>-NFSA equals the language
accepted by its \<open>\<epsilon>\<close>-free counterpart.  The key observation is that
every \<open>\<epsilon>\<close>-step in the execution relation is absorbed by the
\<open>\<epsilon>\<close>-closure in @{term EpsilonFreeTransition}.\<close>

lemma EpsilonFree_same_language_1:
  assumes fin:"Finite(\<Sigma>)"
  and fsa:"(S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
  and "i\<in>Lists(\<Sigma>)" "i <-\<epsilon>-N (S,s\<^sub>0,t,F){in alphabet}\<Sigma>"
  shows "i <-N (S,s\<^sub>0,EpsilonFreeTransition(S,t,\<Sigma>),{q\<in>S. \<epsilon>-cl(S,t,\<Sigma>,{q})\<inter>F\<noteq>0}){in alphabet}\<Sigma>"
proof-
  have s0S:"s\<^sub>0\<in>S" using fsa unfolding FullNFSA_def[OF fin] by auto
  let ?t' = "EpsilonFreeTransition(S,t,\<Sigma>)"
  let ?F' = "{q\<in>S. \<epsilon>-cl(S,t,\<Sigma>,{q})\<inter>F\<noteq>0}"
  have nfsa:"(S,s\<^sub>0,?t',?F'){is an NFSA for alphabet}\<Sigma>"
    using EpsilonFree_is_NFSA[OF fin fsa] .
  have rel_eq:"({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>) =
               ({reduce N-relation}(S,?t'){in alphabet}\<Sigma>)"
    using epsilon_free_rel_eq[OF fin fsa] .
  from assms(4) show ?thesis unfolding FullNFSASatisfy_def[OF fin fsa assms(3)]
  proof(elim disjE exE conjE)
    assume "i=0" and ecl:"(\<epsilon>-cl(S,t,\<Sigma>,{s\<^sub>0}))\<inter>F\<noteq>0"
    from s0S have "{s\<^sub>0}\<subseteq>S" by auto
    from epsilon_cl_refl_sub[OF fin fsa this] have "s\<^sub>0\<in>\<epsilon>-cl(S,t,\<Sigma>,{s\<^sub>0})" by auto
    with \<open>i=0\<close> s0S ecl show ?thesis
      unfolding NFSASatisfy_def[OF fin nfsa assms(3)] by auto
  next
    assume "\<exists>q\<in>Pow(S).  \<epsilon>-cl(S, t, \<Sigma>, q)\<inter>F\<noteq>0 \<and> \<langle>\<langle>i,{s\<^sub>0}\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*"
    then obtain q where q:"q\<in>Pow(S)" " \<epsilon>-cl(S, t, \<Sigma>, q)\<inter>F\<noteq>0" "\<langle>\<langle>i,{s\<^sub>0}\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*" by auto
    from rel_eq q(3) have "\<langle>\<langle>i,{s\<^sub>0}\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>({reduce N-relation}(S,?t'){in alphabet}\<Sigma>)^*" by auto
    moreover from q(1,2,3) have "q\<inter>?F'\<noteq>0"
    proof-
      let ?R = "{reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>"
      from q(3) have "\<langle>\<langle>i,{s\<^sub>0}\<rangle>,\<langle>0,q\<rangle>\<rangle> \<in> id(field(?R)) \<union> (?R O ?R^*)"
        using rtrancl_unfold by auto
      then show ?thesis
      proof(elim UnE)
        assume "\<langle>\<langle>i,{s\<^sub>0}\<rangle>,\<langle>0,q\<rangle>\<rangle> \<in> id(field(?R))"
        then have "q = {s\<^sub>0}" by auto
        with q(2) s0S show ?thesis by auto
      next
        assume "\<langle>\<langle>i,{s\<^sub>0}\<rangle>,\<langle>0,q\<rangle>\<rangle> \<in> ?R O ?R^*"
        then obtain mid where "\<langle>mid,\<langle>0,q\<rangle>\<rangle>\<in>?R"
          unfolding compE by auto
        then obtain W QQ where WQQ:"W\<in>NELists(\<Sigma>)" "QQ\<in>Pow(S)"
          "q = \<epsilon>-cl(S, t, \<Sigma>, \<Union>s\<in>\<epsilon>-cl(S, t, \<Sigma>, QQ). t ` \<langle>s, Last(W)\<rangle>)"
          unfolding FullNFSAExecutionRelation_def[OF fin fsa] by auto
        have tT:"t:S\<times>succ(\<Sigma>)\<rightarrow>Pow(S)" using fsa unfolding FullNFSA_def[OF fin] by auto
        have unionS:"(\<Union>s\<in>\<epsilon>-cl(S, t, \<Sigma>, QQ). t ` \<langle>s, Last(W)\<rangle>) \<in> Pow(S)"
        proof -
          {
            fix x assume "x \<in> (\<Union>s\<in>\<epsilon>-cl(S, t, \<Sigma>, QQ). t ` \<langle>s, Last(W)\<rangle>)"
            then obtain ss where ss:"ss\<in>\<epsilon>-cl(S, t, \<Sigma>, QQ)" "x\<in>t`\<langle>ss,Last(W)\<rangle>" by auto
            from WQQ(2) ss(1) have ssS:"ss\<in>S" using EpsilonClosure_def[OF fin fsa] by auto
            have lastSig:"Last(W)\<in>succ(\<Sigma>)" using last_type[OF WQQ(1)] by auto
            have "\<langle>ss,Last(W)\<rangle>\<in>S\<times>succ(\<Sigma>)" using ssS lastSig by auto
            from apply_type[OF tT this] ss(2) have "x\<in>S" by auto
          }
          then show ?thesis by auto
        qed
        from epsilon_cl_idem[OF fin fsa unionS] WQQ(3)
          have clq:"\<epsilon>-cl(S,t,\<Sigma>,q) = q" by auto
        with q(2) obtain g where g:"g\<in>q" "g\<in>F" by auto
        from q(1) g(1) have gS:"g\<in>S" by auto
        have "{g}\<subseteq>S" using gS by auto
        from epsilon_cl_refl_sub[OF fin fsa this] have "g\<in>\<epsilon>-cl(S,t,\<Sigma>,{g})" by auto
        with g(2) gS have "g\<in>?F'" by auto
        with g(1) show ?thesis by auto
      qed
    qed
    ultimately show ?thesis
      unfolding NFSASatisfy_def[OF fin nfsa assms(3)] using q(1) by auto
  qed
qed

lemma EpsilonFree_same_language_2:
  assumes fin:"Finite(\<Sigma>)"
  and fsa:"(S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
  and "i\<in>Lists(\<Sigma>)" "i <-N (S,s\<^sub>0,EpsilonFreeTransition(S,t,\<Sigma>),{q\<in>S. \<epsilon>-cl(S,t,\<Sigma>,{q})\<inter>F\<noteq>0}){in alphabet}\<Sigma>"
  shows "i <-\<epsilon>-N (S,s\<^sub>0,t,F){in alphabet}\<Sigma>"
proof-
  have s0S:"s\<^sub>0\<in>S" using fsa unfolding FullNFSA_def[OF fin] by auto
  let ?t' = "EpsilonFreeTransition(S,t,\<Sigma>)"
  let ?F' = "{q\<in>S. \<epsilon>-cl(S,t,\<Sigma>,{q})\<inter>F\<noteq>0}"
  have nfsa:"(S,s\<^sub>0,?t',?F'){is an NFSA for alphabet}\<Sigma>"
    using EpsilonFree_is_NFSA[OF fin fsa] .
  have rel_eq:"({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>) =
               ({reduce N-relation}(S,?t'){in alphabet}\<Sigma>)"
    using epsilon_free_rel_eq[OF fin fsa] .
  from assms(4) show ?thesis unfolding NFSASatisfy_def[OF fin nfsa assms(3)]
  proof(elim disjE exE conjE)
    assume "i=0" "s\<^sub>0\<in>?F'"
    then show ?thesis unfolding FullNFSASatisfy_def[OF fin fsa assms(3)] by auto
  next
    assume "\<exists>q\<in>Pow(S). q\<inter>?F'\<noteq>0 \<and> \<langle>\<langle>i,{s\<^sub>0}\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>({reduce N-relation}(S,?t'){in alphabet}\<Sigma>)^*"
    then obtain q where q:"q\<in>Pow(S)" "q\<inter>?F'\<noteq>0" "\<langle>\<langle>i,{s\<^sub>0}\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>({reduce N-relation}(S,?t'){in alphabet}\<Sigma>)^*" by auto
    from rel_eq q(3) have "\<langle>\<langle>i,{s\<^sub>0}\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*" by auto
    moreover from q(1,2) have "\<epsilon>-cl(S,t,\<Sigma>,q)\<inter>F\<noteq>0"
    proof-
      from q(2) obtain f where f:"f\<in>q" "f\<in>?F'" by auto
      from f(2) have fS:"f\<in>S" and ecl:"\<epsilon>-cl(S,t,\<Sigma>,{f})\<inter>F\<noteq>0" by auto
      from q(1) have qS:"q\<subseteq>S" by auto
      have fq:"{f}\<subseteq>q" using f(1) by auto
      have fS':"{f}\<subseteq>S" using fS by auto
      from epsilon_cl_mono[OF fin fsa qS fq]
        have "\<epsilon>-cl(S,t,\<Sigma>,{f}) \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,q)" .
      with ecl show ?thesis by auto
    qed
    ultimately show ?thesis
      unfolding FullNFSASatisfy_def[OF fin fsa assms(3)] using q(1) by auto
  qed
qed

corollary EpsilonFree_same_language:
  assumes fin:"Finite(\<Sigma>)"
  and fsa:"(S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
  shows "{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N (S,s\<^sub>0,t,F){in alphabet}\<Sigma>}=
  {i\<in>Lists(\<Sigma>). i <-N (S,s\<^sub>0,EpsilonFreeTransition(S,t,\<Sigma>),{q\<in>S. \<epsilon>-cl(S,t,\<Sigma>,{q})\<inter>F\<noteq>0}){in alphabet}\<Sigma>}"
  using EpsilonFree_same_language_2[OF assms] EpsilonFree_same_language_1[OF assms] by auto


text\<open>Every language recognised by an \<open>\<epsilon>\<close>-NFSA is regular.\<close>

theorem epsilonNFSA_lang_is_regular:
  assumes fin:"Finite(\<Sigma>)"
  and fsa:"(S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
  shows "{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N (S,s\<^sub>0,t,F){in alphabet}\<Sigma>} {is a regular language on}\<Sigma>"
proof-
  let ?t' = "EpsilonFreeTransition(S,t,\<Sigma>)"
  let ?F' = "{q\<in>S. \<epsilon>-cl(S,t,\<Sigma>,{q})\<inter>F\<noteq>0}"
  have nfsa:"(S,s\<^sub>0,?t',?F'){is an NFSA for alphabet}\<Sigma>" using EpsilonFree_is_NFSA[OF fin fsa] .
  have lang_eq:"{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N (S,s\<^sub>0,t,F){in alphabet}\<Sigma>} =
                {i\<in>Lists(\<Sigma>). i <-N (S,s\<^sub>0,?t',?F'){in alphabet}\<Sigma>}"
    using EpsilonFree_same_language[OF fin fsa] .
  have loc:"NonDetFinStateAuto(S,s\<^sub>0,?t',?F',\<Sigma>)"
    unfolding NonDetFinStateAuto_def using fin nfsa by auto
  have "{i\<in>Lists(\<Sigma>). i <-N (S,s\<^sub>0,?t',?F'){in alphabet}\<Sigma>} {is a regular language on}\<Sigma>"
    using NonDetFinStateAuto.lang_is_regular[OF loc] by auto
  with lang_eq show ?thesis by auto
qed

subsection\<open>Concatenation of regular languages\<close>

text\<open>We now prove the main theorem: the concatenation of two regular
languages is regular.  The proof constructs an \<open>\<epsilon>\<close>-NFSA that first
simulates the automaton for \<open>L\<^sub>1\<close>, then makes a free \<open>\<epsilon>\<close>-transition
to the initial state of the automaton for \<open>L\<^sub>2\<close> upon reaching an
accepting state of the first, and finally accepts when the second
automaton accepts.\<close>

text\<open>The combined state space for the product \<open>\<epsilon>\<close>-NFSA is the
disjoint union \<open>S\<^sub>1\<times>{0}\<union>S\<^sub>2\<times>{1}\<close>.\<close>

definition concat_eNFSA_states where
  "concat_eNFSA_states(S1,S2) \<equiv> S1\<times>{0} \<union> S2\<times>{1}"

text\<open>The transition function of the product \<open>\<epsilon>\<close>-NFSA.
A state \<open>\<langle>s,0\<rangle>\<close> in the first component reads \<open>a\<in>\<Sigma>\<close> by following
\<open>t\<^sub>1\<close>; on the \<open>\<epsilon>\<close>-symbol (encoded as \<open>\<Sigma>\<close>) it jumps to
\<open>\<langle>s\<^sub>02,1\<rangle>\<close> when \<open>s\<in>F\<^sub>1\<close>, and has no \<open>\<epsilon>\<close>-move otherwise.
A state \<open>\<langle>s,1\<rangle>\<close> in the second component reads \<open>a\<in>\<Sigma>\<close> by following
\<open>t\<^sub>2\<close>, and ignores \<open>\<epsilon>\<close>-steps.\<close>

definition concat_eNFSA_trans where
  "Finite(\<Sigma>) \<Longrightarrow>
   (S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma> \<Longrightarrow>
   (S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma> \<Longrightarrow>
   concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>) \<equiv>
     {\<langle>\<langle>\<langle>s,0\<rangle>,q\<rangle>, {t1`\<langle>s,q\<rangle>}\<times>{0}\<rangle>. \<langle>s,q\<rangle>\<in>S1\<times>\<Sigma>}
     \<union> {\<langle>\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle>, {x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}\<rangle>. s\<in>S1}
     \<union> {\<langle>\<langle>\<langle>s,1\<rangle>,q\<rangle>, {t2`\<langle>s,q\<rangle>}\<times>{1}\<rangle>. \<langle>s,q\<rangle>\<in>S2\<times>\<Sigma>}
     \<union> {\<langle>\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle>, 0\<rangle>. s\<in>S2}"

text\<open>The product automaton is a valid \<open>\<epsilon>\<close>-NFSA.\<close>

lemma concat_eNFSA_valid:
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  shows "(concat_eNFSA_states(S1,S2), \<langle>s01,0\<rangle>,
  concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>), F2\<times>{1}
  ){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
proof-
  have S1fin:"Finite(S1)" and S2fin:"Finite(S2)"
    and s01S:"s01\<in>S1" and s02S:"s02\<in>S2"
    and F1S:"F1\<subseteq>S1" and F2S:"F2\<subseteq>S2"
    and t1:"t1:S1\<times>\<Sigma> \<rightarrow> S1" and t2:"t2:S2\<times>\<Sigma> \<rightarrow> S2"
    using A1 A2 unfolding DFSA_def[OF fin] by auto
  let ?SS = "concat_eNFSA_states(S1,S2)"
  let ?tc = "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  have finS10:"Finite(S1\<times>{0})"
    using Finite1_L12[of S1 "{0}"] Fin_into_Finite Finite_into_Fin S1fin by auto
  have finS21:"Finite(S2\<times>{1})"
    using Finite1_L12[of S2 "{1}"] Fin_into_Finite Finite_into_Fin S2fin by auto
  have finSS:"Finite(?SS)" unfolding concat_eNFSA_states_def
    using finS10 finS21 Finite_Un by auto
  have s01SS:"\<langle>s01,0\<rangle>\<in>?SS" unfolding concat_eNFSA_states_def using s01S by auto
  have F2SS:"F2\<times>{1} \<subseteq> ?SS" unfolding concat_eNFSA_states_def using F2S by auto
  have tc_type:"?tc : ?SS\<times>succ(\<Sigma>) \<rightarrow> Pow(?SS)"
  proof-
    have ran:"?tc \<in> Pow((?SS\<times>succ(\<Sigma>))\<times>Pow(?SS))"
    proof-
      {
        fix t assume t:"t\<in>?tc"
        then obtain x y where tt:"\<langle>x,y\<rangle> = t" unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
        with t have xy:"\<langle>x,y\<rangle>\<in>?tc" by auto
        have xy_dom:"x\<in>?SS\<times>succ(\<Sigma>)"
          using xy unfolding concat_eNFSA_trans_def[OF fin A1 A2]
                             concat_eNFSA_states_def
          by (auto intro: succI1 succI2)
        have xy_img:"y\<subseteq>?SS"
        proof-
          from xy consider
            (a) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S1\<times>\<Sigma> \<and> x=\<langle>\<langle>s,0\<rangle>,aa\<rangle> \<and> y={t1`\<langle>s,aa\<rangle>}\<times>{0}" |
            (b) "\<exists>s. s\<in>S1 \<and> x=\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle> \<and> y={x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}" |
            (c) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S2\<times>\<Sigma> \<and> x=\<langle>\<langle>s,1\<rangle>,aa\<rangle> \<and> y={t2`\<langle>s,aa\<rangle>}\<times>{1}" |
            (d) "\<exists>s. s\<in>S2 \<and> x=\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle> \<and> y=0"
            unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show "y\<subseteq>?SS"
          proof cases
            case a
            then obtain s aa where sa:"\<langle>s,aa\<rangle>\<in>S1\<times>\<Sigma>" "y={t1`\<langle>s,aa\<rangle>}\<times>{0}" by auto
            from sa(1) have "t1`\<langle>s,aa\<rangle>\<in>S1" using apply_type[OF t1] by auto
            with sa(2) show ?thesis unfolding concat_eNFSA_states_def by auto
          next
            case b
            then obtain s where sb:"s\<in>S1" "y={x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}" by auto
            then show ?thesis using s02S F2S unfolding concat_eNFSA_states_def by auto
          next
            case c
            then obtain s aa where sa:"\<langle>s,aa\<rangle>\<in>S2\<times>\<Sigma>" "y={t2`\<langle>s,aa\<rangle>}\<times>{1}" by auto
            from sa(1) have "t2`\<langle>s,aa\<rangle>\<in>S2" using apply_type[OF t2] by auto
            with sa(2) show ?thesis unfolding concat_eNFSA_states_def by auto
          next
            case d then show ?thesis by auto
          qed
        qed
        from xy_dom xy_img have "\<langle>x,y\<rangle>\<in>(?SS\<times>succ(\<Sigma>))\<times>Pow(?SS)" by auto
        with tt have "t\<in>(?SS\<times>succ(\<Sigma>))\<times>Pow(?SS)" by auto
      }
      then show ?thesis by auto
    qed
    moreover have "function(?tc)"
    proof -
      {
        fix x y z
        assume h1:"\<langle>x,y\<rangle>\<in>?tc" and h2:"\<langle>x,z\<rangle>\<in>?tc"
        from h1 consider
          (a1) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S1\<times>\<Sigma> \<and> x=\<langle>\<langle>s,0\<rangle>,aa\<rangle> \<and> y={t1`\<langle>s,aa\<rangle>}\<times>{0}" |
          (b1) "\<exists>s. s\<in>S1 \<and> x=\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle> \<and> y={x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}" |
          (c1) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S2\<times>\<Sigma> \<and> x=\<langle>\<langle>s,1\<rangle>,aa\<rangle> \<and> y={t2`\<langle>s,aa\<rangle>}\<times>{1}" |
          (d1) "\<exists>s. s\<in>S2 \<and> x=\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle> \<and> y=0"
          unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
        then have "y=z"
        proof cases
          case a1
          then obtain s aa where sa:"\<langle>s,aa\<rangle>\<in>S1\<times>\<Sigma>" "x=\<langle>\<langle>s,0\<rangle>,aa\<rangle>" "y={t1`\<langle>s,aa\<rangle>}\<times>{0}" by auto
          from h2 consider
            (a2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S1\<times>\<Sigma> \<and> x=\<langle>\<langle>s,0\<rangle>,aa\<rangle> \<and> z={t1`\<langle>s,aa\<rangle>}\<times>{0}" |
            (b2) "\<exists>s. s\<in>S1 \<and> x=\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle> \<and> z={x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}" |
            (c2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S2\<times>\<Sigma> \<and> x=\<langle>\<langle>s,1\<rangle>,aa\<rangle> \<and> z={t2`\<langle>s,aa\<rangle>}\<times>{1}" |
            (d2) "\<exists>s. s\<in>S2 \<and> x=\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle> \<and> z=0"
          unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show ?thesis
          proof cases
            case a2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S1\<times>\<Sigma>" "x=\<langle>\<langle>p,0\<rangle>,q\<rangle>" "z={t1`\<langle>p,q\<rangle>}\<times>{0}" by auto
            from pq(2) sa(2) have "p=s" "q=aa" by auto
            with sa(3) pq(3) show ?thesis by auto
            next
            case b2
            then obtain p where pq:"p\<in>S1" "x=\<langle>\<langle>p,0\<rangle>,\<Sigma>\<rangle>" "z={x\<in>{\<langle>s02,1\<rangle>}. p\<in>F1}" by auto
            from pq(2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case c2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S2\<times>\<Sigma>" "x=\<langle>\<langle>p,1\<rangle>,q\<rangle>" "z={t2`\<langle>p,q\<rangle>}\<times>{1}" by auto
            from pq(2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case d2
            then obtain p where pq:"p\<in>S2" "x=\<langle>\<langle>p,1\<rangle>,\<Sigma>\<rangle>" "z=0" by auto
            from pq(2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
          qed
        next
          case b1
          then obtain s where sa:"s\<in>S1" "x=\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle>" "y={x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}" by auto
          from h2 consider
            (a2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S1\<times>\<Sigma> \<and> x=\<langle>\<langle>s,0\<rangle>,aa\<rangle> \<and> z={t1`\<langle>s,aa\<rangle>}\<times>{0}" |
            (b2) "\<exists>s. s\<in>S1 \<and> x=\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle> \<and> z={x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}" |
            (c2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S2\<times>\<Sigma> \<and> x=\<langle>\<langle>s,1\<rangle>,aa\<rangle> \<and> z={t2`\<langle>s,aa\<rangle>}\<times>{1}" |
            (d2) "\<exists>s. s\<in>S2 \<and> x=\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle> \<and> z=0"
          unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show ?thesis
          proof cases
            case a2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S1\<times>\<Sigma>" "x=\<langle>\<langle>p,0\<rangle>,q\<rangle>" "z={t1`\<langle>p,q\<rangle>}\<times>{0}" by auto
            from pq(1,2) sa(2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case b2
            then obtain p where pq:"p\<in>S1" "x=\<langle>\<langle>p,0\<rangle>,\<Sigma>\<rangle>" "z={x\<in>{\<langle>s02,1\<rangle>}. p\<in>F1}" by auto
            from pq(2) sa(1,2) have "p=s" by auto
            with sa(3) pq(3) show ?thesis by auto
            next
            case c2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S2\<times>\<Sigma>" "x=\<langle>\<langle>p,1\<rangle>,q\<rangle>" "z={t2`\<langle>p,q\<rangle>}\<times>{1}" by auto
            from pq(2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case d2
            then obtain p where pq:"p\<in>S2" "x=\<langle>\<langle>p,1\<rangle>,\<Sigma>\<rangle>" "z=0" by auto
            from pq(2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
          qed
        next
          case c1
          then obtain s aa where sa:"\<langle>s,aa\<rangle>\<in>S2\<times>\<Sigma>" "x=\<langle>\<langle>s,1\<rangle>,aa\<rangle>" "y={t2`\<langle>s,aa\<rangle>}\<times>{1}" by auto
          from h2 consider
            (a2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S1\<times>\<Sigma> \<and> x=\<langle>\<langle>s,0\<rangle>,aa\<rangle> \<and> z={t1`\<langle>s,aa\<rangle>}\<times>{0}" |
            (b2) "\<exists>s. s\<in>S1 \<and> x=\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle> \<and> z={x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}" |
            (c2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S2\<times>\<Sigma> \<and> x=\<langle>\<langle>s,1\<rangle>,aa\<rangle> \<and> z={t2`\<langle>s,aa\<rangle>}\<times>{1}" |
            (d2) "\<exists>s. s\<in>S2 \<and> x=\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle> \<and> z=0"
          unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show ?thesis
          proof cases
            case a2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S1\<times>\<Sigma>" "x=\<langle>\<langle>p,0\<rangle>,q\<rangle>" "z={t1`\<langle>p,q\<rangle>}\<times>{0}" by auto
            from pq(1,2) sa(2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case b2
            then obtain p where pq:"p\<in>S1" "x=\<langle>\<langle>p,0\<rangle>,\<Sigma>\<rangle>" "z={x\<in>{\<langle>s02,1\<rangle>}. p\<in>F1}" by auto
            from pq(2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case c2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S2\<times>\<Sigma>" "x=\<langle>\<langle>p,1\<rangle>,q\<rangle>" "z={t2`\<langle>p,q\<rangle>}\<times>{1}" by auto
            from pq(2) sa(1,2) have "p=s" "q=aa" by auto
            with sa(3) pq(3) show ?thesis by auto
            next
            case d2
            then obtain p where pq:"p\<in>S2" "x=\<langle>\<langle>p,1\<rangle>,\<Sigma>\<rangle>" "z=0" by auto
            from pq(2) sa(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
          qed
        next
          case d1
          then obtain s where sb:"s\<in>S2" "x=\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle>" "y=0" by auto
          from h2 consider
            (a2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S1\<times>\<Sigma> \<and> x=\<langle>\<langle>s,0\<rangle>,aa\<rangle> \<and> z={t1`\<langle>s,aa\<rangle>}\<times>{0}" |
            (b2) "\<exists>s. s\<in>S1 \<and> x=\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle> \<and> z={x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}" |
            (c2) "\<exists>s aa. \<langle>s,aa\<rangle>\<in>S2\<times>\<Sigma> \<and> x=\<langle>\<langle>s,1\<rangle>,aa\<rangle> \<and> z={t2`\<langle>s,aa\<rangle>}\<times>{1}" |
            (d2) "\<exists>s. s\<in>S2 \<and> x=\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle> \<and> z=0"
          unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show ?thesis
          proof cases
            case a2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S1\<times>\<Sigma>" "x=\<langle>\<langle>p,0\<rangle>,q\<rangle>" "z={t1`\<langle>p,q\<rangle>}\<times>{0}" by auto
            from pq(1,2) sb(2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case b2
            then obtain p where pq:"p\<in>S1" "x=\<langle>\<langle>p,0\<rangle>,\<Sigma>\<rangle>" "z={x\<in>{\<langle>s02,1\<rangle>}. p\<in>F1}" by auto
            from pq(2) sb(1,2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case c2
            then obtain p q where pq:"\<langle>p,q\<rangle>\<in>S2\<times>\<Sigma>" "x=\<langle>\<langle>p,1\<rangle>,q\<rangle>" "z={t2`\<langle>p,q\<rangle>}\<times>{1}" by auto
            from pq(1,2) sb(2) have False using mem_irrefl by auto
            then show ?thesis by auto
            next
            case d2
            then obtain p where pq:"p\<in>S2" "x=\<langle>\<langle>p,1\<rangle>,\<Sigma>\<rangle>" "z=0" by auto
            from pq(2) sb(1,2) have "p=s" by auto
            with sb(3) pq(3) show ?thesis by auto
            next
          qed
        qed
      }
      then show ?thesis unfolding function_def by auto
    qed
    moreover have "?SS\<times>succ(\<Sigma>) \<subseteq> domain(?tc)"
    proof
      fix x assume hx:"x\<in>?SS\<times>succ(\<Sigma>)"
      then obtain p aa where pa:"p\<in>?SS" "aa\<in>succ(\<Sigma>)" "x=\<langle>p,aa\<rangle>" by auto
      from pa(1) obtain s where ps:
        "(s\<in>S1 \<and> p=\<langle>s,0\<rangle>) \<or> (s\<in>S2 \<and> p=\<langle>s,1\<rangle>)"
        unfolding concat_eNFSA_states_def by auto
      from pa(2) have acase:"aa\<in>\<Sigma> \<or> aa=\<Sigma>" using succ_iff by auto
      from ps show "x\<in>domain(?tc)"
      proof (elim disjE conjE)
        assume hs1:"s\<in>S1" and hsp1:"p=\<langle>s,0\<rangle>"
        from acase show ?thesis
        proof (elim disjE)
          assume "aa\<in>\<Sigma>"
          with hs1 hsp1 pa(3) have "\<langle>x,{t1`\<langle>s,aa\<rangle>}\<times>{0}\<rangle>\<in>?tc"
            unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show ?thesis unfolding domain_def by auto
        next
          assume "aa=\<Sigma>"
          with hs1 hsp1 pa(3) have "\<langle>x,{v\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}\<rangle>\<in>?tc"
            unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show ?thesis unfolding domain_def by auto
        qed
      next
        assume hs2:"s\<in>S2" and hsp2:"p=\<langle>s,1\<rangle>"
        from acase show ?thesis
        proof (elim disjE)
          assume "aa\<in>\<Sigma>"
          with hs2 hsp2 pa(3) have "\<langle>x,{t2`\<langle>s,aa\<rangle>}\<times>{1}\<rangle>\<in>?tc"
            unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show ?thesis unfolding domain_def by auto
        next
          assume "aa=\<Sigma>"
          with hs2 hsp2 pa(3) have "\<langle>x,0\<rangle>\<in>?tc"
            unfolding concat_eNFSA_trans_def[OF fin A1 A2] by auto
          then show ?thesis unfolding domain_def by auto
        qed
      qed
    qed
    ultimately show ?thesis unfolding Pi_def by auto
  qed
  show ?thesis unfolding FullNFSA_def[OF fin]
    using finSS s01SS F2SS tc_type by auto
qed

text\<open>The $\varepsilon$-transition of a component-0 state $\langle s,0\rangle$
is $\{\langle s_{02},1\rangle\}$ when $s\in F_1$, and empty otherwise.\<close>

lemma concat_eNFSA_eps_comp0:
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and sS1:"s\<in>S1"
  shows "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)`\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle>
         = {x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}"
proof-
  let ?tc = "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  let ?SS = "concat_eNFSA_states(S1,S2)"
  have fsa:"(?SS,\<langle>s01,0\<rangle>,?tc,F2\<times>{1}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using concat_eNFSA_valid[OF fin A1 A2] .
  have tT:"?tc : ?SS\<times>succ(\<Sigma>) \<rightarrow> Pow(?SS)"
    using fsa unfolding FullNFSA_def[OF fin] by auto
  have pair:"\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle> \<in> ?SS\<times>succ(\<Sigma>)"
    using sS1 unfolding concat_eNFSA_states_def by (auto intro: succI1)
  have "\<langle>\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle>, {x\<in>{\<langle>s02,1\<rangle>}. s\<in>F1}\<rangle> \<in> ?tc"
    unfolding concat_eNFSA_trans_def[OF fin A1 A2] using sS1 by auto
  then show ?thesis using apply_equality[OF _ tT, of "\<langle>\<langle>s,0\<rangle>,\<Sigma>\<rangle>"] pair by auto
qed

text\<open>The $\varepsilon$-transition of a component-1 state $\langle s,1\rangle$ is empty.\<close>

lemma concat_eNFSA_eps_comp1:
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and sS2:"s\<in>S2"
  shows "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)`\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle> = 0"
proof-
  let ?tc = "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  let ?SS = "concat_eNFSA_states(S1,S2)"
  have fsa:"(?SS,\<langle>s01,0\<rangle>,?tc,F2\<times>{1}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using concat_eNFSA_valid[OF fin A1 A2] .
  have tT:"?tc : ?SS\<times>succ(\<Sigma>) \<rightarrow> Pow(?SS)"
    using fsa unfolding FullNFSA_def[OF fin] by auto
  have pair:"\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle> \<in> ?SS\<times>succ(\<Sigma>)"
    using sS2 unfolding concat_eNFSA_states_def by (auto intro: succI1)
  have "\<langle>\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle>, 0\<rangle> \<in> ?tc"
    unfolding concat_eNFSA_trans_def[OF fin A1 A2] using sS2 by auto
  then show ?thesis using apply_equality[OF _ tT, of "\<langle>\<langle>s,1\<rangle>,\<Sigma>\<rangle>"] pair by auto
qed

text\<open>The normal transition of a component-0 state $\langle s,0\rangle$
is a transition of the first DFSA.\<close>

lemma concat_eNFSA_eps_comp0':
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and sS1:"s\<in>S1" and sig:"q\<in>\<Sigma>"
  shows "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)`\<langle>\<langle>s,0\<rangle>,q\<rangle>
         = {t1`\<langle>s,q\<rangle>}\<times>{0}"
proof-
  let ?tc = "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  let ?SS = "concat_eNFSA_states(S1,S2)"
  have fsa:"(?SS,\<langle>s01,0\<rangle>,?tc,F2\<times>{1}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using concat_eNFSA_valid[OF fin A1 A2] .
  have tT:"?tc : ?SS\<times>succ(\<Sigma>) \<rightarrow> Pow(?SS)"
    using fsa unfolding FullNFSA_def[OF fin] by auto
  have pair:"\<langle>\<langle>s,0\<rangle>,q\<rangle> \<in> ?SS\<times>succ(\<Sigma>)"
    using sS1 sig unfolding concat_eNFSA_states_def by auto
  have "\<langle>\<langle>\<langle>s,0\<rangle>,q\<rangle>, {t1`\<langle>s,q\<rangle>}\<times>{0}\<rangle> \<in> ?tc"
    unfolding concat_eNFSA_trans_def[OF fin A1 A2] using sS1 sig by auto
  then show ?thesis using apply_equality[OF _ tT, of "\<langle>\<langle>s,0\<rangle>,q\<rangle>"] pair by auto
qed

text\<open>The normal transition of a component-1 state $\langle s,1\rangle$ is
a normal transition of the second DFSA.\<close>

lemma concat_eNFSA_eps_comp1':
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and sS2:"s\<in>S2" and sig:"q\<in>\<Sigma>"
  shows "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)`\<langle>\<langle>s,1\<rangle>,q\<rangle> = {t2`\<langle>s,q\<rangle>}\<times>{1}"
proof-
  let ?tc = "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  let ?SS = "concat_eNFSA_states(S1,S2)"
  have fsa:"(?SS,\<langle>s01,0\<rangle>,?tc,F2\<times>{1}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using concat_eNFSA_valid[OF fin A1 A2] .
  have tT:"?tc : ?SS\<times>succ(\<Sigma>) \<rightarrow> Pow(?SS)"
    using fsa unfolding FullNFSA_def[OF fin] by auto
  have pair:"\<langle>\<langle>s,1\<rangle>,q\<rangle> \<in> ?SS\<times>succ(\<Sigma>)"
    using sS2 sig unfolding concat_eNFSA_states_def by (auto)
  have "\<langle>\<langle>\<langle>s,1\<rangle>,q\<rangle>, {t2`\<langle>s,q\<rangle>}\<times>{1}\<rangle> \<in> ?tc"
    unfolding concat_eNFSA_trans_def[OF fin A1 A2] using sS2 sig by auto
  then show ?thesis using apply_equality[OF _ tT, of "\<langle>\<langle>s,1\<rangle>,q\<rangle>"] pair by auto
qed

text\<open>The normal transition of a component-1 state $\langle s,1\rangle$ is
a normal transition of the second DFSA.\<close>

lemma concat_eNFSA_eps_closure:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma>
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  defines "s\<^sub>0 \<equiv> \<langle>s01,0\<rangle>"
  defines "F \<equiv> F2\<times>{1}"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and sig:"q\<in>Pow(S)"
  shows "\<epsilon>-cl(S,t,\<Sigma>,q) = q \<union> {x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1) \<noteq>0}"
proof
  from sig have sub:"q \<subseteq> concat_eNFSA_states(S1,S2)" unfolding S_def by auto
  {
    fix y assume "y\<in>\<epsilon>-cl(S,t,\<Sigma>,q)"
    then obtain P where P:"P\<in>Pow(S)" "y\<in>P" "\<langle>q,P\<rangle>\<in>({\<langle>Q,{s\<in>S. \<exists>q\<in>Q. s \<in> t`\<langle>q,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(S)}^*)"
      unfolding S_def t_def EpsilonClosure_def[OF fin concat_eNFSA_valid[OF fin A1 A2] sub] by auto
    let ?r = "{\<langle>Q,{s\<in>S. \<exists>q\<in>Q. s \<in> t`\<langle>q,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(S)}"
    {
      assume "\<langle>q,P\<rangle>\<in>id(field(?r))"
      then have "P=q" by auto
      with P(2) have "y:q" by auto
      then have "y: q \<union> {x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1) \<noteq>0}" by auto
    } moreover
    {
      assume "\<langle>q,P\<rangle>\<notin>id(field(?r))"
      moreover from P(3) have "\<langle>q,P\<rangle>\<in>id(field(?r))\<union>(?r O ?r^*)" using rtrancl_unfold by auto
      ultimately have "\<langle>q,P\<rangle>\<in>(?r O ?r^*)" by auto
      then obtain Q where q:"\<langle>q,Q\<rangle>\<in>?r^*" "\<langle>Q,P\<rangle>\<in>?r" using compE by auto
      from q(2) have p:"P={s\<in>S. \<exists>u\<in>Q. s\<in>t`\<langle>u,\<Sigma>\<rangle>}" "Q\<in>Pow(S)" by auto
      from P(2) p(1) obtain u where u:"u\<in>Q" "y\<in>t`\<langle>u,\<Sigma>\<rangle>" by auto
      {
        assume "u\<in>S1\<times>1"
        then obtain us where uu:"u=\<langle>us,0\<rangle>" "us\<in>S1" by auto
        then have t:"t`\<langle>u,\<Sigma>\<rangle> = {x\<in>{\<langle>s02,1\<rangle>}. us\<in>F1}" using concat_eNFSA_eps_comp0[OF fin A1 A2]
          unfolding t_def by auto
        {
          assume "us\<notin>F1"
          with t have False using u(2) by auto
        }
        then have "us\<in>F1" by auto
        with t have "t`\<langle>u,\<Sigma>\<rangle> = {\<langle>s02,1\<rangle>}" by auto
        with u(2) have "y=\<langle>s02,1\<rangle>" by auto moreover
        from uu(1) `us\<in>F1` have "u\<in>F1\<times>1" by auto
        ultimately have "u\<in>F1\<times>1" "y=\<langle>s02,1\<rangle>" by auto
      } moreover
      {
        assume as:"u\<notin>S1\<times>1"
        from u(1) p(2) have "u:(S1\<times>1)\<union>(S2\<times>{1})" unfolding concat_eNFSA_states_def S_def by auto
        with as have "u\<in>S2\<times>{1}" by auto
        then obtain sq where "sq\<in>S2" "u=\<langle>sq,1\<rangle>" by auto
        then have t:"t`\<langle>u,\<Sigma>\<rangle> = 0" using concat_eNFSA_eps_comp1[OF fin A1 A2] t_def by auto
        with u(2) have False by auto
      }
      ultimately
      have A:"u\<in>F1\<times>{0}" "y=\<langle>s02,1\<rangle>" by auto
      {
        assume "\<langle>q,Q\<rangle>\<in>id(field(?r))"
        then have "q=Q" by auto
        with A(1) u(1) have "q\<inter>(F1\<times>1)\<noteq>0" by auto
        with A(2) have "y\<in>{x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1)\<noteq>0}" by auto
        then have "y\<in>q\<union>{x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1)\<noteq>0}" by auto
      } moreover
      {
        assume "\<langle>q,Q\<rangle>\<notin>id(field(?r))"
        moreover from q(1) have "\<langle>q,Q\<rangle>\<in>id(field(?r))\<union>(?r O ?r^*)" using rtrancl_unfold by auto
        ultimately have "\<langle>q,Q\<rangle>\<in>(?r O ?r^*)" by auto
        then obtain w where q:"\<langle>q,w\<rangle>\<in>?r^*" "\<langle>w,Q\<rangle>\<in>?r" using compE by auto
        from q(2) have "Q={s\<in>S. \<exists>g\<in>w. s\<in>t`\<langle>g,\<Sigma>\<rangle>}" "w\<in>Pow(S)" by auto
        with u(1) obtain v where v:"v\<in>w" "u\<in>t`\<langle>v,\<Sigma>\<rangle>" by auto
        {
           assume "v\<in>S1\<times>1"
          then obtain us where uu:"v=\<langle>us,0\<rangle>" "us\<in>S1" by auto
          then have t:"t`\<langle>v,\<Sigma>\<rangle> = {x\<in>{\<langle>s02,1\<rangle>}. us\<in>F1}" using concat_eNFSA_eps_comp0[OF fin A1 A2]
            unfolding t_def by auto
          {
            assume "us\<notin>F1"
            with t have False using v(2) by auto
          }
          then have "us\<in>F1" by auto
          with t have "t`\<langle>v,\<Sigma>\<rangle> = {\<langle>s02,1\<rangle>}" by auto
          with v(2) have "u=\<langle>s02,1\<rangle>" by auto
          with A(1) have False by auto
        }
        then have as:"v\<notin>S1\<times>1" by auto
        from v(1) `w\<in>Pow(S)` have "v:(S1\<times>1)\<union>(S2\<times>{1})" unfolding concat_eNFSA_states_def S_def by auto
        with as have "v\<in>S2\<times>{1}" by auto
        then obtain sq where "sq\<in>S2" "v=\<langle>sq,1\<rangle>" by auto
        then have t:"t`\<langle>v,\<Sigma>\<rangle> = 0" using concat_eNFSA_eps_comp1[OF fin A1 A2] t_def by auto
        with v(2) have False by auto
      } ultimately
      have "y\<in>q\<union>{x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1)\<noteq>0}" by blast
    } ultimately
    have "y\<in>q\<union>{x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1)\<noteq>0}" by blast
  }
  then show "\<epsilon>-cl(S, t, \<Sigma>, q) \<subseteq>
    q \<union>
    {x \<in> {\<langle>s02, 1\<rangle>}.
     q \<inter> F1 \<times> 1 \<noteq> \<emptyset>}" by blast
next
  from sig have sub:"q \<subseteq> concat_eNFSA_states(S1,S2)" unfolding S_def by auto 
  from A1 have subSt:"F1 \<subseteq> S1" unfolding DFSA_def[OF fin] by auto
  from A2 have init2:"s02\<in>S2" unfolding DFSA_def[OF fin] by auto
  let ?r = "{\<langle>Q,{s\<in>S. \<exists>q\<in>Q. s \<in> t`\<langle>q,\<Sigma>\<rangle>}\<rangle>. Q\<in>Pow(S)}"
  {
    fix y assume as:"y\<in>q\<union>{x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1)\<noteq>0}"
    {
      assume "y\<in>q"
      then have "y\<in>\<epsilon>-cl(S, t, \<Sigma>, q)" using epsilon_cl_refl_sub[OF fin concat_eNFSA_valid[OF fin A1 A2] sub]
        S_def t_def by auto
    } moreover
    {
      assume "y\<notin>q"
      with as have as:"y\<in>{x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1)\<noteq>0}" by auto
      {
        assume "q\<inter>(F1\<times>1) = 0"
        with as have False by auto
      }
      then have ne:"q\<inter>(F1\<times>1)\<noteq>0" by auto
      with as have y:"y=\<langle>s02,1\<rangle>" by auto
      from ne obtain qq where qq:"qq\<in>F1" "\<langle>qq,0\<rangle>\<in>q" by auto
      from qq(1) have "t`\<langle>\<langle>qq,0\<rangle>,\<Sigma>\<rangle> = {y}" using y concat_eNFSA_eps_comp0[OF fin A1 A2, of qq] subSt t_def by auto
      then have "y:t`\<langle>\<langle>qq,0\<rangle>,\<Sigma>\<rangle>" by auto
      with qq(2) have "\<exists>m\<in>q. y\<in>t`\<langle>m,\<Sigma>\<rangle>" by blast
      moreover have "y:S" using y init2 S_def concat_eNFSA_states_def by auto
      ultimately have B:"y\<in>{s\<in>S. \<exists>m\<in>q. s\<in>t`\<langle>m,\<Sigma>\<rangle>}" by auto
      have "\<langle>q,{s\<in>S. \<exists>m\<in>q. s\<in>t`\<langle>m,\<Sigma>\<rangle>}\<rangle>\<in>?r" using sig by auto
      then have "\<langle>q,{s\<in>S. \<exists>m\<in>q. s\<in>t`\<langle>m,\<Sigma>\<rangle>}\<rangle>\<in>?r^*" using r_into_rtrancl by auto
      then have "{s\<in>S. \<exists>m\<in>q. s\<in>t`\<langle>m,\<Sigma>\<rangle>} \<subseteq> \<epsilon>-cl(S, t, \<Sigma>, q)"
        using EpsilonClosure_def[OF fin concat_eNFSA_valid[OF fin A1 A2] sub]
          S_def t_def by auto
      with B have "y\<in>\<epsilon>-cl(S, t, \<Sigma>, q)" by auto
    }
    ultimately have "y\<in>\<epsilon>-cl(S, t, \<Sigma>, q)" by auto
  }
  then show "q \<union>
    {x \<in> {\<langle>s02, 1\<rangle>}.
     q \<inter> F1 \<times> 1 \<noteq> \<emptyset>} \<subseteq> \<epsilon>-cl(S, t, \<Sigma>, q)" by auto
qed

text\<open>Once L2 is reached, the relation is equivalent to its DFSA\<close>

lemma concat_FSA_apply_L2_step:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma>
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  defines "s\<^sub>0 \<equiv> \<langle>s01,0\<rangle>"
  defines "F \<equiv> F2\<times>{1}"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and j:"\<langle>\<langle>j,p\<rangle>,\<langle>r,q\<rangle>\<rangle>\<in>({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)^*" "j\<noteq>0"
  and states:"\<langle>p,1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,P)" "P\<in>Pow(S)"
  shows "\<exists>Q\<in>Pow(S). \<langle>q,1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,Q) \<and> (\<langle>\<langle>j,P\<rangle>,\<langle>r,Q\<rangle>\<rangle>\<in>(({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*))"
proof-
  let ?r="{reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>"
  from j(1) have "\<langle>j,p\<rangle>\<in>field(({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)^*)" using fieldI1 by auto
  then have "\<langle>j,p\<rangle>\<in>field({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)" using rtrancl_field by auto
  then have jl:"j\<in>Lists(\<Sigma>)" using DetFinStateAuto.reduce_field(1) A2 unfolding DetFinStateAuto_def
    using fin by blast
  have "\<exists>Q\<in>Pow(S). \<langle>snd(\<langle>r, q\<rangle>),1\<rangle> \<in> \<epsilon>-cl(S,t,\<Sigma>,Q) \<and> \<langle>\<langle>j, P\<rangle>, fst(\<langle>r,q\<rangle>), Q\<rangle> \<in> ?r^*"
  proof(rule rtrancl_induct[OF j(1), where P="\<lambda>s. \<exists>Q\<in>Pow(S). \<langle>snd(s),1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,Q) \<and> (\<langle>\<langle>j,P\<rangle>,\<langle>fst(s),Q\<rangle>\<rangle>\<in>(?r^*))"])
    have "j\<in>NELists(\<Sigma>)" using non_zero_List_func_is_NEList j(2) jl by auto
    with states(2) have "\<langle>j,P\<rangle>\<in>field(?r)" using eps_nfsa_field(2)[OF fin concat_eNFSA_valid[OF fin A1 A2]]
      S_def t_def s\<^sub>0_def by auto
    then have "\<langle>\<langle>j,P\<rangle>,\<langle>j,P\<rangle>\<rangle>\<in>?r^*" using rtrancl_refl by auto
    with states show "\<exists>Q\<in>Pow(S).
      \<langle>snd(\<langle>j, p\<rangle>),1\<rangle> \<in> \<epsilon>-cl(S,t,\<Sigma>,Q) \<and>
      \<langle>\<langle>j, P\<rangle>, fst(\<langle>j, p\<rangle>),
      Q\<rangle> \<in> ?r^*" by auto
  next
    fix y z assume as:"\<langle>\<langle>j,p\<rangle>,y\<rangle>\<in>({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)^*" 
    "\<langle>y,z\<rangle>\<in>({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)" 
    "\<exists>Q\<in>Pow(S). \<langle>snd(y),1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,Q) \<and> \<langle>\<langle>j,P\<rangle>,fst(y),Q\<rangle>\<in>?r^*" 
    from as(2) obtain yl ys where yz:"yl\<in>NELists(\<Sigma>)" "ys\<in>S2" "y=\<langle>yl,ys\<rangle>" "z=\<langle>Init(yl),t2`\<langle>ys,Last(yl)\<rangle>\<rangle>"
      unfolding DFSAExecutionRelation_def[OF fin A2] by auto
    from yz(3) as(3) obtain Qy where Q:"Qy\<in>Pow(S)" "\<langle>ys,1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)" "\<langle>\<langle>j,P\<rangle>,yl,Qy\<rangle>\<in>?r^*" by auto
    have "\<langle>\<langle>yl,Qy\<rangle>,Init(yl),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<rangle>\<in>?r"
      unfolding FullNFSAExecutionRelation_def[OF fin concat_eNFSA_valid[OF fin A1 A2]]
          S_def t_def s\<^sub>0_def using yz(1) Q(1) S_def by auto
    with Q(3) have "\<langle>\<langle>j,P\<rangle>,Init(yl),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<rangle>\<in>?r^*"
      using rtrancl_into_rtrancl by auto
    with yz(4) have A:"\<langle>\<langle>j,P\<rangle>,fst(z),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<rangle>\<in>?r^*" by auto
    from yz(1) have "Last(yl)\<in>\<Sigma>" using last_type by auto
    then have C1:"t`\<langle>\<langle>ys,1\<rangle>,Last(yl)\<rangle>={t2`\<langle>ys,Last(yl)\<rangle>}\<times>{1}" using concat_eNFSA_eps_comp1'[OF fin A1 A2 yz(2)]
      unfolding t_def by auto
    have tT:"t:S\<times>succ(\<Sigma>)\<rightarrow>Pow(S)" using concat_eNFSA_valid[OF fin A1 A2]
      unfolding t_def FullNFSA_def[OF fin] s\<^sub>0_def S_def by auto
    have unionS:"\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)} \<in> Pow(S)"
    proof
      {
        fix x assume "x \<in> \<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)}"
        then obtain ss where ss:"ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)" "x\<in>t`\<langle>ss,Last(yl)\<rangle>" by auto
        from Q(1) ss(1) have ssS:"ss\<in>S" using EpsilonClosure_def[OF fin concat_eNFSA_valid[OF fin A1 A2]]
          unfolding S_def t_def by auto
        have lastSig:"Last(yl)\<in>succ(\<Sigma>)" using last_type[OF yz(1)] by auto
        have "\<langle>ss,Last(yl)\<rangle>\<in>S\<times>succ(\<Sigma>)" using ssS lastSig by auto
        from apply_type[OF tT this] ss(2) have "x\<in>S" by auto
      }
      then show "\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)} \<subseteq> S" by auto
    qed
    then have B:"\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<in>Pow(S)" 
      using EpsilonClosure_def[OF fin concat_eNFSA_valid[OF fin A1 A2]] S_def t_def by auto
    then have D:"\<epsilon>-cl(S,t,\<Sigma>,\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})) = \<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})"
      using epsilon_cl_idem[OF fin concat_eNFSA_valid[OF fin A1 A2]] unionS S_def t_def by auto
    have "Qy \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,Qy)" using epsilon_cl_refl_sub[OF fin concat_eNFSA_valid[OF fin A1 A2]]
      using Q(1) S_def t_def by auto
    with Q(2) have s:"t`\<langle>\<langle>ys,1\<rangle>,Last(yl)\<rangle> \<subseteq> \<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)}" by auto
    with unionS have C2:"\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>\<langle>ys,1\<rangle>,Last(yl)\<rangle>) \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})"
      using epsilon_cl_mono[OF fin concat_eNFSA_valid[OF fin A1 A2]] unfolding S_def t_def by auto
    from unionS s have "t`\<langle>\<langle>ys,1\<rangle>,Last(yl)\<rangle> \<subseteq> S" by auto
    then have "t`\<langle>\<langle>ys,1\<rangle>,Last(yl)\<rangle> \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,t`\<langle>\<langle>ys,1\<rangle>,Last(yl)\<rangle>)" using
      epsilon_cl_refl_sub[OF fin concat_eNFSA_valid[OF fin A1 A2]]
      unfolding S_def t_def by auto
    with C1 C2 have "\<langle>t2`\<langle>ys,Last(yl)\<rangle>,1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})" by auto
    with D have C:"\<langle>t2`\<langle>ys,Last(yl)\<rangle>,1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(yl)\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)}))" by auto
    from A B C yz(4) show "\<exists>Q\<in>Pow(S). \<langle>snd(z),1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,Q) \<and> \<langle>\<langle>j,P\<rangle>,fst(z),Q\<rangle>\<in>?r^*" by auto
  qed
  then show ?thesis by auto
qed

text\<open>Once the only thing left is a word in L2, it passes if s02 is one of the initial
states.\<close>

lemma concat_FSA_apply_L2:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma>
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  defines "s\<^sub>0 \<equiv> \<langle>s01,0\<rangle>"
  defines "F \<equiv> F2\<times>{1}"
  defines "L1 \<equiv> {i\<in>Lists(\<Sigma>). i <-D (S1,s01,t1,F1){in alphabet}\<Sigma>}"
  defines "L2 \<equiv> {i\<in>Lists(\<Sigma>). i <-D (S2,s02,t2,F2){in alphabet}\<Sigma>}"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and j:"j\<in>L2" "\<langle>s02,1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)" "Q\<in>Pow(S)" "j\<noteq>0"
  shows "\<exists>q\<in>Pow(S). ((\<epsilon>-cl(S,t,\<Sigma>,q) \<inter> F \<noteq> \<emptyset>) \<and> (\<langle>\<langle>j,Q\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>(({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*)))"
proof-
  from j(4) j(1) have jne:"j\<in>NELists(\<Sigma>)" using non_zero_List_func_is_NEList unfolding L2_def by auto
  from j(1) have l2:"j <-D (S2,s02,t2,F2){in alphabet}\<Sigma>" "j\<in>Lists(\<Sigma>)" unfolding L2_def by auto
  from l2(1) j(4) have "\<exists>q\<in>F2. \<langle>\<langle>j, s02\<rangle>, \<emptyset>, q\<rangle> \<in> ({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)^*"
    unfolding DFSASatisfy_def[OF fin A2 l2(2)] by auto
  then obtain u where u:"u\<in>F2" "\<langle>\<langle>j,s02\<rangle>,0,u\<rangle>\<in>({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)^*"
    by auto
  have "\<exists>Qa\<in>Pow(S).
      \<langle>u, 1\<rangle> \<in> \<epsilon>-cl(S,t,\<Sigma>,Qa) \<and>
      \<langle>\<langle>j, Q\<rangle>, 0, Qa\<rangle> \<in>
      ({reduce \<epsilon>-N-relation} (S,t){in alphabet}\<Sigma>)^*"
    using concat_FSA_apply_L2_step[OF fin A1 A2 u(2) j(4)] 
    j(2,3) unfolding S_def t_def s\<^sub>0_def by auto
  then obtain H where h:"H\<in>Pow(S)" "\<langle>u,1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,H)" "\<langle>\<langle>j,Q\<rangle>,0,H\<rangle>\<in>({reduce \<epsilon>-N-relation} (S,t){in alphabet}\<Sigma>)^*"
    by auto
  from u(1) have "\<langle>u,1\<rangle>\<in>F" unfolding F_def by auto
  moreover note h(2)
  ultimately have "\<epsilon>-cl(S,t,\<Sigma>,H)\<inter>F\<noteq>0" by auto
  with h(1,3) show ?thesis by auto
qed

text\<open>Running a word of the form Concat(v,j) to v in a DFSA is
  the same as running j from the same starting state.\<close>

lemma (in DetFinStateAuto) dfa_run_suffix:
  assumes vL:"v\<in>Lists(\<Sigma>)" and jNE:"j\<in>NELists(\<Sigma>)"
    and run:"\<langle>\<langle>Concat(v,j),s\<rangle>,\<langle>v,q\<rangle>\<rangle>\<in>r\<^sub>D^*"
  shows "\<langle>\<langle>j,s\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>r\<^sub>D^*"
proof-
  from jNE obtain n where n:"n\<in>nat" "j:succ(n)\<rightarrow>\<Sigma>" unfolding NELists_def by auto
  let ?P="\<lambda>k. \<forall>v\<in>Lists(\<Sigma>). \<forall>j. j:succ(k)\<rightarrow>\<Sigma> \<longrightarrow>
      (\<forall>s q. \<langle>\<langle>Concat(v,j),s\<rangle>,\<langle>v,q\<rangle>\<rangle>\<in>r\<^sub>D^* \<longrightarrow> \<langle>\<langle>j,s\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>r\<^sub>D^*)"
  \<comment> \<open>Base case: j is a one-element list\<close>
  have base:"?P(0)"
  proof(intro ballI allI impI)
    fix v' j' s' q'
    assume vL':"v'\<in>Lists(\<Sigma>)" and j1':"j':succ(0)\<rightarrow>\<Sigma>"
      and run1':"\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle>\<in>r\<^sub>D^*"
    from j1' nat_0I have jNE':"j'\<in>NELists(\<Sigma>)" unfolding NELists_def by auto
    from j1' nat_0I have initj':"Init(j'):0\<rightarrow>\<Sigma>" using init_props(1)[of 0 j'] by auto
    then have initj'0:"Init(j')=0" unfolding Pi_def function_def by auto
    have lastj':"Last(j')\<in>\<Sigma>" using last_type[OF jNE'] by auto
    have Cvj':"Concat(v',j')\<in>NELists(\<Sigma>)" using concat_is_NElist[OF vL' jNE'] by auto
    \<comment> \<open>Extract first step: id case is impossible because domains differ\<close>
    have "\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle> \<in> id(field(r\<^sub>D)) \<union> (r\<^sub>D^* O r\<^sub>D)"
      using rtrancl_rev[of r\<^sub>D] run1' by auto
    then have "\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle> \<in> r\<^sub>D^* O r\<^sub>D"
    proof
      assume id:"\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle>\<in>id(field(r\<^sub>D))"
      then have ceq:"Concat(v',j')=v'" by auto
      from vL' obtain m where m:"m\<in>nat" "v':m\<rightarrow>\<Sigma>" unfolding Lists_def by auto
      have "Concat(v',j'):m#+succ(0)\<rightarrow>\<Sigma>" using concat_props(1)[OF m(1) nat_succI[OF nat_0I] m(2) j1'] by auto
      with ceq m(2) have "m#+succ(0) = m" using domain_of_fun[of v' m "\<lambda>_. \<Sigma>"] domain_of_fun[of "Concat(v',j')" "m #+ 1" "\<lambda>_. \<Sigma>"] by auto
      with m(1) have "succ(m) = m" using add_succ_right by auto moreover
      have "m\<in>succ(m)" by auto
      ultimately have "m\<in>m" using subst[of "succ(m)" m "\<lambda>q. m\<in>q"] by blast
      then show ?thesis using mem_irrefl[of m] by auto
    next
      assume "\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle> \<in> r\<^sub>D^* O r\<^sub>D" 
      then show "\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle> \<in> r\<^sub>D^* O r\<^sub>D" .
    qed
    then have "\<And>P. (\<And>y. \<langle>\<langle>Concat(v',j'),s'\<rangle>,y\<rangle>\<in>r\<^sub>D \<Longrightarrow> \<langle>y,\<langle>v',q'\<rangle>\<rangle>\<in>r\<^sub>D^* \<Longrightarrow> P) \<Longrightarrow> P"
      using compE[of "\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle>" "r\<^sub>D" "r\<^sub>D^*"] by auto
    then obtain y where step:"\<langle>\<langle>Concat(v',j'),s'\<rangle>,y\<rangle>\<in>r\<^sub>D" "\<langle>y,\<langle>v',q'\<rangle>\<rangle>\<in>r\<^sub>D^*" .
    from step(1) have yww:
      "y=\<langle>Init(Concat(v',j')),t`\<langle>s',Last(Concat(v',j'))\<rangle>\<rangle>"
      unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA] by auto
    have lastEq:"Last(Concat(v',j'))=Last(j')" using concat_last_NElist[OF vL' jNE'] by auto
    have initEq:"Init(Concat(v',j'))=Concat(v',Init(j'))"
      using concat_init_NElist[OF vL' jNE'] by auto
    from yww lastEq initEq initj'0 have yeq:
      "y=\<langle>Concat(v',0),t`\<langle>s',Last(j')\<rangle>\<rangle>" by auto
    have "Concat(v',0)=v'" using concat_0_left[OF vL'] by auto
    with yeq have yeq2:"y=\<langle>v',t`\<langle>s',Last(j')\<rangle>\<rangle>" by auto
    \<comment> \<open>Remaining run from v' forces q'=t(s',Last(j'))\<close>
    from step(2) yeq2 have remrun:"\<langle>\<langle>v',t`\<langle>s',Last(j')\<rangle>\<rangle>,\<langle>v',q'\<rangle>\<rangle>\<in>r\<^sub>D^*" by auto
    from remrun have "\<langle>v',t`\<langle>s',Last(j')\<rangle>\<rangle>\<in>field(r\<^sub>D)"
      using rtrancl_field relation_field_times_field[OF relation_rtrancl[of r\<^sub>D]] by auto
    then have rfld:"\<langle>\<langle>v',t`\<langle>s',Last(j')\<rangle>\<rangle>,\<langle>v',t`\<langle>s',Last(j')\<rangle>\<rangle>\<rangle>\<in>r\<^sub>D^*"
      using rtrancl_refl by auto
    from remrun rfld have q'eq:"q'=t`\<langle>s',Last(j')\<rangle>" using relation_deteministic by blast
    \<comment> \<open>One step on j' gives the conclusion\<close>
    have jstep:"\<langle>\<langle>j',s'\<rangle>,\<langle>Init(j'),t`\<langle>s',Last(j')\<rangle>\<rangle>\<rangle>\<in>r\<^sub>D"
  using step(1) unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA]
      using jNE' by auto
    from jstep initj'0 q'eq show "\<langle>\<langle>j',s'\<rangle>,\<langle>0,q'\<rangle>\<rangle>\<in>r\<^sub>D^*"
      using r_into_rtrancl by auto
  qed
  \<comment> \<open>Inductive step: Init(j) has type succ(k), apply IH\<close>
  have step:"\<And>k. k\<in>nat \<Longrightarrow> ?P(k) \<Longrightarrow> ?P(succ(k))"
  proof-
    fix k assume kn:"k\<in>nat" and IH:"?P(k)"
    show "?P(succ(k))"
    proof(intro ballI allI impI)
    fix v' j' s' q'
    assume vL':"v'\<in>Lists(\<Sigma>)" and jk':"j':succ(succ(k))\<rightarrow>\<Sigma>"
      and run':"\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle>\<in>r\<^sub>D^*"
    from jk' nat_succI[OF kn] have jNE':"j'\<in>NELists(\<Sigma>)" unfolding NELists_def by auto
    from jk' kn have initj':"Init(j'):succ(k)\<rightarrow>\<Sigma>" using init_props(1)[OF nat_succI[OF kn]] by auto
    then have initjNE':"Init(j')\<in>NELists(\<Sigma>)" unfolding NELists_def using kn by auto
    have lastj':"Last(j')\<in>\<Sigma>" using last_type[OF jNE'] by auto
    have Cvj':"Concat(v',j')\<in>NELists(\<Sigma>)" using concat_is_NElist[OF vL' jNE'] by auto
    \<comment> \<open>Extract first step\<close>
    have "\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle> \<in> id(field(r\<^sub>D)) \<union> (r\<^sub>D^* O r\<^sub>D)"
      using rtrancl_rev[of r\<^sub>D] run' by auto
    then have "\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle> \<in> r\<^sub>D^* O r\<^sub>D"
    proof
      assume id:"\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle>\<in>id(field(r\<^sub>D))"
      then have ceq:"Concat(v',j')=v'" by auto
      from vL' obtain m where m:"m\<in>nat" "v':m\<rightarrow>\<Sigma>" unfolding Lists_def by auto
      have A:"Concat(v',j'):m#+succ(succ(k))\<rightarrow>\<Sigma>" using concat_props(1)[OF m(1) _ m(2) jk'] nat_succI kn by auto
      from ceq have "domain(Concat(v',j')) = domain(v')" by auto
      with A have "m#+succ(succ(k)) = domain(v')" using domain_of_fun[of "Concat(v',j')" "m #+ succ(succ(k))" "\<lambda>_. \<Sigma>"]
        by auto
      with m(2) have "m#+succ(succ(k)) = m" using domain_of_fun[of v' m "\<lambda>_. \<Sigma>"] by blast
      with m(1) have "succ(m) = m" using add_succ_right by auto moreover
      have "m\<in>succ(m)" by auto
      ultimately have "m\<in>m" using subst[of "succ(m)" m "\<lambda>q. m\<in>q"] by blast
      then show ?thesis using mem_irrefl[of m] by auto
    next
      assume "\<langle>\<langle>Concat(v',j'),s'\<rangle>,\<langle>v',q'\<rangle>\<rangle> \<in> r\<^sub>D^* O r\<^sub>D" 
      then show ?thesis by assumption
    qed
    then obtain y where step':"\<langle>\<langle>Concat(v',j'),s'\<rangle>,y\<rangle>\<in>r\<^sub>D" "\<langle>y,\<langle>v',q'\<rangle>\<rangle>\<in>r\<^sub>D^*"
      using compE by auto
    from step'(1) obtain ww ss where yww:
      "ww\<in>NELists(\<Sigma>)" "ss\<in>S" "y=\<langle>Init(ww),t`\<langle>ss,Last(ww)\<rangle>\<rangle>"
      "\<langle>Concat(v',j'),s'\<rangle>=\<langle>ww,ss\<rangle>"
      unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA] by auto
    from yww(4) have wweq:"ww=Concat(v',j')" "ss=s'" by auto
    have lastEq:"Last(Concat(v',j'))=Last(j')" using concat_last_NElist[OF vL' jNE'] by auto
    have initEq:"Init(Concat(v',j'))=Concat(v',Init(j'))"
      using concat_init_NElist[OF vL' jNE'] by auto
    from yww(3) wweq lastEq initEq have yeq:
      "y=\<langle>Concat(v',Init(j')),t`\<langle>s',Last(j')\<rangle>\<rangle>" by auto
    from step'(2) yeq have remrun:
      "\<langle>\<langle>Concat(v',Init(j')),t`\<langle>s',Last(j')\<rangle>\<rangle>,\<langle>v',q'\<rangle>\<rangle>\<in>r\<^sub>D^*" by auto
    \<comment> \<open>Apply IH to Init(j') to get run from Init(j')\<close>
    from IH initj' vL' have
      "\<forall>s'' q''. \<langle>\<langle>Concat(v',Init(j')),s''\<rangle>,\<langle>v',q''\<rangle>\<rangle>\<in>r\<^sub>D^* \<longrightarrow>
          \<langle>\<langle>Init(j'),s''\<rangle>,\<langle>0,q''\<rangle>\<rangle>\<in>r\<^sub>D^*" by auto
    with remrun have IHresult:
      "\<langle>\<langle>Init(j'),t`\<langle>s',Last(j')\<rangle>\<rangle>,\<langle>0,q'\<rangle>\<rangle>\<in>r\<^sub>D^*" by auto
    \<comment> \<open>One step on j' then chain\<close>
    have jstep:"\<langle>\<langle>j',s'\<rangle>,\<langle>Init(j'),t`\<langle>s',Last(j')\<rangle>\<rangle>\<rangle>\<in>r\<^sub>D"
      unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA]
      using jNE' yww(2) wweq(2) by auto
    from jstep IHresult show "\<langle>\<langle>j',s'\<rangle>,\<langle>0,q'\<rangle>\<rangle>\<in>r\<^sub>D^*"
      using rtrancl_into_trancl2 trancl_into_rtrancl by auto
    qed
  qed
  from step have "?P(n)" using nat_induct[of _ ?P, OF n(1) base] by auto
  with vL n(2) run show ?thesis by auto
qed

text\<open>If a DFSA run reduces word w to word v, then v is an initial prefix of w,
i.e., there exists a suffix j with w = Concat(v,j).\<close>

lemma (in DetFinStateAuto) list_prefix_split:
  assumes run: "\<langle>\<langle>w,s\<rangle>,\<langle>v,q\<rangle>\<rangle> \<in> r\<^sub>D^*"
  shows "\<exists> j\<in>Lists(\<Sigma>). w = Concat(v,j)"
proof-
  have wL: "w\<in>Lists(\<Sigma>)"
  proof-
    from run have "\<langle>w,s\<rangle>\<in>field(r\<^sub>D^*)" using fieldI1 by auto
    then have "\<langle>w,s\<rangle>\<in>field(r\<^sub>D)"
      using rtrancl_field[of r\<^sub>D] relation_field_times_field[OF relation_rtrancl[of r\<^sub>D]] by auto
    then show ?thesis using reduce_field(1) by auto
  qed
  have "\<exists>j\<in>Lists(\<Sigma>). w = Concat(fst(\<langle>v,q\<rangle>),j)"
  proof(rule rtrancl_induct[OF run, where P="\<lambda>z. \<exists>j\<in>Lists(\<Sigma>). w = Concat(fst(z),j)"])
    have z:"0\<in>Lists(\<Sigma>)" unfolding Lists_def Pi_def function_def using nat_0I by auto
    with wL have "Concat(fst(\<langle>w,s\<rangle>),0) = w" using concat_0_left by auto
    with z show "\<exists>j\<in>Lists(\<Sigma>). w = Concat(fst(\<langle>w,s\<rangle>),j)" using exI[of "\<lambda>j. j\<in>Lists(\<Sigma>) \<and> w= Concat(fst(\<langle>w,s\<rangle>),j)" 0]
      by auto
  next
    fix y z
    assume "\<langle>\<langle>w,s\<rangle>,y\<rangle>\<in>r\<^sub>D^*" "\<langle>y,z\<rangle>\<in>r\<^sub>D" "\<exists>j\<in>Lists(\<Sigma>). w = Concat(fst(y),j)"
    from \<open>\<langle>y,z\<rangle>\<in>r\<^sub>D\<close> obtain y1 y2 where y:
      "y1\<in>NELists(\<Sigma>)" "y2\<in>S" "y=\<langle>y1,y2\<rangle>" "z=\<langle>Init(y1),t`\<langle>y2,Last(y1)\<rangle>\<rangle>"
      unfolding DFSAExecutionRelation_def[OF finite_alphabet DFSA] by auto
    from \<open>\<exists>j\<in>Lists(\<Sigma>). w = Concat(fst(y),j)\<close> y(3) obtain j where j:
      "j\<in>Lists(\<Sigma>)" "w = Concat(y1,j)" by auto
    from j(1) obtain m where m:"m\<in>nat" "j:m\<rightarrow>\<Sigma>" unfolding Lists_def by auto
    from y(1) obtain n where n:"n\<in>nat" "y1:succ(n)\<rightarrow>\<Sigma>" unfolding NELists_def by auto
    have lastY:"Last(y1)\<in>\<Sigma>" using last_type[OF y(1)] by auto
    have initY:"Init(y1):n\<rightarrow>\<Sigma>" using init_props(1)[OF n(1) n(2)] by auto
    have sing:"{\<langle>0,Last(y1)\<rangle>}:1\<rightarrow>\<Sigma>" using list_len1_singleton[OF lastY] by auto
    have y1eq:"y1 = Concat(Init(y1),{\<langle>0,Last(y1)\<rangle>})"
    proof-
      have "y1 = Append(Init(y1), Last(y1))"
        using init_props(3)[OF n(1) n(2)] last_seq_elem[OF n(2)] by auto
      also have "Append(Init(y1), Last(y1)) = Concat(Init(y1), {\<langle>0,Last(y1)\<rangle>})"
        using append_concat_pair[OF n(1) initY lastY] by auto
      finally show ?thesis .
    qed
    have assoc:"Concat(Concat(Init(y1),{\<langle>0,Last(y1)\<rangle>}),j) =
        Concat(Init(y1),Concat({\<langle>0,Last(y1)\<rangle>},j))"
      using concat_assoc[OF n(1) _ m(1) initY sing m(2)] by auto
    have jL:"Concat({\<langle>0,Last(y1)\<rangle>},j)\<in>Lists(\<Sigma>)"
    proof-
      have "{\<langle>0,Last(y1)\<rangle>}\<in>Lists(\<Sigma>)"
        using list_len1_singleton[OF lastY] one_is_nat unfolding Lists_def by auto
      then show ?thesis using concat_is_list[OF _ j(1)] by auto
    qed
    from j(2) y1eq assoc have "w = Concat(Init(y1), Concat({\<langle>0,Last(y1)\<rangle>},j))" by auto
    with jL y(4) show "\<exists>j'\<in>Lists(\<Sigma>). w = Concat(fst(z),j')" by auto
  qed
  then show ?thesis by auto
qed

text\<open>Once L1 is reached, the relation is equivalent to its DFSA\<close>

text\<open>Step 1: We prove concat\_FSA\_apply\_L1\_step using the three sub-lemmas above.
Note: the statement requires an additional hypothesis that the prefix s is a list over \<open>\<Sigma>\<close>.\<close>

lemma concat_FSA_apply_L1_step:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma>
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  defines "s\<^sub>0 \<equiv> \<langle>s01,0\<rangle>"
  defines "F \<equiv> F2\<times>{1}"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and j:"\<langle>\<langle>j,p\<rangle>,\<langle>r,q\<rangle>\<rangle>\<in>({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)^*" "j\<noteq>0"
  and states:"\<langle>p,0\<rangle>\<in>P" "P\<in>Pow(S)"
  and sL:"s\<in>Lists(\<Sigma>)"
  shows "\<exists>Q\<in>Pow(S). \<langle>q,0\<rangle>\<in>Q \<and> (\<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,r),Q\<rangle>\<rangle>\<in>(({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*))"
proof-
  let ?r="{reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>"
  from j(1) have "\<langle>j,p\<rangle>\<in>field(({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)^*)" using fieldI1 by auto
  then have "\<langle>j,p\<rangle>\<in>field({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)" using rtrancl_field by auto
  then have jl:"j\<in>Lists(\<Sigma>)" using DetFinStateAuto.reduce_field(1) A1 unfolding DetFinStateAuto_def
    using fin by blast
  have jne:"j\<in>NELists(\<Sigma>)" using non_zero_List_func_is_NEList j(2) jl by auto
  have Csj:"Concat(s,j)\<in>NELists(\<Sigma>)" using concat_is_NElist[OF sL jne] by auto
  have "\<exists>Q\<in>Pow(S). \<langle>snd(\<langle>r,q\<rangle>),0\<rangle>\<in>Q \<and> \<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,fst(\<langle>r,q\<rangle>)),Q\<rangle>\<rangle>\<in>?r^*"
  proof(rule rtrancl_induct[OF j(1), where P="\<lambda>v. \<exists>Q\<in>Pow(S). \<langle>snd(v),0\<rangle>\<in>Q \<and> (\<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,fst(v)),Q\<rangle>\<rangle>\<in>(?r^*))"])
    from states(2) have "\<langle>Concat(s,j),P\<rangle>\<in>field(?r)"
      using eps_nfsa_field(2)[OF fin concat_eNFSA_valid[OF fin A1 A2]]
      S_def t_def s\<^sub>0_def Csj by auto
    then have "\<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,j),P\<rangle>\<rangle>\<in>?r^*" using rtrancl_refl by auto
    with states show "\<exists>Q\<in>Pow(S).
      \<langle>snd(\<langle>j,p\<rangle>),0\<rangle>\<in>Q \<and>
      \<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,fst(\<langle>j,p\<rangle>)),Q\<rangle>\<rangle>\<in>?r^*" by auto
  next
    fix y z assume as:"\<langle>\<langle>j,p\<rangle>,y\<rangle>\<in>({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)^*"
      "\<langle>y,z\<rangle>\<in>({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)"
      "\<exists>Q\<in>Pow(S). \<langle>snd(y),0\<rangle>\<in>Q \<and> \<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,fst(y)),Q\<rangle>\<rangle>\<in>?r^*"
    from as(2) obtain yl ys where yz:"yl\<in>NELists(\<Sigma>)" "ys\<in>S1" "y=\<langle>yl,ys\<rangle>" "z=\<langle>Init(yl),t1`\<langle>ys,Last(yl)\<rangle>\<rangle>"
      unfolding DFSAExecutionRelation_def[OF fin A1] by auto
    from yz(3) as(3) obtain Qy where Q:"Qy\<in>Pow(S)" "\<langle>ys,0\<rangle>\<in>Qy" "\<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,yl),Qy\<rangle>\<rangle>\<in>?r^*"
      by auto
    have Csyl:"Concat(s,yl)\<in>NELists(\<Sigma>)" using concat_is_NElist[OF sL yz(1)] by auto
    have lastEq:"Last(Concat(s,yl)) = Last(yl)" using concat_last_NElist[OF sL yz(1)] by auto
    have initEq:"Init(Concat(s,yl)) = Concat(s,Init(yl))" using concat_init_NElist[OF sL yz(1)] by auto
    have "\<langle>\<langle>Concat(s,yl),Qy\<rangle>,Init(Concat(s,yl)),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(Concat(s,yl))\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<rangle>\<in>?r"
      unfolding FullNFSAExecutionRelation_def[OF fin concat_eNFSA_valid[OF fin A1 A2]]
          S_def t_def s\<^sub>0_def using Csyl Q(1) S_def by auto
    with lastEq initEq
    have step:"\<langle>\<langle>Concat(s,yl),Qy\<rangle>,Concat(s,Init(yl)),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<rangle>\<in>?r"
      by auto
    with Q(3) have "\<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,Init(yl)),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<rangle>\<rangle>\<in>?r^*"
      using rtrancl_into_rtrancl by auto
    with yz(4) have A:"\<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,fst(z)),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<rangle>\<rangle>\<in>?r^*"
      by auto
    from yz(1) have "Last(yl)\<in>\<Sigma>" using last_type by auto
    then have C1:"t`\<langle>\<langle>ys,0\<rangle>,Last(yl)\<rangle>={t1`\<langle>ys,Last(yl)\<rangle>}\<times>{0}"
      using concat_eNFSA_eps_comp0'[OF fin A1 A2 yz(2)] unfolding t_def by auto
    have tT:"t:S\<times>succ(\<Sigma>)\<rightarrow>Pow(S)" using concat_eNFSA_valid[OF fin A1 A2]
      unfolding t_def FullNFSA_def[OF fin] s\<^sub>0_def S_def by auto
    have unionS:"\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)}\<in>Pow(S)"
    proof
      { fix x assume "x\<in>\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)}"
        then obtain ss where ss:"ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)" "x\<in>t`\<langle>ss,Last(yl)\<rangle>" by auto
        from Q(1) ss(1) have ssS:"ss\<in>S" using S_def t_def
          EpsilonClosure_def[OF fin concat_eNFSA_valid[OF fin A1 A2]] by auto
        have lastSig:"Last(yl)\<in>succ(\<Sigma>)" using last_type[OF yz(1)] by auto
        have "\<langle>ss,Last(yl)\<rangle>\<in>S\<times>succ(\<Sigma>)" using ssS lastSig by auto
        from apply_type[OF tT this] ss(2) have "x\<in>S" by auto }
      then show "(\<Union>ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy). t`\<langle>ss,Last(yl)\<rangle>) \<subseteq> S" by auto
    qed
    then have B:"\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})\<in>Pow(S)"
      using EpsilonClosure_def[OF fin concat_eNFSA_valid[OF fin A1 A2]] S_def t_def by auto
    have "Qy \<subseteq> \<epsilon>-cl(S,t,\<Sigma>,Qy)" using epsilon_cl_refl_sub[OF fin concat_eNFSA_valid[OF fin A1 A2]]
      using Q(1) S_def t_def by auto
    with Q(2) have sub:"t`\<langle>\<langle>ys,0\<rangle>,Last(yl)\<rangle>\<subseteq>\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)}" by auto
    with unionS have C2:"\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>\<langle>ys,0\<rangle>,Last(yl)\<rangle>)\<subseteq>\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})"
      using epsilon_cl_mono[OF fin concat_eNFSA_valid[OF fin A1 A2]] unfolding S_def t_def by auto
    from unionS sub have "t`\<langle>\<langle>ys,0\<rangle>,Last(yl)\<rangle>\<subseteq>S" by auto
    then have "t`\<langle>\<langle>ys,0\<rangle>,Last(yl)\<rangle>\<subseteq>\<epsilon>-cl(S,t,\<Sigma>,t`\<langle>\<langle>ys,0\<rangle>,Last(yl)\<rangle>)"
      using epsilon_cl_refl_sub[OF fin concat_eNFSA_valid[OF fin A1 A2]]
      unfolding S_def t_def by auto
    with C1 C2 have C:"\<langle>t1`\<langle>ys,Last(yl)\<rangle>,0\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Qy)})" by auto
    from A B C yz(4) show "\<exists>Q\<in>Pow(S). \<langle>snd(z),0\<rangle>\<in>Q \<and> \<langle>\<langle>Concat(s,j),P\<rangle>,\<langle>Concat(s,fst(z)),Q\<rangle>\<rangle>\<in>?r^*"
      by auto
  qed
  then show ?thesis by auto
qed

text\<open>Once the only thing left is a word in L1, it passes if s01 is one of the initial
states.\<close>

lemma concat_FSA_apply_L1:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma>
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  defines "s\<^sub>0 \<equiv> \<langle>s01,0\<rangle>"
  defines "F \<equiv> F2\<times>{1}"
  defines "L1 \<equiv> {i\<in>Lists(\<Sigma>). i <-D (S1,s01,t1,F1){in alphabet}\<Sigma>}"
  defines "L2 \<equiv> {i\<in>Lists(\<Sigma>). i <-D (S2,s02,t2,F2){in alphabet}\<Sigma>}"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and j:"j\<in>L1" "\<langle>s01,0\<rangle>\<in>Q" "Q\<in>Pow(S)" "j\<noteq>0"
  and k:"u\<in>Lists(\<Sigma>)"
  shows "\<exists>q\<in>Pow(S). \<langle>s02,1\<rangle>\<in>q \<and> (\<langle>\<langle>Concat(u,j),Q\<rangle>,\<langle>u,q\<rangle>\<rangle>\<in>(({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*))"
proof-
  let ?r="({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)"
  from j(1) have jj:"j\<in>Lists(\<Sigma>)" "j <-D (S1,s01,t1,F1){in alphabet}\<Sigma>"
    unfolding L1_def by auto
  from jj(2) j(4) obtain q where q:"q\<in>F1" "\<langle>\<langle>j,s01\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in>({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)^*"
    unfolding DFSASatisfy_def[OF fin A1 jj(1)] by auto
  then obtain K where k_def:"K\<in>Pow(S)" "\<langle>q,0\<rangle>\<in>K" "\<langle>\<langle>Concat(u,j),Q\<rangle>,\<langle>Concat(u,0),K\<rangle>\<rangle>\<in>(({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*)"
    using concat_FSA_apply_L1_step[OF fin A1 A2 q(2) j(4,2), of u] j(3) k unfolding S_def t_def s\<^sub>0_def L2_def by auto
  have u:"Concat(u,0) = u" using k concat_0_left[of u] by auto
  {
    assume "\<langle>\<langle>Concat(u,j),Q\<rangle>,\<langle>Concat(u,0),K\<rangle>\<rangle>\<in>id(field(?r))"
    then have "Concat(u,j) = u" using u by auto moreover
    from k obtain n where u:"n\<in>nat" "u:n\<rightarrow>\<Sigma>" unfolding L2_def Lists_def by auto
    ultimately have "domain(Concat(u,j)) = n" using func1_1_L1 by auto
    moreover from jj(1) j(4) have "j:NELists(\<Sigma>)" using non_zero_List_func_is_NEList
      by auto
    then obtain k where jk:"k\<in>nat" "j:succ(k)\<rightarrow>\<Sigma>" unfolding NELists_def by auto
    from jk(2) u(2) have "Concat(u,j):n#+succ(k)\<rightarrow>\<Sigma>" using concat_props(1)[OF u(1) nat_succI[OF jk(1)]] by auto
    then have "domain(Concat(u,j)) = n#+succ(k)" using func1_1_L1 by auto
    ultimately have "n=n#+succ(k)" by blast
    then have "n#+0=n#+succ(k)" using add_0_right[OF u(1)] trans[of "n#+0" n "n#+succ(k)"] 
      by blast
    then have "0=succ(k)" using add_left_cancel[OF _ _ _ nat_succI[OF jk(1)], of n n 0] by auto
    then have False by auto
  } moreover
  {
    assume "\<langle>\<langle>Concat(u,j),Q\<rangle>,\<langle>Concat(u,0),K\<rangle>\<rangle>\<notin>id(field(?r))"
    moreover have "\<langle>\<langle>Concat(u,j),Q\<rangle>,\<langle>Concat(u,0),K\<rangle>\<rangle>\<in>id(field(?r))\<union>(?r O ?r^*)"
      using k_def(3) rtrancl_unfold by auto
    ultimately have "\<langle>\<langle>Concat(u,j),Q\<rangle>,\<langle>Concat(u,0),K\<rangle>\<rangle>\<in>(?r O ?r^*)" by auto
    then obtain P where P:"\<langle>\<langle>Concat(u,j),Q\<rangle>,P\<rangle>\<in>?r^*" "\<langle>P,\<langle>Concat(u,0),K\<rangle>\<rangle>\<in>?r" using compE by auto
    from P(2) have A:"K=\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(fst(P))\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,snd(P))})" "fst(P)\<in>NELists(\<Sigma>)"
      "snd(P)\<in>Pow(S)" using FullNFSAExecutionRelation_def[OF fin concat_eNFSA_valid[OF fin A1 A2]]
      S_def t_def s\<^sub>0_def by auto
    {
      fix w \<sigma> assume as:"w\<in>Pow(S)" "\<sigma>\<in>\<Sigma>"
      have type:"t:S\<times>succ(\<Sigma>)\<rightarrow>Pow(S)" using concat_eNFSA_valid[OF fin A1 A2]
          using FullNFSA_def[OF fin] S_def t_def by auto
      have s:"\<sigma>\<in>succ(\<Sigma>)" using as(2) by auto
      {
        fix m assume "m\<in>\<epsilon>-cl(S,t,\<Sigma>,w)"
        then have "m\<in>S" using as(1) EpsilonClosure_def[OF fin concat_eNFSA_valid[OF fin A1 A2]]
          S_def t_def by auto
        with s have "t`\<langle>m,\<sigma>\<rangle>\<in>Pow(S)" using apply_type[OF type] by auto
      }
      then have "\<Union>{t`\<langle>m,\<sigma>\<rangle>. m\<in>\<epsilon>-cl(S,t,\<Sigma>,w)} \<in>Pow(S)" by auto
    }
    moreover from A(2) have "Last(fst(P)):\<Sigma>" using last_type by auto
    moreover note A(3) ultimately
    have "\<Union>{t`\<langle>s,Last(fst(P))\<rangle>. s\<in>\<epsilon>-cl(S,t,\<Sigma>,snd(P))}\<in>Pow(S)" by auto
    with A(1) have A:"\<epsilon>-cl(S,t,\<Sigma>,K) = K" using epsilon_cl_idem[OF fin concat_eNFSA_valid[OF fin A1 A2]]
      S_def t_def s\<^sub>0_def k_def(1) by auto
    have "\<langle>s02,1\<rangle>\<in>\<epsilon>-cl(S,t,\<Sigma>,K)" using concat_eNFSA_eps_closure[OF fin A1 A2]
      k_def(1,2) q(1) unfolding S_def t_def by auto
    with A have "\<langle>s02,1\<rangle>\<in>K" by auto
  }
  ultimately have "\<langle>s02,1\<rangle>\<in>K" by auto
  with k_def(1,3) u show ?thesis by auto
qed

text\<open>The $\varepsilon$-closure of a set of side-1 states stays within side 1:
for $T \subseteq S_2$ we have $\varepsilon$-cl$(S,t,\Sigma,T\times\{1\}) = T\times\{1\}$.
This holds because the $\varepsilon$-transition from every side-1 state is empty
(by \<open>concat_eNFSA_eps_comp1\<close>), so the closure adds nothing.\<close>

lemma epsilon_cl_side1:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma>
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and sig:"T\<subseteq>S2"
  shows "\<epsilon>-cl(S,t,\<Sigma>,T\<times>{1}) = T\<times>{1}"
proof-
  have TS:"T\<times>{1}\<in>Pow(concat_eNFSA_states(S1,S2))"
    using sig unfolding concat_eNFSA_states_def by auto
  have eq:"\<epsilon>-cl(S,t,\<Sigma>,T\<times>{1}) = T\<times>{1} \<union> {x\<in>{\<langle>s02,1\<rangle>}. (T\<times>{1})\<inter>(F1\<times>1)\<noteq>0}"
    using concat_eNFSA_eps_closure[OF fin A1 A2 TS] unfolding S_def t_def by auto
  have "(T\<times>{1})\<inter>(F1\<times>1) = 0" by auto
  with eq show ?thesis by auto
qed

text\<open>One letter step in the concat $\varepsilon$-NFSA, starting from a state set
of the form $\{\langle q_1,0\rangle\} \cup Q_2\times\{1\}$, produces a state set of the
same form, with the side-0 singleton updated by the DFA transition of $A_1$.\<close>

lemma exec_step_form:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma> q1 Q2 ltr
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and q1S1:"q1\<in>S1" and Q2S2:"Q2\<subseteq>S2" and ltrS:"ltr\<in>\<Sigma>"
  shows "\<exists>Q2n\<in>Pow(S2). \<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,ltr\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1})})
                  = {\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>} \<union> Q2n\<times>{1}"
proof-
  have t1T:"t1:S1\<times>\<Sigma>\<rightarrow>S1" using A1 unfolding DFSA_def[OF fin] by auto
  have t2T:"t2:S2\<times>\<Sigma>\<rightarrow>S2" using A2 unfolding DFSA_def[OF fin] by auto
  have s02S2:"s02\<in>S2" using A2 unfolding DFSA_def[OF fin] by auto
  have q1'S1:"t1`\<langle>q1,ltr\<rangle>\<in>S1" using apply_type[OF t1T] q1S1 ltrS by auto
  have RS:"{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<in>Pow(concat_eNFSA_states(S1,S2))"
    using q1S1 Q2S2 unfolding concat_eNFSA_states_def by auto
  \<comment> \<open>epsilon-closure of the starting set\<close>
  have ecl:"\<epsilon>-cl(S,t,\<Sigma>,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}) =
    {\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<union>{x\<in>{\<langle>s02,1\<rangle>}. q1\<in>F1}"
  proof-
    have eq:"\<epsilon>-cl(S,t,\<Sigma>,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}) =
      ({\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}) \<union> {x\<in>{\<langle>s02,1\<rangle>}. ({\<langle>q1,0\<rangle>}\<union>Q2\<times>{1})\<inter>(F1\<times>1)\<noteq>0}"
      using concat_eNFSA_eps_closure[OF fin A1 A2 RS] unfolding S_def t_def by auto
    have "({\<langle>q1,0\<rangle>}\<union>Q2\<times>{1})\<inter>(F1\<times>1) = {x\<in>{\<langle>q1,0\<rangle>}. q1\<in>F1}"
      by auto
    with eq show ?thesis by auto
  qed
  \<comment> \<open>union of t-images over the epsilon-closure\<close>
  let ?cl = "{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<union>{x\<in>{\<langle>s02,1\<rangle>}. q1\<in>F1}"
  let ?U = "\<Union>{t`\<langle>ss,ltr\<rangle>. ss\<in>?cl}"
  have step0:"t`\<langle>\<langle>q1,0\<rangle>,ltr\<rangle> = {t1`\<langle>q1,ltr\<rangle>}\<times>{0}"
    using concat_eNFSA_eps_comp0'[OF fin A1 A2 q1S1 ltrS] unfolding t_def by auto
  have stepR:"\<And>r. r\<in>Q2 \<Longrightarrow> t`\<langle>\<langle>r,1\<rangle>,ltr\<rangle> = {t2`\<langle>r,ltr\<rangle>}\<times>{1}"
    using Q2S2 ltrS concat_eNFSA_eps_comp1'[OF fin A1 A2 _ ltrS] unfolding t_def by auto
  have stepS02:"t`\<langle>\<langle>s02,1\<rangle>,ltr\<rangle> = {t2`\<langle>s02,ltr\<rangle>}\<times>{1}"
    using concat_eNFSA_eps_comp1'[OF fin A1 A2 s02S2 ltrS] unfolding t_def by auto
  have Uform:"?U = {\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>} \<union>
    ({t2`\<langle>r,ltr\<rangle>. r\<in>Q2} \<union> {x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1}"
  proof(rule equalityI)
    { 
      fix x assume "x\<in>?U"
      then obtain ss where ss:"ss\<in>?cl" "x\<in>t`\<langle>ss,ltr\<rangle>" by auto
      from ss(1) have "ss=\<langle>q1,0\<rangle> \<or> (\<exists>r\<in>Q2. ss=\<langle>r,1\<rangle>) \<or> (q1\<in>F1 \<and> ss=\<langle>s02,1\<rangle>)" by blast
      moreover { assume "ss=\<langle>q1,0\<rangle>"
        with ss(2) step0 have "x=\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>" by auto
        then have "x\<in>{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}" by auto }
      moreover { assume "\<exists>r\<in>Q2. ss=\<langle>r,1\<rangle>"
        then obtain r where r:"r\<in>Q2" "ss=\<langle>r,1\<rangle>" by auto
        with ss(2) stepR[OF r(1)] have "x=\<langle>t2`\<langle>r,ltr\<rangle>,1\<rangle>" by auto
        with r(1) have "x\<in>{t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<times>{1}" by auto }
      moreover { assume "q1\<in>F1 \<and> ss=\<langle>s02,1\<rangle>"
        with ss(2) stepS02 have "x=\<langle>t2`\<langle>s02,ltr\<rangle>,1\<rangle>" by auto
        then have "x\<in>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1}\<times>{1}"
          using \<open>q1\<in>F1 \<and> ss=\<langle>s02,1\<rangle>\<close> by auto }
      ultimately have "x\<in>{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}\<union>({t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1}"
        by auto 
    }
    then show "?U \<subseteq> {\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}\<union>({t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1}" by blast
    { fix x assume
        "x\<in>{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}\<union>({t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1}"
      then have "x=\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle> \<or>
        (\<exists>r\<in>Q2. x=\<langle>t2`\<langle>r,ltr\<rangle>,1\<rangle>) \<or> (q1\<in>F1 \<and> x=\<langle>t2`\<langle>s02,ltr\<rangle>,1\<rangle>)" by blast
      moreover { assume "x=\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>"
        then have "x\<in>t`\<langle>\<langle>q1,0\<rangle>,ltr\<rangle>" using step0 by auto
        then have "x\<in>?U" by auto }
      moreover { assume "\<exists>r\<in>Q2. x=\<langle>t2`\<langle>r,ltr\<rangle>,1\<rangle>"
        then obtain r where r:"r\<in>Q2" "x=\<langle>t2`\<langle>r,ltr\<rangle>,1\<rangle>" by auto
        then have "x\<in>t`\<langle>\<langle>r,1\<rangle>,ltr\<rangle>" using stepR[OF r(1)] by auto
        with r(1) have "x\<in>?U" by auto }
      moreover { assume "q1\<in>F1 \<and> x=\<langle>t2`\<langle>s02,ltr\<rangle>,1\<rangle>"
        then have "x\<in>t`\<langle>\<langle>s02,1\<rangle>,ltr\<rangle>" using stepS02 by auto
        then have "x\<in>?U" using \<open>q1\<in>F1 \<and> x=_\<close> by auto }
      ultimately have "x\<in>?U" by blast }
    then show "{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}\<union>({t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1} \<subseteq> ?U"
      by blast
  qed
  (* Q2_mid \<subseteq> S2*)
  let ?Q2mid = "{t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1}"
  have Q2midS2:"?Q2mid \<subseteq> S2"
  proof
    fix x assume "x\<in>?Q2mid"
    then have "(\<exists>r\<in>Q2. x=t2`\<langle>r,ltr\<rangle>) \<or> (q1\<in>F1 \<and> x=t2`\<langle>s02,ltr\<rangle>)" by blast
    moreover { assume "\<exists>r\<in>Q2. x=t2`\<langle>r,ltr\<rangle>"
      then obtain r where r:"r\<in>Q2" "x=t2`\<langle>r,ltr\<rangle>" by auto
      from Q2S2 r(1) have "r\<in>S2" by auto
      with ltrS have "t2`\<langle>r,ltr\<rangle>\<in>S2" using apply_type[OF t2T] by auto
      with r(2) have "x\<in>S2" by auto }
    moreover { assume "q1\<in>F1 \<and> x=t2`\<langle>s02,ltr\<rangle>"
      with ltrS have "t2`\<langle>s02,ltr\<rangle>\<in>S2" using apply_type[OF t2T] s02S2 by auto
      then have "x\<in>S2" using \<open>q1\<in>F1 \<and> x=_\<close> by auto }
    ultimately show "x\<in>S2" by auto
  qed
  (* U \<in> Pow(S): needed for the second epsilon-closure*)
  have US:"?U\<in>Pow(concat_eNFSA_states(S1,S2))"
    using q1'S1 Q2midS2
    unfolding Uform concat_eNFSA_states_def by auto
  (* second epsilon-closure*)
  have ecl2:"\<epsilon>-cl(S,t,\<Sigma>,?U) = ?U \<union> {x\<in>{\<langle>s02,1\<rangle>}. ?U\<inter>(F1\<times>1)\<noteq>0}"
    using concat_eNFSA_eps_closure[OF fin A1 A2 US] unfolding S_def t_def by auto
  have Uint:"?U\<inter>(F1\<times>1) = {x\<in>{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}. t1`\<langle>q1,ltr\<rangle>\<in>F1}"
    unfolding Uform by auto
  have "\<epsilon>-cl(S,t,\<Sigma>,?U) = {\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>} \<union>
    (?Q2mid \<union> {x\<in>{s02}. t1`\<langle>q1,ltr\<rangle>\<in>F1})\<times>{1}"
    using ecl2 Uint Uform by auto
  moreover have "?Q2mid \<union> {x\<in>{s02}. t1`\<langle>q1,ltr\<rangle>\<in>F1} \<subseteq> S2"
    using Q2midS2 s02S2 by auto
  ultimately show ?thesis
    using ecl
    by (intro bexI[of _ "?Q2mid\<union>{x\<in>{s02}. t1`\<langle>q1,ltr\<rangle>\<in>F1}" "Pow(S2)"]) auto
qed

text\<open>Explicit form of the next state set after one step of the concat \<open>\<epsilon>\<close>-NFSA.\<close>

lemma exec_step_Q2_form:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma> q1 Q2 ltr
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and q1S1:"q1\<in>S1" and Q2S2:"Q2\<subseteq>S2" and ltrS:"ltr\<in>\<Sigma>"
  shows "\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,ltr\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1})})
       = {\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>} \<union>
         ({t2`\<langle>r,ltr\<rangle>. r\<in>Q2} \<union> {x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1} \<union>
          {x\<in>{s02}. t1`\<langle>q1,ltr\<rangle>\<in>F1})\<times>{1}"
proof-
  have t1T:"t1:S1\<times>\<Sigma>\<rightarrow>S1" using A1 unfolding DFSA_def[OF fin] by auto
  have t2T:"t2:S2\<times>\<Sigma>\<rightarrow>S2" using A2 unfolding DFSA_def[OF fin] by auto
  have s02S2:"s02\<in>S2" using A2 unfolding DFSA_def[OF fin] by auto
  have q1'S1:"t1`\<langle>q1,ltr\<rangle>\<in>S1" using apply_type[OF t1T] q1S1 ltrS by auto
  have RS:"{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<in>Pow(concat_eNFSA_states(S1,S2))"
    using q1S1 Q2S2 unfolding concat_eNFSA_states_def by auto
  have ecl:"\<epsilon>-cl(S,t,\<Sigma>,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}) =
    {\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<union>{x\<in>{\<langle>s02,1\<rangle>}. q1\<in>F1}"
  proof-
    have eq:"\<epsilon>-cl(S,t,\<Sigma>,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}) =
      ({\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}) \<union> {x\<in>{\<langle>s02,1\<rangle>}. ({\<langle>q1,0\<rangle>}\<union>Q2\<times>{1})\<inter>(F1\<times>1)\<noteq>0}"
      using concat_eNFSA_eps_closure[OF fin A1 A2 RS] unfolding S_def t_def by auto
    have "({\<langle>q1,0\<rangle>}\<union>Q2\<times>{1})\<inter>(F1\<times>1) = {x\<in>{\<langle>q1,0\<rangle>}. q1\<in>F1}"
      by auto
    with eq show ?thesis by auto
  qed
  let ?cl = "{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<union>{x\<in>{\<langle>s02,1\<rangle>}. q1\<in>F1}"
  let ?U = "\<Union>{t`\<langle>ss,ltr\<rangle>. ss\<in>?cl}"
  have step0:"t`\<langle>\<langle>q1,0\<rangle>,ltr\<rangle> = {t1`\<langle>q1,ltr\<rangle>}\<times>{0}"
    using concat_eNFSA_eps_comp0'[OF fin A1 A2 q1S1 ltrS] unfolding t_def by auto
  have stepR:"\<And>r. r\<in>Q2 \<Longrightarrow> t`\<langle>\<langle>r,1\<rangle>,ltr\<rangle> = {t2`\<langle>r,ltr\<rangle>}\<times>{1}"
    using Q2S2 ltrS concat_eNFSA_eps_comp1'[OF fin A1 A2 _ ltrS] unfolding t_def by auto
  have stepS02:"t`\<langle>\<langle>s02,1\<rangle>,ltr\<rangle> = {t2`\<langle>s02,ltr\<rangle>}\<times>{1}"
    using concat_eNFSA_eps_comp1'[OF fin A1 A2 s02S2 ltrS] unfolding t_def by auto
  have Uform:"?U = {\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>} \<union>
    ({t2`\<langle>r,ltr\<rangle>. r\<in>Q2} \<union> {x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1}"
  proof(rule equalityI)
    { fix x assume "x\<in>?U"
      then obtain ss where ss:"ss\<in>?cl" "x\<in>t`\<langle>ss,ltr\<rangle>" by auto
      from ss(1) have "ss=\<langle>q1,0\<rangle> \<or> (\<exists>r\<in>Q2. ss=\<langle>r,1\<rangle>) \<or> (q1\<in>F1 \<and> ss=\<langle>s02,1\<rangle>)" by blast
      moreover { assume "ss=\<langle>q1,0\<rangle>"
        with ss(2) step0 have "x=\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>" by auto
        then have "x\<in>{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}" by auto }
      moreover { assume "\<exists>r\<in>Q2. ss=\<langle>r,1\<rangle>"
        then obtain r where r:"r\<in>Q2" "ss=\<langle>r,1\<rangle>" by auto
        with ss(2) stepR[OF r(1)] have "x=\<langle>t2`\<langle>r,ltr\<rangle>,1\<rangle>" by auto
        with r(1) have "x\<in>{t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<times>{1}" by auto }
      moreover { assume "q1\<in>F1 \<and> ss=\<langle>s02,1\<rangle>"
        with ss(2) stepS02 have "x=\<langle>t2`\<langle>s02,ltr\<rangle>,1\<rangle>" by auto
        then have "x\<in>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1}\<times>{1}"
          using \<open>q1\<in>F1 \<and> ss=\<langle>s02,1\<rangle>\<close> by auto }
      ultimately have "x\<in>{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}\<union>({t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1}"
        by auto }
    then show "?U \<subseteq> {\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}\<union>({t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1}" by blast
    { fix x assume
        "x\<in>{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}\<union>({t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1}"
      then have "x=\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle> \<or>
        (\<exists>r\<in>Q2. x=\<langle>t2`\<langle>r,ltr\<rangle>,1\<rangle>) \<or> (q1\<in>F1 \<and> x=\<langle>t2`\<langle>s02,ltr\<rangle>,1\<rangle>)" by blast
      moreover { assume "x=\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>"
        then have "x\<in>t`\<langle>\<langle>q1,0\<rangle>,ltr\<rangle>" using step0 by auto
        then have "x\<in>?U" by auto }
      moreover { assume "\<exists>r\<in>Q2. x=\<langle>t2`\<langle>r,ltr\<rangle>,1\<rangle>"
        then obtain r where r:"r\<in>Q2" "x=\<langle>t2`\<langle>r,ltr\<rangle>,1\<rangle>" by auto
        then have "x\<in>t`\<langle>\<langle>r,1\<rangle>,ltr\<rangle>" using stepR[OF r(1)] by auto
        with r(1) have "x\<in>?U" by auto }
      moreover { assume "q1\<in>F1 \<and> x=\<langle>t2`\<langle>s02,ltr\<rangle>,1\<rangle>"
        then have "x\<in>t`\<langle>\<langle>s02,1\<rangle>,ltr\<rangle>" using stepS02 by auto
        then have "x\<in>?U" using \<open>q1\<in>F1 \<and> x=_\<close> by auto }
      ultimately have "x\<in>?U" by blast }
    then show "{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}\<union>({t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1})\<times>{1} \<subseteq> ?U"
      by blast
  qed
  let ?Q2mid = "{t2`\<langle>r,ltr\<rangle>. r\<in>Q2}\<union>{x\<in>{t2`\<langle>s02,ltr\<rangle>}. q1\<in>F1}"
  have US:"?U\<in>Pow(concat_eNFSA_states(S1,S2))"
  proof-
    have Q2midS2:"?Q2mid \<subseteq> S2"
    proof
      fix x assume "x\<in>?Q2mid"
      then have "(\<exists>r\<in>Q2. x=t2`\<langle>r,ltr\<rangle>) \<or> (q1\<in>F1 \<and> x=t2`\<langle>s02,ltr\<rangle>)" by blast
      moreover { assume "\<exists>r\<in>Q2. x=t2`\<langle>r,ltr\<rangle>"
        then obtain r where r:"r\<in>Q2" "x=t2`\<langle>r,ltr\<rangle>" by auto
        from Q2S2 r(1) have "r\<in>S2" by auto
        with ltrS have "t2`\<langle>r,ltr\<rangle>\<in>S2" using apply_type[OF t2T] by auto
        with r(2) have "x\<in>S2" by auto }
      moreover { assume "q1\<in>F1 \<and> x=t2`\<langle>s02,ltr\<rangle>"
        with ltrS have "t2`\<langle>s02,ltr\<rangle>\<in>S2" using apply_type[OF t2T] s02S2 by auto
        then have "x\<in>S2" using \<open>q1\<in>F1 \<and> x=_\<close> by auto }
      ultimately show "x\<in>S2" by auto
    qed
    show ?thesis using q1'S1 Q2midS2 unfolding Uform concat_eNFSA_states_def by auto
  qed
  have ecl2:"\<epsilon>-cl(S,t,\<Sigma>,?U) = ?U \<union> {x\<in>{\<langle>s02,1\<rangle>}. ?U\<inter>(F1\<times>1)\<noteq>0}"
    using concat_eNFSA_eps_closure[OF fin A1 A2 US] unfolding S_def t_def by auto
  have Uint:"?U\<inter>(F1\<times>1) = {x\<in>{\<langle>t1`\<langle>q1,ltr\<rangle>,0\<rangle>}. t1`\<langle>q1,ltr\<rangle>\<in>F1}"
    unfolding Uform by auto
  show ?thesis using ecl ecl2 Uint Uform by auto
qed

text\<open>If the concat $\varepsilon$-NFSA executes word $w$ (non-empty) from $\{\langle s_{01},0\rangle\}$
and reaches $\langle v,Q\rangle$, then $Q$ has the form $\{\langle q_1,0\rangle\}\cup Q_2\times\{1\}$
with $q_1\in S_1$, $Q_2\subseteq S_2$, and $A_1$ tracks the word: $\langle\langle w,s_{01}\rangle,\langle v,q_1\rangle\rangle\in r_{D_1}^*$.\<close>

lemma exec_state_form:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma> w v Q
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and wNE:"w\<in>NELists(\<Sigma>)"
  and run:"\<langle>\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>,\<langle>v,Q\<rangle>\<rangle> \<in> (({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*)"
  shows "\<exists>q1\<in>S1. \<exists>Q2\<in>Pow(S2). Q = {\<langle>q1,0\<rangle>} \<union> Q2\<times>{1} \<and>
         \<langle>\<langle>w,s01\<rangle>,\<langle>v,q1\<rangle>\<rangle>\<in>(({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)^*)"
proof-
  let ?r  = "{reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>"
  let ?rD = "{reduce D-relation}(S1,t1){in alphabet}\<Sigma>"
  have fsa:"(S,\<langle>s01,0\<rangle>,t,F2\<times>{1}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using concat_eNFSA_valid[OF fin A1 A2] unfolding S_def t_def by auto
  have s01S1:"s01\<in>S1" using A1 unfolding DFSA_def[OF fin] by auto
  have wfield:"\<langle>w,s01\<rangle>\<in>field(?rD)"
    using wNE s01S1 DetFinStateAuto.reduce_field(2)
    unfolding DetFinStateAuto_def using A1 fin by blast
  let ?P = "\<lambda>uR. \<exists>q1\<in>S1. \<exists>Q2\<in>Pow(S2). snd(uR) = {\<langle>q1,0\<rangle>}\<union>Q2\<times>{1} \<and>
              \<langle>\<langle>w,s01\<rangle>,\<langle>fst(uR),q1\<rangle>\<rangle>\<in>?rD^*"
  have "?P(\<langle>v,Q\<rangle>)"
  proof(rule rtrancl_induct[of "\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>" "\<langle>v,Q\<rangle>" ?r ?P])
    show "\<langle>\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>,\<langle>v,Q\<rangle>\<rangle>\<in>?r^*" using run .
    \<comment> \<open>base case: initial state set \<open>{\<langle>s01,0\<rangle>}\<close> has the form with q1=s01, \<open>Q2=\<emptyset>\<close>\<close>
    show "?P(\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>)"
      using rtrancl_refl[OF wfield] s01S1 by auto
  next
    fix y z
    assume IH_run:"\<langle>\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>,y\<rangle>\<in>?r^*"
      and step:"\<langle>y,z\<rangle>\<in>?r"
      and IH:"?P(y)"
    \<comment> \<open>unpack the \<open>\<epsilon>\<close>-NFSA step: first rewrite the hypothesis, then extract\<close>
    from step have step_unf:"\<langle>y,z\<rangle>\<in>{\<langle>\<langle>w,Q\<rangle>,\<langle>Init(w),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(w)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)})\<rangle>\<rangle>. \<langle>w,Q\<rangle>\<in>NELists(\<Sigma>)\<times>Pow(S)}"
      unfolding FullNFSAExecutionRelation_def[OF fin fsa] by simp
    from step_unf obtain yl R where yz:
      "yl\<in>NELists(\<Sigma>)" "R\<in>Pow(S)"
      "y=\<langle>yl,R\<rangle>"
      "z=\<langle>Init(yl),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,R)})\<rangle>"
      by auto
    \<comment> \<open>unpack the inductive hypothesis\<close>
    from IH yz(3) obtain q1 Q2 where IHd:
      "q1\<in>S1" "Q2\<in>Pow(S2)" "R={\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}"
      "\<langle>\<langle>w,s01\<rangle>,\<langle>yl,q1\<rangle>\<rangle>\<in>?rD^*"
      by auto
    have Q2S2:"Q2\<subseteq>S2" using IHd(2) by auto
    have aS:"Last(yl)\<in>\<Sigma>" using last_type[OF yz(1)] .
    \<comment> \<open>apply \<open>exec_step_form\<close> to get the new structured state\<close>
    from exec_step_form[OF fin A1 A2 IHd(1) Q2S2 aS]
    obtain Q2n where Q2n:"Q2n\<in>Pow(S2)"
      "\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1})})
       = {\<langle>t1`\<langle>q1,Last(yl)\<rangle>,0\<rangle>}\<union>Q2n\<times>{1}"
      unfolding S_def t_def by auto
    have zform:"z=\<langle>Init(yl),{\<langle>t1`\<langle>q1,Last(yl)\<rangle>,0\<rangle>}\<union>Q2n\<times>{1}\<rangle>"
      using yz(4) Q2n(2) IHd(3) by auto
    \<comment> \<open>DFA tracking: one more step of A1\<close>
    have t1S1:"t1`\<langle>q1,Last(yl)\<rangle>\<in>S1"
      using A1 IHd(1) aS unfolding DFSA_def[OF fin] by (auto intro: apply_type)
    have dfaStep:"\<langle>\<langle>yl,q1\<rangle>,\<langle>Init(yl),t1`\<langle>q1,Last(yl)\<rangle>\<rangle>\<rangle>\<in>?rD"
      unfolding DFSAExecutionRelation_def[OF fin A1] using yz(1) IHd(1) by auto
    have newDfa:"\<langle>\<langle>w,s01\<rangle>,\<langle>Init(yl),t1`\<langle>q1,Last(yl)\<rangle>\<rangle>\<rangle>\<in>?rD^*"
      using rtrancl_into_rtrancl[OF IHd(4) dfaStep] .
    \<comment> \<open>conclude: P(z) holds with \<open>q1_next=t1`\<langle>q1,Last(yl)\<rangle>\<close> and Q2n\<close>
    show "?P(z)" using zform t1S1 Q2n(1) newDfa by auto
  qed
  then show ?thesis by auto
qed

text\<open>For each component-2 state \<open>q2\<close> that appears in the state set reached by
the concat \<open>\<epsilon>\<close>-NFSA after reading non-empty word \<open>w\<close>, either (a) there is a
non-empty suffix \<open>yl_k\<close> of \<open>w\<close> such that A1 ran from \<open>s01\<close> to some \<open>f1\<in>F1\<close>
while consuming the complementary prefix, and A2 then ran from \<open>s02\<close> to \<open>q2\<close>
while consuming \<open>yl_k\<close>; or (b) \<open>q2 = s02\<close> and the \<open>\<epsilon>\<close>-jump into A2 happened
only at the very end, so A1 reached some \<open>f1\<in>F1\<close> after consuming all of \<open>w\<close>.\<close>

lemma exec_A2_component:
  fixes S1 S2 s01 s02 t1 t2 F1 F2 \<Sigma> w v q1 Q2 q2
  defines "t \<equiv> concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  defines "S \<equiv> concat_eNFSA_states(S1,S2)"
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and wNE:"w\<in>NELists(\<Sigma>)"
  and run:"\<langle>\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>,\<langle>v,{\<langle>q1,0\<rangle>} \<union> Q2\<times>{1}\<rangle>\<rangle>
             \<in> (({reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>)^*)"
  and q1S1:"q1\<in>S1"
  and Q2S2:"Q2\<in>Pow(S2)"
  and q2Q2:"q2\<in>Q2"
  shows "(\<exists>yl_k\<in>NELists(\<Sigma>). \<exists>f1\<in>F1.
            \<langle>\<langle>w,s01\<rangle>,\<langle>yl_k,f1\<rangle>\<rangle>\<in>({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)^* \<and>
            \<langle>\<langle>yl_k,s02\<rangle>,\<langle>v,q2\<rangle>\<rangle>\<in>({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)^*)
         \<or>
         (q2 = s02 \<and> (\<exists>f1\<in>F1.
            \<langle>\<langle>w,s01\<rangle>,\<langle>v,f1\<rangle>\<rangle>\<in>({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)^*))"
proof-
  let ?r\<epsilon> = "{reduce \<epsilon>-N-relation}(S,t){in alphabet}\<Sigma>"
  let ?rD1 = "{reduce D-relation}(S1,t1){in alphabet}\<Sigma>"
  let ?rD2 = "{reduce D-relation}(S2,t2){in alphabet}\<Sigma>"
  have s01S1:"s01\<in>S1" using A1 unfolding DFSA_def[OF fin] by auto
  have s02S2:"s02\<in>S2" using A2 unfolding DFSA_def[OF fin] by auto
  have t1T:"t1:S1\<times>\<Sigma>\<rightarrow>S1" using A1 unfolding DFSA_def[OF fin] by auto
  have t2T:"t2:S2\<times>\<Sigma>\<rightarrow>S2" using A2 unfolding DFSA_def[OF fin] by auto
  have fsa:"(S,\<langle>s01,0\<rangle>,t,F2\<times>{1}){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using concat_eNFSA_valid[OF fin A1 A2] unfolding S_def t_def by auto
  have wfieldD1:"\<langle>w,s01\<rangle>\<in>field(?rD1)"
    using wNE s01S1 DetFinStateAuto.reduce_field(2)
    unfolding DetFinStateAuto_def using A1 fin by blast
  \<comment> \<open>Enriched predicate: tracks A1 state and for every A2 state records \<open>case_a/case_b\<close>.\<close>
  let ?case_a = "\<lambda>q2' v'. \<exists>yl_k\<in>NELists(\<Sigma>). \<exists>f1\<in>F1.
      \<langle>\<langle>w,s01\<rangle>,\<langle>yl_k,f1\<rangle>\<rangle>\<in>?rD1^* \<and> \<langle>\<langle>yl_k,s02\<rangle>,\<langle>v',q2'\<rangle>\<rangle>\<in>?rD2^*"
  let ?case_b = "\<lambda>q2' v'. q2'=s02 \<and> (\<exists>f1\<in>F1. \<langle>\<langle>w,s01\<rangle>,\<langle>v',f1\<rangle>\<rangle>\<in>?rD1^*)"
  let ?P = "\<lambda>uR. \<exists>q1'\<in>S1. \<exists>Q2'\<in>Pow(S2). snd(uR) = {\<langle>q1',0\<rangle>}\<union>Q2'\<times>{1} \<and>
      \<langle>\<langle>w,s01\<rangle>,\<langle>fst(uR),q1'\<rangle>\<rangle>\<in>?rD1^* \<and>
      (\<forall>q2'\<in>Q2'. ?case_a(q2', fst(uR)) \<or> ?case_b(q2', fst(uR)))"
  have Pmain:"?P(\<langle>v, {\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<rangle>)"
  proof(rule rtrancl_induct[of "\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>" "\<langle>v,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<rangle>" ?r\<epsilon> ?P])
    show "\<langle>\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>,\<langle>v,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<rangle>\<rangle>\<in>?r\<epsilon>^*" using run .
    \<comment> \<open>Base: Q2'=\<open>\<emptyset>\<close>, vacuous \<open>\<forall>\<close>.\<close>
    show "?P(\<langle>w,{\<langle>s01,0\<rangle>}\<rangle>)"
      using rtrancl_refl[OF wfieldD1] s01S1 by auto
  next
    fix y z
    assume step:"\<langle>y,z\<rangle>\<in>?r\<epsilon>"
    assume IH:"?P(y)"
    \<comment> \<open>Unpack the \<open>\<epsilon>\<close>-NFSA step.\<close>
    from step have step_unf:
      "\<langle>y,z\<rangle>\<in>{\<langle>\<langle>w,Q\<rangle>,\<langle>Init(w),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(w)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,Q)})\<rangle>\<rangle>.
        \<langle>w,Q\<rangle>\<in>NELists(\<Sigma>)\<times>Pow(S)}"
      unfolding FullNFSAExecutionRelation_def[OF fin fsa] by simp
    from step_unf obtain yl R where yz:
      "yl\<in>NELists(\<Sigma>)" "R\<in>Pow(S)" "y=\<langle>yl,R\<rangle>"
      "z=\<langle>Init(yl),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>ss,Last(yl)\<rangle>. ss\<in>\<epsilon>-cl(S,t,\<Sigma>,R)})\<rangle>"
      by auto
    \<comment> \<open>Unpack the inductive hypothesis.\<close>
    from IH yz(3) obtain q1ih Q2ih where IHd:
      "q1ih\<in>S1" "Q2ih\<in>Pow(S2)" "R={\<langle>q1ih,0\<rangle>}\<union>Q2ih\<times>{1}"
      "\<langle>\<langle>w,s01\<rangle>,\<langle>yl,q1ih\<rangle>\<rangle>\<in>?rD1^*"
      "\<forall>q2'\<in>Q2ih. ?case_a(q2', yl) \<or> ?case_b(q2', yl)"
      by auto
    have Q2ihS2:"Q2ih\<subseteq>S2" using IHd(2) by auto
    have ltrS:"Last(yl)\<in>\<Sigma>" using last_type[OF yz(1)] .
    \<comment> \<open>Name the letter and the new A1 state.\<close>
    let ?ltr = "Last(yl)"
    let ?q1' = "t1`\<langle>q1ih,?ltr\<rangle>"
    \<comment> \<open>Explicit Q2n via \<open>exec_step_Q2_form\<close>.\<close>
    let ?Q2n = "{t2`\<langle>r,?ltr\<rangle>. r\<in>Q2ih} \<union> {x\<in>{t2`\<langle>s02,?ltr\<rangle>}. q1ih\<in>F1} \<union>
               {x\<in>{s02}. ?q1'\<in>F1}"
    have zform:"z=\<langle>Init(yl),{\<langle>?q1',0\<rangle>}\<union>?Q2n\<times>{1}\<rangle>"
      using exec_step_Q2_form[OF fin A1 A2 IHd(1) Q2ihS2 ltrS] yz(4) IHd(3)
      unfolding S_def t_def by auto
    have q1'S1:"?q1'\<in>S1" using apply_type[OF t1T] IHd(1) ltrS by auto
    have Q2nS2:"?Q2n\<in>Pow(S2)"
    proof-
      { fix x assume "x\<in>?Q2n"
        then have "(\<exists>r\<in>Q2ih. x=t2`\<langle>r,?ltr\<rangle>) \<or> (q1ih\<in>F1 \<and> x=t2`\<langle>s02,?ltr\<rangle>) \<or>
            (?q1'\<in>F1 \<and> x=s02)" by blast
        moreover { assume "\<exists>r\<in>Q2ih. x=t2`\<langle>r,?ltr\<rangle>"
          then obtain r where r:"r\<in>Q2ih" "x=t2`\<langle>r,?ltr\<rangle>" by auto
          from Q2ihS2 r(1) have "r\<in>S2" by auto
          with ltrS have "x\<in>S2" using r(2) apply_type[OF t2T] by auto }
        moreover { assume "q1ih\<in>F1 \<and> x=t2`\<langle>s02,?ltr\<rangle>"
          with ltrS s02S2 have "x\<in>S2" using apply_type[OF t2T] by auto }
        moreover { assume "?q1'\<in>F1 \<and> x=s02"
          with s02S2 have "x\<in>S2" by auto }
        ultimately have "x\<in>S2" by auto }
      then show ?thesis by auto
    qed
    \<comment> \<open>Extend the A1 DFA tracking by one step.\<close>
    have dfaStep1:"\<langle>\<langle>yl,q1ih\<rangle>,\<langle>Init(yl),?q1'\<rangle>\<rangle>\<in>?rD1"
      unfolding DFSAExecutionRelation_def[OF fin A1] using yz(1) IHd(1) by auto
    have newDfa1:"\<langle>\<langle>w,s01\<rangle>,\<langle>Init(yl),?q1'\<rangle>\<rangle>\<in>?rD1^*"
      using rtrancl_into_rtrancl[OF IHd(4) dfaStep1] .
    \<comment> \<open>For every \<open>q2'\<in>Q2n\<close> prove \<open>case_a\<close> or \<open>case_b\<close>.\<close>
    have allQ2n:"\<forall>q2'\<in>?Q2n. ?case_a(q2', Init(yl)) \<or> ?case_b(q2', Init(yl))"
    proof
      fix q2' assume q2'Q2n:"q2'\<in>?Q2n"
      from q2'Q2n have cases:"(\<exists>r\<in>Q2ih. q2'=t2`\<langle>r,?ltr\<rangle>) \<or>
          (q1ih\<in>F1 \<and> q2'=t2`\<langle>s02,?ltr\<rangle>) \<or> (?q1'\<in>F1 \<and> q2'=s02)"
        by blast
      moreover
      { \<comment> \<open>Case: \<open>q2'=t2(r,ltr)\<close> for some \<open>r\<in>Q2ih\<close>.\<close>
        assume "\<exists>r\<in>Q2ih. q2'=t2`\<langle>r,?ltr\<rangle>"
        then obtain r where r:"r\<in>Q2ih" "q2'=t2`\<langle>r,?ltr\<rangle>" by auto
        from Q2ihS2 r(1) have rS2:"r\<in>S2" by auto
        from IHd(5) r(1) have IHr:"?case_a(r, yl) \<or> ?case_b(r, yl)" by auto
        moreover
        { assume ca:"?case_a(r, yl)"
          then obtain yk f1 where yk:
            "yk\<in>NELists(\<Sigma>)" "f1\<in>F1"
            "\<langle>\<langle>w,s01\<rangle>,\<langle>yk,f1\<rangle>\<rangle>\<in>?rD1^*"
            "\<langle>\<langle>yk,s02\<rangle>,\<langle>yl,r\<rangle>\<rangle>\<in>?rD2^*" by auto
          have step2:"\<langle>\<langle>yl,r\<rangle>,\<langle>Init(yl),t2`\<langle>r,?ltr\<rangle>\<rangle>\<rangle>\<in>?rD2"
            unfolding DFSAExecutionRelation_def[OF fin A2] using yz(1) rS2 by auto
          have nd2:"\<langle>\<langle>yk,s02\<rangle>,\<langle>Init(yl),t2`\<langle>r,?ltr\<rangle>\<rangle>\<rangle>\<in>?rD2^*"
            using rtrancl_into_rtrancl[OF yk(4) step2] .
          have "?case_a(q2', Init(yl))"
            using yk(1,2,3) nd2 r(2) by auto }
        moreover
        { assume cb:"?case_b(r, yl)"
          then have rs02:"r=s02" and "\<exists>f1\<in>F1. \<langle>\<langle>w,s01\<rangle>,\<langle>yl,f1\<rangle>\<rangle>\<in>?rD1^*" by auto
          then obtain f1H where f1H:"f1H\<in>F1" "\<langle>\<langle>w,s01\<rangle>,\<langle>yl,f1H\<rangle>\<rangle>\<in>?rD1^*" by auto
          have step2:"\<langle>\<langle>yl,s02\<rangle>,\<langle>Init(yl),t2`\<langle>s02,?ltr\<rangle>\<rangle>\<rangle>\<in>?rD2"
            unfolding DFSAExecutionRelation_def[OF fin A2] using yz(1) s02S2 by auto
          have nd2:"\<langle>\<langle>yl,s02\<rangle>,\<langle>Init(yl),t2`\<langle>s02,?ltr\<rangle>\<rangle>\<rangle>\<in>?rD2^*"
            using r_into_rtrancl step2 by auto
          have "?case_a(q2', Init(yl))"
            using yz(1) f1H(1,2) nd2 r(2) rs02 by auto }
        ultimately have "?case_a(q2', Init(yl)) \<or> ?case_b(q2', Init(yl))" by auto }
      moreover
      { \<comment> \<open>Case: \<open>q1ih\<in>F1\<close> so A2 enters via \<open>\<epsilon>\<close>-jump and takes one step.\<close>
        assume "q1ih\<in>F1 \<and> q2'=t2`\<langle>s02,?ltr\<rangle>"
        then have q1ihF1:"q1ih\<in>F1" and q2form:"q2'=t2`\<langle>s02,?ltr\<rangle>" by auto
        have step2:"\<langle>\<langle>yl,s02\<rangle>,\<langle>Init(yl),t2`\<langle>s02,?ltr\<rangle>\<rangle>\<rangle>\<in>?rD2"
          unfolding DFSAExecutionRelation_def[OF fin A2] using yz(1) s02S2 by auto
        have nd2:"\<langle>\<langle>yl,s02\<rangle>,\<langle>Init(yl),t2`\<langle>s02,?ltr\<rangle>\<rangle>\<rangle>\<in>?rD2^*"
          using r_into_rtrancl step2 by auto
        have "?case_a(q2', Init(yl))"
          using yz(1) q1ihF1 IHd(4) nd2 q2form by auto }
      moreover
      { \<comment> \<open>Case: \<open>q1'\<in>F1\<close> so A2 enters at \<open>s02\<close> after this step.\<close>
        assume "?q1'\<in>F1 \<and> q2'=s02"
        then have "?case_b(q2', Init(yl))"
          using newDfa1 by auto }
      ultimately show "?case_a(q2', Init(yl)) \<or> ?case_b(q2', Init(yl))" by auto
    qed
    \<comment> \<open>Assemble \<open>?P(z)\<close>: simplify \<open>fst\<close>/\<open>snd\<close> first, then introduce witnesses.\<close>
    show "?P(z)"
    proof-
      from zform have fstZ:"fst(z) = Init(yl)"
        and sndZ:"snd(z) = {\<langle>?q1',0\<rangle>}\<union>?Q2n\<times>{1}" by auto
      have nd1:"\<langle>\<langle>w,s01\<rangle>,\<langle>fst(z),?q1'\<rangle>\<rangle>\<in>?rD1^*" using fstZ newDfa1 by auto
      have allz:"\<forall>q2''\<in>?Q2n. ?case_a(q2'', fst(z)) \<or> ?case_b(q2'', fst(z))"
        using fstZ allQ2n by auto
      have "\<exists>q1''\<in>S1. \<exists>Q2''\<in>Pow(S2). snd(z) = {\<langle>q1'',0\<rangle>}\<union>Q2''\<times>{1} \<and>
            \<langle>\<langle>w,s01\<rangle>,\<langle>fst(z),q1''\<rangle>\<rangle>\<in>?rD1^* \<and>
            (\<forall>q2''\<in>Q2''. ?case_a(q2'', fst(z)) \<or> ?case_b(q2'', fst(z)))"
        using q1'S1 Q2nS2 sndZ nd1 allz
        by (intro bexI[of _ ?q1' S1] bexI[of _ ?Q2n "Pow(S2)"]) auto
      then show ?thesis by auto
    qed
  qed
  \<comment> \<open>Extract conclusion from \<open>Pmain\<close>.\<close>
  from Pmain obtain q1p Q2p where Pd:
    "q1p\<in>S1" "Q2p\<in>Pow(S2)"
    "{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1} = {\<langle>q1p,0\<rangle>}\<union>Q2p\<times>{1}"
    "\<langle>\<langle>w,s01\<rangle>,\<langle>v,q1p\<rangle>\<rangle>\<in>?rD1^*"
    "\<forall>q2'\<in>Q2p. ?case_a(q2', v) \<or> ?case_b(q2', v)"
    by auto
  have q2Q2p:"q2\<in>Q2p"
  proof-
    have "\<langle>q2,1\<rangle>\<in>Q2\<times>{1}" using q2Q2 by auto
    then have "\<langle>q2,1\<rangle>\<in>{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}" by auto
    with Pd(3) have "\<langle>q2,1\<rangle>\<in>{\<langle>q1p,0\<rangle>}\<union>Q2p\<times>{1}" by auto
    then show "q2\<in>Q2p" by auto
  qed
  from Pd(5) q2Q2p show ?thesis by auto
qed

text\<open>The language of the product \<open>\<epsilon>\<close>-NFSA equals the concatenation
of the two component languages.\<close>

lemma concat_eNFSA_language:
  assumes fin:"Finite(\<Sigma>)"
  and A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
  and A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
  and L1_def:"L1 = {i\<in>Lists(\<Sigma>). i <-D (S1,s01,t1,F1){in alphabet}\<Sigma>}"
  and L2_def:"L2 = {i\<in>Lists(\<Sigma>). i <-D (S2,s02,t2,F2){in alphabet}\<Sigma>}"
  shows "{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (concat_eNFSA_states(S1,S2),
             \<langle>s01,0\<rangle>,
             concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>),
             F2\<times>{1}){in alphabet}\<Sigma>}
        = concat(L1,L2)"
proof-
  have lang1:"L1 {is a language with alphabet}\<Sigma>"
    using L1_def unfolding IsALanguage_def[OF fin] by auto
  have lang2:"L2 {is a language with alphabet}\<Sigma>"
    using L2_def unfolding IsALanguage_def[OF fin] by auto
  let ?s\<^sub>0="\<langle>s01,0\<rangle>"
  let ?S="concat_eNFSA_states(S1,S2)"
  let ?t="concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  let ?F="F2\<times>{1}"
  have ss:"?s\<^sub>0\<in>?S" unfolding concat_eNFSA_states_def using A1 unfolding DFSA_def[OF fin] by auto
  then have ss2:"{?s\<^sub>0} \<subseteq> ?S" by auto
  then have ss3:"{?s\<^sub>0}\<in>Pow(?S)" by auto
  {
    fix i assume "i\<in>{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}"
    then have i:"i\<in>Lists(\<Sigma>)" "i <-\<epsilon>-N (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>" by auto
    from i(2) have r:"(\<exists>q\<in>Pow(?S). (\<epsilon>-cl(?S,?t,\<Sigma>,q) \<inter> ?F \<noteq> \<emptyset>) \<and>
      (\<langle>\<langle>i, {?s\<^sub>0}\<rangle>, \<emptyset>, q\<rangle> \<in>
      (({reduce \<epsilon>-N-relation}(?S,?t){in alphabet}\<Sigma>)^*)))\<or>(i=0 \<and> \<epsilon>-cl(?S,?t,\<Sigma>,{?s\<^sub>0}) \<inter> ?F \<noteq> \<emptyset>)"
      unfolding FullNFSASatisfy_def[OF fin concat_eNFSA_valid[OF fin A1 A2] i(1)] by auto
    {
      assume i0:"i=0" and ecl:"\<epsilon>-cl(?S,?t,\<Sigma>,{?s\<^sub>0}) \<inter> ?F \<noteq> \<emptyset>"
      have "\<epsilon>-cl(?S,?t,\<Sigma>,{?s\<^sub>0}) = {?s\<^sub>0}\<union>{x\<in>{\<langle>s02,1\<rangle>}. s01\<in>F1}" using concat_eNFSA_eps_closure[OF fin A1 A2 ss3] by auto
      moreover have "?s\<^sub>0\<notin>?F" by auto
      ultimately have "\<epsilon>-cl(?S,?t,\<Sigma>,{?s\<^sub>0}) \<inter> ?F = {x\<in>{\<langle>s02,1\<rangle>}. s01\<in>F1}\<inter>?F" by auto
      with ecl obtain p where p:"p\<in>?F" "p\<in>{x\<in>{\<langle>s02,1\<rangle>}. s01\<in>F1}" by auto
      {
        assume "s01\<notin>F1"
        with p(2) have False by auto
      }
      then have s01F1:"s01\<in>F1" by auto
      with p(2) have "p=\<langle>s02,1\<rangle>"  by auto
      with p(1) have s02F2:"s02\<in>F2" by auto
      from i(1) i0 have zero_L:"(0:Lists(\<Sigma>))" by auto
      have "0 <-D (S1,s01,t1,F1){in alphabet}\<Sigma>"
        unfolding DFSASatisfy_def[OF fin A1 zero_L] using s01F1 by auto
      then have zero_L1:"(0:L1)" unfolding L1_def using zero_L by auto
      have "0 <-D (S2,s02,t2,F2){in alphabet}\<Sigma>"
        unfolding DFSASatisfy_def[OF fin A2 zero_L] using s02F2 by auto
      then have zero_L2:"(0:L2)" unfolding L2_def using zero_L by auto
      have concat00:"Concat(0,0) = 0"
        unfolding Concat_def ShiftedSeq_def NatInterval_def by auto
      have "(0:concat(L1,L2))"
        unfolding concat_def[OF lang1 lang2]
        using zero_L2 zero_L1 concat00 by auto
      with i0 have "i:concat(L1,L2)" by auto
    } moreover
    {
      assume "\<not>(i=0 \<and> \<epsilon>-cl(?S,?t,\<Sigma>,{?s\<^sub>0}) \<inter> ?F \<noteq> \<emptyset>)"
      with r obtain q where q:"q:Pow(?S)" "\<epsilon>-cl(?S,?t,\<Sigma>,q) \<inter> ?F \<noteq> \<emptyset>" "\<langle>\<langle>i, {?s\<^sub>0}\<rangle>, \<emptyset>, q\<rangle> \<in>
    (({reduce \<epsilon>-N-relation}(?S,?t){in alphabet}\<Sigma>)^*)" by auto
      from q(1) have ecl_eq:"\<epsilon>-cl(?S,?t,\<Sigma>,q) = q\<union>{x\<in>{\<langle>s02,1\<rangle>}. q\<inter>(F1\<times>1)\<noteq>0}"
        using concat_eNFSA_eps_closure[OF fin A1 A2] by auto
      then have "i:concat(L1,L2)"
      proof -
        let ?r\<epsilon> = "{reduce \<epsilon>-N-relation}(?S,?t){in alphabet}\<Sigma>"
        let ?rD1 = "{reduce D-relation}(S1,t1){in alphabet}\<Sigma>"
        let ?rD2 = "{reduce D-relation}(S2,t2){in alphabet}\<Sigma>"
        have zero_L:"(0::i)\<in>Lists(\<Sigma>)"
          unfolding Lists_def Pi_def function_def using nat_0I by auto
        \<comment> \<open>Step 1: derive \<open>i\<in>NELists(\<Sigma>)\<close>.
            If \<open>i=0\<close> the \<open>r\<epsilon>^*\<close> run is the identity, forcing \<open>q=\{s\<^sub>0\}\<close> and
            \<open>\<epsilon>-cl(\{s\<^sub>0\})\<inter>F\<noteq>\<emptyset>\<close>, which contradicts the surrounding negated assumption.\<close>
        have iNE:"i\<in>NELists(\<Sigma>)"
        proof (rule ccontr)
          assume inoNE:"i\<notin>NELists(\<Sigma>)"
          from i(1) obtain k where k:"k\<in>nat" "i:k\<rightarrow>\<Sigma>" unfolding Lists_def by auto
          have "k=0"
          proof (rule ccontr)
            assume "k\<noteq>0"
            from k(1) this obtain p where p:"p\<in>nat" "k=succ(p)" using Nat_ZF_1_L3 by auto
            with k(2) have "i:succ(p)\<rightarrow>\<Sigma>" by simp
            then have "i\<in>NELists(\<Sigma>)" unfolding NELists_def using p(1) by auto
            with inoNE show False by simp
          qed
          with k(2) have "i:0\<rightarrow>\<Sigma>" by simp
          then have i0:"i=0" unfolding Pi_def function_def by auto
          from q(3) i0 have run0:"\<langle>\<langle>0,{?s\<^sub>0}\<rangle>,0,q\<rangle>\<in>?r\<epsilon>^*" by simp
          from rtrancl_rev[of ?r\<epsilon>] run0 have
            "\<langle>\<langle>0,{?s\<^sub>0}\<rangle>,0,q\<rangle>\<in>id(field(?r\<epsilon>)) \<union>
             (?r\<epsilon>^* O ?r\<epsilon>)" by auto
          moreover {
            assume "\<langle>\<langle>0,{?s\<^sub>0}\<rangle>,0,q\<rangle>\<in>id(field(?r\<epsilon>))"
            then have "q={?s\<^sub>0}" by auto
            with q(2) have "\<epsilon>-cl(?S,?t,\<Sigma>,{?s\<^sub>0})\<inter>?F\<noteq>0" by simp
            with \<open>\<not>(i=0 \<and> \<epsilon>-cl(?S,?t,\<Sigma>,{?s\<^sub>0}) \<inter> ?F \<noteq> \<emptyset>)\<close> i0 have False by auto
          }
          moreover {
            assume "\<langle>\<langle>0,{?s\<^sub>0}\<rangle>,0,q\<rangle>\<in>?r\<epsilon>^* O ?r\<epsilon>"
            then obtain y where "\<langle>\<langle>0,{?s\<^sub>0}\<rangle>,y\<rangle>\<in>?r\<epsilon>" using compE by auto
            then have "0\<in>NELists(\<Sigma>)"
              unfolding FullNFSAExecutionRelation_def[OF fin
                concat_eNFSA_valid[OF fin A1 A2]] by auto
            then have False unfolding NELists_def Pi_def by auto
          }
          ultimately show False by auto
        qed
        \<comment> \<open>Step 2: apply \<open>exec_state_form\<close> to decompose \<open>q\<close>.\<close>
        from exec_state_form[OF fin A1 A2 iNE q(3)] obtain q1 Q2 where qform:
          "q1\<in>S1" "Q2\<in>Pow(S2)" "q={\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}"
          "\<langle>\<langle>i,s01\<rangle>,\<langle>0,q1\<rangle>\<rangle>\<in>?rD1^*"
          by auto
        \<comment> \<open>Step 3: \<open>\<epsilon>-cl(q)\<inter>?F\<noteq>\<emptyset>\<close> forces \<open>Q2\<inter>F2\<noteq>\<emptyset>\<close> or \<open>q1\<in>F1\<and>s02\<in>F2\<close>.\<close>
        have caseSplit:"Q2\<inter>F2\<noteq>0 \<or> (q1\<in>F1 \<and> s02\<in>F2)"
        proof (rule ccontr)
          assume "\<not>(Q2\<inter>F2\<noteq>0 \<or> (q1\<in>F1 \<and> s02\<in>F2))"
          then have Q2F2:"Q2\<inter>F2=0" and notcA:"\<not>(q1\<in>F1 \<and> s02\<in>F2)" by auto
          {
            assume as:"q\<inter>(F1\<times>1)\<noteq>0"
            with qform(3) have "\<langle>q1,0\<rangle>\<in>F1\<times>1" by auto
            then have "q1\<in>F1" by auto
            with notcA have A:"s02\<notin>F2" by auto
            from Q2F2 have "(Q2\<times>{1})\<inter>?F =0" by auto
            then have "q\<inter>?F = 0" using qform(3) by auto moreover
            from as ecl_eq have "\<langle>s02,1\<rangle>:\<epsilon>-cl(?S,?t,\<Sigma>,q)" by auto
            ultimately have "\<epsilon>-cl(?S,?t,\<Sigma>,q)\<inter>?F = {\<langle>s02,1\<rangle>}\<inter>?F"
              using ecl_eq by auto
            with A have "\<epsilon>-cl(?S,?t,\<Sigma>,q)\<inter>?F = 0" by auto
            with q(2) have False by auto
          }
          then have "q\<inter>(F1\<times>1) =0" by auto
          then have "\<epsilon>-cl(?S,?t,\<Sigma>,q) = q" using ecl_eq by auto
          then have "\<epsilon>-cl(?S,?t,\<Sigma>,q)\<inter>?F = q\<inter>?F" by auto
          then have "\<epsilon>-cl(?S,?t,\<Sigma>,q)\<inter>?F = (Q2\<inter>F2)\<times>{1}" using qform(3) by auto
          with Q2F2 have "\<epsilon>-cl(?S,?t,\<Sigma>,q)\<inter>?F = 0" by auto
          with q(2) show False by auto
        qed
        have D1:"DetFinStateAuto(S1,s01,t1,F1,\<Sigma>)"
          unfolding DetFinStateAuto_def using fin A1 by auto
        have D2:"DetFinStateAuto(S2,s02,t2,F2,\<Sigma>)"
          unfolding DetFinStateAuto_def using fin A2 by auto
        have s01S1:"s01\<in>S1" using A1 unfolding DFSA_def[OF fin] by auto
        \<comment> \<open>\<open>Concat(0,i)=i\<close>: used to build the witness \<open>i=Concat(0,i)\<close> in concat.\<close>
        have C0i:"Concat(0,i)=i"
        proof -
          from i(1) obtain k where k:"k\<in>nat" "i:k\<rightarrow>\<Sigma>" unfolding Lists_def by auto
          have zk:"(0::i):0\<rightarrow>\<Sigma>" unfolding Pi_def function_def by auto
          have t1c:"Concat(0,i):k\<rightarrow>\<Sigma>"
            using concat_props(1)[OF nat_0I k(1) zk k(2)] add_0 k(1) by simp
          have ptw:"\<forall>j\<in>k. Concat(0,i)`j = i`j"
          proof
            fix j assume jk:"j\<in>k"
            from jk k(1) have jN:"j\<in>nat" using elem_nat_is_nat by blast
            then have s:"0 #+ j = j" by auto
            have jI:"0 #+ j\<in>NatInterval(0,k)"
              using jk unfolding NatInterval_def by auto
            from concat_props(3)[OF nat_0I k(1) zk k(2)] jI jN
            show "Concat(0,i)`j = i`j" by auto
          qed
          from t1c k(2) ptw show "Concat(0,i)=i"
            using fun_extension[of "Concat(0,i)" k "\<lambda>_. \<Sigma>" i "\<lambda>_. \<Sigma>"] by auto
        qed
        \<comment> \<open>Shared helper: \<open>i\<in>L1\<close> and \<open>0\<in>L2\<close> imply \<open>i\<in>concat(L1,L2)\<close> via \<open>Concat(0,i)=i\<close>.\<close>
        have conc_from_L1_0L2:"i\<in>L1 \<Longrightarrow> 0\<in>L2 \<Longrightarrow> i\<in>concat(L1,L2)"
        proof -
          assume "i\<in>L1" "0\<in>L2"
          then have "\<langle>i,0\<rangle>\<in>L1\<times>L2" by auto
          then have "Concat(0,i):concat(L1,L2)" unfolding concat_def[OF lang1 lang2] by auto
          then show "i\<in>concat(L1,L2)" using C0i by auto
        qed
        have run_A2:"\<langle>\<langle>i,{\<langle>s01,0\<rangle>}\<rangle>,\<langle>0,{\<langle>q1,0\<rangle>}\<union>Q2\<times>{1}\<rangle>\<rangle>\<in>?r\<epsilon>^*"
          using q(3) qform(3) by auto
        from caseSplit show "i\<in>concat(L1,L2)"
        proof (elim disjE)
          \<comment> \<open>Case B: pick \<open>q2\<in>Q2\<inter>F2\<close> and apply \<open>exec_A2_component\<close>.\<close>
          assume cB:"Q2\<inter>F2\<noteq>0"
          then obtain q2 where q2:"q2\<in>Q2" "q2\<in>F2" by auto
          from exec_A2_component[OF fin A1 A2 iNE run_A2 qform(1) qform(2) q2(1)]
          show "i\<in>concat(L1,L2)"
          proof (elim disjE)
            \<comment> \<open>case\_a: A1 ran \<open>i\<close> to \<open>yl_k\<in>NELists\<close>, then A2 ran \<open>yl_k\<close> to \<open>q2\<in>F2\<close>.\<close>
            assume "\<exists>yl_k\<in>NELists(\<Sigma>). \<exists>f1\<in>F1.
                      \<langle>\<langle>i,s01\<rangle>,\<langle>yl_k,f1\<rangle>\<rangle>\<in>?rD1^* \<and>
                      \<langle>\<langle>yl_k,s02\<rangle>,\<langle>0,q2\<rangle>\<rangle>\<in>?rD2^*"
            then obtain yl_k f1 where
              yk_ne:"yl_k\<in>NELists(\<Sigma>)" and f1F1:"f1\<in>F1" and
              ca1:"\<langle>\<langle>i,s01\<rangle>,\<langle>yl_k,f1\<rangle>\<rangle>\<in>?rD1^*" and
              ca2:"\<langle>\<langle>yl_k,s02\<rangle>,\<langle>0,q2\<rangle>\<rangle>\<in>?rD2^*" by auto
            have ykL:"yl_k\<in>Lists(\<Sigma>)" using yk_ne unfolding NELists_def Lists_def by auto
            have yk_L2:"yl_k\<in>L2"
            proof -
              have "yl_k <-D (S2,s02,t2,F2){in alphabet}\<Sigma>"
                unfolding DFSASatisfy_def[OF fin A2 ykL] using q2(2) ca2 by auto
              then show "yl_k\<in>L2" unfolding L2_def using ykL by auto
            qed
            from DetFinStateAuto.list_prefix_split[OF D1 ca1] obtain jl where
              jl_L:"jl\<in>Lists(\<Sigma>)" and i_spl:"i=Concat(yl_k,jl)" by auto
            \<comment> \<open>\<open>jl\<in>L1\<close>: if \<open>jl=0\<close> use determinism to get \<open>s01\<in>F1\<close>;
                otherwise apply \<open>dfa_run_suffix\<close>.\<close>
            have jlL1:"jl\<in>L1"
            proof -
              {
                assume jl0:"jl=0"
                have ieq:"i=yl_k"
                  using jl0 i_spl concat_0_left[OF ykL] by simp
                with ca1 have same:"\<langle>\<langle>yl_k,s01\<rangle>,\<langle>yl_k,f1\<rangle>\<rangle>\<in>?rD1^*" by simp
                have fld:"\<langle>yl_k,s01\<rangle>\<in>field(?rD1)"
                  using DetFinStateAuto.reduce_field(2)[OF D1] yk_ne s01S1 by auto
                have id_r:"\<langle>\<langle>yl_k,s01\<rangle>,\<langle>yl_k,s01\<rangle>\<rangle>\<in>?rD1^*"
                  using rtrancl_refl fld by auto
                from DetFinStateAuto.relation_deteministic[OF D1 same id_r]
                have "f1=s01" .
                with f1F1 have s01F1:"s01\<in>F1" by simp
                have "0 <-D (S1,s01,t1,F1){in alphabet}\<Sigma>"
                  unfolding DFSASatisfy_def[OF fin A1 zero_L] using s01F1 by auto
                with jl0 have "jl\<in>L1" unfolding L1_def using zero_L by auto
              } moreover {
                assume "jl\<noteq>0"
                from jl_L obtain m where m:"m\<in>nat" "jl:m\<rightarrow>\<Sigma>"
                  unfolding Lists_def by auto
                  {
                    assume "m=0"
                    with m(2) have "jl=0" by auto
                    with \<open>jl\<noteq>0\<close> have False by auto
                  }
                with m(1) obtain p where p:"p\<in>nat" "m=succ(p)"
                  using Nat_ZF_1_L3 by auto
                with m(2) have jlNE:"jl\<in>NELists(\<Sigma>)"
                  unfolding NELists_def using p(1) by auto
                from i_spl ca1 have
                  rspl:"\<langle>\<langle>Concat(yl_k,jl),s01\<rangle>,\<langle>yl_k,f1\<rangle>\<rangle>\<in>?rD1^*" by simp
                from DetFinStateAuto.dfa_run_suffix[OF D1 ykL jlNE rspl]
                have rjl:"\<langle>\<langle>jl,s01\<rangle>,\<langle>0,f1\<rangle>\<rangle>\<in>?rD1^*" .
                have "jl <-D (S1,s01,t1,F1){in alphabet}\<Sigma>"
                  unfolding DFSASatisfy_def[OF fin A1 jl_L] using f1F1 rjl by auto
                then have "jl\<in>L1" unfolding L1_def using jl_L by auto
              }
              ultimately show "jl\<in>L1" by auto
            qed
            show "i\<in>concat(L1,L2)"
              unfolding concat_def[OF lang1 lang2] i_spl using jlL1 yk_L2 by auto
          next
            \<comment> \<open>case\_b: \<open>q2=s02\<close> and A1 ran all of \<open>i\<close> to some \<open>f1\<in>F1\<close>.\<close>
            assume cb:"q2=s02 \<and> (\<exists>f1\<in>F1. \<langle>\<langle>i,s01\<rangle>,\<langle>0,f1\<rangle>\<rangle>\<in>?rD1^*)"
            then have s02F2:"s02\<in>F2" using q2(2) by auto
            from cb obtain f1 where f1F1:"f1\<in>F1" and
              cb1:"\<langle>\<langle>i,s01\<rangle>,\<langle>0,f1\<rangle>\<rangle>\<in>?rD1^*" by auto
            have iL1:"i\<in>L1"
            proof -
              have "i <-D (S1,s01,t1,F1){in alphabet}\<Sigma>"
                unfolding DFSASatisfy_def[OF fin A1 i(1)] using f1F1 cb1 by auto
              then show "i\<in>L1" unfolding L1_def using i(1) by auto
            qed
            have zL2:"0\<in>L2"
            proof -
              have "0 <-D (S2,s02,t2,F2){in alphabet}\<Sigma>"
                unfolding DFSASatisfy_def[OF fin A2 zero_L] using s02F2 by auto
              then show "0\<in>L2" unfolding L2_def using zero_L by auto
            qed
            show "i\<in>concat(L1,L2)" using conc_from_L1_0L2 iL1 zL2 by auto
          qed
        next
          \<comment> \<open>Case A: \<open>q1\<in>F1\<close> and \<open>s02\<in>F2\<close>.  A1 accepted \<open>i\<close>; \<open>0\<in>L2\<close> by \<open>s02\<in>F2\<close>.\<close>
          assume cA:"q1\<in>F1 \<and> s02\<in>F2"
          then have q1F1:"q1\<in>F1" and s02F2:"s02\<in>F2" by auto
          have iL1:"i\<in>L1"
          proof -
            have "i <-D (S1,s01,t1,F1){in alphabet}\<Sigma>"
              unfolding DFSASatisfy_def[OF fin A1 i(1)] using q1F1 qform(4) by auto
            then show "i\<in>L1" unfolding L1_def using i(1) by auto
          qed
          have zL2:"0\<in>L2"
          proof -
            have "0 <-D (S2,s02,t2,F2){in alphabet}\<Sigma>"
              unfolding DFSASatisfy_def[OF fin A2 zero_L] using s02F2 by auto
            then show "0\<in>L2" unfolding L2_def using zero_L by auto
          qed
          show "i\<in>concat(L1,L2)" using conc_from_L1_0L2 iL1 zL2 by auto
        qed
      qed
    } ultimately
    have "i:concat(L1,L2)" by auto
  } moreover
  {
    fix i assume "i:concat(L1,L2)"
    then obtain j u where uj:"u\<in>L2" "j\<in>L1" "i=Concat(u,j)" using concat_def[OF lang1 lang2] by auto
    from uj have c:"Concat(u,j)\<in>Lists(\<Sigma>)" unfolding L1_def L2_def using concat_is_list by auto
    {
      assume j0:"j\<noteq>0" moreover
      from uj(1) have uu:"u\<in>Lists(\<Sigma>)" unfolding L2_def by auto moreover
      have "{\<langle>s01,0\<rangle>}\<subseteq>S1\<times>1" using A1 unfolding DFSA_def[OF fin] by auto
      then have "{\<langle>s01,0\<rangle>}\<in>Pow(?S)" unfolding concat_eNFSA_states_def by auto
      ultimately obtain Q1 where A:"Q1\<in>Pow(?S)" "\<langle>s02,1\<rangle>\<in>Q1" 
        "\<langle>\<langle>Concat(u,j),{\<langle>s01,0\<rangle>}\<rangle>,u,Q1\<rangle>\<in>(({reduce \<epsilon>-N-relation}(?S,?t){in alphabet}\<Sigma>)^*)"
        using concat_FSA_apply_L1[OF fin A1 A2, of j "{\<langle>s01,0\<rangle>}" u] uj(2) unfolding L1_def
        by auto
      from A have A22:"\<langle>s02,1\<rangle>\<in>\<epsilon>-cl(?S,?t,\<Sigma>,Q1)"
        using concat_eNFSA_eps_closure[OF fin A1 A2] by auto
      {
        assume u0:"u\<noteq>0"
        from concat_FSA_apply_L2[OF fin A1 A2 _ A22 A(1) u0] uj(1)
          obtain Q2 where B:"Q2\<in>Pow(?S)" " \<epsilon>-cl(?S,?t,\<Sigma>,Q2)\<inter>?F\<noteq>0"
          "\<langle>\<langle>u,Q1\<rangle>,0,Q2\<rangle>\<in>(({reduce \<epsilon>-N-relation}(?S,?t){in alphabet}\<Sigma>)^*)"
          unfolding L2_def by auto
        from A(3) B(3) have "\<langle>\<langle>Concat(u,j),{?s\<^sub>0}\<rangle>,0,Q2\<rangle>\<in>(({reduce \<epsilon>-N-relation}(?S,?t){in alphabet}\<Sigma>)^*)"
          using trans_rtrancl[of "({reduce \<epsilon>-N-relation}(?S,?t){in alphabet}\<Sigma>)"]
          unfolding trans_def by auto
        then have "Concat(u,j) <-\<epsilon>-N (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>"
          using FullNFSASatisfy_def[OF fin concat_eNFSA_valid[OF fin A1 A2]] B(1,2)
          c by auto
        with uj(3) c have "i:{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}" by auto
      } moreover
      {
        assume u0:"u=0"
        {
          assume "s02\<in>F2"
          with A(2) have "Q1\<inter>?F\<noteq>0" by auto moreover
          from A(1) have "Q1 \<subseteq> \<epsilon>-cl(?S,?t,\<Sigma>,Q1)" using epsilon_cl_refl_sub[OF fin
            concat_eNFSA_valid[OF fin A1 A2]] by auto
          ultimately have "\<epsilon>-cl(?S,?t,\<Sigma>,Q1)\<inter>?F\<noteq>0" by auto
          with A(1,3) have "Concat(u,j) <-\<epsilon>-N (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>"
            using FullNFSASatisfy_def[OF fin concat_eNFSA_valid[OF fin A1 A2], of "Concat(u,j)"]
            c `u=0` by auto
          with uj(3) c have "i:{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}" by auto
        } moreover
        {
          assume G:"s02\<notin>F2"
          let ?dr="{reduce D-relation}(S2,t2){in alphabet}\<Sigma>"
          have "0:0\<rightarrow>\<Sigma>" unfolding Pi_def function_def by auto
          then have l0:"0\<in>Lists(\<Sigma>)" unfolding Lists_def by blast
          from u0 uj(1) have "0 <-D (S2,s02,t2,F2){in alphabet}\<Sigma>" unfolding L2_def by auto
          with l0 obtain q where q:"q\<in>F2" "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<in>({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)^*" 
            using DFSASatisfy_def[OF fin A2, of 0] G by auto
          {
            assume "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<in>id(field(?dr))"
            then have False using G q(1) by auto
          }
          then have "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<notin>id(field(?dr))" by auto moreover
          from q(2) have "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<in>id(field(?dr))\<union>(?dr^* O ?dr)" using rtrancl_rev
            by auto
          ultimately have "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<in>(?dr^* O ?dr)" by auto
          then obtain y where y:"\<langle>\<langle>0,s02\<rangle>,y\<rangle>\<in>?dr" "\<langle>y,\<langle>0,q\<rangle>\<rangle>\<in>?dr^*" using compE by auto
          from y(1) have "0\<in>NELists(\<Sigma>)" unfolding DFSAExecutionRelation_def[OF fin A2]
            by auto
          then have False unfolding NELists_def Pi_def by auto
        }
        ultimately have "i:{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}" by auto
      }
      ultimately have "i:{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}" by auto
    } moreover
    {
      assume j0:"j=0"
      then have iu:"i=u" using concat_0_left uj(3) uj(1) unfolding L2_def by auto
      have "0:0\<rightarrow>\<Sigma>" unfolding Pi_def function_def by auto
      then have l0:"0\<in>Lists(\<Sigma>)" unfolding Lists_def by blast
      {
        assume G:"s01\<notin>F1"
        let ?dr="{reduce D-relation}(S1,t1){in alphabet}\<Sigma>"
        from j0 uj(2) have "0 <-D (S1,s01,t1,F1){in alphabet}\<Sigma>" unfolding L1_def by auto
        with l0 obtain q where q:"q\<in>F1" "\<langle>\<langle>0,s01\<rangle>,0,q\<rangle>\<in>({reduce D-relation}(S1,t1){in alphabet}\<Sigma>)^*" 
          using DFSASatisfy_def[OF fin A1, of 0] G by auto
        {
          assume "\<langle>\<langle>0,s01\<rangle>,0,q\<rangle>\<in>id(field(?dr))"
          then have False using G q(1) by auto
        }
        then have "\<langle>\<langle>0,s01\<rangle>,0,q\<rangle>\<notin>id(field(?dr))" by auto moreover
        from q(2) have "\<langle>\<langle>0,s01\<rangle>,0,q\<rangle>\<in>id(field(?dr))\<union>(?dr^* O ?dr)" using rtrancl_rev
          by auto
        ultimately have "\<langle>\<langle>0,s01\<rangle>,0,q\<rangle>\<in>(?dr^* O ?dr)" by auto
        then obtain y where y:"\<langle>\<langle>0,s01\<rangle>,y\<rangle>\<in>?dr" "\<langle>y,\<langle>0,q\<rangle>\<rangle>\<in>?dr^*" using compE by auto
        from y(1) have "0\<in>NELists(\<Sigma>)" unfolding DFSAExecutionRelation_def[OF fin A1]
          by auto
        then have False unfolding NELists_def Pi_def by auto
      }
      then have "s01\<in>F1" by auto moreover
      have p:"{\<langle>s01,0\<rangle>}:Pow(?S)" using A1 unfolding concat_eNFSA_states_def
        DFSA_def[OF fin] by auto
      ultimately have B:"\<epsilon>-cl(?S,?t,\<Sigma>,{\<langle>s01,0\<rangle>}) = {\<langle>s01,0\<rangle>,\<langle>s02,1\<rangle>}"
        using concat_eNFSA_eps_closure[OF fin A1 A2, of "{\<langle>s01,0\<rangle>}"] by auto
      {
        assume u0:"u=0"
        {
          assume G:"s02\<notin>F2"
          let ?dr="{reduce D-relation}(S2,t2){in alphabet}\<Sigma>"
          from u0 uj(1) have "0 <-D (S2,s02,t2,F2){in alphabet}\<Sigma>" unfolding L2_def by auto
          with l0 obtain q where q:"q\<in>F2" "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<in>({reduce D-relation}(S2,t2){in alphabet}\<Sigma>)^*" 
            using DFSASatisfy_def[OF fin A2, of 0] G by auto
          {
            assume "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<in>id(field(?dr))"
            then have False using G q(1) by auto
          }
          then have "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<notin>id(field(?dr))" by auto moreover
          from q(2) have "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<in>id(field(?dr))\<union>(?dr^* O ?dr)" using rtrancl_rev
            by auto
          ultimately have "\<langle>\<langle>0,s02\<rangle>,0,q\<rangle>\<in>(?dr^* O ?dr)" by auto
          then obtain y where y:"\<langle>\<langle>0,s02\<rangle>,y\<rangle>\<in>?dr" "\<langle>y,\<langle>0,q\<rangle>\<rangle>\<in>?dr^*" using compE by auto
          from y(1) have "0\<in>NELists(\<Sigma>)" unfolding DFSAExecutionRelation_def[OF fin A2]
            by auto
          then have False unfolding NELists_def Pi_def by auto
        }
        then have "s02\<in>F2" by auto
        then have A:"\<langle>s02,1\<rangle>\<in>?F" by auto
        from A B have "\<epsilon>-cl(?S,?t,\<Sigma>,{\<langle>s01,0\<rangle>}) \<inter>?F \<noteq>0" by auto
        with iu u0 have "i=0 \<and> \<epsilon>-cl(?S,?t,\<Sigma>,{\<langle>s01,0\<rangle>}) \<inter>?F \<noteq>0" by auto
        then have "i:{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}" 
            using FullNFSASatisfy_def[OF fin concat_eNFSA_valid[OF fin A1 A2]]
            l0 iu u0 by auto
      } moreover
      {
        assume u0:"u\<noteq>0"
        from B have B:"\<langle>s02,1\<rangle>\<in>\<epsilon>-cl(?S,?t,\<Sigma>,{\<langle>s01,0\<rangle>})" by auto
        from concat_FSA_apply_L2[OF fin A1 A2 _ B p u0] uj(1) B
          obtain Q2 where B:"Q2\<in>Pow(?S)" " \<epsilon>-cl(?S,?t,\<Sigma>,Q2)\<inter>?F\<noteq>0"
          "\<langle>\<langle>u,{\<langle>s01,0\<rangle>}\<rangle>,0,Q2\<rangle>\<in>(({reduce \<epsilon>-N-relation}(?S,?t){in alphabet}\<Sigma>)^*)"
          unfolding L2_def by auto
        then have "i:{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}" using iu uj(1) unfolding L2_def
            using FullNFSASatisfy_def[OF fin concat_eNFSA_valid[OF fin A1 A2]]
            by auto
      }
      ultimately have "i:{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}" by auto
    }
    ultimately have "i:{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N
            (?S,?s\<^sub>0,?t,?F){in alphabet}\<Sigma>}" by auto
  }
  ultimately show ?thesis by blast
qed

text\<open>The concatenation of two regular languages is regular.\<close>

theorem concat_language_regular:
  assumes fin:"Finite(\<Sigma>)"
  and "L1{is a regular language on}\<Sigma>"
  and "L2{is a regular language on}\<Sigma>"
  shows "concat(L1,L2) {is a regular language on}\<Sigma>"
proof-
  from fin assms(2) obtain S1 s01 t1 F1 where
    A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
    and "L1 = DetFinStateAuto.LanguageDFSA(S1,s01,t1,F1,\<Sigma>)"
    using IsRegularLanguage_def by auto
  then have A1:"(S1,s01,t1,F1){is an DFSA for alphabet}\<Sigma>"
    and L1_eq:"L1 = {i\<in>Lists(\<Sigma>). i <-D (S1,s01,t1,F1){in alphabet}\<Sigma>}"
    using DetFinStateAuto_def fin A1 by auto
  from fin assms(3) obtain S2 s02 t2 F2 where
    A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
    and "L2 = DetFinStateAuto.LanguageDFSA(S2,s02,t2,F2,\<Sigma>)"
    using IsRegularLanguage_def by auto
  then have A2:"(S2,s02,t2,F2){is an DFSA for alphabet}\<Sigma>"
    and L2_eq:"L2 = {i\<in>Lists(\<Sigma>). i <-D (S2,s02,t2,F2){in alphabet}\<Sigma>}"
    using DetFinStateAuto_def fin A2 by auto
  let ?SS = "concat_eNFSA_states(S1,S2)"
  let ?s0 = "\<langle>s01,0\<rangle>"
  let ?tc = "concat_eNFSA_trans(S1,s01,t1,F1,S2,s02,t2,F2,\<Sigma>)"
  let ?Fc = "F2\<times>{1}"
  have valid:"(?SS,?s0,?tc,?Fc){is an \<epsilon>-NFSA for alphabet}\<Sigma>"
    using concat_eNFSA_valid[OF fin A1 A2] .
  have lang_eq:"{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N (?SS,?s0,?tc,?Fc){in alphabet}\<Sigma>} = concat(L1,L2)"
    using concat_eNFSA_language[OF fin A1 A2 L1_eq L2_eq] .
  have "{i\<in>Lists(\<Sigma>). i <-\<epsilon>-N (?SS,?s0,?tc,?Fc){in alphabet}\<Sigma>} {is a regular language on}\<Sigma>"
    using epsilonNFSA_lang_is_regular[OF fin valid] .
  with lang_eq show ?thesis by auto
qed

end
