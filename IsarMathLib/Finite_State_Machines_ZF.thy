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
  DFSAExecutionRelation ("{reduce D-relation}'(_,_,_'){in alphabet}_") where
  "Finite(\<Sigma>) \<Longrightarrow> (S,s\<^sub>0,t,F){is an DFSA for alphabet}\<Sigma> \<Longrightarrow> 
  {reduce D-relation}(S,s\<^sub>0,t){in alphabet}\<Sigma> \<equiv> {\<langle>\<langle>w,s\<rangle>,\<langle>Init(w),t`\<langle>s,Last(w)\<rangle>\<rangle>\<rangle>. \<langle>w,s\<rangle>\<in>NELists(\<Sigma>)\<times>S}"

text\<open>We define a word to be fully reducible by a finite
state automaton if in the transitive closure of the previous
relation it is related to the pair of the empty word and a final state.

Since the empty word with the initial state need not be in
@{term "field({reduce D-relation}(S,s\<^sub>0,t){in alphabet}\<Sigma>)"},
we add the extra condition that @{term "\<langle>\<langle>0,s\<^sub>0\<rangle>,\<langle>0,s\<^sub>0\<rangle>\<rangle>"}
is also a valid transition.\<close>

definition
  DFSASatisfy ("_ <-D '(_,_,_,_'){in alphabet}_") where
  "Finite(\<Sigma>) \<Longrightarrow> (S,s\<^sub>0,t,F){is an DFSA for alphabet}\<Sigma> \<Longrightarrow> i\<in>Lists(\<Sigma>) \<Longrightarrow> 
  i <-D (S,s\<^sub>0,t,F){in alphabet}\<Sigma> \<equiv> (\<exists>q\<in>F. \<langle>\<langle>i,s\<^sub>0\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in> ({reduce D-relation}(S,s\<^sub>0,t){in alphabet}\<Sigma>)^*) \<or> (i = 0 \<and> s\<^sub>0\<in>F)"

text\<open>We define a locale for better notation\<close>

locale DetFinStateAuto =
  fixes S and s\<^sub>0 and t and F and \<Sigma>
  assumes finite_alphabet: "Finite(\<Sigma>)"
  
  assumes DFSA: "(S,s\<^sub>0,t,F){is an DFSA for alphabet}\<Sigma>"

text\<open>We abbreviate the reduce relation to a single symbol
within this locale.\<close>

abbreviation (in DetFinStateAuto) "r\<^sub>D" where
 "r\<^sub>D \<equiv> {reduce D-relation}(S,s\<^sub>0,t){in alphabet}\<Sigma>"

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
  let ?r = "DetFinStateAuto.r\<^sub>D(?S,?s,?t,\<Sigma>)"
  let ?r1 = "DetFinStateAuto.r\<^sub>D(S1,s1,t1,\<Sigma>)"
  let ?r2 = "DetFinStateAuto.r\<^sub>D(S2,s2,t2,\<Sigma>)"
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
  let ?r = "DetFinStateAuto.r\<^sub>D(S,s,t,\<Sigma>)"
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
    \<Longrightarrow> concat(L1,L2) = {Concat(w1,w2). \<langle>w1,w2\<rangle>\<in>L1\<times>L2}"

text\<open>The result of concatenating two languages is a language.\<close>

lemma concat_language:
  assumes "Finite(\<Sigma>)"
  and "L1 {is a language with alphabet}\<Sigma>"
  and "L2 {is a language with alphabet}\<Sigma>"
shows "concat(L1,L2) {is a language with alphabet}\<Sigma>"
proof-
  {
    fix w assume "w\<in>concat(L1,L2)"
    then obtain w1 w2 where w:"w=Concat(w1,w2)" "w1\<in>L1" "w2\<in>L2" unfolding concat_def[OF assms(2,3)]
      by auto
    from this(2,3) assms(2,3) obtain n1 n2 where "n1\<in>nat" "n2\<in>nat" "w1:n1\<rightarrow>\<Sigma>" "w2:n2\<rightarrow>\<Sigma>"
      unfolding IsALanguage_def[OF assms(1)] Lists_def by blast
    then have "Concat(w1,w2):n1#+n2 \<rightarrow> \<Sigma>" "n1#+n2 \<in>nat" using concat_props(1) by auto
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
  NFSAExecutionRelation ("{reduce N-relation} '(_,_,_'){in alphabet}_") where
  "Finite(\<Sigma>) \<Longrightarrow> (S,s\<^sub>0,t,F){is an NFSA for alphabet}\<Sigma> \<Longrightarrow> 
  {reduce N-relation}(S,s\<^sub>0,t){in alphabet}\<Sigma> \<equiv> {\<langle>\<langle>w,Q\<rangle>,\<langle>Init(w),\<Union>{t`\<langle>s,Last(w)\<rangle>. s\<in>Q}\<rangle>\<rangle>. \<langle>w,Q\<rangle>\<in>NELists(\<Sigma>)\<times>Pow(S)}"

text\<open>The full reduction is conceived as one of those possible
paths reaching a final state.\<close>

definition
  NFSASatisfy ("_ <-N '(_,_,_,_'){in alphabet}_") where
  "Finite(\<Sigma>) \<Longrightarrow> (S,s\<^sub>0,t,F){is an NFSA for alphabet}\<Sigma> \<Longrightarrow> i\<in>Lists(\<Sigma>) \<Longrightarrow> 
  i <-N (S,s\<^sub>0,t,F){in alphabet}\<Sigma> \<equiv> (\<exists>q\<in>Pow(S). (q\<inter>F\<noteq>0 \<and> \<langle>\<langle>i,{s\<^sub>0}\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in> ({reduce N-relation}(S,s\<^sub>0,t){in alphabet}\<Sigma>)^*)) \<or> (i = 0 \<and> s\<^sub>0\<in>F)"

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
    \<Longrightarrow> \<epsilon>-cl(S,t,\<Sigma>,E) \<equiv> \<Union>{P\<in>Pow(S). \<langle>E,P\<rangle>\<in>({\<langle>Q,{s\<in>S. \<exists>q\<in>Q. t`\<langle>q,\<Sigma>\<rangle> = s}\<rangle>. Q\<in>Pow(S)}^*)}"

text\<open>The reduction relation is then extended
by considering any such transitions.\<close>

definition
  FullNFSAExecutionRelation ("{reduce \<epsilon>-N-relation} '(_,_,_'){in alphabet}_") where
  "Finite(\<Sigma>) \<Longrightarrow> (S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma> \<Longrightarrow> 
  {reduce \<epsilon>-N-relation}(S,s\<^sub>0,t){in alphabet}\<Sigma> \<equiv> {\<langle>\<langle>w,Q\<rangle>,\<langle>Init(w),\<epsilon>-cl(S,t,\<Sigma>,\<Union>{t`\<langle>s,Last(w)\<rangle>. s\<in>Q})\<rangle>\<rangle>. \<langle>w,Q\<rangle>\<in>NELists(\<Sigma>)\<times>Pow(S)}"

text\<open>The full reduction of a word is similar to that
of the automata without $\varepsilon$-transitions.\<close>

definition
  FullNFSASatisfy ("_ <-\<epsilon>-N '(_,_,_,_'){in alphabet}_") where
  "Finite(\<Sigma>) \<Longrightarrow> (S,s\<^sub>0,t,F){is an \<epsilon>-NFSA for alphabet}\<Sigma> \<Longrightarrow> i\<in>Lists(\<Sigma>) \<Longrightarrow> 
  i <-\<epsilon>-N (S,s\<^sub>0,t,F){in alphabet}\<Sigma> \<equiv> (\<exists>q\<in>Pow(S). (q\<inter>F\<noteq>0 \<and> \<langle>\<langle>i,{s\<^sub>0}\<rangle>,\<langle>0,q\<rangle>\<rangle>\<in> ({reduce \<epsilon>-N-relation}(S,s\<^sub>0,t){in alphabet}\<Sigma>)^*)) \<or> (i = 0 \<and> s\<^sub>0\<in>F)"

text\<open>We define a locale to create some notation\<close>

locale NonDetFinStateAuto =
  fixes S and s\<^sub>0 and t and F and \<Sigma>
  assumes finite_alphabet: "Finite(\<Sigma>)"
  
  assumes NFSA: "(S,s\<^sub>0,t,F){is an NFSA for alphabet}\<Sigma>"

text\<open>Notation for the transition relation\<close>

abbreviation (in NonDetFinStateAuto) nd_rel ("r\<^sub>N")
  where "r\<^sub>N \<equiv> {reduce N-relation}(S,s\<^sub>0,t){in alphabet}\<Sigma>"

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
  "rPow \<equiv> DetFinStateAuto.r\<^sub>D(Pow(S),{s\<^sub>0},tPow,\<Sigma>)"

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

(*theorem concat_language:
  assumes "Finite(\<Sigma>)"
  and "L1{is a regular language on}\<Sigma>"
  and "L2{is a regular language on}\<Sigma>"
shows "concat(L1,L2) {is a regular language on}\<Sigma>"
proof-
  (*TODO: Need first to show that $\varepsilon$-transitions generate regular languages.*)
  oops
*)

end