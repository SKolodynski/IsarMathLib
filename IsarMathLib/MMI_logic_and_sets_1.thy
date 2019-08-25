(* 
    This file is a part of MMIsar - a translation of Metamath's set.mm to Isabelle 2005 (ZF logic).

    Copyright (C) 2006  Slawomir Kolodynski

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
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

*)

section \<open>More on logic and sets in Metamatah\<close>

theory MMI_logic_and_sets_1 imports MMI_logic_and_sets

begin

subsection\<open>Basic Metamath theorems, continued\<close>

text\<open>This section continues \<open>MMI_logic_and_sets\<close>. 
  It exists only so that we  don't have all Metamath basic 
  theorems in one huge file.\<close>

(**  dependencies of nnind and peano2nn *************)

lemma MMI_pm3_27d: assumes A1: "\<phi> \<longrightarrow> \<psi> \<and> ch"   
   shows "\<phi> \<longrightarrow> ch"
   using assms by auto

(*lemma MMI_elrab: original
  assumes A1: "x = A \<longrightarrow>  \<phi> \<longleftrightarrow> \<psi>"   
   shows "A \<in> {x \<in> B. \<phi> } \<longleftrightarrow> A \<in> B \<and> \<psi>"
   using assms by auto*)

lemma MMI_elrab:
  assumes A1: "\<forall>x. x = A \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<psi>(x)"   
  shows "A \<in> {x \<in> B. \<phi>(x) } \<longleftrightarrow> A \<in> B \<and> \<psi>(A)"
  using assms by auto

lemma MMI_ssrab2: 
   shows "{x \<in> A. \<phi>(x) } \<subseteq> A"
  by auto

lemma MMI_anim12d: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch" and
    A2: "\<phi> \<longrightarrow>  \<theta> \<longrightarrow> \<tau>"   
   shows "\<phi> \<longrightarrow> \<psi> \<and> \<theta> \<longrightarrow> ch \<and> \<tau>"
   using assms by auto

lemma MMI_mpcom: assumes A1: "\<psi> \<longrightarrow> \<phi>" and
    A2: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch"   
   shows "\<psi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_rabex: assumes A1: "A = A"   
   shows "{x \<in> A. \<phi>(x) } = {x \<in> A. \<phi>(x) }"
   using assms by auto

lemma MMI_rcla4cv: assumes A1: "\<forall>x. x = A \<longrightarrow> \<phi>(x) \<longleftrightarrow> \<psi>(x)"   
   shows "(\<forall>x\<in>B. \<phi>(x)) \<longrightarrow>  A \<in> B \<longrightarrow> \<psi>(A)"
  using assms by auto

lemma MMI_a2i: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch"   
   shows "(\<phi> \<longrightarrow> \<psi>) \<longrightarrow> \<phi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_19_20i: assumes A1: "\<forall>x. \<phi>(x) \<longrightarrow> \<psi>(x)"   
   shows "(\<forall>x. \<phi>(x)) \<longrightarrow> (\<forall>x. \<psi>(x))"
   using assms by auto

(*lemma MMI_elintab: assumes A1: "A = A"
   shows "A \<in> \<Inter> {x\<in> Pow(\<real>). \<phi> } \<longleftrightarrow> 
   (\<forall>x. \<phi> \<longrightarrow> A \<in> x)"
   using assms by auto; original *)
(* the Additional assumption is required bc. in Isabelle
  intersection of empty set is (pretty much) undefined *)

lemma MMI_elintab: assumes A1: "A = A"
  and Additional: "{x\<in>B. \<phi>(x) } \<noteq> 0"
   shows "A \<in> \<Inter> {x\<in>B. \<phi>(x) } \<longleftrightarrow> (\<forall>x\<in>B. \<phi>(x) \<longrightarrow> A \<in> x)"
   using assms by auto

(********* nn1suc **********)

(*lemma MMI_dfsbcq: 
   shows "A = B \<longrightarrow> 
   [ A / x ] \<phi> \<longleftrightarrow> [ B / x ] \<phi>"
  by auto

lemma MMI_sbequ: 
   shows "x = y \<longrightarrow> 
   [ x / z ] \<phi> \<longleftrightarrow> [ y / z ] \<phi>"
  by auto*)

lemma MMI_elex: 
   shows "A \<in> B \<longrightarrow> ( \<exists>x. x = A)"
  by auto

(*lemma MMI_hbsbc1: assumes A1: "y \<in> A \<longrightarrow> (\<forall>x. y \<in> A)"   
   shows "(A \<in> B \<longrightarrow> [ A / x ] \<phi>) \<longrightarrow> 
   (\<forall>x. A \<in> B \<longrightarrow> [ A / x ] \<phi>)"
   using assms by auto*)

(*lemma MMI_hbbi: assumes A1: "\<phi> \<longrightarrow> (\<forall>x. \<phi>)" and
    A2: "\<psi> \<longrightarrow> (\<forall>x. \<psi>)"   
   shows "\<phi> \<longleftrightarrow> \<psi> \<longrightarrow>  (\<forall>x. \<phi> \<longleftrightarrow> \<psi>)"
   using assms by auto;

lemma MMI_sbceq1a: 
   shows "x = A \<longrightarrow> 
   \<phi> \<longleftrightarrow> [ A / x ] \<phi>"
  by auto

lemma MMI_19_23ai: assumes A1: "\<psi> \<longrightarrow> (\<forall>x. \<psi>)" and
    A2: "\<phi> \<longrightarrow> \<psi>"   
   shows "( \<exists>x. \<phi>) \<longrightarrow> \<psi>"
   using assms by auto*)

lemma MMI_pm5_74rd: assumes A1: "\<phi> \<longrightarrow> 
   (\<psi> \<longrightarrow> ch) \<longleftrightarrow> 
   (\<psi> \<longrightarrow> \<theta>)"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> 
   ch \<longleftrightarrow> \<theta>"
   using assms by auto

lemma MMI_pm5_74d: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> 
   ch \<longleftrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> 
   (\<psi> \<longrightarrow> ch) \<longleftrightarrow> 
   (\<psi> \<longrightarrow> \<theta>)"
   using assms by auto

(*lemma MMI_sb19_21: assumes A1: "\<phi> \<longrightarrow> (\<forall>x. \<phi>)"   
   shows "[ y / x ] (\<phi> \<longrightarrow> \<psi>) \<longleftrightarrow> 
   (\<phi> \<longrightarrow> [ y / x ] \<psi>)"
   using assms by auto*)

lemma MMI_isseti: assumes A1: "A = A"   
   shows " \<exists>x. x = A"
   using assms by auto

(*lemma MMI_hbsbc1v: assumes A1: "A = A"   
   shows "[ A / x ] \<phi> \<longrightarrow> (\<forall>x. [ A / x ] \<phi>)"
   using assms by auto

lemma MMI_sbc19_21g: assumes A1: "\<phi> \<longrightarrow> (\<forall>x. \<phi>)"   
   shows "A \<in> B \<longrightarrow> 
   [ A / x ] (\<phi> \<longrightarrow> \<psi>) \<longleftrightarrow> 
   (\<phi> \<longrightarrow> [ A / x ] \<psi>)"
   using assms by auto*)

(******* nnaddclt ***********)

lemma MMI_a2d: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> 
   (\<psi> \<longrightarrow> ch) \<longrightarrow> 
   \<psi> \<longrightarrow> \<theta>"
   using assms by auto

(*** nnmulclt ***)

lemma MMI_exp4b: assumes A1: "\<phi> \<and> \<psi> \<longrightarrow> 
   ch \<and> \<theta> \<longrightarrow> \<tau>"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> 
   ch \<longrightarrow> 
   \<theta> \<longrightarrow> \<tau>"
   using assms by auto

lemma MMI_pm2_43b: assumes A1: "\<psi> \<longrightarrow> 
   \<phi> \<longrightarrow> \<psi> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch"
   using assms by auto

(********* nn2get nnge1t nngt1ne1t *********)
lemma MMI_biantrud: assumes A1: "\<phi> \<longrightarrow> \<psi>"   
   shows "\<phi> \<longrightarrow> 
   ch \<longleftrightarrow> ch \<and> \<psi>"
   using assms by auto

lemma MMI_anc2li: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> \<phi> \<and> ch"
   using assms by auto

lemma MMI_biantrurd: assumes A1: "\<phi> \<longrightarrow> \<psi>"   
   shows "\<phi> \<longrightarrow> 
   ch \<longleftrightarrow> \<psi> \<and> ch"
   using assms by auto

(*****nnle1eq1t-lt1nnn***********)
lemma MMI_sylc: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch" and
    A2: "\<theta> \<longrightarrow> \<phi>" and
    A3: "\<theta> \<longrightarrow> \<psi>"   
   shows "\<theta> \<longrightarrow> ch"
   using assms by auto

lemma MMI_con3i: assumes Aa: "\<phi> \<longrightarrow> \<psi>"   
   shows "\<not>\<psi> \<longrightarrow> \<not>\<phi>"
   using assms by auto

(*********** nnleltp1t - nnaddm1clt ***********)
lemma MMI_mpan2i: assumes A1: "ch" and
    A2: "\<phi> \<longrightarrow> 
   \<psi> \<and> ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_ralbidv: assumes A1: "\<forall>x. \<phi> \<longrightarrow>  \<psi>(x) \<longleftrightarrow> ch(x)"   
   shows "\<phi> \<longrightarrow> (\<forall>x\<in>A. \<psi>(x)) \<longleftrightarrow> (\<forall>x\<in>A. ch(x))"
   using assms by auto

lemma MMI_mp3an23: assumes A1: "\<psi>" and
    A2: "ch" and
    A3: "\<phi> \<and> \<psi> \<and> ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> \<theta>"
   using assms by auto

lemma (in MMIsar0) MMI_syl5eqbrr: assumes A1: "\<phi> \<longrightarrow> A \<ls> B" and
    A2: "A = C"   
   shows "\<phi> \<longrightarrow> C \<ls> B"
   using assms by auto

lemma MMI_rcla4va: assumes A1: "\<forall>x. x = A \<longrightarrow> \<phi>(x) \<longleftrightarrow> \<psi>(A)"   
   shows "A \<in> B \<and> (\<forall>x\<in>B. \<phi>(x)) \<longrightarrow> \<psi>(A)"
   using assms by auto

lemma MMI_3anrot: 
   shows "\<phi> \<and> \<psi> \<and> ch \<longleftrightarrow> \<psi> \<and> ch \<and> \<phi>"
  by auto

lemma MMI_3simpc: 
   shows "\<phi> \<and> \<psi> \<and> ch \<longrightarrow> \<psi> \<and> ch"
  by auto

lemma MMI_anandir: 
   shows "(\<phi> \<and> \<psi>) \<and> ch \<longleftrightarrow> 
   (\<phi> \<and> ch) \<and> \<psi> \<and> ch"
  by auto

lemma MMI_eqeqan12d: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<psi> \<longrightarrow> C = D"   
   shows "\<phi> \<and> \<psi> \<longrightarrow> 
   A = C \<longleftrightarrow> B = D"
   using assms by auto

lemma MMI_3imtr3d: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch" and
    A2: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> \<theta>" and
    A3: "\<phi> \<longrightarrow> 
   ch \<longleftrightarrow> \<tau>"   
   shows "\<phi> \<longrightarrow> 
   \<theta> \<longrightarrow> \<tau>"
   using assms by auto

lemma MMI_exp31: assumes A1: "(\<phi> \<and> \<psi>) \<and> ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> ch \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_com3l: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> ch \<longrightarrow> \<theta>"   
   shows "\<psi> \<longrightarrow> 
   ch \<longrightarrow> 
   \<phi> \<longrightarrow> \<theta>"
   using assms by auto

(** original
lemma MMI_r19_21adv: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> x \<in> A \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> (\<forall>x\<in>A. ch)"
   using assms by auto *)
lemma MMI_r19_21adv: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> (\<forall>x. x \<in> A \<longrightarrow> ch)"   
   shows "\<phi> \<longrightarrow> \<psi> \<longrightarrow> (\<forall>x\<in>A. ch)"
   using assms by auto

lemma MMI_cbvralv: assumes A1: "\<forall>x y. x = y \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<psi>(y)"   
   shows "(\<forall>x\<in>A. \<phi>(x)) \<longleftrightarrow> (\<forall>y\<in>A. \<psi>(y))"
   using assms by auto

lemma MMI_syl5ib: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch" and
    A2: "\<theta> \<longleftrightarrow> \<psi>"   
   shows "\<phi> \<longrightarrow> \<theta> \<longrightarrow> ch"
   using assms by auto

lemma MMI_pm2_21i: assumes A1: "\<not>\<phi>"   
   shows "\<phi> \<longrightarrow> \<psi>"
   using assms by auto

lemma MMI_imim2d: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   (\<theta> \<longrightarrow> \<psi>) \<longrightarrow> \<theta> \<longrightarrow> ch"
   using assms by auto

lemma MMI_syl6eqelr: assumes A1: "\<phi> \<longrightarrow> B = A" and
    A2: "B \<in> C"   
   shows "\<phi> \<longrightarrow> A \<in> C"
   using assms by auto

(********** nndivt,nndivtrt ****************)

lemma MMI_r19_23adv: 
  assumes A1: "\<forall>x. \<phi> \<longrightarrow>  x \<in> A \<longrightarrow> \<psi>(x) \<longrightarrow> ch"   
  shows "\<phi> \<longrightarrow> ( \<exists>x\<in>A. \<psi>(x)) \<longrightarrow> ch"
  using assms by auto

(*****9re - 2nn *********************)

lemma (in MMIsar0) MMI_breqtrr: assumes A1: "A \<ls> B" and
    A2: "C = B"   
   shows "A \<ls> C"
   using assms by auto

(******* ltdiv23i- lble ****************)

lemma (in MMIsar0) MMI_eqbrtr: assumes A1: "A = B" and
    A2: "B \<ls> C"   
   shows "A \<ls> C"
   using assms by auto

lemma MMI_nrex: assumes A1: "\<forall>x. x \<in> A \<longrightarrow> \<not>\<psi>(x)"   
   shows "\<not>( \<exists>x\<in>A. \<psi>(x))"
   using assms by auto

lemma MMI_iman: 
   shows "(\<phi> \<longrightarrow> \<psi>) \<longleftrightarrow> 
   \<not>(\<phi> \<and> \<not>\<psi>)"
  by auto

lemma MMI_im2anan9r: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch" and
    A2: "\<theta> \<longrightarrow> 
   \<tau> \<longrightarrow> \<eta>"   
   shows "\<theta> \<and> \<phi> \<longrightarrow> 
   \<psi> \<and> \<tau> \<longrightarrow> ch \<and> \<eta>"
   using assms by auto

lemma MMI_ssel: 
   shows "A \<subseteq>B \<longrightarrow> 
   C \<in> A \<longrightarrow> C \<in> B"
  by auto

lemma MMI_com3r: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> ch \<longrightarrow> \<theta>"   
   shows "ch \<longrightarrow> 
   \<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> \<theta>"
   using assms by auto


(*lemma MMI_r19_21aivv: 
  assumes A1: "\<forall>x y. \<phi> \<longrightarrow>  (x \<in> A \<and> y \<in> B \<longrightarrow> \<psi>(x,y))"   
   shows "\<phi> \<longrightarrow> (\<forall>x\<in>A. \<forall>y\<in>B. \<psi>(x,y))"
   using assms by auto;*)


lemma MMI_r19_21aivv: 
  assumes A1: "\<phi> \<longrightarrow>  (\<forall>x y.  x \<in> A \<and> y \<in> B \<longrightarrow> \<psi>(x,y))"   
   shows "\<phi> \<longrightarrow> (\<forall>x\<in>A. \<forall>y\<in>B. \<psi>(x,y))"
   using assms by auto

lemma MMI_reucl2: 
   shows 
  "(\<exists>!x. x\<in>A \<and> \<phi>(x)) \<longrightarrow> \<Union> {x \<in> A. \<phi>(x)} \<in> {x \<in> A. \<phi>(x) }"
proof
  assume "\<exists>!x. x\<in>A \<and> \<phi>(x)"
  then obtain a where I: "{a} = {x\<in>A. \<phi>(x)}" by auto
  moreover have "\<Union>{a} = a" by auto
  moreover have "a \<in> {a}" by blast
  ultimately show "\<Union> {x \<in> A. \<phi>(x)} \<in> {x \<in> A. \<phi>(x) }"
    by simp
qed

lemma MMI_hbra1: 
   shows "(\<forall>x\<in>A. \<phi>(x)) \<longrightarrow> (\<forall>x. \<forall>x\<in>A. \<phi>(x))"
  by auto

lemma MMI_hbrab: assumes A1: "\<phi> \<longrightarrow> (\<forall>x. \<phi>)" and
    A2: "z \<in> A \<longrightarrow> (\<forall>x. z \<in> A)"   
   shows "z \<in> {y \<in> A. \<phi> } \<longrightarrow> 
   (\<forall>x. z \<in> {y \<in> A. \<phi> })"
   using assms by auto

lemma MMI_hbuni: assumes A1: "y \<in> A \<longrightarrow> (\<forall>x. y \<in> A)"   
   shows "y \<in> \<Union> A \<longrightarrow>  (\<forall>x. y \<in> \<Union> A)"
   using assms by auto

lemma (in MMIsar0) MMI_hbbr: assumes A1: "y \<in> A \<longrightarrow> (\<forall>x. y \<in> A)" and
    A2: "y \<in> R \<longrightarrow> (\<forall>x. y \<in> R)" and
    A3: "y \<in> B \<longrightarrow> (\<forall>x. y \<in> B)"   
   shows 
  "A \<lsq> B \<longrightarrow> (\<forall>x. A \<lsq> B)"
  "A \<ls> B \<longrightarrow> (\<forall>x. A \<ls> B)"
   using assms by auto

lemma MMI_rcla4: assumes A1: "\<psi> \<longrightarrow> (\<forall>x. \<psi>)" and
    A2: "\<forall>x. x = A \<longrightarrow> \<phi> \<longleftrightarrow> \<psi>"   
   shows "A \<in> B \<longrightarrow>  (\<forall>x\<in>B. \<phi>) \<longrightarrow> \<psi>"
   using assms by auto

lemma twimp2eq: assumes "p\<longrightarrow>q" and "q\<longrightarrow>p" shows "p\<longleftrightarrow>q"
  using assms by blast

lemma MMI_cbvreuv: assumes A1: "\<forall>x y. x = y \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<psi>(y)"   
   shows "(\<exists>!x. x\<in>A\<and>\<phi>(x)) \<longleftrightarrow> (\<exists>!y. y\<in>A\<and>\<psi>(y))"
   using assms
proof -
  { assume A2: "\<exists>!x. x\<in>A \<and> \<phi>(x)"
    then obtain a where I: "a\<in>A" and II: "\<phi>(a)" by auto
    with A1 have "\<psi>(a)" by simp
    with I have "\<exists>y. y\<in>A\<and>\<psi>(y)" by auto
    moreover
    { fix y\<^sub>1 y\<^sub>2
      assume "y\<^sub>1\<in>A \<and> \<psi>(y\<^sub>1)" and "y\<^sub>2\<in>A \<and> \<psi>(y\<^sub>2)"
      with A1 have "y\<^sub>1\<in>A \<and> \<phi>(y\<^sub>1)" and "y\<^sub>2\<in>A \<and> \<phi>(y\<^sub>2)" by auto
      with A2 have "y\<^sub>1 = y\<^sub>2" by auto }
    ultimately have "\<exists>!y. y\<in>A \<and> \<psi>(y)" by auto
  } then have "(\<exists>!x. x\<in>A\<and>\<phi>(x)) \<longrightarrow> (\<exists>!y. y\<in>A\<and>\<psi>(y))" by simp
  moreover
  { assume A2: "\<exists>!y. y\<in>A \<and> \<psi>(y)"
    then obtain a where I: "a\<in>A" and II: "\<psi>(a)" by auto
    with A1 have "\<phi>(a)" by simp
    with I have "\<exists>x. x\<in>A \<and> \<phi>(x)" by auto
    moreover
    { fix x\<^sub>1 x\<^sub>2
      assume "x\<^sub>1\<in>A \<and> \<phi>(x\<^sub>1)" and "x\<^sub>2\<in>A \<and> \<phi>(x\<^sub>2)"
      with A1 have "x\<^sub>1\<in>A \<and> \<psi>(x\<^sub>1)" and "x\<^sub>2\<in>A \<and> \<psi>(x\<^sub>2)" by auto
      with A2 have "x\<^sub>1 = x\<^sub>2" by auto }
    ultimately have "\<exists>!x. x\<in>A \<and> \<phi>(x)" by auto
  } then have "(\<exists>!y. y\<in>A\<and>\<psi>(y)) \<longrightarrow> (\<exists>!x. x\<in>A\<and>\<phi>(x))" by simp
  ultimately show ?thesis by (rule twimp2eq)
qed
      
lemma MMI_hbeleq: assumes A1: "y \<in> A \<longrightarrow> (\<forall>x. y \<in> A)"   
   shows "y = A \<longrightarrow> (\<forall>x. y = A)"
   using assms by auto

lemma MMI_ralbid: assumes A1: "\<phi> \<longrightarrow> (\<forall>x. \<phi>)" and
    A2: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   (\<forall>x\<in>A. \<psi>) \<longleftrightarrow> (\<forall>x\<in>A. ch)"
   using assms by auto

lemma MMI_reuuni3: 
  assumes A1: "\<forall>x y. x = y \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<psi>(y)" and
    A2: "\<forall>x. x = \<Union> {y \<in> A. \<psi>(y) } \<longrightarrow>  (\<phi>(x) \<longleftrightarrow> ch)"   
   shows "(\<exists>!x. x\<in>A \<and> \<phi>(x)) \<longrightarrow> ch"
proof
  assume A3: "\<exists>!x. x\<in>A \<and> \<phi>(x)"
  then obtain a where I: "{a} = {x\<in>A. \<phi>(x)}" by auto
  with A1 have "{a} = {y\<in>A. \<psi>(y)}" by auto
  moreover have "\<Union>{a} = a" by auto
  ultimately have "a = \<Union> {y \<in> A. \<psi>(y) }" by auto
  with A2 have "\<phi>(a) \<longleftrightarrow> ch" by simp
  moreover 
  have "a \<in> {a}" by simp
  with I have "\<phi>(a)" by simp
  ultimately show "ch" by simp
qed

(******* lbinfm ****************)

lemma MMI_ssex: assumes A1: "B = B"   
   shows "A \<subseteq>B \<longrightarrow> A = A"
   using assms by auto

lemma MMI_rabexg: 
   shows "A \<in> B \<longrightarrow> 
   {x \<in> A. \<phi>(x) } = {x \<in> A. \<phi>(x) }"
  by auto

lemma MMI_uniexg: 
   shows "A \<in> B \<longrightarrow> \<Union>A = \<Union>A "
  by auto

(*lemma (in MMIsar0) MMI_brcnvg: 
  shows "A \<in> C \<and> B \<in> D \<longrightarrow>  A > B \<longleftrightarrow> B \<ls> A"
  using cltrr_def convcltrr_def converse_iff by auto original *)

lemma (in MMIsar0) MMI_brcnvg: 
  shows "A = A \<and> B = B \<longrightarrow>  A > B \<longleftrightarrow> B \<ls> A"
  using cltrr_def convcltrr_def converse_iff by auto

lemma MMI_r19_21aiva: assumes A1: "\<forall>x. \<phi> \<and> x \<in> A \<longrightarrow> \<psi>(x)"   
   shows "\<phi> \<longrightarrow> (\<forall>x\<in>A. \<psi>(x))"
   using assms by auto

lemma MMI_ancrd: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> ch \<and> \<psi>"
   using assms by auto

lemma MMI_reuuni2: 
  assumes A1: "\<forall>x. x = B \<longrightarrow> \<phi>(x) \<longleftrightarrow> \<psi>"   
   shows "B \<in> A \<and> (\<exists>!x. x\<in>A\<and>\<phi>(x)) \<longrightarrow> 
   \<psi> \<longleftrightarrow>  \<Union> {x \<in> A. \<phi>(x) } = B"
proof
  assume A2: "B \<in> A \<and> (\<exists>!x. x\<in>A\<and>\<phi>(x))"
  { assume "\<psi>"
    with A1 have "\<phi>(B)" by simp
    with A2 have "{x \<in> A. \<phi>(x) } = {B}" by auto
    then have "\<Union> {x \<in> A. \<phi>(x) } = B" by auto }
  moreover
  { assume A3: "\<Union> {x \<in> A. \<phi>(x) } = B"
    moreover 
    from A2 obtain b where I: "{b} = {x \<in> A. \<phi>(x) }" by auto
    moreover have "\<Union>{b} = b" by auto
    ultimately have "\<Union> {x \<in> A. \<phi>(x) } = b" by simp
    with A3 I have "{B} = {x \<in> A. \<phi>(x) }" by simp
    moreover have "B \<in> {B}" by simp
    ultimately have "\<phi>(B)" by auto
    with A1 have "\<psi>" by simp }
  ultimately show "\<psi> \<longleftrightarrow>  \<Union> {x \<in> A. \<phi>(x) } = B" by blast
qed

lemma (in MMIsar0) MMI_cnvso: 
   shows "\<cltrrset> Orders A \<longleftrightarrow> converse(\<cltrrset>) Orders A"
  using cnvso by simp

lemma (in MMIsar0) MMI_supeu: assumes A1: "\<cltrrset> Orders A"   
   shows "( \<exists>x\<in>A. (\<forall>y\<in>B. \<not>(x\<ls>y)) \<and> (\<forall>y\<in>A. y \<ls> x \<longrightarrow> ( \<exists>z\<in>B. y \<ls> z))) \<longrightarrow> 
   (\<exists>!x. x\<in>A\<and>(\<forall>y\<in>B. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>A. y \<ls> x \<longrightarrow> ( \<exists>z\<in>B. y \<ls> z)))"
proof
  assume 
    "\<exists>x\<in>A. (\<forall>y\<in>B. \<not>(x\<ls>y)) \<and> (\<forall>y\<in>A. y \<ls> x \<longrightarrow> ( \<exists>z\<in>B. y \<ls> z))"
  then obtain x where 
    "x\<in>A"  "\<forall>y\<in>B. \<langle>x,y\<rangle> \<notin> \<cltrrset>"  
    "\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> \<cltrrset>  \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> \<cltrrset>)"
    using cltrr_def by auto
  with A1 have
    "\<exists>!x. x\<in>A\<and>(\<forall>y\<in>B. \<langle>x,y\<rangle> \<notin> \<cltrrset>) \<and> (\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> \<cltrrset> \<longrightarrow> 
    ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> \<cltrrset>))"
    using supeu by simp
  then show
    "\<exists>!x. x\<in>A\<and>(\<forall>y\<in>B. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>A. y \<ls> x \<longrightarrow> ( \<exists>z\<in>B. y \<ls> z))"
    using cltrr_def by simp
qed

(** This is actually not in Metamath, we need it only because 
    Isabelle does not support $a R b$ notation for relations $R$. 
    Metamath covers both we MMI_supeu and MMI_infeu 
    in one theorem, we need two **)

lemma (in MMIsar0) MMI_infeu: assumes A1: "converse(\<cltrrset>) Orders A"   
   shows 
  "(\<exists>x\<in>A. (\<forall>y\<in>B. \<not>(x > y)) \<and> (\<forall>y\<in>A. y  >  x \<longrightarrow> ( \<exists>z\<in>B. y  >  z))) \<longrightarrow> 
   (\<exists>!x. x\<in>A\<and>(\<forall>y\<in>B. \<not>(x  >  y)) \<and> (\<forall>y\<in>A. y  >  x \<longrightarrow> ( \<exists>z\<in>B. y  >  z)))"
proof
  let ?r = "converse(\<cltrrset>)"
  assume 
    "\<exists>x\<in>A. (\<forall>y\<in>B. \<not>(x > y)) \<and> (\<forall>y\<in>A. y  >  x \<longrightarrow> ( \<exists>z\<in>B. y  >  z))"
  then obtain x where 
    "x\<in>A"  "\<forall>y\<in>B. \<langle>x,y\<rangle> \<notin> ?r"  
    "\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> ?r  \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> ?r)"
    using convcltrr_def by auto
  with A1 have
    "\<exists>!x. x\<in>A\<and>(\<forall>y\<in>B. \<langle>x,y\<rangle> \<notin> ?r) \<and> (\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> ?r \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> ?r))"
    by (rule supeu)
  then show
    "\<exists>!x. x\<in>A\<and>(\<forall>y\<in>B. \<not>(x  >  y)) \<and> (\<forall>y\<in>A. y  >  x \<longrightarrow> ( \<exists>z\<in>B. y  >  z))"
    using convcltrr_def by simp
qed

(******** lbinfmcl, lbinfmle ***********************)

lemma MMI_eqeltrd: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<phi> \<longrightarrow> B \<in> C"   
   shows "\<phi> \<longrightarrow> A \<in> C"
   using assms by auto

lemma (in MMIsar0) MMI_eqbrtrd: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<phi> \<longrightarrow> B \<lsq> C"   
   shows "\<phi> \<longrightarrow> A \<lsq> C"
   using assms by auto

(****** sup2 ************************************)

lemma MMI_df_ral: shows "(\<forall>x\<in>A. \<phi>(x)) \<longleftrightarrow> (\<forall>x. x\<in>A \<longrightarrow> \<phi>(x))"
  by auto

lemma MMI_df_3an: shows  "(\<phi> \<and> \<psi>  \<and> ch ) \<longleftrightarrow> ( (\<phi> \<and> \<psi> ) \<and> ch )"
  by auto

lemma MMI_pm2_43d: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> \<psi> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_biimprcd: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch"   
   shows "ch \<longrightarrow> 
   \<phi> \<longrightarrow> \<psi>"
   using assms by auto

lemma MMI_19_20dv: assumes A1: "\<forall> y. \<phi> \<longrightarrow> \<psi>(y) \<longrightarrow> ch(y)"   
   shows "\<phi> \<longrightarrow>  (\<forall>y. \<psi>(y)) \<longrightarrow> (\<forall>y. ch(y))"
   using assms by auto

lemma MMI_cla4ev: assumes A1: "A = A" and
    A2: "\<forall>x. x = A \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<psi>(x)"   
   shows "\<psi>(A) \<longrightarrow> ( \<exists>x. \<phi>(x))"
   using assms by auto

lemma MMI_19_23adv: assumes A1: "\<forall>x. \<phi> \<longrightarrow> \<psi>(x) \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow>  ( \<exists>x. \<psi>(x)) \<longrightarrow> ch"
   using assms by auto

lemma MMI_cbvexv: assumes A1: "\<forall>x y. x = y \<longrightarrow> \<phi>(x) \<longleftrightarrow> \<psi>(y)"   
   shows "( \<exists>x. \<phi>(x)) \<longleftrightarrow> ( \<exists>y. \<psi>(y))"
   using assms by auto

(********** sup3 *********************)

lemma MMI_bicomi: assumes A1: "\<phi> \<longleftrightarrow> \<psi>"   
   shows "\<psi> \<longleftrightarrow> \<phi>"
   using assms by auto

lemma MMI_syl9: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch" and
    A2: "\<theta> \<longrightarrow> ch \<longrightarrow> \<tau>"   
   shows "\<phi> \<longrightarrow> 
   \<theta> \<longrightarrow> 
   \<psi> \<longrightarrow> \<tau>"
   using assms by auto

lemma MMI_imp31: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> ch \<longrightarrow> \<theta>"   
   shows "(\<phi> \<and> \<psi>) \<and> ch \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_pm5_32i: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch"   
   shows "\<phi> \<and> \<psi> \<longleftrightarrow> \<phi> \<and> ch"
   using assms by auto

(****** infm3 *************************)

lemma MMI_3impib: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<and> ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<and> \<psi> \<and> ch \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_pm4_71rd: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch \<and> \<psi>"
   using assms by auto

lemma MMI_exbidv: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   ( \<exists>x. \<psi>) \<longleftrightarrow> ( \<exists>x. ch)"
   using assms by auto

(** original
lemma MMI_rexxfr: assumes A1: "y \<in> B \<longrightarrow> A \<in> B" and
    A2: "x \<in> B \<longrightarrow> ( \<exists>y\<in>B. x = A)" and
    A3: "x = A \<longrightarrow> 
   \<phi> \<longleftrightarrow> \<psi>"   
   shows "( \<exists>x\<in>B. \<phi>) \<longleftrightarrow> ( \<exists>y\<in>B. \<psi>)"
   using assms by auto *********)

lemma MMI_rexxfr: assumes A1: "\<forall>y. y \<in> B \<longrightarrow> A(y) \<in> B" and
    A2: "\<forall> x. x \<in> B \<longrightarrow> ( \<exists>y\<in>B. x = A(y))" and
    A3: "\<forall> x y. x = A(y) \<longrightarrow> ( \<phi>(x) \<longleftrightarrow> \<psi>(y) ) "   
   shows "( \<exists>x\<in>B. \<phi>(x)) \<longleftrightarrow> ( \<exists>y\<in>B. \<psi>(y))"
proof
  assume "\<exists>x\<in>B. \<phi>(x)"
  then obtain x where "x\<in>B" and I: "\<phi>(x)" by auto
  with A2 obtain y where II: "y\<in>B" and "x=A(y)" by auto
  with A3 I have "\<psi>(y)" by simp
  with II show "\<exists>y\<in>B. \<psi>(y)" by auto
next assume "\<exists>y\<in>B. \<psi>(y)"
  then obtain y where "y\<in>B" and III: "\<psi>(y)" by auto
  with A1 have IV: "A(y) \<in> B" by simp
  with A2 obtain x where "x\<in>B" and "A(x) = A(y)" by auto
  with A3 III have "\<phi>(A(y))" by auto
  with IV show "\<exists>x\<in>B. \<phi>(x)" by auto
qed
  
lemma MMI_n0: 
   shows "\<not>(A = 0) \<longleftrightarrow> ( \<exists>x. x \<in> A)"
  by auto

lemma MMI_rabn0: 
   shows "\<not>({x \<in> A. \<phi>(x) } = 0) \<longleftrightarrow> ( \<exists>x\<in>A. \<phi>(x))"
  by auto

lemma MMI_impexp: 
   shows "(\<phi> \<and> \<psi> \<longrightarrow> ch) \<longleftrightarrow> 
   (\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch)"
  by auto

lemma MMI_albidv: assumes A1: "\<forall>x. \<phi> \<longrightarrow>  \<psi>(x) \<longleftrightarrow> ch(x)"   
   shows "\<phi> \<longrightarrow>  (\<forall>x. \<psi>(x)) \<longleftrightarrow> (\<forall>x. ch(x))"
   using assms by auto

lemma MMI_ralxfr: assumes A1: "\<forall>y. y \<in> B \<longrightarrow> A(y) \<in> B" and
    A2: "\<forall>x. x \<in> B \<longrightarrow> ( \<exists>y\<in>B. x = A(y))" and
    A3: "\<forall>x y. x = A(y) \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<psi>(y)"   
   shows "(\<forall>x\<in>B. \<phi>(x)) \<longleftrightarrow> (\<forall>y\<in>B. \<psi>(y))"
proof
  assume A4: "\<forall>x\<in>B. \<phi>(x)"
  { fix y assume "y\<in>B"
    with A1 A3 A4 have "\<psi>(y)" by auto
  } then show "\<forall>y\<in>B. \<psi>(y)" by simp
next assume A5: "\<forall>y\<in>B. \<psi>(y)"
  { fix x assume "x\<in>B"
    with A2 A3 A5 have "\<phi>(x)" by auto
  } then show "\<forall>x\<in>B. \<phi>(x)" by simp
qed

lemma MMI_rexbidv: assumes A1: "\<forall>x. \<phi> \<longrightarrow>  \<psi>(x) \<longleftrightarrow> ch(x)"   
   shows "\<phi> \<longrightarrow> ( \<exists>x\<in>A. \<psi>(x)) \<longleftrightarrow> ( \<exists>x\<in>A. ch(x))"
   using assms by auto

lemma MMI_imbi1i: assumes Aa: "\<phi> \<longleftrightarrow> \<psi>"   
   shows "(\<phi> \<longrightarrow> ch) \<longleftrightarrow> (\<psi> \<longrightarrow> ch)"
   using assms by auto

lemma MMI_3bitr4r: assumes A1: "\<phi> \<longleftrightarrow> \<psi>" and
    A2: "ch \<longleftrightarrow> \<phi>" and
    A3: "\<theta> \<longleftrightarrow> \<psi>"   
   shows "\<theta> \<longleftrightarrow> ch"
   using assms by auto

lemma MMI_rexbiia: assumes A1: "\<forall>x. x \<in> A \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<psi>(x)"   
   shows "( \<exists>x\<in>A. \<phi>(x)) \<longleftrightarrow> ( \<exists>x\<in>A. \<psi>(x))"
   using assms by auto

lemma MMI_anass: 
   shows "(\<phi> \<and> \<psi>) \<and> ch \<longleftrightarrow> \<phi> \<and> \<psi> \<and> ch"
  by auto

lemma MMI_rexbii2: assumes A1: "\<forall>x. x \<in> A \<and> \<phi>(x) \<longleftrightarrow> x \<in> B \<and> \<psi>(x)"   
   shows "( \<exists>x\<in>A. \<phi>(x)) \<longleftrightarrow> ( \<exists>x\<in>B. \<psi>(x))"
   using assms by auto

lemma MMI_sylibrd: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch" and
    A2: "\<phi> \<longrightarrow> 
   \<theta> \<longleftrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> \<theta>"
   using assms by auto

(************** suprcl, suprub *******************)

lemma (in MMIsar0) MMI_supcl: assumes A1:   "\<cltrrset> Orders A"
  shows 
  "( \<exists>x\<in>A. (\<forall>y\<in>B. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>A. y \<ls> x \<longrightarrow> 
  ( \<exists>z\<in>B. y \<ls> z))) \<longrightarrow>  Sup(B,A,\<cltrrset>) \<in> A"
proof
  let ?R = "\<cltrrset>"
  assume 
    "\<exists>x\<in>A. (\<forall>y\<in>B. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>A. y \<ls> x \<longrightarrow> ( \<exists>z\<in>B. y \<ls> z))"
  then have 
    "\<exists>x\<in>A. (\<forall>y\<in>B. \<not>(\<langle>x,y\<rangle> \<in> ?R) ) \<and> (\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> ?R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> ?R))"
    using cltrr_def by simp
  with A1 show "Sup(B,A,?R) \<in> A" by (rule sup_props)
qed

lemma (in MMIsar0) MMI_supub: assumes A1: "\<cltrrset> Orders A"   
   shows 
  "( \<exists>x\<in>A. (\<forall>y\<in>B. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>A. y \<ls> x \<longrightarrow> ( \<exists>z\<in>B. y \<ls> z))) \<longrightarrow> 
   C \<in> B \<longrightarrow> \<not>( Sup(B,A,\<cltrrset>) \<ls> C)"
proof
  let ?R = "\<cltrrset>"
  assume 
    "\<exists>x\<in>A. (\<forall>y\<in>B. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>A. y \<ls> x \<longrightarrow> ( \<exists>z\<in>B. y \<ls> z))"
  then have
    "\<exists>x\<in>A. (\<forall>y\<in>B. \<langle>x,y\<rangle> \<notin> ?R) \<and> (\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> ?R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> ?R))"
    using cltrr_def by simp
  with A1 have I: "\<forall>y\<in>B. \<langle>Sup(B,A,?R),y\<rangle> \<notin> ?R" by (rule sup_props)
  { assume "C \<in> B"
    with I have  "\<not>( Sup(B,A,?R) \<ls> C)" using cltrr_def by simp
  } then show "C \<in> B \<longrightarrow> \<not>( Sup(B,A,?R) \<ls> C)" by simp
qed

lemma MMI_sseld: assumes A1: "\<phi> \<longrightarrow> A \<subseteq> B"   
   shows "\<phi> \<longrightarrow> C \<in> A \<longrightarrow> C \<in> B"
   using assms by auto

(********suprlub - suprleub **********************)

lemma (in MMIsar0) MMI_suplub: assumes A1: "\<cltrrset> Orders A"   
   shows "( \<exists>x\<in>A. (\<forall>y\<in>B. \<not>(x \<ls> y)) \<and> 
  (\<forall>y\<in>A. y \<ls> x \<longrightarrow> ( \<exists>z\<in>B. y \<ls> z))) \<longrightarrow> 
   C \<in> A \<and> C \<ls> Sup(B,A,\<cltrrset>) \<longrightarrow> ( \<exists>z\<in>B. C \<ls> z)"
proof
  let ?R = "\<cltrrset>"
  assume 
    "\<exists>x\<in>A. (\<forall>y\<in>B. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>A. y \<ls> x \<longrightarrow> ( \<exists>z\<in>B. y \<ls> z))"
  then have
    "\<exists>x\<in>A. (\<forall>y\<in>B. \<langle>x,y\<rangle> \<notin> ?R) \<and> (\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> ?R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> ?R))"
    using cltrr_def by simp
  with A1 have I:
    "\<forall>y\<in>A. \<langle>y,Sup(B,A,?R)\<rangle> \<in> ?R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> ?R )"
    by (rule sup_props)
  then show "C \<in> A \<and> C \<ls> Sup(B,A,?R) \<longrightarrow> ( \<exists>z\<in>B. C \<ls> z)"
    using cltrr_def by simp
qed

lemma (in MMIsar0) MMI_supnub: assumes A1: "\<cltrrset> Orders A"   
   shows 
  "(\<exists>x\<in>A. (\<forall>y\<in>B. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>A. y \<ls> x \<longrightarrow> 
  ( \<exists>z\<in>B. y \<ls> z))) \<longrightarrow> 
   C \<in> A \<and> (\<forall>z\<in>B. \<not>(C \<ls> z)) \<longrightarrow> \<not>(C \<ls> Sup(B,A,\<cltrrset>))"
proof
  let ?R = "\<cltrrset>"
  assume 
    "\<exists>x\<in>A. (\<forall>y\<in>B. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>A. y \<ls> x \<longrightarrow> ( \<exists>z\<in>B. y \<ls> z))"
  then have
    "\<exists>x\<in>A. (\<forall>y\<in>B. \<langle>x,y\<rangle> \<notin> ?R) \<and> (\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> ?R \<longrightarrow> ( \<exists>z\<in>B. \<langle>y,z\<rangle> \<in> ?R))"
    using cltrr_def by simp
  with A1 show
    "C \<in> A \<and> (\<forall>z\<in>B. \<not>(C \<ls> z)) \<longrightarrow> \<not>(C \<ls> Sup(B,A,\<cltrrset>))"
    using cltrr_def supnub by simp
qed

lemma MMI_pm5_32d: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow>  ch \<longleftrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow>  \<psi> \<and> ch \<longleftrightarrow> \<psi> \<and> \<theta>"
   using assms by auto

(********* sup3i - suprnubi **********************)

lemma (in MMIsar0) MMI_supcli: 
  assumes A1: "\<cltrrset> Orders A" and A2: 
  "\<exists>x\<in>A. (\<forall>y\<in>B. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>A. y \<ls> x \<longrightarrow> ( \<exists>z\<in>B. y \<ls> z))"   
  shows "Sup(B,A,\<cltrrset>) \<in> A"
  using assms MMI_supcl by simp

lemma (in MMIsar0) MMI_suplubi: assumes A1: "\<cltrrset> Orders A" and
  A2: "\<exists>x\<in>A. (\<forall>y\<in>B. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>A. y \<ls> x \<longrightarrow> ( \<exists>z\<in>B. y \<ls> z))"  
  shows "C \<in> A \<and> C \<ls> Sup(B,A,\<cltrrset>) \<longrightarrow> ( \<exists>z\<in>B. C \<ls> z)"
proof -
  from A1 have "( \<exists>x\<in>A. (\<forall>y\<in>B. \<not>(x \<ls> y)) \<and> 
    (\<forall>y\<in>A. y \<ls> x \<longrightarrow> ( \<exists>z\<in>B. y \<ls> z))) \<longrightarrow> 
    C \<in> A \<and> C \<ls> Sup(B,A,\<cltrrset>) \<longrightarrow> ( \<exists>z\<in>B. C \<ls> z)"
    by (rule MMI_suplub)
  with A2 show "C \<in> A \<and> C \<ls> Sup(B,A,\<cltrrset>) \<longrightarrow> ( \<exists>z\<in>B. C \<ls> z)"
    by simp
qed

lemma  (in MMIsar0) MMI_supnubi: assumes A1: "\<cltrrset> Orders A" and
    A2: " \<exists>x\<in>A. (\<forall>y\<in>B. \<not>(x \<ls> y)) \<and> 
  (\<forall>y\<in>A. y \<ls> x \<longrightarrow> ( \<exists>z\<in>B. y \<ls> z))"   
   shows "C \<in> A \<and> (\<forall>z\<in>B. \<not>(C \<ls> z)) \<longrightarrow> \<not>(C \<ls>Sup(B,A,\<cltrrset>))"
   using assms  MMI_supnub by simp

(************ suprleubi - dfinfmr *********************)

lemma MMI_reuunixfr_helper: assumes
  A1: "\<forall>x y. x = B(y) \<longrightarrow> \<phi>(x) \<longleftrightarrow> \<psi>(y)" and 
  A2: "\<forall>y. y\<in>A \<longrightarrow> B(y) \<in> A" and
  A3: "\<forall> x. x \<in> A \<longrightarrow>  (\<exists>!y. y\<in>A \<and> x = B(y))" and
  A4: "\<exists>!x. x\<in>A \<and> \<phi>(x)"
shows "\<exists>!y. y\<in>A \<and> \<psi>(y)"
proof
  from A4 obtain x where I: "x\<in>A" and II: "\<phi>(x)" by auto
  with A3 obtain y where III: "y\<in>A" and "x = B(y)" by auto
  with A1 II show "\<exists>y. y \<in> A \<and> \<psi>(y)" by auto
next fix y\<^sub>1 y\<^sub>2
  assume A5: "y\<^sub>1 \<in> A \<and> \<psi>(y\<^sub>1)"   "y\<^sub>2 \<in> A \<and> \<psi>(y\<^sub>2)"
  with A2 have IV: "B(y\<^sub>1) \<in> A" and "B(y\<^sub>2) \<in> A" by auto
  with A4 A1 A5 have "y\<^sub>1 \<in> A" and "y\<^sub>2 \<in> A" and "B(y\<^sub>1) = B(y\<^sub>2)" by auto
  with A3 IV show "y\<^sub>1 = y\<^sub>2" by blast
qed
 
lemma MMI_reuunixfr: assumes A1: "\<forall> z. z \<in> C \<longrightarrow> (\<forall>y. z \<in> C)" and
    A2: "\<forall> y. y \<in> A \<longrightarrow> B(y) \<in> A" and
    A3: "\<Union> {y \<in> A. \<psi>(y) } \<in> A \<longrightarrow> C \<in> A" and
    A4: "\<forall>x y. x = B(y) \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<psi>(y)" and
    A5: "\<forall> y. y = \<Union> {y \<in> A. \<psi>(y) } \<longrightarrow> B(y) = C" and
    A6: "\<forall> x. x \<in> A \<longrightarrow>  (\<exists>!y. y\<in>A \<and> x = B(y))"   
   shows "(\<exists>!x. x\<in>A \<and> \<phi>(x)) \<longrightarrow>  \<Union> {x \<in> A. \<phi>(x) } = C"
proof
  let ?D = "\<Union> {y \<in> A. \<psi>(y)}"
  assume A7: "\<exists>!x. x\<in>A \<and> \<phi>(x)"
  with A4 A2 A6 have I: "\<exists>!y. y\<in>A \<and> \<psi>(y)" by (rule MMI_reuunixfr_helper)
  with A3 have T: "C \<in> A" using ZF1_1_L9 by simp 
  from A4 A5 have "\<phi>(C) \<longleftrightarrow> \<psi>(?D)" by auto
  moreover from I have "\<psi>(?D)" by (rule ZF1_1_L9)
  ultimately have "\<phi>(C)" by simp
  with T A7 show "\<Union> {x \<in> A. \<phi>(x) } = C" by auto
qed
  
lemma MMI_hbrab1: 
   shows "y \<in> {x \<in> A. \<phi>(x) } \<longrightarrow>  (\<forall>x. y \<in> {x \<in> A. \<phi>(x) })"
  by auto

lemma MMI_reuhyp: assumes A1: "\<forall>x. x \<in> C \<longrightarrow> B(x) \<in> C" and
    A2: "\<forall> x y.  x \<in> C \<and> y \<in> C \<longrightarrow>  x = A(y) \<longleftrightarrow> y = B(x)"   
   shows "\<forall> x. x \<in> C \<longrightarrow> (\<exists>!y. y\<in>C \<and> x = A(y))"
proof -
  { fix x
    assume A3: "x\<in>C"
    with A1 have I: "B(x) \<in> C" by simp
    with A2 A3 have II: "x = A(B(x))" by simp
    have "\<exists>!y. y\<in>C \<and> x = A(y)"
    proof
      from I II show "\<exists>y. y\<in>C \<and> x = A(y)" by auto
    next fix y\<^sub>1 y\<^sub>2 
      assume A4: "y\<^sub>1 \<in> C \<and> x = A(y\<^sub>1)"   "y\<^sub>2 \<in> C \<and> x = A(y\<^sub>2)"
      with A3 have "x \<in> C \<and> y\<^sub>1 \<in> C" and "x \<in> C \<and> y\<^sub>2 \<in> C" by auto
      with A2 have "x = A(y\<^sub>1) \<longleftrightarrow> y\<^sub>1 = B(x)" and "x = A(y\<^sub>2) \<longleftrightarrow> y\<^sub>2 = B(x)"
	by auto
      with A4 show "y\<^sub>1 = y\<^sub>2" by auto
    qed
  } then show ?thesis by simp
qed

lemma (in MMIsar0) MMI_brcnv: assumes A1: "A = A" and
    A2: "B = B"   
   shows "A > B \<longleftrightarrow> B \<ls> A"
   using convcltrr_def cltrr_def by auto

lemma MMI_imbi12i: assumes A1: "\<phi> \<longleftrightarrow> \<psi>" and
    A2: "ch \<longleftrightarrow> \<theta>"   
   shows "(\<phi> \<longrightarrow> ch) \<longleftrightarrow>  (\<psi> \<longrightarrow> \<theta>)"
   using assms by auto

lemma MMI_ralbii: assumes A1: "\<forall> x. \<phi>(x) \<longleftrightarrow> \<psi>(x)"   
   shows "(\<forall>x\<in>A. \<phi>(x)) \<longleftrightarrow> (\<forall>x\<in>A. \<psi>(x))"
   using assms by auto

lemma MMI_rabbidv: assumes A1: "\<forall> x. \<phi> \<longrightarrow> x \<in> A \<longrightarrow>  \<psi>(x) \<longleftrightarrow> ch(x)"   
   shows "\<phi> \<longrightarrow>  {x \<in> A. \<psi>(x) } = {x \<in> A. ch(x) }"
   using assms by auto

lemma MMI_unieqd: assumes A1: "\<phi> \<longrightarrow> A = B"   
   shows "\<phi> \<longrightarrow> \<Union> A = \<Union> B"
   using assms by auto

(************ infmsup, infmrcl **********************)

lemma MMI_rabbii: assumes A1: "\<forall> x. x \<in> A \<longrightarrow>  \<psi>(x) \<longleftrightarrow> ch(x)"   
   shows "{x \<in> A. \<psi>(x) } = {x \<in> A. ch(x) }"
   using assms by auto

lemma MMI_unieqi: assumes A1: "A = B"   
   shows "\<Union> A = \<Union> B"
   using assms by auto

lemma MMI_syl5rbb: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch" and
    A2: "\<theta> \<longleftrightarrow> \<psi>"   
   shows "\<phi> \<longrightarrow> 
   ch \<longleftrightarrow> \<theta>"
   using assms by auto

lemma MMI_reubii: assumes A1: "\<forall>x. \<phi>(x) \<longleftrightarrow> \<psi>(x)"   
   shows "(\<exists>!x. x\<in>A \<and> \<phi>(x)) \<longleftrightarrow> (\<exists>!x. x\<in>A \<and> \<psi>(x))"
   using assms by auto

lemma MMI_3imtr3: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "\<phi> \<longleftrightarrow> ch" and
    A3: "\<psi> \<longleftrightarrow> \<theta>"   
   shows "ch \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_syl6d: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> ch \<longrightarrow> \<theta>" and
    A2: "\<phi> \<longrightarrow> 
   \<theta> \<longrightarrow> \<tau>"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> ch \<longrightarrow> \<tau>"
   using assms by auto

lemma MMI_n0i: 
   shows "B \<in> A \<longrightarrow> \<not>(A = 0)"
  by auto

end