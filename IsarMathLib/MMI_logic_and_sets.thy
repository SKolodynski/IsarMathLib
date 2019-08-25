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

section \<open>Logic and sets in Metamatah\<close>

theory MMI_logic_and_sets imports MMI_prelude

begin

subsection\<open>Basic Metamath theorems\<close>

text\<open>This section contains Metamath theorems that the more advanced 
  theorems from \<open>MMIsar.thy\<close> depend on. Most of these theorems 
  are proven automatically by Isabelle, some have to be proven by hand 
  and some have to be modified to convert from Tarski-Megill 
  metalogic used by Metamath to one based on explicit notion of 
  free and bound variables.\<close>   

(*text{*The next definition is what Metamath $X\in V$ is
  translated to. I am not sure why it works, probably because
  Isabelle does a type inference and the "=" sign
  indicates that both sides are sets.*}

consts
   IsASet :: "i\<Rightarrow>o" ("_ isASet" [90] 90)

defs
  set_def [simp]: "X isASet \<equiv>  X = X"*)

lemma MMI_ax_mp: assumes "\<phi>" and "\<phi> \<longrightarrow> \<psi>" shows "\<psi>"
  using assms by auto

lemma MMI_sseli: assumes A1: "A \<subseteq> B"   
   shows "C \<in> A \<longrightarrow> C \<in> B"
   using assms by auto

lemma MMI_sselii: assumes A1: "A \<subseteq> B" and
    A2: "C \<in> A"   
   shows "C \<in> B"
   using assms by auto

lemma MMI_syl: assumes A1: "\<phi> \<longrightarrow> ps" and
    A2: "ps \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_elimhyp: assumes A1: "A = if ( \<phi> , A , B ) \<longrightarrow> ( \<phi> \<longleftrightarrow> \<psi> )" and
    A2: "B = if ( \<phi> , A , B ) \<longrightarrow> ( ch \<longleftrightarrow> \<psi> )" and
    A3: "ch"   
   shows "\<psi>"
proof -
  { assume "\<phi>"
    with A1 have "\<psi>" by simp }
  moreover
  { assume "\<not>\<phi>"
    with A2 A3 have "\<psi>" by simp }
  ultimately show "\<psi>" by auto
qed

lemma MMI_neeq1: 
   shows "A = B \<longrightarrow> ( A \<noteq> C \<longleftrightarrow> B \<noteq> C )"
  by auto

lemma MMI_mp2: assumes A1: "\<phi>" and
    A2: "\<psi>" and
    A3: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> chi )"   
   shows "chi"
   using assms by auto

lemma MMI_xpex: assumes A1: "A isASet" and
    A2: "B isASet"   
   shows "( A \<times> B ) isASet"
   using assms by auto

lemma MMI_fex: 
   shows 
  "A \<in> C \<longrightarrow> ( F : A \<rightarrow> B \<longrightarrow> F isASet )"
  "A isASet \<longrightarrow> ( F : A \<rightarrow> B \<longrightarrow> F isASet )"
  by auto

lemma MMI_3eqtr4d: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<phi> \<longrightarrow> C = A" and
    A3: "\<phi> \<longrightarrow> D = B"   
   shows "\<phi> \<longrightarrow> C = D"
   using assms by auto

lemma MMI_3coml: assumes A1: "( \<phi> \<and> \<psi> \<and> chi ) \<longrightarrow> th"   
   shows "( \<psi> \<and> chi \<and> \<phi> ) \<longrightarrow> th"
   using assms by auto

lemma MMI_sylan: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> chi" and
    A2: "th \<longrightarrow> \<phi>"   
   shows "( th \<and> \<psi> ) \<longrightarrow> chi"
   using assms by auto

lemma MMI_3impa: assumes A1: "( ( \<phi> \<and> \<psi> ) \<and> chi ) \<longrightarrow> th"   
   shows "( \<phi> \<and> \<psi> \<and> chi ) \<longrightarrow> th"
   using assms by auto

lemma MMI_3adant2: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> chi"   
   shows "( \<phi> \<and> th \<and> \<psi> ) \<longrightarrow> chi"
   using assms by auto

lemma MMI_3adant1: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> chi"   
   shows "( th \<and> \<phi> \<and> \<psi> ) \<longrightarrow> chi"
   using assms by auto

lemma (in MMIsar0) MMI_opreq12d: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<phi> \<longrightarrow> C = D"   
   shows 
  "\<phi> \<longrightarrow> ( A \<ca> C ) = ( B \<ca> D )"
  "\<phi> \<longrightarrow> ( A \<cdot> C ) = ( B \<cdot> D )"
  "\<phi> \<longrightarrow> ( A \<cs> C ) = ( B \<cs> D )"
  "\<phi> \<longrightarrow> ( A \<cdiv> C ) = ( B \<cdiv> D )"
   using assms by auto

lemma MMI_mp2an: assumes A1: "\<phi>" and
    A2: "\<psi>" and
    A3: "( \<phi> \<and> \<psi> ) \<longrightarrow> chi"   
   shows "chi"
   using assms by auto

lemma MMI_mp3an: assumes A1: "\<phi>" and
    A2: "\<psi>" and
    A3: "ch" and
    A4: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"   
   shows "\<theta>"
   using assms by auto

lemma MMI_eqeltrr: assumes A1: "A = B" and
    A2: "A \<in> C"   
   shows "B \<in> C"
   using assms by auto

lemma MMI_eqtr: assumes A1: "A = B" and
    A2: "B = C"   
   shows "A = C"
   using assms by auto

(*********************10-20 ******************************************)

lemma MMI_impbi: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "\<psi> \<longrightarrow> \<phi>"   
   shows "\<phi> \<longleftrightarrow> \<psi>"
proof
  assume "\<phi>" with A1 show "\<psi>" by simp
next
  assume "\<psi>" with A2 show "\<phi>" by simp
qed

lemma MMI_mp3an3: assumes A1: "ch" and
    A2: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"   
   shows "( \<phi> \<and> \<psi> ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_eqeq12d: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<phi> \<longrightarrow> C = D"   
   shows "\<phi> \<longrightarrow> ( A = C \<longleftrightarrow> B = D )"
   using assms by auto

lemma MMI_mpan2: assumes A1: "\<psi>" and
    A2: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ch"
   using assms by auto

lemma (in MMIsar0) MMI_opreq2: 
   shows 
  "A = B \<longrightarrow> ( C \<ca> A ) = ( C \<ca> B )"
  "A = B \<longrightarrow> ( C \<cdot> A ) = ( C \<cdot> B )"
  "A = B \<longrightarrow> ( C \<cs> A ) = ( C \<cs> B )"
  "A = B \<longrightarrow> ( C \<cdiv> A ) = ( C \<cdiv> B )"
  by auto

lemma MMI_syl5bir: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<theta> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ( \<theta> \<longrightarrow> \<psi> )"
   using assms by auto

lemma MMI_adantr: assumes A1: "\<phi> \<longrightarrow> \<psi>"   
   shows "( \<phi> \<and> ch ) \<longrightarrow> \<psi>"
   using assms by auto

lemma MMI_mpan: assumes A1: "\<phi>" and
    A2: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch"   
   shows "\<psi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_eqeq1d: assumes A1: "\<phi> \<longrightarrow> A = B"   
   shows "\<phi> \<longrightarrow> ( A = C \<longleftrightarrow> B = C )"
   using assms by auto

lemma (in MMIsar0) MMI_opreq1: 
   shows 
  "A = B \<longrightarrow> ( A \<cdot> C ) = ( B \<cdot> C )"
  "A = B \<longrightarrow> ( A \<ca> C ) = ( B \<ca> C )"
  "A = B \<longrightarrow> ( A \<cs> C ) = ( B \<cs> C )"
  "A = B \<longrightarrow> ( A \<cdiv> C ) = ( B \<cdiv> C )"
  by auto

lemma MMI_syl6eq: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "B = C"   
   shows "\<phi> \<longrightarrow> A = C"
   using assms by auto

lemma MMI_syl6bi: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> \<theta> )"
   using assms by auto

lemma MMI_imp: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )"   
   shows "( \<phi> \<and> \<psi> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_sylibd: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( ch \<longleftrightarrow> \<theta> )"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> \<theta> )"
   using assms by auto

lemma MMI_ex: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )"
   using assms by auto

lemma MMI_r19_23aiv: assumes A1: "\<forall>x.  (x \<in> A  \<longrightarrow> (\<phi>(x) \<longrightarrow> \<psi> ))"   
   shows "( \<exists> x \<in> A . \<phi>(x) ) \<longrightarrow> \<psi>"
  using assms by auto

lemma MMI_bitr: assumes A1: "\<phi> \<longleftrightarrow> \<psi>" and
    A2: "\<psi> \<longleftrightarrow> ch"   
   shows "\<phi> \<longleftrightarrow> ch"
   using assms by auto

lemma MMI_eqeq12i: assumes A1: "A = B" and
    A2: "C = D"   
   shows "A = C \<longleftrightarrow> B = D"
   using assms by auto

lemma MMI_dedth3h: 
  assumes A1: "A = if ( \<phi> , A , D ) \<longrightarrow> ( \<theta> \<longleftrightarrow> ta )" and
    A2: "B = if ( \<psi> , B , R ) \<longrightarrow> ( ta \<longleftrightarrow> et )" and
    A3: "C = if ( ch , C , S ) \<longrightarrow> ( et \<longleftrightarrow> ze )" and
    A4: "ze"   
   shows "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_bibi1d: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( ( \<psi> \<longleftrightarrow> \<theta> ) \<longleftrightarrow> ( ch \<longleftrightarrow> \<theta> ) )"
   using assms by auto

lemma MMI_eqeq1: 
   shows "A = B \<longrightarrow> ( A = C \<longleftrightarrow> B = C )"
  by auto

lemma MMI_bibi12d: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( \<theta> \<longleftrightarrow> ta )"   
   shows "\<phi> \<longrightarrow> ( ( \<psi> \<longleftrightarrow> \<theta> ) \<longleftrightarrow> ( ch \<longleftrightarrow> ta ) )"
   using assms by auto

lemma MMI_eqeq2d: assumes A1: "\<phi> \<longrightarrow> A = B"   
   shows "\<phi> \<longrightarrow> ( C = A \<longleftrightarrow> C = B )"
   using assms by auto

lemma MMI_eqeq2: 
   shows "A = B \<longrightarrow> ( C = A \<longleftrightarrow> C = B )"
  by auto

lemma MMI_elimel: assumes A1: "B \<in> C"   
   shows "if ( A \<in> C , A , B ) \<in> C"
   using assms by auto

lemma MMI_3adant3: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch"   
   shows "( \<phi> \<and> \<psi> \<and> \<theta> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_bitr3d: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> \<theta> )"   
   shows "\<phi> \<longrightarrow> ( ch \<longleftrightarrow> \<theta> )"
   using assms by auto

(****************** 20-30 add12t - peano2cn *************)

lemma MMI_3eqtr3d: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<phi> \<longrightarrow> A = C" and
    A3: "\<phi> \<longrightarrow> B = D"   
   shows "\<phi> \<longrightarrow> C = D"
   using assms by auto

lemma (in MMIsar0) MMI_opreq1d: assumes A1: "\<phi> \<longrightarrow> A = B"   
   shows 
  "\<phi> \<longrightarrow> ( A \<ca> C ) = ( B \<ca> C )"
  "\<phi> \<longrightarrow> ( A \<cs> C ) = ( B \<cs> C )"
  "\<phi> \<longrightarrow> ( A \<cdot> C ) = ( B \<cdot> C )"
  "\<phi> \<longrightarrow> ( A \<cdiv> C ) = ( B \<cdiv> C )"
   using assms by auto

lemma MMI_3com12: assumes A1: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"   
   shows "( \<psi> \<and> \<phi> \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

lemma (in MMIsar0) MMI_opreq2d: assumes A1: "\<phi> \<longrightarrow> A = B"   
   shows 
  "\<phi> \<longrightarrow> ( C \<ca> A ) = ( C \<ca> B )"
  "\<phi> \<longrightarrow> ( C \<cs> A ) = ( C \<cs> B )"
  "\<phi> \<longrightarrow> ( C \<cdot> A ) = ( C \<cdot> B )"
  "\<phi> \<longrightarrow> ( C \<cdiv> A ) = ( C \<cdiv> B )"
   using assms by auto

lemma MMI_3com23: assumes A1: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"   
   shows "( \<phi> \<and> ch \<and> \<psi> ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_3expa: assumes A1: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"   
   shows "( ( \<phi> \<and> \<psi> ) \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_adantrr: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch"   
   shows "( \<phi> \<and> ( \<psi> \<and> \<theta> ) ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_3expb: assumes A1: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"   
   shows "( \<phi> \<and> ( \<psi> \<and> ch ) ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_an4s: assumes A1: "( ( \<phi> \<and> \<psi> ) \<and> ( ch \<and> \<theta> ) ) \<longrightarrow> \<tau>"   
   shows "( ( \<phi> \<and> ch ) \<and> ( \<psi> \<and> \<theta> ) ) \<longrightarrow> \<tau>"
   using assms by auto

lemma MMI_eqtrd: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<phi> \<longrightarrow> B = C"   
   shows "\<phi> \<longrightarrow> A = C"
   using assms by auto

lemma MMI_ad2ant2l: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch"   
   shows "( ( \<theta> \<and> \<phi> ) \<and> ( \<tau> \<and> \<psi> ) ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_pm3_2i: assumes A1: "\<phi>" and
    A2: "\<psi>"   
   shows "\<phi> \<and> \<psi>"
   using assms by auto

lemma (in MMIsar0) MMI_opreq2i: assumes A1: "A = B"   
   shows 
  "( C \<ca> A ) = ( C \<ca> B )"
  "( C \<cs> A ) = ( C \<cs> B )"
  "( C \<cdot> A ) = ( C \<cdot> B )"
   using assms by auto

(************31,33 peano2re, negeu, subval ******************************)

lemma MMI_mpbir2an: assumes A1: "\<phi> \<longleftrightarrow> ( \<psi> \<and> ch )" and
    A2: "\<psi>" and
    A3: "ch"   
   shows "\<phi>"
   using assms by auto

lemma MMI_reu4: assumes A1: "\<forall>x y. x = y \<longrightarrow> ( \<phi>(x) \<longleftrightarrow> \<psi>(y) )"   
   shows "( \<exists>! x . x \<in> A \<and> \<phi>(x) ) \<longleftrightarrow> 
  ( ( \<exists> x \<in> A . \<phi>(x) ) \<and> ( \<forall> x \<in> A . \<forall> y \<in> A . 
  ( ( \<phi>(x) \<and> \<psi>(y) ) \<longrightarrow> x = y ) ) )"
   using assms by auto

lemma MMI_risset: 
   shows "A \<in> B \<longleftrightarrow> ( \<exists> x \<in> B . x = A )"
  by auto

lemma MMI_sylib: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "\<psi> \<longleftrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_mp3an13: assumes A1: "\<phi>" and
    A2: "ch" and
    A3: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"   
   shows "\<psi> \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_eqcomd: assumes A1: "\<phi> \<longrightarrow> A = B"   
   shows "\<phi> \<longrightarrow> B = A"
   using assms by auto

lemma MMI_sylan9eqr: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<psi> \<longrightarrow> B = C"   
   shows "( \<psi> \<and> \<phi> ) \<longrightarrow> A = C"
   using assms by auto

lemma MMI_exp32: assumes A1: "( \<phi> \<and> ( \<psi> \<and> ch ) ) \<longrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ( ch \<longrightarrow> \<theta> ) )"
   using assms by auto

lemma MMI_impcom: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )"   
   shows "( \<psi> \<and> \<phi> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_a1d: assumes A1: "\<phi> \<longrightarrow> \<psi>"   
   shows "\<phi> \<longrightarrow> ( ch \<longrightarrow> \<psi> )"
   using assms by auto

lemma MMI_r19_21aiv: assumes A1: "\<forall>x. \<phi> \<longrightarrow> ( x \<in> A \<longrightarrow> \<psi>(x) )"   
   shows "\<phi> \<longrightarrow> ( \<forall> x \<in> A . \<psi>(x) )"
   using assms by auto

lemma MMI_r19_22: 
   shows "( \<forall> x \<in> A . ( \<phi>(x) \<longrightarrow> \<psi>(x) ) ) \<longrightarrow> 
  ( ( \<exists> x \<in> A . \<phi>(x) ) \<longrightarrow> ( \<exists> x \<in> A . \<psi>(x) ) )"
  by auto

lemma MMI_syl6: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )" and
    A2: "ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> \<theta> )"
   using assms by auto

lemma MMI_mpid: assumes A1: "\<phi> \<longrightarrow> ch" and
    A2: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ( ch \<longrightarrow> \<theta> ) )"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> \<theta> )"
   using assms by auto

lemma MMI_eqtr3t: 
   shows "( A = C \<and> B = C ) \<longrightarrow> A = B"
  by auto

lemma MMI_syl5bi: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<theta> \<longrightarrow> \<psi>"   
   shows "\<phi> \<longrightarrow> ( \<theta> \<longrightarrow> ch )"
   using assms by auto

lemma MMI_mp3an1: assumes A1: "\<phi>" and
    A2: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"   
   shows "( \<psi> \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_rgen2: assumes A1: "\<forall>x y. ( x \<in> A \<and> y \<in> A ) \<longrightarrow> \<phi>(x,y)"   
   shows "\<forall> x \<in> A . \<forall> y \<in> A . \<phi>(x,y)"
   using assms by auto

(*************** 35-37 negeq-negeqd **************************)

lemma MMI_ax_17: shows "\<phi> \<longrightarrow> (\<forall>x. \<phi>)" by simp


lemma MMI_3eqtr4g: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "C = A" and
    A3: "D = B"   
   shows "\<phi> \<longrightarrow> C = D"
   using assms by auto

(*** hbneq ***************************************************)

lemma MMI_3imtr4: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "ch \<longleftrightarrow> \<phi>" and
    A3: "\<theta> \<longleftrightarrow> \<psi>"   
   shows "ch \<longrightarrow> \<theta>"
   using assms by auto

(*lemma MMI_hbopr: assumes A1: "y \<in> A \<longrightarrow> ( \<forall> x . y \<in> A )" and
    A2: "y \<in> F \<longrightarrow> ( \<forall> x . y \<in> F )" and
    A3: "y \<in> B \<longrightarrow> ( \<forall> x . y \<in> B )"   
   shows "y \<in> ( A F B ) \<longrightarrow> ( \<forall> x . y \<in> ( A F B ) )"
   using assms by auto 
  no way to translate hopefuly we will manage to avoid using this*)

lemma MMI_eleq2i: assumes A1: "A = B"   
   shows "C \<in> A \<longleftrightarrow> C \<in> B"
   using assms by auto

lemma MMI_albii: assumes A1: "\<phi> \<longleftrightarrow> \<psi>"   
   shows "( \<forall> x . \<phi> ) \<longleftrightarrow> ( \<forall> x . \<psi> )"
   using assms by auto

(*************subcl-subadd **********************************)
lemma MMI_reucl: 
   shows "( \<exists>! x . x \<in> A \<and> \<phi>(x) ) \<longrightarrow> \<Union> { x \<in> A . \<phi>(x) } \<in> A"
proof
  assume A1: "\<exists>! x . x \<in> A \<and> \<phi>(x)"
  then obtain a where I: "a\<in>A"  and "\<phi>(a)" by auto
  with A1 have "{ x \<in> A . \<phi>(x) } = {a}" by blast
  with I show " \<Union> { x \<in> A . \<phi>(x) } \<in> A" by simp
qed

lemma MMI_dedth2h: assumes A1: "A = if ( \<phi> , A , C ) \<longrightarrow> ( ch \<longleftrightarrow> \<theta> )" and
    A2: "B = if ( \<psi> , B , D ) \<longrightarrow> ( \<theta> \<longleftrightarrow> \<tau> )" and
    A3: "\<tau>"   
   shows "( \<phi> \<and> \<psi> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_eleq1d: assumes A1: "\<phi> \<longrightarrow> A = B"   
   shows "\<phi> \<longrightarrow> ( A \<in> C \<longleftrightarrow> B \<in> C )"
   using assms by auto

lemma MMI_syl5eqel: assumes A1: "\<phi> \<longrightarrow> A \<in> B" and
    A2: "C = A"   
   shows "\<phi> \<longrightarrow> C \<in> B"
   using assms by auto

(** a lemma in ZF that roughly corresponds to Mematamath euuni **)

lemma IML_eeuni: assumes A1: "x \<in> A" and A2: "\<exists>! t . t \<in> A \<and> \<phi>(t)"
  shows "\<phi>(x) \<longleftrightarrow> \<Union> { x \<in> A . \<phi>(x) } = x"
proof
  assume "\<phi>(x)" 
  with A1 A2 show "\<Union> { x \<in> A . \<phi>(x) } = x" by auto
next assume A3: "\<Union> { x \<in> A . \<phi>(x) } = x"
  from A2 obtain y where "y\<in>A" and I: "\<phi>(y)" by auto
  with A2 A3 have "x = y" by auto
  with I show "\<phi>(x)" by simp
qed
    
lemma MMI_reuuni1: 
   shows "( x \<in> A \<and> ( \<exists>! x . x \<in> A \<and> \<phi>(x) ) ) \<longrightarrow> 
  ( \<phi>(x) \<longleftrightarrow> \<Union> { x \<in> A . \<phi>(x) } = x )"
  using IML_eeuni by simp

lemma MMI_eqeq1i: assumes A1: "A = B"   
   shows "A = C \<longleftrightarrow> B = C"
   using assms by auto

lemma MMI_syl6rbbr: assumes A1: "\<forall>x. \<phi>(x) \<longrightarrow> ( \<psi>(x) \<longleftrightarrow> ch(x) )" and
    A2: "\<forall>x. \<theta>(x) \<longleftrightarrow> ch(x)"   
   shows "\<forall> x. \<phi>(x) \<longrightarrow> ( \<theta>(x) \<longleftrightarrow> \<psi>(x) )"
   using assms by auto

(*** the original version of MMI_syl6rbbr without quantifiers **********)

lemma MMI_syl6rbbrA: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<theta> \<longleftrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ( \<theta> \<longleftrightarrow> \<psi> )"
   using assms by auto

lemma MMI_vtoclga: assumes A1: "\<forall>x. x = A \<longrightarrow> ( \<phi>(x) \<longleftrightarrow> \<psi>)" and
    A2: "\<forall>x. x \<in> B \<longrightarrow> \<phi>(x)"
   shows "A \<in> B \<longrightarrow> \<psi>"
   using assms by auto

(************  subsub23 - addsubt ******************)

lemma MMI_3bitr4: assumes A1: "\<phi> \<longleftrightarrow> \<psi>" and
    A2: "ch \<longleftrightarrow> \<phi>" and
    A3: "\<theta> \<longleftrightarrow> \<psi>"   
   shows "ch \<longleftrightarrow> \<theta>"
   using assms by auto

lemma MMI_mpbii: assumes Amin: "\<psi>" and
    Amaj: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_eqid: 
   shows "A = A"
  by auto

lemma MMI_pm3_27: 
   shows "( \<phi> \<and> \<psi> ) \<longrightarrow> \<psi>"
  by auto

lemma MMI_pm3_26: 
   shows "( \<phi> \<and> \<psi> ) \<longrightarrow> \<phi>"
  by auto

lemma MMI_ancoms: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch"   
   shows "( \<psi> \<and> \<phi> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_syl3anc: assumes A1: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>" and
    A2: "\<tau> \<longrightarrow> \<phi>" and
    A3: "\<tau> \<longrightarrow> \<psi>" and
    A4: "\<tau> \<longrightarrow> ch"   
   shows "\<tau> \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_syl5eq: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "C = A"   
   shows "\<phi> \<longrightarrow> C = B"
   using assms by auto

lemma MMI_eqcomi: assumes A1: "A = B"   
   shows "B = A"
   using assms by auto

lemma MMI_3eqtr: assumes A1: "A = B" and
    A2: "B = C" and
    A3: "C = D"   
   shows "A = D"
   using assms by auto

lemma MMI_mpbir: assumes Amin: "\<psi>" and
    Amaj: "\<phi> \<longleftrightarrow> \<psi>"   
   shows "\<phi>"
   using assms by auto

lemma MMI_syl3an3: assumes A1: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>" and
    A2: "\<tau> \<longrightarrow> ch"   
   shows "( \<phi> \<and> \<psi> \<and> \<tau> ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_3eqtrd: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<phi> \<longrightarrow> B = C" and
    A3: "\<phi> \<longrightarrow> C = D"   
   shows "\<phi> \<longrightarrow> A = D"
   using assms by auto

lemma MMI_syl5: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )" and
    A2: "\<theta> \<longrightarrow> \<psi>"   
   shows "\<phi> \<longrightarrow> ( \<theta> \<longrightarrow> ch )"
   using assms by auto

lemma MMI_exp3a: assumes A1: "\<phi> \<longrightarrow> ( ( \<psi> \<and> ch ) \<longrightarrow> \<theta> )"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ( ch \<longrightarrow> \<theta> ) )"
   using assms by auto

lemma MMI_com12: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )"   
   shows "\<psi> \<longrightarrow> ( \<phi> \<longrightarrow> ch )"
   using assms by auto

lemma MMI_3imp: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ( ch \<longrightarrow> \<theta> ) )"   
   shows "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

(********* addsub12t-subidt *************)

lemma MMI_3eqtr3: assumes A1: "A = B" and
    A2: "A = C" and
    A3: "B = D"   
   shows "C = D"
   using assms by auto

lemma (in MMIsar0) MMI_opreq1i: assumes A1: "A = B"   
   shows 
  "( A \<ca> C ) = ( B \<ca> C )"
  "( A \<cs> C ) = ( B \<cs> C )"
  "( A \<cdiv> C ) = ( B \<cdiv> C )"
  "( A \<cdot> C ) = ( B \<cdot> C )"
   using assms by auto

lemma MMI_eqtr3: assumes A1: "A = B" and
    A2: "A = C"   
   shows "B = C"
   using assms by auto

lemma MMI_dedth: assumes A1: "A = if ( \<phi> , A , B ) \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "ch"   
   shows "\<phi> \<longrightarrow> \<psi>"
   using assms by auto

lemma MMI_id: 
   shows "\<phi> \<longrightarrow> \<phi>"
  by auto

lemma MMI_eqtr3d: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<phi> \<longrightarrow> A = C"   
   shows "\<phi> \<longrightarrow> B = C"
   using assms by auto

lemma MMI_sylan2: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch" and
    A2: "\<theta> \<longrightarrow> \<psi>"   
   shows "( \<phi> \<and> \<theta> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_adantl: assumes A1: "\<phi> \<longrightarrow> \<psi>"   
   shows "( ch \<and> \<phi> ) \<longrightarrow> \<psi>"
   using assms by auto

lemma (in MMIsar0) MMI_opreq12: 
   shows 
  "( A = B \<and> C = D ) \<longrightarrow> ( A \<ca> C ) = ( B \<ca> D )"
  "( A = B \<and> C = D ) \<longrightarrow> ( A \<cs> C ) = ( B \<cs> D )"
  "( A = B \<and> C = D ) \<longrightarrow> ( A \<cdot> C ) = ( B \<cdot> D )"
  "( A = B \<and> C = D ) \<longrightarrow> ( A \<cdiv> C ) = ( B \<cdiv> D )"
  by auto

lemma MMI_anidms: assumes A1: "( \<phi> \<and> \<phi> ) \<longrightarrow> \<psi>"   
   shows "\<phi> \<longrightarrow> \<psi>"
   using assms by auto

(******** subid1t-neg11 *************************)

lemma MMI_anabsan2: assumes A1: "( \<phi> \<and> ( \<psi> \<and> \<psi> ) ) \<longrightarrow> ch"   
   shows "( \<phi> \<and> \<psi> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_3simp2: 
   shows "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<psi>"
  by auto

lemma MMI_3simp3: 
   shows "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> ch"
  by auto

lemma MMI_sylbir: assumes A1: "\<psi> \<longleftrightarrow> \<phi>" and
    A2: "\<psi> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_3eqtr3g: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "A = C" and
    A3: "B = D"   
   shows "\<phi> \<longrightarrow> C = D"
   using assms by auto

lemma MMI_3bitr: assumes A1: "\<phi> \<longleftrightarrow> \<psi>" and
    A2: "\<psi> \<longleftrightarrow> ch" and
    A3: "ch \<longleftrightarrow> \<theta>"   
   shows "\<phi> \<longleftrightarrow> \<theta>"
   using assms by auto

(************ negcon1-subeq0t**************)

lemma MMI_3bitr3: assumes A1: "\<phi> \<longleftrightarrow> \<psi>" and
    A2: "\<phi> \<longleftrightarrow> ch" and
    A3: "\<psi> \<longleftrightarrow> \<theta>"   
   shows "ch \<longleftrightarrow> \<theta>"
   using assms by auto

lemma MMI_eqcom: 
   shows "A = B \<longleftrightarrow> B = A"
  by auto

lemma MMI_syl6bb: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "ch \<longleftrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> \<theta> )"
   using assms by auto

lemma MMI_3bitr3d: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> \<theta> )" and
    A3: "\<phi> \<longrightarrow> ( ch \<longleftrightarrow> \<tau> )"   
   shows "\<phi> \<longrightarrow> ( \<theta> \<longleftrightarrow> \<tau> )"
   using assms by auto

lemma MMI_syl3an2: assumes A1: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>" and
    A2: "\<tau> \<longrightarrow> \<psi>"   
   shows "( \<phi> \<and> \<tau> \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

(********neg0-0re ********************)

lemma MMI_df_rex: 
   shows "( \<exists> x \<in> A . \<phi>(x) ) \<longleftrightarrow> ( \<exists> x . ( x \<in> A \<and> \<phi>(x) ) )"
  by auto

lemma MMI_mpbi: assumes Amin: "\<phi>" and
    Amaj: "\<phi> \<longleftrightarrow> \<psi>"   
   shows "\<psi>"
   using assms by auto

lemma MMI_mp3an12: assumes A1: "\<phi>" and
    A2: "\<psi>" and
    A3: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"   
   shows "ch \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_syl5bb: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<theta> \<longleftrightarrow> \<psi>"   
   shows "\<phi> \<longrightarrow> ( \<theta> \<longleftrightarrow> ch )"
   using assms by auto

lemma MMI_eleq1a: 
   shows "A \<in> B \<longrightarrow> ( C = A \<longrightarrow> C \<in> B )"
  by auto

lemma MMI_sylbird: assumes A1: "\<phi> \<longrightarrow> ( ch \<longleftrightarrow> \<psi> )" and
    A2: "\<phi> \<longrightarrow> ( ch \<longrightarrow> \<theta> )"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> \<theta> )"
   using assms by auto

lemma MMI_19_23aiv: assumes A1: "\<forall>x. \<phi>(x) \<longrightarrow> \<psi>"   
   shows "( \<exists> x . \<phi>(x) ) \<longrightarrow> \<psi>"
   using assms by auto

lemma MMI_eqeltrrd: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<phi> \<longrightarrow> A \<in> C"   
   shows "\<phi> \<longrightarrow> B \<in> C"
   using assms by auto

lemma MMI_syl2an: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch" and
    A2: "\<theta> \<longrightarrow> \<phi>" and
    A3: "\<tau> \<longrightarrow> \<psi>"   
   shows "( \<theta> \<and> \<tau> ) \<longrightarrow> ch"
   using assms by auto

(*********** mulid2t-muladdt *********************)

lemma MMI_adantrl: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch"   
   shows "( \<phi> \<and> ( \<theta> \<and> \<psi> ) ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_ad2ant2r: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch"   
   shows "( ( \<phi> \<and> \<theta> ) \<and> ( \<psi> \<and> \<tau> ) ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_adantll: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch"   
   shows "( ( \<theta> \<and> \<phi> ) \<and> \<psi> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_anandirs: assumes A1: "( ( \<phi> \<and> ch ) \<and> ( \<psi> \<and> ch ) ) \<longrightarrow> \<tau>"   
   shows "( ( \<phi> \<and> \<psi> ) \<and> ch ) \<longrightarrow> \<tau>"
   using assms by auto

lemma MMI_adantlr: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch"   
   shows "( ( \<phi> \<and> \<theta> ) \<and> \<psi> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_an42s: assumes A1: "( ( \<phi> \<and> \<psi> ) \<and> ( ch \<and> \<theta> ) ) \<longrightarrow> \<tau>"   
   shows "( ( \<phi> \<and> ch ) \<and> ( \<theta> \<and> \<psi> ) ) \<longrightarrow> \<tau>"
   using assms by auto

(******* muladd11t-muladd*****************************)

lemma MMI_mp3an2: assumes A1: "\<psi>" and
    A2: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"   
   shows "( \<phi> \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

(********** subdit-mulneg1 **************************)

lemma MMI_3simp1: 
   shows "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<phi>"
  by auto

lemma MMI_3impb: assumes A1: "( \<phi> \<and> ( \<psi> \<and> ch ) ) \<longrightarrow> \<theta>"   
   shows "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_mpbird: assumes Amin: "\<phi> \<longrightarrow> ch" and
    Amaj: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> \<psi>"
   using assms by auto

lemma (in MMIsar0) MMI_opreq12i: assumes A1: "A = B" and
  A2: "C = D"   
  shows 
  "( A \<ca> C ) = ( B \<ca> D )"
  "( A \<cdot> C ) = ( B \<cdot> D )"
  "( A \<cs> C ) = ( B \<cs> D )"
  using assms by auto

lemma MMI_3eqtr4: assumes A1: "A = B" and
  A2: "C = A" and
  A3: "D = B"   
  shows "C = D"
  using assms by auto

(*********mulneg2-negdit****************)

lemma MMI_eqtr4d: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<phi> \<longrightarrow> C = B"   
   shows "\<phi> \<longrightarrow> A = C"
   using assms by auto

(**** negdi2t - nnncan1t ***************)

lemma MMI_3eqtr3rd: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<phi> \<longrightarrow> A = C" and
    A3: "\<phi> \<longrightarrow> B = D"   
   shows "\<phi> \<longrightarrow> D = C"
   using assms by auto

lemma MMI_sylanc: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch" and
    A2: "\<theta> \<longrightarrow> \<phi>" and
    A3: "\<theta> \<longrightarrow> \<psi>"   
   shows "\<theta> \<longrightarrow> ch"
   using assms by auto

(*** nnncan2t-pnpcan2t *******************)

lemma MMI_anim12i: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "ch \<longrightarrow> \<theta>"   
   shows "( \<phi> \<and> ch ) \<longrightarrow> ( \<psi> \<and> \<theta> )"
   using assms by auto

lemma (in MMIsar0) MMI_opreqan12d: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<psi> \<longrightarrow> C = D"   
   shows 
  "( \<phi> \<and> \<psi> ) \<longrightarrow> ( A \<ca> C ) = ( B \<ca> D )"
  "( \<phi> \<and> \<psi> ) \<longrightarrow> ( A \<cs> C ) = ( B \<cs> D )"
  "( \<phi> \<and> \<psi> ) \<longrightarrow> ( A \<cdot> C ) = ( B \<cdot> D )"
   using assms by auto

lemma MMI_sylanr2: assumes A1: "( \<phi> \<and> ( \<psi> \<and> ch ) ) \<longrightarrow> \<theta>" and
    A2: "\<tau> \<longrightarrow> ch"   
   shows "( \<phi> \<and> ( \<psi> \<and> \<tau> ) ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_sylanl2: assumes A1: "( ( \<phi> \<and> \<psi> ) \<and> ch ) \<longrightarrow> \<theta>" and
    A2: "\<tau> \<longrightarrow> \<psi>"   
   shows "( ( \<phi> \<and> \<tau> ) \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_ancom2s: assumes A1: "( \<phi> \<and> ( \<psi> \<and> ch ) ) \<longrightarrow> \<theta>"   
   shows "( \<phi> \<and> ( ch \<and> \<psi> ) ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_anandis: assumes A1: "( ( \<phi> \<and> \<psi> ) \<and> ( \<phi> \<and> ch ) ) \<longrightarrow> \<tau>"   
   shows "( \<phi> \<and> ( \<psi> \<and> ch ) ) \<longrightarrow> \<tau>"
   using assms by auto

lemma MMI_sylan9eq: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<psi> \<longrightarrow> B = C"   
   shows "( \<phi> \<and> \<psi> ) \<longrightarrow> A = C"
   using assms by auto

(******pnncant-mul0ort**********************)

lemma MMI_keephyp: assumes A1: "A = if ( \<phi> , A , B ) \<longrightarrow> ( \<psi> \<longleftrightarrow> \<theta> )" and
    A2: "B = if ( \<phi> , A , B ) \<longrightarrow> ( ch \<longleftrightarrow> \<theta> )" and
    A3: "\<psi>" and
    A4: "ch"   
   shows "\<theta>"
proof -
  { assume "\<phi>"
    with A1 A3 have "\<theta>" by simp }
  moreover
  { assume "\<not>\<phi>"
    with A2 A4 have "\<theta>" by simp }
  ultimately show "\<theta>" by auto
qed

lemma MMI_eleq1: 
   shows "A = B \<longrightarrow> ( A \<in> C \<longleftrightarrow> B \<in> C )"
  by auto

lemma MMI_pm4_2i: 
   shows "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> \<psi> )"
  by auto

lemma MMI_3anbi123d: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( \<theta> \<longleftrightarrow> \<tau> )" and
    A3: "\<phi> \<longrightarrow> ( \<eta> \<longleftrightarrow> \<zeta> )"   
   shows "\<phi> \<longrightarrow> ( ( \<psi> \<and> \<theta> \<and> \<eta> ) \<longleftrightarrow> ( ch \<and> \<tau> \<and> \<zeta> ) )"
   using assms by auto

lemma MMI_imbi12d: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( \<theta> \<longleftrightarrow> \<tau> )"   
   shows "\<phi> \<longrightarrow> ( ( \<psi> \<longrightarrow> \<theta> ) \<longleftrightarrow> ( ch \<longrightarrow> \<tau> ) )"
   using assms by auto

lemma MMI_bitrd: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( ch \<longleftrightarrow> \<theta> )"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> \<theta> )"
   using assms by auto

lemma MMI_df_ne: 
   shows "( A \<noteq> B \<longleftrightarrow> \<not> ( A = B ) )"
  by auto

lemma MMI_3pm3_2i: assumes A1: "\<phi>" and
    A2: "\<psi>" and
    A3: "ch"   
   shows "\<phi> \<and> \<psi> \<and> ch"
   using assms by auto

lemma MMI_eqeq2i: assumes A1: "A = B"   
   shows "C = A \<longleftrightarrow> C = B"
   using assms by auto

lemma MMI_syl5bbr: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<psi> \<longleftrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> ( \<theta> \<longleftrightarrow> ch )"
   using assms by auto

lemma MMI_biimpd: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )"
   using assms by auto

lemma MMI_orrd: assumes A1: "\<phi> \<longrightarrow> ( \<not> ( \<psi> ) \<longrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<or> ch )"
   using assms by auto

lemma MMI_jaoi: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "ch \<longrightarrow> \<psi>"   
   shows "( \<phi> \<or> ch ) \<longrightarrow> \<psi>"
   using assms by auto

lemma MMI_oridm: 
   shows "( \<phi> \<or> \<phi> ) \<longleftrightarrow> \<phi>"
  by auto

lemma MMI_orbi1d: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( ( \<psi> \<or> \<theta> ) \<longleftrightarrow> ( ch \<or> \<theta> ) )"
   using assms by auto

lemma MMI_orbi2d: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( ( \<theta> \<or> \<psi> ) \<longleftrightarrow> ( \<theta> \<or> ch ) )"
   using assms by auto

(********* muln0bt-receu ******************)

lemma MMI_3bitr4g: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<theta> \<longleftrightarrow> \<psi>" and
    A3: "\<tau> \<longleftrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ( \<theta> \<longleftrightarrow> \<tau> )"
   using assms by auto

lemma MMI_negbid: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( \<not> ( \<psi> ) \<longleftrightarrow> \<not> ( ch ) )"
   using assms by auto

lemma MMI_ioran: 
   shows "\<not> ( ( \<phi> \<or> \<psi> ) ) \<longleftrightarrow> 
 ( \<not> ( \<phi> ) \<and> \<not> ( \<psi> ) )"
  by auto

lemma MMI_syl6rbb: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "ch \<longleftrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> ( \<theta> \<longleftrightarrow> \<psi> )"
   using assms by auto

lemma MMI_anbi12i: assumes A1: "\<phi> \<longleftrightarrow> \<psi>" and
    A2: "ch \<longleftrightarrow> \<theta>"   
   shows "( \<phi> \<and> ch ) \<longleftrightarrow> ( \<psi> \<and> \<theta> )"
   using assms by auto

(*******divmul-divclz ******************)


lemma MMI_keepel: assumes A1: "A \<in> C" and
    A2: "B \<in> C"   
   shows "if ( \<phi> , A , B ) \<in> C"
   using assms by auto

lemma MMI_imbi2d: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( ( \<theta> \<longrightarrow> \<psi> ) \<longleftrightarrow> ( \<theta> \<longrightarrow> ch ) )"
   using assms by auto

(** this was recognized as known , although not proven yet**)

lemma MMI_eqeltr: assumes "A = B" and "B \<in> C"
  shows "A \<in> C" using assms by auto

(*****divclt-divcan2t*******************)

lemma MMI_3impia: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ( ch \<longrightarrow> \<theta> )"   
   shows "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

(********* divne0bt-divrecz************)

lemma MMI_eqneqd: assumes A1: "\<phi> \<longrightarrow> ( A = B \<longleftrightarrow> C = D )"   
   shows "\<phi> \<longrightarrow> ( A \<noteq> B \<longleftrightarrow> C \<noteq> D )"
   using assms by auto

lemma MMI_3ad2ant2: assumes A1: "\<phi> \<longrightarrow> ch"   
   shows "( \<psi> \<and> \<phi> \<and> \<theta> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_mp3anl3: assumes A1: "ch" and
    A2: "( ( \<phi> \<and> \<psi> \<and> ch ) \<and> \<theta> ) \<longrightarrow> \<tau>"   
   shows "( ( \<phi> \<and> \<psi> ) \<and> \<theta> ) \<longrightarrow> \<tau>"
   using assms by auto

lemma MMI_bitr4d: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( \<theta> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> \<theta> )"
   using assms by auto

lemma MMI_neeq1d: assumes A1: "\<phi> \<longrightarrow> A = B"   
   shows "\<phi> \<longrightarrow> ( A \<noteq> C \<longleftrightarrow> B \<noteq> C )"
   using assms by auto

(*******divrect-div23***********************)

lemma MMI_3anim123i: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "ch \<longrightarrow> \<theta>" and
    A3: "\<tau> \<longrightarrow> \<eta>"   
   shows "( \<phi> \<and> ch \<and> \<tau> ) \<longrightarrow> ( \<psi> \<and> \<theta> \<and> \<eta> )"
   using assms by auto

lemma MMI_3exp: assumes A1: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ( ch \<longrightarrow> \<theta> ) )"
   using assms by auto

lemma MMI_exp4a: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ( ( ch \<and> \<theta> ) \<longrightarrow> \<tau> ) )"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ( ch \<longrightarrow> ( \<theta> \<longrightarrow> \<tau> ) ) )"
   using assms by auto

lemma MMI_3imp1: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ( ch \<longrightarrow> ( \<theta> \<longrightarrow> \<tau> ) ) )"   
   shows "( ( \<phi> \<and> \<psi> \<and> ch ) \<and> \<theta> ) \<longrightarrow> \<tau>"
   using assms by auto

lemma MMI_anim1i: assumes A1: "\<phi> \<longrightarrow> \<psi>"   
   shows "( \<phi> \<and> ch ) \<longrightarrow> ( \<psi> \<and> ch )"
   using assms by auto

lemma MMI_3adantl1: assumes A1: "( ( \<phi> \<and> \<psi> ) \<and> ch ) \<longrightarrow> \<theta>"   
   shows "( ( \<tau> \<and> \<phi> \<and> \<psi> ) \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_3adantl2: assumes A1: "( ( \<phi> \<and> \<psi> ) \<and> ch ) \<longrightarrow> \<theta>"   
   shows "( ( \<phi> \<and> \<tau> \<and> \<psi> ) \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_3comr: assumes A1: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"   
   shows "( ch \<and> \<phi> \<and> \<psi> ) \<longrightarrow> \<theta>"
   using assms by auto

(***********divdirz-div11t*************************)

lemma MMI_bitr3: assumes A1: "\<psi> \<longleftrightarrow> \<phi>" and
    A2: "\<psi> \<longleftrightarrow> ch"   
   shows "\<phi> \<longleftrightarrow> ch"
   using assms by auto

lemma MMI_anbi12d: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( \<theta> \<longleftrightarrow> \<tau> )"   
   shows "\<phi> \<longrightarrow> ( ( \<psi> \<and> \<theta> ) \<longleftrightarrow> ( ch \<and> \<tau> ) )"
   using assms by auto

lemma MMI_pm3_26i: assumes A1: "\<phi> \<and> \<psi>"   
   shows "\<phi>"
   using assms by auto

lemma MMI_pm3_27i: assumes A1: "\<phi> \<and> \<psi>"   
   shows "\<psi>"
   using assms by auto

(*********dividt-divsubdirt************************)

lemma MMI_anabsan: assumes A1: "( ( \<phi> \<and> \<phi> ) \<and> \<psi> ) \<longrightarrow> ch"   
   shows "( \<phi> \<and> \<psi> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_3eqtr4rd: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<phi> \<longrightarrow> C = A" and
    A3: "\<phi> \<longrightarrow> D = B"   
   shows "\<phi> \<longrightarrow> D = C"
   using assms by auto

lemma MMI_syl3an1: assumes A1: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>" and
    A2: "\<tau> \<longrightarrow> \<phi>"   
   shows "( \<tau> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_syl3anl2: assumes A1: "( ( \<phi> \<and> \<psi> \<and> ch ) \<and> \<theta> ) \<longrightarrow> \<tau>" and
    A2: "\<eta> \<longrightarrow> \<psi>"   
   shows "( ( \<phi> \<and> \<eta> \<and> ch ) \<and> \<theta> ) \<longrightarrow> \<tau>"
   using assms by auto

(******* recrect-divmuldiv ****************)


lemma MMI_jca: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "\<phi> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<and> ch )"
   using assms by auto

lemma MMI_3ad2ant3: assumes A1: "\<phi> \<longrightarrow> ch"   
   shows "( \<psi> \<and> \<theta> \<and> \<phi> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_anim2i: assumes A1: "\<phi> \<longrightarrow> \<psi>"   
   shows "( ch \<and> \<phi> ) \<longrightarrow> ( ch \<and> \<psi> )"
   using assms by auto

lemma MMI_ancom: 
   shows "( \<phi> \<and> \<psi> ) \<longleftrightarrow> ( \<psi> \<and> \<phi> )"
  by auto

lemma MMI_anbi1i: assumes Aaa: "\<phi> \<longleftrightarrow> \<psi>"   
   shows "( \<phi> \<and> ch ) \<longleftrightarrow> ( \<psi> \<and> ch )"
   using assms by auto

lemma MMI_an42: 
   shows "( ( \<phi> \<and> \<psi> ) \<and> ( ch \<and> \<theta> ) ) \<longleftrightarrow> 
 ( ( \<phi> \<and> ch ) \<and> ( \<theta> \<and> \<psi> ) )"
  by auto

lemma MMI_sylanb: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch" and
    A2: "\<theta> \<longleftrightarrow> \<phi>"   
   shows "( \<theta> \<and> \<psi> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_an4: 
   shows "( ( \<phi> \<and> \<psi> ) \<and> ( ch \<and> \<theta> ) ) \<longleftrightarrow> 
 ( ( \<phi> \<and> ch ) \<and> ( \<psi> \<and> \<theta> ) )"
  by auto

lemma MMI_syl2anb: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch" and
    A2: "\<theta> \<longleftrightarrow> \<phi>" and
    A3: "\<tau> \<longleftrightarrow> \<psi>"   
   shows "( \<theta> \<and> \<tau> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_eqtr2d: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<phi> \<longrightarrow> B = C"   
   shows "\<phi> \<longrightarrow> C = A"
   using assms by auto

lemma MMI_sylbid: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( ch \<longrightarrow> \<theta> )"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> \<theta> )"
   using assms by auto

lemma MMI_sylanl1: assumes A1: "( ( \<phi> \<and> \<psi> ) \<and> ch ) \<longrightarrow> \<theta>" and
    A2: "\<tau> \<longrightarrow> \<phi>"   
   shows "( ( \<tau> \<and> \<psi> ) \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_sylan2b: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch" and
    A2: "\<theta> \<longleftrightarrow> \<psi>"   
   shows "( \<phi> \<and> \<theta> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_pm3_22: 
   shows "( \<phi> \<and> \<psi> ) \<longrightarrow> ( \<psi> \<and> \<phi> )"
  by auto

lemma MMI_ancli: assumes A1: "\<phi> \<longrightarrow> \<psi>"   
   shows "\<phi> \<longrightarrow> ( \<phi> \<and> \<psi> )"
   using assms by auto

lemma MMI_ad2antlr: assumes A1: "\<phi> \<longrightarrow> \<psi>"   
   shows "( ( ch \<and> \<phi> ) \<and> \<theta> ) \<longrightarrow> \<psi>"
   using assms by auto

lemma MMI_biimpa: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "( \<phi> \<and> \<psi> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_sylan2i: assumes A1: "\<phi> \<longrightarrow> ( ( \<psi> \<and> ch ) \<longrightarrow> \<theta> )" and
    A2: "\<tau> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ( ( \<psi> \<and> \<tau> ) \<longrightarrow> \<theta> )"
   using assms by auto

lemma MMI_3jca: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "\<phi> \<longrightarrow> ch" and
    A3: "\<phi> \<longrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<and> ch \<and> \<theta> )"
   using assms by auto

lemma MMI_com34: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ( ch \<longrightarrow> ( \<theta> \<longrightarrow> \<tau> ) ) )"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ( \<theta> \<longrightarrow> ( ch \<longrightarrow> \<tau> ) ) )"
   using assms by auto

lemma MMI_imp43: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ( ch \<longrightarrow> ( \<theta> \<longrightarrow> \<tau> ) ) )"   
   shows "( ( \<phi> \<and> \<psi> ) \<and> ( ch \<and> \<theta> ) ) \<longrightarrow> \<tau>"
   using assms by auto

lemma MMI_3anass: 
   shows "( \<phi> \<and> \<psi> \<and> ch ) \<longleftrightarrow> ( \<phi> \<and> ( \<psi> \<and> ch ) )"
  by auto

(************ divmul13-redivclt*************)

lemma MMI_3eqtr4r: assumes A1: "A = B" and
    A2: "C = A" and
    A3: "D = B"   
   shows "D = C"
   using assms by auto

lemma MMI_jctl: assumes A1: "\<psi>"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<and> \<phi> )"
   using assms by auto

lemma MMI_sylibr: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "ch \<longleftrightarrow> \<psi>"   
   shows "\<phi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_mpanl1: assumes A1: "\<phi>" and
    A2: "( ( \<phi> \<and> \<psi> ) \<and> ch ) \<longrightarrow> \<theta>"   
   shows "( \<psi> \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_a1i: assumes A1: "\<phi>"   
   shows "\<psi> \<longrightarrow> \<phi>"
   using assms by auto

lemma (in MMIsar0) MMI_opreqan12rd: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<psi> \<longrightarrow> C = D"   
   shows 
  "( \<psi> \<and> \<phi> ) \<longrightarrow> ( A \<ca> C ) = ( B \<ca> D )"
  "( \<psi> \<and> \<phi> ) \<longrightarrow> ( A \<cdot> C ) = ( B \<cdot> D )"
  "( \<psi> \<and> \<phi> ) \<longrightarrow> ( A \<cs> C ) = ( B \<cs> D )"
  "( \<psi> \<and> \<phi> ) \<longrightarrow> ( A \<cdiv> C ) = ( B \<cdiv> D )"
   using assms by auto

lemma MMI_3adantl3: assumes A1: "( ( \<phi> \<and> \<psi> ) \<and> ch ) \<longrightarrow> \<theta>"   
   shows "( ( \<phi> \<and> \<psi> \<and> \<tau> ) \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_sylbi: assumes A1: "\<phi> \<longleftrightarrow> \<psi>" and
    A2: "\<psi> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ch"
   using assms by auto

(*******pnfnre,minfnre*******************)

lemma MMI_eirr: 
   shows "\<not> ( A \<in> A )"
  by (rule mem_not_refl)

lemma MMI_eleq1i: assumes A1: "A = B"   
   shows "A \<in> C \<longleftrightarrow> B \<in> C"
   using assms by auto

lemma MMI_mtbir: assumes A1: "\<not> ( \<psi> )" and
    A2: "\<phi> \<longleftrightarrow> \<psi>"   
   shows "\<not> ( \<phi> )"
   using assms by auto

lemma MMI_mto: assumes A1: "\<not> ( \<psi> )" and
    A2: "\<phi> \<longrightarrow> \<psi>"   
   shows "\<not> ( \<phi> )"
   using assms by auto

lemma MMI_df_nel: 
   shows "( A \<notin> B \<longleftrightarrow> \<not> ( A \<in> B ) )"
  by auto

lemma MMI_snid: assumes A1: "A isASet"   
   shows "A \<in> { A }"
   using assms by auto

lemma MMI_en2lp: 
   shows "\<not> ( A \<in> B \<and> B \<in> A )"
proof
  assume A1: "A \<in> B \<and> B \<in> A"
  then have "A \<in> B" by simp
  moreover
  { assume "\<not> (\<not> ( A \<in> B \<and> B \<in> A ))"
    then have "B\<in>A" by auto}
  ultimately have "\<not>( A \<in> B \<and> B \<in> A )"
    by (rule mem_asym)
  with A1 show False by simp
qed

lemma MMI_imnan: 
   shows "( \<phi> \<longrightarrow> \<not> ( \<psi> ) ) \<longleftrightarrow> \<not> ( ( \<phi> \<and> \<psi> ) )"
  by auto

(****ressxr-ltxrltt*******************************)

lemma MMI_sseqtr4: assumes A1: "A \<subseteq> B" and
    A2: "C = B"   
   shows "A \<subseteq> C"
   using assms by auto

lemma MMI_ssun1: 
   shows "A \<subseteq> ( A \<union> B )"
  by auto

lemma MMI_ibar: 
   shows "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ( \<phi> \<and> \<psi> ) )"
  by auto

lemma MMI_mtbiri: assumes Amin: "\<not> ( ch )" and
    Amaj: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> \<not> ( \<psi> )"
   using assms by auto

lemma MMI_con2i: assumes Aa: "\<phi> \<longrightarrow> \<not> ( \<psi> )"   
   shows "\<psi> \<longrightarrow> \<not> ( \<phi> )"
   using assms by auto

lemma MMI_intnand: assumes A1: "\<phi> \<longrightarrow> \<not> ( \<psi> )"   
   shows "\<phi> \<longrightarrow> \<not> ( ( ch \<and> \<psi> ) )"
   using assms by auto

lemma MMI_intnanrd: assumes A1: "\<phi> \<longrightarrow> \<not> ( \<psi> )"   
   shows "\<phi> \<longrightarrow> \<not> ( ( \<psi> \<and> ch ) )"
   using assms by auto

lemma MMI_biorf: 
   shows "\<not> ( \<phi> ) \<longrightarrow> ( \<psi> \<longleftrightarrow> ( \<phi> \<or> \<psi> ) )"
  by auto

lemma MMI_bitr2d: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( ch \<longleftrightarrow> \<theta> )"   
   shows "\<phi> \<longrightarrow> ( \<theta> \<longleftrightarrow> \<psi> )"
   using assms by auto

lemma MMI_orass: 
   shows "( ( \<phi> \<or> \<psi> ) \<or> ch ) \<longleftrightarrow> ( \<phi> \<or> ( \<psi> \<or> ch ) )"
  by auto

lemma MMI_orcom: 
   shows "( \<phi> \<or> \<psi> ) \<longleftrightarrow> ( \<psi> \<or> \<phi> )"
  by auto

(************** axlttri,axlttrn****************)
(* note these are not really axioms of 
    complex numbers, just extensions of
    pre_axlttri and pre_axlttrn that are assumed
    in the context.                           
*)

lemma MMI_3bitr4d: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( \<theta> \<longleftrightarrow> \<psi> )" and
    A3: "\<phi> \<longrightarrow> ( \<tau> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( \<theta> \<longleftrightarrow> \<tau> )"
   using assms by auto

lemma MMI_3imtr4d: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( \<theta> \<longleftrightarrow> \<psi> )" and
    A3: "\<phi> \<longrightarrow> ( \<tau> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( \<theta> \<longrightarrow> \<tau> )"
   using assms by auto

(**********axltadd-ltnlet*************************)

lemma MMI_3impdi: assumes A1: "( ( \<phi> \<and> \<psi> ) \<and> ( \<phi> \<and> ch ) ) \<longrightarrow> \<theta>"   
   shows "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_bi2anan9: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<theta> \<longrightarrow> ( \<tau> \<longleftrightarrow> \<eta> )"   
   shows "( \<phi> \<and> \<theta> ) \<longrightarrow> ( ( \<psi> \<and> \<tau> ) \<longleftrightarrow> ( ch \<and> \<eta> ) )"
   using assms by auto

lemma MMI_ssel2: 
   shows "( ( A \<subseteq> B \<and> C \<in> A ) \<longrightarrow> C \<in> B )"
  by auto

lemma MMI_an1rs: assumes A1: "( ( \<phi> \<and> \<psi> ) \<and> ch ) \<longrightarrow> \<theta>"   
   shows "( ( \<phi> \<and> ch ) \<and> \<psi> ) \<longrightarrow> \<theta>"
   using assms by auto

(*lemma MMI_ralbidva_original: 
     assumes A1: "( \<phi> \<and> x \<in> A ) \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow>  ( ( \<forall> x \<in> A . \<psi> ) \<longleftrightarrow> ( \<forall> x \<in> A . ch ) )"
   using assms by auto;*)

lemma MMI_ralbidva: assumes A1: "\<forall>x. ( \<phi> \<and> x \<in> A ) \<longrightarrow> ( \<psi>(x) \<longleftrightarrow> ch(x) )"   
   shows "\<phi> \<longrightarrow>  ( ( \<forall> x \<in> A . \<psi>(x) ) \<longleftrightarrow> ( \<forall> x \<in> A . ch(x) ) )"
   using assms by auto

lemma MMI_rexbidva: assumes A1: "\<forall>x. ( \<phi> \<and> x \<in> A ) \<longrightarrow> ( \<psi>(x) \<longleftrightarrow> ch(x) )"   
   shows "\<phi> \<longrightarrow>  ( ( \<exists> x \<in> A . \<psi>(x) ) \<longleftrightarrow> ( \<exists> x \<in> A . ch(x) ) )"
   using assms by auto

lemma MMI_con2bid: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> \<not> ( ch ) )"   
   shows "\<phi> \<longrightarrow> ( ch \<longleftrightarrow> \<not> ( \<psi> ) )"
   using assms by auto

(********ltso***************************)
lemma MMI_so: assumes 
  A1: "\<forall>x y z. ( x \<in> A \<and> y \<in> A \<and> z \<in> A ) \<longrightarrow>   
  ( ( \<langle>x,y\<rangle> \<in> R \<longleftrightarrow> \<not> ( ( x = y \<or> \<langle>y, x\<rangle> \<in> R ) ) ) \<and> 
  ( ( \<langle>x, y\<rangle> \<in> R  \<and> \<langle>y, z\<rangle> \<in> R ) \<longrightarrow> \<langle>x, z\<rangle> \<in> R ) )"   
  shows "R Orders A"
  using assms StrictOrder_def by auto

(***********lttri2t-letri3t**********************)

lemma MMI_con1bid: assumes A1: "\<phi> \<longrightarrow> ( \<not> ( \<psi> ) \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( \<not> ( ch ) \<longleftrightarrow> \<psi> )"
   using assms by auto

lemma MMI_sotrieq: 
  shows "( (R Orders A) \<and> ( B \<in> A \<and> C \<in> A ) ) \<longrightarrow>   
  ( B = C \<longleftrightarrow> \<not> ( ( \<langle>B,C\<rangle> \<in> R \<or> \<langle>C, B\<rangle> \<in> R ) ) )"
proof -
  { assume A1: "R Orders A"  and A2: "B \<in> A \<and> C \<in> A" 
    from A1 have "\<forall>x y z. (x\<in>A \<and> y\<in>A \<and> z\<in>A) \<longrightarrow> 
      (\<langle>x,y\<rangle> \<in> R \<longleftrightarrow> \<not>(x=y \<or> \<langle>y,x\<rangle> \<in> R)) \<and> 
      (\<langle>x,y\<rangle> \<in> R \<and> \<langle>y,z\<rangle> \<in> R \<longrightarrow> \<langle>x,z\<rangle> \<in> R)"
      by (unfold StrictOrder_def)
    then have 
      "\<forall>x y. x\<in>A \<and> y\<in>A \<longrightarrow> (\<langle>x,y\<rangle> \<in> R \<longleftrightarrow> \<not>(x=y \<or> \<langle>y,x\<rangle> \<in> R))"
      by auto
    with A2 have I: "\<langle>B,C\<rangle> \<in> R \<longleftrightarrow> \<not>(B=C \<or> \<langle>C,B\<rangle> \<in> R)"
      by blast
    then have "B = C \<longleftrightarrow> \<not> ( \<langle>B,C\<rangle> \<in> R \<or> \<langle>C, B\<rangle> \<in> R )"
      by auto
  } then show "( (R Orders A) \<and> ( B \<in> A \<and> C \<in> A ) ) \<longrightarrow>   
      ( B = C \<longleftrightarrow> \<not> ( ( \<langle>B,C\<rangle> \<in> R \<or> \<langle>C, B\<rangle> \<in> R ) ) )" by simp
qed

lemma MMI_bicomd: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( ch \<longleftrightarrow> \<psi> )"
   using assms by auto

lemma MMI_sotrieq2: 
  shows "( R Orders A \<and> ( B \<in> A \<and> C \<in> A ) ) \<longrightarrow>   
  ( B =  C \<longleftrightarrow> ( \<not> ( \<langle>B, C\<rangle> \<in> R ) \<and> \<not> ( \<langle>C, B\<rangle> \<in> R ) ) )"
  using  MMI_sotrieq by auto

lemma MMI_orc: 
   shows "\<phi> \<longrightarrow> ( \<phi> \<or> \<psi> )"
  by auto

lemma MMI_syl6bbr: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<theta> \<longleftrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> \<theta> )"
   using assms by auto

(***********leloet-lelttrd*****************)

lemma MMI_orbi1i: assumes A1: "\<phi> \<longleftrightarrow> \<psi>"   
   shows "( \<phi> \<or> ch ) \<longleftrightarrow> ( \<psi> \<or> ch )"
   using assms by auto

lemma MMI_syl5rbbr: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<psi> \<longleftrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> ( ch \<longleftrightarrow> \<theta> )"
   using assms by auto

lemma MMI_anbi2d: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( ( \<theta> \<and> \<psi> ) \<longleftrightarrow> ( \<theta> \<and> ch ) )"
   using assms by auto

lemma MMI_ord: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<or> ch )"   
   shows "\<phi> \<longrightarrow> ( \<not> ( \<psi> ) \<longrightarrow> ch )"
   using assms by auto

lemma MMI_impbid: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( ch \<longrightarrow> \<psi> )"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"
   using assms by blast

lemma MMI_jcad: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> \<theta> )"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ( ch \<and> \<theta> ) )"
   using assms by auto

lemma MMI_ax_1: 
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> \<phi> )"
  by auto

lemma MMI_pm2_24: 
   shows "\<phi> \<longrightarrow> ( \<not> ( \<phi> ) \<longrightarrow> \<psi> )"
  by auto

lemma MMI_imp3a: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ( ch \<longrightarrow> \<theta> ) )"   
   shows "\<phi> \<longrightarrow> ( ( \<psi> \<and> ch ) \<longrightarrow> \<theta> )"
   using assms by auto

lemma (in MMIsar0) MMI_breq1: 
   shows 
  "A = B \<longrightarrow> ( A \<lsq> C \<longleftrightarrow> B \<lsq> C )"
  "A = B \<longrightarrow> ( A \<ls> C \<longleftrightarrow> B \<ls> C )"
  by auto

lemma MMI_biimprd: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( ch \<longrightarrow> \<psi> )"
   using assms by auto

lemma MMI_jaod: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( \<theta> \<longrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( ( \<psi> \<or> \<theta> ) \<longrightarrow> ch )"
   using assms by auto

lemma MMI_com23: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ( ch \<longrightarrow> \<theta> ) )"   
   shows "\<phi> \<longrightarrow> ( ch \<longrightarrow> ( \<psi> \<longrightarrow> \<theta> ) )"
   using assms by auto

lemma (in MMIsar0) MMI_breq2: 
   shows 
  "A = B \<longrightarrow> ( C \<lsq> A \<longleftrightarrow> C \<lsq> B )"
  "A = B \<longrightarrow> ( C \<ls> A \<longleftrightarrow> C \<ls> B )"
  by auto

lemma MMI_syld: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( ch \<longrightarrow> \<theta> )"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> \<theta> )"
   using assms by auto

lemma MMI_biimpcd: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<psi> \<longrightarrow> ( \<phi> \<longrightarrow> ch )"
   using assms by auto

lemma MMI_mp2and: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "\<phi> \<longrightarrow> ch" and
    A3: "\<phi> \<longrightarrow> ( ( \<psi> \<and> ch ) \<longrightarrow> \<theta> )"   
   shows "\<phi> \<longrightarrow> \<theta>"
   using assms by auto

(**********ltletrd-renemnft*********************)

lemma MMI_sonr: 
   shows "( R Orders A \<and> B \<in> A ) \<longrightarrow> \<not> ( \<langle>B,B\<rangle> \<in> R )"
  unfolding StrictOrder_def by auto

lemma MMI_orri: assumes A1: "\<not> ( \<phi> ) \<longrightarrow> \<psi>"   
   shows "\<phi> \<or> \<psi>"
   using assms by auto

lemma MMI_mpbiri: assumes Amin: "ch" and
    Amaj: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> \<psi>"
   using assms by auto

lemma MMI_pm2_46: 
   shows "\<not> ( ( \<phi> \<or> \<psi> ) ) \<longrightarrow> \<not> ( \<psi> )"
  by auto

lemma MMI_elun: 
   shows "A \<in> ( B \<union> C ) \<longleftrightarrow> ( A \<in> B \<or> A \<in> C )"
  by auto

lemma (in MMIsar0) MMI_pnfxr: 
   shows "\<cpnf> \<in> \<real>\<^sup>*"
  using cxr_def by simp

lemma MMI_elisseti: assumes A1: "A \<in> B"   
   shows "A isASet"
   using assms by auto

lemma (in MMIsar0) MMI_mnfxr: 
   shows "\<cmnf> \<in> \<real>\<^sup>*"
  using  cxr_def by simp

lemma MMI_elpr2: assumes A1: "B isASet" and
    A2: "C isASet"   
   shows "A \<in> { B , C } \<longleftrightarrow> ( A = B \<or> A = C )"
   using assms by auto

lemma MMI_orbi2i: assumes A1: "\<phi> \<longleftrightarrow> \<psi>"   
   shows "( ch \<or> \<phi> ) \<longleftrightarrow> ( ch \<or> \<psi> )"
   using assms by auto

lemma MMI_3orass: 
   shows "( \<phi> \<or> \<psi> \<or> ch ) \<longleftrightarrow> ( \<phi> \<or> ( \<psi> \<or> ch ) )"
  by auto

lemma MMI_bitr4: assumes A1: "\<phi> \<longleftrightarrow> \<psi>" and
    A2: "ch \<longleftrightarrow> \<psi>"   
   shows "\<phi> \<longleftrightarrow> ch"
   using assms by auto

lemma MMI_eleq2: 
   shows "A = B \<longrightarrow> ( C \<in> A \<longleftrightarrow> C \<in> B )"
  by auto

lemma MMI_nelneq: 
   shows "( A \<in> C \<and> \<not> ( B \<in> C ) ) \<longrightarrow> \<not> ( A = B )"
  by auto

(************ renfdisj - pnfget *********************)

lemma MMI_df_pr: 
   shows "{ A , B } = ( { A } \<union> { B } )"
  by auto

lemma MMI_ineq2i: assumes A1: "A = B"   
   shows "( C \<inter> A ) = ( C \<inter> B )"
   using assms by auto

lemma MMI_mt2: assumes A1: "\<psi>" and
    A2: "\<phi> \<longrightarrow> \<not> ( \<psi> )"   
   shows "\<not> ( \<phi> )"
   using assms by auto

lemma MMI_disjsn: 
   shows "( A \<inter> { B } ) = 0 \<longleftrightarrow> \<not> ( B \<in> A )"
  by auto

lemma MMI_undisj2: 
   shows "( ( A \<inter> B ) =   
 0 \<and> ( A \<inter> C ) =   
 0 ) \<longleftrightarrow> ( A \<inter> ( B \<union> C ) ) = 0"
  by auto

lemma MMI_disjssun: 
   shows "( ( A \<inter> B ) =  0 \<longrightarrow> ( A \<subseteq> ( B \<union> C ) \<longleftrightarrow> A \<subseteq> C ) )"
  by auto

lemma MMI_uncom: 
   shows "( A \<union> B ) = ( B \<union> A )"
  by auto

lemma MMI_sseq2i: assumes A1: "A = B"   
   shows "( C \<subseteq> A \<longleftrightarrow> C \<subseteq> B )"
   using assms by auto

lemma MMI_disj: 
   shows "( A \<inter> B ) =   
 0 \<longleftrightarrow> ( \<forall> x \<in> A . \<not> ( x \<in> B ) )"
  by auto

lemma MMI_syl5ibr: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )" and
    A2: "\<psi> \<longleftrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> ( \<theta> \<longrightarrow> ch )"
   using assms by auto

lemma MMI_con3d: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( \<not> ( ch ) \<longrightarrow> \<not> ( \<psi> ) )"
   using assms by auto

(* original lemma MMI_dfrex2: 
   shows "( \<exists> x \<in> A . \<phi> ) \<longleftrightarrow>  \<not> ( ( \<forall> x \<in> A . \<not> ( \<phi> ) ) )"
  by auto*)

lemma MMI_dfrex2: 
  shows "( \<exists> x \<in> A . \<phi>(x) ) \<longleftrightarrow>  \<not> ( ( \<forall> x \<in> A . \<not> \<phi>(x) ) )"
  by auto

lemma MMI_visset: 
   shows "x isASet"
  by auto

lemma MMI_elpr: assumes A1: "A isASet"   
   shows "A \<in> { B , C } \<longleftrightarrow> ( A = B \<or> A = C )"
   using assms by auto

lemma MMI_rexbii: assumes A1: "\<forall>x. \<phi>(x) \<longleftrightarrow> \<psi>(x)"   
   shows "( \<exists> x \<in> A . \<phi>(x) ) \<longleftrightarrow> ( \<exists> x \<in> A . \<psi>(x) )"
   using assms by auto

lemma MMI_r19_43: 
   shows "( \<exists> x \<in> A . ( \<phi>(x) \<or> \<psi>(x) ) ) \<longleftrightarrow>   
 ( ( \<exists> x \<in> A . \<phi>(x) \<or> ( \<exists> x \<in> A . \<psi>(x) ) ) )"
  by auto

lemma MMI_exancom: 
   shows "( \<exists> x . ( \<phi>(x) \<and> \<psi>(x) ) ) \<longleftrightarrow>   
 ( \<exists> x . ( \<psi>(x) \<and> \<phi>(x) ) )"
  by auto

lemma MMI_ceqsexv: assumes A1: "A isASet" and
    A2: "\<forall>x. x = A \<longrightarrow> ( \<phi>(x) \<longleftrightarrow> \<psi>(x) )"   
   shows "( \<exists> x . ( x = A \<and> \<phi>(x) ) ) \<longleftrightarrow> \<psi>(A)"
   using assms by auto

lemma MMI_orbi12i_orig: assumes A1: "\<phi> \<longleftrightarrow> \<psi>" and
    A2: "ch \<longleftrightarrow> \<theta>"   
   shows "( \<phi> \<or> ch ) \<longleftrightarrow> ( \<psi> \<or> \<theta> )"
   using assms by auto

lemma MMI_orbi12i: assumes A1: "(\<exists>x. \<phi>(x)) \<longleftrightarrow> \<psi>" and
    A2: "(\<exists>x. ch(x)) \<longleftrightarrow> \<theta>"   
   shows "( \<exists>x. \<phi>(x) ) \<or> (\<exists>x. ch(x) ) \<longleftrightarrow> ( \<psi> \<or> \<theta> )"
   using assms by auto

lemma MMI_syl6ib: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )" and
    A2: "ch \<longleftrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> \<theta> )"
   using assms by auto

lemma MMI_intnan: assumes A1: "\<not> ( \<phi> )"   
   shows "\<not> ( ( \<psi> \<and> \<phi> ) )"
   using assms by auto

lemma MMI_intnanr: assumes A1: "\<not> ( \<phi> )"   
   shows "\<not> ( ( \<phi> \<and> \<psi> ) )"
   using assms by auto

lemma MMI_pm3_2ni: assumes A1: "\<not> ( \<phi> )" and
    A2: "\<not> ( \<psi> )"   
   shows "\<not> ( ( \<phi> \<or> \<psi> ) )"
   using assms by auto

lemma (in MMIsar0) MMI_breq12: 
   shows 
  "( A = B \<and> C = D ) \<longrightarrow> ( A \<ls> C \<longleftrightarrow> B \<ls> D )"
  "( A = B \<and> C = D ) \<longrightarrow> ( A \<lsq> C \<longleftrightarrow> B \<lsq> D )"
  by auto

lemma MMI_necom: 
   shows "A \<noteq> B \<longleftrightarrow> B \<noteq> A"
  by auto

lemma MMI_3jaoi: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "ch \<longrightarrow> \<psi>" and
    A3: "\<theta> \<longrightarrow> \<psi>"   
   shows "( \<phi> \<or> ch \<or> \<theta> ) \<longrightarrow> \<psi>"
   using assms by auto

lemma MMI_jctr: assumes A1: "\<psi>"   
   shows "\<phi> \<longrightarrow> ( \<phi> \<and> \<psi> )"
   using assms by auto

lemma MMI_olc: 
   shows "\<phi> \<longrightarrow> ( \<psi> \<or> \<phi> )"
  by auto

lemma MMI_3syl: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "\<psi> \<longrightarrow> ch" and
    A3: "ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> \<theta>"
   using assms by auto

(************** mnflet- xrlelttrt ***************)

lemma MMI_mtbird: assumes Amin: "\<phi> \<longrightarrow> \<not> ( ch )" and
    Amaj: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> \<not> ( \<psi> )"
   using assms by auto

lemma MMI_pm2_21d: assumes A1: "\<phi> \<longrightarrow> \<not> ( \<psi> )"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )"
   using assms by auto

lemma MMI_3jaodan: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch" and
    A2: "( \<phi> \<and> \<theta> ) \<longrightarrow> ch" and
    A3: "( \<phi> \<and> \<tau> ) \<longrightarrow> ch"   
   shows "( \<phi> \<and> ( \<psi> \<or> \<theta> \<or> \<tau> ) ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_sylan2br: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch" and
    A2: "\<psi> \<longleftrightarrow> \<theta>"   
   shows "( \<phi> \<and> \<theta> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_3jaoian: assumes A1: "( \<phi> \<and> \<psi> ) \<longrightarrow> ch" and
    A2: "( \<theta> \<and> \<psi> ) \<longrightarrow> ch" and
    A3: "( \<tau> \<and> \<psi> ) \<longrightarrow> ch"   
   shows "( ( \<phi> \<or> \<theta> \<or> \<tau> ) \<and> \<psi> ) \<longrightarrow> ch"
   using assms by auto

lemma MMI_mtbid: assumes Amin: "\<phi> \<longrightarrow> \<not> ( \<psi> )" and
    Amaj: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> \<not> ( ch )"
   using assms by auto

lemma MMI_con1d: assumes A1: "\<phi> \<longrightarrow> ( \<not> ( \<psi> ) \<longrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( \<not> ( ch ) \<longrightarrow> \<psi> )"
   using assms by auto

lemma MMI_pm2_21nd: assumes A1: "\<phi> \<longrightarrow> \<psi>"   
   shows "\<phi> \<longrightarrow> ( \<not> ( \<psi> ) \<longrightarrow> ch )"
   using assms by auto

lemma MMI_syl3an1b: assumes A1: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>" and
    A2: "\<tau> \<longleftrightarrow> \<phi>"   
   shows "( \<tau> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_adantld: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( ( \<theta> \<and> \<psi> ) \<longrightarrow> ch )"
   using assms by auto

lemma MMI_adantrd: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ( ( \<psi> \<and> \<theta> ) \<longrightarrow> ch )"
   using assms by auto

lemma MMI_anasss: assumes A1: "( ( \<phi> \<and> \<psi> ) \<and> ch ) \<longrightarrow> \<theta>"   
   shows "( \<phi> \<and> ( \<psi> \<and> ch ) ) \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_syl3an3b: assumes A1: "( \<phi> \<and> \<psi> \<and> ch ) \<longrightarrow> \<theta>" and
    A2: "\<tau> \<longleftrightarrow> ch"   
   shows "( \<phi> \<and> \<psi> \<and> \<tau> ) \<longrightarrow> \<theta>"
   using assms by auto

(**************xrltletrt-lttri3***********************)


lemma MMI_mpbid: assumes Amin: "\<phi> \<longrightarrow> \<psi>" and
    Amaj: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "\<phi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_orbi12d: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )" and
    A2: "\<phi> \<longrightarrow> ( \<theta> \<longleftrightarrow> \<tau> )"   
   shows "\<phi> \<longrightarrow> ( ( \<psi> \<or> \<theta> ) \<longleftrightarrow> ( ch \<or> \<tau> ) )"
   using assms by auto

lemma MMI_ianor: 
   shows "\<not> ( \<phi> \<and> \<psi> ) \<longleftrightarrow> \<not> \<phi> \<or> \<not> \<psi> "
  by auto

lemma MMI_bitr2: assumes A1: "\<phi> \<longleftrightarrow> \<psi>" and
    A2: "\<psi> \<longleftrightarrow> ch"   
   shows "ch \<longleftrightarrow> \<phi>"
   using assms by auto

lemma MMI_biimp: assumes A1: "\<phi> \<longleftrightarrow> \<psi>"   
   shows "\<phi> \<longrightarrow> \<psi>"
   using assms by auto

lemma MMI_mpan2d: assumes A1: "\<phi> \<longrightarrow> ch" and
    A2: "\<phi> \<longrightarrow> ( ( \<psi> \<and> ch ) \<longrightarrow> \<theta> )"   
   shows "\<phi> \<longrightarrow> ( \<psi> \<longrightarrow> \<theta> )"
   using assms by auto

lemma MMI_ad2antrr: assumes A1: "\<phi> \<longrightarrow> \<psi>"   
   shows "( ( \<phi> \<and> ch ) \<and> \<theta> ) \<longrightarrow> \<psi>"
   using assms by auto

lemma MMI_biimpac: assumes A1: "\<phi> \<longrightarrow> ( \<psi> \<longleftrightarrow> ch )"   
   shows "( \<psi> \<and> \<phi> ) \<longrightarrow> ch"
   using assms by auto

(***********letri3-ltne**************************)

lemma MMI_con2bii: assumes A1: "\<phi> \<longleftrightarrow> \<not> ( \<psi> )"   
   shows "\<psi> \<longleftrightarrow> \<not> ( \<phi> )"
   using assms by auto

lemma MMI_pm3_26bd: assumes A1: "\<phi> \<longleftrightarrow> ( \<psi> \<and> ch )"   
   shows "\<phi> \<longrightarrow> \<psi>"
   using assms by auto

(******* le2tri3 - leadd2 ***********************)

lemma MMI_biimpr: assumes A1: "\<phi> \<longleftrightarrow> \<psi>"   
   shows "\<psi> \<longrightarrow> \<phi>"
   using assms by auto

lemma (in MMIsar0) MMI_3brtr3g: assumes A1: "\<phi> \<longrightarrow> A \<ls> B" and
    A2: "A = C" and
    A3: "B = D"   
   shows "\<phi> \<longrightarrow> C \<ls> D"
   using assms by auto

lemma (in MMIsar0) MMI_breq12i: assumes A1: "A = B" and
    A2: "C = D"   
   shows 
  "A \<ls> C \<longleftrightarrow> B \<ls> D"
  "A \<lsq> C \<longleftrightarrow> B \<lsq> D"
   using assms by auto

lemma MMI_negbii: assumes Aa: "\<phi> \<longleftrightarrow> \<psi>"   
   shows "\<not>\<phi> \<longleftrightarrow> \<not>\<psi>"
   using assms by auto

(********* ltsubadd - addgt0 ***************)

lemma (in MMIsar0) MMI_breq1i: assumes A1: "A = B"   
   shows 
  "A \<ls> C \<longleftrightarrow> B \<ls> C"
  "A \<lsq> C \<longleftrightarrow> B \<lsq> C"
   using assms by auto

(****** addge0 - ltneg **********************)

lemma MMI_syl5eqr: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "A = C"   
   shows "\<phi> \<longrightarrow> C = B"
   using assms by auto

lemma (in MMIsar0) MMI_breq2d: assumes A1: "\<phi> \<longrightarrow> A = B"   
   shows 
   "\<phi> \<longrightarrow> C \<ls> A \<longleftrightarrow> C \<ls> B"
   "\<phi> \<longrightarrow> C \<lsq> A \<longleftrightarrow> C \<lsq> B"
   using assms by auto

lemma MMI_ccase: assumes A1: "\<phi> \<and> \<psi> \<longrightarrow> \<tau>" and
    A2: "ch \<and> \<psi> \<longrightarrow> \<tau>" and
    A3: "\<phi> \<and> \<theta> \<longrightarrow> \<tau>" and
    A4: "ch \<and> \<theta> \<longrightarrow> \<tau>"   
   shows "(\<phi> \<or> ch) \<and> (\<psi> \<or> \<theta>) \<longrightarrow> \<tau>"
   using assms by auto

lemma MMI_pm3_27bd: assumes A1: "\<phi> \<longleftrightarrow> \<psi> \<and> ch"   
   shows "\<phi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_nsyl3: assumes A1: "\<phi> \<longrightarrow> \<not>\<psi>" and
    A2: "ch \<longrightarrow> \<psi>"   
   shows "ch \<longrightarrow> \<not>\<phi>"
   using assms by auto

lemma MMI_jctild: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch" and
    A2: "\<phi> \<longrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> \<theta> \<and> ch"
   using assms by auto

lemma MMI_jctird: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch" and
    A2: "\<phi> \<longrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> ch \<and> \<theta>"
   using assms by auto

lemma MMI_ccase2: assumes A1: "\<phi> \<and> \<psi> \<longrightarrow> \<tau>" and
    A2: "ch \<longrightarrow> \<tau>" and
    A3: "\<theta> \<longrightarrow> \<tau>"   
   shows "(\<phi> \<or> ch) \<and> (\<psi> \<or> \<theta>) \<longrightarrow> \<tau>"
   using assms by auto

(******** leneg - msqgt0 **************)

lemma MMI_3bitr3r: assumes A1: "\<phi> \<longleftrightarrow> \<psi>" and
    A2: "\<phi> \<longleftrightarrow> ch" and
    A3: "\<psi> \<longleftrightarrow> \<theta>"   
   shows "\<theta> \<longleftrightarrow> ch"
   using assms by auto

lemma (in MMIsar0) MMI_syl6breq: assumes A1: "\<phi> \<longrightarrow> A \<ls> B" and
    A2: "B = C"   
   shows 
  "\<phi> \<longrightarrow> A \<ls>  C"
   using assms by auto

(********* msqge0 - addge01t ******************)

lemma MMI_pm2_61i: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "\<not>\<phi> \<longrightarrow> \<psi>"   
   shows "\<psi>"
   using assms by auto

lemma MMI_syl6req: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "B = C"   
   shows "\<phi> \<longrightarrow> C = A"
   using assms by auto

lemma MMI_pm2_61d: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch" and
    A2: "\<phi> \<longrightarrow> 
   \<not>\<psi> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_orim1d: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<or> \<theta> \<longrightarrow> ch \<or> \<theta>"
   using assms by auto

lemma (in MMIsar0) MMI_breq1d: assumes A1: "\<phi> \<longrightarrow> A = B"   
   shows 
  "\<phi> \<longrightarrow> A \<ls> C \<longleftrightarrow> B \<ls> C"
  "\<phi> \<longrightarrow> A \<lsq> C \<longleftrightarrow> B \<lsq> C"
   using assms by auto

lemma (in MMIsar0) MMI_breq12d: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<phi> \<longrightarrow> C = D"   
   shows 
  "\<phi> \<longrightarrow> A \<ls> C \<longleftrightarrow> B \<ls> D"
  "\<phi> \<longrightarrow> A \<lsq> C \<longleftrightarrow> B \<lsq> D"
   using assms by auto

lemma MMI_bibi2d: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   (\<theta> \<longleftrightarrow> \<psi>) \<longleftrightarrow> 
   \<theta> \<longleftrightarrow> ch"
   using assms by auto

(********* addge02t - leaddsubt *************)

lemma MMI_con4bid: assumes A1: "\<phi> \<longrightarrow> 
   \<not>\<psi> \<longleftrightarrow> \<not>ch"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch"
   using assms by auto

lemma MMI_3com13: assumes A1: "\<phi> \<and> \<psi> \<and> ch \<longrightarrow> \<theta>"   
   shows "ch \<and> \<psi> \<and> \<phi> \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_3bitr3rd: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch" and
    A2: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> \<theta>" and
    A3: "\<phi> \<longrightarrow> 
   ch \<longleftrightarrow> \<tau>"   
   shows "\<phi> \<longrightarrow> 
   \<tau> \<longleftrightarrow> \<theta>"
   using assms by auto

(*********** leaddsub2t - lt2addt ***************)
lemma MMI_3imtr4g: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch" and
    A2: "\<theta> \<longleftrightarrow> \<psi>" and
    A3: "\<tau> \<longleftrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   \<theta> \<longrightarrow> \<tau>"
   using assms by auto

lemma MMI_expcom: assumes A1: "\<phi> \<and> \<psi> \<longrightarrow> ch"   
   shows "\<psi> \<longrightarrow> \<phi> \<longrightarrow> ch"
   using assms by auto

lemma (in MMIsar0) MMI_breq2i: assumes A1: "A = B"   
   shows 
  "C \<ls> A \<longleftrightarrow> C \<ls> B"
  "C \<lsq> A \<longleftrightarrow> C \<lsq> B"
   using assms by auto

lemma MMI_3bitr2r: assumes A1: "\<phi> \<longleftrightarrow> \<psi>" and
    A2: "ch \<longleftrightarrow> \<psi>" and
    A3: "ch \<longleftrightarrow> \<theta>"   
   shows "\<theta> \<longleftrightarrow> \<phi>"
   using assms by auto

lemma MMI_dedth4h: assumes A1: "A =  if(\<phi>, A, R) \<longrightarrow> 
   \<tau> \<longleftrightarrow> \<eta>" and
    A2: "B =  if(\<psi>, B, S) \<longrightarrow> 
   \<eta> \<longleftrightarrow> \<zeta>" and
    A3: "C =  if(ch, C, F) \<longrightarrow> 
   \<zeta> \<longleftrightarrow> si" and
    A4: "D =  if(\<theta>, D, G) \<longrightarrow> si \<longleftrightarrow> rh" and
    A5: "rh"   
   shows "(\<phi> \<and> \<psi>) \<and> ch \<and> \<theta> \<longrightarrow> \<tau>"
   using assms by auto

lemma MMI_anbi1d: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<and> \<theta> \<longleftrightarrow> ch \<and> \<theta>"
   using assms by auto


(******** le2addt - posdift *********************)

lemma (in MMIsar0) MMI_breqtrrd: assumes A1: "\<phi> \<longrightarrow> A \<ls> B" and
    A2: "\<phi> \<longrightarrow> C = B"   
   shows "\<phi> \<longrightarrow> A \<ls> C"
   using assms by auto

(******* ltnegt - posdif *****************)

lemma MMI_syl3an: assumes A1: "\<phi> \<and> \<psi> \<and> ch \<longrightarrow> \<theta>" and
    A2: "\<tau> \<longrightarrow> \<phi>" and
    A3: "\<eta> \<longrightarrow> \<psi>" and
    A4: "\<zeta> \<longrightarrow> ch"   
   shows "\<tau> \<and> \<eta> \<and> \<zeta> \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_3bitrd: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch" and
    A2: "\<phi> \<longrightarrow> 
   ch \<longleftrightarrow> \<theta>" and
    A3: "\<phi> \<longrightarrow> 
   \<theta> \<longleftrightarrow> \<tau>"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> \<tau>"
   using assms by auto

(************ ltnegcon1 - lt01 **********************)

lemma (in MMIsar0) MMI_breqtr: assumes A1: "A \<ls> B" and
    A2: "B = C"   
   shows "A \<ls> C"
   using assms by auto

(*********** eqneg - ltp1 ********************)

lemma MMI_mpi: assumes A1: "\<psi>" and
    A2: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_eqtr2: assumes A1: "A = B" and
    A2: "B = C"   
   shows "C = A"
   using assms by auto

lemma MMI_eqneqi: assumes A1: "A = B \<longleftrightarrow> C = D"   
   shows "A \<noteq> B \<longleftrightarrow> C \<noteq> D"
   using assms by auto

lemma (in MMIsar0) MMI_eqbrtrrd: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<phi> \<longrightarrow> A \<ls> C"   
   shows "\<phi> \<longrightarrow> B \<ls> C"
   using assms by auto

lemma MMI_mpd: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_mpdan: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "\<phi> \<and> \<psi> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ch"
   using assms by auto

(************ recgt0i - ltdiv1i ***************)

lemma (in MMIsar0) MMI_breqtrd: assumes A1: "\<phi> \<longrightarrow> A \<ls> B" and
    A2: "\<phi> \<longrightarrow> B = C"   
   shows "\<phi> \<longrightarrow> A \<ls> C"
   using assms by auto

lemma MMI_mpand: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "\<phi> \<longrightarrow> 
   \<psi> \<and> ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> ch \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_imbi1d: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   (\<psi> \<longrightarrow> \<theta>) \<longleftrightarrow> 
   (ch \<longrightarrow> \<theta>)"
   using assms by auto

lemma MMI_mtbii: assumes Amin: "\<not>\<psi>" and
    Amaj: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch"   
   shows "\<phi> \<longrightarrow> \<not>ch"
   using assms by auto

(********** ltdiv1 - lemul2t **************)

lemma MMI_sylan2d: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<and> ch \<longrightarrow> \<theta>" and
    A2: "\<phi> \<longrightarrow> \<tau> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<and> \<tau> \<longrightarrow> \<theta>"
   using assms by auto

(********* ltmul2 - ltmulgt12t ***********)
lemma MMI_imp32: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<and> \<psi> \<and> ch \<longrightarrow> \<theta>"
   using assms by auto

lemma (in MMIsar0) MMI_breqan12d: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<psi> \<longrightarrow> C = D"   
   shows 
  "\<phi> \<and> \<psi> \<longrightarrow>  A \<ls> C \<longleftrightarrow> B \<ls> D"
  "\<phi> \<and> \<psi> \<longrightarrow>  A \<lsq> C \<longleftrightarrow> B \<lsq> D"
   using assms by auto

lemma MMI_a1dd: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> \<theta> \<longrightarrow> ch"
   using assms by auto

lemma (in MMIsar0) MMI_3brtr3d: assumes A1: "\<phi> \<longrightarrow> A \<lsq> B" and
    A2: "\<phi> \<longrightarrow> A = C" and
    A3: "\<phi> \<longrightarrow> B = D"   
   shows "\<phi> \<longrightarrow> C \<lsq> D"
   using assms by auto

lemma MMI_ad2antll: assumes A1: "\<phi> \<longrightarrow> \<psi>"   
   shows "ch \<and> \<theta> \<and> \<phi> \<longrightarrow> \<psi>"
   using assms by auto

lemma MMI_adantrrl: assumes A1: "\<phi> \<and> \<psi> \<and> ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<and> \<psi> \<and> \<tau> \<and> ch \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_syl2ani: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<and> ch \<longrightarrow> \<theta>" and
    A2: "\<tau> \<longrightarrow> \<psi>" and
    A3: "\<eta> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   \<tau> \<and> \<eta> \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_im2anan9: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch" and
    A2: "\<theta> \<longrightarrow> 
   \<tau> \<longrightarrow> \<eta>"   
   shows "\<phi> \<and> \<theta> \<longrightarrow> 
   \<psi> \<and> \<tau> \<longrightarrow> ch \<and> \<eta>"
   using assms by auto

lemma MMI_ancomsd: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<and> ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> 
   ch \<and> \<psi> \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_mpani: assumes A1: "\<psi>" and
    A2: "\<phi> \<longrightarrow> 
   \<psi> \<and> ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<longrightarrow> ch \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_syldan: assumes A1: "\<phi> \<and> \<psi> \<longrightarrow> ch" and
    A2: "\<phi> \<and> ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<and> \<psi> \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_mp3anl1: assumes A1: "\<phi>" and
    A2: "(\<phi> \<and> \<psi> \<and> ch) \<and> \<theta> \<longrightarrow> \<tau>"   
   shows "(\<psi> \<and> ch) \<and> \<theta> \<longrightarrow> \<tau>"
   using assms by auto

lemma MMI_3ad2ant1: assumes A1: "\<phi> \<longrightarrow> ch"   
   shows "\<phi> \<and> \<psi> \<and> \<theta> \<longrightarrow> ch"
   using assms by auto

(********* lemulge11t - divgt0i2 ***********)

lemma MMI_pm3_2: 
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> \<phi> \<and> \<psi>"
  by auto

lemma MMI_pm2_43i: assumes A1: "\<phi> \<longrightarrow> 
   \<phi> \<longrightarrow> \<psi>"   
   shows "\<phi> \<longrightarrow> \<psi>"
   using assms by auto

lemma MMI_jctil: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "ch"   
   shows "\<phi> \<longrightarrow> ch \<and> \<psi>"
   using assms by auto

lemma MMI_mpanl12: assumes A1: "\<phi>" and
    A2: "\<psi>" and
    A3: "(\<phi> \<and> \<psi>) \<and> ch \<longrightarrow> \<theta>"   
   shows "ch \<longrightarrow> \<theta>"
   using assms by auto

(********* divgt0i - ledivmul2t ***************)

lemma MMI_mpanr1: assumes A1: "\<psi>" and
    A2: "\<phi> \<and> \<psi> \<and> ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<and> ch \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_ad2antrl: assumes A1: "\<phi> \<longrightarrow> \<psi>"   
   shows "ch \<and> \<phi> \<and> \<theta> \<longrightarrow> \<psi>"
   using assms by auto

lemma MMI_3adant3r: assumes A1: "\<phi> \<and> \<psi> \<and> ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<and> \<psi> \<and> ch \<and> \<tau> \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_3adant1l: assumes A1: "\<phi> \<and> \<psi> \<and> ch \<longrightarrow> \<theta>"   
   shows "(\<tau> \<and> \<phi>) \<and> \<psi> \<and> ch \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_3adant2r: assumes A1: "\<phi> \<and> \<psi> \<and> ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<and> (\<psi> \<and> \<tau>) \<and> ch \<longrightarrow> \<theta>"
   using assms by auto

(********** lemuldivt - lerect ****************)

lemma MMI_3bitr4rd: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch" and
    A2: "\<phi> \<longrightarrow> 
   \<theta> \<longleftrightarrow> \<psi>" and
    A3: "\<phi> \<longrightarrow> 
   \<tau> \<longleftrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   \<tau> \<longleftrightarrow> \<theta>"
   using assms by auto

lemma MMI_3anrev: 
   shows "\<phi> \<and> \<psi> \<and> ch \<longleftrightarrow> ch \<and> \<psi> \<and> \<phi>"
  by auto

lemma MMI_eqtr4: assumes A1: "A = B" and
    A2: "C = B"   
   shows "A = C"
   using assms by auto

lemma MMI_anidm: 
   shows "\<phi> \<and> \<phi> \<longleftrightarrow> \<phi>"
  by auto

lemma MMI_bi2anan9r: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch" and
    A2: "\<theta> \<longrightarrow> 
   \<tau> \<longleftrightarrow> \<eta>"   
   shows "\<theta> \<and> \<phi> \<longrightarrow> 
   \<psi> \<and> \<tau> \<longleftrightarrow> ch \<and> \<eta>"
   using assms by auto

lemma MMI_3imtr3g: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch" and
    A2: "\<psi> \<longleftrightarrow> \<theta>" and
    A3: "ch \<longleftrightarrow> \<tau>"   
   shows "\<phi> \<longrightarrow> 
   \<theta> \<longrightarrow> \<tau>"
   using assms by auto

lemma MMI_a3d: assumes A1: "\<phi> \<longrightarrow> 
   \<not>\<psi> \<longrightarrow> \<not>ch"   
   shows "\<phi> \<longrightarrow> ch \<longrightarrow> \<psi>"
   using assms by auto

lemma MMI_sylan9bbr: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch" and
    A2: "\<theta> \<longrightarrow> 
   ch \<longleftrightarrow> \<tau>"   
   shows "\<theta> \<and> \<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> \<tau>"
   using assms by auto

lemma MMI_sylan9bb: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch" and
    A2: "\<theta> \<longrightarrow> 
   ch \<longleftrightarrow> \<tau>"   
   shows "\<phi> \<and> \<theta> \<longrightarrow> 
   \<psi> \<longleftrightarrow> \<tau>"
   using assms by auto

lemma MMI_3bitr3g: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longleftrightarrow> ch" and
    A2: "\<psi> \<longleftrightarrow> \<theta>" and
    A3: "ch \<longleftrightarrow> \<tau>"   
   shows "\<phi> \<longrightarrow> 
   \<theta> \<longleftrightarrow> \<tau>"
   using assms by auto

lemma MMI_pm5_21: 
   shows "\<not>\<phi> \<and> \<not>\<psi> \<longrightarrow> 
   \<phi> \<longleftrightarrow> \<psi>"
  by auto

(******** lerectOLD - ltdiv23 ************)

lemma MMI_an6: 
   shows "(\<phi> \<and> \<psi> \<and> ch) \<and> \<theta> \<and> \<tau> \<and> \<eta> \<longleftrightarrow> 
   (\<phi> \<and> \<theta>) \<and> (\<psi> \<and> \<tau>) \<and> ch \<and> \<eta>"
  by auto

lemma MMI_syl3anl1: assumes A1: "(\<phi> \<and> \<psi> \<and> ch) \<and> \<theta> \<longrightarrow> \<tau>" and
    A2: "\<eta> \<longrightarrow> \<phi>"   
   shows "(\<eta> \<and> \<psi> \<and> ch) \<and> \<theta> \<longrightarrow> \<tau>"
   using assms by auto

lemma MMI_imp4a: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> 
   ch \<longrightarrow> 
   \<theta> \<longrightarrow> \<tau>"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> 
   ch \<and> \<theta> \<longrightarrow> \<tau>"
   using assms by auto

lemma (in MMIsar0) MMI_breqan12rd: assumes A1: "\<phi> \<longrightarrow> A = B" and
    A2: "\<psi> \<longrightarrow> C = D"   
   shows 
  "\<psi> \<and> \<phi> \<longrightarrow>  A \<ls> C \<longleftrightarrow> B \<ls> D"
  "\<psi> \<and> \<phi> \<longrightarrow>  A \<lsq> C \<longleftrightarrow> B \<lsq> D"
   using assms by auto

(****** lediv23t - halfpos ******************)

lemma (in MMIsar0) MMI_3brtr4d: assumes A1: "\<phi> \<longrightarrow> A \<ls> B" and
    A2: "\<phi> \<longrightarrow> C = A" and
    A3: "\<phi> \<longrightarrow> D = B"   
   shows "\<phi> \<longrightarrow> C \<ls> D"
   using assms by auto

lemma MMI_adantrrr: assumes A1: "\<phi> \<and> \<psi> \<and> ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<and> \<psi> \<and> ch \<and> \<tau> \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_adantrlr: assumes A1: "\<phi> \<and> \<psi> \<and> ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<and> (\<psi> \<and> \<tau>) \<and> ch \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_imdistani: assumes A1: "\<phi> \<longrightarrow> \<psi> \<longrightarrow> ch"   
   shows "\<phi> \<and> \<psi> \<longrightarrow> \<phi> \<and> ch"
   using assms by auto

lemma MMI_anabss3: assumes A1: "(\<phi> \<and> \<psi>) \<and> \<psi> \<longrightarrow> ch"   
   shows "\<phi> \<and> \<psi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_mp3anl2: assumes A1: "\<psi>" and
    A2: "(\<phi> \<and> \<psi> \<and> ch) \<and> \<theta> \<longrightarrow> \<tau>"   
   shows "(\<phi> \<and> ch) \<and> \<theta> \<longrightarrow> \<tau>"
   using assms by auto

(****** ledivp1t - squeeze0 ****************)

lemma MMI_mpanl2: assumes A1: "\<psi>" and
    A2: "(\<phi> \<and> \<psi>) \<and> ch \<longrightarrow> \<theta>"   
   shows "\<phi> \<and> ch \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_mpancom: assumes A1: "\<psi> \<longrightarrow> \<phi>" and
    A2: "\<phi> \<and> \<psi> \<longrightarrow> ch"   
   shows "\<psi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_or12: 
   shows "\<phi> \<or> \<psi> \<or> ch \<longleftrightarrow> \<psi> \<or> \<phi> \<or> ch"
  by auto

lemma MMI_rcla4ev: assumes A1: "\<forall>x. x = A \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<psi>"   
   shows "A \<in> B \<and> \<psi> \<longrightarrow> ( \<exists>x\<in>B. \<phi>(x) )"
   using assms by auto

lemma MMI_jctir: assumes A1: "\<phi> \<longrightarrow> \<psi>" and
    A2: "ch"   
   shows "\<phi> \<longrightarrow> \<psi> \<and> ch"
   using assms by auto

lemma MMI_iffalse: 
   shows "\<not>\<phi> \<longrightarrow>  if(\<phi>, A, B) = B"
  by auto

lemma MMI_iftrue: 
   shows "\<phi> \<longrightarrow>  if(\<phi>, A, B) = A"
  by auto

lemma MMI_pm2_61d2: assumes A1: "\<phi> \<longrightarrow> 
   \<not>\<psi> \<longrightarrow> ch" and
    A2: "\<psi> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_pm2_61dan: assumes A1: "\<phi> \<and> \<psi> \<longrightarrow> ch" and
    A2: "\<phi> \<and> \<not>\<psi> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_orcanai: assumes A1: "\<phi> \<longrightarrow> \<psi> \<or> ch"   
   shows "\<phi> \<and> \<not>\<psi> \<longrightarrow> ch"
   using assms by auto

lemma MMI_ifcl: 
   shows "A \<in> C \<and> B \<in> C \<longrightarrow>  if(\<phi>, A, B) \<in> C"
  by auto

lemma MMI_imim2i: assumes A1: "\<phi> \<longrightarrow> \<psi>"   
   shows "(ch \<longrightarrow> \<phi>) \<longrightarrow> ch \<longrightarrow> \<psi>"
   using assms by auto

lemma MMI_com13: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> ch \<longrightarrow> \<theta>"   
   shows "ch \<longrightarrow> 
   \<psi> \<longrightarrow> 
   \<phi> \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_rcla4v: assumes A1: "\<forall>x. x = A \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<psi>"   
   shows "A \<in> B \<longrightarrow>  (\<forall>x\<in>B. \<phi>(x)) \<longrightarrow> \<psi>"
   using assms by auto

lemma MMI_syl5d: assumes A1: "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> ch \<longrightarrow> \<theta>" and
    A2: "\<phi> \<longrightarrow> \<tau> \<longrightarrow> ch"   
   shows "\<phi> \<longrightarrow> 
   \<psi> \<longrightarrow> 
   \<tau> \<longrightarrow> \<theta>"
   using assms by auto

lemma MMI_eqcoms: assumes A1: "A = B \<longrightarrow> \<phi>"   
   shows "B = A \<longrightarrow> \<phi>"
   using assms by auto

(******* nnssre - nnex **************)

lemma MMI_rgen: assumes A1: "\<forall>x. x \<in> A \<longrightarrow> \<phi>(x)"   
   shows "\<forall>x\<in>A. \<phi>(x)"
   using assms by auto

lemma (in MMIsar0) MMI_reex: 
   shows "\<real> = \<real>"
  by auto

lemma MMI_sstri: assumes A1: "A \<subseteq>B" and
    A2: "B \<subseteq>C"   
   shows "A \<subseteq>C"
   using assms by auto

lemma MMI_ssexi: assumes A1: "B = B" and
    A2: "A \<subseteq>B"   
   shows "A = A"
   using assms by auto


end
