(* 
    This file is a part of MMIsar - a translation of Metamath's set.mm to Isabelle 2005 (ZF logic).

    Copyright (C) 2007  Slawomir Kolodynski

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

section \<open>Complex numbers in Metamatah 2\<close>

theory MMI_Complex_ZF_2 
imports MMI_logic_and_sets_1 MMI_Complex_ZF_1 InductiveSeq_ZF

begin

text\<open>This theory contains theorems (with proofs) about complex numbers
  imported from the Metamath's set.mm database. 
  The original Metamath proofs were mostly written by Norman Megill, 
  see the Metamath Proof Explorer pages for more detailed atribution.
  This theory contains about 100 theorems from \<open>1nn\<close> to \<open>infmrcl\<close>
\<close>

  (** proven by hand, really the definition of natural numbers *)

lemma (in MMIsar0) MMI_df_n: shows
  "\<nat> = \<Inter> {x\<in> Pow(\<real>). \<one> \<in> x \<and> (\<forall>y\<in>x. y \<ca> \<one> \<in> x) }"
proof -
  let ?K\<^sub>1 = "{N \<in> Pow(\<real>). \<one> \<in> N \<and> (\<forall>n. n\<in>N \<longrightarrow> n\<ca>\<one> \<in> N)}"
  let ?K\<^sub>2 = "{N \<in> Pow(\<real>). \<one> \<in> N \<and> (\<forall>n\<in>N. n\<ca>\<one> \<in> N)}"
  { fix N assume "N \<in> ?K\<^sub>1"
    hence "N \<in> Pow(\<real>)"   "\<one> \<in> N"   "\<forall>n. n\<in>N \<longrightarrow> n\<ca>\<one> \<in> N"
      by auto
    then have "N \<in> ?K\<^sub>2" by auto }
  moreover
  { fix N assume "N \<in> ?K\<^sub>2"
    hence "N \<in> Pow(\<real>)"   "\<one> \<in> N"   "\<forall>n\<in>N. n\<ca>\<one> \<in> N"
      by auto
    then have "N \<in> ?K\<^sub>1" by auto }
  ultimately have "?K\<^sub>1 = ?K\<^sub>2" by blast
  then show ?thesis using cxn_def by simp
qed

    (** a helper lemma that is needed bc. in Isabelle the intersection
    of empty set is pretty much undefined. To use the definition
    of natural numbers we need to show that we are intersecting a nonempty
    collection of sets. *)

lemma (in MMIsar0) MMI_Ndef_nonempty:
  shows "{x \<in> Pow(\<real>). \<one> \<in> x \<and> (\<forall>y\<in>x. y \<ca> \<one> \<in> x) } \<noteq> 0"
proof -
  have 
    "\<caddset> : ( \<complex> \<times> \<complex> ) \<rightarrow> \<complex>"   "\<real> \<subseteq> \<complex>"   and I: "\<one> \<in> \<real>"   
    using MMI_axaddopr MMI_axresscn MMI_ax1re by auto
  moreover from I have "\<forall>y\<in>\<real>. \<caddset>`\<langle>y,\<one>\<rangle> \<in> \<real>"
    using MMI_axaddrcl ca_def by simp
  ultimately have 
    "{x\<in> Pow(\<real>). \<one> \<in> x \<and> (\<forall>y\<in>x. \<caddset>`\<langle>y,\<one>\<rangle> \<in> x) } \<noteq> 0"
    using binop_gen_set_ex1 by auto
  then show ?thesis using ca_def by simp
qed

(** this corresponds to Metamath's 1nn. Proven by Isabelle.**)

lemma (in MMIsar0) MMI_1nn: shows "\<one> \<in> \<nat>"
  using MMI_df_n MMI_Ndef_nonempty by auto

(** 501, 502 ******************************************)

(*lemma (in MMIsar0) MMI_nnex: shows "\<nat> = \<nat>" by simp;

lemma (in MMIsar0) MMI_peano2nn: 
   shows "A \<in> \<nat> \<longrightarrow> A \<ca> \<one> \<in> \<nat>"
  using MMI_df_n MMI_Ndef_nonempty by auto;

proof -
   have S1: "z = A \<longrightarrow> 
   z \<ca> \<one> = A \<ca> \<one>" by (rule MMI_opreq1)
   from S1 have S2: "z = A \<longrightarrow> 
   z \<ca> \<one> \<in> \<nat> \<longleftrightarrow> A \<ca> \<one> \<in> \<nat>" by (rule MMI_eleq1d)
   have S3: "y = z \<longrightarrow> 
   y \<ca> \<one> = z \<ca> \<one>" by (rule MMI_opreq1)
   from S3 have S4: "y = z \<longrightarrow> 
   y \<ca> \<one> \<in> x \<longleftrightarrow> z \<ca> \<one> \<in> x" by (rule MMI_eleq1d)
   from S4 have S5: "(\<forall>y\<in>x. y \<ca> \<one> \<in> x) \<longrightarrow> 
   z \<in> x \<longrightarrow> z \<ca> \<one> \<in> x" by (rule MMI_rcla4cv)
   from S5 have S6: "\<one> \<in> x \<and> (\<forall>y\<in>x. y \<ca> \<one> \<in> x) \<longrightarrow> 
   z \<in> x \<longrightarrow> z \<ca> \<one> \<in> x" by (rule MMI_adantl)
   from S6 have S7: "(\<one> \<in> x \<and> (\<forall>y\<in>x. y \<ca> \<one> \<in> x) \<longrightarrow> z \<in> x) \<longrightarrow> 
   \<one> \<in> x \<and> (\<forall>y\<in>x. y \<ca> \<one> \<in> x) \<longrightarrow> z \<ca> \<one> \<in> x" by (rule MMI_a2i)
   from S7 have S8: "(\<forall>x. \<one> \<in> x \<and> (\<forall>y\<in>x. y \<ca> \<one> \<in> x) \<longrightarrow> z \<in> x) \<longrightarrow> 
   (\<forall>x. \<one> \<in> x \<and> (\<forall>y\<in>x. y \<ca> \<one> \<in> x) \<longrightarrow> z \<ca> \<one> \<in> x)" by (rule MMI_19_20i)
   have S9: "z = z" by (rule MMI_visset)
   from S9 have S10: "z \<in> \<Inter> {x\<in> Pow(\<real>). \<one> \<in> x \<and> (\<forall>y\<in>x. y \<ca> \<one> \<in> x) } \<longleftrightarrow> 
   (\<forall>x. \<one> \<in> x \<and> (\<forall>y\<in>x. y \<ca> \<one> \<in> x) \<longrightarrow> z \<in> x)" by (rule MMI_elintab)
   have S11: "z \<ca> \<one> = z \<ca> \<one>" by (rule MMI_oprex)
   from S11 have S12: "z \<ca> \<one> \<in> \<Inter> {x\<in> Pow(\<real>). \<one> \<in> x \<and> (\<forall>y\<in>x. y \<ca> \<one> \<in> x) } \<longleftrightarrow> 
   (\<forall>x. \<one> \<in> x \<and> (\<forall>y\<in>x. y \<ca> \<one> \<in> x) \<longrightarrow> z \<ca> \<one> \<in> x)" by (rule MMI_elintab)
   from S8 S10 S12 have S13: "z \<in> \<Inter> {x\<in> Pow(\<real>). \<one> \<in> x \<and> (\<forall>y\<in>x. y \<ca> \<one> \<in> x) } \<longrightarrow> 
   z \<ca> \<one> \<in> \<Inter> {x\<in> Pow(\<real>). \<one> \<in> x \<and> (\<forall>y\<in>x. y \<ca> \<one> \<in> x) }" by (rule MMI_3imtr4)
   have S14: "\<nat> = \<Inter> {x\<in> Pow(\<real>). \<one> \<in> x \<and> (\<forall>y\<in>x. y \<ca> \<one> \<in> x) }" by (rule MMI_df_n)
   from S14 have S15: "z \<in> \<nat> \<longleftrightarrow> 
   z \<in> \<Inter> {x\<in> Pow(\<real>). \<one> \<in> x \<and> (\<forall>y\<in>x. y \<ca> \<one> \<in> x) }" by (rule MMI_eleq2i)
   from S14 have S16: "\<nat> = \<Inter> {x\<in> Pow(\<real>). \<one> \<in> x \<and> (\<forall>y\<in>x. y \<ca> \<one> \<in> x) }" .
   from S16 have S17: "z \<ca> \<one> \<in> \<nat> \<longleftrightarrow> 
   z \<ca> \<one> \<in> \<Inter> {x\<in> Pow(\<real>). \<one> \<in> x \<and> (\<forall>y\<in>x. y \<ca> \<one> \<in> x) }" by (rule MMI_eleq2i)
   from S13 S15 S17 have S18: "z \<in> \<nat> \<longrightarrow> z \<ca> \<one> \<in> \<nat>" by (rule MMI_3imtr4)
   from S2 S18 show "A \<in> \<nat> \<longrightarrow> A \<ca> \<one> \<in> \<nat>" by (rule MMI_vtoclga)
qed the original proof **)

(** first attempt, true, but not what needed **)
lemma (in MMIsar0) MMI_nnind0: 
    assumes A1: "\<forall>x. x = \<one> \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<psi>(x)" and
    A2: "\<forall>y x. x = y \<longrightarrow>  \<phi>(x) \<longleftrightarrow> ch(x\<ca>\<one>)" and
    A3: "\<forall>y x. x = y \<ca> \<one> \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<theta>(x)" and
    A4: "\<forall>x. x = A \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<tau>(x)" and
    A5: "\<psi>(\<one>)" and
    A6: "\<forall>y. y \<in> \<nat> \<longrightarrow> ch(y\<ca>\<one>) \<longrightarrow> \<theta>(y\<ca>\<one>)"   
   shows "A \<in> \<nat> \<longrightarrow> \<tau>(A)"
proof -
   from A1 have S1: "\<forall>x. x = \<one> \<longrightarrow>   \<phi>(x) \<longleftrightarrow> \<psi>(x)".
   from S1 have S2: "\<one> \<in> {x \<in> \<nat>. \<phi>(x) } \<longleftrightarrow> \<one> \<in> \<nat> \<and> \<psi>(\<one>)" by (rule MMI_elrab)
   have S3: "\<one> \<in> \<nat>" by (rule MMI_1nn)
   from A5 have S4: "\<psi>(\<one>)".
   from S2 S3 S4 have S5: "\<one> \<in> {x \<in> \<nat>. \<phi>(x) }" by (rule MMI_mpbir2an)
   have S6: "{x \<in> \<nat>. \<phi>(x) } \<subseteq>\<nat>" by (rule MMI_ssrab2)
   { fix y
     from S6 have S7: "y \<in> {x \<in> \<nat>. \<phi>(x) } \<longrightarrow> y \<in> \<nat>" by (rule MMI_sseli)
     have S8: "y \<in> \<nat> \<longrightarrow> y \<ca> \<one> \<in> \<nat>" by (rule MMI_peano2nn)
     from S8 have S9: "y \<in> \<nat> \<longrightarrow>  y \<in> \<nat> \<longrightarrow> y \<ca> \<one> \<in> \<nat>" by (rule MMI_a1d)
     from A6 have S10: "y \<in> \<nat> \<longrightarrow> ch(y\<ca>\<one>) \<longrightarrow> \<theta>(y\<ca>\<one>)" by simp
     from S9 S10 have S11: "y \<in> \<nat> \<longrightarrow>  y \<in> \<nat> \<and> ch(y\<ca>\<one>) \<longrightarrow>  y \<ca> \<one> \<in> \<nat> \<and> \<theta>(y\<ca>\<one>)" 
       by (rule MMI_anim12d)
     from A2 have S12: "\<forall> x. x = y \<longrightarrow>  \<phi>(x) \<longleftrightarrow> ch(x\<ca>\<one>)" by simp
     from S12 have S13: "y \<in> {x \<in> \<nat>. \<phi>(x) } \<longleftrightarrow> y \<in> \<nat> \<and> ch(y\<ca>\<one>)" by (rule MMI_elrab)
     from A3 have S14: "\<forall> x. x = y \<ca> \<one> \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<theta>(x)" by simp
     from S14 have S15: "y \<ca> \<one> \<in> {x \<in> \<nat>. \<phi>(x) } \<longleftrightarrow>  y \<ca> \<one> \<in> \<nat> \<and> \<theta>(y\<ca>\<one>)" 
       by (rule MMI_elrab)
     from S11 S13 S15 have S16: 
       "y \<in> \<nat> \<longrightarrow>  y \<in> {x \<in> \<nat>. \<phi>(x) } \<longrightarrow>  y \<ca> \<one> \<in> {x \<in> \<nat>. \<phi>(x) }" by (rule MMI_3imtr4g)
   from S7 S16 have S17: "y \<in> {x \<in> \<nat>. \<phi>(x) } \<longrightarrow>  y \<ca> \<one> \<in> {x \<in> \<nat>. \<phi>(x) }" 
     by (rule MMI_mpcom) }
   then have S17: "\<forall>y. y \<in> {x \<in> \<nat>. \<phi>(x) } \<longrightarrow>  y \<ca> \<one> \<in> {x \<in> \<nat>. \<phi>(x) }"
     by simp
   from S17 have S18: "\<forall>y\<in>{x \<in> \<nat>. \<phi>(x) }. y \<ca> \<one> \<in> {x \<in> \<nat>. \<phi>(x) }" by (rule MMI_rgen)
   have S19: "\<nat> = \<nat>" by (rule MMI_nnex)
   from S19 have S20: "{x \<in> \<nat>. \<phi>(x) } = {x \<in> \<nat>. \<phi>(x) }" by (rule MMI_rabex)
   from S20 have S21: "\<one> \<in> {x \<in> \<nat>. \<phi>(x) } \<and> (\<forall>y\<in>{x \<in> \<nat>. \<phi>(x) }. y \<ca> \<one> \<in> {x \<in> \<nat>. \<phi>(x) }) \<longrightarrow> 
   \<nat> \<subseteq>{x \<in> \<nat>. \<phi>(x) }" by (rule MMI_peano5nn)
   from S5 S18 S21 have S22: "\<nat> \<subseteq>{x \<in> \<nat>. \<phi>(x) }" by (rule MMI_mp2an)
   from S22 have S23: "A \<in> \<nat> \<longrightarrow>  A \<in> {x \<in> \<nat>. \<phi>(x) }" by (rule MMI_sseli)
   from A4 have S24: "\<forall>x. x = A \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<tau>(x)" .
   from S24 have S25: "A \<in> {x \<in> \<nat>. \<phi>(x) } \<longleftrightarrow> A \<in> \<nat> \<and> \<tau>(A)" by (rule MMI_elrab)
   from S23 S25 have S26: "A \<in> \<nat> \<longrightarrow> A \<in> \<nat> \<and> \<tau>(A)" by (rule MMI_sylib)
   from S26 show "A \<in> \<nat> \<longrightarrow> \<tau>(A)" by (rule MMI_pm3_27d)
qed

(** this version is needed, at least in nnaddclt **************)
lemma (in MMIsar0) MMI_nnind: 
    assumes A1: "\<forall>x. x = \<one> \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<psi>(\<one>)" and
    A2: "\<forall>x y. x = y \<longrightarrow>  \<phi>(x) \<longleftrightarrow> ch(y)" and
    A3: "\<forall>x y. x = y \<ca> \<one> \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<theta>(y\<ca>\<one>)" and
    A4: "\<forall>x. x = B \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<tau>(B)" and
    A5: "\<psi>(\<one>)" and
    A6: "\<forall>y. y \<in> \<nat> \<longrightarrow> ch(y) \<longrightarrow> \<theta>(y\<ca>\<one>)"   
   shows "B \<in> \<nat> \<longrightarrow> \<tau>(B)"
proof -
   from A1 have S1: "\<forall>x. x = \<one> \<longrightarrow>   \<phi>(x) \<longleftrightarrow> \<psi>(\<one>)".
   from S1 have S2: "\<one> \<in> {x \<in> \<nat>. \<phi>(x) } \<longleftrightarrow> \<one> \<in> \<nat> \<and> \<psi>(\<one>)" by (rule MMI_elrab)
   have S3: "\<one> \<in> \<nat>" by (rule MMI_1nn)
   from A5 have S4: "\<psi>(\<one>)".
   from S2 S3 S4 have S5: "\<one> \<in> {x \<in> \<nat>. \<phi>(x) }" by (rule MMI_mpbir2an)
   have S6: "{x \<in> \<nat>. \<phi>(x) } \<subseteq> \<nat>" by (rule MMI_ssrab2)
   { fix y
     from S6 have S7: "y \<in> {x \<in> \<nat>. \<phi>(x) } \<longrightarrow> y \<in> \<nat>" by (rule MMI_sseli)
     have S8: "y \<in> \<nat> \<longrightarrow> y \<ca> \<one> \<in> \<nat>" by (rule MMI_peano2nn)
     from S8 have S9: "y \<in> \<nat> \<longrightarrow>  y \<in> \<nat> \<longrightarrow> y \<ca> \<one> \<in> \<nat>" by (rule MMI_a1d)
     from A6 have S10: "y \<in> \<nat> \<longrightarrow> ch(y) \<longrightarrow> \<theta>(y\<ca>\<one>)" by simp
     from S9 S10 have S11: "y \<in> \<nat> \<longrightarrow>  y \<in> \<nat> \<and> ch(y) \<longrightarrow>  y \<ca> \<one> \<in> \<nat> \<and> \<theta>(y\<ca>\<one>)" 
       by (rule MMI_anim12d)
     from A2 have S12: "\<forall> x. x = y \<longrightarrow>  \<phi>(x) \<longleftrightarrow> ch(y)" by simp
     from S12 have S13: "y \<in> {x \<in> \<nat>. \<phi>(x) } \<longleftrightarrow> y \<in> \<nat> \<and> ch(y)" by (rule MMI_elrab)
     from A3 have S14: "\<forall> x. x = y \<ca> \<one> \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<theta>(y\<ca>\<one>)" by simp
     from S14 have S15: "y \<ca> \<one> \<in> {x \<in> \<nat>. \<phi>(x) } \<longleftrightarrow>  y \<ca> \<one> \<in> \<nat> \<and> \<theta>(y\<ca>\<one>)" 
       by (rule MMI_elrab)
     from S11 S13 S15 have S16: 
       "y \<in> \<nat> \<longrightarrow>  y \<in> {x \<in> \<nat>. \<phi>(x) } \<longrightarrow>  y \<ca> \<one> \<in> {x \<in> \<nat>. \<phi>(x) }" by (rule MMI_3imtr4g)
   from S7 S16 have "y \<in> {x \<in> \<nat>. \<phi>(x) } \<longrightarrow>  y \<ca> \<one> \<in> {x \<in> \<nat>. \<phi>(x) }" 
     by (rule MMI_mpcom) }
   then have S17: "\<forall>y. y \<in> {x \<in> \<nat>. \<phi>(x) } \<longrightarrow>  y \<ca> \<one> \<in> {x \<in> \<nat>. \<phi>(x) }"
     by simp
   from S17 have S18: "\<forall>y\<in>{x \<in> \<nat>. \<phi>(x) }. y \<ca> \<one> \<in> {x \<in> \<nat>. \<phi>(x) }" by (rule MMI_rgen)
   have S19: "\<nat> = \<nat>" by (rule MMI_nnex)
   from S19 have S20: "{x \<in> \<nat>. \<phi>(x) } = {x \<in> \<nat>. \<phi>(x) }" by (rule MMI_rabex)
   from S20 have S21: 
     "\<one> \<in> {x \<in> \<nat>. \<phi>(x) } \<and> (\<forall>y\<in>{x \<in> \<nat>. \<phi>(x) }. y \<ca> \<one> \<in> {x \<in> \<nat>. \<phi>(x) }) \<longrightarrow> 
     \<nat> \<subseteq>{x \<in> \<nat>. \<phi>(x) }" by (rule MMI_peano5nn)
   from S5 S18 S21 have S22: "\<nat> \<subseteq>{x \<in> \<nat>. \<phi>(x) }" by (rule MMI_mp2an)
   from S22 have S23: "B \<in> \<nat> \<longrightarrow>  B \<in> {x \<in> \<nat>. \<phi>(x) }" by (rule MMI_sseli)
   from A4 have S24: "\<forall>x. x = B \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<tau>(B)" .
   from S24 have S25: "B \<in> {x \<in> \<nat>. \<phi>(x) } \<longleftrightarrow> B \<in> \<nat> \<and> \<tau>(B)" by (rule MMI_elrab)
   from S23 S25 have S26: "B \<in> \<nat> \<longrightarrow> B \<in> \<nat> \<and> \<tau>(B)" by (rule MMI_sylib)
   from S26 show "B \<in> \<nat> \<longrightarrow> \<tau>(B)" by (rule MMI_pm3_27d)
qed

text\<open>Induction - on (real) natural numbers -  version for humans.\<close>

corollary (in MMIsar0) nnind1: 
  assumes A1: "\<psi>(\<one>)" and 
  A2: "\<forall>k \<in> \<nat>. \<psi>(k) \<longrightarrow> \<psi>(k\<ca>\<one>)" and
  A3: "n \<in> \<nat>"
  shows "\<psi>(n)"
proof -
  have "\<forall>x. x = \<one> \<longrightarrow>  \<psi>(x) \<longleftrightarrow> \<psi>(\<one>)" by simp
  moreover have "\<forall>x y. x = y \<longrightarrow>  \<psi>(x) \<longleftrightarrow> \<psi>(y)" by simp
  moreover have "\<forall>x y. x = y \<ca> \<one> \<longrightarrow>  \<psi>(x) \<longleftrightarrow> \<psi>(y\<ca>\<one>)" by simp
  moreover have "\<forall>x. x = n \<longrightarrow>  \<psi>(x) \<longleftrightarrow> \<psi>(n)" by simp
  moreover note A1
  moreover from A2 have "\<forall>k. k \<in> \<nat> \<longrightarrow> \<psi>(k) \<longrightarrow> \<psi>(k\<ca>\<one>)" by blast
  ultimately have "n \<in> \<nat> \<longrightarrow> \<psi>(n)" by (rule MMI_nnind)
  with A3 show "\<psi>(n)" by simp
qed
(* I have no idea what this theorem even means

lemma (in MMIsar0) MMI_nn1suc: assumes A1: "x = \<one> \<longrightarrow> 
   \<phi> \<longleftrightarrow> \<psi>" and
    A3: "x = y \<ca> \<one> \<longrightarrow> 
   \<phi> \<longleftrightarrow> ch" and
    A4: "x = A \<longrightarrow> 
   \<phi> \<longleftrightarrow> \<theta>" and
    A5: "\<psi>" and
    A6: "y \<in> \<nat> \<longrightarrow> ch"   
   shows "A \<in> \<nat> \<longrightarrow> \<theta>"
proof -
   have S1: "z = \<one> \<longrightarrow> 
   [ z / x ] (A \<in> \<nat> \<longrightarrow> \<phi>) \<longleftrightarrow> 
   [ \<one> / x ] (A \<in> \<nat> \<longrightarrow> \<phi>)" by (rule MMI_dfsbcq)
   have S2: "z = y \<longrightarrow> 
   [ z / x ] (A \<in> \<nat> \<longrightarrow> \<phi>) \<longleftrightarrow> 
   [ y / x ] (A \<in> \<nat> \<longrightarrow> \<phi>)" by (rule MMI_sbequ)
   have S3: "z = y \<ca> \<one> \<longrightarrow> 
   [ z / x ] (A \<in> \<nat> \<longrightarrow> \<phi>) \<longleftrightarrow> 
   [ y \<ca> \<one> / x ] (A \<in> \<nat> \<longrightarrow> \<phi>)" by (rule MMI_dfsbcq)
   have S4: "z = A \<longrightarrow> 
   [ z / x ] \<phi> \<longleftrightarrow> [ A / x ] \<phi>" by (rule MMI_dfsbcq)
   have S5: "A \<in> \<nat> \<longrightarrow> ( \<exists>x. x = A)" by (rule MMI_elex)
   have S6: "z \<in> A \<longrightarrow> (\<forall>x. z \<in> A)" by (rule MMI_ax_17)
   from S6 have S7: "(A \<in> \<nat> \<longrightarrow> [ A / x ] \<phi>) \<longrightarrow> 
   (\<forall>x. A \<in> \<nat> \<longrightarrow> [ A / x ] \<phi>)" by (rule MMI_hbsbc1)
   have S8: "(A \<in> \<nat> \<longrightarrow> \<theta>) \<longrightarrow> 
   (\<forall>x. A \<in> \<nat> \<longrightarrow> \<theta>)" by (rule MMI_ax_17)
   from S7 S8 have S9: "(A \<in> \<nat> \<longrightarrow> [ A / x ] \<phi>) \<longleftrightarrow> 
   (A \<in> \<nat> \<longrightarrow> \<theta>) \<longrightarrow> 
   (\<forall>x. (A \<in> \<nat> \<longrightarrow> [ A / x ] \<phi>) \<longleftrightarrow> 
   (A \<in> \<nat> \<longrightarrow> \<theta>))" by (rule MMI_hbbi)
   have S10: "x = A \<longrightarrow> 
   \<phi> \<longleftrightarrow> [ A / x ] \<phi>" by (rule MMI_sbceq1a)
   from A4 have S11: "x = A \<longrightarrow> 
   \<phi> \<longleftrightarrow> \<theta>".
   from S10 S11 have S12: "x = A \<longrightarrow> 
   [ A / x ] \<phi> \<longleftrightarrow> \<theta>" by (rule MMI_bitr3d)
   from S12 have S13: "x = A \<longrightarrow> 
   (A \<in> \<nat> \<longrightarrow> [ A / x ] \<phi>) \<longleftrightarrow> 
   (A \<in> \<nat> \<longrightarrow> \<theta>)" by (rule MMI_imbi2d)
   from S9 S13 have S14: "( \<exists>x. x = A) \<longrightarrow> 
   (A \<in> \<nat> \<longrightarrow> [ A / x ] \<phi>) \<longleftrightarrow> 
   (A \<in> \<nat> \<longrightarrow> \<theta>)" by (rule MMI_19_23ai)
   from S5 S14 have S15: "A \<in> \<nat> \<longrightarrow> 
   (A \<in> \<nat> \<longrightarrow> [ A / x ] \<phi>) \<longleftrightarrow> 
   (A \<in> \<nat> \<longrightarrow> \<theta>)" by (rule MMI_syl)
   from S15 have S16: "A \<in> \<nat> \<longrightarrow> 
   A \<in> \<nat> \<longrightarrow> 
   [ A / x ] \<phi> \<longleftrightarrow> \<theta>" by (rule MMI_pm5_74rd)
   from S16 have S17: "A \<in> \<nat> \<longrightarrow> 
   [ A / x ] \<phi> \<longleftrightarrow> \<theta>" by (rule MMI_pm2_43i)
   from S4 S17 have S18: "A \<in> \<nat> \<and> z = A \<longrightarrow> 
   [ z / x ] \<phi> \<longleftrightarrow> \<theta>" by (rule MMI_sylan9bbr)
   from S18 have S19: "z = A \<longrightarrow> 
   A \<in> \<nat> \<longrightarrow> 
   [ z / x ] \<phi> \<longleftrightarrow> \<theta>" by (rule MMI_expcom)
   from S19 have S20: "z = A \<longrightarrow> 
   (A \<in> \<nat> \<longrightarrow> [ z / x ] \<phi>) \<longleftrightarrow> 
   (A \<in> \<nat> \<longrightarrow> \<theta>)" by (rule MMI_pm5_74d)
   have S21: "A \<in> \<nat> \<longrightarrow> (\<forall>x. A \<in> \<nat>)" by (rule MMI_ax_17)
   from S21 have S22: "[ z / x ] (A \<in> \<nat> \<longrightarrow> \<phi>) \<longleftrightarrow> 
   (A \<in> \<nat> \<longrightarrow> [ z / x ] \<phi>)" by (rule MMI_sb19_21)
   from S20 S22 have S23: "z = A \<longrightarrow> 
   [ z / x ] (A \<in> \<nat> \<longrightarrow> \<phi>) \<longleftrightarrow> 
   (A \<in> \<nat> \<longrightarrow> \<theta>)" by (rule MMI_syl5bb)
   have S24: "\<one> \<in> \<nat>" by (rule MMI_1nn)
   from S24 have S25: "\<one> = \<one>" by (rule MMI_elisseti)
   from S25 have S26: " \<exists>x. x = \<one>" by (rule MMI_isseti)
   from S25 have S27: "\<one> = \<one>" .
   from S27 have S28: "[ \<one> / x ] \<phi> \<longrightarrow> 
   (\<forall>x. [ \<one> / x ] \<phi>)" by (rule MMI_hbsbc1v)
   from A5 have S29: "\<psi>".
   from A1 have S30: "x = \<one> \<longrightarrow> 
   \<phi> \<longleftrightarrow> \<psi>".
   from S29 S30 have S31: "x = \<one> \<longrightarrow> \<phi>" by (rule MMI_mpbiri)
   have S32: "x = \<one> \<longrightarrow> 
   \<phi> \<longleftrightarrow> [ \<one> / x ] \<phi>" by (rule MMI_sbceq1a)
   from S31 S32 have S33: "x = \<one> \<longrightarrow> [ \<one> / x ] \<phi>" by (rule MMI_mpbid)
   from S28 S33 have S34: "( \<exists>x. x = \<one>) \<longrightarrow> [ \<one> / x ] \<phi>" by (rule MMI_19_23ai)
   from S26 S34 have S35: "[ \<one> / x ] \<phi>" by (rule MMI_ax_mp)
   from S35 have S36: "A \<in> \<nat> \<longrightarrow> [ \<one> / x ] \<phi>" by (rule MMI_a1i)
   from S25 have S37: "\<one> = \<one>" .
   from S21 have S38: "A \<in> \<nat> \<longrightarrow> (\<forall>x. A \<in> \<nat>)" .
   from S38 have S39: "\<one> = \<one> \<longrightarrow> 
   [ \<one> / x ] (A \<in> \<nat> \<longrightarrow> \<phi>) \<longleftrightarrow> 
   (A \<in> \<nat> \<longrightarrow> [ \<one> / x ] \<phi>)" by (rule MMI_sbc19_21g)
   from S37 S39 have S40: "[ \<one> / x ] (A \<in> \<nat> \<longrightarrow> \<phi>) \<longleftrightarrow> 
   (A \<in> \<nat> \<longrightarrow> [ \<one> / x ] \<phi>)" by (rule MMI_ax_mp)
   from S36 S40 have S41: "[ \<one> / x ] (A \<in> \<nat> \<longrightarrow> \<phi>)" by (rule MMI_mpbir)
   from A6 have S42: "y \<in> \<nat> \<longrightarrow> ch".
   have S43: "y \<ca> \<one> = y \<ca> \<one>" by (rule MMI_oprex)
   from S43 have S44: " \<exists>x. x = y \<ca> \<one>" by (rule MMI_isseti)
   have S45: "ch \<longrightarrow> (\<forall>x. ch)" by (rule MMI_ax_17)
   from S43 have S46: "y \<ca> \<one> = y \<ca> \<one>" .
   from S46 have S47: "[ y \<ca> \<one> / x ] \<phi> \<longrightarrow> 
   (\<forall>x. [ y \<ca> \<one> / x ] \<phi>)" by (rule MMI_hbsbc1v)
   from S45 S47 have S48: "ch \<longleftrightarrow> [ y \<ca> \<one> / x ] \<phi> \<longrightarrow> 
   (\<forall>x. ch \<longleftrightarrow> [ y \<ca> \<one> / x ] \<phi>)" by (rule MMI_hbbi)
   from A3 have S49: "x = y \<ca> \<one> \<longrightarrow> 
   \<phi> \<longleftrightarrow> ch".
   have S50: "x = y \<ca> \<one> \<longrightarrow> 
   \<phi> \<longleftrightarrow> [ y \<ca> \<one> / x ] \<phi>" by (rule MMI_sbceq1a)
   from S49 S50 have S51: "x = y \<ca> \<one> \<longrightarrow> 
   ch \<longleftrightarrow> [ y \<ca> \<one> / x ] \<phi>" by (rule MMI_bitr3d)
   from S48 S51 have S52: "( \<exists>x. x = y \<ca> \<one>) \<longrightarrow> 
   ch \<longleftrightarrow> [ y \<ca> \<one> / x ] \<phi>" by (rule MMI_19_23ai)
   from S44 S52 have S53: "ch \<longleftrightarrow> [ y \<ca> \<one> / x ] \<phi>" by (rule MMI_ax_mp)
   from S42 S53 have S54: "y \<in> \<nat> \<longrightarrow> [ y \<ca> \<one> / x ] \<phi>" by (rule MMI_sylib)
   from S54 have S55: "y \<in> \<nat> \<longrightarrow> 
   A \<in> \<nat> \<longrightarrow> [ y \<ca> \<one> / x ] \<phi>" by (rule MMI_a1d)
   from S43 have S56: "y \<ca> \<one> = y \<ca> \<one>" .
   from S21 have S57: "A \<in> \<nat> \<longrightarrow> (\<forall>x. A \<in> \<nat>)" .
   from S57 have S58: "y \<ca> \<one> = y \<ca> \<one> \<longrightarrow> 
   [ y \<ca> \<one> / x ] (A \<in> \<nat> \<longrightarrow> \<phi>) \<longleftrightarrow> 
   (A \<in> \<nat> \<longrightarrow> [ y \<ca> \<one> / x ] \<phi>)" by (rule MMI_sbc19_21g)
   from S56 S58 have S59: "[ y \<ca> \<one> / x ] (A \<in> \<nat> \<longrightarrow> \<phi>) \<longleftrightarrow> 
   (A \<in> \<nat> \<longrightarrow> [ y \<ca> \<one> / x ] \<phi>)" by (rule MMI_ax_mp)
   from S55 S59 have S60: "y \<in> \<nat> \<longrightarrow> 
   [ y \<ca> \<one> / x ] (A \<in> \<nat> \<longrightarrow> \<phi>)" by (rule MMI_sylibr)
   from S60 have S61: "y \<in> \<nat> \<longrightarrow> 
   [ y / x ] (A \<in> \<nat> \<longrightarrow> \<phi>) \<longrightarrow> 
   [ y \<ca> \<one> / x ] (A \<in> \<nat> \<longrightarrow> \<phi>)" by (rule MMI_a1d)
   from S1 S2 S3 S23 S41 S61 have S62: "A \<in> \<nat> \<longrightarrow> 
   A \<in> \<nat> \<longrightarrow> \<theta>" by (rule MMI_nnind)
   from S62 show "A \<in> \<nat> \<longrightarrow> \<theta>" by (rule MMI_pm2_43i)
qed*)
lemma (in MMIsar0) MMI_nn1suc: assumes 
  A1: "\<forall>x. x = \<one> \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<psi>(\<one>)" and
  A3: "\<forall>x y. x = y \<ca> \<one> \<longrightarrow>  \<phi>(x) \<longleftrightarrow> ch(y\<ca>\<one>)" and
  A4: "\<forall>x. x = A \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<theta>(A)" and
  A5: "\<psi>(\<one>)" and
  A6: "\<forall>y. y \<in> \<nat> \<longrightarrow> ch(y\<ca>\<one>)"   
   shows "A \<in> \<nat> \<longrightarrow> \<theta>(A)"
proof -
  have S1: "\<forall> z. z = \<one> \<longrightarrow> (A \<in> \<nat> \<longrightarrow> \<phi>(z)) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> \<phi>(\<one>))" by auto(*(rule MMI_dfsbcq);*)
  have S2: "\<forall>z y. z = y \<longrightarrow> (A \<in> \<nat> \<longrightarrow> \<phi>(z)) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> \<phi>(y))" by auto (*(rule MMI_sbequ);*)
  have S3: "\<forall>z y. z = y \<ca> \<one> \<longrightarrow>  (A \<in> \<nat> \<longrightarrow> \<phi>(z)) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> \<phi>(y\<ca>\<one>))" 
    by auto (*(rule MMI_dfsbcq)*)
  { fix z 
    have S4: "z = A \<longrightarrow>  \<phi>(z) \<longleftrightarrow> \<phi>(A)" by auto (*(rule MMI_dfsbcq)*)
    have S5: "A \<in> \<nat> \<longrightarrow> ( \<exists>x. x = A)" by (rule MMI_elex)
    have S6: "z \<in> A \<longrightarrow> (\<forall>x. z \<in> A)" by (rule MMI_ax_17)
    from S6 have S7: "(A \<in> \<nat> \<longrightarrow> \<phi>(A)) \<longrightarrow> (\<forall>x. A \<in> \<nat> \<longrightarrow> \<phi>(A))" by auto (*(rule MMI_hbsbc1)*)
    have S8: "(A \<in> \<nat> \<longrightarrow> \<theta>(A)) \<longrightarrow> (\<forall>x. A \<in> \<nat> \<longrightarrow> \<theta>(A))" by (rule MMI_ax_17)
    have S9: 
      "((A \<in> \<nat> \<longrightarrow> \<phi>(A)) \<longleftrightarrow>  (A \<in> \<nat> \<longrightarrow> \<theta>(A))) \<longrightarrow>  (\<forall>x. (A \<in> \<nat> \<longrightarrow> \<phi>(A)) \<longleftrightarrow> 
      (A \<in> \<nat> \<longrightarrow> \<theta>(A)))" by auto
    have S10: "\<forall>x. x = A \<longrightarrow> \<phi>(x) \<longleftrightarrow> \<phi>(A)" by auto (*(rule MMI_sbceq1a)*)
    from A4 have S11: "\<forall>x. x = A \<longrightarrow> \<phi>(x) \<longleftrightarrow> \<theta>(A)".
    from S10 S11 have S12: "\<forall> x. x = A \<longrightarrow> \<phi>(x) \<longleftrightarrow> \<theta>(A)" by auto (*(rule MMI_bitr3d);*)
    from S12 have S13: "\<forall>x. x = A \<longrightarrow> (A \<in> \<nat> \<longrightarrow> \<phi>(x)) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> \<theta>(A))" by auto (*(rule MMI_imbi2d);*)
    from S9 S13 have S14: "( \<exists>x. x = A) \<longrightarrow>  (A \<in> \<nat> \<longrightarrow> \<phi>(A)) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> \<theta>(A))" 
      by auto (*(rule MMI_19_23ai)*)
    from S5 S14 have S15: "A \<in> \<nat> \<longrightarrow> (A \<in> \<nat> \<longrightarrow> \<phi>(A)) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> \<theta>(A))" by (rule MMI_syl)
    from S15 have S16: "A \<in> \<nat> \<longrightarrow>  A \<in> \<nat> \<longrightarrow> \<phi>(A) \<longleftrightarrow> \<theta>(A)" by (rule MMI_pm5_74rd)
    from S16 have S17: "A \<in> \<nat> \<longrightarrow> \<phi>(A) \<longleftrightarrow> \<theta>(A)" by (rule MMI_pm2_43i)
    from S4 S17 have S18: "A \<in> \<nat> \<and> z = A \<longrightarrow> \<phi>(z) \<longleftrightarrow> \<theta>(A)" by (rule MMI_sylan9bbr)
    from S18 have S19: "z = A \<longrightarrow>  A \<in> \<nat> \<longrightarrow> \<phi>(z) \<longleftrightarrow> \<theta>(A)" by (rule MMI_expcom)
    from S19 have S20: "z = A \<longrightarrow>  (A \<in> \<nat> \<longrightarrow> \<phi>(z)) \<longleftrightarrow>  (A \<in> \<nat> \<longrightarrow> \<theta>(A))" 
      by (rule MMI_pm5_74d)
    have S21: "A \<in> \<nat> \<longrightarrow> (\<forall>x. A \<in> \<nat>)" by (rule MMI_ax_17)
    from S21 have S22: "(A \<in> \<nat> \<longrightarrow> \<phi>(z)) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> \<phi>(z))" by auto (*(rule MMI_sb19_21)*)
    from S20 S22 have "z = A \<longrightarrow>  (A \<in> \<nat> \<longrightarrow> \<phi>(z)) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> \<theta>(A))" 
      by (rule MMI_syl5bb)
  } then have S23: "\<forall>z. z = A \<longrightarrow>  (A \<in> \<nat> \<longrightarrow> \<phi>(z)) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> \<theta>(A))"
    by simp
   have S24: "\<one> \<in> \<nat>" by (rule MMI_1nn)
   from S24 have S25: "\<one> = \<one>" by simp (*(rule MMI_elisseti);*)
   from S25 have S26: " \<exists>x. x = \<one>" by (rule MMI_isseti)
   from S25 have S27: "\<one> = \<one>" .
   from S27 have S28: "\<phi>(\<one>) \<longrightarrow>  (\<forall>x. \<phi>(\<one>))" by simp (*(rule MMI_hbsbc1v);*)
   from A5 have S29: "\<psi>(\<one>)".
   from A1 have S30: "\<forall> x. x = \<one> \<longrightarrow> \<phi>(x) \<longleftrightarrow> \<psi>(\<one>)".
   from S29 S30 have S31: "\<forall>x. x = \<one> \<longrightarrow> \<phi>(x)" by simp (*(rule MMI_mpbiri);*)
   have S32: "\<forall> x. x = \<one> \<longrightarrow> \<phi>(x) \<longleftrightarrow> \<phi>(\<one>)" by simp (*(rule MMI_sbceq1a);*)
   from S31 S32 have S33: "\<forall>x. x = \<one> \<longrightarrow> \<phi>(\<one>)" by blast (*(rule MMI_mpbid);*)
   from S28 S33 have S34: "( \<exists>x. x = \<one>) \<longrightarrow> \<phi>(\<one>)" by auto (*(rule MMI_19_23ai);*)
   from S26 S34 have S35: "\<phi>(\<one>)" by (rule MMI_ax_mp)
   from S35 have S36: "A \<in> \<nat> \<longrightarrow> \<phi>(\<one>)" by (rule MMI_a1i)
   from S25 have S37: "\<one> = \<one>" .
   have S38: "A \<in> \<nat> \<longrightarrow> (\<forall>x. A \<in> \<nat>)" by (rule MMI_ax_17)
   from S38 have S39: "\<one> = \<one> \<longrightarrow> (A \<in> \<nat> \<longrightarrow> \<phi>(\<one>)) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> \<phi>(\<one>))" 
     by simp (*(rule MMI_sbc19_21g);*)
   from S37 S39 have S40: "(A \<in> \<nat> \<longrightarrow> \<phi>(\<one>)) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> \<phi>(\<one>))" 
     by (rule MMI_ax_mp)
   from S36 S40 have S41: "(A \<in> \<nat> \<longrightarrow> \<phi>(\<one>))" by (rule MMI_mpbir)
   { fix y
     from A6 have S42: "y \<in> \<nat> \<longrightarrow> ch(y\<ca>\<one>)" by simp
     have S43: "y \<ca> \<one> = y \<ca> \<one>" by simp (*(rule MMI_oprex);*)
     from S43 have S44: " \<exists>x. x = y \<ca> \<one>" by (rule MMI_isseti)
     have S45: "ch(y\<ca>\<one>) \<longrightarrow> (\<forall>x. ch(y\<ca>\<one>))" by (rule MMI_ax_17)
     from S43 have S46: "y \<ca> \<one> = y \<ca> \<one>" .
     from S46 have S47: "\<phi>(y \<ca> \<one>) \<longrightarrow>  (\<forall>x. \<phi>(y \<ca> \<one>))" by simp (*(rule MMI_hbsbc1v);*)
     from S45 S47 have S48: 
       "(ch(y \<ca> \<one>) \<longleftrightarrow> \<phi>(y \<ca> \<one>)) \<longrightarrow>  (\<forall>x. ch(y \<ca> \<one>) \<longleftrightarrow> \<phi>(y \<ca> \<one>))" by simp 
       (*(rule MMI_hbbi)*)
     from A3 have S49: "\<forall>x y. x = y \<ca> \<one> \<longrightarrow> \<phi>(x) \<longleftrightarrow> ch(y\<ca>\<one>)".
     have S50: "\<forall>x. x = y \<ca> \<one> \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<phi>(y \<ca> \<one>)" by simp (*(rule MMI_sbceq1a);*)
     from S49 S50 have S51: "\<forall> x. x = y \<ca> \<one> \<longrightarrow>  ch(y \<ca> \<one>) \<longleftrightarrow> \<phi>(y \<ca> \<one>)" 
       by simp (*(rule MMI_bitr3d)*)
     from S48 S51 have S52: "( \<exists>x. x = y \<ca> \<one>) \<longrightarrow> ch(y \<ca> \<one>) \<longleftrightarrow> \<phi>(y \<ca> \<one>)" by auto
       (*(rule MMI_19_23ai);*)
     from S44 S52 have S53: "ch(y \<ca> \<one>) \<longleftrightarrow> \<phi>(y \<ca> \<one>)" by (rule MMI_ax_mp)
     from S42 S53 have S54: "y \<in> \<nat> \<longrightarrow> \<phi>(y \<ca> \<one>)" by (rule MMI_sylib)
     from S54 have S55: "y \<in> \<nat> \<longrightarrow>  A \<in> \<nat> \<longrightarrow> \<phi>(y \<ca> \<one>)" by (rule MMI_a1d)
     from S43 have S56: "y \<ca> \<one> = y \<ca> \<one>" .
     have S57: "A \<in> \<nat> \<longrightarrow> (\<forall>x. A \<in> \<nat>)" by (rule MMI_ax_17)
     from S57 have S58: "y \<ca> \<one> = y \<ca> \<one> \<longrightarrow> (A \<in> \<nat> \<longrightarrow> \<phi>(y \<ca> \<one>)) \<longleftrightarrow> 
       (A \<in> \<nat> \<longrightarrow> \<phi>(y \<ca> \<one>))" by simp (*(rule MMI_sbc19_21g);*)
     from S56 S58 have S59: "(A \<in> \<nat> \<longrightarrow> \<phi>(y \<ca> \<one>)) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> \<phi>(y \<ca> \<one>))" 
       by (rule MMI_ax_mp)
     from S55 S59 have S60: "y \<in> \<nat> \<longrightarrow> (A \<in> \<nat> \<longrightarrow> \<phi>(y \<ca> \<one>))" by (rule MMI_sylibr)
     from S60 have S61: "y \<in> \<nat> \<longrightarrow>  (A \<in> \<nat> \<longrightarrow> \<phi>(y)) \<longrightarrow> (A \<in> \<nat> \<longrightarrow> \<phi>(y \<ca> \<one>))" by (rule MMI_a1d)
   } then have S61: "\<forall>y. y \<in> \<nat> \<longrightarrow>  (A \<in> \<nat> \<longrightarrow> \<phi>(y)) \<longrightarrow> (A \<in> \<nat> \<longrightarrow> \<phi>(y \<ca> \<one>))"
     by simp
   from S1 S2 S3 S23 S41 S61 have S62: "A \<in> \<nat> \<longrightarrow>  A \<in> \<nat> \<longrightarrow> \<theta>(A)" by (rule MMI_nnind)
   from S62 show "A \<in> \<nat> \<longrightarrow> \<theta>(A)" by (rule MMI_pm2_43i)
qed


lemma (in MMIsar0) MMI_nnaddclt: 
   shows "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> A \<ca> B \<in> \<nat>"
proof -
  { fix x
    have S1: "x = \<one> \<longrightarrow> A \<ca> x = A \<ca> \<one>" by (rule MMI_opreq2)
    from S1 have S2: "x = \<one> \<longrightarrow> 
      A \<ca> x \<in> \<nat> \<longleftrightarrow> A \<ca> \<one> \<in> \<nat>" by (rule MMI_eleq1d)
    from S2 have "x = \<one> \<longrightarrow> 
      (A \<in> \<nat> \<longrightarrow> A \<ca> x \<in> \<nat>) \<longleftrightarrow> 
      (A \<in> \<nat> \<longrightarrow> A \<ca> \<one> \<in> \<nat>)" by (rule MMI_imbi2d) 
  } then have S3: "\<forall>x. x = \<one> \<longrightarrow> 
      (A \<in> \<nat> \<longrightarrow> A \<ca> x \<in> \<nat>) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> A \<ca> \<one> \<in> \<nat>)"
    by simp
  { fix x y
    have S4: "x = y \<longrightarrow> A \<ca> x = A \<ca> y" by (rule MMI_opreq2)
    from S4 have S5: "x = y \<longrightarrow> 
      A \<ca> x \<in> \<nat> \<longleftrightarrow> A \<ca> y \<in> \<nat>" by (rule MMI_eleq1d)
    from S5 have "x = y \<longrightarrow> 
      (A \<in> \<nat> \<longrightarrow> A \<ca> x \<in> \<nat>) \<longleftrightarrow> 
      (A \<in> \<nat> \<longrightarrow> A \<ca> y \<in> \<nat>)" by (rule MMI_imbi2d)
    } then have S6: "\<forall>x y. x = y \<longrightarrow> 
	(A \<in> \<nat> \<longrightarrow> A \<ca> x \<in> \<nat>) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> A \<ca> y \<in> \<nat>)"
      by simp
    { fix x y
      have S7: "x = y \<ca> \<one> \<longrightarrow> 
	A \<ca> x = A \<ca> (y \<ca> \<one>)" by (rule MMI_opreq2)
      from S7 have S8: "x = y \<ca> \<one> \<longrightarrow> 
	A \<ca> x \<in> \<nat> \<longleftrightarrow> 
	A \<ca> (y \<ca> \<one>) \<in> \<nat>" by (rule MMI_eleq1d)
      from S8 have "x = y \<ca> \<one> \<longrightarrow> 
	(A \<in> \<nat> \<longrightarrow> A \<ca> x \<in> \<nat>) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> A \<ca> (y \<ca> \<one>) \<in> \<nat>)" 
	by (rule MMI_imbi2d)
    } then have S9: "\<forall>x y. x = y \<ca> \<one> \<longrightarrow> 
	(A \<in> \<nat> \<longrightarrow> A \<ca> x \<in> \<nat>) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> A \<ca> (y \<ca> \<one>) \<in> \<nat>)"
      by simp
    { fix x
      have S10: "x = B \<longrightarrow> A \<ca> x = A \<ca> B" by (rule MMI_opreq2)
      from S10 have S11: "x = B \<longrightarrow> 
	A \<ca> x \<in> \<nat> \<longleftrightarrow> A \<ca> B \<in> \<nat>" by (rule MMI_eleq1d)
      from S11 have "x = B \<longrightarrow> 
	(A \<in> \<nat> \<longrightarrow> A \<ca> x \<in> \<nat>) \<longleftrightarrow> 
	(A \<in> \<nat> \<longrightarrow> A \<ca> B \<in> \<nat>)" by (rule MMI_imbi2d)
    } then have S12: "\<forall>x. x = B \<longrightarrow> 
	(A \<in> \<nat> \<longrightarrow> A \<ca> x \<in> \<nat>) \<longleftrightarrow> 	(A \<in> \<nat> \<longrightarrow> A \<ca> B \<in> \<nat>)"
      by simp
   have S13: "A \<in> \<nat> \<longrightarrow> A \<ca> \<one> \<in> \<nat>" by (rule MMI_peano2nn)
   have S14: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   { fix y
     have S15: "A \<in> \<complex> \<and> y \<in> \<complex> \<and> \<one> \<in> \<complex> \<longrightarrow> 
       A \<ca> y \<ca> \<one> = A \<ca> (y \<ca> \<one>)" by (rule MMI_axaddass)
     from S14 S15 have S16: "A \<in> \<complex> \<and> y \<in> \<complex> \<longrightarrow> 
       A \<ca> y \<ca> \<one> = A \<ca> (y \<ca> \<one>)" by (rule MMI_mp3an3)
     have S17: "A \<in> \<nat> \<longrightarrow> A \<in> \<complex>" by (rule MMI_nncnt)
     have S18: "y \<in> \<nat> \<longrightarrow> y \<in> \<complex>" by (rule MMI_nncnt)
     from S16 S17 S18 have S19: "A \<in> \<nat> \<and> y \<in> \<nat> \<longrightarrow> 
       A \<ca> y \<ca> \<one> = A \<ca> (y \<ca> \<one>)" by (rule MMI_syl2an)
     from S19 have S20: "A \<in> \<nat> \<and> y \<in> \<nat> \<longrightarrow> 
       A \<ca> y \<ca> \<one> \<in> \<nat> \<longleftrightarrow> 
       A \<ca> (y \<ca> \<one>) \<in> \<nat>" by (rule MMI_eleq1d)
     have S21: "A \<ca> y \<in> \<nat> \<longrightarrow> 
       A \<ca> y \<ca> \<one> \<in> \<nat>" by (rule MMI_peano2nn)
     from S20 S21 have S22: "A \<in> \<nat> \<and> y \<in> \<nat> \<longrightarrow> 
       A \<ca> y \<in> \<nat> \<longrightarrow> 
       A \<ca> (y \<ca> \<one>) \<in> \<nat>" by (rule MMI_syl5bi)
     from S22 have S23: "y \<in> \<nat> \<longrightarrow> 
       A \<in> \<nat> \<longrightarrow> 
       A \<ca> y \<in> \<nat> \<longrightarrow> 
       A \<ca> (y \<ca> \<one>) \<in> \<nat>" by (rule MMI_expcom)
     from S23 have "y \<in> \<nat> \<longrightarrow> 
       (A \<in> \<nat> \<longrightarrow> A \<ca> y \<in> \<nat>) \<longrightarrow>   A \<in> \<nat> \<longrightarrow>  A \<ca> (y \<ca> \<one>) \<in> \<nat>" 
       by (rule MMI_a2d)
   } then have  S24: "\<forall>y. y \<in> \<nat> \<longrightarrow> 
       (A \<in> \<nat> \<longrightarrow> A \<ca> y \<in> \<nat>) \<longrightarrow>   A \<in> \<nat> \<longrightarrow>  A \<ca> (y \<ca> \<one>) \<in> \<nat>" 
     by simp
   from S3 S6 S9 S12 S13 S24 have S25: "B \<in> \<nat> \<longrightarrow> 
   A \<in> \<nat> \<longrightarrow> A \<ca> B \<in> \<nat>" by (rule MMI_nnind)
   from S25 show "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> A \<ca> B \<in> \<nat>" by (rule MMI_impcom)
qed


lemma (in MMIsar0) MMI_nnmulclt: 
   shows "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> A\<cdot>B \<in> \<nat>"
proof -
  { fix x
    have S1: "x = \<one> \<longrightarrow> A\<cdot>x = A\<cdot>\<one>" by (rule MMI_opreq2)
    from S1 have S2: "x = \<one> \<longrightarrow> 
      A\<cdot>x \<in> \<nat> \<longleftrightarrow> A\<cdot>\<one> \<in> \<nat>" by (rule MMI_eleq1d)
    from S2 have "x = \<one> \<longrightarrow> 
      (A \<in> \<nat> \<longrightarrow> A\<cdot>x \<in> \<nat>) \<longleftrightarrow> 
      (A \<in> \<nat> \<longrightarrow> A\<cdot>\<one> \<in> \<nat>)" by (rule MMI_imbi2d)
    } then have S3: "\<forall> x. x = \<one> \<longrightarrow> 
      (A \<in> \<nat> \<longrightarrow> A\<cdot>x \<in> \<nat>) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> A\<cdot>\<one> \<in> \<nat>)"
      by simp
    { fix x y 
      have S4: "x = y \<longrightarrow> A\<cdot>x = A\<cdot>y" by (rule MMI_opreq2)
      from S4 have S5: "x = y \<longrightarrow> 
	A\<cdot>x \<in> \<nat> \<longleftrightarrow> A\<cdot>y \<in> \<nat>" by (rule MMI_eleq1d)
      from S5 have "x = y \<longrightarrow> 
	(A \<in> \<nat> \<longrightarrow> A\<cdot>x \<in> \<nat>) \<longleftrightarrow> 
	(A \<in> \<nat> \<longrightarrow> A\<cdot>y \<in> \<nat>)" by (rule MMI_imbi2d)
    } then have S6: "\<forall>x y. x = y \<longrightarrow> 
	(A \<in> \<nat> \<longrightarrow> A\<cdot>x \<in> \<nat>) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> A\<cdot>y \<in> \<nat>)"
      by simp
    {fix x y
      have S7: "x = y \<ca> \<one> \<longrightarrow> 
	A\<cdot>x = A\<cdot>(y \<ca> \<one>)" by (rule MMI_opreq2)
      from S7 have S8: "x = y \<ca> \<one> \<longrightarrow> 
	A\<cdot>x \<in> \<nat> \<longleftrightarrow> 
	A\<cdot>(y \<ca> \<one>) \<in> \<nat>" by (rule MMI_eleq1d)
      from S8 have "x = y \<ca> \<one> \<longrightarrow> 
	(A \<in> \<nat> \<longrightarrow> A\<cdot>x \<in> \<nat>) \<longleftrightarrow> 
	(A \<in> \<nat> \<longrightarrow> 
	A\<cdot>(y \<ca> \<one>) \<in> \<nat>)" by (rule MMI_imbi2d)
    } then have S9: "\<forall> x y. x = y \<ca> \<one> \<longrightarrow> 
	(A \<in> \<nat> \<longrightarrow> A\<cdot>x \<in> \<nat>) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> A\<cdot>(y \<ca> \<one>) \<in> \<nat>)"
      by simp
    { fix x 
      have S10: "x = B \<longrightarrow> A\<cdot>x = A\<cdot>B" by (rule MMI_opreq2)
      from S10 have S11: "x = B \<longrightarrow> 
	A\<cdot>x \<in> \<nat> \<longleftrightarrow> A\<cdot>B \<in> \<nat>" by (rule MMI_eleq1d)
      from S11 have "x = B \<longrightarrow> 
	(A \<in> \<nat> \<longrightarrow> A\<cdot>x \<in> \<nat>) \<longleftrightarrow> 
	(A \<in> \<nat> \<longrightarrow> A\<cdot>B \<in> \<nat>)" by (rule MMI_imbi2d)
    } then have S12: "\<forall> x. x = B \<longrightarrow> 
	(A \<in> \<nat> \<longrightarrow> A\<cdot>x \<in> \<nat>) \<longleftrightarrow> (A \<in> \<nat> \<longrightarrow> A\<cdot>B \<in> \<nat>)"
      by simp
    have S13: "A \<in> \<nat> \<longrightarrow> A \<in> \<complex>" by (rule MMI_nncnt)
    have S14: "A \<in> \<complex> \<longrightarrow> A\<cdot>\<one> = A" by (rule MMI_ax1id)
    from S14 have S15: "A \<in> \<complex> \<longrightarrow> 
      A\<cdot>\<one> \<in> \<nat> \<longleftrightarrow> A \<in> \<nat>" by (rule MMI_eleq1d)
    from S15 have S16: "A \<in> \<complex> \<longrightarrow> 
      A \<in> \<nat> \<longrightarrow> A\<cdot>\<one> \<in> \<nat>" by (rule MMI_biimprd)
    from S13 S16 have S17: "A \<in> \<nat> \<longrightarrow> A\<cdot>\<one> \<in> \<nat>" by (rule MMI_mpcom)
    have S18: "\<one> \<in> \<complex>" by (rule MMI_1cn)
    { fix y
      have S19: "A \<in> \<complex> \<and> y \<in> \<complex> \<and> \<one> \<in> \<complex> \<longrightarrow> 
	A\<cdot>(y \<ca> \<one>) = A\<cdot>y \<ca> A\<cdot>\<one>" by (rule MMI_axdistr)
      from S18 S19 have S20: "A \<in> \<complex> \<and> y \<in> \<complex> \<longrightarrow> 
	A\<cdot>(y \<ca> \<one>) = A\<cdot>y \<ca> A\<cdot>\<one>" by (rule MMI_mp3an3)
      from S14 have S21: "A \<in> \<complex> \<longrightarrow> A\<cdot>\<one> = A" .
      from S21 have S22: "A \<in> \<complex> \<longrightarrow> 
	A\<cdot>y \<ca> A\<cdot>\<one> = A\<cdot>y \<ca> A" by (rule MMI_opreq2d)
      from S22 have S23: "A \<in> \<complex> \<and> y \<in> \<complex> \<longrightarrow> 
	A\<cdot>y \<ca> A\<cdot>\<one> = A\<cdot>y \<ca> A" by (rule MMI_adantr)
      from S20 S23 have S24: "A \<in> \<complex> \<and> y \<in> \<complex> \<longrightarrow> 
	A\<cdot>(y \<ca> \<one>) = A\<cdot>y \<ca> A" by (rule MMI_eqtrd)
      from S13 have S25: "A \<in> \<nat> \<longrightarrow> A \<in> \<complex>" .
      have S26: "y \<in> \<nat> \<longrightarrow> y \<in> \<complex>" by (rule MMI_nncnt)
      from S24 S25 S26 have S27: "A \<in> \<nat> \<and> y \<in> \<nat> \<longrightarrow> 
	A\<cdot>(y \<ca> \<one>) = A\<cdot>y \<ca> A" by (rule MMI_syl2an)
      from S27 have S28: "A \<in> \<nat> \<and> y \<in> \<nat> \<longrightarrow> 
	A\<cdot>(y \<ca> \<one>) \<in> \<nat> \<longleftrightarrow> A\<cdot>y \<ca> A \<in> \<nat>" by (rule MMI_eleq1d)
      have S29: "A\<cdot>y \<in> \<nat> \<and> A \<in> \<nat> \<longrightarrow> A\<cdot>y \<ca> A \<in> \<nat>" by (rule MMI_nnaddclt)
      from S29 have S30: "A \<in> \<nat> \<and> A\<cdot>y \<in> \<nat> \<longrightarrow> A\<cdot>y \<ca> A \<in> \<nat>" by (rule MMI_ancoms)
      from S28 S30 have S31: "A \<in> \<nat> \<and> y \<in> \<nat> \<longrightarrow> 
	A \<in> \<nat> \<and> A\<cdot>y \<in> \<nat> \<longrightarrow> 
	A\<cdot>(y \<ca> \<one>) \<in> \<nat>" by (rule MMI_syl5bir)
      from S31 have S32: "A \<in> \<nat> \<longrightarrow> 
	y \<in> \<nat> \<longrightarrow> 
	A \<in> \<nat> \<longrightarrow> 
	A\<cdot>y \<in> \<nat> \<longrightarrow> 
	A\<cdot>(y \<ca> \<one>) \<in> \<nat>" by (rule MMI_exp4b)
      from S32 have S33: "y \<in> \<nat> \<longrightarrow> 
	A \<in> \<nat> \<longrightarrow> 
	A\<cdot>y \<in> \<nat> \<longrightarrow> 
	A\<cdot>(y \<ca> \<one>) \<in> \<nat>" by (rule MMI_pm2_43b)
      from S33 have "y \<in> \<nat> \<longrightarrow> 
	(A \<in> \<nat> \<longrightarrow> A\<cdot>y \<in> \<nat>) \<longrightarrow>   A \<in> \<nat> \<longrightarrow>  A\<cdot>(y \<ca> \<one>) \<in> \<nat>" by (rule MMI_a2d)
    } then have S34: "\<forall> y. y \<in> \<nat> \<longrightarrow> 
	(A \<in> \<nat> \<longrightarrow> A\<cdot>y \<in> \<nat>) \<longrightarrow>   A \<in> \<nat> \<longrightarrow>  A\<cdot>(y \<ca> \<one>) \<in> \<nat>"
      by simp
    from S3 S6 S9 S12 S17 S34 have S35: "B \<in> \<nat> \<longrightarrow> 
      A \<in> \<nat> \<longrightarrow> A\<cdot>B \<in> \<nat>" by (rule MMI_nnind)
   from S35 show "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> A\<cdot>B \<in> \<nat>" by (rule MMI_impcom)
qed

lemma (in MMIsar0) MMI_nn2get: 
   shows "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   ( \<exists>x\<in>\<nat>. A \<lsq> x \<and> B \<lsq> x)"
proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<lsq> B \<or> B \<lsq> A" by (rule MMI_letrit)
   have S2: "A \<in> \<nat> \<longrightarrow> A \<in> \<real>" by (rule MMI_nnret)
   have S3: "B \<in> \<nat> \<longrightarrow> B \<in> \<real>" by (rule MMI_nnret)
   from S1 S2 S3 have S4: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> A \<lsq> B \<or> B \<lsq> A" by (rule MMI_syl2an)
   from S3 have S5: "B \<in> \<nat> \<longrightarrow> B \<in> \<real>" .
   have S6: "B \<in> \<real> \<longrightarrow> B \<lsq> B" by (rule MMI_leidt)
   from S6 have S7: "B \<in> \<real> \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A \<lsq> B \<and> B \<lsq> B" by (rule MMI_biantrud)
   from S7 have S8: "B \<in> \<real> \<longrightarrow> 
   A \<lsq> B \<longrightarrow> A \<lsq> B \<and> B \<lsq> B" by (rule MMI_biimpd)
   from S5 S8 have S9: "B \<in> \<nat> \<longrightarrow> 
   A \<lsq> B \<longrightarrow> A \<lsq> B \<and> B \<lsq> B" by (rule MMI_syl)
   from S9 have S10: "B \<in> \<nat> \<longrightarrow> 
   A \<lsq> B \<longrightarrow> 
   B \<in> \<nat> \<and> A \<lsq> B \<and> B \<lsq> B" by (rule MMI_anc2li)
   have S11: "x = B \<longrightarrow> 
   A \<lsq> x \<longleftrightarrow> A \<lsq> B" by (rule MMI_breq2)
   have S12: "x = B \<longrightarrow> 
   B \<lsq> x \<longleftrightarrow> B \<lsq> B" by (rule MMI_breq2)
   from S11 S12 have S13: "x = B \<longrightarrow> 
   A \<lsq> x \<and> B \<lsq> x \<longleftrightarrow> A \<lsq> B \<and> B \<lsq> B" by (rule MMI_anbi12d)
   from S13 have S14: "B \<in> \<nat> \<and> A \<lsq> B \<and> B \<lsq> B \<longrightarrow> 
   ( \<exists>x\<in>\<nat>. A \<lsq> x \<and> B \<lsq> x)" by auto (*by (rule MMI_rcla4ev)*)
   from S10 S14 have S15: "B \<in> \<nat> \<longrightarrow> 
   A \<lsq> B \<longrightarrow> 
   ( \<exists>x\<in>\<nat>. A \<lsq> x \<and> B \<lsq> x)" by (rule MMI_syl6)
   from S15 have S16: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   A \<lsq> B \<longrightarrow> 
   ( \<exists>x\<in>\<nat>. A \<lsq> x \<and> B \<lsq> x)" by (rule MMI_adantl)
   from S2 have S17: "A \<in> \<nat> \<longrightarrow> A \<in> \<real>" .
   have S18: "A \<in> \<real> \<longrightarrow> A \<lsq> A" by (rule MMI_leidt)
   from S18 have S19: "A \<in> \<real> \<longrightarrow> 
   B \<lsq> A \<longleftrightarrow> A \<lsq> A \<and> B \<lsq> A" by (rule MMI_biantrurd)
   from S19 have S20: "A \<in> \<real> \<longrightarrow> 
   B \<lsq> A \<longrightarrow> A \<lsq> A \<and> B \<lsq> A" by (rule MMI_biimpd)
   from S17 S20 have S21: "A \<in> \<nat> \<longrightarrow> 
   B \<lsq> A \<longrightarrow> A \<lsq> A \<and> B \<lsq> A" by (rule MMI_syl)
   from S21 have S22: "A \<in> \<nat> \<longrightarrow> 
   B \<lsq> A \<longrightarrow> 
   A \<in> \<nat> \<and> A \<lsq> A \<and> B \<lsq> A" by (rule MMI_anc2li)
   have S23: "x = A \<longrightarrow> 
   A \<lsq> x \<longleftrightarrow> A \<lsq> A" by (rule MMI_breq2)
   have S24: "x = A \<longrightarrow> 
   B \<lsq> x \<longleftrightarrow> B \<lsq> A" by (rule MMI_breq2)
   from S23 S24 have S25: "x = A \<longrightarrow> 
   A \<lsq> x \<and> B \<lsq> x \<longleftrightarrow> A \<lsq> A \<and> B \<lsq> A" by (rule MMI_anbi12d)
   from S25 have S26: "A \<in> \<nat> \<and> A \<lsq> A \<and> B \<lsq> A \<longrightarrow> 
   ( \<exists>x\<in>\<nat>. A \<lsq> x \<and> B \<lsq> x)" by auto (*(rule MMI_rcla4ev)*)
   from S22 S26 have S27: "A \<in> \<nat> \<longrightarrow> 
   B \<lsq> A \<longrightarrow> 
   ( \<exists>x\<in>\<nat>. A \<lsq> x \<and> B \<lsq> x)" by (rule MMI_syl6)
   from S27 have S28: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   B \<lsq> A \<longrightarrow> 
   ( \<exists>x\<in>\<nat>. A \<lsq> x \<and> B \<lsq> x)" by (rule MMI_adantr)
   from S16 S28 have S29: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   A \<lsq> B \<or> B \<lsq> A \<longrightarrow> 
   ( \<exists>x\<in>\<nat>. A \<lsq> x \<and> B \<lsq> x)" by (rule MMI_jaod)
   from S4 S29 show "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   ( \<exists>x\<in>\<nat>. A \<lsq> x \<and> B \<lsq> x)" by (rule MMI_mpd)
qed

lemma (in MMIsar0) MMI_nnge1t: 
   shows "A \<in> \<nat> \<longrightarrow> \<one> \<lsq> A"
proof -
  {fix x
    have "x = \<one> \<longrightarrow> 
      \<one> \<lsq> x \<longleftrightarrow> \<one> \<lsq> \<one>" by (rule MMI_breq2)
  } then have S1: "\<forall> x. x = \<one> \<longrightarrow>  \<one> \<lsq> x \<longleftrightarrow> \<one> \<lsq> \<one>"
    by simp
  { fix x y
    have "x = y \<longrightarrow> 
      \<one> \<lsq> x \<longleftrightarrow> \<one> \<lsq> y" by (rule MMI_breq2)
  } then have S2: "\<forall>x y.  x = y \<longrightarrow> \<one> \<lsq> x \<longleftrightarrow> \<one> \<lsq> y"
    by simp
  { fix x y
    have "x = y \<ca> \<one> \<longrightarrow> 
      \<one> \<lsq> x \<longleftrightarrow> \<one> \<lsq> y \<ca> \<one>" by (rule MMI_breq2)
  } then have S3: 
      "\<forall>x y. x = y \<ca> \<one> \<longrightarrow> \<one> \<lsq> x \<longleftrightarrow> \<one> \<lsq> y \<ca> \<one>"
    by simp
  { fix x
    have "x = A \<longrightarrow> 
      \<one> \<lsq> x \<longleftrightarrow> \<one> \<lsq> A" by (rule MMI_breq2)
  } then have S4: "\<forall> x. x = A \<longrightarrow> \<one> \<lsq> x \<longleftrightarrow> \<one> \<lsq> A"
    by simp
   have S5: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S5 have S6: "\<one> \<lsq> \<one>" by (rule MMI_leid)
   { fix y
     have S7: "y \<in> \<nat> \<longrightarrow> y \<in> \<real>" by (rule MMI_nnret)
     have S8: "y \<in> \<real> \<longrightarrow> y \<in> \<complex>" by (rule MMI_recnt)
     have S9: "y \<in> \<complex> \<longrightarrow> y \<ca> \<zero> = y" by (rule MMI_ax0id)
     from S8 S9 have S10: "y \<in> \<real> \<longrightarrow> y \<ca> \<zero> = y" by (rule MMI_syl)
     from S10 have S11: "y \<in> \<real> \<longrightarrow> 
       \<one> \<lsq> y \<ca> \<zero> \<longleftrightarrow> \<one> \<lsq> y" by (rule MMI_breq2d)
     have S12: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
     have S13: "\<zero> \<in> \<real>" by (rule MMI_0re)
     have S14: "\<one> \<in> \<real>" by (rule MMI_ax1re)
     have S15: "\<zero> \<in> \<real> \<and> \<one> \<in> \<real> \<and> y \<in> \<real> \<longrightarrow> 
       \<zero> \<ls> \<one> \<longrightarrow> 
       y \<ca> \<zero> \<ls> y \<ca> \<one>" by (rule MMI_axltadd)
     from S13 S14 S15 have S16: "y \<in> \<real> \<longrightarrow> 
       \<zero> \<ls> \<one> \<longrightarrow> 
       y \<ca> \<zero> \<ls> y \<ca> \<one>" by (rule MMI_mp3an12)
     from S12 S16 have S17: "y \<in> \<real> \<longrightarrow> 
       y \<ca> \<zero> \<ls> y \<ca> \<one>" by (rule MMI_mpi)
     have S18: "\<one> \<in> \<real>" by (rule MMI_ax1re)
     have S19: "y \<ca> \<zero> \<in> \<real> \<and> y \<ca> \<one> \<in> \<real> \<and> \<one> \<in> \<real> \<longrightarrow> 
       y \<ca> \<zero> \<ls> y \<ca> \<one> \<and> y \<ca> \<one> \<ls> \<one> \<longrightarrow> y \<ca> \<zero> \<ls> \<one>" by (rule MMI_axlttrn)
     from S18 S19 have S20: "y \<ca> \<zero> \<in> \<real> \<and> y \<ca> \<one> \<in> \<real> \<longrightarrow> 
       y \<ca> \<zero> \<ls> y \<ca> \<one> \<and> y \<ca> \<one> \<ls> \<one> \<longrightarrow> y \<ca> \<zero> \<ls> \<one>" by (rule MMI_mp3an3)
     have S21: "\<zero> \<in> \<real>" by (rule MMI_0re)
     have S22: "y \<in> \<real> \<and> \<zero> \<in> \<real> \<longrightarrow> y \<ca> \<zero> \<in> \<real>" by (rule MMI_axaddrcl)
     from S21 S22 have S23: "y \<in> \<real> \<longrightarrow> y \<ca> \<zero> \<in> \<real>" by (rule MMI_mpan2)
     have S24: "y \<in> \<real> \<longrightarrow> y \<ca> \<one> \<in> \<real>" by (rule MMI_peano2re)
     from S20 S23 S24 have S25: "y \<in> \<real> \<longrightarrow> 
       y \<ca> \<zero> \<ls> y \<ca> \<one> \<and> y \<ca> \<one> \<ls> \<one> \<longrightarrow> y \<ca> \<zero> \<ls> \<one>" by (rule MMI_sylanc)
     from S17 S25 have S26: "y \<in> \<real> \<longrightarrow> 
       y \<ca> \<one> \<ls> \<one> \<longrightarrow> y \<ca> \<zero> \<ls> \<one>" by (rule MMI_mpand)
     from S26 have S27: "y \<in> \<real> \<longrightarrow> 
       \<not>(y \<ca> \<zero> \<ls> \<one>) \<longrightarrow> 
       \<not>(y \<ca> \<one> \<ls> \<one>)" by (rule MMI_con3d)
     from S23 have S28: "y \<in> \<real> \<longrightarrow> y \<ca> \<zero> \<in> \<real>" .
     have S29: "\<one> \<in> \<real>" by (rule MMI_ax1re)
     from S28 S29 have S30: "y \<in> \<real> \<longrightarrow> 
       \<one> \<in> \<real> \<and> y \<ca> \<zero> \<in> \<real>" by (rule MMI_jctil)
     have S31: "\<one> \<in> \<real> \<and> y \<ca> \<zero> \<in> \<real> \<longrightarrow> 
       \<one> \<lsq> y \<ca> \<zero> \<longleftrightarrow> 
       \<not>(y \<ca> \<zero> \<ls> \<one>)" by (rule MMI_lenltt)
     from S30 S31 have S32: "y \<in> \<real> \<longrightarrow> 
       \<one> \<lsq> y \<ca> \<zero> \<longleftrightarrow> 
       \<not>(y \<ca> \<zero> \<ls> \<one>)" by (rule MMI_syl)
     from S24 have S33: "y \<in> \<real> \<longrightarrow> y \<ca> \<one> \<in> \<real>" .
     have S34: "\<one> \<in> \<real>" by (rule MMI_ax1re)
     from S33 S34 have S35: "y \<in> \<real> \<longrightarrow> 
       \<one> \<in> \<real> \<and> y \<ca> \<one> \<in> \<real>" by (rule MMI_jctil)
     have S36: "\<one> \<in> \<real> \<and> y \<ca> \<one> \<in> \<real> \<longrightarrow> 
       \<one> \<lsq> y \<ca> \<one> \<longleftrightarrow> 
       \<not>(y \<ca> \<one> \<ls> \<one>)" by (rule MMI_lenltt)
     from S35 S36 have S37: "y \<in> \<real> \<longrightarrow> 
       \<one> \<lsq> y \<ca> \<one> \<longleftrightarrow> 
       \<not>(y \<ca> \<one> \<ls> \<one>)" by (rule MMI_syl)
     from S27 S32 S37 have S38: "y \<in> \<real> \<longrightarrow> 
       \<one> \<lsq> y \<ca> \<zero> \<longrightarrow> \<one> \<lsq> y \<ca> \<one>" by (rule MMI_3imtr4d)
     from S11 S38 have S39: "y \<in> \<real> \<longrightarrow> 
       \<one> \<lsq> y \<longrightarrow> \<one> \<lsq> y \<ca> \<one>" by (rule MMI_sylbird)
     from S7 S39 have S40: "y \<in> \<nat> \<longrightarrow> 
       \<one> \<lsq> y \<longrightarrow> \<one> \<lsq> y \<ca> \<one>" by (rule MMI_syl)
   } then have S40: "\<forall>y. y \<in> \<nat> \<longrightarrow> \<one> \<lsq> y \<longrightarrow> \<one> \<lsq> y \<ca> \<one>"
     by simp
   from S1 S2 S3 S4 S6 S40 show "A \<in> \<nat> \<longrightarrow> \<one> \<lsq> A" by (rule MMI_nnind)
 qed

lemma (in MMIsar0) MMI_nngt1ne1t: 
   shows "A \<in> \<nat> \<longrightarrow> 
   \<one> \<ls> A \<longleftrightarrow> \<not>(A = \<one>)"
proof -
   have S1: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S2: "\<one> \<in> \<real> \<and> A \<in> \<real> \<and> \<one> \<lsq> A \<longrightarrow> 
   \<one> \<ls> A \<longleftrightarrow> \<not>(\<one> = A)" by (rule MMI_leltnet)
   from S1 S2 have S3: "A \<in> \<real> \<and> \<one> \<lsq> A \<longrightarrow> 
   \<one> \<ls> A \<longleftrightarrow> \<not>(\<one> = A)" by (rule MMI_mp3an1)
   have S4: "A \<in> \<nat> \<longrightarrow> A \<in> \<real>" by (rule MMI_nnret)
   have S5: "A \<in> \<nat> \<longrightarrow> \<one> \<lsq> A" by (rule MMI_nnge1t)
   from S3 S4 S5 have S6: "A \<in> \<nat> \<longrightarrow> 
   \<one> \<ls> A \<longleftrightarrow> \<not>(\<one> = A)" by (rule MMI_sylanc)
   have S7: "\<one> = A \<longleftrightarrow> A = \<one>" by (rule MMI_eqcom)
   from S7 have S8: "\<not>(\<one> = A) \<longleftrightarrow> \<not>(A = \<one>)" by (rule MMI_negbii)
   from S6 S8 show "A \<in> \<nat> \<longrightarrow> 
   \<one> \<ls> A \<longleftrightarrow> \<not>(A = \<one>)" by (rule MMI_syl6bb)
qed

lemma (in MMIsar0) MMI_nnle1eq1t: 
   shows "A \<in> \<nat> \<longrightarrow> 
   A \<lsq> \<one> \<longleftrightarrow> A = \<one>"
proof -
   have S1: "A \<in> \<nat> \<longrightarrow> \<one> \<lsq> A" by (rule MMI_nnge1t)
   from S1 have S2: "A \<in> \<nat> \<longrightarrow> 
   A \<lsq> \<one> \<longleftrightarrow> 
   A \<lsq> \<one> \<and> \<one> \<lsq> A" by (rule MMI_biantrud)
   have S3: "A \<in> \<nat> \<longrightarrow> A \<in> \<real>" by (rule MMI_nnret)
   have S4: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S5: "A \<in> \<real> \<and> \<one> \<in> \<real> \<longrightarrow> 
   A = \<one> \<longleftrightarrow> 
   A \<lsq> \<one> \<and> \<one> \<lsq> A" by (rule MMI_letri3t)
   from S4 S5 have S6: "A \<in> \<real> \<longrightarrow> 
   A = \<one> \<longleftrightarrow> 
   A \<lsq> \<one> \<and> \<one> \<lsq> A" by (rule MMI_mpan2)
   from S3 S6 have S7: "A \<in> \<nat> \<longrightarrow> 
   A = \<one> \<longleftrightarrow> 
   A \<lsq> \<one> \<and> \<one> \<lsq> A" by (rule MMI_syl)
   from S2 S7 show "A \<in> \<nat> \<longrightarrow> 
   A \<lsq> \<one> \<longleftrightarrow> A = \<one>" by (rule MMI_bitr4d)
qed

lemma (in MMIsar0) MMI_nngt0t: 
   shows "A \<in> \<nat> \<longrightarrow> \<zero> \<ls> A"
proof -
   have S1: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   have S2: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S3: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S4: "\<zero> \<in> \<real> \<and> \<one> \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one> \<and> \<one> \<lsq> A \<longrightarrow> \<zero> \<ls> A" by (rule MMI_ltletrt)
   from S2 S3 S4 have S5: "A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one> \<and> \<one> \<lsq> A \<longrightarrow> \<zero> \<ls> A" by (rule MMI_mp3an12)
   from S1 S5 have S6: "A \<in> \<real> \<longrightarrow> 
   \<one> \<lsq> A \<longrightarrow> \<zero> \<ls> A" by (rule MMI_mpani)
   have S7: "A \<in> \<nat> \<longrightarrow> A \<in> \<real>" by (rule MMI_nnret)
   have S8: "A \<in> \<nat> \<longrightarrow> \<one> \<lsq> A" by (rule MMI_nnge1t)
   from S6 S7 S8 show "A \<in> \<nat> \<longrightarrow> \<zero> \<ls> A" by (rule MMI_sylc)
qed

lemma (in MMIsar0) MMI_lt1nnn: 
   shows "A \<in> \<real> \<and> A \<ls> \<one> \<longrightarrow> \<not>(A \<in> \<nat>)"
proof -
   have S1: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S2: "A \<in> \<real> \<and> \<one> \<in> \<real> \<longrightarrow> 
   A \<ls> \<one> \<longleftrightarrow> \<not>(\<one> \<lsq> A)" by (rule MMI_ltnlet)
   from S1 S2 have S3: "A \<in> \<real> \<longrightarrow> 
   A \<ls> \<one> \<longleftrightarrow> \<not>(\<one> \<lsq> A)" by (rule MMI_mpan2)
   have S4: "A \<in> \<nat> \<longrightarrow> \<one> \<lsq> A" by (rule MMI_nnge1t)
   from S4 have S5: "\<not>(\<one> \<lsq> A) \<longrightarrow> \<not>(A \<in> \<nat>)" by (rule MMI_con3i)
   from S3 S5 have S6: "A \<in> \<real> \<longrightarrow> 
   A \<ls> \<one> \<longrightarrow> \<not>(A \<in> \<nat>)" by (rule MMI_syl6bi)
   from S6 show "A \<in> \<real> \<and> A \<ls> \<one> \<longrightarrow> \<not>(A \<in> \<nat>)" by (rule MMI_imp)
qed

(*********** 511-515****************************)

lemma (in MMIsar0) MMI_0nnn: 
   shows "\<not>(\<zero> \<in> \<nat>)"
proof -
   have S1: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S2: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   have S3: "\<zero> \<in> \<real> \<and> \<zero> \<ls> \<one> \<longrightarrow> \<not>(\<zero> \<in> \<nat>)" by (rule MMI_lt1nnn)
   from S1 S2 S3 show "\<not>(\<zero> \<in> \<nat>)" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_nnne0t: 
   shows "A \<in> \<nat> \<longrightarrow> A \<noteq> \<zero>"
proof -
   have S1: "\<not>(\<zero> \<in> \<nat>)" by (rule MMI_0nnn)
   have S2: "A = \<zero> \<longrightarrow> 
   A \<in> \<nat> \<longleftrightarrow> \<zero> \<in> \<nat>" by (rule MMI_eleq1)
   from S1 S2 have S3: "A = \<zero> \<longrightarrow> \<not>(A \<in> \<nat>)" by (rule MMI_mtbiri)
   from S3 have S4: "A \<in> \<nat> \<longrightarrow> \<not>(A = \<zero>)" by (rule MMI_con2i)
   have S5: "A \<noteq> \<zero> \<longleftrightarrow> \<not>(A = \<zero>)" by (rule MMI_df_ne)
   from S4 S5 show "A \<in> \<nat> \<longrightarrow> A \<noteq> \<zero>" by (rule MMI_sylibr)
qed

lemma (in MMIsar0) MMI_nngt0: assumes A1: "A \<in> \<nat>"   
   shows "\<zero> \<ls> A"
proof -
   from A1 have S1: "A \<in> \<nat>".
   have S2: "A \<in> \<nat> \<longrightarrow> \<zero> \<ls> A" by (rule MMI_nngt0t)
   from S1 S2 show "\<zero> \<ls> A" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_nnne0: assumes A1: "A \<in> \<nat>"   
   shows "A \<noteq> \<zero>"
proof -
   from A1 have S1: "A \<in> \<nat>".
   from S1 have S2: "A \<in> \<real>" by (rule MMI_nnre)
   from A1 have S3: "A \<in> \<nat>".
   from S3 have S4: "\<zero> \<ls> A" by (rule MMI_nngt0)
   from S2 S4 show "A \<noteq> \<zero>" by (rule MMI_gt0ne0i)
qed

lemma (in MMIsar0) MMI_nnrecgt0t: 
   shows "A \<in> \<nat> \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A"
proof -
   have S1: "A \<in> \<nat> \<longrightarrow> \<one> \<lsq> A" by (rule MMI_nnge1t)
   have S2: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   have S3: "A \<in> \<nat> \<longrightarrow> A \<in> \<real>" by (rule MMI_nnret)
   have S4: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S5: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S6: "\<zero> \<in> \<real> \<and> \<one> \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one> \<and> \<one> \<lsq> A \<longrightarrow> \<zero> \<ls> A" by (rule MMI_ltletrt)
   from S4 S5 S6 have S7: "A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one> \<and> \<one> \<lsq> A \<longrightarrow> \<zero> \<ls> A" by (rule MMI_mp3an12)
   have S8: "A \<in> \<real> \<and> \<zero> \<ls> A \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_recgt0t)
   from S8 have S9: "A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_ex)
   from S7 S9 have S10: "A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> \<one> \<and> \<one> \<lsq> A \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_syld)
   from S3 S10 have S11: "A \<in> \<nat> \<longrightarrow> 
   \<zero> \<ls> \<one> \<and> \<one> \<lsq> A \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_syl)
   from S2 S11 have S12: "A \<in> \<nat> \<longrightarrow> 
   \<one> \<lsq> A \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_mpani)
   from S1 S12 show "A \<in> \<nat> \<longrightarrow> \<zero> \<ls> \<one>\<cdiv>A" by (rule MMI_mpd)
qed

text\<open>I am unable to translate the proof of Metamath's nnleltp1. Isabelle 
  chokes on a comlicated application of nn1suc. A couple of theorems below
  are proven by hand in Isabelle to wokaround this. 
  In the next theorem we show that $a < a+1$.\<close>

lemma (in MMIsar0) num_le_numplus1: assumes "a\<in>\<real>"
  shows "a \<ls> a\<ca>\<one>"
  using assms MMI_ax1re MMI_lt01 MMI_ltaddpos
  by simp

text\<open>The next theorem
  shows that of $a\leq b$, then $a< b+1$.\<close>

lemma (in MMIsar0) lsq_imp_ls_plus1: 
  assumes A1: "a\<in>\<real>"   "b\<in>\<real>" and A3: "a\<lsq>b"
  shows "a \<ls> b\<ca>\<one>"
proof -
  from A1 have "b \<ls> b\<ca>\<one>" using num_le_numplus1 by simp
  with A1 A3 show "a \<ls> b\<ca>\<one>" using MMI_ax1re MMI_axaddrcl MMI_lelttr
    by blast
qed

text\<open>There are no natural numbers between $1$ and $2$.\<close>

lemma (in MMIsar0) no_nat_between12: 
  assumes A1: "n \<in> \<nat>"
  shows "n \<ls> \<one>\<ca>\<one> \<longrightarrow> n \<lsq> \<one>"
proof -
  have "\<one> \<ls> \<one>\<ca>\<one> \<longrightarrow> \<one> \<lsq> \<one>" 
    using MMI_1nn MMI_nnge1t by simp
  moreover
  { fix k assume A2: "k\<in>\<nat>"
    { assume A3: "k\<ca>\<one> \<ls> \<one>\<ca>\<one>"
      from A2 MMI_ax1re have T: "k \<in> \<real>"  "\<one> \<in> \<real>" 
	using MMI_nnre by auto
      with A3 have "k \<ls> \<one>" using MMI_ltadd1 by blast
      with T A2 have False using MMI_lt1nnn by simp
    } then have "\<not>(k\<ca>\<one> \<ls> \<one>\<ca>\<one>)" by auto
    hence
      "(k \<ls> \<one>\<ca>\<one> \<longrightarrow> k \<lsq> \<one>) \<longrightarrow> (k\<ca>\<one> \<ls> \<one>\<ca>\<one> \<longrightarrow> k \<ca> \<one> \<lsq> \<one>)"
      by simp
  } then have "\<forall>k\<in>\<nat>. 
      (k \<ls> \<one>\<ca>\<one> \<longrightarrow> k \<lsq> \<one>) \<longrightarrow> (k\<ca>\<one> \<ls> \<one>\<ca>\<one> \<longrightarrow> k \<ca> \<one> \<lsq> \<one>)"
    by simp
  moreover note A1
  ultimately show "n \<ls> \<one>\<ca>\<one> \<longrightarrow> n \<lsq> \<one>"
    by (rule nnind1)
qed

text\<open>Natural number greater than $1$ has a predecessor.\<close>

lemma (in MMIsar0) nat_ge1_has_pred: assumes A1: "n \<in> \<nat>"
  shows "\<one> \<ls> n \<longrightarrow> (\<exists>j\<in>\<nat>. n = j\<ca>\<one>)"
proof -
  from MMI_ax1re have "\<not>(\<one>\<ls>\<one>)" using MMI_ltnr by simp
  then have "\<one> \<ls> \<one> \<longrightarrow> (\<exists>j\<in>\<nat>. \<one> = j\<ca>\<one>)" by simp
  moreover
  { fix k assume A2: "k\<in>\<nat>" and A3: "\<one> \<ls> k \<longrightarrow> (\<exists>j\<in>\<nat>. k = j\<ca>\<one>)" and
    A4: "\<one> \<ls> k\<ca>\<one>"
    from A2 have "k=\<one> \<or> \<one>\<ls>k" using MMI_nngt1ne1t by simp
    moreover
    { assume "k=\<one>"
      then have "\<one>\<in>\<nat>" and "k\<ca>\<one> = \<one>\<ca>\<one>"
	using MMI_1nn by auto
      hence "\<exists>i\<in>\<nat>. k\<ca>\<one> = i\<ca>\<one>" by auto }
    moreover
    { assume "\<one> \<ls> k"
      with A3 obtain j where "j\<in>\<nat>" and "k = j\<ca>\<one>"
	by auto
      then have "j\<ca>\<one> \<in> \<nat>" and "k\<ca>\<one> = j\<ca>\<one>\<ca>\<one>"
	using MMI_peano2nn by auto
      then have "\<exists>i\<in>\<nat>. k\<ca>\<one> = i\<ca>\<one>" by auto }
    ultimately have "\<exists>i\<in>\<nat>. k\<ca>\<one> = i\<ca>\<one>" by auto
  } then have "\<forall>k\<in>\<nat>. 
      (\<one> \<ls> k \<longrightarrow> (\<exists>j\<in>\<nat>. k = j\<ca>\<one>)) \<longrightarrow> (\<one> \<ls> k\<ca>\<one> \<longrightarrow> (\<exists>i\<in>\<nat>. k\<ca>\<one> = i\<ca>\<one>))"
    by auto
  moreover note A1
  ultimately show "\<one> \<ls> n \<longrightarrow> (\<exists>j\<in>\<nat>. n = j\<ca>\<one>)"
    by (rule nnind1)
qed

text\<open>If the successor is smaller, then the number is smaller.\<close>

lemma (in MMIsar0) succ_le_imp_le: assumes A1: "a\<in>\<real>"   "b\<in>\<real>" and A2: "a\<ca>\<one> \<ls> b"
  shows "a\<ls>b"
proof -
  from A1 have T: "a\<in>\<real>"  "a\<ca>\<one> \<in> \<real>"  "b\<in>\<real>"
    using MMI_ax1re MMI_axaddrcl by auto
  moreover from A1 A2 have 
    "a \<ls> a\<ca>\<one>"   "a\<ca>\<one> \<ls> b"
    using num_le_numplus1 by auto
  ultimately show "a\<ls>b" using MMI_axlttrn by blast
qed
    
text\<open>For natural numbers greater numbers can be obtained by adding a natural number.\<close>

lemma (in MMIsar0) nat_ge_repr: assumes A1: "n \<in> \<nat>"  "m \<in> \<nat>"
  shows "m\<ls>n \<longrightarrow> (\<exists>j\<in>\<nat>. n = m \<ca> j)"
proof -
  { assume "\<one> \<ls> n"
    with A1 obtain k where I: "k\<in>\<nat>" and II: "n = k\<ca>\<one>"
      using nat_ge1_has_pred by auto
    with MMI_axaddcom MMI_ax1re MMI_axresscn have "k \<in> \<complex>" and "\<one> \<in> \<complex>"
      using MMI_nncn by auto
    with MMI_axaddcom I II have "\<exists>k\<in>\<nat>. n = \<one> \<ca> k"
      by auto
  } then have "\<one> \<ls> n \<longrightarrow> (\<exists>j\<in>\<nat>. n = \<one> \<ca> j)" by simp
  moreover
  { fix k assume A2: "k\<in>\<nat>" and 
    A3: "k\<ls>n \<longrightarrow> (\<exists>j\<in>\<nat>. n = k \<ca> j)" and A4: "k\<ca>\<one> \<ls> n"
    from A1 A2 have T: "n\<in>\<real>"  "k\<in>\<real>" using MMI_nnre by auto
    with A3 A4 obtain j where III: "j\<in>\<nat>" and IV: "n = k \<ca> j"
      using succ_le_imp_le by auto
    with A4 T III MMI_ax1re have "\<one> \<ls> j"
      using MMI_nnre MMI_ltadd2 by blast
    with III obtain i where V: "i\<in>\<nat>" and VI: "j = i\<ca>\<one>"
      using nat_ge1_has_pred by auto
    with IV have "n = k \<ca> (i\<ca>\<one>)" by simp
    moreover from V MMI_ax1re MMI_axresscn MMI_axaddcom have  
      "k \<ca> (i\<ca>\<one>) = k \<ca> (\<one>\<ca>i)"
      using MMI_nncn by auto
    moreover from T V MMI_ax1re MMI_axresscn MMI_axaddass have
      "k \<ca> \<one>\<ca>i = k \<ca> (\<one>\<ca>i)"
      using MMI_nncn by blast
    ultimately have "n = k \<ca> \<one>\<ca>i" by simp
    with V have "\<exists>i\<in>\<nat>. n = k\<ca>\<one> \<ca> i" by auto
  } then have "\<forall>k\<in>\<nat>. (k\<ls>n \<longrightarrow> (\<exists>j\<in>\<nat>. n = k \<ca> j)) \<longrightarrow> 
      (k\<ca>\<one> \<ls> n \<longrightarrow> (\<exists>i\<in>\<nat>. n = k\<ca>\<one> \<ca> i))" by simp
  moreover from A1 have "m \<in> \<nat>" by simp
  ultimately show "m\<ls>n \<longrightarrow> (\<exists>j\<in>\<nat>. n = m \<ca> j)"
    by (rule nnind1)
qed
  
text\<open>In natural numbers less $a+1$ implies less or equal $a$.\<close>

lemma (in MMIsar0) nat_ls_plus_one_imp_lsq:
  assumes A1: "n \<in> \<nat>"  "m \<in> \<nat>" and A2: "n \<ls> m\<ca>\<one>" 
  shows "n \<lsq> m"
proof -
  from MMI_1cn A1 have T: "m \<in> \<complex>"  "n \<in> \<complex>"  "\<one> \<in> \<complex>" 
    using MMI_nncn by auto
  from A1 have "m\<ca>\<one> \<in> \<nat>" using MMI_peano2nn by simp
  with A1 A2 obtain k where I: "k\<in>\<nat>" and II: "m\<ca>\<one> = n\<ca>k"
    using nat_ge_repr by auto
  then have "k = \<one> \<or> \<one>\<ls>k" using MMI_nngt1ne1t by auto
  moreover
  { assume "k=\<one>"
    with II T have "m = n" using MMI_addcan2 by simp }
  moreover
  { assume "\<one>\<ls>k"
    with I obtain i where III: "i\<in>\<nat>" and IV: "k = i\<ca>\<one>"
      using nat_ge1_has_pred by auto
    with A1 II III have "m\<ca>\<one> = n\<ca>i \<ca> \<one>"
      using MMI_nncn MMI_1cn MMI_axaddass by simp
    with MMI_axaddcl T III have "m = n\<ca>i" using MMI_nncn MMI_addcan2
      by auto
    moreover from A1 III have "n\<in>\<real>"  "i\<in>\<real>"   "\<zero> \<ls> i"
      using MMI_nnre MMI_nngt0t by auto
    ultimately have "n \<ls> m" using MMI_ltaddpost by auto }
  ultimately have "n=m \<or> n \<ls> m" by auto
  with A1 show "n \<lsq> m" using MMI_nnre MMI_leloet by auto
qed

(********* 516 - 520 *************************)
 
text\<open>The next theorem is the reason we proved the theorems above 
  (see the comment to \<open>num_le_numplus1\<close>.\<close>

lemma (in MMIsar0) MMI_nnleltp1t: 
  shows "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> A \<lsq> B \<longleftrightarrow> A \<ls> B \<ca> \<one>"
proof
  assume A1: "A \<in> \<nat> \<and> B \<in> \<nat>"
  then have "A \<lsq> B \<longrightarrow> A \<ls> B \<ca> \<one>" 
    using MMI_nnre lsq_imp_ls_plus1 by simp
  moreover from A1 have "A \<ls> B \<ca> \<one> \<longrightarrow> A \<lsq> B"
    using nat_ls_plus_one_imp_lsq by simp
  ultimately show  "A \<lsq> B \<longleftrightarrow> A \<ls> B \<ca> \<one>"
    by blast
qed

(* here is the original almost translated proof of nnleltp1t:

proof -
   have S1: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A \<ls> B \<or> A = B" by (rule MMI_leloet)
   have S2: "A \<in> \<nat> \<longrightarrow> A \<in> \<real>" by (rule MMI_nnret)
   have S3: "B \<in> \<nat> \<longrightarrow> B \<in> \<real>" by (rule MMI_nnret)
   from S1 S2 S3 have S4: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A \<ls> B \<or> A = B" by (rule MMI_syl2an)
   have S5: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   have S6: "\<zero> \<in> \<real>" by (rule MMI_0re)
   have S7: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S6 S7 have S8: "\<zero> \<in> \<real> \<and> \<one> \<in> \<real>" by (rule MMI_pm3_2i)
   have S9: "(A \<in> \<real> \<and> \<zero> \<in> \<real>) \<and> B \<in> \<real> \<and> \<one> \<in> \<real> \<longrightarrow> 
   A \<ls> B \<and> \<zero> \<ls> \<one> \<longrightarrow> 
   A \<ca> \<zero> \<ls> B \<ca> \<one>" by (rule MMI_lt2addt)
   from S9 have S10: "(A \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<in> \<real> \<and> \<one> \<in> \<real> \<longrightarrow> 
   A \<ls> B \<and> \<zero> \<ls> \<one> \<longrightarrow> 
   A \<ca> \<zero> \<ls> B \<ca> \<one>" by (rule MMI_an4s)
   from S8 S10 have S11: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ls> B \<and> \<zero> \<ls> \<one> \<longrightarrow> 
   A \<ca> \<zero> \<ls> B \<ca> \<one>" by (rule MMI_mpan2)
   from S5 S11 have S12: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ls> B \<longrightarrow> 
   A \<ca> \<zero> \<ls> B \<ca> \<one>" by (rule MMI_mpan2i)
   have S13: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<in> \<real>" by (rule MMI_pm3_26)
   have S14: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S15: "A \<in> \<complex> \<longrightarrow> A \<ca> \<zero> = A" by (rule MMI_ax0id)
   from S13 S14 S15 have S16: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<ca> \<zero> = A" by (rule MMI_3syl)
   from S16 have S17: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ca> \<zero> \<ls> B \<ca> \<one> \<longleftrightarrow> A \<ls> B \<ca> \<one>" by (rule MMI_breq1d)
   from S12 S17 have S18: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ls> B \<longrightarrow> A \<ls> B \<ca> \<one>" by (rule MMI_sylibd)
   have S19: "A = B \<longrightarrow> 
   A \<ls> B \<ca> \<one> \<longleftrightarrow> B \<ls> B \<ca> \<one>" by (rule MMI_breq1)
   have S20: "B \<in> \<real> \<longrightarrow> B \<ls> B \<ca> \<one>" by (rule MMI_ltp1t)
   from S19 S20 have S21: "A = B \<longrightarrow> 
   B \<in> \<real> \<longrightarrow> A \<ls> B \<ca> \<one>" by (rule MMI_syl5bir)
   from S21 have S22: "B \<in> \<real> \<longrightarrow> 
   A = B \<longrightarrow> A \<ls> B \<ca> \<one>" by (rule MMI_com12)
   from S22 have S23: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A = B \<longrightarrow> A \<ls> B \<ca> \<one>" by (rule MMI_adantl)
   from S18 S23 have S24: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ls> B \<or> A = B \<longrightarrow> A \<ls> B \<ca> \<one>" by (rule MMI_jaod)
   from S2 have S25: "A \<in> \<nat> \<longrightarrow> A \<in> \<real>" .
   from S3 have S26: "B \<in> \<nat> \<longrightarrow> B \<in> \<real>" .
   from S24 S25 S26 have S27: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   A \<ls> B \<or> A = B \<longrightarrow> A \<ls> B \<ca> \<one>" by (rule MMI_syl2an)
   { fix z
     have S28: "z = A \<longrightarrow> 
       z \<ls> B \<ca> \<one> \<longleftrightarrow> A \<ls> B \<ca> \<one>" by (rule MMI_breq1)
     have S29: "z = A \<longrightarrow> 
       z \<ls> B \<longleftrightarrow> A \<ls> B" by (rule MMI_breq1)
     have S30: "z = A \<longrightarrow> 
       z = B \<longleftrightarrow> A = B" by (rule MMI_eqeq1)
     from S29 S30 have S31: "z = A \<longrightarrow> 
       z \<ls> B \<or> z = B \<longleftrightarrow> A \<ls> B \<or> A = B" by (rule MMI_orbi12d)
     from S28 S31 have S32: "z = A \<longrightarrow> 
       (z \<ls> B \<ca> \<one> \<longrightarrow> z \<ls> B \<or> z = B) \<longleftrightarrow> 
       (A \<ls> B \<ca> \<one> \<longrightarrow> A \<ls> B \<or> A = B)" by (rule MMI_imbi12d)
     from S32 have S33: "A \<in> \<nat> \<longrightarrow> 
       (\<forall>z\<in>\<nat>. z \<ls> B \<ca> \<one> \<longrightarrow> z \<ls> B \<or> z = B) \<longrightarrow> 
       A \<ls> B \<ca> \<one> \<longrightarrow> A \<ls> B \<or> A = B" by auto; (rule MMI_rcla4v)
     { fix x
       have S34: "x = \<one> \<longrightarrow> 
	 x \<ca> \<one> = \<one> \<ca> \<one>" by (rule MMI_opreq1)
       from S34 have S35: "x = \<one> \<longrightarrow> 
	 z \<ls> x \<ca> \<one> \<longleftrightarrow> z \<ls> \<one> \<ca> \<one>" by (rule MMI_breq2d)
       have S36: "x = \<one> \<longrightarrow> 
	 z \<ls> x \<longleftrightarrow> z \<ls> \<one>" by (rule MMI_breq2)
       have S37: "x = \<one> \<longrightarrow> 
	 z = x \<longleftrightarrow> z = \<one>" by (rule MMI_eqeq2)
       from S36 S37 have S38: "x = \<one> \<longrightarrow> 
	 z \<ls> x \<or> z = x \<longleftrightarrow> 
	 z \<ls> \<one> \<or> z = \<one>" by (rule MMI_orbi12d)
       from S35 S38 have S39: "x = \<one> \<longrightarrow> 
	 (z \<ls> x \<ca> \<one> \<longrightarrow> z \<ls> x \<or> z = x) \<longleftrightarrow> 
	 (z \<ls> \<one> \<ca> \<one> \<longrightarrow> 
	 z \<ls> \<one> \<or> z = \<one>)" by (rule MMI_imbi12d)
       from S39 have S40: "x = \<one> \<longrightarrow> 
	 (\<forall>z\<in>\<nat>. z \<ls> x \<ca> \<one> \<longrightarrow> z \<ls> x \<or> z = x) \<longleftrightarrow> 
	 (\<forall>z\<in>\<nat>. z \<ls> \<one> \<ca> \<one> \<longrightarrow> 
	 z \<ls> \<one> \<or> z = \<one>)" by auto; (rule MMI_ralbidv)
       have S41: "x = y \<longrightarrow> 
	 x \<ca> \<one> = y \<ca> \<one>" by (rule MMI_opreq1)
       from S41 have S42: "x = y \<longrightarrow> 
	 z \<ls> x \<ca> \<one> \<longleftrightarrow> z \<ls> y \<ca> \<one>" by (rule MMI_breq2d)
       have S43: "x = y \<longrightarrow> 
	 z \<ls> x \<longleftrightarrow> z \<ls> y" by (rule MMI_breq2)
       have S44: "x = y \<longrightarrow> 
	 z = x \<longleftrightarrow> z = y" by (rule MMI_eqeq2)
       from S43 S44 have S45: "x = y \<longrightarrow> 
	 z \<ls> x \<or> z = x \<longleftrightarrow> z \<ls> y \<or> z = y" by (rule MMI_orbi12d)
       from S42 S45 have S46: "x = y \<longrightarrow> 
	 (z \<ls> x \<ca> \<one> \<longrightarrow> z \<ls> x \<or> z = x) \<longleftrightarrow> 
	 (z \<ls> y \<ca> \<one> \<longrightarrow> z \<ls> y \<or> z = y)" by (rule MMI_imbi12d)
       from S46 have S47: "x = y \<longrightarrow> 
	 (\<forall>z\<in>\<nat>. z \<ls> x \<ca> \<one> \<longrightarrow> z \<ls> x \<or> z = x) \<longleftrightarrow> 
	 (\<forall>z\<in>\<nat>. z \<ls> y \<ca> \<one> \<longrightarrow> z \<ls> y \<or> z = y)" by auto; (rule MMI_ralbidv)
       have S48: "x = y \<ca> \<one> \<longrightarrow> 
	 x \<ca> \<one> = y \<ca> \<one> \<ca> \<one>" by (rule MMI_opreq1)
       from S48 have S49: "x = y \<ca> \<one> \<longrightarrow> 
	 z \<ls> x \<ca> \<one> \<longleftrightarrow> 
	 z \<ls> y \<ca> \<one> \<ca> \<one>" by (rule MMI_breq2d)
       have S50: "x = y \<ca> \<one> \<longrightarrow> 
	 z \<ls> x \<longleftrightarrow> z \<ls> y \<ca> \<one>" by (rule MMI_breq2)
       have S51: "x = y \<ca> \<one> \<longrightarrow> 
	 z = x \<longleftrightarrow> z = y \<ca> \<one>" by (rule MMI_eqeq2)
       from S50 S51 have S52: "x = y \<ca> \<one> \<longrightarrow> 
	 z \<ls> x \<or> z = x \<longleftrightarrow> 
	 z \<ls> y \<ca> \<one> \<or> z = y \<ca> \<one>" by (rule MMI_orbi12d)
       from S49 S52 have S53: "x = y \<ca> \<one> \<longrightarrow> 
	 (z \<ls> x \<ca> \<one> \<longrightarrow> z \<ls> x \<or> z = x) \<longleftrightarrow> 
	 (z \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
	 z \<ls> y \<ca> \<one> \<or> z = y \<ca> \<one>)" by (rule MMI_imbi12d)
       from S53 have S54: "x = y \<ca> \<one> \<longrightarrow> 
	 (\<forall>z\<in>\<nat>. z \<ls> x \<ca> \<one> \<longrightarrow> z \<ls> x \<or> z = x) \<longleftrightarrow> 
	 (\<forall>z\<in>\<nat>. z \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
	 z \<ls> y \<ca> \<one> \<or> z = y \<ca> \<one>)" by auto; (rule MMI_ralbidv)
       have S55: "x = B \<longrightarrow> 
	 x \<ca> \<one> = B \<ca> \<one>" by (rule MMI_opreq1)
       from S55 have S56: "x = B \<longrightarrow> 
	 z \<ls> x \<ca> \<one> \<longleftrightarrow> z \<ls> B \<ca> \<one>" by (rule MMI_breq2d)
       have S57: "x = B \<longrightarrow> 
	 z \<ls> x \<longleftrightarrow> z \<ls> B" by (rule MMI_breq2)
       have S58: "x = B \<longrightarrow> 
	 z = x \<longleftrightarrow> z = B" by (rule MMI_eqeq2)
       from S57 S58 have S59: "x = B \<longrightarrow> 
	 z \<ls> x \<or> z = x \<longleftrightarrow> z \<ls> B \<or> z = B" by (rule MMI_orbi12d)
       from S56 S59 have S60: "x = B \<longrightarrow> 
	 (z \<ls> x \<ca> \<one> \<longrightarrow> z \<ls> x \<or> z = x) \<longleftrightarrow> 
	 (z \<ls> B \<ca> \<one> \<longrightarrow> z \<ls> B \<or> z = B)" by (rule MMI_imbi12d)
       from S60 have S61: "x = B \<longrightarrow> 
	 (\<forall>z\<in>\<nat>. z \<ls> x \<ca> \<one> \<longrightarrow> z \<ls> x \<or> z = x) \<longleftrightarrow> 
	 (\<forall>z\<in>\<nat>. z \<ls> B \<ca> \<one> \<longrightarrow> z \<ls> B \<or> z = B)" by auto; (rule MMI_ralbidv)
       have S62: "x = \<one> \<longrightarrow> 
	 x \<ls> \<one> \<ca> \<one> \<longleftrightarrow> 
	 \<one> \<ls> \<one> \<ca> \<one>" by (rule MMI_breq1)
       have S63: "x = \<one> \<longrightarrow> 
	 x \<ls> \<one> \<longleftrightarrow> \<one> \<ls> \<one>" by (rule MMI_breq1)
       have S64: "x = \<one> \<longrightarrow> 
	 x = \<one> \<longleftrightarrow> \<one> = \<one>" by (rule MMI_eqeq1)
       from S63 S64 have S65: "x = \<one> \<longrightarrow> 
	 x \<ls> \<one> \<or> x = \<one> \<longleftrightarrow> 
	 \<one> \<ls> \<one> \<or> \<one> = \<one>" by (rule MMI_orbi12d)
       from S62 S65 have 
	 "x = \<one> \<longrightarrow>  (x \<ls> \<one> \<ca> \<one> \<longrightarrow>  x \<ls> \<one> \<or> x = \<one>) \<longleftrightarrow>  (\<one> \<ls> \<one> \<ca> \<one> \<longrightarrow> \<one> \<ls> \<one> \<or> \<one> = \<one>)" 
	 by (rule MMI_imbi12d)
     } then have S66: 
	 "\<forall> x. x = \<one> \<longrightarrow>  (x \<ls> \<one> \<ca> \<one> \<longrightarrow>  x \<ls> \<one> \<or> x = \<one>) \<longleftrightarrow> 
	 (\<one> \<ls> \<one> \<ca> \<one> \<longrightarrow> \<one> \<ls> \<one> \<or> \<one> = \<one>)"
       by simp;
     { fix x y
       have S67: "x = y \<ca> \<one> \<longrightarrow> 
	 x \<ls> \<one> \<ca> \<one> \<longleftrightarrow> 
	 y \<ca> \<one> \<ls> \<one> \<ca> \<one>" by (rule MMI_breq1);
       have S68: "x = y \<ca> \<one> \<longrightarrow> 
	 x \<ls> \<one> \<longleftrightarrow> y \<ca> \<one> \<ls> \<one>" by (rule MMI_breq1)
       have S69: "x = y \<ca> \<one> \<longrightarrow> 
	 x = \<one> \<longleftrightarrow> y \<ca> \<one> = \<one>" by (rule MMI_eqeq1)
       from S68 S69 have S70: "x = y \<ca> \<one> \<longrightarrow> 
	 x \<ls> \<one> \<or> x = \<one> \<longleftrightarrow> 
	 y \<ca> \<one> \<ls> \<one> \<or> y \<ca> \<one> = \<one>" by (rule MMI_orbi12d);
       from S67 S70 have S71: "x = y \<ca> \<one> \<longrightarrow> 
	 (x \<ls> \<one> \<ca> \<one> \<longrightarrow> 
	 x \<ls> \<one> \<or> x = \<one>) \<longleftrightarrow> 
	 (y \<ca> \<one> \<ls> \<one> \<ca> \<one> \<longrightarrow> 
	 y \<ca> \<one> \<ls> \<one> \<or> y \<ca> \<one> = \<one>)" by (rule MMI_imbi12d)
     } then have S71: "\<forall>x y. x = y \<ca> \<one> \<longrightarrow> 
	 (x \<ls> \<one> \<ca> \<one> \<longrightarrow> 
	 x \<ls> \<one> \<or> x = \<one>) \<longleftrightarrow> 
	 (y \<ca> \<one> \<ls> \<one> \<ca> \<one> \<longrightarrow> 
	 y \<ca> \<one> \<ls> \<one> \<or> y \<ca> \<one> = \<one>)" by simp;
     { fix x
       have S72: "x = z \<longrightarrow> 
	 x \<ls> \<one> \<ca> \<one> \<longleftrightarrow> z \<ls> \<one> \<ca> \<one>" by (rule MMI_breq1)
       have S73: "x = z \<longrightarrow> 
	 x \<ls> \<one> \<longleftrightarrow> z \<ls> \<one>" by (rule MMI_breq1)
       have S74: "x = z \<longrightarrow> 
	 x = \<one> \<longleftrightarrow> z = \<one>" by (rule MMI_eqeq1)
       from S73 S74 have S75: "x = z \<longrightarrow> 
	 x \<ls> \<one> \<or> x = \<one> \<longleftrightarrow> 
	 z \<ls> \<one> \<or> z = \<one>" by (rule MMI_orbi12d)
       from S72 S75 have "x = z \<longrightarrow> 
	 (x \<ls> \<one> \<ca> \<one> \<longrightarrow> 
	 x \<ls> \<one> \<or> x = \<one>) \<longleftrightarrow> 
	 (z \<ls> \<one> \<ca> \<one> \<longrightarrow> 
	 z \<ls> \<one> \<or> z = \<one>)" by (rule MMI_imbi12d)
     } then have S76: "\<forall> x. x = z \<longrightarrow> 
	 (x \<ls> \<one> \<ca> \<one> \<longrightarrow> 
	 x \<ls> \<one> \<or> x = \<one>) \<longleftrightarrow> 
	 (z \<ls> \<one> \<ca> \<one> \<longrightarrow> 
	 z \<ls> \<one> \<or> z = \<one>)" by simp;
     have S77: "\<one> = \<one>" by (rule MMI_eqid)
     from S77 have S78: "\<not>(\<one> \<ls> \<one>) \<longrightarrow> \<one> = \<one>" by (rule MMI_a1i)
     from S78 have S79: "\<one> \<ls> \<one> \<or> \<one> = \<one>" by (rule MMI_orri)
     from S79 have S80: "\<one> \<ls> \<one> \<ca> \<one> \<longrightarrow> 
       \<one> \<ls> \<one> \<or> \<one> = \<one>" by (rule MMI_a1i)
     { fix y
       have S81: "y \<in> \<nat> \<longrightarrow> y \<in> \<real>" by (rule MMI_nnret)
       have S82: "\<one> \<in> \<real>" by (rule MMI_ax1re)
       have S83: "\<one> \<in> \<real>" by (rule MMI_ax1re)
       have S84: "y \<in> \<real> \<and> \<one> \<in> \<real> \<and> \<one> \<in> \<real> \<longrightarrow> 
	 y \<ls> \<one> \<longleftrightarrow> 
	 y \<ca> \<one> \<ls> \<one> \<ca> \<one>" by (rule MMI_ltadd1t)
       from S82 S83 S84 have S85: "y \<in> \<real> \<longrightarrow> 
	 y \<ls> \<one> \<longleftrightarrow> 
	 y \<ca> \<one> \<ls> \<one> \<ca> \<one>" by (rule MMI_mp3an23)
       from S81 S85 have S86: "y \<in> \<nat> \<longrightarrow> 
	 y \<ls> \<one> \<longleftrightarrow> 
	 y \<ca> \<one> \<ls> \<one> \<ca> \<one>" by (rule MMI_syl)
       have S87: "y \<in> \<nat> \<longrightarrow> \<one> \<lsq> y" by (rule MMI_nnge1t)
       from S81 have S88: "y \<in> \<nat> \<longrightarrow> y \<in> \<real>" .
       have S89: "\<one> \<in> \<real>" by (rule MMI_ax1re)
       have S90: "\<one> \<in> \<real> \<and> y \<in> \<real> \<longrightarrow> 
	 \<one> \<lsq> y \<longleftrightarrow> \<not>(y \<ls> \<one>)" by (rule MMI_lenltt)
       from S89 S90 have S91: "y \<in> \<real> \<longrightarrow> 
	 \<one> \<lsq> y \<longleftrightarrow> \<not>(y \<ls> \<one>)" by (rule MMI_mpan)
       from S88 S91 have S92: "y \<in> \<nat> \<longrightarrow> 
	 \<one> \<lsq> y \<longleftrightarrow> \<not>(y \<ls> \<one>)" by (rule MMI_syl)
       from S87 S92 have S93: "y \<in> \<nat> \<longrightarrow> \<not>(y \<ls> \<one>)" by (rule MMI_mpbid)
       from S93 have S94: "y \<in> \<nat> \<longrightarrow> 
	 y \<ls> \<one> \<longrightarrow> 
	 y \<ca> \<one> \<ls> \<one> \<or> y \<ca> \<one> = \<one>" by (rule MMI_pm2_21d)
       from S86 S94 have "y \<in> \<nat> \<longrightarrow> 
	 y \<ca> \<one> \<ls> \<one> \<ca> \<one> \<longrightarrow> 
	 y \<ca> \<one> \<ls> \<one> \<or> y \<ca> \<one> = \<one>" by (rule MMI_sylbird)
     } then have  S95: "\<forall> y. y \<in> \<nat> \<longrightarrow> 
	 y \<ca> \<one> \<ls> \<one> \<ca> \<one> \<longrightarrow> 
	 y \<ca> \<one> \<ls> \<one> \<or> y \<ca> \<one> = \<one>" by simp;
     from S66 S71 S76 S80 S95 have "z \<in> \<nat> \<longrightarrow> 
       z \<ls> \<one> \<ca> \<one> \<longrightarrow> 
       z \<ls> \<one> \<or> z = \<one>" by (rule MMI_nn1suc);
   } then have  S96: "\<forall>z. z \<in> \<nat> \<longrightarrow>  z \<ls> \<one> \<ca> \<one> \<longrightarrow> z \<ls> \<one> \<or> z = \<one>"
     by simp;       
   from S96 have S97: "\<forall>z\<in>\<nat>. z \<ls> \<one> \<ca> \<one> \<longrightarrow> 
     z \<ls> \<one> \<or> z = \<one>" by (rule MMI_rgen);
   { fix x
     have S98: "x = \<one> \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<ca> \<one> \<longleftrightarrow> 
       \<one> \<ls> y \<ca> \<one> \<ca> \<one>" by (rule MMI_breq1)
     have S99: "x = \<one> \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<longleftrightarrow> \<one> \<ls> y \<ca> \<one>" by (rule MMI_breq1)
     have S100: "x = \<one> \<longrightarrow> 
       x = y \<ca> \<one> \<longleftrightarrow> \<one> = y \<ca> \<one>" by (rule MMI_eqeq1)
     from S99 S100 have S101: "x = \<one> \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<or> x = y \<ca> \<one> \<longleftrightarrow> 
       \<one> \<ls> y \<ca> \<one> \<or> \<one> = y \<ca> \<one>" by (rule MMI_orbi12d)
     from S98 S101 have S102: "x = \<one> \<longrightarrow> 
       (x \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<or> x = y \<ca> \<one>) \<longleftrightarrow> 
       (\<one> \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       \<one> \<ls> y \<ca> \<one> \<or> \<one> = y \<ca> \<one>)" by (rule MMI_imbi12d)
     from S102 have "x = \<one> \<longrightarrow> 
       (y \<in> \<nat> \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<or> x = y \<ca> \<one>) \<longleftrightarrow> 
       (y \<in> \<nat> \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       \<one> \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       \<one> \<ls> y \<ca> \<one> \<or> \<one> = y \<ca> \<one>)" by (rule MMI_imbi2d)
   } then have S103: "\<forall> x. x = \<one> \<longrightarrow> 
       (y \<in> \<nat> \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<or> x = y \<ca> \<one>) \<longleftrightarrow> 
       (y \<in> \<nat> \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       \<one> \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       \<one> \<ls> y \<ca> \<one> \<or> \<one> = y \<ca> \<one>)" by simp;
   { fix x v
     have S104: "x = v \<ca> \<one> \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<ca> \<one> \<longleftrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<ca> \<one>" by (rule MMI_breq1)
     have S105: "x = v \<ca> \<one> \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<longleftrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one>" by (rule MMI_breq1)
     have S106: "x = v \<ca> \<one> \<longrightarrow> 
       x = y \<ca> \<one> \<longleftrightarrow> 
       v \<ca> \<one> = y \<ca> \<one>" by (rule MMI_eqeq1)
     from S105 S106 have S107: "x = v \<ca> \<one> \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<or> x = y \<ca> \<one> \<longleftrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<or> v \<ca> \<one> = y \<ca> \<one>" by (rule MMI_orbi12d)
     from S104 S107 have S108: "x = v \<ca> \<one> \<longrightarrow> 
       (x \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<or> x = y \<ca> \<one>) \<longleftrightarrow> 
       (v \<ca> \<one> \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<or> v \<ca> \<one> = y \<ca> \<one>)" by (rule MMI_imbi12d)
     from S108 have "x = v \<ca> \<one> \<longrightarrow> 
       (y \<in> \<nat> \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<or> x = y \<ca> \<one>) \<longleftrightarrow> 
       (y \<in> \<nat> \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<or> v \<ca> \<one> = y \<ca> \<one>)" by (rule MMI_imbi2d)
   } then have S109: "\<forall>x v. x = v \<ca> \<one> \<longrightarrow> 
       (y \<in> \<nat> \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<or> x = y \<ca> \<one>) \<longleftrightarrow> 
       (y \<in> \<nat> \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<or> v \<ca> \<one> = y \<ca> \<one>)"
     by simp;
   { fix x
     have S110: "x = z \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<ca> \<one> \<longleftrightarrow> 
       z \<ls> y \<ca> \<one> \<ca> \<one>" by (rule MMI_breq1)
     have S111: "x = z \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<longleftrightarrow> z \<ls> y \<ca> \<one>" by (rule MMI_breq1)
     have S112: "x = z \<longrightarrow> 
       x = y \<ca> \<one> \<longleftrightarrow> z = y \<ca> \<one>" by (rule MMI_eqeq1)
     from S111 S112 have S113: "x = z \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<or> x = y \<ca> \<one> \<longleftrightarrow> 
       z \<ls> y \<ca> \<one> \<or> z = y \<ca> \<one>" by (rule MMI_orbi12d)
     from S110 S113 have S114: "x = z \<longrightarrow> 
       (x \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<or> x = y \<ca> \<one>) \<longleftrightarrow> 
   (z \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       z \<ls> y \<ca> \<one> \<or> z = y \<ca> \<one>)" by (rule MMI_imbi12d)
     from S114 have "x = z \<longrightarrow> 
       (y \<in> \<nat> \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<or> x = y \<ca> \<one>) \<longleftrightarrow> 
       (y \<in> \<nat> \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       z \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       z \<ls> y \<ca> \<one> \<or> z = y \<ca> \<one>)" by (rule MMI_imbi2d)
     } then have S115: "\<forall>x. x = z \<longrightarrow> 
       (y \<in> \<nat> \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       x \<ls> y \<ca> \<one> \<or> x = y \<ca> \<one>) \<longleftrightarrow> 
       (y \<in> \<nat> \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       z \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       z \<ls> y \<ca> \<one> \<or> z = y \<ca> \<one>)" by simp;
     have S116: "y \<in> \<nat> \<longrightarrow> \<zero> \<ls> y" by (rule MMI_nngt0t)
     have S117: "y \<in> \<nat> \<longrightarrow> y \<in> \<real>" by (rule MMI_nnret);
     have S118: "\<zero> \<in> \<real>" by (rule MMI_0re)
     have S119: "\<one> \<in> \<real>" by (rule MMI_ax1re)
     have S120: "\<zero> \<in> \<real> \<and> y \<in> \<real> \<and> \<one> \<in> \<real> \<longrightarrow> 
       \<zero> \<ls> y \<longleftrightarrow> 
       \<zero> \<ca> \<one> \<ls> y \<ca> \<one>" by (rule MMI_ltadd1t)
     from S118 S119 S120 have S121: "y \<in> \<real> \<longrightarrow> 
       \<zero> \<ls> y \<longleftrightarrow> 
       \<zero> \<ca> \<one> \<ls> y \<ca> \<one>" by (rule MMI_mp3an13)
     from S117 S121 have S122: "y \<in> \<nat> \<longrightarrow> 
       \<zero> \<ls> y \<longleftrightarrow> 
       \<zero> \<ca> \<one> \<ls> y \<ca> \<one>" by (rule MMI_syl)
     from S116 S122 have S123: "y \<in> \<nat> \<longrightarrow> 
       \<zero> \<ca> \<one> \<ls> y \<ca> \<one>" by (rule MMI_mpbid)
     have S124: "\<one> \<in> \<complex>" by (rule MMI_1cn)
     from S124 have S125: "\<zero> \<ca> \<one> = \<one>" by (rule MMI_addid2)
     from S123 S125 have S126: "y \<in> \<nat> \<longrightarrow> \<one> \<ls> y \<ca> \<one>" by (rule MMI_syl5eqbrr)
     from S126 have S127: "y \<in> \<nat> \<longrightarrow> 
       \<not>(\<one> \<ls> y \<ca> \<one>) \<longrightarrow> \<one> = y \<ca> \<one>" by (rule MMI_pm2_21nd)
     from S127 have S128: "y \<in> \<nat> \<longrightarrow> 
       \<one> \<ls> y \<ca> \<one> \<or> \<one> = y \<ca> \<one>" by (rule MMI_orrd)
     from S128 have S129: "y \<in> \<nat> \<longrightarrow> 
       \<one> \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       \<one> \<ls> y \<ca> \<one> \<or> \<one> = y \<ca> \<one>" by (rule MMI_a1d)
     from S129 have S130: "y \<in> \<nat> \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
   \<one> \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       \<one> \<ls> y \<ca> \<one> \<or> \<one> = y \<ca> \<one>" by (rule MMI_adantr)
     { fix v
       have S131: "w = v \<longrightarrow> 
	 w \<ls> y \<ca> \<one> \<longleftrightarrow> v \<ls> y \<ca> \<one>" by (rule MMI_breq1);
       have S132: "w = v \<longrightarrow> 
	 w \<ls> y \<longleftrightarrow> v \<ls> y" by (rule MMI_breq1)
       have S133: "w = v \<longrightarrow> 
	 w = y \<longleftrightarrow> v = y" by (rule MMI_eqeq1)
       from S132 S133 have S134: "w = v \<longrightarrow> 
	 w \<ls> y \<or> w = y \<longleftrightarrow> v \<ls> y \<or> v = y" by (rule MMI_orbi12d)
       from S131 S134 have S135: "w = v \<longrightarrow> 
	 (w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longleftrightarrow> 
	 (v \<ls> y \<ca> \<one> \<longrightarrow> v \<ls> y \<or> v = y)" by (rule MMI_imbi12d)
       from S135 have S136: "v \<in> \<nat> \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
	 v \<ls> y \<ca> \<one> \<longrightarrow> v \<ls> y \<or> v = y" by auto; (rule MMI_rcla4va)
       from S136 have S137: "(v \<in> \<nat> \<and> y \<in> \<nat>) \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
	 v \<ls> y \<ca> \<one> \<longrightarrow> v \<ls> y \<or> v = y" by (rule MMI_adantlr)
       have S138: "\<one> \<in> \<real>" by (rule MMI_ax1re)
       have S139: "v \<in> \<real> \<and> y \<ca> \<one> \<in> \<real> \<and> \<one> \<in> \<real> \<longrightarrow> 
	 v \<ls> y \<ca> \<one> \<longleftrightarrow> 
	 v \<ca> \<one> \<ls> y \<ca> \<one> \<ca> \<one>" by (rule MMI_ltadd1t)
       from S138 S139 have S140: "v \<in> \<real> \<and> y \<ca> \<one> \<in> \<real> \<longrightarrow> 
	 v \<ls> y \<ca> \<one> \<longleftrightarrow> 
	 v \<ca> \<one> \<ls> y \<ca> \<one> \<ca> \<one>" by (rule MMI_mp3an3)
       have S141: "v \<in> \<nat> \<longrightarrow> v \<in> \<real>" by (rule MMI_nnret)
       have S142: "y \<in> \<nat> \<longrightarrow> y \<ca> \<one> \<in> \<nat>" by (rule MMI_peano2nn)
     have S143: "y \<ca> \<one> \<in> \<nat> \<longrightarrow> y \<ca> \<one> \<in> \<real>" by (rule MMI_nnret)
     from S142 S143 have S144: "y \<in> \<nat> \<longrightarrow> y \<ca> \<one> \<in> \<real>" by (rule MMI_syl)
     from S140 S141 S144 have S145: "v \<in> \<nat> \<and> y \<in> \<nat> \<longrightarrow> 
       v \<ls> y \<ca> \<one> \<longleftrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<ca> \<one>" by (rule MMI_syl2an)
     from S145 have S146: "(v \<in> \<nat> \<and> y \<in> \<nat>) \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       v \<ls> y \<ca> \<one> \<longleftrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<ca> \<one>" by (rule MMI_adantr)
     have S147: "\<one> \<in> \<real>" by (rule MMI_ax1re)
     have S148: "v \<in> \<real> \<and> y \<in> \<real> \<and> \<one> \<in> \<real> \<longrightarrow> 
       v \<ls> y \<longleftrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one>" by (rule MMI_ltadd1t)
     have S149: "v \<in> \<real> \<longrightarrow> v \<in> \<complex>" by (rule MMI_recnt)
     have S150: "y \<in> \<real> \<longrightarrow> y \<in> \<complex>" by (rule MMI_recnt)
     have S151: "\<one> \<in> \<real> \<longrightarrow> \<one> \<in> \<complex>" by (rule MMI_recnt)
     from S149 S150 S151 have S152: "v \<in> \<real> \<and> y \<in> \<real> \<and> \<one> \<in> \<real> \<longrightarrow> 
       v \<in> \<complex> \<and> y \<in> \<complex> \<and> \<one> \<in> \<complex>" by (rule MMI_3anim123i)
     have S153: "\<one> \<in> \<complex> \<and> v \<in> \<complex> \<and> y \<in> \<complex> \<longleftrightarrow> 
       v \<in> \<complex> \<and> y \<in> \<complex> \<and> \<one> \<in> \<complex>" by (rule MMI_3anrot)
     from S152 S153 have S154: "v \<in> \<real> \<and> y \<in> \<real> \<and> \<one> \<in> \<real> \<longrightarrow> 
       \<one> \<in> \<complex> \<and> v \<in> \<complex> \<and> y \<in> \<complex>" by (rule MMI_sylibr)
     have S155: "\<one> \<in> \<complex> \<and> v \<in> \<complex> \<and> y \<in> \<complex> \<longrightarrow> 
       v \<in> \<complex> \<and> y \<in> \<complex>" by (rule MMI_3simpc)
     have S156: "\<one> \<in> \<complex> \<and> v \<in> \<complex> \<and> y \<in> \<complex> \<longrightarrow> \<one> \<in> \<complex>" by (rule MMI_3simp1)
     from S155 S156 have S157: "\<one> \<in> \<complex> \<and> v \<in> \<complex> \<and> y \<in> \<complex> \<longrightarrow> 
       (v \<in> \<complex> \<and> y \<in> \<complex>) \<and> \<one> \<in> \<complex>" by (rule MMI_jca)
     have S158: "(v \<in> \<complex> \<and> y \<in> \<complex>) \<and> \<one> \<in> \<complex> \<longleftrightarrow> 
       (v \<in> \<complex> \<and> \<one> \<in> \<complex>) \<and> y \<in> \<complex> \<and> \<one> \<in> \<complex>" by (rule MMI_anandir)
     from S157 S158 have S159: "\<one> \<in> \<complex> \<and> v \<in> \<complex> \<and> y \<in> \<complex> \<longrightarrow> 
       (v \<in> \<complex> \<and> \<one> \<in> \<complex>) \<and> y \<in> \<complex> \<and> \<one> \<in> \<complex>" by (rule MMI_sylib)
     have S160: "v \<in> \<complex> \<and> \<one> \<in> \<complex> \<longrightarrow> 
       v \<ca> \<one> = \<one> \<ca> v" by (rule MMI_axaddcom)
     have S161: "y \<in> \<complex> \<and> \<one> \<in> \<complex> \<longrightarrow> 
       y \<ca> \<one> = \<one> \<ca> y" by (rule MMI_axaddcom)
     from S160 S161 have S162: "(v \<in> \<complex> \<and> \<one> \<in> \<complex>) \<and> y \<in> \<complex> \<and> \<one> \<in> \<complex> \<longrightarrow> 
       v \<ca> \<one> = y \<ca> \<one> \<longleftrightarrow> 
       \<one> \<ca> v = \<one> \<ca> y" by (rule MMI_eqeqan12d);
     from S159 S162 have S163: "\<one> \<in> \<complex> \<and> v \<in> \<complex> \<and> y \<in> \<complex> \<longrightarrow> 
       v \<ca> \<one> = y \<ca> \<one> \<longleftrightarrow> 
       \<one> \<ca> v = \<one> \<ca> y" by (rule MMI_syl)
     have S164: "\<one> \<in> \<complex> \<and> v \<in> \<complex> \<and> y \<in> \<complex> \<longrightarrow> 
       \<one> \<ca> v = \<one> \<ca> y \<longleftrightarrow> v = y" by (rule MMI_addcant)
     from S163 S164 have S165: "\<one> \<in> \<complex> \<and> v \<in> \<complex> \<and> y \<in> \<complex> \<longrightarrow> 
       v = y \<longleftrightarrow> 
       v \<ca> \<one> = y \<ca> \<one>" by (rule MMI_bitr2d)
     from S154 S165 have S166: "v \<in> \<real> \<and> y \<in> \<real> \<and> \<one> \<in> \<real> \<longrightarrow> 
       v = y \<longleftrightarrow> 
       v \<ca> \<one> = y \<ca> \<one>" by (rule MMI_syl)
     from S148 S166 have S167: "v \<in> \<real> \<and> y \<in> \<real> \<and> \<one> \<in> \<real> \<longrightarrow> 
       v \<ls> y \<or> v = y \<longleftrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<or> v \<ca> \<one> = y \<ca> \<one>" by (rule MMI_orbi12d)
     from S147 S167 have S168: "v \<in> \<real> \<and> y \<in> \<real> \<longrightarrow> 
       v \<ls> y \<or> v = y \<longleftrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<or> v \<ca> \<one> = y \<ca> \<one>" by (rule MMI_mp3an3)
     from S141 have S169: "v \<in> \<nat> \<longrightarrow> v \<in> \<real>" .
     have S170: "y \<in> \<nat> \<longrightarrow> y \<in> \<real>" by (rule MMI_nnret);
     from S168 S169 S170 have S171: "v \<in> \<nat> \<and> y \<in> \<nat> \<longrightarrow> 
       v \<ls> y \<or> v = y \<longleftrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<or> v \<ca> \<one> = y \<ca> \<one>" by (rule MMI_syl2an)
     from S171 have S172: "(v \<in> \<nat> \<and> y \<in> \<nat>) \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       v \<ls> y \<or> v = y \<longleftrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<or> v \<ca> \<one> = y \<ca> \<one>" by (rule MMI_adantr)
     from S137 S146 S172 have S173: "(v \<in> \<nat> \<and> y \<in> \<nat>) \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<or> v \<ca> \<one> = y \<ca> \<one>" by (rule MMI_3imtr3d)
     from S173 have S174: "v \<in> \<nat> \<longrightarrow> 
       y \<in> \<nat> \<longrightarrow> 
       (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<or> v \<ca> \<one> = y \<ca> \<one>" by (rule MMI_exp31)
     from S174 have "v \<in> \<nat> \<longrightarrow> 
       y \<in> \<nat> \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<or> v \<ca> \<one> = y \<ca> \<one>" by (rule MMI_imp3a)
   } then have S175: "\<forall> v. v \<in> \<nat> \<longrightarrow> 
       ( y \<in> \<nat> \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
       v \<ca> \<one> \<ls> y \<ca> \<one> \<or> v \<ca> \<one> = y \<ca> \<one> )" by simp;
   from S103 S109 S115 S130 S175 have S176: "z \<in> \<nat> \<longrightarrow> 
   ( y \<in> \<nat> \<and> (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
   z \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
   z \<ls> y \<ca> \<one> \<or> z = y \<ca> \<one>)" 
 ************ this is where Isabelle stops ********************
 ********* if you know how to fix it, please let me know ******
 by (rule MMI_nn1suc)

   from S176 have S177: "z \<in> \<nat> \<longrightarrow> 
   y \<in> \<nat> \<longrightarrow> 
   (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
   z \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
   z \<ls> y \<ca> \<one> \<or> z = y \<ca> \<one>" by (rule MMI_exp3a);
   from S177 have S178: "y \<in> \<nat> \<longrightarrow> 
   (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
   z \<in> \<nat> \<longrightarrow> 
   z \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
   z \<ls> y \<ca> \<one> \<or> z = y \<ca> \<one>" by (rule MMI_com3l)
   from S178 have S179: "y \<in> \<nat> \<longrightarrow> 
   (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y) \<longrightarrow> 
   (\<forall>z\<in>\<nat>. z \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
   z \<ls> y \<ca> \<one> \<or> z = y \<ca> \<one>)" by (rule MMI_r19_21adv)
   have S180: "z = w \<longrightarrow> 
   z \<ls> y \<ca> \<one> \<longleftrightarrow> w \<ls> y \<ca> \<one>" by (rule MMI_breq1)
   have S181: "z = w \<longrightarrow> 
   z \<ls> y \<longleftrightarrow> w \<ls> y" by (rule MMI_breq1)
   have S182: "z = w \<longrightarrow> 
   z = y \<longleftrightarrow> w = y" by (rule MMI_eqeq1)
   from S181 S182 have S183: "z = w \<longrightarrow> 
   z \<ls> y \<or> z = y \<longleftrightarrow> w \<ls> y \<or> w = y" by (rule MMI_orbi12d)
   from S180 S183 have S184: "z = w \<longrightarrow> 
   (z \<ls> y \<ca> \<one> \<longrightarrow> z \<ls> y \<or> z = y) \<longleftrightarrow> 
   (w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y)" by (rule MMI_imbi12d)
   from S184 have S185: "(\<forall>z\<in>\<nat>. z \<ls> y \<ca> \<one> \<longrightarrow> z \<ls> y \<or> z = y) \<longleftrightarrow> 
   (\<forall>w\<in>\<nat>. w \<ls> y \<ca> \<one> \<longrightarrow> w \<ls> y \<or> w = y)" by (rule MMI_cbvralv)
   from S179 S185 have S186: "y \<in> \<nat> \<longrightarrow> 
   (\<forall>z\<in>\<nat>. z \<ls> y \<ca> \<one> \<longrightarrow> z \<ls> y \<or> z = y) \<longrightarrow> 
   (\<forall>z\<in>\<nat>. z \<ls> y \<ca> \<one> \<ca> \<one> \<longrightarrow> 
   z \<ls> y \<ca> \<one> \<or> z = y \<ca> \<one>)" by (rule MMI_syl5ib)
   from S40 S47 S54 S61 S97 S186 have S187: "B \<in> \<nat> \<longrightarrow> 
   (\<forall>z\<in>\<nat>. z \<ls> B \<ca> \<one> \<longrightarrow> z \<ls> B \<or> z = B)" by (rule MMI_nnind)
   from S33 S187 have S188: "A \<in> \<nat> \<longrightarrow> 
   B \<in> \<nat> \<longrightarrow> 
   A \<ls> B \<ca> \<one> \<longrightarrow> A \<ls> B \<or> A = B" by (rule MMI_syl5)
   from S188 have S189: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   A \<ls> B \<ca> \<one> \<longrightarrow> A \<ls> B \<or> A = B" by (rule MMI_imp)
   from S27 S189 have S190: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   A \<ls> B \<or> A = B \<longleftrightarrow> A \<ls> B \<ca> \<one>" by (rule MMI_impbid)
   from S4 S190 show "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   A \<lsq> B \<longleftrightarrow> A \<ls> B \<ca> \<one>" by (rule MMI_bitrd)
qed; *)


lemma (in MMIsar0) MMI_nnltp1let: 
   shows "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A \<ca> \<one> \<lsq> B"
proof -
   have S1: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S2: "A \<in> \<real> \<and> B \<in> \<real> \<and> \<one> \<in> \<real> \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   A \<ca> \<one> \<ls> B \<ca> \<one>" by (rule MMI_ltadd1t)
   from S1 S2 have S3: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   A \<ca> \<one> \<ls> B \<ca> \<one>" by (rule MMI_mp3an3)
   have S4: "A \<in> \<nat> \<longrightarrow> A \<in> \<real>" by (rule MMI_nnret)
   have S5: "B \<in> \<nat> \<longrightarrow> B \<in> \<real>" by (rule MMI_nnret)
   from S3 S4 S5 have S6: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   A \<ca> \<one> \<ls> B \<ca> \<one>" by (rule MMI_syl2an)
   have S7: "A \<ca> \<one> \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   A \<ca> \<one> \<lsq> B \<longleftrightarrow> 
   A \<ca> \<one> \<ls> B \<ca> \<one>" by (rule MMI_nnleltp1t)
   have S8: "A \<in> \<nat> \<longrightarrow> A \<ca> \<one> \<in> \<nat>" by (rule MMI_peano2nn)
   from S7 S8 have S9: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   A \<ca> \<one> \<lsq> B \<longleftrightarrow> 
   A \<ca> \<one> \<ls> B \<ca> \<one>" by (rule MMI_sylan)
   from S6 S9 show "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A \<ca> \<one> \<lsq> B" by (rule MMI_bitr4d)
qed

lemma (in MMIsar0) MMI_nnsub: assumes A1: "A \<in> \<nat>" and
    A2: "B \<in> \<nat>"   
   shows "A \<ls> B \<longleftrightarrow> B \<cs> A \<in> \<nat>"
proof -
   from A2 have S1: "B \<in> \<nat>".
   { fix x
     have S2: "x = \<one> \<longrightarrow> 
       A \<ls> x \<longleftrightarrow> A \<ls> \<one>" by (rule MMI_breq2)
     have S3: "x = \<one> \<longrightarrow> x \<cs> A = \<one> \<cs> A" by (rule MMI_opreq1)
     from S3 have S4: "x = \<one> \<longrightarrow> 
       x \<cs> A \<in> \<nat> \<longleftrightarrow> \<one> \<cs> A \<in> \<nat>" by (rule MMI_eleq1d)
     from S2 S4 have "x = \<one> \<longrightarrow> 
       (A \<ls> x \<longrightarrow> x \<cs> A \<in> \<nat>) \<longleftrightarrow> 
       (A \<ls> \<one> \<longrightarrow> \<one> \<cs> A \<in> \<nat>)" by (rule MMI_imbi12d)
   } then have S5: "\<forall> x. x = \<one> \<longrightarrow> 
       (A \<ls> x \<longrightarrow> x \<cs> A \<in> \<nat>) \<longleftrightarrow> (A \<ls> \<one> \<longrightarrow> \<one> \<cs> A \<in> \<nat>)" 
     by simp
   { fix x y
     have S6: "x = y \<longrightarrow> 
       A \<ls> x \<longleftrightarrow> A \<ls> y" by (rule MMI_breq2)
     have S7: "x = y \<longrightarrow> x \<cs> A = y \<cs> A" by (rule MMI_opreq1)
     from S7 have S8: "x = y \<longrightarrow> 
       x \<cs> A \<in> \<nat> \<longleftrightarrow> y \<cs> A \<in> \<nat>" by (rule MMI_eleq1d)
     from S6 S8 have "x = y \<longrightarrow> 
       (A \<ls> x \<longrightarrow> x \<cs> A \<in> \<nat>) \<longleftrightarrow> 
       (A \<ls> y \<longrightarrow> y \<cs> A \<in> \<nat>)" by (rule MMI_imbi12d)
   } then have S9: "\<forall>x y. x = y \<longrightarrow> 
       (A \<ls> x \<longrightarrow> x \<cs> A \<in> \<nat>) \<longleftrightarrow> 
       (A \<ls> y \<longrightarrow> y \<cs> A \<in> \<nat>)" by simp
   { fix x y
     have S10: "x = y \<ca> \<one> \<longrightarrow> 
       A \<ls> x \<longleftrightarrow> A \<ls> y \<ca> \<one>" by (rule MMI_breq2)
     have S11: "x = y \<ca> \<one> \<longrightarrow> 
       x \<cs> A = y \<ca> \<one> \<cs> A" by (rule MMI_opreq1)
     from S11 have S12: "x = y \<ca> \<one> \<longrightarrow> 
       x \<cs> A \<in> \<nat> \<longleftrightarrow> 
       y \<ca> \<one> \<cs> A \<in> \<nat>" by (rule MMI_eleq1d)
     from S10 S12 have "x = y \<ca> \<one> \<longrightarrow> 
       (A \<ls> x \<longrightarrow> x \<cs> A \<in> \<nat>) \<longleftrightarrow> 
       (A \<ls> y \<ca> \<one> \<longrightarrow> 
       y \<ca> \<one> \<cs> A \<in> \<nat>)" by (rule MMI_imbi12d)
   } then have S13: "\<forall>x y.  x = y \<ca> \<one> \<longrightarrow> (A \<ls> x \<longrightarrow> x \<cs> A \<in> \<nat>) \<longleftrightarrow> 
       (A \<ls> y \<ca> \<one> \<longrightarrow> y \<ca> \<one> \<cs> A \<in> \<nat>)" by simp
   { fix x
     have S14: "x = B \<longrightarrow> 
       A \<ls> x \<longleftrightarrow> A \<ls> B" by (rule MMI_breq2)
     have S15: "x = B \<longrightarrow> x \<cs> A = B \<cs> A" by (rule MMI_opreq1)
     from S15 have S16: "x = B \<longrightarrow> 
       x \<cs> A \<in> \<nat> \<longleftrightarrow> B \<cs> A \<in> \<nat>" by (rule MMI_eleq1d)
     from S14 S16 have S17: "x = B \<longrightarrow> 
       (A \<ls> x \<longrightarrow> x \<cs> A \<in> \<nat>) \<longleftrightarrow> 
       (A \<ls> B \<longrightarrow> B \<cs> A \<in> \<nat>)" by (rule MMI_imbi12d)
   } then have S17: "\<forall>x. x = B \<longrightarrow> 
       (A \<ls> x \<longrightarrow> x \<cs> A \<in> \<nat>) \<longleftrightarrow> (A \<ls> B \<longrightarrow> B \<cs> A \<in> \<nat>)" 
     by simp
   from A1 have S18: "A \<in> \<nat>".
   have S19: "A \<in> \<nat> \<longrightarrow> \<one> \<lsq> A" by (rule MMI_nnge1t)
   from S18 S19 have S20: "\<one> \<lsq> A" by (rule MMI_ax_mp)
   have S21: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from A1 have S22: "A \<in> \<nat>".
   from S22 have S23: "A \<in> \<real>" by (rule MMI_nnre)
   from S21 S23 have S24: "\<one> \<lsq> A \<longleftrightarrow> \<not>(A \<ls> \<one>)" by (rule MMI_lenlt)
   from S20 S24 have S25: "\<not>(A \<ls> \<one>)" by (rule MMI_mpbi)
   from S25 have S26: "A \<ls> \<one> \<longrightarrow> \<one> \<cs> A \<in> \<nat>" by (rule MMI_pm2_21i)
   { fix y
     have S27: "y \<in> \<nat> \<longrightarrow> y \<in> \<real>" by (rule MMI_nnret)
     from S23 have S28: "A \<in> \<real>" .
     from S27 S28 have S29: "y \<in> \<nat> \<longrightarrow> 
       A \<in> \<real> \<and> y \<in> \<real>" by (rule MMI_jctil)
     have S30: "A \<in> \<real> \<and> y \<in> \<real> \<longrightarrow> 
       A \<lsq> y \<longleftrightarrow> A \<ls> y \<or> A = y" by (rule MMI_leloet)
     from S29 S30 have S31: "y \<in> \<nat> \<longrightarrow> 
       A \<lsq> y \<longleftrightarrow> A \<ls> y \<or> A = y" by (rule MMI_syl)
     from A1 have S32: "A \<in> \<nat>".
     have S33: "A \<in> \<nat> \<and> y \<in> \<nat> \<longrightarrow> 
       A \<lsq> y \<longleftrightarrow> A \<ls> y \<ca> \<one>" by (rule MMI_nnleltp1t)
     from S32 S33 have S34: "y \<in> \<nat> \<longrightarrow> 
       A \<lsq> y \<longleftrightarrow> A \<ls> y \<ca> \<one>" by (rule MMI_mpan)
     from S31 S34 have S35: "y \<in> \<nat> \<longrightarrow> 
       A \<ls> y \<or> A = y \<longleftrightarrow> A \<ls> y \<ca> \<one>" by (rule MMI_bitr3d)
     have S36: "y \<in> \<nat> \<longrightarrow> y \<in> \<complex>" by (rule MMI_nncnt)
     from A1 have S37: "A \<in> \<nat>".
     from S37 have S38: "A \<in> \<complex>" by (rule MMI_nncn)
     from S36 S38 have S39: "y \<in> \<nat> \<longrightarrow> 
       y \<in> \<complex> \<and> A \<in> \<complex>" by (rule MMI_jctir)
     have S40: "\<one> \<in> \<complex>" by (rule MMI_1cn)
     have S41: "y \<in> \<complex> \<and> \<one> \<in> \<complex> \<and> A \<in> \<complex> \<longrightarrow> 
       y \<ca> \<one> \<cs> A = y \<cs> A \<ca> \<one>" by (rule MMI_addsubt)
     from S40 S41 have S42: "y \<in> \<complex> \<and> A \<in> \<complex> \<longrightarrow> 
       y \<ca> \<one> \<cs> A = y \<cs> A \<ca> \<one>" by (rule MMI_mp3an2)
     from S39 S42 have S43: "y \<in> \<nat> \<longrightarrow> 
       y \<ca> \<one> \<cs> A = y \<cs> A \<ca> \<one>" by (rule MMI_syl)
     from S43 have S44: "y \<in> \<nat> \<longrightarrow> 
       y \<ca> \<one> \<cs> A \<in> \<nat> \<longleftrightarrow> 
       y \<cs> A \<ca> \<one> \<in> \<nat>" by (rule MMI_eleq1d)
     have S45: "y \<cs> A \<in> \<nat> \<longrightarrow> 
       y \<cs> A \<ca> \<one> \<in> \<nat>" by (rule MMI_peano2nn)
     from S44 S45 have S46: "y \<in> \<nat> \<longrightarrow> 
       y \<cs> A \<in> \<nat> \<longrightarrow> 
       y \<ca> \<one> \<cs> A \<in> \<nat>" by (rule MMI_syl5bir)
     from S46 have S47: "y \<in> \<nat> \<longrightarrow> 
       (A \<ls> y \<longrightarrow> y \<cs> A \<in> \<nat>) \<longrightarrow> 
       A \<ls> y \<longrightarrow> 
       y \<ca> \<one> \<cs> A \<in> \<nat>" by (rule MMI_imim2d)
     from S47 have S48: "y \<in> \<nat> \<longrightarrow> 
       A \<ls> y \<longrightarrow> 
       (A \<ls> y \<longrightarrow> y \<cs> A \<in> \<nat>) \<longrightarrow> 
       y \<ca> \<one> \<cs> A \<in> \<nat>" by (rule MMI_com23)
     have S49: "A = y \<longrightarrow> 
       A \<ca> \<one> = y \<ca> \<one>" by (rule MMI_opreq1)
     from S49 have S50: "A = y \<longrightarrow> 
       A \<ca> \<one> \<cs> A = y \<ca> \<one> \<cs> A" by (rule MMI_opreq1d)
     from S38 have S51: "A \<in> \<complex>" .
     have S52: "\<one> \<in> \<complex>" by (rule MMI_1cn)
     from S38 have S53: "A \<in> \<complex>" .
     from S51 S52 S53 have S54: "A \<ca> \<one> \<cs> A = A \<cs> A \<ca> \<one>" by (rule MMI_addsub)
     from S38 have S55: "A \<in> \<complex>" .
     from S55 have S56: "A \<cs> A = \<zero>" by (rule MMI_subid)
     from S56 have S57: "A \<cs> A \<ca> \<one> = \<zero> \<ca> \<one>" by (rule MMI_opreq1i)
     have S58: "\<one> \<in> \<complex>" by (rule MMI_1cn)
     from S58 have S59: "\<zero> \<ca> \<one> = \<one>" by (rule MMI_addid2)
     from S54 S57 S59 have S60: "A \<ca> \<one> \<cs> A = \<one>" by (rule MMI_3eqtr)
     have S61: "\<one> \<in> \<nat>" by (rule MMI_1nn)
     from S60 S61 have S62: "A \<ca> \<one> \<cs> A \<in> \<nat>" by (rule MMI_eqeltr)
     from S50 S62 have S63: "A = y \<longrightarrow> 
       y \<ca> \<one> \<cs> A \<in> \<nat>" by (rule MMI_syl6eqelr)
     from S63 have S64: "A = y \<longrightarrow> 
       (A \<ls> y \<longrightarrow> y \<cs> A \<in> \<nat>) \<longrightarrow> 
       y \<ca> \<one> \<cs> A \<in> \<nat>" by (rule MMI_a1d)
     from S64 have S65: "y \<in> \<nat> \<longrightarrow> 
       A = y \<longrightarrow> 
       (A \<ls> y \<longrightarrow> y \<cs> A \<in> \<nat>) \<longrightarrow> 
       y \<ca> \<one> \<cs> A \<in> \<nat>" by (rule MMI_a1i)
     from S48 S65 have S66: "y \<in> \<nat> \<longrightarrow> 
       A \<ls> y \<or> A = y \<longrightarrow> 
       (A \<ls> y \<longrightarrow> y \<cs> A \<in> \<nat>) \<longrightarrow> 
       y \<ca> \<one> \<cs> A \<in> \<nat>" by (rule MMI_jaod)
     from S35 S66 have S67: "y \<in> \<nat> \<longrightarrow> 
       A \<ls> y \<ca> \<one> \<longrightarrow> 
       (A \<ls> y \<longrightarrow> y \<cs> A \<in> \<nat>) \<longrightarrow> 
       y \<ca> \<one> \<cs> A \<in> \<nat>" by (rule MMI_sylbird)
     from S67 have S68: "y \<in> \<nat> \<longrightarrow> 
       (A \<ls> y \<longrightarrow> y \<cs> A \<in> \<nat>) \<longrightarrow> 
       A \<ls> y \<ca> \<one> \<longrightarrow> 
       y \<ca> \<one> \<cs> A \<in> \<nat>" by (rule MMI_com23)
   } then have S68: "\<forall>y. y \<in> \<nat> \<longrightarrow> 
       (A \<ls> y \<longrightarrow> y \<cs> A \<in> \<nat>) \<longrightarrow> 
       A \<ls> y \<ca> \<one> \<longrightarrow> 
       y \<ca> \<one> \<cs> A \<in> \<nat>" by simp
   from S5 S9 S13 S17 S26 S68 have S69: "B \<in> \<nat> \<longrightarrow> 
     A \<ls> B \<longrightarrow> B \<cs> A \<in> \<nat>" by (rule MMI_nnind)
   from S1 S69 have S70: "A \<ls> B \<longrightarrow> B \<cs> A \<in> \<nat>" by (rule MMI_ax_mp)
   have S71: "B \<cs> A \<in> \<nat> \<longrightarrow> \<zero> \<ls> B \<cs> A" by (rule MMI_nngt0t)
   from S23 have S72: "A \<in> \<real>" .
   from A2 have S73: "B \<in> \<nat>".
   from S73 have S74: "B \<in> \<real>" by (rule MMI_nnre)
   from S72 S74 have S75: "A \<ls> B \<longleftrightarrow> \<zero> \<ls> B \<cs> A" by (rule MMI_posdif)
   from S71 S75 have S76: "B \<cs> A \<in> \<nat> \<longrightarrow> A \<ls> B" by (rule MMI_sylibr)
   from S70 S76 show "A \<ls> B \<longleftrightarrow> B \<cs> A \<in> \<nat>" by (rule MMI_impbi)
qed

lemma (in MMIsar0) MMI_nnsubt: 
   shows "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> B \<cs> A \<in> \<nat>"
proof -
   have S1: "A =  if(A \<in> \<nat>, A, \<one>) \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<nat>, A, \<one>)) \<ls> B" by (rule MMI_breq1)
   have S2: "A =  if(A \<in> \<nat>, A, \<one>) \<longrightarrow> 
   B \<cs> A = B \<cs> ( if(A \<in> \<nat>, A, \<one>))" by (rule MMI_opreq2)
   from S2 have S3: "A =  if(A \<in> \<nat>, A, \<one>) \<longrightarrow> 
   B \<cs> A \<in> \<nat> \<longleftrightarrow> 
   B \<cs> ( if(A \<in> \<nat>, A, \<one>)) \<in> \<nat>" by (rule MMI_eleq1d)
   from S1 S3 have S4: "A =  if(A \<in> \<nat>, A, \<one>) \<longrightarrow> 
   (A \<ls> B \<longleftrightarrow> B \<cs> A \<in> \<nat>) \<longleftrightarrow> 
   ( if(A \<in> \<nat>, A, \<one>)) \<ls> B \<longleftrightarrow> 
   B \<cs> ( if(A \<in> \<nat>, A, \<one>)) \<in> \<nat>" by (rule MMI_bibi12d)
   have S5: "B =  if(B \<in> \<nat>, B, \<one>) \<longrightarrow> 
   ( if(A \<in> \<nat>, A, \<one>)) \<ls> B \<longleftrightarrow> 
   ( if(A \<in> \<nat>, A, \<one>)) \<ls> ( if(B \<in> \<nat>, B, \<one>))" by (rule MMI_breq2)
   have S6: "B =  if(B \<in> \<nat>, B, \<one>) \<longrightarrow> 
   B \<cs> ( if(A \<in> \<nat>, A, \<one>)) = ( if(B \<in> \<nat>, B, \<one>)) \<cs> ( if(A \<in> \<nat>, A, \<one>))" by (rule MMI_opreq1)
   from S6 have S7: "B =  if(B \<in> \<nat>, B, \<one>) \<longrightarrow> 
   B \<cs> ( if(A \<in> \<nat>, A, \<one>)) \<in> \<nat> \<longleftrightarrow> 
   ( if(B \<in> \<nat>, B, \<one>)) \<cs> ( if(A \<in> \<nat>, A, \<one>)) \<in> \<nat>" by (rule MMI_eleq1d)
   from S5 S7 have S8: "B =  if(B \<in> \<nat>, B, \<one>) \<longrightarrow> 
   (( if(A \<in> \<nat>, A, \<one>)) \<ls> B \<longleftrightarrow> 
   B \<cs> ( if(A \<in> \<nat>, A, \<one>)) \<in> \<nat>) \<longleftrightarrow> 
   ( if(A \<in> \<nat>, A, \<one>)) \<ls> ( if(B \<in> \<nat>, B, \<one>)) \<longleftrightarrow> 
   ( if(B \<in> \<nat>, B, \<one>)) \<cs> ( if(A \<in> \<nat>, A, \<one>)) \<in> \<nat>" by (rule MMI_bibi12d)
   have S9: "\<one> \<in> \<nat>" by (rule MMI_1nn)
   from S9 have S10: " if(A \<in> \<nat>, A, \<one>) \<in> \<nat>" by (rule MMI_elimel)
   have S11: "\<one> \<in> \<nat>" by (rule MMI_1nn)
   from S11 have S12: " if(B \<in> \<nat>, B, \<one>) \<in> \<nat>" by (rule MMI_elimel)
   from S10 S12 have S13: "( if(A \<in> \<nat>, A, \<one>)) \<ls> ( if(B \<in> \<nat>, B, \<one>)) \<longleftrightarrow> 
   ( if(B \<in> \<nat>, B, \<one>)) \<cs> ( if(A \<in> \<nat>, A, \<one>)) \<in> \<nat>" by (rule MMI_nnsub)
   from S4 S8 S13 show "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> B \<cs> A \<in> \<nat>" by (rule MMI_dedth2h)
qed

lemma (in MMIsar0) MMI_nnaddm1clt: 
   shows "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   A \<ca> B \<cs> \<one> \<in> \<nat>"
proof -
   have S1: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S2: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S3: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S2 S3 have S4: "\<one> \<ca> \<one> \<in> \<real>" by (rule MMI_readdcl)
   have S5: "\<one> \<in> \<real> \<and> \<one> \<ca> \<one> \<in> \<real> \<and> A \<ca> B \<in> \<real> \<longrightarrow> 
   \<one> \<ls> \<one> \<ca> \<one> \<and> \<one> \<ca> \<one> \<lsq> A \<ca> B \<longrightarrow> \<one> \<ls> A \<ca> B" by (rule MMI_ltletrt)
   from S1 S4 S5 have S6: "A \<ca> B \<in> \<real> \<longrightarrow> 
   \<one> \<ls> \<one> \<ca> \<one> \<and> \<one> \<ca> \<one> \<lsq> A \<ca> B \<longrightarrow> \<one> \<ls> A \<ca> B" by (rule MMI_mp3an12)
   have S7: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<ca> B \<in> \<real>" by (rule MMI_axaddrcl)
   have S8: "A \<in> \<nat> \<longrightarrow> A \<in> \<real>" by (rule MMI_nnret)
   have S9: "B \<in> \<nat> \<longrightarrow> B \<in> \<real>" by (rule MMI_nnret)
   from S7 S8 S9 have S10: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> A \<ca> B \<in> \<real>" by (rule MMI_syl2an)
   from S4 have S11: "\<one> \<ca> \<one> \<in> \<real>" .
   from S11 have S12: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   \<one> \<ca> \<one> \<in> \<real>" by (rule MMI_a1i)
   from S9 have S13: "B \<in> \<nat> \<longrightarrow> B \<in> \<real>" .
   have S14: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S15: "\<one> \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> \<one> \<ca> B \<in> \<real>" by (rule MMI_axaddrcl)
   from S14 S15 have S16: "B \<in> \<real> \<longrightarrow> \<one> \<ca> B \<in> \<real>" by (rule MMI_mpan)
   from S13 S16 have S17: "B \<in> \<nat> \<longrightarrow> \<one> \<ca> B \<in> \<real>" by (rule MMI_syl)
   from S17 have S18: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> \<one> \<ca> B \<in> \<real>" by (rule MMI_adantl)
   from S10 have S19: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> A \<ca> B \<in> \<real>" .
   have S20: "B \<in> \<nat> \<longrightarrow> \<one> \<lsq> B" by (rule MMI_nnge1t)
   from S9 have S21: "B \<in> \<nat> \<longrightarrow> B \<in> \<real>" .
   have S22: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S23: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S24: "\<one> \<in> \<real> \<and> B \<in> \<real> \<and> \<one> \<in> \<real> \<longrightarrow> 
   \<one> \<lsq> B \<longleftrightarrow> 
   \<one> \<ca> \<one> \<lsq> \<one> \<ca> B" by (rule MMI_leadd2t)
   from S22 S23 S24 have S25: "B \<in> \<real> \<longrightarrow> 
   \<one> \<lsq> B \<longleftrightarrow> 
   \<one> \<ca> \<one> \<lsq> \<one> \<ca> B" by (rule MMI_mp3an13)
   from S21 S25 have S26: "B \<in> \<nat> \<longrightarrow> 
   \<one> \<lsq> B \<longleftrightarrow> 
   \<one> \<ca> \<one> \<lsq> \<one> \<ca> B" by (rule MMI_syl)
   from S20 S26 have S27: "B \<in> \<nat> \<longrightarrow> 
   \<one> \<ca> \<one> \<lsq> \<one> \<ca> B" by (rule MMI_mpbid)
   from S27 have S28: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   \<one> \<ca> \<one> \<lsq> \<one> \<ca> B" by (rule MMI_adantl)
   have S29: "A \<in> \<nat> \<longrightarrow> \<one> \<lsq> A" by (rule MMI_nnge1t)
   from S29 have S30: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> \<one> \<lsq> A" by (rule MMI_adantr)
   have S31: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S32: "\<one> \<in> \<real> \<and> A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<one> \<lsq> A \<longleftrightarrow> 
   \<one> \<ca> B \<lsq> A \<ca> B" by (rule MMI_leadd1t)
   from S31 S32 have S33: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<one> \<lsq> A \<longleftrightarrow> 
   \<one> \<ca> B \<lsq> A \<ca> B" by (rule MMI_mp3an1)
   from S8 have S34: "A \<in> \<nat> \<longrightarrow> A \<in> \<real>" .
   from S9 have S35: "B \<in> \<nat> \<longrightarrow> B \<in> \<real>" .
   from S33 S34 S35 have S36: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   \<one> \<lsq> A \<longleftrightarrow> 
   \<one> \<ca> B \<lsq> A \<ca> B" by (rule MMI_syl2an)
   from S30 S36 have S37: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   \<one> \<ca> B \<lsq> A \<ca> B" by (rule MMI_mpbid)
   from S12 S18 S19 S28 S37 have S38: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   \<one> \<ca> \<one> \<lsq> A \<ca> B" by (rule MMI_letrd)
   have S39: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S39 have S40: "\<one> \<ls> \<one> \<ca> \<one>" by (rule MMI_ltp1)
   from S38 S40 have S41: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   \<one> \<ls> \<one> \<ca> \<one> \<and> \<one> \<ca> \<one> \<lsq> A \<ca> B" by (rule MMI_jctil)
   from S6 S10 S41 have S42: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> \<one> \<ls> A \<ca> B" by (rule MMI_sylc)
   have S43: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> A \<ca> B \<in> \<nat>" by (rule MMI_nnaddclt)
   have S44: "\<one> \<in> \<nat>" by (rule MMI_1nn)
   have S45: "\<one> \<in> \<nat> \<and> A \<ca> B \<in> \<nat> \<longrightarrow> 
   \<one> \<ls> A \<ca> B \<longleftrightarrow> 
   A \<ca> B \<cs> \<one> \<in> \<nat>" by (rule MMI_nnsubt)
   from S44 S45 have S46: "A \<ca> B \<in> \<nat> \<longrightarrow> 
   \<one> \<ls> A \<ca> B \<longleftrightarrow> 
   A \<ca> B \<cs> \<one> \<in> \<nat>" by (rule MMI_mpan)
   from S43 S46 have S47: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   \<one> \<ls> A \<ca> B \<longleftrightarrow> 
   A \<ca> B \<cs> \<one> \<in> \<nat>" by (rule MMI_syl)
   from S42 S47 show "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   A \<ca> B \<cs> \<one> \<in> \<nat>" by (rule MMI_mpbid)
qed

(****** 521,522 *************************)

lemma (in MMIsar0) MMI_nndivt: 
   shows "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   ( \<exists>x\<in>\<nat>. A\<cdot>x = B) \<longleftrightarrow> B\<cdiv>A \<in> \<nat>"
proof -
   have S1: "A \<in> \<nat> \<longrightarrow> A \<noteq> \<zero>" by (rule MMI_nnne0t)
   from S1 have S2: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> A \<noteq> \<zero>" by (rule MMI_adantr)
   { fix x
     have S3: "A \<in> \<complex> \<and> x \<in> \<complex> \<and> A \<noteq> \<zero> \<longrightarrow> A\<cdot>x\<cdiv>A = x" by (rule MMI_divcan3t)
     from S3 have S4: "A \<in> \<complex> \<and> A \<noteq> \<zero> \<and> x \<in> \<complex> \<longrightarrow> A\<cdot>x\<cdiv>A = x" by (rule MMI_3com23)
     from S4 have S5: "(A \<in> \<complex> \<and> A \<noteq> \<zero>) \<and> x \<in> \<complex> \<longrightarrow> A\<cdot>x\<cdiv>A = x" by (rule MMI_3expa)
     have S6: "x \<in> \<nat> \<longrightarrow> x \<in> \<complex>" by (rule MMI_nncnt)
     from S5 S6 have S7: "(A \<in> \<complex> \<and> A \<noteq> \<zero>) \<and> x \<in> \<nat> \<longrightarrow> A\<cdot>x\<cdiv>A = x" by (rule MMI_sylan2)
     from S7 have S8: "(A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero>) \<and> x \<in> \<nat> \<longrightarrow> A\<cdot>x\<cdiv>A = x" 
       by (rule MMI_3adantl2)
     from S8 have S9: "(A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero>) \<and> x \<in> \<nat> \<longrightarrow> x = A\<cdot>x\<cdiv>A" 
       by (rule MMI_eqcomd)
     have S10: "A\<cdot>x = B \<longrightarrow> A\<cdot>x\<cdiv>A = B\<cdiv>A" by (rule MMI_opreq1)
     from S9 S10 have S11: 
       "((A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero>) \<and> x \<in> \<nat>) \<and> A\<cdot>x = B \<longrightarrow> x = B\<cdiv>A" 
       by (rule MMI_sylan9eq)
     have S12: "((A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero>) \<and> x \<in> \<nat>) \<and> A\<cdot>x = B \<longrightarrow> 
       (A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero>) \<and> x \<in> \<nat>" by (rule MMI_pm3_26)
     from S12 have S13: 
       "((A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero>) \<and> x \<in> \<nat>) \<and> A\<cdot>x = B \<longrightarrow> x \<in> \<nat>" by (rule MMI_pm3_27d)
     from S11 S13 have S14: 
       "((A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero>) \<and> x \<in> \<nat>) \<and> A\<cdot>x = B \<longrightarrow> B\<cdiv>A \<in> \<nat>" 
       by (rule MMI_eqeltrrd)
     from S14 have "A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero> \<longrightarrow> x \<in> \<nat> \<longrightarrow> 
       A\<cdot>x = B \<longrightarrow> B\<cdiv>A \<in> \<nat>" by (rule MMI_exp31)
     } then have S15: "\<forall>x. A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero> \<longrightarrow> x \<in> \<nat> \<longrightarrow> 
	 A\<cdot>x = B \<longrightarrow> B\<cdiv>A \<in> \<nat>" by simp
   from S15 have S16: "A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero> \<longrightarrow> 
   ( \<exists>x\<in>\<nat>. A\<cdot>x = B) \<longrightarrow> B\<cdiv>A \<in> \<nat>" by (rule MMI_r19_23adv)
   have S17: "A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero> \<longrightarrow> A\<cdot>(B\<cdiv>A) = B" by (rule MMI_divcan2t)
   have S18: "x = B\<cdiv>A \<longrightarrow> 
     A\<cdot>x = A\<cdot>(B\<cdiv>A)" by (rule MMI_opreq2)
   from S18 have S19: "x = B\<cdiv>A \<longrightarrow> 
     A\<cdot>x = B \<longleftrightarrow> A\<cdot>(B\<cdiv>A) = B" by (rule MMI_eqeq1d)
   from S19 have S20: "B\<cdiv>A \<in> \<nat> \<and> A\<cdot>(B\<cdiv>A) = B \<longrightarrow> 
     ( \<exists>x\<in>\<nat>. A\<cdot>x = B)" by auto (*(rule MMI_rcla4ev)*)
   from S20 have S21: "A\<cdot>(B\<cdiv>A) = B \<longrightarrow> 
     B\<cdiv>A \<in> \<nat> \<longrightarrow> 
     ( \<exists>x\<in>\<nat>. A\<cdot>x = B)" by (rule MMI_expcom)
   from S17 S21 have S22: "A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero> \<longrightarrow> 
     B\<cdiv>A \<in> \<nat> \<longrightarrow> 
     ( \<exists>x\<in>\<nat>. A\<cdot>x = B)" by (rule MMI_syl)
   from S16 S22 have S23: "A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero> \<longrightarrow> 
     ( \<exists>x\<in>\<nat>. A\<cdot>x = B) \<longleftrightarrow> B\<cdiv>A \<in> \<nat>" by (rule MMI_impbid)
   from S23 have S24: "A \<in> \<complex> \<longrightarrow> 
     B \<in> \<complex> \<longrightarrow> 
     A \<noteq> \<zero> \<longrightarrow> 
     ( \<exists>x\<in>\<nat>. A\<cdot>x = B) \<longleftrightarrow> B\<cdiv>A \<in> \<nat>" by (rule MMI_3exp)
   from S24 have S25: "A \<in> \<complex> \<and> B \<in> \<complex> \<longrightarrow> 
     A \<noteq> \<zero> \<longrightarrow> 
     ( \<exists>x\<in>\<nat>. A\<cdot>x = B) \<longleftrightarrow> B\<cdiv>A \<in> \<nat>" by (rule MMI_imp)
   have S26: "A \<in> \<nat> \<longrightarrow> A \<in> \<complex>" by (rule MMI_nncnt)
   have S27: "B \<in> \<nat> \<longrightarrow> B \<in> \<complex>" by (rule MMI_nncnt)
   from S25 S26 S27 have S28: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
     A \<noteq> \<zero> \<longrightarrow> 
     ( \<exists>x\<in>\<nat>. A\<cdot>x = B) \<longleftrightarrow> B\<cdiv>A \<in> \<nat>" by (rule MMI_syl2an)
   from S2 S28 show "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
     ( \<exists>x\<in>\<nat>. A\<cdot>x = B) \<longleftrightarrow> B\<cdiv>A \<in> \<nat>" by (rule MMI_mpd)
 qed

lemma (in MMIsar0) MMI_nndivtrt: 
   shows "(A \<in> \<nat> \<and> B \<in> \<nat> \<and> C \<in> \<complex>) \<and> B\<cdiv>A \<in> \<nat> \<and> C\<cdiv>B \<in> \<nat> \<longrightarrow> C\<cdiv>A \<in> \<nat>"
proof -
   have S1: "((B \<in> \<complex> \<and> A \<in> \<complex>) \<and> C \<in> \<complex> \<and> B \<in> \<complex>) \<and> A \<noteq> \<zero> \<and> B \<noteq> \<zero> \<longrightarrow> 
   (B\<cdiv>A)\<cdot>(C\<cdiv>B) = (B\<cdiv>B)\<cdot>(C\<cdiv>A)" by (rule MMI_divmul24t)
   have S2: "B \<in> \<nat> \<longrightarrow> B \<in> \<complex>" by (rule MMI_nncnt)
   have S3: "A \<in> \<nat> \<longrightarrow> A \<in> \<complex>" by (rule MMI_nncnt)
   from S2 S3 have S4: "B \<in> \<nat> \<and> A \<in> \<nat> \<longrightarrow> 
   B \<in> \<complex> \<and> A \<in> \<complex>" by (rule MMI_anim12i)
   from S4 have S5: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   B \<in> \<complex> \<and> A \<in> \<complex>" by (rule MMI_ancoms)
   from S5 have S6: "A \<in> \<nat> \<and> B \<in> \<nat> \<and> C \<in> \<complex> \<longrightarrow> 
   B \<in> \<complex> \<and> A \<in> \<complex>" by (rule MMI_3adant3)
   from S2 have S7: "B \<in> \<nat> \<longrightarrow> B \<in> \<complex>" .
   from S7 have S8: "C \<in> \<complex> \<and> B \<in> \<nat> \<longrightarrow> 
   C \<in> \<complex> \<and> B \<in> \<complex>" by (rule MMI_anim2i)
   from S8 have S9: "B \<in> \<nat> \<and> C \<in> \<complex> \<longrightarrow> 
   C \<in> \<complex> \<and> B \<in> \<complex>" by (rule MMI_ancoms)
   from S9 have S10: "A \<in> \<nat> \<and> B \<in> \<nat> \<and> C \<in> \<complex> \<longrightarrow> 
   C \<in> \<complex> \<and> B \<in> \<complex>" by (rule MMI_3adant1)
   from S6 S10 have S11: "A \<in> \<nat> \<and> B \<in> \<nat> \<and> C \<in> \<complex> \<longrightarrow> 
   (B \<in> \<complex> \<and> A \<in> \<complex>) \<and> C \<in> \<complex> \<and> B \<in> \<complex>" by (rule MMI_jca)
   have S12: "A \<in> \<nat> \<longrightarrow> A \<noteq> \<zero>" by (rule MMI_nnne0t)
   have S13: "B \<in> \<nat> \<longrightarrow> B \<noteq> \<zero>" by (rule MMI_nnne0t)
   from S12 S13 have S14: "A \<in> \<nat> \<and> B \<in> \<nat> \<longrightarrow> 
   A \<noteq> \<zero> \<and> B \<noteq> \<zero>" by (rule MMI_anim12i)
   from S14 have S15: "A \<in> \<nat> \<and> B \<in> \<nat> \<and> C \<in> \<complex> \<longrightarrow> 
   A \<noteq> \<zero> \<and> B \<noteq> \<zero>" by (rule MMI_3adant3)
   from S1 S11 S15 have S16: "A \<in> \<nat> \<and> B \<in> \<nat> \<and> C \<in> \<complex> \<longrightarrow> 
   (B\<cdiv>A)\<cdot>(C\<cdiv>B) = (B\<cdiv>B)\<cdot>(C\<cdiv>A)" by (rule MMI_sylanc)
   have S17: "B \<in> \<complex> \<and> B \<noteq> \<zero> \<longrightarrow> B\<cdiv>B = \<one>" by (rule MMI_dividt)
   from S2 have S18: "B \<in> \<nat> \<longrightarrow> B \<in> \<complex>" .
   from S13 have S19: "B \<in> \<nat> \<longrightarrow> B \<noteq> \<zero>" .
   from S17 S18 S19 have S20: "B \<in> \<nat> \<longrightarrow> B\<cdiv>B = \<one>" by (rule MMI_sylanc)
   from S20 have S21: "B \<in> \<nat> \<longrightarrow> 
   (B\<cdiv>B)\<cdot>(C\<cdiv>A) = \<one>\<cdot>(C\<cdiv>A)" by (rule MMI_opreq1d)
   from S21 have S22: "A \<in> \<nat> \<and> B \<in> \<nat> \<and> C \<in> \<complex> \<longrightarrow> 
   (B\<cdiv>B)\<cdot>(C\<cdiv>A) = \<one>\<cdot>(C\<cdiv>A)" by (rule MMI_3ad2ant2)
   have S23: "C \<in> \<complex> \<and> A \<in> \<complex> \<and> A \<noteq> \<zero> \<longrightarrow> C\<cdiv>A \<in> \<complex>" by (rule MMI_divclt)
   from S23 have S24: "C \<in> \<complex> \<and> A \<in> \<complex> \<and> A \<noteq> \<zero> \<longrightarrow> C\<cdiv>A \<in> \<complex>" 
     by (rule MMI_3expb)
   from S3 have S25: "A \<in> \<nat> \<longrightarrow> A \<in> \<complex>" .
   from S12 have S26: "A \<in> \<nat> \<longrightarrow> A \<noteq> \<zero>" .
   from S25 S26 have S27: "A \<in> \<nat> \<longrightarrow> 
   A \<in> \<complex> \<and> A \<noteq> \<zero>" by (rule MMI_jca)
   from S24 S27 have S28: "C \<in> \<complex> \<and> A \<in> \<nat> \<longrightarrow> C\<cdiv>A \<in> \<complex>" 
     by (rule MMI_sylan2)
   from S28 have S29: "A \<in> \<nat> \<and> C \<in> \<complex> \<longrightarrow> C\<cdiv>A \<in> \<complex>" by (rule MMI_ancoms)
   have S30: "C\<cdiv>A \<in> \<complex> \<longrightarrow> 
   \<one>\<cdot>(C\<cdiv>A) = C\<cdiv>A" by (rule MMI_mulid2t)
   from S29 S30 have S31: "A \<in> \<nat> \<and> C \<in> \<complex> \<longrightarrow> 
   \<one>\<cdot>(C\<cdiv>A) = C\<cdiv>A" by (rule MMI_syl)
   from S31 have S32: "A \<in> \<nat> \<and> B \<in> \<nat> \<and> C \<in> \<complex> \<longrightarrow> 
   \<one>\<cdot>(C\<cdiv>A) = C\<cdiv>A" by (rule MMI_3adant2)
   from S16 S22 S32 have S33: "A \<in> \<nat> \<and> B \<in> \<nat> \<and> C \<in> \<complex> \<longrightarrow> 
   (B\<cdiv>A)\<cdot>(C\<cdiv>B) = C\<cdiv>A" by (rule MMI_3eqtrd)
   from S33 have S34: "A \<in> \<nat> \<and> B \<in> \<nat> \<and> C \<in> \<complex> \<longrightarrow> 
   (B\<cdiv>A)\<cdot>(C\<cdiv>B) \<in> \<nat> \<longleftrightarrow> C\<cdiv>A \<in> \<nat>" by (rule MMI_eleq1d)
   have S35: "B\<cdiv>A \<in> \<nat> \<and> C\<cdiv>B \<in> \<nat> \<longrightarrow> 
   (B\<cdiv>A)\<cdot>(C\<cdiv>B) \<in> \<nat>" by (rule MMI_nnmulclt)
   from S34 S35 have S36: "A \<in> \<nat> \<and> B \<in> \<nat> \<and> C \<in> \<complex> \<longrightarrow> 
   B\<cdiv>A \<in> \<nat> \<and> C\<cdiv>B \<in> \<nat> \<longrightarrow> C\<cdiv>A \<in> \<nat>" by (rule MMI_syl5bi)
   from S36 show 
     "(A \<in> \<nat> \<and> B \<in> \<nat> \<and> C \<in> \<complex>) \<and> B\<cdiv>A \<in> \<nat> \<and> C\<cdiv>B \<in> \<nat> \<longrightarrow> 
     C\<cdiv>A \<in> \<nat>" by (rule MMI_imp)
qed

text\<open>A bunch of definitions converted to lemmas.\<close>

lemma (in MMIsar0) MMI_df_2: shows "\<two> = \<one>\<ca>\<one>"
  using two_def by simp

lemma (in MMIsar0) MMI_df_3: shows "\<three> = \<two>\<ca>\<one>"
  using three_def by simp

lemma (in MMIsar0) MMI_df_4: shows "\<four> = \<three>\<ca>\<one>"
  using four_def by simp

lemma (in MMIsar0) MMI_df_5: shows "\<five> = \<four>\<ca>\<one>"
  using five_def by simp

lemma (in MMIsar0) MMI_df_6: shows "\<six> = \<five>\<ca>\<one>"
  using six_def by simp

lemma (in MMIsar0) MMI_df_7: shows "\<seven> = \<six>\<ca>\<one>"
  using seven_def by simp

lemma (in MMIsar0) MMI_df_8: shows "\<eight> = \<seven>\<ca>\<one>"
  using eight_def by simp

lemma (in MMIsar0) MMI_df_9: shows "\<nine> = \<eight>\<ca>\<one>"
  using nine_def by simp

(************ 523-530************************)

lemma (in MMIsar0) MMI_2re: 
   shows "\<two> \<in> \<real>"
proof -
   have S1: "\<two> = \<one> \<ca> \<one>" by (rule MMI_df_2)
   have S2: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S3: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S2 S3 have S4: "\<one> \<ca> \<one> \<in> \<real>" by (rule MMI_readdcl)
   from S1 S4 show "\<two> \<in> \<real>" by (rule MMI_eqeltr)
qed

lemma (in MMIsar0) MMI_2cn: 
   shows "\<two> \<in> \<complex>"
proof -
   have S1: "\<two> \<in> \<real>" by (rule MMI_2re)
   from S1 show "\<two> \<in> \<complex>" by (rule MMI_recn)
qed

lemma (in MMIsar0) MMI_3re: 
   shows "\<three> \<in> \<real>"
proof -
   have S1: "\<three> = \<two> \<ca> \<one>" by (rule MMI_df_3)
   have S2: "\<two> \<in> \<real>" by (rule MMI_2re)
   have S3: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S2 S3 have S4: "\<two> \<ca> \<one> \<in> \<real>" by (rule MMI_readdcl)
   from S1 S4 show "\<three> \<in> \<real>" by (rule MMI_eqeltr)
qed

lemma (in MMIsar0) MMI_4re: 
   shows "\<four> \<in> \<real>"
proof -
   have S1: "\<four> = \<three> \<ca> \<one>" by (rule MMI_df_4)
   have S2: "\<three> \<in> \<real>" by (rule MMI_3re)
   have S3: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S2 S3 have S4: "\<three> \<ca> \<one> \<in> \<real>" by (rule MMI_readdcl)
   from S1 S4 show "\<four> \<in> \<real>" by (rule MMI_eqeltr)
qed

lemma (in MMIsar0) MMI_5re: 
   shows "\<five> \<in> \<real>"
proof -
   have S1: "\<five> = \<four> \<ca> \<one>" by (rule MMI_df_5)
   have S2: "\<four> \<in> \<real>" by (rule MMI_4re)
   have S3: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S2 S3 have S4: "\<four> \<ca> \<one> \<in> \<real>" by (rule MMI_readdcl)
   from S1 S4 show "\<five> \<in> \<real>" by (rule MMI_eqeltr)
qed

lemma (in MMIsar0) MMI_6re: 
   shows "\<six> \<in> \<real>"
proof -
   have S1: "\<six> = \<five> \<ca> \<one>" by (rule MMI_df_6)
   have S2: "\<five> \<in> \<real>" by (rule MMI_5re)
   have S3: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S2 S3 have S4: "\<five> \<ca> \<one> \<in> \<real>" by (rule MMI_readdcl)
   from S1 S4 show "\<six> \<in> \<real>" by (rule MMI_eqeltr)
qed

lemma (in MMIsar0) MMI_7re: 
   shows "\<seven> \<in> \<real>"
proof -
   have S1: "\<seven> = \<six> \<ca> \<one>" by (rule MMI_df_7)
   have S2: "\<six> \<in> \<real>" by (rule MMI_6re)
   have S3: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S2 S3 have S4: "\<six> \<ca> \<one> \<in> \<real>" by (rule MMI_readdcl)
   from S1 S4 show "\<seven> \<in> \<real>" by (rule MMI_eqeltr)
qed

lemma (in MMIsar0) MMI_8re: 
   shows "\<eight> \<in> \<real>"
proof -
   have S1: "\<eight> = \<seven> \<ca> \<one>" by (rule MMI_df_8)
   have S2: "\<seven> \<in> \<real>" by (rule MMI_7re)
   have S3: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S2 S3 have S4: "\<seven> \<ca> \<one> \<in> \<real>" by (rule MMI_readdcl)
   from S1 S4 show "\<eight> \<in> \<real>" by (rule MMI_eqeltr)
qed

(************ 531-540*****************************)

lemma (in MMIsar0) MMI_9re: 
   shows "\<nine> \<in> \<real>"
proof -
   have S1: "\<nine> = \<eight> \<ca> \<one>" by (rule MMI_df_9)
   have S2: "\<eight> \<in> \<real>" by (rule MMI_8re)
   have S3: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S2 S3 have S4: "\<eight> \<ca> \<one> \<in> \<real>" by (rule MMI_readdcl)
   from S1 S4 show "\<nine> \<in> \<real>" by (rule MMI_eqeltr)
qed

lemma (in MMIsar0) MMI_2pos: 
   shows "\<zero> \<ls> \<two>"
proof -
   have S1: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S2: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S3: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   have S4: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   from S1 S2 S3 S4 have S5: "\<zero> \<ls> \<one> \<ca> \<one>" by (rule MMI_addgt0i)
   have S6: "\<two> = \<one> \<ca> \<one>" by (rule MMI_df_2)
   from S5 S6 show "\<zero> \<ls> \<two>" by (rule MMI_breqtrr)
qed

lemma (in MMIsar0) MMI_3pos: 
   shows "\<zero> \<ls> \<three>"
proof -
   have S1: "\<two> \<in> \<real>" by (rule MMI_2re)
   have S2: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S3: "\<zero> \<ls> \<two>" by (rule MMI_2pos)
   have S4: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   from S1 S2 S3 S4 have S5: "\<zero> \<ls> \<two> \<ca> \<one>" by (rule MMI_addgt0i)
   have S6: "\<three> = \<two> \<ca> \<one>" by (rule MMI_df_3)
   from S5 S6 show "\<zero> \<ls> \<three>" by (rule MMI_breqtrr)
qed

lemma (in MMIsar0) MMI_4pos: 
   shows "\<zero> \<ls> \<four>"
proof -
   have S1: "\<three> \<in> \<real>" by (rule MMI_3re)
   have S2: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S3: "\<zero> \<ls> \<three>" by (rule MMI_3pos)
   have S4: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   from S1 S2 S3 S4 have S5: "\<zero> \<ls> \<three> \<ca> \<one>" by (rule MMI_addgt0i)
   have S6: "\<four> = \<three> \<ca> \<one>" by (rule MMI_df_4)
   from S5 S6 show "\<zero> \<ls> \<four>" by (rule MMI_breqtrr)
qed

lemma (in MMIsar0) MMI_5pos: 
   shows "\<zero> \<ls> \<five>"
proof -
   have S1: "\<four> \<in> \<real>" by (rule MMI_4re)
   have S2: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S3: "\<zero> \<ls> \<four>" by (rule MMI_4pos)
   have S4: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   from S1 S2 S3 S4 have S5: "\<zero> \<ls> \<four> \<ca> \<one>" by (rule MMI_addgt0i)
   have S6: "\<five> = \<four> \<ca> \<one>" by (rule MMI_df_5)
   from S5 S6 show "\<zero> \<ls> \<five>" by (rule MMI_breqtrr)
qed

lemma (in MMIsar0) MMI_6pos: 
   shows "\<zero> \<ls> \<six>"
proof -
   have S1: "\<five> \<in> \<real>" by (rule MMI_5re)
   have S2: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S3: "\<zero> \<ls> \<five>" by (rule MMI_5pos)
   have S4: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   from S1 S2 S3 S4 have S5: "\<zero> \<ls> \<five> \<ca> \<one>" by (rule MMI_addgt0i)
   have S6: "\<six> = \<five> \<ca> \<one>" by (rule MMI_df_6)
   from S5 S6 show "\<zero> \<ls> \<six>" by (rule MMI_breqtrr)
qed

lemma (in MMIsar0) MMI_7pos: 
   shows "\<zero> \<ls> \<seven>"
proof -
   have S1: "\<six> \<in> \<real>" by (rule MMI_6re)
   have S2: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S3: "\<zero> \<ls> \<six>" by (rule MMI_6pos)
   have S4: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   from S1 S2 S3 S4 have S5: "\<zero> \<ls> \<six> \<ca> \<one>" by (rule MMI_addgt0i)
   have S6: "\<seven> = \<six> \<ca> \<one>" by (rule MMI_df_7)
   from S5 S6 show "\<zero> \<ls> \<seven>" by (rule MMI_breqtrr)
qed

lemma (in MMIsar0) MMI_8pos: 
   shows "\<zero> \<ls> \<eight>"
proof -
   have S1: "\<seven> \<in> \<real>" by (rule MMI_7re)
   have S2: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S3: "\<zero> \<ls> \<seven>" by (rule MMI_7pos)
   have S4: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   from S1 S2 S3 S4 have S5: "\<zero> \<ls> \<seven> \<ca> \<one>" by (rule MMI_addgt0i)
   have S6: "\<eight> = \<seven> \<ca> \<one>" by (rule MMI_df_8)
   from S5 S6 show "\<zero> \<ls> \<eight>" by (rule MMI_breqtrr)
qed

lemma (in MMIsar0) MMI_9pos: 
   shows "\<zero> \<ls> \<nine>"
proof -
   have S1: "\<eight> \<in> \<real>" by (rule MMI_8re)
   have S2: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S3: "\<zero> \<ls> \<eight>" by (rule MMI_8pos)
   have S4: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   from S1 S2 S3 S4 have S5: "\<zero> \<ls> \<eight> \<ca> \<one>" by (rule MMI_addgt0i)
   have S6: "\<nine> = \<eight> \<ca> \<one>" by (rule MMI_df_9)
   from S5 S6 show "\<zero> \<ls> \<nine>" by (rule MMI_breqtrr)
qed

lemma (in MMIsar0) MMI_2nn: 
   shows "\<two> \<in> \<nat>"
proof -
   have S1: "\<two> = \<one> \<ca> \<one>" by (rule MMI_df_2)
   have S2: "\<one> \<in> \<nat>" by (rule MMI_1nn)
   have S3: "\<one> \<in> \<nat>" by (rule MMI_1nn)
   have S4: "\<one> \<in> \<nat> \<and> \<one> \<in> \<nat> \<longrightarrow> 
   \<one> \<ca> \<one> \<in> \<nat>" by (rule MMI_nnaddclt)
   from S2 S3 S4 have S5: "\<one> \<ca> \<one> \<in> \<nat>" by (rule MMI_mp2an)
   from S1 S5 show "\<two> \<in> \<nat>" by (rule MMI_eqeltr)
qed

(********** 541-560*************************)

lemma (in MMIsar0) MMI_3nn: 
   shows "\<three> \<in> \<nat>"
proof -
   have S1: "\<three> = \<two> \<ca> \<one>" by (rule MMI_df_3)
   have S2: "\<two> \<in> \<nat>" by (rule MMI_2nn)
   have S3: "\<one> \<in> \<nat>" by (rule MMI_1nn)
   have S4: "\<two> \<in> \<nat> \<and> \<one> \<in> \<nat> \<longrightarrow> 
   \<two> \<ca> \<one> \<in> \<nat>" by (rule MMI_nnaddclt)
   from S2 S3 S4 have S5: "\<two> \<ca> \<one> \<in> \<nat>" by (rule MMI_mp2an)
   from S1 S5 show "\<three> \<in> \<nat>" by (rule MMI_eqeltr)
qed

lemma (in MMIsar0) MMI_2p2e4: 
   shows "\<two> \<ca> \<two> = \<four>"
proof -
   have S1: "\<two> = \<one> \<ca> \<one>" by (rule MMI_df_2)
   from S1 have S2: "\<two> \<ca> \<two> = \<two> \<ca> (\<one> \<ca> \<one>)" by (rule MMI_opreq2i)
   have S3: "\<four> = \<three> \<ca> \<one>" by (rule MMI_df_4)
   have S4: "\<three> = \<two> \<ca> \<one>" by (rule MMI_df_3)
   from S4 have S5: "\<three> \<ca> \<one> = \<two> \<ca> \<one> \<ca> \<one>" by (rule MMI_opreq1i)
   have S6: "\<two> \<in> \<complex>" by (rule MMI_2cn)
   have S7: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S8: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S6 S7 S8 have S9: "\<two> \<ca> \<one> \<ca> \<one> = \<two> \<ca> (\<one> \<ca> \<one>)" by (rule MMI_addass)
   from S3 S5 S9 have S10: "\<four> = \<two> \<ca> (\<one> \<ca> \<one>)" by (rule MMI_3eqtr)
   from S2 S10 show "\<two> \<ca> \<two> = \<four>" by (rule MMI_eqtr4)
qed

lemma (in MMIsar0) MMI_4nn: 
   shows "\<four> \<in> \<nat>"
proof -
   have S1: "\<two> \<ca> \<two> = \<four>" by (rule MMI_2p2e4)
   have S2: "\<two> \<in> \<nat>" by (rule MMI_2nn)
   have S3: "\<two> \<in> \<nat>" by (rule MMI_2nn)
   have S4: "\<two> \<in> \<nat> \<and> \<two> \<in> \<nat> \<longrightarrow> 
   \<two> \<ca> \<two> \<in> \<nat>" by (rule MMI_nnaddclt)
   from S2 S3 S4 have S5: "\<two> \<ca> \<two> \<in> \<nat>" by (rule MMI_mp2an)
   from S1 S5 show "\<four> \<in> \<nat>" by (rule MMI_eqeltrr)
qed

lemma (in MMIsar0) MMI_2times: assumes A1: "A \<in> \<complex>"   
   shows "\<two>\<cdot>A = A \<ca> A"
proof -
   have S1: "\<two> = \<one> \<ca> \<one>" by (rule MMI_df_2)
   from S1 have S2: "\<two>\<cdot>A = (\<one> \<ca> \<one>)\<cdot>A" by (rule MMI_opreq1i)
   from A1 have S3: "A \<in> \<complex>".
   from S3 have S4: "(\<one> \<ca> \<one>)\<cdot>A = A \<ca> A" by (rule MMI_1p1times)
   from S2 S4 show "\<two>\<cdot>A = A \<ca> A" by (rule MMI_eqtr)
qed

lemma (in MMIsar0) MMI_2timest: 
   shows "A \<in> \<complex> \<longrightarrow> \<two>\<cdot>A = A \<ca> A"
proof -
   have S1: "A =  if(A \<in> \<complex>, A, \<zero>) \<longrightarrow> 
   \<two>\<cdot>A = \<two>\<cdot>( if(A \<in> \<complex>, A, \<zero>))" by (rule MMI_opreq2)
   have S2: "A =  if(A \<in> \<complex>, A, \<zero>) \<longrightarrow> 
   A =  if(A \<in> \<complex>, A, \<zero>)" by (rule MMI_id)
   from S2 have S3: "A =  if(A \<in> \<complex>, A, \<zero>) \<longrightarrow> 
   A =  if(A \<in> \<complex>, A, \<zero>)" .
   from S2 S3 have S4: "A =  if(A \<in> \<complex>, A, \<zero>) \<longrightarrow> 
   A \<ca> A = ( if(A \<in> \<complex>, A, \<zero>)) \<ca> ( if(A \<in> \<complex>, A, \<zero>))" by (rule MMI_opreq12d)
   from S1 S4 have S5: "A =  if(A \<in> \<complex>, A, \<zero>) \<longrightarrow> 
   \<two>\<cdot>A = A \<ca> A \<longleftrightarrow> 
   \<two>\<cdot>( if(A \<in> \<complex>, A, \<zero>)) = ( if(A \<in> \<complex>, A, \<zero>)) \<ca> ( if(A \<in> \<complex>, A, \<zero>))" by (rule MMI_eqeq12d)
   have S6: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S6 have S7: " if(A \<in> \<complex>, A, \<zero>) \<in> \<complex>" by (rule MMI_elimel)
   from S7 have S8: "\<two>\<cdot>( if(A \<in> \<complex>, A, \<zero>)) = ( if(A \<in> \<complex>, A, \<zero>)) \<ca> ( if(A \<in> \<complex>, A, \<zero>))" by (rule MMI_2times)
   from S5 S8 show "A \<in> \<complex> \<longrightarrow> \<two>\<cdot>A = A \<ca> A" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_times2: assumes A1: "A \<in> \<complex>"   
   shows "A\<cdot>\<two> = A \<ca> A"
proof -
   from A1 have S1: "A \<in> \<complex>".
   have S2: "\<two> \<in> \<complex>" by (rule MMI_2cn)
   from S1 S2 have S3: "A\<cdot>\<two> = \<two>\<cdot>A" by (rule MMI_mulcom)
   from A1 have S4: "A \<in> \<complex>".
   from S4 have S5: "\<two>\<cdot>A = A \<ca> A" by (rule MMI_2times)
   from S3 S5 show "A\<cdot>\<two> = A \<ca> A" by (rule MMI_eqtr)
qed

lemma (in MMIsar0) MMI_3p2e5: 
   shows "\<three> \<ca> \<two> = \<five>"
proof -
   have S1: "\<four> = \<three> \<ca> \<one>" by (rule MMI_df_4)
   from S1 have S2: "\<four> \<ca> \<one> = \<three> \<ca> \<one> \<ca> \<one>" by (rule MMI_opreq1i)
   have S3: "\<five> = \<four> \<ca> \<one>" by (rule MMI_df_5)
   have S4: "\<two> = \<one> \<ca> \<one>" by (rule MMI_df_2)
   from S4 have S5: "\<three> \<ca> \<two> = \<three> \<ca> (\<one> \<ca> \<one>)" by (rule MMI_opreq2i)
   have S6: "\<three> \<in> \<real>" by (rule MMI_3re)
   from S6 have S7: "\<three> \<in> \<complex>" by (rule MMI_recn)
   have S8: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S9: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S7 S8 S9 have S10: "\<three> \<ca> \<one> \<ca> \<one> = \<three> \<ca> (\<one> \<ca> \<one>)" by (rule MMI_addass)
   from S5 S10 have S11: "\<three> \<ca> \<two> = \<three> \<ca> \<one> \<ca> \<one>" by (rule MMI_eqtr4)
   from S2 S3 S11 show "\<three> \<ca> \<two> = \<five>" by (rule MMI_3eqtr4r)
qed

lemma (in MMIsar0) MMI_3p3e6: 
   shows "\<three> \<ca> \<three> = \<six>"
proof -
   have S1: "\<three> \<ca> \<two> = \<five>" by (rule MMI_3p2e5)
   from S1 have S2: "\<three> \<ca> \<two> \<ca> \<one> = \<five> \<ca> \<one>" by (rule MMI_opreq1i)
   have S3: "\<three> = \<two> \<ca> \<one>" by (rule MMI_df_3)
   from S3 have S4: "\<three> \<ca> \<three> = \<three> \<ca> (\<two> \<ca> \<one>)" by (rule MMI_opreq2i)
   have S5: "\<three> \<in> \<real>" by (rule MMI_3re)
   from S5 have S6: "\<three> \<in> \<complex>" by (rule MMI_recn)
   have S7: "\<two> \<in> \<complex>" by (rule MMI_2cn)
   have S8: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S6 S7 S8 have S9: "\<three> \<ca> \<two> \<ca> \<one> = \<three> \<ca> (\<two> \<ca> \<one>)" by (rule MMI_addass)
   from S4 S9 have S10: "\<three> \<ca> \<three> = \<three> \<ca> \<two> \<ca> \<one>" by (rule MMI_eqtr4)
   have S11: "\<six> = \<five> \<ca> \<one>" by (rule MMI_df_6)
   from S2 S10 S11 show "\<three> \<ca> \<three> = \<six>" by (rule MMI_3eqtr4)
qed

lemma (in MMIsar0) MMI_4p2e6: 
   shows "\<four> \<ca> \<two> = \<six>"
proof -
   have S1: "\<five> = \<four> \<ca> \<one>" by (rule MMI_df_5)
   from S1 have S2: "\<five> \<ca> \<one> = \<four> \<ca> \<one> \<ca> \<one>" by (rule MMI_opreq1i)
   have S3: "\<six> = \<five> \<ca> \<one>" by (rule MMI_df_6)
   have S4: "\<two> = \<one> \<ca> \<one>" by (rule MMI_df_2)
   from S4 have S5: "\<four> \<ca> \<two> = \<four> \<ca> (\<one> \<ca> \<one>)" by (rule MMI_opreq2i)
   have S6: "\<four> \<in> \<real>" by (rule MMI_4re)
   from S6 have S7: "\<four> \<in> \<complex>" by (rule MMI_recn)
   have S8: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S9: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S7 S8 S9 have S10: "\<four> \<ca> \<one> \<ca> \<one> = \<four> \<ca> (\<one> \<ca> \<one>)" by (rule MMI_addass)
   from S5 S10 have S11: "\<four> \<ca> \<two> = \<four> \<ca> \<one> \<ca> \<one>" by (rule MMI_eqtr4)
   from S2 S3 S11 show "\<four> \<ca> \<two> = \<six>" by (rule MMI_3eqtr4r)
qed

lemma (in MMIsar0) MMI_4p3e7: 
   shows "\<four> \<ca> \<three> = \<seven>"
proof -
   have S1: "\<four> \<ca> \<two> = \<six>" by (rule MMI_4p2e6)
   from S1 have S2: "\<four> \<ca> \<two> \<ca> \<one> = \<six> \<ca> \<one>" by (rule MMI_opreq1i)
   have S3: "\<three> = \<two> \<ca> \<one>" by (rule MMI_df_3)
   from S3 have S4: "\<four> \<ca> \<three> = \<four> \<ca> (\<two> \<ca> \<one>)" by (rule MMI_opreq2i)
   have S5: "\<four> \<in> \<real>" by (rule MMI_4re)
   from S5 have S6: "\<four> \<in> \<complex>" by (rule MMI_recn)
   have S7: "\<two> \<in> \<complex>" by (rule MMI_2cn)
   have S8: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S6 S7 S8 have S9: "\<four> \<ca> \<two> \<ca> \<one> = \<four> \<ca> (\<two> \<ca> \<one>)" by (rule MMI_addass)
   from S4 S9 have S10: "\<four> \<ca> \<three> = \<four> \<ca> \<two> \<ca> \<one>" by (rule MMI_eqtr4)
   have S11: "\<seven> = \<six> \<ca> \<one>" by (rule MMI_df_7)
   from S2 S10 S11 show "\<four> \<ca> \<three> = \<seven>" by (rule MMI_3eqtr4)
qed

lemma (in MMIsar0) MMI_4p4e8: 
   shows "\<four> \<ca> \<four> = \<eight>"
proof -
   have S1: "\<four> \<ca> \<three> = \<seven>" by (rule MMI_4p3e7)
   from S1 have S2: "\<four> \<ca> \<three> \<ca> \<one> = \<seven> \<ca> \<one>" by (rule MMI_opreq1i)
   have S3: "\<four> = \<three> \<ca> \<one>" by (rule MMI_df_4)
   from S3 have S4: "\<four> \<ca> \<four> = \<four> \<ca> (\<three> \<ca> \<one>)" by (rule MMI_opreq2i)
   have S5: "\<four> \<in> \<real>" by (rule MMI_4re)
   from S5 have S6: "\<four> \<in> \<complex>" by (rule MMI_recn)
   have S7: "\<three> \<in> \<real>" by (rule MMI_3re)
   from S7 have S8: "\<three> \<in> \<complex>" by (rule MMI_recn)
   have S9: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S6 S8 S9 have S10: "\<four> \<ca> \<three> \<ca> \<one> = \<four> \<ca> (\<three> \<ca> \<one>)" by (rule MMI_addass)
   from S4 S10 have S11: "\<four> \<ca> \<four> = \<four> \<ca> \<three> \<ca> \<one>" by (rule MMI_eqtr4)
   have S12: "\<eight> = \<seven> \<ca> \<one>" by (rule MMI_df_8)
   from S2 S11 S12 show "\<four> \<ca> \<four> = \<eight>" by (rule MMI_3eqtr4)
qed

lemma (in MMIsar0) MMI_5p2e7: 
   shows "\<five> \<ca> \<two> = \<seven>"
proof -
   have S1: "\<six> = \<five> \<ca> \<one>" by (rule MMI_df_6)
   from S1 have S2: "\<six> \<ca> \<one> = \<five> \<ca> \<one> \<ca> \<one>" by (rule MMI_opreq1i)
   have S3: "\<seven> = \<six> \<ca> \<one>" by (rule MMI_df_7)
   have S4: "\<two> = \<one> \<ca> \<one>" by (rule MMI_df_2)
   from S4 have S5: "\<five> \<ca> \<two> = \<five> \<ca> (\<one> \<ca> \<one>)" by (rule MMI_opreq2i)
   have S6: "\<five> \<in> \<real>" by (rule MMI_5re)
   from S6 have S7: "\<five> \<in> \<complex>" by (rule MMI_recn)
   have S8: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S9: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S7 S8 S9 have S10: "\<five> \<ca> \<one> \<ca> \<one> = \<five> \<ca> (\<one> \<ca> \<one>)" by (rule MMI_addass)
   from S5 S10 have S11: "\<five> \<ca> \<two> = \<five> \<ca> \<one> \<ca> \<one>" by (rule MMI_eqtr4)
   from S2 S3 S11 show "\<five> \<ca> \<two> = \<seven>" by (rule MMI_3eqtr4r)
qed

lemma (in MMIsar0) MMI_5p3e8: 
   shows "\<five> \<ca> \<three> = \<eight>"
proof -
   have S1: "\<five> \<ca> \<two> = \<seven>" by (rule MMI_5p2e7)
   from S1 have S2: "\<five> \<ca> \<two> \<ca> \<one> = \<seven> \<ca> \<one>" by (rule MMI_opreq1i)
   have S3: "\<three> = \<two> \<ca> \<one>" by (rule MMI_df_3)
   from S3 have S4: "\<five> \<ca> \<three> = \<five> \<ca> (\<two> \<ca> \<one>)" by (rule MMI_opreq2i)
   have S5: "\<five> \<in> \<real>" by (rule MMI_5re)
   from S5 have S6: "\<five> \<in> \<complex>" by (rule MMI_recn)
   have S7: "\<two> \<in> \<complex>" by (rule MMI_2cn)
   have S8: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S6 S7 S8 have S9: "\<five> \<ca> \<two> \<ca> \<one> = \<five> \<ca> (\<two> \<ca> \<one>)" by (rule MMI_addass)
   from S4 S9 have S10: "\<five> \<ca> \<three> = \<five> \<ca> \<two> \<ca> \<one>" by (rule MMI_eqtr4)
   have S11: "\<eight> = \<seven> \<ca> \<one>" by (rule MMI_df_8)
   from S2 S10 S11 show "\<five> \<ca> \<three> = \<eight>" by (rule MMI_3eqtr4)
qed

lemma (in MMIsar0) MMI_5p4e9: 
   shows "\<five> \<ca> \<four> = \<nine>"
proof -
   have S1: "\<five> \<ca> \<three> = \<eight>" by (rule MMI_5p3e8)
   from S1 have S2: "\<five> \<ca> \<three> \<ca> \<one> = \<eight> \<ca> \<one>" by (rule MMI_opreq1i)
   have S3: "\<four> = \<three> \<ca> \<one>" by (rule MMI_df_4)
   from S3 have S4: "\<five> \<ca> \<four> = \<five> \<ca> (\<three> \<ca> \<one>)" by (rule MMI_opreq2i)
   have S5: "\<five> \<in> \<real>" by (rule MMI_5re)
   from S5 have S6: "\<five> \<in> \<complex>" by (rule MMI_recn)
   have S7: "\<three> \<in> \<real>" by (rule MMI_3re)
   from S7 have S8: "\<three> \<in> \<complex>" by (rule MMI_recn)
   have S9: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S6 S8 S9 have S10: "\<five> \<ca> \<three> \<ca> \<one> = \<five> \<ca> (\<three> \<ca> \<one>)" by (rule MMI_addass)
   from S4 S10 have S11: "\<five> \<ca> \<four> = \<five> \<ca> \<three> \<ca> \<one>" by (rule MMI_eqtr4)
   have S12: "\<nine> = \<eight> \<ca> \<one>" by (rule MMI_df_9)
   from S2 S11 S12 show "\<five> \<ca> \<four> = \<nine>" by (rule MMI_3eqtr4)
qed

lemma (in MMIsar0) MMI_6p2e8: 
   shows "\<six> \<ca> \<two> = \<eight>"
proof -
   have S1: "\<seven> = \<six> \<ca> \<one>" by (rule MMI_df_7)
   from S1 have S2: "\<seven> \<ca> \<one> = \<six> \<ca> \<one> \<ca> \<one>" by (rule MMI_opreq1i)
   have S3: "\<eight> = \<seven> \<ca> \<one>" by (rule MMI_df_8)
   have S4: "\<two> = \<one> \<ca> \<one>" by (rule MMI_df_2)
   from S4 have S5: "\<six> \<ca> \<two> = \<six> \<ca> (\<one> \<ca> \<one>)" by (rule MMI_opreq2i)
   have S6: "\<six> \<in> \<real>" by (rule MMI_6re)
   from S6 have S7: "\<six> \<in> \<complex>" by (rule MMI_recn)
   have S8: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S9: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S7 S8 S9 have S10: "\<six> \<ca> \<one> \<ca> \<one> = \<six> \<ca> (\<one> \<ca> \<one>)" by (rule MMI_addass)
   from S5 S10 have S11: "\<six> \<ca> \<two> = \<six> \<ca> \<one> \<ca> \<one>" by (rule MMI_eqtr4)
   from S2 S3 S11 show "\<six> \<ca> \<two> = \<eight>" by (rule MMI_3eqtr4r)
qed

lemma (in MMIsar0) MMI_6p3e9: 
   shows "\<six> \<ca> \<three> = \<nine>"
proof -
   have S1: "\<six> \<ca> \<two> = \<eight>" by (rule MMI_6p2e8)
   from S1 have S2: "\<six> \<ca> \<two> \<ca> \<one> = \<eight> \<ca> \<one>" by (rule MMI_opreq1i)
   have S3: "\<three> = \<two> \<ca> \<one>" by (rule MMI_df_3)
   from S3 have S4: "\<six> \<ca> \<three> = \<six> \<ca> (\<two> \<ca> \<one>)" by (rule MMI_opreq2i)
   have S5: "\<six> \<in> \<real>" by (rule MMI_6re)
   from S5 have S6: "\<six> \<in> \<complex>" by (rule MMI_recn)
   have S7: "\<two> \<in> \<complex>" by (rule MMI_2cn)
   have S8: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S6 S7 S8 have S9: "\<six> \<ca> \<two> \<ca> \<one> = \<six> \<ca> (\<two> \<ca> \<one>)" by (rule MMI_addass)
   from S4 S9 have S10: "\<six> \<ca> \<three> = \<six> \<ca> \<two> \<ca> \<one>" by (rule MMI_eqtr4)
   have S11: "\<nine> = \<eight> \<ca> \<one>" by (rule MMI_df_9)
   from S2 S10 S11 show "\<six> \<ca> \<three> = \<nine>" by (rule MMI_3eqtr4)
qed

lemma (in MMIsar0) MMI_7p2e9: 
   shows "\<seven> \<ca> \<two> = \<nine>"
proof -
   have S1: "\<eight> = \<seven> \<ca> \<one>" by (rule MMI_df_8)
   from S1 have S2: "\<eight> \<ca> \<one> = \<seven> \<ca> \<one> \<ca> \<one>" by (rule MMI_opreq1i)
   have S3: "\<nine> = \<eight> \<ca> \<one>" by (rule MMI_df_9)
   have S4: "\<two> = \<one> \<ca> \<one>" by (rule MMI_df_2)
   from S4 have S5: "\<seven> \<ca> \<two> = \<seven> \<ca> (\<one> \<ca> \<one>)" by (rule MMI_opreq2i)
   have S6: "\<seven> \<in> \<real>" by (rule MMI_7re)
   from S6 have S7: "\<seven> \<in> \<complex>" by (rule MMI_recn)
   have S8: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S9: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S7 S8 S9 have S10: "\<seven> \<ca> \<one> \<ca> \<one> = \<seven> \<ca> (\<one> \<ca> \<one>)" by (rule MMI_addass)
   from S5 S10 have S11: "\<seven> \<ca> \<two> = \<seven> \<ca> \<one> \<ca> \<one>" by (rule MMI_eqtr4)
   from S2 S3 S11 show "\<seven> \<ca> \<two> = \<nine>" by (rule MMI_3eqtr4r)
qed

lemma (in MMIsar0) MMI_2t2e4: 
   shows "\<two>\<cdot>\<two> = \<four>"
proof -
   have S1: "\<two> \<in> \<complex>" by (rule MMI_2cn)
   from S1 have S2: "\<two>\<cdot>\<two> = \<two> \<ca> \<two>" by (rule MMI_2times)
   have S3: "\<two> \<ca> \<two> = \<four>" by (rule MMI_2p2e4)
   from S2 S3 show "\<two>\<cdot>\<two> = \<four>" by (rule MMI_eqtr)
qed

lemma (in MMIsar0) MMI_3t2e6: 
   shows "\<three>\<cdot>\<two> = \<six>"
proof -
   have S1: "\<three> \<in> \<real>" by (rule MMI_3re)
   from S1 have S2: "\<three> \<in> \<complex>" by (rule MMI_recn)
   from S2 have S3: "\<three>\<cdot>\<two> = \<three> \<ca> \<three>" by (rule MMI_times2)
   have S4: "\<three> \<ca> \<three> = \<six>" by (rule MMI_3p3e6)
   from S3 S4 show "\<three>\<cdot>\<two> = \<six>" by (rule MMI_eqtr)
qed

lemma (in MMIsar0) MMI_3t3e9: 
   shows "\<three>\<cdot>\<three> = \<nine>"
proof -
   have S1: "\<three> = \<two> \<ca> \<one>" by (rule MMI_df_3)
   from S1 have S2: "\<three>\<cdot>\<three> = \<three>\<cdot>(\<two> \<ca> \<one>)" by (rule MMI_opreq2i)
   have S3: "\<three> \<in> \<real>" by (rule MMI_3re)
   from S3 have S4: "\<three> \<in> \<complex>" by (rule MMI_recn)
   have S5: "\<two> \<in> \<complex>" by (rule MMI_2cn)
   have S6: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S4 S5 S6 have S7: "\<three>\<cdot>(\<two> \<ca> \<one>) = \<three>\<cdot>\<two> \<ca> \<three>\<cdot>\<one>" by (rule MMI_adddi)
   have S8: "\<three>\<cdot>\<two> = \<six>" by (rule MMI_3t2e6)
   from S4 have S9: "\<three> \<in> \<complex>" .
   from S9 have S10: "\<three>\<cdot>\<one> = \<three>" by (rule MMI_mulid1)
   from S8 S10 have S11: "\<three>\<cdot>\<two> \<ca> \<three>\<cdot>\<one> = \<six> \<ca> \<three>" by (rule MMI_opreq12i)
   from S7 S11 have S12: "\<three>\<cdot>(\<two> \<ca> \<one>) = \<six> \<ca> \<three>" by (rule MMI_eqtr)
   have S13: "\<six> \<ca> \<three> = \<nine>" by (rule MMI_6p3e9)
   from S2 S12 S13 show "\<three>\<cdot>\<three> = \<nine>" by (rule MMI_3eqtr)
qed

(******** 561-578 ********************)

lemma (in MMIsar0) MMI_ltdiv23i: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>" and
    A3: "C \<in> \<real>" and
    A4: "\<zero> \<ls> B" and
    A5: "\<zero> \<ls> C"   
   shows "A\<cdiv>B \<ls> C \<longleftrightarrow> A\<cdiv>C \<ls> B"
proof -
   from A4 have S1: "\<zero> \<ls> B".
   from A5 have S2: "\<zero> \<ls> C".
   from A1 have S3: "A \<in> \<real>".
   from A2 have S4: "B \<in> \<real>".
   from A3 have S5: "C \<in> \<real>".
   from S3 S4 S5 have S6: "\<zero> \<ls> B \<and> \<zero> \<ls> C \<longrightarrow> 
   A\<cdiv>B \<ls> C \<longleftrightarrow> A\<cdiv>C \<ls> B" by (rule MMI_ltdiv23)
   from S1 S2 S6 show "A\<cdiv>B \<ls> C \<longleftrightarrow> A\<cdiv>C \<ls> B" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_4t2e8: 
   shows "\<four>\<cdot>\<two> = \<eight>"
proof -
   have S1: "\<four> \<in> \<real>" by (rule MMI_4re)
   from S1 have S2: "\<four> \<in> \<complex>" by (rule MMI_recn)
   from S2 have S3: "\<four>\<cdot>\<two> = \<four> \<ca> \<four>" by (rule MMI_times2)
   have S4: "\<four> \<ca> \<four> = \<eight>" by (rule MMI_4p4e8)
   from S3 S4 show "\<four>\<cdot>\<two> = \<eight>" by (rule MMI_eqtr)
qed

lemma (in MMIsar0) MMI_4d2e2: 
   shows "\<four>\<cdiv>\<two> = \<two>"
proof -
   have S1: "\<two>\<cdot>\<two> = \<four>" by (rule MMI_2t2e4)
   have S2: "\<four> \<in> \<real>" by (rule MMI_4re)
   from S2 have S3: "\<four> \<in> \<complex>" by (rule MMI_recn)
   have S4: "\<two> \<in> \<complex>" by (rule MMI_2cn)
   have S5: "\<two> \<in> \<complex>" by (rule MMI_2cn)
   have S6: "\<two> \<in> \<real>" by (rule MMI_2re)
   have S7: "\<zero> \<ls> \<two>" by (rule MMI_2pos)
   from S6 S7 have S8: "\<two> \<noteq> \<zero>" by (rule MMI_gt0ne0i)
   from S3 S4 S5 S8 have S9: "\<four>\<cdiv>\<two> = \<two> \<longleftrightarrow> \<two>\<cdot>\<two> = \<four>" by (rule MMI_divmul)
   from S1 S9 show "\<four>\<cdiv>\<two> = \<two>" by (rule MMI_mpbir)
qed

lemma (in MMIsar0) MMI_1lt2: 
   shows "\<one> \<ls> \<two>"
proof -
   have S1: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S1 have S2: "\<one> \<ls> \<one> \<ca> \<one>" by (rule MMI_ltp1)
   have S3: "\<two> = \<one> \<ca> \<one>" by (rule MMI_df_2)
   from S2 S3 show "\<one> \<ls> \<two>" by (rule MMI_breqtrr)
qed

lemma (in MMIsar0) MMI_halfgt0: 
   shows "\<zero> \<ls> \<one>\<cdiv>\<two>"
proof -
   have S1: "\<two> \<in> \<real>" by (rule MMI_2re)
   have S2: "\<zero> \<ls> \<two>" by (rule MMI_2pos)
   from S1 S2 show "\<zero> \<ls> \<one>\<cdiv>\<two>" by (rule MMI_recgt0i)
qed

lemma (in MMIsar0) MMI_halflt1: 
   shows "\<one>\<cdiv>\<two> \<ls> \<one>"
proof -
   have S1: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S1 have S2: "\<one>\<cdiv>\<one> = \<one>" by (rule MMI_div1)
   have S3: "\<one> \<ls> \<two>" by (rule MMI_1lt2)
   from S2 S3 have S4: "\<one>\<cdiv>\<one> \<ls> \<two>" by (rule MMI_eqbrtr)
   have S5: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S6: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S7: "\<two> \<in> \<real>" by (rule MMI_2re)
   have S8: "\<zero> \<ls> \<one>" by (rule MMI_lt01)
   have S9: "\<zero> \<ls> \<two>" by (rule MMI_2pos)
   from S5 S6 S7 S8 S9 have S10: "\<one>\<cdiv>\<one> \<ls> \<two> \<longleftrightarrow> 
   \<one>\<cdiv>\<two> \<ls> \<one>" by (rule MMI_ltdiv23i)
   from S4 S10 show "\<one>\<cdiv>\<two> \<ls> \<one>" by (rule MMI_mpbi)
qed

lemma (in MMIsar0) MMI_halfclt: 
   shows "A \<in> \<complex> \<longrightarrow> 
   A\<cdiv>\<two> \<in> \<complex>"
proof -
   have S1: "\<two> \<in> \<complex>" by (rule MMI_2cn)
   have S2: "\<two> \<in> \<real>" by (rule MMI_2re)
   have S3: "\<zero> \<ls> \<two>" by (rule MMI_2pos)
   from S2 S3 have S4: "\<two> \<noteq> \<zero>" by (rule MMI_gt0ne0i)
   have S5: "A \<in> \<complex> \<and> \<two> \<in> \<complex> \<and> \<two> \<noteq> \<zero> \<longrightarrow> 
   A\<cdiv>\<two> \<in> \<complex>" by (rule MMI_divclt)
   from S1 S4 S5 show "A \<in> \<complex> \<longrightarrow> 
   A\<cdiv>\<two> \<in> \<complex>" by (rule MMI_mp3an23)
qed

lemma (in MMIsar0) MMI_rehalfclt: 
   shows "A \<in> \<real> \<longrightarrow> A\<cdiv>\<two> \<in> \<real>"
proof -
   have S1: "\<two> \<in> \<real>" by (rule MMI_2re)
   have S2: "\<two> \<in> \<real>" by (rule MMI_2re)
   have S3: "\<zero> \<ls> \<two>" by (rule MMI_2pos)
   from S2 S3 have S4: "\<two> \<noteq> \<zero>" by (rule MMI_gt0ne0i)
   have S5: "A \<in> \<real> \<and> \<two> \<in> \<real> \<and> \<two> \<noteq> \<zero> \<longrightarrow> A\<cdiv>\<two> \<in> \<real>" by (rule MMI_redivclt)
   from S1 S4 S5 show "A \<in> \<real> \<longrightarrow> A\<cdiv>\<two> \<in> \<real>" by (rule MMI_mp3an23)
qed

lemma (in MMIsar0) MMI_half0t: 
   shows "A \<in> \<complex> \<longrightarrow> 
   A\<cdiv>\<two> = \<zero> \<longleftrightarrow> A = \<zero>"
proof -
   have S1: "\<two> \<in> \<complex>" by (rule MMI_2cn)
   have S2: "\<two> \<in> \<real>" by (rule MMI_2re)
   have S3: "\<zero> \<ls> \<two>" by (rule MMI_2pos)
   from S2 S3 have S4: "\<two> \<noteq> \<zero>" by (rule MMI_gt0ne0i)
   have S5: "A \<in> \<complex> \<and> \<two> \<in> \<complex> \<and> \<two> \<noteq> \<zero> \<longrightarrow> 
   A\<cdiv>\<two> = \<zero> \<longleftrightarrow> A = \<zero>" by (rule MMI_diveq0t)
   from S1 S4 S5 show "A \<in> \<complex> \<longrightarrow> 
   A\<cdiv>\<two> = \<zero> \<longleftrightarrow> A = \<zero>" by (rule MMI_mp3an23)
qed

lemma (in MMIsar0) MMI_halfpost: 
   shows "A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<longleftrightarrow> A\<cdiv>\<two> \<ls> A"
proof -
   have S1: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   \<zero> \<ls> A \<longleftrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq2)
   have S2: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdiv>(\<one> \<ca> \<one>) = ( if(A \<in> \<real>, A, \<zero>))\<cdiv>(\<one> \<ca> \<one>)" by (rule MMI_opreq1)
   have S3: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A =  if(A \<in> \<real>, A, \<zero>)" by (rule MMI_id)
   from S2 S3 have S4: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   A\<cdiv>(\<one> \<ca> \<one>) \<ls> A \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>(\<one> \<ca> \<one>) \<ls> ( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_breq12d)
   from S1 S4 have S5: "A =  if(A \<in> \<real>, A, \<zero>) \<longrightarrow> 
   (\<zero> \<ls> A \<longleftrightarrow> 
   A\<cdiv>(\<one> \<ca> \<one>) \<ls> A) \<longleftrightarrow> 
   \<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>(\<one> \<ca> \<one>) \<ls> ( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_bibi12d)
   have S6: "\<zero> \<in> \<real>" by (rule MMI_0re)
   from S6 have S7: " if(A \<in> \<real>, A, \<zero>) \<in> \<real>" by (rule MMI_elimel)
   from S7 have S8: "\<zero> \<ls> ( if(A \<in> \<real>, A, \<zero>)) \<longleftrightarrow> 
   ( if(A \<in> \<real>, A, \<zero>))\<cdiv>(\<one> \<ca> \<one>) \<ls> ( if(A \<in> \<real>, A, \<zero>))" by (rule MMI_halfpos)
   from S5 S8 have S9: "A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<longleftrightarrow> 
   A\<cdiv>(\<one> \<ca> \<one>) \<ls> A" by (rule MMI_dedth)
   have S10: "\<two> = \<one> \<ca> \<one>" by (rule MMI_df_2)
   from S10 have S11: "A\<cdiv>\<two> = A\<cdiv>(\<one> \<ca> \<one>)" by auto (*rule MMI_opreq2i*)
   from S11 have S12: "A\<cdiv>\<two> \<ls> A \<longleftrightarrow> 
   A\<cdiv>(\<one> \<ca> \<one>) \<ls> A" by (rule MMI_breq1i)
   from S9 S12 show "A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<longleftrightarrow> A\<cdiv>\<two> \<ls> A" by (rule MMI_syl6bbr)
qed

lemma (in MMIsar0) MMI_halfpos2t: 
   shows "A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<longleftrightarrow> \<zero> \<ls> A\<cdiv>\<two>"
proof -
   have S1: "\<two> \<in> \<real>" by (rule MMI_2re)
   have S2: "\<zero> \<ls> \<two>" by (rule MMI_2pos)
   have S3: "A \<in> \<real> \<and> \<two> \<in> \<real> \<and> \<zero> \<ls> \<two> \<longrightarrow> 
   \<zero> \<ls> A \<longleftrightarrow> \<zero> \<ls> A\<cdiv>\<two>" by (rule MMI_gt0divt)
   from S1 S2 S3 show "A \<in> \<real> \<longrightarrow> 
   \<zero> \<ls> A \<longleftrightarrow> \<zero> \<ls> A\<cdiv>\<two>" by (rule MMI_mp3an23)
qed

lemma (in MMIsar0) MMI_halfnneg2t: 
   shows "A \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> \<zero> \<lsq> A\<cdiv>\<two>"
proof -
   have S1: "\<two> \<in> \<real>" by (rule MMI_2re)
   have S2: "\<zero> \<ls> \<two>" by (rule MMI_2pos)
   have S3: "A \<in> \<real> \<and> \<two> \<in> \<real> \<and> \<zero> \<ls> \<two> \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> \<zero> \<lsq> A\<cdiv>\<two>" by (rule MMI_ge0divt)
   from S1 S2 S3 show "A \<in> \<real> \<longrightarrow> 
   \<zero> \<lsq> A \<longleftrightarrow> \<zero> \<lsq> A\<cdiv>\<two>" by (rule MMI_mp3an23)
qed

lemma (in MMIsar0) MMI_2halvest: 
   shows "A \<in> \<complex> \<longrightarrow> 
   A\<cdiv>\<two> \<ca> A\<cdiv>\<two> = A"
proof -
   have S1: "A \<in> \<complex> \<longrightarrow> \<two>\<cdot>A = A \<ca> A" by (rule MMI_2timest)
   from S1 have S2: "A \<in> \<complex> \<longrightarrow> 
   \<two>\<cdot>A\<cdiv>\<two> = (A \<ca> A)\<cdiv>\<two>" by (rule MMI_opreq1d)
   have S3: "\<two> \<in> \<complex>" by (rule MMI_2cn)
   have S4: "\<two> \<in> \<real>" by (rule MMI_2re)
   have S5: "\<zero> \<ls> \<two>" by (rule MMI_2pos)
   from S4 S5 have S6: "\<two> \<noteq> \<zero>" by (rule MMI_gt0ne0i)
   have S7: "\<two> \<in> \<complex> \<and> A \<in> \<complex> \<and> \<two> \<noteq> \<zero> \<longrightarrow> 
   \<two>\<cdot>A\<cdiv>\<two> = A" by (rule MMI_divcan3t)
   from S3 S6 S7 have S8: "A \<in> \<complex> \<longrightarrow> 
   \<two>\<cdot>A\<cdiv>\<two> = A" by (rule MMI_mp3an13)
   have S9: "\<two> \<in> \<complex>" by (rule MMI_2cn)
   from S6 have S10: "\<two> \<noteq> \<zero>" .
   have S11: "(A \<in> \<complex> \<and> A \<in> \<complex> \<and> \<two> \<in> \<complex>) \<and> \<two> \<noteq> \<zero> \<longrightarrow> 
   (A \<ca> A)\<cdiv>\<two> = A\<cdiv>\<two> \<ca> A\<cdiv>\<two>" by (rule MMI_divdirt)
   from S10 S11 have S12: "A \<in> \<complex> \<and> A \<in> \<complex> \<and> \<two> \<in> \<complex> \<longrightarrow> 
   (A \<ca> A)\<cdiv>\<two> = A\<cdiv>\<two> \<ca> A\<cdiv>\<two>" by (rule MMI_mpan2)
   from S9 S12 have S13: "A \<in> \<complex> \<and> A \<in> \<complex> \<longrightarrow> 
   (A \<ca> A)\<cdiv>\<two> = A\<cdiv>\<two> \<ca> A\<cdiv>\<two>" by (rule MMI_mp3an3)
   from S13 have S14: "A \<in> \<complex> \<longrightarrow> 
   (A \<ca> A)\<cdiv>\<two> = A\<cdiv>\<two> \<ca> A\<cdiv>\<two>" by (rule MMI_anidms)
   from S2 S8 S14 show "A \<in> \<complex> \<longrightarrow> 
   A\<cdiv>\<two> \<ca> A\<cdiv>\<two> = A" by (rule MMI_3eqtr3rd)
qed

lemma (in MMIsar0) MMI_nominpos: 
   shows "\<not>( \<exists>x\<in>\<real>. \<zero> \<ls> x \<and> \<not>( \<exists>y\<in>\<real>. \<zero> \<ls> y \<and> y \<ls> x))"
proof -
   have S1: "\<zero> \<ls> \<two>" by (rule MMI_2pos)
   have S2: "\<two> \<in> \<real>" by (rule MMI_2re)
   { fix x
     have S3: "(x \<in> \<real> \<and> \<two> \<in> \<real>) \<and> \<zero> \<ls> x \<and> \<zero> \<ls> \<two> \<longrightarrow> \<zero> \<ls> x\<cdiv>\<two>" 
       by (rule MMI_divgt0t)
     from S3 have S4: "x \<in> \<real> \<and> \<two> \<in> \<real> \<longrightarrow> 
       \<zero> \<ls> x \<and> \<zero> \<ls> \<two> \<longrightarrow> \<zero> \<ls> x\<cdiv>\<two>" by (rule MMI_ex)
     from S2 S4 have S5: "x \<in> \<real> \<longrightarrow> 
       \<zero> \<ls> x \<and> \<zero> \<ls> \<two> \<longrightarrow> \<zero> \<ls> x\<cdiv>\<two>" by (rule MMI_mpan2)
     from S1 S5 have S6: "x \<in> \<real> \<longrightarrow> 
       \<zero> \<ls> x \<longrightarrow> \<zero> \<ls> x\<cdiv>\<two>" by (rule MMI_mpan2i)
     have S7: "x \<in> \<real> \<longrightarrow> 
       \<zero> \<ls> x \<longleftrightarrow> x\<cdiv>\<two> \<ls> x" by (rule MMI_halfpost)
     from S7 have S8: "x \<in> \<real> \<longrightarrow> 
       \<zero> \<ls> x \<longrightarrow> x\<cdiv>\<two> \<ls> x" by (rule MMI_biimpd)
     from S6 S8 have S9: "x \<in> \<real> \<longrightarrow> 
       \<zero> \<ls> x \<longrightarrow> 
       \<zero> \<ls> x\<cdiv>\<two> \<and> x\<cdiv>\<two> \<ls> x" by (rule MMI_jcad)
     have S10: "x \<in> \<real> \<longrightarrow> x\<cdiv>\<two> \<in> \<real>" by (rule MMI_rehalfclt)
     from S9 S10 have S11: "x \<in> \<real> \<longrightarrow> 
       \<zero> \<ls> x \<longrightarrow> 
       x\<cdiv>\<two> \<in> \<real> \<and> \<zero> \<ls> x\<cdiv>\<two> \<and> x\<cdiv>\<two> \<ls> x" by (rule MMI_jctild)
     have S12: "y = x\<cdiv>\<two> \<longrightarrow> 
       \<zero> \<ls> y \<longleftrightarrow> \<zero> \<ls> x\<cdiv>\<two>" by (rule MMI_breq2)
     have S13: "y = x\<cdiv>\<two> \<longrightarrow> 
       y \<ls> x \<longleftrightarrow> x\<cdiv>\<two> \<ls> x" by (rule MMI_breq1)
     from S12 S13 have S14: "y = x\<cdiv>\<two> \<longrightarrow> 
       \<zero> \<ls> y \<and> y \<ls> x \<longleftrightarrow> 
       \<zero> \<ls> x\<cdiv>\<two> \<and> x\<cdiv>\<two> \<ls> x" by (rule MMI_anbi12d)
     from S14 have S15: "x\<cdiv>\<two> \<in> \<real> \<and> \<zero> \<ls> x\<cdiv>\<two> \<and> x\<cdiv>\<two> \<ls> x \<longrightarrow> 
       ( \<exists>y\<in>\<real>. \<zero> \<ls> y \<and> y \<ls> x)" by auto (*rule MMI_rcla4ev*)
     from S11 S15 have S16: "x \<in> \<real> \<longrightarrow> 
       \<zero> \<ls> x \<longrightarrow> 
       ( \<exists>y\<in>\<real>. \<zero> \<ls> y \<and> y \<ls> x)" by (rule MMI_syl6)
     have S17: "(\<zero> \<ls> x \<longrightarrow> 
       ( \<exists>y\<in>\<real>. \<zero> \<ls> y \<and> y \<ls> x)) \<longleftrightarrow> 
       \<not>(\<zero> \<ls> x \<and> \<not>( \<exists>y\<in>\<real>. \<zero> \<ls> y \<and> y \<ls> x))" by (rule MMI_iman)
     from S16 S17 have "x \<in> \<real> \<longrightarrow> 
       \<not>(\<zero> \<ls> x \<and> \<not>( \<exists>y\<in>\<real>. \<zero> \<ls> y \<and> y \<ls> x))" by (rule MMI_sylib)
     } then have  S18: "\<forall> x. x \<in> \<real> \<longrightarrow> 
       \<not>(\<zero> \<ls> x \<and> \<not>( \<exists>y\<in>\<real>. \<zero> \<ls> y \<and> y \<ls> x))" by simp
   from S18 show "\<not>( \<exists>x\<in>\<real>. \<zero> \<ls> x \<and> \<not>( \<exists>y\<in>\<real>. \<zero> \<ls> y \<and> y \<ls> x))" 
     by (rule MMI_nrex)
qed

lemma (in MMIsar0) MMI_avglet: 
   shows "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (A \<ca> B)\<cdiv>\<two> \<lsq> A \<or> (A \<ca> B)\<cdiv>\<two> \<lsq> B"
proof -
   have S1: "\<two>\<cdot>A \<in> \<real> \<and> A \<ca> B \<in> \<real> \<longrightarrow> 
   \<two>\<cdot>A \<ls> A \<ca> B \<longleftrightarrow> 
   \<not>(A \<ca> B \<lsq> \<two>\<cdot>A)" by (rule MMI_ltnlet)
   have S2: "\<two> \<in> \<real>" by (rule MMI_2re)
   have S3: "\<two> \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> \<two>\<cdot>A \<in> \<real>" by (rule MMI_axmulrcl)
   from S2 S3 have S4: "A \<in> \<real> \<longrightarrow> \<two>\<cdot>A \<in> \<real>" by (rule MMI_mpan)
   from S4 have S5: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> \<two>\<cdot>A \<in> \<real>" by (rule MMI_adantr)
   have S6: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<ca> B \<in> \<real>" by (rule MMI_axaddrcl)
   from S1 S5 S6 have S7: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<two>\<cdot>A \<ls> A \<ca> B \<longleftrightarrow> 
   \<not>(A \<ca> B \<lsq> \<two>\<cdot>A)" by (rule MMI_sylanc)
   have S8: "A \<in> \<real> \<and> B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A \<ca> A \<ls> A \<ca> B" by (rule MMI_ltadd2t)
   have S9: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<in> \<real>" by (rule MMI_pm3_26)
   have S10: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> B \<in> \<real>" by (rule MMI_pm3_27)
   from S9 have S11: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<in> \<real>" .
   from S8 S9 S10 S11 have S12: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A \<ca> A \<ls> A \<ca> B" by (rule MMI_syl3anc)
   have S13: "A \<in> \<real> \<and> B \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A \<ca> B \<ls> B \<ca> B" by (rule MMI_ltadd1t)
   from S9 have S14: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<in> \<real>" .
   from S10 have S15: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> B \<in> \<real>" .
   from S10 have S16: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> B \<in> \<real>" .
   from S13 S14 S15 S16 have S17: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ls> B \<longleftrightarrow> A \<ca> B \<ls> B \<ca> B" by (rule MMI_syl3anc)
   from S12 S17 have S18: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ca> A \<ls> A \<ca> B \<longleftrightarrow> A \<ca> B \<ls> B \<ca> B" by (rule MMI_bitr3d)
   have S19: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S20: "A \<in> \<complex> \<longrightarrow> \<two>\<cdot>A = A \<ca> A" by (rule MMI_2timest)
   from S19 S20 have S21: "A \<in> \<real> \<longrightarrow> \<two>\<cdot>A = A \<ca> A" by (rule MMI_syl)
   from S21 have S22: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> \<two>\<cdot>A = A \<ca> A" by (rule MMI_adantr)
   from S22 have S23: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<two>\<cdot>A \<ls> A \<ca> B \<longleftrightarrow> A \<ca> A \<ls> A \<ca> B" by (rule MMI_breq1d)
   have S24: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   have S25: "B \<in> \<complex> \<longrightarrow> \<two>\<cdot>B = B \<ca> B" by (rule MMI_2timest)
   from S24 S25 have S26: "B \<in> \<real> \<longrightarrow> \<two>\<cdot>B = B \<ca> B" by (rule MMI_syl)
   from S26 have S27: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> \<two>\<cdot>B = B \<ca> B" by (rule MMI_adantl)
   from S27 have S28: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ca> B \<ls> \<two>\<cdot>B \<longleftrightarrow> A \<ca> B \<ls> B \<ca> B" by (rule MMI_breq2d)
   from S18 S23 S28 have S29: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<two>\<cdot>A \<ls> A \<ca> B \<longleftrightarrow> A \<ca> B \<ls> \<two>\<cdot>B" by (rule MMI_3bitr4d)
   have S30: "A \<ca> B \<in> \<real> \<and> \<two>\<cdot>B \<in> \<real> \<longrightarrow> 
   A \<ca> B \<ls> \<two>\<cdot>B \<longrightarrow> 
   A \<ca> B \<lsq> \<two>\<cdot>B" by (rule MMI_ltlet)
   from S6 have S31: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<ca> B \<in> \<real>" .
   have S32: "\<two> \<in> \<real>" by (rule MMI_2re)
   have S33: "\<two> \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> \<two>\<cdot>B \<in> \<real>" by (rule MMI_axmulrcl)
   from S32 S33 have S34: "B \<in> \<real> \<longrightarrow> \<two>\<cdot>B \<in> \<real>" by (rule MMI_mpan)
   from S34 have S35: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> \<two>\<cdot>B \<in> \<real>" by (rule MMI_adantl)
   from S30 S31 S35 have S36: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ca> B \<ls> \<two>\<cdot>B \<longrightarrow> 
   A \<ca> B \<lsq> \<two>\<cdot>B" by (rule MMI_sylanc)
   from S29 S36 have S37: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<two>\<cdot>A \<ls> A \<ca> B \<longrightarrow> 
   A \<ca> B \<lsq> \<two>\<cdot>B" by (rule MMI_sylbid)
   from S7 S37 have S38: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   \<not>(A \<ca> B \<lsq> \<two>\<cdot>A) \<longrightarrow> 
   A \<ca> B \<lsq> \<two>\<cdot>B" by (rule MMI_sylbird)
   from S38 have S39: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   A \<ca> B \<lsq> \<two>\<cdot>A \<or> A \<ca> B \<lsq> \<two>\<cdot>B" by (rule MMI_orrd)
   have S40: "\<two> \<in> \<real>" by (rule MMI_2re)
   have S41: "\<zero> \<ls> \<two>" by (rule MMI_2pos)
   have S42: "(A \<ca> B \<in> \<real> \<and> \<two> \<in> \<real> \<and> A \<in> \<real>) \<and> \<zero> \<ls> \<two> \<longrightarrow> 
   (A \<ca> B)\<cdiv>\<two> \<lsq> A \<longleftrightarrow> 
   A \<ca> B \<lsq> \<two>\<cdot>A" by (rule MMI_ledivmult)
   from S41 S42 have S43: "A \<ca> B \<in> \<real> \<and> \<two> \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   (A \<ca> B)\<cdiv>\<two> \<lsq> A \<longleftrightarrow> 
   A \<ca> B \<lsq> \<two>\<cdot>A" by (rule MMI_mpan2)
   from S40 S43 have S44: "A \<ca> B \<in> \<real> \<and> A \<in> \<real> \<longrightarrow> 
   (A \<ca> B)\<cdiv>\<two> \<lsq> A \<longleftrightarrow> 
   A \<ca> B \<lsq> \<two>\<cdot>A" by (rule MMI_mp3an2)
   from S6 have S45: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<ca> B \<in> \<real>" .
   from S9 have S46: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<in> \<real>" .
   from S44 S45 S46 have S47: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (A \<ca> B)\<cdiv>\<two> \<lsq> A \<longleftrightarrow> 
   A \<ca> B \<lsq> \<two>\<cdot>A" by (rule MMI_sylanc)
   have S48: "\<two> \<in> \<real>" by (rule MMI_2re)
   have S49: "\<zero> \<ls> \<two>" by (rule MMI_2pos)
   have S50: "(A \<ca> B \<in> \<real> \<and> \<two> \<in> \<real> \<and> B \<in> \<real>) \<and> \<zero> \<ls> \<two> \<longrightarrow> 
   (A \<ca> B)\<cdiv>\<two> \<lsq> B \<longleftrightarrow> 
   A \<ca> B \<lsq> \<two>\<cdot>B" by (rule MMI_ledivmult)
   from S49 S50 have S51: "A \<ca> B \<in> \<real> \<and> \<two> \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (A \<ca> B)\<cdiv>\<two> \<lsq> B \<longleftrightarrow> 
   A \<ca> B \<lsq> \<two>\<cdot>B" by (rule MMI_mpan2)
   from S48 S51 have S52: "A \<ca> B \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (A \<ca> B)\<cdiv>\<two> \<lsq> B \<longleftrightarrow> 
   A \<ca> B \<lsq> \<two>\<cdot>B" by (rule MMI_mp3an2)
   from S6 have S53: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> A \<ca> B \<in> \<real>" .
   from S10 have S54: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> B \<in> \<real>" .
   from S52 S53 S54 have S55: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (A \<ca> B)\<cdiv>\<two> \<lsq> B \<longleftrightarrow> 
   A \<ca> B \<lsq> \<two>\<cdot>B" by (rule MMI_sylanc)
   from S47 S55 have S56: "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (A \<ca> B)\<cdiv>\<two> \<lsq> A \<or> (A \<ca> B)\<cdiv>\<two> \<lsq> B \<longleftrightarrow> 
   A \<ca> B \<lsq> \<two>\<cdot>A \<or> A \<ca> B \<lsq> \<two>\<cdot>B" by (rule MMI_orbi12d)
   from S39 S56 show "A \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
   (A \<ca> B)\<cdiv>\<two> \<lsq> A \<or> (A \<ca> B)\<cdiv>\<two> \<lsq> B" by (rule MMI_mpbird)
qed

lemma (in MMIsar0) MMI_lbreu: 
   shows "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
   (\<exists>!x. x\<in>S\<and>(\<forall>y\<in>S. x \<lsq> y))"
proof -
  { fix x w
    have S1: "y = w \<longrightarrow> 
      x \<lsq> y \<longleftrightarrow> x \<lsq> w" by (rule MMI_breq2)
    from S1 have S2: "w \<in> S \<longrightarrow> 
      (\<forall>y\<in>S. x \<lsq> y) \<longrightarrow> x \<lsq> w" by auto (*rule MMI_rcla4v*)
    have S3: "y = x \<longrightarrow> 
      w \<lsq> y \<longleftrightarrow> w \<lsq> x" by (rule MMI_breq2)
    from S3 have S4: "x \<in> S \<longrightarrow> 
      (\<forall>y\<in>S. w \<lsq> y) \<longrightarrow> w \<lsq> x" by auto (*rule MMI_rcla4v*)
    from S2 S4 have S5: "x \<in> S \<and> w \<in> S \<longrightarrow> 
      (\<forall>y\<in>S. x \<lsq> y) \<and> (\<forall>y\<in>S. w \<lsq> y) \<longrightarrow> x \<lsq> w \<and> w \<lsq> x" 
      by (rule MMI_im2anan9r)
    have S6: "S \<subseteq>\<real> \<longrightarrow> 
      x \<in> S \<longrightarrow> x \<in> \<real>" by (rule MMI_ssel)
    have S7: "S \<subseteq>\<real> \<longrightarrow> 
      w \<in> S \<longrightarrow> w \<in> \<real>" by (rule MMI_ssel)
    from S6 S7 have S8: "S \<subseteq>\<real> \<longrightarrow> 
      x \<in> S \<and> w \<in> S \<longrightarrow> 
      x \<in> \<real> \<and> w \<in> \<real>" by (rule MMI_anim12d)
    from S8 have S9: "(x \<in> S \<and> w \<in> S) \<and> S \<subseteq>\<real> \<longrightarrow> 
      x \<in> \<real> \<and> w \<in> \<real>" by (rule MMI_impcom)
    have S10: "x \<in> \<real> \<and> w \<in> \<real> \<longrightarrow> 
      x = w \<longleftrightarrow> x \<lsq> w \<and> w \<lsq> x" by (rule MMI_letri3t)
    from S9 S10 have S11: "(x \<in> S \<and> w \<in> S) \<and> S \<subseteq>\<real> \<longrightarrow> 
      x = w \<longleftrightarrow> x \<lsq> w \<and> w \<lsq> x" by (rule MMI_syl)
    from S11 have S12: "(x \<in> S \<and> w \<in> S) \<and> S \<subseteq>\<real> \<longrightarrow> 
      x \<lsq> w \<and> w \<lsq> x \<longrightarrow> x = w" by (rule MMI_biimprd)
    from S12 have S13: "x \<in> S \<and> w \<in> S \<longrightarrow> 
      S \<subseteq>\<real> \<longrightarrow> 
      x \<lsq> w \<and> w \<lsq> x \<longrightarrow> x = w" by (rule MMI_ex)
    from S13 have S14: "x \<in> S \<and> w \<in> S \<longrightarrow> 
      x \<lsq> w \<and> w \<lsq> x \<longrightarrow> 
      S \<subseteq>\<real> \<longrightarrow> x = w" by (rule MMI_com23)
    from S5 S14 have S15: "x \<in> S \<and> w \<in> S \<longrightarrow> 
      (\<forall>y\<in>S. x \<lsq> y) \<and> (\<forall>y\<in>S. w \<lsq> y) \<longrightarrow> 
      S \<subseteq>\<real> \<longrightarrow> x = w" by (rule MMI_syld)
    from S15 have "S \<subseteq>\<real> \<longrightarrow> 
      x \<in> S \<and> w \<in> S \<longrightarrow> 
      (\<forall>y\<in>S. x \<lsq> y) \<and> (\<forall>y\<in>S. w \<lsq> y) \<longrightarrow> x = w" by (rule MMI_com3r)
  } then have S16: "\<forall>x w . S \<subseteq>\<real> \<longrightarrow> x \<in> S \<and> w \<in> S \<longrightarrow> 
      (\<forall>y\<in>S. x \<lsq> y) \<and> (\<forall>y\<in>S. w \<lsq> y) \<longrightarrow> x = w" by auto
  from S16 have S17: "S \<subseteq>\<real> \<longrightarrow> 
    (\<forall>x\<in>S. \<forall>w\<in>S. (\<forall>y\<in>S. x \<lsq> y) \<and> (\<forall>y\<in>S. w \<lsq> y) \<longrightarrow> x = w)" 
    by auto (*rule MMI_r19_21aivv*)
  from S17 have S18: "( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<and> S \<subseteq>\<real> \<longrightarrow> 
    ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<and> (\<forall>x\<in>S. \<forall>w\<in>S. (\<forall>y\<in>S. x \<lsq> y) \<and> (\<forall>y\<in>S. w \<lsq> y) \<longrightarrow> x = w)" 
    by (rule MMI_anim2i)
  from S18 have S19: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
    ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<and> (\<forall>x\<in>S. \<forall>w\<in>S. (\<forall>y\<in>S. x \<lsq> y) \<and> (\<forall>y\<in>S. w \<lsq> y) \<longrightarrow> x = w)" 
    by (rule MMI_ancoms)
  have S20: "\<forall>x. x = w \<longrightarrow>  x \<lsq> y \<longleftrightarrow> w \<lsq> y" by auto (*rule MMI_breq1*)
  from S20 have S21: "\<forall> x. x = w \<longrightarrow> 
    (\<forall>y\<in>S. x \<lsq> y) \<longleftrightarrow> (\<forall>y\<in>S. w \<lsq> y)" by auto (*rule MMI_ralbidv*)
  from S21 have S22: "(\<exists>!x. x\<in>S\<and>(\<forall>y\<in>S. x \<lsq> y)) \<longleftrightarrow> 
    ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<and> (\<forall>x\<in>S. \<forall>w\<in>S. (\<forall>y\<in>S. x \<lsq> y) \<and> (\<forall>y\<in>S. w \<lsq> y) \<longrightarrow> x = w)" 
     by auto  (*rule MMI_reu4*)
   from S19 S22 show "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
     (\<exists>!x. x\<in>S\<and>(\<forall>y\<in>S. x \<lsq> y))" by auto (*rule MMI_sylibr*)
 qed

lemma (in MMIsar0) MMI_lbcl: 
   shows "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
   \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> S"
proof -
   have S1: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
   (\<exists>!x. x\<in>S\<and>(\<forall>y\<in>S. x \<lsq> y))" by (rule MMI_lbreu)
   have S2: "(\<exists>!x. x\<in>S\<and>(\<forall>y\<in>S. x \<lsq> y)) \<longrightarrow> 
   \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }" by (rule MMI_reucl2)
   have S3: "{x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<subseteq>S" by (rule MMI_ssrab2)
   from S3 have S4: "\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
   \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> S" by (rule MMI_sseli)
   from S1 S2 S4 show "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
   \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> S" by (rule MMI_3syl)
qed

lemma (in MMIsar0) MMI_lble: 
   shows "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<and> A \<in> S \<longrightarrow> 
   (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> A"
proof -
   have S1: "(\<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
   (\<forall>y. \<forall>y\<in>S. x \<lsq> y)" by (rule MMI_hbra1)
   { fix w
     have S2: "w \<in> S \<longrightarrow> (\<forall>y. w \<in> S)" by (rule MMI_ax_17)
     from S1 S2 have S3: "w \<in> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
       (\<forall>y. w \<in> {x \<in> S. \<forall>y\<in>S. x \<lsq> y })" by auto (*rule MMI_hbrab*)
     from S3 have "w \<in> \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
       (\<forall>y. w \<in> \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y })" by (rule MMI_hbuni)
   } then have S4: "\<forall>w. w \<in> \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
       (\<forall>y. w \<in> \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y })" by simp
       (*have S5: "w \<in> <_ \<longrightarrow> (\<forall>y. w \<in> <_)" by (rule MMI_ax_17)
       have S6: "w \<in> A \<longrightarrow> (\<forall>y. w \<in> A)" by (rule MMI_ax_17) *)
   have S7: "(\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> A \<longrightarrow> 
     (\<forall>y. (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> A)" by auto
   have S8: "y = A \<longrightarrow> 
     (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> y \<longleftrightarrow> 
     (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> A" by (rule MMI_breq2)
   from S7 S8 have S9: "A \<in> S \<longrightarrow> 
     (\<forall>y\<in>S. (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> y) \<longrightarrow> 
     (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> A" by auto (*rule MMI_rcla4*)
   from S9 have S10: "A \<in> S \<and> (\<forall>y\<in>S. (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> y) \<longrightarrow> 
     (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> A" by (rule MMI_imp)
   have S11: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
     (\<exists>!x. x\<in>S\<and>(\<forall>y\<in>S. x \<lsq> y))" by (rule MMI_lbreu)
   have S12: "x = w \<longrightarrow> 
     x \<lsq> y \<longleftrightarrow> w \<lsq> y" by (rule MMI_breq1)
   from S12 have S13: "x = w \<longrightarrow> 
     (\<forall>y\<in>S. x \<lsq> y) \<longleftrightarrow> (\<forall>y\<in>S. w \<lsq> y)" by auto (*rule MMI_ralbidv*)
   from S13 have S14: "(\<exists>!x. x\<in>S\<and>(\<forall>y\<in>S. x \<lsq> y)) \<longleftrightarrow> 
     (\<exists>!w. w\<in>S\<and>(\<forall>y\<in>S. w \<lsq> y))" by auto (*rule MMI_cbvreuv*)
   from S11 S14 have S15: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
     (\<exists>!w. w\<in>S\<and>(\<forall>y\<in>S. w \<lsq> y))" by (rule MMI_sylib)
   { fix w x
     have S16: "w = x \<longrightarrow> 
       w \<lsq> y \<longleftrightarrow> x \<lsq> y" by (rule MMI_breq1)
     from S16 have "w = x \<longrightarrow> 
       (\<forall>y\<in>S. w \<lsq> y) \<longleftrightarrow> (\<forall>y\<in>S. x \<lsq> y)" by auto (*rule MMI_ralbidv*)
   } then have S17: "\<forall>w x. w = x \<longrightarrow> 
       (\<forall>y\<in>S. w \<lsq> y) \<longleftrightarrow> (\<forall>y\<in>S. x \<lsq> y)" by simp
   from S4 have S18: "\<forall> w. w \<in> \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
   (\<forall>y. w \<in> \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y })" .
   from S18 have S19: "\<forall>w. w = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
   (\<forall>y. w = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y })" by auto (*rule MMI_hbeleq*)
   { fix w
     have S20: "w = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
       w \<lsq> y \<longleftrightarrow> 
       (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> y" by (rule MMI_breq1)
     from S19 S20 have "w = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
       (\<forall>y\<in>S. w \<lsq> y) \<longleftrightarrow> 
       (\<forall>y\<in>S. (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> y)" by auto (*rule MMI_ralbid*)
   } then have S21: "\<forall> w. w = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
       (\<forall>y\<in>S. w \<lsq> y) \<longleftrightarrow> 
       (\<forall>y\<in>S. (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> y)" by simp
   from S17 S21 have S22: "(\<exists>!w. w\<in>S\<and>(\<forall>y\<in>S. w \<lsq> y)) \<longrightarrow> 
   (\<forall>y\<in>S. (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> y)" by (rule MMI_reuuni3)
   from S15 S22 have S23: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
   (\<forall>y\<in>S. (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> y)" by (rule MMI_syl)
   from S10 S23 have S24: "A \<in> S \<and> S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
   (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> A" by (rule MMI_sylan2)
   from S24 have S25: "A \<in> S \<and> S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
   (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> A" by (rule MMI_3impb)
   from S25 show "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<and> A \<in> S \<longrightarrow> 
   (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> A" by (rule MMI_3coml)
qed

(************* proven by hand **********************)

lemma (in MMIsar0) MMI_df_sup: shows
  "Sup(B,A,\<cltrrset>) = \<Union> {x \<in> A. (\<forall>y\<in>B. \<not>(x\<ls>y) ) \<and> 
  (\<forall>y\<in>A. y\<ls>x  \<longrightarrow> (\<exists>z\<in>B. y\<ls>z))}"
  using Sup_def cltrr_def by simp

(** not really in the Metamath, but needed **)

lemma (in MMIsar0) MMI_df_inf: shows
  "Sup(B,A,converse(\<cltrrset>)) = \<Union> {x \<in> A. (\<forall>y\<in>B. \<not>(x > y) ) \<and> 
  (\<forall>y\<in>A. y > x  \<longrightarrow> (\<exists>z\<in>B. y > z))}"
  using Sup_def convcltrr_def by simp

(********* 579 ******************************)

lemma (in MMIsar0) MMI_lbinfm: 
   shows "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
    Sup(S,\<real>,converse(\<cltrrset>))  = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }"
proof -
  { fix z
    have S1: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<and> z \<in> S \<longrightarrow> 
      (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> z" by (rule MMI_lble)
    from S1 have S2: "(S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y)) \<and> z \<in> S \<longrightarrow> 
      (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> z" by (rule MMI_3expa)
    have S3: "\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> \<real> \<and> z \<in> \<real> \<longrightarrow> 
      (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> z \<longleftrightarrow> 
      \<not>(z \<ls> (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }))" by (rule MMI_lenltt)
    have S4: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
      \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> S" by (rule MMI_lbcl)
    have S5: "S \<subseteq>\<real> \<and> \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> S \<longrightarrow> 
      \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> \<real>" by (rule MMI_ssel2)
    from S4 S5 have S6: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
      \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> \<real>" by (rule MMI_syldan)
    from S6 have S7: "(S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y)) \<and> z \<in> S \<longrightarrow> 
      \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> \<real>" by (rule MMI_adantr)
    have S8: "S \<subseteq>\<real> \<and> z \<in> S \<longrightarrow> z \<in> \<real>" by (rule MMI_ssel2)
    from S8 have S9: "(S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y)) \<and> z \<in> S \<longrightarrow> z \<in> \<real>" 
      by (rule MMI_adantlr)
    from S3 S7 S9 have S10: "(S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y)) \<and> z \<in> S \<longrightarrow> 
      (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> z \<longleftrightarrow> 
      \<not>(z \<ls> (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }))" by (rule MMI_sylanc)
    from S2 S10 have S11: "(S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y)) \<and> z \<in> S \<longrightarrow> 
      \<not>(z \<ls> (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }))" by (rule MMI_mpbid)
    have S12: "\<real> = \<real>" by (rule MMI_reex)
    from S12 have S13: "S \<subseteq>\<real> \<longrightarrow> S = S" by (rule MMI_ssex)
    have S14: "S = S \<longrightarrow> 
      {x \<in> S. \<forall>y\<in>S. x \<lsq> y } = {x \<in> S. \<forall>y\<in>S. x \<lsq> y }" by auto (*rule MMI_rabexg*)
    from S13 S14 have S15: "S \<subseteq>\<real> \<longrightarrow> 
      {x \<in> S. \<forall>y\<in>S. x \<lsq> y } = {x \<in> S. \<forall>y\<in>S. x \<lsq> y }" by (rule MMI_syl)
    have S16: "{x \<in> S. \<forall>y\<in>S. x \<lsq> y } = {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
      \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }" 
      by auto(*rule MMI_uniexg*)
      (*have S17: "z = z" by simp;*) (*rule MMI_visset*)
    have S18: "\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<and> z = z \<longrightarrow> 
      (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z \<longleftrightarrow> 
      z \<ls> (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y })" by (rule MMI_brcnvg)
    from S18 have S19: "\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> V \<longrightarrow> 
      (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z \<longleftrightarrow> 
      z \<ls> (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y })" by auto (*rule MMI_mpan2*)
    from S15 S16 S19 have S20: "S \<subseteq>\<real> \<longrightarrow> 
      (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z \<longleftrightarrow> 
      z \<ls> (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y })" 
      using cltrr_def convcltrr_def converse_iff by auto(*rule MMI_3syl*)
    from S20 have S21: "S \<subseteq>\<real> \<longrightarrow> 
      \<not>((\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z) \<longleftrightarrow> 
      \<not>(z \<ls> (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }))" by (rule MMI_negbid)
    from S21 have S22: "(S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y)) \<and> z \<in> S \<longrightarrow> 
      \<not>((\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z) \<longleftrightarrow> 
      \<not>(z \<ls> (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }))" by (rule MMI_ad2antrr)
    from S11 S22 have "(S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y)) \<and> z \<in> S \<longrightarrow> 
      \<not>((\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z)" by (rule MMI_mpbird)
    } then have S23: "\<forall>z. (S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y)) \<and> z \<in> S \<longrightarrow> 
	\<not>((\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z)" by simp
     from S23 have S24: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
       (\<forall>z\<in>S. \<not>((\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z))" by (rule MMI_r19_21aiva)
   have S25: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
   \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> S" by (rule MMI_lbcl)
   { fix z
     from S25 have S26: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
       z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> 
       \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> S" by (rule MMI_a1d)
     from S26 have S27: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
       z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> 
       \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> S \<and> z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y })" 
       by (rule MMI_ancrd)
     have S28: "w = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow>  z > w \<longleftrightarrow> 
       z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y })" by auto (*rule MMI_breq2*)
     from S28 have S29: 
       "\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> S \<and> z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> ( \<exists>w\<in>S. z > w)" 
       by auto (*rule MMI_rcla4ev*)
     from S27 S29 have S30: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
       z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> ( \<exists>w\<in>S. z > w)" by (rule MMI_syl6)
     from S30 have "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
       z \<in> \<real> \<longrightarrow>  z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> ( \<exists>w\<in>S. z > w)" 
       by (rule MMI_a1d)
   } then have S31: "\<forall> z. S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
       z \<in> \<real> \<longrightarrow>  z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> ( \<exists>w\<in>S. z > w)" by simp
       (*{ fix v
       { fix z*)
   from S31 have S32: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
     (\<forall>z\<in>\<real>. z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> ( \<exists>w\<in>S. z > w))" 
     by (rule MMI_r19_21aiv)
   from S24 S32 have S33: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
     (\<forall>z\<in>S. \<not>((\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z)) \<and> (\<forall>z\<in>\<real>. z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> 
     ( \<exists>w\<in>S. z > w))" by (rule MMI_jca)
   { fix v
     { fix z 
       have S34: "v = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow>  v > z \<longleftrightarrow>  
	 (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z" by auto (*rule MMI_breq1*)
       from S34 have "v = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
	 \<not>(v > z) \<longleftrightarrow> 
	 \<not>((\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z)" by (rule MMI_negbid)
     } then have S35: "\<forall> z. v = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
	 \<not>(v > z) \<longleftrightarrow>  \<not>((\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z)" by simp
     from S35 have S36: "v = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
       (\<forall>z\<in>S. \<not>(v > z)) \<longleftrightarrow> 
       (\<forall>z\<in>S. \<not>((\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z))" by (rule MMI_ralbidv)
     { fix z
       have S37: "v = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
	 z > v \<longleftrightarrow>   z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y })" 
	 by auto (*rule MMI_breq2*)
       from S37 have S38: "v = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
	 (z > v \<longrightarrow> ( \<exists>w\<in>S. z > w)) \<longleftrightarrow> 
	 (z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> ( \<exists>w\<in>S. z > w))" 
	 by (rule MMI_imbi1d)
     } then have S38: "\<forall>z. v = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
	 (z > v \<longrightarrow> ( \<exists>w\<in>S. z > w)) \<longleftrightarrow> 
	 (z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> ( \<exists>w\<in>S. z > w))" by simp
     from S38 have S39: "v = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
       (\<forall>z\<in>\<real>. z > v \<longrightarrow> ( \<exists>w\<in>S. z > w)) \<longleftrightarrow> 
       (\<forall>z\<in>\<real>. z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> ( \<exists>w\<in>S. z > w))" 
       by auto (*rule MMI_ralbidv*)
     from S36 S39 have "v = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
       (\<forall>z\<in>S. \<not>(v > z)) \<and> (\<forall>z\<in>\<real>. z > v \<longrightarrow> ( \<exists>w\<in>S. z > w)) \<longleftrightarrow> 
       (\<forall>z\<in>S. \<not>((\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z)) \<and> 
       (\<forall>z\<in>\<real>. z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> ( \<exists>w\<in>S. z > w))" 
       by (rule MMI_anbi12d)
   } then have S40: "\<forall>v. v = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
       (\<forall>z\<in>S. \<not>(v > z)) \<and> (\<forall>z\<in>\<real>. z > v \<longrightarrow> ( \<exists>w\<in>S. z > w)) \<longleftrightarrow> 
       (\<forall>z\<in>S. \<not>((\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z)) \<and> 
       (\<forall>z\<in>\<real>. z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> ( \<exists>w\<in>S. z > w))" by simp
   from S40 have S41: "\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> \<real> \<and> 
     (\<exists>!v. v\<in>\<real>\<and>(\<forall>z\<in>S. \<not>(v > z)) \<and> (\<forall>z\<in>\<real>. z > v \<longrightarrow> ( \<exists>w\<in>S. z > w))) \<longrightarrow> 
     (\<forall>z\<in>S. \<not>((\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z)) \<and> 
     (\<forall>z\<in>\<real>. z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> 
     ( \<exists>w\<in>S. z > w)) \<longleftrightarrow> 
     \<Union> {v \<in> \<real>. (\<forall>z\<in>S. \<not>(v > z)) \<and> (\<forall>z\<in>\<real>. z > v \<longrightarrow> ( \<exists>w\<in>S. z > w)) } = 
     \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }" 
     by (rule MMI_reuuni2)
   have S42: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
     \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> S" by (rule MMI_lbcl)
   have S43: "S \<subseteq>\<real> \<longrightarrow> 
     \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> S \<longrightarrow> 
     \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> \<real>" by (rule MMI_ssel)
   from S43 have S44: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
     \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> S \<longrightarrow> 
     \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> \<real>" by (rule MMI_adantr)
   from S42 S44 have S45: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
   \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> \<real>" by (rule MMI_mpd)
   from S40 have S46: "\<forall>v. v = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<longrightarrow> 
   (\<forall>z\<in>S. \<not>(v > z)) \<and> (\<forall>z\<in>\<real>. z > v \<longrightarrow> ( \<exists>w\<in>S. z > w)) \<longleftrightarrow> 
   (\<forall>z\<in>S. \<not>((\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z)) \<and> 
     (\<forall>z\<in>\<real>. z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> ( \<exists>w\<in>S. z > w))" .
   from S46 have S47: 
     "\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> \<real> \<and> 
     (\<forall>z\<in>S. \<not>((\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z)) \<and> 
     (\<forall>z\<in>\<real>. z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> ( \<exists>w\<in>S. z > w)) \<longrightarrow> 
   ( \<exists>v\<in>\<real>. (\<forall>z\<in>S. \<not>(v > z)) \<and> (\<forall>z\<in>\<real>. z > v \<longrightarrow> ( \<exists>w\<in>S. z > w)))" 
     by (rule MMI_rcla4ev)
   from S45  have S48: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
   \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> \<real>" by auto
   from S33 have S49: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
   (\<forall>z\<in>S. \<not>((\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z)) \<and> 
     (\<forall>z\<in>\<real>. z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> ( \<exists>w\<in>S. z > w))" by auto
   from S47 S48 S49 have S50: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
   ( \<exists>v\<in>\<real>. (\<forall>z\<in>S. \<not>(v > z)) \<and> (\<forall>z\<in>\<real>. z > v \<longrightarrow> ( \<exists>w\<in>S. z > w)))" 
     by (rule MMI_sylanc)
   have S51: "\<cltrrset> Orders \<real>" by (rule MMI_ltso)
   have S52: "\<cltrrset> Orders \<real> \<longleftrightarrow> converse(\<cltrrset>) Orders \<real>" 
     by (rule MMI_cnvso)
   from S51 S52 have S53: "converse(\<cltrrset>) Orders \<real>" by (rule MMI_mpbi)
   from S53 have S54: "( \<exists>v\<in>\<real>. (\<forall>z\<in>S. \<not>(v > z)) \<and> (\<forall>z\<in>\<real>. z > v \<longrightarrow> 
     ( \<exists>w\<in>S. z > w))) \<longrightarrow> (\<exists>!v. v\<in>\<real>\<and>(\<forall>z\<in>S. \<not>(v > z)) \<and> (\<forall>z\<in>\<real>. z > v \<longrightarrow> 
     ( \<exists>w\<in>S. z > w)))" 
     by (rule MMI_infeu)
   from S50 S54 have S55: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
   (\<exists>!v. v\<in>\<real>\<and>(\<forall>z\<in>S. \<not>(v > z)) \<and> (\<forall>z\<in>\<real>. z > v \<longrightarrow> ( \<exists>w\<in>S. z > w)))" 
     by (rule MMI_syl)
   from S41 S45 S55 have S56: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
   (\<forall>z\<in>S. \<not>((\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) > z)) \<and> 
     (\<forall>z\<in>\<real>. z > (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<longrightarrow> ( \<exists>w\<in>S. z > w)) \<longleftrightarrow> 
   \<Union> {v \<in> \<real>. (\<forall>z\<in>S. \<not>(v > z)) \<and> (\<forall>z\<in>\<real>. z > v \<longrightarrow> ( \<exists>w\<in>S. z > w)) } = 
     \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }" 
     by (rule MMI_sylanc)
   from S33 S56 have S57: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
     \<Union> {v \<in> \<real>. (\<forall>z\<in>S. \<not>(v > z)) \<and> (\<forall>z\<in>\<real>. z > v \<longrightarrow> ( \<exists>w\<in>S. z > w)) } = 
     \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }" 
     by (rule MMI_mpbid)
   have S58: 
     "Sup(S,\<real>,converse(\<cltrrset>))  = 
     \<Union> {v \<in> \<real>. (\<forall>z\<in>S. \<not>(v > z)) \<and> (\<forall>z\<in>\<real>. z > v \<longrightarrow> ( \<exists>w\<in>S. z > w)) }" 
     by (rule MMI_df_inf)
   from S57 S58 show "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
    Sup(S,\<real>,converse(\<cltrrset>))  = 
     \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }" by (rule MMI_syl5eq)
qed

(******** 580-581*******************************)

lemma (in MMIsar0) MMI_lbinfmcl: 
  shows 
  "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow>  
  Sup(S,\<real>,converse(\<cltrrset>)) \<in> S"
proof -
  have S1: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
    Sup(S,\<real>,converse(\<cltrrset>))  = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }" 
    by (rule MMI_lbinfm)
  have S2: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
    \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y } \<in> S" by (rule MMI_lbcl)
  from S1 S2 show 
    "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow>  Sup(S,\<real>,converse(\<cltrrset>))  \<in> S"
    by (rule MMI_eqeltrd)
qed

lemma (in MMIsar0) MMI_lbinfmle: 
   shows 
  "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<and> A \<in> S \<longrightarrow>  
  Sup(S,\<real>,converse(\<cltrrset>))  \<lsq> A"
proof -
  have S1: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<longrightarrow> 
    Sup(S,\<real>,converse(\<cltrrset>))  = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }" 
    by (rule MMI_lbinfm)
  from S1 have S2: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<and> A \<in> S \<longrightarrow> 
    Sup(S,\<real>,converse(\<cltrrset>)) = \<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }" 
    by (rule MMI_3adant3)
  have S3: "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<and> A \<in> S \<longrightarrow> 
    (\<Union> {x \<in> S. \<forall>y\<in>S. x \<lsq> y }) \<lsq> A" by (rule MMI_lble)
  from S2 S3 show 
    "S \<subseteq>\<real> \<and> ( \<exists>x\<in>S. \<forall>y\<in>S. x \<lsq> y) \<and> A \<in> S \<longrightarrow>  
    Sup(S,\<real>,converse(\<cltrrset>))  \<lsq> A" 
    by (rule MMI_eqbrtrd)
qed

(******** 582 ***********************************)

lemma (in MMIsar0) MMI_sup2: 
   shows "A \<subseteq>\<real> \<and> A \<noteq> 0 \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x \<or> y = x) \<longrightarrow> 
   ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z)))"
proof -
  { fix x
    have S1: "x \<in> \<real> \<longrightarrow> x \<ca> \<one> \<in> \<real>" by (rule MMI_peano2re)
    from S1 have S2: "x \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> x \<or> y = x) \<longrightarrow> x \<ca> \<one> \<in> \<real>" by (rule MMI_adantr)
    from S2 have S3: "A \<subseteq>\<real> \<longrightarrow> 
      x \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> x \<or> y = x) \<longrightarrow> x \<ca> \<one> \<in> \<real>" by (rule MMI_a1i)
    { fix y
      have S4: "A \<subseteq>\<real> \<longrightarrow> 
	y \<in> A \<longrightarrow> y \<in> \<real>" by (rule MMI_ssel)
      have S5: "y \<in> \<real> \<and> x \<in> \<real> \<and> x \<ca> \<one> \<in> \<real> \<longrightarrow> 
	y \<ls> x \<and> x \<ls> x \<ca> \<one> \<longrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_axlttrn)
      from S5 have S6: "y \<in> \<real> \<and> x \<in> \<real> \<and> x \<ca> \<one> \<in> \<real> \<longrightarrow> 
	y \<ls> x \<and> x \<ls> x \<ca> \<one> \<longrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_3expb)
      from S1 have S7: "x \<in> \<real> \<longrightarrow> x \<ca> \<one> \<in> \<real>" .
      from S7 have S8: "x \<in> \<real> \<longrightarrow> 
	x \<in> \<real> \<and> x \<ca> \<one> \<in> \<real>" by (rule MMI_ancli)
      from S6 S8 have S9: "y \<in> \<real> \<and> x \<in> \<real> \<longrightarrow> 
	y \<ls> x \<and> x \<ls> x \<ca> \<one> \<longrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_sylan2)
      have S10: "x \<in> \<real> \<longrightarrow> x \<ls> x \<ca> \<one>" by (rule MMI_ltp1t)
      from S9 S10 have S11: "y \<in> \<real> \<and> x \<in> \<real> \<longrightarrow> 
	y \<ls> x \<and> x \<in> \<real> \<longrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_sylan2i)
      from S11 have S12: "y \<in> \<real> \<longrightarrow> 
	x \<in> \<real> \<longrightarrow> 
	y \<ls> x \<longrightarrow> 
	x \<in> \<real> \<longrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_exp4b)
      from S12 have S13: "y \<in> \<real> \<longrightarrow> 
	x \<in> \<real> \<longrightarrow> 
	x \<in> \<real> \<longrightarrow> 
	y \<ls> x \<longrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_com34)
      from S13 have S14: "y \<in> \<real> \<longrightarrow> 
	x \<in> \<real> \<longrightarrow> 
	y \<ls> x \<longrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_pm2_43d)
      from S14 have S15: "y \<in> \<real> \<and> x \<in> \<real> \<longrightarrow> 
	y \<ls> x \<longrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_imp)
      from S10 have S16: "x \<in> \<real> \<longrightarrow> x \<ls> x \<ca> \<one>" .
      have S17: "y = x \<longrightarrow> 
	y \<ls> x \<ca> \<one> \<longleftrightarrow> x \<ls> x \<ca> \<one>" by (rule MMI_breq1)
      from S17 have S18: "x \<ls> x \<ca> \<one> \<longrightarrow> 
	y = x \<longrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_biimprcd)
      from S16 S18 have S19: "x \<in> \<real> \<longrightarrow> 
	y = x \<longrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_syl)
      from S19 have S20: "y \<in> \<real> \<and> x \<in> \<real> \<longrightarrow> 
	y = x \<longrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_adantl)
      from S15 S20 have S21: "y \<in> \<real> \<and> x \<in> \<real> \<longrightarrow> 
	y \<ls> x \<or> y = x \<longrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_jaod)
      from S21 have S22: "y \<in> \<real> \<longrightarrow> 
	x \<in> \<real> \<longrightarrow> 
	y \<ls> x \<or> y = x \<longrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_ex)
      from S4 S22 have S23: "A \<subseteq>\<real> \<longrightarrow> 
	y \<in> A \<longrightarrow> 
	x \<in> \<real> \<longrightarrow> 
	y \<ls> x \<or> y = x \<longrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_syl6)
      from S23 have S24: "A \<subseteq>\<real> \<longrightarrow> 
	x \<in> \<real> \<longrightarrow> 
	y \<in> A \<longrightarrow> 
	y \<ls> x \<or> y = x \<longrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_com23)
      from S24 have S25: "A \<subseteq>\<real> \<and> x \<in> \<real> \<longrightarrow> 
	y \<in> A \<longrightarrow> 
	y \<ls> x \<or> y = x \<longrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_imp)
      from S25 have "A \<subseteq>\<real> \<and> x \<in> \<real> \<longrightarrow> 
	(y \<in> A \<longrightarrow> y \<ls> x \<or> y = x) \<longrightarrow> 
	y \<in> A \<longrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_a2d)
    } then have S26: "\<forall> y. A \<subseteq>\<real> \<and> x \<in> \<real> \<longrightarrow> 
	(y \<in> A \<longrightarrow> y \<ls> x \<or> y = x) \<longrightarrow> 
	y \<in> A \<longrightarrow> y \<ls> x \<ca> \<one>" by simp
    from S26 have S27: "A \<subseteq>\<real> \<and> x \<in> \<real> \<longrightarrow> 
      (\<forall>y. y \<in> A \<longrightarrow> y \<ls> x \<or> y = x) \<longrightarrow> 
      (\<forall>y. y \<in> A \<longrightarrow> y \<ls> x \<ca> \<one>)" by (rule MMI_19_20dv)
    have S28: "(\<forall>y\<in>A. y \<ls> x \<or> y = x) \<longleftrightarrow> 
      (\<forall>y. y \<in> A \<longrightarrow> y \<ls> x \<or> y = x)" by (rule MMI_df_ral)
    have S29: "(\<forall>y\<in>A. y \<ls> x \<ca> \<one>) \<longleftrightarrow> 
      (\<forall>y. y \<in> A \<longrightarrow> y \<ls> x \<ca> \<one>)" by (rule MMI_df_ral)
    from S27 S28 S29 have S30: "A \<subseteq>\<real> \<and> x \<in> \<real> \<longrightarrow> 
      (\<forall>y\<in>A. y \<ls> x \<or> y = x) \<longrightarrow> 
      (\<forall>y\<in>A. y \<ls> x \<ca> \<one>)" by (rule MMI_3imtr4g)
    from S30 have S31: "A \<subseteq>\<real> \<longrightarrow> 
      x \<in> \<real> \<longrightarrow> 
      (\<forall>y\<in>A. y \<ls> x \<or> y = x) \<longrightarrow> 
      (\<forall>y\<in>A. y \<ls> x \<ca> \<one>)" by (rule MMI_ex)
    from S31 have S32: "A \<subseteq>\<real> \<longrightarrow> 
      x \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> x \<or> y = x) \<longrightarrow> 
      (\<forall>y\<in>A. y \<ls> x \<ca> \<one>)" by (rule MMI_imp3a)
    from S3 S32 have S33: "A \<subseteq>\<real> \<longrightarrow> 
      x \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> x \<or> y = x) \<longrightarrow> 
      x \<ca> \<one> \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> x \<ca> \<one>)" by (rule MMI_jcad)
    have S34: "x \<ca> \<one> = x \<ca> \<one>" by auto (*rule MMI_oprex*)
    have S35: "z = x \<ca> \<one> \<longrightarrow> 
      z \<in> \<real> \<longleftrightarrow> x \<ca> \<one> \<in> \<real>" by (rule MMI_eleq1)
    have S36: "z = x \<ca> \<one> \<longrightarrow> 
      y \<ls> z \<longleftrightarrow> y \<ls> x \<ca> \<one>" by (rule MMI_breq2)
    from S36 have S37: "z = x \<ca> \<one> \<longrightarrow> 
      (\<forall>y\<in>A. y \<ls> z) \<longleftrightarrow> 
      (\<forall>y\<in>A. y \<ls> x \<ca> \<one>)" by auto (*rule MMI_ralbidv*)
    from S35 S37 have S38: "z = x \<ca> \<one> \<longrightarrow> 
      z \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> z) \<longleftrightarrow> 
      x \<ca> \<one> \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> x \<ca> \<one>)" by (rule MMI_anbi12d)
    from S34 S38 have S39: "x \<ca> \<one> \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> x \<ca> \<one>) \<longrightarrow> 
      ( \<exists>z. z \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> z))" by auto (*rule MMI_cla4ev*)
    from S33 S39 have "A \<subseteq>\<real> \<longrightarrow> 
      x \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> x \<or> y = x) \<longrightarrow> 
      ( \<exists>z. z \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> z))" by (rule MMI_syl6)
  } then have S40: "\<forall> x. A \<subseteq>\<real> \<longrightarrow> 
      x \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> x \<or> y = x) \<longrightarrow> 
      ( \<exists>z. z \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> z))" by auto
  from S40 have S41: "A \<subseteq>\<real> \<longrightarrow> 
    ( \<exists>x. x \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> x \<or> y = x)) \<longrightarrow> 
    ( \<exists>z. z \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> z))" by (rule MMI_19_23adv)
  have S42: "z = x \<longrightarrow> 
    z \<in> \<real> \<longleftrightarrow> x \<in> \<real>" by (rule MMI_eleq1)
  have S43: "z = x \<longrightarrow> 
    y \<ls> z \<longleftrightarrow> y \<ls> x" by (rule MMI_breq2)
  from S43 have S44: "z = x \<longrightarrow> 
    (\<forall>y\<in>A. y \<ls> z) \<longleftrightarrow> (\<forall>y\<in>A. y \<ls> x)" by auto (*rule MMI_ralbidv*)
  from S42 S44 have S45: "z = x \<longrightarrow> 
    z \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> z) \<longleftrightarrow> 
    x \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> x)" by (rule MMI_anbi12d)
  from S45 have S46: "( \<exists>z. z \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> z)) \<longleftrightarrow> 
    ( \<exists>x. x \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> x))" by auto (*rule MMI_cbvexv*)
  from S41 S46 have S47: "A \<subseteq>\<real> \<longrightarrow> 
    ( \<exists>x. x \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> x \<or> y = x)) \<longrightarrow> 
   ( \<exists>x. x \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> x))" by (rule MMI_syl6ib)
   have S48: "( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x \<or> y = x) \<longleftrightarrow> 
   ( \<exists>x. x \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> x \<or> y = x))" by (rule MMI_df_rex)
   have S49: "( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x) \<longleftrightarrow> 
   ( \<exists>x. x \<in> \<real> \<and> (\<forall>y\<in>A. y \<ls> x))" by (rule MMI_df_rex)
   from S47 S48 S49 have S50: "A \<subseteq>\<real> \<longrightarrow> 
   ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x \<or> y = x) \<longrightarrow> 
   ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x)" by (rule MMI_3imtr4g)
   from S50 have S51: "A \<subseteq>\<real> \<and> A \<noteq> 0 \<longrightarrow> 
   ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x \<or> y = x) \<longrightarrow> 
   ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x)" by (rule MMI_adantr)
   from S51 have S52: "(A \<subseteq>\<real> \<and> A \<noteq> 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x \<or> y = x) \<longrightarrow> 
   (A \<subseteq>\<real> \<and> A \<noteq> 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x)" by (rule MMI_imdistani)
   have S53: "A \<subseteq>\<real> \<and> A \<noteq> 0 \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x \<or> y = x) \<longleftrightarrow> 
   (A \<subseteq>\<real> \<and> A \<noteq> 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x \<or> y = x)" by (rule MMI_df_3an)
   have S54: "A \<subseteq>\<real> \<and> A \<noteq> 0 \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x) \<longleftrightarrow> 
   (A \<subseteq>\<real> \<and> A \<noteq> 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x)" by (rule MMI_df_3an)
   from S52 S53 S54 have S55: "A \<subseteq>\<real> \<and> A \<noteq> 0 \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x \<or> y = x) \<longrightarrow> 
   A \<subseteq>\<real> \<and> A \<noteq> 0 \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x)" by (rule MMI_3imtr4)
   have S56: "A \<subseteq>\<real> \<and> A \<noteq> 0 \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x) \<longrightarrow> 
   ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z)))" 
     by (rule MMI_axsup)
   from S55 S56 show "A \<subseteq>\<real> \<and> A \<noteq> 0 \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x \<or> y = x) \<longrightarrow> 
   ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z)))" 
     by (rule MMI_syl)
qed

(************* 583 *************************)

lemma (in MMIsar0) MMI_sup3: 
   shows "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
   ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z)))"
proof -
   have S1: "A \<noteq> 0 \<longleftrightarrow> \<not>(A = 0)" by (rule MMI_df_ne)
   from S1 have S2: "\<not>(A = 0) \<longleftrightarrow> A \<noteq> 0" by (rule MMI_bicomi)
   from S2 have S3: "A \<subseteq>\<real> \<longrightarrow> 
   \<not>(A = 0) \<longleftrightarrow> A \<noteq> 0" by (rule MMI_a1i)
   { fix x
     { fix y
       have S4: "A \<subseteq>\<real> \<longrightarrow> 
	 y \<in> A \<longrightarrow> y \<in> \<real>" by (rule MMI_ssel)
       have S5: "y \<in> \<real> \<and> x \<in> \<real> \<longrightarrow> 
       y \<lsq> x \<longleftrightarrow> y \<ls> x \<or> y = x" by (rule MMI_leloet)
       from S5 have S6: "x \<in> \<real> \<longrightarrow> 
	 y \<in> \<real> \<longrightarrow> 
	 y \<lsq> x \<longleftrightarrow> y \<ls> x \<or> y = x" by (rule MMI_expcom)
       from S4 S6 have S7: "A \<subseteq>\<real> \<longrightarrow> 
	 x \<in> \<real> \<longrightarrow> 
	 y \<in> A \<longrightarrow> 
	 y \<lsq> x \<longleftrightarrow> y \<ls> x \<or> y = x" by (rule MMI_syl9)
       from S7 have "(A \<subseteq>\<real> \<and> x \<in> \<real>) \<and> y \<in> A \<longrightarrow> 
	 y \<lsq> x \<longleftrightarrow> y \<ls> x \<or> y = x" by (rule MMI_imp31)
     } then have S8: "\<forall>y. (A \<subseteq>\<real> \<and> x \<in> \<real>) \<and> y \<in> A \<longrightarrow> 
	 y \<lsq> x \<longleftrightarrow> y \<ls> x \<or> y = x" by simp
     from S8 have "A \<subseteq>\<real> \<and> x \<in> \<real> \<longrightarrow> 
       (\<forall>y\<in>A. y \<lsq> x) \<longleftrightarrow> 
       (\<forall>y\<in>A. y \<ls> x \<or> y = x)" by (rule MMI_ralbidva)
   } then have S9: "\<forall>x. A \<subseteq>\<real> \<and> x \<in> \<real> \<longrightarrow> 
       (\<forall>y\<in>A. y \<lsq> x) \<longleftrightarrow> 
       (\<forall>y\<in>A. y \<ls> x \<or> y = x)" by simp
   from S9 have S10: "A \<subseteq>\<real> \<longrightarrow> 
     ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longleftrightarrow> 
     ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x \<or> y = x)" by (rule MMI_rexbidva)
   from S3 S10 have S11: "A \<subseteq>\<real> \<longrightarrow> 
     \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longleftrightarrow> 
     A \<noteq> 0 \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x \<or> y = x)" by (rule MMI_anbi12d)
   from S11 have S12: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longleftrightarrow> 
     A \<subseteq>\<real> \<and> A \<noteq> 0 \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x \<or> y = x)" by (rule MMI_pm5_32i)
   have S13: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longleftrightarrow> 
   A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)" by (rule MMI_3anass)
   have S14: "A \<subseteq>\<real> \<and> A \<noteq> 0 \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x \<or> y = x) \<longleftrightarrow> 
   A \<subseteq>\<real> \<and> A \<noteq> 0 \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x \<or> y = x)" by (rule MMI_3anass)
   from S12 S13 S14 have S15: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longleftrightarrow> 
   A \<subseteq>\<real> \<and> A \<noteq> 0 \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x \<or> y = x)" by (rule MMI_3bitr4)
   have S16: "A \<subseteq>\<real> \<and> A \<noteq> 0 \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<ls> x \<or> y = x) \<longrightarrow> 
   ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z)))" 
     by (rule MMI_sup2)
   from S15 S16 show "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
   ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z)))" 
     by (rule MMI_sylbi)
qed

(******* 584 **********************************************)

lemma (in MMIsar0) MMI_infm3lem: 
   shows "x \<in> \<real> \<longrightarrow> 
   ( \<exists>y\<in>\<real>. x = (\<cn>y))"
proof -
   have S1: "y = (\<cn>x) \<longrightarrow> (\<cn>y) = (\<cn>(\<cn>x))" by (rule MMI_negeq)
   from S1 have S2: "y = (\<cn>x) \<longrightarrow> 
   x = (\<cn>y) \<longleftrightarrow> x = (\<cn>(\<cn>x))" by (rule MMI_eqeq2d)
   from S2 have S3: "(\<cn>x) \<in> \<real> \<and> x = (\<cn>(\<cn>x)) \<longrightarrow> 
   ( \<exists>y\<in>\<real>. x = (\<cn>y))" by auto (*rule MMI_rcla4ev*)
   have S4: "x \<in> \<real> \<longrightarrow> (\<cn>x) \<in> \<real>" by (rule MMI_renegclt)
   have S5: "x \<in> \<real> \<longrightarrow> x \<in> \<complex>" by (rule MMI_recnt)
   have S6: "x \<in> \<complex> \<longrightarrow> (\<cn>(\<cn>x)) = x" by (rule MMI_negnegt)
   from S5 S6 have S7: "x \<in> \<real> \<longrightarrow> (\<cn>(\<cn>x)) = x" by (rule MMI_syl)
   from S7 have S8: "x \<in> \<real> \<longrightarrow> x = (\<cn>(\<cn>x))" by (rule MMI_eqcomd)
   from S3 S4 S8 show "x \<in> \<real> \<longrightarrow> 
   ( \<exists>y\<in>\<real>. x = (\<cn>y))" by (rule MMI_sylanc)
qed

(******** 585 ********************************************)

lemma (in MMIsar0) MMI_infm3: 
   shows "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
   ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y)))"
proof -
  { fix v
    have S1: "A \<subseteq>\<real> \<longrightarrow> 
      v \<in> A \<longrightarrow> v \<in> \<real>" by (rule MMI_ssel)
    from S1 have "A \<subseteq>\<real> \<longrightarrow> 
      v \<in> A \<longleftrightarrow> 
      v \<in> \<real> \<and> v \<in> A" by (rule MMI_pm4_71rd)
  } then have S2: "\<forall> v. A \<subseteq>\<real> \<longrightarrow>  v \<in> A \<longleftrightarrow>  v \<in> \<real> \<and> v \<in> A" by simp
  from S2 have S3: "A \<subseteq>\<real> \<longrightarrow> 
    ( \<exists>v. v \<in> A) \<longleftrightarrow> 
    ( \<exists>v. v \<in> \<real> \<and> v \<in> A)" by auto (*rule MMI_exbidv*)
   have S4: "( \<exists>v\<in>\<real>. v \<in> A) \<longleftrightarrow> 
   ( \<exists>v. v \<in> \<real> \<and> v \<in> A)" by (rule MMI_df_rex)
   { fix w
     have "w \<in> \<real> \<longrightarrow> (\<cn>w) \<in> \<real>" by (rule MMI_renegclt)
   } then have S5: "\<forall>w. w \<in> \<real> \<longrightarrow> (\<cn>w) \<in> \<real>" by simp
   { fix v
     have "v \<in> \<real> \<longrightarrow> 
       ( \<exists>w\<in>\<real>. v = (\<cn>w))" by (rule MMI_infm3lem)
   } then have S6: "\<forall> v. v \<in> \<real> \<longrightarrow> ( \<exists>w\<in>\<real>. v = (\<cn>w))" by simp
   { fix v w
     have  "v = (\<cn>w) \<longrightarrow> 
       v \<in> A \<longleftrightarrow> (\<cn>w) \<in> A" by (rule MMI_eleq1)
   } then have S7: "\<forall>v w. v = (\<cn>w) \<longrightarrow> v \<in> A \<longleftrightarrow> (\<cn>w) \<in> A"
     by simp
   from S5 S6 S7 have S8: "( \<exists>v\<in>\<real>. v \<in> A) \<longleftrightarrow> 
   ( \<exists>w\<in>\<real>. (\<cn>w) \<in> A)" by (rule MMI_rexxfr)
   from S4 S8 have S9: "( \<exists>v. v \<in> \<real> \<and> v \<in> A) \<longleftrightarrow> 
   ( \<exists>w\<in>\<real>. (\<cn>w) \<in> A)" by (rule MMI_bitr3)
   from S3 S9 have S10: "A \<subseteq>\<real> \<longrightarrow> 
   ( \<exists>v. v \<in> A) \<longleftrightarrow> 
   ( \<exists>w\<in>\<real>. (\<cn>w) \<in> A)" by (rule MMI_syl6bb)
   have S11: "\<not>(A = 0) \<longleftrightarrow> ( \<exists>v. v \<in> A)" by (rule MMI_n0)
   have S12: "\<not>({w \<in> \<real>. (\<cn>w) \<in> A } = 0) \<longleftrightarrow> 
   ( \<exists>w\<in>\<real>. (\<cn>w) \<in> A)" by (rule MMI_rabn0)
   from S10 S11 S12 have S13: "A \<subseteq>\<real> \<longrightarrow> 
   \<not>(A = 0) \<longleftrightarrow> 
   \<not>({w \<in> \<real>. (\<cn>w) \<in> A } = 0)" by (rule MMI_3bitr4g)
   { fix x
     { fix y
       have S14: "A \<subseteq>\<real> \<longrightarrow> 
	 y \<in> A \<longrightarrow> y \<in> \<real>" by (rule MMI_ssel)
       from S14 have S15: "A \<subseteq>\<real> \<longrightarrow> 
	 y \<in> A \<longleftrightarrow> 
	 y \<in> \<real> \<and> y \<in> A" by (rule MMI_pm4_71rd)
       from S15 have S16: "A \<subseteq>\<real> \<longrightarrow> 
	 (y \<in> A \<longrightarrow> x \<lsq> y) \<longleftrightarrow> 
	 (y \<in> \<real> \<and> y \<in> A \<longrightarrow> x \<lsq> y)" by (rule MMI_imbi1d)
       have S17: "(y \<in> \<real> \<and> y \<in> A \<longrightarrow> x \<lsq> y) \<longleftrightarrow> 
	 (y \<in> \<real> \<longrightarrow> 
	 y \<in> A \<longrightarrow> x \<lsq> y)" by (rule MMI_impexp)
       from S16 S17 have "A \<subseteq>\<real> \<longrightarrow> 
	 (y \<in> A \<longrightarrow> x \<lsq> y) \<longleftrightarrow> 
	 (y \<in> \<real> \<longrightarrow> 
	 y \<in> A \<longrightarrow> x \<lsq> y)" by (rule MMI_syl6bb)
     } then have S18: "\<forall>y. A \<subseteq>\<real> \<longrightarrow> 
	 (y \<in> A \<longrightarrow> x \<lsq> y) \<longleftrightarrow> 
	 (y \<in> \<real> \<longrightarrow> 
	 y \<in> A \<longrightarrow> x \<lsq> y)" by simp
     from S18 have S19: "A \<subseteq>\<real> \<longrightarrow> 
       (\<forall>y. y \<in> A \<longrightarrow> x \<lsq> y) \<longleftrightarrow> 
       (\<forall>y. y \<in> \<real> \<longrightarrow> 
       y \<in> A \<longrightarrow> x \<lsq> y)" by (rule MMI_albidv)
     have S20: "(\<forall>y\<in>A. x \<lsq> y) \<longleftrightarrow> 
       (\<forall>y. y \<in> A \<longrightarrow> x \<lsq> y)" by (rule MMI_df_ral)
     { fix v
       have  "v \<in> \<real> \<longrightarrow> (\<cn>v) \<in> \<real>" by (rule MMI_renegclt)
     } then have S21: "\<forall> v. v \<in> \<real> \<longrightarrow> (\<cn>v) \<in> \<real>" by simp
     { fix y
       have "y \<in> \<real> \<longrightarrow> 
	 ( \<exists>v\<in>\<real>. y = (\<cn>v))" by (rule MMI_infm3lem)
     } then have S22: "\<forall>y. y \<in> \<real> \<longrightarrow> ( \<exists>v\<in>\<real>. y = (\<cn>v))"
       by simp
     { fix y v
       have S23: "y = (\<cn>v) \<longrightarrow> 
	 y \<in> A \<longleftrightarrow> (\<cn>v) \<in> A" by (rule MMI_eleq1)   
       have S24: "y = (\<cn>v) \<longrightarrow> 
	 x \<lsq> y \<longleftrightarrow> x \<lsq> (\<cn>v)" by (rule MMI_breq2)
       from S23 S24 have "y = (\<cn>v) \<longrightarrow> 
	 (y \<in> A \<longrightarrow> x \<lsq> y) \<longleftrightarrow> 
	 ((\<cn>v) \<in> A \<longrightarrow> x \<lsq> (\<cn>v))" by (rule MMI_imbi12d)
     } then have S25: "\<forall> y v. y = (\<cn>v) \<longrightarrow> (y \<in> A \<longrightarrow> x \<lsq> y) \<longleftrightarrow> 
	 ((\<cn>v) \<in> A \<longrightarrow> x \<lsq> (\<cn>v))" by simp
     from S21 S22 S25 have S26: "(\<forall>y\<in>\<real>. y \<in> A \<longrightarrow> x \<lsq> y) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> x \<lsq> (\<cn>v))" by (rule MMI_ralxfr)
     have S27: "(\<forall>y\<in>\<real>. y \<in> A \<longrightarrow> x \<lsq> y) \<longleftrightarrow> 
       (\<forall>y. y \<in> \<real> \<longrightarrow>  y \<in> A \<longrightarrow> x \<lsq> y)" by (rule MMI_df_ral)
     from S26 S27 have S28: "(\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> x \<lsq> (\<cn>v)) \<longleftrightarrow> 
       (\<forall>y. y \<in> \<real> \<longrightarrow> 
       y \<in> A \<longrightarrow> x \<lsq> y)" by (rule MMI_bitr3)
     from S19 S20 S28 have "A \<subseteq>\<real> \<longrightarrow> 
       (\<forall>y\<in>A. x \<lsq> y) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> x \<lsq> (\<cn>v))" by auto (*rule MMI_3bitr4g*)
   } then have S29: "\<forall> x. A \<subseteq>\<real> \<longrightarrow> (\<forall>y\<in>A. x \<lsq> y) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> x \<lsq> (\<cn>v))" by simp
   from S29 have S30: "A \<subseteq>\<real> \<longrightarrow> 
     ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longleftrightarrow> 
     ( \<exists>x\<in>\<real>. \<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> x \<lsq> (\<cn>v))" 
     by (rule MMI_rexbidv)
   { fix u
     have "u \<in> \<real> \<longrightarrow> (\<cn>u) \<in> \<real>" by (rule MMI_renegclt)
   } then have S31: "\<forall> u. u \<in> \<real> \<longrightarrow> (\<cn>u) \<in> \<real>" by simp
   { fix x
     have S32: "x \<in> \<real> \<longrightarrow> ( \<exists>u\<in>\<real>. x = (\<cn>u))" by (rule MMI_infm3lem)
   } then have S32: "\<forall> x. x \<in> \<real> \<longrightarrow> ( \<exists>u\<in>\<real>. x = (\<cn>u))" by simp
   { fix x u
     have S33: "x = (\<cn>u) \<longrightarrow> 
       x \<lsq> (\<cn>v) \<longleftrightarrow> (\<cn>u) \<lsq> (\<cn>v)" by (rule MMI_breq1)
     from S33 have S34: "x = (\<cn>u) \<longrightarrow> 
       ((\<cn>v) \<in> A \<longrightarrow> x \<lsq> (\<cn>v)) \<longleftrightarrow> 
       ((\<cn>v) \<in> A \<longrightarrow> (\<cn>u) \<lsq> (\<cn>v))" by (rule MMI_imbi2d)
     from S34 have S35: "x = (\<cn>u) \<longrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> x \<lsq> (\<cn>v)) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> (\<cn>u) \<lsq> (\<cn>v))" 
       by auto (*rule MMI_ralbidv*)
   } then have S35: "\<forall>x u. x = (\<cn>u) \<longrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> x \<lsq> (\<cn>v)) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> (\<cn>u) \<lsq> (\<cn>v))" by simp
   from S31 S32 S35 have S36: 
     "( \<exists>x\<in>\<real>. \<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> x \<lsq> (\<cn>v)) \<longleftrightarrow> 
   ( \<exists>u\<in>\<real>. \<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> (\<cn>u) \<lsq> (\<cn>v))" 
     by (rule MMI_rexxfr)
   { fix u
     { fix v
       have S37: "v \<in> \<real> \<and> u \<in> \<real> \<longrightarrow> 
	 v \<lsq> u \<longleftrightarrow> (\<cn>u) \<lsq> (\<cn>v)" by (rule MMI_lenegt)
       from S37 have S38: "u \<in> \<real> \<and> v \<in> \<real> \<longrightarrow> 
	 v \<lsq> u \<longleftrightarrow> (\<cn>u) \<lsq> (\<cn>v)" by (rule MMI_ancoms)
       from S38 have S39: "u \<in> \<real> \<and> v \<in> \<real> \<longrightarrow> 
	 ((\<cn>v) \<in> A \<longrightarrow> v \<lsq> u) \<longleftrightarrow> 
	 ((\<cn>v) \<in> A \<longrightarrow> (\<cn>u) \<lsq> (\<cn>v))" by (rule MMI_imbi2d)
     } then have  S39: "\<forall> v. u \<in> \<real> \<and> v \<in> \<real> \<longrightarrow> 
	 ((\<cn>v) \<in> A \<longrightarrow> v \<lsq> u) \<longleftrightarrow> 
	 ((\<cn>v) \<in> A \<longrightarrow> (\<cn>u) \<lsq> (\<cn>v))" by simp
     from S39 have S40: "u \<in> \<real> \<longrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> v \<lsq> u) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> (\<cn>u) \<lsq> (\<cn>v))" by (rule MMI_ralbidva)
     have S41: "w = v \<longrightarrow> (\<cn>w) = (\<cn>v)" by (rule MMI_negeq)
     from S41 have S42: "w = v \<longrightarrow> 
       (\<cn>w) \<in> A \<longleftrightarrow> (\<cn>v) \<in> A" by (rule MMI_eleq1d)
     from S42 have S43: "v \<in> {w \<in> \<real>. (\<cn>w) \<in> A } \<longleftrightarrow> 
       v \<in> \<real> \<and> (\<cn>v) \<in> A" by auto (*rule MMI_elrab*)
     from S43 have S44: "(v \<in> {w \<in> \<real>. (\<cn>w) \<in> A } \<longrightarrow> v \<lsq> u) \<longleftrightarrow> 
       (v \<in> \<real> \<and> (\<cn>v) \<in> A \<longrightarrow> v \<lsq> u)" by (rule MMI_imbi1i)
     have S45: "(v \<in> \<real> \<and> (\<cn>v) \<in> A \<longrightarrow> v \<lsq> u) \<longleftrightarrow> 
       (v \<in> \<real> \<longrightarrow> 
       (\<cn>v) \<in> A \<longrightarrow> v \<lsq> u)" by (rule MMI_impexp)
     from S44 S45 have S46: "(v \<in> {w \<in> \<real>. (\<cn>w) \<in> A } \<longrightarrow> v \<lsq> u) \<longleftrightarrow> 
       (v \<in> \<real> \<longrightarrow> 
       (\<cn>v) \<in> A \<longrightarrow> v \<lsq> u)" by (rule MMI_bitr)
     from S46 have S47: "(\<forall>v. v \<in> {w \<in> \<real>. (\<cn>w) \<in> A } \<longrightarrow> v \<lsq> u) \<longleftrightarrow> 
       (\<forall>v. v \<in> \<real> \<longrightarrow> 
       (\<cn>v) \<in> A \<longrightarrow> v \<lsq> u)" by auto (*rule MMI_albii*)
     have S48: "(\<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<lsq> u) \<longleftrightarrow> 
       (\<forall>v. v \<in> {w \<in> \<real>. (\<cn>w) \<in> A } \<longrightarrow> v \<lsq> u)" by (rule MMI_df_ral)
     have S49: "(\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> v \<lsq> u) \<longleftrightarrow> 
       (\<forall>v. v \<in> \<real> \<longrightarrow> 
       (\<cn>v) \<in> A \<longrightarrow> v \<lsq> u)" by (rule MMI_df_ral)
     from S47 S48 S49 have S50: "(\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> v \<lsq> u) \<longleftrightarrow> 
       (\<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<lsq> u)" by (rule MMI_3bitr4r)
     from S40 S50 have "u \<in> \<real> \<longrightarrow> 
       (\<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<lsq> u) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> (\<cn>u) \<lsq> (\<cn>v))" by (rule MMI_syl5bbr)
   } then have S51: "\<forall> u. u \<in> \<real> \<longrightarrow> 
       (\<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<lsq> u) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> (\<cn>u) \<lsq> (\<cn>v))" by simp
   from S51 have S52: "( \<exists>u\<in>\<real>. \<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<lsq> u) \<longleftrightarrow> 
     ( \<exists>u\<in>\<real>. \<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> (\<cn>u) \<lsq> (\<cn>v))" 
     by (rule MMI_rexbiia)
   from S36 S52 have S53: "( \<exists>x\<in>\<real>. \<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> x \<lsq> (\<cn>v)) \<longleftrightarrow> 
     ( \<exists>u\<in>\<real>. \<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<lsq> u)" by (rule MMI_bitr4)
   from S30 S53 have S54: "A \<subseteq>\<real> \<longrightarrow> 
     ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longleftrightarrow> 
     ( \<exists>u\<in>\<real>. \<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<lsq> u)" by (rule MMI_syl6bb)
   from S13 S54 have S55: "A \<subseteq>\<real> \<longrightarrow> 
     \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longleftrightarrow> 
     \<not>({w \<in> \<real>. (\<cn>w) \<in> A } = 0) \<and> 
     ( \<exists>u\<in>\<real>. \<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<lsq> u)" by (rule MMI_anbi12d)
   have S56: "{w \<in> \<real>. (\<cn>w) \<in> A } \<subseteq>\<real>" by (rule MMI_ssrab2)
   have S57: "{w \<in> \<real>. (\<cn>w) \<in> A } \<subseteq>\<real> \<and> \<not>({w \<in> \<real>. (\<cn>w) \<in> A } = 0) \<and> 
     ( \<exists>u\<in>\<real>. \<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<lsq> u) \<longrightarrow> 
     ( \<exists>u\<in>\<real>. (\<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. \<not>(u \<ls> v)) \<and> (\<forall>v\<in>\<real>. v \<ls> u \<longrightarrow> 
     ( \<exists>t\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<ls> t)))" by (rule MMI_sup3)
   from S56 S57 have S58: 
     "\<not>({w \<in> \<real>. (\<cn>w) \<in> A } = 0) \<and> 
     ( \<exists>u\<in>\<real>. \<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<lsq> u) \<longrightarrow> 
     ( \<exists>u\<in>\<real>. (\<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. \<not>(u \<ls> v)) \<and> (\<forall>v\<in>\<real>. v \<ls> u \<longrightarrow> 
     ( \<exists>t\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<ls> t)))" by (rule MMI_mp3an1)
   from S55 S58 have S59: "A \<subseteq>\<real> \<longrightarrow> 
   \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
   ( \<exists>u\<in>\<real>. (\<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. \<not>(u \<ls> v)) \<and> (\<forall>v\<in>\<real>. v \<ls> u \<longrightarrow> 
   ( \<exists>t\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<ls> t)))" by (rule MMI_syl6bi)
   { fix x
     { fix y
       have S60: "A \<subseteq>\<real> \<longrightarrow> 
	 y \<in> A \<longleftrightarrow> 
	 y \<in> \<real> \<and> y \<in> A" using MMI_ssel MMI_pm4_71rd by simp
       from S60 have S61: "A \<subseteq>\<real> \<longrightarrow> 
	 (y \<in> A \<longrightarrow> \<not>(y \<ls> x)) \<longleftrightarrow> 
	 (y \<in> \<real> \<and> y \<in> A \<longrightarrow> \<not>(y \<ls> x))" by (rule MMI_imbi1d)
       have S62: "(y \<in> \<real> \<and> y \<in> A \<longrightarrow> \<not>(y \<ls> x)) \<longleftrightarrow> 
	 (y \<in> \<real> \<longrightarrow> 
	 y \<in> A \<longrightarrow> \<not>(y \<ls> x))" by (rule MMI_impexp)
       from S61 S62 have S63: "A \<subseteq>\<real> \<longrightarrow>  (y \<in> A \<longrightarrow> \<not>(y \<ls> x)) \<longleftrightarrow> 
	 (y \<in> \<real> \<longrightarrow> y \<in> A \<longrightarrow> \<not>(y \<ls> x))" by (rule MMI_syl6bb)
     } then have S63: "\<forall>y. A \<subseteq>\<real> \<longrightarrow>  (y \<in> A \<longrightarrow> \<not>(y \<ls> x)) \<longleftrightarrow> 
	 (y \<in> \<real> \<longrightarrow> y \<in> A \<longrightarrow> \<not>(y \<ls> x))" by simp
     from S63 have S64: "A \<subseteq>\<real> \<longrightarrow> 
       (\<forall>y. y \<in> A \<longrightarrow> \<not>(y \<ls> x)) \<longleftrightarrow> 
       (\<forall>y. y \<in> \<real> \<longrightarrow> 
       y \<in> A \<longrightarrow> \<not>(y \<ls> x))" by (rule MMI_albidv)
     have S65: "(\<forall>y\<in>A. \<not>(y \<ls> x)) \<longleftrightarrow> 
       (\<forall>y. y \<in> A \<longrightarrow> \<not>(y \<ls> x))" by (rule MMI_df_ral)
     { fix v
       have "v \<in> \<real> \<longrightarrow> (\<cn>v) \<in> \<real>" by (rule MMI_renegclt)
     } then have S66: "\<forall> v. v \<in> \<real> \<longrightarrow> (\<cn>v) \<in> \<real>" by simp
     { fix y
       have S67: "y \<in> \<real> \<longrightarrow>  ( \<exists>v\<in>\<real>. y = (\<cn>v))"  by (rule MMI_infm3lem)
     } then have S67: "\<forall> y. y \<in> \<real> \<longrightarrow>  ( \<exists>v\<in>\<real>. y = (\<cn>v))" by simp
     { fix y v
       have S68: "y = (\<cn>v) \<longrightarrow>  y \<in> A \<longleftrightarrow> (\<cn>v) \<in> A" by (rule MMI_eleq1)
       have S69: "y = (\<cn>v) \<longrightarrow> 
	 y \<ls> x \<longleftrightarrow> (\<cn>v) \<ls> x" by (rule MMI_breq1)
       from S69 have S70: "y = (\<cn>v) \<longrightarrow> 
	 \<not>(y \<ls> x) \<longleftrightarrow> \<not>((\<cn>v) \<ls> x)" by (rule MMI_negbid)
       from S68 S70 have "y = (\<cn>v) \<longrightarrow> 
	 (y \<in> A \<longrightarrow> \<not>(y \<ls> x)) \<longleftrightarrow> 
	 ((\<cn>v) \<in> A \<longrightarrow> \<not>((\<cn>v) \<ls> x))" by (rule MMI_imbi12d)
     } then have S71: "\<forall>y v. y = (\<cn>v) \<longrightarrow> (y \<in> A \<longrightarrow> \<not>(y \<ls> x)) \<longleftrightarrow> 
	 ((\<cn>v) \<in> A \<longrightarrow> \<not>((\<cn>v) \<ls> x))" by simp
     from S66 S67 S71 have S72: "(\<forall>y\<in>\<real>. y \<in> A \<longrightarrow> \<not>(y \<ls> x)) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> \<not>((\<cn>v) \<ls> x))" by (rule MMI_ralxfr)
     have S73: "(\<forall>y\<in>\<real>. y \<in> A \<longrightarrow> \<not>(y \<ls> x)) \<longleftrightarrow> 
       (\<forall>y. y \<in> \<real> \<longrightarrow> 
       y \<in> A \<longrightarrow> \<not>(y \<ls> x))" by (rule MMI_df_ral)
     from S72 S73 have S74: "(\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> \<not>((\<cn>v) \<ls> x)) \<longleftrightarrow> 
       (\<forall>y. y \<in> \<real> \<longrightarrow> 
       y \<in> A \<longrightarrow> \<not>(y \<ls> x))" by (rule MMI_bitr3)
     from S64 S65 S74 have S75: "A \<subseteq>\<real> \<longrightarrow> 
       (\<forall>y\<in>A. \<not>(y \<ls> x)) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> \<not>((\<cn>v) \<ls> x))" by (rule MMI_3bitr4g)
     have S76: "A \<subseteq>\<real> \<longrightarrow> 
       z \<in> A \<longrightarrow> z \<in> \<real>" by (rule MMI_ssel)
     { fix v
       from S76 have S77: "A \<subseteq>\<real> \<longrightarrow> 
	 z \<in> A \<and> z \<ls> (\<cn>v) \<longrightarrow> z \<in> \<real>" by (rule MMI_adantrd)
       from S77 have S78: "A \<subseteq>\<real> \<longrightarrow> 
	 z \<in> A \<and> z \<ls> (\<cn>v) \<longleftrightarrow> 
	 z \<in> \<real> \<and> z \<in> A \<and> z \<ls> (\<cn>v)" by (rule MMI_pm4_71rd)
       from S78 have S79: "A \<subseteq>\<real> \<longrightarrow> 
	 ( \<exists>z. z \<in> A \<and> z \<ls> (\<cn>v)) \<longleftrightarrow> 
	 ( \<exists>z. z \<in> \<real> \<and> z \<in> A \<and> z \<ls> (\<cn>v))" by auto (*rule MMI_exbidv*)
       have S80: "( \<exists>z\<in>A. z \<ls> (\<cn>v)) \<longleftrightarrow> 
	 ( \<exists>z. z \<in> A \<and> z \<ls> (\<cn>v))" by (rule MMI_df_rex)
       { fix t
	 have "t \<in> \<real> \<longrightarrow> (\<cn>t) \<in> \<real>" by (rule MMI_renegclt)
       } then have  S81: "\<forall> t. t \<in> \<real> \<longrightarrow> (\<cn>t) \<in> \<real>" by simp
       { fix z
	 have "z \<in> \<real> \<longrightarrow> ( \<exists>t\<in>\<real>. z = (\<cn>t))" by (rule MMI_infm3lem)
       } then have S82: "\<forall> z. z \<in> \<real> \<longrightarrow> ( \<exists>t\<in>\<real>. z = (\<cn>t))" by simp
       { fix z t
	 have S83: "z = (\<cn>t) \<longrightarrow> 
	   z \<in> A \<longleftrightarrow> (\<cn>t) \<in> A" by (rule MMI_eleq1)
	 have S84: "z = (\<cn>t) \<longrightarrow> 
	   z \<ls> (\<cn>v) \<longleftrightarrow> (\<cn>t) \<ls> (\<cn>v)" by (rule MMI_breq1)
	 from S83 S84 have S85: "z = (\<cn>t) \<longrightarrow> 
	   z \<in> A \<and> z \<ls> (\<cn>v) \<longleftrightarrow> 
	   (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)" by (rule MMI_anbi12d)
       } then have S85: "\<forall>z t. z = (\<cn>t) \<longrightarrow> 
	   z \<in> A \<and> z \<ls> (\<cn>v) \<longleftrightarrow> 
	   (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)" by simp
       from S81 S82 S85 have S86: "( \<exists>z\<in>\<real>. z \<in> A \<and> z \<ls> (\<cn>v)) \<longleftrightarrow> 
	 ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v))" by (rule MMI_rexxfr)
       have S87: "( \<exists>z\<in>\<real>. z \<in> A \<and> z \<ls> (\<cn>v)) \<longleftrightarrow> 
	 ( \<exists>z. z \<in> \<real> \<and> z \<in> A \<and> z \<ls> (\<cn>v))" by (rule MMI_df_rex)
       from S86 S87 have S88: "( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)) \<longleftrightarrow> 
	 ( \<exists>z. z \<in> \<real> \<and> z \<in> A \<and> z \<ls> (\<cn>v))" by (rule MMI_bitr3)
       from S79 S80 S88 have S89: "A \<subseteq>\<real> \<longrightarrow> 
	 ( \<exists>z\<in>A. z \<ls> (\<cn>v)) \<longleftrightarrow> 
	 ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v))" by (rule MMI_3bitr4g)
       from S89 have "A \<subseteq>\<real> \<longrightarrow> 
	 (x \<ls> (\<cn>v) \<longrightarrow> 
	 ( \<exists>z\<in>A. z \<ls> (\<cn>v))) \<longleftrightarrow> 
	 (x \<ls> (\<cn>v) \<longrightarrow> 
	 ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)))" by (rule MMI_imbi2d)
     } then have  S90: "\<forall> v. A \<subseteq>\<real> \<longrightarrow> 
	 (x \<ls> (\<cn>v) \<longrightarrow> 
	 ( \<exists>z\<in>A. z \<ls> (\<cn>v))) \<longleftrightarrow> 
	 (x \<ls> (\<cn>v) \<longrightarrow> 
	 ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)))" by auto
     from S90 have S91: "A \<subseteq>\<real> \<longrightarrow> 
       (\<forall>v\<in>\<real>. x \<ls> (\<cn>v) \<longrightarrow> 
       ( \<exists>z\<in>A. z \<ls> (\<cn>v))) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. x \<ls> (\<cn>v) \<longrightarrow> 
       ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)))" by (rule MMI_ralbidv)
     { fix v
       have "v \<in> \<real> \<longrightarrow> (\<cn>v) \<in> \<real>" by (rule MMI_renegclt)
     } then have S92: "\<forall> v. v \<in> \<real> \<longrightarrow> (\<cn>v) \<in> \<real>" by simp
     { fix y
       have "y \<in> \<real> \<longrightarrow>  ( \<exists>v\<in>\<real>. y = (\<cn>v))" by (rule MMI_infm3lem)
     } then have S93: "\<forall> y. y \<in> \<real> \<longrightarrow>  ( \<exists>v\<in>\<real>. y = (\<cn>v))" by simp
     { fix y v
       have S94: "y = (\<cn>v) \<longrightarrow>  x \<ls> y \<longleftrightarrow> x \<ls> (\<cn>v)" by (rule MMI_breq2)
       { fix z
	 have "y = (\<cn>v) \<longrightarrow> 
	   z \<ls> y \<longleftrightarrow> z \<ls> (\<cn>v)" by (rule MMI_breq2)
       } then have S95: "\<forall> z. y = (\<cn>v) \<longrightarrow> 
	   z \<ls> y \<longleftrightarrow> z \<ls> (\<cn>v)" by simp
       from S95 have S96: "y = (\<cn>v) \<longrightarrow> 
	 ( \<exists>z\<in>A. z \<ls> y) \<longleftrightarrow> 
	 ( \<exists>z\<in>A. z \<ls> (\<cn>v))" by (rule MMI_rexbidv)
       from S94 S96 have S97: "y = (\<cn>v) \<longrightarrow> 
	 (x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y)) \<longleftrightarrow> 
	 (x \<ls> (\<cn>v) \<longrightarrow> 
	 ( \<exists>z\<in>A. z \<ls> (\<cn>v)))" by (rule MMI_imbi12d)
     } then have S97: "\<forall> y v. y = (\<cn>v) \<longrightarrow> 
	 (x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y)) \<longleftrightarrow> 
	 (x \<ls> (\<cn>v) \<longrightarrow> 
	 ( \<exists>z\<in>A. z \<ls> (\<cn>v)))" by simp
     from S92 S93 S97 have S98: "(\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y)) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. x \<ls> (\<cn>v) \<longrightarrow> 
       ( \<exists>z\<in>A. z \<ls> (\<cn>v)))" by (rule MMI_ralxfr)
     from S91 S98 have S99: "A \<subseteq>\<real> \<longrightarrow> 
       (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y)) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. x \<ls> (\<cn>v) \<longrightarrow> 
       ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)))" by (rule MMI_syl5bb)
     from S75 S99 have S100: "A \<subseteq>\<real> \<longrightarrow> 
       (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y)) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> \<not>((\<cn>v) \<ls> x)) \<and> (\<forall>v\<in>\<real>. x \<ls> (\<cn>v) \<longrightarrow> 
       ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)))" by (rule MMI_anbi12d)
   } then have S100: "\<forall>x. A \<subseteq>\<real> \<longrightarrow> 
       (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y)) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> \<not>((\<cn>v) \<ls> x)) \<and> (\<forall>v\<in>\<real>. x \<ls> (\<cn>v) \<longrightarrow> 
       ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)))" by simp
   from S100 have S101: "A \<subseteq>\<real> \<longrightarrow> 
   ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y))) \<longleftrightarrow> 
   ( \<exists>x\<in>\<real>. (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> 
     \<not>((\<cn>v) \<ls> x)) \<and> (\<forall>v\<in>\<real>. x \<ls> (\<cn>v) \<longrightarrow> 
   ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v))))" by (rule MMI_rexbidv)
   { fix u
     have "u \<in> \<real> \<longrightarrow> (\<cn>u) \<in> \<real>" by (rule MMI_renegclt)
   } then have S102: "\<forall> u. u \<in> \<real> \<longrightarrow> (\<cn>u) \<in> \<real>" by simp
   { fix x
     have "x \<in> \<real> \<longrightarrow>  ( \<exists>u\<in>\<real>. x = (\<cn>u))" by (rule MMI_infm3lem)
   } then have S103: "\<forall> x. x \<in> \<real> \<longrightarrow>  ( \<exists>u\<in>\<real>. x = (\<cn>u))" by simp
   { fix x u
     have S104: "x = (\<cn>u) \<longrightarrow> 
       (\<cn>v) \<ls> x \<longleftrightarrow> (\<cn>v) \<ls> (\<cn>u)" by (rule MMI_breq2)
     from S104 have S105: "x = (\<cn>u) \<longrightarrow> 
       \<not>((\<cn>v) \<ls> x) \<longleftrightarrow> 
       \<not>((\<cn>v) \<ls> (\<cn>u))" by (rule MMI_negbid)
     from S105 have S106: "x = (\<cn>u) \<longrightarrow> 
       ((\<cn>v) \<in> A \<longrightarrow> \<not>((\<cn>v) \<ls> x)) \<longleftrightarrow> 
       ((\<cn>v) \<in> A \<longrightarrow> 
       \<not>((\<cn>v) \<ls> (\<cn>u)))" by (rule MMI_imbi2d)
     from S106 have S107: "x = (\<cn>u) \<longrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> \<not>((\<cn>v) \<ls> x)) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> 
       \<not>((\<cn>v) \<ls> (\<cn>u)))" by auto (*rule MMI_ralbidv*)
     have S108: "x = (\<cn>u) \<longrightarrow> 
       x \<ls> (\<cn>v) \<longleftrightarrow> (\<cn>u) \<ls> (\<cn>v)" by (rule MMI_breq1)
     from S108 have S109: "x = (\<cn>u) \<longrightarrow> 
       (x \<ls> (\<cn>v) \<longrightarrow> 
       ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v))) \<longleftrightarrow> 
       ((\<cn>u) \<ls> (\<cn>v) \<longrightarrow> 
       ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)))" by (rule MMI_imbi1d)
     from S109 have S110: "x = (\<cn>u) \<longrightarrow> 
       (\<forall>v\<in>\<real>. x \<ls> (\<cn>v) \<longrightarrow> 
       ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v))) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>u) \<ls> (\<cn>v) \<longrightarrow> 
       ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)))" by auto (*rule MMI_ralbidv*)
     from S107 S110 have "x = (\<cn>u) \<longrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> \<not>((\<cn>v) \<ls> x)) \<and> (\<forall>v\<in>\<real>. x \<ls> (\<cn>v) \<longrightarrow> 
       ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v))) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> 
       \<not>((\<cn>v) \<ls> (\<cn>u))) \<and> (\<forall>v\<in>\<real>. (\<cn>u) \<ls> (\<cn>v) \<longrightarrow> 
       ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)))" by (rule MMI_anbi12d)
     } then have S111: "\<forall>x u. x = (\<cn>u) \<longrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> \<not>((\<cn>v) \<ls> x)) \<and> (\<forall>v\<in>\<real>. x \<ls> (\<cn>v) \<longrightarrow> 
       ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v))) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> 
       \<not>((\<cn>v) \<ls> (\<cn>u))) \<and> (\<forall>v\<in>\<real>. (\<cn>u) \<ls> (\<cn>v) \<longrightarrow> 
       ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)))" by simp
   from S102 S103 S111 have S112: 
     "( \<exists>x\<in>\<real>. (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> \<not>((\<cn>v) \<ls> x)) \<and> (\<forall>v\<in>\<real>. x \<ls> (\<cn>v) \<longrightarrow> 
   ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)))) \<longleftrightarrow> 
   ( \<exists>u\<in>\<real>. (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> 
   \<not>((\<cn>v) \<ls> (\<cn>u))) \<and> (\<forall>v\<in>\<real>. (\<cn>u) \<ls> (\<cn>v) \<longrightarrow> 
   ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v))))" by (rule MMI_rexxfr)
   { fix u
     { fix v
       have S113: "u \<in> \<real> \<and> v \<in> \<real> \<longrightarrow> 
	 u \<ls> v \<longleftrightarrow> (\<cn>v) \<ls> (\<cn>u)" by (rule MMI_ltnegt)
       from S113 have S114: "u \<in> \<real> \<and> v \<in> \<real> \<longrightarrow> 
	 \<not>(u \<ls> v) \<longleftrightarrow> 
	 \<not>((\<cn>v) \<ls> (\<cn>u))" by (rule MMI_negbid)
       from S114 have "u \<in> \<real> \<and> v \<in> \<real> \<longrightarrow> 
	 ((\<cn>v) \<in> A \<longrightarrow> \<not>(u \<ls> v)) \<longleftrightarrow> 
	 ((\<cn>v) \<in> A \<longrightarrow> 
	 \<not>((\<cn>v) \<ls> (\<cn>u)))" by (rule MMI_imbi2d)
     } then have S115: "\<forall> v. u \<in> \<real> \<and> v \<in> \<real> \<longrightarrow> 
	 ((\<cn>v) \<in> A \<longrightarrow> \<not>(u \<ls> v)) \<longleftrightarrow> 
	 ((\<cn>v) \<in> A \<longrightarrow> 
	 \<not>((\<cn>v) \<ls> (\<cn>u)))" by simp
     from S115 have S116: "u \<in> \<real> \<longrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> \<not>(u \<ls> v)) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> 
       \<not>((\<cn>v) \<ls> (\<cn>u)))" by (rule MMI_ralbidva)
     have S117: "v \<in> {w \<in> \<real>. (\<cn>w) \<in> A } \<longleftrightarrow> 
       v \<in> \<real> \<and> (\<cn>v) \<in> A" using MMI_negeq  MMI_eleq1d by auto
     from S117 have S118: "(v \<in> {w \<in> \<real>. (\<cn>w) \<in> A } \<longrightarrow> \<not>(u \<ls> v)) \<longleftrightarrow> 
       (v \<in> \<real> \<and> (\<cn>v) \<in> A \<longrightarrow> \<not>(u \<ls> v))" by (rule MMI_imbi1i)
     have S119: "(v \<in> \<real> \<and> (\<cn>v) \<in> A \<longrightarrow> \<not>(u \<ls> v)) \<longleftrightarrow> 
       (v \<in> \<real> \<longrightarrow> 
       (\<cn>v) \<in> A \<longrightarrow> \<not>(u \<ls> v))" by (rule MMI_impexp)
     from S118 S119 have S120: "(v \<in> {w \<in> \<real>. (\<cn>w) \<in> A } \<longrightarrow> \<not>(u \<ls> v)) \<longleftrightarrow> 
       (v \<in> \<real> \<longrightarrow> 
       (\<cn>v) \<in> A \<longrightarrow> \<not>(u \<ls> v))" by (rule MMI_bitr)
     from S120 have S121: "(\<forall>v. v \<in> {w \<in> \<real>. (\<cn>w) \<in> A } \<longrightarrow> \<not>(u \<ls> v)) \<longleftrightarrow> 
       (\<forall>v. v \<in> \<real> \<longrightarrow> 
       (\<cn>v) \<in> A \<longrightarrow> \<not>(u \<ls> v))" by auto (*rule MMI_albii*)
     have S122: "(\<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. \<not>(u \<ls> v)) \<longleftrightarrow> 
       (\<forall>v. v \<in> {w \<in> \<real>. (\<cn>w) \<in> A } \<longrightarrow> \<not>(u \<ls> v))" by (rule MMI_df_ral)
     have S123: "(\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> \<not>(u \<ls> v)) \<longleftrightarrow> 
       (\<forall>v. v \<in> \<real> \<longrightarrow> 
       (\<cn>v) \<in> A \<longrightarrow> \<not>(u \<ls> v))" by (rule MMI_df_ral)
     from S121 S122 S123 have S124: "(\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> \<not>(u \<ls> v)) \<longleftrightarrow> 
       (\<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. \<not>(u \<ls> v))" by (rule MMI_3bitr4r)
     from S116 S124 have S125: "u \<in> \<real> \<longrightarrow> 
       (\<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. \<not>(u \<ls> v)) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> 
       \<not>((\<cn>v) \<ls> (\<cn>u)))" by (rule MMI_syl5bbr)
     { fix v 
       have S126: "v \<in> \<real> \<and> u \<in> \<real> \<longrightarrow> 
	 v \<ls> u \<longleftrightarrow> (\<cn>u) \<ls> (\<cn>v)" by (rule MMI_ltnegt)
       from S126 have S127: "u \<in> \<real> \<and> v \<in> \<real> \<longrightarrow> 
	 v \<ls> u \<longleftrightarrow> (\<cn>u) \<ls> (\<cn>v)" by (rule MMI_ancoms)
       { fix t
	 have S128: "v \<in> \<real> \<and> t \<in> \<real> \<longrightarrow> 
	   v \<ls> t \<longleftrightarrow> (\<cn>t) \<ls> (\<cn>v)" by (rule MMI_ltnegt)
	 from S128 have "v \<in> \<real> \<and> t \<in> \<real> \<longrightarrow> 
	   (\<cn>t) \<in> A \<and> v \<ls> t \<longleftrightarrow> 
	   (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)" by (rule MMI_anbi2d)
       } then have S129: "\<forall> t. v \<in> \<real> \<and> t \<in> \<real> \<longrightarrow> 
	   (\<cn>t) \<in> A \<and> v \<ls> t \<longleftrightarrow> 
	   (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)" by simp
       from S129 have S130: "v \<in> \<real> \<longrightarrow> 
	 ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> v \<ls> t) \<longleftrightarrow> 
	 ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v))" by (rule MMI_rexbidva)
       have S131: "w = t \<longrightarrow> (\<cn>w) = (\<cn>t)" by (rule MMI_negeq)
       from S131 have S132: "w = t \<longrightarrow> 
	 (\<cn>w) \<in> A \<longleftrightarrow> (\<cn>t) \<in> A" by (rule MMI_eleq1d)
       from S132 have S133: "t \<in> {w \<in> \<real>. (\<cn>w) \<in> A } \<longleftrightarrow> 
	 t \<in> \<real> \<and> (\<cn>t) \<in> A" by auto (*rule MMI_elrab*)
       from S133 have S134: "t \<in> {w \<in> \<real>. (\<cn>w) \<in> A } \<and> v \<ls> t \<longleftrightarrow> 
	 (t \<in> \<real> \<and> (\<cn>t) \<in> A) \<and> v \<ls> t" by (rule MMI_anbi1i)
       have S135: "(t \<in> \<real> \<and> (\<cn>t) \<in> A) \<and> v \<ls> t \<longleftrightarrow> 
	 t \<in> \<real> \<and> (\<cn>t) \<in> A \<and> v \<ls> t" by (rule MMI_anass)
       from S134 S135 have S136: "t \<in> {w \<in> \<real>. (\<cn>w) \<in> A } \<and> v \<ls> t \<longleftrightarrow> 
	 t \<in> \<real> \<and> (\<cn>t) \<in> A \<and> v \<ls> t" by (rule MMI_bitr)
       from S136 have S137: "( \<exists>t\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<ls> t) \<longleftrightarrow> 
	 ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> v \<ls> t)" by auto (*rule MMI_rexbii2*)
       from S130 S137 have S138: "v \<in> \<real> \<longrightarrow> 
	 ( \<exists>t\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<ls> t) \<longleftrightarrow> 
	 ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v))" by (rule MMI_syl5bb)
       from S138 have S139: "u \<in> \<real> \<and> v \<in> \<real> \<longrightarrow> 
       ( \<exists>t\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<ls> t) \<longleftrightarrow> 
	 ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v))" by (rule MMI_adantl)
       from S127 S139 have "u \<in> \<real> \<and> v \<in> \<real> \<longrightarrow> 
	 (v \<ls> u \<longrightarrow> 
	 ( \<exists>t\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<ls> t)) \<longleftrightarrow> 
	 ((\<cn>u) \<ls> (\<cn>v) \<longrightarrow> 
	 ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)))" by (rule MMI_imbi12d)
     } then have S140: "\<forall> v. u \<in> \<real> \<and> v \<in> \<real> \<longrightarrow> 
	 (v \<ls> u \<longrightarrow> 
	 ( \<exists>t\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<ls> t)) \<longleftrightarrow> 
	 ((\<cn>u) \<ls> (\<cn>v) \<longrightarrow> 
	 ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)))" by simp
     from S140 have S141: "u \<in> \<real> \<longrightarrow> 
     (\<forall>v\<in>\<real>. v \<ls> u \<longrightarrow> 
       ( \<exists>t\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<ls> t)) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>u) \<ls> (\<cn>v) \<longrightarrow> 
       ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)))" by (rule MMI_ralbidva)
     from S125 S141 have S142: "u \<in> \<real> \<longrightarrow> 
       (\<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. \<not>(u \<ls> v)) \<and> (\<forall>v\<in>\<real>. v \<ls> u \<longrightarrow> 
       ( \<exists>t\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<ls> t)) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> 
       \<not>((\<cn>v) \<ls> (\<cn>u))) \<and> (\<forall>v\<in>\<real>. (\<cn>u) \<ls> (\<cn>v) \<longrightarrow> 
       ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)))" by (rule MMI_anbi12d)
   } then have S142: "\<forall> u. u \<in> \<real> \<longrightarrow> 
       (\<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. \<not>(u \<ls> v)) \<and> (\<forall>v\<in>\<real>. v \<ls> u \<longrightarrow> 
       ( \<exists>t\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<ls> t)) \<longleftrightarrow> 
       (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> 
       \<not>((\<cn>v) \<ls> (\<cn>u))) \<and> (\<forall>v\<in>\<real>. (\<cn>u) \<ls> (\<cn>v) \<longrightarrow> 
       ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)))" by simp
   from S142 have S143: 
     "( \<exists>u\<in>\<real>. (\<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. \<not>(u \<ls> v)) \<and> (\<forall>v\<in>\<real>. v \<ls> u \<longrightarrow> 
     ( \<exists>t\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<ls> t))) \<longleftrightarrow> 
     ( \<exists>u\<in>\<real>. (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> 
     \<not>((\<cn>v) \<ls> (\<cn>u))) \<and> (\<forall>v\<in>\<real>. (\<cn>u) \<ls> (\<cn>v) \<longrightarrow> 
     ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v))))" by (rule MMI_rexbiia)
   from S112 S143 have S144: 
     "( \<exists>x\<in>\<real>. (\<forall>v\<in>\<real>. (\<cn>v) \<in> A \<longrightarrow> 
     \<not>((\<cn>v) \<ls> x)) \<and> (\<forall>v\<in>\<real>. x \<ls> (\<cn>v) \<longrightarrow> 
   ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>v)))) \<longleftrightarrow> 
   ( \<exists>u\<in>\<real>. (\<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. \<not>(u \<ls> v)) \<and> (\<forall>v\<in>\<real>. v \<ls> u \<longrightarrow> 
   ( \<exists>t\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<ls> t)))" by (rule MMI_bitr4)
   from S101 S144 have S145: "A \<subseteq>\<real> \<longrightarrow> 
   ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y))) \<longleftrightarrow> 
   ( \<exists>u\<in>\<real>. (\<forall>v\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. \<not>(u \<ls> v)) \<and> (\<forall>v\<in>\<real>. v \<ls> u \<longrightarrow> 
   ( \<exists>t\<in>{w \<in> \<real>. (\<cn>w) \<in> A }. v \<ls> t)))" by (rule MMI_syl6bb)
   from S59 S145 have S146: "A \<subseteq>\<real> \<longrightarrow> 
   \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
   ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y)))" 
     by (rule MMI_sylibrd)
   from S146 show "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
   ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y)))" 
     by (rule MMI_3impib)
qed

(***** 586,587 ****************************************)

lemma (in MMIsar0) MMI_suprcl: 
   shows "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
    Sup(A,\<real>,\<cltrrset>) \<in> \<real>"
proof -
   have S1: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
   ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z)))" 
     by (rule MMI_sup3)
   have S2: "\<cltrrset> Orders \<real>" by (rule MMI_ltso)
   from S2 have S3: 
     "( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z))) \<longrightarrow> 
    Sup(A,\<real>,\<cltrrset>)  \<in> \<real>" by (rule MMI_supcl)
   from S1 S3 show "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
    Sup(A,\<real>,\<cltrrset>)  \<in> \<real>" by (rule MMI_syl)
qed

lemma (in MMIsar0) MMI_suprub: 
   shows "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> A \<longrightarrow> 
  B \<lsq>  Sup(A,\<real>,\<cltrrset>) "
proof -
   have S1: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
   ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z)))" 
     by (rule MMI_sup3)
   have S2: " \<cltrrset> Orders \<real>" by (rule MMI_ltso)
   from S2 have S3: 
     "( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z))) \<longrightarrow> 
   B \<in> A \<longrightarrow> \<not>( Sup(A,\<real>,\<cltrrset>)  \<ls> B)" by (rule MMI_supub)
   from S1 S3 have S4: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
   B \<in> A \<longrightarrow> 
   \<not>( Sup(A,\<real>,\<cltrrset>)  \<ls> B)" by (rule MMI_syl)
   from S4 have S5: "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> A \<longrightarrow> 
   \<not>( Sup(A,\<real>,\<cltrrset>)  \<ls> B)" by (rule MMI_imp)
   have S6: "B \<in> \<real> \<and>  Sup(A,\<real>,\<cltrrset>)  \<in> \<real> \<longrightarrow> 
   B \<lsq>  Sup(A,\<real>,\<cltrrset>)  \<longleftrightarrow> 
   \<not>( Sup(A,\<real>,\<cltrrset>)  \<ls> B)" by (rule MMI_lenltt)
   have S7: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> A \<subseteq>\<real>" 
     by (rule MMI_3simp1)
   from S7 have S8: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
   B \<in> A \<longrightarrow> B \<in> \<real>" by (rule MMI_sseld)
   from S8 have S9: 
     "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> A \<longrightarrow> B \<in> \<real>" 
     by (rule MMI_imp)
   have S10: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
    Sup(A,\<real>,\<cltrrset>)  \<in> \<real>" by (rule MMI_suprcl)
   from S10 have S11: "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> A \<longrightarrow> 
    Sup(A,\<real>,\<cltrrset>)  \<in> \<real>" by (rule MMI_adantr)
   from S6 S9 S11 have S12: 
     "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> A \<longrightarrow> 
   B \<lsq>  Sup(A,\<real>,\<cltrrset>)  \<longleftrightarrow> \<not>( Sup(A,\<real>,\<cltrrset>)  \<ls> B)" 
     by (rule MMI_sylanc)
   from S5 S12 show 
     "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> A \<longrightarrow> 
     B \<lsq>  Sup(A,\<real>,\<cltrrset>)" by (rule MMI_mpbird)
qed

(********** 588 - 590 *****************************)

lemma (in MMIsar0) MMI_suprlub: 
   shows  "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> 
  ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> \<real> \<and> B \<ls>  Sup(A,\<real>,\<cltrrset>) \<longrightarrow> 
  ( \<exists>z\<in>A. B \<ls> z)"
proof -
   have S1: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
   ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z)))" 
     by (rule MMI_sup3)
   have S2: "\<cltrrset> Orders \<real>" by (rule MMI_ltso)
   from S2 have S3: 
     "( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z))) \<longrightarrow> 
   B \<in> \<real> \<and> B \<ls>  Sup(A,\<real>,\<cltrrset>) \<longrightarrow> ( \<exists>z\<in>A. B \<ls> z)" 
     by (rule MMI_suplub)
   from S1 S3 have S4: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
   B \<in> \<real> \<and> B \<ls>  Sup(A,\<real>,\<cltrrset>) \<longrightarrow> ( \<exists>z\<in>A. B \<ls> z)" by (rule MMI_syl)
   from S4 show "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> 
     ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> \<real> \<and> B \<ls>  Sup(A,\<real>,\<cltrrset>) \<longrightarrow> 
     ( \<exists>z\<in>A. B \<ls> z)" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_suprnub: 
   shows "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> 
  ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> \<real> \<and> (\<forall>z\<in>A. \<not>(B \<ls> z)) \<longrightarrow> 
   \<not>(B \<ls>  Sup(A,\<real>,\<cltrrset>))"
proof -
  have S1: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
    ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z)))" 
    by (rule MMI_sup3)
  have S2: "\<cltrrset> Orders \<real>" by (rule MMI_ltso)
  from S2 have S3: 
    "( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z))) \<longrightarrow> 
    B \<in> \<real> \<and> (\<forall>z\<in>A. \<not>(B \<ls> z)) \<longrightarrow> 
    \<not>(B \<ls>  Sup(A,\<real>,\<cltrrset>))" by (rule MMI_supnub)
  from S1 S3 have S4: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
    B \<in> \<real> \<and> (\<forall>z\<in>A. \<not>(B \<ls> z)) \<longrightarrow> 
    \<not>(B \<ls>  Sup(A,\<real>,\<cltrrset>))" by (rule MMI_syl)
  from S4 show "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> 
    ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> \<real> \<and> (\<forall>z\<in>A. \<not>(B \<ls> z)) \<longrightarrow> 
   \<not>(B \<ls>  Sup(A,\<real>,\<cltrrset>))" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_suprleub: 
   shows 
  "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> \<real> \<and> (\<forall>z\<in>A. z \<lsq> B) \<longrightarrow> 
    Sup(A,\<real>,\<cltrrset>) \<lsq> B"
proof -
  { fix z
    have S1: "z \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
      z \<lsq> B \<longleftrightarrow> \<not>(B \<ls> z)" by (rule MMI_lenltt)
    have S2: "A \<subseteq>\<real> \<and> z \<in> A \<longrightarrow> z \<in> \<real>" by (rule MMI_ssel2)
    from S1 S2 have S3: "(A \<subseteq>\<real> \<and> z \<in> A) \<and> B \<in> \<real> \<longrightarrow> 
      z \<lsq> B \<longleftrightarrow> \<not>(B \<ls> z)" by (rule MMI_sylan)
    from S3 have "(A \<subseteq>\<real> \<and> B \<in> \<real>) \<and> z \<in> A \<longrightarrow> 
      z \<lsq> B \<longleftrightarrow> \<not>(B \<ls> z)" by (rule MMI_an1rs)
  } then have S4: "\<forall>z. (A \<subseteq>\<real> \<and> B \<in> \<real>) \<and> z \<in> A \<longrightarrow> 
      z \<lsq> B \<longleftrightarrow> \<not>(B \<ls> z)" by simp
  from S4 have S5: "A \<subseteq>\<real> \<and> B \<in> \<real> \<longrightarrow> 
    (\<forall>z\<in>A. z \<lsq> B) \<longleftrightarrow> 
    (\<forall>z\<in>A. \<not>(B \<ls> z))" by (rule MMI_ralbidva)
  from S5 have S6: "A \<subseteq>\<real> \<longrightarrow> 
   B \<in> \<real> \<longrightarrow> 
   (\<forall>z\<in>A. z \<lsq> B) \<longleftrightarrow> 
   (\<forall>z\<in>A. \<not>(B \<ls> z))" by (rule MMI_ex)
   from S6 have S7: "A \<subseteq>\<real> \<longrightarrow> 
   B \<in> \<real> \<and> (\<forall>z\<in>A. z \<lsq> B) \<longleftrightarrow> 
   B \<in> \<real> \<and> (\<forall>z\<in>A. \<not>(B \<ls> z))" by (rule MMI_pm5_32d)
   from S7 have S8: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
   B \<in> \<real> \<and> (\<forall>z\<in>A. z \<lsq> B) \<longleftrightarrow> 
   B \<in> \<real> \<and> (\<forall>z\<in>A. \<not>(B \<ls> z))" by (rule MMI_3ad2ant1)
   have S9: "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> 
     ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> \<real> \<and> (\<forall>z\<in>A. \<not>(B \<ls> z)) \<longrightarrow> 
     \<not>(B \<ls>  Sup(A,\<real>,\<cltrrset>))" by (rule MMI_suprnub)
   have S10: " Sup(A,\<real>,\<cltrrset>) \<in> \<real> \<and> B \<in> \<real> \<longrightarrow> 
    Sup(A,\<real>,\<cltrrset>) \<lsq> B \<longleftrightarrow> 
   \<not>(B \<ls>  Sup(A,\<real>,\<cltrrset>))" by (rule MMI_lenltt)
   have S11: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
    Sup(A,\<real>,\<cltrrset>) \<in> \<real>" by (rule MMI_suprcl)
   from S10 S11 have S12: "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> 
     ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> \<real> \<longrightarrow> 
    Sup(A,\<real>,\<cltrrset>) \<lsq> B \<longleftrightarrow> 
   \<not>(B \<ls>  Sup(A,\<real>,\<cltrrset>))" by (rule MMI_sylan)
   from S12 have S13: "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> 
     ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> \<real> \<and> (\<forall>z\<in>A. \<not>(B \<ls> z)) \<longrightarrow> 
    Sup(A,\<real>,\<cltrrset>) \<lsq> B \<longleftrightarrow> 
   \<not>(B \<ls>  Sup(A,\<real>,\<cltrrset>))" by (rule MMI_adantrr)
   from S9 S13 have S14: "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> 
     ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> \<real> \<and> (\<forall>z\<in>A. \<not>(B \<ls> z)) \<longrightarrow> 
    Sup(A,\<real>,\<cltrrset>) \<lsq> B" by (rule MMI_mpbird)
   from S14 have S15: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
   B \<in> \<real> \<and> (\<forall>z\<in>A. \<not>(B \<ls> z)) \<longrightarrow> 
    Sup(A,\<real>,\<cltrrset>) \<lsq> B" by (rule MMI_ex)
   from S8 S15 have S16: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
   B \<in> \<real> \<and> (\<forall>z\<in>A. z \<lsq> B) \<longrightarrow> 
    Sup(A,\<real>,\<cltrrset>) \<lsq> B" by (rule MMI_sylbid)
   from S16 show "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> 
     ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> \<real> \<and> (\<forall>z\<in>A. z \<lsq> B) \<longrightarrow> 
    Sup(A,\<real>,\<cltrrset>) \<lsq> B" by (rule MMI_imp)
qed

(************** 591 - 595 ******************************)

lemma (in MMIsar0) MMI_sup3i: 
  assumes A1: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)"   
   shows " \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z))"
proof -
   from A1 have S1: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)".
   have S2: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x) \<longrightarrow> 
   ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z)))" 
     by (rule MMI_sup3)
   from S1 S2 show 
     " \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z))" 
     by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_suprcli: 
  assumes A1: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)"   
   shows " Sup(A,\<real>,\<cltrrset>) \<in> \<real>"
proof -
   have S1: "\<cltrrset> Orders \<real>" by (rule MMI_ltso)
   from A1 have S2: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)".
   from S2 have S3: 
     " \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z))" 
     by (rule MMI_sup3i)
   from S1 S3 show " Sup(A,\<real>,\<cltrrset>) \<in> \<real>" by (rule MMI_supcli)
qed

lemma (in MMIsar0) MMI_suprubi: 
  assumes A1: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)"   
   shows "B \<in> A \<longrightarrow> 
   B \<lsq>  Sup(A,\<real>,\<cltrrset>)"
proof -
   from A1 have S1: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)".
   have S2: "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> A \<longrightarrow> 
   B \<lsq>  Sup(A,\<real>,\<cltrrset>)" by (rule MMI_suprub)
   from S1 S2 show "B \<in> A \<longrightarrow> 
   B \<lsq>  Sup(A,\<real>,\<cltrrset>)" by (rule MMI_mpan)
qed

lemma (in MMIsar0) MMI_suprlubi: 
  assumes A1: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)"   
  shows "B \<in> \<real> \<and> B \<ls>  Sup(A,\<real>,\<cltrrset>) \<longrightarrow> ( \<exists>z\<in>A. B \<ls> z)"
proof -
   have S1: "\<cltrrset> Orders \<real>" by (rule MMI_ltso)
   from A1 have S2: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)".
   from S2 have S3: 
     "\<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z))" 
     by (rule MMI_sup3i)
   from S1 S3 show "B \<in> \<real> \<and> B \<ls>  Sup(A,\<real>,\<cltrrset>) \<longrightarrow> ( \<exists>z\<in>A. B \<ls> z)" 
     by (rule MMI_suplubi)
qed

lemma (in MMIsar0) MMI_suprnubi: 
  assumes A1: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)"   
   shows "B \<in> \<real> \<and> (\<forall>z\<in>A. \<not>(B \<ls> z)) \<longrightarrow> 
   \<not>(B \<ls>  Sup(A,\<real>,\<cltrrset>))"
proof -
   have S1: "\<cltrrset> Orders \<real>" by (rule MMI_ltso)
   from A1 have S2: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)".
   from S2 have S3: 
     "\<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x \<ls> y)) \<and> (\<forall>y\<in>\<real>. y \<ls> x \<longrightarrow> ( \<exists>z\<in>A. y \<ls> z))" 
     by (rule MMI_sup3i)
   from S1 S3 show "B \<in> \<real> \<and> (\<forall>z\<in>A. \<not>(B \<ls> z)) \<longrightarrow> 
   \<not>(B \<ls>  Sup(A,\<real>,\<cltrrset>))" by (rule MMI_supnubi)
qed

(************ 596 - 598 ***********************)

lemma (in MMIsar0) MMI_suprleubi: 
  assumes A1: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)"   
   shows "B \<in> \<real> \<and> (\<forall>z\<in>A. z \<lsq> B) \<longrightarrow> 
    Sup(A,\<real>,\<cltrrset>) \<lsq> B"
proof -
   from A1 have S1: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)".
   have S2: 
     "(A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. y \<lsq> x)) \<and> B \<in> \<real> \<and> (\<forall>z\<in>A. z \<lsq> B) \<longrightarrow> 
    Sup(A,\<real>,\<cltrrset>) \<lsq> B" by (rule MMI_suprleub)
   from S1 S2 show "B \<in> \<real> \<and> (\<forall>z\<in>A. z \<lsq> B) \<longrightarrow> 
    Sup(A,\<real>,\<cltrrset>) \<lsq> B" by (rule MMI_mpan)
qed  

lemma (in MMIsar0) MMI_reuunineg: assumes 
  A1: "\<forall>x y. x = (\<cn>y) \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<psi>(y)"   
   shows "(\<exists>!x. x\<in>\<real> \<and> \<phi>(x)) \<longrightarrow> 
   \<Union> {x \<in> \<real>. \<phi>(x) } = (\<cn>(\<Union> {y \<in> \<real>. \<psi>(y) }))"
proof -
  let ?C = "\<cn>(\<Union> {y \<in> \<real>. \<psi>(y) })"
  { fix z
    have S1: "z \<in> {y \<in> \<real>. \<psi>(y) } \<longrightarrow> 
      (\<forall>y. z \<in> {y \<in> \<real>. \<psi>(y) })" by (rule MMI_hbrab1)
    from S1 have S2: "z \<in> \<Union> {y \<in> \<real>. \<psi>(y) } \<longrightarrow> 
      (\<forall>y. z \<in> \<Union> {y \<in> \<real>. \<psi>(y) })" by (rule MMI_hbuni)
    from S2 have "z \<in> (\<cn>(\<Union> {y \<in> \<real>. \<psi>(y) })) \<longrightarrow> 
      (\<forall>y. z \<in> (\<cn>(\<Union> {y \<in> \<real>. \<psi>(y) })))" by (rule MMI_hbneg)
  } then have S3: "\<forall> z. z \<in> ?C \<longrightarrow> (\<forall>y. z \<in> ?C)" by simp
  { fix y
    have "y \<in> \<real> \<longrightarrow> (\<cn>y) \<in> \<real>" by (rule MMI_renegclt)
  } then have S4: "\<forall> y. y \<in> \<real> \<longrightarrow> (\<cn>y) \<in> \<real>" by simp
   have S5: "\<Union> {y \<in> \<real>. \<psi>(y) } \<in> \<real> \<longrightarrow> ?C \<in> \<real>" by (rule MMI_renegclt)
   from A1 have S6: "\<forall>x y.  x = (\<cn>y) \<longrightarrow>  \<phi>(x) \<longleftrightarrow> \<psi>(y)" .
   { fix y
     have "y = \<Union> {y \<in> \<real>. \<psi>(y) } \<longrightarrow> 
       (\<cn>y) = (\<cn>(\<Union> {y \<in> \<real>. \<psi>(y) }))" by (rule MMI_negeq)
   } then have S7: "\<forall> y. y = \<Union> {y \<in> \<real>. \<psi>(y) } \<longrightarrow> 
       (\<cn>y) = (\<cn>(\<Union> {y \<in> \<real>. \<psi>(y) }))" by simp
   { fix x
     have "x \<in> \<real> \<longrightarrow> (\<cn>x) \<in> \<real>" by (rule MMI_renegclt)
   } then have S8: "\<forall> x. x \<in> \<real> \<longrightarrow> (\<cn>x) \<in> \<real>" by simp
   { fix x y
     have S9: "x \<in> \<complex> \<and> y \<in> \<complex> \<longrightarrow> 
       x = (\<cn>y) \<longleftrightarrow> y = (\<cn>x)" by (rule MMI_negcon2t)
     have S10: "x \<in> \<real> \<longrightarrow> x \<in> \<complex>" by (rule MMI_recnt)
     have S11: "y \<in> \<real> \<longrightarrow> y \<in> \<complex>" by (rule MMI_recnt)
     from S9 S10 S11 have "x \<in> \<real> \<and> y \<in> \<real> \<longrightarrow> 
       x = (\<cn>y) \<longleftrightarrow> y = (\<cn>x)" by (rule MMI_syl2an)
   } then have S12: "\<forall>x y. x \<in> \<real> \<and> y \<in> \<real> \<longrightarrow> 
       x = (\<cn>y) \<longleftrightarrow> y = (\<cn>x)" by simp
   from S8 S12 have S13: "\<forall>x. x \<in> \<real> \<longrightarrow> 
   (\<exists>!y. y\<in>\<real>\<and>x = (\<cn>y))" by (rule MMI_reuhyp)
   from S3 S4 S5 S6 S7 S13 show "(\<exists>!x. x\<in>\<real> \<and> \<phi>(x)) \<longrightarrow> 
   \<Union> {x \<in> \<real>. \<phi>(x) } = (\<cn>(\<Union> {y \<in> \<real>. \<psi>(y) }))" by (rule MMI_reuunixfr)
qed

lemma (in MMIsar0) MMI_dfinfmr: 
   shows "A \<subseteq>\<real> \<longrightarrow>  Sup(A,\<real>,converse(\<cltrrset>)) = 
  \<Union> {x \<in> \<real>. (\<forall>y\<in>A. x \<lsq> y) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y)) }"
proof -
  { fix x
    { fix y
      have S1: "x \<in> \<real> \<and> y \<in> \<real> \<longrightarrow> 
	x \<lsq> y \<longleftrightarrow> \<not>(y \<ls> x)" by (rule MMI_lenltt)
      have S2: "x = x" by simp (*rule MMI_visset&*)
      have S3: "y = y" by simp (*rule MMI_visset*)
      from S2 S3 have S4: "x > y \<longleftrightarrow> y \<ls> x" by (rule MMI_brcnv)
      from S4 have S5: "\<not>(x > y) \<longleftrightarrow> \<not>(y \<ls> x)" by (rule MMI_negbii)
      from S1 S5 have S6: "x \<in> \<real> \<and> y \<in> \<real> \<longrightarrow> 
	\<not>(x > y) \<longleftrightarrow> x \<lsq> y" by auto (*rule MMI_syl6rbbr*)
      have S7: "A \<subseteq>\<real> \<and> y \<in> A \<longrightarrow> y \<in> \<real>" by (rule MMI_ssel2)
      from S6 S7 have S8: "x \<in> \<real> \<and> A \<subseteq>\<real> \<and> y \<in> A \<longrightarrow> 
	\<not>(x > y) \<longleftrightarrow> x \<lsq> y" by (rule MMI_sylan2)
      from S8 have S9: "(A \<subseteq>\<real> \<and> y \<in> A) \<and> x \<in> \<real> \<longrightarrow> 
	\<not>(x > y) \<longleftrightarrow> x \<lsq> y" by (rule MMI_ancoms)
      from S9 have "(A \<subseteq>\<real> \<and> x \<in> \<real>) \<and> y \<in> A \<longrightarrow> 
	\<not>(x > y) \<longleftrightarrow> x \<lsq> y" by (rule MMI_an1rs)
    } then have S10: "\<forall> y. (A \<subseteq>\<real> \<and> x \<in> \<real>) \<and> y \<in> A \<longrightarrow> 
	\<not>(x > y) \<longleftrightarrow> x \<lsq> y" by simp
    from S10 have S11: "A \<subseteq>\<real> \<and> x \<in> \<real> \<longrightarrow> 
      (\<forall>y\<in>A. \<not>(x > y)) \<longleftrightarrow> (\<forall>y\<in>A. x \<lsq> y)" by (rule MMI_ralbidva)
    { fix y::i
      have S12: "y = y" by simp
      have S13: "x = x" by simp
      from S12 S13 have S14: "y > x \<longleftrightarrow> x \<ls> y" by (rule MMI_brcnv)
      have S15: "y = y" by simp
      { fix z::i
	have S16: "z = z" by simp
	from S15 S16 have S17: "y > z \<longleftrightarrow> z \<ls> y" by (rule MMI_brcnv)
      } then have  S17: "\<forall> z. y > z \<longleftrightarrow> z \<ls> y" by simp
      from S17 have S18: "( \<exists>z\<in>A. y > z) \<longleftrightarrow> ( \<exists>z\<in>A. z \<ls> y)" by (rule MMI_rexbii)
      from S14 S18 have "(y > x \<longrightarrow> ( \<exists>z\<in>A. y > z)) \<longleftrightarrow> 
	(x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y))" by (rule MMI_imbi12i)
    } then have  S19: "\<forall> y. (y > x \<longrightarrow> ( \<exists>z\<in>A. y > z)) \<longleftrightarrow> 
	(x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y))" by simp
    from S19 have S20: "(\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>z\<in>A. y > z)) \<longleftrightarrow> 
      (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y))" by (rule MMI_ralbii)
    from S20 have S21: "A \<subseteq>\<real> \<and> x \<in> \<real> \<longrightarrow> 
      (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>z\<in>A. y > z)) \<longleftrightarrow> 
      (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y))" by (rule MMI_a1i)
    from S11 S21 have S22: "A \<subseteq>\<real> \<and> x \<in> \<real> \<longrightarrow> 
      (\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>z\<in>A. y > z)) \<longleftrightarrow> 
      (\<forall>y\<in>A. x \<lsq> y) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y))" 
      by (rule MMI_anbi12d)
    from S22 have "A \<subseteq>\<real> \<longrightarrow> x \<in> \<real> \<longrightarrow> 
      (\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>z\<in>A. y > z)) \<longleftrightarrow> 
      (\<forall>y\<in>A. x \<lsq> y) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y))" 
      by (rule MMI_ex)
  } then have S23: "\<forall> x. A \<subseteq>\<real> \<longrightarrow> x \<in> \<real> \<longrightarrow> 
      (\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>z\<in>A. y > z)) \<longleftrightarrow> 
      (\<forall>y\<in>A. x \<lsq> y) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y))"
    by simp
  from S23 have S24: "A \<subseteq>\<real> \<longrightarrow> 
    {x \<in> \<real>. (\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>z\<in>A. y > z)) } = 
    {x \<in> \<real>. (\<forall>y\<in>A. x \<lsq> y) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y)) }" 
    by (rule MMI_rabbidv)
  from S24 have S25: "A \<subseteq>\<real> \<longrightarrow> 
    \<Union> {x \<in> \<real>. (\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>z\<in>A. y > z)) } = 
    \<Union> {x \<in> \<real>. (\<forall>y\<in>A. x \<lsq> y) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y)) }" 
    by (rule MMI_unieqd)
  have S26: "Sup(A,\<real>,converse(\<cltrrset>)) = 
    \<Union> {x \<in> \<real>. (\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>z\<in>A. y > z)) }" 
    by (rule MMI_df_inf)
  from S25 S26 show "A \<subseteq>\<real> \<longrightarrow>  Sup(A,\<real>,converse(\<cltrrset>)) = 
    \<Union> {x \<in> \<real>. (\<forall>y\<in>A. x \<lsq> y) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>z\<in>A. z \<ls> y)) }" 
    by (rule MMI_syl5eq)
qed

(******* 599,600 *****************************)

lemma (in MMIsar0) MMI_infmsup: 
   shows "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
   Sup(A,\<real>,converse(\<cltrrset>)) = (\<cn>Sup({z \<in> \<real>. (\<cn>z) \<in> A },\<real>,\<cltrrset>))"
proof -
  have S1: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
    ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)))" 
    by (rule MMI_infm3)
  from S1 have S2: "A \<subseteq>\<real> \<longrightarrow> 
    \<not>(A = 0) \<longrightarrow> 
    ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
    ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)))" 
    by (rule MMI_3exp)
  { fix x v
    have S3: "x = (\<cn>v) \<longrightarrow> 
      y \<ls> x \<longleftrightarrow> y \<ls> (\<cn>v)" by (rule MMI_breq2)
    from S3 have S4: "x = (\<cn>v) \<longrightarrow> 
      \<not>(y \<ls> x) \<longleftrightarrow> \<not>(y \<ls> (\<cn>v))" by (rule MMI_negbid)
    from S4 have S5: "x = (\<cn>v) \<longrightarrow> 
      (\<forall>y\<in>A. \<not>(y \<ls> x)) \<longleftrightarrow> 
      (\<forall>y\<in>A. \<not>(y \<ls> (\<cn>v)))" by auto (*rule MMI_ralbidv*)
    have S6: "x = (\<cn>v) \<longrightarrow> 
      x \<ls> y \<longleftrightarrow> (\<cn>v) \<ls> y" by (rule MMI_breq1)
    from S6 have S7: "x = (\<cn>v) \<longrightarrow> 
      (x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)) \<longleftrightarrow> 
      ((\<cn>v) \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))" by (rule MMI_imbi1d)
    from S7 have S8: "x = (\<cn>v) \<longrightarrow> 
      (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)) \<longleftrightarrow> 
      (\<forall>y\<in>\<real>. (\<cn>v) \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))" by auto (*rule MMI_ralbidv*)
    from S5 S8 have S9: "x = (\<cn>v) \<longrightarrow> 
      (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)) \<longleftrightarrow> 
      (\<forall>y\<in>A. \<not>(y \<ls> (\<cn>v))) \<and> (\<forall>y\<in>\<real>. (\<cn>v) \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))" 
      by (rule MMI_anbi12d)
  } then have S9: "\<forall> x v. x = (\<cn>v) \<longrightarrow> 
      (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)) \<longleftrightarrow> 
      (\<forall>y\<in>A. \<not>(y \<ls> (\<cn>v))) \<and> (\<forall>y\<in>\<real>. (\<cn>v) \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))" 
    by simp
  from S9 have S10: 
    "(\<exists>!x. x\<in>\<real> \<and> (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))) \<longrightarrow> 
    \<Union> {x \<in> \<real>. (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)) } = 
    (\<cn>(\<Union> {v \<in> \<real>. (\<forall>y\<in>A. \<not>(y \<ls> (\<cn>v))) \<and> (\<forall>y\<in>\<real>. (\<cn>v) \<ls> y \<longrightarrow> 
    ( \<exists>w\<in>A. w \<ls> y)) }))" by (rule MMI_reuunineg)
  have S11: "Sup(A,\<real>,converse(\<cltrrset>)) = 
   \<Union> {x \<in> \<real>. (\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>w\<in>A. y > w)) }" by (rule MMI_df_inf)
  { fix x::i 
    { fix y::i 
      have S12: "x = x" by simp (*rule MMI_visset*)
      have S13: "y = y" by simp (*rule MMI_visset*)
      from S12 S13 have S14: "x > y \<longleftrightarrow> y \<ls> x" by (rule MMI_brcnv)
      from S14 have S15: "\<not>(x > y) \<longleftrightarrow> \<not>(y \<ls> x)" by (rule MMI_negbii)
    } then have  S15: "\<forall> y. \<not>(x > y) \<longleftrightarrow> \<not>(y \<ls> x)" by simp
    from S15 have S16: "(\<forall>y\<in>A. \<not>(x > y)) \<longleftrightarrow> 
      (\<forall>y\<in>A. \<not>(y \<ls> x))" by (rule MMI_ralbii)
    { fix y::i
      have S17: "y = y" by simp
      have S18: "x = x" by simp
      from S17 S18 have S19: "y > x \<longleftrightarrow> x \<ls> y" by (rule MMI_brcnv)
      have S20: "y = y" by simp
      { fix w::i
	have S21: "w = w" by simp (*rule MMI_visset*)
	from S20 S21 have S22: "y > w \<longleftrightarrow> w \<ls> y" by (rule MMI_brcnv)
      } then have  S22: "\<forall> w. y > w \<longleftrightarrow> w \<ls> y" by simp
      from S22 have S23: "( \<exists>w\<in>A. y > w) \<longleftrightarrow> ( \<exists>w\<in>A. w \<ls> y)" by (rule MMI_rexbii)
      from S19 S23 have "(y > x \<longrightarrow> ( \<exists>w\<in>A. y > w)) \<longleftrightarrow> 
	(x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))" by (rule MMI_imbi12i)
    } then have S24: "\<forall>y.(y > x \<longrightarrow> ( \<exists>w\<in>A. y > w)) \<longleftrightarrow> 
	(x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))" by simp
    from S24 have S25: "(\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>w\<in>A. y > w)) \<longleftrightarrow> 
      (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))" by (rule MMI_ralbii)
    from S16 S25 have "(\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>w\<in>A. y > w)) \<longleftrightarrow> 
      (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))" 
      by (rule MMI_anbi12i)
  } then have S26: "\<forall>x. (\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>w\<in>A. y > w)) \<longleftrightarrow> 
      (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))" by simp
  then have S27: "\<forall> x. x \<in> \<real> \<longrightarrow> 
    (\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>w\<in>A. y > w)) \<longleftrightarrow> 
    (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))" by simp
    from S27 have S28: 
      "{x \<in> \<real>. (\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>w\<in>A. y > w)) } = 
      {x \<in> \<real>. (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)) }" 
      by (rule MMI_rabbii)
    from S28 have S29: 
      "\<Union> {x \<in> \<real>. (\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>w\<in>A. y > w)) } = 
      \<Union> {x \<in> \<real>. (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)) }" 
      by (rule MMI_unieqi)
    from S11 S29 have S30: "Sup(A,\<real>,converse(\<cltrrset>)) = 
      \<Union> {x \<in> \<real>. (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)) }" 
      by (rule MMI_eqtr)
    from S10 S30 have S31: 
      "(\<exists>!x. x\<in>\<real> \<and> (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))) \<longrightarrow> 
      Sup(A,\<real>,converse(\<cltrrset>)) = 
      (\<cn>(\<Union> {v \<in> \<real>. (\<forall>y\<in>A. \<not>(y \<ls> (\<cn>v))) \<and> (\<forall>y\<in>\<real>. (\<cn>v) \<ls> y \<longrightarrow> 
      ( \<exists>w\<in>A. w \<ls> y)) }))" by (rule MMI_syl5eq)
    { fix v
      { fix u
	have S32: "v \<in> \<real> \<and> u \<in> \<real> \<longrightarrow> 
	  v \<ls> u \<longleftrightarrow> (\<cn>u) \<ls> (\<cn>v)" by (rule MMI_ltnegt)
	from S32 have S33: "v \<in> \<real> \<and> u \<in> \<real> \<longrightarrow> 
	  \<not>(v \<ls> u) \<longleftrightarrow> 
	  \<not>((\<cn>u) \<ls> (\<cn>v))" by (rule MMI_negbid)
	from S33 have "v \<in> \<real> \<and> u \<in> \<real> \<longrightarrow> 
	  ((\<cn>u) \<in> A \<longrightarrow> \<not>(v \<ls> u)) \<longleftrightarrow> 
	  ((\<cn>u) \<in> A \<longrightarrow> 
	  \<not>((\<cn>u) \<ls> (\<cn>v)))" by (rule MMI_imbi2d)
    } then have  S34: "\<forall> u. v \<in> \<real> \<and> u \<in> \<real> \<longrightarrow> 
	((\<cn>u) \<in> A \<longrightarrow> \<not>(v \<ls> u)) \<longleftrightarrow> 
	((\<cn>u) \<in> A \<longrightarrow> \<not>((\<cn>u) \<ls> (\<cn>v)))" by simp
    from S34 have S35: "v \<in> \<real> \<longrightarrow> 
      (\<forall>u\<in>\<real>. (\<cn>u) \<in> A \<longrightarrow> \<not>(v \<ls> u)) \<longleftrightarrow> 
      (\<forall>u\<in>\<real>. (\<cn>u) \<in> A \<longrightarrow> 
      \<not>((\<cn>u) \<ls> (\<cn>v)))" by (rule MMI_ralbidva)
    have S36: "z = u \<longrightarrow> (\<cn>z) = (\<cn>u)" by (rule MMI_negeq)
    from S36 have S37: "z = u \<longrightarrow> 
      (\<cn>z) \<in> A \<longleftrightarrow> (\<cn>u) \<in> A" by (rule MMI_eleq1d)
    from S37 have S38: "u \<in> {z \<in> \<real>. (\<cn>z) \<in> A } \<longleftrightarrow> 
      u \<in> \<real> \<and> (\<cn>u) \<in> A" by auto (*rule MMI_elrab*)
    from S38 have S39: "(u \<in> {z \<in> \<real>. (\<cn>z) \<in> A } \<longrightarrow> \<not>(v \<ls> u)) \<longleftrightarrow> 
      (u \<in> \<real> \<and> (\<cn>u) \<in> A \<longrightarrow> \<not>(v \<ls> u))" by (rule MMI_imbi1i)
    have S40: "(u \<in> \<real> \<and> (\<cn>u) \<in> A \<longrightarrow> \<not>(v \<ls> u)) \<longleftrightarrow> 
      (u \<in> \<real> \<longrightarrow> 
      (\<cn>u) \<in> A \<longrightarrow> \<not>(v \<ls> u))" by (rule MMI_impexp)
    from S39 S40 have S41: "(u \<in> {z \<in> \<real>. (\<cn>z) \<in> A } \<longrightarrow> \<not>(v \<ls> u)) \<longleftrightarrow> 
      (u \<in> \<real> \<longrightarrow> 
      (\<cn>u) \<in> A \<longrightarrow> \<not>(v \<ls> u))" by (rule MMI_bitr)
    from S41 have S42: "(\<forall>u. u \<in> {z \<in> \<real>. (\<cn>z) \<in> A } \<longrightarrow> \<not>(v \<ls> u)) \<longleftrightarrow> 
      (\<forall>u. u \<in> \<real> \<longrightarrow> 
      (\<cn>u) \<in> A \<longrightarrow> \<not>(v \<ls> u))" by auto (*rule MMI_albii*)
    have S43: "(\<forall>u\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. \<not>(v \<ls> u)) \<longleftrightarrow> 
      (\<forall>u. u \<in> {z \<in> \<real>. (\<cn>z) \<in> A } \<longrightarrow> \<not>(v \<ls> u))" by (rule MMI_df_ral)
    have S44: "(\<forall>u\<in>\<real>. (\<cn>u) \<in> A \<longrightarrow> \<not>(v \<ls> u)) \<longleftrightarrow> 
      (\<forall>u. u \<in> \<real> \<longrightarrow> 
      (\<cn>u) \<in> A \<longrightarrow> \<not>(v \<ls> u))" by (rule MMI_df_ral)
    from S42 S43 S44 have S45: "(\<forall>u\<in>\<real>. (\<cn>u) \<in> A \<longrightarrow> \<not>(v \<ls> u)) \<longleftrightarrow> 
      (\<forall>u\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. \<not>(v \<ls> u))" by (rule MMI_3bitr4r)
    from S35 S45 have S46: "v \<in> \<real> \<longrightarrow> 
      (\<forall>u\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. \<not>(v \<ls> u)) \<longleftrightarrow> 
      (\<forall>u\<in>\<real>. (\<cn>u) \<in> A \<longrightarrow> 
      \<not>((\<cn>u) \<ls> (\<cn>v)))" by (rule MMI_syl5bbr)
    { fix u
      have S47: "u \<in> \<real> \<and> v \<in> \<real> \<longrightarrow> 
	u \<ls> v \<longleftrightarrow> (\<cn>v) \<ls> (\<cn>u)" by (rule MMI_ltnegt)
      from S47 have S48: "v \<in> \<real> \<and> u \<in> \<real> \<longrightarrow> 
	u \<ls> v \<longleftrightarrow> (\<cn>v) \<ls> (\<cn>u)" by (rule MMI_ancoms)
      { fix t
	have S49: "u \<in> \<real> \<and> t \<in> \<real> \<longrightarrow> 
	  u \<ls> t \<longleftrightarrow> (\<cn>t) \<ls> (\<cn>u)" by (rule MMI_ltnegt)
	from S49 have "u \<in> \<real> \<and> t \<in> \<real> \<longrightarrow> 
	  (\<cn>t) \<in> A \<and> u \<ls> t \<longleftrightarrow> 
	  (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u)" by (rule MMI_anbi2d)
      } then have S50: "\<forall> t. u \<in> \<real> \<and> t \<in> \<real> \<longrightarrow> 
	  (\<cn>t) \<in> A \<and> u \<ls> t \<longleftrightarrow> 
	  (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u)" by simp
      from S50 have S51: "u \<in> \<real> \<longrightarrow> 
	( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> u \<ls> t) \<longleftrightarrow> 
	( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u))" by (rule MMI_rexbidva)
      have S52: "z = t \<longrightarrow> (\<cn>z) = (\<cn>t)" by (rule MMI_negeq)
      from S52 have S53: "z = t \<longrightarrow> 
	(\<cn>z) \<in> A \<longleftrightarrow> (\<cn>t) \<in> A" by (rule MMI_eleq1d)
      from S53 have S54: "t \<in> {z \<in> \<real>. (\<cn>z) \<in> A } \<longleftrightarrow> 
	t \<in> \<real> \<and> (\<cn>t) \<in> A" by auto (*rule MMI_elrab*)
      from S54 have S55: "t \<in> {z \<in> \<real>. (\<cn>z) \<in> A } \<and> u \<ls> t \<longleftrightarrow> 
	(t \<in> \<real> \<and> (\<cn>t) \<in> A) \<and> u \<ls> t" by (rule MMI_anbi1i)
      have S56: "(t \<in> \<real> \<and> (\<cn>t) \<in> A) \<and> u \<ls> t \<longleftrightarrow> 
	t \<in> \<real> \<and> (\<cn>t) \<in> A \<and> u \<ls> t" by (rule MMI_anass)
      from S55 S56 have S57: "t \<in> {z \<in> \<real>. (\<cn>z) \<in> A } \<and> u \<ls> t \<longleftrightarrow> 
	t \<in> \<real> \<and> (\<cn>t) \<in> A \<and> u \<ls> t" by (rule MMI_bitr)
      from S57 have S58: "( \<exists>t\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. u \<ls> t) \<longleftrightarrow> 
	( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> u \<ls> t)" by auto (*rule MMI_rexbii2*)
      from S51 S58 have S59: "u \<in> \<real> \<longrightarrow> 
	( \<exists>t\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. u \<ls> t) \<longleftrightarrow> 
	( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u))" by (rule MMI_syl5bb)
      from S59 have S60: "v \<in> \<real> \<and> u \<in> \<real> \<longrightarrow> 
	( \<exists>t\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. u \<ls> t) \<longleftrightarrow> 
	( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u))" by (rule MMI_adantl)
      from S48 S60 have S61: "v \<in> \<real> \<and> u \<in> \<real> \<longrightarrow> 
	(u \<ls> v \<longrightarrow> 
	( \<exists>t\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. u \<ls> t)) \<longleftrightarrow> 
	((\<cn>v) \<ls> (\<cn>u) \<longrightarrow> 
	( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u)))" by (rule MMI_imbi12d)
    } then have S61: "\<forall> u. v \<in> \<real> \<and> u \<in> \<real> \<longrightarrow> 
	(u \<ls> v \<longrightarrow> ( \<exists>t\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. u \<ls> t)) \<longleftrightarrow> 
	((\<cn>v) \<ls> (\<cn>u) \<longrightarrow> ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u)))"
      by simp
    from S61 have S62: "v \<in> \<real> \<longrightarrow> 
      (\<forall>u\<in>\<real>. u \<ls> v \<longrightarrow> 
      ( \<exists>t\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. u \<ls> t)) \<longleftrightarrow> 
      (\<forall>u\<in>\<real>. (\<cn>v) \<ls> (\<cn>u) \<longrightarrow> 
      ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u)))" by (rule MMI_ralbidva)
    from S46 S62 have S63: "v \<in> \<real> \<longrightarrow> 
      (\<forall>u\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. \<not>(v \<ls> u)) \<and> (\<forall>u\<in>\<real>. u \<ls> v \<longrightarrow> 
      ( \<exists>t\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. u \<ls> t)) \<longleftrightarrow> 
      (\<forall>u\<in>\<real>. (\<cn>u) \<in> A \<longrightarrow> 
      \<not>((\<cn>u) \<ls> (\<cn>v))) \<and> (\<forall>u\<in>\<real>. (\<cn>v) \<ls> (\<cn>u) \<longrightarrow> 
      ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u)))" by (rule MMI_anbi12d)
    have S64: "A \<subseteq>\<real> \<longrightarrow> 
      y \<in> A \<longrightarrow> y \<in> \<real>" by (rule MMI_ssel)
    from S64 have S65: "A \<subseteq>\<real> \<longrightarrow> 
      y \<in> A \<longleftrightarrow> 
      y \<in> \<real> \<and> y \<in> A" by (rule MMI_pm4_71rd)
    from S65 have S66: "A \<subseteq>\<real> \<longrightarrow> 
      (y \<in> A \<longrightarrow> \<not>(y \<ls> (\<cn>v))) \<longleftrightarrow> 
      (y \<in> \<real> \<and> y \<in> A \<longrightarrow> \<not>(y \<ls> (\<cn>v)))" by (rule MMI_imbi1d)
    have S67: "(y \<in> \<real> \<and> y \<in> A \<longrightarrow> \<not>(y \<ls> (\<cn>v))) \<longleftrightarrow> 
      (y \<in> \<real> \<longrightarrow> 
      y \<in> A \<longrightarrow> \<not>(y \<ls> (\<cn>v)))" by (rule MMI_impexp)
    from S66 S67 have S68: "A \<subseteq>\<real> \<longrightarrow> 
      (y \<in> \<real> \<longrightarrow> 
      y \<in> A \<longrightarrow> \<not>(y \<ls> (\<cn>v))) \<longleftrightarrow> 
      (y \<in> A \<longrightarrow> \<not>(y \<ls> (\<cn>v)))" by (rule MMI_syl6rbb)
    from S68 have S69: "A \<subseteq>\<real> \<longrightarrow> 
      (\<forall>y. y \<in> \<real> \<longrightarrow> 
      y \<in> A \<longrightarrow> \<not>(y \<ls> (\<cn>v))) \<longleftrightarrow> 
      (\<forall>y. y \<in> A \<longrightarrow> \<not>(y \<ls> (\<cn>v)))" by auto (*rule MMI_albidv*)
    { fix u
      have "u \<in> \<real> \<longrightarrow> (\<cn>u) \<in> \<real>" by (rule MMI_renegclt)
    } then have S70: "\<forall> u. u \<in> \<real> \<longrightarrow> (\<cn>u) \<in> \<real>" by simp
    { fix y
      have "y \<in> \<real> \<longrightarrow> ( \<exists>u\<in>\<real>. y = (\<cn>u))" by (rule MMI_infm3lem)
    } then have S71: "\<forall> y. y \<in> \<real> \<longrightarrow> ( \<exists>u\<in>\<real>. y = (\<cn>u))" by simp
    { fix y u
      have S72: "y = (\<cn>u) \<longrightarrow> 
	y \<in> A \<longleftrightarrow> (\<cn>u) \<in> A" by (rule MMI_eleq1)
      have S73: "y = (\<cn>u) \<longrightarrow> 
	y \<ls> (\<cn>v) \<longleftrightarrow> (\<cn>u) \<ls> (\<cn>v)" by (rule MMI_breq1)
      from S73 have S74: "y = (\<cn>u) \<longrightarrow> 
	\<not>(y \<ls> (\<cn>v)) \<longleftrightarrow> 
	\<not>((\<cn>u) \<ls> (\<cn>v))" by (rule MMI_negbid)
      from S72 S74 have S75: "y = (\<cn>u) \<longrightarrow> 
	(y \<in> A \<longrightarrow> \<not>(y \<ls> (\<cn>v))) \<longleftrightarrow> 
	((\<cn>u) \<in> A \<longrightarrow> 
	\<not>((\<cn>u) \<ls> (\<cn>v)))" by (rule MMI_imbi12d)
    } then have S75: "\<forall>y u. y = (\<cn>u) \<longrightarrow> 
	(y \<in> A \<longrightarrow> \<not>(y \<ls> (\<cn>v))) \<longleftrightarrow> ((\<cn>u) \<in> A \<longrightarrow>  \<not>((\<cn>u) \<ls> (\<cn>v)))" 
      by simp
    from S70 S71 S75 have S76: "(\<forall>y\<in>\<real>. y \<in> A \<longrightarrow> \<not>(y \<ls> (\<cn>v))) \<longleftrightarrow> 
      (\<forall>u\<in>\<real>. (\<cn>u) \<in> A \<longrightarrow> 
      \<not>((\<cn>u) \<ls> (\<cn>v)))" by (rule MMI_ralxfr)
    have S77: "(\<forall>y\<in>\<real>. y \<in> A \<longrightarrow> \<not>(y \<ls> (\<cn>v))) \<longleftrightarrow> 
      (\<forall>y. y \<in> \<real> \<longrightarrow> 
      y \<in> A \<longrightarrow> \<not>(y \<ls> (\<cn>v)))" by (rule MMI_df_ral)
    from S76 S77 have S78: "(\<forall>u\<in>\<real>. (\<cn>u) \<in> A \<longrightarrow> 
      \<not>((\<cn>u) \<ls> (\<cn>v))) \<longleftrightarrow> 
      (\<forall>y. y \<in> \<real> \<longrightarrow> 
      y \<in> A \<longrightarrow> \<not>(y \<ls> (\<cn>v)))" by (rule MMI_bitr3)
    have S79: "(\<forall>y\<in>A. \<not>(y \<ls> (\<cn>v))) \<longleftrightarrow> 
      (\<forall>y. y \<in> A \<longrightarrow> \<not>(y \<ls> (\<cn>v)))" by (rule MMI_df_ral)
    from S69 S78 S79 have S80: "A \<subseteq>\<real> \<longrightarrow> 
      (\<forall>u\<in>\<real>. (\<cn>u) \<in> A \<longrightarrow> 
      \<not>((\<cn>u) \<ls> (\<cn>v))) \<longleftrightarrow> 
      (\<forall>y\<in>A. \<not>(y \<ls> (\<cn>v)))" by (rule MMI_3bitr4g)
    { fix u
      have S81: "A \<subseteq>\<real> \<longrightarrow> 
	w \<in> A \<longrightarrow> w \<in> \<real>" by (rule MMI_ssel)
      from S81 have S82: "A \<subseteq>\<real> \<longrightarrow> 
	w \<in> A \<and> w \<ls> (\<cn>u) \<longrightarrow> w \<in> \<real>" by (rule MMI_adantrd)
      from S82 have S83: "A \<subseteq>\<real> \<longrightarrow> 
	w \<in> A \<and> w \<ls> (\<cn>u) \<longleftrightarrow> 
	w \<in> \<real> \<and> w \<in> A \<and> w \<ls> (\<cn>u)" by (rule MMI_pm4_71rd)
      from S83 have S84: "A \<subseteq>\<real> \<longrightarrow> 
	( \<exists>w. w \<in> A \<and> w \<ls> (\<cn>u)) \<longleftrightarrow> 
	( \<exists>w. w \<in> \<real> \<and> w \<in> A \<and> w \<ls> (\<cn>u))" by auto (*rule MMI_exbidv*)
      have S85: "( \<exists>w\<in>A. w \<ls> (\<cn>u)) \<longleftrightarrow> 
	( \<exists>w. w \<in> A \<and> w \<ls> (\<cn>u))" by (rule MMI_df_rex)
      { fix t
	have S86: "t \<in> \<real> \<longrightarrow> (\<cn>t) \<in> \<real>" by (rule MMI_renegclt)
      } then have S86: "\<forall> t. t \<in> \<real> \<longrightarrow> (\<cn>t) \<in> \<real>" by simp
      { fix w
	have S87: "w \<in> \<real> \<longrightarrow> ( \<exists>t\<in>\<real>. w = (\<cn>t))" by (rule MMI_infm3lem)
      } then have S87: "\<forall> w. w \<in> \<real> \<longrightarrow> ( \<exists>t\<in>\<real>. w = (\<cn>t))" by simp
      { fix w t
	have S88: "w = (\<cn>t) \<longrightarrow> 
	  w \<in> A \<longleftrightarrow> (\<cn>t) \<in> A" by (rule MMI_eleq1)
	have S89: "w = (\<cn>t) \<longrightarrow> 
	  w \<ls> (\<cn>u) \<longleftrightarrow> (\<cn>t) \<ls> (\<cn>u)" by (rule MMI_breq1)
	from S88 S89 have S90: "w = (\<cn>t) \<longrightarrow> 
	  w \<in> A \<and> w \<ls> (\<cn>u) \<longleftrightarrow> 
	  (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u)" by (rule MMI_anbi12d)
      } then have  S90: "\<forall> w t. w = (\<cn>t) \<longrightarrow>  w \<in> A \<and> w \<ls> (\<cn>u) \<longleftrightarrow> 
	  (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u)" by simp
      from S86 S87 S90 have S91: "( \<exists>w\<in>\<real>. w \<in> A \<and> w \<ls> (\<cn>u)) \<longleftrightarrow> 
	( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u))" by (rule MMI_rexxfr)
      have S92: "( \<exists>w\<in>\<real>. w \<in> A \<and> w \<ls> (\<cn>u)) \<longleftrightarrow> 
	( \<exists>w. w \<in> \<real> \<and> w \<in> A \<and> w \<ls> (\<cn>u))" by (rule MMI_df_rex)
      from S91 S92 have S93: "( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u)) \<longleftrightarrow> 
	( \<exists>w. w \<in> \<real> \<and> w \<in> A \<and> w \<ls> (\<cn>u))" by (rule MMI_bitr3)
      from S84 S85 S93 have S94: "A \<subseteq>\<real> \<longrightarrow> 
	( \<exists>w\<in>A. w \<ls> (\<cn>u)) \<longleftrightarrow> 
	( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u))" by (rule MMI_3bitr4g)
      from S94 have "A \<subseteq>\<real> \<longrightarrow> 
	((\<cn>v) \<ls> (\<cn>u) \<longrightarrow> 
	( \<exists>w\<in>A. w \<ls> (\<cn>u))) \<longleftrightarrow> 
	((\<cn>v) \<ls> (\<cn>u) \<longrightarrow> 
	( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u)))" by (rule MMI_imbi2d)
    } then have S95: "\<forall> u. A \<subseteq>\<real> \<longrightarrow> 
	((\<cn>v) \<ls> (\<cn>u) \<longrightarrow> 
	( \<exists>w\<in>A. w \<ls> (\<cn>u))) \<longleftrightarrow> 
       ((\<cn>v) \<ls> (\<cn>u) \<longrightarrow> 
	( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u)))" by simp
    from S95 have S96: "A \<subseteq>\<real> \<longrightarrow> 
      (\<forall>u\<in>\<real>. (\<cn>v) \<ls> (\<cn>u) \<longrightarrow> 
      ( \<exists>w\<in>A. w \<ls> (\<cn>u))) \<longleftrightarrow> 
      (\<forall>u\<in>\<real>. (\<cn>v) \<ls> (\<cn>u) \<longrightarrow> 
      ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u)))" by (rule MMI_ralbidv)
    from S70 have S97: "\<forall> u. u \<in> \<real> \<longrightarrow> (\<cn>u) \<in> \<real>" .
    from S71 have S98: "\<forall> y. y \<in> \<real> \<longrightarrow> ( \<exists>u\<in>\<real>. y = (\<cn>u))" .
    { fix y u
      have S99: "y = (\<cn>u) \<longrightarrow> 
	(\<cn>v) \<ls> y \<longleftrightarrow> (\<cn>v) \<ls> (\<cn>u)" by (rule MMI_breq2)
      { fix w
	have "y = (\<cn>u) \<longrightarrow> 
	  w \<ls> y \<longleftrightarrow> w \<ls> (\<cn>u)" by (rule MMI_breq2)
      } then have S100: "\<forall> w. y = (\<cn>u) \<longrightarrow> 
	  w \<ls> y \<longleftrightarrow> w \<ls> (\<cn>u)" by simp
      from S100 have S101: "y = (\<cn>u) \<longrightarrow> 
	( \<exists>w\<in>A. w \<ls> y) \<longleftrightarrow> 
	( \<exists>w\<in>A. w \<ls> (\<cn>u))" by (rule MMI_rexbidv)
     from S99 S101 have "y = (\<cn>u) \<longrightarrow> 
       ((\<cn>v) \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)) \<longleftrightarrow> 
       ((\<cn>v) \<ls> (\<cn>u) \<longrightarrow> 
       ( \<exists>w\<in>A. w \<ls> (\<cn>u)))" by (rule MMI_imbi12d)
   } then have S102: "\<forall> y u. y = (\<cn>u) \<longrightarrow> 
       ((\<cn>v) \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)) \<longleftrightarrow> 
       ((\<cn>v) \<ls> (\<cn>u) \<longrightarrow> 
       ( \<exists>w\<in>A. w \<ls> (\<cn>u)))" by simp
   from S97 S98 S102 have S103: "(\<forall>y\<in>\<real>. (\<cn>v) \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)) \<longleftrightarrow> 
     (\<forall>u\<in>\<real>. (\<cn>v) \<ls> (\<cn>u) \<longrightarrow> 
     ( \<exists>w\<in>A. w \<ls> (\<cn>u)))" by (rule MMI_ralxfr)
   from S96 S103 have S104: "A \<subseteq>\<real> \<longrightarrow> 
     (\<forall>u\<in>\<real>. (\<cn>v) \<ls> (\<cn>u) \<longrightarrow> 
     ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u))) \<longleftrightarrow> 
     (\<forall>y\<in>\<real>. (\<cn>v) \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))" by (rule MMI_syl5rbb)
   from S80 S104 have S105: "A \<subseteq>\<real> \<longrightarrow> 
     (\<forall>u\<in>\<real>. (\<cn>u) \<in> A \<longrightarrow> 
     \<not>((\<cn>u) \<ls> (\<cn>v))) \<and> (\<forall>u\<in>\<real>. (\<cn>v) \<ls> (\<cn>u) \<longrightarrow> 
     ( \<exists>t\<in>\<real>. (\<cn>t) \<in> A \<and> (\<cn>t) \<ls> (\<cn>u))) \<longleftrightarrow> 
     (\<forall>y\<in>A. \<not>(y \<ls> (\<cn>v))) \<and> (\<forall>y\<in>\<real>. (\<cn>v) \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))" 
     by (rule MMI_anbi12d)
   from S63 S105 have S106: "A \<subseteq>\<real> \<and> v \<in> \<real> \<longrightarrow> 
     (\<forall>u\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. \<not>(v \<ls> u)) \<and> (\<forall>u\<in>\<real>. u \<ls> v \<longrightarrow> 
     ( \<exists>t\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. u \<ls> t)) \<longleftrightarrow> 
     (\<forall>y\<in>A. \<not>(y \<ls> (\<cn>v))) \<and> (\<forall>y\<in>\<real>. (\<cn>v) \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))" 
     by (rule MMI_sylan9bbr)
   from S106 have S107: "A \<subseteq>\<real> \<longrightarrow>  v \<in> \<real> \<longrightarrow> 
     (\<forall>u\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. \<not>(v \<ls> u)) \<and> (\<forall>u\<in>\<real>. u \<ls> v \<longrightarrow> 
     ( \<exists>t\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. u \<ls> t)) \<longleftrightarrow> 
     (\<forall>y\<in>A. \<not>(y \<ls> (\<cn>v))) \<and> (\<forall>y\<in>\<real>. (\<cn>v) \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))" 
     by (rule MMI_ex)
 } then have S107: "\<forall> v. A \<subseteq>\<real> \<longrightarrow>  v \<in> \<real> \<longrightarrow> 
     (\<forall>u\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. \<not>(v \<ls> u)) \<and> (\<forall>u\<in>\<real>. u \<ls> v \<longrightarrow> 
     ( \<exists>t\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. u \<ls> t)) \<longleftrightarrow> 
     (\<forall>y\<in>A. \<not>(y \<ls> (\<cn>v))) \<and> (\<forall>y\<in>\<real>. (\<cn>v) \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))"
   by simp
   from S107 have S108: "A \<subseteq>\<real> \<longrightarrow> 
     {v \<in> \<real>. (\<forall>u\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. \<not>(v \<ls> u)) \<and> (\<forall>u\<in>\<real>. u \<ls> v \<longrightarrow> 
     ( \<exists>t\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. u \<ls> t)) } = 
     {v \<in> \<real>. (\<forall>y\<in>A. \<not>(y \<ls> (\<cn>v))) \<and> (\<forall>y\<in>\<real>. (\<cn>v) \<ls> y \<longrightarrow> 
     ( \<exists>w\<in>A. w \<ls> y)) }" by (rule MMI_rabbidv)
   from S108 have S109: "A \<subseteq>\<real> \<longrightarrow>  
     \<Union> {v \<in> \<real>. (\<forall>u\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. \<not>(v \<ls> u)) \<and> (\<forall>u\<in>\<real>. u \<ls> v \<longrightarrow> 
     ( \<exists>t\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. u \<ls> t)) } = 
     \<Union> {v \<in> \<real>. (\<forall>y\<in>A. \<not>(y \<ls> (\<cn>v))) \<and> 
     (\<forall>y\<in>\<real>. (\<cn>v) \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)) }" by (rule MMI_unieqd)
   have S110: "Sup({z \<in> \<real>. (\<cn>z) \<in> A },\<real>,\<cltrrset>) = 
     \<Union> {v \<in> \<real>. (\<forall>u\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. \<not>(v \<ls> u)) \<and> (\<forall>u\<in>\<real>. u \<ls> v \<longrightarrow> 
     ( \<exists>t\<in>{z \<in> \<real>. (\<cn>z) \<in> A }. u \<ls> t)) }" by (rule MMI_df_sup)
   from S109 S110 have S111: "A \<subseteq>\<real> \<longrightarrow> Sup({z \<in> \<real>. (\<cn>z) \<in> A },\<real>,\<cltrrset>) = 
     \<Union> {v \<in> \<real>. (\<forall>y\<in>A. \<not>(y \<ls> (\<cn>v))) \<and> 
     (\<forall>y\<in>\<real>. (\<cn>v) \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)) }" by (rule MMI_syl5eq)
   from S111 have S112: "A \<subseteq>\<real> \<longrightarrow> 
     (\<cn>Sup({z \<in> \<real>. (\<cn>z) \<in> A },\<real>,\<cltrrset>)) = 
     (\<cn>(\<Union> {v \<in> \<real>. (\<forall>y\<in>A. \<not>(y \<ls> (\<cn>v))) \<and> 
     (\<forall>y\<in>\<real>. (\<cn>v) \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)) }))" by (rule MMI_negeqd)
   from S112 have S113: "A \<subseteq>\<real> \<longrightarrow> 
   (\<cn>(\<Union> {v \<in> \<real>. (\<forall>y\<in>A. \<not>(y \<ls> (\<cn>v))) \<and> 
     (\<forall>y\<in>\<real>. (\<cn>v) \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)) })) = 
     (\<cn>Sup({z \<in> \<real>. (\<cn>z) \<in> A },\<real>,\<cltrrset>))" by (rule MMI_eqcomd)
   from S31 S113 have S114: "A \<subseteq>\<real> \<and> (\<exists>!x. x\<in>\<real> \<and> (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> 
     (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))) \<longrightarrow> 
     Sup(A,\<real>,converse(\<cltrrset>)) = (\<cn>Sup({z \<in> \<real>. (\<cn>z) \<in> A },\<real>,\<cltrrset>))" 
     by (rule MMI_sylan9eqr)
   from S114 have S115: "A \<subseteq>\<real> \<longrightarrow> 
   (\<exists>!x. x\<in>\<real> \<and> (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))) \<longrightarrow> 
   Sup(A,\<real>,converse(\<cltrrset>)) = (\<cn>Sup({z \<in> \<real>. (\<cn>z) \<in> A },\<real>,\<cltrrset>))" 
     by (rule MMI_ex)
   have S116: "\<cltrrset> Orders \<real>" by (rule MMI_ltso)
   have S117: "\<cltrrset> Orders \<real> \<longleftrightarrow> converse(\<cltrrset>) Orders \<real>" by (rule MMI_cnvso)
   from S116 S117 have S118: "converse(\<cltrrset>) Orders \<real>" by (rule MMI_mpbi)
   from S118 have S119: 
     "( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>w\<in>A. y > w))) \<longrightarrow> 
     (\<exists>!x. x\<in>\<real> \<and> (\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>w\<in>A. y > w)))" 
     by (rule MMI_infeu)
   (*from S26 have S120: "(\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>w\<in>A. y > w)) \<longleftrightarrow> 
     (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))" .;*)
   from (*S120*) S26 have S121: 
     "( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>w\<in>A. y > w))) \<longleftrightarrow> 
     ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)))" 
     by (rule MMI_rexbii)
   from S26 have S122: "\<forall> x. (\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>w\<in>A. y > w)) \<longleftrightarrow> 
   (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))" .
   from S122 have S123: 
     "(\<exists>!x. x\<in>\<real> \<and> (\<forall>y\<in>A. \<not>(x > y)) \<and> (\<forall>y\<in>\<real>. y > x \<longrightarrow> ( \<exists>w\<in>A. y > w))) \<longleftrightarrow> 
   (\<exists>!x. x\<in>\<real> \<and> (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)))" 
     by (rule MMI_reubii)
   from S119 S121 S123 have S124: 
     "( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))) \<longrightarrow> 
   (\<exists>!x. x\<in>\<real> \<and> (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y)))" 
     by (rule MMI_3imtr3)
   from S115 S124 have S125: "A \<subseteq>\<real> \<longrightarrow> 
   ( \<exists>x\<in>\<real>. (\<forall>y\<in>A. \<not>(y \<ls> x)) \<and> (\<forall>y\<in>\<real>. x \<ls> y \<longrightarrow> ( \<exists>w\<in>A. w \<ls> y))) \<longrightarrow> 
   Sup(A,\<real>,converse(\<cltrrset>)) = (\<cn>Sup({z \<in> \<real>. (\<cn>z) \<in> A },\<real>,\<cltrrset>))" 
     by (rule MMI_syl5)
   from S2 S125 have S126: "A \<subseteq>\<real> \<longrightarrow> 
   \<not>(A = 0) \<longrightarrow> 
   ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
   Sup(A,\<real>,converse(\<cltrrset>)) = (\<cn>Sup({z \<in> \<real>. (\<cn>z) \<in> A },\<real>,\<cltrrset>))" 
     by (rule MMI_syl6d)
   from S126 show "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
   Sup(A,\<real>,converse(\<cltrrset>)) = (\<cn>Sup({z \<in> \<real>. (\<cn>z) \<in> A },\<real>,\<cltrrset>))" 
     by (rule MMI_3imp)
qed

lemma (in MMIsar0) MMI_infmrcl: 
   shows "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
   Sup(A,\<real>,converse(\<cltrrset>)) \<in> \<real>"
proof -
   have S1: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
   Sup(A,\<real>,converse(\<cltrrset>)) = (\<cn>Sup({v \<in> \<real>. (\<cn>v) \<in> A },\<real>,\<cltrrset>))" 
     by (rule MMI_infmsup)
   have S2: "{v \<in> \<real>. (\<cn>v) \<in> A } \<subseteq>\<real>" by (rule MMI_ssrab2)
   have S3: "{v \<in> \<real>. (\<cn>v) \<in> A } \<subseteq>\<real> \<and> \<not>({v \<in> \<real>. (\<cn>v) \<in> A } = 0) \<and> 
     ( \<exists>z\<in>\<real>. \<forall>w\<in>{v \<in> \<real>. (\<cn>v) \<in> A }. w \<lsq> z) \<longrightarrow> 
     Sup({v \<in> \<real>. (\<cn>v) \<in> A },\<real>,\<cltrrset>) \<in> \<real>" by (rule MMI_suprcl)
   from S2 S3 have S4: "\<not>({v \<in> \<real>. (\<cn>v) \<in> A } = 0) \<and> 
     ( \<exists>z\<in>\<real>. \<forall>w\<in>{v \<in> \<real>. (\<cn>v) \<in> A }. w \<lsq> z) \<longrightarrow> 
     Sup({v \<in> \<real>. (\<cn>v) \<in> A },\<real>,\<cltrrset>) \<in> \<real>" by (rule MMI_mp3an1)
   { fix z
     have S5: "A \<subseteq>\<real> \<longrightarrow> 
       z \<in> A \<longrightarrow> z \<in> \<real>" by (rule MMI_ssel)
     have S6: "z \<in> \<real> \<longrightarrow> (\<cn>z) \<in> \<real>" by (rule MMI_renegclt)
     from S5 S6 have S7: "A \<subseteq>\<real> \<longrightarrow> 
       z \<in> A \<longrightarrow> (\<cn>z) \<in> \<real>" by (rule MMI_syl6)
     have S8: "A \<subseteq>\<real> \<and> z \<in> A \<longrightarrow> z \<in> \<real>" by (rule MMI_ssel2)
     have S9: "z \<in> \<real> \<longrightarrow> z \<in> \<complex>" by (rule MMI_recnt)
     have S10: "z \<in> \<complex> \<longrightarrow> (\<cn>(\<cn>z)) = z" by (rule MMI_negnegt)
     from S8 S9 S10 have S11: "A \<subseteq>\<real> \<and> z \<in> A \<longrightarrow> (\<cn>(\<cn>z)) = z" by (rule MMI_3syl)
     have S12: "A \<subseteq>\<real> \<and> z \<in> A \<longrightarrow> z \<in> A" by (rule MMI_pm3_27)
     from S11 S12 have S13: "A \<subseteq>\<real> \<and> z \<in> A \<longrightarrow> (\<cn>(\<cn>z)) \<in> A" by (rule MMI_eqeltrd)
     from S13 have S14: "A \<subseteq>\<real> \<longrightarrow> 
       z \<in> A \<longrightarrow> (\<cn>(\<cn>z)) \<in> A" by (rule MMI_ex)
     from S7 S14 have S15: "A \<subseteq>\<real> \<longrightarrow> 
       z \<in> A \<longrightarrow> 
       (\<cn>z) \<in> \<real> \<and> (\<cn>(\<cn>z)) \<in> A" by (rule MMI_jcad)
     have S16: "v = (\<cn>z) \<longrightarrow> (\<cn>v) = (\<cn>(\<cn>z))" by (rule MMI_negeq)
     from S16 have S17: "v = (\<cn>z) \<longrightarrow> 
       (\<cn>v) \<in> A \<longleftrightarrow> (\<cn>(\<cn>z)) \<in> A" by (rule MMI_eleq1d)
     from S17 have S18: "(\<cn>z) \<in> {v \<in> \<real>. (\<cn>v) \<in> A } \<longleftrightarrow> 
       (\<cn>z) \<in> \<real> \<and> (\<cn>(\<cn>z)) \<in> A" by auto (*rule MMI_elrab*)
     have S19: "(\<cn>z) \<in> {v \<in> \<real>. (\<cn>v) \<in> A } \<longrightarrow> 
       \<not>({v \<in> \<real>. (\<cn>v) \<in> A } = 0)" by (rule MMI_n0i)
     from S18 S19 have S20: "(\<cn>z) \<in> \<real> \<and> (\<cn>(\<cn>z)) \<in> A \<longrightarrow> 
       \<not>({v \<in> \<real>. (\<cn>v) \<in> A } = 0)" by (rule MMI_sylbir)
     from S15 S20 have "A \<subseteq>\<real> \<longrightarrow> z \<in> A \<longrightarrow> 
       \<not>({v \<in> \<real>. (\<cn>v) \<in> A } = 0)" by (rule MMI_syl6)
   } then have S21: "\<forall> z. A \<subseteq>\<real> \<longrightarrow>  z \<in> A \<longrightarrow> 
       \<not>({v \<in> \<real>. (\<cn>v) \<in> A } = 0)" by simp
   from S21 have S22: "A \<subseteq>\<real> \<longrightarrow> ( \<exists>z. z \<in> A) \<longrightarrow> 
     \<not>({v \<in> \<real>. (\<cn>v) \<in> A } = 0)" by (rule MMI_19_23adv)
   from S22 have S23: "A \<subseteq>\<real> \<and> ( \<exists>z. z \<in> A) \<longrightarrow> 
     \<not>({v \<in> \<real>. (\<cn>v) \<in> A } = 0)" by (rule MMI_imp)
   have S24: "\<not>(A = 0) \<longleftrightarrow> ( \<exists>z. z \<in> A)" by (rule MMI_n0)
   from S23 S24 have S25: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<longrightarrow> 
     \<not>({v \<in> \<real>. (\<cn>v) \<in> A } = 0)" by (rule MMI_sylan2b)
   from S25 have S26: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
     \<not>({v \<in> \<real>. (\<cn>v) \<in> A } = 0)" by (rule MMI_3adant3)
   { fix x
     { fix w
       have S27: "y = (\<cn>w) \<longrightarrow> 
	 x \<lsq> y \<longleftrightarrow> x \<lsq> (\<cn>w)" by (rule MMI_breq2)
       from S27 have S28: "(\<cn>w) \<in> A \<and> (\<forall>y\<in>A. x \<lsq> y) \<longrightarrow> x \<lsq> (\<cn>w)" 
	 by auto (*rule MMI_rcla4va*)
       from S28 have S29: 
	 "(w \<in> \<real> \<and> (\<cn>w) \<in> A) \<and> (\<forall>y\<in>A. x \<lsq> y) \<longrightarrow> x \<lsq> (\<cn>w)" 
	 by (rule MMI_adantll)
       from S29 have S30: 
	 "(x \<in> \<real> \<and> w \<in> \<real> \<and> (\<cn>w) \<in> A) \<and> (\<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
	 x \<lsq> (\<cn>w)" by (rule MMI_adantll)
       have S31: "x \<in> \<real> \<and> w \<in> \<real> \<longrightarrow> 
	 x \<lsq> (\<cn>w) \<longleftrightarrow> w \<lsq> (\<cn>x)" by (rule MMI_lenegcon2t)
       from S31 have S32: "x \<in> \<real> \<and> w \<in> \<real> \<and> (\<cn>w) \<in> A \<longrightarrow> 
	 x \<lsq> (\<cn>w) \<longleftrightarrow> w \<lsq> (\<cn>x)" by (rule MMI_adantrr)
       from S32 have S33: "(x \<in> \<real> \<and> w \<in> \<real> \<and> (\<cn>w) \<in> A) \<and> (\<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
	 x \<lsq> (\<cn>w) \<longleftrightarrow> w \<lsq> (\<cn>x)" by (rule MMI_adantr)
       from S30 S33 have S34: 
	 "(x \<in> \<real> \<and> w \<in> \<real> \<and> (\<cn>w) \<in> A) \<and> (\<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
	 w \<lsq> (\<cn>x)" by (rule MMI_mpbid)
       from S34 have S35: "x \<in> \<real> \<longrightarrow> 
	 w \<in> \<real> \<and> (\<cn>w) \<in> A \<longrightarrow> 
	 (\<forall>y\<in>A. x \<lsq> y) \<longrightarrow> w \<lsq> (\<cn>x)" by (rule MMI_exp31)
       have S36: "v = w \<longrightarrow> (\<cn>v) = (\<cn>w)" by (rule MMI_negeq)
       from S36 have S37: "v = w \<longrightarrow> 
	 (\<cn>v) \<in> A \<longleftrightarrow> (\<cn>w) \<in> A" by (rule MMI_eleq1d)
       from S37 have S38: "w \<in> {v \<in> \<real>. (\<cn>v) \<in> A } \<longleftrightarrow> 
	 w \<in> \<real> \<and> (\<cn>w) \<in> A" by auto (*rule MMI_elrab*)
       from S35 S38 have S39: "x \<in> \<real> \<longrightarrow> 
	 w \<in> {v \<in> \<real>. (\<cn>v) \<in> A } \<longrightarrow> 
	 (\<forall>y\<in>A. x \<lsq> y) \<longrightarrow> w \<lsq> (\<cn>x)" by (rule MMI_syl5ib)
       from S39 have S40: "x \<in> \<real> \<longrightarrow> 
	 (\<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
	 w \<in> {v \<in> \<real>. (\<cn>v) \<in> A } \<longrightarrow> w \<lsq> (\<cn>x)" by (rule MMI_com23)
     } then have S40: "x \<in> \<real> \<longrightarrow>  (\<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
	 (\<forall> w. w \<in> {v \<in> \<real>. (\<cn>v) \<in> A } \<longrightarrow> w \<lsq> (\<cn>x))" by simp
     from S40 have S41: "x \<in> \<real> \<longrightarrow> 
       (\<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
       (\<forall>w\<in>{v \<in> \<real>. (\<cn>v) \<in> A }. w \<lsq> (\<cn>x))" by auto (*rule MMI_r19_21adv*)
     have S42: "x \<in> \<real> \<longrightarrow> (\<cn>x) \<in> \<real>" by (rule MMI_renegclt)
     from S41 S42 have S43: "x \<in> \<real> \<longrightarrow> 
       (\<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
       (\<cn>x) \<in> \<real> \<and> (\<forall>w\<in>{v \<in> \<real>. (\<cn>v) \<in> A }. w \<lsq> (\<cn>x))" by (rule MMI_jctild)
     have S44: "z = (\<cn>x) \<longrightarrow> 
       w \<lsq> z \<longleftrightarrow> w \<lsq> (\<cn>x)" by (rule MMI_breq2)
     from S44 have S45: "z = (\<cn>x) \<longrightarrow> 
       (\<forall>w\<in>{v \<in> \<real>. (\<cn>v) \<in> A }. w \<lsq> z) \<longleftrightarrow> 
       (\<forall>w\<in>{v \<in> \<real>. (\<cn>v) \<in> A }. w \<lsq> (\<cn>x))" by auto (*rule MMI_ralbidv*)
     from S45 have S46: "(\<cn>x) \<in> \<real> \<and> (\<forall>w\<in>{v \<in> \<real>. (\<cn>v) \<in> A }. w \<lsq> (\<cn>x)) \<longrightarrow> 
       ( \<exists>z\<in>\<real>. \<forall>w\<in>{v \<in> \<real>. (\<cn>v) \<in> A }. w \<lsq> z)" by auto (*rule MMI_rcla4ev*)
     from S43 S46 have "x \<in> \<real> \<longrightarrow> 
       (\<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
       ( \<exists>z\<in>\<real>. \<forall>w\<in>{v \<in> \<real>. (\<cn>v) \<in> A }. w \<lsq> z)" by (rule MMI_syl6)
   } then have S47: "\<forall> x. x \<in> \<real> \<longrightarrow> (\<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
       ( \<exists>z\<in>\<real>. \<forall>w\<in>{v \<in> \<real>. (\<cn>v) \<in> A }. w \<lsq> z)"
     by simp
   from S47 have S48: "( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
     ( \<exists>z\<in>\<real>. \<forall>w\<in>{v \<in> \<real>. (\<cn>v) \<in> A }. w \<lsq> z)" by (rule MMI_r19_23aiv)
   from S48 have S49: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
     ( \<exists>z\<in>\<real>. \<forall>w\<in>{v \<in> \<real>. (\<cn>v) \<in> A }. w \<lsq> z)" by (rule MMI_3ad2ant3)
   from S4 S26 S49 have S50: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
     Sup({v \<in> \<real>. (\<cn>v) \<in> A },\<real>,\<cltrrset>) \<in> \<real>" by (rule MMI_sylanc)
   have S51: "Sup({v \<in> \<real>. (\<cn>v) \<in> A },\<real>,\<cltrrset>) \<in> \<real> \<longrightarrow> 
     (\<cn>Sup({v \<in> \<real>. (\<cn>v) \<in> A },\<real>,\<cltrrset>)) \<in> \<real>" by (rule MMI_renegclt)
   from S50 S51 have S52: "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
     (\<cn>Sup({v \<in> \<real>. (\<cn>v) \<in> A },\<real>,\<cltrrset>)) \<in> \<real>" by (rule MMI_syl)
   from S1 S52 show "A \<subseteq>\<real> \<and> \<not>(A = 0) \<and> ( \<exists>x\<in>\<real>. \<forall>y\<in>A. x \<lsq> y) \<longrightarrow> 
     Sup(A,\<real>,converse(\<cltrrset>)) \<in> \<real>" by (rule MMI_eqeltrd)
 qed
end
