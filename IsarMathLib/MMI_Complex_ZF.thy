
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

section \<open>Complex numbers in Metamatah - introduction\<close>

theory MMI_Complex_ZF imports MMI_logic_and_sets

begin 

text\<open>This theory contains theorems (with proofs) about complex numbers
  imported from the Metamath's set.mm database. 
  The original Metamath proofs were mostly written by Norman Megill, 
  see the Metamath Proof Explorer pages for full atribution.
  This theory contains about 200 theorems from "recnt" to "div11t".
\<close>

  lemma (in MMIsar0) MMI_recnt: 
   shows "A \<in> \<real> \<longrightarrow> A \<in> \<complex>"
proof -
   have S1: "\<real> \<subseteq> \<complex>" by (rule MMI_axresscn)
   from S1 show "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_sseli)
qed

lemma (in MMIsar0) MMI_recn: assumes A1: "A \<in> \<real>"   
   shows "A \<in> \<complex>"
proof -
   have S1: "\<real> \<subseteq> \<complex>" by (rule MMI_axresscn)
   from A1 have S2: "A \<in> \<real>".
   from S1 S2 show "A \<in> \<complex>" by (rule MMI_sselii)
qed

lemma (in MMIsar0) MMI_recnd: assumes A1: "\<phi> \<longrightarrow> A \<in> \<real>"   
   shows "\<phi> \<longrightarrow> A \<in> \<complex>"
proof -
   from A1 have S1: "\<phi> \<longrightarrow> A \<in> \<real>".
   have S2: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   from S1 S2 show "\<phi> \<longrightarrow> A \<in> \<complex>" by (rule MMI_syl)
qed

lemma (in MMIsar0) MMI_elimne0: 
   shows "if ( A \<noteq> \<zero> , A , \<one> ) \<noteq> \<zero>"
proof -
   have S1: "A = if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
     ( A \<noteq> \<zero> \<longleftrightarrow> if ( A \<noteq> \<zero> , A , \<one> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   have S2: "\<one> = if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
     ( \<one> \<noteq> \<zero> \<longleftrightarrow> if ( A \<noteq> \<zero> , A , \<one> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   have S3: "\<one> \<noteq> \<zero>" by (rule MMI_ax1ne0)
   from S1 S2 S3 show "if ( A \<noteq> \<zero> , A , \<one> ) \<noteq> \<zero>" by (rule MMI_elimhyp)
qed

lemma (in MMIsar0) MMI_addex: 
   shows "\<caddset> isASet"
proof -
   have S1: "\<complex> isASet" by (rule MMI_axcnex)
   have S2: "\<complex> isASet" by (rule MMI_axcnex)
   from S1 S2 have S3: "( \<complex> \<times> \<complex> ) isASet" by (rule MMI_xpex)
   have S4: "\<caddset> : ( \<complex> \<times> \<complex> ) \<rightarrow> \<complex>" by (rule MMI_axaddopr)
   have S5: "( \<complex> \<times> \<complex> ) isASet \<longrightarrow> 
     ( \<caddset> : ( \<complex> \<times> \<complex> ) \<rightarrow> \<complex> \<longrightarrow> \<caddset> isASet )" by (rule MMI_fex)
   from S3 S4 S5 show "\<caddset> isASet" by (rule MMI_mp2)
qed

lemma (in MMIsar0) MMI_mulex: 
   shows "\<cmulset> isASet"
proof -
   have S1: "\<complex> isASet" by (rule MMI_axcnex)
   have S2: "\<complex> isASet" by (rule MMI_axcnex)
   from S1 S2 have S3: "( \<complex> \<times> \<complex> ) isASet" by (rule MMI_xpex)
   have S4: "\<cmulset> : ( \<complex> \<times> \<complex> ) \<rightarrow> \<complex>" by (rule MMI_axmulopr)
   have S5: "( \<complex> \<times> \<complex> ) isASet \<longrightarrow> 
     ( \<cmulset> : ( \<complex> \<times> \<complex> ) \<rightarrow> \<complex> \<longrightarrow> \<cmulset> isASet )" by (rule MMI_fex)
   from S3 S4 S5 show "\<cmulset> isASet" by (rule MMI_mp2)
qed

lemma (in MMIsar0) MMI_adddirt: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
  ( ( A \<ca> B ) \<cdot> C ) = ( ( A \<cdot> C ) \<ca> ( B \<cdot> C ) )"
proof -
   have S1: "( C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
     ( C \<cdot> ( A \<ca> B ) ) = ( ( C \<cdot> A ) \<ca> ( C \<cdot> B ) )" 
     by (rule MMI_axdistr)
   from S1 have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( C \<cdot> ( A \<ca> B ) ) = ( ( C \<cdot> A ) \<ca> ( C \<cdot> B ) )" by (rule MMI_3coml)
   have S3: "( ( A \<ca> B ) \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cdot> C ) = ( C \<cdot> ( A \<ca> B ) )" by (rule MMI_axmulcom)
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> B ) \<in> \<complex>" by (rule MMI_axaddcl)
   from S3 S4 have S5: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cdot> C ) = ( C \<cdot> ( A \<ca> B ) )" by (rule MMI_sylan)
   from S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cdot> C ) = ( C \<cdot> ( A \<ca> B ) )" by (rule MMI_3impa)
   have S7: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cdot> C ) = ( C \<cdot> A )" 
     by (rule MMI_axmulcom)
   from S7 have S8: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cdot> C ) = ( C \<cdot> A )" 
     by (rule MMI_3adant2)
   have S9: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<cdot> C ) = ( C \<cdot> B )" 
     by (rule MMI_axmulcom)
   from S9 have S10: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<cdot> C ) = ( C \<cdot> B )" 
     by (rule MMI_3adant1)
   from S8 S10 have S11: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<cdot> C ) \<ca> ( B \<cdot> C ) ) = ( ( C \<cdot> A ) \<ca> ( C \<cdot> B ) )" 
     by (rule MMI_opreq12d)
   from S2 S6 S11 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cdot> C ) = ( ( A \<cdot> C ) \<ca> ( B \<cdot> C ) )" 
     by (rule MMI_3eqtr4d)
qed

lemma (in MMIsar0) MMI_addcl: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( A \<ca> B ) \<in> \<complex>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> B ) \<in> \<complex>" by (rule MMI_axaddcl)
   from S1 S2 S3 show "( A \<ca> B ) \<in> \<complex>" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_mulcl: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( A \<cdot> B ) \<in> \<complex>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cdot> B ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S1 S2 S3 show "( A \<cdot> B ) \<in> \<complex>" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_addcom: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( A \<ca> B ) = ( B \<ca> A )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> B ) = ( B \<ca> A )" 
     by (rule MMI_axaddcom)
   from S1 S2 S3 show "( A \<ca> B ) = ( B \<ca> A )" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_mulcom: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( A \<cdot> B ) = ( B \<cdot> A )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cdot> B ) = ( B \<cdot> A )" 
     by (rule MMI_axmulcom)
   from S1 S2 S3 show "( A \<cdot> B ) = ( B \<cdot> A )" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_addass: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( ( A \<ca> B ) \<ca> C ) = ( A \<ca> ( B \<ca> C ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<ca> C ) = 
     ( A \<ca> ( B \<ca> C ) )" by (rule MMI_axaddass)
   from S1 S2 S3 S4 show "( ( A \<ca> B ) \<ca> C ) = 
     ( A \<ca> ( B \<ca> C ) )" by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_mulass: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( ( A \<cdot> B ) \<cdot> C ) = ( A \<cdot> ( B \<cdot> C ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<cdot> B ) \<cdot> C ) = 
     ( A \<cdot> ( B \<cdot> C ) )" by (rule MMI_axmulass)
   from S1 S2 S3 S4 show "( ( A \<cdot> B ) \<cdot> C ) = ( A \<cdot> ( B \<cdot> C ) )" 
     by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_adddi: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( A \<cdot> ( B \<ca> C ) ) = ( ( A \<cdot> B ) \<ca> ( A \<cdot> C ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cdot> ( B \<ca> C ) ) = 
     ( ( A \<cdot> B ) \<ca> ( A \<cdot> C ) )" by (rule MMI_axdistr)
   from S1 S2 S3 S4 show "( A \<cdot> ( B \<ca> C ) ) = 
     ( ( A \<cdot> B ) \<ca> ( A \<cdot> C ) )" by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_adddir: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( ( A \<ca> B ) \<cdot> C ) = ( ( A \<cdot> C ) \<ca> ( B \<cdot> C ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<cdot> C ) = 
     ( ( A \<cdot> C ) \<ca> ( B \<cdot> C ) )" by (rule MMI_adddirt)
   from S1 S2 S3 S4 show "( ( A \<ca> B ) \<cdot> C ) = 
     ( ( A \<cdot> C ) \<ca> ( B \<cdot> C ) )" by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_1cn: 
   shows "\<one> \<in> \<complex>"
proof -
   have S1: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S1 show "\<one> \<in> \<complex>" by (rule MMI_recn)
qed

lemma (in MMIsar0) MMI_0cn: 
   shows "\<zero> \<in> \<complex>"
proof -
   have S1: "( ( \<i> \<cdot> \<i> ) \<ca> \<one> ) = \<zero>" by (rule MMI_axi2m1)
   have S2: "\<i> \<in> \<complex>" by (rule MMI_axicn)
   have S3: "\<i> \<in> \<complex>" by (rule MMI_axicn)
   from S2 S3 have S4: "( \<i> \<cdot> \<i> ) \<in> \<complex>" by (rule MMI_mulcl)
   have S5: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S4 S5 have S6: "( ( \<i> \<cdot> \<i> ) \<ca> \<one> ) \<in> \<complex>" by (rule MMI_addcl)
   from S1 S6 show "\<zero> \<in> \<complex>" by (rule MMI_eqeltrr)
qed

lemma (in MMIsar0) MMI_addid1: assumes A1: "A \<in> \<complex>"   
   shows "( A \<ca> \<zero> ) = A"
proof -
   from A1 have S1: "A \<in> \<complex>".
   have S2: "A \<in> \<complex> \<longrightarrow> ( A \<ca> \<zero> ) = A" by (rule MMI_ax0id)
   from S1 S2 show "( A \<ca> \<zero> ) = A" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_addid2: assumes A1: "A \<in> \<complex>"   
   shows "( \<zero> \<ca> A ) = A"
proof -
   have S1: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from A1 have S2: "A \<in> \<complex>".
   from S1 S2 have S3: "( \<zero> \<ca> A ) = ( A \<ca> \<zero> )" by (rule MMI_addcom)
   from A1 have S4: "A \<in> \<complex>".
   from S4 have S5: "( A \<ca> \<zero> ) = A" by (rule MMI_addid1)
   from S3 S5 show "( \<zero> \<ca> A ) = A" by (rule MMI_eqtr)
qed

(*-----------------------------------------------------------------*)


lemma (in MMIsar0) MMI_mulid1: assumes A1: "A \<in> \<complex>"   
   shows "( A \<cdot> \<one> ) = A"
proof -
   from A1 have S1: "A \<in> \<complex>".
   have S2: "A \<in> \<complex> \<longrightarrow> ( A \<cdot> \<one> ) = A" by (rule MMI_ax1id)
   from S1 S2 show "( A \<cdot> \<one> ) = A" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_mulid2: assumes A1: "A \<in> \<complex>"   
   shows "( \<one> \<cdot> A ) = A"
proof -
   have S1: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from A1 have S2: "A \<in> \<complex>".
   from S1 S2 have S3: "( \<one> \<cdot> A ) = ( A \<cdot> \<one> )" by (rule MMI_mulcom)
   from A1 have S4: "A \<in> \<complex>".
   from S4 have S5: "( A \<cdot> \<one> ) = A" by (rule MMI_mulid1)
   from S3 S5 show "( \<one> \<cdot> A ) = A" by (rule MMI_eqtr)
qed

lemma (in MMIsar0) MMI_negex: assumes A1: "A \<in> \<complex>"   
   shows "\<exists> x \<in> \<complex> . ( A \<ca> x ) = \<zero>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   have S2: "A \<in> \<complex> \<longrightarrow> ( \<exists> x \<in> \<complex> . ( A \<ca> x ) = \<zero> )" by (rule MMI_axnegex)
   from S1 S2 show "\<exists> x \<in> \<complex> . ( A \<ca> x ) = \<zero>" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_recex: assumes A1: "A \<in> \<complex>" and
    A2: "A \<noteq> \<zero>"   
   shows "\<exists> x \<in> \<complex> . ( A \<cdot> x ) = \<one>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "A \<noteq> \<zero>".
   have S3: "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> ( \<exists> x \<in> \<complex> . ( A \<cdot> x ) = \<one> )" 
     by (rule MMI_axrecex)
   from S1 S2 S3 show "\<exists> x \<in> \<complex> . ( A \<cdot> x ) = \<one>" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_readdcl: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "( A \<ca> B ) \<in> \<real>"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<ca> B ) \<in> \<real>" by (rule MMI_axaddrcl)
   from S1 S2 S3 show "( A \<ca> B ) \<in> \<real>" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_remulcl: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "( A \<cdot> B ) \<in> \<real>"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<cdot> B ) \<in> \<real>" by (rule MMI_axmulrcl)
   from S1 S2 S3 show "( A \<cdot> B ) \<in> \<real>" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_addcan: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( A \<ca> B ) = ( A \<ca> C ) \<longleftrightarrow> B = C"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from S1 have S2: "\<exists> x \<in> \<complex> . ( A \<ca> x ) = \<zero>" by (rule MMI_negex)
   from A1 have S3: "A \<in> \<complex>".
   from A2 have S4: "B \<in> \<complex>".
   { fix x
     have S5: "( x \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( x \<ca> A ) \<ca> B ) = 
       ( x \<ca> ( A \<ca> B ) )" by (rule MMI_axaddass)
     from S4 S5 have S6: "( x \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> ( ( x \<ca> A ) \<ca> B ) = 
       ( x \<ca> ( A \<ca> B ) )" by (rule MMI_mp3an3)
     from A3 have S7: "C \<in> \<complex>".
     have S8: "( x \<in> \<complex> \<and> A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( x \<ca> A ) \<ca> C ) = 
       ( x \<ca> ( A \<ca> C ) )" by (rule MMI_axaddass)
     from S7 S8 have S9: "( x \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> ( ( x \<ca> A ) \<ca> C ) = 
       ( x \<ca> ( A \<ca> C ) )" by (rule MMI_mp3an3)
     from S6 S9 have S10: "( x \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> 
       ( ( ( x \<ca> A ) \<ca> B ) = ( ( x \<ca> A ) \<ca> C ) \<longleftrightarrow> 
       ( x \<ca> ( A \<ca> B ) ) = ( x \<ca> ( A \<ca> C ) ) )" 
       by (rule MMI_eqeq12d)
     from S3 S10 have S11: "x \<in> \<complex> \<longrightarrow> ( ( ( x \<ca> A ) \<ca> B ) = 
       ( ( x \<ca> A ) \<ca> C ) \<longleftrightarrow> ( x \<ca> ( A \<ca> B ) ) = 
       ( x \<ca> ( A \<ca> C ) ) )" by (rule MMI_mpan2)
     have S12: "( A \<ca> B ) = ( A \<ca> C ) \<longrightarrow> ( x \<ca> ( A \<ca> B ) ) = 
       ( x \<ca> ( A \<ca> C ) )" by (rule MMI_opreq2)
     from S11 S12 have S13: "x \<in> \<complex> \<longrightarrow> ( ( A \<ca> B ) = ( A \<ca> C ) \<longrightarrow> 
       ( ( x \<ca> A ) \<ca> B ) = ( ( x \<ca> A ) \<ca> C ) )" 
       by (rule MMI_syl5bir)
     from S13 have S14: "( x \<in> \<complex> \<and> ( A \<ca> x ) = \<zero> ) \<longrightarrow> ( ( A \<ca> B ) = 
       ( A \<ca> C ) \<longrightarrow> ( ( x \<ca> A ) \<ca> B ) = 
       ( ( x \<ca> A ) \<ca> C ) )" by (rule MMI_adantr)
     from A1 have S15: "A \<in> \<complex>".
     have S16: "( A \<in> \<complex> \<and> x \<in> \<complex> ) \<longrightarrow> ( A \<ca> x ) = ( x \<ca> A )" 
       by (rule MMI_axaddcom)
     from S15 S16 have S17: "x \<in> \<complex> \<longrightarrow> ( A \<ca> x ) = ( x \<ca> A )" 
       by (rule MMI_mpan)
     from S17 have S18: "x \<in> \<complex> \<longrightarrow> ( ( A \<ca> x ) = \<zero> \<longleftrightarrow> 
       ( x \<ca> A ) = \<zero> )" by (rule MMI_eqeq1d)
     have S19: "( x \<ca> A ) = \<zero> \<longrightarrow> ( ( x \<ca> A ) \<ca> B ) = 
       ( \<zero> \<ca> B )" by (rule MMI_opreq1)
     from A2 have S20: "B \<in> \<complex>".
     from S20 have S21: "( \<zero> \<ca> B ) = B" by (rule MMI_addid2)
     from S19 S21 have S22: "( x \<ca> A ) = \<zero> \<longrightarrow> 
       ( ( x \<ca> A ) \<ca> B ) = B" by (rule MMI_syl6eq)
     have S23: "( x \<ca> A ) = \<zero> \<longrightarrow> ( ( x \<ca> A ) \<ca> C ) = 
       ( \<zero> \<ca> C )" by (rule MMI_opreq1)
     from A3 have S24: "C \<in> \<complex>".
     from S24 have S25: "( \<zero> \<ca> C ) = C" by (rule MMI_addid2)
     from S23 S25 have S26: "( x \<ca> A ) = \<zero> \<longrightarrow> 
       ( ( x \<ca> A ) \<ca> C ) = C" by (rule MMI_syl6eq)
     from S22 S26 have S27: "( x \<ca> A ) = \<zero> \<longrightarrow> 
       ( ( ( x \<ca> A ) \<ca> B ) = ( ( x \<ca> A ) \<ca> C ) \<longleftrightarrow> B = C )" 
       by (rule MMI_eqeq12d)
     from S18 S27 have S28: "x \<in> \<complex> \<longrightarrow> ( ( A \<ca> x ) = \<zero> \<longrightarrow> 
       ( ( ( x \<ca> A ) \<ca> B ) = ( ( x \<ca> A ) \<ca> C ) \<longleftrightarrow> B = C ) )" 
       by (rule MMI_syl6bi)
     from S28 have S29: "( x \<in> \<complex> \<and> ( A \<ca> x ) = \<zero> ) \<longrightarrow> 
       ( ( ( x \<ca> A ) \<ca> B ) = ( ( x \<ca> A ) \<ca> C ) \<longleftrightarrow> B = C )" 
       by (rule MMI_imp)
     from S14 S29 have S30: "( x \<in> \<complex> \<and> ( A \<ca> x ) = \<zero> ) \<longrightarrow> 
       ( ( A \<ca> B ) = ( A \<ca> C ) \<longrightarrow> B = C )" by (rule MMI_sylibd)
     from S30 have "x \<in> \<complex> \<longrightarrow> ( ( A \<ca> x ) = \<zero> \<longrightarrow> 
       ( ( A \<ca> B ) = ( A \<ca> C ) \<longrightarrow> B = C ) )" by (rule MMI_ex)
   } then have S31: "\<forall> x. (x \<in> \<complex> \<longrightarrow> ( ( A \<ca> x ) = \<zero> \<longrightarrow> 
       ( ( A \<ca> B ) = ( A \<ca> C ) \<longrightarrow> B = C ) ))" by auto
   from S31 have S32: "( \<exists> x \<in> \<complex> . ( A \<ca> x ) = \<zero> ) \<longrightarrow> 
     ( ( A \<ca> B ) = ( A \<ca> C ) \<longrightarrow> B = C )" by (rule MMI_r19_23aiv)
   from S2 S32 have S33: "( A \<ca> B ) = ( A \<ca> C ) \<longrightarrow> B = C" 
     by (rule MMI_ax_mp)
   have S34: "B = C \<longrightarrow> ( A \<ca> B ) = ( A \<ca> C )" by (rule MMI_opreq2)
   from S33 S34 show "( A \<ca> B ) = ( A \<ca> C ) \<longleftrightarrow> B = C" 
     by (rule MMI_impbi)
qed

lemma (in MMIsar0) MMI_addcan2: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( A \<ca> C ) = ( B \<ca> C ) \<longleftrightarrow> A = B"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A3 have S2: "C \<in> \<complex>".
   from S1 S2 have S3: "( A \<ca> C ) = ( C \<ca> A )" by (rule MMI_addcom)
   from A2 have S4: "B \<in> \<complex>".
   from A3 have S5: "C \<in> \<complex>".
   from S4 S5 have S6: "( B \<ca> C ) = ( C \<ca> B )" by (rule MMI_addcom)
   from S3 S6 have S7: "( A \<ca> C ) = ( B \<ca> C ) \<longleftrightarrow> 
     ( C \<ca> A ) = ( C \<ca> B )" by (rule MMI_eqeq12i)
   from A3 have S8: "C \<in> \<complex>".
   from A1 have S9: "A \<in> \<complex>".
   from A2 have S10: "B \<in> \<complex>".
   from S8 S9 S10 have S11: "( C \<ca> A ) = ( C \<ca> B ) \<longleftrightarrow> A = B" 
     by (rule MMI_addcan)
   from S7 S11 show "( A \<ca> C ) = ( B \<ca> C ) \<longleftrightarrow> A = B" by (rule MMI_bitr)
qed

lemma (in MMIsar0) MMI_addcant: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
  ( ( A \<ca> B ) = ( A \<ca> C ) \<longleftrightarrow> B = C )"
proof -
   have S1: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> ( A \<ca> B ) = ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B )" by (rule MMI_opreq1)
   have S2: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
     ( A \<ca> C ) = ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> C )" by (rule MMI_opreq1)
   from S1 S2 have S3: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
     ( ( A \<ca> B ) = ( A \<ca> C ) \<longleftrightarrow> 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B ) = ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> C ) )" 
     by (rule MMI_eqeq12d)
   from S3 have S4: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
     ( ( ( A \<ca> B ) = ( A \<ca> C ) \<longleftrightarrow> B = C ) \<longleftrightarrow> 
     ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B ) = ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> C ) 
     \<longleftrightarrow> B = C ) )" by (rule MMI_bibi1d)
   have S5: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_opreq2)
   from S5 have S6: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
     ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B ) = ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> C ) 
     \<longleftrightarrow> ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> C ) )" by (rule MMI_eqeq1d)
   have S7: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> ( B = C \<longleftrightarrow> 
     if ( B \<in> \<complex> , B , \<zero> ) = C )" by (rule MMI_eqeq1)
   from S6 S7 have S8: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
     ( ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> C ) \<longleftrightarrow> B = C ) \<longleftrightarrow> 
     ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> C ) \<longleftrightarrow> if ( B \<in> \<complex> , B , \<zero> ) = C ) )" 
     by (rule MMI_bibi12d)
   have S9: "C = if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> C ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( C \<in> \<complex> , C , \<zero> ) )" 
     by (rule MMI_opreq2)
   from S9 have S10: "C = if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
     ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> C ) \<longleftrightarrow> 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( C \<in> \<complex> , C , \<zero> ) ) )" 
     by (rule MMI_eqeq2d)
   have S11: "C = if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> ( if ( B \<in> \<complex> , B , \<zero> ) = C \<longleftrightarrow> 
     if ( B \<in> \<complex> , B , \<zero> ) = if ( C \<in> \<complex> , C , \<zero> ) )" by (rule MMI_eqeq2)
   from S10 S11 have S12: "C = if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
     ( ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> C ) \<longleftrightarrow> if ( B \<in> \<complex> , B , \<zero> ) = C ) \<longleftrightarrow> 
     ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( C \<in> \<complex> , C , \<zero> ) ) \<longleftrightarrow> 
     if ( B \<in> \<complex> , B , \<zero> ) = if ( C \<in> \<complex> , C , \<zero> ) ) )" by (rule MMI_bibi12d)
   have S13: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S13 have S14: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S15: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S15 have S16: "if ( B \<in> \<complex> , B , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S17: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S17 have S18: "if ( C \<in> \<complex> , C , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S14 S16 S18 have S19: 
     "( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( C \<in> \<complex> , C , \<zero> ) ) \<longleftrightarrow> 
     if ( B \<in> \<complex> , B , \<zero> ) = if ( C \<in> \<complex> , C , \<zero> )" by (rule MMI_addcan)
   from S4 S8 S12 S19 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) = ( A \<ca> C ) \<longleftrightarrow> B = C )" by (rule MMI_dedth3h)
qed

lemma (in MMIsar0) MMI_addcan2t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> C ) = ( B \<ca> C ) \<longleftrightarrow> 
  A = B )"
proof -
   have S1: "( C \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> ( C \<ca> A ) = ( A \<ca> C )" 
     by (rule MMI_axaddcom)
   from S1 have S2: "( C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( C \<ca> A ) = 
     ( A \<ca> C )" by (rule MMI_3adant3)
   have S3: "( C \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( C \<ca> B ) = ( B \<ca> C )" 
     by (rule MMI_axaddcom)
   from S3 have S4: "( C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( C \<ca> B ) = 
     ( B \<ca> C )" by (rule MMI_3adant2)
   from S2 S4 have S5: "( C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
     ( ( C \<ca> A ) = ( C \<ca> B ) \<longleftrightarrow> ( A \<ca> C ) = ( B \<ca> C ) )" 
     by (rule MMI_eqeq12d)
   have S6: "( C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( C \<ca> A ) = 
     ( C \<ca> B ) \<longleftrightarrow> A = B )" by (rule MMI_addcant)
   from S5 S6 have S7: "( C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> C ) = 
     ( B \<ca> C ) \<longleftrightarrow> A = B )" by (rule MMI_bitr3d)
   from S7 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> C ) = 
     ( B \<ca> C ) \<longleftrightarrow> A = B )" by (rule MMI_3coml)
qed

(************************ 20-30********************************)

lemma (in MMIsar0) MMI_add12t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<ca> ( B \<ca> C ) ) = 
  ( B \<ca> ( A \<ca> C ) )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> B ) = ( B \<ca> A )" 
     by (rule MMI_axaddcom)
   from S1 have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<ca> C ) = 
     ( ( B \<ca> A ) \<ca> C )" by (rule MMI_opreq1d)
   from S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<ca> C ) = ( ( B \<ca> A ) \<ca> C )" 
     by (rule MMI_3adant3)
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<ca> C ) = 
     ( A \<ca> ( B \<ca> C ) )" by (rule MMI_axaddass)
   have S5: "( B \<in> \<complex> \<and> A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( B \<ca> A ) \<ca> C ) = 
     ( B \<ca> ( A \<ca> C ) )" by (rule MMI_axaddass)
   from S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( B \<ca> A ) \<ca> C ) = ( B \<ca> ( A \<ca> C ) )" by (rule MMI_3com12)
   from S3 S4 S6 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( A \<ca> ( B \<ca> C ) ) = ( B \<ca> ( A \<ca> C ) )" 
     by (rule MMI_3eqtr3d)
qed

lemma (in MMIsar0) MMI_add23t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<ca> C ) = 
  ( ( A \<ca> C ) \<ca> B )"
proof -
   have S1: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<ca> C ) = ( C \<ca> B )" 
     by (rule MMI_axaddcom)
   from S1 have S2: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<ca> ( B \<ca> C ) ) = 
     ( A \<ca> ( C \<ca> B ) )" by (rule MMI_opreq2d)
   from S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( A \<ca> ( B \<ca> C ) ) = ( A \<ca> ( C \<ca> B ) )" 
     by (rule MMI_3adant1)
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<ca> C ) = 
     ( A \<ca> ( B \<ca> C ) )" by (rule MMI_axaddass)
   have S5: "( A \<in> \<complex> \<and> C \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> C ) \<ca> B ) = 
     ( A \<ca> ( C \<ca> B ) )" by (rule MMI_axaddass)
   from S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> C ) \<ca> B ) = ( A \<ca> ( C \<ca> B ) )" by (rule MMI_3com23)
   from S3 S4 S6 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<ca> C ) = ( ( A \<ca> C ) \<ca> B )" 
     by (rule MMI_3eqtr4d)
qed

lemma (in MMIsar0) MMI_add4t: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
  ( ( A \<ca> B ) \<ca> ( C \<ca> D ) ) = ( ( A \<ca> C ) \<ca> ( B \<ca> D ) )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<ca> C ) = ( ( A \<ca> C ) \<ca> B )" by (rule MMI_add23t)
   from S1 have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<ca> B ) \<ca> C ) \<ca> D ) = 
     ( ( ( A \<ca> C ) \<ca> B ) \<ca> D )" by (rule MMI_opreq1d)
   from S2 have S3: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<ca> B ) \<ca> C ) \<ca> D ) = 
     ( ( ( A \<ca> C ) \<ca> B ) \<ca> D )" by (rule MMI_3expa)
   from S3 have S4: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<ca> B ) \<ca> C ) \<ca> D ) = 
     ( ( ( A \<ca> C ) \<ca> B ) \<ca> D )" by (rule MMI_adantrr)
   have S5: "( ( A \<ca> B ) \<in> \<complex> \<and> C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<ca> B ) \<ca> C ) \<ca> D ) = 
     ( ( A \<ca> B ) \<ca> ( C \<ca> D ) )" by (rule MMI_axaddass)
   from S5 have S6: "( ( A \<ca> B ) \<in> \<complex> \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<ca> B ) \<ca> C ) \<ca> D ) = 
     ( ( A \<ca> B ) \<ca> ( C \<ca> D ) )" by (rule MMI_3expb)
   have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> B ) \<in> \<complex>" by (rule MMI_axaddcl)
   from S6 S7 have S8: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<ca> B ) \<ca> C ) \<ca> D ) = 
     ( ( A \<ca> B ) \<ca> ( C \<ca> D ) )" by (rule MMI_sylan)
   have S9: "( ( A \<ca> C ) \<in> \<complex> \<and> B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<ca> C ) \<ca> B ) \<ca> D ) = 
     ( ( A \<ca> C ) \<ca> ( B \<ca> D ) )" by (rule MMI_axaddass)
   from S9 have S10: "( ( A \<ca> C ) \<in> \<complex> \<and> ( B \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<ca> C ) \<ca> B ) \<ca> D ) = 
     ( ( A \<ca> C ) \<ca> ( B \<ca> D ) )" by (rule MMI_3expb)
   have S11: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<ca> C ) \<in> \<complex>" by (rule MMI_axaddcl)
   from S10 S11 have S12: "( ( A \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<ca> C ) \<ca> B ) \<ca> D ) = 
     ( ( A \<ca> C ) \<ca> ( B \<ca> D ) )" by (rule MMI_sylan)
   from S12 have S13: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<ca> C ) \<ca> B ) \<ca> D ) = 
     ( ( A \<ca> C ) \<ca> ( B \<ca> D ) )" by (rule MMI_an4s)
   from S4 S8 S13 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<ca> B ) \<ca> ( C \<ca> D ) ) = 
     ( ( A \<ca> C ) \<ca> ( B \<ca> D ) )" by (rule MMI_3eqtr3d)
qed

lemma (in MMIsar0) MMI_add42t: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
  ( ( A \<ca> B ) \<ca> ( C \<ca> D ) ) = ( ( A \<ca> C ) \<ca> ( D \<ca> B ) )"
proof -
   have S1: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<ca> B ) \<ca> ( C \<ca> D ) ) = 
     ( ( A \<ca> C ) \<ca> ( B \<ca> D ) )" by (rule MMI_add4t)
   have S2: "( B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( B \<ca> D ) = 
     ( D \<ca> B )" by (rule MMI_axaddcom)
   from S2 have S3: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( B \<ca> D ) = ( D \<ca> B )" by (rule MMI_ad2ant2l)
   from S3 have S4: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<ca> C ) \<ca> ( B \<ca> D ) ) = 
     ( ( A \<ca> C ) \<ca> ( D \<ca> B ) )" by (rule MMI_opreq2d)
   from S1 S4 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<ca> B ) \<ca> ( C \<ca> D ) ) = 
     ( ( A \<ca> C ) \<ca> ( D \<ca> B ) )" by (rule MMI_eqtrd)
qed

lemma (in MMIsar0) MMI_add12: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( A \<ca> ( B \<ca> C ) ) = ( B \<ca> ( A \<ca> C ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<ca> ( B \<ca> C ) ) = 
     ( B \<ca> ( A \<ca> C ) )" by (rule MMI_add12t)
   from S1 S2 S3 S4 show "( A \<ca> ( B \<ca> C ) ) = 
     ( B \<ca> ( A \<ca> C ) )" by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_add23: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( ( A \<ca> B ) \<ca> C ) = ( ( A \<ca> C ) \<ca> B )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<ca> C ) = ( ( A \<ca> C ) \<ca> B )" by (rule MMI_add23t)
   from S1 S2 S3 S4 show "( ( A \<ca> B ) \<ca> C ) = 
     ( ( A \<ca> C ) \<ca> B )" by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_add4: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>" and
    A4: "D \<in> \<complex>"   
   shows "( ( A \<ca> B ) \<ca> ( C \<ca> D ) ) = 
  ( ( A \<ca> C ) \<ca> ( B \<ca> D ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from S1 S2 have S3: "A \<in> \<complex> \<and> B \<in> \<complex>" by (rule MMI_pm3_2i)
   from A3 have S4: "C \<in> \<complex>".
   from A4 have S5: "D \<in> \<complex>".
   from S4 S5 have S6: "C \<in> \<complex> \<and> D \<in> \<complex>" by (rule MMI_pm3_2i)
   have S7: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<ca> B ) \<ca> ( C \<ca> D ) ) = 
     ( ( A \<ca> C ) \<ca> ( B \<ca> D ) )" by (rule MMI_add4t)
   from S3 S6 S7 show "( ( A \<ca> B ) \<ca> ( C \<ca> D ) ) = 
     ( ( A \<ca> C ) \<ca> ( B \<ca> D ) )" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_add42: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>" and
    A4: "D \<in> \<complex>"   
   shows "( ( A \<ca> B ) \<ca> ( C \<ca> D ) ) = 
  ( ( A \<ca> C ) \<ca> ( D \<ca> B ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   from A4 have S4: "D \<in> \<complex>".
   from S1 S2 S3 S4 have S5: "( ( A \<ca> B ) \<ca> ( C \<ca> D ) ) = 
     ( ( A \<ca> C ) \<ca> ( B \<ca> D ) )" by (rule MMI_add4)
   from A2 have S6: "B \<in> \<complex>".
   from A4 have S7: "D \<in> \<complex>".
   from S6 S7 have S8: "( B \<ca> D ) = ( D \<ca> B )" by (rule MMI_addcom)
   from S8 have S9: "( ( A \<ca> C ) \<ca> ( B \<ca> D ) ) = 
     ( ( A \<ca> C ) \<ca> ( D \<ca> B ) )" by (rule MMI_opreq2i)
   from S5 S9 show "( ( A \<ca> B ) \<ca> ( C \<ca> D ) ) = 
     ( ( A \<ca> C ) \<ca> ( D \<ca> B ) )" by (rule MMI_eqtr)
qed

lemma (in MMIsar0) MMI_addid2t: 
   shows "A \<in> \<complex> \<longrightarrow> ( \<zero> \<ca> A ) = A"
proof -
   have S1: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   have S2: "( \<zero> \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> ( \<zero> \<ca> A ) = ( A \<ca> \<zero> )" 
     by (rule MMI_axaddcom)
   from S1 S2 have S3: "A \<in> \<complex> \<longrightarrow> ( \<zero> \<ca> A ) = ( A \<ca> \<zero> )" 
     by (rule MMI_mpan)
   have S4: "A \<in> \<complex> \<longrightarrow> ( A \<ca> \<zero> ) = A" by (rule MMI_ax0id)
   from S3 S4 show "A \<in> \<complex> \<longrightarrow> ( \<zero> \<ca> A ) = A" by (rule MMI_eqtrd)
qed

lemma (in MMIsar0) MMI_peano2cn: 
   shows "A \<in> \<complex> \<longrightarrow> ( A \<ca> \<one> ) \<in> \<complex>"
proof -
   have S1: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S2: "( A \<in> \<complex> \<and> \<one> \<in> \<complex> ) \<longrightarrow> ( A \<ca> \<one> ) \<in> \<complex>" by (rule MMI_axaddcl)
   from S1 S2 show "A \<in> \<complex> \<longrightarrow> ( A \<ca> \<one> ) \<in> \<complex>" by (rule MMI_mpan2)
qed

(*** 31-34 ********************************************************)

lemma (in MMIsar0) MMI_peano2re: 
   shows "A \<in> \<real> \<longrightarrow> ( A \<ca> \<one> ) \<in> \<real>"
proof -
   have S1: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S2: "( A \<in> \<real> \<and> \<one> \<in> \<real> ) \<longrightarrow> ( A \<ca> \<one> ) \<in> \<real>" by (rule MMI_axaddrcl)
   from S1 S2 show "A \<in> \<real> \<longrightarrow> ( A \<ca> \<one> ) \<in> \<real>" by (rule MMI_mpan2)
qed

lemma (in MMIsar0) MMI_negeu: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "\<exists>! x . x \<in> \<complex> \<and> ( A \<ca> x ) = B"
proof -
   { fix x y
     have S1: "x = y \<longrightarrow> ( A \<ca> x ) = ( A \<ca> y )" by (rule MMI_opreq2)
     from S1 have "x = y \<longrightarrow> ( ( A \<ca> x ) = B \<longleftrightarrow> ( A \<ca> y ) = B )" 
       by (rule MMI_eqeq1d)
   } then have S2: "\<forall>x y. x = y \<longrightarrow> ( ( A \<ca> x ) = B \<longleftrightarrow> 
       ( A \<ca> y ) = B )" by simp
   from S2 have S3: "( \<exists>! x . x \<in> \<complex> \<and> ( A \<ca> x ) = B ) \<longleftrightarrow> 
     ( ( \<exists> x \<in> \<complex> . ( A \<ca> x ) = B ) \<and> 
     ( \<forall> x \<in> \<complex> . \<forall> y \<in> \<complex> . ( ( ( A \<ca> x ) = B \<and> ( A \<ca> y ) = B ) \<longrightarrow> 
     x = y ) ) )" by (rule MMI_reu4)
   from A1 have S4: "A \<in> \<complex>".
   from S4 have S5: "\<exists> y \<in> \<complex> . ( A \<ca> y ) = \<zero>" by (rule MMI_negex)
   from A2 have S6: "B \<in> \<complex>".
   { fix y
     have S7: "( y \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( y \<ca> B ) \<in> \<complex>" by (rule MMI_axaddcl)
     from S6 S7 have S8: "y \<in> \<complex> \<longrightarrow> ( y \<ca> B ) \<in> \<complex>" by (rule MMI_mpan2)
     have S9: "( y \<ca> B ) \<in> \<complex> \<longleftrightarrow> ( \<exists> x \<in> \<complex> . x = ( y \<ca> B ) )" 
       by (rule MMI_risset)
     from S8 S9 have S10: "y \<in> \<complex> \<longrightarrow> ( \<exists> x \<in> \<complex> . x = ( y \<ca> B ) )" 
       by (rule MMI_sylib)
     { fix x
       have S11: "x = ( y \<ca> B ) \<longrightarrow> ( A \<ca> x ) = 
	 ( A \<ca> ( y \<ca> B ) )" by (rule MMI_opreq2)
       from A1 have S12: "A \<in> \<complex>".
       from A2 have S13: "B \<in> \<complex>".
       have S14: "( A \<in> \<complex> \<and> y \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
	 ( ( A \<ca> y ) \<ca> B ) = ( A \<ca> ( y \<ca> B ) )" 
	 by (rule MMI_axaddass)
       from S12 S13 S14 have S15: "y \<in> \<complex> \<longrightarrow> ( ( A \<ca> y ) \<ca> B ) = 
	 ( A \<ca> ( y \<ca> B ) )" by (rule MMI_mp3an13)
       from S15 have S16: "y \<in> \<complex> \<longrightarrow> ( A \<ca> ( y \<ca> B ) ) = 
	 ( ( A \<ca> y ) \<ca> B )" by (rule MMI_eqcomd)
       from S11 S16 have S17: "( y \<in> \<complex> \<and> x = ( y \<ca> B ) ) 
	 \<longrightarrow> ( A \<ca> x ) = ( ( A \<ca> y ) \<ca> B )" by (rule MMI_sylan9eqr)
       have S18: "( A \<ca> y ) = \<zero> \<longrightarrow> 
	 ( ( A \<ca> y ) \<ca> B ) = ( \<zero> \<ca> B )" by (rule MMI_opreq1)
       from A2 have S19: "B \<in> \<complex>".
       from S19 have S20: "( \<zero> \<ca> B ) = B" by (rule MMI_addid2)
       from S18 S20 have S21: "( A \<ca> y ) = \<zero> \<longrightarrow> 
	 ( ( A \<ca> y ) \<ca> B ) = B" by (rule MMI_syl6eq)
       from S17 S21 have S22: "( ( A \<ca> y ) = \<zero> \<and> ( y \<in> \<complex> \<and> x = 
	 ( y \<ca> B ) ) ) \<longrightarrow> ( A \<ca> x ) = B" by (rule MMI_sylan9eqr)
       from S22 have S23: "( A \<ca> y ) = \<zero> \<longrightarrow> 
	 ( y \<in> \<complex> \<longrightarrow> ( x = ( y \<ca> B ) \<longrightarrow> ( A \<ca> x ) = B ) )" 
	 by (rule MMI_exp32)
       from S23 have S24: "( y \<in> \<complex> \<and> ( A \<ca> y ) = \<zero> ) \<longrightarrow> 
	 ( x = ( y \<ca> B ) \<longrightarrow> ( A \<ca> x ) = B )" by (rule MMI_impcom)
       from S24 have "( y \<in> \<complex> \<and> ( A \<ca> y ) = \<zero> ) \<longrightarrow> 
	 ( x \<in> \<complex> \<longrightarrow> ( x = ( y \<ca> B ) \<longrightarrow> ( A \<ca> x ) = B ) )" 
	 by (rule MMI_a1d)
     } then have S25: "\<forall> x. ( y \<in> \<complex> \<and> ( A \<ca> y ) = \<zero> ) \<longrightarrow> 
	 ( x \<in> \<complex> \<longrightarrow> ( x = ( y \<ca> B ) \<longrightarrow> ( A \<ca> x ) = B ) )" by auto
     from S25 have S26: "( y \<in> \<complex> \<and> ( A \<ca> y ) = \<zero> ) \<longrightarrow> 
       ( \<forall> x \<in> \<complex> . ( x = ( y \<ca> B ) \<longrightarrow> ( A \<ca> x ) = B ) )" 
       by (rule MMI_r19_21aiv)
     from S26 have S27: "y \<in> \<complex> \<longrightarrow> ( ( A \<ca> y ) = \<zero> \<longrightarrow> 
       ( \<forall> x \<in> \<complex> . ( x = ( y \<ca> B ) \<longrightarrow> ( A \<ca> x ) = B ) ) )" 
       by (rule MMI_ex)
     have S28: "( \<forall> x \<in> \<complex> . ( x = ( y \<ca> B ) \<longrightarrow> ( A \<ca> x ) = B ) ) 
       \<longrightarrow> ( ( \<exists> x \<in> \<complex> . x = ( y \<ca> B ) ) \<longrightarrow> 
       ( \<exists> x \<in> \<complex> . ( A \<ca> x ) = B ) )" by (rule MMI_r19_22)
     from S27 S28 have S29: "y \<in> \<complex> \<longrightarrow> ( ( A \<ca> y ) = \<zero> \<longrightarrow> 
       ( ( \<exists> x \<in> \<complex> . x = ( y \<ca> B ) ) \<longrightarrow> 
       ( \<exists> x \<in> \<complex> . ( A \<ca> x ) = B ) ) )" by (rule MMI_syl6)
     from S10 S29 have "y \<in> \<complex> \<longrightarrow> ( ( A \<ca> y ) = \<zero> \<longrightarrow> 
       ( \<exists> x \<in> \<complex> . ( A \<ca> x ) = B ) )" by (rule MMI_mpid)
   } then have S30: "\<forall> y. y \<in> \<complex> \<longrightarrow> ( ( A \<ca> y ) = \<zero> \<longrightarrow> 
       ( \<exists> x \<in> \<complex> . ( A \<ca> x ) = B ) )" by simp
   from S30 have S31: "( \<exists> y \<in> \<complex> . ( A \<ca> y ) = \<zero> ) \<longrightarrow> 
     ( \<exists> x \<in> \<complex> . ( A \<ca> x ) = B )" by (rule MMI_r19_23aiv)
   from S5 S31 have S32: "\<exists> x \<in> \<complex> . ( A \<ca> x ) = B" by (rule MMI_ax_mp)
   from A1 have S33: "A \<in> \<complex>".
   { fix x y
     have S34: "( A \<in> \<complex> \<and> x \<in> \<complex> \<and> y \<in> \<complex> ) \<longrightarrow> 
       ( ( A \<ca> x ) = ( A \<ca> y ) \<longleftrightarrow> x = y )" by (rule MMI_addcant)
     have S35: "( ( A \<ca> x ) = B \<and> ( A \<ca> y ) = B ) \<longrightarrow> 
       ( A \<ca> x ) = ( A \<ca> y )" by (rule MMI_eqtr3t)
     from S34 S35 have S36: "( A \<in> \<complex> \<and> x \<in> \<complex> \<and> y \<in> \<complex> ) \<longrightarrow> 
       ( ( ( A \<ca> x ) = B \<and> ( A \<ca> y ) = B ) \<longrightarrow> x = y )" 
       by (rule MMI_syl5bi)
     from S33 S36 have "( x \<in> \<complex> \<and> y \<in> \<complex> ) \<longrightarrow> 
       ( ( ( A \<ca> x ) = B \<and> ( A \<ca> y ) = B ) \<longrightarrow> x = y )" 
       by (rule MMI_mp3an1)
   } then have S37: "\<forall>x y . ( x \<in> \<complex> \<and> y \<in> \<complex> ) \<longrightarrow> 
       ( ( ( A \<ca> x ) = B \<and> ( A \<ca> y ) = B ) \<longrightarrow> x = y )" by auto
   from S37 have S38: "\<forall> x \<in> \<complex> . \<forall> y \<in> \<complex> . ( ( ( A \<ca> x ) = B \<and> 
     ( A \<ca> y ) = B ) \<longrightarrow> x = y )" by (rule MMI_rgen2)
   from S3 S32 S38 show "\<exists>! x . x \<in> \<complex> \<and> ( A \<ca> x ) = B" 
     by (rule MMI_mpbir2an)
qed

(** this is proven by definition rather than importing the Metamath proof **)

lemma (in MMIsar0) MMI_subval: assumes "A \<in> \<complex>"  "B \<in> \<complex>"
  shows "A \<cs> B =  \<Union> { x \<in> \<complex> . B \<ca> x = A }"
  using sub_def by simp

(** this is a definition in Metamath *)

lemma (in MMIsar0) MMI_df_neg: shows "(\<cn> A) = \<zero> \<cs> A"
  using cneg_def by simp

(************** 35-37 ****************************************)
 
lemma (in MMIsar0) MMI_negeq: 
   shows "A = B \<longrightarrow> (\<cn>A) = (\<cn> B)"
proof -
   have S1: "A = B \<longrightarrow> ( \<zero> \<cs> A ) = ( \<zero> \<cs> B )" by (rule MMI_opreq2)
   have S2: "(\<cn>A) = ( \<zero> \<cs> A )" by (rule MMI_df_neg)
   have S3: "(\<cn>B) = ( \<zero> \<cs> B )" by (rule MMI_df_neg)
   from S1 S2 S3 show "A = B \<longrightarrow> (\<cn>A) = (\<cn>B)" by (rule MMI_3eqtr4g)
qed

lemma (in MMIsar0) MMI_negeqi: assumes A1: "A = B"   
   shows "(\<cn>  A) = (\<cn>B)"
proof -
   from A1 have S1: "A = B".
   have S2: "A = B \<longrightarrow> (\<cn>A) = (\<cn>B)" by (rule MMI_negeq)
   from S1 S2 show "(\<cn>A) = (\<cn>B)" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_negeqd: assumes A1: "\<phi> \<longrightarrow> A = B"   
   shows "\<phi> \<longrightarrow> (\<cn>A) = (\<cn>B)"
proof -
   from A1 have S1: "\<phi> \<longrightarrow> A = B".
   have S2: "A = B \<longrightarrow> (\<cn>A) = (\<cn>B)" by (rule MMI_negeq)
   from S1 S2 show "\<phi> \<longrightarrow> (\<cn>A) = (\<cn>B)" by (rule MMI_syl)
qed

(**********************auto************************************)

lemma (in MMIsar0) MMI_hbneg: assumes A1: "y \<in> A \<longrightarrow> ( \<forall> x . y \<in> A )"   
   shows "y \<in> ((\<cn>  A)) \<longrightarrow> ( \<forall> x . (y \<in> ((\<cn>  A)) ) )"
  using assms by auto

lemma (in MMIsar0) MMI_minusex: 
   shows "((\<cn>  A)) isASet" by auto

(********38-43************************************************)

lemma (in MMIsar0) MMI_subcl: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( A \<cs> B ) \<in> \<complex>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from S1 S2 have S3: "( A \<cs> B ) = \<Union> { x \<in> \<complex> . ( B \<ca> x ) = A }" 
     by (rule MMI_subval)
   from A2 have S4: "B \<in> \<complex>".
   from A1 have S5: "A \<in> \<complex>".
   from S4 S5 have S6: "\<exists>! x . x \<in> \<complex> \<and> ( B \<ca> x ) = A" by (rule MMI_negeu)
   have S7: "( \<exists>! x . x \<in> \<complex> \<and> ( B \<ca> x ) = A ) \<longrightarrow> 
     \<Union> { x \<in> \<complex> . ( B \<ca> x ) = A } \<in> \<complex>" by (rule MMI_reucl)
   from S6 S7 have S8: "\<Union> { x \<in> \<complex> . ( B \<ca> x ) = A } \<in> \<complex>" 
     by (rule MMI_ax_mp)
   from S3 S8 show "( A \<cs> B ) \<in> \<complex>" by simp
qed

lemma (in MMIsar0) MMI_subclt: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cs> B ) \<in> \<complex>"
proof -
   have S1: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> ( A \<cs> B ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B )" by (rule MMI_opreq1)
   from S1 have S2: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> ( ( A \<cs> B ) \<in> \<complex> \<longleftrightarrow> 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B ) \<in> \<complex> )" by (rule MMI_eleq1d)
   have S3: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_opreq2)
   from S3 have S4: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
     ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B ) \<in> \<complex> \<longleftrightarrow> 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) ) \<in> \<complex> )" 
     by (rule MMI_eleq1d)
   have S5: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S5 have S6: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S7: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S7 have S8: "if ( B \<in> \<complex> , B , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S6 S8 have S9: 
     "( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) ) \<in> \<complex>" 
     by (rule MMI_subcl)
   from S2 S4 S9 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cs> B ) \<in> \<complex>" 
     by (rule MMI_dedth2h)
qed

lemma (in MMIsar0) MMI_negclt: 
   shows "A \<in> \<complex> \<longrightarrow> ( (\<cn>  A) ) \<in> \<complex>"
proof -
   have S1: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   have S2: "( \<zero> \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> ( \<zero> \<cs> A ) \<in> \<complex>" by (rule MMI_subclt)
   from S1 S2 have S3: "A \<in> \<complex> \<longrightarrow> ( \<zero> \<cs> A ) \<in> \<complex>" by (rule MMI_mpan)
   have S4: "( (\<cn>  A) ) = ( \<zero> \<cs> A )" by (rule MMI_df_neg)
   from S3 S4 show "A \<in> \<complex> \<longrightarrow> ( (\<cn>  A) ) \<in> \<complex>" by (rule MMI_syl5eqel)
qed

lemma (in MMIsar0) MMI_negcl: assumes A1: "A \<in> \<complex>"   
   shows "( (\<cn>  A) ) \<in> \<complex>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   have S2: "A \<in> \<complex> \<longrightarrow> ( (\<cn>  A) ) \<in> \<complex>" by (rule MMI_negclt)
   from S1 S2 show "( (\<cn>  A) ) \<in> \<complex>" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_subadd: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( A \<cs> B ) = C \<longleftrightarrow> ( B \<ca> C ) = A"
proof -
   from A3 have S1: "C \<in> \<complex>".
   { fix x
     have S2: "x = C \<longrightarrow> ( ( A \<cs> B ) = x \<longleftrightarrow> ( A \<cs> B ) = C )" 
       by (rule MMI_eqeq2)
     have S3: "x = C \<longrightarrow> ( B \<ca> x ) = ( B \<ca> C )" by (rule MMI_opreq2)
     from S3 have S4: "x = C \<longrightarrow> ( ( B \<ca> x ) = A \<longleftrightarrow> ( B \<ca> C ) = A )" 
       by (rule MMI_eqeq1d)
     from S2 S4 have "x = C \<longrightarrow> ( ( ( A \<cs> B ) = x \<longleftrightarrow> 
       ( B \<ca> x ) = A ) \<longleftrightarrow> ( ( A \<cs> B ) = C \<longleftrightarrow> ( B \<ca> C ) = A ) )" 
       by (rule MMI_bibi12d)
   } then have S5: "\<forall>x. x = C \<longrightarrow> ( ( ( A \<cs> B ) = x \<longleftrightarrow> 
       ( B \<ca> x ) = A ) \<longleftrightarrow> ( ( A \<cs> B ) = C \<longleftrightarrow> 
       ( B \<ca> C ) = A ) )" by simp
   from A2 have S6: "B \<in> \<complex>".
   from A1 have S7: "A \<in> \<complex>".
   from S6 S7 have S8: "\<exists>! x . x \<in> \<complex> \<and> ( B \<ca> x ) = A" by (rule MMI_negeu)
   { fix x 
     have S9: "( x \<in> \<complex> \<and> ( \<exists>! x . x \<in> \<complex> \<and> ( B \<ca> x ) = A ) \<longrightarrow> 
       ( ( B \<ca> x ) = A ) \<longleftrightarrow> \<Union> { x \<in> \<complex> . ( B \<ca> x ) = A } = x )" 
       by (rule MMI_reuuni1)
     from S8 S9 have "x \<in> \<complex> \<longrightarrow> ( ( B \<ca> x ) = A \<longleftrightarrow> 
       \<Union> { x \<in> \<complex> . ( B \<ca> x ) = A } = x )" by (rule MMI_mpan2)
   } then have S10: "\<forall> x. x \<in> \<complex> \<longrightarrow> ( ( B \<ca> x ) = A \<longleftrightarrow> 
       \<Union> { x \<in> \<complex> . ( B \<ca> x ) = A } = x )" by blast
   from A1 have S11: "A \<in> \<complex>".
   from A2 have S12: "B \<in> \<complex>".
   from S11 S12 have S13: "( A \<cs> B ) = \<Union> { x \<in> \<complex> . ( B \<ca> x ) = A }" 
     by (rule MMI_subval)
   from S13 have S14: "\<forall>x. ( A \<cs> B ) = x \<longleftrightarrow> 
     \<Union> { x \<in> \<complex> . ( B \<ca> x ) = A } = x" by simp  (* (rule MMI_eqeq1i)*)
   from S10 S14 have S15: "\<forall>x. x \<in> \<complex> \<longrightarrow> ( ( A \<cs> B ) = x \<longleftrightarrow> 
     ( B \<ca> x ) = A )" by (rule MMI_syl6rbbr)
   from S5 S15 have S16: "C \<in> \<complex> \<longrightarrow> ( ( A \<cs> B ) = C \<longleftrightarrow> 
     ( B \<ca> C ) = A )" by (rule MMI_vtoclga)
   from S1 S16 show "( A \<cs> B ) = C \<longleftrightarrow> ( B \<ca> C ) = A" 
     by (rule MMI_ax_mp)
qed

(*******************44-53*********************************************)


lemma (in MMIsar0) MMI_subsub23: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( A \<cs> B ) = C \<longleftrightarrow> ( A \<cs> C ) = B"
proof -
   from A2 have S1: "B \<in> \<complex>".
   from A3 have S2: "C \<in> \<complex>".
   from S1 S2 have S3: "( B \<ca> C ) = ( C \<ca> B )" by (rule MMI_addcom)
   from S3 have S4: "( B \<ca> C ) = A \<longleftrightarrow> ( C \<ca> B ) = A" 
     by (rule MMI_eqeq1i)
   from A1 have S5: "A \<in> \<complex>".
   from A2 have S6: "B \<in> \<complex>".
   from A3 have S7: "C \<in> \<complex>".
   from S5 S6 S7 have S8: "( A \<cs> B ) = C \<longleftrightarrow> ( B \<ca> C ) = A" 
     by (rule MMI_subadd)
   from A1 have S9: "A \<in> \<complex>".
   from A3 have S10: "C \<in> \<complex>".
   from A2 have S11: "B \<in> \<complex>".
   from S9 S10 S11 have S12: "( A \<cs> C ) = B \<longleftrightarrow> ( C \<ca> B ) = A" 
     by (rule MMI_subadd)
   from S4 S8 S12 show "( A \<cs> B ) = C \<longleftrightarrow> ( A \<cs> C ) = B" 
     by (rule MMI_3bitr4)
qed

lemma (in MMIsar0) MMI_subaddt: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<cs> B ) = C \<longleftrightarrow> 
  ( B \<ca> C ) = A )"
proof -
   have S1: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> ( A \<cs> B ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B )" by (rule MMI_opreq1)
   from S1 have S2: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> ( ( A \<cs> B ) = C \<longleftrightarrow> 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B ) = C )" by (rule MMI_eqeq1d)
   have S3: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> ( ( B \<ca> C ) = A \<longleftrightarrow> 
     ( B \<ca> C ) = if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_eqeq2)
   from S2 S3 have S4: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
     ( ( ( A \<cs> B ) = C \<longleftrightarrow> ( B \<ca> C ) = A ) \<longleftrightarrow> 
     ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B ) = C \<longleftrightarrow> ( B \<ca> C ) = 
     if ( A \<in> \<complex> , A , \<zero> ) ) )" by (rule MMI_bibi12d)
   have S5: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_opreq2)
   from S5 have S6: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
     ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B ) = C \<longleftrightarrow> 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) ) = C )" 
     by (rule MMI_eqeq1d)
   have S7: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> ( B \<ca> C ) = 
     ( if ( B \<in> \<complex> , B , \<zero> ) \<ca> C )" by (rule MMI_opreq1)
   from S7 have S8: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
     ( ( B \<ca> C ) = if ( A \<in> \<complex> , A , \<zero> ) \<longleftrightarrow> 
     ( if ( B \<in> \<complex> , B , \<zero> ) \<ca> C ) = if ( A \<in> \<complex> , A , \<zero> ) )" 
     by (rule MMI_eqeq1d)
   from S6 S8 have S9: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
     ( ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B ) = C \<longleftrightarrow> 
     ( B \<ca> C ) = if ( A \<in> \<complex> , A , \<zero> ) ) \<longleftrightarrow> 
     ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) ) = C \<longleftrightarrow> 
     ( if ( B \<in> \<complex> , B , \<zero> ) \<ca> C ) = if ( A \<in> \<complex> , A , \<zero> ) ) )" 
     by (rule MMI_bibi12d)
   have S10: "C = if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
     ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) ) = C \<longleftrightarrow> 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) ) = 
     if ( C \<in> \<complex> , C , \<zero> ) )" by (rule MMI_eqeq2)
   have S11: "C = if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
     ( if ( B \<in> \<complex> , B , \<zero> ) \<ca> C ) = 
     ( if ( B \<in> \<complex> , B , \<zero> ) \<ca> if ( C \<in> \<complex> , C , \<zero> ) )" by (rule MMI_opreq2)
   from S11 have S12: "C = if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
     ( ( if ( B \<in> \<complex> , B , \<zero> ) \<ca> C ) = if ( A \<in> \<complex> , A , \<zero> ) \<longleftrightarrow> 
     ( if ( B \<in> \<complex> , B , \<zero> ) \<ca> if ( C \<in> \<complex> , C , \<zero> ) ) = 
     if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_eqeq1d)
   from S10 S12 have S13: "C = if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
     ( ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) ) = C \<longleftrightarrow> 
     ( if ( B \<in> \<complex> , B , \<zero> ) \<ca> C ) = if ( A \<in> \<complex> , A , \<zero> ) ) \<longleftrightarrow> 
     ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) ) = 
     if ( C \<in> \<complex> , C , \<zero> ) \<longleftrightarrow> 
     ( if ( B \<in> \<complex> , B , \<zero> ) \<ca> if ( C \<in> \<complex> , C , \<zero> ) ) = 
     if ( A \<in> \<complex> , A , \<zero> ) ) )" by (rule MMI_bibi12d)
   have S14: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S14 have S15: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S16: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S16 have S17: "if ( B \<in> \<complex> , B , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S18: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S18 have S19: "if ( C \<in> \<complex> , C , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S15 S17 S19 have S20: 
     "( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) ) = 
     if ( C \<in> \<complex> , C , \<zero> ) \<longleftrightarrow> 
     ( if ( B \<in> \<complex> , B , \<zero> ) \<ca> if ( C \<in> \<complex> , C , \<zero> ) ) = 
     if ( A \<in> \<complex> , A , \<zero> )" by (rule MMI_subadd)
   from S4 S9 S13 S20 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<cs> B ) = C \<longleftrightarrow> ( B \<ca> C ) = A )" by (rule MMI_dedth3h)
qed

lemma (in MMIsar0) MMI_pncan3t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> ( B \<cs> A ) ) = B"
proof -
   have S1: "( B \<cs> A ) = ( B \<cs> A )" by (rule MMI_eqid)
   have S2: "( B \<in> \<complex> \<and> A \<in> \<complex> \<and> ( B \<cs> A ) \<in> \<complex> ) \<longrightarrow> 
     ( ( B \<cs> A ) = ( B \<cs> A ) \<longleftrightarrow> ( A \<ca> ( B \<cs> A ) ) = B )" 
     by (rule MMI_subaddt)
   have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> B \<in> \<complex>" by (rule MMI_pm3_27)
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> A \<in> \<complex>" by (rule MMI_pm3_26)
   have S5: "( B \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> ( B \<cs> A ) \<in> \<complex>" by (rule MMI_subclt)
   from S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( B \<cs> A ) \<in> \<complex>" 
     by (rule MMI_ancoms)
   from S2 S3 S4 S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( B \<cs> A ) = 
     ( B \<cs> A ) \<longleftrightarrow> ( A \<ca> ( B \<cs> A ) ) = B )" by (rule MMI_syl3anc)
   from S1 S7 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> ( B \<cs> A ) ) = B" 
     by (rule MMI_mpbii)
qed

lemma (in MMIsar0) MMI_pncan3: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( A \<ca> ( B \<cs> A ) ) = B"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> ( B \<cs> A ) ) = B" 
     by (rule MMI_pncan3t)
   from S1 S2 S3 show "( A \<ca> ( B \<cs> A ) ) = B" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_negidt: 
   shows "A \<in> \<complex> \<longrightarrow> ( A \<ca> ( (\<cn>  A) ) ) = \<zero>"
proof -
   have S1: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   have S2: "( A \<in> \<complex> \<and> \<zero> \<in> \<complex> ) \<longrightarrow> ( A \<ca> ( \<zero> \<cs> A ) ) = \<zero>" 
     by (rule MMI_pncan3t)
   from S1 S2 have S3: "A \<in> \<complex> \<longrightarrow> ( A \<ca> ( \<zero> \<cs> A ) ) = \<zero>" 
     by (rule MMI_mpan2)
   have S4: "( (\<cn>  A) ) = ( \<zero> \<cs> A )" by (rule MMI_df_neg)
   from S4 have S5: "( A \<ca> ( (\<cn>  A) ) ) = ( A \<ca> ( \<zero> \<cs> A ) )" 
     by (rule MMI_opreq2i)
   from S3 S5 show "A \<in> \<complex> \<longrightarrow> ( A \<ca> ( (\<cn>  A) ) ) = \<zero>" by (rule MMI_syl5eq)
qed

lemma (in MMIsar0) MMI_negid: assumes A1: "A \<in> \<complex>"   
   shows "( A \<ca> ( (\<cn>  A) ) ) = \<zero>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   have S2: "A \<in> \<complex> \<longrightarrow> ( A \<ca> ( (\<cn>  A) ) ) = \<zero>" by (rule MMI_negidt)
   from S1 S2 show "( A \<ca> ( (\<cn>  A) ) ) = \<zero>" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_negsub: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( A \<ca> ( (\<cn>  B) ) ) = ( A \<cs> B )"
proof -
   from A2 have S1: "B \<in> \<complex>".
   from A1 have S2: "A \<in> \<complex>".
   from A2 have S3: "B \<in> \<complex>".
   from S3 have S4: "( (\<cn>  B) ) \<in> \<complex>" by (rule MMI_negcl)
   from S2 S4 have S5: "( A \<ca> ( (\<cn>  B) ) ) \<in> \<complex>" by (rule MMI_addcl)
   from S1 S5 have S6: "( B \<ca> ( A \<ca> ( (\<cn>  B) ) ) ) = 
     ( ( A \<ca> ( (\<cn>  B) ) ) \<ca> B )" by (rule MMI_addcom)
   from A1 have S7: "A \<in> \<complex>".
   from S4 have S8: "( (\<cn>  B) ) \<in> \<complex>" .
   from A2 have S9: "B \<in> \<complex>".
   from S7 S8 S9 have S10: "( ( A \<ca> ( (\<cn>  B) ) ) \<ca> B ) = 
     ( A \<ca> ( ( (\<cn>  B) ) \<ca> B ) )" by (rule MMI_addass)
   from S4 have S11: "( (\<cn>  B) ) \<in> \<complex>" .
   from A2 have S12: "B \<in> \<complex>".
   from S11 S12 have S13: "( ( (\<cn>  B) ) \<ca> B ) = ( B \<ca> ( (\<cn>  B) ) )" 
     by (rule MMI_addcom)
   from A2 have S14: "B \<in> \<complex>".
   from S14 have S15: "( B \<ca> ( (\<cn>  B) ) ) = \<zero>" by (rule MMI_negid)
   from S13 S15 have S16: "( ( (\<cn>  B) ) \<ca> B ) = \<zero>" by (rule MMI_eqtr)
   from S16 have S17: "( A \<ca> ( ( (\<cn>  B) ) \<ca> B ) ) = ( A \<ca> \<zero> )" 
     by (rule MMI_opreq2i)
   from A1 have S18: "A \<in> \<complex>".
   from S18 have S19: "( A \<ca> \<zero> ) = A" by (rule MMI_addid1)
   from S10 S17 S19 have S20: "( ( A \<ca> ( (\<cn>  B) ) ) \<ca> B ) = A" 
     by (rule MMI_3eqtr)
   from S6 S20 have S21: "( B \<ca> ( A \<ca> ( (\<cn>  B) ) ) ) = A" 
     by (rule MMI_eqtr)
   from A1 have S22: "A \<in> \<complex>".
   from A2 have S23: "B \<in> \<complex>".
   from S5 have S24: "( A \<ca> ( (\<cn>  B) ) ) \<in> \<complex>" .
   from S22 S23 S24 have S25: "( A \<cs> B ) = ( A \<ca> ( (\<cn>  B) ) ) \<longleftrightarrow> 
     ( B \<ca> ( A \<ca> ( (\<cn>  B) ) ) ) = A" by (rule MMI_subadd)
   from S21 S25 have S26: "( A \<cs> B ) = ( A \<ca> ( (\<cn>  B) ) )" 
     by (rule MMI_mpbir)
   from S26 show "( A \<ca> ( (\<cn>  B) ) ) = ( A \<cs> B )" by (rule MMI_eqcomi)
qed

lemma (in MMIsar0) MMI_negsubt: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> ( (\<cn>  B) ) ) = ( A \<cs> B )"
proof -
   have S1: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> ( A \<ca> ( (\<cn>  B) ) ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> ( (\<cn>  B) ) )" by (rule MMI_opreq1)
   have S2: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> ( A \<cs> B ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B )" by (rule MMI_opreq1)
   from S1 S2 have S3: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
     ( ( A \<ca> ( (\<cn>  B) ) ) = ( A \<cs> B ) \<longleftrightarrow> 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> ( (\<cn>  B) ) ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B ) )" by (rule MMI_eqeq12d)
   have S4: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
     ( (\<cn>  B) ) = ( \<cn> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_negeq)
   from S4 have S5: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> ( (\<cn>  B) ) ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> ( \<cn> if ( B \<in> \<complex> , B , \<zero> ) ) )" 
     by (rule MMI_opreq2d)
   have S6: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) )" 
     by (rule MMI_opreq2)
   from S5 S6 have S7: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
     ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> ( (\<cn>  B) ) ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B ) \<longleftrightarrow> 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> ( \<cn> if ( B \<in> \<complex> , B , \<zero> ) ) ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) ) )" 
     by (rule MMI_eqeq12d)
   have S8: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S8 have S9: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S10: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S10 have S11: "if ( B \<in> \<complex> , B , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S9 S11 have S12: 
     "( if ( A \<in> \<complex> , A , \<zero> ) \<ca> ( \<cn> if ( B \<in> \<complex> , B , \<zero> ) ) ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) )" 
     by (rule MMI_negsub)
   from S3 S7 S12 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> ( (\<cn>  B) ) ) = 
     ( A \<cs> B )" by (rule MMI_dedth2h)
qed

lemma (in MMIsar0) MMI_addsubasst: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<cs> C ) = 
  ( A \<ca> ( B \<cs> C ) )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> ( \<cn> C ) \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<ca> ( \<cn> C ) ) = 
     ( A \<ca> ( B \<ca> ( \<cn> C ) ) )" by (rule MMI_axaddass)
   have S2: "C \<in> \<complex> \<longrightarrow> ( \<cn> C ) \<in> \<complex>" by (rule MMI_negclt)
   from S1 S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<ca> ( \<cn> C ) ) = 
     ( A \<ca> ( B \<ca> ( \<cn> C ) ) )" by (rule MMI_syl3an3)
   have S4: "( ( A \<ca> B ) \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<ca> ( \<cn> C ) ) = ( ( A \<ca> B ) \<cs> C )" 
     by (rule MMI_negsubt)
   have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> B ) \<in> \<complex>" by (rule MMI_axaddcl)
   from S4 S5 have S6: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<ca> ( \<cn> C ) ) = ( ( A \<ca> B ) \<cs> C )" 
     by (rule MMI_sylan)
   from S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<ca> ( \<cn> C ) ) = ( ( A \<ca> B ) \<cs> C )" 
     by (rule MMI_3impa)
   have S8: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<ca> ( \<cn> C ) ) = ( B \<cs> C )" 
     by (rule MMI_negsubt)
   from S8 have S9: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( B \<ca> ( \<cn> C ) ) = ( B \<cs> C )" by (rule MMI_3adant1)
   from S9 have S10: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( A \<ca> ( B \<ca> ( \<cn> C ) ) ) = ( A \<ca> ( B \<cs> C ) )" 
     by (rule MMI_opreq2d)
   from S3 S7 S10 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cs> C ) = ( A \<ca> ( B \<cs> C ) )" 
     by (rule MMI_3eqtr3d)
qed

lemma (in MMIsar0) MMI_addsubt: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<cs> C ) = 
  ( ( A \<cs> C ) \<ca> B )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> B ) = ( B \<ca> A )" 
     by (rule MMI_axaddcom)
   from S1 have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<cs> C ) = 
     ( ( B \<ca> A ) \<cs> C )" by (rule MMI_opreq1d)
   from S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cs> C ) = ( ( B \<ca> A ) \<cs> C )" 
     by (rule MMI_3adant3)
   have S4: "( B \<in> \<complex> \<and> A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( B \<ca> A ) \<cs> C ) = 
     ( B \<ca> ( A \<cs> C ) )" by (rule MMI_addsubasst)
   from S4 have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( B \<ca> A ) \<cs> C ) = ( B \<ca> ( A \<cs> C ) )" by (rule MMI_3com12)
   have S6: "( B \<in> \<complex> \<and> ( A \<cs> C ) \<in> \<complex> ) \<longrightarrow> ( B \<ca> ( A \<cs> C ) ) = 
     ( ( A \<cs> C ) \<ca> B )" by (rule MMI_axaddcom)
   from S6 have S7: "B \<in> \<complex> \<longrightarrow> ( ( A \<cs> C ) \<in> \<complex> \<longrightarrow> 
     ( B \<ca> ( A \<cs> C ) ) = ( ( A \<cs> C ) \<ca> B ) )" by (rule MMI_ex)
   have S8: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cs> C ) \<in> \<complex>" by (rule MMI_subclt)
   from S7 S8 have S9: "B \<in> \<complex> \<longrightarrow> ( ( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( B \<ca> ( A \<cs> C ) ) = ( ( A \<cs> C ) \<ca> B ) )" by (rule MMI_syl5)
   from S9 have S10: "B \<in> \<complex> \<longrightarrow> ( A \<in> \<complex> \<longrightarrow> ( C \<in> \<complex> \<longrightarrow> 
     ( B \<ca> ( A \<cs> C ) ) = ( ( A \<cs> C ) \<ca> B ) ) )" 
     by (rule MMI_exp3a)
   from S10 have S11: "A \<in> \<complex> \<longrightarrow> ( B \<in> \<complex> \<longrightarrow> ( C \<in> \<complex> \<longrightarrow> 
     ( B \<ca> ( A \<cs> C ) ) = ( ( A \<cs> C ) \<ca> B ) ) )" 
     by (rule MMI_com12)
   from S11 have S12: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( B \<ca> ( A \<cs> C ) ) = ( ( A \<cs> C ) \<ca> B )" by (rule MMI_3imp)
   from S3 S5 S12 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cs> C ) = ( ( A \<cs> C ) \<ca> B )" by (rule MMI_3eqtrd)
qed

(******** 54-63**************************************)

lemma (in MMIsar0) MMI_addsub12t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<ca> ( B \<cs> C ) ) = 
  ( B \<ca> ( A \<cs> C ) )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> B ) = ( B \<ca> A )" 
     by (rule MMI_axaddcom)
   from S1 have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<cs> C ) = 
     ( ( B \<ca> A ) \<cs> C )" by (rule MMI_opreq1d)
   from S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cs> C ) = ( ( B \<ca> A ) \<cs> C )" 
     by (rule MMI_3adant3)
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<cs> C ) = 
     ( A \<ca> ( B \<cs> C ) )" by (rule MMI_addsubasst)
   have S5: "( B \<in> \<complex> \<and> A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( B \<ca> A ) \<cs> C ) = 
     ( B \<ca> ( A \<cs> C ) )" by (rule MMI_addsubasst)
   from S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( B \<ca> A ) \<cs> C ) = ( B \<ca> ( A \<cs> C ) )" by (rule MMI_3com12)
   from S3 S4 S6 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( A \<ca> ( B \<cs> C ) ) = ( B \<ca> ( A \<cs> C ) )" 
     by (rule MMI_3eqtr3d)
qed

lemma (in MMIsar0) MMI_addsubass: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( ( A \<ca> B ) \<cs> C ) = ( A \<ca> ( B \<cs> C ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<cs> C ) = 
     ( A \<ca> ( B \<cs> C ) )" by (rule MMI_addsubasst)
   from S1 S2 S3 S4 show "( ( A \<ca> B ) \<cs> C ) = 
     ( A \<ca> ( B \<cs> C ) )" by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_addsub: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( ( A \<ca> B ) \<cs> C ) = ( ( A \<cs> C ) \<ca> B )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<cs> C ) = 
     ( ( A \<cs> C ) \<ca> B )" by (rule MMI_addsubt)
   from S1 S2 S3 S4 show "( ( A \<ca> B ) \<cs> C ) = 
     ( ( A \<cs> C ) \<ca> B )" by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_2addsubt: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
  ( ( ( A \<ca> B ) \<ca> C ) \<cs> D ) = ( ( ( A \<ca> C ) \<cs> D ) \<ca> B )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<ca> C ) = 
     ( ( A \<ca> C ) \<ca> B )" by (rule MMI_add23t)
   from S1 have S2: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<ca> C ) = ( ( A \<ca> C ) \<ca> B )" by (rule MMI_3expa)
   from S2 have S3: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<ca> B ) \<ca> C ) = ( ( A \<ca> C ) \<ca> B )" 
     by (rule MMI_adantrr)
   from S3 have S4: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<ca> B ) \<ca> C ) \<cs> D ) = 
     ( ( ( A \<ca> C ) \<ca> B ) \<cs> D )" by (rule MMI_opreq1d)
   have S5: "( ( A \<ca> C ) \<in> \<complex> \<and> B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<ca> C ) \<ca> B ) \<cs> D ) = 
     ( ( ( A \<ca> C ) \<cs> D ) \<ca> B )" by (rule MMI_addsubt)
   from S5 have S6: "( ( A \<ca> C ) \<in> \<complex> \<and> ( B \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<ca> C ) \<ca> B ) \<cs> D ) = 
     ( ( ( A \<ca> C ) \<cs> D ) \<ca> B )" by (rule MMI_3expb)
   have S7: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<ca> C ) \<in> \<complex>" by (rule MMI_axaddcl)
   from S6 S7 have S8: "( ( A \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<ca> C ) \<ca> B ) \<cs> D ) = 
     ( ( ( A \<ca> C ) \<cs> D ) \<ca> B )" by (rule MMI_sylan)
   from S8 have S9: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<ca> C ) \<ca> B ) \<cs> D ) = 
     ( ( ( A \<ca> C ) \<cs> D ) \<ca> B )" by (rule MMI_an4s)
   from S4 S9 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<ca> B ) \<ca> C ) \<cs> D ) = 
     ( ( ( A \<ca> C ) \<cs> D ) \<ca> B )" by (rule MMI_eqtrd)
qed

lemma (in MMIsar0) MMI_negneg: assumes A1: "A \<in> \<complex>"   
   shows "( \<cn> ( (\<cn>  A) ) ) = A"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from S1 have S2: "( (\<cn>  A) ) \<in> \<complex>" by (rule MMI_negcl)
   from S2 have S3: "( ( (\<cn>  A) ) \<ca> ( \<cn> ( (\<cn>  A) ) ) ) = \<zero>" 
     by (rule MMI_negid)
   from S3 have S4: "( A \<ca> ( ( (\<cn>  A) ) \<ca> ( \<cn> ( (\<cn>  A) ) ) ) ) = 
     ( A \<ca> \<zero> )" by (rule MMI_opreq2i)
   from A1 have S5: "A \<in> \<complex>".
   from S5 have S6: "( A \<ca> ( (\<cn>  A) ) ) = \<zero>" by (rule MMI_negid)
   from S6 have S7: "( ( A \<ca> ( (\<cn>  A) ) ) \<ca> ( \<cn> ( (\<cn>  A) ) ) ) = 
     ( \<zero> \<ca> ( \<cn> ( (\<cn>  A) ) ) )" by (rule MMI_opreq1i)
   from A1 have S8: "A \<in> \<complex>".
   from S2 have S9: "( (\<cn>  A) ) \<in> \<complex>" .
   from S2 have S10: "( (\<cn>  A) ) \<in> \<complex>" .
   from S10 have S11: "( \<cn> ( (\<cn>  A) ) ) \<in> \<complex>" by (rule MMI_negcl)
   from S8 S9 S11 have S12: 
     "( ( A \<ca> ( (\<cn>  A) ) ) \<ca> ( \<cn> ( (\<cn>  A) ) ) ) = 
     ( A \<ca> ( ( (\<cn>  A) ) \<ca> ( \<cn> ( (\<cn>  A) ) ) ) )" 
     by (rule MMI_addass)
   from S11 have S13: "( \<cn> ( (\<cn>  A) ) ) \<in> \<complex>" .
   from S13 have S14: "( \<zero> \<ca> ( \<cn> ( (\<cn>  A) ) ) ) = 
     ( \<cn> ( (\<cn>  A) ) )" by (rule MMI_addid2)
   from S7 S12 S14 have S15: 
     "( A \<ca> ( ( (\<cn>  A) ) \<ca> ( \<cn> ( (\<cn>  A) ) ) ) ) = 
     ( \<cn> ( (\<cn>  A) ) )" by (rule MMI_3eqtr3)
   from A1 have S16: "A \<in> \<complex>".
   from S16 have S17: "( A \<ca> \<zero> ) = A" by (rule MMI_addid1)
   from S4 S15 S17 show "( \<cn> ( (\<cn>  A) ) ) = A" by (rule MMI_3eqtr3)
qed

lemma (in MMIsar0) MMI_subid: assumes A1: "A \<in> \<complex>"   
   shows "( A \<cs> A ) = \<zero>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A1 have S2: "A \<in> \<complex>".
   from S1 S2 have S3: "( A \<ca> ( (\<cn>  A) ) ) = ( A \<cs> A )" 
     by (rule MMI_negsub)
   from A1 have S4: "A \<in> \<complex>".
   from S4 have S5: "( A \<ca> ( (\<cn>  A) ) ) = \<zero>" by (rule MMI_negid)
   from S3 S5 show "( A \<cs> A ) = \<zero>" by (rule MMI_eqtr3)
qed

lemma (in MMIsar0) MMI_subid1: assumes A1: "A \<in> \<complex>"   
   shows "( A \<cs> \<zero> ) = A"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from S1 have S2: "( \<zero> \<ca> A ) = A" by (rule MMI_addid2)
   from A1 have S3: "A \<in> \<complex>".
   have S4: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from A1 have S5: "A \<in> \<complex>".
   from S3 S4 S5 have S6: "( A \<cs> \<zero> ) = A \<longleftrightarrow> ( \<zero> \<ca> A ) = A" 
     by (rule MMI_subadd)
   from S2 S6 show "( A \<cs> \<zero> ) = A" by (rule MMI_mpbir)
qed

lemma (in MMIsar0) MMI_negnegt: 
   shows "A \<in> \<complex> \<longrightarrow> ( \<cn> ( (\<cn>  A) ) ) = A"
proof -
   have S1: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> ( (\<cn>  A) ) = 
     ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_negeq)
   from S1 have S2: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> ( \<cn> ( (\<cn>  A) ) ) = 
     ( \<cn> ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) )" by (rule MMI_negeqd)
   have S3: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> A = if ( A \<in> \<complex> , A , \<zero> )" 
     by (rule MMI_id)
   from S2 S3 have S4: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
     ( ( \<cn> ( (\<cn>  A) ) ) = A \<longleftrightarrow> 
     ( \<cn> ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) ) = if ( A \<in> \<complex> , A , \<zero> ) )" 
     by (rule MMI_eqeq12d)
   have S5: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S5 have S6: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S6 have S7: "( \<cn> ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) ) = 
     if ( A \<in> \<complex> , A , \<zero> )" by (rule MMI_negneg)
   from S4 S7 show "A \<in> \<complex> \<longrightarrow> ( \<cn> ( (\<cn>  A) ) ) = A" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_subnegt: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cs> ( (\<cn>  B) ) ) = ( A \<ca> B )"
proof -
   have S1: "( A \<in> \<complex> \<and> ( (\<cn>  B) ) \<in> \<complex> ) \<longrightarrow> 
     ( A \<ca> ( \<cn> ( (\<cn>  B) ) ) ) = ( A \<cs> ( (\<cn>  B) ) )" 
     by (rule MMI_negsubt)
   have S2: "B \<in> \<complex> \<longrightarrow> ( (\<cn>  B) ) \<in> \<complex>" by (rule MMI_negclt)
   from S1 S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
     ( A \<ca> ( \<cn> ( (\<cn>  B) ) ) ) = ( A \<cs> ( (\<cn>  B) ) )" 
     by (rule MMI_sylan2)
   have S4: "B \<in> \<complex> \<longrightarrow> ( \<cn> ( (\<cn>  B) ) ) = B" by (rule MMI_negnegt)
   from S4 have S5: "B \<in> \<complex> \<longrightarrow> ( A \<ca> ( \<cn> ( (\<cn>  B) ) ) ) = 
     ( A \<ca> B )" by (rule MMI_opreq2d)
   from S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
     ( A \<ca> ( \<cn> ( (\<cn>  B) ) ) ) = ( A \<ca> B )" by (rule MMI_adantl)
   from S3 S6 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cs> ( (\<cn>  B) ) ) = 
     ( A \<ca> B )" by (rule MMI_eqtr3d)
qed

lemma (in MMIsar0) MMI_subidt: 
   shows "A \<in> \<complex> \<longrightarrow> ( A \<cs> A ) = \<zero>"
proof -
   have S1: "( A = if ( A \<in> \<complex> , A , \<zero> ) \<and> A = if ( A \<in> \<complex> , A , \<zero> ) ) \<longrightarrow> 
     ( A \<cs> A ) = ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( A \<in> \<complex> , A , \<zero> ) )" 
     by (rule MMI_opreq12)
   from S1 have S2: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
     ( A \<cs> A ) = ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( A \<in> \<complex> , A , \<zero> ) )" 
     by (rule MMI_anidms)
   from S2 have S3: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
     ( ( A \<cs> A ) = \<zero> \<longleftrightarrow> 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( A \<in> \<complex> , A , \<zero> ) ) = \<zero> )" 
     by (rule MMI_eqeq1d)
   have S4: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S4 have S5: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S5 have S6: 
     "( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( A \<in> \<complex> , A , \<zero> ) ) = \<zero>" 
     by (rule MMI_subid)
   from S3 S6 show "A \<in> \<complex> \<longrightarrow> ( A \<cs> A ) = \<zero>" by (rule MMI_dedth)
qed

(************** 64-73 *************************************)
lemma (in MMIsar0) MMI_subid1t: 
   shows "A \<in> \<complex> \<longrightarrow> ( A \<cs> \<zero> ) = A"
proof -
   have S1: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> ( A \<cs> \<zero> ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> \<zero> )" by (rule MMI_opreq1)
   have S2: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
     A = if ( A \<in> \<complex> , A , \<zero> )" by (rule MMI_id)
   from S1 S2 have S3: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
     ( ( A \<cs> \<zero> ) = A \<longleftrightarrow> ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> \<zero> ) = 
     if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_eqeq12d)
   have S4: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S4 have S5: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S5 have S6: "( if ( A \<in> \<complex> , A , \<zero> ) \<cs> \<zero> ) = 
     if ( A \<in> \<complex> , A , \<zero> )" by (rule MMI_subid1)
   from S3 S6 show "A \<in> \<complex> \<longrightarrow> ( A \<cs> \<zero> ) = A" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_pncant: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<cs> B ) = A"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<cs> B ) = 
     ( A \<ca> ( B \<cs> B ) )" by (rule MMI_addsubasst)
   from S1 have S2: "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> B \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cs> B ) = ( A \<ca> ( B \<cs> B ) )" by (rule MMI_3expb)
   from S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<cs> B ) = 
     ( A \<ca> ( B \<cs> B ) )" by (rule MMI_anabsan2)
   have S4: "B \<in> \<complex> \<longrightarrow> ( B \<cs> B ) = \<zero>" by (rule MMI_subidt)
   from S4 have S5: "B \<in> \<complex> \<longrightarrow> ( A \<ca> ( B \<cs> B ) ) = ( A \<ca> \<zero> )" 
     by (rule MMI_opreq2d)
   have S6: "A \<in> \<complex> \<longrightarrow> ( A \<ca> \<zero> ) = A" by (rule MMI_ax0id)
   from S5 S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> ( B \<cs> B ) ) = A" 
     by (rule MMI_sylan9eqr)
   from S3 S7 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<cs> B ) = A" 
     by (rule MMI_eqtrd)
qed

lemma (in MMIsar0) MMI_pncan2t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<cs> A ) = B"
proof -
   have S1: "( B \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> ( B \<ca> A ) = ( A \<ca> B )" 
     by (rule MMI_axaddcom)
   from S1 have S2: "( B \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> ( ( B \<ca> A ) \<cs> A ) = 
     ( ( A \<ca> B ) \<cs> A )" by (rule MMI_opreq1d)
   have S3: "( B \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> ( ( B \<ca> A ) \<cs> A ) = B" 
     by (rule MMI_pncant)
   from S2 S3 have S4: "( B \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cs> A ) = B" by (rule MMI_eqtr3d)
   from S4 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<cs> A ) = B" 
     by (rule MMI_ancoms)
qed

lemma (in MMIsar0) MMI_npcant: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<cs> B ) \<ca> B ) = A"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cs> B ) = ( ( A \<cs> B ) \<ca> B )" 
     by (rule MMI_addsubt)
   from S1 have S2: "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> B \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cs> B ) = ( ( A \<cs> B ) \<ca> B )" by (rule MMI_3expb)
   from S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cs> B ) = ( ( A \<cs> B ) \<ca> B )" 
     by (rule MMI_anabsan2)
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<ca> B ) \<cs> B ) = A" 
     by (rule MMI_pncant)
   from S3 S4 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<cs> B ) \<ca> B ) = A" 
     by (rule MMI_eqtr3d)
qed

lemma (in MMIsar0) MMI_npncant: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
  ( ( A \<cs> B ) \<ca> ( B \<cs> C ) ) = ( A \<cs> C )"
proof -
   have S1: "( ( A \<cs> B ) \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<cs> B ) \<ca> B ) \<cs> C ) = 
     ( ( A \<cs> B ) \<ca> ( B \<cs> C ) )" by (rule MMI_addsubasst)
   have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cs> B ) \<in> \<complex>" by (rule MMI_subclt)
   from S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( A \<cs> B ) \<in> \<complex>" by (rule MMI_3adant3)
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> B \<in> \<complex>" by (rule MMI_3simp2)
   have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> C \<in> \<complex>" by (rule MMI_3simp3)
   from S1 S3 S4 S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<cs> B ) \<ca> B ) \<cs> C ) = 
     ( ( A \<cs> B ) \<ca> ( B \<cs> C ) )" by (rule MMI_syl3anc)
   have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<cs> B ) \<ca> B ) = A" 
     by (rule MMI_npcant)
   from S7 have S8: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<cs> B ) \<ca> B ) \<cs> C ) = ( A \<cs> C )" 
     by (rule MMI_opreq1d)
   from S8 have S9: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<cs> B ) \<ca> B ) \<cs> C ) = ( A \<cs> C )" 
     by (rule MMI_3adant3)
   from S6 S9 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<cs> B ) \<ca> ( B \<cs> C ) ) = ( A \<cs> C )" 
     by (rule MMI_eqtr3d)
qed

lemma (in MMIsar0) MMI_nppcant: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
  ( ( ( A \<cs> B ) \<ca> C ) \<ca> B ) = ( A \<ca> C )"
proof -
   have S1: "( ( A \<cs> B ) \<in> \<complex> \<and> C \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<cs> B ) \<ca> C ) \<ca> B ) = 
     ( ( ( A \<cs> B ) \<ca> B ) \<ca> C )" by (rule MMI_add23t)
   have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cs> B ) \<in> \<complex>" by (rule MMI_subclt)
   from S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cs> B ) \<in> \<complex>" 
     by (rule MMI_3adant3)
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> C \<in> \<complex>" by (rule MMI_3simp3)
   have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> B \<in> \<complex>" by (rule MMI_3simp2)
   from S1 S3 S4 S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<cs> B ) \<ca> C ) \<ca> B ) = 
     ( ( ( A \<cs> B ) \<ca> B ) \<ca> C )" by (rule MMI_syl3anc)
   have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<cs> B ) \<ca> B ) = A" 
     by (rule MMI_npcant)
   from S7 have S8: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<cs> B ) \<ca> B ) \<ca> C ) = ( A \<ca> C )" 
     by (rule MMI_opreq1d)
   from S8 have S9: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<cs> B ) \<ca> B ) \<ca> C ) = ( A \<ca> C )" 
     by (rule MMI_3adant3)
   from S6 S9 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<cs> B ) \<ca> C ) \<ca> B ) = ( A \<ca> C )" by (rule MMI_eqtrd)
qed

lemma (in MMIsar0) MMI_subneg: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( A \<cs> ( (\<cn>  B) ) ) = ( A \<ca> B )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cs> ( (\<cn>  B) ) ) = ( A \<ca> B )" 
     by (rule MMI_subnegt)
   from S1 S2 S3 show "( A \<cs> ( (\<cn>  B) ) ) = ( A \<ca> B )" 
     by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_subeq0: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( A \<cs> B ) = \<zero> \<longleftrightarrow> A = B"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from S1 S2 have S3: "( A \<ca> ( (\<cn>  B) ) ) = ( A \<cs> B )" 
     by (rule MMI_negsub)
   from S3 have S4: "( A \<ca> ( (\<cn>  B) ) ) = \<zero> \<longleftrightarrow> ( A \<cs> B ) = \<zero>" 
     by (rule MMI_eqeq1i)
   have S5: "( A \<ca> ( (\<cn>  B) ) ) = \<zero> \<longrightarrow> 
     ( ( A \<ca> ( (\<cn>  B) ) ) \<ca> B ) = ( \<zero> \<ca> B )" by (rule MMI_opreq1)
   from S4 S5 have S6: "( A \<cs> B ) = \<zero> \<longrightarrow> 
     ( ( A \<ca> ( (\<cn>  B) ) ) \<ca> B ) = ( \<zero> \<ca> B )" by (rule MMI_sylbir)
   from A1 have S7: "A \<in> \<complex>".
   from A2 have S8: "B \<in> \<complex>".
   from S8 have S9: "( (\<cn>  B) ) \<in> \<complex>" by (rule MMI_negcl)
   from A2 have S10: "B \<in> \<complex>".
   from S7 S9 S10 have S11: "( ( A \<ca> ( (\<cn>  B) ) ) \<ca> B ) = 
     ( ( A \<ca> B ) \<ca> ( (\<cn>  B) ) )" by (rule MMI_add23)
   from A1 have S12: "A \<in> \<complex>".
   from A2 have S13: "B \<in> \<complex>".
   from S9 have S14: "( (\<cn>  B) ) \<in> \<complex>" .
   from S12 S13 S14 have S15: "( ( A \<ca> B ) \<ca> ( (\<cn>  B) ) ) = 
     ( A \<ca> ( B \<ca> ( (\<cn>  B) ) ) )" by (rule MMI_addass)
   from A2 have S16: "B \<in> \<complex>".
   from S16 have S17: "( B \<ca> ( (\<cn>  B) ) ) = \<zero>" by (rule MMI_negid)
   from S17 have S18: "( A \<ca> ( B \<ca> ( (\<cn>  B) ) ) ) = ( A \<ca> \<zero> )" 
     by (rule MMI_opreq2i)
   from A1 have S19: "A \<in> \<complex>".
   from S19 have S20: "( A \<ca> \<zero> ) = A" by (rule MMI_addid1)
   from S18 S20 have S21: "( A \<ca> ( B \<ca> ( (\<cn>  B) ) ) ) = A" 
     by (rule MMI_eqtr)
   from S11 S15 S21 have S22: "( ( A \<ca> ( (\<cn>  B) ) ) \<ca> B ) = A" 
     by (rule MMI_3eqtr)
   from A2 have S23: "B \<in> \<complex>".
   from S23 have S24: "( \<zero> \<ca> B ) = B" by (rule MMI_addid2)
   from S6 S22 S24 have S25: "( A \<cs> B ) = \<zero> \<longrightarrow> A = B" 
     by (rule MMI_3eqtr3g)
   have S26: "A = B \<longrightarrow> ( A \<cs> B ) = ( B \<cs> B )" by (rule MMI_opreq1)
   from A2 have S27: "B \<in> \<complex>".
   from S27 have S28: "( B \<cs> B ) = \<zero>" by (rule MMI_subid)
   from S26 S28 have S29: "A = B \<longrightarrow> ( A \<cs> B ) = \<zero>" by (rule MMI_syl6eq)
   from S25 S29 show "( A \<cs> B ) = \<zero> \<longleftrightarrow> A = B" by (rule MMI_impbi)
qed

lemma (in MMIsar0) MMI_neg11: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( (\<cn>  A) ) = ( (\<cn>  B) ) \<longleftrightarrow> A = B"
proof -
   have S1: "( (\<cn>  A) ) = ( \<zero> \<cs> A )" by (rule MMI_df_neg)
   have S2: "( (\<cn>  B) ) = ( \<zero> \<cs> B )" by (rule MMI_df_neg)
   from S1 S2 have S3: "( (\<cn>  A) ) = ( (\<cn>  B) ) \<longleftrightarrow> ( \<zero> \<cs> A ) = 
     ( \<zero> \<cs> B )" by (rule MMI_eqeq12i)
   have S4: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from A1 have S5: "A \<in> \<complex>".
   have S6: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from A2 have S7: "B \<in> \<complex>".
   from S6 S7 have S8: "( \<zero> \<cs> B ) \<in> \<complex>" by (rule MMI_subcl)
   from S4 S5 S8 have S9: "( \<zero> \<cs> A ) = ( \<zero> \<cs> B ) \<longleftrightarrow> 
     ( A \<ca> ( \<zero> \<cs> B ) ) = \<zero>" by (rule MMI_subadd)
   from S2 have S10: "( (\<cn>  B) ) = ( \<zero> \<cs> B )" .
   from S10 have S11: "( A \<ca> ( (\<cn>  B) ) ) = ( A \<ca> ( \<zero> \<cs> B ) )" 
     by (rule MMI_opreq2i)
   from A1 have S12: "A \<in> \<complex>".
   from A2 have S13: "B \<in> \<complex>".
   from S12 S13 have S14: "( A \<ca> ( (\<cn>  B) ) ) = ( A \<cs> B )" 
     by (rule MMI_negsub)
   from S11 S14 have S15: "( A \<ca> ( \<zero> \<cs> B ) ) = ( A \<cs> B )" 
     by (rule MMI_eqtr3)
   from S15 have S16: "( A \<ca> ( \<zero> \<cs> B ) ) = \<zero> \<longleftrightarrow> ( A \<cs> B ) = \<zero>" 
     by (rule MMI_eqeq1i)
   from A1 have S17: "A \<in> \<complex>".
   from A2 have S18: "B \<in> \<complex>".
   from S17 S18 have S19: "( A \<cs> B ) = \<zero> \<longleftrightarrow> A = B" by (rule MMI_subeq0)
   from S16 S19 have S20: "( A \<ca> ( \<zero> \<cs> B ) ) = \<zero> \<longleftrightarrow> A = B" 
     by (rule MMI_bitr)
   from S3 S9 S20 show "( (\<cn>  A) ) = ( (\<cn>  B) ) \<longleftrightarrow> A = B" by (rule MMI_3bitr)
qed

(*********** 75-84****************************************)

lemma (in MMIsar0) MMI_negcon1: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( (\<cn>  A) ) = B \<longleftrightarrow> ( (\<cn>  B) ) = A"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from S1 have S2: "( \<cn> ( (\<cn>  A) ) ) = A" by (rule MMI_negneg)
   from S2 have S3: "( \<cn> ( (\<cn>  A) ) ) = ( (\<cn>  B) ) \<longleftrightarrow> A = ( (\<cn>  B) )" 
     by (rule MMI_eqeq1i)
   from A1 have S4: "A \<in> \<complex>".
   from S4 have S5: "( (\<cn>  A) ) \<in> \<complex>" by (rule MMI_negcl)
   from A2 have S6: "B \<in> \<complex>".
   from S5 S6 have S7: "( \<cn> ( (\<cn>  A) ) ) = 
     ( (\<cn>  B) ) \<longleftrightarrow> ( (\<cn>  A) ) = B" by (rule MMI_neg11)
   have S8: "A = ( (\<cn>  B) ) \<longleftrightarrow> ( (\<cn>  B) ) = A" by (rule MMI_eqcom)
   from S3 S7 S8 show "( (\<cn>  A) ) = B \<longleftrightarrow> ( (\<cn>  B) ) = A" by (rule MMI_3bitr3)
qed

lemma (in MMIsar0) MMI_negcon2: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "A = ( (\<cn>  B) ) \<longleftrightarrow> B = ( (\<cn>  A) )"
proof -
   from A2 have S1: "B \<in> \<complex>".
   from A1 have S2: "A \<in> \<complex>".
   from S1 S2 have S3: "( (\<cn>  B) ) = A \<longleftrightarrow> ( (\<cn>  A) ) = B" 
     by (rule MMI_negcon1)
   have S4: "A = ( (\<cn>  B) ) \<longleftrightarrow> ( (\<cn>  B) ) = A" by (rule MMI_eqcom)
   have S5: "B = ( (\<cn>  A) ) \<longleftrightarrow> ( (\<cn>  A) ) = B" by (rule MMI_eqcom)
   from S3 S4 S5 show "A = ( (\<cn>  B) ) \<longleftrightarrow> B = ( (\<cn>  A) )" by (rule MMI_3bitr4)
qed

lemma (in MMIsar0) MMI_neg11t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( (\<cn>  A) ) = ( (\<cn>  B) ) \<longleftrightarrow> A = B )"
proof -
   have S1: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> ( (\<cn>  A) ) = 
     ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_negeq)
   from S1 have S2: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> ( ( (\<cn>  A) ) = 
     ( (\<cn>  B) ) \<longleftrightarrow> ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) = ( (\<cn>  B) ) )" 
     by (rule MMI_eqeq1d)
   have S3: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> ( A = B \<longleftrightarrow> 
     if ( A \<in> \<complex> , A , \<zero> ) = B )" by (rule MMI_eqeq1)
   from S2 S3 have S4: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
     ( ( ( (\<cn>  A) ) = ( (\<cn>  B) ) \<longleftrightarrow> A = B ) \<longleftrightarrow> 
     ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) = ( (\<cn>  B) ) \<longleftrightarrow> 
     if ( A \<in> \<complex> , A , \<zero> ) = B ) )" by (rule MMI_bibi12d)
   have S5: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> ( (\<cn>  B) ) = 
     ( \<cn> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_negeq)
   from S5 have S6: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
     ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) = ( (\<cn>  B) ) \<longleftrightarrow> 
     ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) = ( \<cn> if ( B \<in> \<complex> , B , \<zero> ) ) )" 
     by (rule MMI_eqeq2d)
   have S7: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> ( if ( A \<in> \<complex> , A , \<zero> ) = B \<longleftrightarrow> 
     if ( A \<in> \<complex> , A , \<zero> ) = if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_eqeq2)
   from S6 S7 have S8: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
     ( ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) = ( (\<cn>  B) ) \<longleftrightarrow> 
     if ( A \<in> \<complex> , A , \<zero> ) = B ) \<longleftrightarrow> ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) = 
     ( \<cn> if ( B \<in> \<complex> , B , \<zero> ) ) \<longleftrightarrow> if ( A \<in> \<complex> , A , \<zero> ) = 
     if ( B \<in> \<complex> , B , \<zero> ) ) )" by (rule MMI_bibi12d)
   have S9: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S9 have S10: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S11: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S11 have S12: "if ( B \<in> \<complex> , B , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S10 S12 have S13: "( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) = 
     ( \<cn> if ( B \<in> \<complex> , B , \<zero> ) ) \<longleftrightarrow> if ( A \<in> \<complex> , A , \<zero> ) = 
     if ( B \<in> \<complex> , B , \<zero> )" by (rule MMI_neg11)
   from S4 S8 S13 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( (\<cn>  A) ) = 
     ( (\<cn>  B) ) \<longleftrightarrow> A = B )" by (rule MMI_dedth2h)
qed

lemma (in MMIsar0) MMI_negcon1t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( (\<cn>  A) ) = B \<longleftrightarrow> ( (\<cn>  B) ) = A )"
proof -
   have S1: "( ( (\<cn>  A) ) \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( \<cn> ( (\<cn>  A) ) ) = 
     ( (\<cn>  B) ) \<longleftrightarrow> ( (\<cn>  A) ) = B )" by (rule MMI_neg11t)
   have S2: "A \<in> \<complex> \<longrightarrow> ( (\<cn>  A) ) \<in> \<complex>" by (rule MMI_negclt)
   from S1 S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( \<cn> ( (\<cn>  A) ) ) = 
     ( (\<cn>  B) ) \<longleftrightarrow> ( (\<cn>  A) ) = B )" by (rule MMI_sylan)
   have S4: "A \<in> \<complex> \<longrightarrow> ( \<cn> ( (\<cn>  A) ) ) = A" by (rule MMI_negnegt)
   from S4 have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( \<cn> ( (\<cn>  A) ) ) = A" 
     by (rule MMI_adantr)
   from S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( \<cn> ( (\<cn>  A) ) ) = 
     ( (\<cn>  B) ) \<longleftrightarrow> A = ( (\<cn>  B) ) )" by (rule MMI_eqeq1d)
   from S3 S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( (\<cn>  A) ) = B \<longleftrightarrow> A = 
     ( (\<cn>  B) ) )" by (rule MMI_bitr3d)
   have S8: "A = ( (\<cn>  B) ) \<longleftrightarrow> ( (\<cn>  B) ) = A" by (rule MMI_eqcom)
   from S7 S8 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( (\<cn>  A) ) = B \<longleftrightarrow> 
     ( (\<cn>  B) ) = A )" by (rule MMI_syl6bb)
qed

lemma (in MMIsar0) MMI_negcon2t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A = ( (\<cn>  B) ) \<longleftrightarrow> B = ( (\<cn>  A) ) )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( (\<cn>  A) ) = B \<longleftrightarrow> ( (\<cn>  B) ) = A )" 
     by (rule MMI_negcon1t)
   have S2: "A = ( (\<cn>  B) ) \<longleftrightarrow> ( (\<cn>  B) ) = A" by (rule MMI_eqcom)
   from S1 S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A = ( (\<cn>  B) ) \<longleftrightarrow> 
     ( (\<cn>  A) ) = B )" by (rule MMI_syl6rbbrA)
   have S4: "( (\<cn>  A) ) = B \<longleftrightarrow> B = ( (\<cn>  A) )" by (rule MMI_eqcom)
   from S3 S4 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A = ( (\<cn>  B) ) \<longleftrightarrow> B = 
     ( (\<cn>  A) ) )" by (rule MMI_syl6bb)
qed

lemma (in MMIsar0) MMI_subcant: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<cs> B ) = 
  ( A \<cs> C ) \<longleftrightarrow> B = C )"
proof -
   have S1: "( A \<in> \<complex> \<and> ( (\<cn>  B) ) \<in> \<complex> \<and> ( \<cn> C ) \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> ( (\<cn>  B) ) ) = ( A \<ca> ( \<cn> C ) ) \<longleftrightarrow> 
     ( (\<cn>  B) ) = ( \<cn> C ) )" by (rule MMI_addcant)
   have S2: "C \<in> \<complex> \<longrightarrow> ( \<cn> C ) \<in> \<complex>" by (rule MMI_negclt)
   from S1 S2 have S3: "( A \<in> \<complex> \<and> ( (\<cn>  B) ) \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> ( (\<cn>  B) ) ) = ( A \<ca> ( \<cn> C ) ) \<longleftrightarrow> 
     ( (\<cn>  B) ) = ( \<cn> C ) )" by (rule MMI_syl3an3)
   have S4: "B \<in> \<complex> \<longrightarrow> ( (\<cn>  B) ) \<in> \<complex>" by (rule MMI_negclt)
   from S3 S4 have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> ( (\<cn>  B) ) ) = ( A \<ca> ( \<cn> C ) ) \<longleftrightarrow> 
     ( (\<cn>  B) ) = ( \<cn> C ) )" by (rule MMI_syl3an2)
   have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> ( (\<cn>  B) ) ) = ( A \<cs> B )" 
     by (rule MMI_negsubt)
   from S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( A \<ca> ( (\<cn>  B) ) ) = ( A \<cs> B )" by (rule MMI_3adant3)
   have S8: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<ca> ( \<cn> C ) ) = ( A \<cs> C )" 
     by (rule MMI_negsubt)
   from S8 have S9: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( A \<ca> ( \<cn> C ) ) = ( A \<cs> C )" by (rule MMI_3adant2)
   from S7 S9 have S10: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> ( (\<cn>  B) ) ) = ( A \<ca> ( \<cn> C ) ) \<longleftrightarrow> 
     ( A \<cs> B ) = ( A \<cs> C ) )" by (rule MMI_eqeq12d)
   have S11: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( (\<cn>  B) ) = ( \<cn> C ) \<longleftrightarrow> B = C )" 
     by (rule MMI_neg11t)
   from S11 have S12: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( (\<cn>  B) ) = ( \<cn> C ) \<longleftrightarrow> B = C )" by (rule MMI_3adant1)
   from S5 S10 S12 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<cs> B ) = ( A \<cs> C ) \<longleftrightarrow> B = C )" by (rule MMI_3bitr3d)
qed

lemma (in MMIsar0) MMI_subcan2t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
  ( ( A \<cs> C ) = ( B \<cs> C ) \<longleftrightarrow> A = B )"
proof -
   have S1: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<ca> ( \<cn> C ) ) = ( A \<cs> C )" 
     by (rule MMI_negsubt)
   from S1 have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( A \<ca> ( \<cn> C ) ) = ( A \<cs> C )" by (rule MMI_3adant2)
   have S3: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<ca> ( \<cn> C ) ) = ( B \<cs> C )" 
     by (rule MMI_negsubt)
   from S3 have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( B \<ca> ( \<cn> C ) ) = ( B \<cs> C )" by (rule MMI_3adant1)
   from S2 S4 have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> ( \<cn> C ) ) = ( B \<ca> ( \<cn> C ) ) \<longleftrightarrow> ( A \<cs> C ) = 
     ( B \<cs> C ) )" by (rule MMI_eqeq12d)
   have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> ( \<cn> C ) \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> ( \<cn> C ) ) = ( B \<ca> ( \<cn> C ) ) \<longleftrightarrow> A = B )" 
     by (rule MMI_addcan2t)
   have S7: "C \<in> \<complex> \<longrightarrow> ( \<cn> C ) \<in> \<complex>" by (rule MMI_negclt)
   from S6 S7 have S8: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> ( \<cn> C ) ) = ( B \<ca> ( \<cn> C ) ) \<longleftrightarrow> A = B )" 
     by (rule MMI_syl3an3)
   from S5 S8 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<cs> C ) = ( B \<cs> C ) \<longleftrightarrow> A = B )" by (rule MMI_bitr3d)
qed

lemma (in MMIsar0) MMI_subcan: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( A \<cs> B ) = ( A \<cs> C ) \<longleftrightarrow> B = C"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<cs> B ) = ( A \<cs> C ) \<longleftrightarrow> B = C )" by (rule MMI_subcant)
   from S1 S2 S3 S4 show "( A \<cs> B ) = ( A \<cs> C ) \<longleftrightarrow> B = C" 
     by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_subcan2: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( A \<cs> C ) = ( B \<cs> C ) \<longleftrightarrow> A = B"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<cs> C ) = ( B \<cs> C ) \<longleftrightarrow> A = B )" by (rule MMI_subcan2t)
   from S1 S2 S3 S4 show "( A \<cs> C ) = ( B \<cs> C ) \<longleftrightarrow> A = B" 
     by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_subeq0t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<cs> B ) = \<zero> \<longleftrightarrow> A = B )"
proof -
   have S1: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> ( A \<cs> B ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B )" by (rule MMI_opreq1)
   from S1 have S2: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> ( ( A \<cs> B ) = \<zero> \<longleftrightarrow> 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B ) = \<zero> )" by (rule MMI_eqeq1d)
   have S3: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> ( A = B \<longleftrightarrow> 
     if ( A \<in> \<complex> , A , \<zero> ) = B )" by (rule MMI_eqeq1)
   from S2 S3 have S4: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
     ( ( ( A \<cs> B ) = \<zero> \<longleftrightarrow> A = B ) \<longleftrightarrow> 
     ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B ) = \<zero> \<longleftrightarrow> 
     if ( A \<in> \<complex> , A , \<zero> ) = B ) )" by (rule MMI_bibi12d)
   have S5: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B ) = 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) )" 
     by (rule MMI_opreq2)
   from S5 have S6: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
     ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B ) = \<zero> \<longleftrightarrow> 
     ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) ) = \<zero> )" 
     by (rule MMI_eqeq1d)
   have S7: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> ( if ( A \<in> \<complex> , A , \<zero> ) = B \<longleftrightarrow> 
     if ( A \<in> \<complex> , A , \<zero> ) = if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_eqeq2)
   from S6 S7 have S8: "B = if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
     ( ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> B ) = \<zero> \<longleftrightarrow> 
     if ( A \<in> \<complex> , A , \<zero> ) = B ) \<longleftrightarrow> 
     ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) ) = \<zero> \<longleftrightarrow> 
     if ( A \<in> \<complex> , A , \<zero> ) = if ( B \<in> \<complex> , B , \<zero> ) ) )" 
     by (rule MMI_bibi12d)
   have S9: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S9 have S10: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S11: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S11 have S12: "if ( B \<in> \<complex> , B , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S10 S12 have S13: 
     "( if ( A \<in> \<complex> , A , \<zero> ) \<cs> if ( B \<in> \<complex> , B , \<zero> ) ) = \<zero> \<longleftrightarrow> 
     if ( A \<in> \<complex> , A , \<zero> ) = if ( B \<in> \<complex> , B , \<zero> )" 
     by (rule MMI_subeq0)
   from S4 S8 S13 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<cs> B ) = \<zero> \<longleftrightarrow> A = B )" by (rule MMI_dedth2h)
qed

(*******************85-90*******************************)

lemma (in MMIsar0) MMI_neg0: 
   shows "( \<cn> \<zero> ) = \<zero>"
proof -
   have S1: "( \<cn> \<zero> ) = ( \<zero> \<cs> \<zero> )" by (rule MMI_df_neg)
   have S2: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S2 have S3: "( \<zero> \<cs> \<zero> ) = \<zero>" by (rule MMI_subid)
   from S1 S3 show "( \<cn> \<zero> ) = \<zero>" by (rule MMI_eqtr)
qed

lemma (in MMIsar0) MMI_renegcl: assumes A1: "A \<in> \<real>"   
   shows "( (\<cn>  A) ) \<in> \<real>"
proof -
   from A1 have S1: "A \<in> \<real>".
   have S2: "A \<in> \<real> \<longrightarrow> ( \<exists> x \<in> \<real> . ( A \<ca> x ) = \<zero> )" by (rule MMI_axrnegex)
   from S1 S2 have S3: "\<exists> x \<in> \<real> . ( A \<ca> x ) = \<zero>" by (rule MMI_ax_mp)
   have S4: "( \<exists> x \<in> \<real> . ( A \<ca> x ) = \<zero> ) \<longleftrightarrow> 
     ( \<exists> x . ( x \<in> \<real> \<and> ( A \<ca> x ) = \<zero> ) )" by (rule MMI_df_rex)
   from S3 S4 have S5: "\<exists> x . ( x \<in> \<real> \<and> ( A \<ca> x ) = \<zero> )" 
     by (rule MMI_mpbi)
   { fix x
     have S6: "x \<in> \<real> \<longrightarrow> x \<in> \<complex>" by (rule MMI_recnt)
     have S7: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
     from A1 have S8: "A \<in> \<real>".
     from S8 have S9: "A \<in> \<complex>" by (rule MMI_recn)
     have S10: "( \<zero> \<in> \<complex> \<and> A \<in> \<complex> \<and> x \<in> \<complex> ) \<longrightarrow> ( ( \<zero> \<cs> A ) = x \<longleftrightarrow> 
       ( A \<ca> x ) = \<zero> )" by (rule MMI_subaddt)
     from S7 S9 S10 have S11: "x \<in> \<complex> \<longrightarrow> ( ( \<zero> \<cs> A ) = x \<longleftrightarrow> 
       ( A \<ca> x ) = \<zero> )" by (rule MMI_mp3an12)
     from S6 S11 have S12: "x \<in> \<real> \<longrightarrow> ( ( \<zero> \<cs> A ) = x \<longleftrightarrow> 
       ( A \<ca> x ) = \<zero> )" by (rule MMI_syl)
     have S13: "( (\<cn>  A) ) = ( \<zero> \<cs> A )" by (rule MMI_df_neg)
     from S13 have S14: "( (\<cn>  A) ) = x \<longleftrightarrow> ( \<zero> \<cs> A ) = x" 
       by (rule MMI_eqeq1i)
     from S12 S14 have S15: "x \<in> \<real> \<longrightarrow> ( ( (\<cn>  A) ) = x \<longleftrightarrow> 
       ( A \<ca> x ) = \<zero> )" by (rule MMI_syl5bb)
     have S16: "x \<in> \<real> \<longrightarrow> ( ( (\<cn>  A) ) = x \<longrightarrow> ( (\<cn>  A) ) \<in> \<real> )" 
       by (rule MMI_eleq1a)
     from S15 S16 have S17: "x \<in> \<real> \<longrightarrow> ( ( A \<ca> x ) = \<zero> \<longrightarrow> 
       ( (\<cn>  A) ) \<in> \<real> )" by (rule MMI_sylbird)
     from S17 have "( x \<in> \<real> \<and> ( A \<ca> x ) = \<zero> ) \<longrightarrow> ( (\<cn>  A) ) \<in> \<real>" 
       by (rule MMI_imp)
     } then have S18: 
	 "\<forall>x . ( x \<in> \<real> \<and> ( A \<ca> x ) = \<zero> ) \<longrightarrow> ( (\<cn>  A) ) \<in> \<real>" 
       by auto
   from S18 have S19: "( \<exists> x . ( x \<in> \<real> \<and> ( A \<ca> x ) = \<zero> ) ) \<longrightarrow> 
     ( (\<cn>  A) ) \<in> \<real>" by (rule MMI_19_23aiv)
   from S5 S19 show "( (\<cn>  A) ) \<in> \<real>" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_renegclt: 
   shows "A \<in> \<real> \<longrightarrow> ( (\<cn>  A) ) \<in> \<real>"
proof -
   have S1: "A = if ( A \<in> \<real> , A , \<one> ) \<longrightarrow> ( (\<cn>  A) ) = 
     ( \<cn> if ( A \<in> \<real> , A , \<one> ) )" by (rule MMI_negeq)
   from S1 have S2: "A = if ( A \<in> \<real> , A , \<one> ) \<longrightarrow> ( ( (\<cn>  A) ) \<in> \<real> \<longleftrightarrow> 
     ( \<cn> if ( A \<in> \<real> , A , \<one> ) ) \<in> \<real> )" by (rule MMI_eleq1d)
   have S3: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S3 have S4: "if ( A \<in> \<real> , A , \<one> ) \<in> \<real>" by (rule MMI_elimel)
   from S4 have S5: "( \<cn> if ( A \<in> \<real> , A , \<one> ) ) \<in> \<real>" by (rule MMI_renegcl)
   from S2 S5 show "A \<in> \<real> \<longrightarrow> ( (\<cn>  A) ) \<in> \<real>" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_resubclt: 
   shows "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<cs> B ) \<in> \<real>"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> ( (\<cn>  B) ) ) = ( A \<cs> B )" 
     by (rule MMI_negsubt)
   have S2: "A \<in> \<real> \<longrightarrow> A \<in> \<complex>" by (rule MMI_recnt)
   have S3: "B \<in> \<real> \<longrightarrow> B \<in> \<complex>" by (rule MMI_recnt)
   from S1 S2 S3 have S4: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<ca> ( (\<cn>  B) ) ) = 
     ( A \<cs> B )" by (rule MMI_syl2an)
   have S5: "( A \<in> \<real> \<and> ( (\<cn>  B) ) \<in> \<real> ) \<longrightarrow> ( A \<ca> ( (\<cn>  B) ) ) \<in> \<real>" 
     by (rule MMI_axaddrcl)
   have S6: "B \<in> \<real> \<longrightarrow> ( (\<cn>  B) ) \<in> \<real>" by (rule MMI_renegclt)
   from S5 S6 have S7: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<ca> ( (\<cn>  B) ) ) \<in> \<real>" 
     by (rule MMI_sylan2)
   from S4 S7 show "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<cs> B ) \<in> \<real>" 
     by (rule MMI_eqeltrrd)
qed

lemma (in MMIsar0) MMI_resubcl: assumes A1: "A \<in> \<real>" and
    A2: "B \<in> \<real>"   
   shows "( A \<cs> B ) \<in> \<real>"
proof -
   from A1 have S1: "A \<in> \<real>".
   from A2 have S2: "B \<in> \<real>".
   have S3: "( A \<in> \<real> \<and> B \<in> \<real> ) \<longrightarrow> ( A \<cs> B ) \<in> \<real>" by (rule MMI_resubclt)
   from S1 S2 S3 show "( A \<cs> B ) \<in> \<real>" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_0re: 
   shows "\<zero> \<in> \<real>"
proof -
   have S1: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S1 have S2: "( \<one> \<cs> \<one> ) = \<zero>" by (rule MMI_subid)
   have S3: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   have S4: "\<one> \<in> \<real>" by (rule MMI_ax1re)
   from S3 S4 have S5: "( \<one> \<cs> \<one> ) \<in> \<real>" by (rule MMI_resubcl)
   from S2 S5 show "\<zero> \<in> \<real>" by (rule MMI_eqeltrr)
qed

(************** 91-95 ****************************************)

lemma (in MMIsar0) MMI_mulid2t: 
   shows "A \<in> \<complex> \<longrightarrow> ( \<one> \<cdot> A ) = A"
proof -
   have S1: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S2: "( \<one> \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> ( \<one> \<cdot> A ) = ( A \<cdot> \<one> )" 
     by (rule MMI_axmulcom)
   from S1 S2 have S3: "A \<in> \<complex> \<longrightarrow> ( \<one> \<cdot> A ) = ( A \<cdot> \<one> )" by (rule MMI_mpan)
   have S4: "A \<in> \<complex> \<longrightarrow> ( A \<cdot> \<one> ) = A" by (rule MMI_ax1id)
   from S3 S4 show "A \<in> \<complex> \<longrightarrow> ( \<one> \<cdot> A ) = A" by (rule MMI_eqtrd)
qed

lemma (in MMIsar0) MMI_mul12t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cdot> ( B \<cdot> C ) ) = 
  ( B \<cdot> ( A \<cdot> C ) )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cdot> B ) = ( B \<cdot> A )" 
     by (rule MMI_axmulcom)
   from S1 have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<cdot> B ) \<cdot> C ) = ( ( B \<cdot> A ) \<cdot> C )" by (rule MMI_opreq1d)
   from S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<cdot> B ) \<cdot> C ) = ( ( B \<cdot> A ) \<cdot> C )" by (rule MMI_3adant3)
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<cdot> B ) \<cdot> C ) = ( A \<cdot> ( B \<cdot> C ) )" by (rule MMI_axmulass)
   have S5: "( B \<in> \<complex> \<and> A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( B \<cdot> A ) \<cdot> C ) = ( B \<cdot> ( A \<cdot> C ) )" by (rule MMI_axmulass)
   from S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( B \<cdot> A ) \<cdot> C ) = ( B \<cdot> ( A \<cdot> C ) )" by (rule MMI_3com12)
   from S3 S4 S6 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( A \<cdot> ( B \<cdot> C ) ) = ( B \<cdot> ( A \<cdot> C ) )" by (rule MMI_3eqtr3d)
qed

lemma (in MMIsar0) MMI_mul23t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<cdot> B ) \<cdot> C ) = 
  ( ( A \<cdot> C ) \<cdot> B )"
proof -
   have S1: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<cdot> C ) = ( C \<cdot> B )" 
     by (rule MMI_axmulcom)
   from S1 have S2: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cdot> ( B \<cdot> C ) ) = 
     ( A \<cdot> ( C \<cdot> B ) )" by (rule MMI_opreq2d)
   from S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cdot> ( B \<cdot> C ) ) = 
     ( A \<cdot> ( C \<cdot> B ) )" by (rule MMI_3adant1)
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<cdot> B ) \<cdot> C ) = 
     ( A \<cdot> ( B \<cdot> C ) )" by (rule MMI_axmulass)
   have S5: "( A \<in> \<complex> \<and> C \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( A \<cdot> C ) \<cdot> B ) = 
     ( A \<cdot> ( C \<cdot> B ) )" by (rule MMI_axmulass)
   from S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<cdot> C ) \<cdot> B ) = ( A \<cdot> ( C \<cdot> B ) )" by (rule MMI_3com23)
   from S3 S4 S6 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<cdot> B ) \<cdot> C ) = ( ( A \<cdot> C ) \<cdot> B )" by (rule MMI_3eqtr4d)
qed

lemma (in MMIsar0) MMI_mul4t: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
  ( ( A \<cdot> B ) \<cdot> ( C \<cdot> D ) ) = ( ( A \<cdot> C ) \<cdot> ( B \<cdot> D ) )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<cdot> B ) \<cdot> C ) = ( ( A \<cdot> C ) \<cdot> B )" by (rule MMI_mul23t)
   from S1 have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<cdot> B ) \<cdot> C ) \<cdot> D ) = ( ( ( A \<cdot> C ) \<cdot> B ) \<cdot> D )" 
     by (rule MMI_opreq1d)
   from S2 have S3: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<cdot> B ) \<cdot> C ) \<cdot> D ) = ( ( ( A \<cdot> C ) \<cdot> B ) \<cdot> D )" 
     by (rule MMI_3expa)
   from S3 have S4: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<cdot> B ) \<cdot> C ) \<cdot> D ) = ( ( ( A \<cdot> C ) \<cdot> B ) \<cdot> D )" 
     by (rule MMI_adantrr)
   have S5: "( ( A \<cdot> B ) \<in> \<complex> \<and> C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<cdot> B ) \<cdot> C ) \<cdot> D ) = ( ( A \<cdot> B ) \<cdot> ( C \<cdot> D ) )" 
     by (rule MMI_axmulass)
   from S5 have S6: "( ( A \<cdot> B ) \<in> \<complex> \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<cdot> B ) \<cdot> C ) \<cdot> D ) = ( ( A \<cdot> B ) \<cdot> ( C \<cdot> D ) )" by (rule MMI_3expb)
   have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cdot> B ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S6 S7 have S8: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<cdot> B ) \<cdot> C ) \<cdot> D ) = ( ( A \<cdot> B ) \<cdot> ( C \<cdot> D ) )" by (rule MMI_sylan)
   have S9: "( ( A \<cdot> C ) \<in> \<complex> \<and> B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<cdot> C ) \<cdot> B ) \<cdot> D ) = ( ( A \<cdot> C ) \<cdot> ( B \<cdot> D ) )" 
     by (rule MMI_axmulass)
   from S9 have S10: "( ( A \<cdot> C ) \<in> \<complex> \<and> ( B \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<cdot> C ) \<cdot> B ) \<cdot> D ) = ( ( A \<cdot> C ) \<cdot> ( B \<cdot> D ) )" 
     by (rule MMI_3expb)
   have S11: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cdot> C ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S10 S11 have S12: "( ( A \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<cdot> C ) \<cdot> B ) \<cdot> D ) = ( ( A \<cdot> C ) \<cdot> ( B \<cdot> D ) )" 
     by (rule MMI_sylan)
   from S12 have S13: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<cdot> C ) \<cdot> B ) \<cdot> D ) = ( ( A \<cdot> C ) \<cdot> ( B \<cdot> D ) )" 
     by (rule MMI_an4s)
   from S4 S8 S13 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<cdot> B ) \<cdot> ( C \<cdot> D ) ) = ( ( A \<cdot> C ) \<cdot> ( B \<cdot> D ) )" 
     by (rule MMI_3eqtr3d)
qed

lemma (in MMIsar0) MMI_muladdt: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
  ( ( A \<ca> B ) \<cdot> ( C \<ca> D ) ) = 
  ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<ca> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) )"
proof -
   have S1: "( ( A \<ca> B ) \<in> \<complex> \<and> C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cdot> ( C \<ca> D ) ) = 
     ( ( ( A \<ca> B ) \<cdot> C ) \<ca> ( ( A \<ca> B ) \<cdot> D ) )" 
     by (rule MMI_axdistr)
   have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> B ) \<in> \<complex>" by (rule MMI_axaddcl)
   from S2 have S3: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( A \<ca> B ) \<in> \<complex>" by (rule MMI_adantr)
   have S4: "( C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> C \<in> \<complex>" by (rule MMI_pm3_26)
   from S4 have S5: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> C \<in> \<complex>" 
     by (rule MMI_adantl)
   have S6: "( C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> D \<in> \<complex>" by (rule MMI_pm3_27)
   from S6 have S7: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> D \<in> \<complex>" 
     by (rule MMI_adantl)
   from S1 S3 S5 S7 have S8: 
     "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow>
     ( ( A \<ca> B ) \<cdot> ( C \<ca> D ) ) = 
     ( ( ( A \<ca> B ) \<cdot> C ) \<ca> ( ( A \<ca> B ) \<cdot> D ) )" 
     by (rule MMI_syl3anc)
   have S9: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cdot> C ) = ( ( A \<cdot> C ) \<ca> ( B \<cdot> C ) )" 
     by (rule MMI_adddirt)
   from S9 have S10: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cdot> C ) = ( ( A \<cdot> C ) \<ca> ( B \<cdot> C ) )" 
     by (rule MMI_3expa)
   from S10 have S11: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cdot> C ) = ( ( A \<cdot> C ) \<ca> ( B \<cdot> C ) )" 
     by (rule MMI_adantrr)
   have S12: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cdot> D ) = ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) )" 
     by (rule MMI_adddirt)
   from S12 have S13: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> D \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cdot> D ) = ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) )" 
     by (rule MMI_3expa)
   from S13 have S14: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cdot> D ) = ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) )" 
     by (rule MMI_adantrl)
   from S11 S14 have S15: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<ca> B ) \<cdot> C ) \<ca> ( ( A \<ca> B ) \<cdot> D ) ) = 
     ( ( ( A \<cdot> C ) \<ca> ( B \<cdot> C ) ) \<ca> ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) ) )" 
     by (rule MMI_opreq12d)
   have S16: 
     "( ( A \<cdot> C ) \<in> \<complex> \<and> ( B \<cdot> C ) \<in> \<complex> \<and> 
     ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) ) \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<cdot> C ) \<ca> ( B \<cdot> C ) ) \<ca> ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) ) ) = 
     ( ( ( A \<cdot> C ) \<ca> ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) ) ) \<ca> ( B \<cdot> C ) )" 
     by (rule MMI_add23t)
   have S17: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cdot> C ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S17 have S18: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( A \<cdot> C ) \<in> \<complex>" by (rule MMI_ad2ant2r)
   have S19: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<cdot> C ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S19 have S20: "( B \<in> \<complex> \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( B \<cdot> C ) \<in> \<complex>" by (rule MMI_adantrr)
   from S20 have S21: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( B \<cdot> C ) \<in> \<complex>" by (rule MMI_adantll)
   have S22: "( ( A \<cdot> D ) \<in> \<complex> \<and> ( B \<cdot> D ) \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) ) \<in> \<complex>" by (rule MMI_axaddcl)
   have S23: "( A \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( A \<cdot> D ) \<in> \<complex>" by (rule MMI_axmulcl)
   have S24: "( B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( B \<cdot> D ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S22 S23 S24 have S25: 
     "( ( A \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( B \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) ) \<in> \<complex>" by (rule MMI_syl2an)
   from S25 have S26: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> D \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) ) \<in> \<complex>" by (rule MMI_anandirs)
   from S26 have S27: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) ) \<in> \<complex>" by (rule MMI_adantrl)
   from S16 S18 S21 S27 have S28: 
     "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<cdot> C ) \<ca> ( B \<cdot> C ) ) \<ca> ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) ) ) = 
     ( ( ( A \<cdot> C ) \<ca> ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) ) ) \<ca> ( B \<cdot> C ) )" 
     by (rule MMI_syl3anc)
   have S29: "( B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( B \<cdot> D ) = ( D \<cdot> B )" 
     by (rule MMI_axmulcom)
   from S29 have S30: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( B \<cdot> D ) = ( D \<cdot> B )" by (rule MMI_ad2ant2l)
   from S30 have S31: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<cdot> C ) \<ca> ( A \<cdot> D ) ) \<ca> ( B \<cdot> D ) ) = 
     ( ( ( A \<cdot> C ) \<ca> ( A \<cdot> D ) ) \<ca> ( D \<cdot> B ) )" 
     by (rule MMI_opreq2d)
   have S32: "( ( A \<cdot> C ) \<in> \<complex> \<and> ( A \<cdot> D ) \<in> \<complex> \<and> ( B \<cdot> D ) \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<cdot> C ) \<ca> ( A \<cdot> D ) ) \<ca> ( B \<cdot> D ) ) = 
     ( ( A \<cdot> C ) \<ca> ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) ) )" 
     by (rule MMI_axaddass)
   from S18 have S33: 
     "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> ( A \<cdot> C ) \<in> \<complex>" .
   from S23 have S34: "( A \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( A \<cdot> D ) \<in> \<complex>" .
   from S34 have S35: "( A \<in> \<complex> \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( A \<cdot> D ) \<in> \<complex>" by (rule MMI_adantrl)
   from S35 have S36: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( A \<cdot> D ) \<in> \<complex>" by (rule MMI_adantlr)
   from S24 have S37: "( B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( B \<cdot> D ) \<in> \<complex>" .
   from S37 have S38: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( B \<cdot> D ) \<in> \<complex>" by (rule MMI_ad2ant2l)
   from S32 S33 S36 S38 have S39: 
     "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<cdot> C ) \<ca> ( A \<cdot> D ) ) \<ca> ( B \<cdot> D ) ) = 
     ( ( A \<cdot> C ) \<ca> ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) ) )" by (rule MMI_syl3anc)
   have S40: "( ( A \<cdot> C ) \<in> \<complex> \<and> ( A \<cdot> D ) \<in> \<complex> \<and> ( D \<cdot> B ) \<in> \<complex> ) \<longrightarrow> 
     ( ( ( A \<cdot> C ) \<ca> ( A \<cdot> D ) ) \<ca> ( D \<cdot> B ) ) = 
     ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<ca> ( A \<cdot> D ) )" by (rule MMI_add23t)
   from S18 have S41: 
     "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> ( A \<cdot> C ) \<in> \<complex>" .
   from S36 have S42: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( A \<cdot> D ) \<in> \<complex>" .
   have S43: "( D \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( D \<cdot> B ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S43 have S44: "( B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( D \<cdot> B ) \<in> \<complex>" 
     by (rule MMI_ancoms)
   from S44 have S45: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( D \<cdot> B ) \<in> \<complex>" by (rule MMI_ad2ant2l)
   from S40 S41 S42 S45 have S46: 
     "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<cdot> C ) \<ca> ( A \<cdot> D ) ) \<ca> ( D \<cdot> B ) ) = 
     ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<ca> ( A \<cdot> D ) )" by (rule MMI_syl3anc)
   from S31 S39 S46 have S47: 
     "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<cdot> C ) \<ca> ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) ) ) = 
     ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<ca> ( A \<cdot> D ) )" by (rule MMI_3eqtr3d)
   have S48: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<cdot> C ) = ( C \<cdot> B )" 
     by (rule MMI_axmulcom)
   from S48 have S49: "( ( A \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( B \<in> \<complex> \<and> C \<in> \<complex> ) ) \<longrightarrow> 
     ( B \<cdot> C ) = ( C \<cdot> B )" by (rule MMI_adantl)
   from S49 have S50: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( B \<cdot> C ) = ( C \<cdot> B )" by (rule MMI_an42s)
   from S47 S50 have S51: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<cdot> C ) \<ca> ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) ) ) \<ca> ( B \<cdot> C ) ) = 
     ( ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<ca> ( A \<cdot> D ) ) \<ca> ( C \<cdot> B ) )" 
     by (rule MMI_opreq12d)
   have S52: 
     "( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<in> \<complex> \<and> ( A \<cdot> D ) \<in> \<complex> \<and> 
     ( C \<cdot> B ) \<in> \<complex> ) \<longrightarrow> 
     ( ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<ca> ( A \<cdot> D ) ) \<ca> ( C \<cdot> B ) ) = 
     ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<ca> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) )" 
     by (rule MMI_axaddass)
   have S53: "( ( A \<cdot> C ) \<in> \<complex> \<and> ( D \<cdot> B ) \<in> \<complex> ) \<longrightarrow> 
     ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<in> \<complex>" by (rule MMI_axaddcl)
   from S17 have S54: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cdot> C ) \<in> \<complex>" .
   from S44 have S55: "( B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( D \<cdot> B ) \<in> \<complex>" .
   from S53 S54 S55 have S56: 
     "( ( A \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<in> \<complex>" by (rule MMI_syl2an)
   from S56 have S57: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<in> \<complex>" by (rule MMI_an4s)
   from S36 have S58: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( A \<cdot> D ) \<in> \<complex>" .
   have S59: "( C \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( C \<cdot> B ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S59 have S60: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( C \<cdot> B ) \<in> \<complex>" 
     by (rule MMI_ancoms)
   from S60 have S61: "( ( A \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( B \<in> \<complex> \<and> C \<in> \<complex> ) ) \<longrightarrow> 
     ( C \<cdot> B ) \<in> \<complex>" by (rule MMI_adantl)
   from S61 have S62: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( C \<cdot> B ) \<in> \<complex>" by (rule MMI_an42s)
   from S52 S57 S58 S62 have S63: 
     "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<ca> ( A \<cdot> D ) ) \<ca> ( C \<cdot> B ) ) = 
     ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<ca> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) )" 
     by (rule MMI_syl3anc)
   from S28 S51 S63 have S64: 
     "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( ( A \<cdot> C ) \<ca> ( B \<cdot> C ) ) \<ca> ( ( A \<cdot> D ) \<ca> ( B \<cdot> D ) ) ) = 
     ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<ca> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) )" 
     by (rule MMI_3eqtrd)
   from S8 S15 S64 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cdot> ( C \<ca> D ) ) = 
     ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<ca> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) )" 
     by (rule MMI_3eqtrd)
qed

(********* 96-100****************************************************)

lemma (in MMIsar0) MMI_muladd11t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( \<one> \<ca> A ) \<cdot> ( \<one> \<ca> B ) ) = 
  ( ( \<one> \<ca> A ) \<ca> ( B \<ca> ( A \<cdot> B ) ) )"
proof -
   have S1: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S2: "( ( \<one> \<ca> A ) \<in> \<complex> \<and> \<one> \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
     ( ( \<one> \<ca> A ) \<cdot> ( \<one> \<ca> B ) ) = 
     ( ( ( \<one> \<ca> A ) \<cdot> \<one> ) \<ca> ( ( \<one> \<ca> A ) \<cdot> B ) )" 
     by (rule MMI_axdistr)
   from S1 S2 have S3: "( ( \<one> \<ca> A ) \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
     ( ( \<one> \<ca> A ) \<cdot> ( \<one> \<ca> B ) ) = 
     ( ( ( \<one> \<ca> A ) \<cdot> \<one> ) \<ca> ( ( \<one> \<ca> A ) \<cdot> B ) )" 
     by (rule MMI_mp3an2)
   have S4: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S5: "( \<one> \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> ( \<one> \<ca> A ) \<in> \<complex>" by (rule MMI_axaddcl)
   from S4 S5 have S6: "A \<in> \<complex> \<longrightarrow> ( \<one> \<ca> A ) \<in> \<complex>" by (rule MMI_mpan)
   from S3 S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
     ( ( \<one> \<ca> A ) \<cdot> ( \<one> \<ca> B ) ) = 
     ( ( ( \<one> \<ca> A ) \<cdot> \<one> ) \<ca> ( ( \<one> \<ca> A ) \<cdot> B ) )" by (rule MMI_sylan)
   from S6 have S8: "A \<in> \<complex> \<longrightarrow> ( \<one> \<ca> A ) \<in> \<complex>" .
   have S9: "( \<one> \<ca> A ) \<in> \<complex> \<longrightarrow> ( ( \<one> \<ca> A ) \<cdot> \<one> ) = ( \<one> \<ca> A )" 
     by (rule MMI_ax1id)
   from S8 S9 have S10: "A \<in> \<complex> \<longrightarrow> ( ( \<one> \<ca> A ) \<cdot> \<one> ) = ( \<one> \<ca> A )" 
     by (rule MMI_syl)
   from S10 have S11: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
     ( ( \<one> \<ca> A ) \<cdot> \<one> ) = ( \<one> \<ca> A )" by (rule MMI_adantr)
   have S12: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S13: "( \<one> \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( \<one> \<ca> A ) \<cdot> B ) = 
     ( ( \<one> \<cdot> B ) \<ca> ( A \<cdot> B ) )" by (rule MMI_adddirt)
   from S12 S13 have S14: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( \<one> \<ca> A ) \<cdot> B ) = ( ( \<one> \<cdot> B ) \<ca> ( A \<cdot> B ) )" by (rule MMI_mp3an1)
   have S15: "B \<in> \<complex> \<longrightarrow> ( \<one> \<cdot> B ) = B" by (rule MMI_mulid2t)
   from S15 have S16: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( \<one> \<cdot> B ) = B" 
     by (rule MMI_adantl)
   from S16 have S17: 
     "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( \<one> \<cdot> B ) \<ca> ( A \<cdot> B ) ) = 
     ( B \<ca> ( A \<cdot> B ) )" by (rule MMI_opreq1d)
   from S14 S17 have S18: 
     "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( ( \<one> \<ca> A ) \<cdot> B ) = 
     ( B \<ca> ( A \<cdot> B ) )" by (rule MMI_eqtrd)
   from S11 S18 have S19: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
     ( ( ( \<one> \<ca> A ) \<cdot> \<one> ) \<ca> ( ( \<one> \<ca> A ) \<cdot> B ) ) = 
     ( ( \<one> \<ca> A ) \<ca> ( B \<ca> ( A \<cdot> B ) ) )" by (rule MMI_opreq12d)
   from S7 S19 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
     ( ( \<one> \<ca> A ) \<cdot> ( \<one> \<ca> B ) ) = 
     ( ( \<one> \<ca> A ) \<ca> ( B \<ca> ( A \<cdot> B ) ) )" 
     by (rule MMI_eqtrd)
qed

lemma (in MMIsar0) MMI_mul12: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( A \<cdot> ( B \<cdot> C ) ) = ( B \<cdot> ( A \<cdot> C ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from S1 S2 have S3: "( A \<cdot> B ) = ( B \<cdot> A )" by (rule MMI_mulcom)
   from S3 have S4: "( ( A \<cdot> B ) \<cdot> C ) = ( ( B \<cdot> A ) \<cdot> C )" 
     by (rule MMI_opreq1i)
   from A1 have S5: "A \<in> \<complex>".
   from A2 have S6: "B \<in> \<complex>".
   from A3 have S7: "C \<in> \<complex>".
   from S5 S6 S7 have S8: "( ( A \<cdot> B ) \<cdot> C ) = ( A \<cdot> ( B \<cdot> C ) )" 
     by (rule MMI_mulass)
   from A2 have S9: "B \<in> \<complex>".
   from A1 have S10: "A \<in> \<complex>".
   from A3 have S11: "C \<in> \<complex>".
   from S9 S10 S11 have S12: "( ( B \<cdot> A ) \<cdot> C ) = ( B \<cdot> ( A \<cdot> C ) )" 
     by (rule MMI_mulass)
   from S4 S8 S12 show "( A \<cdot> ( B \<cdot> C ) ) = ( B \<cdot> ( A \<cdot> C ) )" 
     by (rule MMI_3eqtr3)
qed

lemma (in MMIsar0) MMI_mul23: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( ( A \<cdot> B ) \<cdot> C ) = ( ( A \<cdot> C ) \<cdot> B )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<cdot> B ) \<cdot> C ) = 
     ( ( A \<cdot> C ) \<cdot> B )" by (rule MMI_mul23t)
   from S1 S2 S3 S4 show "( ( A \<cdot> B ) \<cdot> C ) = ( ( A \<cdot> C ) \<cdot> B )" 
     by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_mul4: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>" and
    A4: "D \<in> \<complex>"   
   shows "( ( A \<cdot> B ) \<cdot> ( C \<cdot> D ) ) = ( ( A \<cdot> C ) \<cdot> ( B \<cdot> D ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from S1 S2 have S3: "A \<in> \<complex> \<and> B \<in> \<complex>" by (rule MMI_pm3_2i)
   from A3 have S4: "C \<in> \<complex>".
   from A4 have S5: "D \<in> \<complex>".
   from S4 S5 have S6: "C \<in> \<complex> \<and> D \<in> \<complex>" by (rule MMI_pm3_2i)
   have S7: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<cdot> B ) \<cdot> ( C \<cdot> D ) ) = ( ( A \<cdot> C ) \<cdot> ( B \<cdot> D ) )" 
     by (rule MMI_mul4t)
   from S3 S6 S7 show "( ( A \<cdot> B ) \<cdot> ( C \<cdot> D ) ) = ( ( A \<cdot> C ) \<cdot> ( B \<cdot> D ) )" 
     by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_muladd: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>" and
    A4: "D \<in> \<complex>"   
   shows "( ( A \<ca> B ) \<cdot> ( C \<ca> D ) ) = 
  ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<ca> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from S1 S2 have S3: "A \<in> \<complex> \<and> B \<in> \<complex>" by (rule MMI_pm3_2i)
   from A3 have S4: "C \<in> \<complex>".
   from A4 have S5: "D \<in> \<complex>".
   from S4 S5 have S6: "C \<in> \<complex> \<and> D \<in> \<complex>" by (rule MMI_pm3_2i)
   have S7: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
     ( ( A \<ca> B ) \<cdot> ( C \<ca> D ) ) =
     ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<ca> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) )" 
     by (rule MMI_muladdt)
   from S3 S6 S7 show 
     "( ( A \<ca> B ) \<cdot> ( C \<ca> D ) ) = 
     ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<ca> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) )" 
     by (rule MMI_mp2an)
qed

(************ 101-110 *********************)
lemma (in MMIsar0) MMI_subdit: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> ( B \<cs> C ) ) = ( ( A \<cdot> B ) \<cs> ( A \<cdot> C ) )"
proof -
   have S1: "( A \<in> \<complex> \<and> C \<in> \<complex> \<and> ( B \<cs> C ) \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> ( C \<ca> ( B \<cs> C ) ) ) = 
     ( ( A \<cdot> C ) \<ca> ( A \<cdot> ( B \<cs> C ) ) )" by (rule MMI_axdistr)
   have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> A \<in> \<complex>" by (rule MMI_3simp1)
   have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> C \<in> \<complex>" by (rule MMI_3simp3)
   have S4: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<cs> C ) \<in> \<complex>" by (rule MMI_subclt)
   from S4 have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<cs> C ) \<in> \<complex>" 
     by (rule MMI_3adant1)
   from S1 S2 S3 S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> ( C \<ca> ( B \<cs> C ) ) ) = 
     ( ( A \<cdot> C ) \<ca> ( A \<cdot> ( B \<cs> C ) ) )" by (rule MMI_syl3anc)
   have S7: "( C \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( C \<ca> ( B \<cs> C ) ) = B" by (rule MMI_pncan3t)
   from S7 have S8: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( C \<ca> ( B \<cs> C ) ) = B" by (rule MMI_ancoms)
   from S8 have S9: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( C \<ca> ( B \<cs> C ) ) = B" by (rule MMI_3adant1)
   from S9 have S10: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> ( C \<ca> ( B \<cs> C ) ) ) = ( A \<cdot> B )" by (rule MMI_opreq2d)
   from S6 S10 have S11: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> C ) \<ca> ( A \<cdot> ( B \<cs> C ) ) ) = ( A \<cdot> B )" by (rule MMI_eqtr3d)
   have S12: "( ( A \<cdot> B ) \<in> \<complex> \<and> ( A \<cdot> C ) \<in> \<complex> \<and> ( A \<cdot> ( B \<cs> C ) ) \<in> \<complex> ) \<longrightarrow> 
 ( ( ( A \<cdot> B ) \<cs> ( A \<cdot> C ) ) = ( A \<cdot> ( B \<cs> C ) ) \<longleftrightarrow> 
     ( ( A \<cdot> C ) \<ca> ( A \<cdot> ( B \<cs> C ) ) ) = ( A \<cdot> B ) )" by (rule MMI_subaddt)
   have S13: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cdot> B ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S13 have S14: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cdot> B ) \<in> \<complex>" 
     by (rule MMI_3adant3)
   have S15: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cdot> C ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S15 have S16: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cdot> C ) \<in> \<complex>" 
     by (rule MMI_3adant2)
   have S17: "( A \<in> \<complex> \<and> ( B \<cs> C ) \<in> \<complex> ) \<longrightarrow> ( A \<cdot> ( B \<cs> C ) ) \<in> \<complex>" 
     by (rule MMI_axmulcl)
   from S4 have S18: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<cs> C ) \<in> \<complex>" .
   from S17 S18 have S19: "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> C \<in> \<complex> ) ) \<longrightarrow> 
     ( A \<cdot> ( B \<cs> C ) ) \<in> \<complex>" by (rule MMI_sylan2)
   from S19 have S20: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
     ( A \<cdot> ( B \<cs> C ) ) \<in> \<complex>" by (rule MMI_3impb)
   from S12 S14 S16 S20 have S21: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( ( A \<cdot> B ) \<cs> ( A \<cdot> C ) ) = ( A \<cdot> ( B \<cs> C ) ) \<longleftrightarrow> 
     ( ( A \<cdot> C ) \<ca> ( A \<cdot> ( B \<cs> C ) ) ) = ( A \<cdot> B ) )" by (rule MMI_syl3anc)
   from S11 S21 have S22: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cs> ( A \<cdot> C ) ) = ( A \<cdot> ( B \<cs> C ) )" by (rule MMI_mpbird)
   from S22 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> ( B \<cs> C ) ) = ( ( A \<cdot> B ) \<cs> ( A \<cdot> C ) )" by (rule MMI_eqcomd)
qed

lemma (in MMIsar0) MMI_subdirt: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cdot> C ) = ( ( A \<cdot> C ) \<cs> ( B \<cdot> C ) )"
proof -
   have S1: "( C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( C \<cdot> ( A \<cs> B ) ) = ( ( C \<cdot> A ) \<cs> ( C \<cdot> B ) )" by (rule MMI_subdit)
   from S1 have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( C \<cdot> ( A \<cs> B ) ) = ( ( C \<cdot> A ) \<cs> ( C \<cdot> B ) )" by (rule MMI_3coml)
   have S3: "( ( A \<cs> B ) \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cdot> C ) = ( C \<cdot> ( A \<cs> B ) )" by (rule MMI_axmulcom)
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cs> B ) \<in> \<complex>" by (rule MMI_subclt)
   from S3 S4 have S5: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cdot> C ) = ( C \<cdot> ( A \<cs> B ) )" by (rule MMI_sylan)
   from S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cdot> C ) = ( C \<cdot> ( A \<cs> B ) )" by (rule MMI_3impa)
   have S7: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cdot> C ) = ( C \<cdot> A )" by (rule MMI_axmulcom)
   from S7 have S8: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cdot> C ) = ( C \<cdot> A )" 
     by (rule MMI_3adant2)
   have S9: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<cdot> C ) = ( C \<cdot> B )" by (rule MMI_axmulcom)
   from S9 have S10: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<cdot> C ) = ( C \<cdot> B )" 
     by (rule MMI_3adant1)
   from S8 S10 have S11: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> C ) \<cs> ( B \<cdot> C ) ) = ( ( C \<cdot> A ) \<cs> ( C \<cdot> B ) )" 
     by (rule MMI_opreq12d)
   from S2 S6 S11 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cdot> C ) = ( ( A \<cdot> C ) \<cs> ( B \<cdot> C ) )" by (rule MMI_3eqtr4d)
qed

lemma (in MMIsar0) MMI_subdi: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( A \<cdot> ( B \<cs> C ) ) = ( ( A \<cdot> B ) \<cs> ( A \<cdot> C ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> ( B \<cs> C ) ) = ( ( A \<cdot> B ) \<cs> ( A \<cdot> C ) )" by (rule MMI_subdit)
   from S1 S2 S3 S4 show "( A \<cdot> ( B \<cs> C ) ) = ( ( A \<cdot> B ) \<cs> ( A \<cdot> C ) )" 
     by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_subdir: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( ( A \<cs> B ) \<cdot> C ) = ( ( A \<cdot> C ) \<cs> ( B \<cdot> C ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cdot> C ) = ( ( A \<cdot> C ) \<cs> ( B \<cdot> C ) )" by (rule MMI_subdirt)
   from S1 S2 S3 S4 show "( ( A \<cs> B ) \<cdot> C ) = ( ( A \<cdot> C ) \<cs> ( B \<cdot> C ) )" 
     by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_mul01: assumes A1: "A \<in> \<complex>"   
   shows "( A \<cdot> \<zero> ) = \<zero>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   have S2: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   have S3: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S1 S2 S3 have S4: "( A \<cdot> ( \<zero> \<cs> \<zero> ) ) = ( ( A \<cdot> \<zero> ) \<cs> ( A \<cdot> \<zero> ) )" 
     by (rule MMI_subdi)
   have S5: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S5 have S6: "( \<zero> \<cs> \<zero> ) = \<zero>" by (rule MMI_subid)
   from S6 have S7: "( A \<cdot> ( \<zero> \<cs> \<zero> ) ) = ( A \<cdot> \<zero> )" by (rule MMI_opreq2i)
   from A1 have S8: "A \<in> \<complex>".
   have S9: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S8 S9 have S10: "( A \<cdot> \<zero> ) \<in> \<complex>" by (rule MMI_mulcl)
   from S10 have S11: "( ( A \<cdot> \<zero> ) \<cs> ( A \<cdot> \<zero> ) ) = \<zero>" by (rule MMI_subid)
   from S4 S7 S11 show "( A \<cdot> \<zero> ) = \<zero>" by (rule MMI_3eqtr3)
qed

lemma (in MMIsar0) MMI_mul02: assumes A1: "A \<in> \<complex>"   
   shows "( \<zero> \<cdot> A ) = \<zero>"
proof -
   have S1: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from A1 have S2: "A \<in> \<complex>".
   from S1 S2 have S3: "( \<zero> \<cdot> A ) = ( A \<cdot> \<zero> )" by (rule MMI_mulcom)
   from A1 have S4: "A \<in> \<complex>".
   from S4 have S5: "( A \<cdot> \<zero> ) = \<zero>" by (rule MMI_mul01)
   from S3 S5 show "( \<zero> \<cdot> A ) = \<zero>" by (rule MMI_eqtr)
qed

lemma (in MMIsar0) MMI_1p1times: assumes A1: "A \<in> \<complex>"   
   shows "( ( \<one> \<ca> \<one> ) \<cdot> A ) = ( A \<ca> A )"
proof -
   have S1: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S2: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from A1 have S3: "A \<in> \<complex>".
   from S1 S2 S3 have S4: "( ( \<one> \<ca> \<one> ) \<cdot> A ) = ( ( \<one> \<cdot> A ) \<ca> ( \<one> \<cdot> A ) )" 
     by (rule MMI_adddir)
   from A1 have S5: "A \<in> \<complex>".
   from S5 have S6: "( \<one> \<cdot> A ) = A" by (rule MMI_mulid2)
   from S6 have S7: "( \<one> \<cdot> A ) = A" .
   from S6 S7 have S8: "( ( \<one> \<cdot> A ) \<ca> ( \<one> \<cdot> A ) ) = ( A \<ca> A )" 
     by (rule MMI_opreq12i)
   from S4 S8 show "( ( \<one> \<ca> \<one> ) \<cdot> A ) = ( A \<ca> A )" 
     by (rule MMI_eqtr)
qed

lemma (in MMIsar0) MMI_mul01t: 
   shows "A \<in> \<complex> \<longrightarrow> ( A \<cdot> \<zero> ) = \<zero>"
proof -
   have S1: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<cdot> \<zero> ) = ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> \<zero> )" by (rule MMI_opreq1)
   from S1 have S2: "A = if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> \<zero> ) = \<zero> \<longleftrightarrow> ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> \<zero> ) = \<zero> )" by (rule MMI_eqeq1d)
   have S3: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S3 have S4: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S4 have S5: "( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> \<zero> ) = \<zero>" by (rule MMI_mul01)
   from S2 S5 show "A \<in> \<complex> \<longrightarrow> ( A \<cdot> \<zero> ) = \<zero>" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_mul02t: 
   shows "A \<in> \<complex> \<longrightarrow> ( \<zero> \<cdot> A ) = \<zero>"
proof -
   have S1: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   have S2: "( \<zero> \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> ( \<zero> \<cdot> A ) = ( A \<cdot> \<zero> )" by (rule MMI_axmulcom)
   from S1 S2 have S3: "A \<in> \<complex> \<longrightarrow> ( \<zero> \<cdot> A ) = ( A \<cdot> \<zero> )" by (rule MMI_mpan)
   have S4: "A \<in> \<complex> \<longrightarrow> ( A \<cdot> \<zero> ) = \<zero>" by (rule MMI_mul01t)
   from S3 S4 show "A \<in> \<complex> \<longrightarrow> ( \<zero> \<cdot> A ) = \<zero>" by (rule MMI_eqtrd)
qed

lemma (in MMIsar0) MMI_mulneg1: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( ( (\<cn>  A) ) \<cdot> B ) = ( \<cn> ( A \<cdot> B ) )"
proof -
   from A2 have S1: "B \<in> \<complex>".
   from S1 have S2: "( B \<cdot> \<zero> ) = \<zero>" by (rule MMI_mul01)
   from A2 have S3: "B \<in> \<complex>".
   from A1 have S4: "A \<in> \<complex>".
   from S3 S4 have S5: "( B \<cdot> A ) = ( A \<cdot> B )" by (rule MMI_mulcom)
   from S2 S5 have S6: "( ( B \<cdot> \<zero> ) \<cs> ( B \<cdot> A ) ) = ( \<zero> \<cs> ( A \<cdot> B ) )" 
     by (rule MMI_opreq12i)
   have S7: "( (\<cn>  A) ) = ( \<zero> \<cs> A )" by (rule MMI_df_neg)
   from S7 have S8: "( ( (\<cn>  A) ) \<cdot> B ) = ( ( \<zero> \<cs> A ) \<cdot> B )" 
     by (rule MMI_opreq1i)
   have S9: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from A1 have S10: "A \<in> \<complex>".
   from S9 S10 have S11: "( \<zero> \<cs> A ) \<in> \<complex>" by (rule MMI_subcl)
   from A2 have S12: "B \<in> \<complex>".
   from S11 S12 have S13: "( ( \<zero> \<cs> A ) \<cdot> B ) = ( B \<cdot> ( \<zero> \<cs> A ) )" 
     by (rule MMI_mulcom)
   from A2 have S14: "B \<in> \<complex>".
   have S15: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from A1 have S16: "A \<in> \<complex>".
   from S14 S15 S16 have 
     S17: "( B \<cdot> ( \<zero> \<cs> A ) ) = ( ( B \<cdot> \<zero> ) \<cs> ( B \<cdot> A ) )" 
     by (rule MMI_subdi)
   from S8 S13 S17 have 
     S18: "( ( (\<cn>  A) ) \<cdot> B ) = ( ( B \<cdot> \<zero> ) \<cs> ( B \<cdot> A ) )" by (rule MMI_3eqtr)
   have S19: "( \<cn> ( A \<cdot> B ) ) = ( \<zero> \<cs> ( A \<cdot> B ) )" by (rule MMI_df_neg)
   from S6 S18 S19 show "( ( (\<cn>  A) ) \<cdot> B ) = ( \<cn> ( A \<cdot> B ) )" 
     by (rule MMI_3eqtr4)
qed

(*********111-120*********************************)

lemma (in MMIsar0) MMI_mulneg2: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( A \<cdot> ( (\<cn>  B) ) ) = 
 ( \<cn> ( A \<cdot> B ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from S2 have S3: "( (\<cn>  B) ) \<in> \<complex>" by (rule MMI_negcl)
   from S1 S3 have S4: "( A \<cdot> ( (\<cn>  B) ) ) = 
 ( ( (\<cn>  B) ) \<cdot> A )" by (rule MMI_mulcom)
   from A2 have S5: "B \<in> \<complex>".
   from A1 have S6: "A \<in> \<complex>".
   from S5 S6 have S7: "( ( (\<cn>  B) ) \<cdot> A ) = 
 ( \<cn> ( B \<cdot> A ) )" by (rule MMI_mulneg1)
   from A2 have S8: "B \<in> \<complex>".
   from A1 have S9: "A \<in> \<complex>".
   from S8 S9 have S10: "( B \<cdot> A ) = ( A \<cdot> B )" by (rule MMI_mulcom)
   from S10 have S11: "( \<cn> ( B \<cdot> A ) ) = 
 ( \<cn> ( A \<cdot> B ) )" by (rule MMI_negeqi)
   from S4 S7 S11 show "( A \<cdot> ( (\<cn>  B) ) ) = 
 ( \<cn> ( A \<cdot> B ) )" by (rule MMI_3eqtr)
qed

lemma (in MMIsar0) MMI_mul2neg: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( ( (\<cn>  A) ) \<cdot> ( (\<cn>  B) ) ) = 
 ( A \<cdot> B )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from S2 have S3: "( (\<cn>  B) ) \<in> \<complex>" by (rule MMI_negcl)
   from S1 S3 have S4: "( ( (\<cn>  A) ) \<cdot> ( (\<cn>  B) ) ) = 
 ( \<cn> ( A \<cdot> ( (\<cn>  B) ) ) )" by (rule MMI_mulneg1)
   from A1 have S5: "A \<in> \<complex>".
   from S3 have S6: "( (\<cn>  B) ) \<in> \<complex>" .
   from S5 S6 have S7: "( A \<cdot> ( (\<cn>  B) ) ) = 
 ( ( (\<cn>  B) ) \<cdot> A )" by (rule MMI_mulcom)
   from A2 have S8: "B \<in> \<complex>".
   from A1 have S9: "A \<in> \<complex>".
   from S8 S9 have S10: "( ( (\<cn>  B) ) \<cdot> A ) = 
 ( \<cn> ( B \<cdot> A ) )" by (rule MMI_mulneg1)
   from S7 S10 have S11: "( A \<cdot> ( (\<cn>  B) ) ) = 
 ( \<cn> ( B \<cdot> A ) )" by (rule MMI_eqtr)
   from S11 have S12: "( \<cn> ( A \<cdot> ( (\<cn>  B) ) ) ) = 
 ( \<cn> ( \<cn> ( B \<cdot> A ) ) )" by (rule MMI_negeqi)
   from A2 have S13: "B \<in> \<complex>".
   from A1 have S14: "A \<in> \<complex>".
   from S13 S14 have S15: "( B \<cdot> A ) \<in> \<complex>" by (rule MMI_mulcl)
   from S15 have S16: "( \<cn> ( \<cn> ( B \<cdot> A ) ) ) = 
 ( B \<cdot> A )" by (rule MMI_negneg)
   from S4 S12 S16 have S17: "( ( (\<cn>  A) ) \<cdot> ( (\<cn>  B) ) ) = 
 ( B \<cdot> A )" by (rule MMI_3eqtr)
   from A2 have S18: "B \<in> \<complex>".
   from A1 have S19: "A \<in> \<complex>".
   from S18 S19 have S20: "( B \<cdot> A ) = ( A \<cdot> B )" by (rule MMI_mulcom)
   from S17 S20 show "( ( (\<cn>  A) ) \<cdot> ( (\<cn>  B) ) ) = 
 ( A \<cdot> B )" by (rule MMI_eqtr)
qed

lemma (in MMIsar0) MMI_negdi: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( \<cn> ( A \<ca> B ) ) = 
 ( ( (\<cn>  A) ) \<ca> ( (\<cn>  B) ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from S1 S2 have S3: "( A \<ca> B ) \<in> \<complex>" by (rule MMI_addcl)
   from S3 have S4: "( \<one> \<cdot> ( A \<ca> B ) ) = 
 ( A \<ca> B )" by (rule MMI_mulid2)
   from S4 have S5: "( \<cn> ( \<one> \<cdot> ( A \<ca> B ) ) ) = 
 ( \<cn> ( A \<ca> B ) )" by (rule MMI_negeqi)
   have S6: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S6 have S7: "( \<cn> \<one> ) \<in> \<complex>" by (rule MMI_negcl)
   from A1 have S8: "A \<in> \<complex>".
   from A2 have S9: "B \<in> \<complex>".
   from S7 S8 S9 have S10: "( ( \<cn> \<one> ) \<cdot> ( A \<ca> B ) ) = 
 ( ( ( \<cn> \<one> ) \<cdot> A ) \<ca> ( ( \<cn> \<one> ) \<cdot> B ) )" by (rule MMI_adddi)
   have S11: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S3 have S12: "( A \<ca> B ) \<in> \<complex>" .
   from S11 S12 have S13: "( ( \<cn> \<one> ) \<cdot> ( A \<ca> B ) ) = 
 ( \<cn> ( \<one> \<cdot> ( A \<ca> B ) ) )" by (rule MMI_mulneg1)
   have S14: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from A1 have S15: "A \<in> \<complex>".
   from S14 S15 have S16: "( ( \<cn> \<one> ) \<cdot> A ) = 
 ( \<cn> ( \<one> \<cdot> A ) )" by (rule MMI_mulneg1)
   from A1 have S17: "A \<in> \<complex>".
   from S17 have S18: "( \<one> \<cdot> A ) = A" by (rule MMI_mulid2)
   from S18 have S19: "( \<cn> ( \<one> \<cdot> A ) ) = ( (\<cn>  A) )" by (rule MMI_negeqi)
   from S16 S19 have S20: "( ( \<cn> \<one> ) \<cdot> A ) = ( (\<cn>  A) )" by (rule MMI_eqtr)
   have S21: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from A2 have S22: "B \<in> \<complex>".
   from S21 S22 have S23: "( ( \<cn> \<one> ) \<cdot> B ) = 
 ( \<cn> ( \<one> \<cdot> B ) )" by (rule MMI_mulneg1)
   from A2 have S24: "B \<in> \<complex>".
   from S24 have S25: "( \<one> \<cdot> B ) = B" by (rule MMI_mulid2)
   from S25 have S26: "( \<cn> ( \<one> \<cdot> B ) ) = ( (\<cn>  B) )" by (rule MMI_negeqi)
   from S23 S26 have S27: "( ( \<cn> \<one> ) \<cdot> B ) = ( (\<cn>  B) )" by (rule MMI_eqtr)
   from S20 S27 have S28: "( ( ( \<cn> \<one> ) \<cdot> A ) \<ca> ( ( \<cn> \<one> ) \<cdot> B ) ) = 
 ( ( (\<cn>  A) ) \<ca> ( (\<cn>  B) ) )" by (rule MMI_opreq12i)
   from S10 S13 S28 have S29: "( \<cn> ( \<one> \<cdot> ( A \<ca> B ) ) ) = 
 ( ( (\<cn>  A) ) \<ca> ( (\<cn>  B) ) )" by (rule MMI_3eqtr3)
   from S5 S29 show "( \<cn> ( A \<ca> B ) ) = 
 ( ( (\<cn>  A) ) \<ca> ( (\<cn>  B) ) )" by (rule MMI_eqtr3)
qed

lemma (in MMIsar0) MMI_negsubdi: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( \<cn> ( A \<cs> B ) ) = 
 ( ( (\<cn>  A) ) \<ca> B )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from S2 have S3: "( (\<cn>  B) ) \<in> \<complex>" by (rule MMI_negcl)
   from S1 S3 have S4: "( \<cn> ( A \<ca> ( (\<cn>  B) ) ) ) = 
 ( ( (\<cn>  A) ) \<ca> ( \<cn> ( (\<cn>  B) ) ) )" by (rule MMI_negdi)
   from A1 have S5: "A \<in> \<complex>".
   from A2 have S6: "B \<in> \<complex>".
   from S5 S6 have S7: "( A \<ca> ( (\<cn>  B) ) ) = ( A \<cs> B )" by (rule MMI_negsub)
   from S7 have S8: "( \<cn> ( A \<ca> ( (\<cn>  B) ) ) ) = 
 ( \<cn> ( A \<cs> B ) )" by (rule MMI_negeqi)
   from A2 have S9: "B \<in> \<complex>".
   from S9 have S10: "( \<cn> ( (\<cn>  B) ) ) = B" by (rule MMI_negneg)
   from S10 have S11: "( ( (\<cn>  A) ) \<ca> ( \<cn> ( (\<cn>  B) ) ) ) = 
 ( ( (\<cn>  A) ) \<ca> B )" by (rule MMI_opreq2i)
   from S4 S8 S11 show "( \<cn> ( A \<cs> B ) ) = 
 ( ( (\<cn>  A) ) \<ca> B )" by (rule MMI_3eqtr3)
qed

lemma (in MMIsar0) MMI_negsubdi2: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( \<cn> ( A \<cs> B ) ) = ( B \<cs> A )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from S1 S2 have S3: "( \<cn> ( A \<cs> B ) ) = 
 ( ( (\<cn>  A) ) \<ca> B )" by (rule MMI_negsubdi)
   from A1 have S4: "A \<in> \<complex>".
   from S4 have S5: "( (\<cn>  A) ) \<in> \<complex>" by (rule MMI_negcl)
   from A2 have S6: "B \<in> \<complex>".
   from S5 S6 have S7: "( ( (\<cn>  A) ) \<ca> B ) = 
 ( B \<ca> ( (\<cn>  A) ) )" by (rule MMI_addcom)
   from A2 have S8: "B \<in> \<complex>".
   from A1 have S9: "A \<in> \<complex>".
   from S8 S9 have S10: "( B \<ca> ( (\<cn>  A) ) ) = ( B \<cs> A )" by (rule MMI_negsub)
   from S3 S7 S10 show "( \<cn> ( A \<cs> B ) ) = ( B \<cs> A )" by (rule MMI_3eqtr)
qed

lemma (in MMIsar0) MMI_mulneg1t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( (\<cn>  A) ) \<cdot> B ) = 
 ( \<cn> ( A \<cdot> B ) )"
proof -
   have S1: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( (\<cn>  A) ) = 
 ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_negeq)
   from S1 have S2: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( (\<cn>  A) ) \<cdot> B ) = 
 ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> B )" by (rule MMI_opreq1d)
   have S3: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<cdot> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B )" by (rule MMI_opreq1)
   from S3 have S4: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( \<cn> ( A \<cdot> B ) ) = 
 ( \<cn> ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) )" by (rule MMI_negeqd)
   from S2 S4 have S5: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( ( (\<cn>  A) ) \<cdot> B ) = 
 ( \<cn> ( A \<cdot> B ) ) \<longleftrightarrow> 
 ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> B ) = 
 ( \<cn> ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) ) )" by (rule MMI_eqeq12d)
   have S6: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> B ) = 
 ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_opreq2)
   have S7: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_opreq2)
   from S7 have S8: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( \<cn> ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) ) = 
 ( \<cn> ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) ) )" by (rule MMI_negeqd)
   from S6 S8 have S9: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> B ) = 
 ( \<cn> ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) ) \<longleftrightarrow> 
 ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) ) = 
 ( \<cn> ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) ) ) )" by (rule MMI_eqeq12d)
   have S10: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S10 have S11: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S12: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S12 have S13: "if ( B \<in> \<complex> , B , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S11 S13 have S14: "( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) ) = 
 ( \<cn> ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) ) )" by (rule MMI_mulneg1)
   from S5 S9 S14 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( (\<cn>  A) ) \<cdot> B ) = 
 ( \<cn> ( A \<cdot> B ) )" by (rule MMI_dedth2h)
qed

lemma (in MMIsar0) MMI_mulneg2t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> ( (\<cn>  B) ) ) = 
 ( \<cn> ( A \<cdot> B ) )"
proof -
   have S1: "( B \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> 
 ( ( (\<cn>  B) ) \<cdot> A ) = 
 ( \<cn> ( B \<cdot> A ) )" by (rule MMI_mulneg1t)
   from S1 have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( (\<cn>  B) ) \<cdot> A ) = 
 ( \<cn> ( B \<cdot> A ) )" by (rule MMI_ancoms)
   have S3: "( A \<in> \<complex> \<and> ( (\<cn>  B) ) \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> ( (\<cn>  B) ) ) = 
 ( ( (\<cn>  B) ) \<cdot> A )" by (rule MMI_axmulcom)
   have S4: "B \<in> \<complex> \<longrightarrow> ( (\<cn>  B) ) \<in> \<complex>" by (rule MMI_negclt)
   from S3 S4 have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> ( (\<cn>  B) ) ) = 
 ( ( (\<cn>  B) ) \<cdot> A )" by (rule MMI_sylan2)
   have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> B ) = ( B \<cdot> A )" by (rule MMI_axmulcom)
   from S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( A \<cdot> B ) ) = 
 ( \<cn> ( B \<cdot> A ) )" by (rule MMI_negeqd)
   from S2 S5 S7 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> ( (\<cn>  B) ) ) = 
 ( \<cn> ( A \<cdot> B ) )" by (rule MMI_3eqtr4d)
qed

lemma (in MMIsar0) MMI_mulneg12t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( (\<cn>  A) ) \<cdot> B ) = 
 ( A \<cdot> ( (\<cn>  B) ) )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( (\<cn>  A) ) \<cdot> B ) = 
 ( \<cn> ( A \<cdot> B ) )" by (rule MMI_mulneg1t)
   have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> ( (\<cn>  B) ) ) = 
 ( \<cn> ( A \<cdot> B ) )" by (rule MMI_mulneg2t)
   from S1 S2 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( (\<cn>  A) ) \<cdot> B ) = 
 ( A \<cdot> ( (\<cn>  B) ) )" by (rule MMI_eqtr4d)
qed

lemma (in MMIsar0) MMI_mul2negt: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( (\<cn>  A) ) \<cdot> ( (\<cn>  B) ) ) = 
 ( A \<cdot> B )"
proof -
   have S1: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( (\<cn>  A) ) = 
 ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_negeq)
   from S1 have S2: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( (\<cn>  A) ) \<cdot> ( (\<cn>  B) ) ) = 
 ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> ( (\<cn>  B) ) )" by (rule MMI_opreq1d)
   have S3: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<cdot> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B )" by (rule MMI_opreq1)
   from S2 S3 have S4: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( ( (\<cn>  A) ) \<cdot> ( (\<cn>  B) ) ) = 
 ( A \<cdot> B ) \<longleftrightarrow> 
 ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> ( (\<cn>  B) ) ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) )" by (rule MMI_eqeq12d)
   have S5: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( (\<cn>  B) ) = 
 ( \<cn> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_negeq)
   from S5 have S6: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> ( (\<cn>  B) ) ) = 
 ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> ( \<cn> if ( B \<in> \<complex> , B , \<zero> ) ) )" by (rule MMI_opreq2d)
   have S7: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_opreq2)
   from S6 S7 have S8: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> ( (\<cn>  B) ) ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) \<longleftrightarrow> 
 ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> ( \<cn> if ( B \<in> \<complex> , B , \<zero> ) ) ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) ) )" by (rule MMI_eqeq12d)
   have S9: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S9 have S10: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S11: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S11 have S12: "if ( B \<in> \<complex> , B , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S10 S12 have S13: "( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> ( \<cn> if ( B \<in> \<complex> , B , \<zero> ) ) ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_mul2neg)
   from S4 S8 S13 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( (\<cn>  A) ) \<cdot> ( (\<cn>  B) ) ) = 
 ( A \<cdot> B )" by (rule MMI_dedth2h)
qed

lemma (in MMIsar0) MMI_negdit: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( A \<ca> B ) ) = 
 ( ( (\<cn>  A) ) \<ca> ( (\<cn>  B) ) )"
proof -
   have S1: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<ca> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B )" by (rule MMI_opreq1)
   from S1 have S2: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( \<cn> ( A \<ca> B ) ) = 
 ( \<cn> ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B ) )" by (rule MMI_negeqd)
   have S3: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( (\<cn>  A) ) = 
 ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_negeq)
   from S3 have S4: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( (\<cn>  A) ) \<ca> ( (\<cn>  B) ) ) = 
 ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<ca> ( (\<cn>  B) ) )" by (rule MMI_opreq1d)
   from S2 S4 have S5: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( \<cn> ( A \<ca> B ) ) = 
 ( ( (\<cn>  A) ) \<ca> ( (\<cn>  B) ) ) \<longleftrightarrow> 
 ( \<cn> ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B ) ) = 
 ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<ca> ( (\<cn>  B) ) ) )" by (rule MMI_eqeq12d)
   have S6: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_opreq2)
   from S6 have S7: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( \<cn> ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B ) ) = 
 ( \<cn> ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) )" by (rule MMI_negeqd)
   have S8: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( (\<cn>  B) ) = 
 ( \<cn> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_negeq)
   from S8 have S9: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<ca> ( (\<cn>  B) ) ) = 
 ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<ca> ( \<cn> if ( B \<in> \<complex> , B , \<zero> ) ) )" by (rule MMI_opreq2d)
   from S7 S9 have S10: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( \<cn> ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B ) ) = 
 ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<ca> ( (\<cn>  B) ) ) \<longleftrightarrow> 
 ( \<cn> ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) ) = 
 ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<ca> ( \<cn> if ( B \<in> \<complex> , B , \<zero> ) ) ) )" by (rule MMI_eqeq12d)
   have S11: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S11 have S12: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S13: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S13 have S14: "if ( B \<in> \<complex> , B , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S12 S14 have S15: "( \<cn> ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) ) = 
 ( ( \<cn> if ( A \<in> \<complex> , A , \<zero> ) ) \<ca> ( \<cn> if ( B \<in> \<complex> , B , \<zero> ) ) )" by (rule MMI_negdi)
   from S5 S10 S15 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( A \<ca> B ) ) = 
 ( ( (\<cn>  A) ) \<ca> ( (\<cn>  B) ) )" by (rule MMI_dedth2h)
qed

(************121 -130************************************)

lemma (in MMIsar0) MMI_negdi2t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( A \<ca> B ) ) = ( ( (\<cn>  A) ) \<cs> B )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( A \<ca> B ) ) = 
 ( ( (\<cn>  A) ) \<ca> ( (\<cn>  B) ) )" by (rule MMI_negdit)
   have S2: "( ( (\<cn>  A) ) \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( (\<cn>  A) ) \<ca> ( (\<cn>  B) ) ) = 
 ( ( (\<cn>  A) ) \<cs> B )" by (rule MMI_negsubt)
   have S3: "A \<in> \<complex> \<longrightarrow> ( (\<cn>  A) ) \<in> \<complex>" by (rule MMI_negclt)
   from S2 S3 have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( (\<cn>  A) ) \<ca> ( (\<cn>  B) ) ) = 
 ( ( (\<cn>  A) ) \<cs> B )" by (rule MMI_sylan)
   from S1 S4 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( A \<ca> B ) ) = ( ( (\<cn>  A) ) \<cs> B )"
 by (rule MMI_eqtrd)
qed

lemma (in MMIsar0) MMI_negsubdit: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( A \<cs> B ) ) = ( ( (\<cn>  A) ) \<ca> B )"
proof -
   have S1: "( A \<in> \<complex> \<and> ( (\<cn>  B) ) \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( A \<ca> ( (\<cn>  B) ) ) ) = 
 ( ( (\<cn>  A) ) \<ca> ( \<cn> ( (\<cn>  B) ) ) )" by (rule MMI_negdit)
   have S2: "B \<in> \<complex> \<longrightarrow> ( (\<cn>  B) ) \<in> \<complex>" by (rule MMI_negclt)
   from S1 S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( A \<ca> ( (\<cn>  B) ) ) ) = 
 ( ( (\<cn>  A) ) \<ca> ( \<cn> ( (\<cn>  B) ) ) )" by (rule MMI_sylan2)
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> ( (\<cn>  B) ) ) = ( A \<cs> B )" by (rule MMI_negsubt)
   from S4 have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( A \<ca> ( (\<cn>  B) ) ) ) = 
 ( \<cn> ( A \<cs> B ) )" by (rule MMI_negeqd)
   have S6: "B \<in> \<complex> \<longrightarrow> ( \<cn> ( (\<cn>  B) ) ) = B" by (rule MMI_negnegt)
   from S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( \<cn> ( (\<cn>  B) ) ) = B" 
     by (rule MMI_adantl)
   from S7 have S8: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( (\<cn>  A) ) \<ca> ( \<cn> ( (\<cn>  B) ) ) ) = 
 ( ( (\<cn>  A) ) \<ca> B )" by (rule MMI_opreq2d)
   from S3 S5 S8 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( A \<cs> B ) ) = ( ( (\<cn>  A) ) \<ca> B )"
 by (rule MMI_3eqtr3d)
qed

lemma (in MMIsar0) MMI_negsubdi2t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( A \<cs> B ) ) = ( B \<cs> A )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( A \<cs> B ) ) = ( ( (\<cn>  A) ) \<ca> B )" by (rule MMI_negsubdit)
   have S2: "( ( (\<cn>  A) ) \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( (\<cn>  A) ) \<ca> B ) = ( B \<ca> ( (\<cn>  A) ) )" by (rule MMI_axaddcom)
   have S3: "A \<in> \<complex> \<longrightarrow> ( (\<cn>  A) ) \<in> \<complex>" by (rule MMI_negclt)
   from S2 S3 have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( (\<cn>  A) ) \<ca> B ) = ( B \<ca> ( (\<cn>  A) ) )" by (rule MMI_sylan)
   have S5: "( B \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> 
 ( B \<ca> ( (\<cn>  A) ) ) = ( B \<cs> A )" by (rule MMI_negsubt)
   from S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( B \<ca> ( (\<cn>  A) ) ) = ( B \<cs> A )" by (rule MMI_ancoms)
   from S1 S4 S6 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( A \<cs> B ) ) = ( B \<cs> A )"
 by (rule MMI_3eqtrd)
qed

lemma (in MMIsar0) MMI_subsub2t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( B \<cs> C ) ) = ( A \<ca> ( C \<cs> B ) )"
proof -
   have S1: "( A \<in> \<complex> \<and> ( B \<cs> C ) \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> ( \<cn> ( B \<cs> C ) ) ) = 
 ( A \<cs> ( B \<cs> C ) )" by (rule MMI_negsubt)
   have S2: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<cs> C ) \<in> \<complex>" by (rule MMI_subclt)
   from S1 S2 have S3: "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> C \<in> \<complex> ) ) \<longrightarrow> 
 ( A \<ca> ( \<cn> ( B \<cs> C ) ) ) = 
 ( A \<cs> ( B \<cs> C ) )" by (rule MMI_sylan2)
   from S3 have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> ( \<cn> ( B \<cs> C ) ) ) = 
 ( A \<cs> ( B \<cs> C ) )" by (rule MMI_3impb)
   have S5: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( B \<cs> C ) ) = ( C \<cs> B )" by (rule MMI_negsubdi2t)
   from S5 have S6: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> ( \<cn> ( B \<cs> C ) ) ) = 
 ( A \<ca> ( C \<cs> B ) )" by (rule MMI_opreq2d)
   from S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> ( \<cn> ( B \<cs> C ) ) ) = 
 ( A \<ca> ( C \<cs> B ) )" by (rule MMI_3adant1)
   from S4 S7 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( B \<cs> C ) ) = ( A \<ca> ( C \<cs> B ) )"
 by (rule MMI_eqtr3d)
qed

lemma (in MMIsar0) MMI_subsubt: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( B \<cs> C ) ) = ( ( A \<cs> B ) \<ca> C )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( B \<cs> C ) ) = ( A \<ca> ( C \<cs> B ) )" by (rule MMI_subsub2t)
   have S2: "( A \<in> \<complex> \<and> C \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> C ) \<cs> B ) = ( A \<ca> ( C \<cs> B ) )" by (rule MMI_addsubasst)
   have S3: "( A \<in> \<complex> \<and> C \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> C ) \<cs> B ) = ( ( A \<cs> B ) \<ca> C )" by (rule MMI_addsubt)
   from S2 S3 have S4: "( A \<in> \<complex> \<and> C \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> ( C \<cs> B ) ) = ( ( A \<cs> B ) \<ca> C )" by (rule MMI_eqtr3d)
   from S4 have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> ( C \<cs> B ) ) = ( ( A \<cs> B ) \<ca> C )" by (rule MMI_3com23)
   from S1 S5 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( B \<cs> C ) ) = ( ( A \<cs> B ) \<ca> C )"
 by (rule MMI_eqtrd)
qed

lemma (in MMIsar0) MMI_subsub3t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( B \<cs> C ) ) = ( ( A \<ca> C ) \<cs> B )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( B \<cs> C ) ) = ( A \<ca> ( C \<cs> B ) )" by (rule MMI_subsub2t)
   have S2: "( A \<in> \<complex> \<and> C \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> C ) \<cs> B ) = ( A \<ca> ( C \<cs> B ) )" by (rule MMI_addsubasst)
   from S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> C ) \<cs> B ) = ( A \<ca> ( C \<cs> B ) )" by (rule MMI_3com23)
   from S1 S3 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( B \<cs> C ) ) = ( ( A \<ca> C ) \<cs> B )"
 by (rule MMI_eqtr4d)
qed

lemma (in MMIsar0) MMI_subsub4t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cs> C ) = ( A \<cs> ( B \<ca> C ) )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> ( \<cn> C ) \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( B \<cs> ( \<cn> C ) ) ) = 
 ( ( A \<cs> B ) \<ca> ( \<cn> C ) )" by (rule MMI_subsubt)
   have S2: "C \<in> \<complex> \<longrightarrow> ( \<cn> C ) \<in> \<complex>" by (rule MMI_negclt)
   from S1 S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( B \<cs> ( \<cn> C ) ) ) = 
 ( ( A \<cs> B ) \<ca> ( \<cn> C ) )" by (rule MMI_syl3an3)
   have S4: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( B \<cs> ( \<cn> C ) ) = ( B \<ca> C )" by (rule MMI_subnegt)
   from S4 have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( B \<cs> ( \<cn> C ) ) = ( B \<ca> C )" by (rule MMI_3adant1)
   from S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( B \<cs> ( \<cn> C ) ) ) = 
 ( A \<cs> ( B \<ca> C ) )" by (rule MMI_opreq2d)
   have S7: "( ( A \<cs> B ) \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<ca> ( \<cn> C ) ) = 
 ( ( A \<cs> B ) \<cs> C )" by (rule MMI_negsubt)
   have S8: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cs> B ) \<in> \<complex>" by (rule MMI_subclt)
   from S7 S8 have S9: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<ca> ( \<cn> C ) ) = 
 ( ( A \<cs> B ) \<cs> C )" by (rule MMI_sylan)
   from S9 have S10: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<ca> ( \<cn> C ) ) = 
 ( ( A \<cs> B ) \<cs> C )" by (rule MMI_3impa)
   from S3 S6 S10 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cs> C ) = ( A \<cs> ( B \<ca> C ) )"
 by (rule MMI_3eqtr3rd)
qed

lemma (in MMIsar0) MMI_sub23t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cs> C ) = ( ( A \<cs> C ) \<cs> B )"
proof -
   have S1: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( B \<ca> C ) = ( C \<ca> B )" by (rule MMI_axaddcom)
   from S1 have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( B \<ca> C ) = ( C \<ca> B )" by (rule MMI_3adant1)
   from S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( B \<ca> C ) ) = ( A \<cs> ( C \<ca> B ) )" by (rule MMI_opreq2d)
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cs> C ) = ( A \<cs> ( B \<ca> C ) )" by (rule MMI_subsub4t)
   have S5: "( A \<in> \<complex> \<and> C \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> C ) \<cs> B ) = ( A \<cs> ( C \<ca> B ) )" by (rule MMI_subsub4t)
   from S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> C ) \<cs> B ) = ( A \<cs> ( C \<ca> B ) )" by (rule MMI_3com23)
   from S3 S4 S6 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cs> C ) = ( ( A \<cs> C ) \<cs> B )"
 by (rule MMI_3eqtr4d)
qed

lemma (in MMIsar0) MMI_nnncant: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> ( B \<cs> C ) ) \<cs> C ) = ( A \<cs> B )"
proof -
   have S1: "( A \<in> \<complex> \<and> ( B \<cs> C ) \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> ( B \<cs> C ) ) \<cs> C ) = 
 ( A \<cs> ( ( B \<cs> C ) \<ca> C ) )" by (rule MMI_subsub4t)
   have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> A \<in> \<complex>" by (rule MMI_3simp1)
   have S3: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<cs> C ) \<in> \<complex>" by (rule MMI_subclt)
   from S3 have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( B \<cs> C ) \<in> \<complex>" by (rule MMI_3adant1)
   have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> C \<in> \<complex>" by (rule MMI_3simp3)
   from S1 S2 S4 S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> ( B \<cs> C ) ) \<cs> C ) = 
 ( A \<cs> ( ( B \<cs> C ) \<ca> C ) )" by (rule MMI_syl3anc)
   have S7: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( B \<cs> C ) \<ca> C ) = B" by (rule MMI_npcant)
   from S7 have S8: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( ( B \<cs> C ) \<ca> C ) ) = ( A \<cs> B )" by (rule MMI_opreq2d)
   from S8 have S9: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( ( B \<cs> C ) \<ca> C ) ) = ( A \<cs> B )" by (rule MMI_3adant1)
   from S6 S9 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> ( B \<cs> C ) ) \<cs> C ) = ( A \<cs> B )"
 by (rule MMI_eqtrd)
qed

lemma (in MMIsar0) MMI_nnncan1t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cs> ( A \<cs> C ) ) = ( C \<cs> B )"
proof -
   have S1: "( ( A \<cs> B ) \<in> \<complex> \<and> ( A \<cs> C ) \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<ca> ( \<cn> ( A \<cs> C ) ) ) = 
 ( ( A \<cs> B ) \<cs> ( A \<cs> C ) )" by (rule MMI_negsubt)
   have S2: "( ( A \<cs> B ) \<in> \<complex> \<and> ( \<cn> ( A \<cs> C ) ) \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<ca> ( \<cn> ( A \<cs> C ) ) ) = 
 ( ( \<cn> ( A \<cs> C ) ) \<ca> ( A \<cs> B ) )" by (rule MMI_axaddcom)
   have S3: "( A \<cs> C ) \<in> \<complex> \<longrightarrow> ( \<cn> ( A \<cs> C ) ) \<in> \<complex>" 
     by (rule MMI_negclt)
   from S2 S3 have S4: "( ( A \<cs> B ) \<in> \<complex> \<and> ( A \<cs> C ) \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<ca> ( \<cn> ( A \<cs> C ) ) ) = 
 ( ( \<cn> ( A \<cs> C ) ) \<ca> ( A \<cs> B ) )" by (rule MMI_sylan2)
   from S1 S4 have S5: "( ( A \<cs> B ) \<in> \<complex> \<and> ( A \<cs> C ) \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cs> ( A \<cs> C ) ) = 
 ( ( \<cn> ( A \<cs> C ) ) \<ca> ( A \<cs> B ) )" by (rule MMI_eqtr3d)
   have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cs> B ) \<in> \<complex>" by (rule MMI_subclt)
   from S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> B ) \<in> \<complex>" by (rule MMI_3adant3)
   have S8: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cs> C ) \<in> \<complex>" by (rule MMI_subclt)
   from S8 have S9: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> C ) \<in> \<complex>" by (rule MMI_3adant2)
   from S5 S7 S9 have S10: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cs> ( A \<cs> C ) ) = 
 ( ( \<cn> ( A \<cs> C ) ) \<ca> ( A \<cs> B ) )" by (rule MMI_sylanc)
   have S11: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( A \<cs> C ) ) = ( C \<cs> A )" by (rule MMI_negsubdi2t)
   from S11 have S12: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( A \<cs> C ) ) = ( C \<cs> A )" by (rule MMI_3adant2)
   from S12 have S13: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( \<cn> ( A \<cs> C ) ) \<ca> ( A \<cs> B ) ) = 
 ( ( C \<cs> A ) \<ca> ( A \<cs> B ) )" by (rule MMI_opreq1d)
   have S14: "( C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( C \<cs> A ) \<ca> ( A \<cs> B ) ) = ( C \<cs> B )" by (rule MMI_npncant)
   from S14 have S15: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( C \<cs> A ) \<ca> ( A \<cs> B ) ) = ( C \<cs> B )" by (rule MMI_3coml)
   from S10 S13 S15 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cs> ( A \<cs> C ) ) = ( C \<cs> B )"
 by (rule MMI_3eqtrd)
qed

(*****131-140***************************************)

lemma (in MMIsar0) MMI_nnncan2t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> C ) \<cs> ( B \<cs> C ) ) = ( A \<cs> B )"
proof -
   have S1: "( A \<in> \<complex> \<and> ( B \<cs> C ) \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> ( B \<cs> C ) ) \<cs> C ) = 
 ( ( A \<cs> C ) \<cs> ( B \<cs> C ) )" by (rule MMI_sub23t)
   have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> A \<in> \<complex>" by (rule MMI_3simp1)
   have S3: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<cs> C ) \<in> \<complex>" by (rule MMI_subclt)
   from S3 have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( B \<cs> C ) \<in> \<complex>" by (rule MMI_3adant1)
   have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> C \<in> \<complex>" by (rule MMI_3simp3)
   from S1 S2 S4 S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> ( B \<cs> C ) ) \<cs> C ) = 
 ( ( A \<cs> C ) \<cs> ( B \<cs> C ) )" by (rule MMI_syl3anc)
   have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> ( B \<cs> C ) ) \<cs> C ) = ( A \<cs> B )" by (rule MMI_nnncant)
   from S6 S7 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> C ) \<cs> ( B \<cs> C ) ) = ( A \<cs> B )" by (rule MMI_eqtr3d)
qed

lemma (in MMIsar0) MMI_nncant: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( A \<cs> B ) ) = B"
proof -
   have S1: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   have S2: "( A \<in> \<complex> \<and> \<zero> \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> \<zero> ) \<cs> ( A \<cs> B ) ) = ( B \<cs> \<zero> )" by (rule MMI_nnncan1t)
   from S1 S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> \<zero> ) \<cs> ( A \<cs> B ) ) = ( B \<cs> \<zero> )" by (rule MMI_mp3an2)
   have S4: "A \<in> \<complex> \<longrightarrow> ( A \<cs> \<zero> ) = A" by (rule MMI_subid1t)
   from S4 have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cs> \<zero> ) = A" 
     by (rule MMI_adantr)
   from S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> \<zero> ) \<cs> ( A \<cs> B ) ) = 
 ( A \<cs> ( A \<cs> B ) )" by (rule MMI_opreq1d)
   have S7: "B \<in> \<complex> \<longrightarrow> ( B \<cs> \<zero> ) = B" by (rule MMI_subid1t)
   from S7 have S8: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( B \<cs> \<zero> ) = B" 
     by (rule MMI_adantl)
   from S3 S6 S8 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( A \<cs> B ) ) = B" by (rule MMI_3eqtr3d)
qed

lemma (in MMIsar0) MMI_nppcan2t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> ( B \<ca> C ) ) \<ca> C ) = ( A \<cs> B )"
proof -
   have S1: "( A \<in> \<complex> \<and> ( B \<ca> C ) \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( ( B \<ca> C ) \<cs> C ) ) = 
 ( ( A \<cs> ( B \<ca> C ) ) \<ca> C )" by (rule MMI_subsubt)
   have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> A \<in> \<complex>" by (rule MMI_3simp1)
   have S3: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<ca> C ) \<in> \<complex>" by (rule MMI_axaddcl)
   from S3 have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( B \<ca> C ) \<in> \<complex>" by (rule MMI_3adant1)
   have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> C \<in> \<complex>" by (rule MMI_3simp3)
   from S1 S2 S4 S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( ( B \<ca> C ) \<cs> C ) ) = 
 ( ( A \<cs> ( B \<ca> C ) ) \<ca> C )" by (rule MMI_syl3anc)
   have S7: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( B \<ca> C ) \<cs> C ) = B" by (rule MMI_pncant)
   from S7 have S8: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( B \<ca> C ) \<cs> C ) = B" by (rule MMI_3adant1)
   from S8 have S9: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cs> ( ( B \<ca> C ) \<cs> C ) ) = ( A \<cs> B )" by (rule MMI_opreq2d)
   from S6 S9 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cs> ( B \<ca> C ) ) \<ca> C ) = ( A \<cs> B )" by (rule MMI_eqtr3d)
qed

lemma (in MMIsar0) MMI_mulm1t: 
   shows "A \<in> \<complex> \<longrightarrow> ( ( \<cn> \<one> ) \<cdot> A ) = ( (\<cn>  A) )"
proof -
   have S1: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S2: "( \<one> \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> 
 ( ( \<cn> \<one> ) \<cdot> A ) = ( \<cn> ( \<one> \<cdot> A ) )" by (rule MMI_mulneg1t)
   from S1 S2 have S3: "A \<in> \<complex> \<longrightarrow> 
 ( ( \<cn> \<one> ) \<cdot> A ) = ( \<cn> ( \<one> \<cdot> A ) )" by (rule MMI_mpan)
   have S4: "A \<in> \<complex> \<longrightarrow> ( \<one> \<cdot> A ) = A" by (rule MMI_mulid2t)
   from S4 have S5: "A \<in> \<complex> \<longrightarrow> ( \<cn> ( \<one> \<cdot> A ) ) = ( (\<cn>  A) )" 
     by (rule MMI_negeqd)
   from S3 S5 show "A \<in> \<complex> \<longrightarrow> ( ( \<cn> \<one> ) \<cdot> A ) = ( (\<cn>  A) )" 
     by (rule MMI_eqtrd)
qed

lemma (in MMIsar0) MMI_mulm1: assumes A1: "A \<in> \<complex>"   
   shows "( ( \<cn> \<one> ) \<cdot> A ) = ( (\<cn>  A) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   have S2: "A \<in> \<complex> \<longrightarrow> ( ( \<cn> \<one> ) \<cdot> A ) = ( (\<cn>  A) )" by (rule MMI_mulm1t)
   from S1 S2 show "( ( \<cn> \<one> ) \<cdot> A ) = ( (\<cn>  A) )" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_sub4t: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cs> ( C \<ca> D ) ) = 
 ( ( A \<cs> C ) \<ca> ( B \<cs> D ) )"
proof -
   have S1: "( C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( C \<ca> D ) ) = 
 ( ( \<cn> C ) \<ca> ( \<cn> D ) )" by (rule MMI_negdit)
   from S1 have S2: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( \<cn> ( C \<ca> D ) ) = 
 ( ( \<cn> C ) \<ca> ( \<cn> D ) )" by (rule MMI_adantl)
   from S2 have S3: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<ca> B ) \<ca> ( \<cn> ( C \<ca> D ) ) ) = 
 ( ( A \<ca> B ) \<ca> ( ( \<cn> C ) \<ca> ( \<cn> D ) ) )" 
     by (rule MMI_opreq2d)
   have S4: 
     "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( ( \<cn> C ) \<in> \<complex> \<and> ( \<cn> D ) \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<ca> B ) \<ca> ( ( \<cn> C ) \<ca> ( \<cn> D ) ) ) = 
 ( ( A \<ca> ( \<cn> C ) ) \<ca> ( B \<ca> ( \<cn> D ) ) )" by (rule MMI_add4t)
   have S5: "C \<in> \<complex> \<longrightarrow> ( \<cn> C ) \<in> \<complex>" by (rule MMI_negclt)
   have S6: "D \<in> \<complex> \<longrightarrow> ( \<cn> D ) \<in> \<complex>" by (rule MMI_negclt)
   from S5 S6 have S7: "( C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
 ( ( \<cn> C ) \<in> \<complex> \<and> ( \<cn> D ) \<in> \<complex> )" by (rule MMI_anim12i)
   from S4 S7 have S8: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<ca> B ) \<ca> ( ( \<cn> C ) \<ca> ( \<cn> D ) ) ) = 
 ( ( A \<ca> ( \<cn> C ) ) \<ca> ( B \<ca> ( \<cn> D ) ) )" by (rule MMI_sylan2)
   from S3 S8 have S9: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<ca> B ) \<ca> ( \<cn> ( C \<ca> D ) ) ) = 
 ( ( A \<ca> ( \<cn> C ) ) \<ca> ( B \<ca> ( \<cn> D ) ) )" by (rule MMI_eqtrd)
   have S10: "( ( A \<ca> B ) \<in> \<complex> \<and> ( C \<ca> D ) \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<ca> ( \<cn> ( C \<ca> D ) ) ) = 
 ( ( A \<ca> B ) \<cs> ( C \<ca> D ) )" by (rule MMI_negsubt)
   have S11: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> B ) \<in> \<complex>" by (rule MMI_axaddcl)
   have S12: "( C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( C \<ca> D ) \<in> \<complex>" by (rule MMI_axaddcl)
   from S10 S11 S12 have S13: 
     "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<ca> B ) \<ca> ( \<cn> ( C \<ca> D ) ) ) = 
 ( ( A \<ca> B ) \<cs> ( C \<ca> D ) )" by (rule MMI_syl2an)
   have S14: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> ( \<cn> C ) ) = ( A \<cs> C )" by (rule MMI_negsubt)
   from S14 have S15: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( A \<ca> ( \<cn> C ) ) = ( A \<cs> C )" by (rule MMI_ad2ant2r)
   have S16: "( B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
 ( B \<ca> ( \<cn> D ) ) = ( B \<cs> D )" by (rule MMI_negsubt)
   from S16 have S17: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( B \<ca> ( \<cn> D ) ) = ( B \<cs> D )" by (rule MMI_ad2ant2l)
   from S15 S17 have S18: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<ca> ( \<cn> C ) ) \<ca> ( B \<ca> ( \<cn> D ) ) ) = 
 ( ( A \<cs> C ) \<ca> ( B \<cs> D ) )" by (rule MMI_opreq12d)
   from S9 S13 S18 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cs> ( C \<ca> D ) ) = 
 ( ( A \<cs> C ) \<ca> ( B \<cs> D ) )" by (rule MMI_3eqtr3d)
qed

lemma (in MMIsar0) MMI_sub4: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>" and
    A4: "D \<in> \<complex>"   
   shows "( ( A \<ca> B ) \<cs> ( C \<ca> D ) ) = 
 ( ( A \<cs> C ) \<ca> ( B \<cs> D ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from S1 S2 have S3: "A \<in> \<complex> \<and> B \<in> \<complex>" by (rule MMI_pm3_2i)
   from A3 have S4: "C \<in> \<complex>".
   from A4 have S5: "D \<in> \<complex>".
   from S4 S5 have S6: "C \<in> \<complex> \<and> D \<in> \<complex>" by (rule MMI_pm3_2i)
   have S7: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cs> ( C \<ca> D ) ) = 
 ( ( A \<cs> C ) \<ca> ( B \<cs> D ) )" by (rule MMI_sub4t)
   from S3 S6 S7 show "( ( A \<ca> B ) \<cs> ( C \<ca> D ) ) = 
 ( ( A \<cs> C ) \<ca> ( B \<cs> D ) )" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_mulsubt: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cdot> ( C \<cs> D ) ) = 
 ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<cs> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> ( (\<cn>  B) ) ) = ( A \<cs> B )" by (rule MMI_negsubt)
   have S2: "( C \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
 ( C \<ca> ( \<cn> D ) ) = ( C \<cs> D )" by (rule MMI_negsubt)
   from S1 S2 have S3: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<ca> ( (\<cn>  B) ) ) \<cdot> ( C \<ca> ( \<cn> D ) ) ) = 
 ( ( A \<cs> B ) \<cdot> ( C \<cs> D ) )" by (rule MMI_opreqan12d)
   have S4: "( ( A \<in> \<complex> \<and> ( (\<cn>  B) ) \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> ( \<cn> D ) \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<ca> ( (\<cn>  B) ) ) \<cdot> ( C \<ca> ( \<cn> D ) ) ) = 
 ( ( ( A \<cdot> C ) \<ca> ( ( \<cn> D ) \<cdot> ( (\<cn>  B) ) ) ) \<ca> ( ( A \<cdot> ( \<cn> D ) ) \<ca> ( C \<cdot> ( (\<cn>  B) ) ) ) )" by (rule MMI_muladdt)
   have S5: "D \<in> \<complex> \<longrightarrow> ( \<cn> D ) \<in> \<complex>" by (rule MMI_negclt)
   from S4 S5 have S6: "( ( A \<in> \<complex> \<and> ( (\<cn>  B) ) \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<ca> ( (\<cn>  B) ) ) \<cdot> ( C \<ca> ( \<cn> D ) ) ) = 
 ( ( ( A \<cdot> C ) \<ca> ( ( \<cn> D ) \<cdot> ( (\<cn>  B) ) ) ) \<ca> 
     ( ( A \<cdot> ( \<cn> D ) ) \<ca> ( C \<cdot> ( (\<cn>  B) ) ) ) )" by (rule MMI_sylanr2)
   have S7: "B \<in> \<complex> \<longrightarrow> ( (\<cn>  B) ) \<in> \<complex>" by (rule MMI_negclt)
   from S6 S7 have S8: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<ca> ( (\<cn>  B) ) ) \<cdot> ( C \<ca> ( \<cn> D ) ) ) = 
 ( ( ( A \<cdot> C ) \<ca> ( ( \<cn> D ) \<cdot> ( (\<cn>  B) ) ) ) 
     \<ca> ( ( A \<cdot> ( \<cn> D ) ) \<ca> ( C \<cdot> ( (\<cn>  B) ) ) ) )" 
     by (rule MMI_sylanl2)
   have S9: "( D \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( \<cn> D ) \<cdot> ( (\<cn>  B) ) ) = ( D \<cdot> B )" by (rule MMI_mul2negt)
   from S9 have S10: "( B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
 ( ( \<cn> D ) \<cdot> ( (\<cn>  B) ) ) = ( D \<cdot> B )" by (rule MMI_ancoms)
   from S10 have S11: "( B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> C ) \<ca> ( ( \<cn> D ) \<cdot> ( (\<cn>  B) ) ) ) = 
 ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) )" by (rule MMI_opreq2d)
   from S11 have S12: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<cdot> C ) \<ca> ( ( \<cn> D ) \<cdot> ( (\<cn>  B) ) ) ) = 
 ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) )" by (rule MMI_ad2ant2l)
   have S13: "( A \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> ( \<cn> D ) ) = ( \<cn> ( A \<cdot> D ) )" by (rule MMI_mulneg2t)
   have S14: "( C \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( C \<cdot> ( (\<cn>  B) ) ) = ( \<cn> ( C \<cdot> B ) )" by (rule MMI_mulneg2t)
   from S13 S14 have S15: "( ( A \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> B \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<cdot> ( \<cn> D ) ) \<ca> ( C \<cdot> ( (\<cn>  B) ) ) ) = 
 ( ( \<cn> ( A \<cdot> D ) ) \<ca> ( \<cn> ( C \<cdot> B ) ) )" by (rule MMI_opreqan12d)
   have S16: "( ( A \<cdot> D ) \<in> \<complex> \<and> ( C \<cdot> B ) \<in> \<complex> ) \<longrightarrow> 
 ( \<cn> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) ) = 
 ( ( \<cn> ( A \<cdot> D ) ) \<ca> ( \<cn> ( C \<cdot> B ) ) )" by (rule MMI_negdit)
   have S17: "( A \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( A \<cdot> D ) \<in> \<complex>" by (rule MMI_axmulcl)
   have S18: "( C \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( C \<cdot> B ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S16 S17 S18 have S19: 
     "( ( A \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> B \<in> \<complex> ) ) \<longrightarrow> 
 ( \<cn> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) ) = 
 ( ( \<cn> ( A \<cdot> D ) ) \<ca> ( \<cn> ( C \<cdot> B ) ) )" by (rule MMI_syl2an)
   from S15 S19 have S20: "( ( A \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> B \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<cdot> ( \<cn> D ) ) \<ca> ( C \<cdot> ( (\<cn>  B) ) ) ) = 
 ( \<cn> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) )" by (rule MMI_eqtr4d)
   from S20 have S21: "( ( A \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( B \<in> \<complex> \<and> C \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<cdot> ( \<cn> D ) ) \<ca> ( C \<cdot> ( (\<cn>  B) ) ) ) = 
 ( \<cn> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) )" by (rule MMI_ancom2s)
   from S21 have S22: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<cdot> ( \<cn> D ) ) \<ca> ( C \<cdot> ( (\<cn>  B) ) ) ) = 
 ( \<cn> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) )" by (rule MMI_an42s)
   from S12 S22 have S23: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( ( A \<cdot> C ) \<ca> ( ( \<cn> D ) \<cdot> ( (\<cn>  B) ) ) ) \<ca> 
     ( ( A \<cdot> ( \<cn> D ) ) \<ca> ( C \<cdot> ( (\<cn>  B) ) ) ) ) = 
 ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<ca> ( \<cn> ( ( A \<cdot> D ) \<ca> 
     ( C \<cdot> B ) ) ) )" by (rule MMI_opreq12d)
   have S24: "( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<in> \<complex> \<and> ( ( A \<cdot> D ) \<ca> 
     ( C \<cdot> B ) ) \<in> \<complex> ) \<longrightarrow> 
 ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<ca> ( \<cn> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) ) ) = 
 ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<cs> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) )" 
     by (rule MMI_negsubt)
   have S25: "( ( A \<cdot> C ) \<in> \<complex> \<and> ( D \<cdot> B ) \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<in> \<complex>" by (rule MMI_axaddcl)
   have S26: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( A \<cdot> C ) \<in> \<complex>" by (rule MMI_axmulcl)
   have S27: "( D \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( D \<cdot> B ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S27 have S28: "( B \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( D \<cdot> B ) \<in> \<complex>" 
     by (rule MMI_ancoms)
   from S25 S26 S28 have S29: 
     "( ( A \<in> \<complex> \<and> C \<in> \<complex> ) \<and> ( B \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<in> \<complex>" by (rule MMI_syl2an)
   from S29 have S30: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<in> \<complex>" by (rule MMI_an4s)
   have S31: "( ( A \<cdot> D ) \<in> \<complex> \<and> ( C \<cdot> B ) \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) \<in> \<complex>" by (rule MMI_axaddcl)
   from S17 have S32: "( A \<in> \<complex> \<and> D \<in> \<complex> ) \<longrightarrow> ( A \<cdot> D ) \<in> \<complex>" .
   from S18 have S33: "( C \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( C \<cdot> B ) \<in> \<complex>" .
   from S33 have S34: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( C \<cdot> B ) \<in> \<complex>" 
     by (rule MMI_ancoms)
   from S31 S32 S34 have S35: 
     "( ( A \<in> \<complex> \<and> D \<in> \<complex> ) \<and> ( B \<in> \<complex> \<and> C \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) \<in> \<complex>" by (rule MMI_syl2an)
   from S35 have S36: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) \<in> \<complex>" by (rule MMI_an42s)
   from S24 S30 S36 have S37: 
     "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<ca> ( \<cn> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) ) ) = 
 ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<cs> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) )" 
     by (rule MMI_sylanc)
   from S8 S23 S37 have S38: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<ca> ( (\<cn>  B) ) ) \<cdot> ( C \<ca> ( \<cn> D ) ) ) = 
 ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<cs> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) )" 
     by (rule MMI_3eqtrd)
   from S3 S38 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( C \<in> \<complex> \<and> D \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cdot> ( C \<cs> D ) ) = 
 ( ( ( A \<cdot> C ) \<ca> ( D \<cdot> B ) ) \<cs> ( ( A \<cdot> D ) \<ca> ( C \<cdot> B ) ) )" 
     by (rule MMI_eqtr3d)
qed

lemma (in MMIsar0) MMI_pnpcant: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cs> ( A \<ca> C ) ) = ( B \<cs> C )"
proof -
   have S1: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> ( A \<in> \<complex> \<and> C \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cs> ( A \<ca> C ) ) = 
 ( ( A \<cs> A ) \<ca> ( B \<cs> C ) )" by (rule MMI_sub4t)
   from S1 have S2: "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> C \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cs> ( A \<ca> C ) ) = 
 ( ( A \<cs> A ) \<ca> ( B \<cs> C ) )" by (rule MMI_anandis)
   have S3: "A \<in> \<complex> \<longrightarrow> ( A \<cs> A ) = \<zero>" by (rule MMI_subidt)
   from S3 have S4: "A \<in> \<complex> \<longrightarrow> 
 ( ( A \<cs> A ) \<ca> ( B \<cs> C ) ) = 
 ( \<zero> \<ca> ( B \<cs> C ) )" by (rule MMI_opreq1d)
   have S5: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( B \<cs> C ) \<in> \<complex>" by (rule MMI_subclt)
   have S6: "( B \<cs> C ) \<in> \<complex> \<longrightarrow> 
 ( \<zero> \<ca> ( B \<cs> C ) ) = ( B \<cs> C )" by (rule MMI_addid2t)
   from S5 S6 have S7: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( \<zero> \<ca> ( B \<cs> C ) ) = ( B \<cs> C )" by (rule MMI_syl)
   from S4 S7 have S8: "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> C \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<cs> A ) \<ca> ( B \<cs> C ) ) = ( B \<cs> C )" by (rule MMI_sylan9eq)
   from S2 S8 have S9: "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> C \<in> \<complex> ) ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cs> ( A \<ca> C ) ) = ( B \<cs> C )" by (rule MMI_eqtrd)
   from S9 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cs> ( A \<ca> C ) ) = ( B \<cs> C )" by (rule MMI_3impb)
qed

lemma (in MMIsar0) MMI_pnpcan2t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> C ) \<cs> ( B \<ca> C ) ) = ( A \<cs> B )"
proof -
   have S1: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> C ) = ( C \<ca> A )" by (rule MMI_axaddcom)
   from S1 have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> C ) = ( C \<ca> A )" by (rule MMI_3adant2)
   have S3: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( B \<ca> C ) = ( C \<ca> B )" by (rule MMI_axaddcom)
   from S3 have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( B \<ca> C ) = ( C \<ca> B )" by (rule MMI_3adant1)
   from S2 S4 have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> C ) \<cs> ( B \<ca> C ) ) = 
 ( ( C \<ca> A ) \<cs> ( C \<ca> B ) )" by (rule MMI_opreq12d)
   have S6: "( C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( C \<ca> A ) \<cs> ( C \<ca> B ) ) = ( A \<cs> B )" by (rule MMI_pnpcant)
   from S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( C \<ca> A ) \<cs> ( C \<ca> B ) ) = ( A \<cs> B )" by (rule MMI_3coml)
   from S5 S7 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> C ) \<cs> ( B \<ca> C ) ) = ( A \<cs> B )" by (rule MMI_eqtrd)
qed

(*******141-150*********************************)
lemma (in MMIsar0) MMI_pnncant: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cs> ( A \<cs> C ) ) = ( B \<ca> C )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> ( \<cn> C ) \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cs> ( A \<ca> ( \<cn> C ) ) ) = 
 ( B \<cs> ( \<cn> C ) )" by (rule MMI_pnpcant)
   have S2: "C \<in> \<complex> \<longrightarrow> ( \<cn> C ) \<in> \<complex>" by (rule MMI_negclt)
   from S1 S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cs> ( A \<ca> ( \<cn> C ) ) ) = 
 ( B \<cs> ( \<cn> C ) )" by (rule MMI_syl3an3)
   have S4: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> ( \<cn> C ) ) = ( A \<cs> C )" by (rule MMI_negsubt)
   from S4 have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> ( \<cn> C ) ) = ( A \<cs> C )" by (rule MMI_3adant2)
   from S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cs> ( A \<ca> ( \<cn> C ) ) ) = 
 ( ( A \<ca> B ) \<cs> ( A \<cs> C ) )" by (rule MMI_opreq2d)
   have S7: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( B \<cs> ( \<cn> C ) ) = ( B \<ca> C )" by (rule MMI_subnegt)
   from S7 have S8: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( B \<cs> ( \<cn> C ) ) = ( B \<ca> C )" by (rule MMI_3adant1)
   from S3 S6 S8 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cs> ( A \<cs> C ) ) = ( B \<ca> C )" by (rule MMI_3eqtr3d)
qed

lemma (in MMIsar0) MMI_ppncant: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<ca> ( C \<cs> B ) ) = ( A \<ca> C )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> B ) = ( B \<ca> A )" by (rule MMI_axaddcom)
   from S1 have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> B ) = ( B \<ca> A )" by (rule MMI_3adant3)
   from S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cs> ( B \<cs> C ) ) = 
 ( ( B \<ca> A ) \<cs> ( B \<cs> C ) )" by (rule MMI_opreq1d)
   have S4: "( ( A \<ca> B ) \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cs> ( B \<cs> C ) ) = 
 ( ( A \<ca> B ) \<ca> ( C \<cs> B ) )" by (rule MMI_subsub2t)
   have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<ca> B ) \<in> \<complex>" by (rule MMI_axaddcl)
   from S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> B ) \<in> \<complex>" by (rule MMI_3adant3)
   have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> B \<in> \<complex>" by (rule MMI_3simp2)
   have S8: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> C \<in> \<complex>" by (rule MMI_3simp3)
   from S4 S6 S7 S8 have S9: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cs> ( B \<cs> C ) ) = 
 ( ( A \<ca> B ) \<ca> ( C \<cs> B ) )" by (rule MMI_syl3anc)
   have S10: "( B \<in> \<complex> \<and> A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( B \<ca> A ) \<cs> ( B \<cs> C ) ) = ( A \<ca> C )" by (rule MMI_pnncant)
   from S10 have S11: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( B \<ca> A ) \<cs> ( B \<cs> C ) ) = ( A \<ca> C )" by (rule MMI_3com12)
   from S3 S9 S11 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<ca> ( C \<cs> B ) ) = ( A \<ca> C )" by (rule MMI_3eqtr3d)
qed

lemma (in MMIsar0) MMI_pnncan: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "( ( A \<ca> B ) \<cs> ( A \<cs> C ) ) = ( B \<ca> C )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cs> ( A \<cs> C ) ) = ( B \<ca> C )" by (rule MMI_pnncant)
   from S1 S2 S3 S4 show "( ( A \<ca> B ) \<cs> ( A \<cs> C ) ) = ( B \<ca> C )" by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_mulcan: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>" and
    A4: "A \<noteq> \<zero>"   
   shows "( A \<cdot> B ) = ( A \<cdot> C ) \<longleftrightarrow> B = C"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A4 have S2: "A \<noteq> \<zero>".
   from S1 S2 have S3: "\<exists> x \<in> \<complex> . ( A \<cdot> x ) = \<one>" by (rule MMI_recex)
   from A1 have S4: "A \<in> \<complex>".
   from A2 have S5: "B \<in> \<complex>".
   { fix x
     have S6: "( x \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
       ( ( x \<cdot> A ) \<cdot> B ) = ( x \<cdot> ( A \<cdot> B ) )" by (rule MMI_axmulass)
     from S5 S6 have S7: "( x \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> 
       ( ( x \<cdot> A ) \<cdot> B ) = ( x \<cdot> ( A \<cdot> B ) )" by (rule MMI_mp3an3)
     from A3 have S8: "C \<in> \<complex>".
     have S9: "( x \<in> \<complex> \<and> A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
       ( ( x \<cdot> A ) \<cdot> C ) = ( x \<cdot> ( A \<cdot> C ) )" by (rule MMI_axmulass)
     from S8 S9 have S10: "( x \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> 
       ( ( x \<cdot> A ) \<cdot> C ) = ( x \<cdot> ( A \<cdot> C ) )" by (rule MMI_mp3an3)
     from S7 S10 have S11: "( x \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> 
       ( ( ( x \<cdot> A ) \<cdot> B ) = 
       ( ( x \<cdot> A ) \<cdot> C ) \<longleftrightarrow> 
       ( x \<cdot> ( A \<cdot> B ) ) = 
       ( x \<cdot> ( A \<cdot> C ) ) )" by (rule MMI_eqeq12d)
     from S4 S11 have S12: "x \<in> \<complex> \<longrightarrow> 
       ( ( ( x \<cdot> A ) \<cdot> B ) = 
       ( ( x \<cdot> A ) \<cdot> C ) \<longleftrightarrow> 
       ( x \<cdot> ( A \<cdot> B ) ) = 
       ( x \<cdot> ( A \<cdot> C ) ) )" by (rule MMI_mpan2)
     have S13: 
       "( A \<cdot> B ) =  ( A \<cdot> C ) \<longrightarrow> 
       ( x \<cdot> ( A \<cdot> B ) ) = ( x \<cdot> ( A \<cdot> C ) )" by (rule MMI_opreq2)
     from S12 S13 have S14: "x \<in> \<complex> \<longrightarrow>  
       ( ( A \<cdot> B ) =  ( A \<cdot> C ) \<longrightarrow>  ( ( x \<cdot> A ) \<cdot> B ) = 
       ( ( x \<cdot> A ) \<cdot> C ) )" by (rule MMI_syl5bir)
     from S14 have S15: 
       "( x \<in> \<complex> \<and> ( A \<cdot> x ) =  \<one> ) \<longrightarrow>  ( ( A \<cdot> B ) = 
       ( A \<cdot> C ) \<longrightarrow>  ( ( x \<cdot> A ) \<cdot> B ) = 
       ( ( x \<cdot> A ) \<cdot> C ) )" by (rule MMI_adantr)
     from A1 have S16: "A \<in> \<complex>".
     have S17: "( A \<in> \<complex> \<and> x \<in> \<complex> ) \<longrightarrow> 
       ( A \<cdot> x ) = ( x \<cdot> A )" by (rule MMI_axmulcom)
     from S16 S17 have S18: "x \<in> \<complex> \<longrightarrow> ( A \<cdot> x ) = ( x \<cdot> A )" 
       by (rule MMI_mpan)
     from S18 have S19: "x \<in> \<complex> \<longrightarrow> 
       ( ( A \<cdot> x ) = \<one> \<longleftrightarrow> ( x \<cdot> A ) = \<one> )" by (rule MMI_eqeq1d)
     have S20: "( x \<cdot> A ) = 
       \<one> \<longrightarrow> ( ( x \<cdot> A ) \<cdot> B ) = ( \<one> \<cdot> B )" by (rule MMI_opreq1)
     from A2 have S21: "B \<in> \<complex>".
     from S21 have S22: "( \<one> \<cdot> B ) = B" by (rule MMI_mulid2)
     from S20 S22 have S23: "( x \<cdot> A ) = \<one> \<longrightarrow> ( ( x \<cdot> A ) \<cdot> B ) = B" 
       by (rule MMI_syl6eq)
     have S24: "( x \<cdot> A ) = 
       \<one> \<longrightarrow> ( ( x \<cdot> A ) \<cdot> C ) = ( \<one> \<cdot> C )" by (rule MMI_opreq1)
     from A3 have S25: "C \<in> \<complex>".
     from S25 have S26: "( \<one> \<cdot> C ) = C" by (rule MMI_mulid2)
     from S24 S26 have S27: "( x \<cdot> A ) = \<one> \<longrightarrow> ( ( x \<cdot> A ) \<cdot> C ) = C" 
       by (rule MMI_syl6eq)
     from S23 S27 have S28: "( x \<cdot> A ) =  \<one> \<longrightarrow> 
       ( ( ( x \<cdot> A ) \<cdot> B ) = 
       ( ( x \<cdot> A ) \<cdot> C ) \<longleftrightarrow> B = C )" by (rule MMI_eqeq12d)
     from S19 S28 have S29: "x \<in> \<complex> \<longrightarrow> 
       ( ( A \<cdot> x ) =  \<one> \<longrightarrow> 
       ( ( ( x \<cdot> A ) \<cdot> B ) = 
       ( ( x \<cdot> A ) \<cdot> C ) \<longleftrightarrow> B = C ) )" by (rule MMI_syl6bi)
     from S29 have S30: 
       "( x \<in> \<complex> \<and> ( A \<cdot> x ) = \<one> ) \<longrightarrow> 
       ( ( ( x \<cdot> A ) \<cdot> B ) = 
       ( ( x \<cdot> A ) \<cdot> C ) \<longleftrightarrow> B = C )" by (rule MMI_imp)
     from S15 S30 have S31: 
       "( x \<in> \<complex> \<and> ( A \<cdot> x ) = \<one> ) \<longrightarrow> 
       ( ( A \<cdot> B ) = ( A \<cdot> C ) \<longrightarrow> B = C )" by (rule MMI_sylibd)
     from S31 have "x \<in> \<complex> \<longrightarrow> 
       ( ( A \<cdot> x ) = \<one> \<longrightarrow>  ( ( A \<cdot> B ) = ( A \<cdot> C ) \<longrightarrow> B = C ) )" 
       by (rule MMI_ex)
     } then have  S32: "\<forall> x. x \<in> \<complex> \<longrightarrow> 
       ( ( A \<cdot> x ) = \<one> \<longrightarrow>  ( ( A \<cdot> B ) = ( A \<cdot> C ) \<longrightarrow> B = C ) )" 
       by auto
     from S32 have S33: "( \<exists> x \<in> \<complex> . ( A \<cdot> x ) =  \<one> ) \<longrightarrow> 
       ( ( A \<cdot> B ) = ( A \<cdot> C ) \<longrightarrow> B = C )" by (rule MMI_r19_23aiv)
     from S3 S33 have S34: "( A \<cdot> B ) = ( A \<cdot> C ) \<longrightarrow> B = C" 
       by (rule MMI_ax_mp)
     have S35: "B = C \<longrightarrow> ( A \<cdot> B ) = ( A \<cdot> C )" by (rule MMI_opreq2)
     from S34 S35 show "( A \<cdot> B ) = ( A \<cdot> C ) \<longleftrightarrow> B = C" by (rule MMI_impbi)
qed

lemma (in MMIsar0) MMI_mulcant2: assumes A1: "A \<noteq> \<zero>"   
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> B ) = ( A \<cdot> C ) \<longleftrightarrow> B = C )"
proof -
   have S1: "A = 
 if ( A \<in> \<complex> , A , \<one> ) \<longrightarrow> 
 ( A \<cdot> B ) = 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> B )" by (rule MMI_opreq1)
   have S2: "A = 
 if ( A \<in> \<complex> , A , \<one> ) \<longrightarrow> 
 ( A \<cdot> C ) = 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> C )" by (rule MMI_opreq1)
   from S1 S2 have S3: "A = 
 if ( A \<in> \<complex> , A , \<one> ) \<longrightarrow> 
 ( ( A \<cdot> B ) = 
 ( A \<cdot> C ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> B ) = 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> C ) )" by (rule MMI_eqeq12d)
   from S3 have S4: "A = 
 if ( A \<in> \<complex> , A , \<one> ) \<longrightarrow> 
 ( ( ( A \<cdot> B ) = ( A \<cdot> C ) \<longleftrightarrow> B = C ) \<longleftrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> B ) = 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> C ) \<longleftrightarrow> 
 B = C ) )" by (rule MMI_bibi1d)
   have S5: "B = 
 if ( B \<in> \<complex> , B , \<one> ) \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> B ) = 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> if ( B \<in> \<complex> , B , \<one> ) )" by (rule MMI_opreq2)
   from S5 have S6: "B = 
 if ( B \<in> \<complex> , B , \<one> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> B ) = 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> C ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> if ( B \<in> \<complex> , B , \<one> ) ) = 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> C ) )" by (rule MMI_eqeq1d)
   have S7: "B = 
 if ( B \<in> \<complex> , B , \<one> ) \<longrightarrow> 
 ( B = C \<longleftrightarrow> if ( B \<in> \<complex> , B , \<one> ) = C )" by (rule MMI_eqeq1)
   from S6 S7 have S8: "B = 
 if ( B \<in> \<complex> , B , \<one> ) \<longrightarrow> 
 ( ( ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> B ) = ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> C ) \<longleftrightarrow> B = C ) \<longleftrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> if ( B \<in> \<complex> , B , \<one> ) ) = 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> C ) \<longleftrightarrow> 
 if ( B \<in> \<complex> , B , \<one> ) = C ) )" by (rule MMI_bibi12d)
   have S9: "C = 
 if ( C \<in> \<complex> , C , \<one> ) \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> C ) = 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> if ( C \<in> \<complex> , C , \<one> ) )" by (rule MMI_opreq2)
   from S9 have S10: "C = 
 if ( C \<in> \<complex> , C , \<one> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> if ( B \<in> \<complex> , B , \<one> ) ) = 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> C ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> if ( B \<in> \<complex> , B , \<one> ) ) = 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> if ( C \<in> \<complex> , C , \<one> ) ) )" by (rule MMI_eqeq2d)
   have S11: "C = 
 if ( C \<in> \<complex> , C , \<one> ) \<longrightarrow> 
 ( if ( B \<in> \<complex> , B , \<one> ) = 
 C \<longleftrightarrow> 
 if ( B \<in> \<complex> , B , \<one> ) = 
 if ( C \<in> \<complex> , C , \<one> ) )" by (rule MMI_eqeq2)
   from S10 S11 have S12: "C = 
 if ( C \<in> \<complex> , C , \<one> ) \<longrightarrow> 
 ( ( ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> if ( B \<in> \<complex> , B , \<one> ) ) = ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> C ) \<longleftrightarrow> if ( B \<in> \<complex> , B , \<one> ) = C ) \<longleftrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> if ( B \<in> \<complex> , B , \<one> ) ) = 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> if ( C \<in> \<complex> , C , \<one> ) ) \<longleftrightarrow> 
 if ( B \<in> \<complex> , B , \<one> ) = 
 if ( C \<in> \<complex> , C , \<one> ) ) )" by (rule MMI_bibi12d)
   have S13: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S13 have S14: "if ( A \<in> \<complex> , A , \<one> ) \<in> \<complex>" by (rule MMI_elimel)
   have S15: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S15 have S16: "if ( B \<in> \<complex> , B , \<one> ) \<in> \<complex>" by (rule MMI_elimel)
   have S17: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S17 have S18: "if ( C \<in> \<complex> , C , \<one> ) \<in> \<complex>" by (rule MMI_elimel)
   have S19: "A = 
 if ( A \<in> \<complex> , A , \<one> ) \<longrightarrow> 
 ( A \<noteq> \<zero> \<longleftrightarrow> if ( A \<in> \<complex> , A , \<one> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   have S20: "\<one> = 
 if ( A \<in> \<complex> , A , \<one> ) \<longrightarrow> 
 ( \<one> \<noteq> \<zero> \<longleftrightarrow> if ( A \<in> \<complex> , A , \<one> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   from A1 have S21: "A \<noteq> \<zero>".
   have S22: "\<one> \<noteq> \<zero>" by (rule MMI_ax1ne0)
   from S19 S20 S21 S22 have S23: "if ( A \<in> \<complex> , A , \<one> ) \<noteq> \<zero>" by (rule MMI_keephyp)
   from S14 S16 S18 S23 have S24: "( if ( A \<in> \<complex> , A , \<one> ) \<cdot> if ( B \<in> \<complex> , B , \<one> ) ) = 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdot> if ( C \<in> \<complex> , C , \<one> ) ) \<longleftrightarrow> 
 if ( B \<in> \<complex> , B , \<one> ) = 
 if ( C \<in> \<complex> , C , \<one> )" by (rule MMI_mulcan)
   from S4 S8 S12 S24 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> B ) = ( A \<cdot> C ) \<longleftrightarrow> B = C )" by (rule MMI_dedth3h)
qed

lemma (in MMIsar0) MMI_mulcant: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) = ( A \<cdot> C ) \<longleftrightarrow> B = C )"
proof -
   have S1: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( A \<in> \<complex> \<longleftrightarrow> if ( A \<noteq> \<zero> , A , \<one> ) \<in> \<complex> )" by (rule MMI_eleq1)
   have S2: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( B \<in> \<complex> \<longleftrightarrow> B \<in> \<complex> )" by (rule MMI_pm4_2i)
   have S3: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( C \<in> \<complex> \<longleftrightarrow> C \<in> \<complex> )" by (rule MMI_pm4_2i)
   from S1 S2 S3 have S4: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longleftrightarrow> 
 ( if ( A \<noteq> \<zero> , A , \<one> ) \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) )" by (rule MMI_3anbi123d)
   have S5: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( A \<cdot> B ) = 
 ( if ( A \<noteq> \<zero> , A , \<one> ) \<cdot> B )" by (rule MMI_opreq1)
   have S6: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( A \<cdot> C ) = 
 ( if ( A \<noteq> \<zero> , A , \<one> ) \<cdot> C )" by (rule MMI_opreq1)
   from S5 S6 have S7: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( ( A \<cdot> B ) = 
 ( A \<cdot> C ) \<longleftrightarrow> 
 ( if ( A \<noteq> \<zero> , A , \<one> ) \<cdot> B ) = 
 ( if ( A \<noteq> \<zero> , A , \<one> ) \<cdot> C ) )" by (rule MMI_eqeq12d)
   from S7 have S8: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( ( ( A \<cdot> B ) = ( A \<cdot> C ) \<longleftrightarrow> B = C ) \<longleftrightarrow> 
 ( ( if ( A \<noteq> \<zero> , A , \<one> ) \<cdot> B ) = 
 ( if ( A \<noteq> \<zero> , A , \<one> ) \<cdot> C ) \<longleftrightarrow> 
 B = C ) )" by (rule MMI_bibi1d)
   from S4 S8 have S9: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( ( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> ( ( A \<cdot> B ) = ( A \<cdot> C ) \<longleftrightarrow> B = C ) ) \<longleftrightarrow> 
 ( ( if ( A \<noteq> \<zero> , A , \<one> ) \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( if ( A \<noteq> \<zero> , A , \<one> ) \<cdot> B ) = 
 ( if ( A \<noteq> \<zero> , A , \<one> ) \<cdot> C ) \<longleftrightarrow> 
 B = C ) ) )" by (rule MMI_imbi12d)
   have S10: "if ( A \<noteq> \<zero> , A , \<one> ) \<noteq> \<zero>" by (rule MMI_elimne0)
   from S10 have S11: "( if ( A \<noteq> \<zero> , A , \<one> ) \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( if ( A \<noteq> \<zero> , A , \<one> ) \<cdot> B ) = 
 ( if ( A \<noteq> \<zero> , A , \<one> ) \<cdot> C ) \<longleftrightarrow> B = C )" by (rule MMI_mulcant2)
   from S9 S11 have S12: "A \<noteq> \<zero> \<longrightarrow> 
 ( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> B ) = ( A \<cdot> C ) \<longleftrightarrow> B = C ) )" by (rule MMI_dedth)
   from S12 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) = ( A \<cdot> C ) \<longleftrightarrow> B = C )" by (rule MMI_impcom)
qed

lemma (in MMIsar0) MMI_mulcan2t: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> C ) = ( B \<cdot> C ) \<longleftrightarrow> A = B )"
proof -
   have S1: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> C ) = ( C \<cdot> A )" by (rule MMI_axmulcom)
   from S1 have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> C ) = ( C \<cdot> A )" by (rule MMI_3adant2)
   have S3: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( B \<cdot> C ) = ( C \<cdot> B )" by (rule MMI_axmulcom)
   from S3 have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( B \<cdot> C ) = ( C \<cdot> B )" by (rule MMI_3adant1)
   from S2 S4 have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> C ) = 
 ( B \<cdot> C ) \<longleftrightarrow> ( C \<cdot> A ) = ( C \<cdot> B ) )" by (rule MMI_eqeq12d)
   from S5 have S6: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> C ) = 
 ( B \<cdot> C ) \<longleftrightarrow> ( C \<cdot> A ) = ( C \<cdot> B ) )" by (rule MMI_adantr)
   have S7: "( ( C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( C \<cdot> A ) = ( C \<cdot> B ) \<longleftrightarrow> A = B )" by (rule MMI_mulcant)
   from S7 have S8: "( C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( C \<noteq> \<zero> \<longrightarrow> 
 ( ( C \<cdot> A ) = ( C \<cdot> B ) \<longleftrightarrow> A = B ) )" by (rule MMI_ex)
   from S8 have S9: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( C \<noteq> \<zero> \<longrightarrow> 
 ( ( C \<cdot> A ) = ( C \<cdot> B ) \<longleftrightarrow> A = B ) )" by (rule MMI_3coml)
   from S9 have S10: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( C \<cdot> A ) = ( C \<cdot> B ) \<longleftrightarrow> A = B )" by (rule MMI_imp)
   from S6 S10 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> C ) = ( B \<cdot> C ) \<longleftrightarrow> A = B )" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_mul0or: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "( A \<cdot> B ) = \<zero> \<longleftrightarrow> ( A = \<zero> \<or> B = \<zero> )"
proof -
   have S1: "A \<noteq> \<zero> \<longleftrightarrow> \<not> ( A = \<zero> )" by (rule MMI_df_ne)
   from A1 have S2: "A \<in> \<complex>".
   from A2 have S3: "B \<in> \<complex>".
   have S4: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S2 S3 S4 have S5: "A \<in> \<complex> \<and> B \<in> \<complex> \<and> \<zero> \<in> \<complex>" by (rule MMI_3pm3_2i)
   have S6: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> \<zero> \<in> \<complex> ) \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) = ( A \<cdot> \<zero> ) \<longleftrightarrow> B = \<zero> )" by (rule MMI_mulcant)
   from S5 S6 have S7: "A \<noteq> \<zero> \<longrightarrow> 
 ( ( A \<cdot> B ) = ( A \<cdot> \<zero> ) \<longleftrightarrow> B = \<zero> )" by (rule MMI_mpan)
   from A1 have S8: "A \<in> \<complex>".
   from S8 have S9: "( A \<cdot> \<zero> ) = \<zero>" by (rule MMI_mul01)
   from S9 have S10: "( A \<cdot> B ) = ( A \<cdot> \<zero> ) \<longleftrightarrow> ( A \<cdot> B ) = \<zero>" by (rule MMI_eqeq2i)
   from S7 S10 have S11: "A \<noteq> \<zero> \<longrightarrow> ( ( A \<cdot> B ) = \<zero> \<longleftrightarrow> B = \<zero> )" by (rule MMI_syl5bbr)
   from S11 have S12: "A \<noteq> \<zero> \<longrightarrow> ( ( A \<cdot> B ) = \<zero> \<longrightarrow> B = \<zero> )" by (rule MMI_biimpd)
   from S1 S12 have S13: "\<not> ( A = 
 \<zero> ) \<longrightarrow> ( ( A \<cdot> B ) = \<zero> \<longrightarrow> B = \<zero> )" by (rule MMI_sylbir)
   from S13 have S14: "( A \<cdot> B ) = 
 \<zero> \<longrightarrow> ( \<not> ( A = \<zero> ) \<longrightarrow> B = \<zero> )" by (rule MMI_com12)
   from S14 have S15: "( A \<cdot> B ) = \<zero> \<longrightarrow> ( A = \<zero> \<or> B = \<zero> )" by (rule MMI_orrd)
   have S16: "A = \<zero> \<longrightarrow> ( A \<cdot> B ) = ( \<zero> \<cdot> B )" by (rule MMI_opreq1)
   from A2 have S17: "B \<in> \<complex>".
   from S17 have S18: "( \<zero> \<cdot> B ) = \<zero>" by (rule MMI_mul02)
   from S16 S18 have S19: "A = \<zero> \<longrightarrow> ( A \<cdot> B ) = \<zero>" by (rule MMI_syl6eq)
   have S20: "B = \<zero> \<longrightarrow> ( A \<cdot> B ) = ( A \<cdot> \<zero> )" by (rule MMI_opreq2)
   from S9 have S21: "( A \<cdot> \<zero> ) = \<zero>" .
   from S20 S21 have S22: "B = \<zero> \<longrightarrow> ( A \<cdot> B ) = \<zero>" by (rule MMI_syl6eq)
   from S19 S22 have S23: "( A = \<zero> \<or> B = \<zero> ) \<longrightarrow> ( A \<cdot> B ) = \<zero>" by (rule MMI_jaoi)
   from S15 S23 show "( A \<cdot> B ) = \<zero> \<longleftrightarrow> ( A = \<zero> \<or> B = \<zero> )" by (rule MMI_impbi)
qed

lemma (in MMIsar0) MMI_msq0: assumes A1: "A \<in> \<complex>"   
   shows "( A \<cdot> A ) = \<zero> \<longleftrightarrow> A = \<zero>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A1 have S2: "A \<in> \<complex>".
   from S1 S2 have S3: "( A \<cdot> A ) = \<zero> \<longleftrightarrow> ( A = \<zero> \<or> A = \<zero> )" by (rule MMI_mul0or)
   have S4: "( A = \<zero> \<or> A = \<zero> ) \<longleftrightarrow> A = \<zero>" by (rule MMI_oridm)
   from S3 S4 show "( A \<cdot> A ) = \<zero> \<longleftrightarrow> A = \<zero>" by (rule MMI_bitr)
qed

lemma (in MMIsar0) MMI_mul0ort: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> B ) = \<zero> \<longleftrightarrow> ( A = \<zero> \<or> B = \<zero> ) )"
proof -
   have S1: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<cdot> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B )" by (rule MMI_opreq1)
   from S1 have S2: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) = 
 \<zero> \<longleftrightarrow> ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) = \<zero> )" by (rule MMI_eqeq1d)
   have S3: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A = \<zero> \<longleftrightarrow> if ( A \<in> \<complex> , A , \<zero> ) = \<zero> )" by (rule MMI_eqeq1)
   from S3 have S4: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( A = \<zero> \<or> B = \<zero> ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) = \<zero> \<or> B = \<zero> ) )" by (rule MMI_orbi1d)
   from S2 S4 have S5: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( ( A \<cdot> B ) = \<zero> \<longleftrightarrow> ( A = \<zero> \<or> B = \<zero> ) ) \<longleftrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) = 
 \<zero> \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) = 
 \<zero> \<or> B = \<zero> ) ) )" by (rule MMI_bibi12d)
   have S6: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_opreq2)
   from S6 have S7: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) = 
 \<zero> \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) ) = 
 \<zero> )" by (rule MMI_eqeq1d)
   have S8: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( B = \<zero> \<longleftrightarrow> if ( B \<in> \<complex> , B , \<zero> ) = \<zero> )" by (rule MMI_eqeq1)
   from S8 have S9: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) = \<zero> \<or> B = \<zero> ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) = 
 \<zero> \<or> if ( B \<in> \<complex> , B , \<zero> ) = \<zero> ) )" by (rule MMI_orbi2d)
   from S7 S9 have S10: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) = \<zero> \<longleftrightarrow> ( if ( A \<in> \<complex> , A , \<zero> ) = \<zero> \<or> B = \<zero> ) ) \<longleftrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) ) = 
 \<zero> \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) = 
 \<zero> \<or> if ( B \<in> \<complex> , B , \<zero> ) = \<zero> ) ) )" by (rule MMI_bibi12d)
   have S11: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S11 have S12: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S13: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S13 have S14: "if ( B \<in> \<complex> , B , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S12 S14 have S15: "( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) ) = 
 \<zero> \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) = 
 \<zero> \<or> if ( B \<in> \<complex> , B , \<zero> ) = \<zero> )" by (rule MMI_mul0or)
   from S5 S10 S15 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> B ) = \<zero> \<longleftrightarrow> ( A = \<zero> \<or> B = \<zero> ) )" by (rule MMI_dedth2h)
qed

(********* 151-153**************************)

lemma (in MMIsar0) MMI_muln0bt: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) \<longleftrightarrow> ( A \<cdot> B ) \<noteq> \<zero> )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> B ) = \<zero> \<longleftrightarrow> ( A = \<zero> \<or> B = \<zero> ) )" by (rule MMI_mul0ort)
   from S1 have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( \<not> ( ( A \<cdot> B ) = \<zero> ) \<longleftrightarrow> 
 \<not> ( ( A = \<zero> \<or> B = \<zero> ) ) )" by (rule MMI_negbid)
   have S3: "\<not> ( ( A = \<zero> \<or> B = \<zero> ) ) \<longleftrightarrow> 
 ( \<not> ( A = \<zero> ) \<and> \<not> ( B = \<zero> ) )" by (rule MMI_ioran)
   from S2 S3 have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( \<not> ( A = \<zero> ) \<and> \<not> ( B = \<zero> ) ) \<longleftrightarrow> 
 \<not> ( ( A \<cdot> B ) = \<zero> ) )" by (rule MMI_syl6rbb)
   have S5: "A \<noteq> \<zero> \<longleftrightarrow> \<not> ( A = \<zero> )" by (rule MMI_df_ne)
   have S6: "B \<noteq> \<zero> \<longleftrightarrow> \<not> ( B = \<zero> )" by (rule MMI_df_ne)
   from S5 S6 have S7: "( A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) \<longleftrightarrow> 
 ( \<not> ( A = \<zero> ) \<and> \<not> ( B = \<zero> ) )" by (rule MMI_anbi12i)
   have S8: "( A \<cdot> B ) \<noteq> \<zero> \<longleftrightarrow> \<not> ( ( A \<cdot> B ) = \<zero> )" by (rule MMI_df_ne)
   from S4 S7 S8 show "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) \<longleftrightarrow> ( A \<cdot> B ) \<noteq> \<zero> )" by (rule MMI_3bitr4g)
qed

lemma (in MMIsar0) MMI_muln0: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "A \<noteq> \<zero>" and
    A4: "B \<noteq> \<zero>"   
   shows "( A \<cdot> B ) \<noteq> \<zero>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "A \<noteq> \<zero>".
   from A4 have S4: "B \<noteq> \<zero>".
   from S3 S4 have S5: "A \<noteq> \<zero> \<and> B \<noteq> \<zero>" by (rule MMI_pm3_2i)
   have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<noteq> \<zero> \<and> B \<noteq> \<zero> ) \<longleftrightarrow> ( A \<cdot> B ) \<noteq> \<zero> )" by (rule MMI_muln0bt)
   from S5 S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cdot> B ) \<noteq> \<zero>" by (rule MMI_mpbii)
   from S1 S2 S7 show "( A \<cdot> B ) \<noteq> \<zero>" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_receu: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "A \<noteq> \<zero>"   
   shows "\<exists>! x . x \<in> \<complex> \<and> ( A \<cdot> x ) = B"
proof -
  { fix x y
    have S1: "x = y \<longrightarrow> ( A \<cdot> x ) = ( A \<cdot> y )" by (rule MMI_opreq2)
    from S1 have S2: "x = y \<longrightarrow> ( ( A \<cdot> x ) = B \<longleftrightarrow> ( A \<cdot> y ) = B )" 
      by (rule MMI_eqeq1d)
  } then have S2: "\<forall> x y. x = y \<longrightarrow> ( ( A \<cdot> x ) = B \<longleftrightarrow> ( A \<cdot> y ) = B )"
    by simp
    from S2 have S3: 
      "( \<exists>! x . x \<in> \<complex> \<and> ( A \<cdot> x ) =  B ) \<longleftrightarrow> 
      ( ( \<exists> x \<in> \<complex> . ( A \<cdot> x ) = B ) \<and> 
      ( \<forall> x \<in> \<complex> . \<forall> y \<in> \<complex> . ( ( ( A \<cdot> x ) = B \<and> ( A \<cdot> y ) = B ) \<longrightarrow> x = y ) ) )" 
      by (rule MMI_reu4)
    from A1 have S4: "A \<in> \<complex>".
    from A3 have S5: "A \<noteq> \<zero>".
   from S4 S5 have S6: "\<exists> y \<in> \<complex> . ( A \<cdot> y ) = \<one>" by (rule MMI_recex)
   from A2 have S7: "B \<in> \<complex>".
   { fix y
     have S8: "( y \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( y \<cdot> B ) \<in> \<complex>" by (rule MMI_axmulcl)
     from S7 S8 have S9: "y \<in> \<complex> \<longrightarrow> ( y \<cdot> B ) \<in> \<complex>" by (rule MMI_mpan2)
     have S10: "( y \<cdot> B ) \<in> \<complex> \<longleftrightarrow> 
       ( \<exists> x \<in> \<complex> . x = ( y \<cdot> B ) )" by (rule MMI_risset)
     from S9 S10 have S11: "y \<in> \<complex> \<longrightarrow> ( \<exists> x \<in> \<complex> . x = ( y \<cdot> B ) )" 
       by (rule MMI_sylib)
     { fix x
       have S12: "x =  ( y \<cdot> B ) \<longrightarrow> 
	 ( A \<cdot> x ) = ( A \<cdot> ( y \<cdot> B ) )" by (rule MMI_opreq2)
       from A1 have S13: "A \<in> \<complex>".
       from A2 have S14: "B \<in> \<complex>".
       have S15: "( A \<in> \<complex> \<and> y \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
	 ( ( A \<cdot> y ) \<cdot> B ) = ( A \<cdot> ( y \<cdot> B ) )" by (rule MMI_axmulass)
       from S13 S14 S15 have S16: "y \<in> \<complex> \<longrightarrow> 
	 ( ( A \<cdot> y ) \<cdot> B ) = ( A \<cdot> ( y \<cdot> B ) )" by (rule MMI_mp3an13)
       from S16 have S17: "y \<in> \<complex> \<longrightarrow> 
	 ( A \<cdot> ( y \<cdot> B ) ) = ( ( A \<cdot> y ) \<cdot> B )" by (rule MMI_eqcomd)
       from S12 S17 have S18: "( y \<in> \<complex> \<and> x = 
	 ( y \<cdot> B ) ) \<longrightarrow> 
	 ( A \<cdot> x ) = ( ( A \<cdot> y ) \<cdot> B )" by (rule MMI_sylan9eqr)
       have S19: "( A \<cdot> y ) = 
	 \<one> \<longrightarrow> ( ( A \<cdot> y ) \<cdot> B ) = ( \<one> \<cdot> B )" by (rule MMI_opreq1)
       from A2 have S20: "B \<in> \<complex>".
       from S20 have S21: "( \<one> \<cdot> B ) = B" by (rule MMI_mulid2)
       from S19 S21 have S22: "( A \<cdot> y ) = \<one> \<longrightarrow> ( ( A \<cdot> y ) \<cdot> B ) = B" 
	 by (rule MMI_syl6eq)
       from S18 S22 have S23: 
	 "( ( A \<cdot> y ) = \<one> \<and> ( y \<in> \<complex> \<and> x = 
	 ( y \<cdot> B ) ) ) \<longrightarrow> ( A \<cdot> x ) = B" by (rule MMI_sylan9eqr)
       from S23 have S24: 
	 "( A \<cdot> y ) = \<one> \<longrightarrow>  ( y \<in> \<complex> \<longrightarrow> 
	 ( x = ( y \<cdot> B ) \<longrightarrow> ( A \<cdot> x ) = B ) )" by (rule MMI_exp32)
       from S24 have S25: "( y \<in> \<complex> \<and> ( A \<cdot> y ) = 
	 \<one> ) \<longrightarrow> 
	 ( x = ( y \<cdot> B ) \<longrightarrow> ( A \<cdot> x ) = B )" by (rule MMI_impcom)
       from S25 have
	 "( y \<in> \<complex> \<and> ( A \<cdot> y ) = \<one> ) \<longrightarrow> ( x \<in> \<complex> \<longrightarrow> 
	 ( x = ( y \<cdot> B ) \<longrightarrow> ( A \<cdot> x ) = B ) )" by (rule MMI_a1d)
       } then have S26: 
	 "\<forall> x . ( y \<in> \<complex> \<and> ( A \<cdot> y ) = \<one> ) \<longrightarrow> ( x \<in> \<complex> \<longrightarrow> 
	 ( x = ( y \<cdot> B ) \<longrightarrow> ( A \<cdot> x ) = B ) )" by simp
       from S26 have S27: 
	 "( y \<in> \<complex> \<and> ( A \<cdot> y ) = \<one> ) \<longrightarrow> 
	 ( \<forall> x \<in> \<complex> . ( x = ( y \<cdot> B ) \<longrightarrow> ( A \<cdot> x ) = B ) )" by (rule MMI_r19_21aiv)
       from S27 have S28: "y \<in> \<complex> \<longrightarrow> 
	 ( ( A \<cdot> y ) =	\<one> \<longrightarrow> 
	 ( \<forall> x \<in> \<complex> . ( x = ( y \<cdot> B ) \<longrightarrow> ( A \<cdot> x ) = B ) ) )" by (rule MMI_ex)
       have S29: "( \<forall> x \<in> \<complex> . ( x = ( y \<cdot> B ) \<longrightarrow> ( A \<cdot> x ) = B ) ) \<longrightarrow> 
	 ( ( \<exists> x \<in> \<complex> . x = ( y \<cdot> B ) ) \<longrightarrow> 
	 ( \<exists> x \<in> \<complex> . ( A \<cdot> x ) = B ) )" by (rule MMI_r19_22)
       from S28 S29 have S30: 
	 "y \<in> \<complex> \<longrightarrow> ( ( A \<cdot> y ) =  \<one> \<longrightarrow> 
	 ( ( \<exists> x \<in> \<complex> . x = ( y \<cdot> B ) ) \<longrightarrow> 
	 ( \<exists> x \<in> \<complex> . ( A \<cdot> x ) = B ) ) )" by (rule MMI_syl6)
       from S11 S30 have 
	 "y \<in> \<complex> \<longrightarrow>  ( ( A \<cdot> y ) =  \<one> \<longrightarrow> ( \<exists> x \<in> \<complex> . ( A \<cdot> x ) = B ) )" 
	 by (rule MMI_mpid)
       } then have S31: 
	   "\<forall> y . y \<in> \<complex> \<longrightarrow>  ( ( A \<cdot> y ) =  \<one> \<longrightarrow> ( \<exists> x \<in> \<complex> . ( A \<cdot> x ) = B ) )" 
	 by simp
       from S31 have S32: "( \<exists> y \<in> \<complex> . ( A \<cdot> y ) = 
	 \<one> ) \<longrightarrow> ( \<exists> x \<in> \<complex> . ( A \<cdot> x ) = B )" by (rule MMI_r19_23aiv)
       from S6 S32 have S33: "\<exists> x \<in> \<complex> . ( A \<cdot> x ) = B" by (rule MMI_ax_mp)
       from A1 have S34: "A \<in> \<complex>".
       from A3 have S35: "A \<noteq> \<zero>".
       { fix x y
	 from S35 have S36: "( A \<in> \<complex> \<and> x \<in> \<complex> \<and> y \<in> \<complex> ) \<longrightarrow> 
	   ( ( A \<cdot> x ) = ( A \<cdot> y ) \<longleftrightarrow> x = y )" by (rule MMI_mulcant2)
	 have S37: 
	   "( ( A \<cdot> x ) =   B \<and> ( A \<cdot> y ) = 
	   B ) \<longrightarrow> ( A \<cdot> x ) = ( A \<cdot> y )" by (rule MMI_eqtr3t)
	 from S36 S37 have S38: "( A \<in> \<complex> \<and> x \<in> \<complex> \<and> y \<in> \<complex> ) \<longrightarrow> 
	   ( ( ( A \<cdot> x ) = B \<and> ( A \<cdot> y ) = B ) \<longrightarrow> 
	   x = y )" by (rule MMI_syl5bi)
	 from S34 S38 have "( x \<in> \<complex> \<and> y \<in> \<complex> ) \<longrightarrow> 
	   ( ( ( A \<cdot> x ) = B \<and> ( A \<cdot> y ) = B ) \<longrightarrow> 
	   x = y )" by (rule MMI_mp3an1)
       } then have  S39: "\<forall> x y. ( x \<in> \<complex> \<and> y \<in> \<complex> ) \<longrightarrow> 
	   ( ( ( A \<cdot> x ) = B \<and> ( A \<cdot> y ) = B ) \<longrightarrow> 
	   x = y )" by auto
       from S39 have S40: 
	 "\<forall> x \<in> \<complex> . \<forall> y \<in> \<complex> . ( ( ( A \<cdot> x ) = B \<and> ( A \<cdot> y ) = B ) \<longrightarrow> 
	 x = y )" by (rule MMI_rgen2)
       from S3 S33 S40 show "\<exists>! x . x \<in> \<complex> \<and> ( A \<cdot> x ) = B" by (rule MMI_mpbir2an)
qed

(** this is proven by definition rather than importing the Metamath proof **)

lemma (in MMIsar0) MMI_divval: assumes "A \<in> \<complex>"  "B \<in> \<complex>" "B \<noteq> \<zero>"
  shows "A \<cdiv> B =  \<Union> { x \<in> \<complex> . B \<cdot> x = A }"
  using cdiv_def by simp

(****** 154-160***********************************)


lemma (in MMIsar0) MMI_divmul: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>" and
    A4: "B \<noteq> \<zero>"   
   shows "( A \<cdiv> B ) = C \<longleftrightarrow> ( B \<cdot> C ) = A"
proof -
   from A3 have S1: "C \<in> \<complex>".
   { fix x
     have S2: "x = 
       C \<longrightarrow> ( ( A \<cdiv> B ) = x \<longleftrightarrow> ( A \<cdiv> B ) = C )" by (rule MMI_eqeq2)
     have S3: "x = C \<longrightarrow> ( B \<cdot> x ) = ( B \<cdot> C )" by (rule MMI_opreq2)
     from S3 have S4: "x = 
       C \<longrightarrow> ( ( B \<cdot> x ) = A \<longleftrightarrow> ( B \<cdot> C ) = A )" by (rule MMI_eqeq1d)
     from S2 S4 have  
       "x = C \<longrightarrow> 
       ( ( ( A \<cdiv> B ) = x \<longleftrightarrow> ( B \<cdot> x ) = A ) \<longleftrightarrow> 
       ( ( A \<cdiv> B ) = C \<longleftrightarrow> ( B \<cdot> C ) = A ) )" by (rule MMI_bibi12d)
   } then have S5: "\<forall>x. x = C \<longrightarrow> 
       ( ( ( A \<cdiv> B ) = x \<longleftrightarrow> ( B \<cdot> x ) = A ) \<longleftrightarrow> 
       ( ( A \<cdiv> B ) = C \<longleftrightarrow> ( B \<cdot> C ) = A ) )"
     by simp
   from A2 have S6: "B \<in> \<complex>".
   from A1 have S7: "A \<in> \<complex>".
   from A4 have S8: "B \<noteq> \<zero>".
   from S6 S7 S8 have S9: "\<exists>! x . x \<in> \<complex> \<and> ( B \<cdot> x ) = A" by (rule MMI_receu)
   { fix x
     have S10: "( x \<in> \<complex> \<and> ( \<exists>! x . x \<in> \<complex> \<and> ( B \<cdot> x ) = A ) ) \<longrightarrow> 
       ( ( B \<cdot> x ) = 
       A \<longleftrightarrow> \<Union> { x \<in> \<complex> . ( B \<cdot> x ) = A } = x )" by (rule MMI_reuuni1)
     from S9 S10 have  
       "x \<in> \<complex> \<longrightarrow> ( ( B \<cdot> x ) =  A \<longleftrightarrow> \<Union> { x \<in> \<complex> . ( B \<cdot> x ) = A } = x )" 
       by (rule MMI_mpan2)
   } then have S11: 
       "\<forall> x. x \<in> \<complex> \<longrightarrow> ( ( B \<cdot> x ) =  A \<longleftrightarrow> \<Union> { x \<in> \<complex> . ( B \<cdot> x ) = A } = x )" 
     by blast
   from A1 have S12: "A \<in> \<complex>".
   from A2 have S13: "B \<in> \<complex>".
   from A4 have S14: "B \<noteq> \<zero>".
   from S12 S13 S14 have S15: "( A \<cdiv> B ) = 
     \<Union> { x \<in> \<complex> . ( B \<cdot> x ) = A }" by (rule MMI_divval)
   from S15 have S16: "\<forall> x. ( A \<cdiv> B ) = 
     x \<longleftrightarrow> \<Union> { x \<in> \<complex> . ( B \<cdot> x ) = A } = x" by simp(*rule MMI_eqeq1i*)
   from S11 S16 have S17: "\<forall> x. x \<in> \<complex> \<longrightarrow> 
     ( ( A \<cdiv> B ) = x \<longleftrightarrow> ( B \<cdot> x ) = A )" by (rule MMI_syl6rbbr)
   from S5 S17 have S18: "C \<in> \<complex> \<longrightarrow> 
     ( ( A \<cdiv> B ) = C \<longleftrightarrow> ( B \<cdot> C ) = A )" by (rule MMI_vtoclga)
   from S1 S18 show "( A \<cdiv> B ) = C \<longleftrightarrow> ( B \<cdot> C ) = A" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_divmulz: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "B \<noteq> \<zero> \<longrightarrow> 
 ( ( A \<cdiv> B ) = C \<longleftrightarrow> ( B \<cdot> C ) = A )"
proof -
   have S1: "B = 
 if ( B \<noteq> \<zero> , B , \<one> ) \<longrightarrow> 
 ( A \<cdiv> B ) = 
 ( A \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) )" by (rule MMI_opreq2)
   from S1 have S2: "B = 
 if ( B \<noteq> \<zero> , B , \<one> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) = 
 C \<longleftrightarrow> ( A \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) ) = C )" by (rule MMI_eqeq1d)
   have S3: "B = 
 if ( B \<noteq> \<zero> , B , \<one> ) \<longrightarrow> 
 ( B \<cdot> C ) = 
 ( if ( B \<noteq> \<zero> , B , \<one> ) \<cdot> C )" by (rule MMI_opreq1)
   from S3 have S4: "B = 
 if ( B \<noteq> \<zero> , B , \<one> ) \<longrightarrow> 
 ( ( B \<cdot> C ) = 
 A \<longleftrightarrow> ( if ( B \<noteq> \<zero> , B , \<one> ) \<cdot> C ) = A )" by (rule MMI_eqeq1d)
   from S2 S4 have S5: "B = 
 if ( B \<noteq> \<zero> , B , \<one> ) \<longrightarrow> 
 ( ( ( A \<cdiv> B ) = C \<longleftrightarrow> ( B \<cdot> C ) = A ) \<longleftrightarrow> 
 ( ( A \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) ) = 
 C \<longleftrightarrow> 
 ( if ( B \<noteq> \<zero> , B , \<one> ) \<cdot> C ) = A ) )" by (rule MMI_bibi12d)
   from A1 have S6: "A \<in> \<complex>".
   from A2 have S7: "B \<in> \<complex>".
   have S8: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S7 S8 have S9: "if ( B \<noteq> \<zero> , B , \<one> ) \<in> \<complex>" by (rule MMI_keepel)
   from A3 have S10: "C \<in> \<complex>".
   have S11: "if ( B \<noteq> \<zero> , B , \<one> ) \<noteq> \<zero>" by (rule MMI_elimne0)
   from S6 S9 S10 S11 have S12: "( A \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) ) = 
 C \<longleftrightarrow> ( if ( B \<noteq> \<zero> , B , \<one> ) \<cdot> C ) = A" by (rule MMI_divmul)
   from S5 S12 show "B \<noteq> \<zero> \<longrightarrow> 
 ( ( A \<cdiv> B ) = C \<longleftrightarrow> ( B \<cdot> C ) = A )" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_divmult: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) = C \<longleftrightarrow> ( B \<cdot> C ) = A )"
proof -
   have S1: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B )" by (rule MMI_opreq1)
   from S1 have S2: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) = 
 C \<longleftrightarrow> ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B ) = C )" by (rule MMI_eqeq1d)
   have S3: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( B \<cdot> C ) = 
 A \<longleftrightarrow> ( B \<cdot> C ) = if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_eqeq2)
   from S2 S3 have S4: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( ( A \<cdiv> B ) = C \<longleftrightarrow> ( B \<cdot> C ) = A ) \<longleftrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B ) = 
 C \<longleftrightarrow> 
 ( B \<cdot> C ) = if ( A \<in> \<complex> , A , \<zero> ) ) )" by (rule MMI_bibi12d)
   from S4 have S5: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<longrightarrow> ( ( A \<cdiv> B ) = C \<longleftrightarrow> ( B \<cdot> C ) = A ) ) \<longleftrightarrow> 
 ( B \<noteq> \<zero> \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B ) = 
 C \<longleftrightarrow> 
 ( B \<cdot> C ) = if ( A \<in> \<complex> , A , \<zero> ) ) ) )" by (rule MMI_imbi2d)
   have S6: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( B \<noteq> \<zero> \<longleftrightarrow> if ( B \<in> \<complex> , B , \<zero> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   have S7: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_opreq2)
   from S7 have S8: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B ) = 
 C \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) = 
 C )" by (rule MMI_eqeq1d)
   have S9: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( B \<cdot> C ) = 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<cdot> C )" by (rule MMI_opreq1)
   from S9 have S10: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( B \<cdot> C ) = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longleftrightarrow> 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<cdot> C ) = 
 if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_eqeq1d)
   from S8 S10 have S11: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B ) = C \<longleftrightarrow> ( B \<cdot> C ) = if ( A \<in> \<complex> , A , \<zero> ) ) \<longleftrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) = 
 C \<longleftrightarrow> 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<cdot> C ) = 
 if ( A \<in> \<complex> , A , \<zero> ) ) )" by (rule MMI_bibi12d)
   from S6 S11 have S12: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<longrightarrow> ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B ) = C \<longleftrightarrow> ( B \<cdot> C ) = if ( A \<in> \<complex> , A , \<zero> ) ) ) \<longleftrightarrow> 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) = 
 C \<longleftrightarrow> 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<cdot> C ) = 
 if ( A \<in> \<complex> , A , \<zero> ) ) ) )" by (rule MMI_imbi12d)
   have S13: "C = 
 if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) = 
 C \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) = 
 if ( C \<in> \<complex> , C , \<zero> ) )" by (rule MMI_eqeq2)
   have S14: "C = 
 if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<cdot> C ) = 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<cdot> if ( C \<in> \<complex> , C , \<zero> ) )" by (rule MMI_opreq2)
   from S14 have S15: "C = 
 if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
 ( ( if ( B \<in> \<complex> , B , \<zero> ) \<cdot> C ) = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longleftrightarrow> 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<cdot> if ( C \<in> \<complex> , C , \<zero> ) ) = 
 if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_eqeq1d)
   from S13 S15 have S16: "C = 
 if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
 ( ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) = C \<longleftrightarrow> ( if ( B \<in> \<complex> , B , \<zero> ) \<cdot> C ) = if ( A \<in> \<complex> , A , \<zero> ) ) \<longleftrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) = 
 if ( C \<in> \<complex> , C , \<zero> ) \<longleftrightarrow> 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<cdot> if ( C \<in> \<complex> , C , \<zero> ) ) = 
 if ( A \<in> \<complex> , A , \<zero> ) ) )" by (rule MMI_bibi12d)
   from S16 have S17: "C = 
 if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
 ( ( if ( B \<in> \<complex> , B , \<zero> ) \<noteq> \<zero> \<longrightarrow> ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) = C \<longleftrightarrow> ( if ( B \<in> \<complex> , B , \<zero> ) \<cdot> C ) = if ( A \<in> \<complex> , A , \<zero> ) ) ) \<longleftrightarrow> 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) = 
 if ( C \<in> \<complex> , C , \<zero> ) \<longleftrightarrow> 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<cdot> if ( C \<in> \<complex> , C , \<zero> ) ) = 
 if ( A \<in> \<complex> , A , \<zero> ) ) ) )" by (rule MMI_imbi2d)
   have S18: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S18 have S19: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S20: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S20 have S21: "if ( B \<in> \<complex> , B , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S22: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S22 have S23: "if ( C \<in> \<complex> , C , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S19 S21 S23 have S24: "if ( B \<in> \<complex> , B , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) = 
 if ( C \<in> \<complex> , C , \<zero> ) \<longleftrightarrow> 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<cdot> if ( C \<in> \<complex> , C , \<zero> ) ) = 
 if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_divmulz)
   from S5 S12 S17 S24 have S25: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( B \<noteq> \<zero> \<longrightarrow> 
 ( ( A \<cdiv> B ) = C \<longleftrightarrow> ( B \<cdot> C ) = A ) )" by (rule MMI_dedth3h)
   from S25 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) = C \<longleftrightarrow> ( B \<cdot> C ) = A )" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_divmul2t: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) = C \<longleftrightarrow> A = ( B \<cdot> C ) )"
proof -
   have S1: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) = C \<longleftrightarrow> ( B \<cdot> C ) = A )" by (rule MMI_divmult)
   have S2: "( B \<cdot> C ) = A \<longleftrightarrow> A = ( B \<cdot> C )" by (rule MMI_eqcom)
   from S1 S2 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) = C \<longleftrightarrow> A = ( B \<cdot> C ) )" by (rule MMI_syl6bb)
qed

lemma (in MMIsar0) MMI_divmul3t: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) = C \<longleftrightarrow> A = ( C \<cdot> B ) )"
proof -
   have S1: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) = C \<longleftrightarrow> A = ( B \<cdot> C ) )" by (rule MMI_divmul2t)
   have S2: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( B \<cdot> C ) = ( C \<cdot> B )" by (rule MMI_axmulcom)
   from S2 have S3: "( B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A = ( B \<cdot> C ) \<longleftrightarrow> A = ( C \<cdot> B ) )" by (rule MMI_eqeq2d)
   from S3 have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A = ( B \<cdot> C ) \<longleftrightarrow> A = ( C \<cdot> B ) )" by (rule MMI_3adant1)
   from S4 have S5: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A = ( B \<cdot> C ) \<longleftrightarrow> A = ( C \<cdot> B ) )" by (rule MMI_adantr)
   from S1 S5 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) = C \<longleftrightarrow> A = ( C \<cdot> B ) )" by (rule MMI_bitrd)
qed

lemma (in MMIsar0) MMI_divcl: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "B \<noteq> \<zero>"   
   shows "( A \<cdiv> B ) \<in> \<complex>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "B \<noteq> \<zero>".
   from S1 S2 S3 have S4: "( A \<cdiv> B ) = 
 \<Union> { x \<in> \<complex> . ( B \<cdot> x ) = A }" by (rule MMI_divval)
   from A2 have S5: "B \<in> \<complex>".
   from A1 have S6: "A \<in> \<complex>".
   from A3 have S7: "B \<noteq> \<zero>".
   from S5 S6 S7 have S8: "\<exists>! x . x \<in> \<complex> \<and> ( B \<cdot> x ) = A" by (rule MMI_receu)
   have S9: "( \<exists>! x . x \<in> \<complex> \<and> ( B \<cdot> x ) = 
 A ) \<longrightarrow> \<Union> { x \<in> \<complex> . ( B \<cdot> x ) = A } \<in> \<complex>" by (rule MMI_reucl)
   from S8 S9 have S10: "\<Union> { x \<in> \<complex> . ( B \<cdot> x ) = A } \<in> \<complex>" by (rule MMI_ax_mp)
   from S4 S10 show "( A \<cdiv> B ) \<in> \<complex>" by (rule MMI_eqeltr)
qed

lemma (in MMIsar0) MMI_divclz: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "B \<noteq> \<zero> \<longrightarrow> ( A \<cdiv> B ) \<in> \<complex>"
proof -
   have S1: "B = 
 if ( B \<noteq> \<zero> , B , \<one> ) \<longrightarrow> 
 ( A \<cdiv> B ) = 
 ( A \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) )" by (rule MMI_opreq2)
   from S1 have S2: "B = 
 if ( B \<noteq> \<zero> , B , \<one> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<in> \<complex> \<longleftrightarrow> 
 ( A \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) ) \<in> \<complex> )" by (rule MMI_eleq1d)
   from A1 have S3: "A \<in> \<complex>".
   from A2 have S4: "B \<in> \<complex>".
   have S5: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S4 S5 have S6: "if ( B \<noteq> \<zero> , B , \<one> ) \<in> \<complex>" by (rule MMI_keepel)
   have S7: "if ( B \<noteq> \<zero> , B , \<one> ) \<noteq> \<zero>" by (rule MMI_elimne0)
   from S3 S6 S7 have S8: "( A \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) ) \<in> \<complex>" by (rule MMI_divcl)
   from S2 S8 show "B \<noteq> \<zero> \<longrightarrow> ( A \<cdiv> B ) \<in> \<complex>" by (rule MMI_dedth)
qed

(************** 161-170 *****************************)


lemma (in MMIsar0) MMI_divclt: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) \<in> \<complex>"
proof -
   have S1: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B )" by (rule MMI_opreq1)
   from S1 have S2: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<in> \<complex> \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B ) \<in> \<complex> )" by (rule MMI_eleq1d)
   from S2 have S3: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<longrightarrow> ( A \<cdiv> B ) \<in> \<complex> ) \<longleftrightarrow> 
 ( B \<noteq> \<zero> \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B ) \<in> \<complex> ) )" by (rule MMI_imbi2d)
   have S4: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( B \<noteq> \<zero> \<longleftrightarrow> if ( B \<in> \<complex> , B , \<zero> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   have S5: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_opreq2)
   from S5 have S6: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B ) \<in> \<complex> \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) \<in> \<complex> )" by (rule MMI_eleq1d)
   from S4 S6 have S7: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<longrightarrow> ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B ) \<in> \<complex> ) \<longleftrightarrow> 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) \<in> \<complex> ) )" by (rule MMI_imbi12d)
   have S8: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S8 have S9: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S10: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S10 have S11: "if ( B \<in> \<complex> , B , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S9 S11 have S12: "if ( B \<in> \<complex> , B , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) \<in> \<complex>" by (rule MMI_divclz)
   from S3 S7 S12 have S13: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( B \<noteq> \<zero> \<longrightarrow> ( A \<cdiv> B ) \<in> \<complex> )" by (rule MMI_dedth2h)
   from S13 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) \<in> \<complex>" by (rule MMI_3impia)
qed

lemma (in MMIsar0) MMI_reccl: assumes A1: "A \<in> \<complex>" and
    A2: "A \<noteq> \<zero>"   
   shows "( \<one> \<cdiv> A ) \<in> \<complex>"
proof -
   have S1: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from A1 have S2: "A \<in> \<complex>".
   from A2 have S3: "A \<noteq> \<zero>".
   from S1 S2 S3 show "( \<one> \<cdiv> A ) \<in> \<complex>" by (rule MMI_divcl)
qed

lemma (in MMIsar0) MMI_recclz: assumes A1: "A \<in> \<complex>"   
   shows "A \<noteq> \<zero> \<longrightarrow> ( \<one> \<cdiv> A ) \<in> \<complex>"
proof -
   have S1: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from A1 have S2: "A \<in> \<complex>".
   from S1 S2 show "A \<noteq> \<zero> \<longrightarrow> ( \<one> \<cdiv> A ) \<in> \<complex>" by (rule MMI_divclz)
qed

lemma (in MMIsar0) MMI_recclt: 
   shows "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> ( \<one> \<cdiv> A ) \<in> \<complex>"
proof -
   have S1: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S2: "( \<one> \<in> \<complex> \<and> A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( \<one> \<cdiv> A ) \<in> \<complex>" by (rule MMI_divclt)
   from S1 S2 show "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> ( \<one> \<cdiv> A ) \<in> \<complex>" by (rule MMI_mp3an1)
qed

lemma (in MMIsar0) MMI_divcan2: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "A \<noteq> \<zero>"   
   shows "( A \<cdot> ( B \<cdiv> A ) ) = B"
proof -
   have S1: "( B \<cdiv> A ) = ( B \<cdiv> A )" by (rule MMI_eqid)
   from A2 have S2: "B \<in> \<complex>".
   from A1 have S3: "A \<in> \<complex>".
   from A2 have S4: "B \<in> \<complex>".
   from A1 have S5: "A \<in> \<complex>".
   from A3 have S6: "A \<noteq> \<zero>".
   from S4 S5 S6 have S7: "( B \<cdiv> A ) \<in> \<complex>" by (rule MMI_divcl)
   from A3 have S8: "A \<noteq> \<zero>".
   from S2 S3 S7 S8 have S9: "( B \<cdiv> A ) = 
 ( B \<cdiv> A ) \<longleftrightarrow> ( A \<cdot> ( B \<cdiv> A ) ) = B" by (rule MMI_divmul)
   from S1 S9 show "( A \<cdot> ( B \<cdiv> A ) ) = B" by (rule MMI_mpbi)
qed

lemma (in MMIsar0) MMI_divcan1: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "A \<noteq> \<zero>"   
   shows "( ( B \<cdiv> A ) \<cdot> A ) = B"
proof -
   from A2 have S1: "B \<in> \<complex>".
   from A1 have S2: "A \<in> \<complex>".
   from A3 have S3: "A \<noteq> \<zero>".
   from S1 S2 S3 have S4: "( B \<cdiv> A ) \<in> \<complex>" by (rule MMI_divcl)
   from A1 have S5: "A \<in> \<complex>".
   from S4 S5 have S6: "( ( B \<cdiv> A ) \<cdot> A ) = ( A \<cdot> ( B \<cdiv> A ) )" by (rule MMI_mulcom)
   from A1 have S7: "A \<in> \<complex>".
   from A2 have S8: "B \<in> \<complex>".
   from A3 have S9: "A \<noteq> \<zero>".
   from S7 S8 S9 have S10: "( A \<cdot> ( B \<cdiv> A ) ) = B" by (rule MMI_divcan2)
   from S6 S10 show "( ( B \<cdiv> A ) \<cdot> A ) = B" by (rule MMI_eqtr)
qed

lemma (in MMIsar0) MMI_divcan1z: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "A \<noteq> \<zero> \<longrightarrow> ( ( B \<cdiv> A ) \<cdot> A ) = B"
proof -
   have S1: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( B \<cdiv> A ) = 
 ( B \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) )" by (rule MMI_opreq2)
   have S2: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 A = if ( A \<noteq> \<zero> , A , \<one> )" by (rule MMI_id)
   from S1 S2 have S3: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( ( B \<cdiv> A ) \<cdot> A ) = 
 ( ( B \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) ) \<cdot> if ( A \<noteq> \<zero> , A , \<one> ) )" by (rule MMI_opreq12d)
   from S3 have S4: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( ( ( B \<cdiv> A ) \<cdot> A ) = 
 B \<longleftrightarrow> 
 ( ( B \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) ) \<cdot> if ( A \<noteq> \<zero> , A , \<one> ) ) = 
 B )" by (rule MMI_eqeq1d)
   from A1 have S5: "A \<in> \<complex>".
   have S6: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S5 S6 have S7: "if ( A \<noteq> \<zero> , A , \<one> ) \<in> \<complex>" by (rule MMI_keepel)
   from A2 have S8: "B \<in> \<complex>".
   have S9: "if ( A \<noteq> \<zero> , A , \<one> ) \<noteq> \<zero>" by (rule MMI_elimne0)
   from S7 S8 S9 have S10: "( ( B \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) ) \<cdot> if ( A \<noteq> \<zero> , A , \<one> ) ) = 
 B" by (rule MMI_divcan1)
   from S4 S10 show "A \<noteq> \<zero> \<longrightarrow> ( ( B \<cdiv> A ) \<cdot> A ) = B" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_divcan2z: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "A \<noteq> \<zero> \<longrightarrow> ( A \<cdot> ( B \<cdiv> A ) ) = B"
proof -
   have S1: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 A = if ( A \<noteq> \<zero> , A , \<one> )" by (rule MMI_id)
   have S2: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( B \<cdiv> A ) = 
 ( B \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) )" by (rule MMI_opreq2)
   from S1 S2 have S3: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( A \<cdot> ( B \<cdiv> A ) ) = 
 ( if ( A \<noteq> \<zero> , A , \<one> ) \<cdot> ( B \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) ) )" by (rule MMI_opreq12d)
   from S3 have S4: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( ( A \<cdot> ( B \<cdiv> A ) ) = 
 B \<longleftrightarrow> 
 ( if ( A \<noteq> \<zero> , A , \<one> ) \<cdot> ( B \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) ) ) = 
 B )" by (rule MMI_eqeq1d)
   from A1 have S5: "A \<in> \<complex>".
   have S6: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S5 S6 have S7: "if ( A \<noteq> \<zero> , A , \<one> ) \<in> \<complex>" by (rule MMI_keepel)
   from A2 have S8: "B \<in> \<complex>".
   have S9: "if ( A \<noteq> \<zero> , A , \<one> ) \<noteq> \<zero>" by (rule MMI_elimne0)
   from S7 S8 S9 have S10: "( if ( A \<noteq> \<zero> , A , \<one> ) \<cdot> ( B \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) ) ) = 
 B" by (rule MMI_divcan2)
   from S4 S10 show "A \<noteq> \<zero> \<longrightarrow> ( A \<cdot> ( B \<cdiv> A ) ) = B" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_divcan1t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( ( B \<cdiv> A ) \<cdot> A ) = B"
proof -
   have S1: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<noteq> \<zero> \<longleftrightarrow> if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   have S2: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( B \<cdiv> A ) = 
 ( B \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_opreq2)
   have S3: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 A = if ( A \<in> \<complex> , A , \<zero> )" by (rule MMI_id)
   from S2 S3 have S4: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( B \<cdiv> A ) \<cdot> A ) = 
 ( ( B \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_opreq12d)
   from S4 have S5: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( ( B \<cdiv> A ) \<cdot> A ) = 
 B \<longleftrightarrow> 
 ( ( B \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> if ( A \<in> \<complex> , A , \<zero> ) ) = 
 B )" by (rule MMI_eqeq1d)
   from S1 S5 have S6: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( A \<noteq> \<zero> \<longrightarrow> ( ( B \<cdiv> A ) \<cdot> A ) = B ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( ( B \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> if ( A \<in> \<complex> , A , \<zero> ) ) = 
 B ) )" by (rule MMI_imbi12d)
   have S7: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( B \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) = 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_opreq1)
   from S7 have S8: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( B \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> if ( A \<in> \<complex> , A , \<zero> ) ) = 
 ( ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_opreq1d)
   have S9: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 B = if ( B \<in> \<complex> , B , \<zero> )" by (rule MMI_id)
   from S8 S9 have S10: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( ( B \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> if ( A \<in> \<complex> , A , \<zero> ) ) = 
 B \<longleftrightarrow> 
 ( ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> if ( A \<in> \<complex> , A , \<zero> ) ) = 
 if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_eqeq12d)
   from S10 have S11: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> \<longrightarrow> ( ( B \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> if ( A \<in> \<complex> , A , \<zero> ) ) = B ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> if ( A \<in> \<complex> , A , \<zero> ) ) = 
 if ( B \<in> \<complex> , B , \<zero> ) ) )" by (rule MMI_imbi2d)
   have S12: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S12 have S13: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S14: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S14 have S15: "if ( B \<in> \<complex> , B , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S13 S15 have S16: "if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) \<cdot> if ( A \<in> \<complex> , A , \<zero> ) ) = 
 if ( B \<in> \<complex> , B , \<zero> )" by (rule MMI_divcan1z)
   from S6 S11 S16 have S17: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( A \<noteq> \<zero> \<longrightarrow> ( ( B \<cdiv> A ) \<cdot> A ) = B )" by (rule MMI_dedth2h)
   from S17 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( ( B \<cdiv> A ) \<cdot> A ) = B" by (rule MMI_3impia)
qed

lemma (in MMIsar0) MMI_divcan2t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdot> ( B \<cdiv> A ) ) = B"
proof -
   have S1: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<noteq> \<zero> \<longleftrightarrow> if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   have S2: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 A = if ( A \<in> \<complex> , A , \<zero> )" by (rule MMI_id)
   have S3: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( B \<cdiv> A ) = 
 ( B \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_opreq2)
   from S2 S3 have S4: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<cdot> ( B \<cdiv> A ) ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( B \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) )" by (rule MMI_opreq12d)
   from S4 have S5: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> ( B \<cdiv> A ) ) = 
 B \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( B \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) ) = 
 B )" by (rule MMI_eqeq1d)
   from S1 S5 have S6: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( A \<noteq> \<zero> \<longrightarrow> ( A \<cdot> ( B \<cdiv> A ) ) = B ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( B \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) ) = 
 B ) )" by (rule MMI_imbi12d)
   have S7: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( B \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) = 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_opreq1)
   from S7 have S8: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( B \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) )" by (rule MMI_opreq2d)
   have S9: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 B = if ( B \<in> \<complex> , B , \<zero> )" by (rule MMI_id)
   from S8 S9 have S10: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( B \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) ) = 
 B \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) ) = 
 if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_eqeq12d)
   from S10 have S11: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> \<longrightarrow> ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( B \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) ) = B ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) ) = 
 if ( B \<in> \<complex> , B , \<zero> ) ) )" by (rule MMI_imbi2d)
   have S12: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S12 have S13: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S14: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S14 have S15: "if ( B \<in> \<complex> , B , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S13 S15 have S16: "if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) ) = 
 if ( B \<in> \<complex> , B , \<zero> )" by (rule MMI_divcan2z)
   from S6 S11 S16 have S17: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( A \<noteq> \<zero> \<longrightarrow> ( A \<cdot> ( B \<cdiv> A ) ) = B )" by (rule MMI_dedth2h)
   from S17 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdot> ( B \<cdiv> A ) ) = B" by (rule MMI_3impia)
qed

(************** 171-180**************************)

lemma (in MMIsar0) MMI_divne0bt: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<noteq> \<zero> \<longleftrightarrow> ( A \<cdiv> B ) \<noteq> \<zero> )"
proof -
   have S1: "B \<in> \<complex> \<longrightarrow> ( B \<cdot> \<zero> ) = \<zero>" by (rule MMI_mul01t)
   from S1 have S2: "B \<in> \<complex> \<longrightarrow> ( ( B \<cdot> \<zero> ) = A \<longleftrightarrow> \<zero> = A )" by (rule MMI_eqeq1d)
   have S3: "A = \<zero> \<longleftrightarrow> \<zero> = A" by (rule MMI_eqcom)
   from S2 S3 have S4: "B \<in> \<complex> \<longrightarrow> ( A = \<zero> \<longleftrightarrow> ( B \<cdot> \<zero> ) = A )" by (rule MMI_syl6rbbrA)
   from S4 have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A = \<zero> \<longleftrightarrow> ( B \<cdot> \<zero> ) = A )" by (rule MMI_3ad2ant2)
   have S6: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   have S7: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> \<zero> \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) = \<zero> \<longleftrightarrow> ( B \<cdot> \<zero> ) = A )" by (rule MMI_divmult)
   from S6 S7 have S8: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) = \<zero> \<longleftrightarrow> ( B \<cdot> \<zero> ) = A )" by (rule MMI_mp3anl3)
   from S8 have S9: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) = \<zero> \<longleftrightarrow> ( B \<cdot> \<zero> ) = A )" by (rule MMI_3impa)
   from S5 S9 have S10: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A = \<zero> \<longleftrightarrow> ( A \<cdiv> B ) = \<zero> )" by (rule MMI_bitr4d)
   from S10 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<noteq> \<zero> \<longleftrightarrow> ( A \<cdiv> B ) \<noteq> \<zero> )" by (rule MMI_eqneqd)
qed

lemma (in MMIsar0) MMI_divne0: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "A \<noteq> \<zero>" and
    A4: "B \<noteq> \<zero>"   
   shows "( A \<cdiv> B ) \<noteq> \<zero>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A4 have S3: "B \<noteq> \<zero>".
   from A3 have S4: "A \<noteq> \<zero>".
   have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<noteq> \<zero> \<longleftrightarrow> ( A \<cdiv> B ) \<noteq> \<zero> )" by (rule MMI_divne0bt)
   from S4 S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) \<noteq> \<zero>" by (rule MMI_mpbii)
   from S1 S2 S3 S6 show "( A \<cdiv> B ) \<noteq> \<zero>" by (rule MMI_mp3an)
qed

lemma (in MMIsar0) MMI_recne0z: assumes A1: "A \<in> \<complex>"   
   shows "A \<noteq> \<zero> \<longrightarrow> ( \<one> \<cdiv> A ) \<noteq> \<zero>"
proof -
   have S1: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( \<one> \<cdiv> A ) = 
 ( \<one> \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) )" by (rule MMI_opreq2)
   from S1 have S2: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( ( \<one> \<cdiv> A ) \<noteq> \<zero> \<longleftrightarrow> 
 ( \<one> \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) ) \<noteq> \<zero> )" by (rule MMI_neeq1d)
   have S3: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from A1 have S4: "A \<in> \<complex>".
   have S5: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S4 S5 have S6: "if ( A \<noteq> \<zero> , A , \<one> ) \<in> \<complex>" by (rule MMI_keepel)
   have S7: "\<one> \<noteq> \<zero>" by (rule MMI_ax1ne0)
   have S8: "if ( A \<noteq> \<zero> , A , \<one> ) \<noteq> \<zero>" by (rule MMI_elimne0)
   from S3 S6 S7 S8 have S9: "( \<one> \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) ) \<noteq> \<zero>" by (rule MMI_divne0)
   from S2 S9 show "A \<noteq> \<zero> \<longrightarrow> ( \<one> \<cdiv> A ) \<noteq> \<zero>" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_recne0t: 
   shows "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> ( \<one> \<cdiv> A ) \<noteq> \<zero>"
proof -
   have S1: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<noteq> \<zero> \<longleftrightarrow> if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   have S2: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( \<one> \<cdiv> A ) = 
 ( \<one> \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_opreq2)
   from S2 have S3: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( \<one> \<cdiv> A ) \<noteq> \<zero> \<longleftrightarrow> 
 ( \<one> \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) \<noteq> \<zero> )" by (rule MMI_neeq1d)
   from S1 S3 have S4: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( A \<noteq> \<zero> \<longrightarrow> ( \<one> \<cdiv> A ) \<noteq> \<zero> ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( \<one> \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) \<noteq> \<zero> ) )" by (rule MMI_imbi12d)
   have S5: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S5 have S6: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S6 have S7: "if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( \<one> \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) \<noteq> \<zero>" by (rule MMI_recne0z)
   from S4 S7 have S8: "A \<in> \<complex> \<longrightarrow> ( A \<noteq> \<zero> \<longrightarrow> ( \<one> \<cdiv> A ) \<noteq> \<zero> )" by (rule MMI_dedth)
   from S8 show "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> ( \<one> \<cdiv> A ) \<noteq> \<zero>" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_recid: assumes A1: "A \<in> \<complex>" and
    A2: "A \<noteq> \<zero>"   
   shows "( A \<cdot> ( \<one> \<cdiv> A ) ) = \<one>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   have S2: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from A2 have S3: "A \<noteq> \<zero>".
   from S1 S2 S3 show "( A \<cdot> ( \<one> \<cdiv> A ) ) = \<one>" by (rule MMI_divcan2)
qed

lemma (in MMIsar0) MMI_recidz: assumes A1: "A \<in> \<complex>"   
   shows "A \<noteq> \<zero> \<longrightarrow> ( A \<cdot> ( \<one> \<cdiv> A ) ) = \<one>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   have S2: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S1 S2 show "A \<noteq> \<zero> \<longrightarrow> ( A \<cdot> ( \<one> \<cdiv> A ) ) = \<one>" by (rule MMI_divcan2z)
qed

lemma (in MMIsar0) MMI_recidt: 
   shows "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdot> ( \<one> \<cdiv> A ) ) = \<one>"
proof -
   have S1: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<noteq> \<zero> \<longleftrightarrow> if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   have S2: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 A = if ( A \<in> \<complex> , A , \<zero> )" by (rule MMI_id)
   have S3: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( \<one> \<cdiv> A ) = 
 ( \<one> \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_opreq2)
   from S2 S3 have S4: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<cdot> ( \<one> \<cdiv> A ) ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( \<one> \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) )" by (rule MMI_opreq12d)
   from S4 have S5: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> ( \<one> \<cdiv> A ) ) = 
 \<one> \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( \<one> \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) ) = 
 \<one> )" by (rule MMI_eqeq1d)
   from S1 S5 have S6: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( A \<noteq> \<zero> \<longrightarrow> ( A \<cdot> ( \<one> \<cdiv> A ) ) = \<one> ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( \<one> \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) ) = 
 \<one> ) )" by (rule MMI_imbi12d)
   have S7: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S7 have S8: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S8 have S9: "if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( \<one> \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) ) = 
 \<one>" by (rule MMI_recidz)
   from S6 S9 have S10: "A \<in> \<complex> \<longrightarrow> 
 ( A \<noteq> \<zero> \<longrightarrow> ( A \<cdot> ( \<one> \<cdiv> A ) ) = \<one> )" by (rule MMI_dedth)
   from S10 show "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdot> ( \<one> \<cdiv> A ) ) = \<one>" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_recid2t: 
   shows "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( ( \<one> \<cdiv> A ) \<cdot> A ) = \<one>"
proof -
   have S1: "( ( \<one> \<cdiv> A ) \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> 
 ( ( \<one> \<cdiv> A ) \<cdot> A ) = ( A \<cdot> ( \<one> \<cdiv> A ) )" by (rule MMI_axmulcom)
   have S2: "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> ( \<one> \<cdiv> A ) \<in> \<complex>" by (rule MMI_recclt)
   have S3: "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> A \<in> \<complex>" by (rule MMI_pm3_26)
   from S1 S2 S3 have S4: "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( ( \<one> \<cdiv> A ) \<cdot> A ) = ( A \<cdot> ( \<one> \<cdiv> A ) )" by (rule MMI_sylanc)
   have S5: "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdot> ( \<one> \<cdiv> A ) ) = \<one>" by (rule MMI_recidt)
   from S4 S5 show "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( ( \<one> \<cdiv> A ) \<cdot> A ) = \<one>" by (rule MMI_eqtrd)
qed

lemma (in MMIsar0) MMI_divrec: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "B \<noteq> \<zero>"   
   shows "( A \<cdiv> B ) = ( A \<cdot> ( \<one> \<cdiv> B ) )"
proof -
   from A2 have S1: "B \<in> \<complex>".
   from A1 have S2: "A \<in> \<complex>".
   from A2 have S3: "B \<in> \<complex>".
   from A3 have S4: "B \<noteq> \<zero>".
   from S3 S4 have S5: "( \<one> \<cdiv> B ) \<in> \<complex>" by (rule MMI_reccl)
   from S2 S5 have S6: "( A \<cdot> ( \<one> \<cdiv> B ) ) \<in> \<complex>" by (rule MMI_mulcl)
   from S1 S6 have S7: "( B \<cdot> ( A \<cdot> ( \<one> \<cdiv> B ) ) ) = 
 ( ( A \<cdot> ( \<one> \<cdiv> B ) ) \<cdot> B )" by (rule MMI_mulcom)
   from A1 have S8: "A \<in> \<complex>".
   from S5 have S9: "( \<one> \<cdiv> B ) \<in> \<complex>" .
   from A2 have S10: "B \<in> \<complex>".
   from S8 S9 S10 have S11: "( ( A \<cdot> ( \<one> \<cdiv> B ) ) \<cdot> B ) = 
 ( A \<cdot> ( ( \<one> \<cdiv> B ) \<cdot> B ) )" by (rule MMI_mulass)
   from A2 have S12: "B \<in> \<complex>".
   have S13: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from A3 have S14: "B \<noteq> \<zero>".
   from S12 S13 S14 have S15: "( ( \<one> \<cdiv> B ) \<cdot> B ) = \<one>" by (rule MMI_divcan1)
   from S15 have S16: "( A \<cdot> ( ( \<one> \<cdiv> B ) \<cdot> B ) ) = ( A \<cdot> \<one> )" by (rule MMI_opreq2i)
   from A1 have S17: "A \<in> \<complex>".
   from S17 have S18: "( A \<cdot> \<one> ) = A" by (rule MMI_mulid1)
   from S16 S18 have S19: "( A \<cdot> ( ( \<one> \<cdiv> B ) \<cdot> B ) ) = A" by (rule MMI_eqtr)
   from S7 S11 S19 have S20: "( B \<cdot> ( A \<cdot> ( \<one> \<cdiv> B ) ) ) = A" by (rule MMI_3eqtr)
   from A1 have S21: "A \<in> \<complex>".
   from A2 have S22: "B \<in> \<complex>".
   from S6 have S23: "( A \<cdot> ( \<one> \<cdiv> B ) ) \<in> \<complex>" .
   from A3 have S24: "B \<noteq> \<zero>".
   from S21 S22 S23 S24 have S25: "( A \<cdiv> B ) = 
 ( A \<cdot> ( \<one> \<cdiv> B ) ) \<longleftrightarrow> 
 ( B \<cdot> ( A \<cdot> ( \<one> \<cdiv> B ) ) ) = A" by (rule MMI_divmul)
   from S20 S25 show "( A \<cdiv> B ) = ( A \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_mpbir)
qed

lemma (in MMIsar0) MMI_divrecz: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "B \<noteq> \<zero> \<longrightarrow> ( A \<cdiv> B ) = ( A \<cdot> ( \<one> \<cdiv> B ) )"
proof -
   have S1: "B = 
 if ( B \<noteq> \<zero> , B , \<one> ) \<longrightarrow> 
 ( A \<cdiv> B ) = 
 ( A \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) )" by (rule MMI_opreq2)
   have S2: "B = 
 if ( B \<noteq> \<zero> , B , \<one> ) \<longrightarrow> 
 ( \<one> \<cdiv> B ) = 
 ( \<one> \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) )" by (rule MMI_opreq2)
   from S2 have S3: "B = 
 if ( B \<noteq> \<zero> , B , \<one> ) \<longrightarrow> 
 ( A \<cdot> ( \<one> \<cdiv> B ) ) = 
 ( A \<cdot> ( \<one> \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) ) )" by (rule MMI_opreq2d)
   from S1 S3 have S4: "B = 
 if ( B \<noteq> \<zero> , B , \<one> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) = 
 ( A \<cdot> ( \<one> \<cdiv> B ) ) \<longleftrightarrow> 
 ( A \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) ) = 
 ( A \<cdot> ( \<one> \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) ) ) )" by (rule MMI_eqeq12d)
   from A1 have S5: "A \<in> \<complex>".
   from A2 have S6: "B \<in> \<complex>".
   have S7: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S6 S7 have S8: "if ( B \<noteq> \<zero> , B , \<one> ) \<in> \<complex>" by (rule MMI_keepel)
   have S9: "if ( B \<noteq> \<zero> , B , \<one> ) \<noteq> \<zero>" by (rule MMI_elimne0)
   from S5 S8 S9 have S10: "( A \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) ) = 
 ( A \<cdot> ( \<one> \<cdiv> if ( B \<noteq> \<zero> , B , \<one> ) ) )" by (rule MMI_divrec)
   from S4 S10 show "B \<noteq> \<zero> \<longrightarrow> ( A \<cdiv> B ) = ( A \<cdot> ( \<one> \<cdiv> B ) )" 
     by (rule MMI_dedth)
qed

(**********181-190*************************************)

lemma (in MMIsar0) MMI_divrect: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) = ( A \<cdot> ( \<one> \<cdiv> B ) )"
proof -
   have S1: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B )" by (rule MMI_opreq1)
   have S2: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<cdot> ( \<one> \<cdiv> B ) ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_opreq1)
   from S1 S2 have S3: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) = 
 ( A \<cdot> ( \<one> \<cdiv> B ) ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( \<one> \<cdiv> B ) ) )" by (rule MMI_eqeq12d)
   from S3 have S4: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<longrightarrow> ( A \<cdiv> B ) = ( A \<cdot> ( \<one> \<cdiv> B ) ) ) \<longleftrightarrow> 
 ( B \<noteq> \<zero> \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( \<one> \<cdiv> B ) ) ) )" by (rule MMI_imbi2d)
   have S5: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( B \<noteq> \<zero> \<longleftrightarrow> if ( B \<in> \<complex> , B , \<zero> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   have S6: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_opreq2)
   have S7: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( \<one> \<cdiv> B ) = 
 ( \<one> \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_opreq2)
   from S7 have S8: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( \<one> \<cdiv> B ) ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( \<one> \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) )" by (rule MMI_opreq2d)
   from S6 S8 have S9: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( \<one> \<cdiv> B ) ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( \<one> \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) ) )" by (rule MMI_eqeq12d)
   from S5 S9 have S10: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( B \<noteq> \<zero> \<longrightarrow> ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> B ) = ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( \<one> \<cdiv> B ) ) ) \<longleftrightarrow> 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( \<one> \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) ) ) )" by (rule MMI_imbi12d)
   have S11: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S11 have S12: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S13: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S13 have S14: "if ( B \<in> \<complex> , B , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S12 S14 have S15: "if ( B \<in> \<complex> , B , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> ( \<one> \<cdiv> if ( B \<in> \<complex> , B , \<zero> ) ) )" by (rule MMI_divrecz)
   from S4 S10 S15 have S16: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( B \<noteq> \<zero> \<longrightarrow> 
 ( A \<cdiv> B ) = ( A \<cdot> ( \<one> \<cdiv> B ) ) )" by (rule MMI_dedth2h)
   from S16 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) = ( A \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_3impia)
qed

lemma (in MMIsar0) MMI_divrec2t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) = ( ( \<one> \<cdiv> B ) \<cdot> A )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) = ( A \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_divrect)
   have S2: "( A \<in> \<complex> \<and> ( \<one> \<cdiv> B ) \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> ( \<one> \<cdiv> B ) ) = ( ( \<one> \<cdiv> B ) \<cdot> A )" by (rule MMI_axmulcom)
   have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> A \<in> \<complex>" by (rule MMI_3simp1)
   have S4: "( B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> ( \<one> \<cdiv> B ) \<in> \<complex>" by (rule MMI_recclt)
   from S4 have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( \<one> \<cdiv> B ) \<in> \<complex>" by (rule MMI_3adant1)
   from S2 S3 S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdot> ( \<one> \<cdiv> B ) ) = ( ( \<one> \<cdiv> B ) \<cdot> A )" by (rule MMI_sylanc)
   from S1 S6 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) = ( ( \<one> \<cdiv> B ) \<cdot> A )" by (rule MMI_eqtrd)
qed

lemma (in MMIsar0) MMI_divasst: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> C ) = ( A \<cdot> ( B \<cdiv> C ) )"
proof -
   have S1: "A \<in> \<complex> \<longrightarrow> A \<in> \<complex>" by (rule MMI_id)
   have S2: "B \<in> \<complex> \<longrightarrow> B \<in> \<complex>" by (rule MMI_id)
   have S3: "( C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> ( \<one> \<cdiv> C ) \<in> \<complex>" by (rule MMI_recclt)
   from S1 S2 S3 have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> ( \<one> \<cdiv> C ) \<in> \<complex> )" by (rule MMI_3anim123i)
   from S4 have S5: "A \<in> \<complex> \<longrightarrow> 
 ( B \<in> \<complex> \<longrightarrow> 
 ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> ( \<one> \<cdiv> C ) \<in> \<complex> ) ) )" by (rule MMI_3exp)
   from S5 have S6: "A \<in> \<complex> \<longrightarrow> 
 ( B \<in> \<complex> \<longrightarrow> 
 ( C \<in> \<complex> \<longrightarrow> 
 ( C \<noteq> \<zero> \<longrightarrow> 
 ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> ( \<one> \<cdiv> C ) \<in> \<complex> ) ) ) )" by (rule MMI_exp4a)
   from S6 have S7: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> ( \<one> \<cdiv> C ) \<in> \<complex> )" by (rule MMI_3imp1)
   have S8: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> ( \<one> \<cdiv> C ) \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdot> ( \<one> \<cdiv> C ) ) = 
 ( A \<cdot> ( B \<cdot> ( \<one> \<cdiv> C ) ) )" by (rule MMI_axmulass)
   from S7 S8 have S9: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdot> ( \<one> \<cdiv> C ) ) = 
 ( A \<cdot> ( B \<cdot> ( \<one> \<cdiv> C ) ) )" by (rule MMI_syl)
   have S10: "( ( A \<cdot> B ) \<in> \<complex> \<and> C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> C ) = 
 ( ( A \<cdot> B ) \<cdot> ( \<one> \<cdiv> C ) )" by (rule MMI_divrect)
   from S10 have S11: "( ( ( A \<cdot> B ) \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> C ) = 
 ( ( A \<cdot> B ) \<cdot> ( \<one> \<cdiv> C ) )" by (rule MMI_3expa)
   have S12: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> ( A \<cdot> B ) \<in> \<complex>" by (rule MMI_axmulcl)
   from S12 have S13: "( ( A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<in> \<complex> \<and> C \<in> \<complex> )" by (rule MMI_anim1i)
   from S13 have S14: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<in> \<complex> \<and> C \<in> \<complex> )" by (rule MMI_3impa)
   from S11 S14 have S15: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> C ) = 
 ( ( A \<cdot> B ) \<cdot> ( \<one> \<cdiv> C ) )" by (rule MMI_sylan)
   have S16: "( B \<in> \<complex> \<and> C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( B \<cdiv> C ) = ( B \<cdot> ( \<one> \<cdiv> C ) )" by (rule MMI_divrect)
   from S16 have S17: "( ( B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( B \<cdiv> C ) = ( B \<cdot> ( \<one> \<cdiv> C ) )" by (rule MMI_3expa)
   from S17 have S18: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( B \<cdiv> C ) = ( B \<cdot> ( \<one> \<cdiv> C ) )" by (rule MMI_3adantl1)
   from S18 have S19: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdot> ( B \<cdiv> C ) ) = 
 ( A \<cdot> ( B \<cdot> ( \<one> \<cdiv> C ) ) )" by (rule MMI_opreq2d)
   from S9 S15 S19 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> C ) = ( A \<cdot> ( B \<cdiv> C ) )" by (rule MMI_3eqtr4d)
qed

lemma (in MMIsar0) MMI_div23t: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> C ) = ( ( A \<cdiv> C ) \<cdot> B )"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> B ) = ( B \<cdot> A )" by (rule MMI_axmulcom)
   from S1 have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> B ) = ( B \<cdot> A )" by (rule MMI_3adant3)
   from S2 have S3: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdot> B ) = ( B \<cdot> A )" by (rule MMI_adantr)
   from S3 have S4: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> C ) = ( ( B \<cdot> A ) \<cdiv> C )" by (rule MMI_opreq1d)
   have S5: "( ( B \<in> \<complex> \<and> A \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( B \<cdot> A ) \<cdiv> C ) = ( B \<cdot> ( A \<cdiv> C ) )" by (rule MMI_divasst)
   from S5 have S6: "( B \<in> \<complex> \<and> A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( C \<noteq> \<zero> \<longrightarrow> 
 ( ( B \<cdot> A ) \<cdiv> C ) = 
 ( B \<cdot> ( A \<cdiv> C ) ) )" by (rule MMI_ex)
   from S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( C \<noteq> \<zero> \<longrightarrow> 
 ( ( B \<cdot> A ) \<cdiv> C ) = 
 ( B \<cdot> ( A \<cdiv> C ) ) )" by (rule MMI_3com12)
   from S7 have S8: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( B \<cdot> A ) \<cdiv> C ) = ( B \<cdot> ( A \<cdiv> C ) )" by (rule MMI_imp)
   have S9: "( B \<in> \<complex> \<and> ( A \<cdiv> C ) \<in> \<complex> ) \<longrightarrow> 
 ( B \<cdot> ( A \<cdiv> C ) ) = ( ( A \<cdiv> C ) \<cdot> B )" by (rule MMI_axmulcom)
   have S10: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> B \<in> \<complex>" by (rule MMI_3simp2)
   from S10 have S11: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 B \<in> \<complex>" by (rule MMI_adantr)
   have S12: "( A \<in> \<complex> \<and> C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> C ) \<in> \<complex>" by (rule MMI_divclt)
   from S12 have S13: "( ( A \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> C ) \<in> \<complex>" by (rule MMI_3expa)
   from S13 have S14: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> C ) \<in> \<complex>" by (rule MMI_3adantl2)
   from S9 S11 S14 have S15: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( B \<cdot> ( A \<cdiv> C ) ) = ( ( A \<cdiv> C ) \<cdot> B )" by (rule MMI_sylanc)
   from S4 S8 S15 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> C ) = ( ( A \<cdiv> C ) \<cdot> B )" by (rule MMI_3eqtrd)
qed

lemma (in MMIsar0) MMI_div13t: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> C ) = ( ( C \<cdiv> B ) \<cdot> A )"
proof -
   have S1: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> C ) = ( C \<cdot> A )" by (rule MMI_axmulcom)
   from S1 have S2: "( A \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> C ) \<cdiv> B ) = ( ( C \<cdot> A ) \<cdiv> B )" by (rule MMI_opreq1d)
   from S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> C ) \<cdiv> B ) = ( ( C \<cdot> A ) \<cdiv> B )" by (rule MMI_3adant2)
   from S3 have S4: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> C ) \<cdiv> B ) = ( ( C \<cdot> A ) \<cdiv> B )" by (rule MMI_adantr)
   have S5: "( ( A \<in> \<complex> \<and> C \<in> \<complex> \<and> B \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> C ) \<cdiv> B ) = ( ( A \<cdiv> B ) \<cdot> C )" by (rule MMI_div23t)
   from S5 have S6: "( A \<in> \<complex> \<and> C \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( B \<noteq> \<zero> \<longrightarrow> 
 ( ( A \<cdot> C ) \<cdiv> B ) = 
 ( ( A \<cdiv> B ) \<cdot> C ) )" by (rule MMI_ex)
   from S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( B \<noteq> \<zero> \<longrightarrow> 
 ( ( A \<cdot> C ) \<cdiv> B ) = 
 ( ( A \<cdiv> B ) \<cdot> C ) )" by (rule MMI_3com23)
   from S7 have S8: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> C ) \<cdiv> B ) = ( ( A \<cdiv> B ) \<cdot> C )" by (rule MMI_imp)
   have S9: "( ( C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( C \<cdot> A ) \<cdiv> B ) = ( ( C \<cdiv> B ) \<cdot> A )" by (rule MMI_div23t)
   from S9 have S10: "( C \<in> \<complex> \<and> A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( B \<noteq> \<zero> \<longrightarrow> 
 ( ( C \<cdot> A ) \<cdiv> B ) = 
 ( ( C \<cdiv> B ) \<cdot> A ) )" by (rule MMI_ex)
   from S10 have S11: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( B \<noteq> \<zero> \<longrightarrow> 
 ( ( C \<cdot> A ) \<cdiv> B ) = 
 ( ( C \<cdiv> B ) \<cdot> A ) )" by (rule MMI_3coml)
   from S11 have S12: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( C \<cdot> A ) \<cdiv> B ) = ( ( C \<cdiv> B ) \<cdot> A )" by (rule MMI_imp)
   from S4 S8 S12 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> B ) \<cdot> C ) = ( ( C \<cdiv> B ) \<cdot> A )" by (rule MMI_3eqtr3d)
qed

lemma (in MMIsar0) MMI_div12t: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdot> ( B \<cdiv> C ) ) = ( B \<cdot> ( A \<cdiv> C ) )"
proof -
   have S1: "( A \<in> \<complex> \<and> ( B \<cdiv> C ) \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> ( B \<cdiv> C ) ) = ( ( B \<cdiv> C ) \<cdot> A )" by (rule MMI_axmulcom)
   have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> A \<in> \<complex>" by (rule MMI_3simp1)
   from S2 have S3: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 A \<in> \<complex>" by (rule MMI_adantr)
   have S4: "( B \<in> \<complex> \<and> C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( B \<cdiv> C ) \<in> \<complex>" by (rule MMI_divclt)
   from S4 have S5: "( ( B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( B \<cdiv> C ) \<in> \<complex>" by (rule MMI_3expa)
   from S5 have S6: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( B \<cdiv> C ) \<in> \<complex>" by (rule MMI_3adantl1)
   from S1 S3 S6 have S7: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdot> ( B \<cdiv> C ) ) = ( ( B \<cdiv> C ) \<cdot> A )" by (rule MMI_sylanc)
   have S8: "( ( B \<in> \<complex> \<and> C \<in> \<complex> \<and> A \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( B \<cdiv> C ) \<cdot> A ) = ( ( A \<cdiv> C ) \<cdot> B )" by (rule MMI_div13t)
   from S8 have S9: "( B \<in> \<complex> \<and> C \<in> \<complex> \<and> A \<in> \<complex> ) \<longrightarrow> 
 ( C \<noteq> \<zero> \<longrightarrow> 
 ( ( B \<cdiv> C ) \<cdot> A ) = 
 ( ( A \<cdiv> C ) \<cdot> B ) )" by (rule MMI_ex)
   from S9 have S10: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( C \<noteq> \<zero> \<longrightarrow> 
 ( ( B \<cdiv> C ) \<cdot> A ) = 
 ( ( A \<cdiv> C ) \<cdot> B ) )" by (rule MMI_3comr)
   from S10 have S11: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( B \<cdiv> C ) \<cdot> A ) = ( ( A \<cdiv> C ) \<cdot> B )" by (rule MMI_imp)
   have S12: "( ( A \<cdiv> C ) \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdiv> C ) \<cdot> B ) = ( B \<cdot> ( A \<cdiv> C ) )" by (rule MMI_axmulcom)
   have S13: "( A \<in> \<complex> \<and> C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> C ) \<in> \<complex>" by (rule MMI_divclt)
   from S13 have S14: "( ( A \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> C ) \<in> \<complex>" by (rule MMI_3expa)
   from S14 have S15: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> C ) \<in> \<complex>" by (rule MMI_3adantl2)
   have S16: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> B \<in> \<complex>" by (rule MMI_3simp2)
   from S16 have S17: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 B \<in> \<complex>" by (rule MMI_adantr)
   from S12 S15 S17 have S18: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> C ) \<cdot> B ) = ( B \<cdot> ( A \<cdiv> C ) )" by (rule MMI_sylanc)
   from S7 S11 S18 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdot> ( B \<cdiv> C ) ) = ( B \<cdot> ( A \<cdiv> C ) )" by (rule MMI_3eqtrd)
qed

lemma (in MMIsar0) MMI_divassz: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "C \<noteq> \<zero> \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> C ) = ( A \<cdot> ( B \<cdiv> C ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   from S1 S2 S3 have S4: "A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex>" by (rule MMI_3pm3_2i)
   have S5: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> C ) = ( A \<cdot> ( B \<cdiv> C ) )" by (rule MMI_divasst)
   from S4 S5 show "C \<noteq> \<zero> \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> C ) = ( A \<cdot> ( B \<cdiv> C ) )" by (rule MMI_mpan)
qed

lemma (in MMIsar0) MMI_divass: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>" and
    A4: "C \<noteq> \<zero>"   
   shows "( ( A \<cdot> B ) \<cdiv> C ) = ( A \<cdot> ( B \<cdiv> C ) )"
proof -
   from A4 have S1: "C \<noteq> \<zero>".
   from A1 have S2: "A \<in> \<complex>".
   from A2 have S3: "B \<in> \<complex>".
   from A3 have S4: "C \<in> \<complex>".
   from S2 S3 S4 have S5: "C \<noteq> \<zero> \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> C ) = ( A \<cdot> ( B \<cdiv> C ) )" by (rule MMI_divassz)
   from S1 S5 show "( ( A \<cdot> B ) \<cdiv> C ) = ( A \<cdot> ( B \<cdiv> C ) )" by (rule MMI_ax_mp)
qed

lemma (in MMIsar0) MMI_divdir: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>" and
    A4: "C \<noteq> \<zero>"   
   shows "( ( A \<ca> B ) \<cdiv> C ) = 
 ( ( A \<cdiv> C ) \<ca> ( B \<cdiv> C ) )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   from A4 have S4: "C \<noteq> \<zero>".
   from S3 S4 have S5: "( \<one> \<cdiv> C ) \<in> \<complex>" by (rule MMI_reccl)
   from S1 S2 S5 have S6: "( ( A \<ca> B ) \<cdot> ( \<one> \<cdiv> C ) ) = 
 ( ( A \<cdot> ( \<one> \<cdiv> C ) ) \<ca> ( B \<cdot> ( \<one> \<cdiv> C ) ) )" by (rule MMI_adddir)
   from A1 have S7: "A \<in> \<complex>".
   from A2 have S8: "B \<in> \<complex>".
   from S7 S8 have S9: "( A \<ca> B ) \<in> \<complex>" by (rule MMI_addcl)
   from A3 have S10: "C \<in> \<complex>".
   from A4 have S11: "C \<noteq> \<zero>".
   from S9 S10 S11 have S12: "( ( A \<ca> B ) \<cdiv> C ) = 
 ( ( A \<ca> B ) \<cdot> ( \<one> \<cdiv> C ) )" by (rule MMI_divrec)
   from A1 have S13: "A \<in> \<complex>".
   from A3 have S14: "C \<in> \<complex>".
   from A4 have S15: "C \<noteq> \<zero>".
   from S13 S14 S15 have S16: "( A \<cdiv> C ) = ( A \<cdot> ( \<one> \<cdiv> C ) )" by (rule MMI_divrec)
   from A2 have S17: "B \<in> \<complex>".
   from A3 have S18: "C \<in> \<complex>".
   from A4 have S19: "C \<noteq> \<zero>".
   from S17 S18 S19 have S20: "( B \<cdiv> C ) = ( B \<cdot> ( \<one> \<cdiv> C ) )" by (rule MMI_divrec)
   from S16 S20 have S21: "( ( A \<cdiv> C ) \<ca> ( B \<cdiv> C ) ) = 
 ( ( A \<cdot> ( \<one> \<cdiv> C ) ) \<ca> ( B \<cdot> ( \<one> \<cdiv> C ) ) )" by (rule MMI_opreq12i)
   from S6 S12 S21 show "( ( A \<ca> B ) \<cdiv> C ) = 
 ( ( A \<cdiv> C ) \<ca> ( B \<cdiv> C ) )" by (rule MMI_3eqtr4)
qed

lemma (in MMIsar0) MMI_div23: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>" and
    A4: "C \<noteq> \<zero>"   
   shows "( ( A \<cdot> B ) \<cdiv> C ) = ( ( A \<cdiv> C ) \<cdot> B )"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from S1 S2 have S3: "( A \<cdot> B ) = ( B \<cdot> A )" by (rule MMI_mulcom)
   from S3 have S4: "( ( A \<cdot> B ) \<cdiv> C ) = ( ( B \<cdot> A ) \<cdiv> C )" 
     by (rule MMI_opreq1i)
   from A2 have S5: "B \<in> \<complex>".
   from A1 have S6: "A \<in> \<complex>".
   from A3 have S7: "C \<in> \<complex>".
   from A4 have S8: "C \<noteq> \<zero>".
   from S5 S6 S7 S8 have 
     S9: "( ( B \<cdot> A ) \<cdiv> C ) = ( B \<cdot> ( A \<cdiv> C ) )" by (rule MMI_divass)
   from A2 have S10: "B \<in> \<complex>".
   from A1 have S11: "A \<in> \<complex>".
   from A3 have S12: "C \<in> \<complex>".
   from A4 have S13: "C \<noteq> \<zero>".
   from S11 S12 S13 have S14: "( A \<cdiv> C ) \<in> \<complex>" by (rule MMI_divcl)
   from S10 S14 have S15: "( B \<cdot> ( A \<cdiv> C ) ) = ( ( A \<cdiv> C ) \<cdot> B )" 
     by (rule MMI_mulcom)
   from S4 S9 S15 show "( ( A \<cdot> B ) \<cdiv> C ) = ( ( A \<cdiv> C ) \<cdot> B )" 
     by (rule MMI_3eqtr)
qed

(************* 191-200*************************************)


lemma (in MMIsar0) MMI_divdirz: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>"   
   shows "C \<noteq> \<zero> \<longrightarrow> 
 ( ( A \<ca> B ) \<cdiv> C ) = 
 ( ( A \<cdiv> C ) \<ca> ( B \<cdiv> C ) )"
proof -
   have S1: "C = 
 if ( C \<noteq> \<zero> , C , \<one> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cdiv> C ) = 
 ( ( A \<ca> B ) \<cdiv> if ( C \<noteq> \<zero> , C , \<one> ) )" by (rule MMI_opreq2)
   have S2: "C = 
 if ( C \<noteq> \<zero> , C , \<one> ) \<longrightarrow> 
 ( A \<cdiv> C ) = 
 ( A \<cdiv> if ( C \<noteq> \<zero> , C , \<one> ) )" by (rule MMI_opreq2)
   have S3: "C = 
 if ( C \<noteq> \<zero> , C , \<one> ) \<longrightarrow> 
 ( B \<cdiv> C ) = 
 ( B \<cdiv> if ( C \<noteq> \<zero> , C , \<one> ) )" by (rule MMI_opreq2)
   from S2 S3 have S4: "C = 
 if ( C \<noteq> \<zero> , C , \<one> ) \<longrightarrow> 
 ( ( A \<cdiv> C ) \<ca> ( B \<cdiv> C ) ) = 
 ( ( A \<cdiv> if ( C \<noteq> \<zero> , C , \<one> ) ) \<ca> ( B \<cdiv> if ( C \<noteq> \<zero> , C , \<one> ) ) )" by (rule MMI_opreq12d)
   from S1 S4 have S5: "C = 
 if ( C \<noteq> \<zero> , C , \<one> ) \<longrightarrow> 
 ( ( ( A \<ca> B ) \<cdiv> C ) = 
 ( ( A \<cdiv> C ) \<ca> ( B \<cdiv> C ) ) \<longleftrightarrow> 
 ( ( A \<ca> B ) \<cdiv> if ( C \<noteq> \<zero> , C , \<one> ) ) = 
 ( ( A \<cdiv> if ( C \<noteq> \<zero> , C , \<one> ) ) \<ca> ( B \<cdiv> if ( C \<noteq> \<zero> , C , \<one> ) ) ) )" by (rule MMI_eqeq12d)
   from A1 have S6: "A \<in> \<complex>".
   from A2 have S7: "B \<in> \<complex>".
   from A3 have S8: "C \<in> \<complex>".
   have S9: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S8 S9 have S10: "if ( C \<noteq> \<zero> , C , \<one> ) \<in> \<complex>" by (rule MMI_keepel)
   have S11: "if ( C \<noteq> \<zero> , C , \<one> ) \<noteq> \<zero>" by (rule MMI_elimne0)
   from S6 S7 S10 S11 have S12: "( ( A \<ca> B ) \<cdiv> if ( C \<noteq> \<zero> , C , \<one> ) ) = 
 ( ( A \<cdiv> if ( C \<noteq> \<zero> , C , \<one> ) ) \<ca> ( B \<cdiv> if ( C \<noteq> \<zero> , C , \<one> ) ) )" by (rule MMI_divdir)
   from S5 S12 show "C \<noteq> \<zero> \<longrightarrow> 
 ( ( A \<ca> B ) \<cdiv> C ) = 
 ( ( A \<cdiv> C ) \<ca> ( B \<cdiv> C ) )" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_divdirt: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cdiv> C ) = 
 ( ( A \<cdiv> C ) \<ca> ( B \<cdiv> C ) )"
proof -
   have S1: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<ca> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B )" by (rule MMI_opreq1)
   from S1 have S2: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cdiv> C ) = 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B ) \<cdiv> C )" by (rule MMI_opreq1d)
   have S3: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<cdiv> C ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> C )" by (rule MMI_opreq1)
   from S3 have S4: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> C ) \<ca> ( B \<cdiv> C ) ) = 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> C ) \<ca> ( B \<cdiv> C ) )" by (rule MMI_opreq1d)
   from S2 S4 have S5: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( ( A \<ca> B ) \<cdiv> C ) = 
 ( ( A \<cdiv> C ) \<ca> ( B \<cdiv> C ) ) \<longleftrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B ) \<cdiv> C ) = 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> C ) \<ca> ( B \<cdiv> C ) ) )" by (rule MMI_eqeq12d)
   from S5 have S6: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( C \<noteq> \<zero> \<longrightarrow> ( ( A \<ca> B ) \<cdiv> C ) = ( ( A \<cdiv> C ) \<ca> ( B \<cdiv> C ) ) ) \<longleftrightarrow> 
 ( C \<noteq> \<zero> \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B ) \<cdiv> C ) = 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> C ) \<ca> ( B \<cdiv> C ) ) ) )" by (rule MMI_imbi2d)
   have S7: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_opreq2)
   from S7 have S8: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B ) \<cdiv> C ) = 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) \<cdiv> C )" by (rule MMI_opreq1d)
   have S9: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( B \<cdiv> C ) = 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> C )" by (rule MMI_opreq1)
   from S9 have S10: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> C ) \<ca> ( B \<cdiv> C ) ) = 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> C ) \<ca> ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> C ) )" by (rule MMI_opreq2d)
   from S8 S10 have S11: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B ) \<cdiv> C ) = 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> C ) \<ca> ( B \<cdiv> C ) ) \<longleftrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) \<cdiv> C ) = 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> C ) \<ca> ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> C ) ) )" by (rule MMI_eqeq12d)
   from S11 have S12: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( C \<noteq> \<zero> \<longrightarrow> ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> B ) \<cdiv> C ) = ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> C ) \<ca> ( B \<cdiv> C ) ) ) \<longleftrightarrow> 
 ( C \<noteq> \<zero> \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) \<cdiv> C ) = 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> C ) \<ca> ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> C ) ) ) )" by (rule MMI_imbi2d)
   have S13: "C = 
 if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
 ( C \<noteq> \<zero> \<longleftrightarrow> if ( C \<in> \<complex> , C , \<zero> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   have S14: "C = 
 if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) \<cdiv> C ) = 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) \<cdiv> if ( C \<in> \<complex> , C , \<zero> ) )" by (rule MMI_opreq2)
   have S15: "C = 
 if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> C ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( C \<in> \<complex> , C , \<zero> ) )" by (rule MMI_opreq2)
   have S16: "C = 
 if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> C ) = 
 ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> if ( C \<in> \<complex> , C , \<zero> ) )" by (rule MMI_opreq2)
   from S15 S16 have S17: "C = 
 if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> C ) \<ca> ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> C ) ) = 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( C \<in> \<complex> , C , \<zero> ) ) \<ca> ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> if ( C \<in> \<complex> , C , \<zero> ) ) )" by (rule MMI_opreq12d)
   from S14 S17 have S18: "C = 
 if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
 ( ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) \<cdiv> C ) = 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> C ) \<ca> ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> C ) ) \<longleftrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) \<cdiv> if ( C \<in> \<complex> , C , \<zero> ) ) = 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( C \<in> \<complex> , C , \<zero> ) ) \<ca> ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> if ( C \<in> \<complex> , C , \<zero> ) ) ) )" by (rule MMI_eqeq12d)
   from S13 S18 have S19: "C = 
 if ( C \<in> \<complex> , C , \<zero> ) \<longrightarrow> 
 ( ( C \<noteq> \<zero> \<longrightarrow> ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) \<cdiv> C ) = ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> C ) \<ca> ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> C ) ) ) \<longleftrightarrow> 
 ( if ( C \<in> \<complex> , C , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) \<cdiv> if ( C \<in> \<complex> , C , \<zero> ) ) = 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( C \<in> \<complex> , C , \<zero> ) ) \<ca> ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> if ( C \<in> \<complex> , C , \<zero> ) ) ) ) )" by (rule MMI_imbi12d)
   have S20: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S20 have S21: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S22: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S22 have S23: "if ( B \<in> \<complex> , B , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S24: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S24 have S25: "if ( C \<in> \<complex> , C , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S21 S23 S25 have S26: "if ( C \<in> \<complex> , C , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<ca> if ( B \<in> \<complex> , B , \<zero> ) ) \<cdiv> if ( C \<in> \<complex> , C , \<zero> ) ) = 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdiv> if ( C \<in> \<complex> , C , \<zero> ) ) \<ca> ( if ( B \<in> \<complex> , B , \<zero> ) \<cdiv> if ( C \<in> \<complex> , C , \<zero> ) ) )" by (rule MMI_divdirz)
   from S6 S12 S19 S26 have S27: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( C \<noteq> \<zero> \<longrightarrow> 
 ( ( A \<ca> B ) \<cdiv> C ) = 
 ( ( A \<cdiv> C ) \<ca> ( B \<cdiv> C ) ) )" by (rule MMI_dedth3h)
   from S27 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<ca> B ) \<cdiv> C ) = 
 ( ( A \<cdiv> C ) \<ca> ( B \<cdiv> C ) )" by (rule MMI_imp)
qed

lemma (in MMIsar0) MMI_divcan3: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "A \<noteq> \<zero>"   
   shows "( ( A \<cdot> B ) \<cdiv> A ) = B"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from A1 have S3: "A \<in> \<complex>".
   from A3 have S4: "A \<noteq> \<zero>".
   from S1 S2 S3 S4 have S5: "( ( A \<cdot> B ) \<cdiv> A ) = ( A \<cdot> ( B \<cdiv> A ) )" by (rule MMI_divass)
   from A1 have S6: "A \<in> \<complex>".
   from A2 have S7: "B \<in> \<complex>".
   from A3 have S8: "A \<noteq> \<zero>".
   from S6 S7 S8 have S9: "( A \<cdot> ( B \<cdiv> A ) ) = B" by (rule MMI_divcan2)
   from S5 S9 show "( ( A \<cdot> B ) \<cdiv> A ) = B" by (rule MMI_eqtr)
qed

lemma (in MMIsar0) MMI_divcan4: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "A \<noteq> \<zero>"   
   shows "( ( B \<cdot> A ) \<cdiv> A ) = B"
proof -
   from A2 have S1: "B \<in> \<complex>".
   from A1 have S2: "A \<in> \<complex>".
   from S1 S2 have S3: "( B \<cdot> A ) = ( A \<cdot> B )" by (rule MMI_mulcom)
   from S3 have S4: "( ( B \<cdot> A ) \<cdiv> A ) = ( ( A \<cdot> B ) \<cdiv> A )" by (rule MMI_opreq1i)
   from A1 have S5: "A \<in> \<complex>".
   from A2 have S6: "B \<in> \<complex>".
   from A3 have S7: "A \<noteq> \<zero>".
   from S5 S6 S7 have S8: "( ( A \<cdot> B ) \<cdiv> A ) = B" by (rule MMI_divcan3)
   from S4 S8 show "( ( B \<cdot> A ) \<cdiv> A ) = B" by (rule MMI_eqtr)
qed

lemma (in MMIsar0) MMI_divcan3z: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "A \<noteq> \<zero> \<longrightarrow> ( ( A \<cdot> B ) \<cdiv> A ) = B"
proof -
   have S1: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( A \<cdot> B ) = 
 ( if ( A \<noteq> \<zero> , A , \<one> ) \<cdot> B )" by (rule MMI_opreq1)
   have S2: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 A = if ( A \<noteq> \<zero> , A , \<one> )" by (rule MMI_id)
   from S1 S2 have S3: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> A ) = 
 ( ( if ( A \<noteq> \<zero> , A , \<one> ) \<cdot> B ) \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) )" by (rule MMI_opreq12d)
   from S3 have S4: "A = 
 if ( A \<noteq> \<zero> , A , \<one> ) \<longrightarrow> 
 ( ( ( A \<cdot> B ) \<cdiv> A ) = 
 B \<longleftrightarrow> 
 ( ( if ( A \<noteq> \<zero> , A , \<one> ) \<cdot> B ) \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) ) = 
 B )" by (rule MMI_eqeq1d)
   from A1 have S5: "A \<in> \<complex>".
   have S6: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S5 S6 have S7: "if ( A \<noteq> \<zero> , A , \<one> ) \<in> \<complex>" by (rule MMI_keepel)
   from A2 have S8: "B \<in> \<complex>".
   have S9: "if ( A \<noteq> \<zero> , A , \<one> ) \<noteq> \<zero>" by (rule MMI_elimne0)
   from S7 S8 S9 have S10: "( ( if ( A \<noteq> \<zero> , A , \<one> ) \<cdot> B ) \<cdiv> if ( A \<noteq> \<zero> , A , \<one> ) ) = 
 B" by (rule MMI_divcan3)
   from S4 S10 show "A \<noteq> \<zero> \<longrightarrow> ( ( A \<cdot> B ) \<cdiv> A ) = B" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_divcan4z: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>"   
   shows "A \<noteq> \<zero> \<longrightarrow> ( ( B \<cdot> A ) \<cdiv> A ) = B"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "B \<in> \<complex>".
   from S1 S2 have S3: "A \<noteq> \<zero> \<longrightarrow> ( ( A \<cdot> B ) \<cdiv> A ) = B" by (rule MMI_divcan3z)
   from A2 have S4: "B \<in> \<complex>".
   from A1 have S5: "A \<in> \<complex>".
   from S4 S5 have S6: "( B \<cdot> A ) = ( A \<cdot> B )" by (rule MMI_mulcom)
   from S6 have S7: "( ( B \<cdot> A ) \<cdiv> A ) = ( ( A \<cdot> B ) \<cdiv> A )" by (rule MMI_opreq1i)
   from S3 S7 show "A \<noteq> \<zero> \<longrightarrow> ( ( B \<cdot> A ) \<cdiv> A ) = B" by (rule MMI_syl5eq)
qed

lemma (in MMIsar0) MMI_divcan3t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> A ) = B"
proof -
   have S1: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<noteq> \<zero> \<longleftrightarrow> if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   have S2: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( A \<cdot> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B )" by (rule MMI_opreq1)
   have S3: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 A = if ( A \<in> \<complex> , A , \<zero> )" by (rule MMI_id)
   from S2 S3 have S4: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> A ) = 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_opreq12d)
   from S4 have S5: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( ( A \<cdot> B ) \<cdiv> A ) = 
 B \<longleftrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) = 
 B )" by (rule MMI_eqeq1d)
   from S1 S5 have S6: "A = 
 if ( A \<in> \<complex> , A , \<zero> ) \<longrightarrow> 
 ( ( A \<noteq> \<zero> \<longrightarrow> ( ( A \<cdot> B ) \<cdiv> A ) = B ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) = 
 B ) )" by (rule MMI_imbi12d)
   have S7: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) = 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_opreq2)
   from S7 have S8: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) = 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) )" by (rule MMI_opreq1d)
   have S9: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 B = if ( B \<in> \<complex> , B , \<zero> )" by (rule MMI_id)
   from S8 S9 have S10: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) = 
 B \<longleftrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) = 
 if ( B \<in> \<complex> , B , \<zero> ) )" by (rule MMI_eqeq12d)
   from S10 have S11: "B = 
 if ( B \<in> \<complex> , B , \<zero> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> \<longrightarrow> ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> B ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) = B ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) = 
 if ( B \<in> \<complex> , B , \<zero> ) ) )" by (rule MMI_imbi2d)
   have S12: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S12 have S13: "if ( A \<in> \<complex> , A , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   have S14: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   from S14 have S15: "if ( B \<in> \<complex> , B , \<zero> ) \<in> \<complex>" by (rule MMI_elimel)
   from S13 S15 have S16: "if ( A \<in> \<complex> , A , \<zero> ) \<noteq> \<zero> \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<zero> ) \<cdot> if ( B \<in> \<complex> , B , \<zero> ) ) \<cdiv> if ( A \<in> \<complex> , A , \<zero> ) ) = 
 if ( B \<in> \<complex> , B , \<zero> )" by (rule MMI_divcan3z)
   from S6 S11 S16 have S17: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( A \<noteq> \<zero> \<longrightarrow> ( ( A \<cdot> B ) \<cdiv> A ) = B )" by (rule MMI_dedth2h)
   from S17 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> A ) = B" by (rule MMI_3impia)
qed

lemma (in MMIsar0) MMI_divcan4t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( ( B \<cdot> A ) \<cdiv> A ) = B"
proof -
   have S1: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( A \<cdot> B ) = ( B \<cdot> A )" by (rule MMI_axmulcom)
   from S1 have S2: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> A ) = ( ( B \<cdot> A ) \<cdiv> A )" by (rule MMI_opreq1d)
   from S2 have S3: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> A ) = ( ( B \<cdot> A ) \<cdiv> A )" by (rule MMI_3adant3)
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdot> B ) \<cdiv> A ) = B" by (rule MMI_divcan3t)
   from S3 S4 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( ( B \<cdot> A ) \<cdiv> A ) = B" by (rule MMI_eqtr3d)
qed

lemma (in MMIsar0) MMI_div11: assumes A1: "A \<in> \<complex>" and
    A2: "B \<in> \<complex>" and
    A3: "C \<in> \<complex>" and
    A4: "C \<noteq> \<zero>"   
   shows "( A \<cdiv> C ) = ( B \<cdiv> C ) \<longleftrightarrow> A = B"
proof -
   from A3 have S1: "C \<in> \<complex>".
   from A1 have S2: "A \<in> \<complex>".
   from A3 have S3: "C \<in> \<complex>".
   from A4 have S4: "C \<noteq> \<zero>".
   from S2 S3 S4 have S5: "( A \<cdiv> C ) \<in> \<complex>" by (rule MMI_divcl)
   from A2 have S6: "B \<in> \<complex>".
   from A3 have S7: "C \<in> \<complex>".
   from A4 have S8: "C \<noteq> \<zero>".
   from S6 S7 S8 have S9: "( B \<cdiv> C ) \<in> \<complex>" by (rule MMI_divcl)
   from A4 have S10: "C \<noteq> \<zero>".
   from S1 S5 S9 S10 have S11: "( C \<cdot> ( A \<cdiv> C ) ) = 
 ( C \<cdot> ( B \<cdiv> C ) ) \<longleftrightarrow> 
 ( A \<cdiv> C ) = ( B \<cdiv> C )" by (rule MMI_mulcan)
   from A3 have S12: "C \<in> \<complex>".
   from A1 have S13: "A \<in> \<complex>".
   from A4 have S14: "C \<noteq> \<zero>".
   from S12 S13 S14 have S15: "( C \<cdot> ( A \<cdiv> C ) ) = A" by (rule MMI_divcan2)
   from A3 have S16: "C \<in> \<complex>".
   from A2 have S17: "B \<in> \<complex>".
   from A4 have S18: "C \<noteq> \<zero>".
   from S16 S17 S18 have S19: "( C \<cdot> ( B \<cdiv> C ) ) = B" by (rule MMI_divcan2)
   from S15 S19 have S20: "( C \<cdot> ( A \<cdiv> C ) ) = 
 ( C \<cdot> ( B \<cdiv> C ) ) \<longleftrightarrow> A = B" by (rule MMI_eqeq12i)
   from S11 S20 show "( A \<cdiv> C ) = ( B \<cdiv> C ) \<longleftrightarrow> A = B" by (rule MMI_bitr3)
qed

lemma (in MMIsar0) MMI_div11t: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> C ) = ( B \<cdiv> C ) \<longleftrightarrow> A = B )"
proof -
   have S1: "A = 
 if ( A \<in> \<complex> , A , \<one> ) \<longrightarrow> 
 ( A \<cdiv> C ) = 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdiv> C )" by (rule MMI_opreq1)
   from S1 have S2: "A = 
 if ( A \<in> \<complex> , A , \<one> ) \<longrightarrow> 
 ( ( A \<cdiv> C ) = 
 ( B \<cdiv> C ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdiv> C ) = 
 ( B \<cdiv> C ) )" by (rule MMI_eqeq1d)
   have S3: "A = 
 if ( A \<in> \<complex> , A , \<one> ) \<longrightarrow> 
 ( A = B \<longleftrightarrow> if ( A \<in> \<complex> , A , \<one> ) = B )" by (rule MMI_eqeq1)
   from S2 S3 have S4: "A = 
 if ( A \<in> \<complex> , A , \<one> ) \<longrightarrow> 
 ( ( ( A \<cdiv> C ) = ( B \<cdiv> C ) \<longleftrightarrow> A = B ) \<longleftrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<one> ) \<cdiv> C ) = 
 ( B \<cdiv> C ) \<longleftrightarrow> 
 if ( A \<in> \<complex> , A , \<one> ) = B ) )" by (rule MMI_bibi12d)
   have S5: "B = 
 if ( B \<in> \<complex> , B , \<one> ) \<longrightarrow> 
 ( B \<cdiv> C ) = 
 ( if ( B \<in> \<complex> , B , \<one> ) \<cdiv> C )" by (rule MMI_opreq1)
   from S5 have S6: "B = 
 if ( B \<in> \<complex> , B , \<one> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<one> ) \<cdiv> C ) = 
 ( B \<cdiv> C ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdiv> C ) = 
 ( if ( B \<in> \<complex> , B , \<one> ) \<cdiv> C ) )" by (rule MMI_eqeq2d)
   have S7: "B = 
 if ( B \<in> \<complex> , B , \<one> ) \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<one> ) = 
 B \<longleftrightarrow> 
 if ( A \<in> \<complex> , A , \<one> ) = 
 if ( B \<in> \<complex> , B , \<one> ) )" by (rule MMI_eqeq2)
   from S6 S7 have S8: "B = 
 if ( B \<in> \<complex> , B , \<one> ) \<longrightarrow> 
 ( ( ( if ( A \<in> \<complex> , A , \<one> ) \<cdiv> C ) = ( B \<cdiv> C ) \<longleftrightarrow> if ( A \<in> \<complex> , A , \<one> ) = B ) \<longleftrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<one> ) \<cdiv> C ) = 
 ( if ( B \<in> \<complex> , B , \<one> ) \<cdiv> C ) \<longleftrightarrow> 
 if ( A \<in> \<complex> , A , \<one> ) = 
 if ( B \<in> \<complex> , B , \<one> ) ) )" by (rule MMI_bibi12d)
   have S9: "C = 
 if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<longrightarrow> 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdiv> C ) = 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdiv> if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) )" by (rule MMI_opreq2)
   have S10: "C = 
 if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<longrightarrow> 
 ( if ( B \<in> \<complex> , B , \<one> ) \<cdiv> C ) = 
 ( if ( B \<in> \<complex> , B , \<one> ) \<cdiv> if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) )" by (rule MMI_opreq2)
   from S9 S10 have S11: "C = 
 if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<longrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<one> ) \<cdiv> C ) = 
 ( if ( B \<in> \<complex> , B , \<one> ) \<cdiv> C ) \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdiv> if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) ) = 
 ( if ( B \<in> \<complex> , B , \<one> ) \<cdiv> if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) ) )" by (rule MMI_eqeq12d)
   from S11 have S12: "C = 
 if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<longrightarrow> 
 ( ( ( if ( A \<in> \<complex> , A , \<one> ) \<cdiv> C ) = ( if ( B \<in> \<complex> , B , \<one> ) \<cdiv> C ) \<longleftrightarrow> if ( A \<in> \<complex> , A , \<one> ) = if ( B \<in> \<complex> , B , \<one> ) ) \<longleftrightarrow> 
 ( ( if ( A \<in> \<complex> , A , \<one> ) \<cdiv> if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) ) = 
 ( if ( B \<in> \<complex> , B , \<one> ) \<cdiv> if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) ) \<longleftrightarrow> 
 if ( A \<in> \<complex> , A , \<one> ) = 
 if ( B \<in> \<complex> , B , \<one> ) ) )" by (rule MMI_bibi1d)
   have S13: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S13 have S14: "if ( A \<in> \<complex> , A , \<one> ) \<in> \<complex>" by (rule MMI_elimel)
   have S15: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S15 have S16: "if ( B \<in> \<complex> , B , \<one> ) \<in> \<complex>" by (rule MMI_elimel)
   have S17: "C = 
 if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<longrightarrow> 
 ( C \<in> \<complex> \<longleftrightarrow> 
 if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<in> \<complex> )" by (rule MMI_eleq1)
   have S18: "C = 
 if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<longrightarrow> 
 ( C \<noteq> \<zero> \<longleftrightarrow> 
 if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   from S17 S18 have S19: "C = 
 if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<longrightarrow> 
 ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longleftrightarrow> 
 ( if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<in> \<complex> \<and> if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<noteq> \<zero> ) )" by (rule MMI_anbi12d)
   have S20: "\<one> = 
 if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<longrightarrow> 
 ( \<one> \<in> \<complex> \<longleftrightarrow> 
 if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<in> \<complex> )" by (rule MMI_eleq1)
   have S21: "\<one> = 
 if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<longrightarrow> 
 ( \<one> \<noteq> \<zero> \<longleftrightarrow> 
 if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<noteq> \<zero> )" by (rule MMI_neeq1)
   from S20 S21 have S22: "\<one> = 
 if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<longrightarrow> 
 ( ( \<one> \<in> \<complex> \<and> \<one> \<noteq> \<zero> ) \<longleftrightarrow> 
 ( if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<in> \<complex> \<and> if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<noteq> \<zero> ) )" by (rule MMI_anbi12d)
   have S23: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   have S24: "\<one> \<noteq> \<zero>" by (rule MMI_ax1ne0)
   from S23 S24 have S25: "\<one> \<in> \<complex> \<and> \<one> \<noteq> \<zero>" by (rule MMI_pm3_2i)
   from S19 S22 S25 have S26: "if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<in> \<complex> \<and> if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<noteq> \<zero>" by (rule MMI_elimhyp)
   from S26 have S27: "if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<in> \<complex>" by (rule MMI_pm3_26i)
   from S26 have S28: "if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<in> \<complex> \<and> if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<noteq> \<zero>" .
   from S28 have S29: "if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) \<noteq> \<zero>" by (rule MMI_pm3_27i)
   from S14 S16 S27 S29 have S30: "( if ( A \<in> \<complex> , A , \<one> ) \<cdiv> if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) ) = 
 ( if ( B \<in> \<complex> , B , \<one> ) \<cdiv> if ( ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) , C , \<one> ) ) \<longleftrightarrow> 
 if ( A \<in> \<complex> , A , \<one> ) = 
 if ( B \<in> \<complex> , B , \<one> )" by (rule MMI_div11)
   from S4 S8 S12 S30 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> C ) = ( B \<cdiv> C ) \<longleftrightarrow> A = B )" by (rule MMI_dedth3h)
qed


end
