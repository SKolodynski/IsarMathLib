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

section \<open>Metamath examples\<close>

theory MMI_examples imports MMI_Complex_ZF

begin 

text\<open>This theory contains 10 theorems translated from 
  Metamath (with proofs). It is included
  in the proof document as an illustration of how a translated
  Metamath proof looks like. The "known\_theorems.txt"
  file included in the IsarMathLib distribution provides
  a list of all translated facts.\<close>

(******201-210****************************)

lemma (in MMIsar0) MMI_dividt: 
   shows "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> ( A \<cdiv> A ) = \<one>"
proof -
   have S1: "( A \<in> \<complex> \<and> A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> A ) = ( A \<cdot> ( \<one> \<cdiv> A ) )" by (rule MMI_divrect)
   from S1 have S2: "( ( A \<in> \<complex> \<and> A \<in> \<complex> ) \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> A ) = ( A \<cdot> ( \<one> \<cdiv> A ) )" by (rule MMI_3expa)
   from S2 have S3: "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> A ) = ( A \<cdot> ( \<one> \<cdiv> A ) )" by (rule MMI_anabsan)
   have S4: "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdot> ( \<one> \<cdiv> A ) ) = \<one>" by (rule MMI_recidt)
   from S3 S4 show "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> ( A \<cdiv> A ) = \<one>" by (rule MMI_eqtrd)
qed

lemma (in MMIsar0) MMI_div0t: 
   shows "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> ( \<zero> \<cdiv> A ) = \<zero>"
proof -
   have S1: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   have S2: "( \<zero> \<in> \<complex> \<and> A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( \<zero> \<cdiv> A ) = ( \<zero> \<cdot> ( \<one> \<cdiv> A ) )" by (rule MMI_divrect)
   from S1 S2 have S3: "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( \<zero> \<cdiv> A ) = ( \<zero> \<cdot> ( \<one> \<cdiv> A ) )" by (rule MMI_mp3an1)
   have S4: "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> ( \<one> \<cdiv> A ) \<in> \<complex>" by (rule MMI_recclt)
   have S5: "( \<one> \<cdiv> A ) \<in> \<complex> \<longrightarrow> ( \<zero> \<cdot> ( \<one> \<cdiv> A ) ) = \<zero>" 
     by (rule MMI_mul02t)
   from S4 S5 have S6: "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> 
 ( \<zero> \<cdot> ( \<one> \<cdiv> A ) ) = \<zero>" by (rule MMI_syl)
   from S3 S6 show "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> ( \<zero> \<cdiv> A ) = \<zero>" by (rule MMI_eqtrd)
qed

lemma (in MMIsar0) MMI_diveq0t: 
   shows "( A \<in> \<complex> \<and> C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> C ) = \<zero> \<longleftrightarrow> A = \<zero> )"
proof -
   have S1: "( C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> ( \<zero> \<cdiv> C ) = \<zero>" by (rule MMI_div0t)
   from S1 have S2: "( C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> C ) = 
 ( \<zero> \<cdiv> C ) \<longleftrightarrow> ( A \<cdiv> C ) = \<zero> )" by (rule MMI_eqeq2d)
   from S2 have S3: "( A \<in> \<complex> \<and> C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> C ) = 
 ( \<zero> \<cdiv> C ) \<longleftrightarrow> ( A \<cdiv> C ) = \<zero> )" by (rule MMI_3adant1)
   have S4: "\<zero> \<in> \<complex>" by (rule MMI_0cn)
   have S5: "( A \<in> \<complex> \<and> \<zero> \<in> \<complex> \<and> ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> C ) = ( \<zero> \<cdiv> C ) \<longleftrightarrow> A = \<zero> )" by (rule MMI_div11t)
   from S4 S5 have S6: "( A \<in> \<complex> \<and> ( C \<in> \<complex> \<and> C \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( A \<cdiv> C ) = ( \<zero> \<cdiv> C ) \<longleftrightarrow> A = \<zero> )" by (rule MMI_mp3an2)
   from S6 have S7: "( A \<in> \<complex> \<and> C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> C ) = ( \<zero> \<cdiv> C ) \<longleftrightarrow> A = \<zero> )" by (rule MMI_3impb)
   from S3 S7 show "( A \<in> \<complex> \<and> C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> C ) = \<zero> \<longleftrightarrow> A = \<zero> )" by (rule MMI_bitr3d)
qed

lemma (in MMIsar0) MMI_recrec: assumes A1: "A \<in> \<complex>" and
    A2: "A \<noteq> \<zero>"   
   shows "( \<one> \<cdiv> ( \<one> \<cdiv> A ) ) = A"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "A \<noteq> \<zero>".
   from S1 S2 have S3: "( \<one> \<cdiv> A ) \<in> \<complex>" by (rule MMI_reccl)
   have S4: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from A1 have S5: "A \<in> \<complex>".
   have S6: "\<one> \<noteq> \<zero>" by (rule MMI_ax1ne0)
   from A2 have S7: "A \<noteq> \<zero>".
   from S4 S5 S6 S7 have S8: "( \<one> \<cdiv> A ) \<noteq> \<zero>" by (rule MMI_divne0)
   from S3 S8 have S9: "( ( \<one> \<cdiv> A ) \<cdot> ( \<one> \<cdiv> ( \<one> \<cdiv> A ) ) ) = \<one>" 
     by (rule MMI_recid)
   from S9 have S10: "( A \<cdot> ( ( \<one> \<cdiv> A ) \<cdot> ( \<one> \<cdiv> ( \<one> \<cdiv> A ) ) ) ) = 
 ( A \<cdot> \<one> )" by (rule MMI_opreq2i)
   from A1 have S11: "A \<in> \<complex>".
   from A2 have S12: "A \<noteq> \<zero>".
   from S11 S12 have S13: "( A \<cdot> ( \<one> \<cdiv> A ) ) = \<one>" by (rule MMI_recid)
   from S13 have S14: "( ( A \<cdot> ( \<one> \<cdiv> A ) ) \<cdot> ( \<one> \<cdiv> ( \<one> \<cdiv> A ) ) ) = 
 ( \<one> \<cdot> ( \<one> \<cdiv> ( \<one> \<cdiv> A ) ) )" by (rule MMI_opreq1i)
   from A1 have S15: "A \<in> \<complex>".
   from S3 have S16: "( \<one> \<cdiv> A ) \<in> \<complex>" .
   from S3 have S17: "( \<one> \<cdiv> A ) \<in> \<complex>" .
   from S8 have S18: "( \<one> \<cdiv> A ) \<noteq> \<zero>" .
   from S17 S18 have S19: "( \<one> \<cdiv> ( \<one> \<cdiv> A ) ) \<in> \<complex>" by (rule MMI_reccl)
   from S15 S16 S19 have S20: 
     "( ( A \<cdot> ( \<one> \<cdiv> A ) ) \<cdot> ( \<one> \<cdiv> ( \<one> \<cdiv> A ) ) ) = 
 ( A \<cdot> ( ( \<one> \<cdiv> A ) \<cdot> ( \<one> \<cdiv> ( \<one> \<cdiv> A ) ) ) )" by (rule MMI_mulass)
   from S19 have S21: "( \<one> \<cdiv> ( \<one> \<cdiv> A ) ) \<in> \<complex>" .
   from S21 have S22: "( \<one> \<cdot> ( \<one> \<cdiv> ( \<one> \<cdiv> A ) ) ) = 
 ( \<one> \<cdiv> ( \<one> \<cdiv> A ) )" by (rule MMI_mulid2)
   from S14 S20 S22 have S23: 
     "( A \<cdot> ( ( \<one> \<cdiv> A ) \<cdot> ( \<one> \<cdiv> ( \<one> \<cdiv> A ) ) ) ) = 
 ( \<one> \<cdiv> ( \<one> \<cdiv> A ) )" by (rule MMI_3eqtr3)
   from A1 have S24: "A \<in> \<complex>".
   from S24 have S25: "( A \<cdot> \<one> ) = A" by (rule MMI_mulid1)
   from S10 S23 S25 show "( \<one> \<cdiv> ( \<one> \<cdiv> A ) ) = A" by (rule MMI_3eqtr3)
qed

lemma (in MMIsar0) MMI_divid: assumes A1: "A \<in> \<complex>" and
    A2: "A \<noteq> \<zero>"   
   shows "( A \<cdiv> A ) = \<one>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A1 have S2: "A \<in> \<complex>".
   from A2 have S3: "A \<noteq> \<zero>".
   from S1 S2 S3 have S4: "( A \<cdiv> A ) = ( A \<cdot> ( \<one> \<cdiv> A ) )" by (rule MMI_divrec)
   from A1 have S5: "A \<in> \<complex>".
   from A2 have S6: "A \<noteq> \<zero>".
   from S5 S6 have S7: "( A \<cdot> ( \<one> \<cdiv> A ) ) = \<one>" by (rule MMI_recid)
   from S4 S7 show "( A \<cdiv> A ) = \<one>" by (rule MMI_eqtr)
qed

lemma (in MMIsar0) MMI_div0: assumes A1: "A \<in> \<complex>" and
    A2: "A \<noteq> \<zero>"   
   shows "( \<zero> \<cdiv> A ) = \<zero>"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from A2 have S2: "A \<noteq> \<zero>".
   have S3: "( A \<in> \<complex> \<and> A \<noteq> \<zero> ) \<longrightarrow> ( \<zero> \<cdiv> A ) = \<zero>" by (rule MMI_div0t)
   from S1 S2 S3 show "( \<zero> \<cdiv> A ) = \<zero>" by (rule MMI_mp2an)
qed

lemma (in MMIsar0) MMI_div1: assumes A1: "A \<in> \<complex>"   
   shows "( A \<cdiv> \<one> ) = A"
proof -
   from A1 have S1: "A \<in> \<complex>".
   from S1 have S2: "( \<one> \<cdot> A ) = A" by (rule MMI_mulid2)
   from A1 have S3: "A \<in> \<complex>".
   have S4: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from A1 have S5: "A \<in> \<complex>".
   have S6: "\<one> \<noteq> \<zero>" by (rule MMI_ax1ne0)
   from S3 S4 S5 S6 have S7: "( A \<cdiv> \<one> ) = A \<longleftrightarrow> ( \<one> \<cdot> A ) = A" 
     by (rule MMI_divmul)
   from S2 S7 show "( A \<cdiv> \<one> ) = A" by (rule MMI_mpbir)
qed

lemma (in MMIsar0) MMI_div1t: 
   shows "A \<in> \<complex> \<longrightarrow> ( A \<cdiv> \<one> ) = A"
proof -
   have S1: "A = 
 if ( A \<in> \<complex> , A , \<one> ) \<longrightarrow> 
 ( A \<cdiv> \<one> ) = 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdiv> \<one> )" by (rule MMI_opreq1)
   have S2: "A = 
 if ( A \<in> \<complex> , A , \<one> ) \<longrightarrow> 
 A = if ( A \<in> \<complex> , A , \<one> )" by (rule MMI_id)
   from S1 S2 have S3: "A = 
 if ( A \<in> \<complex> , A , \<one> ) \<longrightarrow> 
 ( ( A \<cdiv> \<one> ) = 
 A \<longleftrightarrow> 
 ( if ( A \<in> \<complex> , A , \<one> ) \<cdiv> \<one> ) = 
 if ( A \<in> \<complex> , A , \<one> ) )" by (rule MMI_eqeq12d)
   have S4: "\<one> \<in> \<complex>" by (rule MMI_1cn)
   from S4 have S5: "if ( A \<in> \<complex> , A , \<one> ) \<in> \<complex>" by (rule MMI_elimel)
   from S5 have S6: "( if ( A \<in> \<complex> , A , \<one> ) \<cdiv> \<one> ) = 
 if ( A \<in> \<complex> , A , \<one> )" by (rule MMI_div1)
   from S3 S6 show "A \<in> \<complex> \<longrightarrow> ( A \<cdiv> \<one> ) = A" by (rule MMI_dedth)
qed

lemma (in MMIsar0) MMI_divnegt: 
   shows "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( \<cn> ( A \<cdiv> B ) ) = ( ( \<cn> A ) \<cdiv> B )"
proof -
   have S1: "( A \<in> \<complex> \<and> ( \<one> \<cdiv> B ) \<in> \<complex> ) \<longrightarrow> 
 ( ( \<cn> A ) \<cdot> ( \<one> \<cdiv> B ) ) = 
 ( \<cn> ( A \<cdot> ( \<one> \<cdiv> B ) ) )" by (rule MMI_mulneg1t)
   have S2: "( B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> ( \<one> \<cdiv> B ) \<in> \<complex>" by (rule MMI_recclt)
   from S1 S2 have S3: "( A \<in> \<complex> \<and> ( B \<in> \<complex> \<and> B \<noteq> \<zero> ) ) \<longrightarrow> 
 ( ( \<cn> A ) \<cdot> ( \<one> \<cdiv> B ) ) = 
 ( \<cn> ( A \<cdot> ( \<one> \<cdiv> B ) ) )" by (rule MMI_sylan2)
   from S3 have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( \<cn> A ) \<cdot> ( \<one> \<cdiv> B ) ) = 
 ( \<cn> ( A \<cdot> ( \<one> \<cdiv> B ) ) )" by (rule MMI_3impb)
   have S5: "( ( \<cn> A ) \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( \<cn> A ) \<cdiv> B ) = 
 ( ( \<cn> A ) \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_divrect)
   have S6: "A \<in> \<complex> \<longrightarrow> ( \<cn> A ) \<in> \<complex>" by (rule MMI_negclt)
   from S5 S6 have S7: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( ( \<cn> A ) \<cdiv> B ) = 
 ( ( \<cn> A ) \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_syl3an1)
   have S8: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> B ) = ( A \<cdot> ( \<one> \<cdiv> B ) )" by (rule MMI_divrect)
   from S8 have S9: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( \<cn> ( A \<cdiv> B ) ) = 
 ( \<cn> ( A \<cdot> ( \<one> \<cdiv> B ) ) )" by (rule MMI_negeqd)
   from S4 S7 S9 show "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> B \<noteq> \<zero> ) \<longrightarrow> 
 ( \<cn> ( A \<cdiv> B ) ) = ( ( \<cn> A ) \<cdiv> B )" by (rule MMI_3eqtr4rd)
qed

lemma (in MMIsar0) MMI_divsubdirt: 
   shows "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cdiv> C ) = 
 ( ( A \<cdiv> C ) \<cs> ( B \<cdiv> C ) )"
proof -
   have S1: "( ( A \<in> \<complex> \<and> ( \<cn> B ) \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<ca> ( \<cn> B ) ) \<cdiv> C ) = 
 ( ( A \<cdiv> C ) \<ca> ( ( \<cn> B ) \<cdiv> C ) )" by (rule MMI_divdirt)
   have S2: "B \<in> \<complex> \<longrightarrow> ( \<cn> B ) \<in> \<complex>" by (rule MMI_negclt)
   from S1 S2 have S3: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<ca> ( \<cn> B ) ) \<cdiv> C ) = 
 ( ( A \<cdiv> C ) \<ca> ( ( \<cn> B ) \<cdiv> C ) )" by (rule MMI_syl3anl2)
   have S4: "( A \<in> \<complex> \<and> B \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> ( \<cn> B ) ) = ( A \<cs> B )" by (rule MMI_negsubt)
   from S4 have S5: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( A \<ca> ( \<cn> B ) ) = ( A \<cs> B )" by (rule MMI_3adant3)
   from S5 have S6: "( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<ca> ( \<cn> B ) ) \<cdiv> C ) = 
 ( ( A \<cs> B ) \<cdiv> C )" by (rule MMI_opreq1d)
   from S6 have S7: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<ca> ( \<cn> B ) ) \<cdiv> C ) = 
 ( ( A \<cs> B ) \<cdiv> C )" by (rule MMI_adantr)
   have S8: "( B \<in> \<complex> \<and> C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( \<cn> ( B \<cdiv> C ) ) = ( ( \<cn> B ) \<cdiv> C )" by (rule MMI_divnegt)
   from S8 have S9: "( ( B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( \<cn> ( B \<cdiv> C ) ) = ( ( \<cn> B ) \<cdiv> C )" by (rule MMI_3expa)
   from S9 have S10: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( \<cn> ( B \<cdiv> C ) ) = ( ( \<cn> B ) \<cdiv> C )" by (rule MMI_3adantl1)
   from S10 have S11: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> C ) \<ca> ( \<cn> ( B \<cdiv> C ) ) ) = 
 ( ( A \<cdiv> C ) \<ca> ( ( \<cn> B ) \<cdiv> C ) )" by (rule MMI_opreq2d)
   have S12: "( ( A \<cdiv> C ) \<in> \<complex> \<and> ( B \<cdiv> C ) \<in> \<complex> ) \<longrightarrow> 
 ( ( A \<cdiv> C ) \<ca> ( \<cn> ( B \<cdiv> C ) ) ) = 
 ( ( A \<cdiv> C ) \<cs> ( B \<cdiv> C ) )" by (rule MMI_negsubt)
   have S13: "( A \<in> \<complex> \<and> C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> C ) \<in> \<complex>" by (rule MMI_divclt)
   from S13 have S14: "( ( A \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> C ) \<in> \<complex>" by (rule MMI_3expa)
   from S14 have S15: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( A \<cdiv> C ) \<in> \<complex>" by (rule MMI_3adantl2)
   have S16: "( B \<in> \<complex> \<and> C \<in> \<complex> \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( B \<cdiv> C ) \<in> \<complex>" by (rule MMI_divclt)
   from S16 have S17: "( ( B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( B \<cdiv> C ) \<in> \<complex>" by (rule MMI_3expa)
   from S17 have S18: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( B \<cdiv> C ) \<in> \<complex>" by (rule MMI_3adantl1)
   from S12 S15 S18 have S19: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> C ) \<ca> ( \<cn> ( B \<cdiv> C ) ) ) = 
 ( ( A \<cdiv> C ) \<cs> ( B \<cdiv> C ) )" by (rule MMI_sylanc)
   from S11 S19 have S20: "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cdiv> C ) \<ca> ( ( \<cn> B ) \<cdiv> C ) ) = 
 ( ( A \<cdiv> C ) \<cs> ( B \<cdiv> C ) )" by (rule MMI_eqtr3d)
   from S3 S7 S20 show "( ( A \<in> \<complex> \<and> B \<in> \<complex> \<and> C \<in> \<complex> ) \<and> C \<noteq> \<zero> ) \<longrightarrow> 
 ( ( A \<cs> B ) \<cdiv> C ) = 
 ( ( A \<cdiv> C ) \<cs> ( B \<cdiv> C ) )" by (rule MMI_3eqtr3d)
qed


end

